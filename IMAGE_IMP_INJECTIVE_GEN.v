Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IMAGE_IMP_INJECTIVE_GEN_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import EXTENSION_spec.
Require Import FINITE_IMAGE_spec.
Require Import IN_IMAGE_spec.
Require Import SUBSET_REFL_spec.
Require Import SURJECTIVE_IFF_INJECTIVE_GEN_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17500_spec.
Require Import thm17784_spec.
Require Import thm17930_spec.
Require Import thm1820_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
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
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19490_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
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
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Lemma lem4945028 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4945029 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem4945030 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem4945029 t1) (@lem4945028 t1)). Qed.
Lemma lem4945031 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem4945030 t1 t2). Qed.
Lemma lem4945032 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem4945033 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem4945032 t1 t2) (@lem4945031 t1 t2)). Qed.
Lemma lem4945034 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem4945033 t1 t2 t3). Qed.
Lemma lem4945035 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem4945036 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem4945035 t1 t2 t3) (@lem4945034 t1 t2 t3)). Qed.
Lemma lem4945037 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem4945036 t1 t2 t3)). Qed.
Lemma lem4945038 {A B : Type'} : term7 A B.
Proof. exact (@lem4944739 A B). Qed.
Lemma lem4945039 {A B : Type'} (s : A -> Prop) : term8 A B s.
Proof. exact (@lem4945038 A B s). Qed.
Lemma lem4945040 {A B : Type'} (s : A -> Prop) : (term8 A B s) = (term9 A B s).
Proof. exact (eq_refl (term8 A B s)). Qed.
Lemma lem4945041 {A B : Type'} (s : A -> Prop) : term9 A B s.
Proof. exact (EQ_MP (@lem4945040 A B s) (@lem4945039 A B s)). Qed.
Lemma lem4945042 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term10 A B s t.
Proof. exact (@lem4945041 A B s t). Qed.
Lemma lem4945043 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term10 A B s t) = (term11 A B t s).
Proof. exact (eq_refl (term10 A B s t)). Qed.
Lemma lem4945044 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term11 A B t s.
Proof. exact (EQ_MP (@lem4945043 A B t s) (@lem4945042 A B s t)). Qed.
Lemma lem4945045 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : term12 A B t s f.
Proof. exact (@lem4945044 A B t s f). Qed.
Lemma lem4945046 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term12 A B t s f) = (term13 A B t s f).
Proof. exact (eq_refl (term12 A B t s f)). Qed.
Lemma lem4945047 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : term13 A B t s f.
Proof. exact (EQ_MP (@lem4945046 A B t s f) (@lem4945045 A B t s f)). Qed.
Lemma lem4945048 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : term14 A B f s t.
Proof. exact (h1). Qed.
Lemma lem4945052 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : (@CARD A s) = (@CARD B t)) : (@CARD A s) = (@CARD B t).
Proof. exact (h1). Qed.
Lemma lem4945053 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : (@CARD A s) = (@CARD B t)) : (@CARD B t) = (@CARD A s).
Proof. exact (SYM (@lem4945052 A B s t h1)). Qed.
Lemma lem4945054 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : (@CARD B t) = (@CARD A s)) : (@CARD B t) = (@CARD A s).
Proof. exact (h1). Qed.
Lemma lem4945055 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : (@CARD B t) = (@CARD A s)) : (@CARD A s) = (@CARD B t).
Proof. exact (SYM (@lem4945054 A B t s h1)). Qed.
Lemma lem4945056 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : ((@CARD A s) = (@CARD B t)) = ((@CARD B t) = (@CARD A s)).
Proof. exact (prop_ext (fun h1 : (@CARD A s) = (@CARD B t) => @lem4945053 A B s t h1) (fun h1 : (@CARD B t) = (@CARD A s) => @lem4945055 A B t s h1)). Qed.
Lemma lem4945057 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4945058 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term15 A B s t) = (term16 A B t s).
Proof. exact (MK_COMB (@lem4945057) (@lem4945056 A B t s)). Qed.
Lemma lem4945059 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : (@IMAGE A B f s) = t) : (@IMAGE A B f s) = t.
Proof. exact (h1). Qed.
Lemma lem4945060 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : (@IMAGE A B f s) = t) : t = (@IMAGE A B f s).
Proof. exact (SYM (@lem4945059 A B f s t h1)). Qed.
Lemma lem4945061 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : t = (@IMAGE A B f s)) : t = (@IMAGE A B f s).
Proof. exact (h1). Qed.
Lemma lem4945062 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : t = (@IMAGE A B f s)) : (@IMAGE A B f s) = t.
Proof. exact (SYM (@lem4945061 A B t f s h1)). Qed.
Lemma lem4945063 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : ((@IMAGE A B f s) = t) = (t = (@IMAGE A B f s)).
Proof. exact (prop_ext (fun h1 : (@IMAGE A B f s) = t => @lem4945060 A B f s t h1) (fun h1 : t = (@IMAGE A B f s) => @lem4945062 A B t f s h1)). Qed.
Lemma lem4945064 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term17 A B f s t) = (term18 A B t f s).
Proof. exact (MK_COMB (@lem4945058 A B t s) (@lem4945063 A B t f s)). Qed.
Lemma lem4945065 {A : Type'} (s : A -> Prop) : (term19 A s) = (term19 A s).
Proof. exact (eq_refl (term19 A s)). Qed.
Lemma lem4945066 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term14 A B f s t) = (term20 A B t f s).
Proof. exact (MK_COMB (@lem4945065 A s) (@lem4945064 A B t f s)). Qed.
Lemma lem4945067 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : term20 A B t f s.
Proof. exact (EQ_MP (@lem4945066 A B t f s) (@lem4945048 A B f s t h1)). Qed.
Lemma lem4945068 {A B : Type'} (f : A -> B) : term21 A B f.
Proof. exact (@lem3615104 A B f). Qed.
Lemma lem4945069 {A B : Type'} (f : A -> B) : (term21 A B f) = (term22 A B f).
Proof. exact (eq_refl (term21 A B f)). Qed.
Lemma lem4945070 {A B : Type'} (f : A -> B) : term22 A B f.
Proof. exact (EQ_MP (@lem4945069 A B f) (@lem4945068 A B f)). Qed.
Lemma lem4945071 {A B : Type'} (f : A -> B) (s : A -> Prop) : term23 A B f s.
Proof. exact (@lem4945070 A B f s). Qed.
Lemma lem4945072 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term23 A B f s) = (term24 A B f s).
Proof. exact (eq_refl (term23 A B f s)). Qed.
Lemma lem4945073 {A B : Type'} (f : A -> B) (s : A -> Prop) : term24 A B f s.
Proof. exact (EQ_MP (@lem4945072 A B f s) (@lem4945071 A B f s)). Qed.
Lemma lem4945074 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4945075 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : term25 A B f s.
Proof. exact (@lem4945073 A B f s (@lem4945074 A s h1)). Qed.
Lemma lem4945076 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term25 A B f s) = ((term25 A B f s) = True).
Proof. exact (@lem7 (term25 A B f s)). Qed.
Lemma lem4945077 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : (term25 A B f s) = True.
Proof. exact (EQ_MP (@lem4945076 A B f s) (@lem4945075 A B f s h1)). Qed.
Lemma lem4945083 {A : Type'} (s : A -> Prop) : term26 A s.
Proof. exact (@lem3217397 A s). Qed.
Lemma lem4945084 {A : Type'} (s : A -> Prop) : (term26 A s) = (@SUBSET A s s).
Proof. exact (eq_refl (term26 A s)). Qed.
Lemma lem4945085 {A : Type'} (s : A -> Prop) : @SUBSET A s s.
Proof. exact (EQ_MP (@lem4945084 A s) (@lem4945083 A s)). Qed.
Lemma lem4945086 {A : Type'} (s : A -> Prop) : (@SUBSET A s s) = ((@SUBSET A s s) = True).
Proof. exact (@lem7 (@SUBSET A s s)). Qed.
Lemma lem4945088 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : term18 A B t f s.
Proof. exact (proj2 (@lem4945067 A B f s t h1)). Qed.
Lemma lem4945091 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : @FINITE A s.
Proof. exact (proj1 (@lem4945067 A B f s t h1)). Qed.
Lemma lem4945092 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem4945097 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term27 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4945098 (p : Prop) (q : Prop) (p' : Prop) : term28 p q p'.
Proof. exact (fun q' : Prop => @lem4945097 p q p' q'). Qed.
Lemma lem4945099 (p : Prop) (q : Prop) : term29 p q.
Proof. exact (fun p' : Prop => @lem4945098 p q p'). Qed.
Lemma lem4945100 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : term30 A B t s f.
Proof. exact (@lem4945099 (term13 A B t s f) (term31 A B s f)). Qed.
Lemma lem4945101 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (p' : Prop) : term32 A B t s f p'.
Proof. exact (@lem4945100 A B t s f p'). Qed.
Lemma lem4945102 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (p' : Prop) : (term32 A B t s f p') = (term33 A B t s f p').
Proof. exact (eq_refl (term32 A B t s f p')). Qed.
Lemma lem4945103 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (p' : Prop) : term33 A B t s f p'.
Proof. exact (EQ_MP (@lem4945102 A B t s f p') (@lem4945101 A B t s f p')). Qed.
Lemma lem4945104 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : term34 A B t s f p' q'.
Proof. exact (@lem4945103 A B t s f p' q'). Qed.
Lemma lem4945105 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : (term34 A B t s f p' q') = (term35 A B t s f p' q').
Proof. exact (eq_refl (term34 A B t s f p' q')). Qed.
Lemma lem4945106 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : term35 A B t s f p' q'.
Proof. exact (EQ_MP (@lem4945105 A B t s f p' q') (@lem4945104 A B t s f p' q')). Qed.
Lemma lem4945110 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term27 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4945111 (p : Prop) (q : Prop) (p' : Prop) : term28 p q p'.
Proof. exact (fun q' : Prop => @lem4945110 p q p' q'). Qed.
Lemma lem4945112 (p : Prop) (q : Prop) : term29 p q.
Proof. exact (fun p' : Prop => @lem4945111 p q p'). Qed.
Lemma lem4945113 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : term36 A B t s f.
Proof. exact (@lem4945112 (term37 A B f s t) ((term38 A B t s f) = (term31 A B s f))). Qed.
Lemma lem4945114 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (p' : Prop) : term39 A B t s f p'.
Proof. exact (@lem4945113 A B t s f p'). Qed.
Lemma lem4945115 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (p' : Prop) : (term39 A B t s f p') = (term40 A B t s f p').
Proof. exact (eq_refl (term39 A B t s f p')). Qed.
Lemma lem4945116 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (p' : Prop) : term40 A B t s f p'.
Proof. exact (EQ_MP (@lem4945115 A B t s f p') (@lem4945114 A B t s f p')). Qed.
Lemma lem4945117 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : term41 A B t s f p' q'.
Proof. exact (@lem4945116 A B t s f p' q'). Qed.
Lemma lem4945118 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : (term41 A B t s f p' q') = (term42 A B t s f p' q').
Proof. exact (eq_refl (term41 A B t s f p' q')). Qed.
Lemma lem4945119 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : term42 A B t s f p' q'.
Proof. exact (EQ_MP (@lem4945118 A B t s f p' q') (@lem4945117 A B t s f p' q')). Qed.
Lemma lem4945123 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem4945092 A s) (@lem4945091 A B f s t h1)). Qed.
Lemma lem4945124 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4945125 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : (term19 A s) = (and True).
Proof. exact (MK_COMB (@lem4945124) (@lem4945123 A B f s t h1)). Qed.
Lemma lem4945129 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : t = (@IMAGE A B f s).
Proof. exact (proj2 (@lem4945088 A B f s t h1)). Qed.
Lemma lem4945130 {B : Type'} : (@FINITE B) = (@FINITE B).
Proof. exact (eq_refl (@FINITE B)). Qed.
Lemma lem4945131 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : (@FINITE B t) = (term25 A B f s).
Proof. exact (MK_COMB (@lem4945130 B) (@lem4945129 A B f s t h1)). Qed.
Lemma lem4945133 {A B : Type'} (f : A -> B) (s : A -> Prop) : term43 A B f s.
Proof. exact (fun h0 : @FINITE A s => @lem4945077 A B f s h0). Qed.
Lemma lem4945134 {A B : Type'} (f : A -> B) (s : A -> Prop) : term43 A B f s.
Proof. exact (@lem4945133 A B f s). Qed.
Lemma lem4945136 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem4945092 A s) (@lem4945091 A B f s t h1)). Qed.
Lemma lem4945137 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : True = (@FINITE A s).
Proof. exact (SYM (@lem4945136 A B f s t h1)). Qed.
Lemma lem4945138 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : @FINITE A s.
Proof. exact (EQ_MP (@lem4945137 A B f s t h1) (@lem0)). Qed.
Lemma lem4945139 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : (term25 A B f s) = True.
Proof. exact (@lem4945134 A B f s (@lem4945138 A B f s t h1)). Qed.
Lemma lem4945140 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : (@FINITE B t) = True.
Proof. exact (TRANS (@lem4945131 A B f s t h1) (@lem4945139 A B f s t h1)). Qed.
Lemma lem4945141 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4945142 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : (term19 B t) = (and True).
Proof. exact (MK_COMB (@lem4945141) (@lem4945140 A B f s t h1)). Qed.
Lemma lem4945148 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : (@CARD B t) = (@CARD A s).
Proof. exact (proj1 (@lem4945088 A B f s t h1)). Qed.
Lemma lem4945149 {A : Type'} (s : A -> Prop) : (term44 A s) = (term44 A s).
Proof. exact (eq_refl (term44 A s)). Qed.
Lemma lem4945150 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : ((@CARD A s) = (@CARD B t)) = ((@CARD A s) = (@CARD A s)).
Proof. exact (MK_COMB (@lem4945149 A s) (@lem4945148 A B f s t h1)). Qed.
Lemma lem4945152 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4945153 (x : nat) : (x = x) = True.
Proof. exact (@lem4945152 nat x). Qed.
Lemma lem4945154 {A : Type'} (s : A -> Prop) : ((@CARD A s) = (@CARD A s)) = True.
Proof. exact (@lem4945153 (@CARD A s)). Qed.
Lemma lem4945155 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : ((@CARD A s) = (@CARD B t)) = True.
Proof. exact (TRANS (@lem4945150 A B f s t h1) (@lem4945154 A s)). Qed.
Lemma lem4945156 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4945157 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : (term15 A B s t) = (and True).
Proof. exact (MK_COMB (@lem4945156) (@lem4945155 A B f s t h1)). Qed.
Lemma lem4945161 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : t = (@IMAGE A B f s).
Proof. exact (proj2 (@lem4945088 A B f s t h1)). Qed.
Lemma lem4945162 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term45 A B f s) = (term45 A B f s).
Proof. exact (eq_refl (term45 A B f s)). Qed.
Lemma lem4945163 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : (term46 A B f s t) = (term47 A B f s).
Proof. exact (MK_COMB (@lem4945162 A B f s) (@lem4945161 A B f s t h1)). Qed.
Lemma lem4945165 {A : Type'} (s : A -> Prop) : (@SUBSET A s s) = True.
Proof. exact (EQ_MP (@lem4945086 A s) (@lem4945085 A s)). Qed.
Lemma lem4945166 {B : Type'} (s : B -> Prop) : (@SUBSET B s s) = True.
Proof. exact (@lem4945165 B s). Qed.
Lemma lem4945167 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term47 A B f s) = True.
Proof. exact (@lem4945166 B (@IMAGE A B f s)). Qed.
Lemma lem4945168 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : (term46 A B f s t) = True.
Proof. exact (TRANS (@lem4945163 A B f s t h1) (@lem4945167 A B f s)). Qed.
Lemma lem4945169 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : (term48 A B f s t) = (True /\ True).
Proof. exact (MK_COMB (@lem4945157 A B f s t h1) (@lem4945168 A B f s t h1)). Qed.
Lemma lem4945171 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4945172 : (True /\ True) = True.
Proof. exact (@lem4945171 True). Qed.
Lemma lem4945173 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : (term48 A B f s t) = True.
Proof. exact (TRANS (@lem4945169 A B f s t h1) (@lem4945172)). Qed.
Lemma lem4945174 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : (term49 A B f s t) = (True /\ True).
Proof. exact (MK_COMB (@lem4945142 A B f s t h1) (@lem4945173 A B f s t h1)). Qed.
Lemma lem4945176 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4945177 : (True /\ True) = True.
Proof. exact (@lem4945176 True). Qed.
Lemma lem4945178 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : (term49 A B f s t) = True.
Proof. exact (TRANS (@lem4945174 A B f s t h1) (@lem4945177)). Qed.
Lemma lem4945179 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : (term37 A B f s t) = (True /\ True).
Proof. exact (MK_COMB (@lem4945125 A B f s t h1) (@lem4945178 A B f s t h1)). Qed.
Lemma lem4945181 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4945182 : (True /\ True) = True.
Proof. exact (@lem4945181 True). Qed.
Lemma lem4945183 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : (term37 A B f s t) = True.
Proof. exact (TRANS (@lem4945179 A B f s t h1) (@lem4945182)). Qed.
Lemma lem4945184 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (q' : Prop) : term50 A B t s f q'.
Proof. exact (@lem4945119 A B t s f True q'). Qed.
Lemma lem4945185 {A B : Type'} (q' : Prop) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : term51 A B t s f q'.
Proof. exact (@lem4945184 A B t s f q' (@lem4945183 A B f s t h1)). Qed.
Lemma lem4945200 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term27 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4945201 (p : Prop) (q : Prop) (p' : Prop) : term28 p q p'.
Proof. exact (fun q' : Prop => @lem4945200 p q p' q'). Qed.
Lemma lem4945202 (p : Prop) (q : Prop) : term29 p q.
Proof. exact (fun p' : Prop => @lem4945201 p q p'). Qed.
Lemma lem4945203 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : term52 A B t s f y.
Proof. exact (@lem4945202 (@IN B y t) (term53 A B s f y)). Qed.
Lemma lem4945204 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) (p' : Prop) : term54 A B t s f y p'.
Proof. exact (@lem4945203 A B t s f y p'). Qed.
Lemma lem4945205 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) (p' : Prop) : (term54 A B t s f y p') = (term55 A B t s f y p').
Proof. exact (eq_refl (term54 A B t s f y p')). Qed.
Lemma lem4945206 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) (p' : Prop) : term55 A B t s f y p'.
Proof. exact (EQ_MP (@lem4945205 A B t s f y p') (@lem4945204 A B t s f y p')). Qed.
Lemma lem4945207 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) (p' : Prop) (q' : Prop) : term56 A B t s f y p' q'.
Proof. exact (@lem4945206 A B t s f y p' q'). Qed.
Lemma lem4945208 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) (p' : Prop) (q' : Prop) : (term56 A B t s f y p' q') = (term57 A B t s f y p' q').
Proof. exact (eq_refl (term56 A B t s f y p' q')). Qed.
Lemma lem4945209 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) (p' : Prop) (q' : Prop) : term57 A B t s f y p' q'.
Proof. exact (EQ_MP (@lem4945208 A B t s f y p' q') (@lem4945207 A B t s f y p' q')). Qed.
Lemma lem4945211 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : t = (@IMAGE A B f s).
Proof. exact (proj2 (@lem4945088 A B f s t h1)). Qed.
Lemma lem4945212 {B : Type'} (y : B) : (@IN B y) = (@IN B y).
Proof. exact (eq_refl (@IN B y)). Qed.
Lemma lem4945213 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : (@IN B y t) = (term58 A B y f s).
Proof. exact (MK_COMB (@lem4945212 B y) (@lem4945211 A B f s t h1)). Qed.
Lemma lem4945214 {A B : Type'} (t : B -> Prop) (y : B) (f : A -> B) (s : A -> Prop) (q' : Prop) : term59 A B t y f s q'.
Proof. exact (@lem4945209 A B t s f y (term58 A B y f s) q'). Qed.
Lemma lem4945215 {A B : Type'} (y : B) (q' : Prop) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : term60 A B t y f s q'.
Proof. exact (@lem4945214 A B t y f s q' (@lem4945213 A B y f s t h1)). Qed.
Lemma lem4945227 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term53 A B s f y) = (term53 A B s f y).
Proof. exact (eq_refl (term53 A B s f y)). Qed.
Lemma lem4945228 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : term61 A B s f y.
Proof. exact (fun h0 : term58 A B y f s => @lem4945227 A B s f y). Qed.
Lemma lem4945229 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : term62 A B t s f y.
Proof. exact (@lem4945215 A B y (term53 A B s f y) f s t h1). Qed.
Lemma lem4945230 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : (term63 A B t s f y) = (term64 A B s f y).
Proof. exact (@lem4945229 A B y f s t h1 (@lem4945228 A B s f y)). Qed.
Lemma lem4945270 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : (term65 A B t s f) = (term66 A B s f).
Proof. exact (fun_ext (fun y : B => @lem4945230 A B y f s t h1)). Qed.
Lemma lem4945310 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4945311 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : (term38 A B t s f) = (term67 A B s f).
Proof. exact (MK_COMB (@lem4945310 B) (@lem4945270 A B f s t h1)). Qed.
Lemma lem4945355 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4945356 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : (term68 A B t s f) = (term69 A B s f).
Proof. exact (MK_COMB (@lem4945355) (@lem4945311 A B f s t h1)). Qed.
Lemma lem4945453 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term31 A B s f) = (term31 A B s f).
Proof. exact (eq_refl (term31 A B s f)). Qed.
Lemma lem4945454 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : ((term38 A B t s f) = (term31 A B s f)) = ((term67 A B s f) = (term31 A B s f)).
Proof. exact (MK_COMB (@lem4945356 A B f s t h1) (@lem4945453 A B s f)). Qed.
Lemma lem4945553 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : term70 A B t s f.
Proof. exact (fun h0 : True => @lem4945454 A B f s t h1). Qed.
Lemma lem4945554 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : term71 A B t s f.
Proof. exact (@lem4945185 A B ((term67 A B s f) = (term31 A B s f)) f s t h1). Qed.
Lemma lem4945555 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : (term13 A B t s f) = (term72 A B s f).
Proof. exact (@lem4945554 A B f s t h1 (@lem4945553 A B f s t h1)). Qed.
Lemma lem4945557 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem4945558 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term72 A B s f) = ((term67 A B s f) = (term31 A B s f)).
Proof. exact (@lem4945557 ((term67 A B s f) = (term31 A B s f))). Qed.
Lemma lem4945657 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : (term13 A B t s f) = ((term67 A B s f) = (term31 A B s f)).
Proof. exact (TRANS (@lem4945555 A B f s t h1) (@lem4945558 A B s f)). Qed.
Lemma lem4945658 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (q' : Prop) : term73 A B t s f q'.
Proof. exact (@lem4945106 A B t s f ((term67 A B s f) = (term31 A B s f)) q'). Qed.
Lemma lem4945659 {A B : Type'} (q' : Prop) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : term74 A B t s f q'.
Proof. exact (@lem4945658 A B t s f q' (@lem4945657 A B f s t h1)). Qed.
Lemma lem4945714 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term31 A B s f) = (term31 A B s f).
Proof. exact (eq_refl (term31 A B s f)). Qed.
Lemma lem4945715 {A B : Type'} (s : A -> Prop) (f : A -> B) : term75 A B s f.
Proof. exact (fun h0 : (term67 A B s f) = (term31 A B s f) => @lem4945714 A B s f). Qed.
Lemma lem4945716 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : term76 A B t s f.
Proof. exact (@lem4945659 A B (term31 A B s f) f s t h1). Qed.
Lemma lem4945717 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : (term77 A B t s f) = (term78 A B s f).
Proof. exact (@lem4945716 A B f s t h1 (@lem4945715 A B s f)). Qed.
Lemma lem4946043 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : (term78 A B s f) = (term77 A B t s f).
Proof. exact (SYM (@lem4945717 A B f s t h1)). Qed.
Lemma lem4946045 (p : Prop) : p = (term79 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4946046 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term78 A B s f) = (term80 A B s f).
Proof. exact (@lem4946045 (term78 A B s f)). Qed.
Lemma lem4946047 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term80 A B s f) = (term78 A B s f).
Proof. exact (SYM (@lem4946046 A B s f)). Qed.
Lemma lem4946048 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term81 A B s f) : term81 A B s f.
Proof. exact (h1). Qed.
Lemma lem4946049 {B : Type'} : term82 B.
Proof. exact (@lem3181245 B). Qed.
Lemma lem4946051 {A : Type'} : term82 A.
Proof. exact (@lem3181245 A). Qed.
Lemma lem4946052 {A B : Type'} : term83 A B.
Proof. exact (@lem3206070 A B). Qed.
Lemma lem4946053 {A : Type'} : term84 A.
Proof. exact (@lem3206070 A A). Qed.
Lemma lem4946055 {A : Type'} : term85 A.
Proof. exact (@lem3206070 A nat). Qed.
Lemma lem4946056 {A B : Type'} : term86 A B.
Proof. exact (@lem3206070 A (B -> Prop)). Qed.
Lemma lem4946059 {A : Type'} : term87 A.
Proof. exact (@lem3206070 A (A -> Prop)). Qed.
Lemma lem4946060 {B : Type'} : term84 B.
Proof. exact (@lem3206070 B B). Qed.
Lemma lem4946064 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term88 A B t s f) : term88 A B t s f.
Proof. exact (h1). Qed.
Lemma lem4946065 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : term89 A B t s f.
Proof. exact (fun h0 : term88 A B t s f => @lem4946064 A B t s f h0). Qed.
Lemma lem4946066 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term89 A B t s f) : term89 A B t s f.
Proof. exact (h1). Qed.
Lemma lem4946067 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term88 A B t s f) : term88 A B t s f.
Proof. exact (h1). Qed.
Lemma lem4946068 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term88 A B t s f) (h2 : term89 A B t s f) : term88 A B t s f.
Proof. exact (@lem4946066 A B t s f h2 (@lem4946067 A B t s f h1)). Qed.
Lemma lem4946069 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term88 A B t s f) : term90 A B t s f.
Proof. exact (fun h0 : term89 A B t s f => @lem4946068 A B t s f h1 h0). Qed.
Lemma lem4946070 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term89 A B t s f) : term89 A B t s f.
Proof. exact (h1). Qed.
Lemma lem4946071 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term88 A B t s f) (h2 : term89 A B t s f) : term88 A B t s f.
Proof. exact (@lem4946069 A B t s f h1 (@lem4946070 A B t s f h2)). Qed.
Lemma lem4946072 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term89 A B t s f) : term89 A B t s f.
Proof. exact (fun h0 : term88 A B t s f => @lem4946071 A B t s f h0 h1). Qed.
Lemma lem4946073 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : term91 A B t s f.
Proof. exact (fun h0 : term89 A B t s f => @lem4946072 A B t s f h0). Qed.
Lemma lem4946076 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : term89 A B t s f.
Proof. exact (@lem4946073 A B t s f (@lem4946065 A B t s f)). Qed.
Lemma lem4946077 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : term89 A B t s f.
Proof. exact (@lem4946076 A B t s f). Qed.
Lemma lem4946583 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4946584 {B : Type'} : (term92 B) = (term93 B).
Proof. exact (@lem4946583 (term82 B)). Qed.
Lemma lem4946597 {A : Type'} : (term94 A) = (term94 A).
Proof. exact (eq_refl (term94 A)). Qed.
Lemma lem4946598 {A B : Type'} : (term95 A B) = (term96 A B).
Proof. exact (MK_COMB (@lem4946597 A) (@lem4946584 B)). Qed.
Lemma lem4946601 {A : Type'} : (term97 A) = (term97 A).
Proof. exact (eq_refl (term97 A)). Qed.
Lemma lem4946602 {A B : Type'} : (term98 A B) = (term99 A B).
Proof. exact (MK_COMB (@lem4946601 A) (@lem4946598 A B)). Qed.
Lemma lem4946605 {A B : Type'} : (term100 A B) = (term100 A B).
Proof. exact (eq_refl (term100 A B)). Qed.
Lemma lem4946606 {A B : Type'} : (term101 A B) = (term102 A B).
Proof. exact (MK_COMB (@lem4946605 A B) (@lem4946602 A B)). Qed.
Lemma lem4946609 {A : Type'} : (term103 A) = (term103 A).
Proof. exact (eq_refl (term103 A)). Qed.
Lemma lem4946610 {A B : Type'} : (term104 A B) = (term105 A B).
Proof. exact (MK_COMB (@lem4946609 A) (@lem4946606 A B)). Qed.
Lemma lem4946613 {B : Type'} : (term106 B) = (term106 B).
Proof. exact (eq_refl (term106 B)). Qed.
Lemma lem4946614 {A B : Type'} : (term107 A B) = (term108 A B).
Proof. exact (MK_COMB (@lem4946613 B) (@lem4946610 A B)). Qed.
Lemma lem4946617 {A B : Type'} : (term109 A B) = (term109 A B).
Proof. exact (eq_refl (term109 A B)). Qed.
Lemma lem4946618 {A B : Type'} : (term110 A B) = (term111 A B).
Proof. exact (MK_COMB (@lem4946617 A B) (@lem4946614 A B)). Qed.
Lemma lem4946621 {A : Type'} : (term106 A) = (term106 A).
Proof. exact (eq_refl (term106 A)). Qed.
Lemma lem4946622 {A B : Type'} : (term112 A B) = (term113 A B).
Proof. exact (MK_COMB (@lem4946621 A) (@lem4946618 A B)). Qed.
Lemma lem4946625 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term114 A B s f) = (term114 A B s f).
Proof. exact (eq_refl (term114 A B s f)). Qed.
Lemma lem4946626 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term115 A B s f) = (term116 A B s f).
Proof. exact (MK_COMB (@lem4946625 A B s f) (@lem4946622 A B)). Qed.
Lemma lem4946629 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term117 A B t f s) = (term117 A B t f s).
Proof. exact (eq_refl (term117 A B t f s)). Qed.
Lemma lem4946630 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term88 A B t s f) = (term118 A B t s f).
Proof. exact (MK_COMB (@lem4946629 A B t f s) (@lem4946626 A B s f)). Qed.
Lemma lem4946633 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term119 A B s f) = (term120 A B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4946630 A B t s f)). Qed.
Lemma lem4946634 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4946635 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term121 A B s f) = (term122 A B s f).
Proof. exact (MK_COMB (@lem4946634 B) (@lem4946633 A B s f)). Qed.
Lemma lem4946640 {A B : Type'} (f : A -> B) : (term123 A B f) = (term124 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4946635 A B s f)). Qed.
Lemma lem4946641 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4946642 {A B : Type'} (f : A -> B) : (term125 A B f) = (term126 A B f).
Proof. exact (MK_COMB (@lem4946641 A) (@lem4946640 A B f)). Qed.
Lemma lem4946647 {A B : Type'} : (term127 A B) = (term128 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem4946642 A B f)). Qed.
Lemma lem4946648 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4946657 {A B : Type'} : (term129 A B) = (term130 A B).
Proof. exact (MK_COMB (@lem4946648 A B) (@lem4946647 A B)). Qed.
Lemma lem4946662 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : ((@IN B x s) = (@IN B x t)) = ((@IN B x s) = (@IN B x t)).
Proof. exact (eq_refl ((@IN B x s) = (@IN B x t))). Qed.
Lemma lem4946663 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term131 B s t) = (term131 B s t).
Proof. exact (fun_ext (fun x : B => @lem4946662 B s x t)). Qed.
Lemma lem4946664 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4946665 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term132 B s t) = (term132 B s t).
Proof. exact (MK_COMB (@lem4946664 B) (@lem4946663 B s t)). Qed.
Lemma lem4946668 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term133 B s t) = (term133 B s t).
Proof. exact (eq_refl (term133 B s t)). Qed.
Lemma lem4946669 {B : Type'} (s : B -> Prop) (t : B -> Prop) : ((s = t) = (term132 B s t)) = ((s = t) = (term132 B s t)).
Proof. exact (MK_COMB (@lem4946668 B s t) (@lem4946665 B s t)). Qed.
Lemma lem4946670 {B : Type'} (s : B -> Prop) : (term134 B s) = (term134 B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4946669 B s t)). Qed.
Lemma lem4946671 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4946672 {B : Type'} (s : B -> Prop) : (term135 B s) = (term135 B s).
Proof. exact (MK_COMB (@lem4946671 B) (@lem4946670 B s)). Qed.
Lemma lem4946673 {B : Type'} : (term136 B) = (term136 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem4946672 B s)). Qed.
Lemma lem4946674 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4946675 {B : Type'} : (term82 B) = (term82 B).
Proof. exact (MK_COMB (@lem4946674 B) (@lem4946673 B)). Qed.
Lemma lem4946676 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4946677 {B : Type'} : (term93 B) = (term93 B).
Proof. exact (MK_COMB (@lem4946676) (@lem4946675 B)). Qed.
Lemma lem4946682 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : ((@IN A x s) = (@IN A x t)) = ((@IN A x s) = (@IN A x t)).
Proof. exact (eq_refl ((@IN A x s) = (@IN A x t))). Qed.
Lemma lem4946683 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term131 A s t) = (term131 A s t).
Proof. exact (fun_ext (fun x : A => @lem4946682 A s x t)). Qed.
Lemma lem4946684 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4946685 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term132 A s t) = (term132 A s t).
Proof. exact (MK_COMB (@lem4946684 A) (@lem4946683 A s t)). Qed.
Lemma lem4946688 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term133 A s t) = (term133 A s t).
Proof. exact (eq_refl (term133 A s t)). Qed.
Lemma lem4946689 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((s = t) = (term132 A s t)) = ((s = t) = (term132 A s t)).
Proof. exact (MK_COMB (@lem4946688 A s t) (@lem4946685 A s t)). Qed.
Lemma lem4946690 {A : Type'} (s : A -> Prop) : (term134 A s) = (term134 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4946689 A s t)). Qed.
Lemma lem4946691 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4946692 {A : Type'} (s : A -> Prop) : (term135 A s) = (term135 A s).
Proof. exact (MK_COMB (@lem4946691 A) (@lem4946690 A s)). Qed.
Lemma lem4946693 {A : Type'} : (term136 A) = (term136 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4946692 A s)). Qed.
Lemma lem4946694 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4946695 {A : Type'} : (term82 A) = (term82 A).
Proof. exact (MK_COMB (@lem4946694 A) (@lem4946693 A)). Qed.
Lemma lem4946696 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4946697 {A : Type'} : (term94 A) = (term94 A).
Proof. exact (MK_COMB (@lem4946696) (@lem4946695 A)). Qed.
Lemma lem4946698 {A B : Type'} : (term96 A B) = (term96 A B).
Proof. exact (MK_COMB (@lem4946697 A) (@lem4946677 B)). Qed.
Lemma lem4946703 {A : Type'} (y : nat) (f : A -> nat) (x : A) (s : A -> Prop) : (term137 A y f x s) = (term137 A y f x s).
Proof. exact (eq_refl (term137 A y f x s)). Qed.
Lemma lem4946704 {A : Type'} (y : nat) (f : A -> nat) (s : A -> Prop) : (term138 A y f s) = (term138 A y f s).
Proof. exact (fun_ext (fun x : A => @lem4946703 A y f x s)). Qed.
Lemma lem4946705 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4946706 {A : Type'} (y : nat) (f : A -> nat) (s : A -> Prop) : (term139 A y f s) = (term139 A y f s).
Proof. exact (MK_COMB (@lem4946705 A) (@lem4946704 A y f s)). Qed.
Lemma lem4946709 {A : Type'} (y : nat) (f : A -> nat) (s : A -> Prop) : (term140 A y f s) = (term140 A y f s).
Proof. exact (eq_refl (term140 A y f s)). Qed.
Lemma lem4946710 {A : Type'} (y : nat) (f : A -> nat) (s : A -> Prop) : ((term141 A y f s) = (term139 A y f s)) = ((term141 A y f s) = (term139 A y f s)).
Proof. exact (MK_COMB (@lem4946709 A y f s) (@lem4946706 A y f s)). Qed.
Lemma lem4946711 {A : Type'} (y : nat) (s : A -> Prop) : (term142 A y s) = (term142 A y s).
Proof. exact (fun_ext (fun f : A -> nat => @lem4946710 A y f s)). Qed.
Lemma lem4946712 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem4946713 {A : Type'} (y : nat) (s : A -> Prop) : (term143 A y s) = (term143 A y s).
Proof. exact (MK_COMB (@lem4946712 A) (@lem4946711 A y s)). Qed.
Lemma lem4946714 {A : Type'} (y : nat) : (term144 A y) = (term144 A y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4946713 A y s)). Qed.
Lemma lem4946715 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4946716 {A : Type'} (y : nat) : (term145 A y) = (term145 A y).
Proof. exact (MK_COMB (@lem4946715 A) (@lem4946714 A y)). Qed.
Lemma lem4946717 {A : Type'} : (term146 A) = (term146 A).
Proof. exact (fun_ext (fun y : nat => @lem4946716 A y)). Qed.
Lemma lem4946718 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4946719 {A : Type'} : (term85 A) = (term85 A).
Proof. exact (MK_COMB (@lem4946718) (@lem4946717 A)). Qed.
Lemma lem4946720 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4946721 {A : Type'} : (term97 A) = (term97 A).
Proof. exact (MK_COMB (@lem4946720) (@lem4946719 A)). Qed.
Lemma lem4946722 {A B : Type'} : (term99 A B) = (term99 A B).
Proof. exact (MK_COMB (@lem4946721 A) (@lem4946698 A B)). Qed.
Lemma lem4946727 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (x : A) (s : A -> Prop) : (term147 A B y f x s) = (term147 A B y f x s).
Proof. exact (eq_refl (term147 A B y f x s)). Qed.
Lemma lem4946728 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (s : A -> Prop) : (term148 A B y f s) = (term148 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem4946727 A B y f x s)). Qed.
Lemma lem4946729 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4946730 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (s : A -> Prop) : (term149 A B y f s) = (term149 A B y f s).
Proof. exact (MK_COMB (@lem4946729 A) (@lem4946728 A B y f s)). Qed.
Lemma lem4946733 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (s : A -> Prop) : (term150 A B y f s) = (term150 A B y f s).
Proof. exact (eq_refl (term150 A B y f s)). Qed.
Lemma lem4946734 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (s : A -> Prop) : ((term151 A B y f s) = (term149 A B y f s)) = ((term151 A B y f s) = (term149 A B y f s)).
Proof. exact (MK_COMB (@lem4946733 A B y f s) (@lem4946730 A B y f s)). Qed.
Lemma lem4946735 {A B : Type'} (y : B -> Prop) (s : A -> Prop) : (term152 A B y s) = (term152 A B y s).
Proof. exact (fun_ext (fun f : type1413 A B => @lem4946734 A B y f s)). Qed.
Lemma lem4946736 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem4946737 {A B : Type'} (y : B -> Prop) (s : A -> Prop) : (term153 A B y s) = (term153 A B y s).
Proof. exact (MK_COMB (@lem4946736 A B) (@lem4946735 A B y s)). Qed.
Lemma lem4946738 {A B : Type'} (y : B -> Prop) : (term154 A B y) = (term154 A B y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4946737 A B y s)). Qed.
Lemma lem4946739 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4946740 {A B : Type'} (y : B -> Prop) : (term155 A B y) = (term155 A B y).
Proof. exact (MK_COMB (@lem4946739 A) (@lem4946738 A B y)). Qed.
Lemma lem4946741 {A B : Type'} : (term156 A B) = (term156 A B).
Proof. exact (fun_ext (fun y : B -> Prop => @lem4946740 A B y)). Qed.
Lemma lem4946742 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4946743 {A B : Type'} : (term86 A B) = (term86 A B).
Proof. exact (MK_COMB (@lem4946742 B) (@lem4946741 A B)). Qed.
Lemma lem4946744 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4946745 {A B : Type'} : (term100 A B) = (term100 A B).
Proof. exact (MK_COMB (@lem4946744) (@lem4946743 A B)). Qed.
Lemma lem4946746 {A B : Type'} : (term102 A B) = (term102 A B).
Proof. exact (MK_COMB (@lem4946745 A B) (@lem4946722 A B)). Qed.
Lemma lem4946751 {A : Type'} (y : A -> Prop) (f : type1402 A) (x : A) (s : A -> Prop) : (term157 A y f x s) = (term157 A y f x s).
Proof. exact (eq_refl (term157 A y f x s)). Qed.
Lemma lem4946752 {A : Type'} (y : A -> Prop) (f : type1402 A) (s : A -> Prop) : (term158 A y f s) = (term158 A y f s).
Proof. exact (fun_ext (fun x : A => @lem4946751 A y f x s)). Qed.
Lemma lem4946753 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4946754 {A : Type'} (y : A -> Prop) (f : type1402 A) (s : A -> Prop) : (term159 A y f s) = (term159 A y f s).
Proof. exact (MK_COMB (@lem4946753 A) (@lem4946752 A y f s)). Qed.
Lemma lem4946757 {A : Type'} (y : A -> Prop) (f : type1402 A) (s : A -> Prop) : (term160 A y f s) = (term160 A y f s).
Proof. exact (eq_refl (term160 A y f s)). Qed.
Lemma lem4946758 {A : Type'} (y : A -> Prop) (f : type1402 A) (s : A -> Prop) : ((term161 A y f s) = (term159 A y f s)) = ((term161 A y f s) = (term159 A y f s)).
Proof. exact (MK_COMB (@lem4946757 A y f s) (@lem4946754 A y f s)). Qed.
Lemma lem4946759 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term162 A y s) = (term162 A y s).
Proof. exact (fun_ext (fun f : type1402 A => @lem4946758 A y f s)). Qed.
Lemma lem4946760 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem4946761 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term163 A y s) = (term163 A y s).
Proof. exact (MK_COMB (@lem4946760 A) (@lem4946759 A y s)). Qed.
Lemma lem4946762 {A : Type'} (y : A -> Prop) : (term164 A y) = (term164 A y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4946761 A y s)). Qed.
Lemma lem4946763 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4946764 {A : Type'} (y : A -> Prop) : (term165 A y) = (term165 A y).
Proof. exact (MK_COMB (@lem4946763 A) (@lem4946762 A y)). Qed.
Lemma lem4946765 {A : Type'} : (term166 A) = (term166 A).
Proof. exact (fun_ext (fun y : A -> Prop => @lem4946764 A y)). Qed.
Lemma lem4946766 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4946767 {A : Type'} : (term87 A) = (term87 A).
Proof. exact (MK_COMB (@lem4946766 A) (@lem4946765 A)). Qed.
Lemma lem4946768 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4946769 {A : Type'} : (term103 A) = (term103 A).
Proof. exact (MK_COMB (@lem4946768) (@lem4946767 A)). Qed.
Lemma lem4946770 {A B : Type'} : (term105 A B) = (term105 A B).
Proof. exact (MK_COMB (@lem4946769 A) (@lem4946746 A B)). Qed.
Lemma lem4946775 {B : Type'} (y : B) (f : B -> B) (x : B) (s : B -> Prop) : (term167 B y f x s) = (term167 B y f x s).
Proof. exact (eq_refl (term167 B y f x s)). Qed.
Lemma lem4946776 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term168 B y f s) = (term168 B y f s).
Proof. exact (fun_ext (fun x : B => @lem4946775 B y f x s)). Qed.
Lemma lem4946777 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4946778 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term169 B y f s) = (term169 B y f s).
Proof. exact (MK_COMB (@lem4946777 B) (@lem4946776 B y f s)). Qed.
Lemma lem4946781 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term170 B y f s) = (term170 B y f s).
Proof. exact (eq_refl (term170 B y f s)). Qed.
Lemma lem4946782 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : ((term171 B y f s) = (term169 B y f s)) = ((term171 B y f s) = (term169 B y f s)).
Proof. exact (MK_COMB (@lem4946781 B y f s) (@lem4946778 B y f s)). Qed.
Lemma lem4946783 {B : Type'} (y : B) (s : B -> Prop) : (term172 B y s) = (term172 B y s).
Proof. exact (fun_ext (fun f : B -> B => @lem4946782 B y f s)). Qed.
Lemma lem4946784 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem4946785 {B : Type'} (y : B) (s : B -> Prop) : (term173 B y s) = (term173 B y s).
Proof. exact (MK_COMB (@lem4946784 B) (@lem4946783 B y s)). Qed.
Lemma lem4946786 {B : Type'} (y : B) : (term174 B y) = (term174 B y).
Proof. exact (fun_ext (fun s : B -> Prop => @lem4946785 B y s)). Qed.
Lemma lem4946787 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4946788 {B : Type'} (y : B) : (term175 B y) = (term175 B y).
Proof. exact (MK_COMB (@lem4946787 B) (@lem4946786 B y)). Qed.
Lemma lem4946789 {B : Type'} : (term176 B) = (term176 B).
Proof. exact (fun_ext (fun y : B => @lem4946788 B y)). Qed.
Lemma lem4946790 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4946791 {B : Type'} : (term84 B) = (term84 B).
Proof. exact (MK_COMB (@lem4946790 B) (@lem4946789 B)). Qed.
Lemma lem4946792 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4946793 {B : Type'} : (term106 B) = (term106 B).
Proof. exact (MK_COMB (@lem4946792) (@lem4946791 B)). Qed.
Lemma lem4946794 {A B : Type'} : (term108 A B) = (term108 A B).
Proof. exact (MK_COMB (@lem4946793 B) (@lem4946770 A B)). Qed.
Lemma lem4946799 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term177 A B y f x s) = (term177 A B y f x s).
Proof. exact (eq_refl (term177 A B y f x s)). Qed.
Lemma lem4946800 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term178 A B y f s) = (term178 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem4946799 A B y f x s)). Qed.
Lemma lem4946801 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4946802 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term179 A B y f s) = (term179 A B y f s).
Proof. exact (MK_COMB (@lem4946801 A) (@lem4946800 A B y f s)). Qed.
Lemma lem4946805 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term180 A B y f s) = (term180 A B y f s).
Proof. exact (eq_refl (term180 A B y f s)). Qed.
Lemma lem4946806 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : ((term58 A B y f s) = (term179 A B y f s)) = ((term58 A B y f s) = (term179 A B y f s)).
Proof. exact (MK_COMB (@lem4946805 A B y f s) (@lem4946802 A B y f s)). Qed.
Lemma lem4946807 {A B : Type'} (y : B) (s : A -> Prop) : (term181 A B y s) = (term181 A B y s).
Proof. exact (fun_ext (fun f : A -> B => @lem4946806 A B y f s)). Qed.
Lemma lem4946808 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4946809 {A B : Type'} (y : B) (s : A -> Prop) : (term182 A B y s) = (term182 A B y s).
Proof. exact (MK_COMB (@lem4946808 A B) (@lem4946807 A B y s)). Qed.
Lemma lem4946810 {A B : Type'} (y : B) : (term183 A B y) = (term183 A B y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4946809 A B y s)). Qed.
Lemma lem4946811 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4946812 {A B : Type'} (y : B) : (term184 A B y) = (term184 A B y).
Proof. exact (MK_COMB (@lem4946811 A) (@lem4946810 A B y)). Qed.
Lemma lem4946813 {A B : Type'} : (term185 A B) = (term185 A B).
Proof. exact (fun_ext (fun y : B => @lem4946812 A B y)). Qed.
Lemma lem4946814 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4946815 {A B : Type'} : (term83 A B) = (term83 A B).
Proof. exact (MK_COMB (@lem4946814 B) (@lem4946813 A B)). Qed.
Lemma lem4946816 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4946817 {A B : Type'} : (term109 A B) = (term109 A B).
Proof. exact (MK_COMB (@lem4946816) (@lem4946815 A B)). Qed.
Lemma lem4946818 {A B : Type'} : (term111 A B) = (term111 A B).
Proof. exact (MK_COMB (@lem4946817 A B) (@lem4946794 A B)). Qed.
Lemma lem4946823 {A : Type'} (y : A) (f : A -> A) (x : A) (s : A -> Prop) : (term167 A y f x s) = (term167 A y f x s).
Proof. exact (eq_refl (term167 A y f x s)). Qed.
Lemma lem4946824 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term168 A y f s) = (term168 A y f s).
Proof. exact (fun_ext (fun x : A => @lem4946823 A y f x s)). Qed.
Lemma lem4946825 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4946826 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term169 A y f s) = (term169 A y f s).
Proof. exact (MK_COMB (@lem4946825 A) (@lem4946824 A y f s)). Qed.
Lemma lem4946829 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term170 A y f s) = (term170 A y f s).
Proof. exact (eq_refl (term170 A y f s)). Qed.
Lemma lem4946830 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : ((term171 A y f s) = (term169 A y f s)) = ((term171 A y f s) = (term169 A y f s)).
Proof. exact (MK_COMB (@lem4946829 A y f s) (@lem4946826 A y f s)). Qed.
Lemma lem4946831 {A : Type'} (y : A) (s : A -> Prop) : (term172 A y s) = (term172 A y s).
Proof. exact (fun_ext (fun f : A -> A => @lem4946830 A y f s)). Qed.
Lemma lem4946832 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem4946833 {A : Type'} (y : A) (s : A -> Prop) : (term173 A y s) = (term173 A y s).
Proof. exact (MK_COMB (@lem4946832 A) (@lem4946831 A y s)). Qed.
Lemma lem4946834 {A : Type'} (y : A) : (term174 A y) = (term174 A y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4946833 A y s)). Qed.
Lemma lem4946835 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4946836 {A : Type'} (y : A) : (term175 A y) = (term175 A y).
Proof. exact (MK_COMB (@lem4946835 A) (@lem4946834 A y)). Qed.
Lemma lem4946837 {A : Type'} : (term176 A) = (term176 A).
Proof. exact (fun_ext (fun y : A => @lem4946836 A y)). Qed.
Lemma lem4946838 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4946839 {A : Type'} : (term84 A) = (term84 A).
Proof. exact (MK_COMB (@lem4946838 A) (@lem4946837 A)). Qed.
Lemma lem4946840 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4946841 {A : Type'} : (term106 A) = (term106 A).
Proof. exact (MK_COMB (@lem4946840) (@lem4946839 A)). Qed.
Lemma lem4946842 {A B : Type'} : (term113 A B) = (term113 A B).
Proof. exact (MK_COMB (@lem4946841 A) (@lem4946818 A B)). Qed.
Lemma lem4946855 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term186 A B s f x y) = (term186 A B s f x y).
Proof. exact (eq_refl (term186 A B s f x y)). Qed.
Lemma lem4946856 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term187 A B s f x) = (term187 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem4946855 A B s f x y)). Qed.
Lemma lem4946857 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4946858 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term188 A B s f x) = (term188 A B s f x).
Proof. exact (MK_COMB (@lem4946857 A) (@lem4946856 A B s f x)). Qed.
Lemma lem4946859 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term189 A B s f) = (term189 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4946858 A B s f x)). Qed.
Lemma lem4946860 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4946861 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term31 A B s f) = (term31 A B s f).
Proof. exact (MK_COMB (@lem4946860 A) (@lem4946859 A B s f)). Qed.
Lemma lem4946874 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term186 A B s f x y) = (term186 A B s f x y).
Proof. exact (eq_refl (term186 A B s f x y)). Qed.
Lemma lem4946875 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term187 A B s f x) = (term187 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem4946874 A B s f x y)). Qed.
Lemma lem4946876 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4946877 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term188 A B s f x) = (term188 A B s f x).
Proof. exact (MK_COMB (@lem4946876 A) (@lem4946875 A B s f x)). Qed.
Lemma lem4946878 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term189 A B s f) = (term189 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4946877 A B s f x)). Qed.
Lemma lem4946879 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4946880 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term31 A B s f) = (term31 A B s f).
Proof. exact (MK_COMB (@lem4946879 A) (@lem4946878 A B s f)). Qed.
Lemma lem4946885 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term190 A B s f x y) = (term190 A B s f x y).
Proof. exact (eq_refl (term190 A B s f x y)). Qed.
Lemma lem4946886 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term191 A B s f y) = (term191 A B s f y).
Proof. exact (fun_ext (fun x : A => @lem4946885 A B s f x y)). Qed.
Lemma lem4946887 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4946888 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term53 A B s f y) = (term53 A B s f y).
Proof. exact (MK_COMB (@lem4946887 A) (@lem4946886 A B s f y)). Qed.
Lemma lem4946891 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term192 A B y f s) = (term192 A B y f s).
Proof. exact (eq_refl (term192 A B y f s)). Qed.
Lemma lem4946892 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term64 A B s f y) = (term64 A B s f y).
Proof. exact (MK_COMB (@lem4946891 A B y f s) (@lem4946888 A B s f y)). Qed.
Lemma lem4946893 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term66 A B s f) = (term66 A B s f).
Proof. exact (fun_ext (fun y : B => @lem4946892 A B s f y)). Qed.
Lemma lem4946894 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4946895 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term67 A B s f) = (term67 A B s f).
Proof. exact (MK_COMB (@lem4946894 B) (@lem4946893 A B s f)). Qed.
Lemma lem4946896 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4946897 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term69 A B s f) = (term69 A B s f).
Proof. exact (MK_COMB (@lem4946896) (@lem4946895 A B s f)). Qed.
Lemma lem4946898 {A B : Type'} (s : A -> Prop) (f : A -> B) : ((term67 A B s f) = (term31 A B s f)) = ((term67 A B s f) = (term31 A B s f)).
Proof. exact (MK_COMB (@lem4946897 A B s f) (@lem4946880 A B s f)). Qed.
Lemma lem4946899 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4946900 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term193 A B s f) = (term193 A B s f).
Proof. exact (MK_COMB (@lem4946899) (@lem4946898 A B s f)). Qed.
Lemma lem4946901 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term78 A B s f) = (term78 A B s f).
Proof. exact (MK_COMB (@lem4946900 A B s f) (@lem4946861 A B s f)). Qed.
Lemma lem4946902 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4946903 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term81 A B s f) = (term81 A B s f).
Proof. exact (MK_COMB (@lem4946902) (@lem4946901 A B s f)). Qed.
Lemma lem4946904 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4946905 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term114 A B s f) = (term114 A B s f).
Proof. exact (MK_COMB (@lem4946904) (@lem4946903 A B s f)). Qed.
Lemma lem4946906 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term116 A B s f) = (term116 A B s f).
Proof. exact (MK_COMB (@lem4946905 A B s f) (@lem4946842 A B)). Qed.
Lemma lem4946917 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term117 A B t f s) = (term117 A B t f s).
Proof. exact (eq_refl (term117 A B t f s)). Qed.
Lemma lem4946918 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term118 A B t s f) = (term118 A B t s f).
Proof. exact (MK_COMB (@lem4946917 A B t f s) (@lem4946906 A B s f)). Qed.
Lemma lem4946919 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term120 A B s f) = (term120 A B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4946918 A B t s f)). Qed.
Lemma lem4946920 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4946921 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term122 A B s f) = (term122 A B s f).
Proof. exact (MK_COMB (@lem4946920 B) (@lem4946919 A B s f)). Qed.
Lemma lem4946922 {A B : Type'} (f : A -> B) : (term124 A B f) = (term124 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4946921 A B s f)). Qed.
Lemma lem4946923 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4946924 {A B : Type'} (f : A -> B) : (term126 A B f) = (term126 A B f).
Proof. exact (MK_COMB (@lem4946923 A) (@lem4946922 A B f)). Qed.
Lemma lem4946925 {A B : Type'} : (term128 A B) = (term128 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem4946924 A B f)). Qed.
Lemma lem4946926 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4946927 {A B : Type'} : (term130 A B) = (term130 A B).
Proof. exact (MK_COMB (@lem4946926 A B) (@lem4946925 A B)). Qed.
Lemma lem4947216 {A B : Type'} : (term129 A B) = (term130 A B).
Proof. exact (TRANS (@lem4946657 A B) (@lem4946927 A B)). Qed.
Lemma lem4947217 {A B : Type'} : (term130 A B) = (term129 A B).
Proof. exact (SYM (@lem4947216 A B)). Qed.
Lemma lem4947219 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term81 A B s f) : term81 A B s f.
Proof. exact (h1). Qed.
Lemma lem4947220 {A : Type'} (h1 : term84 A) : term84 A.
Proof. exact (h1). Qed.
Lemma lem4947221 {A B : Type'} (h1 : term83 A B) : term83 A B.
Proof. exact (h1). Qed.
Lemma lem4947222 {B : Type'} (h1 : term84 B) : term84 B.
Proof. exact (h1). Qed.
Lemma lem4947223 {A : Type'} (h1 : term87 A) : term87 A.
Proof. exact (h1). Qed.
Lemma lem4947224 {A B : Type'} (h1 : term86 A B) : term86 A B.
Proof. exact (h1). Qed.
Lemma lem4947225 {A : Type'} (h1 : term85 A) : term85 A.
Proof. exact (h1). Qed.
Lemma lem4947226 {A : Type'} (h1 : term82 A) : term82 A.
Proof. exact (h1). Qed.
Lemma lem4947227 {B : Type'} (h1 : term82 B) : term82 B.
Proof. exact (h1). Qed.
Lemma lem4947252 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term194 A B s f x y) = (term195 A B s f x y).
Proof. exact (@lem17045 (@IN A x s) ((f x) = y)). Qed.
Lemma lem4947255 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term190 A B s f x y) = (term190 A B s f x y).
Proof. exact (eq_refl (term190 A B s f x y)). Qed.
Lemma lem4947256 {A : Type'} (P : A -> Prop) : (term196 A P) = (term197 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem4947257 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term198 A B s f y) = (term199 A B s f y).
Proof. exact (@lem4947256 A (term191 A B s f y)). Qed.
Lemma lem4947258 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term200 A B s f y x) = (term190 A B s f x y).
Proof. exact (eq_refl (term200 A B s f y x)). Qed.
Lemma lem4947259 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4947260 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term201 A B s f y x) = (term194 A B s f x y).
Proof. exact (MK_COMB (@lem4947259) (@lem4947258 A B s f x y)). Qed.
Lemma lem4947261 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term201 A B s f y x) = (term195 A B s f x y).
Proof. exact (TRANS (@lem4947260 A B s f x y) (@lem4947252 A B s f x y)). Qed.
Lemma lem4947262 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term202 A B s f y) = (term203 A B s f y).
Proof. exact (fun_ext (fun x : A => @lem4947261 A B s f x y)). Qed.
Lemma lem4947263 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4947264 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term199 A B s f y) = (term204 A B s f y).
Proof. exact (MK_COMB (@lem4947263 A) (@lem4947262 A B s f y)). Qed.
Lemma lem4947265 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term198 A B s f y) = (term204 A B s f y).
Proof. exact (TRANS (@lem4947257 A B s f y) (@lem4947264 A B s f y)). Qed.
Lemma lem4947266 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term191 A B s f y) = (term191 A B s f y).
Proof. exact (fun_ext (fun x : A => @lem4947255 A B s f x y)). Qed.
Lemma lem4947267 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4947268 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term53 A B s f y) = (term53 A B s f y).
Proof. exact (MK_COMB (@lem4947267 A) (@lem4947266 A B s f y)). Qed.
Lemma lem4947270 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term205 A B y f s) = (term205 A B y f s).
Proof. exact (eq_refl (term205 A B y f s)). Qed.
Lemma lem4947271 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term206 A B s f y) = (term207 A B s f y).
Proof. exact (MK_COMB (@lem4947270 A B y f s) (@lem4947265 A B s f y)). Qed.
Lemma lem4947272 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term208 A B s f y) = (term206 A B s f y).
Proof. exact (@lem17362 (term58 A B y f s) (term53 A B s f y)). Qed.
Lemma lem4947273 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term208 A B s f y) = (term207 A B s f y).
Proof. exact (TRANS (@lem4947272 A B s f y) (@lem4947271 A B s f y)). Qed.
Lemma lem4947275 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term209 A B y f s) = (term209 A B y f s).
Proof. exact (eq_refl (term209 A B y f s)). Qed.
Lemma lem4947276 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term210 A B s f y) = (term210 A B s f y).
Proof. exact (MK_COMB (@lem4947275 A B y f s) (@lem4947268 A B s f y)). Qed.
Lemma lem4947277 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term64 A B s f y) = (term210 A B s f y).
Proof. exact (@lem17265 (term58 A B y f s) (term53 A B s f y)). Qed.
Lemma lem4947278 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term64 A B s f y) = (term210 A B s f y).
Proof. exact (TRANS (@lem4947277 A B s f y) (@lem4947276 A B s f y)). Qed.
Lemma lem4947279 {B : Type'} (P : B -> Prop) : (term211 B P) = (term212 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem4947280 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term213 A B s f) = (term214 A B s f).
Proof. exact (@lem4947279 B (term66 A B s f)). Qed.
Lemma lem4947281 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term215 A B s f y) = (term64 A B s f y).
Proof. exact (eq_refl (term215 A B s f y)). Qed.
Lemma lem4947282 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4947283 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term216 A B s f y) = (term208 A B s f y).
Proof. exact (MK_COMB (@lem4947282) (@lem4947281 A B s f y)). Qed.
Lemma lem4947284 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term216 A B s f y) = (term207 A B s f y).
Proof. exact (TRANS (@lem4947283 A B s f y) (@lem4947273 A B s f y)). Qed.
Lemma lem4947285 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term217 A B s f) = (term218 A B s f).
Proof. exact (fun_ext (fun y : B => @lem4947284 A B s f y)). Qed.
Lemma lem4947286 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4947287 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term214 A B s f) = (term219 A B s f).
Proof. exact (MK_COMB (@lem4947286 B) (@lem4947285 A B s f)). Qed.
Lemma lem4947288 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term213 A B s f) = (term219 A B s f).
Proof. exact (TRANS (@lem4947280 A B s f) (@lem4947287 A B s f)). Qed.
Lemma lem4947289 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term66 A B s f) = (term220 A B s f).
Proof. exact (fun_ext (fun y : B => @lem4947278 A B s f y)). Qed.
Lemma lem4947290 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4947291 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term67 A B s f) = (term221 A B s f).
Proof. exact (MK_COMB (@lem4947290 B) (@lem4947289 A B s f)). Qed.
Lemma lem4947302 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term222 A B s x f y) = (term223 A B s x f y).
Proof. exact (@lem17045 (@IN A y s) ((f x) = (f y))). Qed.
Lemma lem4947307 {A : Type'} (x : A) (s : A -> Prop) : (term224 A x s) = (term224 A x s).
Proof. exact (eq_refl (term224 A x s)). Qed.
Lemma lem4947308 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term225 A B s x f y) = (term226 A B s x f y).
Proof. exact (MK_COMB (@lem4947307 A x s) (@lem4947302 A B s x f y)). Qed.
Lemma lem4947309 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term227 A B s x f y) = (term225 A B s x f y).
Proof. exact (@lem17045 (@IN A x s) (term228 A B s x f y)). Qed.
Lemma lem4947310 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term227 A B s x f y) = (term226 A B s x f y).
Proof. exact (TRANS (@lem4947309 A B s x f y) (@lem4947308 A B s x f y)). Qed.
Lemma lem4947315 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4947320 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term229 A B s f x y) = (term230 A B s f x y).
Proof. exact (@lem17362 (term231 A B s x f y) (x = y)). Qed.
Lemma lem4947321 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4947322 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term232 A B s x f y) = (term233 A B s x f y).
Proof. exact (MK_COMB (@lem4947321) (@lem4947310 A B s x f y)). Qed.
Lemma lem4947323 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term234 A B s f x y) = (term235 A B s f x y).
Proof. exact (MK_COMB (@lem4947322 A B s x f y) (@lem4947315 A x y)). Qed.
Lemma lem4947324 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term186 A B s f x y) = (term234 A B s f x y).
Proof. exact (@lem17265 (term231 A B s x f y) (x = y)). Qed.
Lemma lem4947325 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term186 A B s f x y) = (term235 A B s f x y).
Proof. exact (TRANS (@lem4947324 A B s f x y) (@lem4947323 A B s f x y)). Qed.
Lemma lem4947326 {A : Type'} (P : A -> Prop) : (term211 A P) = (term212 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4947327 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term236 A B s f x) = (term237 A B s f x).
Proof. exact (@lem4947326 A (term187 A B s f x)). Qed.
Lemma lem4947328 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term238 A B s f x y) = (term186 A B s f x y).
Proof. exact (eq_refl (term238 A B s f x y)). Qed.
Lemma lem4947329 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4947330 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term239 A B s f x y) = (term229 A B s f x y).
Proof. exact (MK_COMB (@lem4947329) (@lem4947328 A B s f x y)). Qed.
Lemma lem4947331 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term239 A B s f x y) = (term230 A B s f x y).
Proof. exact (TRANS (@lem4947330 A B s f x y) (@lem4947320 A B s f x y)). Qed.
Lemma lem4947332 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term240 A B s f x) = (term241 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem4947331 A B s f x y)). Qed.
Lemma lem4947333 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4947334 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term237 A B s f x) = (term242 A B s f x).
Proof. exact (MK_COMB (@lem4947333 A) (@lem4947332 A B s f x)). Qed.
Lemma lem4947335 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term236 A B s f x) = (term242 A B s f x).
Proof. exact (TRANS (@lem4947327 A B s f x) (@lem4947334 A B s f x)). Qed.
Lemma lem4947336 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term187 A B s f x) = (term243 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem4947325 A B s f x y)). Qed.
Lemma lem4947337 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4947338 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term188 A B s f x) = (term244 A B s f x).
Proof. exact (MK_COMB (@lem4947337 A) (@lem4947336 A B s f x)). Qed.
Lemma lem4947339 {A : Type'} (P : A -> Prop) : (term211 A P) = (term212 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4947340 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term245 A B s f) = (term246 A B s f).
Proof. exact (@lem4947339 A (term189 A B s f)). Qed.
Lemma lem4947341 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term247 A B s f x) = (term188 A B s f x).
Proof. exact (eq_refl (term247 A B s f x)). Qed.
Lemma lem4947342 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4947343 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term248 A B s f x) = (term236 A B s f x).
Proof. exact (MK_COMB (@lem4947342) (@lem4947341 A B s f x)). Qed.
Lemma lem4947344 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term248 A B s f x) = (term242 A B s f x).
Proof. exact (TRANS (@lem4947343 A B s f x) (@lem4947335 A B s f x)). Qed.
Lemma lem4947345 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term249 A B s f) = (term250 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4947344 A B s f x)). Qed.
Lemma lem4947346 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4947347 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term246 A B s f) = (term251 A B s f).
Proof. exact (MK_COMB (@lem4947346 A) (@lem4947345 A B s f)). Qed.
Lemma lem4947348 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term245 A B s f) = (term251 A B s f).
Proof. exact (TRANS (@lem4947340 A B s f) (@lem4947347 A B s f)). Qed.
Lemma lem4947349 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term189 A B s f) = (term252 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4947338 A B s f x)). Qed.
Lemma lem4947350 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4947351 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term31 A B s f) = (term253 A B s f).
Proof. exact (MK_COMB (@lem4947350 A) (@lem4947349 A B s f)). Qed.
Lemma lem4947352 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4947353 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term254 A B s f) = (term255 A B s f).
Proof. exact (MK_COMB (@lem4947352) (@lem4947288 A B s f)). Qed.
Lemma lem4947354 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term256 A B s f) = (term257 A B s f).
Proof. exact (MK_COMB (@lem4947353 A B s f) (@lem4947348 A B s f)). Qed.
Lemma lem4947355 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4947356 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term258 A B s f) = (term259 A B s f).
Proof. exact (MK_COMB (@lem4947355) (@lem4947291 A B s f)). Qed.
Lemma lem4947357 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term260 A B s f) = (term261 A B s f).
Proof. exact (MK_COMB (@lem4947356 A B s f) (@lem4947351 A B s f)). Qed.
Lemma lem4947358 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4947359 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term262 A B s f) = (term263 A B s f).
Proof. exact (MK_COMB (@lem4947358) (@lem4947357 A B s f)). Qed.
Lemma lem4947360 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term264 A B s f) = (term265 A B s f).
Proof. exact (MK_COMB (@lem4947359 A B s f) (@lem4947354 A B s f)). Qed.
Lemma lem4947361 {A B : Type'} (s : A -> Prop) (f : A -> B) : ((term67 A B s f) = (term31 A B s f)) = (term264 A B s f).
Proof. exact (@lem17500 (term67 A B s f) (term31 A B s f)). Qed.
Lemma lem4947362 {A B : Type'} (s : A -> Prop) (f : A -> B) : ((term67 A B s f) = (term31 A B s f)) = (term265 A B s f).
Proof. exact (TRANS (@lem4947361 A B s f) (@lem4947360 A B s f)). Qed.
Lemma lem4947377 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term229 A B s f x y) = (term230 A B s f x y).
Proof. exact (@lem17362 (term231 A B s x f y) (x = y)). Qed.
Lemma lem4947378 {A : Type'} (P : A -> Prop) : (term211 A P) = (term212 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4947379 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term236 A B s f x) = (term237 A B s f x).
Proof. exact (@lem4947378 A (term187 A B s f x)). Qed.
Lemma lem4947380 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term238 A B s f x y) = (term186 A B s f x y).
Proof. exact (eq_refl (term238 A B s f x y)). Qed.
Lemma lem4947381 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4947382 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term239 A B s f x y) = (term229 A B s f x y).
Proof. exact (MK_COMB (@lem4947381) (@lem4947380 A B s f x y)). Qed.
Lemma lem4947383 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term239 A B s f x y) = (term230 A B s f x y).
Proof. exact (TRANS (@lem4947382 A B s f x y) (@lem4947377 A B s f x y)). Qed.
Lemma lem4947384 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term240 A B s f x) = (term241 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem4947383 A B s f x y)). Qed.
Lemma lem4947385 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4947386 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term237 A B s f x) = (term242 A B s f x).
Proof. exact (MK_COMB (@lem4947385 A) (@lem4947384 A B s f x)). Qed.
Lemma lem4947387 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term236 A B s f x) = (term242 A B s f x).
Proof. exact (TRANS (@lem4947379 A B s f x) (@lem4947386 A B s f x)). Qed.
Lemma lem4947388 {A : Type'} (P : A -> Prop) : (term211 A P) = (term212 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4947389 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term245 A B s f) = (term246 A B s f).
Proof. exact (@lem4947388 A (term189 A B s f)). Qed.
Lemma lem4947390 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term247 A B s f x) = (term188 A B s f x).
Proof. exact (eq_refl (term247 A B s f x)). Qed.
Lemma lem4947391 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4947392 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term248 A B s f x) = (term236 A B s f x).
Proof. exact (MK_COMB (@lem4947391) (@lem4947390 A B s f x)). Qed.
Lemma lem4947393 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term248 A B s f x) = (term242 A B s f x).
Proof. exact (TRANS (@lem4947392 A B s f x) (@lem4947387 A B s f x)). Qed.
Lemma lem4947394 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term249 A B s f) = (term250 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4947393 A B s f x)). Qed.
Lemma lem4947395 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4947396 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term246 A B s f) = (term251 A B s f).
Proof. exact (MK_COMB (@lem4947395 A) (@lem4947394 A B s f)). Qed.
Lemma lem4947397 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term245 A B s f) = (term251 A B s f).
Proof. exact (TRANS (@lem4947389 A B s f) (@lem4947396 A B s f)). Qed.
Lemma lem4947398 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4947399 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term266 A B s f) = (term267 A B s f).
Proof. exact (MK_COMB (@lem4947398) (@lem4947362 A B s f)). Qed.
Lemma lem4947400 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term268 A B s f) = (term269 A B s f).
Proof. exact (MK_COMB (@lem4947399 A B s f) (@lem4947397 A B s f)). Qed.
Lemma lem4947401 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term81 A B s f) = (term268 A B s f).
Proof. exact (@lem17362 ((term67 A B s f) = (term31 A B s f)) (term31 A B s f)). Qed.
Lemma lem4947402 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term81 A B s f) = (term269 A B s f).
Proof. exact (TRANS (@lem4947401 A B s f) (@lem4947400 A B s f)). Qed.
Lemma lem4947753 {A : Type'} (P : Prop) (Q : A -> Prop) : (term270 A P Q) = (term271 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4947754 {A : Type'} (P : Prop) (Q : A -> Prop) : (term270 A P Q) = (term271 A P Q).
Proof. exact (@lem4947753 A P Q). Qed.
Lemma lem4947755 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term272 A B s f y) = (term273 A B s f y).
Proof. exact (@lem4947754 A (term274 A B y f s) (term191 A B s f y)). Qed.
Lemma lem4947756 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term200 A B s f y x) = (term190 A B s f x y).
Proof. exact (eq_refl (term200 A B s f y x)). Qed.
Lemma lem4947757 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term275 A B s f y) = (term191 A B s f y).
Proof. exact (fun_ext (fun x : A => @lem4947756 A B s f x y)). Qed.
Lemma lem4947758 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4947759 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term276 A B s f y) = (term53 A B s f y).
Proof. exact (MK_COMB (@lem4947758 A) (@lem4947757 A B s f y)). Qed.
Lemma lem4947760 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term209 A B y f s) = (term209 A B y f s).
Proof. exact (eq_refl (term209 A B y f s)). Qed.
Lemma lem4947761 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term272 A B s f y) = (term210 A B s f y).
Proof. exact (MK_COMB (@lem4947760 A B y f s) (@lem4947759 A B s f y)). Qed.
Lemma lem4947762 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4947763 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term277 A B s f y) = (term278 A B s f y).
Proof. exact (MK_COMB (@lem4947762) (@lem4947761 A B s f y)). Qed.
Lemma lem4947764 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term200 A B s f y x) = (term190 A B s f x y).
Proof. exact (eq_refl (term200 A B s f y x)). Qed.
Lemma lem4947765 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term209 A B y f s) = (term209 A B y f s).
Proof. exact (eq_refl (term209 A B y f s)). Qed.
Lemma lem4947766 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term279 A B s f y x) = (term280 A B s f x y).
Proof. exact (MK_COMB (@lem4947765 A B y f s) (@lem4947764 A B s f x y)). Qed.
Lemma lem4947767 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term281 A B s f y) = (term282 A B s f y).
Proof. exact (fun_ext (fun x : A => @lem4947766 A B s f x y)). Qed.
Lemma lem4947768 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4947769 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term273 A B s f y) = (term283 A B s f y).
Proof. exact (MK_COMB (@lem4947768 A) (@lem4947767 A B s f y)). Qed.
Lemma lem4947770 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : ((term272 A B s f y) = (term273 A B s f y)) = ((term210 A B s f y) = (term283 A B s f y)).
Proof. exact (MK_COMB (@lem4947763 A B s f y) (@lem4947769 A B s f y)). Qed.
Lemma lem4947771 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term210 A B s f y) = (term283 A B s f y).
Proof. exact (EQ_MP (@lem4947770 A B s f y) (@lem4947755 A B s f y)). Qed.
Lemma lem4947772 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term220 A B s f) = (term284 A B s f).
Proof. exact (fun_ext (fun y : B => @lem4947771 A B s f y)). Qed.
Lemma lem4947773 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4947774 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term221 A B s f) = (term285 A B s f).
Proof. exact (MK_COMB (@lem4947773 B) (@lem4947772 A B s f)). Qed.
Lemma lem4947776 {A B : Type'} (P : type1413 A B) : (term286 A B P) = (term287 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4947777 {A B : Type'} (P : type1470 A B) : (term288 A B P) = (term289 A B P).
Proof. exact (@lem4947776 B A P). Qed.
Lemma lem4947778 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term290 A B s f) = (term291 A B s f).
Proof. exact (@lem4947777 A B (term292 A B s f)). Qed.
Lemma lem4947779 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term293 A B s f y) = (term282 A B s f y).
Proof. exact (eq_refl (term293 A B s f y)). Qed.
Lemma lem4947780 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4947781 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term294 A B s f y x) = (term295 A B s f y x).
Proof. exact (MK_COMB (@lem4947779 A B s f y) (@lem4947780 A x)). Qed.
Lemma lem4947782 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term295 A B s f y x) = (term280 A B s f x y).
Proof. exact (eq_refl (term295 A B s f y x)). Qed.
Lemma lem4947783 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term294 A B s f y x) = (term280 A B s f x y).
Proof. exact (TRANS (@lem4947781 A B s f y x) (@lem4947782 A B s f x y)). Qed.
Lemma lem4947784 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term296 A B s f y) = (term282 A B s f y).
Proof. exact (fun_ext (fun x : A => @lem4947783 A B s f x y)). Qed.
Lemma lem4947785 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4947786 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term297 A B s f y) = (term283 A B s f y).
Proof. exact (MK_COMB (@lem4947785 A) (@lem4947784 A B s f y)). Qed.
Lemma lem4947787 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term298 A B s f) = (term284 A B s f).
Proof. exact (fun_ext (fun y : B => @lem4947786 A B s f y)). Qed.
Lemma lem4947788 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4947789 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term290 A B s f) = (term285 A B s f).
Proof. exact (MK_COMB (@lem4947788 B) (@lem4947787 A B s f)). Qed.
Lemma lem4947790 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4947791 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term299 A B s f) = (term300 A B s f).
Proof. exact (MK_COMB (@lem4947790) (@lem4947789 A B s f)). Qed.
Lemma lem4947792 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term293 A B s f y) = (term282 A B s f y).
Proof. exact (eq_refl (term293 A B s f y)). Qed.
Lemma lem4947793 {A B : Type'} (x : B -> A) (y : B) : (x y) = (x y).
Proof. exact (eq_refl (x y)). Qed.
Lemma lem4947794 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B -> A) (y : B) : (term301 A B s f x y) = (term302 A B s f x y).
Proof. exact (MK_COMB (@lem4947792 A B s f y) (@lem4947793 A B x y)). Qed.
Lemma lem4947795 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B -> A) (y : B) : (term302 A B s f x y) = (term303 A B s f x y).
Proof. exact (eq_refl (term302 A B s f x y)). Qed.
Lemma lem4947796 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B -> A) (y : B) : (term301 A B s f x y) = (term303 A B s f x y).
Proof. exact (TRANS (@lem4947794 A B s f x y) (@lem4947795 A B s f x y)). Qed.
Lemma lem4947797 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B -> A) : (term304 A B s f x) = (term305 A B s f x).
Proof. exact (fun_ext (fun y : B => @lem4947796 A B s f x y)). Qed.
Lemma lem4947798 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4947799 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B -> A) : (term306 A B s f x) = (term307 A B s f x).
Proof. exact (MK_COMB (@lem4947798 B) (@lem4947797 A B s f x)). Qed.
Lemma lem4947800 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term308 A B s f) = (term309 A B s f).
Proof. exact (fun_ext (fun x : B -> A => @lem4947799 A B s f x)). Qed.
Lemma lem4947801 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem4947802 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term291 A B s f) = (term310 A B s f).
Proof. exact (MK_COMB (@lem4947801 A B) (@lem4947800 A B s f)). Qed.
Lemma lem4947803 {A B : Type'} (s : A -> Prop) (f : A -> B) : ((term290 A B s f) = (term291 A B s f)) = ((term285 A B s f) = (term310 A B s f)).
Proof. exact (MK_COMB (@lem4947791 A B s f) (@lem4947802 A B s f)). Qed.
Lemma lem4947804 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term285 A B s f) = (term310 A B s f).
Proof. exact (EQ_MP (@lem4947803 A B s f) (@lem4947778 A B s f)). Qed.
Lemma lem4947805 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term221 A B s f) = (term310 A B s f).
Proof. exact (TRANS (@lem4947774 A B s f) (@lem4947804 A B s f)). Qed.
Lemma lem4947806 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4947807 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term259 A B s f) = (term311 A B s f).
Proof. exact (MK_COMB (@lem4947806) (@lem4947805 A B s f)). Qed.
Lemma lem4947808 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term253 A B s f) = (term253 A B s f).
Proof. exact (eq_refl (term253 A B s f)). Qed.
Lemma lem4947809 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term261 A B s f) = (term312 A B s f).
Proof. exact (MK_COMB (@lem4947807 A B s f) (@lem4947808 A B s f)). Qed.
Lemma lem4947811 {A : Type'} (P : A -> Prop) (Q : Prop) : (term313 A P Q) = (term314 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4947812 {A B : Type'} (P : type805 A B) (Q : Prop) : (term315 A B P Q) = (term316 A B P Q).
Proof. exact (@lem4947811 (B -> A) P Q). Qed.
Lemma lem4947813 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term317 A B s f) = (term318 A B s f).
Proof. exact (@lem4947812 A B (term309 A B s f) (term253 A B s f)). Qed.
Lemma lem4947814 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B -> A) : (term319 A B s f x) = (term307 A B s f x).
Proof. exact (eq_refl (term319 A B s f x)). Qed.
Lemma lem4947815 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term320 A B s f) = (term309 A B s f).
Proof. exact (fun_ext (fun x : B -> A => @lem4947814 A B s f x)). Qed.
Lemma lem4947816 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem4947817 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term321 A B s f) = (term310 A B s f).
Proof. exact (MK_COMB (@lem4947816 A B) (@lem4947815 A B s f)). Qed.
Lemma lem4947818 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4947819 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term322 A B s f) = (term311 A B s f).
Proof. exact (MK_COMB (@lem4947818) (@lem4947817 A B s f)). Qed.
Lemma lem4947820 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term253 A B s f) = (term253 A B s f).
Proof. exact (eq_refl (term253 A B s f)). Qed.
Lemma lem4947821 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term317 A B s f) = (term312 A B s f).
Proof. exact (MK_COMB (@lem4947819 A B s f) (@lem4947820 A B s f)). Qed.
Lemma lem4947822 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4947823 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term323 A B s f) = (term324 A B s f).
Proof. exact (MK_COMB (@lem4947822) (@lem4947821 A B s f)). Qed.
Lemma lem4947824 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B -> A) : (term319 A B s f x) = (term307 A B s f x).
Proof. exact (eq_refl (term319 A B s f x)). Qed.
Lemma lem4947825 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4947826 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B -> A) : (term325 A B s f x) = (term326 A B s f x).
Proof. exact (MK_COMB (@lem4947825) (@lem4947824 A B s f x)). Qed.
Lemma lem4947827 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term253 A B s f) = (term253 A B s f).
Proof. exact (eq_refl (term253 A B s f)). Qed.
Lemma lem4947828 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) : (term327 A B x s f) = (term328 A B x s f).
Proof. exact (MK_COMB (@lem4947826 A B s f x) (@lem4947827 A B s f)). Qed.
Lemma lem4947829 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term329 A B s f) = (term330 A B s f).
Proof. exact (fun_ext (fun x : B -> A => @lem4947828 A B x s f)). Qed.
Lemma lem4947830 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem4947831 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term318 A B s f) = (term331 A B s f).
Proof. exact (MK_COMB (@lem4947830 A B) (@lem4947829 A B s f)). Qed.
Lemma lem4947832 {A B : Type'} (s : A -> Prop) (f : A -> B) : ((term317 A B s f) = (term318 A B s f)) = ((term312 A B s f) = (term331 A B s f)).
Proof. exact (MK_COMB (@lem4947823 A B s f) (@lem4947831 A B s f)). Qed.
Lemma lem4947833 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term312 A B s f) = (term331 A B s f).
Proof. exact (EQ_MP (@lem4947832 A B s f) (@lem4947813 A B s f)). Qed.
Lemma lem4947834 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term261 A B s f) = (term331 A B s f).
Proof. exact (TRANS (@lem4947809 A B s f) (@lem4947833 A B s f)). Qed.
Lemma lem4947835 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4947836 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term263 A B s f) = (term332 A B s f).
Proof. exact (MK_COMB (@lem4947835) (@lem4947834 A B s f)). Qed.
Lemma lem4947838 {A : Type'} (P : A -> Prop) (Q : Prop) : (term313 A P Q) = (term314 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4947839 {B : Type'} (P : B -> Prop) (Q : Prop) : (term313 B P Q) = (term314 B P Q).
Proof. exact (@lem4947838 B P Q). Qed.
Lemma lem4947840 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term333 A B s f) = (term334 A B s f).
Proof. exact (@lem4947839 B (term218 A B s f) (term251 A B s f)). Qed.
Lemma lem4947841 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term335 A B s f y) = (term207 A B s f y).
Proof. exact (eq_refl (term335 A B s f y)). Qed.
Lemma lem4947842 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term336 A B s f) = (term218 A B s f).
Proof. exact (fun_ext (fun y : B => @lem4947841 A B s f y)). Qed.
Lemma lem4947843 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4947844 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term337 A B s f) = (term219 A B s f).
Proof. exact (MK_COMB (@lem4947843 B) (@lem4947842 A B s f)). Qed.
Lemma lem4947845 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4947846 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term338 A B s f) = (term255 A B s f).
Proof. exact (MK_COMB (@lem4947845) (@lem4947844 A B s f)). Qed.
Lemma lem4947847 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term251 A B s f) = (term251 A B s f).
Proof. exact (eq_refl (term251 A B s f)). Qed.
Lemma lem4947848 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term333 A B s f) = (term257 A B s f).
Proof. exact (MK_COMB (@lem4947846 A B s f) (@lem4947847 A B s f)). Qed.
Lemma lem4947849 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4947850 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term339 A B s f) = (term340 A B s f).
Proof. exact (MK_COMB (@lem4947849) (@lem4947848 A B s f)). Qed.
Lemma lem4947851 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term335 A B s f y) = (term207 A B s f y).
Proof. exact (eq_refl (term335 A B s f y)). Qed.
Lemma lem4947852 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4947853 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term341 A B s f y) = (term342 A B s f y).
Proof. exact (MK_COMB (@lem4947852) (@lem4947851 A B s f y)). Qed.
Lemma lem4947854 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term251 A B s f) = (term251 A B s f).
Proof. exact (eq_refl (term251 A B s f)). Qed.
Lemma lem4947855 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : (term343 A B y s f) = (term344 A B y s f).
Proof. exact (MK_COMB (@lem4947853 A B s f y) (@lem4947854 A B s f)). Qed.
Lemma lem4947856 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term345 A B s f) = (term346 A B s f).
Proof. exact (fun_ext (fun y : B => @lem4947855 A B y s f)). Qed.
Lemma lem4947857 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4947858 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term334 A B s f) = (term347 A B s f).
Proof. exact (MK_COMB (@lem4947857 B) (@lem4947856 A B s f)). Qed.
Lemma lem4947859 {A B : Type'} (s : A -> Prop) (f : A -> B) : ((term333 A B s f) = (term334 A B s f)) = ((term257 A B s f) = (term347 A B s f)).
Proof. exact (MK_COMB (@lem4947850 A B s f) (@lem4947858 A B s f)). Qed.
Lemma lem4947860 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term257 A B s f) = (term347 A B s f).
Proof. exact (EQ_MP (@lem4947859 A B s f) (@lem4947840 A B s f)). Qed.
Lemma lem4947862 {A : Type'} (P : Prop) (Q : A -> Prop) : (term348 A P Q) = (term349 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4947863 {A : Type'} (P : Prop) (Q : A -> Prop) : (term348 A P Q) = (term349 A P Q).
Proof. exact (@lem4947862 A P Q). Qed.
Lemma lem4947864 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : (term350 A B y s f) = (term351 A B y s f).
Proof. exact (@lem4947863 A (term207 A B s f y) (term250 A B s f)). Qed.
Lemma lem4947865 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term352 A B s f x) = (term242 A B s f x).
Proof. exact (eq_refl (term352 A B s f x)). Qed.
Lemma lem4947866 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term353 A B s f) = (term250 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4947865 A B s f x)). Qed.
Lemma lem4947867 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4947868 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term354 A B s f) = (term251 A B s f).
Proof. exact (MK_COMB (@lem4947867 A) (@lem4947866 A B s f)). Qed.
Lemma lem4947869 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term342 A B s f y) = (term342 A B s f y).
Proof. exact (eq_refl (term342 A B s f y)). Qed.
Lemma lem4947870 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : (term350 A B y s f) = (term344 A B y s f).
Proof. exact (MK_COMB (@lem4947869 A B s f y) (@lem4947868 A B s f)). Qed.
Lemma lem4947871 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4947872 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : (term355 A B y s f) = (term356 A B y s f).
Proof. exact (MK_COMB (@lem4947871) (@lem4947870 A B y s f)). Qed.
Lemma lem4947873 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term352 A B s f x) = (term242 A B s f x).
Proof. exact (eq_refl (term352 A B s f x)). Qed.
Lemma lem4947874 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term342 A B s f y) = (term342 A B s f y).
Proof. exact (eq_refl (term342 A B s f y)). Qed.
Lemma lem4947875 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) (x : A) : (term357 A B y s f x) = (term358 A B y s f x).
Proof. exact (MK_COMB (@lem4947874 A B s f y) (@lem4947873 A B s f x)). Qed.
Lemma lem4947876 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : (term359 A B y s f) = (term360 A B y s f).
Proof. exact (fun_ext (fun x : A => @lem4947875 A B y s f x)). Qed.
Lemma lem4947877 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4947878 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : (term351 A B y s f) = (term361 A B y s f).
Proof. exact (MK_COMB (@lem4947877 A) (@lem4947876 A B y s f)). Qed.
Lemma lem4947879 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : ((term350 A B y s f) = (term351 A B y s f)) = ((term344 A B y s f) = (term361 A B y s f)).
Proof. exact (MK_COMB (@lem4947872 A B y s f) (@lem4947878 A B y s f)). Qed.
Lemma lem4947880 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : (term344 A B y s f) = (term361 A B y s f).
Proof. exact (EQ_MP (@lem4947879 A B y s f) (@lem4947864 A B y s f)). Qed.
Lemma lem4947882 {A : Type'} (P : Prop) (Q : A -> Prop) : (term348 A P Q) = (term349 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4947883 {A : Type'} (P : Prop) (Q : A -> Prop) : (term348 A P Q) = (term349 A P Q).
Proof. exact (@lem4947882 A P Q). Qed.
Lemma lem4947884 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) (x : A) : (term362 A B y s f x) = (term363 A B y s f x).
Proof. exact (@lem4947883 A (term207 A B s f y) (term241 A B s f x)). Qed.
Lemma lem4947885 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term364 A B s f x y) = (term230 A B s f x y).
Proof. exact (eq_refl (term364 A B s f x y)). Qed.
Lemma lem4947886 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term365 A B s f x) = (term241 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem4947885 A B s f x y)). Qed.
Lemma lem4947887 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4947888 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term366 A B s f x) = (term242 A B s f x).
Proof. exact (MK_COMB (@lem4947887 A) (@lem4947886 A B s f x)). Qed.
Lemma lem4947889 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term342 A B s f y) = (term342 A B s f y).
Proof. exact (eq_refl (term342 A B s f y)). Qed.
Lemma lem4947890 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) (x : A) : (term362 A B y s f x) = (term358 A B y s f x).
Proof. exact (MK_COMB (@lem4947889 A B s f y) (@lem4947888 A B s f x)). Qed.
Lemma lem4947891 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4947892 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) (x : A) : (term367 A B y s f x) = (term368 A B y s f x).
Proof. exact (MK_COMB (@lem4947891) (@lem4947890 A B y s f x)). Qed.
Lemma lem4947893 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term364 A B s f x y) = (term230 A B s f x y).
Proof. exact (eq_refl (term364 A B s f x y)). Qed.
Lemma lem4947894 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term342 A B s f y) = (term342 A B s f y).
Proof. exact (eq_refl (term342 A B s f y)). Qed.
Lemma lem4947895 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) (x : A) (y' : A) : (term369 A B y s f x y') = (term370 A B y s f x y').
Proof. exact (MK_COMB (@lem4947894 A B s f y) (@lem4947893 A B s f x y')). Qed.
Lemma lem4947896 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) (x : A) : (term371 A B y s f x) = (term372 A B y s f x).
Proof. exact (fun_ext (fun y' : A => @lem4947895 A B y s f x y')). Qed.
Lemma lem4947897 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4947898 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) (x : A) : (term363 A B y s f x) = (term373 A B y s f x).
Proof. exact (MK_COMB (@lem4947897 A) (@lem4947896 A B y s f x)). Qed.
Lemma lem4947899 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) (x : A) : ((term362 A B y s f x) = (term363 A B y s f x)) = ((term358 A B y s f x) = (term373 A B y s f x)).
Proof. exact (MK_COMB (@lem4947892 A B y s f x) (@lem4947898 A B y s f x)). Qed.
Lemma lem4947900 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) (x : A) : (term358 A B y s f x) = (term373 A B y s f x).
Proof. exact (EQ_MP (@lem4947899 A B y s f x) (@lem4947884 A B y s f x)). Qed.
Lemma lem4947901 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : (term360 A B y s f) = (term374 A B y s f).
Proof. exact (fun_ext (fun x : A => @lem4947900 A B y s f x)). Qed.
Lemma lem4947902 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4947903 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : (term361 A B y s f) = (term375 A B y s f).
Proof. exact (MK_COMB (@lem4947902 A) (@lem4947901 A B y s f)). Qed.
Lemma lem4947904 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : (term344 A B y s f) = (term375 A B y s f).
Proof. exact (TRANS (@lem4947880 A B y s f) (@lem4947903 A B y s f)). Qed.
Lemma lem4947905 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term346 A B s f) = (term376 A B s f).
Proof. exact (fun_ext (fun y : B => @lem4947904 A B y s f)). Qed.
Lemma lem4947906 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4947907 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term347 A B s f) = (term377 A B s f).
Proof. exact (MK_COMB (@lem4947906 B) (@lem4947905 A B s f)). Qed.
Lemma lem4947908 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term257 A B s f) = (term377 A B s f).
Proof. exact (TRANS (@lem4947860 A B s f) (@lem4947907 A B s f)). Qed.
Lemma lem4947909 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term265 A B s f) = (term378 A B s f).
Proof. exact (MK_COMB (@lem4947836 A B s f) (@lem4947908 A B s f)). Qed.
Lemma lem4947913 {A : Type'} (P : A -> Prop) (Q : Prop) : (term379 A P Q) = (term380 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4947914 {A B : Type'} (P : type805 A B) (Q : Prop) : (term381 A B P Q) = (term382 A B P Q).
Proof. exact (@lem4947913 (B -> A) P Q). Qed.
Lemma lem4947915 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term383 A B s f) = (term384 A B s f).
Proof. exact (@lem4947914 A B (term330 A B s f) (term377 A B s f)). Qed.
Lemma lem4947916 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) : (term385 A B s f x) = (term328 A B x s f).
Proof. exact (eq_refl (term385 A B s f x)). Qed.
Lemma lem4947917 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term386 A B s f) = (term330 A B s f).
Proof. exact (fun_ext (fun x : B -> A => @lem4947916 A B x s f)). Qed.
Lemma lem4947918 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem4947919 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term387 A B s f) = (term331 A B s f).
Proof. exact (MK_COMB (@lem4947918 A B) (@lem4947917 A B s f)). Qed.
Lemma lem4947920 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4947921 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term388 A B s f) = (term332 A B s f).
Proof. exact (MK_COMB (@lem4947920) (@lem4947919 A B s f)). Qed.
Lemma lem4947922 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term377 A B s f) = (term377 A B s f).
Proof. exact (eq_refl (term377 A B s f)). Qed.
Lemma lem4947923 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term383 A B s f) = (term378 A B s f).
Proof. exact (MK_COMB (@lem4947921 A B s f) (@lem4947922 A B s f)). Qed.
Lemma lem4947924 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4947925 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term389 A B s f) = (term390 A B s f).
Proof. exact (MK_COMB (@lem4947924) (@lem4947923 A B s f)). Qed.
Lemma lem4947926 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) : (term385 A B s f x) = (term328 A B x s f).
Proof. exact (eq_refl (term385 A B s f x)). Qed.
Lemma lem4947927 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4947928 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) : (term391 A B s f x) = (term392 A B x s f).
Proof. exact (MK_COMB (@lem4947927) (@lem4947926 A B x s f)). Qed.
Lemma lem4947929 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term377 A B s f) = (term377 A B s f).
Proof. exact (eq_refl (term377 A B s f)). Qed.
Lemma lem4947930 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) : (term393 A B x s f) = (term394 A B x s f).
Proof. exact (MK_COMB (@lem4947928 A B x s f) (@lem4947929 A B s f)). Qed.
Lemma lem4947931 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term395 A B s f) = (term396 A B s f).
Proof. exact (fun_ext (fun x : B -> A => @lem4947930 A B x s f)). Qed.
Lemma lem4947932 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem4947933 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term384 A B s f) = (term397 A B s f).
Proof. exact (MK_COMB (@lem4947932 A B) (@lem4947931 A B s f)). Qed.
Lemma lem4947934 {A B : Type'} (s : A -> Prop) (f : A -> B) : ((term383 A B s f) = (term384 A B s f)) = ((term378 A B s f) = (term397 A B s f)).
Proof. exact (MK_COMB (@lem4947925 A B s f) (@lem4947933 A B s f)). Qed.
Lemma lem4947935 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term378 A B s f) = (term397 A B s f).
Proof. exact (EQ_MP (@lem4947934 A B s f) (@lem4947915 A B s f)). Qed.
Lemma lem4947937 {A : Type'} (P : Prop) (Q : A -> Prop) : (term270 A P Q) = (term271 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4947938 {B : Type'} (P : Prop) (Q : B -> Prop) : (term270 B P Q) = (term271 B P Q).
Proof. exact (@lem4947937 B P Q). Qed.
Lemma lem4947939 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) : (term398 A B x s f) = (term399 A B x s f).
Proof. exact (@lem4947938 B (term328 A B x s f) (term376 A B s f)). Qed.
Lemma lem4947940 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : (term400 A B s f y) = (term375 A B y s f).
Proof. exact (eq_refl (term400 A B s f y)). Qed.
Lemma lem4947941 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term401 A B s f) = (term376 A B s f).
Proof. exact (fun_ext (fun y : B => @lem4947940 A B y s f)). Qed.
Lemma lem4947942 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4947943 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term402 A B s f) = (term377 A B s f).
Proof. exact (MK_COMB (@lem4947942 B) (@lem4947941 A B s f)). Qed.
Lemma lem4947944 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) : (term392 A B x s f) = (term392 A B x s f).
Proof. exact (eq_refl (term392 A B x s f)). Qed.
Lemma lem4947945 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) : (term398 A B x s f) = (term394 A B x s f).
Proof. exact (MK_COMB (@lem4947944 A B x s f) (@lem4947943 A B s f)). Qed.
Lemma lem4947946 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4947947 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) : (term403 A B x s f) = (term404 A B x s f).
Proof. exact (MK_COMB (@lem4947946) (@lem4947945 A B x s f)). Qed.
Lemma lem4947948 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : (term400 A B s f y) = (term375 A B y s f).
Proof. exact (eq_refl (term400 A B s f y)). Qed.
Lemma lem4947949 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) : (term392 A B x s f) = (term392 A B x s f).
Proof. exact (eq_refl (term392 A B x s f)). Qed.
Lemma lem4947950 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) : (term405 A B x s f y) = (term406 A B x y s f).
Proof. exact (MK_COMB (@lem4947949 A B x s f) (@lem4947948 A B y s f)). Qed.
Lemma lem4947951 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) : (term407 A B x s f) = (term408 A B x s f).
Proof. exact (fun_ext (fun y : B => @lem4947950 A B x y s f)). Qed.
Lemma lem4947952 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4947953 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) : (term399 A B x s f) = (term409 A B x s f).
Proof. exact (MK_COMB (@lem4947952 B) (@lem4947951 A B x s f)). Qed.
Lemma lem4947954 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) : ((term398 A B x s f) = (term399 A B x s f)) = ((term394 A B x s f) = (term409 A B x s f)).
Proof. exact (MK_COMB (@lem4947947 A B x s f) (@lem4947953 A B x s f)). Qed.
Lemma lem4947955 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) : (term394 A B x s f) = (term409 A B x s f).
Proof. exact (EQ_MP (@lem4947954 A B x s f) (@lem4947939 A B x s f)). Qed.
Lemma lem4947957 {A : Type'} (P : Prop) (Q : A -> Prop) : (term270 A P Q) = (term271 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4947958 {A : Type'} (P : Prop) (Q : A -> Prop) : (term270 A P Q) = (term271 A P Q).
Proof. exact (@lem4947957 A P Q). Qed.
Lemma lem4947959 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) : (term410 A B x y s f) = (term411 A B x y s f).
Proof. exact (@lem4947958 A (term328 A B x s f) (term374 A B y s f)). Qed.
Lemma lem4947960 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) (x : A) : (term412 A B y s f x) = (term373 A B y s f x).
Proof. exact (eq_refl (term412 A B y s f x)). Qed.
Lemma lem4947961 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : (term413 A B y s f) = (term374 A B y s f).
Proof. exact (fun_ext (fun x : A => @lem4947960 A B y s f x)). Qed.
Lemma lem4947962 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4947963 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : (term414 A B y s f) = (term375 A B y s f).
Proof. exact (MK_COMB (@lem4947962 A) (@lem4947961 A B y s f)). Qed.
Lemma lem4947964 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) : (term392 A B x s f) = (term392 A B x s f).
Proof. exact (eq_refl (term392 A B x s f)). Qed.
Lemma lem4947965 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) : (term410 A B x y s f) = (term406 A B x y s f).
Proof. exact (MK_COMB (@lem4947964 A B x s f) (@lem4947963 A B y s f)). Qed.
Lemma lem4947966 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4947967 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) : (term415 A B x y s f) = (term416 A B x y s f).
Proof. exact (MK_COMB (@lem4947966) (@lem4947965 A B x y s f)). Qed.
Lemma lem4947968 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) (x : A) : (term412 A B y s f x) = (term373 A B y s f x).
Proof. exact (eq_refl (term412 A B y s f x)). Qed.
Lemma lem4947969 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) : (term392 A B x s f) = (term392 A B x s f).
Proof. exact (eq_refl (term392 A B x s f)). Qed.
Lemma lem4947970 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) (x' : A) : (term417 A B x y s f x') = (term418 A B x y s f x').
Proof. exact (MK_COMB (@lem4947969 A B x s f) (@lem4947968 A B y s f x')). Qed.
Lemma lem4947971 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) : (term419 A B x y s f) = (term420 A B x y s f).
Proof. exact (fun_ext (fun x' : A => @lem4947970 A B x y s f x')). Qed.
Lemma lem4947972 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4947973 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) : (term411 A B x y s f) = (term421 A B x y s f).
Proof. exact (MK_COMB (@lem4947972 A) (@lem4947971 A B x y s f)). Qed.
Lemma lem4947974 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) : ((term410 A B x y s f) = (term411 A B x y s f)) = ((term406 A B x y s f) = (term421 A B x y s f)).
Proof. exact (MK_COMB (@lem4947967 A B x y s f) (@lem4947973 A B x y s f)). Qed.
Lemma lem4947975 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) : (term406 A B x y s f) = (term421 A B x y s f).
Proof. exact (EQ_MP (@lem4947974 A B x y s f) (@lem4947959 A B x y s f)). Qed.
Lemma lem4947977 {A : Type'} (P : Prop) (Q : A -> Prop) : (term270 A P Q) = (term271 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4947978 {A : Type'} (P : Prop) (Q : A -> Prop) : (term270 A P Q) = (term271 A P Q).
Proof. exact (@lem4947977 A P Q). Qed.
Lemma lem4947979 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) (x' : A) : (term422 A B x y s f x') = (term423 A B x y s f x').
Proof. exact (@lem4947978 A (term328 A B x s f) (term372 A B y s f x')). Qed.
Lemma lem4947980 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) (x : A) (y' : A) : (term424 A B y s f x y') = (term370 A B y s f x y').
Proof. exact (eq_refl (term424 A B y s f x y')). Qed.
Lemma lem4947981 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) (x : A) : (term425 A B y s f x) = (term372 A B y s f x).
Proof. exact (fun_ext (fun y' : A => @lem4947980 A B y s f x y')). Qed.
Lemma lem4947982 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4947983 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) (x : A) : (term426 A B y s f x) = (term373 A B y s f x).
Proof. exact (MK_COMB (@lem4947982 A) (@lem4947981 A B y s f x)). Qed.
Lemma lem4947984 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) : (term392 A B x s f) = (term392 A B x s f).
Proof. exact (eq_refl (term392 A B x s f)). Qed.
Lemma lem4947985 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) (x' : A) : (term422 A B x y s f x') = (term418 A B x y s f x').
Proof. exact (MK_COMB (@lem4947984 A B x s f) (@lem4947983 A B y s f x')). Qed.
Lemma lem4947986 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4947987 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) (x' : A) : (term427 A B x y s f x') = (term428 A B x y s f x').
Proof. exact (MK_COMB (@lem4947986) (@lem4947985 A B x y s f x')). Qed.
Lemma lem4947988 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) (x : A) (y' : A) : (term424 A B y s f x y') = (term370 A B y s f x y').
Proof. exact (eq_refl (term424 A B y s f x y')). Qed.
Lemma lem4947989 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) : (term392 A B x s f) = (term392 A B x s f).
Proof. exact (eq_refl (term392 A B x s f)). Qed.
Lemma lem4947990 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) (x' : A) (y' : A) : (term429 A B x y s f x' y') = (term430 A B x y s f x' y').
Proof. exact (MK_COMB (@lem4947989 A B x s f) (@lem4947988 A B y s f x' y')). Qed.
Lemma lem4947991 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) (x' : A) : (term431 A B x y s f x') = (term432 A B x y s f x').
Proof. exact (fun_ext (fun y' : A => @lem4947990 A B x y s f x' y')). Qed.
Lemma lem4947992 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4947993 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) (x' : A) : (term423 A B x y s f x') = (term433 A B x y s f x').
Proof. exact (MK_COMB (@lem4947992 A) (@lem4947991 A B x y s f x')). Qed.
Lemma lem4947994 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) (x' : A) : ((term422 A B x y s f x') = (term423 A B x y s f x')) = ((term418 A B x y s f x') = (term433 A B x y s f x')).
Proof. exact (MK_COMB (@lem4947987 A B x y s f x') (@lem4947993 A B x y s f x')). Qed.
Lemma lem4947995 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) (x' : A) : (term418 A B x y s f x') = (term433 A B x y s f x').
Proof. exact (EQ_MP (@lem4947994 A B x y s f x') (@lem4947979 A B x y s f x')). Qed.
Lemma lem4947996 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) : (term420 A B x y s f) = (term434 A B x y s f).
Proof. exact (fun_ext (fun x' : A => @lem4947995 A B x y s f x')). Qed.
Lemma lem4947997 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4947998 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) : (term421 A B x y s f) = (term435 A B x y s f).
Proof. exact (MK_COMB (@lem4947997 A) (@lem4947996 A B x y s f)). Qed.
Lemma lem4947999 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) : (term406 A B x y s f) = (term435 A B x y s f).
Proof. exact (TRANS (@lem4947975 A B x y s f) (@lem4947998 A B x y s f)). Qed.
Lemma lem4948000 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) : (term408 A B x s f) = (term436 A B x s f).
Proof. exact (fun_ext (fun y : B => @lem4947999 A B x y s f)). Qed.
Lemma lem4948001 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4948002 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) : (term409 A B x s f) = (term437 A B x s f).
Proof. exact (MK_COMB (@lem4948001 B) (@lem4948000 A B x s f)). Qed.
Lemma lem4948003 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) : (term394 A B x s f) = (term437 A B x s f).
Proof. exact (TRANS (@lem4947955 A B x s f) (@lem4948002 A B x s f)). Qed.
Lemma lem4948004 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term396 A B s f) = (term438 A B s f).
Proof. exact (fun_ext (fun x : B -> A => @lem4948003 A B x s f)). Qed.
Lemma lem4948005 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem4948006 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term397 A B s f) = (term439 A B s f).
Proof. exact (MK_COMB (@lem4948005 A B) (@lem4948004 A B s f)). Qed.
Lemma lem4948007 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term378 A B s f) = (term439 A B s f).
Proof. exact (TRANS (@lem4947935 A B s f) (@lem4948006 A B s f)). Qed.
Lemma lem4948008 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term265 A B s f) = (term439 A B s f).
Proof. exact (TRANS (@lem4947909 A B s f) (@lem4948007 A B s f)). Qed.
Lemma lem4948009 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4948010 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term267 A B s f) = (term440 A B s f).
Proof. exact (MK_COMB (@lem4948009) (@lem4948008 A B s f)). Qed.
Lemma lem4948011 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term251 A B s f) = (term251 A B s f).
Proof. exact (eq_refl (term251 A B s f)). Qed.
Lemma lem4948012 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term269 A B s f) = (term441 A B s f).
Proof. exact (MK_COMB (@lem4948010 A B s f) (@lem4948011 A B s f)). Qed.
Lemma lem4948014 {A : Type'} (P : A -> Prop) (Q : Prop) : (term313 A P Q) = (term314 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4948015 {A B : Type'} (P : type805 A B) (Q : Prop) : (term315 A B P Q) = (term316 A B P Q).
Proof. exact (@lem4948014 (B -> A) P Q). Qed.
Lemma lem4948016 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term442 A B s f) = (term443 A B s f).
Proof. exact (@lem4948015 A B (term438 A B s f) (term251 A B s f)). Qed.
Lemma lem4948017 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) : (term444 A B s f x) = (term437 A B x s f).
Proof. exact (eq_refl (term444 A B s f x)). Qed.
Lemma lem4948018 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term445 A B s f) = (term438 A B s f).
Proof. exact (fun_ext (fun x : B -> A => @lem4948017 A B x s f)). Qed.
Lemma lem4948019 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem4948020 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term446 A B s f) = (term439 A B s f).
Proof. exact (MK_COMB (@lem4948019 A B) (@lem4948018 A B s f)). Qed.
Lemma lem4948021 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4948022 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term447 A B s f) = (term440 A B s f).
Proof. exact (MK_COMB (@lem4948021) (@lem4948020 A B s f)). Qed.
Lemma lem4948023 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term251 A B s f) = (term251 A B s f).
Proof. exact (eq_refl (term251 A B s f)). Qed.
Lemma lem4948024 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term442 A B s f) = (term441 A B s f).
Proof. exact (MK_COMB (@lem4948022 A B s f) (@lem4948023 A B s f)). Qed.
Lemma lem4948025 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4948026 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term448 A B s f) = (term449 A B s f).
Proof. exact (MK_COMB (@lem4948025) (@lem4948024 A B s f)). Qed.
Lemma lem4948027 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) : (term444 A B s f x) = (term437 A B x s f).
Proof. exact (eq_refl (term444 A B s f x)). Qed.
Lemma lem4948028 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4948029 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) : (term450 A B s f x) = (term451 A B x s f).
Proof. exact (MK_COMB (@lem4948028) (@lem4948027 A B x s f)). Qed.
Lemma lem4948030 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term251 A B s f) = (term251 A B s f).
Proof. exact (eq_refl (term251 A B s f)). Qed.
Lemma lem4948031 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) : (term452 A B x s f) = (term453 A B x s f).
Proof. exact (MK_COMB (@lem4948029 A B x s f) (@lem4948030 A B s f)). Qed.
Lemma lem4948032 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term454 A B s f) = (term455 A B s f).
Proof. exact (fun_ext (fun x : B -> A => @lem4948031 A B x s f)). Qed.
Lemma lem4948033 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem4948034 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term443 A B s f) = (term456 A B s f).
Proof. exact (MK_COMB (@lem4948033 A B) (@lem4948032 A B s f)). Qed.
Lemma lem4948035 {A B : Type'} (s : A -> Prop) (f : A -> B) : ((term442 A B s f) = (term443 A B s f)) = ((term441 A B s f) = (term456 A B s f)).
Proof. exact (MK_COMB (@lem4948026 A B s f) (@lem4948034 A B s f)). Qed.
Lemma lem4948036 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term441 A B s f) = (term456 A B s f).
Proof. exact (EQ_MP (@lem4948035 A B s f) (@lem4948016 A B s f)). Qed.
Lemma lem4948038 {A : Type'} (P : A -> Prop) (Q : Prop) : (term313 A P Q) = (term314 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4948039 {B : Type'} (P : B -> Prop) (Q : Prop) : (term313 B P Q) = (term314 B P Q).
Proof. exact (@lem4948038 B P Q). Qed.
Lemma lem4948040 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) : (term457 A B x s f) = (term458 A B x s f).
Proof. exact (@lem4948039 B (term436 A B x s f) (term251 A B s f)). Qed.
Lemma lem4948041 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) : (term459 A B x s f y) = (term435 A B x y s f).
Proof. exact (eq_refl (term459 A B x s f y)). Qed.
Lemma lem4948042 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) : (term460 A B x s f) = (term436 A B x s f).
Proof. exact (fun_ext (fun y : B => @lem4948041 A B x y s f)). Qed.
Lemma lem4948043 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4948044 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) : (term461 A B x s f) = (term437 A B x s f).
Proof. exact (MK_COMB (@lem4948043 B) (@lem4948042 A B x s f)). Qed.
Lemma lem4948045 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4948046 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) : (term462 A B x s f) = (term451 A B x s f).
Proof. exact (MK_COMB (@lem4948045) (@lem4948044 A B x s f)). Qed.
Lemma lem4948047 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term251 A B s f) = (term251 A B s f).
Proof. exact (eq_refl (term251 A B s f)). Qed.
Lemma lem4948048 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) : (term457 A B x s f) = (term453 A B x s f).
Proof. exact (MK_COMB (@lem4948046 A B x s f) (@lem4948047 A B s f)). Qed.
Lemma lem4948049 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4948050 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) : (term463 A B x s f) = (term464 A B x s f).
Proof. exact (MK_COMB (@lem4948049) (@lem4948048 A B x s f)). Qed.
Lemma lem4948051 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) : (term459 A B x s f y) = (term435 A B x y s f).
Proof. exact (eq_refl (term459 A B x s f y)). Qed.
Lemma lem4948052 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4948053 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) : (term465 A B x s f y) = (term466 A B x y s f).
Proof. exact (MK_COMB (@lem4948052) (@lem4948051 A B x y s f)). Qed.
Lemma lem4948054 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term251 A B s f) = (term251 A B s f).
Proof. exact (eq_refl (term251 A B s f)). Qed.
Lemma lem4948055 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) : (term467 A B x y s f) = (term468 A B x y s f).
Proof. exact (MK_COMB (@lem4948053 A B x y s f) (@lem4948054 A B s f)). Qed.
Lemma lem4948056 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) : (term469 A B x s f) = (term470 A B x s f).
Proof. exact (fun_ext (fun y : B => @lem4948055 A B x y s f)). Qed.
Lemma lem4948057 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4948058 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) : (term458 A B x s f) = (term471 A B x s f).
Proof. exact (MK_COMB (@lem4948057 B) (@lem4948056 A B x s f)). Qed.
Lemma lem4948059 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) : ((term457 A B x s f) = (term458 A B x s f)) = ((term453 A B x s f) = (term471 A B x s f)).
Proof. exact (MK_COMB (@lem4948050 A B x s f) (@lem4948058 A B x s f)). Qed.
Lemma lem4948060 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) : (term453 A B x s f) = (term471 A B x s f).
Proof. exact (EQ_MP (@lem4948059 A B x s f) (@lem4948040 A B x s f)). Qed.
Lemma lem4948062 {A : Type'} (P : A -> Prop) (Q : Prop) : (term313 A P Q) = (term314 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4948063 {A : Type'} (P : A -> Prop) (Q : Prop) : (term313 A P Q) = (term314 A P Q).
Proof. exact (@lem4948062 A P Q). Qed.
Lemma lem4948064 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) : (term472 A B x y s f) = (term473 A B x y s f).
Proof. exact (@lem4948063 A (term434 A B x y s f) (term251 A B s f)). Qed.
Lemma lem4948065 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) (x' : A) : (term474 A B x y s f x') = (term433 A B x y s f x').
Proof. exact (eq_refl (term474 A B x y s f x')). Qed.
Lemma lem4948066 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) : (term475 A B x y s f) = (term434 A B x y s f).
Proof. exact (fun_ext (fun x' : A => @lem4948065 A B x y s f x')). Qed.
Lemma lem4948067 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4948068 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) : (term476 A B x y s f) = (term435 A B x y s f).
Proof. exact (MK_COMB (@lem4948067 A) (@lem4948066 A B x y s f)). Qed.
Lemma lem4948069 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4948070 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) : (term477 A B x y s f) = (term466 A B x y s f).
Proof. exact (MK_COMB (@lem4948069) (@lem4948068 A B x y s f)). Qed.
Lemma lem4948071 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term251 A B s f) = (term251 A B s f).
Proof. exact (eq_refl (term251 A B s f)). Qed.
Lemma lem4948072 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) : (term472 A B x y s f) = (term468 A B x y s f).
Proof. exact (MK_COMB (@lem4948070 A B x y s f) (@lem4948071 A B s f)). Qed.
Lemma lem4948073 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4948074 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) : (term478 A B x y s f) = (term479 A B x y s f).
Proof. exact (MK_COMB (@lem4948073) (@lem4948072 A B x y s f)). Qed.
Lemma lem4948075 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) (x' : A) : (term474 A B x y s f x') = (term433 A B x y s f x').
Proof. exact (eq_refl (term474 A B x y s f x')). Qed.
Lemma lem4948076 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4948077 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) (x' : A) : (term480 A B x y s f x') = (term481 A B x y s f x').
Proof. exact (MK_COMB (@lem4948076) (@lem4948075 A B x y s f x')). Qed.
Lemma lem4948078 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term251 A B s f) = (term251 A B s f).
Proof. exact (eq_refl (term251 A B s f)). Qed.
Lemma lem4948079 {A B : Type'} (x : B -> A) (y : B) (x' : A) (s : A -> Prop) (f : A -> B) : (term482 A B x y x' s f) = (term483 A B x y x' s f).
Proof. exact (MK_COMB (@lem4948077 A B x y s f x') (@lem4948078 A B s f)). Qed.
Lemma lem4948080 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) : (term484 A B x y s f) = (term485 A B x y s f).
Proof. exact (fun_ext (fun x' : A => @lem4948079 A B x y x' s f)). Qed.
Lemma lem4948081 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4948082 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) : (term473 A B x y s f) = (term486 A B x y s f).
Proof. exact (MK_COMB (@lem4948081 A) (@lem4948080 A B x y s f)). Qed.
Lemma lem4948083 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) : ((term472 A B x y s f) = (term473 A B x y s f)) = ((term468 A B x y s f) = (term486 A B x y s f)).
Proof. exact (MK_COMB (@lem4948074 A B x y s f) (@lem4948082 A B x y s f)). Qed.
Lemma lem4948084 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) : (term468 A B x y s f) = (term486 A B x y s f).
Proof. exact (EQ_MP (@lem4948083 A B x y s f) (@lem4948064 A B x y s f)). Qed.
Lemma lem4948086 {A : Type'} (P : A -> Prop) (Q : Prop) : (term313 A P Q) = (term314 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4948087 {A : Type'} (P : A -> Prop) (Q : Prop) : (term313 A P Q) = (term314 A P Q).
Proof. exact (@lem4948086 A P Q). Qed.
Lemma lem4948088 {A B : Type'} (x : B -> A) (y : B) (x' : A) (s : A -> Prop) (f : A -> B) : (term487 A B x y x' s f) = (term488 A B x y x' s f).
Proof. exact (@lem4948087 A (term432 A B x y s f x') (term251 A B s f)). Qed.
Lemma lem4948089 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) (x' : A) (y' : A) : (term489 A B x y s f x' y') = (term430 A B x y s f x' y').
Proof. exact (eq_refl (term489 A B x y s f x' y')). Qed.
Lemma lem4948090 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) (x' : A) : (term490 A B x y s f x') = (term432 A B x y s f x').
Proof. exact (fun_ext (fun y' : A => @lem4948089 A B x y s f x' y')). Qed.
Lemma lem4948091 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4948092 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) (x' : A) : (term491 A B x y s f x') = (term433 A B x y s f x').
Proof. exact (MK_COMB (@lem4948091 A) (@lem4948090 A B x y s f x')). Qed.
Lemma lem4948093 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4948094 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) (x' : A) : (term492 A B x y s f x') = (term481 A B x y s f x').
Proof. exact (MK_COMB (@lem4948093) (@lem4948092 A B x y s f x')). Qed.
Lemma lem4948095 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term251 A B s f) = (term251 A B s f).
Proof. exact (eq_refl (term251 A B s f)). Qed.
Lemma lem4948096 {A B : Type'} (x : B -> A) (y : B) (x' : A) (s : A -> Prop) (f : A -> B) : (term487 A B x y x' s f) = (term483 A B x y x' s f).
Proof. exact (MK_COMB (@lem4948094 A B x y s f x') (@lem4948095 A B s f)). Qed.
Lemma lem4948097 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4948098 {A B : Type'} (x : B -> A) (y : B) (x' : A) (s : A -> Prop) (f : A -> B) : (term493 A B x y x' s f) = (term494 A B x y x' s f).
Proof. exact (MK_COMB (@lem4948097) (@lem4948096 A B x y x' s f)). Qed.
Lemma lem4948099 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) (x' : A) (y' : A) : (term489 A B x y s f x' y') = (term430 A B x y s f x' y').
Proof. exact (eq_refl (term489 A B x y s f x' y')). Qed.
Lemma lem4948100 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4948101 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) (x' : A) (y' : A) : (term495 A B x y s f x' y') = (term496 A B x y s f x' y').
Proof. exact (MK_COMB (@lem4948100) (@lem4948099 A B x y s f x' y')). Qed.
Lemma lem4948102 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term251 A B s f) = (term251 A B s f).
Proof. exact (eq_refl (term251 A B s f)). Qed.
Lemma lem4948103 {A B : Type'} (x : B -> A) (y : B) (x' : A) (y' : A) (s : A -> Prop) (f : A -> B) : (term497 A B x y x' y' s f) = (term498 A B x y x' y' s f).
Proof. exact (MK_COMB (@lem4948101 A B x y s f x' y') (@lem4948102 A B s f)). Qed.
Lemma lem4948104 {A B : Type'} (x : B -> A) (y : B) (x' : A) (s : A -> Prop) (f : A -> B) : (term499 A B x y x' s f) = (term500 A B x y x' s f).
Proof. exact (fun_ext (fun y' : A => @lem4948103 A B x y x' y' s f)). Qed.
Lemma lem4948105 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4948106 {A B : Type'} (x : B -> A) (y : B) (x' : A) (s : A -> Prop) (f : A -> B) : (term488 A B x y x' s f) = (term501 A B x y x' s f).
Proof. exact (MK_COMB (@lem4948105 A) (@lem4948104 A B x y x' s f)). Qed.
Lemma lem4948107 {A B : Type'} (x : B -> A) (y : B) (x' : A) (s : A -> Prop) (f : A -> B) : ((term487 A B x y x' s f) = (term488 A B x y x' s f)) = ((term483 A B x y x' s f) = (term501 A B x y x' s f)).
Proof. exact (MK_COMB (@lem4948098 A B x y x' s f) (@lem4948106 A B x y x' s f)). Qed.
Lemma lem4948108 {A B : Type'} (x : B -> A) (y : B) (x' : A) (s : A -> Prop) (f : A -> B) : (term483 A B x y x' s f) = (term501 A B x y x' s f).
Proof. exact (EQ_MP (@lem4948107 A B x y x' s f) (@lem4948088 A B x y x' s f)). Qed.
Lemma lem4948110 {A : Type'} (P : Prop) (Q : A -> Prop) : (term348 A P Q) = (term349 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4948111 {A : Type'} (P : Prop) (Q : A -> Prop) : (term348 A P Q) = (term349 A P Q).
Proof. exact (@lem4948110 A P Q). Qed.
Lemma lem4948112 {A B : Type'} (x : B -> A) (y : B) (x' : A) (y' : A) (s : A -> Prop) (f : A -> B) : (term502 A B x y x' y' s f) = (term503 A B x y x' y' s f).
Proof. exact (@lem4948111 A (term430 A B x y s f x' y') (term250 A B s f)). Qed.
Lemma lem4948113 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term352 A B s f x) = (term242 A B s f x).
Proof. exact (eq_refl (term352 A B s f x)). Qed.
Lemma lem4948114 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term353 A B s f) = (term250 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4948113 A B s f x)). Qed.
Lemma lem4948115 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4948116 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term354 A B s f) = (term251 A B s f).
Proof. exact (MK_COMB (@lem4948115 A) (@lem4948114 A B s f)). Qed.
Lemma lem4948117 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) (x' : A) (y' : A) : (term496 A B x y s f x' y') = (term496 A B x y s f x' y').
Proof. exact (eq_refl (term496 A B x y s f x' y')). Qed.
Lemma lem4948118 {A B : Type'} (x : B -> A) (y : B) (x' : A) (y' : A) (s : A -> Prop) (f : A -> B) : (term502 A B x y x' y' s f) = (term498 A B x y x' y' s f).
Proof. exact (MK_COMB (@lem4948117 A B x y s f x' y') (@lem4948116 A B s f)). Qed.
Lemma lem4948119 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4948120 {A B : Type'} (x : B -> A) (y : B) (x' : A) (y' : A) (s : A -> Prop) (f : A -> B) : (term504 A B x y x' y' s f) = (term505 A B x y x' y' s f).
Proof. exact (MK_COMB (@lem4948119) (@lem4948118 A B x y x' y' s f)). Qed.
Lemma lem4948121 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) : (term352 A B s f x') = (term242 A B s f x').
Proof. exact (eq_refl (term352 A B s f x')). Qed.
Lemma lem4948122 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) (x' : A) (y' : A) : (term496 A B x y s f x' y') = (term496 A B x y s f x' y').
Proof. exact (eq_refl (term496 A B x y s f x' y')). Qed.
Lemma lem4948123 {A B : Type'} (x : B -> A) (y : B) (x' : A) (y' : A) (s : A -> Prop) (f : A -> B) (x'' : A) : (term506 A B x y x' y' s f x'') = (term507 A B x y x' y' s f x'').
Proof. exact (MK_COMB (@lem4948122 A B x y s f x' y') (@lem4948121 A B s f x'')). Qed.
Lemma lem4948124 {A B : Type'} (x : B -> A) (y : B) (x' : A) (y' : A) (s : A -> Prop) (f : A -> B) : (term508 A B x y x' y' s f) = (term509 A B x y x' y' s f).
Proof. exact (fun_ext (fun x'' : A => @lem4948123 A B x y x' y' s f x'')). Qed.
Lemma lem4948125 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4948126 {A B : Type'} (x : B -> A) (y : B) (x' : A) (y' : A) (s : A -> Prop) (f : A -> B) : (term503 A B x y x' y' s f) = (term510 A B x y x' y' s f).
Proof. exact (MK_COMB (@lem4948125 A) (@lem4948124 A B x y x' y' s f)). Qed.
Lemma lem4948127 {A B : Type'} (x : B -> A) (y : B) (x' : A) (y' : A) (s : A -> Prop) (f : A -> B) : ((term502 A B x y x' y' s f) = (term503 A B x y x' y' s f)) = ((term498 A B x y x' y' s f) = (term510 A B x y x' y' s f)).
Proof. exact (MK_COMB (@lem4948120 A B x y x' y' s f) (@lem4948126 A B x y x' y' s f)). Qed.
Lemma lem4948128 {A B : Type'} (x : B -> A) (y : B) (x' : A) (y' : A) (s : A -> Prop) (f : A -> B) : (term498 A B x y x' y' s f) = (term510 A B x y x' y' s f).
Proof. exact (EQ_MP (@lem4948127 A B x y x' y' s f) (@lem4948112 A B x y x' y' s f)). Qed.
Lemma lem4948130 {A : Type'} (P : Prop) (Q : A -> Prop) : (term348 A P Q) = (term349 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4948131 {A : Type'} (P : Prop) (Q : A -> Prop) : (term348 A P Q) = (term349 A P Q).
Proof. exact (@lem4948130 A P Q). Qed.
Lemma lem4948132 {A B : Type'} (x : B -> A) (y : B) (x' : A) (y' : A) (s : A -> Prop) (f : A -> B) (x'' : A) : (term511 A B x y x' y' s f x'') = (term512 A B x y x' y' s f x'').
Proof. exact (@lem4948131 A (term430 A B x y s f x' y') (term241 A B s f x'')). Qed.
Lemma lem4948133 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (y : A) : (term364 A B s f x' y) = (term230 A B s f x' y).
Proof. exact (eq_refl (term364 A B s f x' y)). Qed.
Lemma lem4948134 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) : (term365 A B s f x') = (term241 A B s f x').
Proof. exact (fun_ext (fun y : A => @lem4948133 A B s f x' y)). Qed.
Lemma lem4948135 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4948136 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) : (term366 A B s f x') = (term242 A B s f x').
Proof. exact (MK_COMB (@lem4948135 A) (@lem4948134 A B s f x')). Qed.
Lemma lem4948137 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) (x' : A) (y' : A) : (term496 A B x y s f x' y') = (term496 A B x y s f x' y').
Proof. exact (eq_refl (term496 A B x y s f x' y')). Qed.
Lemma lem4948138 {A B : Type'} (x : B -> A) (y : B) (x' : A) (y' : A) (s : A -> Prop) (f : A -> B) (x'' : A) : (term511 A B x y x' y' s f x'') = (term507 A B x y x' y' s f x'').
Proof. exact (MK_COMB (@lem4948137 A B x y s f x' y') (@lem4948136 A B s f x'')). Qed.
Lemma lem4948139 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4948140 {A B : Type'} (x : B -> A) (y : B) (x' : A) (y' : A) (s : A -> Prop) (f : A -> B) (x'' : A) : (term513 A B x y x' y' s f x'') = (term514 A B x y x' y' s f x'').
Proof. exact (MK_COMB (@lem4948139) (@lem4948138 A B x y x' y' s f x'')). Qed.
Lemma lem4948141 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (y' : A) : (term364 A B s f x' y') = (term230 A B s f x' y').
Proof. exact (eq_refl (term364 A B s f x' y')). Qed.
Lemma lem4948142 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) (x' : A) (y' : A) : (term496 A B x y s f x' y') = (term496 A B x y s f x' y').
Proof. exact (eq_refl (term496 A B x y s f x' y')). Qed.
Lemma lem4948143 {A B : Type'} (x : B -> A) (y : B) (x' : A) (y' : A) (s : A -> Prop) (f : A -> B) (x'' : A) (y'' : A) : (term515 A B x y x' y' s f x'' y'') = (term516 A B x y x' y' s f x'' y'').
Proof. exact (MK_COMB (@lem4948142 A B x y s f x' y') (@lem4948141 A B s f x'' y'')). Qed.
Lemma lem4948144 {A B : Type'} (x : B -> A) (y : B) (x' : A) (y' : A) (s : A -> Prop) (f : A -> B) (x'' : A) : (term517 A B x y x' y' s f x'') = (term518 A B x y x' y' s f x'').
Proof. exact (fun_ext (fun y'' : A => @lem4948143 A B x y x' y' s f x'' y'')). Qed.
Lemma lem4948145 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4948146 {A B : Type'} (x : B -> A) (y : B) (x' : A) (y' : A) (s : A -> Prop) (f : A -> B) (x'' : A) : (term512 A B x y x' y' s f x'') = (term519 A B x y x' y' s f x'').
Proof. exact (MK_COMB (@lem4948145 A) (@lem4948144 A B x y x' y' s f x'')). Qed.
Lemma lem4948147 {A B : Type'} (x : B -> A) (y : B) (x' : A) (y' : A) (s : A -> Prop) (f : A -> B) (x'' : A) : ((term511 A B x y x' y' s f x'') = (term512 A B x y x' y' s f x'')) = ((term507 A B x y x' y' s f x'') = (term519 A B x y x' y' s f x'')).
Proof. exact (MK_COMB (@lem4948140 A B x y x' y' s f x'') (@lem4948146 A B x y x' y' s f x'')). Qed.
Lemma lem4948148 {A B : Type'} (x : B -> A) (y : B) (x' : A) (y' : A) (s : A -> Prop) (f : A -> B) (x'' : A) : (term507 A B x y x' y' s f x'') = (term519 A B x y x' y' s f x'').
Proof. exact (EQ_MP (@lem4948147 A B x y x' y' s f x'') (@lem4948132 A B x y x' y' s f x'')). Qed.
Lemma lem4948149 {A B : Type'} (x : B -> A) (y : B) (x' : A) (y' : A) (s : A -> Prop) (f : A -> B) : (term509 A B x y x' y' s f) = (term520 A B x y x' y' s f).
Proof. exact (fun_ext (fun x'' : A => @lem4948148 A B x y x' y' s f x'')). Qed.
Lemma lem4948150 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4948151 {A B : Type'} (x : B -> A) (y : B) (x' : A) (y' : A) (s : A -> Prop) (f : A -> B) : (term510 A B x y x' y' s f) = (term521 A B x y x' y' s f).
Proof. exact (MK_COMB (@lem4948150 A) (@lem4948149 A B x y x' y' s f)). Qed.
Lemma lem4948152 {A B : Type'} (x : B -> A) (y : B) (x' : A) (y' : A) (s : A -> Prop) (f : A -> B) : (term498 A B x y x' y' s f) = (term521 A B x y x' y' s f).
Proof. exact (TRANS (@lem4948128 A B x y x' y' s f) (@lem4948151 A B x y x' y' s f)). Qed.
Lemma lem4948153 {A B : Type'} (x : B -> A) (y : B) (x' : A) (s : A -> Prop) (f : A -> B) : (term500 A B x y x' s f) = (term522 A B x y x' s f).
Proof. exact (fun_ext (fun y' : A => @lem4948152 A B x y x' y' s f)). Qed.
Lemma lem4948154 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4948155 {A B : Type'} (x : B -> A) (y : B) (x' : A) (s : A -> Prop) (f : A -> B) : (term501 A B x y x' s f) = (term523 A B x y x' s f).
Proof. exact (MK_COMB (@lem4948154 A) (@lem4948153 A B x y x' s f)). Qed.
Lemma lem4948156 {A B : Type'} (x : B -> A) (y : B) (x' : A) (s : A -> Prop) (f : A -> B) : (term483 A B x y x' s f) = (term523 A B x y x' s f).
Proof. exact (TRANS (@lem4948108 A B x y x' s f) (@lem4948155 A B x y x' s f)). Qed.
Lemma lem4948157 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) : (term485 A B x y s f) = (term524 A B x y s f).
Proof. exact (fun_ext (fun x' : A => @lem4948156 A B x y x' s f)). Qed.
Lemma lem4948158 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4948159 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) : (term486 A B x y s f) = (term525 A B x y s f).
Proof. exact (MK_COMB (@lem4948158 A) (@lem4948157 A B x y s f)). Qed.
Lemma lem4948160 {A B : Type'} (x : B -> A) (y : B) (s : A -> Prop) (f : A -> B) : (term468 A B x y s f) = (term525 A B x y s f).
Proof. exact (TRANS (@lem4948084 A B x y s f) (@lem4948159 A B x y s f)). Qed.
Lemma lem4948161 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) : (term470 A B x s f) = (term526 A B x s f).
Proof. exact (fun_ext (fun y : B => @lem4948160 A B x y s f)). Qed.
Lemma lem4948162 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4948163 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) : (term471 A B x s f) = (term527 A B x s f).
Proof. exact (MK_COMB (@lem4948162 B) (@lem4948161 A B x s f)). Qed.
Lemma lem4948164 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) : (term453 A B x s f) = (term527 A B x s f).
Proof. exact (TRANS (@lem4948060 A B x s f) (@lem4948163 A B x s f)). Qed.
Lemma lem4948165 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term455 A B s f) = (term528 A B s f).
Proof. exact (fun_ext (fun x : B -> A => @lem4948164 A B x s f)). Qed.
Lemma lem4948166 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem4948167 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term456 A B s f) = (term529 A B s f).
Proof. exact (MK_COMB (@lem4948166 A B) (@lem4948165 A B s f)). Qed.
Lemma lem4948168 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term441 A B s f) = (term529 A B s f).
Proof. exact (TRANS (@lem4948036 A B s f) (@lem4948167 A B s f)). Qed.
Lemma lem4948170 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term269 A B s f) = (term529 A B s f).
Proof. exact (TRANS (@lem4948012 A B s f) (@lem4948168 A B s f)). Qed.
Lemma lem4948171 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term81 A B s f) = (term529 A B s f).
Proof. exact (TRANS (@lem4947402 A B s f) (@lem4948170 A B s f)). Qed.
Lemma lem4948172 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term81 A B s f) : term529 A B s f.
Proof. exact (EQ_MP (@lem4948171 A B s f) (@lem4947219 A B s f h1)). Qed.
Lemma lem4948183 {A : Type'} (y : A) (f : A -> A) (x : A) (s : A -> Prop) : (term530 A y f x s) = (term531 A y f x s).
Proof. exact (@lem17045 (y = (f x)) (@IN A x s)). Qed.
Lemma lem4948186 {A : Type'} (y : A) (f : A -> A) (x : A) (s : A -> Prop) : (term167 A y f x s) = (term167 A y f x s).
Proof. exact (eq_refl (term167 A y f x s)). Qed.
Lemma lem4948187 {A : Type'} (P : A -> Prop) : (term196 A P) = (term197 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem4948188 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term532 A y f s) = (term533 A y f s).
Proof. exact (@lem4948187 A (term168 A y f s)). Qed.
Lemma lem4948189 {A : Type'} (y : A) (f : A -> A) (x : A) (s : A -> Prop) : (term534 A y f s x) = (term167 A y f x s).
Proof. exact (eq_refl (term534 A y f s x)). Qed.
Lemma lem4948190 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4948191 {A : Type'} (y : A) (f : A -> A) (x : A) (s : A -> Prop) : (term535 A y f s x) = (term530 A y f x s).
Proof. exact (MK_COMB (@lem4948190) (@lem4948189 A y f x s)). Qed.
Lemma lem4948192 {A : Type'} (y : A) (f : A -> A) (x : A) (s : A -> Prop) : (term535 A y f s x) = (term531 A y f x s).
Proof. exact (TRANS (@lem4948191 A y f x s) (@lem4948183 A y f x s)). Qed.
Lemma lem4948193 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term536 A y f s) = (term537 A y f s).
Proof. exact (fun_ext (fun x : A => @lem4948192 A y f x s)). Qed.
Lemma lem4948194 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4948195 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term533 A y f s) = (term538 A y f s).
Proof. exact (MK_COMB (@lem4948194 A) (@lem4948193 A y f s)). Qed.
Lemma lem4948196 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term532 A y f s) = (term538 A y f s).
Proof. exact (TRANS (@lem4948188 A y f s) (@lem4948195 A y f s)). Qed.
Lemma lem4948197 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term168 A y f s) = (term168 A y f s).
Proof. exact (fun_ext (fun x : A => @lem4948186 A y f x s)). Qed.
Lemma lem4948198 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4948199 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term169 A y f s) = (term169 A y f s).
Proof. exact (MK_COMB (@lem4948198 A) (@lem4948197 A y f s)). Qed.
Lemma lem4948201 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term539 A y f s) = (term539 A y f s).
Proof. exact (eq_refl (term539 A y f s)). Qed.
Lemma lem4948202 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term540 A y f s) = (term540 A y f s).
Proof. exact (MK_COMB (@lem4948201 A y f s) (@lem4948199 A y f s)). Qed.
Lemma lem4948204 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term541 A y f s) = (term541 A y f s).
Proof. exact (eq_refl (term541 A y f s)). Qed.
Lemma lem4948205 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term542 A y f s) = (term543 A y f s).
Proof. exact (MK_COMB (@lem4948204 A y f s) (@lem4948196 A y f s)). Qed.
Lemma lem4948206 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4948207 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term544 A y f s) = (term545 A y f s).
Proof. exact (MK_COMB (@lem4948206) (@lem4948205 A y f s)). Qed.
Lemma lem4948208 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term546 A y f s) = (term547 A y f s).
Proof. exact (MK_COMB (@lem4948207 A y f s) (@lem4948202 A y f s)). Qed.
Lemma lem4948209 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : ((term171 A y f s) = (term169 A y f s)) = (term546 A y f s).
Proof. exact (@lem17784 (term171 A y f s) (term169 A y f s)). Qed.
Lemma lem4948210 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : ((term171 A y f s) = (term169 A y f s)) = (term547 A y f s).
Proof. exact (TRANS (@lem4948209 A y f s) (@lem4948208 A y f s)). Qed.
Lemma lem4948211 {A : Type'} (y : A) (s : A -> Prop) : (term172 A y s) = (term548 A y s).
Proof. exact (fun_ext (fun f : A -> A => @lem4948210 A y f s)). Qed.
Lemma lem4948212 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem4948213 {A : Type'} (y : A) (s : A -> Prop) : (term173 A y s) = (term549 A y s).
Proof. exact (MK_COMB (@lem4948212 A) (@lem4948211 A y s)). Qed.
Lemma lem4948214 {A : Type'} (y : A) : (term174 A y) = (term550 A y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4948213 A y s)). Qed.
Lemma lem4948215 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4948216 {A : Type'} (y : A) : (term175 A y) = (term551 A y).
Proof. exact (MK_COMB (@lem4948215 A) (@lem4948214 A y)). Qed.
Lemma lem4948217 {A : Type'} : (term176 A) = (term552 A).
Proof. exact (fun_ext (fun y : A => @lem4948216 A y)). Qed.
Lemma lem4948218 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4948219 {A : Type'} : (term84 A) = (term553 A).
Proof. exact (MK_COMB (@lem4948218 A) (@lem4948217 A)). Qed.
Lemma lem4948229 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term554 A P Q) = (term555 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4948230 {A : Type'} (P : type488 A) (Q : type488 A) : (term556 A P Q) = (term557 A P Q).
Proof. exact (@lem4948229 (A -> A) P Q). Qed.
Lemma lem4948231 {A : Type'} (y : A) (s : A -> Prop) : (term558 A y s) = (term559 A y s).
Proof. exact (@lem4948230 A (term560 A y s) (term561 A y s)). Qed.
Lemma lem4948232 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term562 A y s f) = (term543 A y f s).
Proof. exact (eq_refl (term562 A y s f)). Qed.
Lemma lem4948233 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4948234 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term563 A y s f) = (term545 A y f s).
Proof. exact (MK_COMB (@lem4948233) (@lem4948232 A y f s)). Qed.
Lemma lem4948235 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term564 A y s f) = (term540 A y f s).
Proof. exact (eq_refl (term564 A y s f)). Qed.
Lemma lem4948236 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term565 A y s f) = (term547 A y f s).
Proof. exact (MK_COMB (@lem4948234 A y f s) (@lem4948235 A y f s)). Qed.
Lemma lem4948237 {A : Type'} (y : A) (s : A -> Prop) : (term566 A y s) = (term548 A y s).
Proof. exact (fun_ext (fun f : A -> A => @lem4948236 A y f s)). Qed.
Lemma lem4948238 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem4948239 {A : Type'} (y : A) (s : A -> Prop) : (term558 A y s) = (term549 A y s).
Proof. exact (MK_COMB (@lem4948238 A) (@lem4948237 A y s)). Qed.
Lemma lem4948240 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4948241 {A : Type'} (y : A) (s : A -> Prop) : (term567 A y s) = (term568 A y s).
Proof. exact (MK_COMB (@lem4948240) (@lem4948239 A y s)). Qed.
Lemma lem4948242 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term562 A y s f) = (term543 A y f s).
Proof. exact (eq_refl (term562 A y s f)). Qed.
Lemma lem4948243 {A : Type'} (y : A) (s : A -> Prop) : (term569 A y s) = (term560 A y s).
Proof. exact (fun_ext (fun f : A -> A => @lem4948242 A y f s)). Qed.
Lemma lem4948244 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem4948245 {A : Type'} (y : A) (s : A -> Prop) : (term570 A y s) = (term571 A y s).
Proof. exact (MK_COMB (@lem4948244 A) (@lem4948243 A y s)). Qed.
Lemma lem4948246 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4948247 {A : Type'} (y : A) (s : A -> Prop) : (term572 A y s) = (term573 A y s).
Proof. exact (MK_COMB (@lem4948246) (@lem4948245 A y s)). Qed.
Lemma lem4948248 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term564 A y s f) = (term540 A y f s).
Proof. exact (eq_refl (term564 A y s f)). Qed.
Lemma lem4948249 {A : Type'} (y : A) (s : A -> Prop) : (term574 A y s) = (term561 A y s).
Proof. exact (fun_ext (fun f : A -> A => @lem4948248 A y f s)). Qed.
Lemma lem4948250 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem4948251 {A : Type'} (y : A) (s : A -> Prop) : (term575 A y s) = (term576 A y s).
Proof. exact (MK_COMB (@lem4948250 A) (@lem4948249 A y s)). Qed.
Lemma lem4948252 {A : Type'} (y : A) (s : A -> Prop) : (term559 A y s) = (term577 A y s).
Proof. exact (MK_COMB (@lem4948247 A y s) (@lem4948251 A y s)). Qed.
Lemma lem4948253 {A : Type'} (y : A) (s : A -> Prop) : ((term558 A y s) = (term559 A y s)) = ((term549 A y s) = (term577 A y s)).
Proof. exact (MK_COMB (@lem4948241 A y s) (@lem4948252 A y s)). Qed.
Lemma lem4948254 {A : Type'} (y : A) (s : A -> Prop) : (term549 A y s) = (term577 A y s).
Proof. exact (EQ_MP (@lem4948253 A y s) (@lem4948231 A y s)). Qed.
Lemma lem4948447 {A : Type'} (y : A) : (term550 A y) = (term578 A y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4948254 A y s)). Qed.
Lemma lem4948448 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4948449 {A : Type'} (y : A) : (term551 A y) = (term579 A y).
Proof. exact (MK_COMB (@lem4948448 A) (@lem4948447 A y)). Qed.
Lemma lem4948451 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term554 A P Q) = (term555 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4948452 {A : Type'} (P : type686 A) (Q : type686 A) : (term580 A P Q) = (term581 A P Q).
Proof. exact (@lem4948451 (A -> Prop) P Q). Qed.
Lemma lem4948453 {A : Type'} (y : A) : (term582 A y) = (term583 A y).
Proof. exact (@lem4948452 A (term584 A y) (term585 A y)). Qed.
Lemma lem4948454 {A : Type'} (y : A) (s : A -> Prop) : (term586 A y s) = (term571 A y s).
Proof. exact (eq_refl (term586 A y s)). Qed.
Lemma lem4948455 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4948456 {A : Type'} (y : A) (s : A -> Prop) : (term587 A y s) = (term573 A y s).
Proof. exact (MK_COMB (@lem4948455) (@lem4948454 A y s)). Qed.
Lemma lem4948457 {A : Type'} (y : A) (s : A -> Prop) : (term588 A y s) = (term576 A y s).
Proof. exact (eq_refl (term588 A y s)). Qed.
Lemma lem4948458 {A : Type'} (y : A) (s : A -> Prop) : (term589 A y s) = (term577 A y s).
Proof. exact (MK_COMB (@lem4948456 A y s) (@lem4948457 A y s)). Qed.
Lemma lem4948459 {A : Type'} (y : A) : (term590 A y) = (term578 A y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4948458 A y s)). Qed.
Lemma lem4948460 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4948461 {A : Type'} (y : A) : (term582 A y) = (term579 A y).
Proof. exact (MK_COMB (@lem4948460 A) (@lem4948459 A y)). Qed.
Lemma lem4948462 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4948463 {A : Type'} (y : A) : (term591 A y) = (term592 A y).
Proof. exact (MK_COMB (@lem4948462) (@lem4948461 A y)). Qed.
Lemma lem4948464 {A : Type'} (y : A) (s : A -> Prop) : (term586 A y s) = (term571 A y s).
Proof. exact (eq_refl (term586 A y s)). Qed.
Lemma lem4948465 {A : Type'} (y : A) : (term593 A y) = (term584 A y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4948464 A y s)). Qed.
Lemma lem4948466 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4948467 {A : Type'} (y : A) : (term594 A y) = (term595 A y).
Proof. exact (MK_COMB (@lem4948466 A) (@lem4948465 A y)). Qed.
Lemma lem4948468 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4948469 {A : Type'} (y : A) : (term596 A y) = (term597 A y).
Proof. exact (MK_COMB (@lem4948468) (@lem4948467 A y)). Qed.
Lemma lem4948470 {A : Type'} (y : A) (s : A -> Prop) : (term588 A y s) = (term576 A y s).
Proof. exact (eq_refl (term588 A y s)). Qed.
Lemma lem4948471 {A : Type'} (y : A) : (term598 A y) = (term585 A y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4948470 A y s)). Qed.
Lemma lem4948472 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4948473 {A : Type'} (y : A) : (term599 A y) = (term600 A y).
Proof. exact (MK_COMB (@lem4948472 A) (@lem4948471 A y)). Qed.
Lemma lem4948474 {A : Type'} (y : A) : (term583 A y) = (term601 A y).
Proof. exact (MK_COMB (@lem4948469 A y) (@lem4948473 A y)). Qed.
Lemma lem4948475 {A : Type'} (y : A) : ((term582 A y) = (term583 A y)) = ((term579 A y) = (term601 A y)).
Proof. exact (MK_COMB (@lem4948463 A y) (@lem4948474 A y)). Qed.
Lemma lem4948476 {A : Type'} (y : A) : (term579 A y) = (term601 A y).
Proof. exact (EQ_MP (@lem4948475 A y) (@lem4948453 A y)). Qed.
Lemma lem4948677 {A : Type'} (y : A) : (term551 A y) = (term601 A y).
Proof. exact (TRANS (@lem4948449 A y) (@lem4948476 A y)). Qed.
Lemma lem4948678 {A : Type'} : (term552 A) = (term602 A).
Proof. exact (fun_ext (fun y : A => @lem4948677 A y)). Qed.
Lemma lem4948679 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4948680 {A : Type'} : (term553 A) = (term603 A).
Proof. exact (MK_COMB (@lem4948679 A) (@lem4948678 A)). Qed.
Lemma lem4948682 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term554 A P Q) = (term555 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4948683 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term554 A P Q) = (term555 A P Q).
Proof. exact (@lem4948682 A P Q). Qed.
Lemma lem4948684 {A : Type'} : (term604 A) = (term605 A).
Proof. exact (@lem4948683 A (term606 A) (term607 A)). Qed.
Lemma lem4948685 {A : Type'} (y : A) : (term608 A y) = (term595 A y).
Proof. exact (eq_refl (term608 A y)). Qed.
Lemma lem4948686 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4948687 {A : Type'} (y : A) : (term609 A y) = (term597 A y).
Proof. exact (MK_COMB (@lem4948686) (@lem4948685 A y)). Qed.
Lemma lem4948688 {A : Type'} (y : A) : (term610 A y) = (term600 A y).
Proof. exact (eq_refl (term610 A y)). Qed.
Lemma lem4948689 {A : Type'} (y : A) : (term611 A y) = (term601 A y).
Proof. exact (MK_COMB (@lem4948687 A y) (@lem4948688 A y)). Qed.
Lemma lem4948690 {A : Type'} : (term612 A) = (term602 A).
Proof. exact (fun_ext (fun y : A => @lem4948689 A y)). Qed.
Lemma lem4948691 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4948692 {A : Type'} : (term604 A) = (term603 A).
Proof. exact (MK_COMB (@lem4948691 A) (@lem4948690 A)). Qed.
Lemma lem4948693 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4948694 {A : Type'} : (term613 A) = (term614 A).
Proof. exact (MK_COMB (@lem4948693) (@lem4948692 A)). Qed.
Lemma lem4948695 {A : Type'} (y : A) : (term608 A y) = (term595 A y).
Proof. exact (eq_refl (term608 A y)). Qed.
Lemma lem4948696 {A : Type'} : (term615 A) = (term606 A).
Proof. exact (fun_ext (fun y : A => @lem4948695 A y)). Qed.
Lemma lem4948697 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4948698 {A : Type'} : (term616 A) = (term617 A).
Proof. exact (MK_COMB (@lem4948697 A) (@lem4948696 A)). Qed.
Lemma lem4948699 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4948700 {A : Type'} : (term618 A) = (term619 A).
Proof. exact (MK_COMB (@lem4948699) (@lem4948698 A)). Qed.
Lemma lem4948701 {A : Type'} (y : A) : (term610 A y) = (term600 A y).
Proof. exact (eq_refl (term610 A y)). Qed.
Lemma lem4948702 {A : Type'} : (term620 A) = (term607 A).
Proof. exact (fun_ext (fun y : A => @lem4948701 A y)). Qed.
Lemma lem4948703 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4948704 {A : Type'} : (term621 A) = (term622 A).
Proof. exact (MK_COMB (@lem4948703 A) (@lem4948702 A)). Qed.
Lemma lem4948705 {A : Type'} : (term605 A) = (term623 A).
Proof. exact (MK_COMB (@lem4948700 A) (@lem4948704 A)). Qed.
Lemma lem4948706 {A : Type'} : ((term604 A) = (term605 A)) = ((term603 A) = (term623 A)).
Proof. exact (MK_COMB (@lem4948694 A) (@lem4948705 A)). Qed.
Lemma lem4948707 {A : Type'} : (term603 A) = (term623 A).
Proof. exact (EQ_MP (@lem4948706 A) (@lem4948684 A)). Qed.
Lemma lem4948916 {A : Type'} : (term553 A) = (term623 A).
Proof. exact (TRANS (@lem4948680 A) (@lem4948707 A)). Qed.
Lemma lem4948918 {A : Type'} (P : Prop) (Q : A -> Prop) : (term270 A P Q) = (term271 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4948919 {A : Type'} (P : Prop) (Q : A -> Prop) : (term270 A P Q) = (term271 A P Q).
Proof. exact (@lem4948918 A P Q). Qed.
Lemma lem4948920 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term624 A y f s) = (term625 A y f s).
Proof. exact (@lem4948919 A (term626 A y f s) (term168 A y f s)). Qed.
Lemma lem4948921 {A : Type'} (y : A) (f : A -> A) (x : A) (s : A -> Prop) : (term534 A y f s x) = (term167 A y f x s).
Proof. exact (eq_refl (term534 A y f s x)). Qed.
Lemma lem4948922 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term627 A y f s) = (term168 A y f s).
Proof. exact (fun_ext (fun x : A => @lem4948921 A y f x s)). Qed.
Lemma lem4948923 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4948924 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term628 A y f s) = (term169 A y f s).
Proof. exact (MK_COMB (@lem4948923 A) (@lem4948922 A y f s)). Qed.
Lemma lem4948925 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term539 A y f s) = (term539 A y f s).
Proof. exact (eq_refl (term539 A y f s)). Qed.
Lemma lem4948926 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term624 A y f s) = (term540 A y f s).
Proof. exact (MK_COMB (@lem4948925 A y f s) (@lem4948924 A y f s)). Qed.
Lemma lem4948927 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4948928 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term629 A y f s) = (term630 A y f s).
Proof. exact (MK_COMB (@lem4948927) (@lem4948926 A y f s)). Qed.
Lemma lem4948929 {A : Type'} (y : A) (f : A -> A) (x : A) (s : A -> Prop) : (term534 A y f s x) = (term167 A y f x s).
Proof. exact (eq_refl (term534 A y f s x)). Qed.
Lemma lem4948930 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term539 A y f s) = (term539 A y f s).
Proof. exact (eq_refl (term539 A y f s)). Qed.
Lemma lem4948931 {A : Type'} (y : A) (f : A -> A) (x : A) (s : A -> Prop) : (term631 A y f s x) = (term632 A y f x s).
Proof. exact (MK_COMB (@lem4948930 A y f s) (@lem4948929 A y f x s)). Qed.
Lemma lem4948932 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term633 A y f s) = (term634 A y f s).
Proof. exact (fun_ext (fun x : A => @lem4948931 A y f x s)). Qed.
Lemma lem4948933 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4948934 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term625 A y f s) = (term635 A y f s).
Proof. exact (MK_COMB (@lem4948933 A) (@lem4948932 A y f s)). Qed.
Lemma lem4948935 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : ((term624 A y f s) = (term625 A y f s)) = ((term540 A y f s) = (term635 A y f s)).
Proof. exact (MK_COMB (@lem4948928 A y f s) (@lem4948934 A y f s)). Qed.
Lemma lem4948936 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term540 A y f s) = (term635 A y f s).
Proof. exact (EQ_MP (@lem4948935 A y f s) (@lem4948920 A y f s)). Qed.
Lemma lem4948937 {A : Type'} (y : A) (s : A -> Prop) : (term561 A y s) = (term636 A y s).
Proof. exact (fun_ext (fun f : A -> A => @lem4948936 A y f s)). Qed.
Lemma lem4948938 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem4948939 {A : Type'} (y : A) (s : A -> Prop) : (term576 A y s) = (term637 A y s).
Proof. exact (MK_COMB (@lem4948938 A) (@lem4948937 A y s)). Qed.
Lemma lem4948941 {A B : Type'} (P : type1413 A B) : (term286 A B P) = (term287 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4948942 {A : Type'} (P : type486 A) : (term638 A P) = (term639 A P).
Proof. exact (@lem4948941 (A -> A) A P). Qed.
Lemma lem4948943 {A : Type'} (y : A) (s : A -> Prop) : (term640 A y s) = (term641 A y s).
Proof. exact (@lem4948942 A (term642 A y s)). Qed.
Lemma lem4948944 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term643 A y s f) = (term634 A y f s).
Proof. exact (eq_refl (term643 A y s f)). Qed.
Lemma lem4948945 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4948946 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) (x : A) : (term644 A y s f x) = (term645 A y f s x).
Proof. exact (MK_COMB (@lem4948944 A y f s) (@lem4948945 A x)). Qed.
Lemma lem4948947 {A : Type'} (y : A) (f : A -> A) (x : A) (s : A -> Prop) : (term645 A y f s x) = (term632 A y f x s).
Proof. exact (eq_refl (term645 A y f s x)). Qed.
Lemma lem4948948 {A : Type'} (y : A) (f : A -> A) (x : A) (s : A -> Prop) : (term644 A y s f x) = (term632 A y f x s).
Proof. exact (TRANS (@lem4948946 A y f s x) (@lem4948947 A y f x s)). Qed.
Lemma lem4948949 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term646 A y s f) = (term634 A y f s).
Proof. exact (fun_ext (fun x : A => @lem4948948 A y f x s)). Qed.
Lemma lem4948950 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4948951 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term647 A y s f) = (term635 A y f s).
Proof. exact (MK_COMB (@lem4948950 A) (@lem4948949 A y f s)). Qed.
Lemma lem4948952 {A : Type'} (y : A) (s : A -> Prop) : (term648 A y s) = (term636 A y s).
Proof. exact (fun_ext (fun f : A -> A => @lem4948951 A y f s)). Qed.
Lemma lem4948953 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem4948954 {A : Type'} (y : A) (s : A -> Prop) : (term640 A y s) = (term637 A y s).
Proof. exact (MK_COMB (@lem4948953 A) (@lem4948952 A y s)). Qed.
Lemma lem4948955 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4948956 {A : Type'} (y : A) (s : A -> Prop) : (term649 A y s) = (term650 A y s).
Proof. exact (MK_COMB (@lem4948955) (@lem4948954 A y s)). Qed.
Lemma lem4948957 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term643 A y s f) = (term634 A y f s).
Proof. exact (eq_refl (term643 A y s f)). Qed.
Lemma lem4948958 {A : Type'} (x : type487 A) (f : A -> A) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem4948959 {A : Type'} (y : A) (s : A -> Prop) (x : type487 A) (f : A -> A) : (term651 A y s x f) = (term652 A y s x f).
Proof. exact (MK_COMB (@lem4948957 A y f s) (@lem4948958 A x f)). Qed.
Lemma lem4948960 {A : Type'} (y : A) (x : type487 A) (f : A -> A) (s : A -> Prop) : (term652 A y s x f) = (term653 A y x f s).
Proof. exact (eq_refl (term652 A y s x f)). Qed.
Lemma lem4948961 {A : Type'} (y : A) (x : type487 A) (f : A -> A) (s : A -> Prop) : (term651 A y s x f) = (term653 A y x f s).
Proof. exact (TRANS (@lem4948959 A y s x f) (@lem4948960 A y x f s)). Qed.
Lemma lem4948962 {A : Type'} (y : A) (x : type487 A) (s : A -> Prop) : (term654 A y s x) = (term655 A y x s).
Proof. exact (fun_ext (fun f : A -> A => @lem4948961 A y x f s)). Qed.
Lemma lem4948963 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem4948964 {A : Type'} (y : A) (x : type487 A) (s : A -> Prop) : (term656 A y s x) = (term657 A y x s).
Proof. exact (MK_COMB (@lem4948963 A) (@lem4948962 A y x s)). Qed.
Lemma lem4948965 {A : Type'} (y : A) (s : A -> Prop) : (term658 A y s) = (term659 A y s).
Proof. exact (fun_ext (fun x : type487 A => @lem4948964 A y x s)). Qed.
Lemma lem4948966 {A : Type'} : (@ex ((A -> A) -> A)) = (@ex ((A -> A) -> A)).
Proof. exact (eq_refl (@ex ((A -> A) -> A))). Qed.
Lemma lem4948967 {A : Type'} (y : A) (s : A -> Prop) : (term641 A y s) = (term660 A y s).
Proof. exact (MK_COMB (@lem4948966 A) (@lem4948965 A y s)). Qed.
Lemma lem4948968 {A : Type'} (y : A) (s : A -> Prop) : ((term640 A y s) = (term641 A y s)) = ((term637 A y s) = (term660 A y s)).
Proof. exact (MK_COMB (@lem4948956 A y s) (@lem4948967 A y s)). Qed.
Lemma lem4948969 {A : Type'} (y : A) (s : A -> Prop) : (term637 A y s) = (term660 A y s).
Proof. exact (EQ_MP (@lem4948968 A y s) (@lem4948943 A y s)). Qed.
Lemma lem4948970 {A : Type'} (y : A) (s : A -> Prop) : (term576 A y s) = (term660 A y s).
Proof. exact (TRANS (@lem4948939 A y s) (@lem4948969 A y s)). Qed.
Lemma lem4948971 {A : Type'} (y : A) : (term585 A y) = (term661 A y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4948970 A y s)). Qed.
Lemma lem4948972 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4948973 {A : Type'} (y : A) : (term600 A y) = (term662 A y).
Proof. exact (MK_COMB (@lem4948972 A) (@lem4948971 A y)). Qed.
Lemma lem4948975 {A B : Type'} (P : type1413 A B) : (term286 A B P) = (term287 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4948976 {A : Type'} (P : type587 A) : (term663 A P) = (term664 A P).
Proof. exact (@lem4948975 (A -> Prop) (type487 A) P). Qed.
Lemma lem4948977 {A : Type'} (y : A) : (term665 A y) = (term666 A y).
Proof. exact (@lem4948976 A (term667 A y)). Qed.
Lemma lem4948978 {A : Type'} (y : A) (s : A -> Prop) : (term668 A y s) = (term659 A y s).
Proof. exact (eq_refl (term668 A y s)). Qed.
Lemma lem4948979 {A : Type'} (x : type487 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4948980 {A : Type'} (y : A) (s : A -> Prop) (x : type487 A) : (term669 A y s x) = (term670 A y s x).
Proof. exact (MK_COMB (@lem4948978 A y s) (@lem4948979 A x)). Qed.
Lemma lem4948981 {A : Type'} (y : A) (x : type487 A) (s : A -> Prop) : (term670 A y s x) = (term657 A y x s).
Proof. exact (eq_refl (term670 A y s x)). Qed.
Lemma lem4948982 {A : Type'} (y : A) (x : type487 A) (s : A -> Prop) : (term669 A y s x) = (term657 A y x s).
Proof. exact (TRANS (@lem4948980 A y s x) (@lem4948981 A y x s)). Qed.
Lemma lem4948983 {A : Type'} (y : A) (s : A -> Prop) : (term671 A y s) = (term659 A y s).
Proof. exact (fun_ext (fun x : type487 A => @lem4948982 A y x s)). Qed.
Lemma lem4948984 {A : Type'} : (@ex ((A -> A) -> A)) = (@ex ((A -> A) -> A)).
Proof. exact (eq_refl (@ex ((A -> A) -> A))). Qed.
Lemma lem4948985 {A : Type'} (y : A) (s : A -> Prop) : (term672 A y s) = (term660 A y s).
Proof. exact (MK_COMB (@lem4948984 A) (@lem4948983 A y s)). Qed.
Lemma lem4948986 {A : Type'} (y : A) : (term673 A y) = (term661 A y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4948985 A y s)). Qed.
Lemma lem4948987 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4948988 {A : Type'} (y : A) : (term665 A y) = (term662 A y).
Proof. exact (MK_COMB (@lem4948987 A) (@lem4948986 A y)). Qed.
Lemma lem4948989 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4948990 {A : Type'} (y : A) : (term674 A y) = (term675 A y).
Proof. exact (MK_COMB (@lem4948989) (@lem4948988 A y)). Qed.
Lemma lem4948991 {A : Type'} (y : A) (s : A -> Prop) : (term668 A y s) = (term659 A y s).
Proof. exact (eq_refl (term668 A y s)). Qed.
Lemma lem4948992 {A : Type'} (x : type623 A) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem4948993 {A : Type'} (y : A) (x : type623 A) (s : A -> Prop) : (term676 A y x s) = (term677 A y x s).
Proof. exact (MK_COMB (@lem4948991 A y s) (@lem4948992 A x s)). Qed.
Lemma lem4948994 {A : Type'} (y : A) (x : type623 A) (s : A -> Prop) : (term677 A y x s) = (term678 A y x s).
Proof. exact (eq_refl (term677 A y x s)). Qed.
Lemma lem4948995 {A : Type'} (y : A) (x : type623 A) (s : A -> Prop) : (term676 A y x s) = (term678 A y x s).
Proof. exact (TRANS (@lem4948993 A y x s) (@lem4948994 A y x s)). Qed.
Lemma lem4948996 {A : Type'} (y : A) (x : type623 A) : (term679 A y x) = (term680 A y x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4948995 A y x s)). Qed.
Lemma lem4948997 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4948998 {A : Type'} (y : A) (x : type623 A) : (term681 A y x) = (term682 A y x).
Proof. exact (MK_COMB (@lem4948997 A) (@lem4948996 A y x)). Qed.
Lemma lem4948999 {A : Type'} (y : A) : (term683 A y) = (term684 A y).
Proof. exact (fun_ext (fun x : type623 A => @lem4948998 A y x)). Qed.
Lemma lem4949000 {A : Type'} : (@ex ((A -> Prop) -> (A -> A) -> A)) = (@ex ((A -> Prop) -> (A -> A) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> A) -> A))). Qed.
Lemma lem4949001 {A : Type'} (y : A) : (term666 A y) = (term685 A y).
Proof. exact (MK_COMB (@lem4949000 A) (@lem4948999 A y)). Qed.
Lemma lem4949002 {A : Type'} (y : A) : ((term665 A y) = (term666 A y)) = ((term662 A y) = (term685 A y)).
Proof. exact (MK_COMB (@lem4948990 A y) (@lem4949001 A y)). Qed.
Lemma lem4949003 {A : Type'} (y : A) : (term662 A y) = (term685 A y).
Proof. exact (EQ_MP (@lem4949002 A y) (@lem4948977 A y)). Qed.
Lemma lem4949004 {A : Type'} (y : A) : (term600 A y) = (term685 A y).
Proof. exact (TRANS (@lem4948973 A y) (@lem4949003 A y)). Qed.
Lemma lem4949005 {A : Type'} : (term607 A) = (term686 A).
Proof. exact (fun_ext (fun y : A => @lem4949004 A y)). Qed.
Lemma lem4949006 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4949007 {A : Type'} : (term622 A) = (term687 A).
Proof. exact (MK_COMB (@lem4949006 A) (@lem4949005 A)). Qed.
Lemma lem4949009 {A B : Type'} (P : type1413 A B) : (term286 A B P) = (term287 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4949010 {A : Type'} (P : type1356 A) : (term688 A P) = (term689 A P).
Proof. exact (@lem4949009 A (type623 A) P). Qed.
Lemma lem4949011 {A : Type'} : (term690 A) = (term691 A).
Proof. exact (@lem4949010 A (term692 A)). Qed.
Lemma lem4949012 {A : Type'} (y : A) : (term693 A y) = (term684 A y).
Proof. exact (eq_refl (term693 A y)). Qed.
Lemma lem4949013 {A : Type'} (x : type623 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4949014 {A : Type'} (y : A) (x : type623 A) : (term694 A y x) = (term695 A y x).
Proof. exact (MK_COMB (@lem4949012 A y) (@lem4949013 A x)). Qed.
Lemma lem4949015 {A : Type'} (y : A) (x : type623 A) : (term695 A y x) = (term682 A y x).
Proof. exact (eq_refl (term695 A y x)). Qed.
Lemma lem4949016 {A : Type'} (y : A) (x : type623 A) : (term694 A y x) = (term682 A y x).
Proof. exact (TRANS (@lem4949014 A y x) (@lem4949015 A y x)). Qed.
Lemma lem4949017 {A : Type'} (y : A) : (term696 A y) = (term684 A y).
Proof. exact (fun_ext (fun x : type623 A => @lem4949016 A y x)). Qed.
Lemma lem4949018 {A : Type'} : (@ex ((A -> Prop) -> (A -> A) -> A)) = (@ex ((A -> Prop) -> (A -> A) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> A) -> A))). Qed.
Lemma lem4949019 {A : Type'} (y : A) : (term697 A y) = (term685 A y).
Proof. exact (MK_COMB (@lem4949018 A) (@lem4949017 A y)). Qed.
Lemma lem4949020 {A : Type'} : (term698 A) = (term686 A).
Proof. exact (fun_ext (fun y : A => @lem4949019 A y)). Qed.
Lemma lem4949021 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4949022 {A : Type'} : (term690 A) = (term687 A).
Proof. exact (MK_COMB (@lem4949021 A) (@lem4949020 A)). Qed.
Lemma lem4949023 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4949024 {A : Type'} : (term699 A) = (term700 A).
Proof. exact (MK_COMB (@lem4949023) (@lem4949022 A)). Qed.
Lemma lem4949025 {A : Type'} (y : A) : (term693 A y) = (term684 A y).
Proof. exact (eq_refl (term693 A y)). Qed.
Lemma lem4949026 {A : Type'} (x : type1361 A) (y : A) : (x y) = (x y).
Proof. exact (eq_refl (x y)). Qed.
Lemma lem4949027 {A : Type'} (x : type1361 A) (y : A) : (term701 A x y) = (term702 A x y).
Proof. exact (MK_COMB (@lem4949025 A y) (@lem4949026 A x y)). Qed.
Lemma lem4949028 {A : Type'} (x : type1361 A) (y : A) : (term702 A x y) = (term703 A x y).
Proof. exact (eq_refl (term702 A x y)). Qed.
Lemma lem4949029 {A : Type'} (x : type1361 A) (y : A) : (term701 A x y) = (term703 A x y).
Proof. exact (TRANS (@lem4949027 A x y) (@lem4949028 A x y)). Qed.
Lemma lem4949030 {A : Type'} (x : type1361 A) : (term704 A x) = (term705 A x).
Proof. exact (fun_ext (fun y : A => @lem4949029 A x y)). Qed.
Lemma lem4949031 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4949032 {A : Type'} (x : type1361 A) : (term706 A x) = (term707 A x).
Proof. exact (MK_COMB (@lem4949031 A) (@lem4949030 A x)). Qed.
Lemma lem4949033 {A : Type'} : (term708 A) = (term709 A).
Proof. exact (fun_ext (fun x : type1361 A => @lem4949032 A x)). Qed.
Lemma lem4949034 {A : Type'} : (@ex (A -> (A -> Prop) -> (A -> A) -> A)) = (@ex (A -> (A -> Prop) -> (A -> A) -> A)).
Proof. exact (eq_refl (@ex (A -> (A -> Prop) -> (A -> A) -> A))). Qed.
Lemma lem4949035 {A : Type'} : (term691 A) = (term710 A).
Proof. exact (MK_COMB (@lem4949034 A) (@lem4949033 A)). Qed.
Lemma lem4949036 {A : Type'} : ((term690 A) = (term691 A)) = ((term687 A) = (term710 A)).
Proof. exact (MK_COMB (@lem4949024 A) (@lem4949035 A)). Qed.
Lemma lem4949037 {A : Type'} : (term687 A) = (term710 A).
Proof. exact (EQ_MP (@lem4949036 A) (@lem4949011 A)). Qed.
Lemma lem4949038 {A : Type'} : (term622 A) = (term710 A).
Proof. exact (TRANS (@lem4949007 A) (@lem4949037 A)). Qed.
Lemma lem4949039 {A : Type'} : (term619 A) = (term619 A).
Proof. exact (eq_refl (term619 A)). Qed.
Lemma lem4949040 {A : Type'} : (term623 A) = (term711 A).
Proof. exact (MK_COMB (@lem4949039 A) (@lem4949038 A)). Qed.
Lemma lem4949042 {A : Type'} (P : Prop) (Q : A -> Prop) : (term348 A P Q) = (term349 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4949043 {A : Type'} (P : Prop) (Q : type391 A) : (term712 A P Q) = (term713 A P Q).
Proof. exact (@lem4949042 (type1361 A) P Q). Qed.
Lemma lem4949044 {A : Type'} : (term714 A) = (term715 A).
Proof. exact (@lem4949043 A (term617 A) (term709 A)). Qed.
Lemma lem4949045 {A : Type'} (x : type1361 A) : (term716 A x) = (term707 A x).
Proof. exact (eq_refl (term716 A x)). Qed.
Lemma lem4949046 {A : Type'} : (term717 A) = (term709 A).
Proof. exact (fun_ext (fun x : type1361 A => @lem4949045 A x)). Qed.
Lemma lem4949047 {A : Type'} : (@ex (A -> (A -> Prop) -> (A -> A) -> A)) = (@ex (A -> (A -> Prop) -> (A -> A) -> A)).
Proof. exact (eq_refl (@ex (A -> (A -> Prop) -> (A -> A) -> A))). Qed.
Lemma lem4949048 {A : Type'} : (term718 A) = (term710 A).
Proof. exact (MK_COMB (@lem4949047 A) (@lem4949046 A)). Qed.
Lemma lem4949049 {A : Type'} : (term619 A) = (term619 A).
Proof. exact (eq_refl (term619 A)). Qed.
Lemma lem4949050 {A : Type'} : (term714 A) = (term711 A).
Proof. exact (MK_COMB (@lem4949049 A) (@lem4949048 A)). Qed.
Lemma lem4949051 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4949052 {A : Type'} : (term719 A) = (term720 A).
Proof. exact (MK_COMB (@lem4949051) (@lem4949050 A)). Qed.
Lemma lem4949053 {A : Type'} (x : type1361 A) : (term716 A x) = (term707 A x).
Proof. exact (eq_refl (term716 A x)). Qed.
Lemma lem4949054 {A : Type'} : (term619 A) = (term619 A).
Proof. exact (eq_refl (term619 A)). Qed.
Lemma lem4949055 {A : Type'} (x : type1361 A) : (term721 A x) = (term722 A x).
Proof. exact (MK_COMB (@lem4949054 A) (@lem4949053 A x)). Qed.
Lemma lem4949056 {A : Type'} : (term723 A) = (term724 A).
Proof. exact (fun_ext (fun x : type1361 A => @lem4949055 A x)). Qed.
Lemma lem4949057 {A : Type'} : (@ex (A -> (A -> Prop) -> (A -> A) -> A)) = (@ex (A -> (A -> Prop) -> (A -> A) -> A)).
Proof. exact (eq_refl (@ex (A -> (A -> Prop) -> (A -> A) -> A))). Qed.
Lemma lem4949058 {A : Type'} : (term715 A) = (term725 A).
Proof. exact (MK_COMB (@lem4949057 A) (@lem4949056 A)). Qed.
Lemma lem4949059 {A : Type'} : ((term714 A) = (term715 A)) = ((term711 A) = (term725 A)).
Proof. exact (MK_COMB (@lem4949052 A) (@lem4949058 A)). Qed.
Lemma lem4949060 {A : Type'} : (term711 A) = (term725 A).
Proof. exact (EQ_MP (@lem4949059 A) (@lem4949044 A)). Qed.
Lemma lem4949061 {A : Type'} : (term623 A) = (term725 A).
Proof. exact (TRANS (@lem4949040 A) (@lem4949060 A)). Qed.
Lemma lem4949062 {A : Type'} : (term553 A) = (term725 A).
Proof. exact (TRANS (@lem4948916 A) (@lem4949061 A)). Qed.
Lemma lem4949063 {A : Type'} : (term84 A) = (term725 A).
Proof. exact (TRANS (@lem4948219 A) (@lem4949062 A)). Qed.
Lemma lem4949064 {A : Type'} (h1 : term84 A) : term725 A.
Proof. exact (EQ_MP (@lem4949063 A) (@lem4947220 A h1)). Qed.
Lemma lem4949075 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term726 A B y f x s) = (term727 A B y f x s).
Proof. exact (@lem17045 (y = (f x)) (@IN A x s)). Qed.
Lemma lem4949078 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term177 A B y f x s) = (term177 A B y f x s).
Proof. exact (eq_refl (term177 A B y f x s)). Qed.
Lemma lem4949079 {A : Type'} (P : A -> Prop) : (term196 A P) = (term197 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem4949080 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term728 A B y f s) = (term729 A B y f s).
Proof. exact (@lem4949079 A (term178 A B y f s)). Qed.
Lemma lem4949081 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term730 A B y f s x) = (term177 A B y f x s).
Proof. exact (eq_refl (term730 A B y f s x)). Qed.
Lemma lem4949082 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4949083 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term731 A B y f s x) = (term726 A B y f x s).
Proof. exact (MK_COMB (@lem4949082) (@lem4949081 A B y f x s)). Qed.
Lemma lem4949084 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term731 A B y f s x) = (term727 A B y f x s).
Proof. exact (TRANS (@lem4949083 A B y f x s) (@lem4949075 A B y f x s)). Qed.
Lemma lem4949085 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term732 A B y f s) = (term733 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem4949084 A B y f x s)). Qed.
Lemma lem4949086 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4949087 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term729 A B y f s) = (term734 A B y f s).
Proof. exact (MK_COMB (@lem4949086 A) (@lem4949085 A B y f s)). Qed.
Lemma lem4949088 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term728 A B y f s) = (term734 A B y f s).
Proof. exact (TRANS (@lem4949080 A B y f s) (@lem4949087 A B y f s)). Qed.
Lemma lem4949089 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term178 A B y f s) = (term178 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem4949078 A B y f x s)). Qed.
Lemma lem4949090 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4949091 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term179 A B y f s) = (term179 A B y f s).
Proof. exact (MK_COMB (@lem4949090 A) (@lem4949089 A B y f s)). Qed.
Lemma lem4949093 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term209 A B y f s) = (term209 A B y f s).
Proof. exact (eq_refl (term209 A B y f s)). Qed.
Lemma lem4949094 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term735 A B y f s) = (term735 A B y f s).
Proof. exact (MK_COMB (@lem4949093 A B y f s) (@lem4949091 A B y f s)). Qed.
Lemma lem4949096 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term736 A B y f s) = (term736 A B y f s).
Proof. exact (eq_refl (term736 A B y f s)). Qed.
Lemma lem4949097 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term737 A B y f s) = (term738 A B y f s).
Proof. exact (MK_COMB (@lem4949096 A B y f s) (@lem4949088 A B y f s)). Qed.
Lemma lem4949098 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4949099 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term739 A B y f s) = (term740 A B y f s).
Proof. exact (MK_COMB (@lem4949098) (@lem4949097 A B y f s)). Qed.
Lemma lem4949100 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term741 A B y f s) = (term742 A B y f s).
Proof. exact (MK_COMB (@lem4949099 A B y f s) (@lem4949094 A B y f s)). Qed.
Lemma lem4949101 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : ((term58 A B y f s) = (term179 A B y f s)) = (term741 A B y f s).
Proof. exact (@lem17784 (term58 A B y f s) (term179 A B y f s)). Qed.
Lemma lem4949102 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : ((term58 A B y f s) = (term179 A B y f s)) = (term742 A B y f s).
Proof. exact (TRANS (@lem4949101 A B y f s) (@lem4949100 A B y f s)). Qed.
Lemma lem4949103 {A B : Type'} (y : B) (s : A -> Prop) : (term181 A B y s) = (term743 A B y s).
Proof. exact (fun_ext (fun f : A -> B => @lem4949102 A B y f s)). Qed.
Lemma lem4949104 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4949105 {A B : Type'} (y : B) (s : A -> Prop) : (term182 A B y s) = (term744 A B y s).
Proof. exact (MK_COMB (@lem4949104 A B) (@lem4949103 A B y s)). Qed.
Lemma lem4949106 {A B : Type'} (y : B) : (term183 A B y) = (term745 A B y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4949105 A B y s)). Qed.
Lemma lem4949107 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4949108 {A B : Type'} (y : B) : (term184 A B y) = (term746 A B y).
Proof. exact (MK_COMB (@lem4949107 A) (@lem4949106 A B y)). Qed.
Lemma lem4949109 {A B : Type'} : (term185 A B) = (term747 A B).
Proof. exact (fun_ext (fun y : B => @lem4949108 A B y)). Qed.
Lemma lem4949110 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4949111 {A B : Type'} : (term83 A B) = (term748 A B).
Proof. exact (MK_COMB (@lem4949110 B) (@lem4949109 A B)). Qed.
Lemma lem4949121 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term554 A P Q) = (term555 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4949122 {A B : Type'} (P : type572 A B) (Q : type572 A B) : (term749 A B P Q) = (term750 A B P Q).
Proof. exact (@lem4949121 (A -> B) P Q). Qed.
Lemma lem4949123 {A B : Type'} (y : B) (s : A -> Prop) : (term751 A B y s) = (term752 A B y s).
Proof. exact (@lem4949122 A B (term753 A B y s) (term754 A B y s)). Qed.
Lemma lem4949124 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term755 A B y s f) = (term738 A B y f s).
Proof. exact (eq_refl (term755 A B y s f)). Qed.
Lemma lem4949125 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4949126 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term756 A B y s f) = (term740 A B y f s).
Proof. exact (MK_COMB (@lem4949125) (@lem4949124 A B y f s)). Qed.
Lemma lem4949127 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term757 A B y s f) = (term735 A B y f s).
Proof. exact (eq_refl (term757 A B y s f)). Qed.
Lemma lem4949128 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term758 A B y s f) = (term742 A B y f s).
Proof. exact (MK_COMB (@lem4949126 A B y f s) (@lem4949127 A B y f s)). Qed.
Lemma lem4949129 {A B : Type'} (y : B) (s : A -> Prop) : (term759 A B y s) = (term743 A B y s).
Proof. exact (fun_ext (fun f : A -> B => @lem4949128 A B y f s)). Qed.
Lemma lem4949130 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4949131 {A B : Type'} (y : B) (s : A -> Prop) : (term751 A B y s) = (term744 A B y s).
Proof. exact (MK_COMB (@lem4949130 A B) (@lem4949129 A B y s)). Qed.
Lemma lem4949132 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4949133 {A B : Type'} (y : B) (s : A -> Prop) : (term760 A B y s) = (term761 A B y s).
Proof. exact (MK_COMB (@lem4949132) (@lem4949131 A B y s)). Qed.
Lemma lem4949134 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term755 A B y s f) = (term738 A B y f s).
Proof. exact (eq_refl (term755 A B y s f)). Qed.
Lemma lem4949135 {A B : Type'} (y : B) (s : A -> Prop) : (term762 A B y s) = (term753 A B y s).
Proof. exact (fun_ext (fun f : A -> B => @lem4949134 A B y f s)). Qed.
Lemma lem4949136 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4949137 {A B : Type'} (y : B) (s : A -> Prop) : (term763 A B y s) = (term764 A B y s).
Proof. exact (MK_COMB (@lem4949136 A B) (@lem4949135 A B y s)). Qed.
Lemma lem4949138 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4949139 {A B : Type'} (y : B) (s : A -> Prop) : (term765 A B y s) = (term766 A B y s).
Proof. exact (MK_COMB (@lem4949138) (@lem4949137 A B y s)). Qed.
Lemma lem4949140 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term757 A B y s f) = (term735 A B y f s).
Proof. exact (eq_refl (term757 A B y s f)). Qed.
Lemma lem4949141 {A B : Type'} (y : B) (s : A -> Prop) : (term767 A B y s) = (term754 A B y s).
Proof. exact (fun_ext (fun f : A -> B => @lem4949140 A B y f s)). Qed.
Lemma lem4949142 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4949143 {A B : Type'} (y : B) (s : A -> Prop) : (term768 A B y s) = (term769 A B y s).
Proof. exact (MK_COMB (@lem4949142 A B) (@lem4949141 A B y s)). Qed.
Lemma lem4949144 {A B : Type'} (y : B) (s : A -> Prop) : (term752 A B y s) = (term770 A B y s).
Proof. exact (MK_COMB (@lem4949139 A B y s) (@lem4949143 A B y s)). Qed.
Lemma lem4949145 {A B : Type'} (y : B) (s : A -> Prop) : ((term751 A B y s) = (term752 A B y s)) = ((term744 A B y s) = (term770 A B y s)).
Proof. exact (MK_COMB (@lem4949133 A B y s) (@lem4949144 A B y s)). Qed.
Lemma lem4949146 {A B : Type'} (y : B) (s : A -> Prop) : (term744 A B y s) = (term770 A B y s).
Proof. exact (EQ_MP (@lem4949145 A B y s) (@lem4949123 A B y s)). Qed.
Lemma lem4949339 {A B : Type'} (y : B) : (term745 A B y) = (term771 A B y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4949146 A B y s)). Qed.
Lemma lem4949340 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4949341 {A B : Type'} (y : B) : (term746 A B y) = (term772 A B y).
Proof. exact (MK_COMB (@lem4949340 A) (@lem4949339 A B y)). Qed.
Lemma lem4949343 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term554 A P Q) = (term555 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4949344 {A : Type'} (P : type686 A) (Q : type686 A) : (term580 A P Q) = (term581 A P Q).
Proof. exact (@lem4949343 (A -> Prop) P Q). Qed.
Lemma lem4949345 {A B : Type'} (y : B) : (term773 A B y) = (term774 A B y).
Proof. exact (@lem4949344 A (term775 A B y) (term776 A B y)). Qed.
Lemma lem4949346 {A B : Type'} (y : B) (s : A -> Prop) : (term777 A B y s) = (term764 A B y s).
Proof. exact (eq_refl (term777 A B y s)). Qed.
Lemma lem4949347 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4949348 {A B : Type'} (y : B) (s : A -> Prop) : (term778 A B y s) = (term766 A B y s).
Proof. exact (MK_COMB (@lem4949347) (@lem4949346 A B y s)). Qed.
Lemma lem4949349 {A B : Type'} (y : B) (s : A -> Prop) : (term779 A B y s) = (term769 A B y s).
Proof. exact (eq_refl (term779 A B y s)). Qed.
Lemma lem4949350 {A B : Type'} (y : B) (s : A -> Prop) : (term780 A B y s) = (term770 A B y s).
Proof. exact (MK_COMB (@lem4949348 A B y s) (@lem4949349 A B y s)). Qed.
Lemma lem4949351 {A B : Type'} (y : B) : (term781 A B y) = (term771 A B y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4949350 A B y s)). Qed.
Lemma lem4949352 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4949353 {A B : Type'} (y : B) : (term773 A B y) = (term772 A B y).
Proof. exact (MK_COMB (@lem4949352 A) (@lem4949351 A B y)). Qed.
Lemma lem4949354 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4949355 {A B : Type'} (y : B) : (term782 A B y) = (term783 A B y).
Proof. exact (MK_COMB (@lem4949354) (@lem4949353 A B y)). Qed.
Lemma lem4949356 {A B : Type'} (y : B) (s : A -> Prop) : (term777 A B y s) = (term764 A B y s).
Proof. exact (eq_refl (term777 A B y s)). Qed.
Lemma lem4949357 {A B : Type'} (y : B) : (term784 A B y) = (term775 A B y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4949356 A B y s)). Qed.
Lemma lem4949358 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4949359 {A B : Type'} (y : B) : (term785 A B y) = (term786 A B y).
Proof. exact (MK_COMB (@lem4949358 A) (@lem4949357 A B y)). Qed.
Lemma lem4949360 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4949361 {A B : Type'} (y : B) : (term787 A B y) = (term788 A B y).
Proof. exact (MK_COMB (@lem4949360) (@lem4949359 A B y)). Qed.
Lemma lem4949362 {A B : Type'} (y : B) (s : A -> Prop) : (term779 A B y s) = (term769 A B y s).
Proof. exact (eq_refl (term779 A B y s)). Qed.
Lemma lem4949363 {A B : Type'} (y : B) : (term789 A B y) = (term776 A B y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4949362 A B y s)). Qed.
Lemma lem4949364 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4949365 {A B : Type'} (y : B) : (term790 A B y) = (term791 A B y).
Proof. exact (MK_COMB (@lem4949364 A) (@lem4949363 A B y)). Qed.
Lemma lem4949366 {A B : Type'} (y : B) : (term774 A B y) = (term792 A B y).
Proof. exact (MK_COMB (@lem4949361 A B y) (@lem4949365 A B y)). Qed.
Lemma lem4949367 {A B : Type'} (y : B) : ((term773 A B y) = (term774 A B y)) = ((term772 A B y) = (term792 A B y)).
Proof. exact (MK_COMB (@lem4949355 A B y) (@lem4949366 A B y)). Qed.
Lemma lem4949368 {A B : Type'} (y : B) : (term772 A B y) = (term792 A B y).
Proof. exact (EQ_MP (@lem4949367 A B y) (@lem4949345 A B y)). Qed.
Lemma lem4949569 {A B : Type'} (y : B) : (term746 A B y) = (term792 A B y).
Proof. exact (TRANS (@lem4949341 A B y) (@lem4949368 A B y)). Qed.
Lemma lem4949570 {A B : Type'} : (term747 A B) = (term793 A B).
Proof. exact (fun_ext (fun y : B => @lem4949569 A B y)). Qed.
Lemma lem4949571 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4949572 {A B : Type'} : (term748 A B) = (term794 A B).
Proof. exact (MK_COMB (@lem4949571 B) (@lem4949570 A B)). Qed.
Lemma lem4949574 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term554 A P Q) = (term555 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4949575 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term554 B P Q) = (term555 B P Q).
Proof. exact (@lem4949574 B P Q). Qed.
Lemma lem4949576 {A B : Type'} : (term795 A B) = (term796 A B).
Proof. exact (@lem4949575 B (term797 A B) (term798 A B)). Qed.
Lemma lem4949577 {A B : Type'} (y : B) : (term799 A B y) = (term786 A B y).
Proof. exact (eq_refl (term799 A B y)). Qed.
Lemma lem4949578 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4949579 {A B : Type'} (y : B) : (term800 A B y) = (term788 A B y).
Proof. exact (MK_COMB (@lem4949578) (@lem4949577 A B y)). Qed.
Lemma lem4949580 {A B : Type'} (y : B) : (term801 A B y) = (term791 A B y).
Proof. exact (eq_refl (term801 A B y)). Qed.
Lemma lem4949581 {A B : Type'} (y : B) : (term802 A B y) = (term792 A B y).
Proof. exact (MK_COMB (@lem4949579 A B y) (@lem4949580 A B y)). Qed.
Lemma lem4949582 {A B : Type'} : (term803 A B) = (term793 A B).
Proof. exact (fun_ext (fun y : B => @lem4949581 A B y)). Qed.
Lemma lem4949583 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4949584 {A B : Type'} : (term795 A B) = (term794 A B).
Proof. exact (MK_COMB (@lem4949583 B) (@lem4949582 A B)). Qed.
Lemma lem4949585 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4949586 {A B : Type'} : (term804 A B) = (term805 A B).
Proof. exact (MK_COMB (@lem4949585) (@lem4949584 A B)). Qed.
Lemma lem4949587 {A B : Type'} (y : B) : (term799 A B y) = (term786 A B y).
Proof. exact (eq_refl (term799 A B y)). Qed.
Lemma lem4949588 {A B : Type'} : (term806 A B) = (term797 A B).
Proof. exact (fun_ext (fun y : B => @lem4949587 A B y)). Qed.
Lemma lem4949589 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4949590 {A B : Type'} : (term807 A B) = (term808 A B).
Proof. exact (MK_COMB (@lem4949589 B) (@lem4949588 A B)). Qed.
Lemma lem4949591 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4949592 {A B : Type'} : (term809 A B) = (term810 A B).
Proof. exact (MK_COMB (@lem4949591) (@lem4949590 A B)). Qed.
Lemma lem4949593 {A B : Type'} (y : B) : (term801 A B y) = (term791 A B y).
Proof. exact (eq_refl (term801 A B y)). Qed.
Lemma lem4949594 {A B : Type'} : (term811 A B) = (term798 A B).
Proof. exact (fun_ext (fun y : B => @lem4949593 A B y)). Qed.
Lemma lem4949595 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4949596 {A B : Type'} : (term812 A B) = (term813 A B).
Proof. exact (MK_COMB (@lem4949595 B) (@lem4949594 A B)). Qed.
Lemma lem4949597 {A B : Type'} : (term796 A B) = (term814 A B).
Proof. exact (MK_COMB (@lem4949592 A B) (@lem4949596 A B)). Qed.
Lemma lem4949598 {A B : Type'} : ((term795 A B) = (term796 A B)) = ((term794 A B) = (term814 A B)).
Proof. exact (MK_COMB (@lem4949586 A B) (@lem4949597 A B)). Qed.
Lemma lem4949599 {A B : Type'} : (term794 A B) = (term814 A B).
Proof. exact (EQ_MP (@lem4949598 A B) (@lem4949576 A B)). Qed.
Lemma lem4949808 {A B : Type'} : (term748 A B) = (term814 A B).
Proof. exact (TRANS (@lem4949572 A B) (@lem4949599 A B)). Qed.
Lemma lem4949810 {A : Type'} (P : Prop) (Q : A -> Prop) : (term270 A P Q) = (term271 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4949811 {A : Type'} (P : Prop) (Q : A -> Prop) : (term270 A P Q) = (term271 A P Q).
Proof. exact (@lem4949810 A P Q). Qed.
Lemma lem4949812 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term815 A B y f s) = (term816 A B y f s).
Proof. exact (@lem4949811 A (term274 A B y f s) (term178 A B y f s)). Qed.
Lemma lem4949813 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term730 A B y f s x) = (term177 A B y f x s).
Proof. exact (eq_refl (term730 A B y f s x)). Qed.
Lemma lem4949814 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term817 A B y f s) = (term178 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem4949813 A B y f x s)). Qed.
Lemma lem4949815 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4949816 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term818 A B y f s) = (term179 A B y f s).
Proof. exact (MK_COMB (@lem4949815 A) (@lem4949814 A B y f s)). Qed.
Lemma lem4949817 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term209 A B y f s) = (term209 A B y f s).
Proof. exact (eq_refl (term209 A B y f s)). Qed.
Lemma lem4949818 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term815 A B y f s) = (term735 A B y f s).
Proof. exact (MK_COMB (@lem4949817 A B y f s) (@lem4949816 A B y f s)). Qed.
Lemma lem4949819 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4949820 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term819 A B y f s) = (term820 A B y f s).
Proof. exact (MK_COMB (@lem4949819) (@lem4949818 A B y f s)). Qed.
Lemma lem4949821 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term730 A B y f s x) = (term177 A B y f x s).
Proof. exact (eq_refl (term730 A B y f s x)). Qed.
Lemma lem4949822 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term209 A B y f s) = (term209 A B y f s).
Proof. exact (eq_refl (term209 A B y f s)). Qed.
Lemma lem4949823 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term821 A B y f s x) = (term822 A B y f x s).
Proof. exact (MK_COMB (@lem4949822 A B y f s) (@lem4949821 A B y f x s)). Qed.
Lemma lem4949824 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term823 A B y f s) = (term824 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem4949823 A B y f x s)). Qed.
Lemma lem4949825 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4949826 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term816 A B y f s) = (term825 A B y f s).
Proof. exact (MK_COMB (@lem4949825 A) (@lem4949824 A B y f s)). Qed.
Lemma lem4949827 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : ((term815 A B y f s) = (term816 A B y f s)) = ((term735 A B y f s) = (term825 A B y f s)).
Proof. exact (MK_COMB (@lem4949820 A B y f s) (@lem4949826 A B y f s)). Qed.
Lemma lem4949828 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term735 A B y f s) = (term825 A B y f s).
Proof. exact (EQ_MP (@lem4949827 A B y f s) (@lem4949812 A B y f s)). Qed.
Lemma lem4949829 {A B : Type'} (y : B) (s : A -> Prop) : (term754 A B y s) = (term826 A B y s).
Proof. exact (fun_ext (fun f : A -> B => @lem4949828 A B y f s)). Qed.
Lemma lem4949830 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4949831 {A B : Type'} (y : B) (s : A -> Prop) : (term769 A B y s) = (term827 A B y s).
Proof. exact (MK_COMB (@lem4949830 A B) (@lem4949829 A B y s)). Qed.
Lemma lem4949833 {A B : Type'} (P : type1413 A B) : (term286 A B P) = (term287 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4949834 {A B : Type'} (P : type551 A B) : (term828 A B P) = (term829 A B P).
Proof. exact (@lem4949833 (A -> B) A P). Qed.
Lemma lem4949835 {A B : Type'} (y : B) (s : A -> Prop) : (term830 A B y s) = (term831 A B y s).
Proof. exact (@lem4949834 A B (term832 A B y s)). Qed.
Lemma lem4949836 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term833 A B y s f) = (term824 A B y f s).
Proof. exact (eq_refl (term833 A B y s f)). Qed.
Lemma lem4949837 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4949838 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) : (term834 A B y s f x) = (term835 A B y f s x).
Proof. exact (MK_COMB (@lem4949836 A B y f s) (@lem4949837 A x)). Qed.
Lemma lem4949839 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term835 A B y f s x) = (term822 A B y f x s).
Proof. exact (eq_refl (term835 A B y f s x)). Qed.
Lemma lem4949840 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term834 A B y s f x) = (term822 A B y f x s).
Proof. exact (TRANS (@lem4949838 A B y f s x) (@lem4949839 A B y f x s)). Qed.
Lemma lem4949841 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term836 A B y s f) = (term824 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem4949840 A B y f x s)). Qed.
Lemma lem4949842 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4949843 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term837 A B y s f) = (term825 A B y f s).
Proof. exact (MK_COMB (@lem4949842 A) (@lem4949841 A B y f s)). Qed.
Lemma lem4949844 {A B : Type'} (y : B) (s : A -> Prop) : (term838 A B y s) = (term826 A B y s).
Proof. exact (fun_ext (fun f : A -> B => @lem4949843 A B y f s)). Qed.
Lemma lem4949845 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4949846 {A B : Type'} (y : B) (s : A -> Prop) : (term830 A B y s) = (term827 A B y s).
Proof. exact (MK_COMB (@lem4949845 A B) (@lem4949844 A B y s)). Qed.
Lemma lem4949847 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4949848 {A B : Type'} (y : B) (s : A -> Prop) : (term839 A B y s) = (term840 A B y s).
Proof. exact (MK_COMB (@lem4949847) (@lem4949846 A B y s)). Qed.
Lemma lem4949849 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term833 A B y s f) = (term824 A B y f s).
Proof. exact (eq_refl (term833 A B y s f)). Qed.
Lemma lem4949850 {A B : Type'} (x : type569 A B) (f : A -> B) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem4949851 {A B : Type'} (y : B) (s : A -> Prop) (x : type569 A B) (f : A -> B) : (term841 A B y s x f) = (term842 A B y s x f).
Proof. exact (MK_COMB (@lem4949849 A B y f s) (@lem4949850 A B x f)). Qed.
Lemma lem4949852 {A B : Type'} (y : B) (x : type569 A B) (f : A -> B) (s : A -> Prop) : (term842 A B y s x f) = (term843 A B y x f s).
Proof. exact (eq_refl (term842 A B y s x f)). Qed.
Lemma lem4949853 {A B : Type'} (y : B) (x : type569 A B) (f : A -> B) (s : A -> Prop) : (term841 A B y s x f) = (term843 A B y x f s).
Proof. exact (TRANS (@lem4949851 A B y s x f) (@lem4949852 A B y x f s)). Qed.
Lemma lem4949854 {A B : Type'} (y : B) (x : type569 A B) (s : A -> Prop) : (term844 A B y s x) = (term845 A B y x s).
Proof. exact (fun_ext (fun f : A -> B => @lem4949853 A B y x f s)). Qed.
Lemma lem4949855 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4949856 {A B : Type'} (y : B) (x : type569 A B) (s : A -> Prop) : (term846 A B y s x) = (term847 A B y x s).
Proof. exact (MK_COMB (@lem4949855 A B) (@lem4949854 A B y x s)). Qed.
Lemma lem4949857 {A B : Type'} (y : B) (s : A -> Prop) : (term848 A B y s) = (term849 A B y s).
Proof. exact (fun_ext (fun x : type569 A B => @lem4949856 A B y x s)). Qed.
Lemma lem4949858 {A B : Type'} : (@ex ((A -> B) -> A)) = (@ex ((A -> B) -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> A))). Qed.
Lemma lem4949859 {A B : Type'} (y : B) (s : A -> Prop) : (term831 A B y s) = (term850 A B y s).
Proof. exact (MK_COMB (@lem4949858 A B) (@lem4949857 A B y s)). Qed.
Lemma lem4949860 {A B : Type'} (y : B) (s : A -> Prop) : ((term830 A B y s) = (term831 A B y s)) = ((term827 A B y s) = (term850 A B y s)).
Proof. exact (MK_COMB (@lem4949848 A B y s) (@lem4949859 A B y s)). Qed.
Lemma lem4949861 {A B : Type'} (y : B) (s : A -> Prop) : (term827 A B y s) = (term850 A B y s).
Proof. exact (EQ_MP (@lem4949860 A B y s) (@lem4949835 A B y s)). Qed.
Lemma lem4949862 {A B : Type'} (y : B) (s : A -> Prop) : (term769 A B y s) = (term850 A B y s).
Proof. exact (TRANS (@lem4949831 A B y s) (@lem4949861 A B y s)). Qed.
Lemma lem4949863 {A B : Type'} (y : B) : (term776 A B y) = (term851 A B y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4949862 A B y s)). Qed.
Lemma lem4949864 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4949865 {A B : Type'} (y : B) : (term791 A B y) = (term852 A B y).
Proof. exact (MK_COMB (@lem4949864 A) (@lem4949863 A B y)). Qed.
Lemma lem4949867 {A B : Type'} (P : type1413 A B) : (term286 A B P) = (term287 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4949868 {A B : Type'} (P : type593 A B) : (term853 A B P) = (term854 A B P).
Proof. exact (@lem4949867 (A -> Prop) (type569 A B) P). Qed.
Lemma lem4949869 {A B : Type'} (y : B) : (term855 A B y) = (term856 A B y).
Proof. exact (@lem4949868 A B (term857 A B y)). Qed.
Lemma lem4949870 {A B : Type'} (y : B) (s : A -> Prop) : (term858 A B y s) = (term849 A B y s).
Proof. exact (eq_refl (term858 A B y s)). Qed.
Lemma lem4949871 {A B : Type'} (x : type569 A B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4949872 {A B : Type'} (y : B) (s : A -> Prop) (x : type569 A B) : (term859 A B y s x) = (term860 A B y s x).
Proof. exact (MK_COMB (@lem4949870 A B y s) (@lem4949871 A B x)). Qed.
Lemma lem4949873 {A B : Type'} (y : B) (x : type569 A B) (s : A -> Prop) : (term860 A B y s x) = (term847 A B y x s).
Proof. exact (eq_refl (term860 A B y s x)). Qed.
Lemma lem4949874 {A B : Type'} (y : B) (x : type569 A B) (s : A -> Prop) : (term859 A B y s x) = (term847 A B y x s).
Proof. exact (TRANS (@lem4949872 A B y s x) (@lem4949873 A B y x s)). Qed.
Lemma lem4949875 {A B : Type'} (y : B) (s : A -> Prop) : (term861 A B y s) = (term849 A B y s).
Proof. exact (fun_ext (fun x : type569 A B => @lem4949874 A B y x s)). Qed.
Lemma lem4949876 {A B : Type'} : (@ex ((A -> B) -> A)) = (@ex ((A -> B) -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> A))). Qed.
Lemma lem4949877 {A B : Type'} (y : B) (s : A -> Prop) : (term862 A B y s) = (term850 A B y s).
Proof. exact (MK_COMB (@lem4949876 A B) (@lem4949875 A B y s)). Qed.
Lemma lem4949878 {A B : Type'} (y : B) : (term863 A B y) = (term851 A B y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4949877 A B y s)). Qed.
Lemma lem4949879 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4949880 {A B : Type'} (y : B) : (term855 A B y) = (term852 A B y).
Proof. exact (MK_COMB (@lem4949879 A) (@lem4949878 A B y)). Qed.
Lemma lem4949881 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4949882 {A B : Type'} (y : B) : (term864 A B y) = (term865 A B y).
Proof. exact (MK_COMB (@lem4949881) (@lem4949880 A B y)). Qed.
Lemma lem4949883 {A B : Type'} (y : B) (s : A -> Prop) : (term858 A B y s) = (term849 A B y s).
Proof. exact (eq_refl (term858 A B y s)). Qed.
Lemma lem4949884 {A B : Type'} (x : type631 A B) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem4949885 {A B : Type'} (y : B) (x : type631 A B) (s : A -> Prop) : (term866 A B y x s) = (term867 A B y x s).
Proof. exact (MK_COMB (@lem4949883 A B y s) (@lem4949884 A B x s)). Qed.
Lemma lem4949886 {A B : Type'} (y : B) (x : type631 A B) (s : A -> Prop) : (term867 A B y x s) = (term868 A B y x s).
Proof. exact (eq_refl (term867 A B y x s)). Qed.
Lemma lem4949887 {A B : Type'} (y : B) (x : type631 A B) (s : A -> Prop) : (term866 A B y x s) = (term868 A B y x s).
Proof. exact (TRANS (@lem4949885 A B y x s) (@lem4949886 A B y x s)). Qed.
Lemma lem4949888 {A B : Type'} (y : B) (x : type631 A B) : (term869 A B y x) = (term870 A B y x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4949887 A B y x s)). Qed.
Lemma lem4949889 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4949890 {A B : Type'} (y : B) (x : type631 A B) : (term871 A B y x) = (term872 A B y x).
Proof. exact (MK_COMB (@lem4949889 A) (@lem4949888 A B y x)). Qed.
Lemma lem4949891 {A B : Type'} (y : B) : (term873 A B y) = (term874 A B y).
Proof. exact (fun_ext (fun x : type631 A B => @lem4949890 A B y x)). Qed.
Lemma lem4949892 {A B : Type'} : (@ex ((A -> Prop) -> (A -> B) -> A)) = (@ex ((A -> Prop) -> (A -> B) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> B) -> A))). Qed.
Lemma lem4949893 {A B : Type'} (y : B) : (term856 A B y) = (term875 A B y).
Proof. exact (MK_COMB (@lem4949892 A B) (@lem4949891 A B y)). Qed.
Lemma lem4949894 {A B : Type'} (y : B) : ((term855 A B y) = (term856 A B y)) = ((term852 A B y) = (term875 A B y)).
Proof. exact (MK_COMB (@lem4949882 A B y) (@lem4949893 A B y)). Qed.
Lemma lem4949895 {A B : Type'} (y : B) : (term852 A B y) = (term875 A B y).
Proof. exact (EQ_MP (@lem4949894 A B y) (@lem4949869 A B y)). Qed.
Lemma lem4949896 {A B : Type'} (y : B) : (term791 A B y) = (term875 A B y).
Proof. exact (TRANS (@lem4949865 A B y) (@lem4949895 A B y)). Qed.
Lemma lem4949897 {A B : Type'} : (term798 A B) = (term876 A B).
Proof. exact (fun_ext (fun y : B => @lem4949896 A B y)). Qed.
Lemma lem4949898 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4949899 {A B : Type'} : (term813 A B) = (term877 A B).
Proof. exact (MK_COMB (@lem4949898 B) (@lem4949897 A B)). Qed.
Lemma lem4949901 {A B : Type'} (P : type1413 A B) : (term286 A B P) = (term287 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4949902 {A B : Type'} (P : type1437 A B) : (term878 A B P) = (term879 A B P).
Proof. exact (@lem4949901 B (type631 A B) P). Qed.
Lemma lem4949903 {A B : Type'} : (term880 A B) = (term881 A B).
Proof. exact (@lem4949902 A B (term882 A B)). Qed.
Lemma lem4949904 {A B : Type'} (y : B) : (term883 A B y) = (term874 A B y).
Proof. exact (eq_refl (term883 A B y)). Qed.
Lemma lem4949905 {A B : Type'} (x : type631 A B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4949906 {A B : Type'} (y : B) (x : type631 A B) : (term884 A B y x) = (term885 A B y x).
Proof. exact (MK_COMB (@lem4949904 A B y) (@lem4949905 A B x)). Qed.
Lemma lem4949907 {A B : Type'} (y : B) (x : type631 A B) : (term885 A B y x) = (term872 A B y x).
Proof. exact (eq_refl (term885 A B y x)). Qed.
Lemma lem4949908 {A B : Type'} (y : B) (x : type631 A B) : (term884 A B y x) = (term872 A B y x).
Proof. exact (TRANS (@lem4949906 A B y x) (@lem4949907 A B y x)). Qed.
Lemma lem4949909 {A B : Type'} (y : B) : (term886 A B y) = (term874 A B y).
Proof. exact (fun_ext (fun x : type631 A B => @lem4949908 A B y x)). Qed.
Lemma lem4949910 {A B : Type'} : (@ex ((A -> Prop) -> (A -> B) -> A)) = (@ex ((A -> Prop) -> (A -> B) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> B) -> A))). Qed.
Lemma lem4949911 {A B : Type'} (y : B) : (term887 A B y) = (term875 A B y).
Proof. exact (MK_COMB (@lem4949910 A B) (@lem4949909 A B y)). Qed.
Lemma lem4949912 {A B : Type'} : (term888 A B) = (term876 A B).
Proof. exact (fun_ext (fun y : B => @lem4949911 A B y)). Qed.
Lemma lem4949913 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4949914 {A B : Type'} : (term880 A B) = (term877 A B).
Proof. exact (MK_COMB (@lem4949913 B) (@lem4949912 A B)). Qed.
Lemma lem4949915 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4949916 {A B : Type'} : (term889 A B) = (term890 A B).
Proof. exact (MK_COMB (@lem4949915) (@lem4949914 A B)). Qed.
Lemma lem4949917 {A B : Type'} (y : B) : (term883 A B y) = (term874 A B y).
Proof. exact (eq_refl (term883 A B y)). Qed.
Lemma lem4949918 {A B : Type'} (x : type1448 A B) (y : B) : (x y) = (x y).
Proof. exact (eq_refl (x y)). Qed.
Lemma lem4949919 {A B : Type'} (x : type1448 A B) (y : B) : (term891 A B x y) = (term892 A B x y).
Proof. exact (MK_COMB (@lem4949917 A B y) (@lem4949918 A B x y)). Qed.
Lemma lem4949920 {A B : Type'} (x : type1448 A B) (y : B) : (term892 A B x y) = (term893 A B x y).
Proof. exact (eq_refl (term892 A B x y)). Qed.
Lemma lem4949921 {A B : Type'} (x : type1448 A B) (y : B) : (term891 A B x y) = (term893 A B x y).
Proof. exact (TRANS (@lem4949919 A B x y) (@lem4949920 A B x y)). Qed.
Lemma lem4949922 {A B : Type'} (x : type1448 A B) : (term894 A B x) = (term895 A B x).
Proof. exact (fun_ext (fun y : B => @lem4949921 A B x y)). Qed.
Lemma lem4949923 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4949924 {A B : Type'} (x : type1448 A B) : (term896 A B x) = (term897 A B x).
Proof. exact (MK_COMB (@lem4949923 B) (@lem4949922 A B x)). Qed.
Lemma lem4949925 {A B : Type'} : (term898 A B) = (term899 A B).
Proof. exact (fun_ext (fun x : type1448 A B => @lem4949924 A B x)). Qed.
Lemma lem4949926 {A B : Type'} : (@ex (B -> (A -> Prop) -> (A -> B) -> A)) = (@ex (B -> (A -> Prop) -> (A -> B) -> A)).
Proof. exact (eq_refl (@ex (B -> (A -> Prop) -> (A -> B) -> A))). Qed.
Lemma lem4949927 {A B : Type'} : (term881 A B) = (term900 A B).
Proof. exact (MK_COMB (@lem4949926 A B) (@lem4949925 A B)). Qed.
Lemma lem4949928 {A B : Type'} : ((term880 A B) = (term881 A B)) = ((term877 A B) = (term900 A B)).
Proof. exact (MK_COMB (@lem4949916 A B) (@lem4949927 A B)). Qed.
Lemma lem4949929 {A B : Type'} : (term877 A B) = (term900 A B).
Proof. exact (EQ_MP (@lem4949928 A B) (@lem4949903 A B)). Qed.
Lemma lem4949930 {A B : Type'} : (term813 A B) = (term900 A B).
Proof. exact (TRANS (@lem4949899 A B) (@lem4949929 A B)). Qed.
Lemma lem4949931 {A B : Type'} : (term810 A B) = (term810 A B).
Proof. exact (eq_refl (term810 A B)). Qed.
Lemma lem4949932 {A B : Type'} : (term814 A B) = (term901 A B).
Proof. exact (MK_COMB (@lem4949931 A B) (@lem4949930 A B)). Qed.
Lemma lem4949934 {A : Type'} (P : Prop) (Q : A -> Prop) : (term348 A P Q) = (term349 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4949935 {A B : Type'} (P : Prop) (Q : type719 A B) : (term902 A B P Q) = (term903 A B P Q).
Proof. exact (@lem4949934 (type1448 A B) P Q). Qed.
Lemma lem4949936 {A B : Type'} : (term904 A B) = (term905 A B).
Proof. exact (@lem4949935 A B (term808 A B) (term899 A B)). Qed.
Lemma lem4949937 {A B : Type'} (x : type1448 A B) : (term906 A B x) = (term897 A B x).
Proof. exact (eq_refl (term906 A B x)). Qed.
Lemma lem4949938 {A B : Type'} : (term907 A B) = (term899 A B).
Proof. exact (fun_ext (fun x : type1448 A B => @lem4949937 A B x)). Qed.
Lemma lem4949939 {A B : Type'} : (@ex (B -> (A -> Prop) -> (A -> B) -> A)) = (@ex (B -> (A -> Prop) -> (A -> B) -> A)).
Proof. exact (eq_refl (@ex (B -> (A -> Prop) -> (A -> B) -> A))). Qed.
Lemma lem4949940 {A B : Type'} : (term908 A B) = (term900 A B).
Proof. exact (MK_COMB (@lem4949939 A B) (@lem4949938 A B)). Qed.
Lemma lem4949941 {A B : Type'} : (term810 A B) = (term810 A B).
Proof. exact (eq_refl (term810 A B)). Qed.
Lemma lem4949942 {A B : Type'} : (term904 A B) = (term901 A B).
Proof. exact (MK_COMB (@lem4949941 A B) (@lem4949940 A B)). Qed.
Lemma lem4949943 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4949944 {A B : Type'} : (term909 A B) = (term910 A B).
Proof. exact (MK_COMB (@lem4949943) (@lem4949942 A B)). Qed.
Lemma lem4949945 {A B : Type'} (x : type1448 A B) : (term906 A B x) = (term897 A B x).
Proof. exact (eq_refl (term906 A B x)). Qed.
Lemma lem4949946 {A B : Type'} : (term810 A B) = (term810 A B).
Proof. exact (eq_refl (term810 A B)). Qed.
Lemma lem4949947 {A B : Type'} (x : type1448 A B) : (term911 A B x) = (term912 A B x).
Proof. exact (MK_COMB (@lem4949946 A B) (@lem4949945 A B x)). Qed.
Lemma lem4949948 {A B : Type'} : (term913 A B) = (term914 A B).
Proof. exact (fun_ext (fun x : type1448 A B => @lem4949947 A B x)). Qed.
Lemma lem4949949 {A B : Type'} : (@ex (B -> (A -> Prop) -> (A -> B) -> A)) = (@ex (B -> (A -> Prop) -> (A -> B) -> A)).
Proof. exact (eq_refl (@ex (B -> (A -> Prop) -> (A -> B) -> A))). Qed.
Lemma lem4949950 {A B : Type'} : (term905 A B) = (term915 A B).
Proof. exact (MK_COMB (@lem4949949 A B) (@lem4949948 A B)). Qed.
Lemma lem4949951 {A B : Type'} : ((term904 A B) = (term905 A B)) = ((term901 A B) = (term915 A B)).
Proof. exact (MK_COMB (@lem4949944 A B) (@lem4949950 A B)). Qed.
Lemma lem4949952 {A B : Type'} : (term901 A B) = (term915 A B).
Proof. exact (EQ_MP (@lem4949951 A B) (@lem4949936 A B)). Qed.
Lemma lem4949953 {A B : Type'} : (term814 A B) = (term915 A B).
Proof. exact (TRANS (@lem4949932 A B) (@lem4949952 A B)). Qed.
Lemma lem4949954 {A B : Type'} : (term748 A B) = (term915 A B).
Proof. exact (TRANS (@lem4949808 A B) (@lem4949953 A B)). Qed.
Lemma lem4949955 {A B : Type'} : (term83 A B) = (term915 A B).
Proof. exact (TRANS (@lem4949111 A B) (@lem4949954 A B)). Qed.
Lemma lem4949956 {A B : Type'} (h1 : term83 A B) : term915 A B.
Proof. exact (EQ_MP (@lem4949955 A B) (@lem4947221 A B h1)). Qed.
Lemma lem4949967 {B : Type'} (y : B) (f : B -> B) (x : B) (s : B -> Prop) : (term530 B y f x s) = (term531 B y f x s).
Proof. exact (@lem17045 (y = (f x)) (@IN B x s)). Qed.
Lemma lem4949970 {B : Type'} (y : B) (f : B -> B) (x : B) (s : B -> Prop) : (term167 B y f x s) = (term167 B y f x s).
Proof. exact (eq_refl (term167 B y f x s)). Qed.
Lemma lem4949971 {B : Type'} (P : B -> Prop) : (term196 B P) = (term197 B P).
Proof. exact (@lem18394 B P). Qed.
Lemma lem4949972 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term532 B y f s) = (term533 B y f s).
Proof. exact (@lem4949971 B (term168 B y f s)). Qed.
Lemma lem4949973 {B : Type'} (y : B) (f : B -> B) (x : B) (s : B -> Prop) : (term534 B y f s x) = (term167 B y f x s).
Proof. exact (eq_refl (term534 B y f s x)). Qed.
Lemma lem4949974 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4949975 {B : Type'} (y : B) (f : B -> B) (x : B) (s : B -> Prop) : (term535 B y f s x) = (term530 B y f x s).
Proof. exact (MK_COMB (@lem4949974) (@lem4949973 B y f x s)). Qed.
Lemma lem4949976 {B : Type'} (y : B) (f : B -> B) (x : B) (s : B -> Prop) : (term535 B y f s x) = (term531 B y f x s).
Proof. exact (TRANS (@lem4949975 B y f x s) (@lem4949967 B y f x s)). Qed.
Lemma lem4949977 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term536 B y f s) = (term537 B y f s).
Proof. exact (fun_ext (fun x : B => @lem4949976 B y f x s)). Qed.
Lemma lem4949978 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4949979 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term533 B y f s) = (term538 B y f s).
Proof. exact (MK_COMB (@lem4949978 B) (@lem4949977 B y f s)). Qed.
Lemma lem4949980 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term532 B y f s) = (term538 B y f s).
Proof. exact (TRANS (@lem4949972 B y f s) (@lem4949979 B y f s)). Qed.
Lemma lem4949981 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term168 B y f s) = (term168 B y f s).
Proof. exact (fun_ext (fun x : B => @lem4949970 B y f x s)). Qed.
Lemma lem4949982 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4949983 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term169 B y f s) = (term169 B y f s).
Proof. exact (MK_COMB (@lem4949982 B) (@lem4949981 B y f s)). Qed.
Lemma lem4949985 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term539 B y f s) = (term539 B y f s).
Proof. exact (eq_refl (term539 B y f s)). Qed.
Lemma lem4949986 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term540 B y f s) = (term540 B y f s).
Proof. exact (MK_COMB (@lem4949985 B y f s) (@lem4949983 B y f s)). Qed.
Lemma lem4949988 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term541 B y f s) = (term541 B y f s).
Proof. exact (eq_refl (term541 B y f s)). Qed.
Lemma lem4949989 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term542 B y f s) = (term543 B y f s).
Proof. exact (MK_COMB (@lem4949988 B y f s) (@lem4949980 B y f s)). Qed.
Lemma lem4949990 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4949991 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term544 B y f s) = (term545 B y f s).
Proof. exact (MK_COMB (@lem4949990) (@lem4949989 B y f s)). Qed.
Lemma lem4949992 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term546 B y f s) = (term547 B y f s).
Proof. exact (MK_COMB (@lem4949991 B y f s) (@lem4949986 B y f s)). Qed.
Lemma lem4949993 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : ((term171 B y f s) = (term169 B y f s)) = (term546 B y f s).
Proof. exact (@lem17784 (term171 B y f s) (term169 B y f s)). Qed.
Lemma lem4949994 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : ((term171 B y f s) = (term169 B y f s)) = (term547 B y f s).
Proof. exact (TRANS (@lem4949993 B y f s) (@lem4949992 B y f s)). Qed.
Lemma lem4949995 {B : Type'} (y : B) (s : B -> Prop) : (term172 B y s) = (term548 B y s).
Proof. exact (fun_ext (fun f : B -> B => @lem4949994 B y f s)). Qed.
Lemma lem4949996 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem4949997 {B : Type'} (y : B) (s : B -> Prop) : (term173 B y s) = (term549 B y s).
Proof. exact (MK_COMB (@lem4949996 B) (@lem4949995 B y s)). Qed.
Lemma lem4949998 {B : Type'} (y : B) : (term174 B y) = (term550 B y).
Proof. exact (fun_ext (fun s : B -> Prop => @lem4949997 B y s)). Qed.
Lemma lem4949999 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4950000 {B : Type'} (y : B) : (term175 B y) = (term551 B y).
Proof. exact (MK_COMB (@lem4949999 B) (@lem4949998 B y)). Qed.
Lemma lem4950001 {B : Type'} : (term176 B) = (term552 B).
Proof. exact (fun_ext (fun y : B => @lem4950000 B y)). Qed.
Lemma lem4950002 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4950003 {B : Type'} : (term84 B) = (term553 B).
Proof. exact (MK_COMB (@lem4950002 B) (@lem4950001 B)). Qed.
Lemma lem4950013 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term554 A P Q) = (term555 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4950014 {B : Type'} (P : type488 B) (Q : type488 B) : (term556 B P Q) = (term557 B P Q).
Proof. exact (@lem4950013 (B -> B) P Q). Qed.
Lemma lem4950015 {B : Type'} (y : B) (s : B -> Prop) : (term558 B y s) = (term559 B y s).
Proof. exact (@lem4950014 B (term560 B y s) (term561 B y s)). Qed.
Lemma lem4950016 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term562 B y s f) = (term543 B y f s).
Proof. exact (eq_refl (term562 B y s f)). Qed.
Lemma lem4950017 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4950018 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term563 B y s f) = (term545 B y f s).
Proof. exact (MK_COMB (@lem4950017) (@lem4950016 B y f s)). Qed.
Lemma lem4950019 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term564 B y s f) = (term540 B y f s).
Proof. exact (eq_refl (term564 B y s f)). Qed.
Lemma lem4950020 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term565 B y s f) = (term547 B y f s).
Proof. exact (MK_COMB (@lem4950018 B y f s) (@lem4950019 B y f s)). Qed.
Lemma lem4950021 {B : Type'} (y : B) (s : B -> Prop) : (term566 B y s) = (term548 B y s).
Proof. exact (fun_ext (fun f : B -> B => @lem4950020 B y f s)). Qed.
Lemma lem4950022 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem4950023 {B : Type'} (y : B) (s : B -> Prop) : (term558 B y s) = (term549 B y s).
Proof. exact (MK_COMB (@lem4950022 B) (@lem4950021 B y s)). Qed.
Lemma lem4950024 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4950025 {B : Type'} (y : B) (s : B -> Prop) : (term567 B y s) = (term568 B y s).
Proof. exact (MK_COMB (@lem4950024) (@lem4950023 B y s)). Qed.
Lemma lem4950026 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term562 B y s f) = (term543 B y f s).
Proof. exact (eq_refl (term562 B y s f)). Qed.
Lemma lem4950027 {B : Type'} (y : B) (s : B -> Prop) : (term569 B y s) = (term560 B y s).
Proof. exact (fun_ext (fun f : B -> B => @lem4950026 B y f s)). Qed.
Lemma lem4950028 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem4950029 {B : Type'} (y : B) (s : B -> Prop) : (term570 B y s) = (term571 B y s).
Proof. exact (MK_COMB (@lem4950028 B) (@lem4950027 B y s)). Qed.
Lemma lem4950030 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4950031 {B : Type'} (y : B) (s : B -> Prop) : (term572 B y s) = (term573 B y s).
Proof. exact (MK_COMB (@lem4950030) (@lem4950029 B y s)). Qed.
Lemma lem4950032 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term564 B y s f) = (term540 B y f s).
Proof. exact (eq_refl (term564 B y s f)). Qed.
Lemma lem4950033 {B : Type'} (y : B) (s : B -> Prop) : (term574 B y s) = (term561 B y s).
Proof. exact (fun_ext (fun f : B -> B => @lem4950032 B y f s)). Qed.
Lemma lem4950034 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem4950035 {B : Type'} (y : B) (s : B -> Prop) : (term575 B y s) = (term576 B y s).
Proof. exact (MK_COMB (@lem4950034 B) (@lem4950033 B y s)). Qed.
Lemma lem4950036 {B : Type'} (y : B) (s : B -> Prop) : (term559 B y s) = (term577 B y s).
Proof. exact (MK_COMB (@lem4950031 B y s) (@lem4950035 B y s)). Qed.
Lemma lem4950037 {B : Type'} (y : B) (s : B -> Prop) : ((term558 B y s) = (term559 B y s)) = ((term549 B y s) = (term577 B y s)).
Proof. exact (MK_COMB (@lem4950025 B y s) (@lem4950036 B y s)). Qed.
Lemma lem4950038 {B : Type'} (y : B) (s : B -> Prop) : (term549 B y s) = (term577 B y s).
Proof. exact (EQ_MP (@lem4950037 B y s) (@lem4950015 B y s)). Qed.
Lemma lem4950231 {B : Type'} (y : B) : (term550 B y) = (term578 B y).
Proof. exact (fun_ext (fun s : B -> Prop => @lem4950038 B y s)). Qed.
Lemma lem4950232 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4950233 {B : Type'} (y : B) : (term551 B y) = (term579 B y).
Proof. exact (MK_COMB (@lem4950232 B) (@lem4950231 B y)). Qed.
Lemma lem4950235 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term554 A P Q) = (term555 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4950236 {B : Type'} (P : type686 B) (Q : type686 B) : (term580 B P Q) = (term581 B P Q).
Proof. exact (@lem4950235 (B -> Prop) P Q). Qed.
Lemma lem4950237 {B : Type'} (y : B) : (term582 B y) = (term583 B y).
Proof. exact (@lem4950236 B (term584 B y) (term585 B y)). Qed.
Lemma lem4950238 {B : Type'} (y : B) (s : B -> Prop) : (term586 B y s) = (term571 B y s).
Proof. exact (eq_refl (term586 B y s)). Qed.
Lemma lem4950239 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4950240 {B : Type'} (y : B) (s : B -> Prop) : (term587 B y s) = (term573 B y s).
Proof. exact (MK_COMB (@lem4950239) (@lem4950238 B y s)). Qed.
Lemma lem4950241 {B : Type'} (y : B) (s : B -> Prop) : (term588 B y s) = (term576 B y s).
Proof. exact (eq_refl (term588 B y s)). Qed.
Lemma lem4950242 {B : Type'} (y : B) (s : B -> Prop) : (term589 B y s) = (term577 B y s).
Proof. exact (MK_COMB (@lem4950240 B y s) (@lem4950241 B y s)). Qed.
Lemma lem4950243 {B : Type'} (y : B) : (term590 B y) = (term578 B y).
Proof. exact (fun_ext (fun s : B -> Prop => @lem4950242 B y s)). Qed.
Lemma lem4950244 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4950245 {B : Type'} (y : B) : (term582 B y) = (term579 B y).
Proof. exact (MK_COMB (@lem4950244 B) (@lem4950243 B y)). Qed.
Lemma lem4950246 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4950247 {B : Type'} (y : B) : (term591 B y) = (term592 B y).
Proof. exact (MK_COMB (@lem4950246) (@lem4950245 B y)). Qed.
Lemma lem4950248 {B : Type'} (y : B) (s : B -> Prop) : (term586 B y s) = (term571 B y s).
Proof. exact (eq_refl (term586 B y s)). Qed.
Lemma lem4950249 {B : Type'} (y : B) : (term593 B y) = (term584 B y).
Proof. exact (fun_ext (fun s : B -> Prop => @lem4950248 B y s)). Qed.
Lemma lem4950250 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4950251 {B : Type'} (y : B) : (term594 B y) = (term595 B y).
Proof. exact (MK_COMB (@lem4950250 B) (@lem4950249 B y)). Qed.
Lemma lem4950252 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4950253 {B : Type'} (y : B) : (term596 B y) = (term597 B y).
Proof. exact (MK_COMB (@lem4950252) (@lem4950251 B y)). Qed.
Lemma lem4950254 {B : Type'} (y : B) (s : B -> Prop) : (term588 B y s) = (term576 B y s).
Proof. exact (eq_refl (term588 B y s)). Qed.
Lemma lem4950255 {B : Type'} (y : B) : (term598 B y) = (term585 B y).
Proof. exact (fun_ext (fun s : B -> Prop => @lem4950254 B y s)). Qed.
Lemma lem4950256 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4950257 {B : Type'} (y : B) : (term599 B y) = (term600 B y).
Proof. exact (MK_COMB (@lem4950256 B) (@lem4950255 B y)). Qed.
Lemma lem4950258 {B : Type'} (y : B) : (term583 B y) = (term601 B y).
Proof. exact (MK_COMB (@lem4950253 B y) (@lem4950257 B y)). Qed.
Lemma lem4950259 {B : Type'} (y : B) : ((term582 B y) = (term583 B y)) = ((term579 B y) = (term601 B y)).
Proof. exact (MK_COMB (@lem4950247 B y) (@lem4950258 B y)). Qed.
Lemma lem4950260 {B : Type'} (y : B) : (term579 B y) = (term601 B y).
Proof. exact (EQ_MP (@lem4950259 B y) (@lem4950237 B y)). Qed.
Lemma lem4950461 {B : Type'} (y : B) : (term551 B y) = (term601 B y).
Proof. exact (TRANS (@lem4950233 B y) (@lem4950260 B y)). Qed.
Lemma lem4950462 {B : Type'} : (term552 B) = (term602 B).
Proof. exact (fun_ext (fun y : B => @lem4950461 B y)). Qed.
Lemma lem4950463 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4950464 {B : Type'} : (term553 B) = (term603 B).
Proof. exact (MK_COMB (@lem4950463 B) (@lem4950462 B)). Qed.
Lemma lem4950466 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term554 A P Q) = (term555 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4950467 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term554 B P Q) = (term555 B P Q).
Proof. exact (@lem4950466 B P Q). Qed.
Lemma lem4950468 {B : Type'} : (term604 B) = (term605 B).
Proof. exact (@lem4950467 B (term606 B) (term607 B)). Qed.
Lemma lem4950469 {B : Type'} (y : B) : (term608 B y) = (term595 B y).
Proof. exact (eq_refl (term608 B y)). Qed.
Lemma lem4950470 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4950471 {B : Type'} (y : B) : (term609 B y) = (term597 B y).
Proof. exact (MK_COMB (@lem4950470) (@lem4950469 B y)). Qed.
Lemma lem4950472 {B : Type'} (y : B) : (term610 B y) = (term600 B y).
Proof. exact (eq_refl (term610 B y)). Qed.
Lemma lem4950473 {B : Type'} (y : B) : (term611 B y) = (term601 B y).
Proof. exact (MK_COMB (@lem4950471 B y) (@lem4950472 B y)). Qed.
Lemma lem4950474 {B : Type'} : (term612 B) = (term602 B).
Proof. exact (fun_ext (fun y : B => @lem4950473 B y)). Qed.
Lemma lem4950475 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4950476 {B : Type'} : (term604 B) = (term603 B).
Proof. exact (MK_COMB (@lem4950475 B) (@lem4950474 B)). Qed.
Lemma lem4950477 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4950478 {B : Type'} : (term613 B) = (term614 B).
Proof. exact (MK_COMB (@lem4950477) (@lem4950476 B)). Qed.
Lemma lem4950479 {B : Type'} (y : B) : (term608 B y) = (term595 B y).
Proof. exact (eq_refl (term608 B y)). Qed.
Lemma lem4950480 {B : Type'} : (term615 B) = (term606 B).
Proof. exact (fun_ext (fun y : B => @lem4950479 B y)). Qed.
Lemma lem4950481 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4950482 {B : Type'} : (term616 B) = (term617 B).
Proof. exact (MK_COMB (@lem4950481 B) (@lem4950480 B)). Qed.
Lemma lem4950483 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4950484 {B : Type'} : (term618 B) = (term619 B).
Proof. exact (MK_COMB (@lem4950483) (@lem4950482 B)). Qed.
Lemma lem4950485 {B : Type'} (y : B) : (term610 B y) = (term600 B y).
Proof. exact (eq_refl (term610 B y)). Qed.
Lemma lem4950486 {B : Type'} : (term620 B) = (term607 B).
Proof. exact (fun_ext (fun y : B => @lem4950485 B y)). Qed.
Lemma lem4950487 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4950488 {B : Type'} : (term621 B) = (term622 B).
Proof. exact (MK_COMB (@lem4950487 B) (@lem4950486 B)). Qed.
Lemma lem4950489 {B : Type'} : (term605 B) = (term623 B).
Proof. exact (MK_COMB (@lem4950484 B) (@lem4950488 B)). Qed.
Lemma lem4950490 {B : Type'} : ((term604 B) = (term605 B)) = ((term603 B) = (term623 B)).
Proof. exact (MK_COMB (@lem4950478 B) (@lem4950489 B)). Qed.
Lemma lem4950491 {B : Type'} : (term603 B) = (term623 B).
Proof. exact (EQ_MP (@lem4950490 B) (@lem4950468 B)). Qed.
Lemma lem4950700 {B : Type'} : (term553 B) = (term623 B).
Proof. exact (TRANS (@lem4950464 B) (@lem4950491 B)). Qed.
Lemma lem4950702 {A : Type'} (P : Prop) (Q : A -> Prop) : (term270 A P Q) = (term271 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4950703 {B : Type'} (P : Prop) (Q : B -> Prop) : (term270 B P Q) = (term271 B P Q).
Proof. exact (@lem4950702 B P Q). Qed.
Lemma lem4950704 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term624 B y f s) = (term625 B y f s).
Proof. exact (@lem4950703 B (term626 B y f s) (term168 B y f s)). Qed.
Lemma lem4950705 {B : Type'} (y : B) (f : B -> B) (x : B) (s : B -> Prop) : (term534 B y f s x) = (term167 B y f x s).
Proof. exact (eq_refl (term534 B y f s x)). Qed.
Lemma lem4950706 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term627 B y f s) = (term168 B y f s).
Proof. exact (fun_ext (fun x : B => @lem4950705 B y f x s)). Qed.
Lemma lem4950707 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4950708 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term628 B y f s) = (term169 B y f s).
Proof. exact (MK_COMB (@lem4950707 B) (@lem4950706 B y f s)). Qed.
Lemma lem4950709 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term539 B y f s) = (term539 B y f s).
Proof. exact (eq_refl (term539 B y f s)). Qed.
Lemma lem4950710 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term624 B y f s) = (term540 B y f s).
Proof. exact (MK_COMB (@lem4950709 B y f s) (@lem4950708 B y f s)). Qed.
Lemma lem4950711 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4950712 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term629 B y f s) = (term630 B y f s).
Proof. exact (MK_COMB (@lem4950711) (@lem4950710 B y f s)). Qed.
Lemma lem4950713 {B : Type'} (y : B) (f : B -> B) (x : B) (s : B -> Prop) : (term534 B y f s x) = (term167 B y f x s).
Proof. exact (eq_refl (term534 B y f s x)). Qed.
Lemma lem4950714 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term539 B y f s) = (term539 B y f s).
Proof. exact (eq_refl (term539 B y f s)). Qed.
Lemma lem4950715 {B : Type'} (y : B) (f : B -> B) (x : B) (s : B -> Prop) : (term631 B y f s x) = (term632 B y f x s).
Proof. exact (MK_COMB (@lem4950714 B y f s) (@lem4950713 B y f x s)). Qed.
Lemma lem4950716 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term633 B y f s) = (term634 B y f s).
Proof. exact (fun_ext (fun x : B => @lem4950715 B y f x s)). Qed.
Lemma lem4950717 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4950718 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term625 B y f s) = (term635 B y f s).
Proof. exact (MK_COMB (@lem4950717 B) (@lem4950716 B y f s)). Qed.
Lemma lem4950719 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : ((term624 B y f s) = (term625 B y f s)) = ((term540 B y f s) = (term635 B y f s)).
Proof. exact (MK_COMB (@lem4950712 B y f s) (@lem4950718 B y f s)). Qed.
Lemma lem4950720 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term540 B y f s) = (term635 B y f s).
Proof. exact (EQ_MP (@lem4950719 B y f s) (@lem4950704 B y f s)). Qed.
Lemma lem4950721 {B : Type'} (y : B) (s : B -> Prop) : (term561 B y s) = (term636 B y s).
Proof. exact (fun_ext (fun f : B -> B => @lem4950720 B y f s)). Qed.
Lemma lem4950722 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem4950723 {B : Type'} (y : B) (s : B -> Prop) : (term576 B y s) = (term637 B y s).
Proof. exact (MK_COMB (@lem4950722 B) (@lem4950721 B y s)). Qed.
Lemma lem4950725 {A B : Type'} (P : type1413 A B) : (term286 A B P) = (term287 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4950726 {B : Type'} (P : type486 B) : (term638 B P) = (term639 B P).
Proof. exact (@lem4950725 (B -> B) B P). Qed.
Lemma lem4950727 {B : Type'} (y : B) (s : B -> Prop) : (term640 B y s) = (term641 B y s).
Proof. exact (@lem4950726 B (term642 B y s)). Qed.
Lemma lem4950728 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term643 B y s f) = (term634 B y f s).
Proof. exact (eq_refl (term643 B y s f)). Qed.
Lemma lem4950729 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4950730 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) (x : B) : (term644 B y s f x) = (term645 B y f s x).
Proof. exact (MK_COMB (@lem4950728 B y f s) (@lem4950729 B x)). Qed.
Lemma lem4950731 {B : Type'} (y : B) (f : B -> B) (x : B) (s : B -> Prop) : (term645 B y f s x) = (term632 B y f x s).
Proof. exact (eq_refl (term645 B y f s x)). Qed.
Lemma lem4950732 {B : Type'} (y : B) (f : B -> B) (x : B) (s : B -> Prop) : (term644 B y s f x) = (term632 B y f x s).
Proof. exact (TRANS (@lem4950730 B y f s x) (@lem4950731 B y f x s)). Qed.
Lemma lem4950733 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term646 B y s f) = (term634 B y f s).
Proof. exact (fun_ext (fun x : B => @lem4950732 B y f x s)). Qed.
Lemma lem4950734 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4950735 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term647 B y s f) = (term635 B y f s).
Proof. exact (MK_COMB (@lem4950734 B) (@lem4950733 B y f s)). Qed.
Lemma lem4950736 {B : Type'} (y : B) (s : B -> Prop) : (term648 B y s) = (term636 B y s).
Proof. exact (fun_ext (fun f : B -> B => @lem4950735 B y f s)). Qed.
Lemma lem4950737 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem4950738 {B : Type'} (y : B) (s : B -> Prop) : (term640 B y s) = (term637 B y s).
Proof. exact (MK_COMB (@lem4950737 B) (@lem4950736 B y s)). Qed.
Lemma lem4950739 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4950740 {B : Type'} (y : B) (s : B -> Prop) : (term649 B y s) = (term650 B y s).
Proof. exact (MK_COMB (@lem4950739) (@lem4950738 B y s)). Qed.
Lemma lem4950741 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term643 B y s f) = (term634 B y f s).
Proof. exact (eq_refl (term643 B y s f)). Qed.
Lemma lem4950742 {B : Type'} (x : type487 B) (f : B -> B) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem4950743 {B : Type'} (y : B) (s : B -> Prop) (x : type487 B) (f : B -> B) : (term651 B y s x f) = (term652 B y s x f).
Proof. exact (MK_COMB (@lem4950741 B y f s) (@lem4950742 B x f)). Qed.
Lemma lem4950744 {B : Type'} (y : B) (x : type487 B) (f : B -> B) (s : B -> Prop) : (term652 B y s x f) = (term653 B y x f s).
Proof. exact (eq_refl (term652 B y s x f)). Qed.
Lemma lem4950745 {B : Type'} (y : B) (x : type487 B) (f : B -> B) (s : B -> Prop) : (term651 B y s x f) = (term653 B y x f s).
Proof. exact (TRANS (@lem4950743 B y s x f) (@lem4950744 B y x f s)). Qed.
Lemma lem4950746 {B : Type'} (y : B) (x : type487 B) (s : B -> Prop) : (term654 B y s x) = (term655 B y x s).
Proof. exact (fun_ext (fun f : B -> B => @lem4950745 B y x f s)). Qed.
Lemma lem4950747 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem4950748 {B : Type'} (y : B) (x : type487 B) (s : B -> Prop) : (term656 B y s x) = (term657 B y x s).
Proof. exact (MK_COMB (@lem4950747 B) (@lem4950746 B y x s)). Qed.
Lemma lem4950749 {B : Type'} (y : B) (s : B -> Prop) : (term658 B y s) = (term659 B y s).
Proof. exact (fun_ext (fun x : type487 B => @lem4950748 B y x s)). Qed.
Lemma lem4950750 {B : Type'} : (@ex ((B -> B) -> B)) = (@ex ((B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B) -> B))). Qed.
Lemma lem4950751 {B : Type'} (y : B) (s : B -> Prop) : (term641 B y s) = (term660 B y s).
Proof. exact (MK_COMB (@lem4950750 B) (@lem4950749 B y s)). Qed.
Lemma lem4950752 {B : Type'} (y : B) (s : B -> Prop) : ((term640 B y s) = (term641 B y s)) = ((term637 B y s) = (term660 B y s)).
Proof. exact (MK_COMB (@lem4950740 B y s) (@lem4950751 B y s)). Qed.
Lemma lem4950753 {B : Type'} (y : B) (s : B -> Prop) : (term637 B y s) = (term660 B y s).
Proof. exact (EQ_MP (@lem4950752 B y s) (@lem4950727 B y s)). Qed.
Lemma lem4950754 {B : Type'} (y : B) (s : B -> Prop) : (term576 B y s) = (term660 B y s).
Proof. exact (TRANS (@lem4950723 B y s) (@lem4950753 B y s)). Qed.
Lemma lem4950755 {B : Type'} (y : B) : (term585 B y) = (term661 B y).
Proof. exact (fun_ext (fun s : B -> Prop => @lem4950754 B y s)). Qed.
Lemma lem4950756 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4950757 {B : Type'} (y : B) : (term600 B y) = (term662 B y).
Proof. exact (MK_COMB (@lem4950756 B) (@lem4950755 B y)). Qed.
Lemma lem4950759 {A B : Type'} (P : type1413 A B) : (term286 A B P) = (term287 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4950760 {B : Type'} (P : type587 B) : (term663 B P) = (term664 B P).
Proof. exact (@lem4950759 (B -> Prop) (type487 B) P). Qed.
Lemma lem4950761 {B : Type'} (y : B) : (term665 B y) = (term666 B y).
Proof. exact (@lem4950760 B (term667 B y)). Qed.
Lemma lem4950762 {B : Type'} (y : B) (s : B -> Prop) : (term668 B y s) = (term659 B y s).
Proof. exact (eq_refl (term668 B y s)). Qed.
Lemma lem4950763 {B : Type'} (x : type487 B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4950764 {B : Type'} (y : B) (s : B -> Prop) (x : type487 B) : (term669 B y s x) = (term670 B y s x).
Proof. exact (MK_COMB (@lem4950762 B y s) (@lem4950763 B x)). Qed.
Lemma lem4950765 {B : Type'} (y : B) (x : type487 B) (s : B -> Prop) : (term670 B y s x) = (term657 B y x s).
Proof. exact (eq_refl (term670 B y s x)). Qed.
Lemma lem4950766 {B : Type'} (y : B) (x : type487 B) (s : B -> Prop) : (term669 B y s x) = (term657 B y x s).
Proof. exact (TRANS (@lem4950764 B y s x) (@lem4950765 B y x s)). Qed.
Lemma lem4950767 {B : Type'} (y : B) (s : B -> Prop) : (term671 B y s) = (term659 B y s).
Proof. exact (fun_ext (fun x : type487 B => @lem4950766 B y x s)). Qed.
Lemma lem4950768 {B : Type'} : (@ex ((B -> B) -> B)) = (@ex ((B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B) -> B))). Qed.
Lemma lem4950769 {B : Type'} (y : B) (s : B -> Prop) : (term672 B y s) = (term660 B y s).
Proof. exact (MK_COMB (@lem4950768 B) (@lem4950767 B y s)). Qed.
Lemma lem4950770 {B : Type'} (y : B) : (term673 B y) = (term661 B y).
Proof. exact (fun_ext (fun s : B -> Prop => @lem4950769 B y s)). Qed.
Lemma lem4950771 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4950772 {B : Type'} (y : B) : (term665 B y) = (term662 B y).
Proof. exact (MK_COMB (@lem4950771 B) (@lem4950770 B y)). Qed.
Lemma lem4950773 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4950774 {B : Type'} (y : B) : (term674 B y) = (term675 B y).
Proof. exact (MK_COMB (@lem4950773) (@lem4950772 B y)). Qed.
Lemma lem4950775 {B : Type'} (y : B) (s : B -> Prop) : (term668 B y s) = (term659 B y s).
Proof. exact (eq_refl (term668 B y s)). Qed.
Lemma lem4950776 {B : Type'} (x : type623 B) (s : B -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem4950777 {B : Type'} (y : B) (x : type623 B) (s : B -> Prop) : (term676 B y x s) = (term677 B y x s).
Proof. exact (MK_COMB (@lem4950775 B y s) (@lem4950776 B x s)). Qed.
Lemma lem4950778 {B : Type'} (y : B) (x : type623 B) (s : B -> Prop) : (term677 B y x s) = (term678 B y x s).
Proof. exact (eq_refl (term677 B y x s)). Qed.
Lemma lem4950779 {B : Type'} (y : B) (x : type623 B) (s : B -> Prop) : (term676 B y x s) = (term678 B y x s).
Proof. exact (TRANS (@lem4950777 B y x s) (@lem4950778 B y x s)). Qed.
Lemma lem4950780 {B : Type'} (y : B) (x : type623 B) : (term679 B y x) = (term680 B y x).
Proof. exact (fun_ext (fun s : B -> Prop => @lem4950779 B y x s)). Qed.
Lemma lem4950781 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4950782 {B : Type'} (y : B) (x : type623 B) : (term681 B y x) = (term682 B y x).
Proof. exact (MK_COMB (@lem4950781 B) (@lem4950780 B y x)). Qed.
Lemma lem4950783 {B : Type'} (y : B) : (term683 B y) = (term684 B y).
Proof. exact (fun_ext (fun x : type623 B => @lem4950782 B y x)). Qed.
Lemma lem4950784 {B : Type'} : (@ex ((B -> Prop) -> (B -> B) -> B)) = (@ex ((B -> Prop) -> (B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> (B -> B) -> B))). Qed.
Lemma lem4950785 {B : Type'} (y : B) : (term666 B y) = (term685 B y).
Proof. exact (MK_COMB (@lem4950784 B) (@lem4950783 B y)). Qed.
Lemma lem4950786 {B : Type'} (y : B) : ((term665 B y) = (term666 B y)) = ((term662 B y) = (term685 B y)).
Proof. exact (MK_COMB (@lem4950774 B y) (@lem4950785 B y)). Qed.
Lemma lem4950787 {B : Type'} (y : B) : (term662 B y) = (term685 B y).
Proof. exact (EQ_MP (@lem4950786 B y) (@lem4950761 B y)). Qed.
Lemma lem4950788 {B : Type'} (y : B) : (term600 B y) = (term685 B y).
Proof. exact (TRANS (@lem4950757 B y) (@lem4950787 B y)). Qed.
Lemma lem4950789 {B : Type'} : (term607 B) = (term686 B).
Proof. exact (fun_ext (fun y : B => @lem4950788 B y)). Qed.
Lemma lem4950790 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4950791 {B : Type'} : (term622 B) = (term687 B).
Proof. exact (MK_COMB (@lem4950790 B) (@lem4950789 B)). Qed.
Lemma lem4950793 {A B : Type'} (P : type1413 A B) : (term286 A B P) = (term287 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4950794 {B : Type'} (P : type1356 B) : (term688 B P) = (term689 B P).
Proof. exact (@lem4950793 B (type623 B) P). Qed.
Lemma lem4950795 {B : Type'} : (term690 B) = (term691 B).
Proof. exact (@lem4950794 B (term692 B)). Qed.
Lemma lem4950796 {B : Type'} (y : B) : (term693 B y) = (term684 B y).
Proof. exact (eq_refl (term693 B y)). Qed.
Lemma lem4950797 {B : Type'} (x : type623 B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4950798 {B : Type'} (y : B) (x : type623 B) : (term694 B y x) = (term695 B y x).
Proof. exact (MK_COMB (@lem4950796 B y) (@lem4950797 B x)). Qed.
Lemma lem4950799 {B : Type'} (y : B) (x : type623 B) : (term695 B y x) = (term682 B y x).
Proof. exact (eq_refl (term695 B y x)). Qed.
Lemma lem4950800 {B : Type'} (y : B) (x : type623 B) : (term694 B y x) = (term682 B y x).
Proof. exact (TRANS (@lem4950798 B y x) (@lem4950799 B y x)). Qed.
Lemma lem4950801 {B : Type'} (y : B) : (term696 B y) = (term684 B y).
Proof. exact (fun_ext (fun x : type623 B => @lem4950800 B y x)). Qed.
Lemma lem4950802 {B : Type'} : (@ex ((B -> Prop) -> (B -> B) -> B)) = (@ex ((B -> Prop) -> (B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> (B -> B) -> B))). Qed.
Lemma lem4950803 {B : Type'} (y : B) : (term697 B y) = (term685 B y).
Proof. exact (MK_COMB (@lem4950802 B) (@lem4950801 B y)). Qed.
Lemma lem4950804 {B : Type'} : (term698 B) = (term686 B).
Proof. exact (fun_ext (fun y : B => @lem4950803 B y)). Qed.
Lemma lem4950805 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4950806 {B : Type'} : (term690 B) = (term687 B).
Proof. exact (MK_COMB (@lem4950805 B) (@lem4950804 B)). Qed.
Lemma lem4950807 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4950808 {B : Type'} : (term699 B) = (term700 B).
Proof. exact (MK_COMB (@lem4950807) (@lem4950806 B)). Qed.
Lemma lem4950809 {B : Type'} (y : B) : (term693 B y) = (term684 B y).
Proof. exact (eq_refl (term693 B y)). Qed.
Lemma lem4950810 {B : Type'} (x : type1361 B) (y : B) : (x y) = (x y).
Proof. exact (eq_refl (x y)). Qed.
Lemma lem4950811 {B : Type'} (x : type1361 B) (y : B) : (term701 B x y) = (term702 B x y).
Proof. exact (MK_COMB (@lem4950809 B y) (@lem4950810 B x y)). Qed.
Lemma lem4950812 {B : Type'} (x : type1361 B) (y : B) : (term702 B x y) = (term703 B x y).
Proof. exact (eq_refl (term702 B x y)). Qed.
Lemma lem4950813 {B : Type'} (x : type1361 B) (y : B) : (term701 B x y) = (term703 B x y).
Proof. exact (TRANS (@lem4950811 B x y) (@lem4950812 B x y)). Qed.
Lemma lem4950814 {B : Type'} (x : type1361 B) : (term704 B x) = (term705 B x).
Proof. exact (fun_ext (fun y : B => @lem4950813 B x y)). Qed.
Lemma lem4950815 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4950816 {B : Type'} (x : type1361 B) : (term706 B x) = (term707 B x).
Proof. exact (MK_COMB (@lem4950815 B) (@lem4950814 B x)). Qed.
Lemma lem4950817 {B : Type'} : (term708 B) = (term709 B).
Proof. exact (fun_ext (fun x : type1361 B => @lem4950816 B x)). Qed.
Lemma lem4950818 {B : Type'} : (@ex (B -> (B -> Prop) -> (B -> B) -> B)) = (@ex (B -> (B -> Prop) -> (B -> B) -> B)).
Proof. exact (eq_refl (@ex (B -> (B -> Prop) -> (B -> B) -> B))). Qed.
Lemma lem4950819 {B : Type'} : (term691 B) = (term710 B).
Proof. exact (MK_COMB (@lem4950818 B) (@lem4950817 B)). Qed.
Lemma lem4950820 {B : Type'} : ((term690 B) = (term691 B)) = ((term687 B) = (term710 B)).
Proof. exact (MK_COMB (@lem4950808 B) (@lem4950819 B)). Qed.
Lemma lem4950821 {B : Type'} : (term687 B) = (term710 B).
Proof. exact (EQ_MP (@lem4950820 B) (@lem4950795 B)). Qed.
Lemma lem4950822 {B : Type'} : (term622 B) = (term710 B).
Proof. exact (TRANS (@lem4950791 B) (@lem4950821 B)). Qed.
Lemma lem4950823 {B : Type'} : (term619 B) = (term619 B).
Proof. exact (eq_refl (term619 B)). Qed.
Lemma lem4950824 {B : Type'} : (term623 B) = (term711 B).
Proof. exact (MK_COMB (@lem4950823 B) (@lem4950822 B)). Qed.
Lemma lem4950826 {A : Type'} (P : Prop) (Q : A -> Prop) : (term348 A P Q) = (term349 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4950827 {B : Type'} (P : Prop) (Q : type391 B) : (term712 B P Q) = (term713 B P Q).
Proof. exact (@lem4950826 (type1361 B) P Q). Qed.
Lemma lem4950828 {B : Type'} : (term714 B) = (term715 B).
Proof. exact (@lem4950827 B (term617 B) (term709 B)). Qed.
Lemma lem4950829 {B : Type'} (x : type1361 B) : (term716 B x) = (term707 B x).
Proof. exact (eq_refl (term716 B x)). Qed.
Lemma lem4950830 {B : Type'} : (term717 B) = (term709 B).
Proof. exact (fun_ext (fun x : type1361 B => @lem4950829 B x)). Qed.
Lemma lem4950831 {B : Type'} : (@ex (B -> (B -> Prop) -> (B -> B) -> B)) = (@ex (B -> (B -> Prop) -> (B -> B) -> B)).
Proof. exact (eq_refl (@ex (B -> (B -> Prop) -> (B -> B) -> B))). Qed.
Lemma lem4950832 {B : Type'} : (term718 B) = (term710 B).
Proof. exact (MK_COMB (@lem4950831 B) (@lem4950830 B)). Qed.
Lemma lem4950833 {B : Type'} : (term619 B) = (term619 B).
Proof. exact (eq_refl (term619 B)). Qed.
Lemma lem4950834 {B : Type'} : (term714 B) = (term711 B).
Proof. exact (MK_COMB (@lem4950833 B) (@lem4950832 B)). Qed.
Lemma lem4950835 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4950836 {B : Type'} : (term719 B) = (term720 B).
Proof. exact (MK_COMB (@lem4950835) (@lem4950834 B)). Qed.
Lemma lem4950837 {B : Type'} (x : type1361 B) : (term716 B x) = (term707 B x).
Proof. exact (eq_refl (term716 B x)). Qed.
Lemma lem4950838 {B : Type'} : (term619 B) = (term619 B).
Proof. exact (eq_refl (term619 B)). Qed.
Lemma lem4950839 {B : Type'} (x : type1361 B) : (term721 B x) = (term722 B x).
Proof. exact (MK_COMB (@lem4950838 B) (@lem4950837 B x)). Qed.
Lemma lem4950840 {B : Type'} : (term723 B) = (term724 B).
Proof. exact (fun_ext (fun x : type1361 B => @lem4950839 B x)). Qed.
Lemma lem4950841 {B : Type'} : (@ex (B -> (B -> Prop) -> (B -> B) -> B)) = (@ex (B -> (B -> Prop) -> (B -> B) -> B)).
Proof. exact (eq_refl (@ex (B -> (B -> Prop) -> (B -> B) -> B))). Qed.
Lemma lem4950842 {B : Type'} : (term715 B) = (term725 B).
Proof. exact (MK_COMB (@lem4950841 B) (@lem4950840 B)). Qed.
Lemma lem4950843 {B : Type'} : ((term714 B) = (term715 B)) = ((term711 B) = (term725 B)).
Proof. exact (MK_COMB (@lem4950836 B) (@lem4950842 B)). Qed.
Lemma lem4950844 {B : Type'} : (term711 B) = (term725 B).
Proof. exact (EQ_MP (@lem4950843 B) (@lem4950828 B)). Qed.
Lemma lem4950845 {B : Type'} : (term623 B) = (term725 B).
Proof. exact (TRANS (@lem4950824 B) (@lem4950844 B)). Qed.
Lemma lem4950846 {B : Type'} : (term553 B) = (term725 B).
Proof. exact (TRANS (@lem4950700 B) (@lem4950845 B)). Qed.
Lemma lem4950847 {B : Type'} : (term84 B) = (term725 B).
Proof. exact (TRANS (@lem4950003 B) (@lem4950846 B)). Qed.
Lemma lem4950848 {B : Type'} (h1 : term84 B) : term725 B.
Proof. exact (EQ_MP (@lem4950847 B) (@lem4947222 B h1)). Qed.
Lemma lem4950859 {A : Type'} (y : A -> Prop) (f : type1402 A) (x : A) (s : A -> Prop) : (term916 A y f x s) = (term917 A y f x s).
Proof. exact (@lem17045 (y = (f x)) (@IN A x s)). Qed.
Lemma lem4950862 {A : Type'} (y : A -> Prop) (f : type1402 A) (x : A) (s : A -> Prop) : (term157 A y f x s) = (term157 A y f x s).
Proof. exact (eq_refl (term157 A y f x s)). Qed.
Lemma lem4950863 {A : Type'} (P : A -> Prop) : (term196 A P) = (term197 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem4950864 {A : Type'} (y : A -> Prop) (f : type1402 A) (s : A -> Prop) : (term918 A y f s) = (term919 A y f s).
Proof. exact (@lem4950863 A (term158 A y f s)). Qed.
Lemma lem4950865 {A : Type'} (y : A -> Prop) (f : type1402 A) (x : A) (s : A -> Prop) : (term920 A y f s x) = (term157 A y f x s).
Proof. exact (eq_refl (term920 A y f s x)). Qed.
Lemma lem4950866 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4950867 {A : Type'} (y : A -> Prop) (f : type1402 A) (x : A) (s : A -> Prop) : (term921 A y f s x) = (term916 A y f x s).
Proof. exact (MK_COMB (@lem4950866) (@lem4950865 A y f x s)). Qed.
Lemma lem4950868 {A : Type'} (y : A -> Prop) (f : type1402 A) (x : A) (s : A -> Prop) : (term921 A y f s x) = (term917 A y f x s).
Proof. exact (TRANS (@lem4950867 A y f x s) (@lem4950859 A y f x s)). Qed.
Lemma lem4950869 {A : Type'} (y : A -> Prop) (f : type1402 A) (s : A -> Prop) : (term922 A y f s) = (term923 A y f s).
Proof. exact (fun_ext (fun x : A => @lem4950868 A y f x s)). Qed.
Lemma lem4950870 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4950871 {A : Type'} (y : A -> Prop) (f : type1402 A) (s : A -> Prop) : (term919 A y f s) = (term924 A y f s).
Proof. exact (MK_COMB (@lem4950870 A) (@lem4950869 A y f s)). Qed.
Lemma lem4950872 {A : Type'} (y : A -> Prop) (f : type1402 A) (s : A -> Prop) : (term918 A y f s) = (term924 A y f s).
Proof. exact (TRANS (@lem4950864 A y f s) (@lem4950871 A y f s)). Qed.
Lemma lem4950873 {A : Type'} (y : A -> Prop) (f : type1402 A) (s : A -> Prop) : (term158 A y f s) = (term158 A y f s).
Proof. exact (fun_ext (fun x : A => @lem4950862 A y f x s)). Qed.
Lemma lem4950874 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4950875 {A : Type'} (y : A -> Prop) (f : type1402 A) (s : A -> Prop) : (term159 A y f s) = (term159 A y f s).
Proof. exact (MK_COMB (@lem4950874 A) (@lem4950873 A y f s)). Qed.
Lemma lem4950877 {A : Type'} (y : A -> Prop) (f : type1402 A) (s : A -> Prop) : (term925 A y f s) = (term925 A y f s).
Proof. exact (eq_refl (term925 A y f s)). Qed.
Lemma lem4950878 {A : Type'} (y : A -> Prop) (f : type1402 A) (s : A -> Prop) : (term926 A y f s) = (term926 A y f s).
Proof. exact (MK_COMB (@lem4950877 A y f s) (@lem4950875 A y f s)). Qed.
Lemma lem4950880 {A : Type'} (y : A -> Prop) (f : type1402 A) (s : A -> Prop) : (term927 A y f s) = (term927 A y f s).
Proof. exact (eq_refl (term927 A y f s)). Qed.
Lemma lem4950881 {A : Type'} (y : A -> Prop) (f : type1402 A) (s : A -> Prop) : (term928 A y f s) = (term929 A y f s).
Proof. exact (MK_COMB (@lem4950880 A y f s) (@lem4950872 A y f s)). Qed.
Lemma lem4950882 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4950883 {A : Type'} (y : A -> Prop) (f : type1402 A) (s : A -> Prop) : (term930 A y f s) = (term931 A y f s).
Proof. exact (MK_COMB (@lem4950882) (@lem4950881 A y f s)). Qed.
Lemma lem4950884 {A : Type'} (y : A -> Prop) (f : type1402 A) (s : A -> Prop) : (term932 A y f s) = (term933 A y f s).
Proof. exact (MK_COMB (@lem4950883 A y f s) (@lem4950878 A y f s)). Qed.
Lemma lem4950885 {A : Type'} (y : A -> Prop) (f : type1402 A) (s : A -> Prop) : ((term161 A y f s) = (term159 A y f s)) = (term932 A y f s).
Proof. exact (@lem17784 (term161 A y f s) (term159 A y f s)). Qed.
Lemma lem4950886 {A : Type'} (y : A -> Prop) (f : type1402 A) (s : A -> Prop) : ((term161 A y f s) = (term159 A y f s)) = (term933 A y f s).
Proof. exact (TRANS (@lem4950885 A y f s) (@lem4950884 A y f s)). Qed.
Lemma lem4950887 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term162 A y s) = (term934 A y s).
Proof. exact (fun_ext (fun f : type1402 A => @lem4950886 A y f s)). Qed.
Lemma lem4950888 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem4950889 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term163 A y s) = (term935 A y s).
Proof. exact (MK_COMB (@lem4950888 A) (@lem4950887 A y s)). Qed.
Lemma lem4950890 {A : Type'} (y : A -> Prop) : (term164 A y) = (term936 A y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4950889 A y s)). Qed.
Lemma lem4950891 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4950892 {A : Type'} (y : A -> Prop) : (term165 A y) = (term937 A y).
Proof. exact (MK_COMB (@lem4950891 A) (@lem4950890 A y)). Qed.
Lemma lem4950893 {A : Type'} : (term166 A) = (term938 A).
Proof. exact (fun_ext (fun y : A -> Prop => @lem4950892 A y)). Qed.
Lemma lem4950894 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4950895 {A : Type'} : (term87 A) = (term939 A).
Proof. exact (MK_COMB (@lem4950894 A) (@lem4950893 A)). Qed.
Lemma lem4950905 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term554 A P Q) = (term555 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4950906 {A : Type'} (P : type421 A) (Q : type421 A) : (term940 A P Q) = (term941 A P Q).
Proof. exact (@lem4950905 (type1402 A) P Q). Qed.
Lemma lem4950907 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term942 A y s) = (term943 A y s).
Proof. exact (@lem4950906 A (term944 A y s) (term945 A y s)). Qed.
Lemma lem4950908 {A : Type'} (y : A -> Prop) (f : type1402 A) (s : A -> Prop) : (term946 A y s f) = (term929 A y f s).
Proof. exact (eq_refl (term946 A y s f)). Qed.
Lemma lem4950909 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4950910 {A : Type'} (y : A -> Prop) (f : type1402 A) (s : A -> Prop) : (term947 A y s f) = (term931 A y f s).
Proof. exact (MK_COMB (@lem4950909) (@lem4950908 A y f s)). Qed.
Lemma lem4950911 {A : Type'} (y : A -> Prop) (f : type1402 A) (s : A -> Prop) : (term948 A y s f) = (term926 A y f s).
Proof. exact (eq_refl (term948 A y s f)). Qed.
Lemma lem4950912 {A : Type'} (y : A -> Prop) (f : type1402 A) (s : A -> Prop) : (term949 A y s f) = (term933 A y f s).
Proof. exact (MK_COMB (@lem4950910 A y f s) (@lem4950911 A y f s)). Qed.
Lemma lem4950913 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term950 A y s) = (term934 A y s).
Proof. exact (fun_ext (fun f : type1402 A => @lem4950912 A y f s)). Qed.
Lemma lem4950914 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem4950915 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term942 A y s) = (term935 A y s).
Proof. exact (MK_COMB (@lem4950914 A) (@lem4950913 A y s)). Qed.
Lemma lem4950916 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4950917 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term951 A y s) = (term952 A y s).
Proof. exact (MK_COMB (@lem4950916) (@lem4950915 A y s)). Qed.
Lemma lem4950918 {A : Type'} (y : A -> Prop) (f : type1402 A) (s : A -> Prop) : (term946 A y s f) = (term929 A y f s).
Proof. exact (eq_refl (term946 A y s f)). Qed.
Lemma lem4950919 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term953 A y s) = (term944 A y s).
Proof. exact (fun_ext (fun f : type1402 A => @lem4950918 A y f s)). Qed.
Lemma lem4950920 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem4950921 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term954 A y s) = (term955 A y s).
Proof. exact (MK_COMB (@lem4950920 A) (@lem4950919 A y s)). Qed.
Lemma lem4950922 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4950923 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term956 A y s) = (term957 A y s).
Proof. exact (MK_COMB (@lem4950922) (@lem4950921 A y s)). Qed.
Lemma lem4950924 {A : Type'} (y : A -> Prop) (f : type1402 A) (s : A -> Prop) : (term948 A y s f) = (term926 A y f s).
Proof. exact (eq_refl (term948 A y s f)). Qed.
Lemma lem4950925 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term958 A y s) = (term945 A y s).
Proof. exact (fun_ext (fun f : type1402 A => @lem4950924 A y f s)). Qed.
Lemma lem4950926 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem4950927 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term959 A y s) = (term960 A y s).
Proof. exact (MK_COMB (@lem4950926 A) (@lem4950925 A y s)). Qed.
Lemma lem4950928 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term943 A y s) = (term961 A y s).
Proof. exact (MK_COMB (@lem4950923 A y s) (@lem4950927 A y s)). Qed.
Lemma lem4950929 {A : Type'} (y : A -> Prop) (s : A -> Prop) : ((term942 A y s) = (term943 A y s)) = ((term935 A y s) = (term961 A y s)).
Proof. exact (MK_COMB (@lem4950917 A y s) (@lem4950928 A y s)). Qed.
Lemma lem4950930 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term935 A y s) = (term961 A y s).
Proof. exact (EQ_MP (@lem4950929 A y s) (@lem4950907 A y s)). Qed.
Lemma lem4951123 {A : Type'} (y : A -> Prop) : (term936 A y) = (term962 A y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4950930 A y s)). Qed.
Lemma lem4951124 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4951125 {A : Type'} (y : A -> Prop) : (term937 A y) = (term963 A y).
Proof. exact (MK_COMB (@lem4951124 A) (@lem4951123 A y)). Qed.
Lemma lem4951127 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term554 A P Q) = (term555 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4951128 {A : Type'} (P : type686 A) (Q : type686 A) : (term580 A P Q) = (term581 A P Q).
Proof. exact (@lem4951127 (A -> Prop) P Q). Qed.
Lemma lem4951129 {A : Type'} (y : A -> Prop) : (term964 A y) = (term965 A y).
Proof. exact (@lem4951128 A (term966 A y) (term967 A y)). Qed.
Lemma lem4951130 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term968 A y s) = (term955 A y s).
Proof. exact (eq_refl (term968 A y s)). Qed.
Lemma lem4951131 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4951132 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term969 A y s) = (term957 A y s).
Proof. exact (MK_COMB (@lem4951131) (@lem4951130 A y s)). Qed.
Lemma lem4951133 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term970 A y s) = (term960 A y s).
Proof. exact (eq_refl (term970 A y s)). Qed.
Lemma lem4951134 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term971 A y s) = (term961 A y s).
Proof. exact (MK_COMB (@lem4951132 A y s) (@lem4951133 A y s)). Qed.
Lemma lem4951135 {A : Type'} (y : A -> Prop) : (term972 A y) = (term962 A y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4951134 A y s)). Qed.
Lemma lem4951136 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4951137 {A : Type'} (y : A -> Prop) : (term964 A y) = (term963 A y).
Proof. exact (MK_COMB (@lem4951136 A) (@lem4951135 A y)). Qed.
Lemma lem4951138 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4951139 {A : Type'} (y : A -> Prop) : (term973 A y) = (term974 A y).
Proof. exact (MK_COMB (@lem4951138) (@lem4951137 A y)). Qed.
Lemma lem4951140 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term968 A y s) = (term955 A y s).
Proof. exact (eq_refl (term968 A y s)). Qed.
Lemma lem4951141 {A : Type'} (y : A -> Prop) : (term975 A y) = (term966 A y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4951140 A y s)). Qed.
Lemma lem4951142 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4951143 {A : Type'} (y : A -> Prop) : (term976 A y) = (term977 A y).
Proof. exact (MK_COMB (@lem4951142 A) (@lem4951141 A y)). Qed.
Lemma lem4951144 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4951145 {A : Type'} (y : A -> Prop) : (term978 A y) = (term979 A y).
Proof. exact (MK_COMB (@lem4951144) (@lem4951143 A y)). Qed.
Lemma lem4951146 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term970 A y s) = (term960 A y s).
Proof. exact (eq_refl (term970 A y s)). Qed.
Lemma lem4951147 {A : Type'} (y : A -> Prop) : (term980 A y) = (term967 A y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4951146 A y s)). Qed.
Lemma lem4951148 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4951149 {A : Type'} (y : A -> Prop) : (term981 A y) = (term982 A y).
Proof. exact (MK_COMB (@lem4951148 A) (@lem4951147 A y)). Qed.
Lemma lem4951150 {A : Type'} (y : A -> Prop) : (term965 A y) = (term983 A y).
Proof. exact (MK_COMB (@lem4951145 A y) (@lem4951149 A y)). Qed.
Lemma lem4951151 {A : Type'} (y : A -> Prop) : ((term964 A y) = (term965 A y)) = ((term963 A y) = (term983 A y)).
Proof. exact (MK_COMB (@lem4951139 A y) (@lem4951150 A y)). Qed.
Lemma lem4951152 {A : Type'} (y : A -> Prop) : (term963 A y) = (term983 A y).
Proof. exact (EQ_MP (@lem4951151 A y) (@lem4951129 A y)). Qed.
Lemma lem4951353 {A : Type'} (y : A -> Prop) : (term937 A y) = (term983 A y).
Proof. exact (TRANS (@lem4951125 A y) (@lem4951152 A y)). Qed.
Lemma lem4951354 {A : Type'} : (term938 A) = (term984 A).
Proof. exact (fun_ext (fun y : A -> Prop => @lem4951353 A y)). Qed.
Lemma lem4951355 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4951356 {A : Type'} : (term939 A) = (term985 A).
Proof. exact (MK_COMB (@lem4951355 A) (@lem4951354 A)). Qed.
Lemma lem4951358 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term554 A P Q) = (term555 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4951359 {A : Type'} (P : type686 A) (Q : type686 A) : (term580 A P Q) = (term581 A P Q).
Proof. exact (@lem4951358 (A -> Prop) P Q). Qed.
Lemma lem4951360 {A : Type'} : (term986 A) = (term987 A).
Proof. exact (@lem4951359 A (term988 A) (term989 A)). Qed.
Lemma lem4951361 {A : Type'} (y : A -> Prop) : (term990 A y) = (term977 A y).
Proof. exact (eq_refl (term990 A y)). Qed.
Lemma lem4951362 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4951363 {A : Type'} (y : A -> Prop) : (term991 A y) = (term979 A y).
Proof. exact (MK_COMB (@lem4951362) (@lem4951361 A y)). Qed.
Lemma lem4951364 {A : Type'} (y : A -> Prop) : (term992 A y) = (term982 A y).
Proof. exact (eq_refl (term992 A y)). Qed.
Lemma lem4951365 {A : Type'} (y : A -> Prop) : (term993 A y) = (term983 A y).
Proof. exact (MK_COMB (@lem4951363 A y) (@lem4951364 A y)). Qed.
Lemma lem4951366 {A : Type'} : (term994 A) = (term984 A).
Proof. exact (fun_ext (fun y : A -> Prop => @lem4951365 A y)). Qed.
Lemma lem4951367 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4951368 {A : Type'} : (term986 A) = (term985 A).
Proof. exact (MK_COMB (@lem4951367 A) (@lem4951366 A)). Qed.
Lemma lem4951369 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4951370 {A : Type'} : (term995 A) = (term996 A).
Proof. exact (MK_COMB (@lem4951369) (@lem4951368 A)). Qed.
Lemma lem4951371 {A : Type'} (y : A -> Prop) : (term990 A y) = (term977 A y).
Proof. exact (eq_refl (term990 A y)). Qed.
Lemma lem4951372 {A : Type'} : (term997 A) = (term988 A).
Proof. exact (fun_ext (fun y : A -> Prop => @lem4951371 A y)). Qed.
Lemma lem4951373 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4951374 {A : Type'} : (term998 A) = (term999 A).
Proof. exact (MK_COMB (@lem4951373 A) (@lem4951372 A)). Qed.
Lemma lem4951375 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4951376 {A : Type'} : (term1000 A) = (term1001 A).
Proof. exact (MK_COMB (@lem4951375) (@lem4951374 A)). Qed.
Lemma lem4951377 {A : Type'} (y : A -> Prop) : (term992 A y) = (term982 A y).
Proof. exact (eq_refl (term992 A y)). Qed.
Lemma lem4951378 {A : Type'} : (term1002 A) = (term989 A).
Proof. exact (fun_ext (fun y : A -> Prop => @lem4951377 A y)). Qed.
Lemma lem4951379 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4951380 {A : Type'} : (term1003 A) = (term1004 A).
Proof. exact (MK_COMB (@lem4951379 A) (@lem4951378 A)). Qed.
Lemma lem4951381 {A : Type'} : (term987 A) = (term1005 A).
Proof. exact (MK_COMB (@lem4951376 A) (@lem4951380 A)). Qed.
Lemma lem4951382 {A : Type'} : ((term986 A) = (term987 A)) = ((term985 A) = (term1005 A)).
Proof. exact (MK_COMB (@lem4951370 A) (@lem4951381 A)). Qed.
Lemma lem4951383 {A : Type'} : (term985 A) = (term1005 A).
Proof. exact (EQ_MP (@lem4951382 A) (@lem4951360 A)). Qed.
Lemma lem4951592 {A : Type'} : (term939 A) = (term1005 A).
Proof. exact (TRANS (@lem4951356 A) (@lem4951383 A)). Qed.
Lemma lem4951594 {A : Type'} (P : Prop) (Q : A -> Prop) : (term270 A P Q) = (term271 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4951595 {A : Type'} (P : Prop) (Q : A -> Prop) : (term270 A P Q) = (term271 A P Q).
Proof. exact (@lem4951594 A P Q). Qed.
Lemma lem4951596 {A : Type'} (y : A -> Prop) (f : type1402 A) (s : A -> Prop) : (term1006 A y f s) = (term1007 A y f s).
Proof. exact (@lem4951595 A (term1008 A y f s) (term158 A y f s)). Qed.
Lemma lem4951597 {A : Type'} (y : A -> Prop) (f : type1402 A) (x : A) (s : A -> Prop) : (term920 A y f s x) = (term157 A y f x s).
Proof. exact (eq_refl (term920 A y f s x)). Qed.
Lemma lem4951598 {A : Type'} (y : A -> Prop) (f : type1402 A) (s : A -> Prop) : (term1009 A y f s) = (term158 A y f s).
Proof. exact (fun_ext (fun x : A => @lem4951597 A y f x s)). Qed.
Lemma lem4951599 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4951600 {A : Type'} (y : A -> Prop) (f : type1402 A) (s : A -> Prop) : (term1010 A y f s) = (term159 A y f s).
Proof. exact (MK_COMB (@lem4951599 A) (@lem4951598 A y f s)). Qed.
Lemma lem4951601 {A : Type'} (y : A -> Prop) (f : type1402 A) (s : A -> Prop) : (term925 A y f s) = (term925 A y f s).
Proof. exact (eq_refl (term925 A y f s)). Qed.
Lemma lem4951602 {A : Type'} (y : A -> Prop) (f : type1402 A) (s : A -> Prop) : (term1006 A y f s) = (term926 A y f s).
Proof. exact (MK_COMB (@lem4951601 A y f s) (@lem4951600 A y f s)). Qed.
Lemma lem4951603 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4951604 {A : Type'} (y : A -> Prop) (f : type1402 A) (s : A -> Prop) : (term1011 A y f s) = (term1012 A y f s).
Proof. exact (MK_COMB (@lem4951603) (@lem4951602 A y f s)). Qed.
Lemma lem4951605 {A : Type'} (y : A -> Prop) (f : type1402 A) (x : A) (s : A -> Prop) : (term920 A y f s x) = (term157 A y f x s).
Proof. exact (eq_refl (term920 A y f s x)). Qed.
Lemma lem4951606 {A : Type'} (y : A -> Prop) (f : type1402 A) (s : A -> Prop) : (term925 A y f s) = (term925 A y f s).
Proof. exact (eq_refl (term925 A y f s)). Qed.
Lemma lem4951607 {A : Type'} (y : A -> Prop) (f : type1402 A) (x : A) (s : A -> Prop) : (term1013 A y f s x) = (term1014 A y f x s).
Proof. exact (MK_COMB (@lem4951606 A y f s) (@lem4951605 A y f x s)). Qed.
Lemma lem4951608 {A : Type'} (y : A -> Prop) (f : type1402 A) (s : A -> Prop) : (term1015 A y f s) = (term1016 A y f s).
Proof. exact (fun_ext (fun x : A => @lem4951607 A y f x s)). Qed.
Lemma lem4951609 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4951610 {A : Type'} (y : A -> Prop) (f : type1402 A) (s : A -> Prop) : (term1007 A y f s) = (term1017 A y f s).
Proof. exact (MK_COMB (@lem4951609 A) (@lem4951608 A y f s)). Qed.
Lemma lem4951611 {A : Type'} (y : A -> Prop) (f : type1402 A) (s : A -> Prop) : ((term1006 A y f s) = (term1007 A y f s)) = ((term926 A y f s) = (term1017 A y f s)).
Proof. exact (MK_COMB (@lem4951604 A y f s) (@lem4951610 A y f s)). Qed.
Lemma lem4951612 {A : Type'} (y : A -> Prop) (f : type1402 A) (s : A -> Prop) : (term926 A y f s) = (term1017 A y f s).
Proof. exact (EQ_MP (@lem4951611 A y f s) (@lem4951596 A y f s)). Qed.
Lemma lem4951613 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term945 A y s) = (term1018 A y s).
Proof. exact (fun_ext (fun f : type1402 A => @lem4951612 A y f s)). Qed.
Lemma lem4951614 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem4951615 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term960 A y s) = (term1019 A y s).
Proof. exact (MK_COMB (@lem4951614 A) (@lem4951613 A y s)). Qed.
Lemma lem4951617 {A B : Type'} (P : type1413 A B) : (term286 A B P) = (term287 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4951618 {A : Type'} (P : type419 A) : (term1020 A P) = (term1021 A P).
Proof. exact (@lem4951617 (type1402 A) A P). Qed.
Lemma lem4951619 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term1022 A y s) = (term1023 A y s).
Proof. exact (@lem4951618 A (term1024 A y s)). Qed.
Lemma lem4951620 {A : Type'} (y : A -> Prop) (f : type1402 A) (s : A -> Prop) : (term1025 A y s f) = (term1016 A y f s).
Proof. exact (eq_refl (term1025 A y s f)). Qed.
Lemma lem4951621 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4951622 {A : Type'} (y : A -> Prop) (f : type1402 A) (s : A -> Prop) (x : A) : (term1026 A y s f x) = (term1027 A y f s x).
Proof. exact (MK_COMB (@lem4951620 A y f s) (@lem4951621 A x)). Qed.
Lemma lem4951623 {A : Type'} (y : A -> Prop) (f : type1402 A) (x : A) (s : A -> Prop) : (term1027 A y f s x) = (term1014 A y f x s).
Proof. exact (eq_refl (term1027 A y f s x)). Qed.
Lemma lem4951624 {A : Type'} (y : A -> Prop) (f : type1402 A) (x : A) (s : A -> Prop) : (term1026 A y s f x) = (term1014 A y f x s).
Proof. exact (TRANS (@lem4951622 A y f s x) (@lem4951623 A y f x s)). Qed.
Lemma lem4951625 {A : Type'} (y : A -> Prop) (f : type1402 A) (s : A -> Prop) : (term1028 A y s f) = (term1016 A y f s).
Proof. exact (fun_ext (fun x : A => @lem4951624 A y f x s)). Qed.
Lemma lem4951626 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4951627 {A : Type'} (y : A -> Prop) (f : type1402 A) (s : A -> Prop) : (term1029 A y s f) = (term1017 A y f s).
Proof. exact (MK_COMB (@lem4951626 A) (@lem4951625 A y f s)). Qed.
Lemma lem4951628 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term1030 A y s) = (term1018 A y s).
Proof. exact (fun_ext (fun f : type1402 A => @lem4951627 A y f s)). Qed.
Lemma lem4951629 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem4951630 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term1022 A y s) = (term1019 A y s).
Proof. exact (MK_COMB (@lem4951629 A) (@lem4951628 A y s)). Qed.
Lemma lem4951631 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4951632 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term1031 A y s) = (term1032 A y s).
Proof. exact (MK_COMB (@lem4951631) (@lem4951630 A y s)). Qed.
Lemma lem4951633 {A : Type'} (y : A -> Prop) (f : type1402 A) (s : A -> Prop) : (term1025 A y s f) = (term1016 A y f s).
Proof. exact (eq_refl (term1025 A y s f)). Qed.
Lemma lem4951634 {A : Type'} (x : type420 A) (f : type1402 A) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem4951635 {A : Type'} (y : A -> Prop) (s : A -> Prop) (x : type420 A) (f : type1402 A) : (term1033 A y s x f) = (term1034 A y s x f).
Proof. exact (MK_COMB (@lem4951633 A y f s) (@lem4951634 A x f)). Qed.
Lemma lem4951636 {A : Type'} (y : A -> Prop) (x : type420 A) (f : type1402 A) (s : A -> Prop) : (term1034 A y s x f) = (term1035 A y x f s).
Proof. exact (eq_refl (term1034 A y s x f)). Qed.
Lemma lem4951637 {A : Type'} (y : A -> Prop) (x : type420 A) (f : type1402 A) (s : A -> Prop) : (term1033 A y s x f) = (term1035 A y x f s).
Proof. exact (TRANS (@lem4951635 A y s x f) (@lem4951636 A y x f s)). Qed.
Lemma lem4951638 {A : Type'} (y : A -> Prop) (x : type420 A) (s : A -> Prop) : (term1036 A y s x) = (term1037 A y x s).
Proof. exact (fun_ext (fun f : type1402 A => @lem4951637 A y x f s)). Qed.
Lemma lem4951639 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem4951640 {A : Type'} (y : A -> Prop) (x : type420 A) (s : A -> Prop) : (term1038 A y s x) = (term1039 A y x s).
Proof. exact (MK_COMB (@lem4951639 A) (@lem4951638 A y x s)). Qed.
Lemma lem4951641 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term1040 A y s) = (term1041 A y s).
Proof. exact (fun_ext (fun x : type420 A => @lem4951640 A y x s)). Qed.
Lemma lem4951642 {A : Type'} : (@ex ((A -> A -> Prop) -> A)) = (@ex ((A -> A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> A -> Prop) -> A))). Qed.
Lemma lem4951643 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term1023 A y s) = (term1042 A y s).
Proof. exact (MK_COMB (@lem4951642 A) (@lem4951641 A y s)). Qed.
Lemma lem4951644 {A : Type'} (y : A -> Prop) (s : A -> Prop) : ((term1022 A y s) = (term1023 A y s)) = ((term1019 A y s) = (term1042 A y s)).
Proof. exact (MK_COMB (@lem4951632 A y s) (@lem4951643 A y s)). Qed.
Lemma lem4951645 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term1019 A y s) = (term1042 A y s).
Proof. exact (EQ_MP (@lem4951644 A y s) (@lem4951619 A y s)). Qed.
Lemma lem4951646 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term960 A y s) = (term1042 A y s).
Proof. exact (TRANS (@lem4951615 A y s) (@lem4951645 A y s)). Qed.
Lemma lem4951647 {A : Type'} (y : A -> Prop) : (term967 A y) = (term1043 A y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4951646 A y s)). Qed.
Lemma lem4951648 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4951649 {A : Type'} (y : A -> Prop) : (term982 A y) = (term1044 A y).
Proof. exact (MK_COMB (@lem4951648 A) (@lem4951647 A y)). Qed.
Lemma lem4951651 {A B : Type'} (P : type1413 A B) : (term286 A B P) = (term287 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4951652 {A : Type'} (P : type579 A) : (term1045 A P) = (term1046 A P).
Proof. exact (@lem4951651 (A -> Prop) (type420 A) P). Qed.
Lemma lem4951653 {A : Type'} (y : A -> Prop) : (term1047 A y) = (term1048 A y).
Proof. exact (@lem4951652 A (term1049 A y)). Qed.
Lemma lem4951654 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term1050 A y s) = (term1041 A y s).
Proof. exact (eq_refl (term1050 A y s)). Qed.
Lemma lem4951655 {A : Type'} (x : type420 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4951656 {A : Type'} (y : A -> Prop) (s : A -> Prop) (x : type420 A) : (term1051 A y s x) = (term1052 A y s x).
Proof. exact (MK_COMB (@lem4951654 A y s) (@lem4951655 A x)). Qed.
Lemma lem4951657 {A : Type'} (y : A -> Prop) (x : type420 A) (s : A -> Prop) : (term1052 A y s x) = (term1039 A y x s).
Proof. exact (eq_refl (term1052 A y s x)). Qed.
Lemma lem4951658 {A : Type'} (y : A -> Prop) (x : type420 A) (s : A -> Prop) : (term1051 A y s x) = (term1039 A y x s).
Proof. exact (TRANS (@lem4951656 A y s x) (@lem4951657 A y x s)). Qed.
Lemma lem4951659 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term1053 A y s) = (term1041 A y s).
Proof. exact (fun_ext (fun x : type420 A => @lem4951658 A y x s)). Qed.
Lemma lem4951660 {A : Type'} : (@ex ((A -> A -> Prop) -> A)) = (@ex ((A -> A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> A -> Prop) -> A))). Qed.
Lemma lem4951661 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term1054 A y s) = (term1042 A y s).
Proof. exact (MK_COMB (@lem4951660 A) (@lem4951659 A y s)). Qed.
Lemma lem4951662 {A : Type'} (y : A -> Prop) : (term1055 A y) = (term1043 A y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4951661 A y s)). Qed.
Lemma lem4951663 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4951664 {A : Type'} (y : A -> Prop) : (term1047 A y) = (term1044 A y).
Proof. exact (MK_COMB (@lem4951663 A) (@lem4951662 A y)). Qed.
Lemma lem4951665 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4951666 {A : Type'} (y : A -> Prop) : (term1056 A y) = (term1057 A y).
Proof. exact (MK_COMB (@lem4951665) (@lem4951664 A y)). Qed.
Lemma lem4951667 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term1050 A y s) = (term1041 A y s).
Proof. exact (eq_refl (term1050 A y s)). Qed.
Lemma lem4951668 {A : Type'} (x : type610 A) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem4951669 {A : Type'} (y : A -> Prop) (x : type610 A) (s : A -> Prop) : (term1058 A y x s) = (term1059 A y x s).
Proof. exact (MK_COMB (@lem4951667 A y s) (@lem4951668 A x s)). Qed.
Lemma lem4951670 {A : Type'} (y : A -> Prop) (x : type610 A) (s : A -> Prop) : (term1059 A y x s) = (term1060 A y x s).
Proof. exact (eq_refl (term1059 A y x s)). Qed.
Lemma lem4951671 {A : Type'} (y : A -> Prop) (x : type610 A) (s : A -> Prop) : (term1058 A y x s) = (term1060 A y x s).
Proof. exact (TRANS (@lem4951669 A y x s) (@lem4951670 A y x s)). Qed.
Lemma lem4951672 {A : Type'} (y : A -> Prop) (x : type610 A) : (term1061 A y x) = (term1062 A y x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4951671 A y x s)). Qed.
Lemma lem4951673 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4951674 {A : Type'} (y : A -> Prop) (x : type610 A) : (term1063 A y x) = (term1064 A y x).
Proof. exact (MK_COMB (@lem4951673 A) (@lem4951672 A y x)). Qed.
Lemma lem4951675 {A : Type'} (y : A -> Prop) : (term1065 A y) = (term1066 A y).
Proof. exact (fun_ext (fun x : type610 A => @lem4951674 A y x)). Qed.
Lemma lem4951676 {A : Type'} : (@ex ((A -> Prop) -> (A -> A -> Prop) -> A)) = (@ex ((A -> Prop) -> (A -> A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> A -> Prop) -> A))). Qed.
Lemma lem4951677 {A : Type'} (y : A -> Prop) : (term1048 A y) = (term1067 A y).
Proof. exact (MK_COMB (@lem4951676 A) (@lem4951675 A y)). Qed.
Lemma lem4951678 {A : Type'} (y : A -> Prop) : ((term1047 A y) = (term1048 A y)) = ((term1044 A y) = (term1067 A y)).
Proof. exact (MK_COMB (@lem4951666 A y) (@lem4951677 A y)). Qed.
Lemma lem4951679 {A : Type'} (y : A -> Prop) : (term1044 A y) = (term1067 A y).
Proof. exact (EQ_MP (@lem4951678 A y) (@lem4951653 A y)). Qed.
Lemma lem4951680 {A : Type'} (y : A -> Prop) : (term982 A y) = (term1067 A y).
Proof. exact (TRANS (@lem4951649 A y) (@lem4951679 A y)). Qed.
Lemma lem4951681 {A : Type'} : (term989 A) = (term1068 A).
Proof. exact (fun_ext (fun y : A -> Prop => @lem4951680 A y)). Qed.
Lemma lem4951682 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4951683 {A : Type'} : (term1004 A) = (term1069 A).
Proof. exact (MK_COMB (@lem4951682 A) (@lem4951681 A)). Qed.
Lemma lem4951685 {A B : Type'} (P : type1413 A B) : (term286 A B P) = (term287 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4951686 {A : Type'} (P : type594 A) : (term1070 A P) = (term1071 A P).
Proof. exact (@lem4951685 (A -> Prop) (type610 A) P). Qed.
Lemma lem4951687 {A : Type'} : (term1072 A) = (term1073 A).
Proof. exact (@lem4951686 A (term1074 A)). Qed.
Lemma lem4951688 {A : Type'} (y : A -> Prop) : (term1075 A y) = (term1066 A y).
Proof. exact (eq_refl (term1075 A y)). Qed.
Lemma lem4951689 {A : Type'} (x : type610 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4951690 {A : Type'} (y : A -> Prop) (x : type610 A) : (term1076 A y x) = (term1077 A y x).
Proof. exact (MK_COMB (@lem4951688 A y) (@lem4951689 A x)). Qed.
Lemma lem4951691 {A : Type'} (y : A -> Prop) (x : type610 A) : (term1077 A y x) = (term1064 A y x).
Proof. exact (eq_refl (term1077 A y x)). Qed.
Lemma lem4951692 {A : Type'} (y : A -> Prop) (x : type610 A) : (term1076 A y x) = (term1064 A y x).
Proof. exact (TRANS (@lem4951690 A y x) (@lem4951691 A y x)). Qed.
Lemma lem4951693 {A : Type'} (y : A -> Prop) : (term1078 A y) = (term1066 A y).
Proof. exact (fun_ext (fun x : type610 A => @lem4951692 A y x)). Qed.
Lemma lem4951694 {A : Type'} : (@ex ((A -> Prop) -> (A -> A -> Prop) -> A)) = (@ex ((A -> Prop) -> (A -> A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> A -> Prop) -> A))). Qed.
Lemma lem4951695 {A : Type'} (y : A -> Prop) : (term1079 A y) = (term1067 A y).
Proof. exact (MK_COMB (@lem4951694 A) (@lem4951693 A y)). Qed.
Lemma lem4951696 {A : Type'} : (term1080 A) = (term1068 A).
Proof. exact (fun_ext (fun y : A -> Prop => @lem4951695 A y)). Qed.
Lemma lem4951697 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4951698 {A : Type'} : (term1072 A) = (term1069 A).
Proof. exact (MK_COMB (@lem4951697 A) (@lem4951696 A)). Qed.
Lemma lem4951699 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4951700 {A : Type'} : (term1081 A) = (term1082 A).
Proof. exact (MK_COMB (@lem4951699) (@lem4951698 A)). Qed.
Lemma lem4951701 {A : Type'} (y : A -> Prop) : (term1075 A y) = (term1066 A y).
Proof. exact (eq_refl (term1075 A y)). Qed.
Lemma lem4951702 {A : Type'} (x : type634 A) (y : A -> Prop) : (x y) = (x y).
Proof. exact (eq_refl (x y)). Qed.
Lemma lem4951703 {A : Type'} (x : type634 A) (y : A -> Prop) : (term1083 A x y) = (term1084 A x y).
Proof. exact (MK_COMB (@lem4951701 A y) (@lem4951702 A x y)). Qed.
Lemma lem4951704 {A : Type'} (x : type634 A) (y : A -> Prop) : (term1084 A x y) = (term1085 A x y).
Proof. exact (eq_refl (term1084 A x y)). Qed.
Lemma lem4951705 {A : Type'} (x : type634 A) (y : A -> Prop) : (term1083 A x y) = (term1085 A x y).
Proof. exact (TRANS (@lem4951703 A x y) (@lem4951704 A x y)). Qed.
Lemma lem4951706 {A : Type'} (x : type634 A) : (term1086 A x) = (term1087 A x).
Proof. exact (fun_ext (fun y : A -> Prop => @lem4951705 A x y)). Qed.
Lemma lem4951707 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4951708 {A : Type'} (x : type634 A) : (term1088 A x) = (term1089 A x).
Proof. exact (MK_COMB (@lem4951707 A) (@lem4951706 A x)). Qed.
Lemma lem4951709 {A : Type'} : (term1090 A) = (term1091 A).
Proof. exact (fun_ext (fun x : type634 A => @lem4951708 A x)). Qed.
Lemma lem4951710 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> (A -> A -> Prop) -> A)) = (@ex ((A -> Prop) -> (A -> Prop) -> (A -> A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> (A -> A -> Prop) -> A))). Qed.
Lemma lem4951711 {A : Type'} : (term1073 A) = (term1092 A).
Proof. exact (MK_COMB (@lem4951710 A) (@lem4951709 A)). Qed.
Lemma lem4951712 {A : Type'} : ((term1072 A) = (term1073 A)) = ((term1069 A) = (term1092 A)).
Proof. exact (MK_COMB (@lem4951700 A) (@lem4951711 A)). Qed.
Lemma lem4951713 {A : Type'} : (term1069 A) = (term1092 A).
Proof. exact (EQ_MP (@lem4951712 A) (@lem4951687 A)). Qed.
Lemma lem4951714 {A : Type'} : (term1004 A) = (term1092 A).
Proof. exact (TRANS (@lem4951683 A) (@lem4951713 A)). Qed.
Lemma lem4951715 {A : Type'} : (term1001 A) = (term1001 A).
Proof. exact (eq_refl (term1001 A)). Qed.
Lemma lem4951716 {A : Type'} : (term1005 A) = (term1093 A).
Proof. exact (MK_COMB (@lem4951715 A) (@lem4951714 A)). Qed.
Lemma lem4951718 {A : Type'} (P : Prop) (Q : A -> Prop) : (term348 A P Q) = (term349 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4951719 {A : Type'} (P : Prop) (Q : type136 A) : (term1094 A P Q) = (term1095 A P Q).
Proof. exact (@lem4951718 (type634 A) P Q). Qed.
Lemma lem4951720 {A : Type'} : (term1096 A) = (term1097 A).
Proof. exact (@lem4951719 A (term999 A) (term1091 A)). Qed.
Lemma lem4951721 {A : Type'} (x : type634 A) : (term1098 A x) = (term1089 A x).
Proof. exact (eq_refl (term1098 A x)). Qed.
Lemma lem4951722 {A : Type'} : (term1099 A) = (term1091 A).
Proof. exact (fun_ext (fun x : type634 A => @lem4951721 A x)). Qed.
Lemma lem4951723 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> (A -> A -> Prop) -> A)) = (@ex ((A -> Prop) -> (A -> Prop) -> (A -> A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> (A -> A -> Prop) -> A))). Qed.
Lemma lem4951724 {A : Type'} : (term1100 A) = (term1092 A).
Proof. exact (MK_COMB (@lem4951723 A) (@lem4951722 A)). Qed.
Lemma lem4951725 {A : Type'} : (term1001 A) = (term1001 A).
Proof. exact (eq_refl (term1001 A)). Qed.
Lemma lem4951726 {A : Type'} : (term1096 A) = (term1093 A).
Proof. exact (MK_COMB (@lem4951725 A) (@lem4951724 A)). Qed.
Lemma lem4951727 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4951728 {A : Type'} : (term1101 A) = (term1102 A).
Proof. exact (MK_COMB (@lem4951727) (@lem4951726 A)). Qed.
Lemma lem4951729 {A : Type'} (x : type634 A) : (term1098 A x) = (term1089 A x).
Proof. exact (eq_refl (term1098 A x)). Qed.
Lemma lem4951730 {A : Type'} : (term1001 A) = (term1001 A).
Proof. exact (eq_refl (term1001 A)). Qed.
Lemma lem4951731 {A : Type'} (x : type634 A) : (term1103 A x) = (term1104 A x).
Proof. exact (MK_COMB (@lem4951730 A) (@lem4951729 A x)). Qed.
Lemma lem4951732 {A : Type'} : (term1105 A) = (term1106 A).
Proof. exact (fun_ext (fun x : type634 A => @lem4951731 A x)). Qed.
Lemma lem4951733 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> (A -> A -> Prop) -> A)) = (@ex ((A -> Prop) -> (A -> Prop) -> (A -> A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> (A -> A -> Prop) -> A))). Qed.
Lemma lem4951734 {A : Type'} : (term1097 A) = (term1107 A).
Proof. exact (MK_COMB (@lem4951733 A) (@lem4951732 A)). Qed.
Lemma lem4951735 {A : Type'} : ((term1096 A) = (term1097 A)) = ((term1093 A) = (term1107 A)).
Proof. exact (MK_COMB (@lem4951728 A) (@lem4951734 A)). Qed.
Lemma lem4951736 {A : Type'} : (term1093 A) = (term1107 A).
Proof. exact (EQ_MP (@lem4951735 A) (@lem4951720 A)). Qed.
Lemma lem4951737 {A : Type'} : (term1005 A) = (term1107 A).
Proof. exact (TRANS (@lem4951716 A) (@lem4951736 A)). Qed.
Lemma lem4951738 {A : Type'} : (term939 A) = (term1107 A).
Proof. exact (TRANS (@lem4951592 A) (@lem4951737 A)). Qed.
Lemma lem4951739 {A : Type'} : (term87 A) = (term1107 A).
Proof. exact (TRANS (@lem4950895 A) (@lem4951738 A)). Qed.
Lemma lem4951740 {A : Type'} (h1 : term87 A) : term1107 A.
Proof. exact (EQ_MP (@lem4951739 A) (@lem4947223 A h1)). Qed.
Lemma lem4951751 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (x : A) (s : A -> Prop) : (term1108 A B y f x s) = (term1109 A B y f x s).
Proof. exact (@lem17045 (y = (f x)) (@IN A x s)). Qed.
Lemma lem4951754 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (x : A) (s : A -> Prop) : (term147 A B y f x s) = (term147 A B y f x s).
Proof. exact (eq_refl (term147 A B y f x s)). Qed.
Lemma lem4951755 {A : Type'} (P : A -> Prop) : (term196 A P) = (term197 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem4951756 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (s : A -> Prop) : (term1110 A B y f s) = (term1111 A B y f s).
Proof. exact (@lem4951755 A (term148 A B y f s)). Qed.
Lemma lem4951757 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (x : A) (s : A -> Prop) : (term1112 A B y f s x) = (term147 A B y f x s).
Proof. exact (eq_refl (term1112 A B y f s x)). Qed.
Lemma lem4951758 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4951759 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (x : A) (s : A -> Prop) : (term1113 A B y f s x) = (term1108 A B y f x s).
Proof. exact (MK_COMB (@lem4951758) (@lem4951757 A B y f x s)). Qed.
Lemma lem4951760 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (x : A) (s : A -> Prop) : (term1113 A B y f s x) = (term1109 A B y f x s).
Proof. exact (TRANS (@lem4951759 A B y f x s) (@lem4951751 A B y f x s)). Qed.
Lemma lem4951761 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (s : A -> Prop) : (term1114 A B y f s) = (term1115 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem4951760 A B y f x s)). Qed.
Lemma lem4951762 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4951763 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (s : A -> Prop) : (term1111 A B y f s) = (term1116 A B y f s).
Proof. exact (MK_COMB (@lem4951762 A) (@lem4951761 A B y f s)). Qed.
Lemma lem4951764 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (s : A -> Prop) : (term1110 A B y f s) = (term1116 A B y f s).
Proof. exact (TRANS (@lem4951756 A B y f s) (@lem4951763 A B y f s)). Qed.
Lemma lem4951765 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (s : A -> Prop) : (term148 A B y f s) = (term148 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem4951754 A B y f x s)). Qed.
Lemma lem4951766 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4951767 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (s : A -> Prop) : (term149 A B y f s) = (term149 A B y f s).
Proof. exact (MK_COMB (@lem4951766 A) (@lem4951765 A B y f s)). Qed.
Lemma lem4951769 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (s : A -> Prop) : (term1117 A B y f s) = (term1117 A B y f s).
Proof. exact (eq_refl (term1117 A B y f s)). Qed.
Lemma lem4951770 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (s : A -> Prop) : (term1118 A B y f s) = (term1118 A B y f s).
Proof. exact (MK_COMB (@lem4951769 A B y f s) (@lem4951767 A B y f s)). Qed.
Lemma lem4951772 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (s : A -> Prop) : (term1119 A B y f s) = (term1119 A B y f s).
Proof. exact (eq_refl (term1119 A B y f s)). Qed.
Lemma lem4951773 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (s : A -> Prop) : (term1120 A B y f s) = (term1121 A B y f s).
Proof. exact (MK_COMB (@lem4951772 A B y f s) (@lem4951764 A B y f s)). Qed.
Lemma lem4951774 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4951775 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (s : A -> Prop) : (term1122 A B y f s) = (term1123 A B y f s).
Proof. exact (MK_COMB (@lem4951774) (@lem4951773 A B y f s)). Qed.
Lemma lem4951776 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (s : A -> Prop) : (term1124 A B y f s) = (term1125 A B y f s).
Proof. exact (MK_COMB (@lem4951775 A B y f s) (@lem4951770 A B y f s)). Qed.
Lemma lem4951777 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (s : A -> Prop) : ((term151 A B y f s) = (term149 A B y f s)) = (term1124 A B y f s).
Proof. exact (@lem17784 (term151 A B y f s) (term149 A B y f s)). Qed.
Lemma lem4951778 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (s : A -> Prop) : ((term151 A B y f s) = (term149 A B y f s)) = (term1125 A B y f s).
Proof. exact (TRANS (@lem4951777 A B y f s) (@lem4951776 A B y f s)). Qed.
Lemma lem4951779 {A B : Type'} (y : B -> Prop) (s : A -> Prop) : (term152 A B y s) = (term1126 A B y s).
Proof. exact (fun_ext (fun f : type1413 A B => @lem4951778 A B y f s)). Qed.
Lemma lem4951780 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem4951781 {A B : Type'} (y : B -> Prop) (s : A -> Prop) : (term153 A B y s) = (term1127 A B y s).
Proof. exact (MK_COMB (@lem4951780 A B) (@lem4951779 A B y s)). Qed.
Lemma lem4951782 {A B : Type'} (y : B -> Prop) : (term154 A B y) = (term1128 A B y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4951781 A B y s)). Qed.
Lemma lem4951783 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4951784 {A B : Type'} (y : B -> Prop) : (term155 A B y) = (term1129 A B y).
Proof. exact (MK_COMB (@lem4951783 A) (@lem4951782 A B y)). Qed.
Lemma lem4951785 {A B : Type'} : (term156 A B) = (term1130 A B).
Proof. exact (fun_ext (fun y : B -> Prop => @lem4951784 A B y)). Qed.
Lemma lem4951786 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4951787 {A B : Type'} : (term86 A B) = (term1131 A B).
Proof. exact (MK_COMB (@lem4951786 B) (@lem4951785 A B)). Qed.
Lemma lem4951797 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term554 A P Q) = (term555 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4951798 {A B : Type'} (P : type475 A B) (Q : type475 A B) : (term1132 A B P Q) = (term1133 A B P Q).
Proof. exact (@lem4951797 (type1413 A B) P Q). Qed.
Lemma lem4951799 {A B : Type'} (y : B -> Prop) (s : A -> Prop) : (term1134 A B y s) = (term1135 A B y s).
Proof. exact (@lem4951798 A B (term1136 A B y s) (term1137 A B y s)). Qed.
Lemma lem4951800 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (s : A -> Prop) : (term1138 A B y s f) = (term1121 A B y f s).
Proof. exact (eq_refl (term1138 A B y s f)). Qed.
Lemma lem4951801 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4951802 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (s : A -> Prop) : (term1139 A B y s f) = (term1123 A B y f s).
Proof. exact (MK_COMB (@lem4951801) (@lem4951800 A B y f s)). Qed.
Lemma lem4951803 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (s : A -> Prop) : (term1140 A B y s f) = (term1118 A B y f s).
Proof. exact (eq_refl (term1140 A B y s f)). Qed.
Lemma lem4951804 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (s : A -> Prop) : (term1141 A B y s f) = (term1125 A B y f s).
Proof. exact (MK_COMB (@lem4951802 A B y f s) (@lem4951803 A B y f s)). Qed.
Lemma lem4951805 {A B : Type'} (y : B -> Prop) (s : A -> Prop) : (term1142 A B y s) = (term1126 A B y s).
Proof. exact (fun_ext (fun f : type1413 A B => @lem4951804 A B y f s)). Qed.
Lemma lem4951806 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem4951807 {A B : Type'} (y : B -> Prop) (s : A -> Prop) : (term1134 A B y s) = (term1127 A B y s).
Proof. exact (MK_COMB (@lem4951806 A B) (@lem4951805 A B y s)). Qed.
Lemma lem4951808 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4951809 {A B : Type'} (y : B -> Prop) (s : A -> Prop) : (term1143 A B y s) = (term1144 A B y s).
Proof. exact (MK_COMB (@lem4951808) (@lem4951807 A B y s)). Qed.
Lemma lem4951810 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (s : A -> Prop) : (term1138 A B y s f) = (term1121 A B y f s).
Proof. exact (eq_refl (term1138 A B y s f)). Qed.
Lemma lem4951811 {A B : Type'} (y : B -> Prop) (s : A -> Prop) : (term1145 A B y s) = (term1136 A B y s).
Proof. exact (fun_ext (fun f : type1413 A B => @lem4951810 A B y f s)). Qed.
Lemma lem4951812 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem4951813 {A B : Type'} (y : B -> Prop) (s : A -> Prop) : (term1146 A B y s) = (term1147 A B y s).
Proof. exact (MK_COMB (@lem4951812 A B) (@lem4951811 A B y s)). Qed.
Lemma lem4951814 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4951815 {A B : Type'} (y : B -> Prop) (s : A -> Prop) : (term1148 A B y s) = (term1149 A B y s).
Proof. exact (MK_COMB (@lem4951814) (@lem4951813 A B y s)). Qed.
Lemma lem4951816 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (s : A -> Prop) : (term1140 A B y s f) = (term1118 A B y f s).
Proof. exact (eq_refl (term1140 A B y s f)). Qed.
Lemma lem4951817 {A B : Type'} (y : B -> Prop) (s : A -> Prop) : (term1150 A B y s) = (term1137 A B y s).
Proof. exact (fun_ext (fun f : type1413 A B => @lem4951816 A B y f s)). Qed.
Lemma lem4951818 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem4951819 {A B : Type'} (y : B -> Prop) (s : A -> Prop) : (term1151 A B y s) = (term1152 A B y s).
Proof. exact (MK_COMB (@lem4951818 A B) (@lem4951817 A B y s)). Qed.
Lemma lem4951820 {A B : Type'} (y : B -> Prop) (s : A -> Prop) : (term1135 A B y s) = (term1153 A B y s).
Proof. exact (MK_COMB (@lem4951815 A B y s) (@lem4951819 A B y s)). Qed.
Lemma lem4951821 {A B : Type'} (y : B -> Prop) (s : A -> Prop) : ((term1134 A B y s) = (term1135 A B y s)) = ((term1127 A B y s) = (term1153 A B y s)).
Proof. exact (MK_COMB (@lem4951809 A B y s) (@lem4951820 A B y s)). Qed.
Lemma lem4951822 {A B : Type'} (y : B -> Prop) (s : A -> Prop) : (term1127 A B y s) = (term1153 A B y s).
Proof. exact (EQ_MP (@lem4951821 A B y s) (@lem4951799 A B y s)). Qed.
Lemma lem4952015 {A B : Type'} (y : B -> Prop) : (term1128 A B y) = (term1154 A B y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4951822 A B y s)). Qed.
Lemma lem4952016 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4952017 {A B : Type'} (y : B -> Prop) : (term1129 A B y) = (term1155 A B y).
Proof. exact (MK_COMB (@lem4952016 A) (@lem4952015 A B y)). Qed.
Lemma lem4952019 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term554 A P Q) = (term555 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4952020 {A : Type'} (P : type686 A) (Q : type686 A) : (term580 A P Q) = (term581 A P Q).
Proof. exact (@lem4952019 (A -> Prop) P Q). Qed.
Lemma lem4952021 {A B : Type'} (y : B -> Prop) : (term1156 A B y) = (term1157 A B y).
Proof. exact (@lem4952020 A (term1158 A B y) (term1159 A B y)). Qed.
Lemma lem4952022 {A B : Type'} (y : B -> Prop) (s : A -> Prop) : (term1160 A B y s) = (term1147 A B y s).
Proof. exact (eq_refl (term1160 A B y s)). Qed.
Lemma lem4952023 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4952024 {A B : Type'} (y : B -> Prop) (s : A -> Prop) : (term1161 A B y s) = (term1149 A B y s).
Proof. exact (MK_COMB (@lem4952023) (@lem4952022 A B y s)). Qed.
Lemma lem4952025 {A B : Type'} (y : B -> Prop) (s : A -> Prop) : (term1162 A B y s) = (term1152 A B y s).
Proof. exact (eq_refl (term1162 A B y s)). Qed.
Lemma lem4952026 {A B : Type'} (y : B -> Prop) (s : A -> Prop) : (term1163 A B y s) = (term1153 A B y s).
Proof. exact (MK_COMB (@lem4952024 A B y s) (@lem4952025 A B y s)). Qed.
Lemma lem4952027 {A B : Type'} (y : B -> Prop) : (term1164 A B y) = (term1154 A B y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4952026 A B y s)). Qed.
Lemma lem4952028 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4952029 {A B : Type'} (y : B -> Prop) : (term1156 A B y) = (term1155 A B y).
Proof. exact (MK_COMB (@lem4952028 A) (@lem4952027 A B y)). Qed.
Lemma lem4952030 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4952031 {A B : Type'} (y : B -> Prop) : (term1165 A B y) = (term1166 A B y).
Proof. exact (MK_COMB (@lem4952030) (@lem4952029 A B y)). Qed.
Lemma lem4952032 {A B : Type'} (y : B -> Prop) (s : A -> Prop) : (term1160 A B y s) = (term1147 A B y s).
Proof. exact (eq_refl (term1160 A B y s)). Qed.
Lemma lem4952033 {A B : Type'} (y : B -> Prop) : (term1167 A B y) = (term1158 A B y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4952032 A B y s)). Qed.
Lemma lem4952034 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4952035 {A B : Type'} (y : B -> Prop) : (term1168 A B y) = (term1169 A B y).
Proof. exact (MK_COMB (@lem4952034 A) (@lem4952033 A B y)). Qed.
Lemma lem4952036 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4952037 {A B : Type'} (y : B -> Prop) : (term1170 A B y) = (term1171 A B y).
Proof. exact (MK_COMB (@lem4952036) (@lem4952035 A B y)). Qed.
Lemma lem4952038 {A B : Type'} (y : B -> Prop) (s : A -> Prop) : (term1162 A B y s) = (term1152 A B y s).
Proof. exact (eq_refl (term1162 A B y s)). Qed.
Lemma lem4952039 {A B : Type'} (y : B -> Prop) : (term1172 A B y) = (term1159 A B y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4952038 A B y s)). Qed.
Lemma lem4952040 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4952041 {A B : Type'} (y : B -> Prop) : (term1173 A B y) = (term1174 A B y).
Proof. exact (MK_COMB (@lem4952040 A) (@lem4952039 A B y)). Qed.
Lemma lem4952042 {A B : Type'} (y : B -> Prop) : (term1157 A B y) = (term1175 A B y).
Proof. exact (MK_COMB (@lem4952037 A B y) (@lem4952041 A B y)). Qed.
Lemma lem4952043 {A B : Type'} (y : B -> Prop) : ((term1156 A B y) = (term1157 A B y)) = ((term1155 A B y) = (term1175 A B y)).
Proof. exact (MK_COMB (@lem4952031 A B y) (@lem4952042 A B y)). Qed.
Lemma lem4952044 {A B : Type'} (y : B -> Prop) : (term1155 A B y) = (term1175 A B y).
Proof. exact (EQ_MP (@lem4952043 A B y) (@lem4952021 A B y)). Qed.
Lemma lem4952245 {A B : Type'} (y : B -> Prop) : (term1129 A B y) = (term1175 A B y).
Proof. exact (TRANS (@lem4952017 A B y) (@lem4952044 A B y)). Qed.
Lemma lem4952246 {A B : Type'} : (term1130 A B) = (term1176 A B).
Proof. exact (fun_ext (fun y : B -> Prop => @lem4952245 A B y)). Qed.
Lemma lem4952247 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4952248 {A B : Type'} : (term1131 A B) = (term1177 A B).
Proof. exact (MK_COMB (@lem4952247 B) (@lem4952246 A B)). Qed.
Lemma lem4952250 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term554 A P Q) = (term555 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4952251 {B : Type'} (P : type686 B) (Q : type686 B) : (term580 B P Q) = (term581 B P Q).
Proof. exact (@lem4952250 (B -> Prop) P Q). Qed.
Lemma lem4952252 {A B : Type'} : (term1178 A B) = (term1179 A B).
Proof. exact (@lem4952251 B (term1180 A B) (term1181 A B)). Qed.
Lemma lem4952253 {A B : Type'} (y : B -> Prop) : (term1182 A B y) = (term1169 A B y).
Proof. exact (eq_refl (term1182 A B y)). Qed.
Lemma lem4952254 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4952255 {A B : Type'} (y : B -> Prop) : (term1183 A B y) = (term1171 A B y).
Proof. exact (MK_COMB (@lem4952254) (@lem4952253 A B y)). Qed.
Lemma lem4952256 {A B : Type'} (y : B -> Prop) : (term1184 A B y) = (term1174 A B y).
Proof. exact (eq_refl (term1184 A B y)). Qed.
Lemma lem4952257 {A B : Type'} (y : B -> Prop) : (term1185 A B y) = (term1175 A B y).
Proof. exact (MK_COMB (@lem4952255 A B y) (@lem4952256 A B y)). Qed.
Lemma lem4952258 {A B : Type'} : (term1186 A B) = (term1176 A B).
Proof. exact (fun_ext (fun y : B -> Prop => @lem4952257 A B y)). Qed.
Lemma lem4952259 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4952260 {A B : Type'} : (term1178 A B) = (term1177 A B).
Proof. exact (MK_COMB (@lem4952259 B) (@lem4952258 A B)). Qed.
Lemma lem4952261 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4952262 {A B : Type'} : (term1187 A B) = (term1188 A B).
Proof. exact (MK_COMB (@lem4952261) (@lem4952260 A B)). Qed.
Lemma lem4952263 {A B : Type'} (y : B -> Prop) : (term1182 A B y) = (term1169 A B y).
Proof. exact (eq_refl (term1182 A B y)). Qed.
Lemma lem4952264 {A B : Type'} : (term1189 A B) = (term1180 A B).
Proof. exact (fun_ext (fun y : B -> Prop => @lem4952263 A B y)). Qed.
Lemma lem4952265 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4952266 {A B : Type'} : (term1190 A B) = (term1191 A B).
Proof. exact (MK_COMB (@lem4952265 B) (@lem4952264 A B)). Qed.
Lemma lem4952267 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4952268 {A B : Type'} : (term1192 A B) = (term1193 A B).
Proof. exact (MK_COMB (@lem4952267) (@lem4952266 A B)). Qed.
Lemma lem4952269 {A B : Type'} (y : B -> Prop) : (term1184 A B y) = (term1174 A B y).
Proof. exact (eq_refl (term1184 A B y)). Qed.
Lemma lem4952270 {A B : Type'} : (term1194 A B) = (term1181 A B).
Proof. exact (fun_ext (fun y : B -> Prop => @lem4952269 A B y)). Qed.
Lemma lem4952271 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4952272 {A B : Type'} : (term1195 A B) = (term1196 A B).
Proof. exact (MK_COMB (@lem4952271 B) (@lem4952270 A B)). Qed.
Lemma lem4952273 {A B : Type'} : (term1179 A B) = (term1197 A B).
Proof. exact (MK_COMB (@lem4952268 A B) (@lem4952272 A B)). Qed.
Lemma lem4952274 {A B : Type'} : ((term1178 A B) = (term1179 A B)) = ((term1177 A B) = (term1197 A B)).
Proof. exact (MK_COMB (@lem4952262 A B) (@lem4952273 A B)). Qed.
Lemma lem4952275 {A B : Type'} : (term1177 A B) = (term1197 A B).
Proof. exact (EQ_MP (@lem4952274 A B) (@lem4952252 A B)). Qed.
Lemma lem4952484 {A B : Type'} : (term1131 A B) = (term1197 A B).
Proof. exact (TRANS (@lem4952248 A B) (@lem4952275 A B)). Qed.
Lemma lem4952486 {A : Type'} (P : Prop) (Q : A -> Prop) : (term270 A P Q) = (term271 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4952487 {A : Type'} (P : Prop) (Q : A -> Prop) : (term270 A P Q) = (term271 A P Q).
Proof. exact (@lem4952486 A P Q). Qed.
Lemma lem4952488 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (s : A -> Prop) : (term1198 A B y f s) = (term1199 A B y f s).
Proof. exact (@lem4952487 A (term1200 A B y f s) (term148 A B y f s)). Qed.
Lemma lem4952489 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (x : A) (s : A -> Prop) : (term1112 A B y f s x) = (term147 A B y f x s).
Proof. exact (eq_refl (term1112 A B y f s x)). Qed.
Lemma lem4952490 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (s : A -> Prop) : (term1201 A B y f s) = (term148 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem4952489 A B y f x s)). Qed.
Lemma lem4952491 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4952492 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (s : A -> Prop) : (term1202 A B y f s) = (term149 A B y f s).
Proof. exact (MK_COMB (@lem4952491 A) (@lem4952490 A B y f s)). Qed.
Lemma lem4952493 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (s : A -> Prop) : (term1117 A B y f s) = (term1117 A B y f s).
Proof. exact (eq_refl (term1117 A B y f s)). Qed.
Lemma lem4952494 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (s : A -> Prop) : (term1198 A B y f s) = (term1118 A B y f s).
Proof. exact (MK_COMB (@lem4952493 A B y f s) (@lem4952492 A B y f s)). Qed.
Lemma lem4952495 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4952496 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (s : A -> Prop) : (term1203 A B y f s) = (term1204 A B y f s).
Proof. exact (MK_COMB (@lem4952495) (@lem4952494 A B y f s)). Qed.
Lemma lem4952497 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (x : A) (s : A -> Prop) : (term1112 A B y f s x) = (term147 A B y f x s).
Proof. exact (eq_refl (term1112 A B y f s x)). Qed.
Lemma lem4952498 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (s : A -> Prop) : (term1117 A B y f s) = (term1117 A B y f s).
Proof. exact (eq_refl (term1117 A B y f s)). Qed.
Lemma lem4952499 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (x : A) (s : A -> Prop) : (term1205 A B y f s x) = (term1206 A B y f x s).
Proof. exact (MK_COMB (@lem4952498 A B y f s) (@lem4952497 A B y f x s)). Qed.
Lemma lem4952500 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (s : A -> Prop) : (term1207 A B y f s) = (term1208 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem4952499 A B y f x s)). Qed.
Lemma lem4952501 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4952502 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (s : A -> Prop) : (term1199 A B y f s) = (term1209 A B y f s).
Proof. exact (MK_COMB (@lem4952501 A) (@lem4952500 A B y f s)). Qed.
Lemma lem4952503 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (s : A -> Prop) : ((term1198 A B y f s) = (term1199 A B y f s)) = ((term1118 A B y f s) = (term1209 A B y f s)).
Proof. exact (MK_COMB (@lem4952496 A B y f s) (@lem4952502 A B y f s)). Qed.
Lemma lem4952504 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (s : A -> Prop) : (term1118 A B y f s) = (term1209 A B y f s).
Proof. exact (EQ_MP (@lem4952503 A B y f s) (@lem4952488 A B y f s)). Qed.
Lemma lem4952505 {A B : Type'} (y : B -> Prop) (s : A -> Prop) : (term1137 A B y s) = (term1210 A B y s).
Proof. exact (fun_ext (fun f : type1413 A B => @lem4952504 A B y f s)). Qed.
Lemma lem4952506 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem4952507 {A B : Type'} (y : B -> Prop) (s : A -> Prop) : (term1152 A B y s) = (term1211 A B y s).
Proof. exact (MK_COMB (@lem4952506 A B) (@lem4952505 A B y s)). Qed.
Lemma lem4952509 {A B : Type'} (P : type1413 A B) : (term286 A B P) = (term287 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4952510 {A B : Type'} (P : type468 A B) : (term1212 A B P) = (term1213 A B P).
Proof. exact (@lem4952509 (type1413 A B) A P). Qed.
Lemma lem4952511 {A B : Type'} (y : B -> Prop) (s : A -> Prop) : (term1214 A B y s) = (term1215 A B y s).
Proof. exact (@lem4952510 A B (term1216 A B y s)). Qed.
Lemma lem4952512 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (s : A -> Prop) : (term1217 A B y s f) = (term1208 A B y f s).
Proof. exact (eq_refl (term1217 A B y s f)). Qed.
Lemma lem4952513 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4952514 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (s : A -> Prop) (x : A) : (term1218 A B y s f x) = (term1219 A B y f s x).
Proof. exact (MK_COMB (@lem4952512 A B y f s) (@lem4952513 A x)). Qed.
Lemma lem4952515 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (x : A) (s : A -> Prop) : (term1219 A B y f s x) = (term1206 A B y f x s).
Proof. exact (eq_refl (term1219 A B y f s x)). Qed.
Lemma lem4952516 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (x : A) (s : A -> Prop) : (term1218 A B y s f x) = (term1206 A B y f x s).
Proof. exact (TRANS (@lem4952514 A B y f s x) (@lem4952515 A B y f x s)). Qed.
Lemma lem4952517 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (s : A -> Prop) : (term1220 A B y s f) = (term1208 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem4952516 A B y f x s)). Qed.
Lemma lem4952518 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4952519 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (s : A -> Prop) : (term1221 A B y s f) = (term1209 A B y f s).
Proof. exact (MK_COMB (@lem4952518 A) (@lem4952517 A B y f s)). Qed.
Lemma lem4952520 {A B : Type'} (y : B -> Prop) (s : A -> Prop) : (term1222 A B y s) = (term1210 A B y s).
Proof. exact (fun_ext (fun f : type1413 A B => @lem4952519 A B y f s)). Qed.
Lemma lem4952521 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem4952522 {A B : Type'} (y : B -> Prop) (s : A -> Prop) : (term1214 A B y s) = (term1211 A B y s).
Proof. exact (MK_COMB (@lem4952521 A B) (@lem4952520 A B y s)). Qed.
Lemma lem4952523 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4952524 {A B : Type'} (y : B -> Prop) (s : A -> Prop) : (term1223 A B y s) = (term1224 A B y s).
Proof. exact (MK_COMB (@lem4952523) (@lem4952522 A B y s)). Qed.
Lemma lem4952525 {A B : Type'} (y : B -> Prop) (f : type1413 A B) (s : A -> Prop) : (term1217 A B y s f) = (term1208 A B y f s).
Proof. exact (eq_refl (term1217 A B y s f)). Qed.
Lemma lem4952526 {A B : Type'} (x : type473 A B) (f : type1413 A B) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem4952527 {A B : Type'} (y : B -> Prop) (s : A -> Prop) (x : type473 A B) (f : type1413 A B) : (term1225 A B y s x f) = (term1226 A B y s x f).
Proof. exact (MK_COMB (@lem4952525 A B y f s) (@lem4952526 A B x f)). Qed.
Lemma lem4952528 {A B : Type'} (y : B -> Prop) (x : type473 A B) (f : type1413 A B) (s : A -> Prop) : (term1226 A B y s x f) = (term1227 A B y x f s).
Proof. exact (eq_refl (term1226 A B y s x f)). Qed.
Lemma lem4952529 {A B : Type'} (y : B -> Prop) (x : type473 A B) (f : type1413 A B) (s : A -> Prop) : (term1225 A B y s x f) = (term1227 A B y x f s).
Proof. exact (TRANS (@lem4952527 A B y s x f) (@lem4952528 A B y x f s)). Qed.
Lemma lem4952530 {A B : Type'} (y : B -> Prop) (x : type473 A B) (s : A -> Prop) : (term1228 A B y s x) = (term1229 A B y x s).
Proof. exact (fun_ext (fun f : type1413 A B => @lem4952529 A B y x f s)). Qed.
Lemma lem4952531 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem4952532 {A B : Type'} (y : B -> Prop) (x : type473 A B) (s : A -> Prop) : (term1230 A B y s x) = (term1231 A B y x s).
Proof. exact (MK_COMB (@lem4952531 A B) (@lem4952530 A B y x s)). Qed.
Lemma lem4952533 {A B : Type'} (y : B -> Prop) (s : A -> Prop) : (term1232 A B y s) = (term1233 A B y s).
Proof. exact (fun_ext (fun x : type473 A B => @lem4952532 A B y x s)). Qed.
Lemma lem4952534 {A B : Type'} : (@ex ((A -> B -> Prop) -> A)) = (@ex ((A -> B -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> B -> Prop) -> A))). Qed.
Lemma lem4952535 {A B : Type'} (y : B -> Prop) (s : A -> Prop) : (term1215 A B y s) = (term1234 A B y s).
Proof. exact (MK_COMB (@lem4952534 A B) (@lem4952533 A B y s)). Qed.
Lemma lem4952536 {A B : Type'} (y : B -> Prop) (s : A -> Prop) : ((term1214 A B y s) = (term1215 A B y s)) = ((term1211 A B y s) = (term1234 A B y s)).
Proof. exact (MK_COMB (@lem4952524 A B y s) (@lem4952535 A B y s)). Qed.
Lemma lem4952537 {A B : Type'} (y : B -> Prop) (s : A -> Prop) : (term1211 A B y s) = (term1234 A B y s).
Proof. exact (EQ_MP (@lem4952536 A B y s) (@lem4952511 A B y s)). Qed.
Lemma lem4952538 {A B : Type'} (y : B -> Prop) (s : A -> Prop) : (term1152 A B y s) = (term1234 A B y s).
Proof. exact (TRANS (@lem4952507 A B y s) (@lem4952537 A B y s)). Qed.
Lemma lem4952539 {A B : Type'} (y : B -> Prop) : (term1159 A B y) = (term1235 A B y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4952538 A B y s)). Qed.
Lemma lem4952540 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4952541 {A B : Type'} (y : B -> Prop) : (term1174 A B y) = (term1236 A B y).
Proof. exact (MK_COMB (@lem4952540 A) (@lem4952539 A B y)). Qed.
Lemma lem4952543 {A B : Type'} (P : type1413 A B) : (term286 A B P) = (term287 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4952544 {A B : Type'} (P : type586 A B) : (term1237 A B P) = (term1238 A B P).
Proof. exact (@lem4952543 (A -> Prop) (type473 A B) P). Qed.
Lemma lem4952545 {A B : Type'} (y : B -> Prop) : (term1239 A B y) = (term1240 A B y).
Proof. exact (@lem4952544 A B (term1241 A B y)). Qed.
Lemma lem4952546 {A B : Type'} (y : B -> Prop) (s : A -> Prop) : (term1242 A B y s) = (term1233 A B y s).
Proof. exact (eq_refl (term1242 A B y s)). Qed.
Lemma lem4952547 {A B : Type'} (x : type473 A B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4952548 {A B : Type'} (y : B -> Prop) (s : A -> Prop) (x : type473 A B) : (term1243 A B y s x) = (term1244 A B y s x).
Proof. exact (MK_COMB (@lem4952546 A B y s) (@lem4952547 A B x)). Qed.
Lemma lem4952549 {A B : Type'} (y : B -> Prop) (x : type473 A B) (s : A -> Prop) : (term1244 A B y s x) = (term1231 A B y x s).
Proof. exact (eq_refl (term1244 A B y s x)). Qed.
Lemma lem4952550 {A B : Type'} (y : B -> Prop) (x : type473 A B) (s : A -> Prop) : (term1243 A B y s x) = (term1231 A B y x s).
Proof. exact (TRANS (@lem4952548 A B y s x) (@lem4952549 A B y x s)). Qed.
Lemma lem4952551 {A B : Type'} (y : B -> Prop) (s : A -> Prop) : (term1245 A B y s) = (term1233 A B y s).
Proof. exact (fun_ext (fun x : type473 A B => @lem4952550 A B y x s)). Qed.
Lemma lem4952552 {A B : Type'} : (@ex ((A -> B -> Prop) -> A)) = (@ex ((A -> B -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> B -> Prop) -> A))). Qed.
Lemma lem4952553 {A B : Type'} (y : B -> Prop) (s : A -> Prop) : (term1246 A B y s) = (term1234 A B y s).
Proof. exact (MK_COMB (@lem4952552 A B) (@lem4952551 A B y s)). Qed.
Lemma lem4952554 {A B : Type'} (y : B -> Prop) : (term1247 A B y) = (term1235 A B y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4952553 A B y s)). Qed.
Lemma lem4952555 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4952556 {A B : Type'} (y : B -> Prop) : (term1239 A B y) = (term1236 A B y).
Proof. exact (MK_COMB (@lem4952555 A) (@lem4952554 A B y)). Qed.
Lemma lem4952557 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4952558 {A B : Type'} (y : B -> Prop) : (term1248 A B y) = (term1249 A B y).
Proof. exact (MK_COMB (@lem4952557) (@lem4952556 A B y)). Qed.
Lemma lem4952559 {A B : Type'} (y : B -> Prop) (s : A -> Prop) : (term1242 A B y s) = (term1233 A B y s).
Proof. exact (eq_refl (term1242 A B y s)). Qed.
Lemma lem4952560 {A B : Type'} (x : type622 A B) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem4952561 {A B : Type'} (y : B -> Prop) (x : type622 A B) (s : A -> Prop) : (term1250 A B y x s) = (term1251 A B y x s).
Proof. exact (MK_COMB (@lem4952559 A B y s) (@lem4952560 A B x s)). Qed.
Lemma lem4952562 {A B : Type'} (y : B -> Prop) (x : type622 A B) (s : A -> Prop) : (term1251 A B y x s) = (term1252 A B y x s).
Proof. exact (eq_refl (term1251 A B y x s)). Qed.
Lemma lem4952563 {A B : Type'} (y : B -> Prop) (x : type622 A B) (s : A -> Prop) : (term1250 A B y x s) = (term1252 A B y x s).
Proof. exact (TRANS (@lem4952561 A B y x s) (@lem4952562 A B y x s)). Qed.
Lemma lem4952564 {A B : Type'} (y : B -> Prop) (x : type622 A B) : (term1253 A B y x) = (term1254 A B y x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4952563 A B y x s)). Qed.
Lemma lem4952565 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4952566 {A B : Type'} (y : B -> Prop) (x : type622 A B) : (term1255 A B y x) = (term1256 A B y x).
Proof. exact (MK_COMB (@lem4952565 A) (@lem4952564 A B y x)). Qed.
Lemma lem4952567 {A B : Type'} (y : B -> Prop) : (term1257 A B y) = (term1258 A B y).
Proof. exact (fun_ext (fun x : type622 A B => @lem4952566 A B y x)). Qed.
Lemma lem4952568 {A B : Type'} : (@ex ((A -> Prop) -> (A -> B -> Prop) -> A)) = (@ex ((A -> Prop) -> (A -> B -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> B -> Prop) -> A))). Qed.
Lemma lem4952569 {A B : Type'} (y : B -> Prop) : (term1240 A B y) = (term1259 A B y).
Proof. exact (MK_COMB (@lem4952568 A B) (@lem4952567 A B y)). Qed.
Lemma lem4952570 {A B : Type'} (y : B -> Prop) : ((term1239 A B y) = (term1240 A B y)) = ((term1236 A B y) = (term1259 A B y)).
Proof. exact (MK_COMB (@lem4952558 A B y) (@lem4952569 A B y)). Qed.
Lemma lem4952571 {A B : Type'} (y : B -> Prop) : (term1236 A B y) = (term1259 A B y).
Proof. exact (EQ_MP (@lem4952570 A B y) (@lem4952545 A B y)). Qed.
Lemma lem4952572 {A B : Type'} (y : B -> Prop) : (term1174 A B y) = (term1259 A B y).
Proof. exact (TRANS (@lem4952541 A B y) (@lem4952571 A B y)). Qed.
Lemma lem4952573 {A B : Type'} : (term1181 A B) = (term1260 A B).
Proof. exact (fun_ext (fun y : B -> Prop => @lem4952572 A B y)). Qed.
Lemma lem4952574 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4952575 {A B : Type'} : (term1196 A B) = (term1261 A B).
Proof. exact (MK_COMB (@lem4952574 B) (@lem4952573 A B)). Qed.
Lemma lem4952577 {A B : Type'} (P : type1413 A B) : (term286 A B P) = (term287 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4952578 {A B : Type'} (P : type818 A B) : (term1262 A B P) = (term1263 A B P).
Proof. exact (@lem4952577 (B -> Prop) (type622 A B) P). Qed.
Lemma lem4952579 {A B : Type'} : (term1264 A B) = (term1265 A B).
Proof. exact (@lem4952578 A B (term1266 A B)). Qed.
Lemma lem4952580 {A B : Type'} (y : B -> Prop) : (term1267 A B y) = (term1258 A B y).
Proof. exact (eq_refl (term1267 A B y)). Qed.
Lemma lem4952581 {A B : Type'} (x : type622 A B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4952582 {A B : Type'} (y : B -> Prop) (x : type622 A B) : (term1268 A B y x) = (term1269 A B y x).
Proof. exact (MK_COMB (@lem4952580 A B y) (@lem4952581 A B x)). Qed.
Lemma lem4952583 {A B : Type'} (y : B -> Prop) (x : type622 A B) : (term1269 A B y x) = (term1256 A B y x).
Proof. exact (eq_refl (term1269 A B y x)). Qed.
Lemma lem4952584 {A B : Type'} (y : B -> Prop) (x : type622 A B) : (term1268 A B y x) = (term1256 A B y x).
Proof. exact (TRANS (@lem4952582 A B y x) (@lem4952583 A B y x)). Qed.
Lemma lem4952585 {A B : Type'} (y : B -> Prop) : (term1270 A B y) = (term1258 A B y).
Proof. exact (fun_ext (fun x : type622 A B => @lem4952584 A B y x)). Qed.
Lemma lem4952586 {A B : Type'} : (@ex ((A -> Prop) -> (A -> B -> Prop) -> A)) = (@ex ((A -> Prop) -> (A -> B -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> B -> Prop) -> A))). Qed.
Lemma lem4952587 {A B : Type'} (y : B -> Prop) : (term1271 A B y) = (term1259 A B y).
Proof. exact (MK_COMB (@lem4952586 A B) (@lem4952585 A B y)). Qed.
Lemma lem4952588 {A B : Type'} : (term1272 A B) = (term1260 A B).
Proof. exact (fun_ext (fun y : B -> Prop => @lem4952587 A B y)). Qed.
Lemma lem4952589 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4952590 {A B : Type'} : (term1264 A B) = (term1261 A B).
Proof. exact (MK_COMB (@lem4952589 B) (@lem4952588 A B)). Qed.
Lemma lem4952591 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4952592 {A B : Type'} : (term1273 A B) = (term1274 A B).
Proof. exact (MK_COMB (@lem4952591) (@lem4952590 A B)). Qed.
Lemma lem4952593 {A B : Type'} (y : B -> Prop) : (term1267 A B y) = (term1258 A B y).
Proof. exact (eq_refl (term1267 A B y)). Qed.
Lemma lem4952594 {A B : Type'} (x : type833 A B) (y : B -> Prop) : (x y) = (x y).
Proof. exact (eq_refl (x y)). Qed.
Lemma lem4952595 {A B : Type'} (x : type833 A B) (y : B -> Prop) : (term1275 A B x y) = (term1276 A B x y).
Proof. exact (MK_COMB (@lem4952593 A B y) (@lem4952594 A B x y)). Qed.
Lemma lem4952596 {A B : Type'} (x : type833 A B) (y : B -> Prop) : (term1276 A B x y) = (term1277 A B x y).
Proof. exact (eq_refl (term1276 A B x y)). Qed.
Lemma lem4952597 {A B : Type'} (x : type833 A B) (y : B -> Prop) : (term1275 A B x y) = (term1277 A B x y).
Proof. exact (TRANS (@lem4952595 A B x y) (@lem4952596 A B x y)). Qed.
Lemma lem4952598 {A B : Type'} (x : type833 A B) : (term1278 A B x) = (term1279 A B x).
Proof. exact (fun_ext (fun y : B -> Prop => @lem4952597 A B x y)). Qed.
Lemma lem4952599 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4952600 {A B : Type'} (x : type833 A B) : (term1280 A B x) = (term1281 A B x).
Proof. exact (MK_COMB (@lem4952599 B) (@lem4952598 A B x)). Qed.
Lemma lem4952601 {A B : Type'} : (term1282 A B) = (term1283 A B).
Proof. exact (fun_ext (fun x : type833 A B => @lem4952600 A B x)). Qed.
Lemma lem4952602 {A B : Type'} : (@ex ((B -> Prop) -> (A -> Prop) -> (A -> B -> Prop) -> A)) = (@ex ((B -> Prop) -> (A -> Prop) -> (A -> B -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> (A -> Prop) -> (A -> B -> Prop) -> A))). Qed.
Lemma lem4952603 {A B : Type'} : (term1265 A B) = (term1284 A B).
Proof. exact (MK_COMB (@lem4952602 A B) (@lem4952601 A B)). Qed.
Lemma lem4952604 {A B : Type'} : ((term1264 A B) = (term1265 A B)) = ((term1261 A B) = (term1284 A B)).
Proof. exact (MK_COMB (@lem4952592 A B) (@lem4952603 A B)). Qed.
Lemma lem4952605 {A B : Type'} : (term1261 A B) = (term1284 A B).
Proof. exact (EQ_MP (@lem4952604 A B) (@lem4952579 A B)). Qed.
Lemma lem4952606 {A B : Type'} : (term1196 A B) = (term1284 A B).
Proof. exact (TRANS (@lem4952575 A B) (@lem4952605 A B)). Qed.
Lemma lem4952607 {A B : Type'} : (term1193 A B) = (term1193 A B).
Proof. exact (eq_refl (term1193 A B)). Qed.
Lemma lem4952608 {A B : Type'} : (term1197 A B) = (term1285 A B).
Proof. exact (MK_COMB (@lem4952607 A B) (@lem4952606 A B)). Qed.
Lemma lem4952610 {A : Type'} (P : Prop) (Q : A -> Prop) : (term348 A P Q) = (term349 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4952611 {A B : Type'} (P : Prop) (Q : type209 A B) : (term1286 A B P Q) = (term1287 A B P Q).
Proof. exact (@lem4952610 (type833 A B) P Q). Qed.
Lemma lem4952612 {A B : Type'} : (term1288 A B) = (term1289 A B).
Proof. exact (@lem4952611 A B (term1191 A B) (term1283 A B)). Qed.
Lemma lem4952613 {A B : Type'} (x : type833 A B) : (term1290 A B x) = (term1281 A B x).
Proof. exact (eq_refl (term1290 A B x)). Qed.
Lemma lem4952614 {A B : Type'} : (term1291 A B) = (term1283 A B).
Proof. exact (fun_ext (fun x : type833 A B => @lem4952613 A B x)). Qed.
Lemma lem4952615 {A B : Type'} : (@ex ((B -> Prop) -> (A -> Prop) -> (A -> B -> Prop) -> A)) = (@ex ((B -> Prop) -> (A -> Prop) -> (A -> B -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> (A -> Prop) -> (A -> B -> Prop) -> A))). Qed.
Lemma lem4952616 {A B : Type'} : (term1292 A B) = (term1284 A B).
Proof. exact (MK_COMB (@lem4952615 A B) (@lem4952614 A B)). Qed.
Lemma lem4952617 {A B : Type'} : (term1193 A B) = (term1193 A B).
Proof. exact (eq_refl (term1193 A B)). Qed.
Lemma lem4952618 {A B : Type'} : (term1288 A B) = (term1285 A B).
Proof. exact (MK_COMB (@lem4952617 A B) (@lem4952616 A B)). Qed.
Lemma lem4952619 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4952620 {A B : Type'} : (term1293 A B) = (term1294 A B).
Proof. exact (MK_COMB (@lem4952619) (@lem4952618 A B)). Qed.
Lemma lem4952621 {A B : Type'} (x : type833 A B) : (term1290 A B x) = (term1281 A B x).
Proof. exact (eq_refl (term1290 A B x)). Qed.
Lemma lem4952622 {A B : Type'} : (term1193 A B) = (term1193 A B).
Proof. exact (eq_refl (term1193 A B)). Qed.
Lemma lem4952623 {A B : Type'} (x : type833 A B) : (term1295 A B x) = (term1296 A B x).
Proof. exact (MK_COMB (@lem4952622 A B) (@lem4952621 A B x)). Qed.
Lemma lem4952624 {A B : Type'} : (term1297 A B) = (term1298 A B).
Proof. exact (fun_ext (fun x : type833 A B => @lem4952623 A B x)). Qed.
Lemma lem4952625 {A B : Type'} : (@ex ((B -> Prop) -> (A -> Prop) -> (A -> B -> Prop) -> A)) = (@ex ((B -> Prop) -> (A -> Prop) -> (A -> B -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> (A -> Prop) -> (A -> B -> Prop) -> A))). Qed.
Lemma lem4952626 {A B : Type'} : (term1289 A B) = (term1299 A B).
Proof. exact (MK_COMB (@lem4952625 A B) (@lem4952624 A B)). Qed.
Lemma lem4952627 {A B : Type'} : ((term1288 A B) = (term1289 A B)) = ((term1285 A B) = (term1299 A B)).
Proof. exact (MK_COMB (@lem4952620 A B) (@lem4952626 A B)). Qed.
Lemma lem4952628 {A B : Type'} : (term1285 A B) = (term1299 A B).
Proof. exact (EQ_MP (@lem4952627 A B) (@lem4952612 A B)). Qed.
Lemma lem4952629 {A B : Type'} : (term1197 A B) = (term1299 A B).
Proof. exact (TRANS (@lem4952608 A B) (@lem4952628 A B)). Qed.
Lemma lem4952630 {A B : Type'} : (term1131 A B) = (term1299 A B).
Proof. exact (TRANS (@lem4952484 A B) (@lem4952629 A B)). Qed.
Lemma lem4952631 {A B : Type'} : (term86 A B) = (term1299 A B).
Proof. exact (TRANS (@lem4951787 A B) (@lem4952630 A B)). Qed.
Lemma lem4952632 {A B : Type'} (h1 : term86 A B) : term1299 A B.
Proof. exact (EQ_MP (@lem4952631 A B) (@lem4947224 A B h1)). Qed.
Lemma lem4952643 {A : Type'} (y : nat) (f : A -> nat) (x : A) (s : A -> Prop) : (term1300 A y f x s) = (term1301 A y f x s).
Proof. exact (@lem17045 (y = (f x)) (@IN A x s)). Qed.
Lemma lem4952646 {A : Type'} (y : nat) (f : A -> nat) (x : A) (s : A -> Prop) : (term137 A y f x s) = (term137 A y f x s).
Proof. exact (eq_refl (term137 A y f x s)). Qed.
Lemma lem4952647 {A : Type'} (P : A -> Prop) : (term196 A P) = (term197 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem4952648 {A : Type'} (y : nat) (f : A -> nat) (s : A -> Prop) : (term1302 A y f s) = (term1303 A y f s).
Proof. exact (@lem4952647 A (term138 A y f s)). Qed.
Lemma lem4952649 {A : Type'} (y : nat) (f : A -> nat) (x : A) (s : A -> Prop) : (term1304 A y f s x) = (term137 A y f x s).
Proof. exact (eq_refl (term1304 A y f s x)). Qed.
Lemma lem4952650 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4952651 {A : Type'} (y : nat) (f : A -> nat) (x : A) (s : A -> Prop) : (term1305 A y f s x) = (term1300 A y f x s).
Proof. exact (MK_COMB (@lem4952650) (@lem4952649 A y f x s)). Qed.
Lemma lem4952652 {A : Type'} (y : nat) (f : A -> nat) (x : A) (s : A -> Prop) : (term1305 A y f s x) = (term1301 A y f x s).
Proof. exact (TRANS (@lem4952651 A y f x s) (@lem4952643 A y f x s)). Qed.
Lemma lem4952653 {A : Type'} (y : nat) (f : A -> nat) (s : A -> Prop) : (term1306 A y f s) = (term1307 A y f s).
Proof. exact (fun_ext (fun x : A => @lem4952652 A y f x s)). Qed.
Lemma lem4952654 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4952655 {A : Type'} (y : nat) (f : A -> nat) (s : A -> Prop) : (term1303 A y f s) = (term1308 A y f s).
Proof. exact (MK_COMB (@lem4952654 A) (@lem4952653 A y f s)). Qed.
Lemma lem4952656 {A : Type'} (y : nat) (f : A -> nat) (s : A -> Prop) : (term1302 A y f s) = (term1308 A y f s).
Proof. exact (TRANS (@lem4952648 A y f s) (@lem4952655 A y f s)). Qed.
Lemma lem4952657 {A : Type'} (y : nat) (f : A -> nat) (s : A -> Prop) : (term138 A y f s) = (term138 A y f s).
Proof. exact (fun_ext (fun x : A => @lem4952646 A y f x s)). Qed.
Lemma lem4952658 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4952659 {A : Type'} (y : nat) (f : A -> nat) (s : A -> Prop) : (term139 A y f s) = (term139 A y f s).
Proof. exact (MK_COMB (@lem4952658 A) (@lem4952657 A y f s)). Qed.
Lemma lem4952661 {A : Type'} (y : nat) (f : A -> nat) (s : A -> Prop) : (term1309 A y f s) = (term1309 A y f s).
Proof. exact (eq_refl (term1309 A y f s)). Qed.
Lemma lem4952662 {A : Type'} (y : nat) (f : A -> nat) (s : A -> Prop) : (term1310 A y f s) = (term1310 A y f s).
Proof. exact (MK_COMB (@lem4952661 A y f s) (@lem4952659 A y f s)). Qed.
Lemma lem4952664 {A : Type'} (y : nat) (f : A -> nat) (s : A -> Prop) : (term1311 A y f s) = (term1311 A y f s).
Proof. exact (eq_refl (term1311 A y f s)). Qed.
Lemma lem4952665 {A : Type'} (y : nat) (f : A -> nat) (s : A -> Prop) : (term1312 A y f s) = (term1313 A y f s).
Proof. exact (MK_COMB (@lem4952664 A y f s) (@lem4952656 A y f s)). Qed.
Lemma lem4952666 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4952667 {A : Type'} (y : nat) (f : A -> nat) (s : A -> Prop) : (term1314 A y f s) = (term1315 A y f s).
Proof. exact (MK_COMB (@lem4952666) (@lem4952665 A y f s)). Qed.
Lemma lem4952668 {A : Type'} (y : nat) (f : A -> nat) (s : A -> Prop) : (term1316 A y f s) = (term1317 A y f s).
Proof. exact (MK_COMB (@lem4952667 A y f s) (@lem4952662 A y f s)). Qed.
Lemma lem4952669 {A : Type'} (y : nat) (f : A -> nat) (s : A -> Prop) : ((term141 A y f s) = (term139 A y f s)) = (term1316 A y f s).
Proof. exact (@lem17784 (term141 A y f s) (term139 A y f s)). Qed.
Lemma lem4952670 {A : Type'} (y : nat) (f : A -> nat) (s : A -> Prop) : ((term141 A y f s) = (term139 A y f s)) = (term1317 A y f s).
Proof. exact (TRANS (@lem4952669 A y f s) (@lem4952668 A y f s)). Qed.
Lemma lem4952671 {A : Type'} (y : nat) (s : A -> Prop) : (term142 A y s) = (term1318 A y s).
Proof. exact (fun_ext (fun f : A -> nat => @lem4952670 A y f s)). Qed.
Lemma lem4952672 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem4952673 {A : Type'} (y : nat) (s : A -> Prop) : (term143 A y s) = (term1319 A y s).
Proof. exact (MK_COMB (@lem4952672 A) (@lem4952671 A y s)). Qed.
Lemma lem4952674 {A : Type'} (y : nat) : (term144 A y) = (term1320 A y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4952673 A y s)). Qed.
Lemma lem4952675 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4952676 {A : Type'} (y : nat) : (term145 A y) = (term1321 A y).
Proof. exact (MK_COMB (@lem4952675 A) (@lem4952674 A y)). Qed.
Lemma lem4952677 {A : Type'} : (term146 A) = (term1322 A).
Proof. exact (fun_ext (fun y : nat => @lem4952676 A y)). Qed.
Lemma lem4952678 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4952679 {A : Type'} : (term85 A) = (term1323 A).
Proof. exact (MK_COMB (@lem4952678) (@lem4952677 A)). Qed.
Lemma lem4952689 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term554 A P Q) = (term555 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4952690 {A : Type'} (P : type704 A) (Q : type704 A) : (term1324 A P Q) = (term1325 A P Q).
Proof. exact (@lem4952689 (A -> nat) P Q). Qed.
Lemma lem4952691 {A : Type'} (y : nat) (s : A -> Prop) : (term1326 A y s) = (term1327 A y s).
Proof. exact (@lem4952690 A (term1328 A y s) (term1329 A y s)). Qed.
Lemma lem4952692 {A : Type'} (y : nat) (f : A -> nat) (s : A -> Prop) : (term1330 A y s f) = (term1313 A y f s).
Proof. exact (eq_refl (term1330 A y s f)). Qed.
Lemma lem4952693 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4952694 {A : Type'} (y : nat) (f : A -> nat) (s : A -> Prop) : (term1331 A y s f) = (term1315 A y f s).
Proof. exact (MK_COMB (@lem4952693) (@lem4952692 A y f s)). Qed.
Lemma lem4952695 {A : Type'} (y : nat) (f : A -> nat) (s : A -> Prop) : (term1332 A y s f) = (term1310 A y f s).
Proof. exact (eq_refl (term1332 A y s f)). Qed.
Lemma lem4952696 {A : Type'} (y : nat) (f : A -> nat) (s : A -> Prop) : (term1333 A y s f) = (term1317 A y f s).
Proof. exact (MK_COMB (@lem4952694 A y f s) (@lem4952695 A y f s)). Qed.
Lemma lem4952697 {A : Type'} (y : nat) (s : A -> Prop) : (term1334 A y s) = (term1318 A y s).
Proof. exact (fun_ext (fun f : A -> nat => @lem4952696 A y f s)). Qed.
Lemma lem4952698 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem4952699 {A : Type'} (y : nat) (s : A -> Prop) : (term1326 A y s) = (term1319 A y s).
Proof. exact (MK_COMB (@lem4952698 A) (@lem4952697 A y s)). Qed.
Lemma lem4952700 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4952701 {A : Type'} (y : nat) (s : A -> Prop) : (term1335 A y s) = (term1336 A y s).
Proof. exact (MK_COMB (@lem4952700) (@lem4952699 A y s)). Qed.
Lemma lem4952702 {A : Type'} (y : nat) (f : A -> nat) (s : A -> Prop) : (term1330 A y s f) = (term1313 A y f s).
Proof. exact (eq_refl (term1330 A y s f)). Qed.
Lemma lem4952703 {A : Type'} (y : nat) (s : A -> Prop) : (term1337 A y s) = (term1328 A y s).
Proof. exact (fun_ext (fun f : A -> nat => @lem4952702 A y f s)). Qed.
Lemma lem4952704 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem4952705 {A : Type'} (y : nat) (s : A -> Prop) : (term1338 A y s) = (term1339 A y s).
Proof. exact (MK_COMB (@lem4952704 A) (@lem4952703 A y s)). Qed.
Lemma lem4952706 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4952707 {A : Type'} (y : nat) (s : A -> Prop) : (term1340 A y s) = (term1341 A y s).
Proof. exact (MK_COMB (@lem4952706) (@lem4952705 A y s)). Qed.
Lemma lem4952708 {A : Type'} (y : nat) (f : A -> nat) (s : A -> Prop) : (term1332 A y s f) = (term1310 A y f s).
Proof. exact (eq_refl (term1332 A y s f)). Qed.
Lemma lem4952709 {A : Type'} (y : nat) (s : A -> Prop) : (term1342 A y s) = (term1329 A y s).
Proof. exact (fun_ext (fun f : A -> nat => @lem4952708 A y f s)). Qed.
Lemma lem4952710 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem4952711 {A : Type'} (y : nat) (s : A -> Prop) : (term1343 A y s) = (term1344 A y s).
Proof. exact (MK_COMB (@lem4952710 A) (@lem4952709 A y s)). Qed.
Lemma lem4952712 {A : Type'} (y : nat) (s : A -> Prop) : (term1327 A y s) = (term1345 A y s).
Proof. exact (MK_COMB (@lem4952707 A y s) (@lem4952711 A y s)). Qed.
Lemma lem4952713 {A : Type'} (y : nat) (s : A -> Prop) : ((term1326 A y s) = (term1327 A y s)) = ((term1319 A y s) = (term1345 A y s)).
Proof. exact (MK_COMB (@lem4952701 A y s) (@lem4952712 A y s)). Qed.
Lemma lem4952714 {A : Type'} (y : nat) (s : A -> Prop) : (term1319 A y s) = (term1345 A y s).
Proof. exact (EQ_MP (@lem4952713 A y s) (@lem4952691 A y s)). Qed.
Lemma lem4952907 {A : Type'} (y : nat) : (term1320 A y) = (term1346 A y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4952714 A y s)). Qed.
Lemma lem4952908 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4952909 {A : Type'} (y : nat) : (term1321 A y) = (term1347 A y).
Proof. exact (MK_COMB (@lem4952908 A) (@lem4952907 A y)). Qed.
Lemma lem4952911 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term554 A P Q) = (term555 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4952912 {A : Type'} (P : type686 A) (Q : type686 A) : (term580 A P Q) = (term581 A P Q).
Proof. exact (@lem4952911 (A -> Prop) P Q). Qed.
Lemma lem4952913 {A : Type'} (y : nat) : (term1348 A y) = (term1349 A y).
Proof. exact (@lem4952912 A (term1350 A y) (term1351 A y)). Qed.
Lemma lem4952914 {A : Type'} (y : nat) (s : A -> Prop) : (term1352 A y s) = (term1339 A y s).
Proof. exact (eq_refl (term1352 A y s)). Qed.
Lemma lem4952915 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4952916 {A : Type'} (y : nat) (s : A -> Prop) : (term1353 A y s) = (term1341 A y s).
Proof. exact (MK_COMB (@lem4952915) (@lem4952914 A y s)). Qed.
Lemma lem4952917 {A : Type'} (y : nat) (s : A -> Prop) : (term1354 A y s) = (term1344 A y s).
Proof. exact (eq_refl (term1354 A y s)). Qed.
Lemma lem4952918 {A : Type'} (y : nat) (s : A -> Prop) : (term1355 A y s) = (term1345 A y s).
Proof. exact (MK_COMB (@lem4952916 A y s) (@lem4952917 A y s)). Qed.
Lemma lem4952919 {A : Type'} (y : nat) : (term1356 A y) = (term1346 A y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4952918 A y s)). Qed.
Lemma lem4952920 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4952921 {A : Type'} (y : nat) : (term1348 A y) = (term1347 A y).
Proof. exact (MK_COMB (@lem4952920 A) (@lem4952919 A y)). Qed.
Lemma lem4952922 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4952923 {A : Type'} (y : nat) : (term1357 A y) = (term1358 A y).
Proof. exact (MK_COMB (@lem4952922) (@lem4952921 A y)). Qed.
Lemma lem4952924 {A : Type'} (y : nat) (s : A -> Prop) : (term1352 A y s) = (term1339 A y s).
Proof. exact (eq_refl (term1352 A y s)). Qed.
Lemma lem4952925 {A : Type'} (y : nat) : (term1359 A y) = (term1350 A y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4952924 A y s)). Qed.
Lemma lem4952926 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4952927 {A : Type'} (y : nat) : (term1360 A y) = (term1361 A y).
Proof. exact (MK_COMB (@lem4952926 A) (@lem4952925 A y)). Qed.
Lemma lem4952928 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4952929 {A : Type'} (y : nat) : (term1362 A y) = (term1363 A y).
Proof. exact (MK_COMB (@lem4952928) (@lem4952927 A y)). Qed.
Lemma lem4952930 {A : Type'} (y : nat) (s : A -> Prop) : (term1354 A y s) = (term1344 A y s).
Proof. exact (eq_refl (term1354 A y s)). Qed.
Lemma lem4952931 {A : Type'} (y : nat) : (term1364 A y) = (term1351 A y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4952930 A y s)). Qed.
Lemma lem4952932 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4952933 {A : Type'} (y : nat) : (term1365 A y) = (term1366 A y).
Proof. exact (MK_COMB (@lem4952932 A) (@lem4952931 A y)). Qed.
Lemma lem4952934 {A : Type'} (y : nat) : (term1349 A y) = (term1367 A y).
Proof. exact (MK_COMB (@lem4952929 A y) (@lem4952933 A y)). Qed.
Lemma lem4952935 {A : Type'} (y : nat) : ((term1348 A y) = (term1349 A y)) = ((term1347 A y) = (term1367 A y)).
Proof. exact (MK_COMB (@lem4952923 A y) (@lem4952934 A y)). Qed.
Lemma lem4952936 {A : Type'} (y : nat) : (term1347 A y) = (term1367 A y).
Proof. exact (EQ_MP (@lem4952935 A y) (@lem4952913 A y)). Qed.
Lemma lem4953137 {A : Type'} (y : nat) : (term1321 A y) = (term1367 A y).
Proof. exact (TRANS (@lem4952909 A y) (@lem4952936 A y)). Qed.
Lemma lem4953138 {A : Type'} : (term1322 A) = (term1368 A).
Proof. exact (fun_ext (fun y : nat => @lem4953137 A y)). Qed.
Lemma lem4953139 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4953140 {A : Type'} : (term1323 A) = (term1369 A).
Proof. exact (MK_COMB (@lem4953139) (@lem4953138 A)). Qed.
Lemma lem4953142 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term554 A P Q) = (term555 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4953143 (P : nat -> Prop) (Q : nat -> Prop) : (term1370 P Q) = (term1371 P Q).
Proof. exact (@lem4953142 nat P Q). Qed.
Lemma lem4953144 {A : Type'} : (term1372 A) = (term1373 A).
Proof. exact (@lem4953143 (term1374 A) (term1375 A)). Qed.
Lemma lem4953145 {A : Type'} (y : nat) : (term1376 A y) = (term1361 A y).
Proof. exact (eq_refl (term1376 A y)). Qed.
Lemma lem4953146 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4953147 {A : Type'} (y : nat) : (term1377 A y) = (term1363 A y).
Proof. exact (MK_COMB (@lem4953146) (@lem4953145 A y)). Qed.
Lemma lem4953148 {A : Type'} (y : nat) : (term1378 A y) = (term1366 A y).
Proof. exact (eq_refl (term1378 A y)). Qed.
Lemma lem4953149 {A : Type'} (y : nat) : (term1379 A y) = (term1367 A y).
Proof. exact (MK_COMB (@lem4953147 A y) (@lem4953148 A y)). Qed.
Lemma lem4953150 {A : Type'} : (term1380 A) = (term1368 A).
Proof. exact (fun_ext (fun y : nat => @lem4953149 A y)). Qed.
Lemma lem4953151 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4953152 {A : Type'} : (term1372 A) = (term1369 A).
Proof. exact (MK_COMB (@lem4953151) (@lem4953150 A)). Qed.
Lemma lem4953153 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4953154 {A : Type'} : (term1381 A) = (term1382 A).
Proof. exact (MK_COMB (@lem4953153) (@lem4953152 A)). Qed.
Lemma lem4953155 {A : Type'} (y : nat) : (term1376 A y) = (term1361 A y).
Proof. exact (eq_refl (term1376 A y)). Qed.
Lemma lem4953156 {A : Type'} : (term1383 A) = (term1374 A).
Proof. exact (fun_ext (fun y : nat => @lem4953155 A y)). Qed.
Lemma lem4953157 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4953158 {A : Type'} : (term1384 A) = (term1385 A).
Proof. exact (MK_COMB (@lem4953157) (@lem4953156 A)). Qed.
Lemma lem4953159 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4953160 {A : Type'} : (term1386 A) = (term1387 A).
Proof. exact (MK_COMB (@lem4953159) (@lem4953158 A)). Qed.
Lemma lem4953161 {A : Type'} (y : nat) : (term1378 A y) = (term1366 A y).
Proof. exact (eq_refl (term1378 A y)). Qed.
Lemma lem4953162 {A : Type'} : (term1388 A) = (term1375 A).
Proof. exact (fun_ext (fun y : nat => @lem4953161 A y)). Qed.
Lemma lem4953163 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4953164 {A : Type'} : (term1389 A) = (term1390 A).
Proof. exact (MK_COMB (@lem4953163) (@lem4953162 A)). Qed.
Lemma lem4953165 {A : Type'} : (term1373 A) = (term1391 A).
Proof. exact (MK_COMB (@lem4953160 A) (@lem4953164 A)). Qed.
Lemma lem4953166 {A : Type'} : ((term1372 A) = (term1373 A)) = ((term1369 A) = (term1391 A)).
Proof. exact (MK_COMB (@lem4953154 A) (@lem4953165 A)). Qed.
Lemma lem4953167 {A : Type'} : (term1369 A) = (term1391 A).
Proof. exact (EQ_MP (@lem4953166 A) (@lem4953144 A)). Qed.
Lemma lem4953376 {A : Type'} : (term1323 A) = (term1391 A).
Proof. exact (TRANS (@lem4953140 A) (@lem4953167 A)). Qed.
Lemma lem4953378 {A : Type'} (P : Prop) (Q : A -> Prop) : (term270 A P Q) = (term271 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4953379 {A : Type'} (P : Prop) (Q : A -> Prop) : (term270 A P Q) = (term271 A P Q).
Proof. exact (@lem4953378 A P Q). Qed.
Lemma lem4953380 {A : Type'} (y : nat) (f : A -> nat) (s : A -> Prop) : (term1392 A y f s) = (term1393 A y f s).
Proof. exact (@lem4953379 A (term1394 A y f s) (term138 A y f s)). Qed.
Lemma lem4953381 {A : Type'} (y : nat) (f : A -> nat) (x : A) (s : A -> Prop) : (term1304 A y f s x) = (term137 A y f x s).
Proof. exact (eq_refl (term1304 A y f s x)). Qed.
Lemma lem4953382 {A : Type'} (y : nat) (f : A -> nat) (s : A -> Prop) : (term1395 A y f s) = (term138 A y f s).
Proof. exact (fun_ext (fun x : A => @lem4953381 A y f x s)). Qed.
Lemma lem4953383 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4953384 {A : Type'} (y : nat) (f : A -> nat) (s : A -> Prop) : (term1396 A y f s) = (term139 A y f s).
Proof. exact (MK_COMB (@lem4953383 A) (@lem4953382 A y f s)). Qed.
Lemma lem4953385 {A : Type'} (y : nat) (f : A -> nat) (s : A -> Prop) : (term1309 A y f s) = (term1309 A y f s).
Proof. exact (eq_refl (term1309 A y f s)). Qed.
Lemma lem4953386 {A : Type'} (y : nat) (f : A -> nat) (s : A -> Prop) : (term1392 A y f s) = (term1310 A y f s).
Proof. exact (MK_COMB (@lem4953385 A y f s) (@lem4953384 A y f s)). Qed.
Lemma lem4953387 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4953388 {A : Type'} (y : nat) (f : A -> nat) (s : A -> Prop) : (term1397 A y f s) = (term1398 A y f s).
Proof. exact (MK_COMB (@lem4953387) (@lem4953386 A y f s)). Qed.
Lemma lem4953389 {A : Type'} (y : nat) (f : A -> nat) (x : A) (s : A -> Prop) : (term1304 A y f s x) = (term137 A y f x s).
Proof. exact (eq_refl (term1304 A y f s x)). Qed.
Lemma lem4953390 {A : Type'} (y : nat) (f : A -> nat) (s : A -> Prop) : (term1309 A y f s) = (term1309 A y f s).
Proof. exact (eq_refl (term1309 A y f s)). Qed.
Lemma lem4953391 {A : Type'} (y : nat) (f : A -> nat) (x : A) (s : A -> Prop) : (term1399 A y f s x) = (term1400 A y f x s).
Proof. exact (MK_COMB (@lem4953390 A y f s) (@lem4953389 A y f x s)). Qed.
Lemma lem4953392 {A : Type'} (y : nat) (f : A -> nat) (s : A -> Prop) : (term1401 A y f s) = (term1402 A y f s).
Proof. exact (fun_ext (fun x : A => @lem4953391 A y f x s)). Qed.
Lemma lem4953393 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4953394 {A : Type'} (y : nat) (f : A -> nat) (s : A -> Prop) : (term1393 A y f s) = (term1403 A y f s).
Proof. exact (MK_COMB (@lem4953393 A) (@lem4953392 A y f s)). Qed.
Lemma lem4953395 {A : Type'} (y : nat) (f : A -> nat) (s : A -> Prop) : ((term1392 A y f s) = (term1393 A y f s)) = ((term1310 A y f s) = (term1403 A y f s)).
Proof. exact (MK_COMB (@lem4953388 A y f s) (@lem4953394 A y f s)). Qed.
Lemma lem4953396 {A : Type'} (y : nat) (f : A -> nat) (s : A -> Prop) : (term1310 A y f s) = (term1403 A y f s).
Proof. exact (EQ_MP (@lem4953395 A y f s) (@lem4953380 A y f s)). Qed.
Lemma lem4953397 {A : Type'} (y : nat) (s : A -> Prop) : (term1329 A y s) = (term1404 A y s).
Proof. exact (fun_ext (fun f : A -> nat => @lem4953396 A y f s)). Qed.
Lemma lem4953398 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem4953399 {A : Type'} (y : nat) (s : A -> Prop) : (term1344 A y s) = (term1405 A y s).
Proof. exact (MK_COMB (@lem4953398 A) (@lem4953397 A y s)). Qed.
Lemma lem4953401 {A B : Type'} (P : type1413 A B) : (term286 A B P) = (term287 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4953402 {A : Type'} (P : type699 A) : (term1406 A P) = (term1407 A P).
Proof. exact (@lem4953401 (A -> nat) A P). Qed.
Lemma lem4953403 {A : Type'} (y : nat) (s : A -> Prop) : (term1408 A y s) = (term1409 A y s).
Proof. exact (@lem4953402 A (term1410 A y s)). Qed.
Lemma lem4953404 {A : Type'} (y : nat) (f : A -> nat) (s : A -> Prop) : (term1411 A y s f) = (term1402 A y f s).
Proof. exact (eq_refl (term1411 A y s f)). Qed.
Lemma lem4953405 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4953406 {A : Type'} (y : nat) (f : A -> nat) (s : A -> Prop) (x : A) : (term1412 A y s f x) = (term1413 A y f s x).
Proof. exact (MK_COMB (@lem4953404 A y f s) (@lem4953405 A x)). Qed.
Lemma lem4953407 {A : Type'} (y : nat) (f : A -> nat) (x : A) (s : A -> Prop) : (term1413 A y f s x) = (term1400 A y f x s).
Proof. exact (eq_refl (term1413 A y f s x)). Qed.
Lemma lem4953408 {A : Type'} (y : nat) (f : A -> nat) (x : A) (s : A -> Prop) : (term1412 A y s f x) = (term1400 A y f x s).
Proof. exact (TRANS (@lem4953406 A y f s x) (@lem4953407 A y f x s)). Qed.
Lemma lem4953409 {A : Type'} (y : nat) (f : A -> nat) (s : A -> Prop) : (term1414 A y s f) = (term1402 A y f s).
Proof. exact (fun_ext (fun x : A => @lem4953408 A y f x s)). Qed.
Lemma lem4953410 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4953411 {A : Type'} (y : nat) (f : A -> nat) (s : A -> Prop) : (term1415 A y s f) = (term1403 A y f s).
Proof. exact (MK_COMB (@lem4953410 A) (@lem4953409 A y f s)). Qed.
Lemma lem4953412 {A : Type'} (y : nat) (s : A -> Prop) : (term1416 A y s) = (term1404 A y s).
Proof. exact (fun_ext (fun f : A -> nat => @lem4953411 A y f s)). Qed.
Lemma lem4953413 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem4953414 {A : Type'} (y : nat) (s : A -> Prop) : (term1408 A y s) = (term1405 A y s).
Proof. exact (MK_COMB (@lem4953413 A) (@lem4953412 A y s)). Qed.
Lemma lem4953415 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4953416 {A : Type'} (y : nat) (s : A -> Prop) : (term1417 A y s) = (term1418 A y s).
Proof. exact (MK_COMB (@lem4953415) (@lem4953414 A y s)). Qed.
Lemma lem4953417 {A : Type'} (y : nat) (f : A -> nat) (s : A -> Prop) : (term1411 A y s f) = (term1402 A y f s).
Proof. exact (eq_refl (term1411 A y s f)). Qed.
Lemma lem4953418 {A : Type'} (x : type703 A) (f : A -> nat) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem4953419 {A : Type'} (y : nat) (s : A -> Prop) (x : type703 A) (f : A -> nat) : (term1419 A y s x f) = (term1420 A y s x f).
Proof. exact (MK_COMB (@lem4953417 A y f s) (@lem4953418 A x f)). Qed.
Lemma lem4953420 {A : Type'} (y : nat) (x : type703 A) (f : A -> nat) (s : A -> Prop) : (term1420 A y s x f) = (term1421 A y x f s).
Proof. exact (eq_refl (term1420 A y s x f)). Qed.
Lemma lem4953421 {A : Type'} (y : nat) (x : type703 A) (f : A -> nat) (s : A -> Prop) : (term1419 A y s x f) = (term1421 A y x f s).
Proof. exact (TRANS (@lem4953419 A y s x f) (@lem4953420 A y x f s)). Qed.
Lemma lem4953422 {A : Type'} (y : nat) (x : type703 A) (s : A -> Prop) : (term1422 A y s x) = (term1423 A y x s).
Proof. exact (fun_ext (fun f : A -> nat => @lem4953421 A y x f s)). Qed.
Lemma lem4953423 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem4953424 {A : Type'} (y : nat) (x : type703 A) (s : A -> Prop) : (term1424 A y s x) = (term1425 A y x s).
Proof. exact (MK_COMB (@lem4953423 A) (@lem4953422 A y x s)). Qed.
Lemma lem4953425 {A : Type'} (y : nat) (s : A -> Prop) : (term1426 A y s) = (term1427 A y s).
Proof. exact (fun_ext (fun x : type703 A => @lem4953424 A y x s)). Qed.
Lemma lem4953426 {A : Type'} : (@ex ((A -> nat) -> A)) = (@ex ((A -> nat) -> A)).
Proof. exact (eq_refl (@ex ((A -> nat) -> A))). Qed.
Lemma lem4953427 {A : Type'} (y : nat) (s : A -> Prop) : (term1409 A y s) = (term1428 A y s).
Proof. exact (MK_COMB (@lem4953426 A) (@lem4953425 A y s)). Qed.
Lemma lem4953428 {A : Type'} (y : nat) (s : A -> Prop) : ((term1408 A y s) = (term1409 A y s)) = ((term1405 A y s) = (term1428 A y s)).
Proof. exact (MK_COMB (@lem4953416 A y s) (@lem4953427 A y s)). Qed.
Lemma lem4953429 {A : Type'} (y : nat) (s : A -> Prop) : (term1405 A y s) = (term1428 A y s).
Proof. exact (EQ_MP (@lem4953428 A y s) (@lem4953403 A y s)). Qed.
Lemma lem4953430 {A : Type'} (y : nat) (s : A -> Prop) : (term1344 A y s) = (term1428 A y s).
Proof. exact (TRANS (@lem4953399 A y s) (@lem4953429 A y s)). Qed.
Lemma lem4953431 {A : Type'} (y : nat) : (term1351 A y) = (term1429 A y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4953430 A y s)). Qed.
Lemma lem4953432 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4953433 {A : Type'} (y : nat) : (term1366 A y) = (term1430 A y).
Proof. exact (MK_COMB (@lem4953432 A) (@lem4953431 A y)). Qed.
Lemma lem4953435 {A B : Type'} (P : type1413 A B) : (term286 A B P) = (term287 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4953436 {A : Type'} (P : type602 A) : (term1431 A P) = (term1432 A P).
Proof. exact (@lem4953435 (A -> Prop) (type703 A) P). Qed.
Lemma lem4953437 {A : Type'} (y : nat) : (term1433 A y) = (term1434 A y).
Proof. exact (@lem4953436 A (term1435 A y)). Qed.
Lemma lem4953438 {A : Type'} (y : nat) (s : A -> Prop) : (term1436 A y s) = (term1427 A y s).
Proof. exact (eq_refl (term1436 A y s)). Qed.
Lemma lem4953439 {A : Type'} (x : type703 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4953440 {A : Type'} (y : nat) (s : A -> Prop) (x : type703 A) : (term1437 A y s x) = (term1438 A y s x).
Proof. exact (MK_COMB (@lem4953438 A y s) (@lem4953439 A x)). Qed.
Lemma lem4953441 {A : Type'} (y : nat) (x : type703 A) (s : A -> Prop) : (term1438 A y s x) = (term1425 A y x s).
Proof. exact (eq_refl (term1438 A y s x)). Qed.
Lemma lem4953442 {A : Type'} (y : nat) (x : type703 A) (s : A -> Prop) : (term1437 A y s x) = (term1425 A y x s).
Proof. exact (TRANS (@lem4953440 A y s x) (@lem4953441 A y x s)). Qed.
Lemma lem4953443 {A : Type'} (y : nat) (s : A -> Prop) : (term1439 A y s) = (term1427 A y s).
Proof. exact (fun_ext (fun x : type703 A => @lem4953442 A y x s)). Qed.
Lemma lem4953444 {A : Type'} : (@ex ((A -> nat) -> A)) = (@ex ((A -> nat) -> A)).
Proof. exact (eq_refl (@ex ((A -> nat) -> A))). Qed.
Lemma lem4953445 {A : Type'} (y : nat) (s : A -> Prop) : (term1440 A y s) = (term1428 A y s).
Proof. exact (MK_COMB (@lem4953444 A) (@lem4953443 A y s)). Qed.
Lemma lem4953446 {A : Type'} (y : nat) : (term1441 A y) = (term1429 A y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4953445 A y s)). Qed.
Lemma lem4953447 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4953448 {A : Type'} (y : nat) : (term1433 A y) = (term1430 A y).
Proof. exact (MK_COMB (@lem4953447 A) (@lem4953446 A y)). Qed.
Lemma lem4953449 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4953450 {A : Type'} (y : nat) : (term1442 A y) = (term1443 A y).
Proof. exact (MK_COMB (@lem4953449) (@lem4953448 A y)). Qed.
Lemma lem4953451 {A : Type'} (y : nat) (s : A -> Prop) : (term1436 A y s) = (term1427 A y s).
Proof. exact (eq_refl (term1436 A y s)). Qed.
Lemma lem4953452 {A : Type'} (x : type643 A) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem4953453 {A : Type'} (y : nat) (x : type643 A) (s : A -> Prop) : (term1444 A y x s) = (term1445 A y x s).
Proof. exact (MK_COMB (@lem4953451 A y s) (@lem4953452 A x s)). Qed.
Lemma lem4953454 {A : Type'} (y : nat) (x : type643 A) (s : A -> Prop) : (term1445 A y x s) = (term1446 A y x s).
Proof. exact (eq_refl (term1445 A y x s)). Qed.
Lemma lem4953455 {A : Type'} (y : nat) (x : type643 A) (s : A -> Prop) : (term1444 A y x s) = (term1446 A y x s).
Proof. exact (TRANS (@lem4953453 A y x s) (@lem4953454 A y x s)). Qed.
Lemma lem4953456 {A : Type'} (y : nat) (x : type643 A) : (term1447 A y x) = (term1448 A y x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4953455 A y x s)). Qed.
Lemma lem4953457 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4953458 {A : Type'} (y : nat) (x : type643 A) : (term1449 A y x) = (term1450 A y x).
Proof. exact (MK_COMB (@lem4953457 A) (@lem4953456 A y x)). Qed.
Lemma lem4953459 {A : Type'} (y : nat) : (term1451 A y) = (term1452 A y).
Proof. exact (fun_ext (fun x : type643 A => @lem4953458 A y x)). Qed.
Lemma lem4953460 {A : Type'} : (@ex ((A -> Prop) -> (A -> nat) -> A)) = (@ex ((A -> Prop) -> (A -> nat) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> nat) -> A))). Qed.
Lemma lem4953461 {A : Type'} (y : nat) : (term1434 A y) = (term1453 A y).
Proof. exact (MK_COMB (@lem4953460 A) (@lem4953459 A y)). Qed.
Lemma lem4953462 {A : Type'} (y : nat) : ((term1433 A y) = (term1434 A y)) = ((term1430 A y) = (term1453 A y)).
Proof. exact (MK_COMB (@lem4953450 A y) (@lem4953461 A y)). Qed.
Lemma lem4953463 {A : Type'} (y : nat) : (term1430 A y) = (term1453 A y).
Proof. exact (EQ_MP (@lem4953462 A y) (@lem4953437 A y)). Qed.
Lemma lem4953464 {A : Type'} (y : nat) : (term1366 A y) = (term1453 A y).
Proof. exact (TRANS (@lem4953433 A y) (@lem4953463 A y)). Qed.
Lemma lem4953465 {A : Type'} : (term1375 A) = (term1454 A).
Proof. exact (fun_ext (fun y : nat => @lem4953464 A y)). Qed.
Lemma lem4953466 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4953467 {A : Type'} : (term1390 A) = (term1455 A).
Proof. exact (MK_COMB (@lem4953466) (@lem4953465 A)). Qed.
Lemma lem4953469 {A B : Type'} (P : type1413 A B) : (term286 A B P) = (term287 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4953470 {A : Type'} (P : type1563 A) : (term1456 A P) = (term1457 A P).
Proof. exact (@lem4953469 nat (type643 A) P). Qed.
Lemma lem4953471 {A : Type'} : (term1458 A) = (term1459 A).
Proof. exact (@lem4953470 A (term1460 A)). Qed.
Lemma lem4953472 {A : Type'} (y : nat) : (term1461 A y) = (term1452 A y).
Proof. exact (eq_refl (term1461 A y)). Qed.
Lemma lem4953473 {A : Type'} (x : type643 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4953474 {A : Type'} (y : nat) (x : type643 A) : (term1462 A y x) = (term1463 A y x).
Proof. exact (MK_COMB (@lem4953472 A y) (@lem4953473 A x)). Qed.
Lemma lem4953475 {A : Type'} (y : nat) (x : type643 A) : (term1463 A y x) = (term1450 A y x).
Proof. exact (eq_refl (term1463 A y x)). Qed.
Lemma lem4953476 {A : Type'} (y : nat) (x : type643 A) : (term1462 A y x) = (term1450 A y x).
Proof. exact (TRANS (@lem4953474 A y x) (@lem4953475 A y x)). Qed.
Lemma lem4953477 {A : Type'} (y : nat) : (term1464 A y) = (term1452 A y).
Proof. exact (fun_ext (fun x : type643 A => @lem4953476 A y x)). Qed.
Lemma lem4953478 {A : Type'} : (@ex ((A -> Prop) -> (A -> nat) -> A)) = (@ex ((A -> Prop) -> (A -> nat) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> nat) -> A))). Qed.
Lemma lem4953479 {A : Type'} (y : nat) : (term1465 A y) = (term1453 A y).
Proof. exact (MK_COMB (@lem4953478 A) (@lem4953477 A y)). Qed.
Lemma lem4953480 {A : Type'} : (term1466 A) = (term1454 A).
Proof. exact (fun_ext (fun y : nat => @lem4953479 A y)). Qed.
Lemma lem4953481 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4953482 {A : Type'} : (term1458 A) = (term1455 A).
Proof. exact (MK_COMB (@lem4953481) (@lem4953480 A)). Qed.
Lemma lem4953483 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4953484 {A : Type'} : (term1467 A) = (term1468 A).
Proof. exact (MK_COMB (@lem4953483) (@lem4953482 A)). Qed.
Lemma lem4953485 {A : Type'} (y : nat) : (term1461 A y) = (term1452 A y).
Proof. exact (eq_refl (term1461 A y)). Qed.
Lemma lem4953486 {A : Type'} (x : type1572 A) (y : nat) : (x y) = (x y).
Proof. exact (eq_refl (x y)). Qed.
Lemma lem4953487 {A : Type'} (x : type1572 A) (y : nat) : (term1469 A x y) = (term1470 A x y).
Proof. exact (MK_COMB (@lem4953485 A y) (@lem4953486 A x y)). Qed.
Lemma lem4953488 {A : Type'} (x : type1572 A) (y : nat) : (term1470 A x y) = (term1471 A x y).
Proof. exact (eq_refl (term1470 A x y)). Qed.
Lemma lem4953489 {A : Type'} (x : type1572 A) (y : nat) : (term1469 A x y) = (term1471 A x y).
Proof. exact (TRANS (@lem4953487 A x y) (@lem4953488 A x y)). Qed.
Lemma lem4953490 {A : Type'} (x : type1572 A) : (term1472 A x) = (term1473 A x).
Proof. exact (fun_ext (fun y : nat => @lem4953489 A x y)). Qed.
Lemma lem4953491 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4953492 {A : Type'} (x : type1572 A) : (term1474 A x) = (term1475 A x).
Proof. exact (MK_COMB (@lem4953491) (@lem4953490 A x)). Qed.
Lemma lem4953493 {A : Type'} : (term1476 A) = (term1477 A).
Proof. exact (fun_ext (fun x : type1572 A => @lem4953492 A x)). Qed.
Lemma lem4953494 {A : Type'} : (@ex (nat -> (A -> Prop) -> (A -> nat) -> A)) = (@ex (nat -> (A -> Prop) -> (A -> nat) -> A)).
Proof. exact (eq_refl (@ex (nat -> (A -> Prop) -> (A -> nat) -> A))). Qed.
Lemma lem4953495 {A : Type'} : (term1459 A) = (term1478 A).
Proof. exact (MK_COMB (@lem4953494 A) (@lem4953493 A)). Qed.
Lemma lem4953496 {A : Type'} : ((term1458 A) = (term1459 A)) = ((term1455 A) = (term1478 A)).
Proof. exact (MK_COMB (@lem4953484 A) (@lem4953495 A)). Qed.
Lemma lem4953497 {A : Type'} : (term1455 A) = (term1478 A).
Proof. exact (EQ_MP (@lem4953496 A) (@lem4953471 A)). Qed.
Lemma lem4953498 {A : Type'} : (term1390 A) = (term1478 A).
Proof. exact (TRANS (@lem4953467 A) (@lem4953497 A)). Qed.
Lemma lem4953499 {A : Type'} : (term1387 A) = (term1387 A).
Proof. exact (eq_refl (term1387 A)). Qed.
Lemma lem4953500 {A : Type'} : (term1391 A) = (term1479 A).
Proof. exact (MK_COMB (@lem4953499 A) (@lem4953498 A)). Qed.
Lemma lem4953502 {A : Type'} (P : Prop) (Q : A -> Prop) : (term348 A P Q) = (term349 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4953503 {A : Type'} (P : Prop) (Q : type927 A) : (term1480 A P Q) = (term1481 A P Q).
Proof. exact (@lem4953502 (type1572 A) P Q). Qed.
Lemma lem4953504 {A : Type'} : (term1482 A) = (term1483 A).
Proof. exact (@lem4953503 A (term1385 A) (term1477 A)). Qed.
Lemma lem4953505 {A : Type'} (x : type1572 A) : (term1484 A x) = (term1475 A x).
Proof. exact (eq_refl (term1484 A x)). Qed.
Lemma lem4953506 {A : Type'} : (term1485 A) = (term1477 A).
Proof. exact (fun_ext (fun x : type1572 A => @lem4953505 A x)). Qed.
Lemma lem4953507 {A : Type'} : (@ex (nat -> (A -> Prop) -> (A -> nat) -> A)) = (@ex (nat -> (A -> Prop) -> (A -> nat) -> A)).
Proof. exact (eq_refl (@ex (nat -> (A -> Prop) -> (A -> nat) -> A))). Qed.
Lemma lem4953508 {A : Type'} : (term1486 A) = (term1478 A).
Proof. exact (MK_COMB (@lem4953507 A) (@lem4953506 A)). Qed.
Lemma lem4953509 {A : Type'} : (term1387 A) = (term1387 A).
Proof. exact (eq_refl (term1387 A)). Qed.
Lemma lem4953510 {A : Type'} : (term1482 A) = (term1479 A).
Proof. exact (MK_COMB (@lem4953509 A) (@lem4953508 A)). Qed.
Lemma lem4953511 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4953512 {A : Type'} : (term1487 A) = (term1488 A).
Proof. exact (MK_COMB (@lem4953511) (@lem4953510 A)). Qed.
Lemma lem4953513 {A : Type'} (x : type1572 A) : (term1484 A x) = (term1475 A x).
Proof. exact (eq_refl (term1484 A x)). Qed.
Lemma lem4953514 {A : Type'} : (term1387 A) = (term1387 A).
Proof. exact (eq_refl (term1387 A)). Qed.
Lemma lem4953515 {A : Type'} (x : type1572 A) : (term1489 A x) = (term1490 A x).
Proof. exact (MK_COMB (@lem4953514 A) (@lem4953513 A x)). Qed.
Lemma lem4953516 {A : Type'} : (term1491 A) = (term1492 A).
Proof. exact (fun_ext (fun x : type1572 A => @lem4953515 A x)). Qed.
Lemma lem4953517 {A : Type'} : (@ex (nat -> (A -> Prop) -> (A -> nat) -> A)) = (@ex (nat -> (A -> Prop) -> (A -> nat) -> A)).
Proof. exact (eq_refl (@ex (nat -> (A -> Prop) -> (A -> nat) -> A))). Qed.
Lemma lem4953518 {A : Type'} : (term1483 A) = (term1493 A).
Proof. exact (MK_COMB (@lem4953517 A) (@lem4953516 A)). Qed.
Lemma lem4953519 {A : Type'} : ((term1482 A) = (term1483 A)) = ((term1479 A) = (term1493 A)).
Proof. exact (MK_COMB (@lem4953512 A) (@lem4953518 A)). Qed.
Lemma lem4953520 {A : Type'} : (term1479 A) = (term1493 A).
Proof. exact (EQ_MP (@lem4953519 A) (@lem4953504 A)). Qed.
Lemma lem4953521 {A : Type'} : (term1391 A) = (term1493 A).
Proof. exact (TRANS (@lem4953500 A) (@lem4953520 A)). Qed.
Lemma lem4953522 {A : Type'} : (term1323 A) = (term1493 A).
Proof. exact (TRANS (@lem4953376 A) (@lem4953521 A)). Qed.
Lemma lem4953523 {A : Type'} : (term85 A) = (term1493 A).
Proof. exact (TRANS (@lem4952679 A) (@lem4953522 A)). Qed.
Lemma lem4953524 {A : Type'} (h1 : term85 A) : term1493 A.
Proof. exact (EQ_MP (@lem4953523 A) (@lem4947225 A h1)). Qed.
Lemma lem4953541 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term1494 A s x t) = (term1495 A s x t).
Proof. exact (@lem17930 (@IN A x s) (@IN A x t)). Qed.
Lemma lem4953552 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : ((@IN A x s) = (@IN A x t)) = (term1496 A s x t).
Proof. exact (@lem17784 (@IN A x s) (@IN A x t)). Qed.
Lemma lem4953553 {A : Type'} (P : A -> Prop) : (term211 A P) = (term212 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4953554 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1497 A s t) = (term1498 A s t).
Proof. exact (@lem4953553 A (term131 A s t)). Qed.
Lemma lem4953555 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term1499 A s t x) = ((@IN A x s) = (@IN A x t)).
Proof. exact (eq_refl (term1499 A s t x)). Qed.
Lemma lem4953556 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4953557 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term1500 A s t x) = (term1494 A s x t).
Proof. exact (MK_COMB (@lem4953556) (@lem4953555 A s x t)). Qed.
Lemma lem4953558 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term1500 A s t x) = (term1495 A s x t).
Proof. exact (TRANS (@lem4953557 A s x t) (@lem4953541 A s x t)). Qed.
Lemma lem4953559 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1501 A s t) = (term1502 A s t).
Proof. exact (fun_ext (fun x : A => @lem4953558 A s x t)). Qed.
Lemma lem4953560 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4953561 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1498 A s t) = (term1503 A s t).
Proof. exact (MK_COMB (@lem4953560 A) (@lem4953559 A s t)). Qed.
Lemma lem4953562 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1497 A s t) = (term1503 A s t).
Proof. exact (TRANS (@lem4953554 A s t) (@lem4953561 A s t)). Qed.
Lemma lem4953563 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term131 A s t) = (term1504 A s t).
Proof. exact (fun_ext (fun x : A => @lem4953552 A s x t)). Qed.
Lemma lem4953564 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4953565 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term132 A s t) = (term1505 A s t).
Proof. exact (MK_COMB (@lem4953564 A) (@lem4953563 A s t)). Qed.
Lemma lem4953567 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1506 A s t) = (term1506 A s t).
Proof. exact (eq_refl (term1506 A s t)). Qed.
Lemma lem4953568 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1507 A s t) = (term1508 A s t).
Proof. exact (MK_COMB (@lem4953567 A s t) (@lem4953565 A s t)). Qed.
Lemma lem4953570 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1509 A s t) = (term1509 A s t).
Proof. exact (eq_refl (term1509 A s t)). Qed.
Lemma lem4953571 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1510 A s t) = (term1511 A s t).
Proof. exact (MK_COMB (@lem4953570 A s t) (@lem4953562 A s t)). Qed.
Lemma lem4953572 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4953573 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1512 A s t) = (term1513 A s t).
Proof. exact (MK_COMB (@lem4953572) (@lem4953571 A s t)). Qed.
Lemma lem4953574 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1514 A s t) = (term1515 A s t).
Proof. exact (MK_COMB (@lem4953573 A s t) (@lem4953568 A s t)). Qed.
Lemma lem4953575 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((s = t) = (term132 A s t)) = (term1514 A s t).
Proof. exact (@lem17784 (s = t) (term132 A s t)). Qed.
Lemma lem4953576 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((s = t) = (term132 A s t)) = (term1515 A s t).
Proof. exact (TRANS (@lem4953575 A s t) (@lem4953574 A s t)). Qed.
Lemma lem4953577 {A : Type'} (s : A -> Prop) : (term134 A s) = (term1516 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4953576 A s t)). Qed.
Lemma lem4953578 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4953579 {A : Type'} (s : A -> Prop) : (term135 A s) = (term1517 A s).
Proof. exact (MK_COMB (@lem4953578 A) (@lem4953577 A s)). Qed.
Lemma lem4953580 {A : Type'} : (term136 A) = (term1518 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4953579 A s)). Qed.
Lemma lem4953581 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4953582 {A : Type'} : (term82 A) = (term1519 A).
Proof. exact (MK_COMB (@lem4953581 A) (@lem4953580 A)). Qed.
Lemma lem4953588 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term554 A P Q) = (term555 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4953589 {A : Type'} (P : type686 A) (Q : type686 A) : (term580 A P Q) = (term581 A P Q).
Proof. exact (@lem4953588 (A -> Prop) P Q). Qed.
Lemma lem4953590 {A : Type'} (s : A -> Prop) : (term1520 A s) = (term1521 A s).
Proof. exact (@lem4953589 A (term1522 A s) (term1523 A s)). Qed.
Lemma lem4953591 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1524 A s t) = (term1511 A s t).
Proof. exact (eq_refl (term1524 A s t)). Qed.
Lemma lem4953592 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4953593 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1525 A s t) = (term1513 A s t).
Proof. exact (MK_COMB (@lem4953592) (@lem4953591 A s t)). Qed.
Lemma lem4953594 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1526 A s t) = (term1508 A s t).
Proof. exact (eq_refl (term1526 A s t)). Qed.
Lemma lem4953595 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1527 A s t) = (term1515 A s t).
Proof. exact (MK_COMB (@lem4953593 A s t) (@lem4953594 A s t)). Qed.
Lemma lem4953596 {A : Type'} (s : A -> Prop) : (term1528 A s) = (term1516 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4953595 A s t)). Qed.
Lemma lem4953597 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4953598 {A : Type'} (s : A -> Prop) : (term1520 A s) = (term1517 A s).
Proof. exact (MK_COMB (@lem4953597 A) (@lem4953596 A s)). Qed.
Lemma lem4953599 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4953600 {A : Type'} (s : A -> Prop) : (term1529 A s) = (term1530 A s).
Proof. exact (MK_COMB (@lem4953599) (@lem4953598 A s)). Qed.
Lemma lem4953601 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1524 A s t) = (term1511 A s t).
Proof. exact (eq_refl (term1524 A s t)). Qed.
Lemma lem4953602 {A : Type'} (s : A -> Prop) : (term1531 A s) = (term1522 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4953601 A s t)). Qed.
Lemma lem4953603 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4953604 {A : Type'} (s : A -> Prop) : (term1532 A s) = (term1533 A s).
Proof. exact (MK_COMB (@lem4953603 A) (@lem4953602 A s)). Qed.
Lemma lem4953605 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4953606 {A : Type'} (s : A -> Prop) : (term1534 A s) = (term1535 A s).
Proof. exact (MK_COMB (@lem4953605) (@lem4953604 A s)). Qed.
Lemma lem4953607 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1526 A s t) = (term1508 A s t).
Proof. exact (eq_refl (term1526 A s t)). Qed.
Lemma lem4953608 {A : Type'} (s : A -> Prop) : (term1536 A s) = (term1523 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4953607 A s t)). Qed.
Lemma lem4953609 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4953610 {A : Type'} (s : A -> Prop) : (term1537 A s) = (term1538 A s).
Proof. exact (MK_COMB (@lem4953609 A) (@lem4953608 A s)). Qed.
Lemma lem4953611 {A : Type'} (s : A -> Prop) : (term1521 A s) = (term1539 A s).
Proof. exact (MK_COMB (@lem4953606 A s) (@lem4953610 A s)). Qed.
Lemma lem4953612 {A : Type'} (s : A -> Prop) : ((term1520 A s) = (term1521 A s)) = ((term1517 A s) = (term1539 A s)).
Proof. exact (MK_COMB (@lem4953600 A s) (@lem4953611 A s)). Qed.
Lemma lem4953613 {A : Type'} (s : A -> Prop) : (term1517 A s) = (term1539 A s).
Proof. exact (EQ_MP (@lem4953612 A s) (@lem4953590 A s)). Qed.
Lemma lem4953759 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term554 A P Q) = (term555 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4953760 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term554 A P Q) = (term555 A P Q).
Proof. exact (@lem4953759 A P Q). Qed.
Lemma lem4953761 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1540 A s t) = (term1541 A s t).
Proof. exact (@lem4953760 A (term1542 A s t) (term1543 A s t)). Qed.
Lemma lem4953762 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term1544 A s t x) = (term1545 A s x t).
Proof. exact (eq_refl (term1544 A s t x)). Qed.
Lemma lem4953763 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4953764 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term1546 A s t x) = (term1547 A s x t).
Proof. exact (MK_COMB (@lem4953763) (@lem4953762 A s x t)). Qed.
Lemma lem4953765 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term1548 A s t x) = (term1549 A s x t).
Proof. exact (eq_refl (term1548 A s t x)). Qed.
Lemma lem4953766 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term1550 A s t x) = (term1496 A s x t).
Proof. exact (MK_COMB (@lem4953764 A s x t) (@lem4953765 A s x t)). Qed.
Lemma lem4953767 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1551 A s t) = (term1504 A s t).
Proof. exact (fun_ext (fun x : A => @lem4953766 A s x t)). Qed.
Lemma lem4953768 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4953769 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1540 A s t) = (term1505 A s t).
Proof. exact (MK_COMB (@lem4953768 A) (@lem4953767 A s t)). Qed.
Lemma lem4953770 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4953771 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1552 A s t) = (term1553 A s t).
Proof. exact (MK_COMB (@lem4953770) (@lem4953769 A s t)). Qed.
Lemma lem4953772 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term1544 A s t x) = (term1545 A s x t).
Proof. exact (eq_refl (term1544 A s t x)). Qed.
Lemma lem4953773 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1554 A s t) = (term1542 A s t).
Proof. exact (fun_ext (fun x : A => @lem4953772 A s x t)). Qed.
Lemma lem4953774 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4953775 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1555 A s t) = (term1556 A s t).
Proof. exact (MK_COMB (@lem4953774 A) (@lem4953773 A s t)). Qed.
Lemma lem4953776 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4953777 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1557 A s t) = (term1558 A s t).
Proof. exact (MK_COMB (@lem4953776) (@lem4953775 A s t)). Qed.
Lemma lem4953778 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term1548 A s t x) = (term1549 A s x t).
Proof. exact (eq_refl (term1548 A s t x)). Qed.
Lemma lem4953779 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1559 A s t) = (term1543 A s t).
Proof. exact (fun_ext (fun x : A => @lem4953778 A s x t)). Qed.
Lemma lem4953780 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4953781 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1560 A s t) = (term1561 A s t).
Proof. exact (MK_COMB (@lem4953780 A) (@lem4953779 A s t)). Qed.
Lemma lem4953782 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1541 A s t) = (term1562 A s t).
Proof. exact (MK_COMB (@lem4953777 A s t) (@lem4953781 A s t)). Qed.
Lemma lem4953783 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term1540 A s t) = (term1541 A s t)) = ((term1505 A s t) = (term1562 A s t)).
Proof. exact (MK_COMB (@lem4953771 A s t) (@lem4953782 A s t)). Qed.
Lemma lem4953784 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1505 A s t) = (term1562 A s t).
Proof. exact (EQ_MP (@lem4953783 A s t) (@lem4953761 A s t)). Qed.
Lemma lem4953881 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1506 A s t) = (term1506 A s t).
Proof. exact (eq_refl (term1506 A s t)). Qed.
Lemma lem4953882 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1508 A s t) = (term1563 A s t).
Proof. exact (MK_COMB (@lem4953881 A s t) (@lem4953784 A s t)). Qed.
Lemma lem4953883 {A : Type'} (s : A -> Prop) : (term1523 A s) = (term1564 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4953882 A s t)). Qed.
Lemma lem4953884 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4953885 {A : Type'} (s : A -> Prop) : (term1538 A s) = (term1565 A s).
Proof. exact (MK_COMB (@lem4953884 A) (@lem4953883 A s)). Qed.
Lemma lem4953934 {A : Type'} (s : A -> Prop) : (term1535 A s) = (term1535 A s).
Proof. exact (eq_refl (term1535 A s)). Qed.
Lemma lem4953935 {A : Type'} (s : A -> Prop) : (term1539 A s) = (term1566 A s).
Proof. exact (MK_COMB (@lem4953934 A s) (@lem4953885 A s)). Qed.
Lemma lem4953936 {A : Type'} (s : A -> Prop) : (term1517 A s) = (term1566 A s).
Proof. exact (TRANS (@lem4953613 A s) (@lem4953935 A s)). Qed.
Lemma lem4953937 {A : Type'} : (term1518 A) = (term1567 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4953936 A s)). Qed.
Lemma lem4953938 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4953939 {A : Type'} : (term1519 A) = (term1568 A).
Proof. exact (MK_COMB (@lem4953938 A) (@lem4953937 A)). Qed.
Lemma lem4953941 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term554 A P Q) = (term555 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4953942 {A : Type'} (P : type686 A) (Q : type686 A) : (term580 A P Q) = (term581 A P Q).
Proof. exact (@lem4953941 (A -> Prop) P Q). Qed.
Lemma lem4953943 {A : Type'} : (term1569 A) = (term1570 A).
Proof. exact (@lem4953942 A (term1571 A) (term1572 A)). Qed.
Lemma lem4953944 {A : Type'} (s : A -> Prop) : (term1573 A s) = (term1533 A s).
Proof. exact (eq_refl (term1573 A s)). Qed.
Lemma lem4953945 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4953946 {A : Type'} (s : A -> Prop) : (term1574 A s) = (term1535 A s).
Proof. exact (MK_COMB (@lem4953945) (@lem4953944 A s)). Qed.
Lemma lem4953947 {A : Type'} (s : A -> Prop) : (term1575 A s) = (term1565 A s).
Proof. exact (eq_refl (term1575 A s)). Qed.
Lemma lem4953948 {A : Type'} (s : A -> Prop) : (term1576 A s) = (term1566 A s).
Proof. exact (MK_COMB (@lem4953946 A s) (@lem4953947 A s)). Qed.
Lemma lem4953949 {A : Type'} : (term1577 A) = (term1567 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4953948 A s)). Qed.
Lemma lem4953950 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4953951 {A : Type'} : (term1569 A) = (term1568 A).
Proof. exact (MK_COMB (@lem4953950 A) (@lem4953949 A)). Qed.
Lemma lem4953952 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4953953 {A : Type'} : (term1578 A) = (term1579 A).
Proof. exact (MK_COMB (@lem4953952) (@lem4953951 A)). Qed.
Lemma lem4953954 {A : Type'} (s : A -> Prop) : (term1573 A s) = (term1533 A s).
Proof. exact (eq_refl (term1573 A s)). Qed.
Lemma lem4953955 {A : Type'} : (term1580 A) = (term1571 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4953954 A s)). Qed.
Lemma lem4953956 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4953957 {A : Type'} : (term1581 A) = (term1582 A).
Proof. exact (MK_COMB (@lem4953956 A) (@lem4953955 A)). Qed.
Lemma lem4953958 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4953959 {A : Type'} : (term1583 A) = (term1584 A).
Proof. exact (MK_COMB (@lem4953958) (@lem4953957 A)). Qed.
Lemma lem4953960 {A : Type'} (s : A -> Prop) : (term1575 A s) = (term1565 A s).
Proof. exact (eq_refl (term1575 A s)). Qed.
Lemma lem4953961 {A : Type'} : (term1585 A) = (term1572 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4953960 A s)). Qed.
Lemma lem4953962 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4953963 {A : Type'} : (term1586 A) = (term1587 A).
Proof. exact (MK_COMB (@lem4953962 A) (@lem4953961 A)). Qed.
Lemma lem4953964 {A : Type'} : (term1570 A) = (term1588 A).
Proof. exact (MK_COMB (@lem4953959 A) (@lem4953963 A)). Qed.
Lemma lem4953965 {A : Type'} : ((term1569 A) = (term1570 A)) = ((term1568 A) = (term1588 A)).
Proof. exact (MK_COMB (@lem4953953 A) (@lem4953964 A)). Qed.
Lemma lem4953966 {A : Type'} : (term1568 A) = (term1588 A).
Proof. exact (EQ_MP (@lem4953965 A) (@lem4953943 A)). Qed.
Lemma lem4954215 {A : Type'} : (term1519 A) = (term1588 A).
Proof. exact (TRANS (@lem4953939 A) (@lem4953966 A)). Qed.
Lemma lem4954217 {A : Type'} (P : Prop) (Q : A -> Prop) : (term270 A P Q) = (term271 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4954218 {A : Type'} (P : Prop) (Q : A -> Prop) : (term270 A P Q) = (term271 A P Q).
Proof. exact (@lem4954217 A P Q). Qed.
Lemma lem4954219 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1589 A s t) = (term1590 A s t).
Proof. exact (@lem4954218 A (s = t) (term1502 A s t)). Qed.
Lemma lem4954220 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term1591 A s t x) = (term1495 A s x t).
Proof. exact (eq_refl (term1591 A s t x)). Qed.
Lemma lem4954221 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1592 A s t) = (term1502 A s t).
Proof. exact (fun_ext (fun x : A => @lem4954220 A s x t)). Qed.
Lemma lem4954222 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4954223 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1593 A s t) = (term1503 A s t).
Proof. exact (MK_COMB (@lem4954222 A) (@lem4954221 A s t)). Qed.
Lemma lem4954224 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1509 A s t) = (term1509 A s t).
Proof. exact (eq_refl (term1509 A s t)). Qed.
Lemma lem4954225 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1589 A s t) = (term1511 A s t).
Proof. exact (MK_COMB (@lem4954224 A s t) (@lem4954223 A s t)). Qed.
Lemma lem4954226 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4954227 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1594 A s t) = (term1595 A s t).
Proof. exact (MK_COMB (@lem4954226) (@lem4954225 A s t)). Qed.
Lemma lem4954228 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term1591 A s t x) = (term1495 A s x t).
Proof. exact (eq_refl (term1591 A s t x)). Qed.
Lemma lem4954229 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1509 A s t) = (term1509 A s t).
Proof. exact (eq_refl (term1509 A s t)). Qed.
Lemma lem4954230 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term1596 A s t x) = (term1597 A s x t).
Proof. exact (MK_COMB (@lem4954229 A s t) (@lem4954228 A s x t)). Qed.
Lemma lem4954231 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1598 A s t) = (term1599 A s t).
Proof. exact (fun_ext (fun x : A => @lem4954230 A s x t)). Qed.
Lemma lem4954232 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4954233 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1590 A s t) = (term1600 A s t).
Proof. exact (MK_COMB (@lem4954232 A) (@lem4954231 A s t)). Qed.
Lemma lem4954234 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term1589 A s t) = (term1590 A s t)) = ((term1511 A s t) = (term1600 A s t)).
Proof. exact (MK_COMB (@lem4954227 A s t) (@lem4954233 A s t)). Qed.
Lemma lem4954235 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1511 A s t) = (term1600 A s t).
Proof. exact (EQ_MP (@lem4954234 A s t) (@lem4954219 A s t)). Qed.
Lemma lem4954236 {A : Type'} (s : A -> Prop) : (term1522 A s) = (term1601 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4954235 A s t)). Qed.
Lemma lem4954237 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4954238 {A : Type'} (s : A -> Prop) : (term1533 A s) = (term1602 A s).
Proof. exact (MK_COMB (@lem4954237 A) (@lem4954236 A s)). Qed.
Lemma lem4954240 {A B : Type'} (P : type1413 A B) : (term286 A B P) = (term287 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4954241 {A : Type'} (P : type672 A) : (term1603 A P) = (term1604 A P).
Proof. exact (@lem4954240 (A -> Prop) A P). Qed.
Lemma lem4954242 {A : Type'} (s : A -> Prop) : (term1605 A s) = (term1606 A s).
Proof. exact (@lem4954241 A (term1607 A s)). Qed.
Lemma lem4954243 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1608 A s t) = (term1599 A s t).
Proof. exact (eq_refl (term1608 A s t)). Qed.
Lemma lem4954244 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4954245 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term1609 A s t x) = (term1610 A s t x).
Proof. exact (MK_COMB (@lem4954243 A s t) (@lem4954244 A x)). Qed.
Lemma lem4954246 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term1610 A s t x) = (term1597 A s x t).
Proof. exact (eq_refl (term1610 A s t x)). Qed.
Lemma lem4954247 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term1609 A s t x) = (term1597 A s x t).
Proof. exact (TRANS (@lem4954245 A s t x) (@lem4954246 A s x t)). Qed.
Lemma lem4954248 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1611 A s t) = (term1599 A s t).
Proof. exact (fun_ext (fun x : A => @lem4954247 A s x t)). Qed.
Lemma lem4954249 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4954250 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1612 A s t) = (term1600 A s t).
Proof. exact (MK_COMB (@lem4954249 A) (@lem4954248 A s t)). Qed.
Lemma lem4954251 {A : Type'} (s : A -> Prop) : (term1613 A s) = (term1601 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4954250 A s t)). Qed.
Lemma lem4954252 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4954253 {A : Type'} (s : A -> Prop) : (term1605 A s) = (term1602 A s).
Proof. exact (MK_COMB (@lem4954252 A) (@lem4954251 A s)). Qed.
Lemma lem4954254 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4954255 {A : Type'} (s : A -> Prop) : (term1614 A s) = (term1615 A s).
Proof. exact (MK_COMB (@lem4954254) (@lem4954253 A s)). Qed.
Lemma lem4954256 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1608 A s t) = (term1599 A s t).
Proof. exact (eq_refl (term1608 A s t)). Qed.
Lemma lem4954257 {A : Type'} (x : type684 A) (t : A -> Prop) : (x t) = (x t).
Proof. exact (eq_refl (x t)). Qed.
Lemma lem4954258 {A : Type'} (s : A -> Prop) (x : type684 A) (t : A -> Prop) : (term1616 A s x t) = (term1617 A s x t).
Proof. exact (MK_COMB (@lem4954256 A s t) (@lem4954257 A x t)). Qed.
Lemma lem4954259 {A : Type'} (s : A -> Prop) (x : type684 A) (t : A -> Prop) : (term1617 A s x t) = (term1618 A s x t).
Proof. exact (eq_refl (term1617 A s x t)). Qed.
Lemma lem4954260 {A : Type'} (s : A -> Prop) (x : type684 A) (t : A -> Prop) : (term1616 A s x t) = (term1618 A s x t).
Proof. exact (TRANS (@lem4954258 A s x t) (@lem4954259 A s x t)). Qed.
Lemma lem4954261 {A : Type'} (s : A -> Prop) (x : type684 A) : (term1619 A s x) = (term1620 A s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4954260 A s x t)). Qed.
Lemma lem4954262 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4954263 {A : Type'} (s : A -> Prop) (x : type684 A) : (term1621 A s x) = (term1622 A s x).
Proof. exact (MK_COMB (@lem4954262 A) (@lem4954261 A s x)). Qed.
Lemma lem4954264 {A : Type'} (s : A -> Prop) : (term1623 A s) = (term1624 A s).
Proof. exact (fun_ext (fun x : type684 A => @lem4954263 A s x)). Qed.
Lemma lem4954265 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem4954266 {A : Type'} (s : A -> Prop) : (term1606 A s) = (term1625 A s).
Proof. exact (MK_COMB (@lem4954265 A) (@lem4954264 A s)). Qed.
Lemma lem4954267 {A : Type'} (s : A -> Prop) : ((term1605 A s) = (term1606 A s)) = ((term1602 A s) = (term1625 A s)).
Proof. exact (MK_COMB (@lem4954255 A s) (@lem4954266 A s)). Qed.
Lemma lem4954268 {A : Type'} (s : A -> Prop) : (term1602 A s) = (term1625 A s).
Proof. exact (EQ_MP (@lem4954267 A s) (@lem4954242 A s)). Qed.
Lemma lem4954269 {A : Type'} (s : A -> Prop) : (term1533 A s) = (term1625 A s).
Proof. exact (TRANS (@lem4954238 A s) (@lem4954268 A s)). Qed.
Lemma lem4954270 {A : Type'} : (term1571 A) = (term1626 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4954269 A s)). Qed.
Lemma lem4954271 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4954272 {A : Type'} : (term1582 A) = (term1627 A).
Proof. exact (MK_COMB (@lem4954271 A) (@lem4954270 A)). Qed.
Lemma lem4954274 {A B : Type'} (P : type1413 A B) : (term286 A B P) = (term287 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4954275 {A : Type'} (P : type597 A) : (term1628 A P) = (term1629 A P).
Proof. exact (@lem4954274 (A -> Prop) (type684 A) P). Qed.
Lemma lem4954276 {A : Type'} : (term1630 A) = (term1631 A).
Proof. exact (@lem4954275 A (term1632 A)). Qed.
Lemma lem4954277 {A : Type'} (s : A -> Prop) : (term1633 A s) = (term1624 A s).
Proof. exact (eq_refl (term1633 A s)). Qed.
Lemma lem4954278 {A : Type'} (x : type684 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4954279 {A : Type'} (s : A -> Prop) (x : type684 A) : (term1634 A s x) = (term1635 A s x).
Proof. exact (MK_COMB (@lem4954277 A s) (@lem4954278 A x)). Qed.
Lemma lem4954280 {A : Type'} (s : A -> Prop) (x : type684 A) : (term1635 A s x) = (term1622 A s x).
Proof. exact (eq_refl (term1635 A s x)). Qed.
Lemma lem4954281 {A : Type'} (s : A -> Prop) (x : type684 A) : (term1634 A s x) = (term1622 A s x).
Proof. exact (TRANS (@lem4954279 A s x) (@lem4954280 A s x)). Qed.
Lemma lem4954282 {A : Type'} (s : A -> Prop) : (term1636 A s) = (term1624 A s).
Proof. exact (fun_ext (fun x : type684 A => @lem4954281 A s x)). Qed.
Lemma lem4954283 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem4954284 {A : Type'} (s : A -> Prop) : (term1637 A s) = (term1625 A s).
Proof. exact (MK_COMB (@lem4954283 A) (@lem4954282 A s)). Qed.
Lemma lem4954285 {A : Type'} : (term1638 A) = (term1626 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4954284 A s)). Qed.
Lemma lem4954286 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4954287 {A : Type'} : (term1630 A) = (term1627 A).
Proof. exact (MK_COMB (@lem4954286 A) (@lem4954285 A)). Qed.
Lemma lem4954288 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4954289 {A : Type'} : (term1639 A) = (term1640 A).
Proof. exact (MK_COMB (@lem4954288) (@lem4954287 A)). Qed.
Lemma lem4954290 {A : Type'} (s : A -> Prop) : (term1633 A s) = (term1624 A s).
Proof. exact (eq_refl (term1633 A s)). Qed.
Lemma lem4954291 {A : Type'} (x : type638 A) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem4954292 {A : Type'} (x : type638 A) (s : A -> Prop) : (term1641 A x s) = (term1642 A x s).
Proof. exact (MK_COMB (@lem4954290 A s) (@lem4954291 A x s)). Qed.
Lemma lem4954293 {A : Type'} (x : type638 A) (s : A -> Prop) : (term1642 A x s) = (term1643 A x s).
Proof. exact (eq_refl (term1642 A x s)). Qed.
Lemma lem4954294 {A : Type'} (x : type638 A) (s : A -> Prop) : (term1641 A x s) = (term1643 A x s).
Proof. exact (TRANS (@lem4954292 A x s) (@lem4954293 A x s)). Qed.
Lemma lem4954295 {A : Type'} (x : type638 A) : (term1644 A x) = (term1645 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4954294 A x s)). Qed.
Lemma lem4954296 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4954297 {A : Type'} (x : type638 A) : (term1646 A x) = (term1647 A x).
Proof. exact (MK_COMB (@lem4954296 A) (@lem4954295 A x)). Qed.
Lemma lem4954298 {A : Type'} : (term1648 A) = (term1649 A).
Proof. exact (fun_ext (fun x : type638 A => @lem4954297 A x)). Qed.
Lemma lem4954299 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A)) = (@ex ((A -> Prop) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A))). Qed.
Lemma lem4954300 {A : Type'} : (term1631 A) = (term1650 A).
Proof. exact (MK_COMB (@lem4954299 A) (@lem4954298 A)). Qed.
Lemma lem4954301 {A : Type'} : ((term1630 A) = (term1631 A)) = ((term1627 A) = (term1650 A)).
Proof. exact (MK_COMB (@lem4954289 A) (@lem4954300 A)). Qed.
Lemma lem4954302 {A : Type'} : (term1627 A) = (term1650 A).
Proof. exact (EQ_MP (@lem4954301 A) (@lem4954276 A)). Qed.
Lemma lem4954303 {A : Type'} : (term1582 A) = (term1650 A).
Proof. exact (TRANS (@lem4954272 A) (@lem4954302 A)). Qed.
Lemma lem4954304 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4954305 {A : Type'} : (term1584 A) = (term1651 A).
Proof. exact (MK_COMB (@lem4954304) (@lem4954303 A)). Qed.
Lemma lem4954306 {A : Type'} : (term1587 A) = (term1587 A).
Proof. exact (eq_refl (term1587 A)). Qed.
Lemma lem4954307 {A : Type'} : (term1588 A) = (term1652 A).
Proof. exact (MK_COMB (@lem4954305 A) (@lem4954306 A)). Qed.
Lemma lem4954309 {A : Type'} (P : A -> Prop) (Q : Prop) : (term313 A P Q) = (term314 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4954310 {A : Type'} (P : type139 A) (Q : Prop) : (term1653 A P Q) = (term1654 A P Q).
Proof. exact (@lem4954309 (type638 A) P Q). Qed.
Lemma lem4954311 {A : Type'} : (term1655 A) = (term1656 A).
Proof. exact (@lem4954310 A (term1649 A) (term1587 A)). Qed.
Lemma lem4954312 {A : Type'} (x : type638 A) : (term1657 A x) = (term1647 A x).
Proof. exact (eq_refl (term1657 A x)). Qed.
Lemma lem4954313 {A : Type'} : (term1658 A) = (term1649 A).
Proof. exact (fun_ext (fun x : type638 A => @lem4954312 A x)). Qed.
Lemma lem4954314 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A)) = (@ex ((A -> Prop) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A))). Qed.
Lemma lem4954315 {A : Type'} : (term1659 A) = (term1650 A).
Proof. exact (MK_COMB (@lem4954314 A) (@lem4954313 A)). Qed.
Lemma lem4954316 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4954317 {A : Type'} : (term1660 A) = (term1651 A).
Proof. exact (MK_COMB (@lem4954316) (@lem4954315 A)). Qed.
Lemma lem4954318 {A : Type'} : (term1587 A) = (term1587 A).
Proof. exact (eq_refl (term1587 A)). Qed.
Lemma lem4954319 {A : Type'} : (term1655 A) = (term1652 A).
Proof. exact (MK_COMB (@lem4954317 A) (@lem4954318 A)). Qed.
Lemma lem4954320 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4954321 {A : Type'} : (term1661 A) = (term1662 A).
Proof. exact (MK_COMB (@lem4954320) (@lem4954319 A)). Qed.
Lemma lem4954322 {A : Type'} (x : type638 A) : (term1657 A x) = (term1647 A x).
Proof. exact (eq_refl (term1657 A x)). Qed.
Lemma lem4954323 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4954324 {A : Type'} (x : type638 A) : (term1663 A x) = (term1664 A x).
Proof. exact (MK_COMB (@lem4954323) (@lem4954322 A x)). Qed.
Lemma lem4954325 {A : Type'} : (term1587 A) = (term1587 A).
Proof. exact (eq_refl (term1587 A)). Qed.
Lemma lem4954326 {A : Type'} (x : type638 A) : (term1665 A x) = (term1666 A x).
Proof. exact (MK_COMB (@lem4954324 A x) (@lem4954325 A)). Qed.
Lemma lem4954327 {A : Type'} : (term1667 A) = (term1668 A).
Proof. exact (fun_ext (fun x : type638 A => @lem4954326 A x)). Qed.
Lemma lem4954328 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A)) = (@ex ((A -> Prop) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A))). Qed.
Lemma lem4954329 {A : Type'} : (term1656 A) = (term1669 A).
Proof. exact (MK_COMB (@lem4954328 A) (@lem4954327 A)). Qed.
Lemma lem4954330 {A : Type'} : ((term1655 A) = (term1656 A)) = ((term1652 A) = (term1669 A)).
Proof. exact (MK_COMB (@lem4954321 A) (@lem4954329 A)). Qed.
Lemma lem4954331 {A : Type'} : (term1652 A) = (term1669 A).
Proof. exact (EQ_MP (@lem4954330 A) (@lem4954311 A)). Qed.
Lemma lem4954332 {A : Type'} : (term1588 A) = (term1669 A).
Proof. exact (TRANS (@lem4954307 A) (@lem4954331 A)). Qed.
Lemma lem4954333 {A : Type'} : (term1519 A) = (term1669 A).
Proof. exact (TRANS (@lem4954215 A) (@lem4954332 A)). Qed.
Lemma lem4954334 {A : Type'} : (term82 A) = (term1669 A).
Proof. exact (TRANS (@lem4953582 A) (@lem4954333 A)). Qed.
Lemma lem4954335 {A : Type'} (h1 : term82 A) : term1669 A.
Proof. exact (EQ_MP (@lem4954334 A) (@lem4947226 A h1)). Qed.
Lemma lem4954352 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term1494 B s x t) = (term1495 B s x t).
Proof. exact (@lem17930 (@IN B x s) (@IN B x t)). Qed.
Lemma lem4954363 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : ((@IN B x s) = (@IN B x t)) = (term1496 B s x t).
Proof. exact (@lem17784 (@IN B x s) (@IN B x t)). Qed.
Lemma lem4954364 {B : Type'} (P : B -> Prop) : (term211 B P) = (term212 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem4954365 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1497 B s t) = (term1498 B s t).
Proof. exact (@lem4954364 B (term131 B s t)). Qed.
Lemma lem4954366 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term1499 B s t x) = ((@IN B x s) = (@IN B x t)).
Proof. exact (eq_refl (term1499 B s t x)). Qed.
Lemma lem4954367 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4954368 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term1500 B s t x) = (term1494 B s x t).
Proof. exact (MK_COMB (@lem4954367) (@lem4954366 B s x t)). Qed.
Lemma lem4954369 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term1500 B s t x) = (term1495 B s x t).
Proof. exact (TRANS (@lem4954368 B s x t) (@lem4954352 B s x t)). Qed.
Lemma lem4954370 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1501 B s t) = (term1502 B s t).
Proof. exact (fun_ext (fun x : B => @lem4954369 B s x t)). Qed.
Lemma lem4954371 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4954372 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1498 B s t) = (term1503 B s t).
Proof. exact (MK_COMB (@lem4954371 B) (@lem4954370 B s t)). Qed.
Lemma lem4954373 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1497 B s t) = (term1503 B s t).
Proof. exact (TRANS (@lem4954365 B s t) (@lem4954372 B s t)). Qed.
Lemma lem4954374 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term131 B s t) = (term1504 B s t).
Proof. exact (fun_ext (fun x : B => @lem4954363 B s x t)). Qed.
Lemma lem4954375 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4954376 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term132 B s t) = (term1505 B s t).
Proof. exact (MK_COMB (@lem4954375 B) (@lem4954374 B s t)). Qed.
Lemma lem4954378 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1506 B s t) = (term1506 B s t).
Proof. exact (eq_refl (term1506 B s t)). Qed.
Lemma lem4954379 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1507 B s t) = (term1508 B s t).
Proof. exact (MK_COMB (@lem4954378 B s t) (@lem4954376 B s t)). Qed.
Lemma lem4954381 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1509 B s t) = (term1509 B s t).
Proof. exact (eq_refl (term1509 B s t)). Qed.
Lemma lem4954382 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1510 B s t) = (term1511 B s t).
Proof. exact (MK_COMB (@lem4954381 B s t) (@lem4954373 B s t)). Qed.
Lemma lem4954383 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4954384 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1512 B s t) = (term1513 B s t).
Proof. exact (MK_COMB (@lem4954383) (@lem4954382 B s t)). Qed.
Lemma lem4954385 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1514 B s t) = (term1515 B s t).
Proof. exact (MK_COMB (@lem4954384 B s t) (@lem4954379 B s t)). Qed.
Lemma lem4954386 {B : Type'} (s : B -> Prop) (t : B -> Prop) : ((s = t) = (term132 B s t)) = (term1514 B s t).
Proof. exact (@lem17784 (s = t) (term132 B s t)). Qed.
Lemma lem4954387 {B : Type'} (s : B -> Prop) (t : B -> Prop) : ((s = t) = (term132 B s t)) = (term1515 B s t).
Proof. exact (TRANS (@lem4954386 B s t) (@lem4954385 B s t)). Qed.
Lemma lem4954388 {B : Type'} (s : B -> Prop) : (term134 B s) = (term1516 B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4954387 B s t)). Qed.
Lemma lem4954389 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4954390 {B : Type'} (s : B -> Prop) : (term135 B s) = (term1517 B s).
Proof. exact (MK_COMB (@lem4954389 B) (@lem4954388 B s)). Qed.
Lemma lem4954391 {B : Type'} : (term136 B) = (term1518 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem4954390 B s)). Qed.
Lemma lem4954392 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4954393 {B : Type'} : (term82 B) = (term1519 B).
Proof. exact (MK_COMB (@lem4954392 B) (@lem4954391 B)). Qed.
Lemma lem4954399 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term554 A P Q) = (term555 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4954400 {B : Type'} (P : type686 B) (Q : type686 B) : (term580 B P Q) = (term581 B P Q).
Proof. exact (@lem4954399 (B -> Prop) P Q). Qed.
Lemma lem4954401 {B : Type'} (s : B -> Prop) : (term1520 B s) = (term1521 B s).
Proof. exact (@lem4954400 B (term1522 B s) (term1523 B s)). Qed.
Lemma lem4954402 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1524 B s t) = (term1511 B s t).
Proof. exact (eq_refl (term1524 B s t)). Qed.
Lemma lem4954403 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4954404 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1525 B s t) = (term1513 B s t).
Proof. exact (MK_COMB (@lem4954403) (@lem4954402 B s t)). Qed.
Lemma lem4954405 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1526 B s t) = (term1508 B s t).
Proof. exact (eq_refl (term1526 B s t)). Qed.
Lemma lem4954406 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1527 B s t) = (term1515 B s t).
Proof. exact (MK_COMB (@lem4954404 B s t) (@lem4954405 B s t)). Qed.
Lemma lem4954407 {B : Type'} (s : B -> Prop) : (term1528 B s) = (term1516 B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4954406 B s t)). Qed.
Lemma lem4954408 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4954409 {B : Type'} (s : B -> Prop) : (term1520 B s) = (term1517 B s).
Proof. exact (MK_COMB (@lem4954408 B) (@lem4954407 B s)). Qed.
Lemma lem4954410 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4954411 {B : Type'} (s : B -> Prop) : (term1529 B s) = (term1530 B s).
Proof. exact (MK_COMB (@lem4954410) (@lem4954409 B s)). Qed.
Lemma lem4954412 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1524 B s t) = (term1511 B s t).
Proof. exact (eq_refl (term1524 B s t)). Qed.
Lemma lem4954413 {B : Type'} (s : B -> Prop) : (term1531 B s) = (term1522 B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4954412 B s t)). Qed.
Lemma lem4954414 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4954415 {B : Type'} (s : B -> Prop) : (term1532 B s) = (term1533 B s).
Proof. exact (MK_COMB (@lem4954414 B) (@lem4954413 B s)). Qed.
Lemma lem4954416 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4954417 {B : Type'} (s : B -> Prop) : (term1534 B s) = (term1535 B s).
Proof. exact (MK_COMB (@lem4954416) (@lem4954415 B s)). Qed.
Lemma lem4954418 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1526 B s t) = (term1508 B s t).
Proof. exact (eq_refl (term1526 B s t)). Qed.
Lemma lem4954419 {B : Type'} (s : B -> Prop) : (term1536 B s) = (term1523 B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4954418 B s t)). Qed.
Lemma lem4954420 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4954421 {B : Type'} (s : B -> Prop) : (term1537 B s) = (term1538 B s).
Proof. exact (MK_COMB (@lem4954420 B) (@lem4954419 B s)). Qed.
Lemma lem4954422 {B : Type'} (s : B -> Prop) : (term1521 B s) = (term1539 B s).
Proof. exact (MK_COMB (@lem4954417 B s) (@lem4954421 B s)). Qed.
Lemma lem4954423 {B : Type'} (s : B -> Prop) : ((term1520 B s) = (term1521 B s)) = ((term1517 B s) = (term1539 B s)).
Proof. exact (MK_COMB (@lem4954411 B s) (@lem4954422 B s)). Qed.
Lemma lem4954424 {B : Type'} (s : B -> Prop) : (term1517 B s) = (term1539 B s).
Proof. exact (EQ_MP (@lem4954423 B s) (@lem4954401 B s)). Qed.
Lemma lem4954570 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term554 A P Q) = (term555 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4954571 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term554 B P Q) = (term555 B P Q).
Proof. exact (@lem4954570 B P Q). Qed.
Lemma lem4954572 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1540 B s t) = (term1541 B s t).
Proof. exact (@lem4954571 B (term1542 B s t) (term1543 B s t)). Qed.
Lemma lem4954573 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term1544 B s t x) = (term1545 B s x t).
Proof. exact (eq_refl (term1544 B s t x)). Qed.
Lemma lem4954574 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4954575 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term1546 B s t x) = (term1547 B s x t).
Proof. exact (MK_COMB (@lem4954574) (@lem4954573 B s x t)). Qed.
Lemma lem4954576 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term1548 B s t x) = (term1549 B s x t).
Proof. exact (eq_refl (term1548 B s t x)). Qed.
Lemma lem4954577 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term1550 B s t x) = (term1496 B s x t).
Proof. exact (MK_COMB (@lem4954575 B s x t) (@lem4954576 B s x t)). Qed.
Lemma lem4954578 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1551 B s t) = (term1504 B s t).
Proof. exact (fun_ext (fun x : B => @lem4954577 B s x t)). Qed.
Lemma lem4954579 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4954580 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1540 B s t) = (term1505 B s t).
Proof. exact (MK_COMB (@lem4954579 B) (@lem4954578 B s t)). Qed.
Lemma lem4954581 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4954582 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1552 B s t) = (term1553 B s t).
Proof. exact (MK_COMB (@lem4954581) (@lem4954580 B s t)). Qed.
Lemma lem4954583 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term1544 B s t x) = (term1545 B s x t).
Proof. exact (eq_refl (term1544 B s t x)). Qed.
Lemma lem4954584 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1554 B s t) = (term1542 B s t).
Proof. exact (fun_ext (fun x : B => @lem4954583 B s x t)). Qed.
Lemma lem4954585 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4954586 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1555 B s t) = (term1556 B s t).
Proof. exact (MK_COMB (@lem4954585 B) (@lem4954584 B s t)). Qed.
Lemma lem4954587 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4954588 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1557 B s t) = (term1558 B s t).
Proof. exact (MK_COMB (@lem4954587) (@lem4954586 B s t)). Qed.
Lemma lem4954589 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term1548 B s t x) = (term1549 B s x t).
Proof. exact (eq_refl (term1548 B s t x)). Qed.
Lemma lem4954590 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1559 B s t) = (term1543 B s t).
Proof. exact (fun_ext (fun x : B => @lem4954589 B s x t)). Qed.
Lemma lem4954591 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4954592 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1560 B s t) = (term1561 B s t).
Proof. exact (MK_COMB (@lem4954591 B) (@lem4954590 B s t)). Qed.
Lemma lem4954593 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1541 B s t) = (term1562 B s t).
Proof. exact (MK_COMB (@lem4954588 B s t) (@lem4954592 B s t)). Qed.
Lemma lem4954594 {B : Type'} (s : B -> Prop) (t : B -> Prop) : ((term1540 B s t) = (term1541 B s t)) = ((term1505 B s t) = (term1562 B s t)).
Proof. exact (MK_COMB (@lem4954582 B s t) (@lem4954593 B s t)). Qed.
Lemma lem4954595 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1505 B s t) = (term1562 B s t).
Proof. exact (EQ_MP (@lem4954594 B s t) (@lem4954572 B s t)). Qed.
Lemma lem4954692 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1506 B s t) = (term1506 B s t).
Proof. exact (eq_refl (term1506 B s t)). Qed.
Lemma lem4954693 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1508 B s t) = (term1563 B s t).
Proof. exact (MK_COMB (@lem4954692 B s t) (@lem4954595 B s t)). Qed.
Lemma lem4954694 {B : Type'} (s : B -> Prop) : (term1523 B s) = (term1564 B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4954693 B s t)). Qed.
Lemma lem4954695 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4954696 {B : Type'} (s : B -> Prop) : (term1538 B s) = (term1565 B s).
Proof. exact (MK_COMB (@lem4954695 B) (@lem4954694 B s)). Qed.
Lemma lem4954745 {B : Type'} (s : B -> Prop) : (term1535 B s) = (term1535 B s).
Proof. exact (eq_refl (term1535 B s)). Qed.
Lemma lem4954746 {B : Type'} (s : B -> Prop) : (term1539 B s) = (term1566 B s).
Proof. exact (MK_COMB (@lem4954745 B s) (@lem4954696 B s)). Qed.
Lemma lem4954747 {B : Type'} (s : B -> Prop) : (term1517 B s) = (term1566 B s).
Proof. exact (TRANS (@lem4954424 B s) (@lem4954746 B s)). Qed.
Lemma lem4954748 {B : Type'} : (term1518 B) = (term1567 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem4954747 B s)). Qed.
Lemma lem4954749 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4954750 {B : Type'} : (term1519 B) = (term1568 B).
Proof. exact (MK_COMB (@lem4954749 B) (@lem4954748 B)). Qed.
Lemma lem4954752 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term554 A P Q) = (term555 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4954753 {B : Type'} (P : type686 B) (Q : type686 B) : (term580 B P Q) = (term581 B P Q).
Proof. exact (@lem4954752 (B -> Prop) P Q). Qed.
Lemma lem4954754 {B : Type'} : (term1569 B) = (term1570 B).
Proof. exact (@lem4954753 B (term1571 B) (term1572 B)). Qed.
Lemma lem4954755 {B : Type'} (s : B -> Prop) : (term1573 B s) = (term1533 B s).
Proof. exact (eq_refl (term1573 B s)). Qed.
Lemma lem4954756 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4954757 {B : Type'} (s : B -> Prop) : (term1574 B s) = (term1535 B s).
Proof. exact (MK_COMB (@lem4954756) (@lem4954755 B s)). Qed.
Lemma lem4954758 {B : Type'} (s : B -> Prop) : (term1575 B s) = (term1565 B s).
Proof. exact (eq_refl (term1575 B s)). Qed.
Lemma lem4954759 {B : Type'} (s : B -> Prop) : (term1576 B s) = (term1566 B s).
Proof. exact (MK_COMB (@lem4954757 B s) (@lem4954758 B s)). Qed.
Lemma lem4954760 {B : Type'} : (term1577 B) = (term1567 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem4954759 B s)). Qed.
Lemma lem4954761 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4954762 {B : Type'} : (term1569 B) = (term1568 B).
Proof. exact (MK_COMB (@lem4954761 B) (@lem4954760 B)). Qed.
Lemma lem4954763 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4954764 {B : Type'} : (term1578 B) = (term1579 B).
Proof. exact (MK_COMB (@lem4954763) (@lem4954762 B)). Qed.
Lemma lem4954765 {B : Type'} (s : B -> Prop) : (term1573 B s) = (term1533 B s).
Proof. exact (eq_refl (term1573 B s)). Qed.
Lemma lem4954766 {B : Type'} : (term1580 B) = (term1571 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem4954765 B s)). Qed.
Lemma lem4954767 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4954768 {B : Type'} : (term1581 B) = (term1582 B).
Proof. exact (MK_COMB (@lem4954767 B) (@lem4954766 B)). Qed.
Lemma lem4954769 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4954770 {B : Type'} : (term1583 B) = (term1584 B).
Proof. exact (MK_COMB (@lem4954769) (@lem4954768 B)). Qed.
Lemma lem4954771 {B : Type'} (s : B -> Prop) : (term1575 B s) = (term1565 B s).
Proof. exact (eq_refl (term1575 B s)). Qed.
Lemma lem4954772 {B : Type'} : (term1585 B) = (term1572 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem4954771 B s)). Qed.
Lemma lem4954773 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4954774 {B : Type'} : (term1586 B) = (term1587 B).
Proof. exact (MK_COMB (@lem4954773 B) (@lem4954772 B)). Qed.
Lemma lem4954775 {B : Type'} : (term1570 B) = (term1588 B).
Proof. exact (MK_COMB (@lem4954770 B) (@lem4954774 B)). Qed.
Lemma lem4954776 {B : Type'} : ((term1569 B) = (term1570 B)) = ((term1568 B) = (term1588 B)).
Proof. exact (MK_COMB (@lem4954764 B) (@lem4954775 B)). Qed.
Lemma lem4954777 {B : Type'} : (term1568 B) = (term1588 B).
Proof. exact (EQ_MP (@lem4954776 B) (@lem4954754 B)). Qed.
Lemma lem4955026 {B : Type'} : (term1519 B) = (term1588 B).
Proof. exact (TRANS (@lem4954750 B) (@lem4954777 B)). Qed.
Lemma lem4955028 {A : Type'} (P : Prop) (Q : A -> Prop) : (term270 A P Q) = (term271 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4955029 {B : Type'} (P : Prop) (Q : B -> Prop) : (term270 B P Q) = (term271 B P Q).
Proof. exact (@lem4955028 B P Q). Qed.
Lemma lem4955030 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1589 B s t) = (term1590 B s t).
Proof. exact (@lem4955029 B (s = t) (term1502 B s t)). Qed.
Lemma lem4955031 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term1591 B s t x) = (term1495 B s x t).
Proof. exact (eq_refl (term1591 B s t x)). Qed.
Lemma lem4955032 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1592 B s t) = (term1502 B s t).
Proof. exact (fun_ext (fun x : B => @lem4955031 B s x t)). Qed.
Lemma lem4955033 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4955034 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1593 B s t) = (term1503 B s t).
Proof. exact (MK_COMB (@lem4955033 B) (@lem4955032 B s t)). Qed.
Lemma lem4955035 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1509 B s t) = (term1509 B s t).
Proof. exact (eq_refl (term1509 B s t)). Qed.
Lemma lem4955036 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1589 B s t) = (term1511 B s t).
Proof. exact (MK_COMB (@lem4955035 B s t) (@lem4955034 B s t)). Qed.
Lemma lem4955037 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4955038 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1594 B s t) = (term1595 B s t).
Proof. exact (MK_COMB (@lem4955037) (@lem4955036 B s t)). Qed.
Lemma lem4955039 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term1591 B s t x) = (term1495 B s x t).
Proof. exact (eq_refl (term1591 B s t x)). Qed.
Lemma lem4955040 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1509 B s t) = (term1509 B s t).
Proof. exact (eq_refl (term1509 B s t)). Qed.
Lemma lem4955041 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term1596 B s t x) = (term1597 B s x t).
Proof. exact (MK_COMB (@lem4955040 B s t) (@lem4955039 B s x t)). Qed.
Lemma lem4955042 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1598 B s t) = (term1599 B s t).
Proof. exact (fun_ext (fun x : B => @lem4955041 B s x t)). Qed.
Lemma lem4955043 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4955044 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1590 B s t) = (term1600 B s t).
Proof. exact (MK_COMB (@lem4955043 B) (@lem4955042 B s t)). Qed.
Lemma lem4955045 {B : Type'} (s : B -> Prop) (t : B -> Prop) : ((term1589 B s t) = (term1590 B s t)) = ((term1511 B s t) = (term1600 B s t)).
Proof. exact (MK_COMB (@lem4955038 B s t) (@lem4955044 B s t)). Qed.
Lemma lem4955046 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1511 B s t) = (term1600 B s t).
Proof. exact (EQ_MP (@lem4955045 B s t) (@lem4955030 B s t)). Qed.
Lemma lem4955047 {B : Type'} (s : B -> Prop) : (term1522 B s) = (term1601 B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4955046 B s t)). Qed.
Lemma lem4955048 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4955049 {B : Type'} (s : B -> Prop) : (term1533 B s) = (term1602 B s).
Proof. exact (MK_COMB (@lem4955048 B) (@lem4955047 B s)). Qed.
Lemma lem4955051 {A B : Type'} (P : type1413 A B) : (term286 A B P) = (term287 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4955052 {B : Type'} (P : type672 B) : (term1603 B P) = (term1604 B P).
Proof. exact (@lem4955051 (B -> Prop) B P). Qed.
Lemma lem4955053 {B : Type'} (s : B -> Prop) : (term1605 B s) = (term1606 B s).
Proof. exact (@lem4955052 B (term1607 B s)). Qed.
Lemma lem4955054 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1608 B s t) = (term1599 B s t).
Proof. exact (eq_refl (term1608 B s t)). Qed.
Lemma lem4955055 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4955056 {B : Type'} (s : B -> Prop) (t : B -> Prop) (x : B) : (term1609 B s t x) = (term1610 B s t x).
Proof. exact (MK_COMB (@lem4955054 B s t) (@lem4955055 B x)). Qed.
Lemma lem4955057 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term1610 B s t x) = (term1597 B s x t).
Proof. exact (eq_refl (term1610 B s t x)). Qed.
Lemma lem4955058 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term1609 B s t x) = (term1597 B s x t).
Proof. exact (TRANS (@lem4955056 B s t x) (@lem4955057 B s x t)). Qed.
Lemma lem4955059 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1611 B s t) = (term1599 B s t).
Proof. exact (fun_ext (fun x : B => @lem4955058 B s x t)). Qed.
Lemma lem4955060 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4955061 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1612 B s t) = (term1600 B s t).
Proof. exact (MK_COMB (@lem4955060 B) (@lem4955059 B s t)). Qed.
Lemma lem4955062 {B : Type'} (s : B -> Prop) : (term1613 B s) = (term1601 B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4955061 B s t)). Qed.
Lemma lem4955063 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4955064 {B : Type'} (s : B -> Prop) : (term1605 B s) = (term1602 B s).
Proof. exact (MK_COMB (@lem4955063 B) (@lem4955062 B s)). Qed.
Lemma lem4955065 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4955066 {B : Type'} (s : B -> Prop) : (term1614 B s) = (term1615 B s).
Proof. exact (MK_COMB (@lem4955065) (@lem4955064 B s)). Qed.
Lemma lem4955067 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1608 B s t) = (term1599 B s t).
Proof. exact (eq_refl (term1608 B s t)). Qed.
Lemma lem4955068 {B : Type'} (x : type684 B) (t : B -> Prop) : (x t) = (x t).
Proof. exact (eq_refl (x t)). Qed.
Lemma lem4955069 {B : Type'} (s : B -> Prop) (x : type684 B) (t : B -> Prop) : (term1616 B s x t) = (term1617 B s x t).
Proof. exact (MK_COMB (@lem4955067 B s t) (@lem4955068 B x t)). Qed.
Lemma lem4955070 {B : Type'} (s : B -> Prop) (x : type684 B) (t : B -> Prop) : (term1617 B s x t) = (term1618 B s x t).
Proof. exact (eq_refl (term1617 B s x t)). Qed.
Lemma lem4955071 {B : Type'} (s : B -> Prop) (x : type684 B) (t : B -> Prop) : (term1616 B s x t) = (term1618 B s x t).
Proof. exact (TRANS (@lem4955069 B s x t) (@lem4955070 B s x t)). Qed.
Lemma lem4955072 {B : Type'} (s : B -> Prop) (x : type684 B) : (term1619 B s x) = (term1620 B s x).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4955071 B s x t)). Qed.
Lemma lem4955073 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4955074 {B : Type'} (s : B -> Prop) (x : type684 B) : (term1621 B s x) = (term1622 B s x).
Proof. exact (MK_COMB (@lem4955073 B) (@lem4955072 B s x)). Qed.
Lemma lem4955075 {B : Type'} (s : B -> Prop) : (term1623 B s) = (term1624 B s).
Proof. exact (fun_ext (fun x : type684 B => @lem4955074 B s x)). Qed.
Lemma lem4955076 {B : Type'} : (@ex ((B -> Prop) -> B)) = (@ex ((B -> Prop) -> B)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> B))). Qed.
Lemma lem4955077 {B : Type'} (s : B -> Prop) : (term1606 B s) = (term1625 B s).
Proof. exact (MK_COMB (@lem4955076 B) (@lem4955075 B s)). Qed.
Lemma lem4955078 {B : Type'} (s : B -> Prop) : ((term1605 B s) = (term1606 B s)) = ((term1602 B s) = (term1625 B s)).
Proof. exact (MK_COMB (@lem4955066 B s) (@lem4955077 B s)). Qed.
Lemma lem4955079 {B : Type'} (s : B -> Prop) : (term1602 B s) = (term1625 B s).
Proof. exact (EQ_MP (@lem4955078 B s) (@lem4955053 B s)). Qed.
Lemma lem4955080 {B : Type'} (s : B -> Prop) : (term1533 B s) = (term1625 B s).
Proof. exact (TRANS (@lem4955049 B s) (@lem4955079 B s)). Qed.
Lemma lem4955081 {B : Type'} : (term1571 B) = (term1626 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem4955080 B s)). Qed.
Lemma lem4955082 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4955083 {B : Type'} : (term1582 B) = (term1627 B).
Proof. exact (MK_COMB (@lem4955082 B) (@lem4955081 B)). Qed.
Lemma lem4955085 {A B : Type'} (P : type1413 A B) : (term286 A B P) = (term287 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4955086 {B : Type'} (P : type597 B) : (term1628 B P) = (term1629 B P).
Proof. exact (@lem4955085 (B -> Prop) (type684 B) P). Qed.
Lemma lem4955087 {B : Type'} : (term1630 B) = (term1631 B).
Proof. exact (@lem4955086 B (term1632 B)). Qed.
Lemma lem4955088 {B : Type'} (s : B -> Prop) : (term1633 B s) = (term1624 B s).
Proof. exact (eq_refl (term1633 B s)). Qed.
Lemma lem4955089 {B : Type'} (x : type684 B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4955090 {B : Type'} (s : B -> Prop) (x : type684 B) : (term1634 B s x) = (term1635 B s x).
Proof. exact (MK_COMB (@lem4955088 B s) (@lem4955089 B x)). Qed.
Lemma lem4955091 {B : Type'} (s : B -> Prop) (x : type684 B) : (term1635 B s x) = (term1622 B s x).
Proof. exact (eq_refl (term1635 B s x)). Qed.
Lemma lem4955092 {B : Type'} (s : B -> Prop) (x : type684 B) : (term1634 B s x) = (term1622 B s x).
Proof. exact (TRANS (@lem4955090 B s x) (@lem4955091 B s x)). Qed.
Lemma lem4955093 {B : Type'} (s : B -> Prop) : (term1636 B s) = (term1624 B s).
Proof. exact (fun_ext (fun x : type684 B => @lem4955092 B s x)). Qed.
Lemma lem4955094 {B : Type'} : (@ex ((B -> Prop) -> B)) = (@ex ((B -> Prop) -> B)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> B))). Qed.
Lemma lem4955095 {B : Type'} (s : B -> Prop) : (term1637 B s) = (term1625 B s).
Proof. exact (MK_COMB (@lem4955094 B) (@lem4955093 B s)). Qed.
Lemma lem4955096 {B : Type'} : (term1638 B) = (term1626 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem4955095 B s)). Qed.
Lemma lem4955097 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4955098 {B : Type'} : (term1630 B) = (term1627 B).
Proof. exact (MK_COMB (@lem4955097 B) (@lem4955096 B)). Qed.
Lemma lem4955099 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4955100 {B : Type'} : (term1639 B) = (term1640 B).
Proof. exact (MK_COMB (@lem4955099) (@lem4955098 B)). Qed.
Lemma lem4955101 {B : Type'} (s : B -> Prop) : (term1633 B s) = (term1624 B s).
Proof. exact (eq_refl (term1633 B s)). Qed.
Lemma lem4955102 {B : Type'} (x : type638 B) (s : B -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem4955103 {B : Type'} (x : type638 B) (s : B -> Prop) : (term1641 B x s) = (term1642 B x s).
Proof. exact (MK_COMB (@lem4955101 B s) (@lem4955102 B x s)). Qed.
Lemma lem4955104 {B : Type'} (x : type638 B) (s : B -> Prop) : (term1642 B x s) = (term1643 B x s).
Proof. exact (eq_refl (term1642 B x s)). Qed.
Lemma lem4955105 {B : Type'} (x : type638 B) (s : B -> Prop) : (term1641 B x s) = (term1643 B x s).
Proof. exact (TRANS (@lem4955103 B x s) (@lem4955104 B x s)). Qed.
Lemma lem4955106 {B : Type'} (x : type638 B) : (term1644 B x) = (term1645 B x).
Proof. exact (fun_ext (fun s : B -> Prop => @lem4955105 B x s)). Qed.
Lemma lem4955107 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4955108 {B : Type'} (x : type638 B) : (term1646 B x) = (term1647 B x).
Proof. exact (MK_COMB (@lem4955107 B) (@lem4955106 B x)). Qed.
Lemma lem4955109 {B : Type'} : (term1648 B) = (term1649 B).
Proof. exact (fun_ext (fun x : type638 B => @lem4955108 B x)). Qed.
Lemma lem4955110 {B : Type'} : (@ex ((B -> Prop) -> (B -> Prop) -> B)) = (@ex ((B -> Prop) -> (B -> Prop) -> B)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> (B -> Prop) -> B))). Qed.
Lemma lem4955111 {B : Type'} : (term1631 B) = (term1650 B).
Proof. exact (MK_COMB (@lem4955110 B) (@lem4955109 B)). Qed.
Lemma lem4955112 {B : Type'} : ((term1630 B) = (term1631 B)) = ((term1627 B) = (term1650 B)).
Proof. exact (MK_COMB (@lem4955100 B) (@lem4955111 B)). Qed.
Lemma lem4955113 {B : Type'} : (term1627 B) = (term1650 B).
Proof. exact (EQ_MP (@lem4955112 B) (@lem4955087 B)). Qed.
Lemma lem4955114 {B : Type'} : (term1582 B) = (term1650 B).
Proof. exact (TRANS (@lem4955083 B) (@lem4955113 B)). Qed.
Lemma lem4955115 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4955116 {B : Type'} : (term1584 B) = (term1651 B).
Proof. exact (MK_COMB (@lem4955115) (@lem4955114 B)). Qed.
Lemma lem4955117 {B : Type'} : (term1587 B) = (term1587 B).
Proof. exact (eq_refl (term1587 B)). Qed.
Lemma lem4955118 {B : Type'} : (term1588 B) = (term1652 B).
Proof. exact (MK_COMB (@lem4955116 B) (@lem4955117 B)). Qed.
Lemma lem4955120 {A : Type'} (P : A -> Prop) (Q : Prop) : (term313 A P Q) = (term314 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4955121 {B : Type'} (P : type139 B) (Q : Prop) : (term1653 B P Q) = (term1654 B P Q).
Proof. exact (@lem4955120 (type638 B) P Q). Qed.
Lemma lem4955122 {B : Type'} : (term1655 B) = (term1656 B).
Proof. exact (@lem4955121 B (term1649 B) (term1587 B)). Qed.
Lemma lem4955123 {B : Type'} (x : type638 B) : (term1657 B x) = (term1647 B x).
Proof. exact (eq_refl (term1657 B x)). Qed.
Lemma lem4955124 {B : Type'} : (term1658 B) = (term1649 B).
Proof. exact (fun_ext (fun x : type638 B => @lem4955123 B x)). Qed.
Lemma lem4955125 {B : Type'} : (@ex ((B -> Prop) -> (B -> Prop) -> B)) = (@ex ((B -> Prop) -> (B -> Prop) -> B)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> (B -> Prop) -> B))). Qed.
Lemma lem4955126 {B : Type'} : (term1659 B) = (term1650 B).
Proof. exact (MK_COMB (@lem4955125 B) (@lem4955124 B)). Qed.
Lemma lem4955127 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4955128 {B : Type'} : (term1660 B) = (term1651 B).
Proof. exact (MK_COMB (@lem4955127) (@lem4955126 B)). Qed.
Lemma lem4955129 {B : Type'} : (term1587 B) = (term1587 B).
Proof. exact (eq_refl (term1587 B)). Qed.
Lemma lem4955130 {B : Type'} : (term1655 B) = (term1652 B).
Proof. exact (MK_COMB (@lem4955128 B) (@lem4955129 B)). Qed.
Lemma lem4955131 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4955132 {B : Type'} : (term1661 B) = (term1662 B).
Proof. exact (MK_COMB (@lem4955131) (@lem4955130 B)). Qed.
Lemma lem4955133 {B : Type'} (x : type638 B) : (term1657 B x) = (term1647 B x).
Proof. exact (eq_refl (term1657 B x)). Qed.
Lemma lem4955134 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4955135 {B : Type'} (x : type638 B) : (term1663 B x) = (term1664 B x).
Proof. exact (MK_COMB (@lem4955134) (@lem4955133 B x)). Qed.
Lemma lem4955136 {B : Type'} : (term1587 B) = (term1587 B).
Proof. exact (eq_refl (term1587 B)). Qed.
Lemma lem4955137 {B : Type'} (x : type638 B) : (term1665 B x) = (term1666 B x).
Proof. exact (MK_COMB (@lem4955135 B x) (@lem4955136 B)). Qed.
Lemma lem4955138 {B : Type'} : (term1667 B) = (term1668 B).
Proof. exact (fun_ext (fun x : type638 B => @lem4955137 B x)). Qed.
Lemma lem4955139 {B : Type'} : (@ex ((B -> Prop) -> (B -> Prop) -> B)) = (@ex ((B -> Prop) -> (B -> Prop) -> B)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> (B -> Prop) -> B))). Qed.
Lemma lem4955140 {B : Type'} : (term1656 B) = (term1669 B).
Proof. exact (MK_COMB (@lem4955139 B) (@lem4955138 B)). Qed.
Lemma lem4955141 {B : Type'} : ((term1655 B) = (term1656 B)) = ((term1652 B) = (term1669 B)).
Proof. exact (MK_COMB (@lem4955132 B) (@lem4955140 B)). Qed.
Lemma lem4955142 {B : Type'} : (term1652 B) = (term1669 B).
Proof. exact (EQ_MP (@lem4955141 B) (@lem4955122 B)). Qed.
Lemma lem4955143 {B : Type'} : (term1588 B) = (term1669 B).
Proof. exact (TRANS (@lem4955118 B) (@lem4955142 B)). Qed.
Lemma lem4955144 {B : Type'} : (term1519 B) = (term1669 B).
Proof. exact (TRANS (@lem4955026 B) (@lem4955143 B)). Qed.
Lemma lem4955145 {B : Type'} : (term82 B) = (term1669 B).
Proof. exact (TRANS (@lem4954393 B) (@lem4955144 B)). Qed.
Lemma lem4955146 {B : Type'} (h1 : term82 B) : term1669 B.
Proof. exact (EQ_MP (@lem4955145 B) (@lem4947227 B h1)). Qed.
Lemma lem4955153 {A B : Type'} (x'''''' : type1448 A B) (h1 : term912 A B x'''''') : term912 A B x''''''.
Proof. exact (h1). Qed.
Lemma lem4955155 {A B : Type'} (x'''''''' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term527 A B x'''''''' s f) : term527 A B x'''''''' s f.
Proof. exact (h1). Qed.
Lemma lem4955156 {A B : Type'} (x'''''''' : B -> A) (y : B) (s : A -> Prop) (f : A -> B) (h1 : term525 A B x'''''''' y s f) : term525 A B x'''''''' y s f.
Proof. exact (h1). Qed.
Lemma lem4955157 {A B : Type'} (x'''''''' : B -> A) (y : B) (x''''''''' : A) (s : A -> Prop) (f : A -> B) (h1 : term523 A B x'''''''' y x''''''''' s f) : term523 A B x'''''''' y x''''''''' s f.
Proof. exact (h1). Qed.
Lemma lem4955158 {A B : Type'} (x'''''''' : B -> A) (y : B) (x''''''''' : A) (y' : A) (s : A -> Prop) (f : A -> B) (h1 : term521 A B x'''''''' y x''''''''' y' s f) : term521 A B x'''''''' y x''''''''' y' s f.
Proof. exact (h1). Qed.
Lemma lem4955159 {A B : Type'} (x'''''''' : B -> A) (y : B) (x''''''''' : A) (y' : A) (s : A -> Prop) (f : A -> B) (x'''''''''' : A) (h1 : term519 A B x'''''''' y x''''''''' y' s f x'''''''''') : term519 A B x'''''''' y x''''''''' y' s f x''''''''''.
Proof. exact (h1). Qed.
Lemma lem4955160 {A B : Type'} (x'''''''' : B -> A) (y : B) (x''''''''' : A) (y' : A) (s : A -> Prop) (f : A -> B) (x'''''''''' : A) (y'' : A) (h1 : term516 A B x'''''''' y x''''''''' y' s f x'''''''''' y'') : term516 A B x'''''''' y x''''''''' y' s f x'''''''''' y''.
Proof. exact (h1). Qed.
Lemma lem4956612 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem4956621 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4956622 {A B : Type'} (f : type1448 A B) (x : B) : (f x) = (@I (B -> (A -> Prop) -> (A -> B) -> A) f x).
Proof. exact (@lem4956621 B (type631 A B) f x). Qed.
Lemma lem4956623 {A B : Type'} (x'''''' : type1448 A B) (y : B) : (x'''''' y) = (@I (B -> (A -> Prop) -> (A -> B) -> A) x'''''' y).
Proof. exact (@lem4956622 A B x'''''' y). Qed.
Lemma lem4956624 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4956625 {A B : Type'} (x'''''' : type1448 A B) (y : B) (s : A -> Prop) : (x'''''' y s) = (@I (B -> (A -> Prop) -> (A -> B) -> A) x'''''' y s).
Proof. exact (MK_COMB (@lem4956623 A B x'''''' y) (@lem4956624 A s)). Qed.
Lemma lem4956627 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4956628 {A B : Type'} (f : type631 A B) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> B) -> A) f x).
Proof. exact (@lem4956627 (A -> Prop) (type569 A B) f x). Qed.
Lemma lem4956629 {A B : Type'} (x'''''' : type1448 A B) (y : B) (s : A -> Prop) : (@I (B -> (A -> Prop) -> (A -> B) -> A) x'''''' y s) = (term1670 A B x'''''' y s).
Proof. exact (@lem4956628 A B (@I (B -> (A -> Prop) -> (A -> B) -> A) x'''''' y) s). Qed.
Lemma lem4956630 {A B : Type'} (x'''''' : type1448 A B) (y : B) (s : A -> Prop) : (x'''''' y s) = (term1670 A B x'''''' y s).
Proof. exact (TRANS (@lem4956625 A B x'''''' y s) (@lem4956629 A B x'''''' y s)). Qed.
Lemma lem4956631 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4956632 {A B : Type'} (x'''''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) : (x'''''' y s f) = (term1671 A B x'''''' y s f).
Proof. exact (MK_COMB (@lem4956630 A B x'''''' y s) (@lem4956631 A B f)). Qed.
Lemma lem4956634 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4956635 {A B : Type'} (f : type569 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> A) f x).
Proof. exact (@lem4956634 (A -> B) A f x). Qed.
Lemma lem4956636 {A B : Type'} (x'''''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) : (term1671 A B x'''''' y s f) = (term1672 A B x'''''' y s f).
Proof. exact (@lem4956635 A B (term1670 A B x'''''' y s) f). Qed.
Lemma lem4956638 {A B : Type'} (x'''''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) : (x'''''' y s f) = (term1672 A B x'''''' y s f).
Proof. exact (TRANS (@lem4956632 A B x'''''' y s f) (@lem4956636 A B x'''''' y s f)). Qed.
Lemma lem4956639 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4956640 {A B : Type'} (x'''''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) : (term1673 A B x'''''' y s f) = (term1674 A B x'''''' y s f).
Proof. exact (MK_COMB (@lem4956612 A) (@lem4956638 A B x'''''' y s f)). Qed.
Lemma lem4956641 {A B : Type'} (x'''''' : type1448 A B) (y : B) (f : A -> B) (s : A -> Prop) : (term1675 A B x'''''' y f s) = (term1676 A B x'''''' y f s).
Proof. exact (MK_COMB (@lem4956640 A B x'''''' y s f) (@lem4956639 A s)). Qed.
Lemma lem4956643 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4956644 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4956643 A (type686 A) f x). Qed.
Lemma lem4956645 {A B : Type'} (x'''''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) : (term1674 A B x'''''' y s f) = (term1677 A B x'''''' y s f).
Proof. exact (@lem4956644 A (@IN A) (term1672 A B x'''''' y s f)). Qed.
Lemma lem4956646 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4956647 {A B : Type'} (x'''''' : type1448 A B) (y : B) (f : A -> B) (s : A -> Prop) : (term1676 A B x'''''' y f s) = (term1678 A B x'''''' y f s).
Proof. exact (MK_COMB (@lem4956645 A B x'''''' y s f) (@lem4956646 A s)). Qed.
Lemma lem4956649 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4956650 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4956649 (A -> Prop) Prop f x). Qed.
Lemma lem4956651 {A B : Type'} (x'''''' : type1448 A B) (y : B) (f : A -> B) (s : A -> Prop) : (term1678 A B x'''''' y f s) = (term1679 A B x'''''' y f s).
Proof. exact (@lem4956650 A (term1677 A B x'''''' y s f) s). Qed.
Lemma lem4956652 {A B : Type'} (x'''''' : type1448 A B) (y : B) (f : A -> B) (s : A -> Prop) : (term1676 A B x'''''' y f s) = (term1679 A B x'''''' y f s).
Proof. exact (TRANS (@lem4956647 A B x'''''' y f s) (@lem4956651 A B x'''''' y f s)). Qed.
Lemma lem4956653 {A B : Type'} (x'''''' : type1448 A B) (y : B) (f : A -> B) (s : A -> Prop) : (term1675 A B x'''''' y f s) = (term1679 A B x'''''' y f s).
Proof. exact (TRANS (@lem4956641 A B x'''''' y f s) (@lem4956652 A B x'''''' y f s)). Qed.
Lemma lem4956656 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4956665 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4956666 {A B : Type'} (f : type1448 A B) (x : B) : (f x) = (@I (B -> (A -> Prop) -> (A -> B) -> A) f x).
Proof. exact (@lem4956665 B (type631 A B) f x). Qed.
Lemma lem4956667 {A B : Type'} (x'''''' : type1448 A B) (y : B) : (x'''''' y) = (@I (B -> (A -> Prop) -> (A -> B) -> A) x'''''' y).
Proof. exact (@lem4956666 A B x'''''' y). Qed.
Lemma lem4956668 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4956669 {A B : Type'} (x'''''' : type1448 A B) (y : B) (s : A -> Prop) : (x'''''' y s) = (@I (B -> (A -> Prop) -> (A -> B) -> A) x'''''' y s).
Proof. exact (MK_COMB (@lem4956667 A B x'''''' y) (@lem4956668 A s)). Qed.
Lemma lem4956671 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4956672 {A B : Type'} (f : type631 A B) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> B) -> A) f x).
Proof. exact (@lem4956671 (A -> Prop) (type569 A B) f x). Qed.
Lemma lem4956673 {A B : Type'} (x'''''' : type1448 A B) (y : B) (s : A -> Prop) : (@I (B -> (A -> Prop) -> (A -> B) -> A) x'''''' y s) = (term1670 A B x'''''' y s).
Proof. exact (@lem4956672 A B (@I (B -> (A -> Prop) -> (A -> B) -> A) x'''''' y) s). Qed.
Lemma lem4956674 {A B : Type'} (x'''''' : type1448 A B) (y : B) (s : A -> Prop) : (x'''''' y s) = (term1670 A B x'''''' y s).
Proof. exact (TRANS (@lem4956669 A B x'''''' y s) (@lem4956673 A B x'''''' y s)). Qed.
Lemma lem4956675 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4956676 {A B : Type'} (x'''''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) : (x'''''' y s f) = (term1671 A B x'''''' y s f).
Proof. exact (MK_COMB (@lem4956674 A B x'''''' y s) (@lem4956675 A B f)). Qed.
Lemma lem4956678 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4956679 {A B : Type'} (f : type569 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> A) f x).
Proof. exact (@lem4956678 (A -> B) A f x). Qed.
Lemma lem4956680 {A B : Type'} (x'''''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) : (term1671 A B x'''''' y s f) = (term1672 A B x'''''' y s f).
Proof. exact (@lem4956679 A B (term1670 A B x'''''' y s) f). Qed.
Lemma lem4956682 {A B : Type'} (x'''''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) : (x'''''' y s f) = (term1672 A B x'''''' y s f).
Proof. exact (TRANS (@lem4956676 A B x'''''' y s f) (@lem4956680 A B x'''''' y s f)). Qed.
Lemma lem4956683 {A B : Type'} (x'''''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) : (term1680 A B x'''''' y s f) = (term1681 A B x'''''' y s f).
Proof. exact (MK_COMB (@lem4956656 A B f) (@lem4956682 A B x'''''' y s f)). Qed.
Lemma lem4956685 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4956686 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem4956685 A B f x). Qed.
Lemma lem4956687 {A B : Type'} (x'''''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) : (term1681 A B x'''''' y s f) = (term1682 A B x'''''' y s f).
Proof. exact (@lem4956686 A B f (term1672 A B x'''''' y s f)). Qed.
Lemma lem4956688 {A B : Type'} (x'''''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) : (term1680 A B x'''''' y s f) = (term1682 A B x'''''' y s f).
Proof. exact (TRANS (@lem4956683 A B x'''''' y s f) (@lem4956687 A B x'''''' y s f)). Qed.
Lemma lem4956689 {B : Type'} (y : B) : (@eq B y) = (@eq B y).
Proof. exact (eq_refl (@eq B y)). Qed.
Lemma lem4956690 {A B : Type'} (x'''''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) : (y = (term1680 A B x'''''' y s f)) = (y = (term1682 A B x'''''' y s f)).
Proof. exact (MK_COMB (@lem4956689 B y) (@lem4956688 A B x'''''' y s f)). Qed.
Lemma lem4956691 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4956692 {A B : Type'} (x'''''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) : (term1683 A B x'''''' y s f) = (term1684 A B x'''''' y s f).
Proof. exact (MK_COMB (@lem4956691) (@lem4956690 A B x'''''' y s f)). Qed.
Lemma lem4956693 {A B : Type'} (x'''''' : type1448 A B) (y : B) (f : A -> B) (s : A -> Prop) : (term1685 A B x'''''' y f s) = (term1686 A B x'''''' y f s).
Proof. exact (MK_COMB (@lem4956692 A B x'''''' y s f) (@lem4956653 A B x'''''' y f s)). Qed.
Lemma lem4956694 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4956703 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4956704 {A B : Type'} (f : type528 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) f x).
Proof. exact (@lem4956703 (A -> B) (type678 A B) f x). Qed.
Lemma lem4956705 {A B : Type'} (f : A -> B) : (@IMAGE A B f) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f).
Proof. exact (@lem4956704 A B (@IMAGE A B) f). Qed.
Lemma lem4956706 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4956707 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@IMAGE A B f s) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f s).
Proof. exact (MK_COMB (@lem4956705 A B f) (@lem4956706 A s)). Qed.
Lemma lem4956709 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4956710 {A B : Type'} (f : type678 A B) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> B -> Prop) f x).
Proof. exact (@lem4956709 (A -> Prop) (B -> Prop) f x). Qed.
Lemma lem4956711 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f s) = (term1687 A B f s).
Proof. exact (@lem4956710 A B (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f) s). Qed.
Lemma lem4956713 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@IMAGE A B f s) = (term1687 A B f s).
Proof. exact (TRANS (@lem4956707 A B f s) (@lem4956711 A B f s)). Qed.
Lemma lem4956714 {B : Type'} (y : B) : (@IN B y) = (@IN B y).
Proof. exact (eq_refl (@IN B y)). Qed.
Lemma lem4956715 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term58 A B y f s) = (term1688 A B y f s).
Proof. exact (MK_COMB (@lem4956714 B y) (@lem4956713 A B f s)). Qed.
Lemma lem4956717 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4956718 {B : Type'} (f : type1364 B) (x : B) : (f x) = (@I (B -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem4956717 B (type686 B) f x). Qed.
Lemma lem4956719 {B : Type'} (y : B) : (@IN B y) = (@I (B -> (B -> Prop) -> Prop) (@IN B) y).
Proof. exact (@lem4956718 B (@IN B) y). Qed.
Lemma lem4956720 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term1687 A B f s) = (term1687 A B f s).
Proof. exact (eq_refl (term1687 A B f s)). Qed.
Lemma lem4956721 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1688 A B y f s) = (term1689 A B y f s).
Proof. exact (MK_COMB (@lem4956719 B y) (@lem4956720 A B f s)). Qed.
Lemma lem4956723 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4956724 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem4956723 (B -> Prop) Prop f x). Qed.
Lemma lem4956725 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1689 A B y f s) = (term1690 A B y f s).
Proof. exact (@lem4956724 B (@I (B -> (B -> Prop) -> Prop) (@IN B) y) (term1687 A B f s)). Qed.
Lemma lem4956726 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1688 A B y f s) = (term1690 A B y f s).
Proof. exact (TRANS (@lem4956721 A B y f s) (@lem4956725 A B y f s)). Qed.
Lemma lem4956727 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term58 A B y f s) = (term1690 A B y f s).
Proof. exact (TRANS (@lem4956715 A B y f s) (@lem4956726 A B y f s)). Qed.
Lemma lem4956728 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term274 A B y f s) = (term1691 A B y f s).
Proof. exact (MK_COMB (@lem4956694) (@lem4956727 A B y f s)). Qed.
Lemma lem4956729 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4956730 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term209 A B y f s) = (term1692 A B y f s).
Proof. exact (MK_COMB (@lem4956729) (@lem4956728 A B y f s)). Qed.
Lemma lem4956731 {A B : Type'} (x'''''' : type1448 A B) (y : B) (f : A -> B) (s : A -> Prop) : (term1693 A B x'''''' y f s) = (term1694 A B x'''''' y f s).
Proof. exact (MK_COMB (@lem4956730 A B y f s) (@lem4956693 A B x'''''' y f s)). Qed.
Lemma lem4956732 {A B : Type'} (x'''''' : type1448 A B) (y : B) (s : A -> Prop) : (term1695 A B x'''''' y s) = (term1696 A B x'''''' y s).
Proof. exact (fun_ext (fun f : A -> B => @lem4956731 A B x'''''' y f s)). Qed.
Lemma lem4956733 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4956734 {A B : Type'} (x'''''' : type1448 A B) (y : B) (s : A -> Prop) : (term1697 A B x'''''' y s) = (term1698 A B x'''''' y s).
Proof. exact (MK_COMB (@lem4956733 A B) (@lem4956732 A B x'''''' y s)). Qed.
Lemma lem4956735 {A B : Type'} (x'''''' : type1448 A B) (y : B) : (term1699 A B x'''''' y) = (term1700 A B x'''''' y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4956734 A B x'''''' y s)). Qed.
Lemma lem4956736 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4956737 {A B : Type'} (x'''''' : type1448 A B) (y : B) : (term893 A B x'''''' y) = (term1701 A B x'''''' y).
Proof. exact (MK_COMB (@lem4956736 A) (@lem4956735 A B x'''''' y)). Qed.
Lemma lem4956738 {A B : Type'} (x'''''' : type1448 A B) : (term895 A B x'''''') = (term1702 A B x'''''').
Proof. exact (fun_ext (fun y : B => @lem4956737 A B x'''''' y)). Qed.
Lemma lem4956739 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4956740 {A B : Type'} (x'''''' : type1448 A B) : (term897 A B x'''''') = (term1703 A B x'''''').
Proof. exact (MK_COMB (@lem4956739 B) (@lem4956738 A B x'''''')). Qed.
Lemma lem4956741 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4956748 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4956749 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4956748 A (type686 A) f x). Qed.
Lemma lem4956750 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem4956749 A (@IN A) x). Qed.
Lemma lem4956751 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4956752 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x s).
Proof. exact (MK_COMB (@lem4956750 A x) (@lem4956751 A s)). Qed.
Lemma lem4956754 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4956755 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4956754 (A -> Prop) Prop f x). Qed.
Lemma lem4956756 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x s) = (term1704 A x s).
Proof. exact (@lem4956755 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) s). Qed.
Lemma lem4956758 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (term1704 A x s).
Proof. exact (TRANS (@lem4956752 A x s) (@lem4956756 A x s)). Qed.
Lemma lem4956759 {A : Type'} (x : A) (s : A -> Prop) : (term1705 A x s) = (term1706 A x s).
Proof. exact (MK_COMB (@lem4956741) (@lem4956758 A x s)). Qed.
Lemma lem4956760 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4956767 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4956769 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem4956767 A B f x). Qed.
Lemma lem4956770 {B : Type'} (y : B) : (@eq B y) = (@eq B y).
Proof. exact (eq_refl (@eq B y)). Qed.
Lemma lem4956771 {A B : Type'} (y : B) (f : A -> B) (x : A) : (y = (f x)) = (y = (@I (A -> B) f x)).
Proof. exact (MK_COMB (@lem4956770 B y) (@lem4956769 A B f x)). Qed.
Lemma lem4956772 {A B : Type'} (y : B) (f : A -> B) (x : A) : (term1707 A B y f x) = (term1708 A B y f x).
Proof. exact (MK_COMB (@lem4956760) (@lem4956771 A B y f x)). Qed.
Lemma lem4956773 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4956774 {A B : Type'} (y : B) (f : A -> B) (x : A) : (term1709 A B y f x) = (term1710 A B y f x).
Proof. exact (MK_COMB (@lem4956773) (@lem4956772 A B y f x)). Qed.
Lemma lem4956775 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term727 A B y f x s) = (term1711 A B y f x s).
Proof. exact (MK_COMB (@lem4956774 A B y f x) (@lem4956759 A x s)). Qed.
Lemma lem4956776 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term733 A B y f s) = (term1712 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem4956775 A B y f x s)). Qed.
Lemma lem4956777 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4956778 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term734 A B y f s) = (term1713 A B y f s).
Proof. exact (MK_COMB (@lem4956777 A) (@lem4956776 A B y f s)). Qed.
Lemma lem4956787 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4956788 {A B : Type'} (f : type528 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) f x).
Proof. exact (@lem4956787 (A -> B) (type678 A B) f x). Qed.
Lemma lem4956789 {A B : Type'} (f : A -> B) : (@IMAGE A B f) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f).
Proof. exact (@lem4956788 A B (@IMAGE A B) f). Qed.
Lemma lem4956790 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4956791 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@IMAGE A B f s) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f s).
Proof. exact (MK_COMB (@lem4956789 A B f) (@lem4956790 A s)). Qed.
Lemma lem4956793 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4956794 {A B : Type'} (f : type678 A B) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> B -> Prop) f x).
Proof. exact (@lem4956793 (A -> Prop) (B -> Prop) f x). Qed.
Lemma lem4956795 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f s) = (term1687 A B f s).
Proof. exact (@lem4956794 A B (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f) s). Qed.
Lemma lem4956797 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@IMAGE A B f s) = (term1687 A B f s).
Proof. exact (TRANS (@lem4956791 A B f s) (@lem4956795 A B f s)). Qed.
Lemma lem4956798 {B : Type'} (y : B) : (@IN B y) = (@IN B y).
Proof. exact (eq_refl (@IN B y)). Qed.
Lemma lem4956799 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term58 A B y f s) = (term1688 A B y f s).
Proof. exact (MK_COMB (@lem4956798 B y) (@lem4956797 A B f s)). Qed.
Lemma lem4956801 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4956802 {B : Type'} (f : type1364 B) (x : B) : (f x) = (@I (B -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem4956801 B (type686 B) f x). Qed.
Lemma lem4956803 {B : Type'} (y : B) : (@IN B y) = (@I (B -> (B -> Prop) -> Prop) (@IN B) y).
Proof. exact (@lem4956802 B (@IN B) y). Qed.
Lemma lem4956804 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term1687 A B f s) = (term1687 A B f s).
Proof. exact (eq_refl (term1687 A B f s)). Qed.
Lemma lem4956805 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1688 A B y f s) = (term1689 A B y f s).
Proof. exact (MK_COMB (@lem4956803 B y) (@lem4956804 A B f s)). Qed.
Lemma lem4956807 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4956808 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem4956807 (B -> Prop) Prop f x). Qed.
Lemma lem4956809 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1689 A B y f s) = (term1690 A B y f s).
Proof. exact (@lem4956808 B (@I (B -> (B -> Prop) -> Prop) (@IN B) y) (term1687 A B f s)). Qed.
Lemma lem4956810 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1688 A B y f s) = (term1690 A B y f s).
Proof. exact (TRANS (@lem4956805 A B y f s) (@lem4956809 A B y f s)). Qed.
Lemma lem4956811 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term58 A B y f s) = (term1690 A B y f s).
Proof. exact (TRANS (@lem4956799 A B y f s) (@lem4956810 A B y f s)). Qed.
Lemma lem4956812 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4956813 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term736 A B y f s) = (term1714 A B y f s).
Proof. exact (MK_COMB (@lem4956812) (@lem4956811 A B y f s)). Qed.
Lemma lem4956814 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term738 A B y f s) = (term1715 A B y f s).
Proof. exact (MK_COMB (@lem4956813 A B y f s) (@lem4956778 A B y f s)). Qed.
Lemma lem4956815 {A B : Type'} (y : B) (s : A -> Prop) : (term753 A B y s) = (term1716 A B y s).
Proof. exact (fun_ext (fun f : A -> B => @lem4956814 A B y f s)). Qed.
Lemma lem4956816 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4956817 {A B : Type'} (y : B) (s : A -> Prop) : (term764 A B y s) = (term1717 A B y s).
Proof. exact (MK_COMB (@lem4956816 A B) (@lem4956815 A B y s)). Qed.
Lemma lem4956818 {A B : Type'} (y : B) : (term775 A B y) = (term1718 A B y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4956817 A B y s)). Qed.
Lemma lem4956819 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4956820 {A B : Type'} (y : B) : (term786 A B y) = (term1719 A B y).
Proof. exact (MK_COMB (@lem4956819 A) (@lem4956818 A B y)). Qed.
Lemma lem4956821 {A B : Type'} : (term797 A B) = (term1720 A B).
Proof. exact (fun_ext (fun y : B => @lem4956820 A B y)). Qed.
Lemma lem4956822 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4956823 {A B : Type'} : (term808 A B) = (term1721 A B).
Proof. exact (MK_COMB (@lem4956822 B) (@lem4956821 A B)). Qed.
Lemma lem4956824 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4956825 {A B : Type'} : (term810 A B) = (term1722 A B).
Proof. exact (MK_COMB (@lem4956824) (@lem4956823 A B)). Qed.
Lemma lem4956826 {A B : Type'} (x'''''' : type1448 A B) : (term912 A B x'''''') = (term1723 A B x'''''').
Proof. exact (MK_COMB (@lem4956825 A B) (@lem4956740 A B x'''''')). Qed.
Lemma lem4956827 {A B : Type'} (x'''''' : type1448 A B) (h1 : term912 A B x'''''') : term1723 A B x''''''.
Proof. exact (EQ_MP (@lem4956826 A B x'''''') (@lem4955153 A B x'''''' h1)). Qed.
Lemma lem4957050 {A : Type'} (x'''''''''' : A) (y'' : A) : (term1724 A x'''''''''' y'') = (term1724 A x'''''''''' y'').
Proof. exact (eq_refl (term1724 A x'''''''''' y'')). Qed.
Lemma lem4957051 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4957056 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4957057 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem4957056 A B f x). Qed.
Lemma lem4957059 {A B : Type'} (f : A -> B) (x'''''''''' : A) : (f x'''''''''') = (@I (A -> B) f x'''''''''').
Proof. exact (@lem4957057 A B f x''''''''''). Qed.
Lemma lem4957064 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4957065 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem4957064 A B f x). Qed.
Lemma lem4957067 {A B : Type'} (f : A -> B) (y'' : A) : (f y'') = (@I (A -> B) f y'').
Proof. exact (@lem4957065 A B f y''). Qed.
Lemma lem4957068 {A B : Type'} (f : A -> B) (x'''''''''' : A) : (term1725 A B f x'''''''''') = (term1726 A B f x'''''''''').
Proof. exact (MK_COMB (@lem4957051 B) (@lem4957059 A B f x'''''''''')). Qed.
Lemma lem4957069 {A B : Type'} (x'''''''''' : A) (f : A -> B) (y'' : A) : ((f x'''''''''') = (f y'')) = ((@I (A -> B) f x'''''''''') = (@I (A -> B) f y'')).
Proof. exact (MK_COMB (@lem4957068 A B f x'''''''''') (@lem4957067 A B f y'')). Qed.
Lemma lem4957076 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4957077 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4957076 A (type686 A) f x). Qed.
Lemma lem4957078 {A : Type'} (y'' : A) : (@IN A y'') = (@I (A -> (A -> Prop) -> Prop) (@IN A) y'').
Proof. exact (@lem4957077 A (@IN A) y''). Qed.
Lemma lem4957079 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4957080 {A : Type'} (y'' : A) (s : A -> Prop) : (@IN A y'' s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) y'' s).
Proof. exact (MK_COMB (@lem4957078 A y'') (@lem4957079 A s)). Qed.
Lemma lem4957082 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4957083 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4957082 (A -> Prop) Prop f x). Qed.
Lemma lem4957084 {A : Type'} (y'' : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) y'' s) = (term1704 A y'' s).
Proof. exact (@lem4957083 A (@I (A -> (A -> Prop) -> Prop) (@IN A) y'') s). Qed.
Lemma lem4957086 {A : Type'} (y'' : A) (s : A -> Prop) : (@IN A y'' s) = (term1704 A y'' s).
Proof. exact (TRANS (@lem4957080 A y'' s) (@lem4957084 A y'' s)). Qed.
Lemma lem4957087 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4957088 {A : Type'} (y'' : A) (s : A -> Prop) : (term1727 A y'' s) = (term1728 A y'' s).
Proof. exact (MK_COMB (@lem4957087) (@lem4957086 A y'' s)). Qed.
Lemma lem4957089 {A B : Type'} (s : A -> Prop) (x'''''''''' : A) (f : A -> B) (y'' : A) : (term228 A B s x'''''''''' f y'') = (term1729 A B s x'''''''''' f y'').
Proof. exact (MK_COMB (@lem4957088 A y'' s) (@lem4957069 A B x'''''''''' f y'')). Qed.
Lemma lem4957096 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4957097 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4957096 A (type686 A) f x). Qed.
Lemma lem4957098 {A : Type'} (x'''''''''' : A) : (@IN A x'''''''''') = (@I (A -> (A -> Prop) -> Prop) (@IN A) x'''''''''').
Proof. exact (@lem4957097 A (@IN A) x''''''''''). Qed.
Lemma lem4957099 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4957100 {A : Type'} (x'''''''''' : A) (s : A -> Prop) : (@IN A x'''''''''' s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x'''''''''' s).
Proof. exact (MK_COMB (@lem4957098 A x'''''''''') (@lem4957099 A s)). Qed.
Lemma lem4957102 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4957103 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4957102 (A -> Prop) Prop f x). Qed.
Lemma lem4957104 {A : Type'} (x'''''''''' : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x'''''''''' s) = (term1704 A x'''''''''' s).
Proof. exact (@lem4957103 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x'''''''''') s). Qed.
Lemma lem4957106 {A : Type'} (x'''''''''' : A) (s : A -> Prop) : (@IN A x'''''''''' s) = (term1704 A x'''''''''' s).
Proof. exact (TRANS (@lem4957100 A x'''''''''' s) (@lem4957104 A x'''''''''' s)). Qed.
Lemma lem4957107 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4957108 {A : Type'} (x'''''''''' : A) (s : A -> Prop) : (term1727 A x'''''''''' s) = (term1728 A x'''''''''' s).
Proof. exact (MK_COMB (@lem4957107) (@lem4957106 A x'''''''''' s)). Qed.
Lemma lem4957109 {A B : Type'} (s : A -> Prop) (x'''''''''' : A) (f : A -> B) (y'' : A) : (term231 A B s x'''''''''' f y'') = (term1730 A B s x'''''''''' f y'').
Proof. exact (MK_COMB (@lem4957108 A x'''''''''' s) (@lem4957089 A B s x'''''''''' f y'')). Qed.
Lemma lem4957110 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4957111 {A B : Type'} (s : A -> Prop) (x'''''''''' : A) (f : A -> B) (y'' : A) : (term1731 A B s x'''''''''' f y'') = (term1732 A B s x'''''''''' f y'').
Proof. exact (MK_COMB (@lem4957110) (@lem4957109 A B s x'''''''''' f y'')). Qed.
Lemma lem4957112 {A B : Type'} (s : A -> Prop) (f : A -> B) (x'''''''''' : A) (y'' : A) : (term230 A B s f x'''''''''' y'') = (term1733 A B s f x'''''''''' y'').
Proof. exact (MK_COMB (@lem4957111 A B s x'''''''''' f y'') (@lem4957050 A x'''''''''' y'')). Qed.
Lemma lem4957119 {A : Type'} (x''''''''' : A) (y' : A) : (term1724 A x''''''''' y') = (term1724 A x''''''''' y').
Proof. exact (eq_refl (term1724 A x''''''''' y')). Qed.
Lemma lem4957120 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4957125 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4957126 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem4957125 A B f x). Qed.
Lemma lem4957128 {A B : Type'} (f : A -> B) (x''''''''' : A) : (f x''''''''') = (@I (A -> B) f x''''''''').
Proof. exact (@lem4957126 A B f x'''''''''). Qed.
Lemma lem4957133 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4957134 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem4957133 A B f x). Qed.
Lemma lem4957136 {A B : Type'} (f : A -> B) (y' : A) : (f y') = (@I (A -> B) f y').
Proof. exact (@lem4957134 A B f y'). Qed.
Lemma lem4957137 {A B : Type'} (f : A -> B) (x''''''''' : A) : (term1725 A B f x''''''''') = (term1726 A B f x''''''''').
Proof. exact (MK_COMB (@lem4957120 B) (@lem4957128 A B f x''''''''')). Qed.
Lemma lem4957138 {A B : Type'} (x''''''''' : A) (f : A -> B) (y' : A) : ((f x''''''''') = (f y')) = ((@I (A -> B) f x''''''''') = (@I (A -> B) f y')).
Proof. exact (MK_COMB (@lem4957137 A B f x''''''''') (@lem4957136 A B f y')). Qed.
Lemma lem4957145 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4957146 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4957145 A (type686 A) f x). Qed.
Lemma lem4957147 {A : Type'} (y' : A) : (@IN A y') = (@I (A -> (A -> Prop) -> Prop) (@IN A) y').
Proof. exact (@lem4957146 A (@IN A) y'). Qed.
Lemma lem4957148 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4957149 {A : Type'} (y' : A) (s : A -> Prop) : (@IN A y' s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) y' s).
Proof. exact (MK_COMB (@lem4957147 A y') (@lem4957148 A s)). Qed.
Lemma lem4957151 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4957152 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4957151 (A -> Prop) Prop f x). Qed.
Lemma lem4957153 {A : Type'} (y' : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) y' s) = (term1704 A y' s).
Proof. exact (@lem4957152 A (@I (A -> (A -> Prop) -> Prop) (@IN A) y') s). Qed.
Lemma lem4957155 {A : Type'} (y' : A) (s : A -> Prop) : (@IN A y' s) = (term1704 A y' s).
Proof. exact (TRANS (@lem4957149 A y' s) (@lem4957153 A y' s)). Qed.
Lemma lem4957156 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4957157 {A : Type'} (y' : A) (s : A -> Prop) : (term1727 A y' s) = (term1728 A y' s).
Proof. exact (MK_COMB (@lem4957156) (@lem4957155 A y' s)). Qed.
Lemma lem4957158 {A B : Type'} (s : A -> Prop) (x''''''''' : A) (f : A -> B) (y' : A) : (term228 A B s x''''''''' f y') = (term1729 A B s x''''''''' f y').
Proof. exact (MK_COMB (@lem4957157 A y' s) (@lem4957138 A B x''''''''' f y')). Qed.
Lemma lem4957165 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4957166 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4957165 A (type686 A) f x). Qed.
Lemma lem4957167 {A : Type'} (x''''''''' : A) : (@IN A x''''''''') = (@I (A -> (A -> Prop) -> Prop) (@IN A) x''''''''').
Proof. exact (@lem4957166 A (@IN A) x'''''''''). Qed.
Lemma lem4957168 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4957169 {A : Type'} (x''''''''' : A) (s : A -> Prop) : (@IN A x''''''''' s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x''''''''' s).
Proof. exact (MK_COMB (@lem4957167 A x''''''''') (@lem4957168 A s)). Qed.
Lemma lem4957171 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4957172 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4957171 (A -> Prop) Prop f x). Qed.
Lemma lem4957173 {A : Type'} (x''''''''' : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x''''''''' s) = (term1704 A x''''''''' s).
Proof. exact (@lem4957172 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x''''''''') s). Qed.
Lemma lem4957175 {A : Type'} (x''''''''' : A) (s : A -> Prop) : (@IN A x''''''''' s) = (term1704 A x''''''''' s).
Proof. exact (TRANS (@lem4957169 A x''''''''' s) (@lem4957173 A x''''''''' s)). Qed.
Lemma lem4957176 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4957177 {A : Type'} (x''''''''' : A) (s : A -> Prop) : (term1727 A x''''''''' s) = (term1728 A x''''''''' s).
Proof. exact (MK_COMB (@lem4957176) (@lem4957175 A x''''''''' s)). Qed.
Lemma lem4957178 {A B : Type'} (s : A -> Prop) (x''''''''' : A) (f : A -> B) (y' : A) : (term231 A B s x''''''''' f y') = (term1730 A B s x''''''''' f y').
Proof. exact (MK_COMB (@lem4957177 A x''''''''' s) (@lem4957158 A B s x''''''''' f y')). Qed.
Lemma lem4957179 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4957180 {A B : Type'} (s : A -> Prop) (x''''''''' : A) (f : A -> B) (y' : A) : (term1731 A B s x''''''''' f y') = (term1732 A B s x''''''''' f y').
Proof. exact (MK_COMB (@lem4957179) (@lem4957178 A B s x''''''''' f y')). Qed.
Lemma lem4957181 {A B : Type'} (s : A -> Prop) (f : A -> B) (x''''''''' : A) (y' : A) : (term230 A B s f x''''''''' y') = (term1733 A B s f x''''''''' y').
Proof. exact (MK_COMB (@lem4957180 A B s x''''''''' f y') (@lem4957119 A x''''''''' y')). Qed.
Lemma lem4957182 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4957183 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4957188 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4957190 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem4957188 A B f x). Qed.
Lemma lem4957191 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4957192 {A B : Type'} (f : A -> B) (x : A) : (term1725 A B f x) = (term1726 A B f x).
Proof. exact (MK_COMB (@lem4957183 B) (@lem4957190 A B f x)). Qed.
Lemma lem4957193 {A B : Type'} (f : A -> B) (x : A) (y : B) : ((f x) = y) = ((@I (A -> B) f x) = y).
Proof. exact (MK_COMB (@lem4957192 A B f x) (@lem4957191 B y)). Qed.
Lemma lem4957194 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term1734 A B f x y) = (term1735 A B f x y).
Proof. exact (MK_COMB (@lem4957182) (@lem4957193 A B f x y)). Qed.
Lemma lem4957195 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4957202 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4957203 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4957202 A (type686 A) f x). Qed.
Lemma lem4957204 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem4957203 A (@IN A) x). Qed.
Lemma lem4957205 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4957206 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x s).
Proof. exact (MK_COMB (@lem4957204 A x) (@lem4957205 A s)). Qed.
Lemma lem4957208 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4957209 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4957208 (A -> Prop) Prop f x). Qed.
Lemma lem4957210 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x s) = (term1704 A x s).
Proof. exact (@lem4957209 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) s). Qed.
Lemma lem4957212 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (term1704 A x s).
Proof. exact (TRANS (@lem4957206 A x s) (@lem4957210 A x s)). Qed.
Lemma lem4957213 {A : Type'} (x : A) (s : A -> Prop) : (term1705 A x s) = (term1706 A x s).
Proof. exact (MK_COMB (@lem4957195) (@lem4957212 A x s)). Qed.
Lemma lem4957214 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4957215 {A : Type'} (x : A) (s : A -> Prop) : (term224 A x s) = (term1736 A x s).
Proof. exact (MK_COMB (@lem4957214) (@lem4957213 A x s)). Qed.
Lemma lem4957216 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term195 A B s f x y) = (term1737 A B s f x y).
Proof. exact (MK_COMB (@lem4957215 A x s) (@lem4957194 A B f x y)). Qed.
Lemma lem4957217 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term203 A B s f y) = (term1738 A B s f y).
Proof. exact (fun_ext (fun x : A => @lem4957216 A B s f x y)). Qed.
Lemma lem4957218 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4957219 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term204 A B s f y) = (term1739 A B s f y).
Proof. exact (MK_COMB (@lem4957218 A) (@lem4957217 A B s f y)). Qed.
Lemma lem4957228 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4957229 {A B : Type'} (f : type528 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) f x).
Proof. exact (@lem4957228 (A -> B) (type678 A B) f x). Qed.
Lemma lem4957230 {A B : Type'} (f : A -> B) : (@IMAGE A B f) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f).
Proof. exact (@lem4957229 A B (@IMAGE A B) f). Qed.
Lemma lem4957231 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4957232 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@IMAGE A B f s) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f s).
Proof. exact (MK_COMB (@lem4957230 A B f) (@lem4957231 A s)). Qed.
Lemma lem4957234 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4957235 {A B : Type'} (f : type678 A B) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> B -> Prop) f x).
Proof. exact (@lem4957234 (A -> Prop) (B -> Prop) f x). Qed.
Lemma lem4957236 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f s) = (term1687 A B f s).
Proof. exact (@lem4957235 A B (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f) s). Qed.
Lemma lem4957238 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@IMAGE A B f s) = (term1687 A B f s).
Proof. exact (TRANS (@lem4957232 A B f s) (@lem4957236 A B f s)). Qed.
Lemma lem4957239 {B : Type'} (y : B) : (@IN B y) = (@IN B y).
Proof. exact (eq_refl (@IN B y)). Qed.
Lemma lem4957240 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term58 A B y f s) = (term1688 A B y f s).
Proof. exact (MK_COMB (@lem4957239 B y) (@lem4957238 A B f s)). Qed.
Lemma lem4957242 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4957243 {B : Type'} (f : type1364 B) (x : B) : (f x) = (@I (B -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem4957242 B (type686 B) f x). Qed.
Lemma lem4957244 {B : Type'} (y : B) : (@IN B y) = (@I (B -> (B -> Prop) -> Prop) (@IN B) y).
Proof. exact (@lem4957243 B (@IN B) y). Qed.
Lemma lem4957245 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term1687 A B f s) = (term1687 A B f s).
Proof. exact (eq_refl (term1687 A B f s)). Qed.
Lemma lem4957246 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1688 A B y f s) = (term1689 A B y f s).
Proof. exact (MK_COMB (@lem4957244 B y) (@lem4957245 A B f s)). Qed.
Lemma lem4957248 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4957249 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem4957248 (B -> Prop) Prop f x). Qed.
Lemma lem4957250 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1689 A B y f s) = (term1690 A B y f s).
Proof. exact (@lem4957249 B (@I (B -> (B -> Prop) -> Prop) (@IN B) y) (term1687 A B f s)). Qed.
Lemma lem4957251 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1688 A B y f s) = (term1690 A B y f s).
Proof. exact (TRANS (@lem4957246 A B y f s) (@lem4957250 A B y f s)). Qed.
Lemma lem4957252 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term58 A B y f s) = (term1690 A B y f s).
Proof. exact (TRANS (@lem4957240 A B y f s) (@lem4957251 A B y f s)). Qed.
Lemma lem4957253 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4957254 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term205 A B y f s) = (term1740 A B y f s).
Proof. exact (MK_COMB (@lem4957253) (@lem4957252 A B y f s)). Qed.
Lemma lem4957255 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term207 A B s f y) = (term1741 A B s f y).
Proof. exact (MK_COMB (@lem4957254 A B y f s) (@lem4957219 A B s f y)). Qed.
Lemma lem4957256 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4957257 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term342 A B s f y) = (term1742 A B s f y).
Proof. exact (MK_COMB (@lem4957256) (@lem4957255 A B s f y)). Qed.
Lemma lem4957258 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) (x''''''''' : A) (y' : A) : (term370 A B y s f x''''''''' y') = (term1743 A B y s f x''''''''' y').
Proof. exact (MK_COMB (@lem4957257 A B s f y) (@lem4957181 A B s f x''''''''' y')). Qed.
Lemma lem4957263 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4957264 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4957265 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4957270 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4957272 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem4957270 A B f x). Qed.
Lemma lem4957277 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4957278 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem4957277 A B f x). Qed.
Lemma lem4957280 {A B : Type'} (f : A -> B) (y : A) : (f y) = (@I (A -> B) f y).
Proof. exact (@lem4957278 A B f y). Qed.
Lemma lem4957281 {A B : Type'} (f : A -> B) (x : A) : (term1725 A B f x) = (term1726 A B f x).
Proof. exact (MK_COMB (@lem4957265 B) (@lem4957272 A B f x)). Qed.
Lemma lem4957282 {A B : Type'} (x : A) (f : A -> B) (y : A) : ((f x) = (f y)) = ((@I (A -> B) f x) = (@I (A -> B) f y)).
Proof. exact (MK_COMB (@lem4957281 A B f x) (@lem4957280 A B f y)). Qed.
Lemma lem4957283 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term1744 A B x f y) = (term1745 A B x f y).
Proof. exact (MK_COMB (@lem4957264) (@lem4957282 A B x f y)). Qed.
Lemma lem4957284 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4957291 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4957292 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4957291 A (type686 A) f x). Qed.
Lemma lem4957293 {A : Type'} (y : A) : (@IN A y) = (@I (A -> (A -> Prop) -> Prop) (@IN A) y).
Proof. exact (@lem4957292 A (@IN A) y). Qed.
Lemma lem4957294 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4957295 {A : Type'} (y : A) (s : A -> Prop) : (@IN A y s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) y s).
Proof. exact (MK_COMB (@lem4957293 A y) (@lem4957294 A s)). Qed.
Lemma lem4957297 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4957298 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4957297 (A -> Prop) Prop f x). Qed.
Lemma lem4957299 {A : Type'} (y : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) y s) = (term1704 A y s).
Proof. exact (@lem4957298 A (@I (A -> (A -> Prop) -> Prop) (@IN A) y) s). Qed.
Lemma lem4957301 {A : Type'} (y : A) (s : A -> Prop) : (@IN A y s) = (term1704 A y s).
Proof. exact (TRANS (@lem4957295 A y s) (@lem4957299 A y s)). Qed.
Lemma lem4957302 {A : Type'} (y : A) (s : A -> Prop) : (term1705 A y s) = (term1706 A y s).
Proof. exact (MK_COMB (@lem4957284) (@lem4957301 A y s)). Qed.
Lemma lem4957303 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4957304 {A : Type'} (y : A) (s : A -> Prop) : (term224 A y s) = (term1736 A y s).
Proof. exact (MK_COMB (@lem4957303) (@lem4957302 A y s)). Qed.
Lemma lem4957305 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term223 A B s x f y) = (term1746 A B s x f y).
Proof. exact (MK_COMB (@lem4957304 A y s) (@lem4957283 A B x f y)). Qed.
Lemma lem4957306 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4957313 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4957314 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4957313 A (type686 A) f x). Qed.
Lemma lem4957315 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem4957314 A (@IN A) x). Qed.
Lemma lem4957316 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4957317 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x s).
Proof. exact (MK_COMB (@lem4957315 A x) (@lem4957316 A s)). Qed.
Lemma lem4957319 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4957320 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4957319 (A -> Prop) Prop f x). Qed.
Lemma lem4957321 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x s) = (term1704 A x s).
Proof. exact (@lem4957320 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) s). Qed.
Lemma lem4957323 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (term1704 A x s).
Proof. exact (TRANS (@lem4957317 A x s) (@lem4957321 A x s)). Qed.
Lemma lem4957324 {A : Type'} (x : A) (s : A -> Prop) : (term1705 A x s) = (term1706 A x s).
Proof. exact (MK_COMB (@lem4957306) (@lem4957323 A x s)). Qed.
Lemma lem4957325 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4957326 {A : Type'} (x : A) (s : A -> Prop) : (term224 A x s) = (term1736 A x s).
Proof. exact (MK_COMB (@lem4957325) (@lem4957324 A x s)). Qed.
Lemma lem4957327 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term226 A B s x f y) = (term1747 A B s x f y).
Proof. exact (MK_COMB (@lem4957326 A x s) (@lem4957305 A B s x f y)). Qed.
Lemma lem4957328 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4957329 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term233 A B s x f y) = (term1748 A B s x f y).
Proof. exact (MK_COMB (@lem4957328) (@lem4957327 A B s x f y)). Qed.
Lemma lem4957330 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term235 A B s f x y) = (term1749 A B s f x y).
Proof. exact (MK_COMB (@lem4957329 A B s x f y) (@lem4957263 A x y)). Qed.
Lemma lem4957331 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term243 A B s f x) = (term1750 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem4957330 A B s f x y)). Qed.
Lemma lem4957332 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4957333 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term244 A B s f x) = (term1751 A B s f x).
Proof. exact (MK_COMB (@lem4957332 A) (@lem4957331 A B s f x)). Qed.
Lemma lem4957334 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term252 A B s f) = (term1752 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4957333 A B s f x)). Qed.
Lemma lem4957335 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4957336 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term253 A B s f) = (term1753 A B s f).
Proof. exact (MK_COMB (@lem4957335 A) (@lem4957334 A B s f)). Qed.
Lemma lem4957337 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4957338 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4957343 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4957344 {A B : Type'} (f : B -> A) (x : B) : (f x) = (@I (B -> A) f x).
Proof. exact (@lem4957343 B A f x). Qed.
Lemma lem4957346 {A B : Type'} (x'''''''' : B -> A) (y : B) : (x'''''''' y) = (@I (B -> A) x'''''''' y).
Proof. exact (@lem4957344 A B x'''''''' y). Qed.
Lemma lem4957347 {A B : Type'} (f : A -> B) (x'''''''' : B -> A) (y : B) : (term1754 A B f x'''''''' y) = (term1755 A B f x'''''''' y).
Proof. exact (MK_COMB (@lem4957338 A B f) (@lem4957346 A B x'''''''' y)). Qed.
Lemma lem4957349 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4957350 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem4957349 A B f x). Qed.
Lemma lem4957351 {A B : Type'} (f : A -> B) (x'''''''' : B -> A) (y : B) : (term1755 A B f x'''''''' y) = (term1756 A B f x'''''''' y).
Proof. exact (@lem4957350 A B f (@I (B -> A) x'''''''' y)). Qed.
Lemma lem4957352 {A B : Type'} (f : A -> B) (x'''''''' : B -> A) (y : B) : (term1754 A B f x'''''''' y) = (term1756 A B f x'''''''' y).
Proof. exact (TRANS (@lem4957347 A B f x'''''''' y) (@lem4957351 A B f x'''''''' y)). Qed.
Lemma lem4957353 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4957354 {A B : Type'} (f : A -> B) (x'''''''' : B -> A) (y : B) : (term1757 A B f x'''''''' y) = (term1758 A B f x'''''''' y).
Proof. exact (MK_COMB (@lem4957337 B) (@lem4957352 A B f x'''''''' y)). Qed.
Lemma lem4957355 {A B : Type'} (f : A -> B) (x'''''''' : B -> A) (y : B) : ((term1754 A B f x'''''''' y) = y) = ((term1756 A B f x'''''''' y) = y).
Proof. exact (MK_COMB (@lem4957354 A B f x'''''''' y) (@lem4957353 B y)). Qed.
Lemma lem4957356 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem4957361 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4957362 {A B : Type'} (f : B -> A) (x : B) : (f x) = (@I (B -> A) f x).
Proof. exact (@lem4957361 B A f x). Qed.
Lemma lem4957364 {A B : Type'} (x'''''''' : B -> A) (y : B) : (x'''''''' y) = (@I (B -> A) x'''''''' y).
Proof. exact (@lem4957362 A B x'''''''' y). Qed.
Lemma lem4957365 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4957366 {A B : Type'} (x'''''''' : B -> A) (y : B) : (term1759 A B x'''''''' y) = (term1760 A B x'''''''' y).
Proof. exact (MK_COMB (@lem4957356 A) (@lem4957364 A B x'''''''' y)). Qed.
Lemma lem4957367 {A B : Type'} (x'''''''' : B -> A) (y : B) (s : A -> Prop) : (term1761 A B x'''''''' y s) = (term1762 A B x'''''''' y s).
Proof. exact (MK_COMB (@lem4957366 A B x'''''''' y) (@lem4957365 A s)). Qed.
Lemma lem4957369 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4957370 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4957369 A (type686 A) f x). Qed.
Lemma lem4957371 {A B : Type'} (x'''''''' : B -> A) (y : B) : (term1760 A B x'''''''' y) = (term1763 A B x'''''''' y).
Proof. exact (@lem4957370 A (@IN A) (@I (B -> A) x'''''''' y)). Qed.
Lemma lem4957372 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4957373 {A B : Type'} (x'''''''' : B -> A) (y : B) (s : A -> Prop) : (term1762 A B x'''''''' y s) = (term1764 A B x'''''''' y s).
Proof. exact (MK_COMB (@lem4957371 A B x'''''''' y) (@lem4957372 A s)). Qed.
Lemma lem4957375 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4957376 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4957375 (A -> Prop) Prop f x). Qed.
Lemma lem4957377 {A B : Type'} (x'''''''' : B -> A) (y : B) (s : A -> Prop) : (term1764 A B x'''''''' y s) = (term1765 A B x'''''''' y s).
Proof. exact (@lem4957376 A (term1763 A B x'''''''' y) s). Qed.
Lemma lem4957378 {A B : Type'} (x'''''''' : B -> A) (y : B) (s : A -> Prop) : (term1762 A B x'''''''' y s) = (term1765 A B x'''''''' y s).
Proof. exact (TRANS (@lem4957373 A B x'''''''' y s) (@lem4957377 A B x'''''''' y s)). Qed.
Lemma lem4957379 {A B : Type'} (x'''''''' : B -> A) (y : B) (s : A -> Prop) : (term1761 A B x'''''''' y s) = (term1765 A B x'''''''' y s).
Proof. exact (TRANS (@lem4957367 A B x'''''''' y s) (@lem4957378 A B x'''''''' y s)). Qed.
Lemma lem4957380 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4957381 {A B : Type'} (x'''''''' : B -> A) (y : B) (s : A -> Prop) : (term1766 A B x'''''''' y s) = (term1767 A B x'''''''' y s).
Proof. exact (MK_COMB (@lem4957380) (@lem4957379 A B x'''''''' y s)). Qed.
Lemma lem4957382 {A B : Type'} (s : A -> Prop) (f : A -> B) (x'''''''' : B -> A) (y : B) : (term1768 A B s f x'''''''' y) = (term1769 A B s f x'''''''' y).
Proof. exact (MK_COMB (@lem4957381 A B x'''''''' y s) (@lem4957355 A B f x'''''''' y)). Qed.
Lemma lem4957383 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4957392 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4957393 {A B : Type'} (f : type528 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) f x).
Proof. exact (@lem4957392 (A -> B) (type678 A B) f x). Qed.
Lemma lem4957394 {A B : Type'} (f : A -> B) : (@IMAGE A B f) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f).
Proof. exact (@lem4957393 A B (@IMAGE A B) f). Qed.
Lemma lem4957395 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4957396 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@IMAGE A B f s) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f s).
Proof. exact (MK_COMB (@lem4957394 A B f) (@lem4957395 A s)). Qed.
Lemma lem4957398 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4957399 {A B : Type'} (f : type678 A B) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> B -> Prop) f x).
Proof. exact (@lem4957398 (A -> Prop) (B -> Prop) f x). Qed.
Lemma lem4957400 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f s) = (term1687 A B f s).
Proof. exact (@lem4957399 A B (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f) s). Qed.
Lemma lem4957402 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@IMAGE A B f s) = (term1687 A B f s).
Proof. exact (TRANS (@lem4957396 A B f s) (@lem4957400 A B f s)). Qed.
Lemma lem4957403 {B : Type'} (y : B) : (@IN B y) = (@IN B y).
Proof. exact (eq_refl (@IN B y)). Qed.
Lemma lem4957404 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term58 A B y f s) = (term1688 A B y f s).
Proof. exact (MK_COMB (@lem4957403 B y) (@lem4957402 A B f s)). Qed.
Lemma lem4957406 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4957407 {B : Type'} (f : type1364 B) (x : B) : (f x) = (@I (B -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem4957406 B (type686 B) f x). Qed.
Lemma lem4957408 {B : Type'} (y : B) : (@IN B y) = (@I (B -> (B -> Prop) -> Prop) (@IN B) y).
Proof. exact (@lem4957407 B (@IN B) y). Qed.
Lemma lem4957409 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term1687 A B f s) = (term1687 A B f s).
Proof. exact (eq_refl (term1687 A B f s)). Qed.
Lemma lem4957410 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1688 A B y f s) = (term1689 A B y f s).
Proof. exact (MK_COMB (@lem4957408 B y) (@lem4957409 A B f s)). Qed.
Lemma lem4957412 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4957413 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem4957412 (B -> Prop) Prop f x). Qed.
Lemma lem4957414 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1689 A B y f s) = (term1690 A B y f s).
Proof. exact (@lem4957413 B (@I (B -> (B -> Prop) -> Prop) (@IN B) y) (term1687 A B f s)). Qed.
Lemma lem4957415 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1688 A B y f s) = (term1690 A B y f s).
Proof. exact (TRANS (@lem4957410 A B y f s) (@lem4957414 A B y f s)). Qed.
Lemma lem4957416 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term58 A B y f s) = (term1690 A B y f s).
Proof. exact (TRANS (@lem4957404 A B y f s) (@lem4957415 A B y f s)). Qed.
Lemma lem4957417 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term274 A B y f s) = (term1691 A B y f s).
Proof. exact (MK_COMB (@lem4957383) (@lem4957416 A B y f s)). Qed.
Lemma lem4957418 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4957419 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term209 A B y f s) = (term1692 A B y f s).
Proof. exact (MK_COMB (@lem4957418) (@lem4957417 A B y f s)). Qed.
Lemma lem4957420 {A B : Type'} (s : A -> Prop) (f : A -> B) (x'''''''' : B -> A) (y : B) : (term303 A B s f x'''''''' y) = (term1770 A B s f x'''''''' y).
Proof. exact (MK_COMB (@lem4957419 A B y f s) (@lem4957382 A B s f x'''''''' y)). Qed.
Lemma lem4957421 {A B : Type'} (s : A -> Prop) (f : A -> B) (x'''''''' : B -> A) : (term305 A B s f x'''''''') = (term1771 A B s f x'''''''').
Proof. exact (fun_ext (fun y : B => @lem4957420 A B s f x'''''''' y)). Qed.
Lemma lem4957422 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4957423 {A B : Type'} (s : A -> Prop) (f : A -> B) (x'''''''' : B -> A) : (term307 A B s f x'''''''') = (term1772 A B s f x'''''''').
Proof. exact (MK_COMB (@lem4957422 B) (@lem4957421 A B s f x'''''''')). Qed.
Lemma lem4957424 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4957425 {A B : Type'} (s : A -> Prop) (f : A -> B) (x'''''''' : B -> A) : (term326 A B s f x'''''''') = (term1773 A B s f x'''''''').
Proof. exact (MK_COMB (@lem4957424) (@lem4957423 A B s f x'''''''')). Qed.
Lemma lem4957426 {A B : Type'} (x'''''''' : B -> A) (s : A -> Prop) (f : A -> B) : (term328 A B x'''''''' s f) = (term1774 A B x'''''''' s f).
Proof. exact (MK_COMB (@lem4957425 A B s f x'''''''') (@lem4957336 A B s f)). Qed.
Lemma lem4957427 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4957428 {A B : Type'} (x'''''''' : B -> A) (s : A -> Prop) (f : A -> B) : (term392 A B x'''''''' s f) = (term1775 A B x'''''''' s f).
Proof. exact (MK_COMB (@lem4957427) (@lem4957426 A B x'''''''' s f)). Qed.
Lemma lem4957429 {A B : Type'} (x'''''''' : B -> A) (y : B) (s : A -> Prop) (f : A -> B) (x''''''''' : A) (y' : A) : (term430 A B x'''''''' y s f x''''''''' y') = (term1776 A B x'''''''' y s f x''''''''' y').
Proof. exact (MK_COMB (@lem4957428 A B x'''''''' s f) (@lem4957258 A B y s f x''''''''' y')). Qed.
Lemma lem4957430 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4957431 {A B : Type'} (x'''''''' : B -> A) (y : B) (s : A -> Prop) (f : A -> B) (x''''''''' : A) (y' : A) : (term496 A B x'''''''' y s f x''''''''' y') = (term1777 A B x'''''''' y s f x''''''''' y').
Proof. exact (MK_COMB (@lem4957430) (@lem4957429 A B x'''''''' y s f x''''''''' y')). Qed.
Lemma lem4957432 {A B : Type'} (x'''''''' : B -> A) (y : B) (x''''''''' : A) (y' : A) (s : A -> Prop) (f : A -> B) (x'''''''''' : A) (y'' : A) : (term516 A B x'''''''' y x''''''''' y' s f x'''''''''' y'') = (term1778 A B x'''''''' y x''''''''' y' s f x'''''''''' y'').
Proof. exact (MK_COMB (@lem4957431 A B x'''''''' y s f x''''''''' y') (@lem4957112 A B s f x'''''''''' y'')). Qed.
Lemma lem4957433 {A B : Type'} (x'''''''' : B -> A) (y : B) (x''''''''' : A) (y' : A) (s : A -> Prop) (f : A -> B) (x'''''''''' : A) (y'' : A) (h1 : term516 A B x'''''''' y x''''''''' y' s f x'''''''''' y'') : term1778 A B x'''''''' y x''''''''' y' s f x'''''''''' y''.
Proof. exact (EQ_MP (@lem4957432 A B x'''''''' y x''''''''' y' s f x'''''''''' y'') (@lem4955160 A B x'''''''' y x''''''''' y' s f x'''''''''' y'' h1)). Qed.
Lemma lem4957434 {A B : Type'} (x'''''''' : B -> A) (y : B) (x''''''''' : A) (y' : A) (s : A -> Prop) (f : A -> B) (x'''''''''' : A) (y'' : A) (h1 : term516 A B x'''''''' y x''''''''' y' s f x'''''''''' y'') : term1733 A B s f x'''''''''' y''.
Proof. exact (proj2 (@lem4957433 A B x'''''''' y x''''''''' y' s f x'''''''''' y'' h1)). Qed.
Lemma lem4957435 {A B : Type'} (x'''''''' : B -> A) (y : B) (x''''''''' : A) (y' : A) (s : A -> Prop) (f : A -> B) (x'''''''''' : A) (y'' : A) (h1 : term516 A B x'''''''' y x''''''''' y' s f x'''''''''' y'') : term1776 A B x'''''''' y s f x''''''''' y'.
Proof. exact (proj1 (@lem4957433 A B x'''''''' y x''''''''' y' s f x'''''''''' y'' h1)). Qed.
Lemma lem4957437 {A B : Type'} (x'''''''' : B -> A) (y : B) (x''''''''' : A) (y' : A) (s : A -> Prop) (f : A -> B) (x'''''''''' : A) (y'' : A) (h1 : term516 A B x'''''''' y x''''''''' y' s f x'''''''''' y'') : term1730 A B s x'''''''''' f y''.
Proof. exact (proj1 (@lem4957434 A B x'''''''' y x''''''''' y' s f x'''''''''' y'' h1)). Qed.
Lemma lem4957438 {A B : Type'} (x'''''''' : B -> A) (y : B) (x''''''''' : A) (y' : A) (s : A -> Prop) (f : A -> B) (x'''''''''' : A) (y'' : A) (h1 : term516 A B x'''''''' y x''''''''' y' s f x'''''''''' y'') : term1729 A B s x'''''''''' f y''.
Proof. exact (proj2 (@lem4957437 A B x'''''''' y x''''''''' y' s f x'''''''''' y'' h1)). Qed.
Lemma lem4957444 {A B : Type'} (x'''''' : type1448 A B) (h1 : term912 A B x'''''') : term1703 A B x''''''.
Proof. exact (proj2 (@lem4956827 A B x'''''' h1)). Qed.
Lemma lem4957462 {A B : Type'} (x'''''''' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term1774 A B x'''''''' s f) : term1774 A B x'''''''' s f.
Proof. exact (h1). Qed.
Lemma lem4957463 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) (x''''''''' : A) (y' : A) (h1 : term1743 A B y s f x''''''''' y') : term1743 A B y s f x''''''''' y'.
Proof. exact (h1). Qed.
Lemma lem4957464 {A B : Type'} (x'''''''' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term1774 A B x'''''''' s f) : term1753 A B s f.
Proof. exact (proj2 (@lem4957462 A B x'''''''' s f h1)). Qed.
Lemma lem4957467 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) (x''''''''' : A) (y' : A) (h1 : term1743 A B y s f x''''''''' y') : term1741 A B s f y.
Proof. exact (proj1 (@lem4957463 A B y s f x''''''''' y' h1)). Qed.
Lemma lem4957474 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) (x''''''''' : A) (y' : A) (h1 : term1743 A B y s f x''''''''' y') : term1739 A B s f y.
Proof. exact (proj2 (@lem4957467 A B y s f x''''''''' y' h1)). Qed.
Lemma lem4958324 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term1749 A B s f x y) = (term1749 A B s f x y).
Proof. exact (eq_refl (term1749 A B s f x y)). Qed.
Lemma lem4958325 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term1750 A B s f x) = (term1750 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem4958324 A B s f x y)). Qed.
Lemma lem4958326 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4958327 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term1751 A B s f x) = (term1751 A B s f x).
Proof. exact (MK_COMB (@lem4958326 A) (@lem4958325 A B s f x)). Qed.
Lemma lem4958328 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term1752 A B s f) = (term1752 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4958327 A B s f x)). Qed.
Lemma lem4958329 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4958331 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term1753 A B s f) = (term1753 A B s f).
Proof. exact (MK_COMB (@lem4958329 A) (@lem4958328 A B s f)). Qed.
Lemma lem4958332 {A B : Type'} (x'''''''' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term1774 A B x'''''''' s f) : term1753 A B s f.
Proof. exact (EQ_MP (@lem4958331 A B s f) (@lem4957464 A B x'''''''' s f h1)). Qed.
Lemma lem4958507 {A B : Type'} (x'''''' : type1448 A B) (y : B) (f : A -> B) (s : A -> Prop) : (term1694 A B x'''''' y f s) = (term1779 A B x'''''' y f s).
Proof. exact (@lem19490 (y = (term1682 A B x'''''' y s f)) (term1691 A B y f s) (term1679 A B x'''''' y f s)). Qed.
Lemma lem4958508 {A B : Type'} (x'''''' : type1448 A B) (y : B) (s : A -> Prop) : (term1696 A B x'''''' y s) = (term1780 A B x'''''' y s).
Proof. exact (fun_ext (fun f : A -> B => @lem4958507 A B x'''''' y f s)). Qed.
Lemma lem4958509 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4958510 {A B : Type'} (x'''''' : type1448 A B) (y : B) (s : A -> Prop) : (term1698 A B x'''''' y s) = (term1781 A B x'''''' y s).
Proof. exact (MK_COMB (@lem4958509 A B) (@lem4958508 A B x'''''' y s)). Qed.
Lemma lem4958511 {A B : Type'} (x'''''' : type1448 A B) (y : B) : (term1700 A B x'''''' y) = (term1782 A B x'''''' y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4958510 A B x'''''' y s)). Qed.
Lemma lem4958512 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4958513 {A B : Type'} (x'''''' : type1448 A B) (y : B) : (term1701 A B x'''''' y) = (term1783 A B x'''''' y).
Proof. exact (MK_COMB (@lem4958512 A) (@lem4958511 A B x'''''' y)). Qed.
Lemma lem4958514 {A B : Type'} (x'''''' : type1448 A B) : (term1702 A B x'''''') = (term1784 A B x'''''').
Proof. exact (fun_ext (fun y : B => @lem4958513 A B x'''''' y)). Qed.
Lemma lem4958515 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4958517 {A B : Type'} (x'''''' : type1448 A B) : (term1703 A B x'''''') = (term1785 A B x'''''').
Proof. exact (MK_COMB (@lem4958515 B) (@lem4958514 A B x'''''')). Qed.
Lemma lem4958518 {A B : Type'} (x'''''' : type1448 A B) (h1 : term912 A B x'''''') : term1785 A B x''''''.
Proof. exact (EQ_MP (@lem4958517 A B x'''''') (@lem4957444 A B x'''''' h1)). Qed.
Lemma lem4959166 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term1737 A B s f x y) = (term1737 A B s f x y).
Proof. exact (eq_refl (term1737 A B s f x y)). Qed.
Lemma lem4959167 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term1738 A B s f y) = (term1738 A B s f y).
Proof. exact (fun_ext (fun x : A => @lem4959166 A B s f x y)). Qed.
Lemma lem4959168 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4959170 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term1739 A B s f y) = (term1739 A B s f y).
Proof. exact (MK_COMB (@lem4959168 A) (@lem4959167 A B s f y)). Qed.
Lemma lem4959171 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) (x''''''''' : A) (y' : A) (h1 : term1743 A B y s f x''''''''' y') : term1739 A B s f y.
Proof. exact (EQ_MP (@lem4959170 A B s f y) (@lem4957474 A B y s f x''''''''' y' h1)). Qed.
Lemma lem4959331 {A B : Type'} (_61758 : A) (x'''''''' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term1774 A B x'''''''' s f) : term1786 A B s f _61758.
Proof. exact (@lem4958332 A B x'''''''' s f h1 _61758). Qed.
Lemma lem4959332 {A B : Type'} (s : A -> Prop) (f : A -> B) (_61758 : A) : (term1786 A B s f _61758) = (term1751 A B s f _61758).
Proof. exact (eq_refl (term1786 A B s f _61758)). Qed.
Lemma lem4959333 {A B : Type'} (_61758 : A) (x'''''''' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term1774 A B x'''''''' s f) : term1751 A B s f _61758.
Proof. exact (EQ_MP (@lem4959332 A B s f _61758) (@lem4959331 A B _61758 x'''''''' s f h1)). Qed.
Lemma lem4959334 {A B : Type'} (_61758 : A) (_61759 : A) (x'''''''' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term1774 A B x'''''''' s f) : term1787 A B s f _61758 _61759.
Proof. exact (@lem4959333 A B _61758 x'''''''' s f h1 _61759). Qed.
Lemma lem4959335 {A B : Type'} (s : A -> Prop) (f : A -> B) (_61758 : A) (_61759 : A) : (term1787 A B s f _61758 _61759) = (term1749 A B s f _61758 _61759).
Proof. exact (eq_refl (term1787 A B s f _61758 _61759)). Qed.
Lemma lem4959336 {A B : Type'} (_61758 : A) (_61759 : A) (x'''''''' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term1774 A B x'''''''' s f) : term1749 A B s f _61758 _61759.
Proof. exact (EQ_MP (@lem4959335 A B s f _61758 _61759) (@lem4959334 A B _61758 _61759 x'''''''' s f h1)). Qed.
Lemma lem4959370 {A B : Type'} (_61771 : B) (x'''''' : type1448 A B) (h1 : term912 A B x'''''') : term1788 A B x'''''' _61771.
Proof. exact (@lem4958518 A B x'''''' h1 _61771). Qed.
Lemma lem4959371 {A B : Type'} (x'''''' : type1448 A B) (_61771 : B) : (term1788 A B x'''''' _61771) = (term1783 A B x'''''' _61771).
Proof. exact (eq_refl (term1788 A B x'''''' _61771)). Qed.
Lemma lem4959372 {A B : Type'} (_61771 : B) (x'''''' : type1448 A B) (h1 : term912 A B x'''''') : term1783 A B x'''''' _61771.
Proof. exact (EQ_MP (@lem4959371 A B x'''''' _61771) (@lem4959370 A B _61771 x'''''' h1)). Qed.
Lemma lem4959373 {A B : Type'} (_61771 : B) (_61772 : A -> Prop) (x'''''' : type1448 A B) (h1 : term912 A B x'''''') : term1789 A B x'''''' _61771 _61772.
Proof. exact (@lem4959372 A B _61771 x'''''' h1 _61772). Qed.
Lemma lem4959374 {A B : Type'} (x'''''' : type1448 A B) (_61771 : B) (_61772 : A -> Prop) : (term1789 A B x'''''' _61771 _61772) = (term1781 A B x'''''' _61771 _61772).
Proof. exact (eq_refl (term1789 A B x'''''' _61771 _61772)). Qed.
Lemma lem4959375 {A B : Type'} (_61771 : B) (_61772 : A -> Prop) (x'''''' : type1448 A B) (h1 : term912 A B x'''''') : term1781 A B x'''''' _61771 _61772.
Proof. exact (EQ_MP (@lem4959374 A B x'''''' _61771 _61772) (@lem4959373 A B _61771 _61772 x'''''' h1)). Qed.
Lemma lem4959376 {A B : Type'} (_61771 : B) (_61772 : A -> Prop) (_61773 : A -> B) (x'''''' : type1448 A B) (h1 : term912 A B x'''''') : term1790 A B x'''''' _61771 _61772 _61773.
Proof. exact (@lem4959375 A B _61771 _61772 x'''''' h1 _61773). Qed.
Lemma lem4959377 {A B : Type'} (x'''''' : type1448 A B) (_61771 : B) (_61773 : A -> B) (_61772 : A -> Prop) : (term1790 A B x'''''' _61771 _61772 _61773) = (term1779 A B x'''''' _61771 _61773 _61772).
Proof. exact (eq_refl (term1790 A B x'''''' _61771 _61772 _61773)). Qed.
Lemma lem4959378 {A B : Type'} (_61771 : B) (_61773 : A -> B) (_61772 : A -> Prop) (x'''''' : type1448 A B) (h1 : term912 A B x'''''') : term1779 A B x'''''' _61771 _61773 _61772.
Proof. exact (EQ_MP (@lem4959377 A B x'''''' _61771 _61773 _61772) (@lem4959376 A B _61771 _61772 _61773 x'''''' h1)). Qed.
Lemma lem4959493 {A B : Type'} (_61812 : A) (y : B) (s : A -> Prop) (f : A -> B) (x''''''''' : A) (y' : A) (h1 : term1743 A B y s f x''''''''' y') : term1791 A B s f y _61812.
Proof. exact (@lem4959171 A B y s f x''''''''' y' h1 _61812). Qed.
Lemma lem4959494 {A B : Type'} (s : A -> Prop) (f : A -> B) (_61812 : A) (y : B) : (term1791 A B s f y _61812) = (term1737 A B s f _61812 y).
Proof. exact (eq_refl (term1791 A B s f y _61812)). Qed.
Lemma lem4959615 {A B : Type'} (s : A -> Prop) (f : A -> B) (_61758 : A) (_61759 : A) : (term1749 A B s f _61758 _61759) = (term1792 A B s f _61758 _61759).
Proof. exact (@lem4945037 (term1706 A _61758 s) (term1746 A B s _61758 f _61759) (_61758 = _61759)). Qed.
Lemma lem4959622 {A B : Type'} (s : A -> Prop) (f : A -> B) (_61758 : A) (_61759 : A) : (term1793 A B s f _61758 _61759) = (term1794 A B s f _61758 _61759).
Proof. exact (@lem4945037 (term1706 A _61759 s) (term1745 A B _61758 f _61759) (_61758 = _61759)). Qed.
Lemma lem4959623 {A : Type'} (_61758 : A) (s : A -> Prop) : (term1736 A _61758 s) = (term1736 A _61758 s).
Proof. exact (eq_refl (term1736 A _61758 s)). Qed.
Lemma lem4959626 {A B : Type'} (s : A -> Prop) (f : A -> B) (_61758 : A) (_61759 : A) : (term1792 A B s f _61758 _61759) = (term1795 A B s f _61758 _61759).
Proof. exact (MK_COMB (@lem4959623 A _61758 s) (@lem4959622 A B s f _61758 _61759)). Qed.
Lemma lem4959628 {A B : Type'} (s : A -> Prop) (f : A -> B) (_61758 : A) (_61759 : A) : (term1749 A B s f _61758 _61759) = (term1795 A B s f _61758 _61759).
Proof. exact (TRANS (@lem4959615 A B s f _61758 _61759) (@lem4959626 A B s f _61758 _61759)). Qed.
Lemma lem4960063 {A B : Type'} (x'''''''' : B -> A) (y : B) (x''''''''' : A) (y' : A) (s : A -> Prop) (f : A -> B) (x'''''''''' : A) (y'' : A) (h1 : term516 A B x'''''''' y x''''''''' y' s f x'''''''''' y'') : term1724 A x'''''''''' y''.
Proof. exact (proj2 (@lem4957434 A B x'''''''' y x''''''''' y' s f x'''''''''' y'' h1)). Qed.
Lemma lem4960230 {A B : Type'} (_61758 : A) (_61759 : A) (x'''''''' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term1774 A B x'''''''' s f) : term1795 A B s f _61758 _61759.
Proof. exact (EQ_MP (@lem4959628 A B s f _61758 _61759) (@lem4959336 A B _61758 _61759 x'''''''' s f h1)). Qed.
Lemma lem4960803 {A B : Type'} (_61812 : A) (y : B) (s : A -> Prop) (f : A -> B) (x''''''''' : A) (y' : A) (h1 : term1743 A B y s f x''''''''' y') : term1737 A B s f _61812 y.
Proof. exact (EQ_MP (@lem4959494 A B s f _61812 y) (@lem4959493 A B _61812 y s f x''''''''' y' h1)). Qed.
Lemma lem4961041 {A B : Type'} (_61771 : B) (_61772 : A -> Prop) (_61773 : A -> B) (x'''''' : type1448 A B) (h1 : term912 A B x'''''') : term1796 A B x'''''' _61771 _61772 _61773.
Proof. exact (proj1 (@lem4959378 A B _61771 _61773 _61772 x'''''' h1)). Qed.
Lemma lem4961055 {A B : Type'} (_61771 : B) (_61773 : A -> B) (_61772 : A -> Prop) (x'''''' : type1448 A B) (h1 : term912 A B x'''''') : term1797 A B x'''''' _61771 _61773 _61772.
Proof. exact (proj2 (@lem4959378 A B _61771 _61773 _61772 x'''''' h1)). Qed.
Lemma lem4962018 {A B : Type'} (x'''''''' : B -> A) (y : B) (x''''''''' : A) (y' : A) (s : A -> Prop) (f : A -> B) (x'''''''''' : A) (y'' : A) (h1 : term516 A B x'''''''' y x''''''''' y' s f x'''''''''' y'') : term1704 A x'''''''''' s.
Proof. exact (proj1 (@lem4957437 A B x'''''''' y x''''''''' y' s f x'''''''''' y'' h1)). Qed.
Lemma lem4962019 {A B : Type'} (x'''''''' : B -> A) (y : B) (x''''''''' : A) (y' : A) (s : A -> Prop) (f : A -> B) (x'''''''''' : A) (y'' : A) (h1 : term516 A B x'''''''' y x''''''''' y' s f x'''''''''' y'') : term1798 A x'''''''''' s.
Proof. exact (fun h0 : term1706 A x'''''''''' s => @lem4962018 A B x'''''''' y x''''''''' y' s f x'''''''''' y'' h1). Qed.
Lemma lem4962021 (p : Prop) : (term1799 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4962022 {A : Type'} (x'''''''''' : A) (s : A -> Prop) : (term1798 A x'''''''''' s) = (term1704 A x'''''''''' s).
Proof. exact (@lem4962021 (term1704 A x'''''''''' s)). Qed.
Lemma lem4962023 {A B : Type'} (x'''''''' : B -> A) (y : B) (x''''''''' : A) (y' : A) (s : A -> Prop) (f : A -> B) (x'''''''''' : A) (y'' : A) (h1 : term516 A B x'''''''' y x''''''''' y' s f x'''''''''' y'') : term1704 A x'''''''''' s.
Proof. exact (EQ_MP (@lem4962022 A x'''''''''' s) (@lem4962019 A B x'''''''' y x''''''''' y' s f x'''''''''' y'' h1)). Qed.
Lemma lem4962025 {A B : Type'} (x'''''''' : B -> A) (y : B) (x''''''''' : A) (y' : A) (s : A -> Prop) (f : A -> B) (x'''''''''' : A) (y'' : A) (h1 : term516 A B x'''''''' y x''''''''' y' s f x'''''''''' y'') : term1704 A y'' s.
Proof. exact (proj1 (@lem4957438 A B x'''''''' y x''''''''' y' s f x'''''''''' y'' h1)). Qed.
Lemma lem4962026 {A B : Type'} (x'''''''' : B -> A) (y : B) (x''''''''' : A) (y' : A) (s : A -> Prop) (f : A -> B) (x'''''''''' : A) (y'' : A) (h1 : term516 A B x'''''''' y x''''''''' y' s f x'''''''''' y'') : term1798 A y'' s.
Proof. exact (fun h0 : term1706 A y'' s => @lem4962025 A B x'''''''' y x''''''''' y' s f x'''''''''' y'' h1). Qed.
Lemma lem4962028 (p : Prop) : (term1799 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4962029 {A : Type'} (y'' : A) (s : A -> Prop) : (term1798 A y'' s) = (term1704 A y'' s).
Proof. exact (@lem4962028 (term1704 A y'' s)). Qed.
Lemma lem4962030 {A B : Type'} (x'''''''' : B -> A) (y : B) (x''''''''' : A) (y' : A) (s : A -> Prop) (f : A -> B) (x'''''''''' : A) (y'' : A) (h1 : term516 A B x'''''''' y x''''''''' y' s f x'''''''''' y'') : term1704 A y'' s.
Proof. exact (EQ_MP (@lem4962029 A y'' s) (@lem4962026 A B x'''''''' y x''''''''' y' s f x'''''''''' y'' h1)). Qed.
Lemma lem4962032 {A B : Type'} (x'''''''' : B -> A) (y : B) (x''''''''' : A) (y' : A) (s : A -> Prop) (f : A -> B) (x'''''''''' : A) (y'' : A) (h1 : term516 A B x'''''''' y x''''''''' y' s f x'''''''''' y'') : (@I (A -> B) f x'''''''''') = (@I (A -> B) f y'').
Proof. exact (proj2 (@lem4957438 A B x'''''''' y x''''''''' y' s f x'''''''''' y'' h1)). Qed.
Lemma lem4962033 {A B : Type'} (x'''''''' : B -> A) (y : B) (x''''''''' : A) (y' : A) (s : A -> Prop) (f : A -> B) (x'''''''''' : A) (y'' : A) (h1 : term516 A B x'''''''' y x''''''''' y' s f x'''''''''' y'') : term1800 A B x'''''''''' f y''.
Proof. exact (fun h0 : term1745 A B x'''''''''' f y'' => @lem4962032 A B x'''''''' y x''''''''' y' s f x'''''''''' y'' h1). Qed.
Lemma lem4962035 (p : Prop) : (term1799 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4962036 {A B : Type'} (x'''''''''' : A) (f : A -> B) (y'' : A) : (term1800 A B x'''''''''' f y'') = ((@I (A -> B) f x'''''''''') = (@I (A -> B) f y'')).
Proof. exact (@lem4962035 ((@I (A -> B) f x'''''''''') = (@I (A -> B) f y''))). Qed.
Lemma lem4962037 {A B : Type'} (x'''''''' : B -> A) (y : B) (x''''''''' : A) (y' : A) (s : A -> Prop) (f : A -> B) (x'''''''''' : A) (y'' : A) (h1 : term516 A B x'''''''' y x''''''''' y' s f x'''''''''' y'') : (@I (A -> B) f x'''''''''') = (@I (A -> B) f y'').
Proof. exact (EQ_MP (@lem4962036 A B x'''''''''' f y'') (@lem4962033 A B x'''''''' y x''''''''' y' s f x'''''''''' y'' h1)). Qed.
Lemma lem4962053 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4962054 {A B : Type'} (f : A -> B) (s : A -> Prop) (_61758 : A) (_61759 : A) : (term1794 A B s f _61758 _61759) = (term1801 A B f s _61758 _61759).
Proof. exact (@lem4962053 (term1745 A B _61758 f _61759) (term1706 A _61759 s) (_61758 = _61759)). Qed.
Lemma lem4962070 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4962071 {A : Type'} (_61758 : A) (_61759 : A) (s : A -> Prop) : (term1802 A s _61758 _61759) = (term1803 A _61758 _61759 s).
Proof. exact (@lem4962070 (_61758 = _61759) (term1706 A _61759 s)). Qed.
Lemma lem4962079 {A B : Type'} (_61758 : A) (f : A -> B) (_61759 : A) : (term1804 A B _61758 f _61759) = (term1804 A B _61758 f _61759).
Proof. exact (eq_refl (term1804 A B _61758 f _61759)). Qed.
Lemma lem4962080 {A B : Type'} (f : A -> B) (_61758 : A) (_61759 : A) (s : A -> Prop) : (term1801 A B f s _61758 _61759) = (term1805 A B f _61758 _61759 s).
Proof. exact (MK_COMB (@lem4962079 A B _61758 f _61759) (@lem4962071 A _61758 _61759 s)). Qed.
Lemma lem4962084 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4962085 {A B : Type'} (_61758 : A) (f : A -> B) (_61759 : A) (s : A -> Prop) : (term1805 A B f _61758 _61759 s) = (term1806 A B _61758 f _61759 s).
Proof. exact (@lem4962084 (_61758 = _61759) (term1745 A B _61758 f _61759) (term1706 A _61759 s)). Qed.
Lemma lem4962105 {A B : Type'} (_61758 : A) (f : A -> B) (_61759 : A) (s : A -> Prop) : (term1801 A B f s _61758 _61759) = (term1806 A B _61758 f _61759 s).
Proof. exact (TRANS (@lem4962080 A B f _61758 _61759 s) (@lem4962085 A B _61758 f _61759 s)). Qed.
Lemma lem4962106 {A B : Type'} (_61758 : A) (f : A -> B) (_61759 : A) (s : A -> Prop) : (term1794 A B s f _61758 _61759) = (term1806 A B _61758 f _61759 s).
Proof. exact (TRANS (@lem4962054 A B f s _61758 _61759) (@lem4962105 A B _61758 f _61759 s)). Qed.
Lemma lem4962107 {A : Type'} (_61758 : A) (s : A -> Prop) : (term1736 A _61758 s) = (term1736 A _61758 s).
Proof. exact (eq_refl (term1736 A _61758 s)). Qed.
Lemma lem4962108 {A B : Type'} (_61758 : A) (f : A -> B) (_61759 : A) (s : A -> Prop) : (term1795 A B s f _61758 _61759) = (term1807 A B _61758 f _61759 s).
Proof. exact (MK_COMB (@lem4962107 A _61758 s) (@lem4962106 A B _61758 f _61759 s)). Qed.
Lemma lem4962112 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4962113 {A B : Type'} (_61758 : A) (f : A -> B) (_61759 : A) (s : A -> Prop) : (term1807 A B _61758 f _61759 s) = (term1808 A B _61758 f _61759 s).
Proof. exact (@lem4962112 (_61758 = _61759) (term1706 A _61758 s) (term1809 A B _61758 f _61759 s)). Qed.
Lemma lem4962129 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4962130 {A B : Type'} (f : A -> B) (_61758 : A) (_61759 : A) (s : A -> Prop) : (term1810 A B _61758 f _61759 s) = (term1811 A B f _61758 _61759 s).
Proof. exact (@lem4962129 (term1745 A B _61758 f _61759) (term1706 A _61758 s) (term1706 A _61759 s)). Qed.
Lemma lem4962148 {A : Type'} (_61758 : A) (_61759 : A) : (term1812 A _61758 _61759) = (term1812 A _61758 _61759).
Proof. exact (eq_refl (term1812 A _61758 _61759)). Qed.
Lemma lem4962149 {A B : Type'} (f : A -> B) (_61758 : A) (_61759 : A) (s : A -> Prop) : (term1808 A B _61758 f _61759 s) = (term1813 A B f _61758 _61759 s).
Proof. exact (MK_COMB (@lem4962148 A _61758 _61759) (@lem4962130 A B f _61758 _61759 s)). Qed.
Lemma lem4962160 {A B : Type'} (f : A -> B) (_61758 : A) (_61759 : A) (s : A -> Prop) : (term1807 A B _61758 f _61759 s) = (term1813 A B f _61758 _61759 s).
Proof. exact (TRANS (@lem4962113 A B _61758 f _61759 s) (@lem4962149 A B f _61758 _61759 s)). Qed.
Lemma lem4962161 {A B : Type'} (f : A -> B) (_61758 : A) (_61759 : A) (s : A -> Prop) : (term1795 A B s f _61758 _61759) = (term1813 A B f _61758 _61759 s).
Proof. exact (TRANS (@lem4962108 A B _61758 f _61759 s) (@lem4962160 A B f _61758 _61759 s)). Qed.
Lemma lem4962162 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4962163 {A B : Type'} (f : A -> B) (_61758 : A) (_61759 : A) (s : A -> Prop) : (term1814 A B s f _61758 _61759) = (term1815 A B f _61758 _61759 s).
Proof. exact (MK_COMB (@lem4962162) (@lem4962161 A B f _61758 _61759 s)). Qed.
Lemma lem4962189 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4962190 {A B : Type'} (_61758 : A) (f : A -> B) (_61759 : A) (s : A -> Prop) : (term1746 A B s _61758 f _61759) = (term1809 A B _61758 f _61759 s).
Proof. exact (@lem4962189 (term1745 A B _61758 f _61759) (term1706 A _61759 s)). Qed.
Lemma lem4962198 {A : Type'} (_61758 : A) (s : A -> Prop) : (term1736 A _61758 s) = (term1736 A _61758 s).
Proof. exact (eq_refl (term1736 A _61758 s)). Qed.
Lemma lem4962199 {A B : Type'} (_61758 : A) (f : A -> B) (_61759 : A) (s : A -> Prop) : (term1747 A B s _61758 f _61759) = (term1810 A B _61758 f _61759 s).
Proof. exact (MK_COMB (@lem4962198 A _61758 s) (@lem4962190 A B _61758 f _61759 s)). Qed.
Lemma lem4962203 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4962204 {A B : Type'} (f : A -> B) (_61758 : A) (_61759 : A) (s : A -> Prop) : (term1810 A B _61758 f _61759 s) = (term1811 A B f _61758 _61759 s).
Proof. exact (@lem4962203 (term1745 A B _61758 f _61759) (term1706 A _61758 s) (term1706 A _61759 s)). Qed.
Lemma lem4962222 {A B : Type'} (f : A -> B) (_61758 : A) (_61759 : A) (s : A -> Prop) : (term1747 A B s _61758 f _61759) = (term1811 A B f _61758 _61759 s).
Proof. exact (TRANS (@lem4962199 A B _61758 f _61759 s) (@lem4962204 A B f _61758 _61759 s)). Qed.
Lemma lem4962223 {A : Type'} (_61758 : A) (_61759 : A) : (term1812 A _61758 _61759) = (term1812 A _61758 _61759).
Proof. exact (eq_refl (term1812 A _61758 _61759)). Qed.
Lemma lem4962224 {A B : Type'} (f : A -> B) (_61758 : A) (_61759 : A) (s : A -> Prop) : (term1816 A B s _61758 f _61759) = (term1813 A B f _61758 _61759 s).
Proof. exact (MK_COMB (@lem4962223 A _61758 _61759) (@lem4962222 A B f _61758 _61759 s)). Qed.
Lemma lem4962235 {A B : Type'} (f : A -> B) (_61758 : A) (_61759 : A) (s : A -> Prop) : ((term1795 A B s f _61758 _61759) = (term1816 A B s _61758 f _61759)) = ((term1813 A B f _61758 _61759 s) = (term1813 A B f _61758 _61759 s)).
Proof. exact (MK_COMB (@lem4962163 A B f _61758 _61759 s) (@lem4962224 A B f _61758 _61759 s)). Qed.
Lemma lem4962237 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4962238 (x : Prop) : (x = x) = True.
Proof. exact (@lem4962237 Prop x). Qed.
Lemma lem4962239 {A B : Type'} (f : A -> B) (_61758 : A) (_61759 : A) (s : A -> Prop) : ((term1813 A B f _61758 _61759 s) = (term1813 A B f _61758 _61759 s)) = True.
Proof. exact (@lem4962238 (term1813 A B f _61758 _61759 s)). Qed.
Lemma lem4962240 {A B : Type'} (s : A -> Prop) (_61758 : A) (f : A -> B) (_61759 : A) : ((term1795 A B s f _61758 _61759) = (term1816 A B s _61758 f _61759)) = True.
Proof. exact (TRANS (@lem4962235 A B f _61758 _61759 s) (@lem4962239 A B f _61758 _61759 s)). Qed.
Lemma lem4962241 {A B : Type'} (s : A -> Prop) (_61758 : A) (f : A -> B) (_61759 : A) : True = ((term1795 A B s f _61758 _61759) = (term1816 A B s _61758 f _61759)).
Proof. exact (SYM (@lem4962240 A B s _61758 f _61759)). Qed.
Lemma lem4962242 {A B : Type'} (s : A -> Prop) (_61758 : A) (f : A -> B) (_61759 : A) : (term1795 A B s f _61758 _61759) = (term1816 A B s _61758 f _61759).
Proof. exact (EQ_MP (@lem4962241 A B s _61758 f _61759) (@lem0)). Qed.
Lemma lem4962243 {A B : Type'} (_61758 : A) (_61759 : A) (x'''''''' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term1774 A B x'''''''' s f) : term1816 A B s _61758 f _61759.
Proof. exact (EQ_MP (@lem4962242 A B s _61758 f _61759) (@lem4960230 A B _61758 _61759 x'''''''' s f h1)). Qed.
Lemma lem4962245 (b : Prop) (a : Prop) : (a \/ b) = (term1817 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4962246 {A B : Type'} (s : A -> Prop) (f : A -> B) (_61758 : A) (_61759 : A) : (term1816 A B s _61758 f _61759) = (term1818 A B s f _61758 _61759).
Proof. exact (@lem4962245 (term1747 A B s _61758 f _61759) (_61758 = _61759)). Qed.
Lemma lem4962248 (a : Prop) (b : Prop) : (term1819 a b) = (term1820 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4962249 {A B : Type'} (s : A -> Prop) (_61758 : A) (f : A -> B) (_61759 : A) : (term1821 A B s _61758 f _61759) = (term1822 A B s _61758 f _61759).
Proof. exact (@lem4962248 (term1706 A _61758 s) (term1746 A B s _61758 f _61759)). Qed.
Lemma lem4962251 (a : Prop) : (term1823 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4962252 {A : Type'} (_61758 : A) (s : A -> Prop) : (term1824 A _61758 s) = (term1704 A _61758 s).
Proof. exact (@lem4962251 (term1704 A _61758 s)). Qed.
Lemma lem4962253 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4962254 {A : Type'} (_61758 : A) (s : A -> Prop) : (term1825 A _61758 s) = (term1728 A _61758 s).
Proof. exact (MK_COMB (@lem4962253) (@lem4962252 A _61758 s)). Qed.
Lemma lem4962256 (a : Prop) (b : Prop) : (term1819 a b) = (term1820 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4962257 {A B : Type'} (s : A -> Prop) (_61758 : A) (f : A -> B) (_61759 : A) : (term1826 A B s _61758 f _61759) = (term1827 A B s _61758 f _61759).
Proof. exact (@lem4962256 (term1706 A _61759 s) (term1745 A B _61758 f _61759)). Qed.
Lemma lem4962259 (a : Prop) : (term1823 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4962260 {A : Type'} (_61759 : A) (s : A -> Prop) : (term1824 A _61759 s) = (term1704 A _61759 s).
Proof. exact (@lem4962259 (term1704 A _61759 s)). Qed.
Lemma lem4962261 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4962262 {A : Type'} (_61759 : A) (s : A -> Prop) : (term1825 A _61759 s) = (term1728 A _61759 s).
Proof. exact (MK_COMB (@lem4962261) (@lem4962260 A _61759 s)). Qed.
Lemma lem4962264 (a : Prop) : (term1823 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4962265 {A B : Type'} (_61758 : A) (f : A -> B) (_61759 : A) : (term1828 A B _61758 f _61759) = ((@I (A -> B) f _61758) = (@I (A -> B) f _61759)).
Proof. exact (@lem4962264 ((@I (A -> B) f _61758) = (@I (A -> B) f _61759))). Qed.
Lemma lem4962266 {A B : Type'} (s : A -> Prop) (_61758 : A) (f : A -> B) (_61759 : A) : (term1827 A B s _61758 f _61759) = (term1729 A B s _61758 f _61759).
Proof. exact (MK_COMB (@lem4962262 A _61759 s) (@lem4962265 A B _61758 f _61759)). Qed.
Lemma lem4962267 {A B : Type'} (s : A -> Prop) (_61758 : A) (f : A -> B) (_61759 : A) : (term1826 A B s _61758 f _61759) = (term1729 A B s _61758 f _61759).
Proof. exact (TRANS (@lem4962257 A B s _61758 f _61759) (@lem4962266 A B s _61758 f _61759)). Qed.
Lemma lem4962268 {A B : Type'} (s : A -> Prop) (_61758 : A) (f : A -> B) (_61759 : A) : (term1822 A B s _61758 f _61759) = (term1730 A B s _61758 f _61759).
Proof. exact (MK_COMB (@lem4962254 A _61758 s) (@lem4962267 A B s _61758 f _61759)). Qed.
Lemma lem4962269 {A B : Type'} (s : A -> Prop) (_61758 : A) (f : A -> B) (_61759 : A) : (term1821 A B s _61758 f _61759) = (term1730 A B s _61758 f _61759).
Proof. exact (TRANS (@lem4962249 A B s _61758 f _61759) (@lem4962268 A B s _61758 f _61759)). Qed.
Lemma lem4962270 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4962271 {A B : Type'} (s : A -> Prop) (_61758 : A) (f : A -> B) (_61759 : A) : (term1829 A B s _61758 f _61759) = (term1830 A B s _61758 f _61759).
Proof. exact (MK_COMB (@lem4962270) (@lem4962269 A B s _61758 f _61759)). Qed.
Lemma lem4962272 {A : Type'} (_61758 : A) (_61759 : A) : (_61758 = _61759) = (_61758 = _61759).
Proof. exact (eq_refl (_61758 = _61759)). Qed.
Lemma lem4962273 {A B : Type'} (s : A -> Prop) (f : A -> B) (_61758 : A) (_61759 : A) : (term1818 A B s f _61758 _61759) = (term1831 A B s f _61758 _61759).
Proof. exact (MK_COMB (@lem4962271 A B s _61758 f _61759) (@lem4962272 A _61758 _61759)). Qed.
Lemma lem4962274 {A B : Type'} (s : A -> Prop) (f : A -> B) (_61758 : A) (_61759 : A) : (term1816 A B s _61758 f _61759) = (term1831 A B s f _61758 _61759).
Proof. exact (TRANS (@lem4962246 A B s f _61758 _61759) (@lem4962273 A B s f _61758 _61759)). Qed.
Lemma lem4962276 {A B : Type'} (x'''''''' : B -> A) (y : B) (x''''''''' : A) (y' : A) (s : A -> Prop) (f : A -> B) (x'''''''''' : A) (y'' : A) (h1 : term516 A B x'''''''' y x''''''''' y' s f x'''''''''' y'') : term1729 A B s x'''''''''' f y''.
Proof. exact (conj (@lem4962030 A B x'''''''' y x''''''''' y' s f x'''''''''' y'' h1) (@lem4962037 A B x'''''''' y x''''''''' y' s f x'''''''''' y'' h1)). Qed.
Lemma lem4962277 {A B : Type'} (x'''''''' : B -> A) (y : B) (x''''''''' : A) (y' : A) (s : A -> Prop) (f : A -> B) (x'''''''''' : A) (y'' : A) (h1 : term516 A B x'''''''' y x''''''''' y' s f x'''''''''' y'') : term1730 A B s x'''''''''' f y''.
Proof. exact (conj (@lem4962023 A B x'''''''' y x''''''''' y' s f x'''''''''' y'' h1) (@lem4962276 A B x'''''''' y x''''''''' y' s f x'''''''''' y'' h1)). Qed.
Lemma lem4962279 {A B : Type'} (_61758 : A) (_61759 : A) (x'''''''' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term1774 A B x'''''''' s f) : term1831 A B s f _61758 _61759.
Proof. exact (EQ_MP (@lem4962274 A B s f _61758 _61759) (@lem4962243 A B _61758 _61759 x'''''''' s f h1)). Qed.
Lemma lem4962280 {A B : Type'} (_61758 : A) (_61759 : A) (x'''''''' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term1774 A B x'''''''' s f) : term1831 A B s f _61758 _61759.
Proof. exact (@lem4962279 A B _61758 _61759 x'''''''' s f h1). Qed.
Lemma lem4962281 {A B : Type'} (x'''''''''' : A) (y'' : A) (x'''''''' : B -> A) (s : A -> Prop) (f : A -> B) (h1 : term1774 A B x'''''''' s f) : term1831 A B s f x'''''''''' y''.
Proof. exact (@lem4962280 A B x'''''''''' y'' x'''''''' s f h1). Qed.
Lemma lem4962284 {A B : Type'} (x'''''''' : B -> A) (y : B) (x''''''''' : A) (y' : A) (s : A -> Prop) (f : A -> B) (x'''''''''' : A) (y'' : A) (h1 : term1774 A B x'''''''' s f) (h2 : term516 A B x'''''''' y x''''''''' y' s f x'''''''''' y'') : x'''''''''' = y''.
Proof. exact (@lem4962281 A B x'''''''''' y'' x'''''''' s f h1 (@lem4962277 A B x'''''''' y x''''''''' y' s f x'''''''''' y'' h2)). Qed.
Lemma lem4962285 {A B : Type'} (x'''''''' : B -> A) (y : B) (x''''''''' : A) (y' : A) (s : A -> Prop) (f : A -> B) (x'''''''''' : A) (y'' : A) (h1 : term1774 A B x'''''''' s f) (h2 : term516 A B x'''''''' y x''''''''' y' s f x'''''''''' y'') : term1832 A x'''''''''' y''.
Proof. exact (fun h0 : term1724 A x'''''''''' y'' => @lem4962284 A B x'''''''' y x''''''''' y' s f x'''''''''' y'' h1 h2). Qed.
Lemma lem4962287 (p : Prop) : (term1799 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4962288 {A : Type'} (x'''''''''' : A) (y'' : A) : (term1832 A x'''''''''' y'') = (x'''''''''' = y'').
Proof. exact (@lem4962287 (x'''''''''' = y'')). Qed.
Lemma lem4962289 {A B : Type'} (x'''''''' : B -> A) (y : B) (x''''''''' : A) (y' : A) (s : A -> Prop) (f : A -> B) (x'''''''''' : A) (y'' : A) (h1 : term1774 A B x'''''''' s f) (h2 : term516 A B x'''''''' y x''''''''' y' s f x'''''''''' y'') : x'''''''''' = y''.
Proof. exact (EQ_MP (@lem4962288 A x'''''''''' y'') (@lem4962285 A B x'''''''' y x''''''''' y' s f x'''''''''' y'' h1 h2)). Qed.
Lemma lem4962292 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4962294 {A : Type'} (x'''''''''' : A) (y'' : A) : (term1724 A x'''''''''' y'') = (term1833 A x'''''''''' y'').
Proof. exact (@lem4962292 (x'''''''''' = y'')). Qed.
Lemma lem4962297 {A B : Type'} (x'''''''' : B -> A) (y : B) (x''''''''' : A) (y' : A) (s : A -> Prop) (f : A -> B) (x'''''''''' : A) (y'' : A) (h1 : term516 A B x'''''''' y x''''''''' y' s f x'''''''''' y'') : term1833 A x'''''''''' y''.
Proof. exact (EQ_MP (@lem4962294 A x'''''''''' y'') (@lem4960063 A B x'''''''' y x''''''''' y' s f x'''''''''' y'' h1)). Qed.
Lemma lem4962300 {A B : Type'} (x'''''''' : B -> A) (y : B) (x''''''''' : A) (y' : A) (s : A -> Prop) (f : A -> B) (x'''''''''' : A) (y'' : A) (h1 : term1774 A B x'''''''' s f) (h2 : term516 A B x'''''''' y x''''''''' y' s f x'''''''''' y'') : False.
Proof. exact (@lem4962297 A B x'''''''' y x''''''''' y' s f x'''''''''' y'' h2 (@lem4962289 A B x'''''''' y x''''''''' y' s f x'''''''''' y'' h1 h2)). Qed.
Lemma lem4962301 {A B : Type'} (x'''''''' : B -> A) (y : B) (x''''''''' : A) (y' : A) (s : A -> Prop) (f : A -> B) (x'''''''''' : A) (y'' : A) (h1 : term1774 A B x'''''''' s f) (h2 : term516 A B x'''''''' y x''''''''' y' s f x'''''''''' y'') : term1834.
Proof. exact (fun h0 : ~ False => @lem4962300 A B x'''''''' y x''''''''' y' s f x'''''''''' y'' h1 h2). Qed.
Lemma lem4962303 (p : Prop) : (term1799 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4962304 : term1834 = False.
Proof. exact (@lem4962303 False). Qed.
Lemma lem4963113 {B : Type'} (x : B) (y : B) (z : B) : term1835 B x y z.
Proof. exact (@lem21385 B x y z). Qed.
Lemma lem4963223 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) (x''''''''' : A) (y' : A) (h1 : term1743 A B y s f x''''''''' y') : term1690 A B y f s.
Proof. exact (proj1 (@lem4957467 A B y s f x''''''''' y' h1)). Qed.
Lemma lem4963224 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) (x''''''''' : A) (y' : A) (h1 : term1743 A B y s f x''''''''' y') : term1836 A B y f s.
Proof. exact (fun h0 : term1691 A B y f s => @lem4963223 A B y s f x''''''''' y' h1). Qed.
Lemma lem4963226 (p : Prop) : (term1799 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4963227 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1836 A B y f s) = (term1690 A B y f s).
Proof. exact (@lem4963226 (term1690 A B y f s)). Qed.
Lemma lem4963228 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) (x''''''''' : A) (y' : A) (h1 : term1743 A B y s f x''''''''' y') : term1690 A B y f s.
Proof. exact (EQ_MP (@lem4963227 A B y f s) (@lem4963224 A B y s f x''''''''' y' h1)). Qed.
Lemma lem4963234 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4963235 {A B : Type'} (x'''''' : type1448 A B) (_61771 : B) (_61773 : A -> B) (_61772 : A -> Prop) : (term1797 A B x'''''' _61771 _61773 _61772) = (term1837 A B x'''''' _61771 _61773 _61772).
Proof. exact (@lem4963234 (term1679 A B x'''''' _61771 _61773 _61772) (term1691 A B _61771 _61773 _61772)). Qed.
Lemma lem4963241 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4963242 {A B : Type'} (x'''''' : type1448 A B) (_61771 : B) (_61773 : A -> B) (_61772 : A -> Prop) : (term1838 A B x'''''' _61771 _61773 _61772) = (term1839 A B x'''''' _61771 _61773 _61772).
Proof. exact (MK_COMB (@lem4963241) (@lem4963235 A B x'''''' _61771 _61773 _61772)). Qed.
Lemma lem4963248 {A B : Type'} (x'''''' : type1448 A B) (_61771 : B) (_61773 : A -> B) (_61772 : A -> Prop) : (term1837 A B x'''''' _61771 _61773 _61772) = (term1837 A B x'''''' _61771 _61773 _61772).
Proof. exact (eq_refl (term1837 A B x'''''' _61771 _61773 _61772)). Qed.
Lemma lem4963249 {A B : Type'} (x'''''' : type1448 A B) (_61771 : B) (_61773 : A -> B) (_61772 : A -> Prop) : ((term1797 A B x'''''' _61771 _61773 _61772) = (term1837 A B x'''''' _61771 _61773 _61772)) = ((term1837 A B x'''''' _61771 _61773 _61772) = (term1837 A B x'''''' _61771 _61773 _61772)).
Proof. exact (MK_COMB (@lem4963242 A B x'''''' _61771 _61773 _61772) (@lem4963248 A B x'''''' _61771 _61773 _61772)). Qed.
Lemma lem4963251 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4963252 (x : Prop) : (x = x) = True.
Proof. exact (@lem4963251 Prop x). Qed.
Lemma lem4963253 {A B : Type'} (x'''''' : type1448 A B) (_61771 : B) (_61773 : A -> B) (_61772 : A -> Prop) : ((term1837 A B x'''''' _61771 _61773 _61772) = (term1837 A B x'''''' _61771 _61773 _61772)) = True.
Proof. exact (@lem4963252 (term1837 A B x'''''' _61771 _61773 _61772)). Qed.
Lemma lem4963254 {A B : Type'} (x'''''' : type1448 A B) (_61771 : B) (_61773 : A -> B) (_61772 : A -> Prop) : ((term1797 A B x'''''' _61771 _61773 _61772) = (term1837 A B x'''''' _61771 _61773 _61772)) = True.
Proof. exact (TRANS (@lem4963249 A B x'''''' _61771 _61773 _61772) (@lem4963253 A B x'''''' _61771 _61773 _61772)). Qed.
Lemma lem4963255 {A B : Type'} (x'''''' : type1448 A B) (_61771 : B) (_61773 : A -> B) (_61772 : A -> Prop) : True = ((term1797 A B x'''''' _61771 _61773 _61772) = (term1837 A B x'''''' _61771 _61773 _61772)).
Proof. exact (SYM (@lem4963254 A B x'''''' _61771 _61773 _61772)). Qed.
Lemma lem4963256 {A B : Type'} (x'''''' : type1448 A B) (_61771 : B) (_61773 : A -> B) (_61772 : A -> Prop) : (term1797 A B x'''''' _61771 _61773 _61772) = (term1837 A B x'''''' _61771 _61773 _61772).
Proof. exact (EQ_MP (@lem4963255 A B x'''''' _61771 _61773 _61772) (@lem0)). Qed.
Lemma lem4963257 {A B : Type'} (_61771 : B) (_61773 : A -> B) (_61772 : A -> Prop) (x'''''' : type1448 A B) (h1 : term912 A B x'''''') : term1837 A B x'''''' _61771 _61773 _61772.
Proof. exact (EQ_MP (@lem4963256 A B x'''''' _61771 _61773 _61772) (@lem4961055 A B _61771 _61773 _61772 x'''''' h1)). Qed.
Lemma lem4963259 (b : Prop) (a : Prop) : (a \/ b) = (term1817 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4963260 {A B : Type'} (x'''''' : type1448 A B) (_61771 : B) (_61773 : A -> B) (_61772 : A -> Prop) : (term1837 A B x'''''' _61771 _61773 _61772) = (term1840 A B x'''''' _61771 _61773 _61772).
Proof. exact (@lem4963259 (term1691 A B _61771 _61773 _61772) (term1679 A B x'''''' _61771 _61773 _61772)). Qed.
Lemma lem4963262 (a : Prop) : (term1823 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4963263 {A B : Type'} (_61771 : B) (_61773 : A -> B) (_61772 : A -> Prop) : (term1841 A B _61771 _61773 _61772) = (term1690 A B _61771 _61773 _61772).
Proof. exact (@lem4963262 (term1690 A B _61771 _61773 _61772)). Qed.
Lemma lem4963264 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4963265 {A B : Type'} (_61771 : B) (_61773 : A -> B) (_61772 : A -> Prop) : (term1842 A B _61771 _61773 _61772) = (term1843 A B _61771 _61773 _61772).
Proof. exact (MK_COMB (@lem4963264) (@lem4963263 A B _61771 _61773 _61772)). Qed.
Lemma lem4963266 {A B : Type'} (x'''''' : type1448 A B) (_61771 : B) (_61773 : A -> B) (_61772 : A -> Prop) : (term1679 A B x'''''' _61771 _61773 _61772) = (term1679 A B x'''''' _61771 _61773 _61772).
Proof. exact (eq_refl (term1679 A B x'''''' _61771 _61773 _61772)). Qed.
Lemma lem4963267 {A B : Type'} (x'''''' : type1448 A B) (_61771 : B) (_61773 : A -> B) (_61772 : A -> Prop) : (term1840 A B x'''''' _61771 _61773 _61772) = (term1844 A B x'''''' _61771 _61773 _61772).
Proof. exact (MK_COMB (@lem4963265 A B _61771 _61773 _61772) (@lem4963266 A B x'''''' _61771 _61773 _61772)). Qed.
Lemma lem4963268 {A B : Type'} (x'''''' : type1448 A B) (_61771 : B) (_61773 : A -> B) (_61772 : A -> Prop) : (term1837 A B x'''''' _61771 _61773 _61772) = (term1844 A B x'''''' _61771 _61773 _61772).
Proof. exact (TRANS (@lem4963260 A B x'''''' _61771 _61773 _61772) (@lem4963267 A B x'''''' _61771 _61773 _61772)). Qed.
Lemma lem4963271 {A B : Type'} (_61771 : B) (_61773 : A -> B) (_61772 : A -> Prop) (x'''''' : type1448 A B) (h1 : term912 A B x'''''') : term1844 A B x'''''' _61771 _61773 _61772.
Proof. exact (EQ_MP (@lem4963268 A B x'''''' _61771 _61773 _61772) (@lem4963257 A B _61771 _61773 _61772 x'''''' h1)). Qed.
Lemma lem4963272 {A B : Type'} (_61771 : B) (_61773 : A -> B) (_61772 : A -> Prop) (x'''''' : type1448 A B) (h1 : term912 A B x'''''') : term1844 A B x'''''' _61771 _61773 _61772.
Proof. exact (@lem4963271 A B _61771 _61773 _61772 x'''''' h1). Qed.
Lemma lem4963273 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x'''''' : type1448 A B) (h1 : term912 A B x'''''') : term1844 A B x'''''' y f s.
Proof. exact (@lem4963272 A B y f s x'''''' h1). Qed.
Lemma lem4963276 {A B : Type'} (x'''''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) (x''''''''' : A) (y' : A) (h1 : term912 A B x'''''') (h2 : term1743 A B y s f x''''''''' y') : term1679 A B x'''''' y f s.
Proof. exact (@lem4963273 A B y f s x'''''' h1 (@lem4963228 A B y s f x''''''''' y' h2)). Qed.
Lemma lem4963277 {A B : Type'} (x'''''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) (x''''''''' : A) (y' : A) (h1 : term912 A B x'''''') (h2 : term1743 A B y s f x''''''''' y') : term1845 A B x'''''' y f s.
Proof. exact (fun h0 : term1846 A B x'''''' y f s => @lem4963276 A B x'''''' y s f x''''''''' y' h1 h2). Qed.
Lemma lem4963279 (p : Prop) : (term1799 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4963280 {A B : Type'} (x'''''' : type1448 A B) (y : B) (f : A -> B) (s : A -> Prop) : (term1845 A B x'''''' y f s) = (term1679 A B x'''''' y f s).
Proof. exact (@lem4963279 (term1679 A B x'''''' y f s)). Qed.
Lemma lem4963281 {A B : Type'} (x'''''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) (x''''''''' : A) (y' : A) (h1 : term912 A B x'''''') (h2 : term1743 A B y s f x''''''''' y') : term1679 A B x'''''' y f s.
Proof. exact (EQ_MP (@lem4963280 A B x'''''' y f s) (@lem4963277 A B x'''''' y s f x''''''''' y' h1 h2)). Qed.
Lemma lem4963283 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) (x''''''''' : A) (y' : A) (h1 : term1743 A B y s f x''''''''' y') : term1690 A B y f s.
Proof. exact (proj1 (@lem4957467 A B y s f x''''''''' y' h1)). Qed.
Lemma lem4963284 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) (x''''''''' : A) (y' : A) (h1 : term1743 A B y s f x''''''''' y') : term1836 A B y f s.
Proof. exact (fun h0 : term1691 A B y f s => @lem4963283 A B y s f x''''''''' y' h1). Qed.
Lemma lem4963286 (p : Prop) : (term1799 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4963287 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1836 A B y f s) = (term1690 A B y f s).
Proof. exact (@lem4963286 (term1690 A B y f s)). Qed.
Lemma lem4963288 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) (x''''''''' : A) (y' : A) (h1 : term1743 A B y s f x''''''''' y') : term1690 A B y f s.
Proof. exact (EQ_MP (@lem4963287 A B y f s) (@lem4963284 A B y s f x''''''''' y' h1)). Qed.
Lemma lem4963294 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4963295 {A B : Type'} (x'''''' : type1448 A B) (_61771 : B) (_61773 : A -> B) (_61772 : A -> Prop) : (term1796 A B x'''''' _61771 _61772 _61773) = (term1847 A B x'''''' _61771 _61773 _61772).
Proof. exact (@lem4963294 (_61771 = (term1682 A B x'''''' _61771 _61772 _61773)) (term1691 A B _61771 _61773 _61772)). Qed.
Lemma lem4963303 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4963304 {A B : Type'} (x'''''' : type1448 A B) (_61771 : B) (_61773 : A -> B) (_61772 : A -> Prop) : (term1848 A B x'''''' _61771 _61772 _61773) = (term1849 A B x'''''' _61771 _61773 _61772).
Proof. exact (MK_COMB (@lem4963303) (@lem4963295 A B x'''''' _61771 _61773 _61772)). Qed.
Lemma lem4963312 {A B : Type'} (x'''''' : type1448 A B) (_61771 : B) (_61773 : A -> B) (_61772 : A -> Prop) : (term1847 A B x'''''' _61771 _61773 _61772) = (term1847 A B x'''''' _61771 _61773 _61772).
Proof. exact (eq_refl (term1847 A B x'''''' _61771 _61773 _61772)). Qed.
Lemma lem4963313 {A B : Type'} (x'''''' : type1448 A B) (_61771 : B) (_61773 : A -> B) (_61772 : A -> Prop) : ((term1796 A B x'''''' _61771 _61772 _61773) = (term1847 A B x'''''' _61771 _61773 _61772)) = ((term1847 A B x'''''' _61771 _61773 _61772) = (term1847 A B x'''''' _61771 _61773 _61772)).
Proof. exact (MK_COMB (@lem4963304 A B x'''''' _61771 _61773 _61772) (@lem4963312 A B x'''''' _61771 _61773 _61772)). Qed.
Lemma lem4963315 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4963316 (x : Prop) : (x = x) = True.
Proof. exact (@lem4963315 Prop x). Qed.
Lemma lem4963317 {A B : Type'} (x'''''' : type1448 A B) (_61771 : B) (_61773 : A -> B) (_61772 : A -> Prop) : ((term1847 A B x'''''' _61771 _61773 _61772) = (term1847 A B x'''''' _61771 _61773 _61772)) = True.
Proof. exact (@lem4963316 (term1847 A B x'''''' _61771 _61773 _61772)). Qed.
Lemma lem4963318 {A B : Type'} (x'''''' : type1448 A B) (_61771 : B) (_61773 : A -> B) (_61772 : A -> Prop) : ((term1796 A B x'''''' _61771 _61772 _61773) = (term1847 A B x'''''' _61771 _61773 _61772)) = True.
Proof. exact (TRANS (@lem4963313 A B x'''''' _61771 _61773 _61772) (@lem4963317 A B x'''''' _61771 _61773 _61772)). Qed.
Lemma lem4963319 {A B : Type'} (x'''''' : type1448 A B) (_61771 : B) (_61773 : A -> B) (_61772 : A -> Prop) : True = ((term1796 A B x'''''' _61771 _61772 _61773) = (term1847 A B x'''''' _61771 _61773 _61772)).
Proof. exact (SYM (@lem4963318 A B x'''''' _61771 _61773 _61772)). Qed.
Lemma lem4963320 {A B : Type'} (x'''''' : type1448 A B) (_61771 : B) (_61773 : A -> B) (_61772 : A -> Prop) : (term1796 A B x'''''' _61771 _61772 _61773) = (term1847 A B x'''''' _61771 _61773 _61772).
Proof. exact (EQ_MP (@lem4963319 A B x'''''' _61771 _61773 _61772) (@lem0)). Qed.
Lemma lem4963321 {A B : Type'} (_61771 : B) (_61773 : A -> B) (_61772 : A -> Prop) (x'''''' : type1448 A B) (h1 : term912 A B x'''''') : term1847 A B x'''''' _61771 _61773 _61772.
Proof. exact (EQ_MP (@lem4963320 A B x'''''' _61771 _61773 _61772) (@lem4961041 A B _61771 _61772 _61773 x'''''' h1)). Qed.
Lemma lem4963323 (b : Prop) (a : Prop) : (a \/ b) = (term1817 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4963324 {A B : Type'} (x'''''' : type1448 A B) (_61771 : B) (_61772 : A -> Prop) (_61773 : A -> B) : (term1847 A B x'''''' _61771 _61773 _61772) = (term1850 A B x'''''' _61771 _61772 _61773).
Proof. exact (@lem4963323 (term1691 A B _61771 _61773 _61772) (_61771 = (term1682 A B x'''''' _61771 _61772 _61773))). Qed.
Lemma lem4963326 (a : Prop) : (term1823 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4963327 {A B : Type'} (_61771 : B) (_61773 : A -> B) (_61772 : A -> Prop) : (term1841 A B _61771 _61773 _61772) = (term1690 A B _61771 _61773 _61772).
Proof. exact (@lem4963326 (term1690 A B _61771 _61773 _61772)). Qed.
Lemma lem4963328 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4963329 {A B : Type'} (_61771 : B) (_61773 : A -> B) (_61772 : A -> Prop) : (term1842 A B _61771 _61773 _61772) = (term1843 A B _61771 _61773 _61772).
Proof. exact (MK_COMB (@lem4963328) (@lem4963327 A B _61771 _61773 _61772)). Qed.
Lemma lem4963330 {A B : Type'} (x'''''' : type1448 A B) (_61771 : B) (_61772 : A -> Prop) (_61773 : A -> B) : (_61771 = (term1682 A B x'''''' _61771 _61772 _61773)) = (_61771 = (term1682 A B x'''''' _61771 _61772 _61773)).
Proof. exact (eq_refl (_61771 = (term1682 A B x'''''' _61771 _61772 _61773))). Qed.
Lemma lem4963331 {A B : Type'} (x'''''' : type1448 A B) (_61771 : B) (_61772 : A -> Prop) (_61773 : A -> B) : (term1850 A B x'''''' _61771 _61772 _61773) = (term1851 A B x'''''' _61771 _61772 _61773).
Proof. exact (MK_COMB (@lem4963329 A B _61771 _61773 _61772) (@lem4963330 A B x'''''' _61771 _61772 _61773)). Qed.
Lemma lem4963332 {A B : Type'} (x'''''' : type1448 A B) (_61771 : B) (_61772 : A -> Prop) (_61773 : A -> B) : (term1847 A B x'''''' _61771 _61773 _61772) = (term1851 A B x'''''' _61771 _61772 _61773).
Proof. exact (TRANS (@lem4963324 A B x'''''' _61771 _61772 _61773) (@lem4963331 A B x'''''' _61771 _61772 _61773)). Qed.
Lemma lem4963335 {A B : Type'} (_61771 : B) (_61772 : A -> Prop) (_61773 : A -> B) (x'''''' : type1448 A B) (h1 : term912 A B x'''''') : term1851 A B x'''''' _61771 _61772 _61773.
Proof. exact (EQ_MP (@lem4963332 A B x'''''' _61771 _61772 _61773) (@lem4963321 A B _61771 _61773 _61772 x'''''' h1)). Qed.
Lemma lem4963336 {A B : Type'} (_61771 : B) (_61772 : A -> Prop) (_61773 : A -> B) (x'''''' : type1448 A B) (h1 : term912 A B x'''''') : term1851 A B x'''''' _61771 _61772 _61773.
Proof. exact (@lem4963335 A B _61771 _61772 _61773 x'''''' h1). Qed.
Lemma lem4963337 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) (x'''''' : type1448 A B) (h1 : term912 A B x'''''') : term1851 A B x'''''' y s f.
Proof. exact (@lem4963336 A B y s f x'''''' h1). Qed.
Lemma lem4963340 {A B : Type'} (x'''''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) (x''''''''' : A) (y' : A) (h1 : term912 A B x'''''') (h2 : term1743 A B y s f x''''''''' y') : y = (term1682 A B x'''''' y s f).
Proof. exact (@lem4963337 A B y s f x'''''' h1 (@lem4963288 A B y s f x''''''''' y' h2)). Qed.
Lemma lem4963341 {A B : Type'} (x'''''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) (x''''''''' : A) (y' : A) (h1 : term912 A B x'''''') (h2 : term1743 A B y s f x''''''''' y') : term1852 A B x'''''' y s f.
Proof. exact (fun h0 : term1853 A B x'''''' y s f => @lem4963340 A B x'''''' y s f x''''''''' y' h1 h2). Qed.
Lemma lem4963343 (p : Prop) : (term1799 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4963344 {A B : Type'} (x'''''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) : (term1852 A B x'''''' y s f) = (y = (term1682 A B x'''''' y s f)).
Proof. exact (@lem4963343 (y = (term1682 A B x'''''' y s f))). Qed.
Lemma lem4963345 {A B : Type'} (x'''''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) (x''''''''' : A) (y' : A) (h1 : term912 A B x'''''') (h2 : term1743 A B y s f x''''''''' y') : y = (term1682 A B x'''''' y s f).
Proof. exact (EQ_MP (@lem4963344 A B x'''''' y s f) (@lem4963341 A B x'''''' y s f x''''''''' y' h1 h2)). Qed.
Lemma lem4963347 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem4963348 {B : Type'} (x : B) : x = x.
Proof. exact (@lem4963347 B x). Qed.
Lemma lem4963349 {B : Type'} (y : B) : y = y.
Proof. exact (@lem4963348 B y). Qed.
Lemma lem4963350 {B : Type'} (y : B) : term1854 B y.
Proof. exact (fun h0 : term1855 B y => @lem4963349 B y). Qed.
Lemma lem4963352 (p : Prop) : (term1799 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4963353 {B : Type'} (y : B) : (term1854 B y) = (y = y).
Proof. exact (@lem4963352 (y = y)). Qed.
Lemma lem4963354 {B : Type'} (y : B) : y = y.
Proof. exact (EQ_MP (@lem4963353 B y) (@lem4963350 B y)). Qed.
Lemma lem4963372 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4963373 {B : Type'} (y : B) (x : B) (z : B) : (term1856 B x y z) = (term1857 B y x z).
Proof. exact (@lem4963372 (y = z) (term1724 B x z)). Qed.
Lemma lem4963383 {B : Type'} (x : B) (y : B) : (term1858 B x y) = (term1858 B x y).
Proof. exact (eq_refl (term1858 B x y)). Qed.
Lemma lem4963384 {B : Type'} (y : B) (x : B) (z : B) : (term1835 B x y z) = (term1859 B y x z).
Proof. exact (MK_COMB (@lem4963383 B x y) (@lem4963373 B y x z)). Qed.
Lemma lem4963388 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4963389 {B : Type'} (y : B) (x : B) (z : B) : (term1859 B y x z) = (term1860 B y x z).
Proof. exact (@lem4963388 (y = z) (term1724 B x y) (term1724 B x z)). Qed.
Lemma lem4963411 {B : Type'} (y : B) (x : B) (z : B) : (term1835 B x y z) = (term1860 B y x z).
Proof. exact (TRANS (@lem4963384 B y x z) (@lem4963389 B y x z)). Qed.
Lemma lem4963412 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4963413 {B : Type'} (y : B) (x : B) (z : B) : (term1861 B x y z) = (term1862 B y x z).
Proof. exact (MK_COMB (@lem4963412) (@lem4963411 B y x z)). Qed.
Lemma lem4963435 {B : Type'} (y : B) (x : B) (z : B) : (term1860 B y x z) = (term1860 B y x z).
Proof. exact (eq_refl (term1860 B y x z)). Qed.
Lemma lem4963436 {B : Type'} (y : B) (x : B) (z : B) : ((term1835 B x y z) = (term1860 B y x z)) = ((term1860 B y x z) = (term1860 B y x z)).
Proof. exact (MK_COMB (@lem4963413 B y x z) (@lem4963435 B y x z)). Qed.
Lemma lem4963438 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4963439 (x : Prop) : (x = x) = True.
Proof. exact (@lem4963438 Prop x). Qed.
Lemma lem4963440 {B : Type'} (y : B) (x : B) (z : B) : ((term1860 B y x z) = (term1860 B y x z)) = True.
Proof. exact (@lem4963439 (term1860 B y x z)). Qed.
Lemma lem4963441 {B : Type'} (y : B) (x : B) (z : B) : ((term1835 B x y z) = (term1860 B y x z)) = True.
Proof. exact (TRANS (@lem4963436 B y x z) (@lem4963440 B y x z)). Qed.
Lemma lem4963442 {B : Type'} (y : B) (x : B) (z : B) : True = ((term1835 B x y z) = (term1860 B y x z)).
Proof. exact (SYM (@lem4963441 B y x z)). Qed.
Lemma lem4963443 {B : Type'} (y : B) (x : B) (z : B) : (term1835 B x y z) = (term1860 B y x z).
Proof. exact (EQ_MP (@lem4963442 B y x z) (@lem0)). Qed.
Lemma lem4963444 {B : Type'} (y : B) (x : B) (z : B) : term1860 B y x z.
Proof. exact (EQ_MP (@lem4963443 B y x z) (@lem4963113 B x y z)). Qed.
Lemma lem4963446 (b : Prop) (a : Prop) : (a \/ b) = (term1817 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4963447 {B : Type'} (x : B) (y : B) (z : B) : (term1860 B y x z) = (term1863 B x y z).
Proof. exact (@lem4963446 (term1864 B y x z) (y = z)). Qed.
Lemma lem4963449 (a : Prop) (b : Prop) : (term1819 a b) = (term1820 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4963450 {B : Type'} (y : B) (x : B) (z : B) : (term1865 B y x z) = (term1866 B y x z).
Proof. exact (@lem4963449 (term1724 B x y) (term1724 B x z)). Qed.
Lemma lem4963452 (a : Prop) : (term1823 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4963453 {B : Type'} (x : B) (y : B) : (term1867 B x y) = (x = y).
Proof. exact (@lem4963452 (x = y)). Qed.
Lemma lem4963454 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4963455 {B : Type'} (x : B) (y : B) : (term1868 B x y) = (term1869 B x y).
Proof. exact (MK_COMB (@lem4963454) (@lem4963453 B x y)). Qed.
Lemma lem4963457 (a : Prop) : (term1823 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4963458 {B : Type'} (x : B) (z : B) : (term1867 B x z) = (x = z).
Proof. exact (@lem4963457 (x = z)). Qed.
Lemma lem4963459 {B : Type'} (y : B) (x : B) (z : B) : (term1866 B y x z) = (term1870 B y x z).
Proof. exact (MK_COMB (@lem4963455 B x y) (@lem4963458 B x z)). Qed.
Lemma lem4963460 {B : Type'} (y : B) (x : B) (z : B) : (term1865 B y x z) = (term1870 B y x z).
Proof. exact (TRANS (@lem4963450 B y x z) (@lem4963459 B y x z)). Qed.
Lemma lem4963461 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4963462 {B : Type'} (y : B) (x : B) (z : B) : (term1871 B y x z) = (term1872 B y x z).
Proof. exact (MK_COMB (@lem4963461) (@lem4963460 B y x z)). Qed.
Lemma lem4963463 {B : Type'} (y : B) (z : B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem4963464 {B : Type'} (x : B) (y : B) (z : B) : (term1863 B x y z) = (term1873 B x y z).
Proof. exact (MK_COMB (@lem4963462 B y x z) (@lem4963463 B y z)). Qed.
Lemma lem4963465 {B : Type'} (x : B) (y : B) (z : B) : (term1860 B y x z) = (term1873 B x y z).
Proof. exact (TRANS (@lem4963447 B x y z) (@lem4963464 B x y z)). Qed.
Lemma lem4963467 {A B : Type'} (x'''''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) (x''''''''' : A) (y' : A) (h1 : term912 A B x'''''') (h2 : term1743 A B y s f x''''''''' y') : term1874 A B x'''''' s f y.
Proof. exact (conj (@lem4963345 A B x'''''' y s f x''''''''' y' h1 h2) (@lem4963354 B y)). Qed.
Lemma lem4963469 {B : Type'} (x : B) (y : B) (z : B) : term1873 B x y z.
Proof. exact (EQ_MP (@lem4963465 B x y z) (@lem4963444 B y x z)). Qed.
Lemma lem4963470 {B : Type'} (x : B) (y : B) (z : B) : term1873 B x y z.
Proof. exact (@lem4963469 B x y z). Qed.
Lemma lem4963471 {A B : Type'} (x'''''' : type1448 A B) (s : A -> Prop) (f : A -> B) (y : B) : term1875 A B x'''''' s f y.
Proof. exact (@lem4963470 B y (term1682 A B x'''''' y s f) y). Qed.
Lemma lem4963474 {A B : Type'} (x'''''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) (x''''''''' : A) (y' : A) (h1 : term912 A B x'''''') (h2 : term1743 A B y s f x''''''''' y') : (term1682 A B x'''''' y s f) = y.
Proof. exact (@lem4963471 A B x'''''' s f y (@lem4963467 A B x'''''' y s f x''''''''' y' h1 h2)). Qed.
Lemma lem4963475 {A B : Type'} (x'''''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) (x''''''''' : A) (y' : A) (h1 : term912 A B x'''''') (h2 : term1743 A B y s f x''''''''' y') : term1876 A B x'''''' s f y.
Proof. exact (fun h0 : term1877 A B x'''''' s f y => @lem4963474 A B x'''''' y s f x''''''''' y' h1 h2). Qed.
Lemma lem4963477 (p : Prop) : (term1799 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4963478 {A B : Type'} (x'''''' : type1448 A B) (s : A -> Prop) (f : A -> B) (y : B) : (term1876 A B x'''''' s f y) = ((term1682 A B x'''''' y s f) = y).
Proof. exact (@lem4963477 ((term1682 A B x'''''' y s f) = y)). Qed.
Lemma lem4963479 {A B : Type'} (x'''''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) (x''''''''' : A) (y' : A) (h1 : term912 A B x'''''') (h2 : term1743 A B y s f x''''''''' y') : (term1682 A B x'''''' y s f) = y.
Proof. exact (EQ_MP (@lem4963478 A B x'''''' s f y) (@lem4963475 A B x'''''' y s f x''''''''' y' h1 h2)). Qed.
Lemma lem4963481 (a : Prop) (b : Prop) : (term1878 a b) = (term1879 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4963482 {A B : Type'} (s : A -> Prop) (f : A -> B) (_61812 : A) (y : B) : (term1737 A B s f _61812 y) = (term1880 A B s f _61812 y).
Proof. exact (@lem4963481 (term1704 A _61812 s) ((@I (A -> B) f _61812) = y)). Qed.
Lemma lem4963484 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4963485 {A B : Type'} (s : A -> Prop) (f : A -> B) (_61812 : A) (y : B) : (term1880 A B s f _61812 y) = (term1881 A B s f _61812 y).
Proof. exact (@lem4963484 (term1882 A B s f _61812 y)). Qed.
Lemma lem4963486 {A B : Type'} (s : A -> Prop) (f : A -> B) (_61812 : A) (y : B) : (term1737 A B s f _61812 y) = (term1881 A B s f _61812 y).
Proof. exact (TRANS (@lem4963482 A B s f _61812 y) (@lem4963485 A B s f _61812 y)). Qed.
Lemma lem4963488 {A B : Type'} (x'''''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) (x''''''''' : A) (y' : A) (h1 : term912 A B x'''''') (h2 : term1743 A B y s f x''''''''' y') : term1883 A B x'''''' s f y.
Proof. exact (conj (@lem4963281 A B x'''''' y s f x''''''''' y' h1 h2) (@lem4963479 A B x'''''' y s f x''''''''' y' h1 h2)). Qed.
Lemma lem4963490 {A B : Type'} (_61812 : A) (y : B) (s : A -> Prop) (f : A -> B) (x''''''''' : A) (y' : A) (h1 : term1743 A B y s f x''''''''' y') : term1881 A B s f _61812 y.
Proof. exact (EQ_MP (@lem4963486 A B s f _61812 y) (@lem4960803 A B _61812 y s f x''''''''' y' h1)). Qed.
Lemma lem4963491 {A B : Type'} (_61812 : A) (y : B) (s : A -> Prop) (f : A -> B) (x''''''''' : A) (y' : A) (h1 : term1743 A B y s f x''''''''' y') : term1881 A B s f _61812 y.
Proof. exact (@lem4963490 A B _61812 y s f x''''''''' y' h1). Qed.
Lemma lem4963492 {A B : Type'} (x'''''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) (x''''''''' : A) (y' : A) (h1 : term1743 A B y s f x''''''''' y') : term1884 A B x'''''' s f y.
Proof. exact (@lem4963491 A B (term1672 A B x'''''' y s f) y s f x''''''''' y' h1). Qed.
Lemma lem4963495 {A B : Type'} (x'''''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) (x''''''''' : A) (y' : A) (h1 : term912 A B x'''''') (h2 : term1743 A B y s f x''''''''' y') : False.
Proof. exact (@lem4963492 A B x'''''' y s f x''''''''' y' h2 (@lem4963488 A B x'''''' y s f x''''''''' y' h1 h2)). Qed.
Lemma lem4963496 {A B : Type'} (x'''''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) (x''''''''' : A) (y' : A) (h1 : term912 A B x'''''') (h2 : term1743 A B y s f x''''''''' y') : term1834.
Proof. exact (fun h0 : ~ False => @lem4963495 A B x'''''' y s f x''''''''' y' h1 h2). Qed.
Lemma lem4963498 (p : Prop) : (term1799 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4963499 : term1834 = False.
Proof. exact (@lem4963498 False). Qed.
Lemma lem4963501 {A B : Type'} (x'''''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) (x''''''''' : A) (y' : A) (h1 : term912 A B x'''''') (h2 : term1743 A B y s f x''''''''' y') : False.
Proof. exact (EQ_MP (@lem4963499) (@lem4963496 A B x'''''' y s f x''''''''' y' h1 h2)). Qed.
Lemma lem4963502 {A B : Type'} (x'''''''' : B -> A) (y : B) (x''''''''' : A) (y' : A) (s : A -> Prop) (f : A -> B) (x'''''''''' : A) (y'' : A) (h1 : term1774 A B x'''''''' s f) (h2 : term516 A B x'''''''' y x''''''''' y' s f x'''''''''' y'') : False.
Proof. exact (EQ_MP (@lem4962304) (@lem4962301 A B x'''''''' y x''''''''' y' s f x'''''''''' y'' h1 h2)). Qed.
Lemma lem4963503 {A B : Type'} (x'''''' : type1448 A B) (x'''''''' : B -> A) (y : B) (x''''''''' : A) (y' : A) (s : A -> Prop) (f : A -> B) (x'''''''''' : A) (y'' : A) (h1 : term912 A B x'''''') (h2 : term516 A B x'''''''' y x''''''''' y' s f x'''''''''' y'') : False.
Proof. exact (or_elim (@lem4957435 A B x'''''''' y x''''''''' y' s f x'''''''''' y'' h2) (fun h0 : term1774 A B x'''''''' s f => @lem4963502 A B x'''''''' y x''''''''' y' s f x'''''''''' y'' h0 h2) (fun h0 : term1743 A B y s f x''''''''' y' => @lem4963501 A B x'''''' y s f x''''''''' y' h1 h0)). Qed.
Lemma lem4963504 {A B : Type'} (x'''''''' : B -> A) (y : B) (x''''''''' : A) (y' : A) (s : A -> Prop) (f : A -> B) (x'''''''''' : A) (x'''''' : type1448 A B) (h1 : term519 A B x'''''''' y x''''''''' y' s f x'''''''''') (h2 : term912 A B x'''''') : False.
Proof. exact (ex_elim (@lem4955159 A B x'''''''' y x''''''''' y' s f x'''''''''' h1) (fun y'' : A => fun h0 : term518 A B x'''''''' y x''''''''' y' s f x'''''''''' y'' => @lem4963503 A B x'''''' x'''''''' y x''''''''' y' s f x'''''''''' y'' h2 h0)). Qed.
Lemma lem4963505 {A B : Type'} (x'''''''' : B -> A) (y : B) (x''''''''' : A) (y' : A) (s : A -> Prop) (f : A -> B) (x'''''' : type1448 A B) (h1 : term521 A B x'''''''' y x''''''''' y' s f) (h2 : term912 A B x'''''') : False.
Proof. exact (ex_elim (@lem4955158 A B x'''''''' y x''''''''' y' s f h1) (fun x'''''''''' : A => fun h0 : term520 A B x'''''''' y x''''''''' y' s f x'''''''''' => @lem4963504 A B x'''''''' y x''''''''' y' s f x'''''''''' x'''''' h0 h2)). Qed.
Lemma lem4963506 {A B : Type'} (x'''''''' : B -> A) (y : B) (x''''''''' : A) (s : A -> Prop) (f : A -> B) (x'''''' : type1448 A B) (h1 : term523 A B x'''''''' y x''''''''' s f) (h2 : term912 A B x'''''') : False.
Proof. exact (ex_elim (@lem4955157 A B x'''''''' y x''''''''' s f h1) (fun y' : A => fun h0 : term522 A B x'''''''' y x''''''''' s f y' => @lem4963505 A B x'''''''' y x''''''''' y' s f x'''''' h0 h2)). Qed.
Lemma lem4963507 {A B : Type'} (x'''''''' : B -> A) (y : B) (s : A -> Prop) (f : A -> B) (x'''''' : type1448 A B) (h1 : term525 A B x'''''''' y s f) (h2 : term912 A B x'''''') : False.
Proof. exact (ex_elim (@lem4955156 A B x'''''''' y s f h1) (fun x''''''''' : A => fun h0 : term524 A B x'''''''' y s f x''''''''' => @lem4963506 A B x'''''''' y x''''''''' s f x'''''' h0 h2)). Qed.
Lemma lem4963508 {A B : Type'} (x'''''''' : B -> A) (s : A -> Prop) (f : A -> B) (x'''''' : type1448 A B) (h1 : term527 A B x'''''''' s f) (h2 : term912 A B x'''''') : False.
Proof. exact (ex_elim (@lem4955155 A B x'''''''' s f h1) (fun y : B => fun h0 : term526 A B x'''''''' s f y => @lem4963507 A B x'''''''' y s f x'''''' h0 h2)). Qed.
Lemma lem4963509 {A B : Type'} (s : A -> Prop) (f : A -> B) (x'''''' : type1448 A B) (h1 : term81 A B s f) (h2 : term912 A B x'''''') : False.
Proof. exact (ex_elim (@lem4948172 A B s f h1) (fun x'''''''' : B -> A => fun h0 : term528 A B s f x'''''''' => @lem4963508 A B x'''''''' s f x'''''' h0 h2)). Qed.
Lemma lem4963510 {A B : Type'} (s : A -> Prop) (f : A -> B) (x'''''' : type1448 A B) (h1 : term84 A) (h2 : term81 A B s f) (h3 : term912 A B x'''''') : False.
Proof. exact (ex_elim (@lem4949064 A h1) (fun x''''''' : type1361 A => fun h0 : term724 A x''''''' => @lem4963509 A B s f x'''''' h2 h3)). Qed.
Lemma lem4963511 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term84 A) (h2 : term83 A B) (h3 : term81 A B s f) : False.
Proof. exact (ex_elim (@lem4949956 A B h2) (fun x'''''' : type1448 A B => fun h0 : term914 A B x'''''' => @lem4963510 A B s f x'''''' h1 h3 h0)). Qed.
Lemma lem4963512 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term84 A) (h2 : term83 A B) (h3 : term84 B) (h4 : term81 A B s f) : False.
Proof. exact (ex_elim (@lem4950848 B h3) (fun x''''' : type1361 B => fun h0 : term724 B x''''' => @lem4963511 A B s f h1 h2 h4)). Qed.
Lemma lem4963513 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term84 A) (h2 : term83 A B) (h3 : term84 B) (h4 : term87 A) (h5 : term81 A B s f) : False.
Proof. exact (ex_elim (@lem4951740 A h4) (fun x'''' : type634 A => fun h0 : term1106 A x'''' => @lem4963512 A B s f h1 h2 h3 h5)). Qed.
Lemma lem4963514 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term84 A) (h2 : term83 A B) (h3 : term84 B) (h4 : term87 A) (h5 : term86 A B) (h6 : term81 A B s f) : False.
Proof. exact (ex_elim (@lem4952632 A B h5) (fun x''' : type833 A B => fun h0 : term1298 A B x''' => @lem4963513 A B s f h1 h2 h3 h4 h6)). Qed.
Lemma lem4963515 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term84 A) (h2 : term83 A B) (h3 : term84 B) (h4 : term87 A) (h5 : term86 A B) (h6 : term85 A) (h7 : term81 A B s f) : False.
Proof. exact (ex_elim (@lem4953524 A h6) (fun x'' : type1572 A => fun h0 : term1492 A x'' => @lem4963514 A B s f h1 h2 h3 h4 h5 h7)). Qed.
Lemma lem4963516 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term84 A) (h2 : term83 A B) (h3 : term84 B) (h4 : term87 A) (h5 : term82 A) (h6 : term86 A B) (h7 : term85 A) (h8 : term81 A B s f) : False.
Proof. exact (ex_elim (@lem4954335 A h5) (fun x' : type638 A => fun h0 : term1668 A x' => @lem4963515 A B s f h1 h2 h3 h4 h6 h7 h8)). Qed.
Lemma lem4963517 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term84 A) (h2 : term83 A B) (h3 : term84 B) (h4 : term87 A) (h5 : term82 A) (h6 : term86 A B) (h7 : term82 B) (h8 : term85 A) (h9 : term81 A B s f) : False.
Proof. exact (ex_elim (@lem4955146 B h7) (fun x : type638 B => fun h0 : term1668 B x => @lem4963516 A B s f h1 h2 h3 h4 h5 h6 h8 h9)). Qed.
Lemma lem4963518 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term84 A) (h2 : term83 A B) (h3 : term84 B) (h4 : term87 A) (h5 : term82 A) (h6 : term86 A B) (h7 : term85 A) (h8 : term81 A B s f) : term92 B.
Proof. exact (fun h0 : term82 B => @lem4963517 A B s f h1 h2 h3 h4 h5 h6 h0 h7 h8). Qed.
Lemma lem4963519 {B : Type'} : (term92 B) = (term93 B).
Proof. exact (@lem69 (term82 B)). Qed.
Lemma lem4963520 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term84 A) (h2 : term83 A B) (h3 : term84 B) (h4 : term87 A) (h5 : term82 A) (h6 : term86 A B) (h7 : term85 A) (h8 : term81 A B s f) : term93 B.
Proof. exact (EQ_MP (@lem4963519 B) (@lem4963518 A B s f h1 h2 h3 h4 h5 h6 h7 h8)). Qed.
Lemma lem4963521 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term84 A) (h2 : term83 A B) (h3 : term84 B) (h4 : term87 A) (h5 : term86 A B) (h6 : term85 A) (h7 : term81 A B s f) : term96 A B.
Proof. exact (fun h0 : term82 A => @lem4963520 A B s f h1 h2 h3 h4 h0 h5 h6 h7). Qed.
Lemma lem4963522 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term84 A) (h2 : term83 A B) (h3 : term84 B) (h4 : term87 A) (h5 : term86 A B) (h6 : term81 A B s f) : term99 A B.
Proof. exact (fun h0 : term85 A => @lem4963521 A B s f h1 h2 h3 h4 h5 h0 h6). Qed.
Lemma lem4963523 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term84 A) (h2 : term83 A B) (h3 : term84 B) (h4 : term87 A) (h5 : term81 A B s f) : term102 A B.
Proof. exact (fun h0 : term86 A B => @lem4963522 A B s f h1 h2 h3 h4 h0 h5). Qed.
Lemma lem4963524 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term84 A) (h2 : term83 A B) (h3 : term84 B) (h4 : term81 A B s f) : term105 A B.
Proof. exact (fun h0 : term87 A => @lem4963523 A B s f h1 h2 h3 h0 h4). Qed.
Lemma lem4963525 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term84 A) (h2 : term83 A B) (h3 : term81 A B s f) : term108 A B.
Proof. exact (fun h0 : term84 B => @lem4963524 A B s f h1 h2 h0 h3). Qed.
Lemma lem4963526 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term84 A) (h2 : term81 A B s f) : term111 A B.
Proof. exact (fun h0 : term83 A B => @lem4963525 A B s f h1 h0 h2). Qed.
Lemma lem4963527 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term81 A B s f) : term113 A B.
Proof. exact (fun h0 : term84 A => @lem4963526 A B s f h0 h1). Qed.
Lemma lem4963528 {A B : Type'} (s : A -> Prop) (f : A -> B) : term116 A B s f.
Proof. exact (fun h0 : term81 A B s f => @lem4963527 A B s f h0). Qed.
Lemma lem4963529 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : term118 A B t s f.
Proof. exact (fun h0 : term20 A B t f s => @lem4963528 A B s f). Qed.
Lemma lem4963534 {A B : Type'} (s : A -> Prop) (f : A -> B) : term122 A B s f.
Proof. exact (fun t : B -> Prop => @lem4963529 A B t s f). Qed.
Lemma lem4963539 {A B : Type'} (f : A -> B) : term126 A B f.
Proof. exact (fun s : A -> Prop => @lem4963534 A B s f). Qed.
Lemma lem4963544 {A B : Type'} : term130 A B.
Proof. exact (fun f : A -> B => @lem4963539 A B f). Qed.
Lemma lem4963545 {A B : Type'} : term129 A B.
Proof. exact (EQ_MP (@lem4947217 A B) (@lem4963544 A B)). Qed.
Lemma lem4963546 {A B : Type'} (f : A -> B) : term1885 A B f.
Proof. exact (@lem4963545 A B f). Qed.
Lemma lem4963547 {A B : Type'} (f : A -> B) : (term1885 A B f) = (term125 A B f).
Proof. exact (eq_refl (term1885 A B f)). Qed.
Lemma lem4963548 {A B : Type'} (f : A -> B) : term125 A B f.
Proof. exact (EQ_MP (@lem4963547 A B f) (@lem4963546 A B f)). Qed.
Lemma lem4963549 {A B : Type'} (f : A -> B) (s : A -> Prop) : term1886 A B f s.
Proof. exact (@lem4963548 A B f s). Qed.
Lemma lem4963550 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term1886 A B f s) = (term121 A B s f).
Proof. exact (eq_refl (term1886 A B f s)). Qed.
Lemma lem4963551 {A B : Type'} (s : A -> Prop) (f : A -> B) : term121 A B s f.
Proof. exact (EQ_MP (@lem4963550 A B s f) (@lem4963549 A B f s)). Qed.
Lemma lem4963552 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : term1887 A B s f t.
Proof. exact (@lem4963551 A B s f t). Qed.
Lemma lem4963553 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term1887 A B s f t) = (term88 A B t s f).
Proof. exact (eq_refl (term1887 A B s f t)). Qed.
Lemma lem4963554 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : term88 A B t s f.
Proof. exact (EQ_MP (@lem4963553 A B t s f) (@lem4963552 A B s f t)). Qed.
Lemma lem4963556 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : term88 A B t s f.
Proof. exact (@lem4946077 A B t s f (@lem4963554 A B t s f)). Qed.
Lemma lem4963557 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : term115 A B s f.
Proof. exact (@lem4963556 A B t s f (@lem4945067 A B f s t h1)). Qed.
Lemma lem4963558 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term81 A B s f) (h2 : term14 A B f s t) : term112 A B.
Proof. exact (@lem4963557 A B f s t h2 (@lem4946048 A B s f h1)). Qed.
Lemma lem4963559 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term81 A B s f) (h2 : term14 A B f s t) : term110 A B.
Proof. exact (@lem4963558 A B f s t h1 h2 (@lem4946053 A)). Qed.
Lemma lem4963560 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term81 A B s f) (h2 : term14 A B f s t) : term107 A B.
Proof. exact (@lem4963559 A B f s t h1 h2 (@lem4946052 A B)). Qed.
Lemma lem4963561 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term81 A B s f) (h2 : term14 A B f s t) : term104 A B.
Proof. exact (@lem4963560 A B f s t h1 h2 (@lem4946060 B)). Qed.
Lemma lem4963562 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term81 A B s f) (h2 : term14 A B f s t) : term101 A B.
Proof. exact (@lem4963561 A B f s t h1 h2 (@lem4946059 A)). Qed.
Lemma lem4963563 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term81 A B s f) (h2 : term14 A B f s t) : term98 A B.
Proof. exact (@lem4963562 A B f s t h1 h2 (@lem4946056 A B)). Qed.
Lemma lem4963564 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term81 A B s f) (h2 : term14 A B f s t) : term95 A B.
Proof. exact (@lem4963563 A B f s t h1 h2 (@lem4946055 A)). Qed.
Lemma lem4963565 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term81 A B s f) (h2 : term14 A B f s t) : term92 B.
Proof. exact (@lem4963564 A B f s t h1 h2 (@lem4946051 A)). Qed.
Lemma lem4963566 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term81 A B s f) (h2 : term14 A B f s t) : False.
Proof. exact (@lem4963565 A B f s t h1 h2 (@lem4946049 B)). Qed.
Lemma lem4963567 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term81 A B s f) (h2 : term14 A B f s t) : (term81 A B s f) = False.
Proof. exact (prop_ext (fun h3 : term81 A B s f => @lem4963566 A B f s t h1 h2) (fun h3 : False => @lem4946048 A B s f h1)). Qed.
Lemma lem4963568 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term81 A B s f) (h2 : term14 A B f s t) : False.
Proof. exact (EQ_MP (@lem4963567 A B f s t h1 h2) (@lem4946048 A B s f h1)). Qed.
Lemma lem4963569 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : term80 A B s f.
Proof. exact (fun h0 : term81 A B s f => @lem4963568 A B f s t h0 h1). Qed.
Lemma lem4963570 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : term78 A B s f.
Proof. exact (EQ_MP (@lem4946047 A B s f) (@lem4963569 A B f s t h1)). Qed.
Lemma lem4963571 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : term77 A B t s f.
Proof. exact (EQ_MP (@lem4946043 A B f s t h1) (@lem4963570 A B f s t h1)). Qed.
Lemma lem4963572 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B f s t) : term31 A B s f.
Proof. exact (@lem4963571 A B f s t h1 (@lem4945047 A B t s f)). Qed.
Lemma lem4963573 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : term1888 A B t s f.
Proof. exact (fun h0 : term14 A B f s t => @lem4963572 A B f s t h0). Qed.
Lemma lem4963578 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term1889 A B t s.
Proof. exact (fun f : A -> B => @lem4963573 A B t s f). Qed.
Lemma lem4963583 {A B : Type'} (s : A -> Prop) : term1890 A B s.
Proof. exact (fun t : B -> Prop => @lem4963578 A B t s). Qed.
Lemma lem4963588 {A B : Type'} : term1891 A B.
Proof. exact (fun s : A -> Prop => @lem4963583 A B s). Qed.
