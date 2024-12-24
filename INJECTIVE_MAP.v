Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INJECTIVE_MAP_term_abbrevs.
Require Import CONS_11_spec.
Require Import DISJ_ACI_spec.
Require Import NOT_CONS_NIL_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1097797_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm1804_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm32_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem1190073 {A B : Type'} (f : A -> B) (h1 : term0 A B f) : term0 A B f.
Proof. exact (h1). Qed.
Lemma lem1190074 {A B : Type'} (f : A -> B) (h1 : term1 A B f) : term1 A B f.
Proof. exact (h1). Qed.
Lemma lem1190076 {A B : Type'} (x : A) (f : A -> B) (h1 : term0 A B f) : term2 A B f x.
Proof. exact (@lem1190073 A B f h1 (@cons A x (@nil A))). Qed.
Lemma lem1190077 {A B : Type'} (f : A -> B) (x : A) : (term2 A B f x) = (term3 A B f x).
Proof. exact (eq_refl (term2 A B f x)). Qed.
Lemma lem1190078 {A B : Type'} (x : A) (f : A -> B) (h1 : term0 A B f) : term3 A B f x.
Proof. exact (EQ_MP (@lem1190077 A B f x) (@lem1190076 A B x f h1)). Qed.
Lemma lem1190079 {A B : Type'} (x : A) (y : A) (f : A -> B) (h1 : term0 A B f) : term4 A B f x y.
Proof. exact (@lem1190078 A B x f h1 (@cons A y (@nil A))). Qed.
Lemma lem1190080 {A B : Type'} (f : A -> B) (x : A) (y : A) : (term4 A B f x y) = (term5 A B f x y).
Proof. exact (eq_refl (term4 A B f x y)). Qed.
Lemma lem1190081 {A B : Type'} (x : A) (y : A) (f : A -> B) (h1 : term0 A B f) : term5 A B f x y.
Proof. exact (EQ_MP (@lem1190080 A B f x y) (@lem1190079 A B x y f h1)). Qed.
Lemma lem1190082 {A : Type'} (h1' : A) : term6 A h1'.
Proof. exact (@lem1113436 A h1'). Qed.
Lemma lem1190083 {A : Type'} (h1' : A) : (term6 A h1') = (term7 A h1').
Proof. exact (eq_refl (term6 A h1')). Qed.
Lemma lem1190084 {A : Type'} (h1' : A) : term7 A h1'.
Proof. exact (EQ_MP (@lem1190083 A h1') (@lem1190082 A h1')). Qed.
Lemma lem1190085 {A : Type'} (h1' : A) (h2' : A) : term8 A h1' h2'.
Proof. exact (@lem1190084 A h1' h2'). Qed.
Lemma lem1190086 {A : Type'} (h1' : A) (h2' : A) : (term8 A h1' h2') = (term9 A h1' h2').
Proof. exact (eq_refl (term8 A h1' h2')). Qed.
Lemma lem1190087 {A : Type'} (h1' : A) (h2' : A) : term9 A h1' h2'.
Proof. exact (EQ_MP (@lem1190086 A h1' h2') (@lem1190085 A h1' h2')). Qed.
Lemma lem1190088 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) : term10 A h1' h2' t1.
Proof. exact (@lem1190087 A h1' h2' t1). Qed.
Lemma lem1190089 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) : (term10 A h1' h2' t1) = (term11 A h1' h2' t1).
Proof. exact (eq_refl (term10 A h1' h2' t1)). Qed.
Lemma lem1190090 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) : term11 A h1' h2' t1.
Proof. exact (EQ_MP (@lem1190089 A h1' h2' t1) (@lem1190088 A h1' h2' t1)). Qed.
Lemma lem1190091 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) (t2 : list A) : term12 A h1' h2' t1 t2.
Proof. exact (@lem1190090 A h1' h2' t1 t2). Qed.
Lemma lem1190092 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) (t2 : list A) : (term12 A h1' h2' t1 t2) = (((@cons A h1' t1) = (@cons A h2' t2)) = (term13 A h1' h2' t1 t2)).
Proof. exact (eq_refl (term12 A h1' h2' t1 t2)). Qed.
Lemma lem1190094 {A B : Type'} : term14 A B.
Proof. exact (proj2 (@lem1097797 A B)). Qed.
Lemma lem1190095 {A B : Type'} (f : A -> B) : term15 A B f.
Proof. exact (@lem1190094 A B f). Qed.
Lemma lem1190096 {A B : Type'} (f : A -> B) : (term15 A B f) = (term16 A B f).
Proof. exact (eq_refl (term15 A B f)). Qed.
Lemma lem1190097 {A B : Type'} (f : A -> B) : term16 A B f.
Proof. exact (EQ_MP (@lem1190096 A B f) (@lem1190095 A B f)). Qed.
Lemma lem1190098 {A B : Type'} (f : A -> B) (h : A) : term17 A B f h.
Proof. exact (@lem1190097 A B f h). Qed.
Lemma lem1190099 {A B : Type'} (h : A) (f : A -> B) : (term17 A B f h) = (term18 A B h f).
Proof. exact (eq_refl (term17 A B f h)). Qed.
Lemma lem1190100 {A B : Type'} (h : A) (f : A -> B) : term18 A B h f.
Proof. exact (EQ_MP (@lem1190099 A B h f) (@lem1190098 A B f h)). Qed.
Lemma lem1190101 {A B : Type'} (h : A) (f : A -> B) (t : list A) : term19 A B h f t.
Proof. exact (@lem1190100 A B h f t). Qed.
Lemma lem1190102 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term19 A B h f t) = ((term20 A B f h t) = (term21 A B h f t)).
Proof. exact (eq_refl (term19 A B h f t)). Qed.
Lemma lem1190104 {A B : Type'} : term22 A B.
Proof. exact (proj1 (@lem1097797 A B)). Qed.
Lemma lem1190105 {A B : Type'} (f : A -> B) : term23 A B f.
Proof. exact (@lem1190104 A B f). Qed.
Lemma lem1190106 {A B : Type'} (f : A -> B) : (term23 A B f) = ((@List.map A B f (@nil A)) = (@nil B)).
Proof. exact (eq_refl (term23 A B f)). Qed.
Lemma lem1190117 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term20 A B f h t) = (term21 A B h f t).
Proof. exact (EQ_MP (@lem1190102 A B h f t) (@lem1190101 A B h f t)). Qed.
Lemma lem1190118 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term20 A B f h t) = (term21 A B h f t).
Proof. exact (@lem1190117 A B h f t). Qed.
Lemma lem1190119 {A B : Type'} (x : A) (f : A -> B) : (term24 A B f x) = (term25 A B x f).
Proof. exact (@lem1190118 A B x f (@nil A)). Qed.
Lemma lem1190121 {A B : Type'} (x : A) (f : A -> B) (y : A) (h1 : (f x) = (f y)) : (f x) = (f y).
Proof. exact (h1). Qed.
Lemma lem1190122 {B : Type'} : (@cons B) = (@cons B).
Proof. exact (eq_refl (@cons B)). Qed.
Lemma lem1190123 {A B : Type'} (x : A) (f : A -> B) (y : A) (h1 : (f x) = (f y)) : (term26 A B f x) = (term26 A B f y).
Proof. exact (MK_COMB (@lem1190122 B) (@lem1190121 A B x f y h1)). Qed.
Lemma lem1190125 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (@nil B).
Proof. exact (EQ_MP (@lem1190106 A B f) (@lem1190105 A B f)). Qed.
Lemma lem1190126 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (@nil B).
Proof. exact (@lem1190125 A B f). Qed.
Lemma lem1190127 {A B : Type'} (x : A) (f : A -> B) (y : A) (h1 : (f x) = (f y)) : (term25 A B x f) = (term27 A B f y).
Proof. exact (MK_COMB (@lem1190123 A B x f y h1) (@lem1190126 A B f)). Qed.
Lemma lem1190128 {A B : Type'} (x : A) (f : A -> B) (y : A) (h1 : (f x) = (f y)) : (term24 A B f x) = (term27 A B f y).
Proof. exact (TRANS (@lem1190119 A B x f) (@lem1190127 A B x f y h1)). Qed.
Lemma lem1190129 {B : Type'} : (@eq (list B)) = (@eq (list B)).
Proof. exact (eq_refl (@eq (list B))). Qed.
Lemma lem1190130 {A B : Type'} (x : A) (f : A -> B) (y : A) (h1 : (f x) = (f y)) : (term28 A B f x) = (term29 A B f y).
Proof. exact (MK_COMB (@lem1190129 B) (@lem1190128 A B x f y h1)). Qed.
Lemma lem1190132 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term20 A B f h t) = (term21 A B h f t).
Proof. exact (EQ_MP (@lem1190102 A B h f t) (@lem1190101 A B h f t)). Qed.
Lemma lem1190133 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term20 A B f h t) = (term21 A B h f t).
Proof. exact (@lem1190132 A B h f t). Qed.
Lemma lem1190134 {A B : Type'} (y : A) (f : A -> B) : (term24 A B f y) = (term25 A B y f).
Proof. exact (@lem1190133 A B y f (@nil A)). Qed.
Lemma lem1190136 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (@nil B).
Proof. exact (EQ_MP (@lem1190106 A B f) (@lem1190105 A B f)). Qed.
Lemma lem1190137 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (@nil B).
Proof. exact (@lem1190136 A B f). Qed.
Lemma lem1190138 {A B : Type'} (f : A -> B) (y : A) : (term26 A B f y) = (term26 A B f y).
Proof. exact (eq_refl (term26 A B f y)). Qed.
Lemma lem1190139 {A B : Type'} (f : A -> B) (y : A) : (term25 A B y f) = (term27 A B f y).
Proof. exact (MK_COMB (@lem1190138 A B f y) (@lem1190137 A B f)). Qed.
Lemma lem1190140 {A B : Type'} (f : A -> B) (y : A) : (term24 A B f y) = (term27 A B f y).
Proof. exact (TRANS (@lem1190134 A B y f) (@lem1190139 A B f y)). Qed.
Lemma lem1190141 {A B : Type'} (x : A) (f : A -> B) (y : A) (h1 : (f x) = (f y)) : ((term24 A B f x) = (term24 A B f y)) = ((term27 A B f y) = (term27 A B f y)).
Proof. exact (MK_COMB (@lem1190130 A B x f y h1) (@lem1190140 A B f y)). Qed.
Lemma lem1190143 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) (t2 : list A) : ((@cons A h1' t1) = (@cons A h2' t2)) = (term13 A h1' h2' t1 t2).
Proof. exact (EQ_MP (@lem1190092 A h1' h2' t1 t2) (@lem1190091 A h1' h2' t1 t2)). Qed.
Lemma lem1190144 {B : Type'} (h1' : B) (h2' : B) (t1 : list B) (t2 : list B) : ((@cons B h1' t1) = (@cons B h2' t2)) = (term13 B h1' h2' t1 t2).
Proof. exact (@lem1190143 B h1' h2' t1 t2). Qed.
Lemma lem1190145 {A B : Type'} (f : A -> B) (y : A) : ((term27 A B f y) = (term27 A B f y)) = (term30 A B f y).
Proof. exact (@lem1190144 B (f y) (f y) (@nil B) (@nil B)). Qed.
Lemma lem1190149 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1190150 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem1190149 B x). Qed.
Lemma lem1190151 {A B : Type'} (f : A -> B) (y : A) : ((f y) = (f y)) = True.
Proof. exact (@lem1190150 B (f y)). Qed.
Lemma lem1190152 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1190153 {A B : Type'} (f : A -> B) (y : A) : (term31 A B f y) = (and True).
Proof. exact (MK_COMB (@lem1190152) (@lem1190151 A B f y)). Qed.
Lemma lem1190155 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1190156 {B : Type'} (x : list B) : (x = x) = True.
Proof. exact (@lem1190155 (list B) x). Qed.
Lemma lem1190157 {B : Type'} : ((@nil B) = (@nil B)) = True.
Proof. exact (@lem1190156 B (@nil B)). Qed.
Lemma lem1190158 {A B : Type'} (f : A -> B) (y : A) : (term30 A B f y) = (True /\ True).
Proof. exact (MK_COMB (@lem1190153 A B f y) (@lem1190157 B)). Qed.
Lemma lem1190160 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1190161 : (True /\ True) = True.
Proof. exact (@lem1190160 True). Qed.
Lemma lem1190162 {A B : Type'} (f : A -> B) (y : A) : (term30 A B f y) = True.
Proof. exact (TRANS (@lem1190158 A B f y) (@lem1190161)). Qed.
Lemma lem1190163 {A B : Type'} (f : A -> B) (y : A) : ((term27 A B f y) = (term27 A B f y)) = True.
Proof. exact (TRANS (@lem1190145 A B f y) (@lem1190162 A B f y)). Qed.
Lemma lem1190164 {A B : Type'} (x : A) (f : A -> B) (y : A) (h1 : (f x) = (f y)) : ((term24 A B f x) = (term24 A B f y)) = True.
Proof. exact (TRANS (@lem1190141 A B x f y h1) (@lem1190163 A B f y)). Qed.
Lemma lem1190165 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1190166 {A B : Type'} (x : A) (f : A -> B) (y : A) (h1 : (f x) = (f y)) : (term32 A B x f y) = (imp True).
Proof. exact (MK_COMB (@lem1190165) (@lem1190164 A B x f y h1)). Qed.
Lemma lem1190168 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) (t2 : list A) : ((@cons A h1' t1) = (@cons A h2' t2)) = (term13 A h1' h2' t1 t2).
Proof. exact (EQ_MP (@lem1190092 A h1' h2' t1 t2) (@lem1190091 A h1' h2' t1 t2)). Qed.
Lemma lem1190169 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) (t2 : list A) : ((@cons A h1' t1) = (@cons A h2' t2)) = (term13 A h1' h2' t1 t2).
Proof. exact (@lem1190168 A h1' h2' t1 t2). Qed.
Lemma lem1190170 {A : Type'} (x : A) (y : A) : ((@cons A x (@nil A)) = (@cons A y (@nil A))) = (term33 A x y).
Proof. exact (@lem1190169 A x y (@nil A) (@nil A)). Qed.
Lemma lem1190176 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1190177 {A : Type'} (x : list A) : (x = x) = True.
Proof. exact (@lem1190176 (list A) x). Qed.
Lemma lem1190178 {A : Type'} : ((@nil A) = (@nil A)) = True.
Proof. exact (@lem1190177 A (@nil A)). Qed.
Lemma lem1190179 {A : Type'} (x : A) (y : A) : (term34 A x y) = (term34 A x y).
Proof. exact (eq_refl (term34 A x y)). Qed.
Lemma lem1190180 {A : Type'} (x : A) (y : A) : (term33 A x y) = (term35 A x y).
Proof. exact (MK_COMB (@lem1190179 A x y) (@lem1190178 A)). Qed.
Lemma lem1190182 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1190183 {A : Type'} (x : A) (y : A) : (term35 A x y) = (x = y).
Proof. exact (@lem1190182 (x = y)). Qed.
Lemma lem1190186 {A : Type'} (x : A) (y : A) : (term33 A x y) = (x = y).
Proof. exact (TRANS (@lem1190180 A x y) (@lem1190183 A x y)). Qed.
Lemma lem1190187 {A : Type'} (x : A) (y : A) : ((@cons A x (@nil A)) = (@cons A y (@nil A))) = (x = y).
Proof. exact (TRANS (@lem1190170 A x y) (@lem1190186 A x y)). Qed.
Lemma lem1190188 {A B : Type'} (x : A) (f : A -> B) (y : A) (h1 : (f x) = (f y)) : (term5 A B f x y) = (term36 A x y).
Proof. exact (MK_COMB (@lem1190166 A B x f y h1) (@lem1190187 A x y)). Qed.
Lemma lem1190190 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1190191 {A : Type'} (x : A) (y : A) : (term36 A x y) = (x = y).
Proof. exact (@lem1190190 (x = y)). Qed.
Lemma lem1190194 {A B : Type'} (x : A) (f : A -> B) (y : A) (h1 : (f x) = (f y)) : (term5 A B f x y) = (x = y).
Proof. exact (TRANS (@lem1190188 A B x f y h1) (@lem1190191 A x y)). Qed.
Lemma lem1190195 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1190196 {A B : Type'} (x : A) (f : A -> B) (y : A) (h1 : (f x) = (f y)) : (term37 A B f x y) = (term38 A x y).
Proof. exact (MK_COMB (@lem1190195) (@lem1190194 A B x f y h1)). Qed.
Lemma lem1190199 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem1190200 {A B : Type'} (x : A) (f : A -> B) (y : A) (h1 : (f x) = (f y)) : (term39 A B f x y) = (term40 A x y).
Proof. exact (MK_COMB (@lem1190196 A B x f y h1) (@lem1190199 A x y)). Qed.
Lemma lem1190204 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem1190205 {A : Type'} (x : A) (y : A) : (term40 A x y) = True.
Proof. exact (@lem1190204 (x = y)). Qed.
Lemma lem1190206 {A B : Type'} (x : A) (f : A -> B) (y : A) (h1 : (f x) = (f y)) : (term39 A B f x y) = True.
Proof. exact (TRANS (@lem1190200 A B x f y h1) (@lem1190205 A x y)). Qed.
Lemma lem1190207 {A B : Type'} (x : A) (f : A -> B) (y : A) (h1 : (f x) = (f y)) : True = (term39 A B f x y).
Proof. exact (SYM (@lem1190206 A B x f y h1)). Qed.
Lemma lem1190208 {A B : Type'} (x : A) (f : A -> B) (y : A) (h1 : (f x) = (f y)) : term39 A B f x y.
Proof. exact (EQ_MP (@lem1190207 A B x f y h1) (@lem0)). Qed.
Lemma lem1190209 {A B : Type'} (x : A) (f : A -> B) (y : A) (h1 : term0 A B f) (h2 : (f x) = (f y)) : x = y.
Proof. exact (@lem1190208 A B x f y h2 (@lem1190081 A B x y f h1)). Qed.
Lemma lem1190210 {A B : Type'} (x : A) (y : A) (f : A -> B) (h1 : term0 A B f) : term41 A B f x y.
Proof. exact (fun h0 : (f x) = (f y) => @lem1190209 A B x f y h1 h0). Qed.
Lemma lem1190215 {A B : Type'} (x : A) (f : A -> B) (h1 : term0 A B f) : term42 A B f x.
Proof. exact (fun y : A => @lem1190210 A B x y f h1). Qed.
Lemma lem1190220 {A B : Type'} (f : A -> B) (h1 : term0 A B f) : term1 A B f.
Proof. exact (fun x : A => @lem1190215 A B x f h1). Qed.
Lemma lem1190222 {A : Type'} (P : type1143 A) : term43 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1190223 {A : Type'} (P : type1143 A) : term43 A P.
Proof. exact (@lem1190222 A P). Qed.
Lemma lem1190224 {A B : Type'} (f : A -> B) : term44 A B f.
Proof. exact (@lem1190223 A (term45 A B f)). Qed.
Lemma lem1190225 {A B : Type'} (f : A -> B) : (term46 A B f) = (term47 A B f).
Proof. exact (eq_refl (term46 A B f)). Qed.
Lemma lem1190226 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1190227 {A B : Type'} (f : A -> B) : (term48 A B f) = (term49 A B f).
Proof. exact (MK_COMB (@lem1190226) (@lem1190225 A B f)). Qed.
Lemma lem1190228 {A B : Type'} (f : A -> B) (t : list A) : (term50 A B f t) = (term51 A B f t).
Proof. exact (eq_refl (term50 A B f t)). Qed.
Lemma lem1190229 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1190230 {A B : Type'} (f : A -> B) (t : list A) : (term52 A B f t) = (term53 A B f t).
Proof. exact (MK_COMB (@lem1190229) (@lem1190228 A B f t)). Qed.
Lemma lem1190231 {A B : Type'} (f : A -> B) (h : A) (t : list A) : (term54 A B f h t) = (term55 A B f h t).
Proof. exact (eq_refl (term54 A B f h t)). Qed.
Lemma lem1190232 {A B : Type'} (f : A -> B) (h : A) (t : list A) : (term56 A B f h t) = (term57 A B f h t).
Proof. exact (MK_COMB (@lem1190230 A B f t) (@lem1190231 A B f h t)). Qed.
Lemma lem1190233 {A B : Type'} (f : A -> B) (h : A) : (term58 A B f h) = (term59 A B f h).
Proof. exact (fun_ext (fun t : list A => @lem1190232 A B f h t)). Qed.
Lemma lem1190234 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1190235 {A B : Type'} (f : A -> B) (h : A) : (term60 A B f h) = (term61 A B f h).
Proof. exact (MK_COMB (@lem1190234 A) (@lem1190233 A B f h)). Qed.
Lemma lem1190236 {A B : Type'} (f : A -> B) : (term62 A B f) = (term63 A B f).
Proof. exact (fun_ext (fun h : A => @lem1190235 A B f h)). Qed.
Lemma lem1190237 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1190238 {A B : Type'} (f : A -> B) : (term64 A B f) = (term65 A B f).
Proof. exact (MK_COMB (@lem1190237 A) (@lem1190236 A B f)). Qed.
Lemma lem1190239 {A B : Type'} (f : A -> B) : (term66 A B f) = (term67 A B f).
Proof. exact (MK_COMB (@lem1190227 A B f) (@lem1190238 A B f)). Qed.
Lemma lem1190240 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1190241 {A B : Type'} (f : A -> B) : (term68 A B f) = (term69 A B f).
Proof. exact (MK_COMB (@lem1190240) (@lem1190239 A B f)). Qed.
Lemma lem1190242 {A B : Type'} (f : A -> B) (l : list A) : (term50 A B f l) = (term51 A B f l).
Proof. exact (eq_refl (term50 A B f l)). Qed.
Lemma lem1190243 {A B : Type'} (f : A -> B) : (term70 A B f) = (term45 A B f).
Proof. exact (fun_ext (fun l : list A => @lem1190242 A B f l)). Qed.
Lemma lem1190244 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1190245 {A B : Type'} (f : A -> B) : (term71 A B f) = (term0 A B f).
Proof. exact (MK_COMB (@lem1190244 A) (@lem1190243 A B f)). Qed.
Lemma lem1190246 {A B : Type'} (f : A -> B) : (term44 A B f) = (term72 A B f).
Proof. exact (MK_COMB (@lem1190241 A B f) (@lem1190245 A B f)). Qed.
Lemma lem1190247 {A B : Type'} (f : A -> B) : term72 A B f.
Proof. exact (EQ_MP (@lem1190246 A B f) (@lem1190224 A B f)). Qed.
Lemma lem1190248 {A B : Type'} (f : A -> B) (t : list A) (h1 : term51 A B f t) : term51 A B f t.
Proof. exact (h1). Qed.
Lemma lem1190250 {A : Type'} (P : type1143 A) : term43 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1190251 {A : Type'} (P : type1143 A) : term43 A P.
Proof. exact (@lem1190250 A P). Qed.
Lemma lem1190252 {A B : Type'} (f : A -> B) : term73 A B f.
Proof. exact (@lem1190251 A (term74 A B f)). Qed.
Lemma lem1190253 {A B : Type'} (f : A -> B) : (term75 A B f) = (term76 A B f).
Proof. exact (eq_refl (term75 A B f)). Qed.
Lemma lem1190254 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1190255 {A B : Type'} (f : A -> B) : (term77 A B f) = (term78 A B f).
Proof. exact (MK_COMB (@lem1190254) (@lem1190253 A B f)). Qed.
Lemma lem1190256 {A B : Type'} (f : A -> B) (t : list A) : (term79 A B f t) = (term80 A B f t).
Proof. exact (eq_refl (term79 A B f t)). Qed.
Lemma lem1190257 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1190258 {A B : Type'} (f : A -> B) (t : list A) : (term81 A B f t) = (term82 A B f t).
Proof. exact (MK_COMB (@lem1190257) (@lem1190256 A B f t)). Qed.
Lemma lem1190259 {A B : Type'} (f : A -> B) (h : A) (t : list A) : (term83 A B f h t) = (term84 A B f h t).
Proof. exact (eq_refl (term83 A B f h t)). Qed.
Lemma lem1190260 {A B : Type'} (f : A -> B) (h : A) (t : list A) : (term85 A B f h t) = (term86 A B f h t).
Proof. exact (MK_COMB (@lem1190258 A B f t) (@lem1190259 A B f h t)). Qed.
Lemma lem1190261 {A B : Type'} (f : A -> B) (h : A) : (term87 A B f h) = (term88 A B f h).
Proof. exact (fun_ext (fun t : list A => @lem1190260 A B f h t)). Qed.
Lemma lem1190262 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1190263 {A B : Type'} (f : A -> B) (h : A) : (term89 A B f h) = (term90 A B f h).
Proof. exact (MK_COMB (@lem1190262 A) (@lem1190261 A B f h)). Qed.
Lemma lem1190264 {A B : Type'} (f : A -> B) : (term91 A B f) = (term92 A B f).
Proof. exact (fun_ext (fun h : A => @lem1190263 A B f h)). Qed.
Lemma lem1190265 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1190266 {A B : Type'} (f : A -> B) : (term93 A B f) = (term94 A B f).
Proof. exact (MK_COMB (@lem1190265 A) (@lem1190264 A B f)). Qed.
Lemma lem1190267 {A B : Type'} (f : A -> B) : (term95 A B f) = (term96 A B f).
Proof. exact (MK_COMB (@lem1190255 A B f) (@lem1190266 A B f)). Qed.
Lemma lem1190268 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1190269 {A B : Type'} (f : A -> B) : (term97 A B f) = (term98 A B f).
Proof. exact (MK_COMB (@lem1190268) (@lem1190267 A B f)). Qed.
Lemma lem1190270 {A B : Type'} (f : A -> B) (m : list A) : (term79 A B f m) = (term80 A B f m).
Proof. exact (eq_refl (term79 A B f m)). Qed.
Lemma lem1190271 {A B : Type'} (f : A -> B) : (term99 A B f) = (term74 A B f).
Proof. exact (fun_ext (fun m : list A => @lem1190270 A B f m)). Qed.
Lemma lem1190272 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1190273 {A B : Type'} (f : A -> B) : (term100 A B f) = (term47 A B f).
Proof. exact (MK_COMB (@lem1190272 A) (@lem1190271 A B f)). Qed.
Lemma lem1190274 {A B : Type'} (f : A -> B) : (term73 A B f) = (term101 A B f).
Proof. exact (MK_COMB (@lem1190269 A B f) (@lem1190273 A B f)). Qed.
Lemma lem1190275 {A B : Type'} (f : A -> B) : term101 A B f.
Proof. exact (EQ_MP (@lem1190274 A B f) (@lem1190252 A B f)). Qed.
Lemma lem1190282 {A : Type'} (P : type1143 A) : term43 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1190283 {A : Type'} (P : type1143 A) : term43 A P.
Proof. exact (@lem1190282 A P). Qed.
Lemma lem1190284 {A B : Type'} (f : A -> B) (h : A) (t : list A) : term102 A B f h t.
Proof. exact (@lem1190283 A (term103 A B f h t)). Qed.
Lemma lem1190285 {A B : Type'} (f : A -> B) (h : A) (t : list A) : (term104 A B f h t) = (term105 A B f h t).
Proof. exact (eq_refl (term104 A B f h t)). Qed.
Lemma lem1190286 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1190287 {A B : Type'} (f : A -> B) (h : A) (t : list A) : (term106 A B f h t) = (term107 A B f h t).
Proof. exact (MK_COMB (@lem1190286) (@lem1190285 A B f h t)). Qed.
Lemma lem1190288 {A B : Type'} (f : A -> B) (h : A) (t : list A) (t' : list A) : (term108 A B f h t t') = (term109 A B f h t t').
Proof. exact (eq_refl (term108 A B f h t t')). Qed.
Lemma lem1190289 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1190290 {A B : Type'} (f : A -> B) (h : A) (t : list A) (t' : list A) : (term110 A B f h t t') = (term111 A B f h t t').
Proof. exact (MK_COMB (@lem1190289) (@lem1190288 A B f h t t')). Qed.
Lemma lem1190291 {A B : Type'} (f : A -> B) (h : A) (t : list A) (h' : A) (t' : list A) : (term112 A B f h t h' t') = (term113 A B f h t h' t').
Proof. exact (eq_refl (term112 A B f h t h' t')). Qed.
Lemma lem1190292 {A B : Type'} (f : A -> B) (h : A) (t : list A) (h' : A) (t' : list A) : (term114 A B f h t h' t') = (term115 A B f h t h' t').
Proof. exact (MK_COMB (@lem1190290 A B f h t t') (@lem1190291 A B f h t h' t')). Qed.
Lemma lem1190293 {A B : Type'} (f : A -> B) (h : A) (t : list A) (h' : A) : (term116 A B f h t h') = (term117 A B f h t h').
Proof. exact (fun_ext (fun t' : list A => @lem1190292 A B f h t h' t')). Qed.
Lemma lem1190294 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1190295 {A B : Type'} (f : A -> B) (h : A) (t : list A) (h' : A) : (term118 A B f h t h') = (term119 A B f h t h').
Proof. exact (MK_COMB (@lem1190294 A) (@lem1190293 A B f h t h')). Qed.
Lemma lem1190296 {A B : Type'} (f : A -> B) (h : A) (t : list A) : (term120 A B f h t) = (term121 A B f h t).
Proof. exact (fun_ext (fun h' : A => @lem1190295 A B f h t h')). Qed.
Lemma lem1190297 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1190298 {A B : Type'} (f : A -> B) (h : A) (t : list A) : (term122 A B f h t) = (term123 A B f h t).
Proof. exact (MK_COMB (@lem1190297 A) (@lem1190296 A B f h t)). Qed.
Lemma lem1190299 {A B : Type'} (f : A -> B) (h : A) (t : list A) : (term124 A B f h t) = (term125 A B f h t).
Proof. exact (MK_COMB (@lem1190287 A B f h t) (@lem1190298 A B f h t)). Qed.
Lemma lem1190300 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1190301 {A B : Type'} (f : A -> B) (h : A) (t : list A) : (term126 A B f h t) = (term127 A B f h t).
Proof. exact (MK_COMB (@lem1190300) (@lem1190299 A B f h t)). Qed.
Lemma lem1190302 {A B : Type'} (f : A -> B) (h : A) (t : list A) (m : list A) : (term108 A B f h t m) = (term109 A B f h t m).
Proof. exact (eq_refl (term108 A B f h t m)). Qed.
Lemma lem1190303 {A B : Type'} (f : A -> B) (h : A) (t : list A) : (term128 A B f h t) = (term103 A B f h t).
Proof. exact (fun_ext (fun m : list A => @lem1190302 A B f h t m)). Qed.
Lemma lem1190304 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1190305 {A B : Type'} (f : A -> B) (h : A) (t : list A) : (term129 A B f h t) = (term55 A B f h t).
Proof. exact (MK_COMB (@lem1190304 A) (@lem1190303 A B f h t)). Qed.
Lemma lem1190306 {A B : Type'} (f : A -> B) (h : A) (t : list A) : (term102 A B f h t) = (term130 A B f h t).
Proof. exact (MK_COMB (@lem1190301 A B f h t) (@lem1190305 A B f h t)). Qed.
Lemma lem1190307 {A B : Type'} (f : A -> B) (h : A) (t : list A) : term130 A B f h t.
Proof. exact (EQ_MP (@lem1190306 A B f h t) (@lem1190284 A B f h t)). Qed.
Lemma lem1190308 {A B : Type'} (f : A -> B) (h : A) (t : list A) (t' : list A) (h1 : term109 A B f h t t') : term109 A B f h t t'.
Proof. exact (h1). Qed.
Lemma lem1190372 {_739 : Type'} (x : _739) (p : Prop) : (term131 _739 x p) = p.
Proof. exact (EQ_MP (@lem1804 _739 x p) (@lem0)). Qed.
Lemma lem1190373 {B : Type'} (x : list B) (p : Prop) : (term132 B x p) = p.
Proof. exact (@lem1190372 (list B) x p). Qed.
Lemma lem1190374 {A B : Type'} (f : A -> B) : (term76 A B f) = ((@nil A) = (@nil A)).
Proof. exact (@lem1190373 B (@List.map A B f (@nil A)) ((@nil A) = (@nil A))). Qed.
Lemma lem1190376 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1190377 {A : Type'} (x : list A) : (x = x) = True.
Proof. exact (@lem1190376 (list A) x). Qed.
Lemma lem1190378 {A : Type'} : ((@nil A) = (@nil A)) = True.
Proof. exact (@lem1190377 A (@nil A)). Qed.
Lemma lem1190383 {A B : Type'} (f : A -> B) : (term76 A B f) = True.
Proof. exact (TRANS (@lem1190374 A B f) (@lem1190378 A)). Qed.
Lemma lem1190384 {A B : Type'} (f : A -> B) : True = (term76 A B f).
Proof. exact (SYM (@lem1190383 A B f)). Qed.
Lemma lem1190385 {A B : Type'} (f : A -> B) : term76 A B f.
Proof. exact (EQ_MP (@lem1190384 A B f) (@lem0)). Qed.
Lemma lem1190398 {A : Type'} (h : A) : term133 A h.
Proof. exact (@lem1111523 A h). Qed.
Lemma lem1190399 {A : Type'} (h : A) : (term133 A h) = (term134 A h).
Proof. exact (eq_refl (term133 A h)). Qed.
Lemma lem1190400 {A : Type'} (h : A) : term134 A h.
Proof. exact (EQ_MP (@lem1190399 A h) (@lem1190398 A h)). Qed.
Lemma lem1190401 {A : Type'} (h : A) (t : list A) : term135 A h t.
Proof. exact (@lem1190400 A h t). Qed.
Lemma lem1190402 {A : Type'} (h : A) (t : list A) : (term135 A h t) = (term136 A h t).
Proof. exact (eq_refl (term135 A h t)). Qed.
Lemma lem1190403 {A : Type'} (h : A) (t : list A) : term136 A h t.
Proof. exact (EQ_MP (@lem1190402 A h t) (@lem1190401 A h t)). Qed.
Lemma lem1190407 {A : Type'} (h : A) (t : list A) (h1 : (@cons A h t) = (@nil A)) : (@cons A h t) = (@nil A).
Proof. exact (h1). Qed.
Lemma lem1190408 {A : Type'} (h : A) (t : list A) (h1 : (@cons A h t) = (@nil A)) : (@nil A) = (@cons A h t).
Proof. exact (SYM (@lem1190407 A h t h1)). Qed.
Lemma lem1190409 {A : Type'} (h : A) (t : list A) (h1 : (@nil A) = (@cons A h t)) : (@nil A) = (@cons A h t).
Proof. exact (h1). Qed.
Lemma lem1190410 {A : Type'} (h : A) (t : list A) (h1 : (@nil A) = (@cons A h t)) : (@cons A h t) = (@nil A).
Proof. exact (SYM (@lem1190409 A h t h1)). Qed.
Lemma lem1190411 {A : Type'} (h : A) (t : list A) : ((@cons A h t) = (@nil A)) = ((@nil A) = (@cons A h t)).
Proof. exact (prop_ext (fun h1 : (@cons A h t) = (@nil A) => @lem1190408 A h t h1) (fun h1 : (@nil A) = (@cons A h t) => @lem1190410 A h t h1)). Qed.
Lemma lem1190412 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1190413 {A : Type'} (h : A) (t : list A) : (term136 A h t) = (term137 A h t).
Proof. exact (MK_COMB (@lem1190412) (@lem1190411 A h t)). Qed.
Lemma lem1190414 {A : Type'} (h : A) (t : list A) : term137 A h t.
Proof. exact (EQ_MP (@lem1190413 A h t) (@lem1190403 A h t)). Qed.
Lemma lem1190415 {A : Type'} (h : A) (t : list A) : term138 A h t.
Proof. exact (@lem82 ((@nil A) = (@cons A h t))). Qed.
Lemma lem1190417 {A B : Type'} : term14 A B.
Proof. exact (proj2 (@lem1097797 A B)). Qed.
Lemma lem1190418 {A B : Type'} (f : A -> B) : term15 A B f.
Proof. exact (@lem1190417 A B f). Qed.
Lemma lem1190419 {A B : Type'} (f : A -> B) : (term15 A B f) = (term16 A B f).
Proof. exact (eq_refl (term15 A B f)). Qed.
Lemma lem1190420 {A B : Type'} (f : A -> B) : term16 A B f.
Proof. exact (EQ_MP (@lem1190419 A B f) (@lem1190418 A B f)). Qed.
Lemma lem1190421 {A B : Type'} (f : A -> B) (h : A) : term17 A B f h.
Proof. exact (@lem1190420 A B f h). Qed.
Lemma lem1190422 {A B : Type'} (h : A) (f : A -> B) : (term17 A B f h) = (term18 A B h f).
Proof. exact (eq_refl (term17 A B f h)). Qed.
Lemma lem1190423 {A B : Type'} (h : A) (f : A -> B) : term18 A B h f.
Proof. exact (EQ_MP (@lem1190422 A B h f) (@lem1190421 A B f h)). Qed.
Lemma lem1190424 {A B : Type'} (h : A) (f : A -> B) (t : list A) : term19 A B h f t.
Proof. exact (@lem1190423 A B h f t). Qed.
Lemma lem1190425 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term19 A B h f t) = ((term20 A B f h t) = (term21 A B h f t)).
Proof. exact (eq_refl (term19 A B h f t)). Qed.
Lemma lem1190427 {A B : Type'} : term22 A B.
Proof. exact (proj1 (@lem1097797 A B)). Qed.
Lemma lem1190428 {A B : Type'} (f : A -> B) : term23 A B f.
Proof. exact (@lem1190427 A B f). Qed.
Lemma lem1190429 {A B : Type'} (f : A -> B) : (term23 A B f) = ((@List.map A B f (@nil A)) = (@nil B)).
Proof. exact (eq_refl (term23 A B f)). Qed.
Lemma lem1190460 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term139 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1190461 (p : Prop) (q : Prop) (p' : Prop) : term140 p q p'.
Proof. exact (fun q' : Prop => @lem1190460 p q p' q'). Qed.
Lemma lem1190462 (p : Prop) (q : Prop) : term141 p q.
Proof. exact (fun p' : Prop => @lem1190461 p q p'). Qed.
Lemma lem1190463 {A B : Type'} (f : A -> B) (h : A) (t : list A) : term142 A B f h t.
Proof. exact (@lem1190462 ((@List.map A B f (@nil A)) = (term20 A B f h t)) ((@nil A) = (@cons A h t))). Qed.
Lemma lem1190464 {A B : Type'} (f : A -> B) (h : A) (t : list A) (p' : Prop) : term143 A B f h t p'.
Proof. exact (@lem1190463 A B f h t p'). Qed.
Lemma lem1190465 {A B : Type'} (f : A -> B) (h : A) (t : list A) (p' : Prop) : (term143 A B f h t p') = (term144 A B f h t p').
Proof. exact (eq_refl (term143 A B f h t p')). Qed.
Lemma lem1190466 {A B : Type'} (f : A -> B) (h : A) (t : list A) (p' : Prop) : term144 A B f h t p'.
Proof. exact (EQ_MP (@lem1190465 A B f h t p') (@lem1190464 A B f h t p')). Qed.
Lemma lem1190467 {A B : Type'} (f : A -> B) (h : A) (t : list A) (p' : Prop) (q' : Prop) : term145 A B f h t p' q'.
Proof. exact (@lem1190466 A B f h t p' q'). Qed.
Lemma lem1190468 {A B : Type'} (f : A -> B) (h : A) (t : list A) (p' : Prop) (q' : Prop) : (term145 A B f h t p' q') = (term146 A B f h t p' q').
Proof. exact (eq_refl (term145 A B f h t p' q')). Qed.
Lemma lem1190469 {A B : Type'} (f : A -> B) (h : A) (t : list A) (p' : Prop) (q' : Prop) : term146 A B f h t p' q'.
Proof. exact (EQ_MP (@lem1190468 A B f h t p' q') (@lem1190467 A B f h t p' q')). Qed.
Lemma lem1190485 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (@nil B).
Proof. exact (EQ_MP (@lem1190429 A B f) (@lem1190428 A B f)). Qed.
Lemma lem1190486 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (@nil B).
Proof. exact (@lem1190485 A B f). Qed.
Lemma lem1190494 {B : Type'} : (@eq (list B)) = (@eq (list B)).
Proof. exact (eq_refl (@eq (list B))). Qed.
Lemma lem1190495 {A B : Type'} (f : A -> B) : (term147 A B f) = (@eq (list B) (@nil B)).
Proof. exact (MK_COMB (@lem1190494 B) (@lem1190486 A B f)). Qed.
Lemma lem1190512 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term20 A B f h t) = (term21 A B h f t).
Proof. exact (EQ_MP (@lem1190425 A B h f t) (@lem1190424 A B h f t)). Qed.
Lemma lem1190513 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term20 A B f h t) = (term21 A B h f t).
Proof. exact (@lem1190512 A B h f t). Qed.
Lemma lem1190558 {A B : Type'} (h : A) (f : A -> B) (t : list A) : ((@List.map A B f (@nil A)) = (term20 A B f h t)) = ((@nil B) = (term21 A B h f t)).
Proof. exact (MK_COMB (@lem1190495 A B f) (@lem1190513 A B h f t)). Qed.
Lemma lem1190560 {A : Type'} (h : A) (t : list A) : ((@nil A) = (@cons A h t)) = False.
Proof. exact (@lem1190415 A h t (@lem1190414 A h t)). Qed.
Lemma lem1190561 {B : Type'} (h : B) (t : list B) : ((@nil B) = (@cons B h t)) = False.
Proof. exact (@lem1190560 B h t). Qed.
Lemma lem1190562 {A B : Type'} (h : A) (f : A -> B) (t : list A) : ((@nil B) = (term21 A B h f t)) = False.
Proof. exact (@lem1190561 B (f h) (@List.map A B f t)). Qed.
Lemma lem1190567 {A B : Type'} (f : A -> B) (h : A) (t : list A) : ((@List.map A B f (@nil A)) = (term20 A B f h t)) = False.
Proof. exact (TRANS (@lem1190558 A B h f t) (@lem1190562 A B h f t)). Qed.
Lemma lem1190568 {A B : Type'} (f : A -> B) (h : A) (t : list A) (q' : Prop) : term148 A B f h t q'.
Proof. exact (@lem1190469 A B f h t False q'). Qed.
Lemma lem1190569 {A B : Type'} (f : A -> B) (h : A) (t : list A) (q' : Prop) : term149 A B f h t q'.
Proof. exact (@lem1190568 A B f h t q' (@lem1190567 A B f h t)). Qed.
Lemma lem1190570 (h1 : False) : False.
Proof. exact (h1). Qed.
Lemma lem1190571 : False = (False = True).
Proof. exact (@lem7 False). Qed.
Lemma lem1190574 {A : Type'} (h : A) (t : list A) : ((@nil A) = (@cons A h t)) = False.
Proof. exact (@lem1190415 A h t (@lem1190414 A h t)). Qed.
Lemma lem1190575 {A : Type'} (h : A) (t : list A) : ((@nil A) = (@cons A h t)) = False.
Proof. exact (@lem1190574 A h t). Qed.
Lemma lem1190577 (h1 : False) : False = True.
Proof. exact (EQ_MP (@lem1190571) (@lem1190570 h1)). Qed.
Lemma lem1190582 {A : Type'} (h : A) (t : list A) (h1 : False) : ((@nil A) = (@cons A h t)) = True.
Proof. exact (TRANS (@lem1190575 A h t) (@lem1190577 h1)). Qed.
Lemma lem1190583 {A : Type'} (h : A) (t : list A) : term150 A h t.
Proof. exact (fun h0 : False => @lem1190582 A h t h0). Qed.
Lemma lem1190584 {A B : Type'} (f : A -> B) (h : A) (t : list A) : term151 A B f h t.
Proof. exact (@lem1190569 A B f h t True). Qed.
Lemma lem1190585 {A B : Type'} (f : A -> B) (h : A) (t : list A) : (term84 A B f h t) = (False -> True).
Proof. exact (@lem1190584 A B f h t (@lem1190583 A h t)). Qed.
Lemma lem1190587 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1190588 : (False -> True) = True.
Proof. exact (@lem1190587 True). Qed.
Lemma lem1190593 {A B : Type'} (f : A -> B) (h : A) (t : list A) : (term84 A B f h t) = True.
Proof. exact (TRANS (@lem1190585 A B f h t) (@lem1190588)). Qed.
Lemma lem1190594 {A B : Type'} (f : A -> B) (h : A) (t : list A) : True = (term84 A B f h t).
Proof. exact (SYM (@lem1190593 A B f h t)). Qed.
Lemma lem1190595 {A B : Type'} (f : A -> B) (h : A) (t : list A) : term84 A B f h t.
Proof. exact (EQ_MP (@lem1190594 A B f h t) (@lem0)). Qed.
Lemma lem1190608 {A : Type'} (h : A) : term133 A h.
Proof. exact (@lem1111523 A h). Qed.
Lemma lem1190609 {A : Type'} (h : A) : (term133 A h) = (term134 A h).
Proof. exact (eq_refl (term133 A h)). Qed.
Lemma lem1190610 {A : Type'} (h : A) : term134 A h.
Proof. exact (EQ_MP (@lem1190609 A h) (@lem1190608 A h)). Qed.
Lemma lem1190611 {A : Type'} (h : A) (t : list A) : term135 A h t.
Proof. exact (@lem1190610 A h t). Qed.
Lemma lem1190612 {A : Type'} (h : A) (t : list A) : (term135 A h t) = (term136 A h t).
Proof. exact (eq_refl (term135 A h t)). Qed.
Lemma lem1190613 {A : Type'} (h : A) (t : list A) : term136 A h t.
Proof. exact (EQ_MP (@lem1190612 A h t) (@lem1190611 A h t)). Qed.
Lemma lem1190614 {A : Type'} (h : A) (t : list A) : term152 A h t.
Proof. exact (@lem82 ((@cons A h t) = (@nil A))). Qed.
Lemma lem1190627 {A B : Type'} : term14 A B.
Proof. exact (proj2 (@lem1097797 A B)). Qed.
Lemma lem1190628 {A B : Type'} (f : A -> B) : term15 A B f.
Proof. exact (@lem1190627 A B f). Qed.
Lemma lem1190629 {A B : Type'} (f : A -> B) : (term15 A B f) = (term16 A B f).
Proof. exact (eq_refl (term15 A B f)). Qed.
Lemma lem1190630 {A B : Type'} (f : A -> B) : term16 A B f.
Proof. exact (EQ_MP (@lem1190629 A B f) (@lem1190628 A B f)). Qed.
Lemma lem1190631 {A B : Type'} (f : A -> B) (h : A) : term17 A B f h.
Proof. exact (@lem1190630 A B f h). Qed.
Lemma lem1190632 {A B : Type'} (h : A) (f : A -> B) : (term17 A B f h) = (term18 A B h f).
Proof. exact (eq_refl (term17 A B f h)). Qed.
Lemma lem1190633 {A B : Type'} (h : A) (f : A -> B) : term18 A B h f.
Proof. exact (EQ_MP (@lem1190632 A B h f) (@lem1190631 A B f h)). Qed.
Lemma lem1190634 {A B : Type'} (h : A) (f : A -> B) (t : list A) : term19 A B h f t.
Proof. exact (@lem1190633 A B h f t). Qed.
Lemma lem1190635 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term19 A B h f t) = ((term20 A B f h t) = (term21 A B h f t)).
Proof. exact (eq_refl (term19 A B h f t)). Qed.
Lemma lem1190637 {A B : Type'} : term22 A B.
Proof. exact (proj1 (@lem1097797 A B)). Qed.
Lemma lem1190638 {A B : Type'} (f : A -> B) : term23 A B f.
Proof. exact (@lem1190637 A B f). Qed.
Lemma lem1190639 {A B : Type'} (f : A -> B) : (term23 A B f) = ((@List.map A B f (@nil A)) = (@nil B)).
Proof. exact (eq_refl (term23 A B f)). Qed.
Lemma lem1190673 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term139 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1190674 (p : Prop) (q : Prop) (p' : Prop) : term140 p q p'.
Proof. exact (fun q' : Prop => @lem1190673 p q p' q'). Qed.
Lemma lem1190675 (p : Prop) (q : Prop) : term141 p q.
Proof. exact (fun p' : Prop => @lem1190674 p q p'). Qed.
Lemma lem1190676 {A B : Type'} (f : A -> B) (h : A) (t : list A) : term153 A B f h t.
Proof. exact (@lem1190675 ((term20 A B f h t) = (@List.map A B f (@nil A))) ((@cons A h t) = (@nil A))). Qed.
Lemma lem1190677 {A B : Type'} (f : A -> B) (h : A) (t : list A) (p' : Prop) : term154 A B f h t p'.
Proof. exact (@lem1190676 A B f h t p'). Qed.
Lemma lem1190678 {A B : Type'} (f : A -> B) (h : A) (t : list A) (p' : Prop) : (term154 A B f h t p') = (term155 A B f h t p').
Proof. exact (eq_refl (term154 A B f h t p')). Qed.
Lemma lem1190679 {A B : Type'} (f : A -> B) (h : A) (t : list A) (p' : Prop) : term155 A B f h t p'.
Proof. exact (EQ_MP (@lem1190678 A B f h t p') (@lem1190677 A B f h t p')). Qed.
Lemma lem1190680 {A B : Type'} (f : A -> B) (h : A) (t : list A) (p' : Prop) (q' : Prop) : term156 A B f h t p' q'.
Proof. exact (@lem1190679 A B f h t p' q'). Qed.
Lemma lem1190681 {A B : Type'} (f : A -> B) (h : A) (t : list A) (p' : Prop) (q' : Prop) : (term156 A B f h t p' q') = (term157 A B f h t p' q').
Proof. exact (eq_refl (term156 A B f h t p' q')). Qed.
Lemma lem1190682 {A B : Type'} (f : A -> B) (h : A) (t : list A) (p' : Prop) (q' : Prop) : term157 A B f h t p' q'.
Proof. exact (EQ_MP (@lem1190681 A B f h t p' q') (@lem1190680 A B f h t p' q')). Qed.
Lemma lem1190698 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term20 A B f h t) = (term21 A B h f t).
Proof. exact (EQ_MP (@lem1190635 A B h f t) (@lem1190634 A B h f t)). Qed.
Lemma lem1190699 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term20 A B f h t) = (term21 A B h f t).
Proof. exact (@lem1190698 A B h f t). Qed.
Lemma lem1190920 {B : Type'} : (@eq (list B)) = (@eq (list B)).
Proof. exact (eq_refl (@eq (list B))). Qed.
Lemma lem1190921 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term158 A B f h t) = (term159 A B h f t).
Proof. exact (MK_COMB (@lem1190920 B) (@lem1190699 A B h f t)). Qed.
Lemma lem1191151 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (@nil B).
Proof. exact (EQ_MP (@lem1190639 A B f) (@lem1190638 A B f)). Qed.
Lemma lem1191152 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (@nil B).
Proof. exact (@lem1191151 A B f). Qed.
Lemma lem1191157 {A B : Type'} (h : A) (f : A -> B) (t : list A) : ((term20 A B f h t) = (@List.map A B f (@nil A))) = ((term21 A B h f t) = (@nil B)).
Proof. exact (MK_COMB (@lem1190921 A B h f t) (@lem1191152 A B f)). Qed.
Lemma lem1191159 {A : Type'} (h : A) (t : list A) : ((@cons A h t) = (@nil A)) = False.
Proof. exact (@lem1190614 A h t (@lem1190613 A h t)). Qed.
Lemma lem1191160 {B : Type'} (h : B) (t : list B) : ((@cons B h t) = (@nil B)) = False.
Proof. exact (@lem1191159 B h t). Qed.
Lemma lem1191161 {A B : Type'} (h : A) (f : A -> B) (t : list A) : ((term21 A B h f t) = (@nil B)) = False.
Proof. exact (@lem1191160 B (f h) (@List.map A B f t)). Qed.
Lemma lem1191166 {A B : Type'} (h : A) (t : list A) (f : A -> B) : ((term20 A B f h t) = (@List.map A B f (@nil A))) = False.
Proof. exact (TRANS (@lem1191157 A B h f t) (@lem1191161 A B h f t)). Qed.
Lemma lem1191167 {A B : Type'} (f : A -> B) (h : A) (t : list A) (q' : Prop) : term160 A B f h t q'.
Proof. exact (@lem1190682 A B f h t False q'). Qed.
Lemma lem1191168 {A B : Type'} (f : A -> B) (h : A) (t : list A) (q' : Prop) : term161 A B f h t q'.
Proof. exact (@lem1191167 A B f h t q' (@lem1191166 A B h t f)). Qed.
Lemma lem1191169 (h1 : False) : False.
Proof. exact (h1). Qed.
Lemma lem1191170 : False = (False = True).
Proof. exact (@lem7 False). Qed.
Lemma lem1191173 {A : Type'} (h : A) (t : list A) : ((@cons A h t) = (@nil A)) = False.
Proof. exact (@lem1190614 A h t (@lem1190613 A h t)). Qed.
Lemma lem1191174 {A : Type'} (h : A) (t : list A) : ((@cons A h t) = (@nil A)) = False.
Proof. exact (@lem1191173 A h t). Qed.
Lemma lem1191176 (h1 : False) : False = True.
Proof. exact (EQ_MP (@lem1191170) (@lem1191169 h1)). Qed.
Lemma lem1191181 {A : Type'} (h : A) (t : list A) (h1 : False) : ((@cons A h t) = (@nil A)) = True.
Proof. exact (TRANS (@lem1191174 A h t) (@lem1191176 h1)). Qed.
Lemma lem1191182 {A : Type'} (h : A) (t : list A) : term162 A h t.
Proof. exact (fun h0 : False => @lem1191181 A h t h0). Qed.
Lemma lem1191183 {A B : Type'} (f : A -> B) (h : A) (t : list A) : term163 A B f h t.
Proof. exact (@lem1191168 A B f h t True). Qed.
Lemma lem1191184 {A B : Type'} (f : A -> B) (h : A) (t : list A) : (term105 A B f h t) = (False -> True).
Proof. exact (@lem1191183 A B f h t (@lem1191182 A h t)). Qed.
Lemma lem1191186 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1191187 : (False -> True) = True.
Proof. exact (@lem1191186 True). Qed.
Lemma lem1191192 {A B : Type'} (f : A -> B) (h : A) (t : list A) : (term105 A B f h t) = True.
Proof. exact (TRANS (@lem1191184 A B f h t) (@lem1191187)). Qed.
Lemma lem1191193 {A B : Type'} (f : A -> B) (h : A) (t : list A) : True = (term105 A B f h t).
Proof. exact (SYM (@lem1191192 A B f h t)). Qed.
Lemma lem1191194 {A B : Type'} (f : A -> B) (h : A) (t : list A) : term105 A B f h t.
Proof. exact (EQ_MP (@lem1191193 A B f h t) (@lem0)). Qed.
Lemma lem1191195 {A : Type'} (h1' : A) : term6 A h1'.
Proof. exact (@lem1113436 A h1'). Qed.
Lemma lem1191196 {A : Type'} (h1' : A) : (term6 A h1') = (term7 A h1').
Proof. exact (eq_refl (term6 A h1')). Qed.
Lemma lem1191197 {A : Type'} (h1' : A) : term7 A h1'.
Proof. exact (EQ_MP (@lem1191196 A h1') (@lem1191195 A h1')). Qed.
Lemma lem1191198 {A : Type'} (h1' : A) (h2' : A) : term8 A h1' h2'.
Proof. exact (@lem1191197 A h1' h2'). Qed.
Lemma lem1191199 {A : Type'} (h1' : A) (h2' : A) : (term8 A h1' h2') = (term9 A h1' h2').
Proof. exact (eq_refl (term8 A h1' h2')). Qed.
Lemma lem1191200 {A : Type'} (h1' : A) (h2' : A) : term9 A h1' h2'.
Proof. exact (EQ_MP (@lem1191199 A h1' h2') (@lem1191198 A h1' h2')). Qed.
Lemma lem1191201 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) : term10 A h1' h2' t1.
Proof. exact (@lem1191200 A h1' h2' t1). Qed.
Lemma lem1191202 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) : (term10 A h1' h2' t1) = (term11 A h1' h2' t1).
Proof. exact (eq_refl (term10 A h1' h2' t1)). Qed.
Lemma lem1191203 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) : term11 A h1' h2' t1.
Proof. exact (EQ_MP (@lem1191202 A h1' h2' t1) (@lem1191201 A h1' h2' t1)). Qed.
Lemma lem1191204 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) (t2 : list A) : term12 A h1' h2' t1 t2.
Proof. exact (@lem1191203 A h1' h2' t1 t2). Qed.
Lemma lem1191205 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) (t2 : list A) : (term12 A h1' h2' t1 t2) = (((@cons A h1' t1) = (@cons A h2' t2)) = (term13 A h1' h2' t1 t2)).
Proof. exact (eq_refl (term12 A h1' h2' t1 t2)). Qed.
Lemma lem1191226 {A B : Type'} : term14 A B.
Proof. exact (proj2 (@lem1097797 A B)). Qed.
Lemma lem1191227 {A B : Type'} (f : A -> B) : term15 A B f.
Proof. exact (@lem1191226 A B f). Qed.
Lemma lem1191228 {A B : Type'} (f : A -> B) : (term15 A B f) = (term16 A B f).
Proof. exact (eq_refl (term15 A B f)). Qed.
Lemma lem1191229 {A B : Type'} (f : A -> B) : term16 A B f.
Proof. exact (EQ_MP (@lem1191228 A B f) (@lem1191227 A B f)). Qed.
Lemma lem1191230 {A B : Type'} (f : A -> B) (h : A) : term17 A B f h.
Proof. exact (@lem1191229 A B f h). Qed.
Lemma lem1191231 {A B : Type'} (h : A) (f : A -> B) : (term17 A B f h) = (term18 A B h f).
Proof. exact (eq_refl (term17 A B f h)). Qed.
Lemma lem1191232 {A B : Type'} (h : A) (f : A -> B) : term18 A B h f.
Proof. exact (EQ_MP (@lem1191231 A B h f) (@lem1191230 A B f h)). Qed.
Lemma lem1191233 {A B : Type'} (h : A) (f : A -> B) (t : list A) : term19 A B h f t.
Proof. exact (@lem1191232 A B h f t). Qed.
Lemma lem1191234 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term19 A B h f t) = ((term20 A B f h t) = (term21 A B h f t)).
Proof. exact (eq_refl (term19 A B h f t)). Qed.
Lemma lem1191279 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term139 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1191280 (p : Prop) (q : Prop) (p' : Prop) : term140 p q p'.
Proof. exact (fun q' : Prop => @lem1191279 p q p' q'). Qed.
Lemma lem1191281 (p : Prop) (q : Prop) : term141 p q.
Proof. exact (fun p' : Prop => @lem1191280 p q p'). Qed.
Lemma lem1191282 {A B : Type'} (f : A -> B) (h : A) (t : list A) (h' : A) (t' : list A) : term164 A B f h t h' t'.
Proof. exact (@lem1191281 ((term20 A B f h t) = (term20 A B f h' t')) ((@cons A h t) = (@cons A h' t'))). Qed.
Lemma lem1191283 {A B : Type'} (f : A -> B) (h : A) (t : list A) (h' : A) (t' : list A) (p' : Prop) : term165 A B f h t h' t' p'.
Proof. exact (@lem1191282 A B f h t h' t' p'). Qed.
Lemma lem1191284 {A B : Type'} (f : A -> B) (h : A) (t : list A) (h' : A) (t' : list A) (p' : Prop) : (term165 A B f h t h' t' p') = (term166 A B f h t h' t' p').
Proof. exact (eq_refl (term165 A B f h t h' t' p')). Qed.
Lemma lem1191285 {A B : Type'} (f : A -> B) (h : A) (t : list A) (h' : A) (t' : list A) (p' : Prop) : term166 A B f h t h' t' p'.
Proof. exact (EQ_MP (@lem1191284 A B f h t h' t' p') (@lem1191283 A B f h t h' t' p')). Qed.
Lemma lem1191286 {A B : Type'} (f : A -> B) (h : A) (t : list A) (h' : A) (t' : list A) (p' : Prop) (q' : Prop) : term167 A B f h t h' t' p' q'.
Proof. exact (@lem1191285 A B f h t h' t' p' q'). Qed.
Lemma lem1191287 {A B : Type'} (f : A -> B) (h : A) (t : list A) (h' : A) (t' : list A) (p' : Prop) (q' : Prop) : (term167 A B f h t h' t' p' q') = (term168 A B f h t h' t' p' q').
Proof. exact (eq_refl (term167 A B f h t h' t' p' q')). Qed.
Lemma lem1191288 {A B : Type'} (f : A -> B) (h : A) (t : list A) (h' : A) (t' : list A) (p' : Prop) (q' : Prop) : term168 A B f h t h' t' p' q'.
Proof. exact (EQ_MP (@lem1191287 A B f h t h' t' p' q') (@lem1191286 A B f h t h' t' p' q')). Qed.
Lemma lem1191304 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term20 A B f h t) = (term21 A B h f t).
Proof. exact (EQ_MP (@lem1191234 A B h f t) (@lem1191233 A B h f t)). Qed.
Lemma lem1191305 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term20 A B f h t) = (term21 A B h f t).
Proof. exact (@lem1191304 A B h f t). Qed.
Lemma lem1191526 {B : Type'} : (@eq (list B)) = (@eq (list B)).
Proof. exact (eq_refl (@eq (list B))). Qed.
Lemma lem1191527 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term158 A B f h t) = (term159 A B h f t).
Proof. exact (MK_COMB (@lem1191526 B) (@lem1191305 A B h f t)). Qed.
Lemma lem1191757 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term20 A B f h t) = (term21 A B h f t).
Proof. exact (EQ_MP (@lem1191234 A B h f t) (@lem1191233 A B h f t)). Qed.
Lemma lem1191758 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term20 A B f h t) = (term21 A B h f t).
Proof. exact (@lem1191757 A B h f t). Qed.
Lemma lem1191759 {A B : Type'} (h' : A) (f : A -> B) (t' : list A) : (term20 A B f h' t') = (term21 A B h' f t').
Proof. exact (@lem1191758 A B h' f t'). Qed.
Lemma lem1191804 {A B : Type'} (h : A) (t : list A) (h' : A) (f : A -> B) (t' : list A) : ((term20 A B f h t) = (term20 A B f h' t')) = ((term21 A B h f t) = (term21 A B h' f t')).
Proof. exact (MK_COMB (@lem1191527 A B h f t) (@lem1191759 A B h' f t')). Qed.
Lemma lem1191806 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) (t2 : list A) : ((@cons A h1' t1) = (@cons A h2' t2)) = (term13 A h1' h2' t1 t2).
Proof. exact (EQ_MP (@lem1191205 A h1' h2' t1 t2) (@lem1191204 A h1' h2' t1 t2)). Qed.
Lemma lem1191807 {B : Type'} (h1' : B) (h2' : B) (t1 : list B) (t2 : list B) : ((@cons B h1' t1) = (@cons B h2' t2)) = (term13 B h1' h2' t1 t2).
Proof. exact (@lem1191806 B h1' h2' t1 t2). Qed.
Lemma lem1191808 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) : ((term21 A B h f t) = (term21 A B h' f t')) = (term169 A B h h' t f t').
Proof. exact (@lem1191807 B (f h) (f h') (@List.map A B f t) (@List.map A B f t')). Qed.
Lemma lem1192091 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) : ((term20 A B f h t) = (term20 A B f h' t')) = (term169 A B h h' t f t').
Proof. exact (TRANS (@lem1191804 A B h t h' f t') (@lem1191808 A B h h' t f t')). Qed.
Lemma lem1192092 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (q' : Prop) : term170 A B h h' t f t' q'.
Proof. exact (@lem1191288 A B f h t h' t' (term169 A B h h' t f t') q'). Qed.
Lemma lem1192093 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (q' : Prop) : term171 A B h h' t f t' q'.
Proof. exact (@lem1192092 A B h h' t f t' q' (@lem1192091 A B h h' t f t')). Qed.
Lemma lem1192098 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) (t2 : list A) : ((@cons A h1' t1) = (@cons A h2' t2)) = (term13 A h1' h2' t1 t2).
Proof. exact (EQ_MP (@lem1191205 A h1' h2' t1 t2) (@lem1191204 A h1' h2' t1 t2)). Qed.
Lemma lem1192099 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) (t2 : list A) : ((@cons A h1' t1) = (@cons A h2' t2)) = (term13 A h1' h2' t1 t2).
Proof. exact (@lem1192098 A h1' h2' t1 t2). Qed.
Lemma lem1192100 {A : Type'} (h : A) (h' : A) (t : list A) (t' : list A) : ((@cons A h t) = (@cons A h' t')) = (term13 A h h' t t').
Proof. exact (@lem1192099 A h h' t t'). Qed.
Lemma lem1192304 {A B : Type'} (f : A -> B) (h : A) (h' : A) (t : list A) (t' : list A) : term172 A B f h h' t t'.
Proof. exact (fun h0 : term169 A B h h' t f t' => @lem1192100 A h h' t t'). Qed.
Lemma lem1192305 {A B : Type'} (f : A -> B) (h : A) (h' : A) (t : list A) (t' : list A) : term173 A B f h h' t t'.
Proof. exact (@lem1192093 A B h h' t f t' (term13 A h h' t t')). Qed.
Lemma lem1192306 {A B : Type'} (f : A -> B) (h : A) (h' : A) (t : list A) (t' : list A) : (term113 A B f h t h' t') = (term174 A B f h h' t t').
Proof. exact (@lem1192305 A B f h h' t t' (@lem1192304 A B f h h' t t')). Qed.
Lemma lem1193343 {A B : Type'} (f : A -> B) (h : A) (t : list A) (h' : A) (t' : list A) : (term174 A B f h h' t t') = (term113 A B f h t h' t').
Proof. exact (SYM (@lem1192306 A B f h h' t t')). Qed.
Lemma lem1193345 (p : Prop) : p = (term175 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1193346 {A B : Type'} (f : A -> B) (h : A) (h' : A) (t : list A) (t' : list A) : (term174 A B f h h' t t') = (term176 A B f h h' t t').
Proof. exact (@lem1193345 (term174 A B f h h' t t')). Qed.
Lemma lem1193347 {A B : Type'} (f : A -> B) (h : A) (h' : A) (t : list A) (t' : list A) : (term176 A B f h h' t t') = (term174 A B f h h' t t').
Proof. exact (SYM (@lem1193346 A B f h h' t t')). Qed.
Lemma lem1193348 {A B : Type'} (f : A -> B) (h : A) (h' : A) (t : list A) (t' : list A) (h1 : term177 A B f h h' t t') : term177 A B f h h' t t'.
Proof. exact (h1). Qed.
Lemma lem1193351 {A B : Type'} (f : A -> B) (h : A) (h' : A) (t : list A) (t' : list A) (h1 : term178 A B f h h' t t') : term178 A B f h h' t t'.
Proof. exact (h1). Qed.
Lemma lem1193352 {A B : Type'} (f : A -> B) (h : A) (h' : A) (t : list A) (t' : list A) : term179 A B f h h' t t'.
Proof. exact (fun h0 : term178 A B f h h' t t' => @lem1193351 A B f h h' t t' h0). Qed.
Lemma lem1193353 {A B : Type'} (f : A -> B) (h : A) (h' : A) (t : list A) (t' : list A) (h1 : term179 A B f h h' t t') : term179 A B f h h' t t'.
Proof. exact (h1). Qed.
Lemma lem1193354 {A B : Type'} (f : A -> B) (h : A) (h' : A) (t : list A) (t' : list A) (h1 : term178 A B f h h' t t') : term178 A B f h h' t t'.
Proof. exact (h1). Qed.
Lemma lem1193355 {A B : Type'} (f : A -> B) (h : A) (h' : A) (t : list A) (t' : list A) (h1 : term178 A B f h h' t t') (h2 : term179 A B f h h' t t') : term178 A B f h h' t t'.
Proof. exact (@lem1193353 A B f h h' t t' h2 (@lem1193354 A B f h h' t t' h1)). Qed.
Lemma lem1193356 {A B : Type'} (f : A -> B) (h : A) (h' : A) (t : list A) (t' : list A) (h1 : term178 A B f h h' t t') : term180 A B f h h' t t'.
Proof. exact (fun h0 : term179 A B f h h' t t' => @lem1193355 A B f h h' t t' h1 h0). Qed.
Lemma lem1193357 {A B : Type'} (f : A -> B) (h : A) (h' : A) (t : list A) (t' : list A) (h1 : term179 A B f h h' t t') : term179 A B f h h' t t'.
Proof. exact (h1). Qed.
Lemma lem1193358 {A B : Type'} (f : A -> B) (h : A) (h' : A) (t : list A) (t' : list A) (h1 : term178 A B f h h' t t') (h2 : term179 A B f h h' t t') : term178 A B f h h' t t'.
Proof. exact (@lem1193356 A B f h h' t t' h1 (@lem1193357 A B f h h' t t' h2)). Qed.
Lemma lem1193359 {A B : Type'} (f : A -> B) (h : A) (h' : A) (t : list A) (t' : list A) (h1 : term179 A B f h h' t t') : term179 A B f h h' t t'.
Proof. exact (fun h0 : term178 A B f h h' t t' => @lem1193358 A B f h h' t t' h0 h1). Qed.
Lemma lem1193360 {A B : Type'} (f : A -> B) (h : A) (h' : A) (t : list A) (t' : list A) : term181 A B f h h' t t'.
Proof. exact (fun h0 : term179 A B f h h' t t' => @lem1193359 A B f h h' t t' h0). Qed.
Lemma lem1193363 {A B : Type'} (f : A -> B) (h : A) (h' : A) (t : list A) (t' : list A) : term179 A B f h h' t t'.
Proof. exact (@lem1193360 A B f h h' t t' (@lem1193352 A B f h h' t t')). Qed.
Lemma lem1193364 {A B : Type'} (f : A -> B) (h : A) (h' : A) (t : list A) (t' : list A) : term179 A B f h h' t t'.
Proof. exact (@lem1193363 A B f h h' t t'). Qed.
Lemma lem1193410 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1193411 {A B : Type'} (f : A -> B) (h : A) (h' : A) (t : list A) (t' : list A) : (term176 A B f h h' t t') = (term182 A B f h h' t t').
Proof. exact (@lem1193410 (term177 A B f h h' t t')). Qed.
Lemma lem1193413 (t : Prop) : (term183 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem1193414 {A B : Type'} (f : A -> B) (h : A) (h' : A) (t : list A) (t' : list A) : (term182 A B f h h' t t') = (term174 A B f h h' t t').
Proof. exact (@lem1193413 (term174 A B f h h' t t')). Qed.
Lemma lem1193417 {A B : Type'} (f : A -> B) (h : A) (h' : A) (t : list A) (t' : list A) : (term176 A B f h h' t t') = (term174 A B f h h' t t').
Proof. exact (TRANS (@lem1193411 A B f h h' t t') (@lem1193414 A B f h h' t t')). Qed.
Lemma lem1193422 {A B : Type'} (f : A -> B) (h : A) (t : list A) (t' : list A) : (term111 A B f h t t') = (term111 A B f h t t').
Proof. exact (eq_refl (term111 A B f h t t')). Qed.
Lemma lem1193423 {A B : Type'} (f : A -> B) (h : A) (h' : A) (t : list A) (t' : list A) : (term184 A B f h h' t t') = (term185 A B f h h' t t').
Proof. exact (MK_COMB (@lem1193422 A B f h t t') (@lem1193417 A B f h h' t t')). Qed.
Lemma lem1193426 {A B : Type'} (f : A -> B) (t : list A) : (term53 A B f t) = (term53 A B f t).
Proof. exact (eq_refl (term53 A B f t)). Qed.
Lemma lem1193427 {A B : Type'} (f : A -> B) (h : A) (h' : A) (t : list A) (t' : list A) : (term186 A B f h h' t t') = (term187 A B f h h' t t').
Proof. exact (MK_COMB (@lem1193426 A B f t) (@lem1193423 A B f h h' t t')). Qed.
Lemma lem1193430 {A B : Type'} (f : A -> B) : (term188 A B f) = (term188 A B f).
Proof. exact (eq_refl (term188 A B f)). Qed.
Lemma lem1193431 {A B : Type'} (f : A -> B) (h : A) (h' : A) (t : list A) (t' : list A) : (term178 A B f h h' t t') = (term189 A B f h h' t t').
Proof. exact (MK_COMB (@lem1193430 A B f) (@lem1193427 A B f h h' t t')). Qed.
Lemma lem1193434 {A B : Type'} (h : A) (h' : A) (t : list A) (t' : list A) : (term190 A B h h' t t') = (term191 A B h h' t t').
Proof. exact (fun_ext (fun f : A -> B => @lem1193431 A B f h h' t t')). Qed.
Lemma lem1193435 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem1193436 {A B : Type'} (h : A) (h' : A) (t : list A) (t' : list A) : (term192 A B h h' t t') = (term193 A B h h' t t').
Proof. exact (MK_COMB (@lem1193435 A B) (@lem1193434 A B h h' t t')). Qed.
Lemma lem1193441 {A B : Type'} (h' : A) (t : list A) (t' : list A) : (term194 A B h' t t') = (term195 A B h' t t').
Proof. exact (fun_ext (fun h : A => @lem1193436 A B h h' t t')). Qed.
Lemma lem1193442 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1193443 {A B : Type'} (h' : A) (t : list A) (t' : list A) : (term196 A B h' t t') = (term197 A B h' t t').
Proof. exact (MK_COMB (@lem1193442 A) (@lem1193441 A B h' t t')). Qed.
Lemma lem1193448 {A B : Type'} (t : list A) (t' : list A) : (term198 A B t t') = (term199 A B t t').
Proof. exact (fun_ext (fun h' : A => @lem1193443 A B h' t t')). Qed.
Lemma lem1193449 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1193450 {A B : Type'} (t : list A) (t' : list A) : (term200 A B t t') = (term201 A B t t').
Proof. exact (MK_COMB (@lem1193449 A) (@lem1193448 A B t t')). Qed.
Lemma lem1193455 {A B : Type'} (t' : list A) : (term202 A B t') = (term203 A B t').
Proof. exact (fun_ext (fun t : list A => @lem1193450 A B t t')). Qed.
Lemma lem1193456 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1193457 {A B : Type'} (t' : list A) : (term204 A B t') = (term205 A B t').
Proof. exact (MK_COMB (@lem1193456 A) (@lem1193455 A B t')). Qed.
Lemma lem1193462 {A B : Type'} : (term206 A B) = (term207 A B).
Proof. exact (fun_ext (fun t' : list A => @lem1193457 A B t')). Qed.
Lemma lem1193463 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1193472 {A B : Type'} : (term208 A B) = (term209 A B).
Proof. exact (MK_COMB (@lem1193463 A) (@lem1193462 A B)). Qed.
Lemma lem1193493 {A B : Type'} (f : A -> B) (h : A) (h' : A) (t : list A) (t' : list A) : (term185 A B f h h' t t') = (term185 A B f h h' t t').
Proof. exact (eq_refl (term185 A B f h h' t t')). Qed.
Lemma lem1193498 {A B : Type'} (f : A -> B) (t : list A) (m : list A) : (term210 A B f t m) = (term210 A B f t m).
Proof. exact (eq_refl (term210 A B f t m)). Qed.
Lemma lem1193499 {A B : Type'} (f : A -> B) (t : list A) : (term211 A B f t) = (term211 A B f t).
Proof. exact (fun_ext (fun m : list A => @lem1193498 A B f t m)). Qed.
Lemma lem1193500 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1193501 {A B : Type'} (f : A -> B) (t : list A) : (term51 A B f t) = (term51 A B f t).
Proof. exact (MK_COMB (@lem1193500 A) (@lem1193499 A B f t)). Qed.
Lemma lem1193502 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1193503 {A B : Type'} (f : A -> B) (t : list A) : (term53 A B f t) = (term53 A B f t).
Proof. exact (MK_COMB (@lem1193502) (@lem1193501 A B f t)). Qed.
Lemma lem1193504 {A B : Type'} (f : A -> B) (h : A) (h' : A) (t : list A) (t' : list A) : (term187 A B f h h' t t') = (term187 A B f h h' t t').
Proof. exact (MK_COMB (@lem1193503 A B f t) (@lem1193493 A B f h h' t t')). Qed.
Lemma lem1193509 {A B : Type'} (f : A -> B) (x : A) (y : A) : (term41 A B f x y) = (term41 A B f x y).
Proof. exact (eq_refl (term41 A B f x y)). Qed.
Lemma lem1193510 {A B : Type'} (f : A -> B) (x : A) : (term212 A B f x) = (term212 A B f x).
Proof. exact (fun_ext (fun y : A => @lem1193509 A B f x y)). Qed.
Lemma lem1193511 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1193512 {A B : Type'} (f : A -> B) (x : A) : (term42 A B f x) = (term42 A B f x).
Proof. exact (MK_COMB (@lem1193511 A) (@lem1193510 A B f x)). Qed.
Lemma lem1193513 {A B : Type'} (f : A -> B) : (term213 A B f) = (term213 A B f).
Proof. exact (fun_ext (fun x : A => @lem1193512 A B f x)). Qed.
Lemma lem1193514 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1193515 {A B : Type'} (f : A -> B) : (term1 A B f) = (term1 A B f).
Proof. exact (MK_COMB (@lem1193514 A) (@lem1193513 A B f)). Qed.
Lemma lem1193516 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1193517 {A B : Type'} (f : A -> B) : (term188 A B f) = (term188 A B f).
Proof. exact (MK_COMB (@lem1193516) (@lem1193515 A B f)). Qed.
Lemma lem1193518 {A B : Type'} (f : A -> B) (h : A) (h' : A) (t : list A) (t' : list A) : (term189 A B f h h' t t') = (term189 A B f h h' t t').
Proof. exact (MK_COMB (@lem1193517 A B f) (@lem1193504 A B f h h' t t')). Qed.
Lemma lem1193519 {A B : Type'} (h : A) (h' : A) (t : list A) (t' : list A) : (term191 A B h h' t t') = (term191 A B h h' t t').
Proof. exact (fun_ext (fun f : A -> B => @lem1193518 A B f h h' t t')). Qed.
Lemma lem1193520 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem1193521 {A B : Type'} (h : A) (h' : A) (t : list A) (t' : list A) : (term193 A B h h' t t') = (term193 A B h h' t t').
Proof. exact (MK_COMB (@lem1193520 A B) (@lem1193519 A B h h' t t')). Qed.
Lemma lem1193522 {A B : Type'} (h' : A) (t : list A) (t' : list A) : (term195 A B h' t t') = (term195 A B h' t t').
Proof. exact (fun_ext (fun h : A => @lem1193521 A B h h' t t')). Qed.
Lemma lem1193523 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1193524 {A B : Type'} (h' : A) (t : list A) (t' : list A) : (term197 A B h' t t') = (term197 A B h' t t').
Proof. exact (MK_COMB (@lem1193523 A) (@lem1193522 A B h' t t')). Qed.
Lemma lem1193525 {A B : Type'} (t : list A) (t' : list A) : (term199 A B t t') = (term199 A B t t').
Proof. exact (fun_ext (fun h' : A => @lem1193524 A B h' t t')). Qed.
Lemma lem1193526 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1193527 {A B : Type'} (t : list A) (t' : list A) : (term201 A B t t') = (term201 A B t t').
Proof. exact (MK_COMB (@lem1193526 A) (@lem1193525 A B t t')). Qed.
Lemma lem1193528 {A B : Type'} (t' : list A) : (term203 A B t') = (term203 A B t').
Proof. exact (fun_ext (fun t : list A => @lem1193527 A B t t')). Qed.
Lemma lem1193529 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1193530 {A B : Type'} (t' : list A) : (term205 A B t') = (term205 A B t').
Proof. exact (MK_COMB (@lem1193529 A) (@lem1193528 A B t')). Qed.
Lemma lem1193531 {A B : Type'} : (term207 A B) = (term207 A B).
Proof. exact (fun_ext (fun t' : list A => @lem1193530 A B t')). Qed.
Lemma lem1193532 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1193533 {A B : Type'} : (term209 A B) = (term209 A B).
Proof. exact (MK_COMB (@lem1193532 A) (@lem1193531 A B)). Qed.
Lemma lem1193602 {A B : Type'} : (term208 A B) = (term209 A B).
Proof. exact (TRANS (@lem1193472 A B) (@lem1193533 A B)). Qed.
Lemma lem1193603 {A B : Type'} : (term209 A B) = (term208 A B).
Proof. exact (SYM (@lem1193602 A B)). Qed.
Lemma lem1193604 {A B : Type'} (f : A -> B) (h1 : term1 A B f) : term1 A B f.
Proof. exact (h1). Qed.
Lemma lem1193605 {A B : Type'} (f : A -> B) (t : list A) (h1 : term51 A B f t) : term51 A B f t.
Proof. exact (h1). Qed.
Lemma lem1193606 {A B : Type'} (f : A -> B) (h : A) (t : list A) (t' : list A) (h1 : term109 A B f h t t') : term109 A B f h t t'.
Proof. exact (h1). Qed.
Lemma lem1193609 (p : Prop) : p = (term175 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1193610 {A : Type'} (h : A) (h' : A) (t : list A) (t' : list A) : (term13 A h h' t t') = (term214 A h h' t t').
Proof. exact (@lem1193609 (term13 A h h' t t')). Qed.
Lemma lem1193611 {A : Type'} (h : A) (h' : A) (t : list A) (t' : list A) : (term214 A h h' t t') = (term13 A h h' t t').
Proof. exact (SYM (@lem1193610 A h h' t t')). Qed.
Lemma lem1193612 {A : Type'} (h : A) (h' : A) (t : list A) (t' : list A) (h1 : term215 A h h' t t') : term215 A h h' t t'.
Proof. exact (h1). Qed.
Lemma lem1193619 {A B : Type'} (f : A -> B) (x : A) (y : A) : (term41 A B f x y) = (term216 A B f x y).
Proof. exact (@lem17265 ((f x) = (f y)) (x = y)). Qed.
Lemma lem1193620 {A B : Type'} (f : A -> B) (x : A) : (term212 A B f x) = (term217 A B f x).
Proof. exact (fun_ext (fun y : A => @lem1193619 A B f x y)). Qed.
Lemma lem1193621 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1193622 {A B : Type'} (f : A -> B) (x : A) : (term42 A B f x) = (term218 A B f x).
Proof. exact (MK_COMB (@lem1193621 A) (@lem1193620 A B f x)). Qed.
Lemma lem1193623 {A B : Type'} (f : A -> B) : (term213 A B f) = (term219 A B f).
Proof. exact (fun_ext (fun x : A => @lem1193622 A B f x)). Qed.
Lemma lem1193624 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1193681 {A B : Type'} (f : A -> B) : (term1 A B f) = (term220 A B f).
Proof. exact (MK_COMB (@lem1193624 A) (@lem1193623 A B f)). Qed.
Lemma lem1193682 {A B : Type'} (f : A -> B) (h1 : term1 A B f) : term220 A B f.
Proof. exact (EQ_MP (@lem1193681 A B f) (@lem1193604 A B f h1)). Qed.
Lemma lem1193689 {A B : Type'} (f : A -> B) (t : list A) (m : list A) : (term210 A B f t m) = (term221 A B f t m).
Proof. exact (@lem17265 ((@List.map A B f t) = (@List.map A B f m)) (t = m)). Qed.
Lemma lem1193690 {A B : Type'} (f : A -> B) (t : list A) : (term211 A B f t) = (term222 A B f t).
Proof. exact (fun_ext (fun m : list A => @lem1193689 A B f t m)). Qed.
Lemma lem1193691 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1193744 {A B : Type'} (f : A -> B) (t : list A) : (term51 A B f t) = (term223 A B f t).
Proof. exact (MK_COMB (@lem1193691 A) (@lem1193690 A B f t)). Qed.
Lemma lem1193745 {A B : Type'} (f : A -> B) (t : list A) (h1 : term51 A B f t) : term223 A B f t.
Proof. exact (EQ_MP (@lem1193744 A B f t) (@lem1193605 A B f t h1)). Qed.
Lemma lem1193756 {A B : Type'} (f : A -> B) (h : A) (t : list A) (t' : list A) : (term109 A B f h t t') = (term224 A B f h t t').
Proof. exact (@lem17265 ((term20 A B f h t) = (@List.map A B f t')) ((@cons A h t) = t')). Qed.
Lemma lem1193767 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term169 A B h h' t f t') : term169 A B h h' t f t'.
Proof. exact (h1). Qed.
Lemma lem1193778 {A : Type'} (h : A) (h' : A) (t : list A) (t' : list A) : (term215 A h h' t t') = (term225 A h h' t t').
Proof. exact (@lem17045 (h = h') (t = t')). Qed.
Lemma lem1193784 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem1193785 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1193786 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem1193791 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1193793 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem1193791 A B f x). Qed.
Lemma lem1193798 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1193799 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem1193798 A B f x). Qed.
Lemma lem1193801 {A B : Type'} (f : A -> B) (y : A) : (f y) = (@I (A -> B) f y).
Proof. exact (@lem1193799 A B f y). Qed.
Lemma lem1193802 {A B : Type'} (f : A -> B) (x : A) : (term226 A B f x) = (term227 A B f x).
Proof. exact (MK_COMB (@lem1193786 B) (@lem1193793 A B f x)). Qed.
Lemma lem1193803 {A B : Type'} (x : A) (f : A -> B) (y : A) : ((f x) = (f y)) = ((@I (A -> B) f x) = (@I (A -> B) f y)).
Proof. exact (MK_COMB (@lem1193802 A B f x) (@lem1193801 A B f y)). Qed.
Lemma lem1193804 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term228 A B x f y) = (term229 A B x f y).
Proof. exact (MK_COMB (@lem1193785) (@lem1193803 A B x f y)). Qed.
Lemma lem1193805 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1193806 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term230 A B x f y) = (term231 A B x f y).
Proof. exact (MK_COMB (@lem1193805) (@lem1193804 A B x f y)). Qed.
Lemma lem1193807 {A B : Type'} (f : A -> B) (x : A) (y : A) : (term216 A B f x y) = (term232 A B f x y).
Proof. exact (MK_COMB (@lem1193806 A B x f y) (@lem1193784 A x y)). Qed.
Lemma lem1193808 {A B : Type'} (f : A -> B) (x : A) : (term217 A B f x) = (term233 A B f x).
Proof. exact (fun_ext (fun y : A => @lem1193807 A B f x y)). Qed.
Lemma lem1193809 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1193810 {A B : Type'} (f : A -> B) (x : A) : (term218 A B f x) = (term234 A B f x).
Proof. exact (MK_COMB (@lem1193809 A) (@lem1193808 A B f x)). Qed.
Lemma lem1193811 {A B : Type'} (f : A -> B) : (term219 A B f) = (term235 A B f).
Proof. exact (fun_ext (fun x : A => @lem1193810 A B f x)). Qed.
Lemma lem1193812 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1193813 {A B : Type'} (f : A -> B) : (term220 A B f) = (term236 A B f).
Proof. exact (MK_COMB (@lem1193812 A) (@lem1193811 A B f)). Qed.
Lemma lem1193814 {A B : Type'} (f : A -> B) (h1 : term1 A B f) : term236 A B f.
Proof. exact (EQ_MP (@lem1193813 A B f) (@lem1193682 A B f h1)). Qed.
Lemma lem1193837 {A B : Type'} (f : A -> B) (t : list A) (m : list A) : (term221 A B f t m) = (term221 A B f t m).
Proof. exact (eq_refl (term221 A B f t m)). Qed.
Lemma lem1193838 {A B : Type'} (f : A -> B) (t : list A) : (term222 A B f t) = (term222 A B f t).
Proof. exact (fun_ext (fun m : list A => @lem1193837 A B f t m)). Qed.
Lemma lem1193839 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1193840 {A B : Type'} (f : A -> B) (t : list A) : (term223 A B f t) = (term223 A B f t).
Proof. exact (MK_COMB (@lem1193839 A) (@lem1193838 A B f t)). Qed.
Lemma lem1193841 {A B : Type'} (f : A -> B) (t : list A) (h1 : term51 A B f t) : term223 A B f t.
Proof. exact (EQ_MP (@lem1193840 A B f t) (@lem1193745 A B f t h1)). Qed.
Lemma lem1193873 {A B : Type'} (f : A -> B) (h : A) (t : list A) (t' : list A) (h1 : term109 A B f h t t') : term224 A B f h t t'.
Proof. exact (EQ_MP (@lem1193756 A B f h t t') (@lem1193606 A B f h t t' h1)). Qed.
Lemma lem1193886 {A B : Type'} (t : list A) (f : A -> B) (t' : list A) : ((@List.map A B f t) = (@List.map A B f t')) = ((@List.map A B f t) = (@List.map A B f t')).
Proof. exact (eq_refl ((@List.map A B f t) = (@List.map A B f t'))). Qed.
Lemma lem1193887 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem1193892 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1193893 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem1193892 A B f x). Qed.
Lemma lem1193895 {A B : Type'} (f : A -> B) (h : A) : (f h) = (@I (A -> B) f h).
Proof. exact (@lem1193893 A B f h). Qed.
Lemma lem1193900 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1193901 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem1193900 A B f x). Qed.
Lemma lem1193903 {A B : Type'} (f : A -> B) (h' : A) : (f h') = (@I (A -> B) f h').
Proof. exact (@lem1193901 A B f h'). Qed.
Lemma lem1193904 {A B : Type'} (f : A -> B) (h : A) : (term226 A B f h) = (term227 A B f h).
Proof. exact (MK_COMB (@lem1193887 B) (@lem1193895 A B f h)). Qed.
Lemma lem1193905 {A B : Type'} (h : A) (f : A -> B) (h' : A) : ((f h) = (f h')) = ((@I (A -> B) f h) = (@I (A -> B) f h')).
Proof. exact (MK_COMB (@lem1193904 A B f h) (@lem1193903 A B f h')). Qed.
Lemma lem1193906 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1193907 {A B : Type'} (h : A) (f : A -> B) (h' : A) : (term237 A B h f h') = (term238 A B h f h').
Proof. exact (MK_COMB (@lem1193906) (@lem1193905 A B h f h')). Qed.
Lemma lem1193908 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) : (term169 A B h h' t f t') = (term239 A B h h' t f t').
Proof. exact (MK_COMB (@lem1193907 A B h f h') (@lem1193886 A B t f t')). Qed.
Lemma lem1193909 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term169 A B h h' t f t') : term239 A B h h' t f t'.
Proof. exact (EQ_MP (@lem1193908 A B h h' t f t') (@lem1193767 A B h h' t f t' h1)). Qed.
Lemma lem1193927 {A : Type'} (h : A) (h' : A) (t : list A) (t' : list A) (h1 : term215 A h h' t t') : term225 A h h' t t'.
Proof. exact (EQ_MP (@lem1193778 A h h' t t') (@lem1193612 A h h' t t' h1)). Qed.
Lemma lem1193943 {A B : Type'} (f : A -> B) (x : A) (y : A) : (term232 A B f x y) = (term232 A B f x y).
Proof. exact (eq_refl (term232 A B f x y)). Qed.
Lemma lem1193944 {A B : Type'} (f : A -> B) (x : A) : (term233 A B f x) = (term233 A B f x).
Proof. exact (fun_ext (fun y : A => @lem1193943 A B f x y)). Qed.
Lemma lem1193945 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1193946 {A B : Type'} (f : A -> B) (x : A) : (term234 A B f x) = (term234 A B f x).
Proof. exact (MK_COMB (@lem1193945 A) (@lem1193944 A B f x)). Qed.
Lemma lem1193947 {A B : Type'} (f : A -> B) : (term235 A B f) = (term235 A B f).
Proof. exact (fun_ext (fun x : A => @lem1193946 A B f x)). Qed.
Lemma lem1193948 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1193950 {A B : Type'} (f : A -> B) : (term236 A B f) = (term236 A B f).
Proof. exact (MK_COMB (@lem1193948 A) (@lem1193947 A B f)). Qed.
Lemma lem1193951 {A B : Type'} (f : A -> B) (h1 : term1 A B f) : term236 A B f.
Proof. exact (EQ_MP (@lem1193950 A B f) (@lem1193814 A B f h1)). Qed.
Lemma lem1193976 {A : Type'} (h : A) (h' : A) (h1 : term240 A h h') : term240 A h h'.
Proof. exact (h1). Qed.
Lemma lem1193988 {A B : Type'} (f : A -> B) (x : A) (y : A) : (term232 A B f x y) = (term232 A B f x y).
Proof. exact (eq_refl (term232 A B f x y)). Qed.
Lemma lem1193989 {A B : Type'} (f : A -> B) (x : A) : (term233 A B f x) = (term233 A B f x).
Proof. exact (fun_ext (fun y : A => @lem1193988 A B f x y)). Qed.
Lemma lem1193990 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1193991 {A B : Type'} (f : A -> B) (x : A) : (term234 A B f x) = (term234 A B f x).
Proof. exact (MK_COMB (@lem1193990 A) (@lem1193989 A B f x)). Qed.
Lemma lem1193992 {A B : Type'} (f : A -> B) : (term235 A B f) = (term235 A B f).
Proof. exact (fun_ext (fun x : A => @lem1193991 A B f x)). Qed.
Lemma lem1193993 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1193995 {A B : Type'} (f : A -> B) : (term236 A B f) = (term236 A B f).
Proof. exact (MK_COMB (@lem1193993 A) (@lem1193992 A B f)). Qed.
Lemma lem1193996 {A B : Type'} (f : A -> B) (h1 : term1 A B f) : term236 A B f.
Proof. exact (EQ_MP (@lem1193995 A B f) (@lem1193814 A B f h1)). Qed.
Lemma lem1194021 {A : Type'} (h : A) (h' : A) (h1 : term240 A h h') : term240 A h h'.
Proof. exact (h1). Qed.
Lemma lem1194049 {A B : Type'} (f : A -> B) (t : list A) (m : list A) : (term221 A B f t m) = (term221 A B f t m).
Proof. exact (eq_refl (term221 A B f t m)). Qed.
Lemma lem1194050 {A B : Type'} (f : A -> B) (t : list A) : (term222 A B f t) = (term222 A B f t).
Proof. exact (fun_ext (fun m : list A => @lem1194049 A B f t m)). Qed.
Lemma lem1194051 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1194053 {A B : Type'} (f : A -> B) (t : list A) : (term223 A B f t) = (term223 A B f t).
Proof. exact (MK_COMB (@lem1194051 A) (@lem1194050 A B f t)). Qed.
Lemma lem1194054 {A B : Type'} (f : A -> B) (t : list A) (h1 : term51 A B f t) : term223 A B f t.
Proof. exact (EQ_MP (@lem1194053 A B f t) (@lem1193841 A B f t h1)). Qed.
Lemma lem1194066 {A : Type'} (t : list A) (t' : list A) (h1 : term241 A t t') : term241 A t t'.
Proof. exact (h1). Qed.
Lemma lem1194094 {A B : Type'} (f : A -> B) (t : list A) (m : list A) : (term221 A B f t m) = (term221 A B f t m).
Proof. exact (eq_refl (term221 A B f t m)). Qed.
Lemma lem1194095 {A B : Type'} (f : A -> B) (t : list A) : (term222 A B f t) = (term222 A B f t).
Proof. exact (fun_ext (fun m : list A => @lem1194094 A B f t m)). Qed.
Lemma lem1194096 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1194098 {A B : Type'} (f : A -> B) (t : list A) : (term223 A B f t) = (term223 A B f t).
Proof. exact (MK_COMB (@lem1194096 A) (@lem1194095 A B f t)). Qed.
Lemma lem1194099 {A B : Type'} (f : A -> B) (t : list A) (h1 : term51 A B f t) : term223 A B f t.
Proof. exact (EQ_MP (@lem1194098 A B f t) (@lem1193841 A B f t h1)). Qed.
Lemma lem1194111 {A : Type'} (t : list A) (t' : list A) (h1 : term241 A t t') : term241 A t t'.
Proof. exact (h1). Qed.
Lemma lem1194115 {A : Type'} (h : A) (t : list A) (t' : list A) (h1 : (@cons A h t) = t') : (@cons A h t) = t'.
Proof. exact (h1). Qed.
Lemma lem1194116 {A B : Type'} (_21228 : A) (f : A -> B) (h1 : term1 A B f) : term242 A B f _21228.
Proof. exact (@lem1193951 A B f h1 _21228). Qed.
Lemma lem1194117 {A B : Type'} (f : A -> B) (_21228 : A) : (term242 A B f _21228) = (term234 A B f _21228).
Proof. exact (eq_refl (term242 A B f _21228)). Qed.
Lemma lem1194118 {A B : Type'} (_21228 : A) (f : A -> B) (h1 : term1 A B f) : term234 A B f _21228.
Proof. exact (EQ_MP (@lem1194117 A B f _21228) (@lem1194116 A B _21228 f h1)). Qed.
Lemma lem1194119 {A B : Type'} (_21228 : A) (_21229 : A) (f : A -> B) (h1 : term1 A B f) : term243 A B f _21228 _21229.
Proof. exact (@lem1194118 A B _21228 f h1 _21229). Qed.
Lemma lem1194120 {A B : Type'} (f : A -> B) (_21228 : A) (_21229 : A) : (term243 A B f _21228 _21229) = (term232 A B f _21228 _21229).
Proof. exact (eq_refl (term243 A B f _21228 _21229)). Qed.
Lemma lem1194125 {A B : Type'} (_21231 : A) (f : A -> B) (h1 : term1 A B f) : term242 A B f _21231.
Proof. exact (@lem1193996 A B f h1 _21231). Qed.
Lemma lem1194126 {A B : Type'} (f : A -> B) (_21231 : A) : (term242 A B f _21231) = (term234 A B f _21231).
Proof. exact (eq_refl (term242 A B f _21231)). Qed.
Lemma lem1194127 {A B : Type'} (_21231 : A) (f : A -> B) (h1 : term1 A B f) : term234 A B f _21231.
Proof. exact (EQ_MP (@lem1194126 A B f _21231) (@lem1194125 A B _21231 f h1)). Qed.
Lemma lem1194128 {A B : Type'} (_21231 : A) (_21232 : A) (f : A -> B) (h1 : term1 A B f) : term243 A B f _21231 _21232.
Proof. exact (@lem1194127 A B _21231 f h1 _21232). Qed.
Lemma lem1194129 {A B : Type'} (f : A -> B) (_21231 : A) (_21232 : A) : (term243 A B f _21231 _21232) = (term232 A B f _21231 _21232).
Proof. exact (eq_refl (term243 A B f _21231 _21232)). Qed.
Lemma lem1194140 {A B : Type'} (_21236 : list A) (f : A -> B) (t : list A) (h1 : term51 A B f t) : term244 A B f t _21236.
Proof. exact (@lem1194054 A B f t h1 _21236). Qed.
Lemma lem1194141 {A B : Type'} (f : A -> B) (t : list A) (_21236 : list A) : (term244 A B f t _21236) = (term221 A B f t _21236).
Proof. exact (eq_refl (term244 A B f t _21236)). Qed.
Lemma lem1194149 {A B : Type'} (_21239 : list A) (f : A -> B) (t : list A) (h1 : term51 A B f t) : term244 A B f t _21239.
Proof. exact (@lem1194099 A B f t h1 _21239). Qed.
Lemma lem1194150 {A B : Type'} (f : A -> B) (t : list A) (_21239 : list A) : (term244 A B f t _21239) = (term221 A B f t _21239).
Proof. exact (eq_refl (term244 A B f t _21239)). Qed.
Lemma lem1194157 {A B : Type'} (_21228 : A) (_21229 : A) (f : A -> B) (h1 : term1 A B f) : term232 A B f _21228 _21229.
Proof. exact (EQ_MP (@lem1194120 A B f _21228 _21229) (@lem1194119 A B _21228 _21229 f h1)). Qed.
Lemma lem1194169 {A : Type'} (h : A) (h' : A) (h1 : term240 A h h') : term240 A h h'.
Proof. exact (h1). Qed.
Lemma lem1194189 {A : Type'} (h : A) (h' : A) (h1 : term240 A h h') : term240 A h h'.
Proof. exact (h1). Qed.
Lemma lem1194203 {A B : Type'} (_21236 : list A) (f : A -> B) (t : list A) (h1 : term51 A B f t) : term221 A B f t _21236.
Proof. exact (EQ_MP (@lem1194141 A B f t _21236) (@lem1194140 A B _21236 f t h1)). Qed.
Lemma lem1194209 {A : Type'} (t : list A) (t' : list A) (h1 : term241 A t t') : term241 A t t'.
Proof. exact (h1). Qed.
Lemma lem1194227 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term169 A B h h' t f t') : (@List.map A B f t) = (@List.map A B f t').
Proof. exact (proj2 (@lem1193909 A B h h' t f t' h1)). Qed.
Lemma lem1194229 {A : Type'} (t : list A) (t' : list A) (h1 : term241 A t t') : term241 A t t'.
Proof. exact (h1). Qed.
Lemma lem1194231 {A : Type'} (h : A) (t : list A) (t' : list A) (h1 : (@cons A h t) = t') : (@cons A h t) = t'.
Proof. exact (h1). Qed.
Lemma lem1194260 {A B : Type'} (_21231 : A) (_21232 : A) (f : A -> B) (h1 : term1 A B f) : term232 A B f _21231 _21232.
Proof. exact (EQ_MP (@lem1194129 A B f _21231 _21232) (@lem1194128 A B _21231 _21232 f h1)). Qed.
Lemma lem1194315 {A : Type'} (h : A) (h' : A) (h1 : term240 A h h') : term240 A h h'.
Proof. exact (h1). Qed.
Lemma lem1194316 {A : Type'} (h : A) (t : list A) (t' : list A) (h1 : (@cons A h t) = t') : t' = (@cons A h t).
Proof. exact (SYM (@lem1194231 A h t t' h1)). Qed.
Lemma lem1194358 {A B : Type'} (_21239 : list A) (f : A -> B) (t : list A) (h1 : term51 A B f t) : term221 A B f t _21239.
Proof. exact (EQ_MP (@lem1194150 A B f t _21239) (@lem1194149 A B _21239 f t h1)). Qed.
Lemma lem1194373 {A B : Type'} (t : list A) (f : A -> B) : (term245 A B t f) = (term245 A B t f).
Proof. exact (eq_refl (term245 A B t f)). Qed.
Lemma lem1194374 {A B : Type'} (f : A -> B) (h : A) (t : list A) (t' : list A) (h1 : (@cons A h t) = t') : (term246 A B t f t') = (term247 A B f h t).
Proof. exact (MK_COMB (@lem1194373 A B t f) (@lem1194316 A h t t' h1)). Qed.
Lemma lem1194375 {A B : Type'} (f : A -> B) (h : A) (t : list A) : (term247 A B f h t) = ((@List.map A B f t) = (term20 A B f h t)).
Proof. exact (eq_refl (term247 A B f h t)). Qed.
Lemma lem1194376 {A B : Type'} (t : list A) (f : A -> B) (t' : list A) : (term248 A B t f t') = (term248 A B t f t').
Proof. exact (eq_refl (term248 A B t f t')). Qed.
Lemma lem1194377 {A B : Type'} (t' : list A) (f : A -> B) (h : A) (t : list A) : ((term246 A B t f t') = (term247 A B f h t)) = ((term246 A B t f t') = ((@List.map A B f t) = (term20 A B f h t))).
Proof. exact (MK_COMB (@lem1194376 A B t f t') (@lem1194375 A B f h t)). Qed.
Lemma lem1194378 {A B : Type'} (t : list A) (f : A -> B) (t' : list A) : (term246 A B t f t') = ((@List.map A B f t) = (@List.map A B f t')).
Proof. exact (eq_refl (term246 A B t f t')). Qed.
Lemma lem1194379 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1194380 {A B : Type'} (t : list A) (f : A -> B) (t' : list A) : (term248 A B t f t') = (term249 A B t f t').
Proof. exact (MK_COMB (@lem1194379) (@lem1194378 A B t f t')). Qed.
Lemma lem1194381 {A B : Type'} (f : A -> B) (h : A) (t : list A) : ((@List.map A B f t) = (term20 A B f h t)) = ((@List.map A B f t) = (term20 A B f h t)).
Proof. exact (eq_refl ((@List.map A B f t) = (term20 A B f h t))). Qed.
Lemma lem1194382 {A B : Type'} (t' : list A) (f : A -> B) (h : A) (t : list A) : ((term246 A B t f t') = ((@List.map A B f t) = (term20 A B f h t))) = (((@List.map A B f t) = (@List.map A B f t')) = ((@List.map A B f t) = (term20 A B f h t))).
Proof. exact (MK_COMB (@lem1194380 A B t f t') (@lem1194381 A B f h t)). Qed.
Lemma lem1194383 {A B : Type'} (t' : list A) (f : A -> B) (h : A) (t : list A) : ((term246 A B t f t') = (term247 A B f h t)) = (((@List.map A B f t) = (@List.map A B f t')) = ((@List.map A B f t) = (term20 A B f h t))).
Proof. exact (TRANS (@lem1194377 A B t' f h t) (@lem1194382 A B t' f h t)). Qed.
Lemma lem1194384 {A B : Type'} (f : A -> B) (h : A) (t : list A) (t' : list A) (h1 : (@cons A h t) = t') : ((@List.map A B f t) = (@List.map A B f t')) = ((@List.map A B f t) = (term20 A B f h t)).
Proof. exact (EQ_MP (@lem1194383 A B t' f h t) (@lem1194374 A B f h t t' h1)). Qed.
Lemma lem1194386 {A : Type'} (t : list A) : (term250 A t) = (term250 A t).
Proof. exact (eq_refl (term250 A t)). Qed.
Lemma lem1194387 {A : Type'} (h : A) (t : list A) (t' : list A) (h1 : (@cons A h t) = t') : (term251 A t t') = (term252 A h t).
Proof. exact (MK_COMB (@lem1194386 A t) (@lem1194316 A h t t' h1)). Qed.
Lemma lem1194388 {A : Type'} (h : A) (t : list A) : (term252 A h t) = (term253 A h t).
Proof. exact (eq_refl (term252 A h t)). Qed.
Lemma lem1194389 {A : Type'} (t : list A) (t' : list A) : (term254 A t t') = (term254 A t t').
Proof. exact (eq_refl (term254 A t t')). Qed.
Lemma lem1194390 {A : Type'} (t' : list A) (h : A) (t : list A) : ((term251 A t t') = (term252 A h t)) = ((term251 A t t') = (term253 A h t)).
Proof. exact (MK_COMB (@lem1194389 A t t') (@lem1194388 A h t)). Qed.
Lemma lem1194391 {A : Type'} (t : list A) (t' : list A) : (term251 A t t') = (term241 A t t').
Proof. exact (eq_refl (term251 A t t')). Qed.
Lemma lem1194392 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1194393 {A : Type'} (t : list A) (t' : list A) : (term254 A t t') = (term255 A t t').
Proof. exact (MK_COMB (@lem1194392) (@lem1194391 A t t')). Qed.
Lemma lem1194394 {A : Type'} (h : A) (t : list A) : (term253 A h t) = (term253 A h t).
Proof. exact (eq_refl (term253 A h t)). Qed.
Lemma lem1194395 {A : Type'} (t' : list A) (h : A) (t : list A) : ((term251 A t t') = (term253 A h t)) = ((term241 A t t') = (term253 A h t)).
Proof. exact (MK_COMB (@lem1194393 A t t') (@lem1194394 A h t)). Qed.
Lemma lem1194396 {A : Type'} (t' : list A) (h : A) (t : list A) : ((term251 A t t') = (term252 A h t)) = ((term241 A t t') = (term253 A h t)).
Proof. exact (TRANS (@lem1194390 A t' h t) (@lem1194395 A t' h t)). Qed.
Lemma lem1194397 {A : Type'} (h : A) (t : list A) (t' : list A) (h1 : (@cons A h t) = t') : (term241 A t t') = (term253 A h t).
Proof. exact (EQ_MP (@lem1194396 A t' h t) (@lem1194387 A h t t' h1)). Qed.
Lemma lem1194398 {A : Type'} (h : A) (t : list A) (t' : list A) (h1 : term241 A t t') (h2 : (@cons A h t) = t') : term253 A h t.
Proof. exact (EQ_MP (@lem1194397 A h t t' h2) (@lem1194229 A t t' h1)). Qed.
Lemma lem1194455 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term169 A B h h' t f t') : (@I (A -> B) f h) = (@I (A -> B) f h').
Proof. exact (proj1 (@lem1193909 A B h h' t f t' h1)). Qed.
Lemma lem1194456 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term169 A B h h' t f t') : term256 A B h f h'.
Proof. exact (fun h0 : term229 A B h f h' => @lem1194455 A B h h' t f t' h1). Qed.
Lemma lem1194458 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1194459 {A B : Type'} (h : A) (f : A -> B) (h' : A) : (term256 A B h f h') = ((@I (A -> B) f h) = (@I (A -> B) f h')).
Proof. exact (@lem1194458 ((@I (A -> B) f h) = (@I (A -> B) f h'))). Qed.
Lemma lem1194460 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term169 A B h h' t f t') : (@I (A -> B) f h) = (@I (A -> B) f h').
Proof. exact (EQ_MP (@lem1194459 A B h f h') (@lem1194456 A B h h' t f t' h1)). Qed.
Lemma lem1194466 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1194467 {A B : Type'} (_21228 : A) (f : A -> B) (_21229 : A) : (term232 A B f _21228 _21229) = (term258 A B _21228 f _21229).
Proof. exact (@lem1194466 (_21228 = _21229) (term229 A B _21228 f _21229)). Qed.
Lemma lem1194477 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1194478 {A B : Type'} (_21228 : A) (f : A -> B) (_21229 : A) : (term259 A B f _21228 _21229) = (term260 A B _21228 f _21229).
Proof. exact (MK_COMB (@lem1194477) (@lem1194467 A B _21228 f _21229)). Qed.
Lemma lem1194488 {A B : Type'} (_21228 : A) (f : A -> B) (_21229 : A) : (term258 A B _21228 f _21229) = (term258 A B _21228 f _21229).
Proof. exact (eq_refl (term258 A B _21228 f _21229)). Qed.
Lemma lem1194489 {A B : Type'} (_21228 : A) (f : A -> B) (_21229 : A) : ((term232 A B f _21228 _21229) = (term258 A B _21228 f _21229)) = ((term258 A B _21228 f _21229) = (term258 A B _21228 f _21229)).
Proof. exact (MK_COMB (@lem1194478 A B _21228 f _21229) (@lem1194488 A B _21228 f _21229)). Qed.
Lemma lem1194491 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1194492 (x : Prop) : (x = x) = True.
Proof. exact (@lem1194491 Prop x). Qed.
Lemma lem1194493 {A B : Type'} (_21228 : A) (f : A -> B) (_21229 : A) : ((term258 A B _21228 f _21229) = (term258 A B _21228 f _21229)) = True.
Proof. exact (@lem1194492 (term258 A B _21228 f _21229)). Qed.
Lemma lem1194494 {A B : Type'} (_21228 : A) (f : A -> B) (_21229 : A) : ((term232 A B f _21228 _21229) = (term258 A B _21228 f _21229)) = True.
Proof. exact (TRANS (@lem1194489 A B _21228 f _21229) (@lem1194493 A B _21228 f _21229)). Qed.
Lemma lem1194495 {A B : Type'} (_21228 : A) (f : A -> B) (_21229 : A) : True = ((term232 A B f _21228 _21229) = (term258 A B _21228 f _21229)).
Proof. exact (SYM (@lem1194494 A B _21228 f _21229)). Qed.
Lemma lem1194496 {A B : Type'} (_21228 : A) (f : A -> B) (_21229 : A) : (term232 A B f _21228 _21229) = (term258 A B _21228 f _21229).
Proof. exact (EQ_MP (@lem1194495 A B _21228 f _21229) (@lem0)). Qed.
Lemma lem1194497 {A B : Type'} (_21228 : A) (_21229 : A) (f : A -> B) (h1 : term1 A B f) : term258 A B _21228 f _21229.
Proof. exact (EQ_MP (@lem1194496 A B _21228 f _21229) (@lem1194157 A B _21228 _21229 f h1)). Qed.
Lemma lem1194499 (b : Prop) (a : Prop) : (a \/ b) = (term261 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1194500 {A B : Type'} (f : A -> B) (_21228 : A) (_21229 : A) : (term258 A B _21228 f _21229) = (term262 A B f _21228 _21229).
Proof. exact (@lem1194499 (term229 A B _21228 f _21229) (_21228 = _21229)). Qed.
Lemma lem1194502 (a : Prop) : (term183 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1194503 {A B : Type'} (_21228 : A) (f : A -> B) (_21229 : A) : (term263 A B _21228 f _21229) = ((@I (A -> B) f _21228) = (@I (A -> B) f _21229)).
Proof. exact (@lem1194502 ((@I (A -> B) f _21228) = (@I (A -> B) f _21229))). Qed.
Lemma lem1194504 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1194505 {A B : Type'} (_21228 : A) (f : A -> B) (_21229 : A) : (term264 A B _21228 f _21229) = (term265 A B _21228 f _21229).
Proof. exact (MK_COMB (@lem1194504) (@lem1194503 A B _21228 f _21229)). Qed.
Lemma lem1194506 {A : Type'} (_21228 : A) (_21229 : A) : (_21228 = _21229) = (_21228 = _21229).
Proof. exact (eq_refl (_21228 = _21229)). Qed.
Lemma lem1194507 {A B : Type'} (f : A -> B) (_21228 : A) (_21229 : A) : (term262 A B f _21228 _21229) = (term266 A B f _21228 _21229).
Proof. exact (MK_COMB (@lem1194505 A B _21228 f _21229) (@lem1194506 A _21228 _21229)). Qed.
Lemma lem1194508 {A B : Type'} (f : A -> B) (_21228 : A) (_21229 : A) : (term258 A B _21228 f _21229) = (term266 A B f _21228 _21229).
Proof. exact (TRANS (@lem1194500 A B f _21228 _21229) (@lem1194507 A B f _21228 _21229)). Qed.
Lemma lem1194511 {A B : Type'} (_21228 : A) (_21229 : A) (f : A -> B) (h1 : term1 A B f) : term266 A B f _21228 _21229.
Proof. exact (EQ_MP (@lem1194508 A B f _21228 _21229) (@lem1194497 A B _21228 _21229 f h1)). Qed.
Lemma lem1194512 {A B : Type'} (_21228 : A) (_21229 : A) (f : A -> B) (h1 : term1 A B f) : term266 A B f _21228 _21229.
Proof. exact (@lem1194511 A B _21228 _21229 f h1). Qed.
Lemma lem1194513 {A B : Type'} (h : A) (h' : A) (f : A -> B) (h1 : term1 A B f) : term266 A B f h h'.
Proof. exact (@lem1194512 A B h h' f h1). Qed.
Lemma lem1194516 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term1 A B f) (h2 : term169 A B h h' t f t') : h = h'.
Proof. exact (@lem1194513 A B h h' f h1 (@lem1194460 A B h h' t f t' h2)). Qed.
Lemma lem1194517 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term1 A B f) (h2 : term169 A B h h' t f t') : term267 A h h'.
Proof. exact (fun h0 : term240 A h h' => @lem1194516 A B h h' t f t' h1 h2). Qed.
Lemma lem1194519 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1194520 {A : Type'} (h : A) (h' : A) : (term267 A h h') = (h = h').
Proof. exact (@lem1194519 (h = h')). Qed.
Lemma lem1194521 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term1 A B f) (h2 : term169 A B h h' t f t') : h = h'.
Proof. exact (EQ_MP (@lem1194520 A h h') (@lem1194517 A B h h' t f t' h1 h2)). Qed.
Lemma lem1194524 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1194526 {A : Type'} (h : A) (h' : A) : (term240 A h h') = (term268 A h h').
Proof. exact (@lem1194524 (h = h')). Qed.
Lemma lem1194529 {A : Type'} (h : A) (h' : A) (h1 : term240 A h h') : term268 A h h'.
Proof. exact (EQ_MP (@lem1194526 A h h') (@lem1194169 A h h' h1)). Qed.
Lemma lem1194532 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term1 A B f) (h2 : term240 A h h') (h3 : term169 A B h h' t f t') : False.
Proof. exact (@lem1194529 A h h' h2 (@lem1194521 A B h h' t f t' h1 h3)). Qed.
Lemma lem1194533 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term1 A B f) (h2 : term240 A h h') (h3 : term169 A B h h' t f t') : term269.
Proof. exact (fun h0 : ~ False => @lem1194532 A B h h' t f t' h1 h2 h3). Qed.
Lemma lem1194535 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1194536 : term269 = False.
Proof. exact (@lem1194535 False). Qed.
Lemma lem1194537 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term1 A B f) (h2 : term240 A h h') (h3 : term169 A B h h' t f t') : False.
Proof. exact (EQ_MP (@lem1194536) (@lem1194533 A B h h' t f t' h1 h2 h3)). Qed.
Lemma lem1194594 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term169 A B h h' t f t') : (@I (A -> B) f h) = (@I (A -> B) f h').
Proof. exact (proj1 (@lem1193909 A B h h' t f t' h1)). Qed.
Lemma lem1194595 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term169 A B h h' t f t') : term256 A B h f h'.
Proof. exact (fun h0 : term229 A B h f h' => @lem1194594 A B h h' t f t' h1). Qed.
Lemma lem1194597 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1194598 {A B : Type'} (h : A) (f : A -> B) (h' : A) : (term256 A B h f h') = ((@I (A -> B) f h) = (@I (A -> B) f h')).
Proof. exact (@lem1194597 ((@I (A -> B) f h) = (@I (A -> B) f h'))). Qed.
Lemma lem1194599 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term169 A B h h' t f t') : (@I (A -> B) f h) = (@I (A -> B) f h').
Proof. exact (EQ_MP (@lem1194598 A B h f h') (@lem1194595 A B h h' t f t' h1)). Qed.
Lemma lem1194605 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1194606 {A B : Type'} (_21231 : A) (f : A -> B) (_21232 : A) : (term232 A B f _21231 _21232) = (term258 A B _21231 f _21232).
Proof. exact (@lem1194605 (_21231 = _21232) (term229 A B _21231 f _21232)). Qed.
Lemma lem1194616 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1194617 {A B : Type'} (_21231 : A) (f : A -> B) (_21232 : A) : (term259 A B f _21231 _21232) = (term260 A B _21231 f _21232).
Proof. exact (MK_COMB (@lem1194616) (@lem1194606 A B _21231 f _21232)). Qed.
Lemma lem1194627 {A B : Type'} (_21231 : A) (f : A -> B) (_21232 : A) : (term258 A B _21231 f _21232) = (term258 A B _21231 f _21232).
Proof. exact (eq_refl (term258 A B _21231 f _21232)). Qed.
Lemma lem1194628 {A B : Type'} (_21231 : A) (f : A -> B) (_21232 : A) : ((term232 A B f _21231 _21232) = (term258 A B _21231 f _21232)) = ((term258 A B _21231 f _21232) = (term258 A B _21231 f _21232)).
Proof. exact (MK_COMB (@lem1194617 A B _21231 f _21232) (@lem1194627 A B _21231 f _21232)). Qed.
Lemma lem1194630 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1194631 (x : Prop) : (x = x) = True.
Proof. exact (@lem1194630 Prop x). Qed.
Lemma lem1194632 {A B : Type'} (_21231 : A) (f : A -> B) (_21232 : A) : ((term258 A B _21231 f _21232) = (term258 A B _21231 f _21232)) = True.
Proof. exact (@lem1194631 (term258 A B _21231 f _21232)). Qed.
Lemma lem1194633 {A B : Type'} (_21231 : A) (f : A -> B) (_21232 : A) : ((term232 A B f _21231 _21232) = (term258 A B _21231 f _21232)) = True.
Proof. exact (TRANS (@lem1194628 A B _21231 f _21232) (@lem1194632 A B _21231 f _21232)). Qed.
Lemma lem1194634 {A B : Type'} (_21231 : A) (f : A -> B) (_21232 : A) : True = ((term232 A B f _21231 _21232) = (term258 A B _21231 f _21232)).
Proof. exact (SYM (@lem1194633 A B _21231 f _21232)). Qed.
Lemma lem1194635 {A B : Type'} (_21231 : A) (f : A -> B) (_21232 : A) : (term232 A B f _21231 _21232) = (term258 A B _21231 f _21232).
Proof. exact (EQ_MP (@lem1194634 A B _21231 f _21232) (@lem0)). Qed.
Lemma lem1194636 {A B : Type'} (_21231 : A) (_21232 : A) (f : A -> B) (h1 : term1 A B f) : term258 A B _21231 f _21232.
Proof. exact (EQ_MP (@lem1194635 A B _21231 f _21232) (@lem1194260 A B _21231 _21232 f h1)). Qed.
Lemma lem1194638 (b : Prop) (a : Prop) : (a \/ b) = (term261 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1194639 {A B : Type'} (f : A -> B) (_21231 : A) (_21232 : A) : (term258 A B _21231 f _21232) = (term262 A B f _21231 _21232).
Proof. exact (@lem1194638 (term229 A B _21231 f _21232) (_21231 = _21232)). Qed.
Lemma lem1194641 (a : Prop) : (term183 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1194642 {A B : Type'} (_21231 : A) (f : A -> B) (_21232 : A) : (term263 A B _21231 f _21232) = ((@I (A -> B) f _21231) = (@I (A -> B) f _21232)).
Proof. exact (@lem1194641 ((@I (A -> B) f _21231) = (@I (A -> B) f _21232))). Qed.
Lemma lem1194643 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1194644 {A B : Type'} (_21231 : A) (f : A -> B) (_21232 : A) : (term264 A B _21231 f _21232) = (term265 A B _21231 f _21232).
Proof. exact (MK_COMB (@lem1194643) (@lem1194642 A B _21231 f _21232)). Qed.
Lemma lem1194645 {A : Type'} (_21231 : A) (_21232 : A) : (_21231 = _21232) = (_21231 = _21232).
Proof. exact (eq_refl (_21231 = _21232)). Qed.
Lemma lem1194646 {A B : Type'} (f : A -> B) (_21231 : A) (_21232 : A) : (term262 A B f _21231 _21232) = (term266 A B f _21231 _21232).
Proof. exact (MK_COMB (@lem1194644 A B _21231 f _21232) (@lem1194645 A _21231 _21232)). Qed.
Lemma lem1194647 {A B : Type'} (f : A -> B) (_21231 : A) (_21232 : A) : (term258 A B _21231 f _21232) = (term266 A B f _21231 _21232).
Proof. exact (TRANS (@lem1194639 A B f _21231 _21232) (@lem1194646 A B f _21231 _21232)). Qed.
Lemma lem1194650 {A B : Type'} (_21231 : A) (_21232 : A) (f : A -> B) (h1 : term1 A B f) : term266 A B f _21231 _21232.
Proof. exact (EQ_MP (@lem1194647 A B f _21231 _21232) (@lem1194636 A B _21231 _21232 f h1)). Qed.
Lemma lem1194651 {A B : Type'} (_21231 : A) (_21232 : A) (f : A -> B) (h1 : term1 A B f) : term266 A B f _21231 _21232.
Proof. exact (@lem1194650 A B _21231 _21232 f h1). Qed.
Lemma lem1194652 {A B : Type'} (h : A) (h' : A) (f : A -> B) (h1 : term1 A B f) : term266 A B f h h'.
Proof. exact (@lem1194651 A B h h' f h1). Qed.
Lemma lem1194655 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term1 A B f) (h2 : term169 A B h h' t f t') : h = h'.
Proof. exact (@lem1194652 A B h h' f h1 (@lem1194599 A B h h' t f t' h2)). Qed.
Lemma lem1194656 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term1 A B f) (h2 : term169 A B h h' t f t') : term267 A h h'.
Proof. exact (fun h0 : term240 A h h' => @lem1194655 A B h h' t f t' h1 h2). Qed.
Lemma lem1194658 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1194659 {A : Type'} (h : A) (h' : A) : (term267 A h h') = (h = h').
Proof. exact (@lem1194658 (h = h')). Qed.
Lemma lem1194660 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term1 A B f) (h2 : term169 A B h h' t f t') : h = h'.
Proof. exact (EQ_MP (@lem1194659 A h h') (@lem1194656 A B h h' t f t' h1 h2)). Qed.
Lemma lem1194663 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1194665 {A : Type'} (h : A) (h' : A) : (term240 A h h') = (term268 A h h').
Proof. exact (@lem1194663 (h = h')). Qed.
Lemma lem1194668 {A : Type'} (h : A) (h' : A) (h1 : term240 A h h') : term268 A h h'.
Proof. exact (EQ_MP (@lem1194665 A h h') (@lem1194315 A h h' h1)). Qed.
Lemma lem1194671 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term1 A B f) (h2 : term240 A h h') (h3 : term169 A B h h' t f t') : False.
Proof. exact (@lem1194668 A h h' h2 (@lem1194660 A B h h' t f t' h1 h3)). Qed.
Lemma lem1194672 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term1 A B f) (h2 : term240 A h h') (h3 : term169 A B h h' t f t') : term269.
Proof. exact (fun h0 : ~ False => @lem1194671 A B h h' t f t' h1 h2 h3). Qed.
Lemma lem1194674 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1194675 : term269 = False.
Proof. exact (@lem1194674 False). Qed.
Lemma lem1194676 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term1 A B f) (h2 : term240 A h h') (h3 : term169 A B h h' t f t') : False.
Proof. exact (EQ_MP (@lem1194675) (@lem1194672 A B h h' t f t' h1 h2 h3)). Qed.
Lemma lem1194733 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term169 A B h h' t f t') : (@List.map A B f t) = (@List.map A B f t').
Proof. exact (proj2 (@lem1193909 A B h h' t f t' h1)). Qed.
Lemma lem1194734 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term169 A B h h' t f t') : term270 A B t f t'.
Proof. exact (fun h0 : term271 A B t f t' => @lem1194733 A B h h' t f t' h1). Qed.
Lemma lem1194736 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1194737 {A B : Type'} (t : list A) (f : A -> B) (t' : list A) : (term270 A B t f t') = ((@List.map A B f t) = (@List.map A B f t')).
Proof. exact (@lem1194736 ((@List.map A B f t) = (@List.map A B f t'))). Qed.
Lemma lem1194738 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term169 A B h h' t f t') : (@List.map A B f t) = (@List.map A B f t').
Proof. exact (EQ_MP (@lem1194737 A B t f t') (@lem1194734 A B h h' t f t' h1)). Qed.
Lemma lem1194744 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1194745 {A B : Type'} (t : list A) (f : A -> B) (_21236 : list A) : (term221 A B f t _21236) = (term272 A B t f _21236).
Proof. exact (@lem1194744 (t = _21236) (term271 A B t f _21236)). Qed.
Lemma lem1194755 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1194756 {A B : Type'} (t : list A) (f : A -> B) (_21236 : list A) : (term273 A B f t _21236) = (term274 A B t f _21236).
Proof. exact (MK_COMB (@lem1194755) (@lem1194745 A B t f _21236)). Qed.
Lemma lem1194766 {A B : Type'} (t : list A) (f : A -> B) (_21236 : list A) : (term272 A B t f _21236) = (term272 A B t f _21236).
Proof. exact (eq_refl (term272 A B t f _21236)). Qed.
Lemma lem1194767 {A B : Type'} (t : list A) (f : A -> B) (_21236 : list A) : ((term221 A B f t _21236) = (term272 A B t f _21236)) = ((term272 A B t f _21236) = (term272 A B t f _21236)).
Proof. exact (MK_COMB (@lem1194756 A B t f _21236) (@lem1194766 A B t f _21236)). Qed.
Lemma lem1194769 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1194770 (x : Prop) : (x = x) = True.
Proof. exact (@lem1194769 Prop x). Qed.
Lemma lem1194771 {A B : Type'} (t : list A) (f : A -> B) (_21236 : list A) : ((term272 A B t f _21236) = (term272 A B t f _21236)) = True.
Proof. exact (@lem1194770 (term272 A B t f _21236)). Qed.
Lemma lem1194772 {A B : Type'} (t : list A) (f : A -> B) (_21236 : list A) : ((term221 A B f t _21236) = (term272 A B t f _21236)) = True.
Proof. exact (TRANS (@lem1194767 A B t f _21236) (@lem1194771 A B t f _21236)). Qed.
Lemma lem1194773 {A B : Type'} (t : list A) (f : A -> B) (_21236 : list A) : True = ((term221 A B f t _21236) = (term272 A B t f _21236)).
Proof. exact (SYM (@lem1194772 A B t f _21236)). Qed.
Lemma lem1194774 {A B : Type'} (t : list A) (f : A -> B) (_21236 : list A) : (term221 A B f t _21236) = (term272 A B t f _21236).
Proof. exact (EQ_MP (@lem1194773 A B t f _21236) (@lem0)). Qed.
Lemma lem1194775 {A B : Type'} (_21236 : list A) (f : A -> B) (t : list A) (h1 : term51 A B f t) : term272 A B t f _21236.
Proof. exact (EQ_MP (@lem1194774 A B t f _21236) (@lem1194203 A B _21236 f t h1)). Qed.
Lemma lem1194777 (b : Prop) (a : Prop) : (a \/ b) = (term261 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1194778 {A B : Type'} (f : A -> B) (t : list A) (_21236 : list A) : (term272 A B t f _21236) = (term275 A B f t _21236).
Proof. exact (@lem1194777 (term271 A B t f _21236) (t = _21236)). Qed.
Lemma lem1194780 (a : Prop) : (term183 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1194781 {A B : Type'} (t : list A) (f : A -> B) (_21236 : list A) : (term276 A B t f _21236) = ((@List.map A B f t) = (@List.map A B f _21236)).
Proof. exact (@lem1194780 ((@List.map A B f t) = (@List.map A B f _21236))). Qed.
Lemma lem1194782 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1194783 {A B : Type'} (t : list A) (f : A -> B) (_21236 : list A) : (term277 A B t f _21236) = (term278 A B t f _21236).
Proof. exact (MK_COMB (@lem1194782) (@lem1194781 A B t f _21236)). Qed.
Lemma lem1194784 {A : Type'} (t : list A) (_21236 : list A) : (t = _21236) = (t = _21236).
Proof. exact (eq_refl (t = _21236)). Qed.
Lemma lem1194785 {A B : Type'} (f : A -> B) (t : list A) (_21236 : list A) : (term275 A B f t _21236) = (term210 A B f t _21236).
Proof. exact (MK_COMB (@lem1194783 A B t f _21236) (@lem1194784 A t _21236)). Qed.
Lemma lem1194786 {A B : Type'} (f : A -> B) (t : list A) (_21236 : list A) : (term272 A B t f _21236) = (term210 A B f t _21236).
Proof. exact (TRANS (@lem1194778 A B f t _21236) (@lem1194785 A B f t _21236)). Qed.
Lemma lem1194789 {A B : Type'} (_21236 : list A) (f : A -> B) (t : list A) (h1 : term51 A B f t) : term210 A B f t _21236.
Proof. exact (EQ_MP (@lem1194786 A B f t _21236) (@lem1194775 A B _21236 f t h1)). Qed.
Lemma lem1194790 {A B : Type'} (_21236 : list A) (f : A -> B) (t : list A) (h1 : term51 A B f t) : term210 A B f t _21236.
Proof. exact (@lem1194789 A B _21236 f t h1). Qed.
Lemma lem1194791 {A B : Type'} (t' : list A) (f : A -> B) (t : list A) (h1 : term51 A B f t) : term210 A B f t t'.
Proof. exact (@lem1194790 A B t' f t h1). Qed.
Lemma lem1194794 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term51 A B f t) (h2 : term169 A B h h' t f t') : t = t'.
Proof. exact (@lem1194791 A B t' f t h1 (@lem1194738 A B h h' t f t' h2)). Qed.
Lemma lem1194795 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term51 A B f t) (h2 : term169 A B h h' t f t') : term279 A t t'.
Proof. exact (fun h0 : term241 A t t' => @lem1194794 A B h h' t f t' h1 h2). Qed.
Lemma lem1194797 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1194798 {A : Type'} (t : list A) (t' : list A) : (term279 A t t') = (t = t').
Proof. exact (@lem1194797 (t = t')). Qed.
Lemma lem1194799 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term51 A B f t) (h2 : term169 A B h h' t f t') : t = t'.
Proof. exact (EQ_MP (@lem1194798 A t t') (@lem1194795 A B h h' t f t' h1 h2)). Qed.
Lemma lem1194802 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1194804 {A : Type'} (t : list A) (t' : list A) : (term241 A t t') = (term280 A t t').
Proof. exact (@lem1194802 (t = t')). Qed.
Lemma lem1194807 {A : Type'} (t : list A) (t' : list A) (h1 : term241 A t t') : term280 A t t'.
Proof. exact (EQ_MP (@lem1194804 A t t') (@lem1194209 A t t' h1)). Qed.
Lemma lem1194810 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term51 A B f t) (h2 : term241 A t t') (h3 : term169 A B h h' t f t') : False.
Proof. exact (@lem1194807 A t t' h2 (@lem1194799 A B h h' t f t' h1 h3)). Qed.
Lemma lem1194811 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term51 A B f t) (h2 : term241 A t t') (h3 : term169 A B h h' t f t') : term269.
Proof. exact (fun h0 : ~ False => @lem1194810 A B h h' t f t' h1 h2 h3). Qed.
Lemma lem1194813 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1194814 : term269 = False.
Proof. exact (@lem1194813 False). Qed.
Lemma lem1194815 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term51 A B f t) (h2 : term241 A t t') (h3 : term169 A B h h' t f t') : False.
Proof. exact (EQ_MP (@lem1194814) (@lem1194811 A B h h' t f t' h1 h2 h3)). Qed.
Lemma lem1194872 {A B : Type'} (h' : A) (f : A -> B) (h : A) (t : list A) (t' : list A) (h1 : term169 A B h h' t f t') (h2 : (@cons A h t) = t') : (@List.map A B f t) = (term20 A B f h t).
Proof. exact (EQ_MP (@lem1194384 A B f h t t' h2) (@lem1194227 A B h h' t f t' h1)). Qed.
Lemma lem1194873 {A B : Type'} (h' : A) (f : A -> B) (h : A) (t : list A) (t' : list A) (h1 : term169 A B h h' t f t') (h2 : (@cons A h t) = t') : term281 A B f h t.
Proof. exact (fun h0 : term282 A B f h t => @lem1194872 A B h' f h t t' h1 h2). Qed.
Lemma lem1194875 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1194876 {A B : Type'} (f : A -> B) (h : A) (t : list A) : (term281 A B f h t) = ((@List.map A B f t) = (term20 A B f h t)).
Proof. exact (@lem1194875 ((@List.map A B f t) = (term20 A B f h t))). Qed.
Lemma lem1194877 {A B : Type'} (h' : A) (f : A -> B) (h : A) (t : list A) (t' : list A) (h1 : term169 A B h h' t f t') (h2 : (@cons A h t) = t') : (@List.map A B f t) = (term20 A B f h t).
Proof. exact (EQ_MP (@lem1194876 A B f h t) (@lem1194873 A B h' f h t t' h1 h2)). Qed.
Lemma lem1194883 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1194884 {A B : Type'} (t : list A) (f : A -> B) (_21239 : list A) : (term221 A B f t _21239) = (term272 A B t f _21239).
Proof. exact (@lem1194883 (t = _21239) (term271 A B t f _21239)). Qed.
Lemma lem1194894 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1194895 {A B : Type'} (t : list A) (f : A -> B) (_21239 : list A) : (term273 A B f t _21239) = (term274 A B t f _21239).
Proof. exact (MK_COMB (@lem1194894) (@lem1194884 A B t f _21239)). Qed.
Lemma lem1194905 {A B : Type'} (t : list A) (f : A -> B) (_21239 : list A) : (term272 A B t f _21239) = (term272 A B t f _21239).
Proof. exact (eq_refl (term272 A B t f _21239)). Qed.
Lemma lem1194906 {A B : Type'} (t : list A) (f : A -> B) (_21239 : list A) : ((term221 A B f t _21239) = (term272 A B t f _21239)) = ((term272 A B t f _21239) = (term272 A B t f _21239)).
Proof. exact (MK_COMB (@lem1194895 A B t f _21239) (@lem1194905 A B t f _21239)). Qed.
Lemma lem1194908 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1194909 (x : Prop) : (x = x) = True.
Proof. exact (@lem1194908 Prop x). Qed.
Lemma lem1194910 {A B : Type'} (t : list A) (f : A -> B) (_21239 : list A) : ((term272 A B t f _21239) = (term272 A B t f _21239)) = True.
Proof. exact (@lem1194909 (term272 A B t f _21239)). Qed.
Lemma lem1194911 {A B : Type'} (t : list A) (f : A -> B) (_21239 : list A) : ((term221 A B f t _21239) = (term272 A B t f _21239)) = True.
Proof. exact (TRANS (@lem1194906 A B t f _21239) (@lem1194910 A B t f _21239)). Qed.
Lemma lem1194912 {A B : Type'} (t : list A) (f : A -> B) (_21239 : list A) : True = ((term221 A B f t _21239) = (term272 A B t f _21239)).
Proof. exact (SYM (@lem1194911 A B t f _21239)). Qed.
Lemma lem1194913 {A B : Type'} (t : list A) (f : A -> B) (_21239 : list A) : (term221 A B f t _21239) = (term272 A B t f _21239).
Proof. exact (EQ_MP (@lem1194912 A B t f _21239) (@lem0)). Qed.
Lemma lem1194914 {A B : Type'} (_21239 : list A) (f : A -> B) (t : list A) (h1 : term51 A B f t) : term272 A B t f _21239.
Proof. exact (EQ_MP (@lem1194913 A B t f _21239) (@lem1194358 A B _21239 f t h1)). Qed.
Lemma lem1194916 (b : Prop) (a : Prop) : (a \/ b) = (term261 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1194917 {A B : Type'} (f : A -> B) (t : list A) (_21239 : list A) : (term272 A B t f _21239) = (term275 A B f t _21239).
Proof. exact (@lem1194916 (term271 A B t f _21239) (t = _21239)). Qed.
Lemma lem1194919 (a : Prop) : (term183 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1194920 {A B : Type'} (t : list A) (f : A -> B) (_21239 : list A) : (term276 A B t f _21239) = ((@List.map A B f t) = (@List.map A B f _21239)).
Proof. exact (@lem1194919 ((@List.map A B f t) = (@List.map A B f _21239))). Qed.
Lemma lem1194921 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1194922 {A B : Type'} (t : list A) (f : A -> B) (_21239 : list A) : (term277 A B t f _21239) = (term278 A B t f _21239).
Proof. exact (MK_COMB (@lem1194921) (@lem1194920 A B t f _21239)). Qed.
Lemma lem1194923 {A : Type'} (t : list A) (_21239 : list A) : (t = _21239) = (t = _21239).
Proof. exact (eq_refl (t = _21239)). Qed.
Lemma lem1194924 {A B : Type'} (f : A -> B) (t : list A) (_21239 : list A) : (term275 A B f t _21239) = (term210 A B f t _21239).
Proof. exact (MK_COMB (@lem1194922 A B t f _21239) (@lem1194923 A t _21239)). Qed.
Lemma lem1194925 {A B : Type'} (f : A -> B) (t : list A) (_21239 : list A) : (term272 A B t f _21239) = (term210 A B f t _21239).
Proof. exact (TRANS (@lem1194917 A B f t _21239) (@lem1194924 A B f t _21239)). Qed.
Lemma lem1194928 {A B : Type'} (_21239 : list A) (f : A -> B) (t : list A) (h1 : term51 A B f t) : term210 A B f t _21239.
Proof. exact (EQ_MP (@lem1194925 A B f t _21239) (@lem1194914 A B _21239 f t h1)). Qed.
Lemma lem1194929 {A B : Type'} (_21239 : list A) (f : A -> B) (t : list A) (h1 : term51 A B f t) : term210 A B f t _21239.
Proof. exact (@lem1194928 A B _21239 f t h1). Qed.
Lemma lem1194930 {A B : Type'} (h : A) (f : A -> B) (t : list A) (h1 : term51 A B f t) : term283 A B f h t.
Proof. exact (@lem1194929 A B (@cons A h t) f t h1). Qed.
Lemma lem1194933 {A B : Type'} (h' : A) (f : A -> B) (h : A) (t : list A) (t' : list A) (h1 : term51 A B f t) (h2 : term169 A B h h' t f t') (h3 : (@cons A h t) = t') : t = (@cons A h t).
Proof. exact (@lem1194930 A B h f t h1 (@lem1194877 A B h' f h t t' h2 h3)). Qed.
Lemma lem1194934 {A B : Type'} (h' : A) (f : A -> B) (h : A) (t : list A) (t' : list A) (h1 : term51 A B f t) (h2 : term169 A B h h' t f t') (h3 : (@cons A h t) = t') : term284 A h t.
Proof. exact (fun h0 : term253 A h t => @lem1194933 A B h' f h t t' h1 h2 h3). Qed.
Lemma lem1194936 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1194937 {A : Type'} (h : A) (t : list A) : (term284 A h t) = (t = (@cons A h t)).
Proof. exact (@lem1194936 (t = (@cons A h t))). Qed.
Lemma lem1194938 {A B : Type'} (h' : A) (f : A -> B) (h : A) (t : list A) (t' : list A) (h1 : term51 A B f t) (h2 : term169 A B h h' t f t') (h3 : (@cons A h t) = t') : t = (@cons A h t).
Proof. exact (EQ_MP (@lem1194937 A h t) (@lem1194934 A B h' f h t t' h1 h2 h3)). Qed.
Lemma lem1194941 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1194943 {A : Type'} (h : A) (t : list A) : (term253 A h t) = (term285 A h t).
Proof. exact (@lem1194941 (t = (@cons A h t))). Qed.
Lemma lem1194946 {A : Type'} (h : A) (t : list A) (t' : list A) (h1 : term241 A t t') (h2 : (@cons A h t) = t') : term285 A h t.
Proof. exact (EQ_MP (@lem1194943 A h t) (@lem1194398 A h t t' h1 h2)). Qed.
Lemma lem1194949 {A B : Type'} (h' : A) (f : A -> B) (h : A) (t : list A) (t' : list A) (h1 : term51 A B f t) (h2 : term241 A t t') (h3 : term169 A B h h' t f t') (h4 : (@cons A h t) = t') : False.
Proof. exact (@lem1194946 A h t t' h2 h4 (@lem1194938 A B h' f h t t' h1 h3 h4)). Qed.
Lemma lem1194950 {A B : Type'} (h' : A) (f : A -> B) (h : A) (t : list A) (t' : list A) (h1 : term51 A B f t) (h2 : term241 A t t') (h3 : term169 A B h h' t f t') (h4 : (@cons A h t) = t') : term269.
Proof. exact (fun h0 : ~ False => @lem1194949 A B h' f h t t' h1 h2 h3 h4). Qed.
Lemma lem1194952 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1194953 : term269 = False.
Proof. exact (@lem1194952 False). Qed.
Lemma lem1194955 {A B : Type'} (h' : A) (f : A -> B) (h : A) (t : list A) (t' : list A) (h1 : term51 A B f t) (h2 : term241 A t t') (h3 : term169 A B h h' t f t') (h4 : (@cons A h t) = t') : False.
Proof. exact (EQ_MP (@lem1194953) (@lem1194950 A B h' f h t t' h1 h2 h3 h4)). Qed.
Lemma lem1194956 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term1 A B f) (h2 : term240 A h h') (h3 : term169 A B h h' t f t') : (term240 A h h') = False.
Proof. exact (prop_ext (fun h4 : term240 A h h' => @lem1194676 A B h h' t f t' h1 h2 h3) (fun h4 : False => @lem1194315 A h h' h2)). Qed.
Lemma lem1194958 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term1 A B f) (h2 : term240 A h h') (h3 : term169 A B h h' t f t') : False.
Proof. exact (EQ_MP (@lem1194956 A B h h' t f t' h1 h2 h3) (@lem1194315 A h h' h2)). Qed.
Lemma lem1194959 {A B : Type'} (h' : A) (f : A -> B) (h : A) (t : list A) (t' : list A) (h1 : term51 A B f t) (h2 : term241 A t t') (h3 : term169 A B h h' t f t') (h4 : (@cons A h t) = t') : ((@cons A h t) = t') = False.
Proof. exact (prop_ext (fun h5 : (@cons A h t) = t' => @lem1194955 A B h' f h t t' h1 h2 h3 h4) (fun h5 : False => @lem1194231 A h t t' h4)). Qed.
Lemma lem1194960 {A B : Type'} (h' : A) (f : A -> B) (h : A) (t : list A) (t' : list A) (h1 : term51 A B f t) (h2 : term241 A t t') (h3 : term169 A B h h' t f t') (h4 : (@cons A h t) = t') : False.
Proof. exact (EQ_MP (@lem1194959 A B h' f h t t' h1 h2 h3 h4) (@lem1194231 A h t t' h4)). Qed.
Lemma lem1194961 {A B : Type'} (h' : A) (f : A -> B) (h : A) (t : list A) (t' : list A) (h1 : term51 A B f t) (h2 : term241 A t t') (h3 : term169 A B h h' t f t') (h4 : (@cons A h t) = t') : (term241 A t t') = False.
Proof. exact (prop_ext (fun h5 : term241 A t t' => @lem1194960 A B h' f h t t' h1 h2 h3 h4) (fun h5 : False => @lem1194229 A t t' h2)). Qed.
Lemma lem1194962 {A B : Type'} (h' : A) (f : A -> B) (h : A) (t : list A) (t' : list A) (h1 : term51 A B f t) (h2 : term241 A t t') (h3 : term169 A B h h' t f t') (h4 : (@cons A h t) = t') : False.
Proof. exact (EQ_MP (@lem1194961 A B h' f h t t' h1 h2 h3 h4) (@lem1194229 A t t' h2)). Qed.
Lemma lem1194963 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term51 A B f t) (h2 : term241 A t t') (h3 : term169 A B h h' t f t') : (term241 A t t') = False.
Proof. exact (prop_ext (fun h4 : term241 A t t' => @lem1194815 A B h h' t f t' h1 h2 h3) (fun h4 : False => @lem1194209 A t t' h2)). Qed.
Lemma lem1194964 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term51 A B f t) (h2 : term241 A t t') (h3 : term169 A B h h' t f t') : False.
Proof. exact (EQ_MP (@lem1194963 A B h h' t f t' h1 h2 h3) (@lem1194209 A t t' h2)). Qed.
Lemma lem1194965 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term1 A B f) (h2 : term240 A h h') (h3 : term169 A B h h' t f t') : (term240 A h h') = False.
Proof. exact (prop_ext (fun h4 : term240 A h h' => @lem1194958 A B h h' t f t' h1 h2 h3) (fun h4 : False => @lem1194189 A h h' h2)). Qed.
Lemma lem1194966 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term1 A B f) (h2 : term240 A h h') (h3 : term169 A B h h' t f t') : False.
Proof. exact (EQ_MP (@lem1194965 A B h h' t f t' h1 h2 h3) (@lem1194189 A h h' h2)). Qed.
Lemma lem1194967 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term1 A B f) (h2 : term240 A h h') (h3 : term169 A B h h' t f t') : (term240 A h h') = False.
Proof. exact (prop_ext (fun h4 : term240 A h h' => @lem1194537 A B h h' t f t' h1 h2 h3) (fun h4 : False => @lem1194169 A h h' h2)). Qed.
Lemma lem1194968 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term1 A B f) (h2 : term240 A h h') (h3 : term169 A B h h' t f t') : False.
Proof. exact (EQ_MP (@lem1194967 A B h h' t f t' h1 h2 h3) (@lem1194169 A h h' h2)). Qed.
Lemma lem1194969 {A B : Type'} (h' : A) (f : A -> B) (h : A) (t : list A) (t' : list A) (h1 : term51 A B f t) (h2 : term241 A t t') (h3 : term169 A B h h' t f t') (h4 : (@cons A h t) = t') : ((@cons A h t) = t') = False.
Proof. exact (prop_ext (fun h5 : (@cons A h t) = t' => @lem1194962 A B h' f h t t' h1 h2 h3 h4) (fun h5 : False => @lem1194115 A h t t' h4)). Qed.
Lemma lem1194970 {A B : Type'} (h' : A) (f : A -> B) (h : A) (t : list A) (t' : list A) (h1 : term51 A B f t) (h2 : term241 A t t') (h3 : term169 A B h h' t f t') (h4 : (@cons A h t) = t') : False.
Proof. exact (EQ_MP (@lem1194969 A B h' f h t t' h1 h2 h3 h4) (@lem1194115 A h t t' h4)). Qed.
Lemma lem1194971 {A B : Type'} (h' : A) (f : A -> B) (h : A) (t : list A) (t' : list A) (h1 : term51 A B f t) (h2 : term241 A t t') (h3 : term169 A B h h' t f t') (h4 : (@cons A h t) = t') : (term241 A t t') = False.
Proof. exact (prop_ext (fun h5 : term241 A t t' => @lem1194970 A B h' f h t t' h1 h2 h3 h4) (fun h5 : False => @lem1194111 A t t' h2)). Qed.
Lemma lem1194972 {A B : Type'} (h' : A) (f : A -> B) (h : A) (t : list A) (t' : list A) (h1 : term51 A B f t) (h2 : term241 A t t') (h3 : term169 A B h h' t f t') (h4 : (@cons A h t) = t') : False.
Proof. exact (EQ_MP (@lem1194971 A B h' f h t t' h1 h2 h3 h4) (@lem1194111 A t t' h2)). Qed.
Lemma lem1194973 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term51 A B f t) (h2 : term241 A t t') (h3 : term169 A B h h' t f t') : (term241 A t t') = False.
Proof. exact (prop_ext (fun h4 : term241 A t t' => @lem1194964 A B h h' t f t' h1 h2 h3) (fun h4 : False => @lem1194066 A t t' h2)). Qed.
Lemma lem1194974 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term51 A B f t) (h2 : term241 A t t') (h3 : term169 A B h h' t f t') : False.
Proof. exact (EQ_MP (@lem1194973 A B h h' t f t' h1 h2 h3) (@lem1194066 A t t' h2)). Qed.
Lemma lem1194975 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term1 A B f) (h2 : term240 A h h') (h3 : term169 A B h h' t f t') : (term240 A h h') = False.
Proof. exact (prop_ext (fun h4 : term240 A h h' => @lem1194966 A B h h' t f t' h1 h2 h3) (fun h4 : False => @lem1194021 A h h' h2)). Qed.
Lemma lem1194976 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term1 A B f) (h2 : term240 A h h') (h3 : term169 A B h h' t f t') : False.
Proof. exact (EQ_MP (@lem1194975 A B h h' t f t' h1 h2 h3) (@lem1194021 A h h' h2)). Qed.
Lemma lem1194977 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term1 A B f) (h2 : term240 A h h') (h3 : term169 A B h h' t f t') : (term240 A h h') = False.
Proof. exact (prop_ext (fun h4 : term240 A h h' => @lem1194968 A B h h' t f t' h1 h2 h3) (fun h4 : False => @lem1193976 A h h' h2)). Qed.
Lemma lem1194978 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term1 A B f) (h2 : term240 A h h') (h3 : term169 A B h h' t f t') : False.
Proof. exact (EQ_MP (@lem1194977 A B h h' t f t' h1 h2 h3) (@lem1193976 A h h' h2)). Qed.
Lemma lem1194979 {A B : Type'} (h' : A) (f : A -> B) (h : A) (t : list A) (t' : list A) (h1 : term51 A B f t) (h2 : term241 A t t') (h3 : term169 A B h h' t f t') (h4 : (@cons A h t) = t') : ((@cons A h t) = t') = False.
Proof. exact (prop_ext (fun h5 : (@cons A h t) = t' => @lem1194972 A B h' f h t t' h1 h2 h3 h4) (fun h5 : False => @lem1194115 A h t t' h4)). Qed.
Lemma lem1194980 {A B : Type'} (h' : A) (f : A -> B) (h : A) (t : list A) (t' : list A) (h1 : term51 A B f t) (h2 : term241 A t t') (h3 : term169 A B h h' t f t') (h4 : (@cons A h t) = t') : False.
Proof. exact (EQ_MP (@lem1194979 A B h' f h t t' h1 h2 h3 h4) (@lem1194115 A h t t' h4)). Qed.
Lemma lem1194981 {A B : Type'} (h' : A) (f : A -> B) (h : A) (t : list A) (t' : list A) (h1 : term51 A B f t) (h2 : term241 A t t') (h3 : term169 A B h h' t f t') (h4 : (@cons A h t) = t') : (term241 A t t') = False.
Proof. exact (prop_ext (fun h5 : term241 A t t' => @lem1194980 A B h' f h t t' h1 h2 h3 h4) (fun h5 : False => @lem1194111 A t t' h2)). Qed.
Lemma lem1194982 {A B : Type'} (h' : A) (f : A -> B) (h : A) (t : list A) (t' : list A) (h1 : term51 A B f t) (h2 : term241 A t t') (h3 : term169 A B h h' t f t') (h4 : (@cons A h t) = t') : False.
Proof. exact (EQ_MP (@lem1194981 A B h' f h t t' h1 h2 h3 h4) (@lem1194111 A t t' h2)). Qed.
Lemma lem1194983 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term51 A B f t) (h2 : term241 A t t') (h3 : term169 A B h h' t f t') : (term241 A t t') = False.
Proof. exact (prop_ext (fun h4 : term241 A t t' => @lem1194974 A B h h' t f t' h1 h2 h3) (fun h4 : False => @lem1194066 A t t' h2)). Qed.
Lemma lem1194984 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term51 A B f t) (h2 : term241 A t t') (h3 : term169 A B h h' t f t') : False.
Proof. exact (EQ_MP (@lem1194983 A B h h' t f t' h1 h2 h3) (@lem1194066 A t t' h2)). Qed.
Lemma lem1194985 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term1 A B f) (h2 : term240 A h h') (h3 : term169 A B h h' t f t') : (term240 A h h') = False.
Proof. exact (prop_ext (fun h4 : term240 A h h' => @lem1194976 A B h h' t f t' h1 h2 h3) (fun h4 : False => @lem1194021 A h h' h2)). Qed.
Lemma lem1194986 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term1 A B f) (h2 : term240 A h h') (h3 : term169 A B h h' t f t') : False.
Proof. exact (EQ_MP (@lem1194985 A B h h' t f t' h1 h2 h3) (@lem1194021 A h h' h2)). Qed.
Lemma lem1194987 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term1 A B f) (h2 : term240 A h h') (h3 : term169 A B h h' t f t') : (term240 A h h') = False.
Proof. exact (prop_ext (fun h4 : term240 A h h' => @lem1194978 A B h h' t f t' h1 h2 h3) (fun h4 : False => @lem1193976 A h h' h2)). Qed.
Lemma lem1194988 {A B : Type'} (h : A) (h' : A) (t : list A) (f : A -> B) (t' : list A) (h1 : term1 A B f) (h2 : term240 A h h') (h3 : term169 A B h h' t f t') : False.
Proof. exact (EQ_MP (@lem1194987 A B h h' t f t' h1 h2 h3) (@lem1193976 A h h' h2)). Qed.
Lemma lem1194989 {A B : Type'} (h' : A) (f : A -> B) (h : A) (t : list A) (t' : list A) (h1 : term51 A B f t) (h2 : term241 A t t') (h3 : term169 A B h h' t f t') (h4 : term109 A B f h t t') : False.
Proof. exact (or_elim (@lem1193873 A B f h t t' h4) (fun h0 : term286 A B h t f t' => @lem1194984 A B h h' t f t' h1 h2 h3) (fun h0 : (@cons A h t) = t' => @lem1194982 A B h' f h t t' h1 h2 h3 h0)). Qed.
Lemma lem1194990 {A B : Type'} (h' : A) (f : A -> B) (h : A) (t : list A) (t' : list A) (h1 : term1 A B f) (h2 : term240 A h h') (h3 : term169 A B h h' t f t') (h4 : term109 A B f h t t') : False.
Proof. exact (or_elim (@lem1193873 A B f h t t' h4) (fun h0 : term286 A B h t f t' => @lem1194988 A B h h' t f t' h1 h2 h3) (fun h0 : (@cons A h t) = t' => @lem1194986 A B h h' t f t' h1 h2 h3)). Qed.
Lemma lem1194991 {A B : Type'} (h' : A) (f : A -> B) (h : A) (t : list A) (t' : list A) (h1 : term1 A B f) (h2 : term51 A B f t) (h3 : term215 A h h' t t') (h4 : term169 A B h h' t f t') (h5 : term109 A B f h t t') : False.
Proof. exact (or_elim (@lem1193927 A h h' t t' h3) (fun h0 : term240 A h h' => @lem1194990 A B h' f h t t' h1 h0 h4 h5) (fun h0 : term241 A t t' => @lem1194989 A B h' f h t t' h2 h0 h4 h5)). Qed.
Lemma lem1194992 {A B : Type'} (h' : A) (f : A -> B) (h : A) (t : list A) (t' : list A) (h1 : term1 A B f) (h2 : term51 A B f t) (h3 : term215 A h h' t t') (h4 : term169 A B h h' t f t') (h5 : term109 A B f h t t') : (term169 A B h h' t f t') = False.
Proof. exact (prop_ext (fun h6 : term169 A B h h' t f t' => @lem1194991 A B h' f h t t' h1 h2 h3 h4 h5) (fun h6 : False => @lem1193767 A B h h' t f t' h4)). Qed.
Lemma lem1194993 {A B : Type'} (h' : A) (f : A -> B) (h : A) (t : list A) (t' : list A) (h1 : term1 A B f) (h2 : term51 A B f t) (h3 : term215 A h h' t t') (h4 : term169 A B h h' t f t') (h5 : term109 A B f h t t') : False.
Proof. exact (EQ_MP (@lem1194992 A B h' f h t t' h1 h2 h3 h4 h5) (@lem1193767 A B h h' t f t' h4)). Qed.
Lemma lem1194994 {A B : Type'} (h' : A) (f : A -> B) (h : A) (t : list A) (t' : list A) (h1 : term1 A B f) (h2 : term51 A B f t) (h3 : term215 A h h' t t') (h4 : term169 A B h h' t f t') (h5 : term109 A B f h t t') : (term215 A h h' t t') = False.
Proof. exact (prop_ext (fun h6 : term215 A h h' t t' => @lem1194993 A B h' f h t t' h1 h2 h3 h4 h5) (fun h6 : False => @lem1193612 A h h' t t' h3)). Qed.
Lemma lem1194995 {A B : Type'} (h' : A) (f : A -> B) (h : A) (t : list A) (t' : list A) (h1 : term1 A B f) (h2 : term51 A B f t) (h3 : term215 A h h' t t') (h4 : term169 A B h h' t f t') (h5 : term109 A B f h t t') : False.
Proof. exact (EQ_MP (@lem1194994 A B h' f h t t' h1 h2 h3 h4 h5) (@lem1193612 A h h' t t' h3)). Qed.
Lemma lem1194996 {A B : Type'} (h' : A) (f : A -> B) (h : A) (t : list A) (t' : list A) (h1 : term1 A B f) (h2 : term51 A B f t) (h3 : term169 A B h h' t f t') (h4 : term109 A B f h t t') : term214 A h h' t t'.
Proof. exact (fun h0 : term215 A h h' t t' => @lem1194995 A B h' f h t t' h1 h2 h0 h3 h4). Qed.
Lemma lem1194997 {A B : Type'} (h' : A) (f : A -> B) (h : A) (t : list A) (t' : list A) (h1 : term1 A B f) (h2 : term51 A B f t) (h3 : term169 A B h h' t f t') (h4 : term109 A B f h t t') : term13 A h h' t t'.
Proof. exact (EQ_MP (@lem1193611 A h h' t t') (@lem1194996 A B h' f h t t' h1 h2 h3 h4)). Qed.
Lemma lem1194998 {A B : Type'} (h' : A) (f : A -> B) (h : A) (t : list A) (t' : list A) (h1 : term1 A B f) (h2 : term51 A B f t) (h3 : term109 A B f h t t') : term174 A B f h h' t t'.
Proof. exact (fun h0 : term169 A B h h' t f t' => @lem1194997 A B h' f h t t' h1 h2 h0 h3). Qed.
Lemma lem1194999 {A B : Type'} (h : A) (h' : A) (t' : list A) (f : A -> B) (t : list A) (h1 : term1 A B f) (h2 : term51 A B f t) : term185 A B f h h' t t'.
Proof. exact (fun h0 : term109 A B f h t t' => @lem1194998 A B h' f h t t' h1 h2 h0). Qed.
Lemma lem1195000 {A B : Type'} (h : A) (h' : A) (t : list A) (t' : list A) (f : A -> B) (h1 : term1 A B f) : term187 A B f h h' t t'.
Proof. exact (fun h0 : term51 A B f t => @lem1194999 A B h h' t' f t h1 h0). Qed.
Lemma lem1195001 {A B : Type'} (f : A -> B) (h : A) (h' : A) (t : list A) (t' : list A) : term189 A B f h h' t t'.
Proof. exact (fun h0 : term1 A B f => @lem1195000 A B h h' t t' f h0). Qed.
Lemma lem1195006 {A B : Type'} (h : A) (h' : A) (t : list A) (t' : list A) : term193 A B h h' t t'.
Proof. exact (fun f : A -> B => @lem1195001 A B f h h' t t'). Qed.
Lemma lem1195011 {A B : Type'} (h' : A) (t : list A) (t' : list A) : term197 A B h' t t'.
Proof. exact (fun h : A => @lem1195006 A B h h' t t'). Qed.
Lemma lem1195016 {A B : Type'} (t : list A) (t' : list A) : term201 A B t t'.
Proof. exact (fun h' : A => @lem1195011 A B h' t t'). Qed.
Lemma lem1195021 {A B : Type'} (t' : list A) : term205 A B t'.
Proof. exact (fun t : list A => @lem1195016 A B t t'). Qed.
Lemma lem1195026 {A B : Type'} : term209 A B.
Proof. exact (fun t' : list A => @lem1195021 A B t'). Qed.
Lemma lem1195027 {A B : Type'} : term208 A B.
Proof. exact (EQ_MP (@lem1193603 A B) (@lem1195026 A B)). Qed.
Lemma lem1195028 {A B : Type'} (t' : list A) : term287 A B t'.
Proof. exact (@lem1195027 A B t'). Qed.
Lemma lem1195029 {A B : Type'} (t' : list A) : (term287 A B t') = (term204 A B t').
Proof. exact (eq_refl (term287 A B t')). Qed.
Lemma lem1195030 {A B : Type'} (t' : list A) : term204 A B t'.
Proof. exact (EQ_MP (@lem1195029 A B t') (@lem1195028 A B t')). Qed.
Lemma lem1195031 {A B : Type'} (t' : list A) (t : list A) : term288 A B t' t.
Proof. exact (@lem1195030 A B t' t). Qed.
Lemma lem1195032 {A B : Type'} (t : list A) (t' : list A) : (term288 A B t' t) = (term200 A B t t').
Proof. exact (eq_refl (term288 A B t' t)). Qed.
Lemma lem1195033 {A B : Type'} (t : list A) (t' : list A) : term200 A B t t'.
Proof. exact (EQ_MP (@lem1195032 A B t t') (@lem1195031 A B t' t)). Qed.
Lemma lem1195034 {A B : Type'} (t : list A) (t' : list A) (h' : A) : term289 A B t t' h'.
Proof. exact (@lem1195033 A B t t' h'). Qed.
Lemma lem1195035 {A B : Type'} (h' : A) (t : list A) (t' : list A) : (term289 A B t t' h') = (term196 A B h' t t').
Proof. exact (eq_refl (term289 A B t t' h')). Qed.
Lemma lem1195036 {A B : Type'} (h' : A) (t : list A) (t' : list A) : term196 A B h' t t'.
Proof. exact (EQ_MP (@lem1195035 A B h' t t') (@lem1195034 A B t t' h')). Qed.
Lemma lem1195037 {A B : Type'} (h' : A) (t : list A) (t' : list A) (h : A) : term290 A B h' t t' h.
Proof. exact (@lem1195036 A B h' t t' h). Qed.
Lemma lem1195038 {A B : Type'} (h : A) (h' : A) (t : list A) (t' : list A) : (term290 A B h' t t' h) = (term192 A B h h' t t').
Proof. exact (eq_refl (term290 A B h' t t' h)). Qed.
Lemma lem1195039 {A B : Type'} (h : A) (h' : A) (t : list A) (t' : list A) : term192 A B h h' t t'.
Proof. exact (EQ_MP (@lem1195038 A B h h' t t') (@lem1195037 A B h' t t' h)). Qed.
Lemma lem1195040 {A B : Type'} (h : A) (h' : A) (t : list A) (t' : list A) (f : A -> B) : term291 A B h h' t t' f.
Proof. exact (@lem1195039 A B h h' t t' f). Qed.
Lemma lem1195041 {A B : Type'} (f : A -> B) (h : A) (h' : A) (t : list A) (t' : list A) : (term291 A B h h' t t' f) = (term178 A B f h h' t t').
Proof. exact (eq_refl (term291 A B h h' t t' f)). Qed.
Lemma lem1195042 {A B : Type'} (f : A -> B) (h : A) (h' : A) (t : list A) (t' : list A) : term178 A B f h h' t t'.
Proof. exact (EQ_MP (@lem1195041 A B f h h' t t') (@lem1195040 A B h h' t t' f)). Qed.
Lemma lem1195044 {A B : Type'} (f : A -> B) (h : A) (h' : A) (t : list A) (t' : list A) : term178 A B f h h' t t'.
Proof. exact (@lem1193364 A B f h h' t t' (@lem1195042 A B f h h' t t')). Qed.
Lemma lem1195045 {A B : Type'} (h : A) (h' : A) (t : list A) (t' : list A) (f : A -> B) (h1 : term1 A B f) : term186 A B f h h' t t'.
Proof. exact (@lem1195044 A B f h h' t t' (@lem1190074 A B f h1)). Qed.
Lemma lem1195046 {A B : Type'} (h : A) (h' : A) (t' : list A) (f : A -> B) (t : list A) (h1 : term1 A B f) (h2 : term51 A B f t) : term184 A B f h h' t t'.
Proof. exact (@lem1195045 A B h h' t t' f h1 (@lem1190248 A B f t h2)). Qed.
Lemma lem1195047 {A B : Type'} (h' : A) (f : A -> B) (h : A) (t : list A) (t' : list A) (h1 : term1 A B f) (h2 : term51 A B f t) (h3 : term109 A B f h t t') : term176 A B f h h' t t'.
Proof. exact (@lem1195046 A B h h' t' f t h1 h2 (@lem1190308 A B f h t t' h3)). Qed.
Lemma lem1195048 {A B : Type'} (h' : A) (f : A -> B) (h : A) (t : list A) (t' : list A) (h1 : term1 A B f) (h2 : term51 A B f t) (h3 : term177 A B f h h' t t') (h4 : term109 A B f h t t') : False.
Proof. exact (@lem1195047 A B h' f h t t' h1 h2 h4 (@lem1193348 A B f h h' t t' h3)). Qed.
Lemma lem1195049 {A B : Type'} (h' : A) (f : A -> B) (h : A) (t : list A) (t' : list A) (h1 : term1 A B f) (h2 : term51 A B f t) (h3 : term177 A B f h h' t t') (h4 : term109 A B f h t t') : (term177 A B f h h' t t') = False.
Proof. exact (prop_ext (fun h5 : term177 A B f h h' t t' => @lem1195048 A B h' f h t t' h1 h2 h3 h4) (fun h5 : False => @lem1193348 A B f h h' t t' h3)). Qed.
Lemma lem1195050 {A B : Type'} (h' : A) (f : A -> B) (h : A) (t : list A) (t' : list A) (h1 : term1 A B f) (h2 : term51 A B f t) (h3 : term177 A B f h h' t t') (h4 : term109 A B f h t t') : False.
Proof. exact (EQ_MP (@lem1195049 A B h' f h t t' h1 h2 h3 h4) (@lem1193348 A B f h h' t t' h3)). Qed.
Lemma lem1195051 {A B : Type'} (h' : A) (f : A -> B) (h : A) (t : list A) (t' : list A) (h1 : term1 A B f) (h2 : term51 A B f t) (h3 : term109 A B f h t t') : term176 A B f h h' t t'.
Proof. exact (fun h0 : term177 A B f h h' t t' => @lem1195050 A B h' f h t t' h1 h2 h0 h3). Qed.
Lemma lem1195052 {A B : Type'} (h' : A) (f : A -> B) (h : A) (t : list A) (t' : list A) (h1 : term1 A B f) (h2 : term51 A B f t) (h3 : term109 A B f h t t') : term174 A B f h h' t t'.
Proof. exact (EQ_MP (@lem1193347 A B f h h' t t') (@lem1195051 A B h' f h t t' h1 h2 h3)). Qed.
Lemma lem1195053 {A B : Type'} (h' : A) (f : A -> B) (h : A) (t : list A) (t' : list A) (h1 : term1 A B f) (h2 : term51 A B f t) (h3 : term109 A B f h t t') : term113 A B f h t h' t'.
Proof. exact (EQ_MP (@lem1193343 A B f h t h' t') (@lem1195052 A B h' f h t t' h1 h2 h3)). Qed.
Lemma lem1195054 {A B : Type'} (h : A) (h' : A) (t' : list A) (f : A -> B) (t : list A) (h1 : term1 A B f) (h2 : term51 A B f t) : term115 A B f h t h' t'.
Proof. exact (fun h0 : term109 A B f h t t' => @lem1195053 A B h' f h t t' h1 h2 h0). Qed.
Lemma lem1195059 {A B : Type'} (h : A) (h' : A) (f : A -> B) (t : list A) (h1 : term1 A B f) (h2 : term51 A B f t) : term119 A B f h t h'.
Proof. exact (fun t' : list A => @lem1195054 A B h h' t' f t h1 h2). Qed.
Lemma lem1195064 {A B : Type'} (h : A) (f : A -> B) (t : list A) (h1 : term1 A B f) (h2 : term51 A B f t) : term123 A B f h t.
Proof. exact (fun h' : A => @lem1195059 A B h h' f t h1 h2). Qed.
Lemma lem1195065 {A B : Type'} (h : A) (f : A -> B) (t : list A) (h1 : term1 A B f) (h2 : term51 A B f t) : term125 A B f h t.
Proof. exact (conj (@lem1191194 A B f h t) (@lem1195064 A B h f t h1 h2)). Qed.
Lemma lem1195066 {A B : Type'} (h : A) (f : A -> B) (t : list A) (h1 : term1 A B f) (h2 : term51 A B f t) : term55 A B f h t.
Proof. exact (@lem1190307 A B f h t (@lem1195065 A B h f t h1 h2)). Qed.
Lemma lem1195067 {A B : Type'} (f : A -> B) (h : A) (t : list A) : term86 A B f h t.
Proof. exact (fun h0 : term80 A B f t => @lem1190595 A B f h t). Qed.
Lemma lem1195072 {A B : Type'} (f : A -> B) (h : A) : term90 A B f h.
Proof. exact (fun t : list A => @lem1195067 A B f h t). Qed.
Lemma lem1195077 {A B : Type'} (f : A -> B) : term94 A B f.
Proof. exact (fun h : A => @lem1195072 A B f h). Qed.
Lemma lem1195078 {A B : Type'} (f : A -> B) : term96 A B f.
Proof. exact (conj (@lem1190385 A B f) (@lem1195077 A B f)). Qed.
Lemma lem1195079 {A B : Type'} (f : A -> B) : term47 A B f.
Proof. exact (@lem1190275 A B f (@lem1195078 A B f)). Qed.
Lemma lem1195080 {A B : Type'} (h : A) (t : list A) (f : A -> B) (h1 : term1 A B f) : term57 A B f h t.
Proof. exact (fun h0 : term51 A B f t => @lem1195066 A B h f t h1 h0). Qed.
Lemma lem1195085 {A B : Type'} (h : A) (f : A -> B) (h1 : term1 A B f) : term61 A B f h.
Proof. exact (fun t : list A => @lem1195080 A B h t f h1). Qed.
Lemma lem1195090 {A B : Type'} (f : A -> B) (h1 : term1 A B f) : term65 A B f.
Proof. exact (fun h : A => @lem1195085 A B h f h1). Qed.
Lemma lem1195091 {A B : Type'} (f : A -> B) (h1 : term1 A B f) : term67 A B f.
Proof. exact (conj (@lem1195079 A B f) (@lem1195090 A B f h1)). Qed.
Lemma lem1195092 {A B : Type'} (f : A -> B) (h1 : term1 A B f) : term0 A B f.
Proof. exact (@lem1190247 A B f (@lem1195091 A B f h1)). Qed.
Lemma lem1195093 {A B : Type'} (f : A -> B) : term292 A B f.
Proof. exact (fun h0 : term1 A B f => @lem1195092 A B f h0). Qed.
Lemma lem1195094 {A B : Type'} (f : A -> B) : term293 A B f.
Proof. exact (fun h0 : term0 A B f => @lem1190220 A B f h0). Qed.
Lemma lem1195095 {A B : Type'} (f : A -> B) : term294 A B f.
Proof. exact (conj (@lem1195094 A B f) (@lem1195093 A B f)). Qed.
Lemma lem1195096 {A B : Type'} (f : A -> B) : (term294 A B f) = ((term0 A B f) = (term1 A B f)).
Proof. exact (@lem32 (term0 A B f) (term1 A B f)). Qed.
Lemma lem1195097 {A B : Type'} (f : A -> B) : (term0 A B f) = (term1 A B f).
Proof. exact (EQ_MP (@lem1195096 A B f) (@lem1195095 A B f)). Qed.
Lemma lem1195102 {A B : Type'} : term295 A B.
Proof. exact (fun f : A -> B => @lem1195097 A B f). Qed.
