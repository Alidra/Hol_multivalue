Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm8050197_term_abbrevs.
Require Import EXTENSION_spec.
Require Import PASTECART_IN_PCROSS_spec.
Require Import thm7660850_spec.
Require Import thm7662539_spec.
Lemma lem8050024 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : term0 _141927 _141928 _141929 s.
Proof. exact (@lem8004229 _141927 _141928 _141929 s). Qed.
Lemma lem8050025 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : (term0 _141927 _141928 _141929 s) = (term1 _141927 _141928 _141929 s).
Proof. exact (eq_refl (term0 _141927 _141928 _141929 s)). Qed.
Lemma lem8050026 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : term1 _141927 _141928 _141929 s.
Proof. exact (EQ_MP (@lem8050025 _141927 _141928 _141929 s) (@lem8050024 _141927 _141928 _141929 s)). Qed.
Lemma lem8050027 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term2 _141927 _141928 _141929 s t.
Proof. exact (@lem8050026 _141927 _141928 _141929 s t). Qed.
Lemma lem8050028 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (term2 _141927 _141928 _141929 s t) = (term3 _141927 _141928 _141929 s t).
Proof. exact (eq_refl (term2 _141927 _141928 _141929 s t)). Qed.
Lemma lem8050029 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term3 _141927 _141928 _141929 s t.
Proof. exact (EQ_MP (@lem8050028 _141927 _141928 _141929 s t) (@lem8050027 _141927 _141928 _141929 s t)). Qed.
Lemma lem8050030 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) (x : cart _141927 _141928) : term4 _141927 _141928 _141929 s t x.
Proof. exact (@lem8050029 _141927 _141928 _141929 s t x). Qed.
Lemma lem8050031 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (term4 _141927 _141928 _141929 s t x) = (term5 _141927 _141928 _141929 x s t).
Proof. exact (eq_refl (term4 _141927 _141928 _141929 s t x)). Qed.
Lemma lem8050032 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term5 _141927 _141928 _141929 x s t.
Proof. exact (EQ_MP (@lem8050031 _141927 _141928 _141929 x s t) (@lem8050030 _141927 _141928 _141929 s t x)). Qed.
Lemma lem8050033 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) (y : cart _141927 _141929) : term6 _141927 _141928 _141929 x s t y.
Proof. exact (@lem8050032 _141927 _141928 _141929 x s t y). Qed.
Lemma lem8050034 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term6 _141927 _141928 _141929 x s t y) = ((term7 _141927 _141928 _141929 x y s t) = (term8 _141927 _141928 _141929 x s y t)).
Proof. exact (eq_refl (term6 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8050074 {A : Type'} (s : A -> Prop) : term9 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem8050075 {A : Type'} (s : A -> Prop) : (term9 A s) = (term10 A s).
Proof. exact (eq_refl (term9 A s)). Qed.
Lemma lem8050076 {A : Type'} (s : A -> Prop) : term10 A s.
Proof. exact (EQ_MP (@lem8050075 A s) (@lem8050074 A s)). Qed.
Lemma lem8050077 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term11 A s t.
Proof. exact (@lem8050076 A s t). Qed.
Lemma lem8050078 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term11 A s t) = ((s = t) = (term12 A s t)).
Proof. exact (eq_refl (term11 A s t)). Qed.
Lemma lem8050105 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term12 A s t).
Proof. exact (EQ_MP (@lem8050078 A s t) (@lem8050077 A s t)). Qed.
Lemma lem8050106 {_143007 _143008 _143009 : Type'} (s : type16 _143007 _143008 _143009) (t : type16 _143007 _143008 _143009) : (s = t) = (term13 _143007 _143008 _143009 s t).
Proof. exact (@lem8050105 (type2 _143007 _143008 _143009) s t). Qed.
Lemma lem8050107 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : ((term14 _143007 _143008 _143009 s f) = (@PCROSS _143007 _143008 _143009 s (@UNIV (cart _143007 _143009)))) = (term15 _143007 _143008 _143009 f s).
Proof. exact (@lem8050106 _143007 _143008 _143009 (term14 _143007 _143008 _143009 s f) (@PCROSS _143007 _143008 _143009 s (@UNIV (cart _143007 _143009)))). Qed.
Lemma lem8050113 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term16 _140454 _140455 _140456 P) = (term17 _140454 _140455 _140456 P).
Proof. exact (EQ_MP (@lem7660850 _140454 _140455 _140456 P) (@lem7662539 _140454 _140455 _140456 P)). Qed.
Lemma lem8050114 {_143007 _143008 _143009 : Type'} (P : type16 _143007 _143008 _143009) : (term16 _143007 _143008 _143009 P) = (term17 _143007 _143008 _143009 P).
Proof. exact (@lem8050113 _143007 _143008 _143009 P). Qed.
Lemma lem8050115 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term18 _143007 _143008 _143009 f s) = (term19 _143007 _143008 _143009 f s).
Proof. exact (@lem8050114 _143007 _143008 _143009 (term20 _143007 _143008 _143009 f s)). Qed.
Lemma lem8050116 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (x : type2 _143007 _143008 _143009) (s : type24 _143007 _143008) : (term21 _143007 _143008 _143009 f s x) = ((term22 _143007 _143008 _143009 x s f) = (term23 _143007 _143008 _143009 x s)).
Proof. exact (eq_refl (term21 _143007 _143008 _143009 f s x)). Qed.
Lemma lem8050117 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term24 _143007 _143008 _143009 f s) = (term20 _143007 _143008 _143009 f s).
Proof. exact (fun_ext (fun x : type2 _143007 _143008 _143009 => @lem8050116 _143007 _143008 _143009 f x s)). Qed.
Lemma lem8050118 {_143007 _143008 _143009 : Type'} : (@all (cart _143007 (finite_sum _143008 _143009))) = (@all (cart _143007 (finite_sum _143008 _143009))).
Proof. exact (eq_refl (@all (cart _143007 (finite_sum _143008 _143009)))). Qed.
Lemma lem8050119 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term18 _143007 _143008 _143009 f s) = (term15 _143007 _143008 _143009 f s).
Proof. exact (MK_COMB (@lem8050118 _143007 _143008 _143009) (@lem8050117 _143007 _143008 _143009 f s)). Qed.
Lemma lem8050120 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8050121 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term25 _143007 _143008 _143009 f s) = (term26 _143007 _143008 _143009 f s).
Proof. exact (MK_COMB (@lem8050120) (@lem8050119 _143007 _143008 _143009 f s)). Qed.
Lemma lem8050122 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (x : cart _143007 _143008) (y : cart _143007 _143009) (s : type24 _143007 _143008) : (term27 _143007 _143008 _143009 f s x y) = ((term28 _143007 _143008 _143009 x y s f) = (term29 _143007 _143008 _143009 x y s)).
Proof. exact (eq_refl (term27 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8050123 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (x : cart _143007 _143008) (s : type24 _143007 _143008) : (term30 _143007 _143008 _143009 f s x) = (term31 _143007 _143008 _143009 f x s).
Proof. exact (fun_ext (fun y : cart _143007 _143009 => @lem8050122 _143007 _143008 _143009 f x y s)). Qed.
Lemma lem8050124 {_143007 _143009 : Type'} : (@all (cart _143007 _143009)) = (@all (cart _143007 _143009)).
Proof. exact (eq_refl (@all (cart _143007 _143009))). Qed.
Lemma lem8050125 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (x : cart _143007 _143008) (s : type24 _143007 _143008) : (term32 _143007 _143008 _143009 f s x) = (term33 _143007 _143008 _143009 f x s).
Proof. exact (MK_COMB (@lem8050124 _143007 _143009) (@lem8050123 _143007 _143008 _143009 f x s)). Qed.
Lemma lem8050126 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term34 _143007 _143008 _143009 f s) = (term35 _143007 _143008 _143009 f s).
Proof. exact (fun_ext (fun x : cart _143007 _143008 => @lem8050125 _143007 _143008 _143009 f x s)). Qed.
Lemma lem8050127 {_143007 _143008 : Type'} : (@all (cart _143007 _143008)) = (@all (cart _143007 _143008)).
Proof. exact (eq_refl (@all (cart _143007 _143008))). Qed.
Lemma lem8050128 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term19 _143007 _143008 _143009 f s) = (term36 _143007 _143008 _143009 f s).
Proof. exact (MK_COMB (@lem8050127 _143007 _143008) (@lem8050126 _143007 _143008 _143009 f s)). Qed.
Lemma lem8050129 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : ((term18 _143007 _143008 _143009 f s) = (term19 _143007 _143008 _143009 f s)) = ((term15 _143007 _143008 _143009 f s) = (term36 _143007 _143008 _143009 f s)).
Proof. exact (MK_COMB (@lem8050121 _143007 _143008 _143009 f s) (@lem8050128 _143007 _143008 _143009 f s)). Qed.
Lemma lem8050130 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term15 _143007 _143008 _143009 f s) = (term36 _143007 _143008 _143009 f s).
Proof. exact (EQ_MP (@lem8050129 _143007 _143008 _143009 f s) (@lem8050115 _143007 _143008 _143009 f s)). Qed.
Lemma lem8050137 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : ((term14 _143007 _143008 _143009 s f) = (@PCROSS _143007 _143008 _143009 s (@UNIV (cart _143007 _143009)))) = (term36 _143007 _143008 _143009 f s).
Proof. exact (TRANS (@lem8050107 _143007 _143008 _143009 f s) (@lem8050130 _143007 _143008 _143009 f s)). Qed.
Lemma lem8050149 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term7 _141927 _141928 _141929 x y s t) = (term8 _141927 _141928 _141929 x s y t).
Proof. exact (EQ_MP (@lem8050034 _141927 _141928 _141929 x s y t) (@lem8050033 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8050150 {_143007 _143008 _143009 : Type'} (x : cart _143007 _143008) (s : type24 _143007 _143008) (y : cart _143007 _143009) (t : type24 _143007 _143009) : (term7 _143007 _143008 _143009 x y s t) = (term8 _143007 _143008 _143009 x s y t).
Proof. exact (@lem8050149 _143007 _143008 _143009 x s y t). Qed.
Lemma lem8050151 {_143007 _143008 _143009 : Type'} (x : cart _143007 _143008) (s : type24 _143007 _143008) (y : cart _143007 _143009) (f : type56 _143007 _143009) : (term28 _143007 _143008 _143009 x y s f) = (term37 _143007 _143008 _143009 x s y f).
Proof. exact (@lem8050150 _143007 _143008 _143009 x s y (@INTERS (cart _143007 _143009) f)). Qed.
Lemma lem8050155 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (h1 : f = (@EMPTY ((cart _143007 _143009) -> Prop))) : f = (@EMPTY ((cart _143007 _143009) -> Prop)).
Proof. exact (h1). Qed.
Lemma lem8050156 {_143007 _143009 : Type'} : (@INTERS (cart _143007 _143009)) = (@INTERS (cart _143007 _143009)).
Proof. exact (eq_refl (@INTERS (cart _143007 _143009))). Qed.
Lemma lem8050157 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (h1 : f = (@EMPTY ((cart _143007 _143009) -> Prop))) : (@INTERS (cart _143007 _143009) f) = (@INTERS (cart _143007 _143009) (@EMPTY ((cart _143007 _143009) -> Prop))).
Proof. exact (MK_COMB (@lem8050156 _143007 _143009) (@lem8050155 _143007 _143009 f h1)). Qed.
Lemma lem8050158 {_143007 _143009 : Type'} (y : cart _143007 _143009) : (@IN (cart _143007 _143009) y) = (@IN (cart _143007 _143009) y).
Proof. exact (eq_refl (@IN (cart _143007 _143009) y)). Qed.
Lemma lem8050159 {_143007 _143009 : Type'} (y : cart _143007 _143009) (f : type56 _143007 _143009) (h1 : f = (@EMPTY ((cart _143007 _143009) -> Prop))) : (term38 _143007 _143009 y f) = (term39 _143007 _143009 y).
Proof. exact (MK_COMB (@lem8050158 _143007 _143009 y) (@lem8050157 _143007 _143009 f h1)). Qed.
Lemma lem8050160 {_143007 _143008 : Type'} (x : cart _143007 _143008) (s : type24 _143007 _143008) : (term40 _143007 _143008 x s) = (term40 _143007 _143008 x s).
Proof. exact (eq_refl (term40 _143007 _143008 x s)). Qed.
Lemma lem8050161 {_143007 _143008 _143009 : Type'} (x : cart _143007 _143008) (s : type24 _143007 _143008) (y : cart _143007 _143009) (f : type56 _143007 _143009) (h1 : f = (@EMPTY ((cart _143007 _143009) -> Prop))) : (term37 _143007 _143008 _143009 x s y f) = (term41 _143007 _143008 _143009 x s y).
Proof. exact (MK_COMB (@lem8050160 _143007 _143008 x s) (@lem8050159 _143007 _143009 y f h1)). Qed.
Lemma lem8050164 {_143007 _143008 _143009 : Type'} (x : cart _143007 _143008) (s : type24 _143007 _143008) (y : cart _143007 _143009) (f : type56 _143007 _143009) (h1 : f = (@EMPTY ((cart _143007 _143009) -> Prop))) : (term28 _143007 _143008 _143009 x y s f) = (term41 _143007 _143008 _143009 x s y).
Proof. exact (TRANS (@lem8050151 _143007 _143008 _143009 x s y f) (@lem8050161 _143007 _143008 _143009 x s y f h1)). Qed.
Lemma lem8050165 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8050166 {_143007 _143008 _143009 : Type'} (x : cart _143007 _143008) (s : type24 _143007 _143008) (y : cart _143007 _143009) (f : type56 _143007 _143009) (h1 : f = (@EMPTY ((cart _143007 _143009) -> Prop))) : (term42 _143007 _143008 _143009 x y s f) = (term43 _143007 _143008 _143009 x s y).
Proof. exact (MK_COMB (@lem8050165) (@lem8050164 _143007 _143008 _143009 x s y f h1)). Qed.
Lemma lem8050168 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term7 _141927 _141928 _141929 x y s t) = (term8 _141927 _141928 _141929 x s y t).
Proof. exact (EQ_MP (@lem8050034 _141927 _141928 _141929 x s y t) (@lem8050033 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8050169 {_143007 _143008 _143009 : Type'} (x : cart _143007 _143008) (s : type24 _143007 _143008) (y : cart _143007 _143009) (t : type24 _143007 _143009) : (term7 _143007 _143008 _143009 x y s t) = (term8 _143007 _143008 _143009 x s y t).
Proof. exact (@lem8050168 _143007 _143008 _143009 x s y t). Qed.
Lemma lem8050170 {_143007 _143008 _143009 : Type'} (x : cart _143007 _143008) (s : type24 _143007 _143008) (y : cart _143007 _143009) : (term29 _143007 _143008 _143009 x y s) = (term44 _143007 _143008 _143009 x s y).
Proof. exact (@lem8050169 _143007 _143008 _143009 x s y (@UNIV (cart _143007 _143009))). Qed.
Lemma lem8050173 {_143007 _143008 _143009 : Type'} (x : cart _143007 _143008) (s : type24 _143007 _143008) (y : cart _143007 _143009) (f : type56 _143007 _143009) (h1 : f = (@EMPTY ((cart _143007 _143009) -> Prop))) : ((term28 _143007 _143008 _143009 x y s f) = (term29 _143007 _143008 _143009 x y s)) = ((term41 _143007 _143008 _143009 x s y) = (term44 _143007 _143008 _143009 x s y)).
Proof. exact (MK_COMB (@lem8050166 _143007 _143008 _143009 x s y f h1) (@lem8050170 _143007 _143008 _143009 x s y)). Qed.
Lemma lem8050178 {_143007 _143008 _143009 : Type'} (x : cart _143007 _143008) (s : type24 _143007 _143008) (f : type56 _143007 _143009) (h1 : f = (@EMPTY ((cart _143007 _143009) -> Prop))) : (term31 _143007 _143008 _143009 f x s) = (term45 _143007 _143008 _143009 x s).
Proof. exact (fun_ext (fun y : cart _143007 _143009 => @lem8050173 _143007 _143008 _143009 x s y f h1)). Qed.
Lemma lem8050179 {_143007 _143009 : Type'} : (@all (cart _143007 _143009)) = (@all (cart _143007 _143009)).
Proof. exact (eq_refl (@all (cart _143007 _143009))). Qed.
Lemma lem8050180 {_143007 _143008 _143009 : Type'} (x : cart _143007 _143008) (s : type24 _143007 _143008) (f : type56 _143007 _143009) (h1 : f = (@EMPTY ((cart _143007 _143009) -> Prop))) : (term33 _143007 _143008 _143009 f x s) = (term46 _143007 _143008 _143009 x s).
Proof. exact (MK_COMB (@lem8050179 _143007 _143009) (@lem8050178 _143007 _143008 _143009 x s f h1)). Qed.
Lemma lem8050187 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (f : type56 _143007 _143009) (h1 : f = (@EMPTY ((cart _143007 _143009) -> Prop))) : (term35 _143007 _143008 _143009 f s) = (term47 _143007 _143008 _143009 s).
Proof. exact (fun_ext (fun x : cart _143007 _143008 => @lem8050180 _143007 _143008 _143009 x s f h1)). Qed.
Lemma lem8050188 {_143007 _143008 : Type'} : (@all (cart _143007 _143008)) = (@all (cart _143007 _143008)).
Proof. exact (eq_refl (@all (cart _143007 _143008))). Qed.
Lemma lem8050189 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (f : type56 _143007 _143009) (h1 : f = (@EMPTY ((cart _143007 _143009) -> Prop))) : (term36 _143007 _143008 _143009 f s) = (term48 _143007 _143008 _143009 s).
Proof. exact (MK_COMB (@lem8050188 _143007 _143008) (@lem8050187 _143007 _143008 _143009 s f h1)). Qed.
Lemma lem8050196 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (f : type56 _143007 _143009) (h1 : f = (@EMPTY ((cart _143007 _143009) -> Prop))) : ((term14 _143007 _143008 _143009 s f) = (@PCROSS _143007 _143008 _143009 s (@UNIV (cart _143007 _143009)))) = (term48 _143007 _143008 _143009 s).
Proof. exact (TRANS (@lem8050137 _143007 _143008 _143009 f s) (@lem8050189 _143007 _143008 _143009 s f h1)). Qed.
Lemma lem8050197 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (f : type56 _143007 _143009) (h1 : f = (@EMPTY ((cart _143007 _143009) -> Prop))) : (term48 _143007 _143008 _143009 s) = ((term14 _143007 _143008 _143009 s f) = (@PCROSS _143007 _143008 _143009 s (@UNIV (cart _143007 _143009)))).
Proof. exact (SYM (@lem8050196 _143007 _143008 _143009 s f h1)). Qed.
