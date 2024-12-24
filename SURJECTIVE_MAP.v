Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SURJECTIVE_MAP_term_abbrevs.
Require Import CONS_11_spec.
Require Import DISJ_ACI_spec.
Require Import LEFT_IMP_EXISTS_THM_spec.
Require Import MAP_spec.
Require Import MAP_EQ_NIL_spec.
Require Import NOT_CONS_NIL_spec.
Require Import list_INDUCT_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1097797_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1822_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
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
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm32_spec.
Require Import thm69_spec.
Require Import thm82_spec.
Lemma lem1195113 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem1195114 {A : Type'} (P : type1143 A) (h1 : term0 A) : term1 A P.
Proof. exact (@lem1195113 A h1 P). Qed.
Lemma lem1195115 {A : Type'} (P : type1143 A) : (term1 A P) = (term2 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem1195116 {A : Type'} (P : type1143 A) (h1 : term0 A) : term2 A P.
Proof. exact (EQ_MP (@lem1195115 A P) (@lem1195114 A P h1)). Qed.
Lemma lem1195117 {A : Type'} (P : type1143 A) (h1 : term3 A P) : term3 A P.
Proof. exact (h1). Qed.
Lemma lem1195118 {A : Type'} (P : type1143 A) (h1 : term0 A) (h2 : term3 A P) : term4 A P.
Proof. exact (@lem1195116 A P h1 (@lem1195117 A P h2)). Qed.
Lemma lem1195119 {A : Type'} (P : type1143 A) (h1 : term3 A P) : term5 A P.
Proof. exact (fun h0 : term0 A => @lem1195118 A P h0 h1). Qed.
Lemma lem1195120 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem1195121 {A : Type'} (P : type1143 A) (h1 : term0 A) (h2 : term3 A P) : term4 A P.
Proof. exact (@lem1195119 A P h2 (@lem1195120 A h1)). Qed.
Lemma lem1195122 {A : Type'} (P : type1143 A) (h1 : term0 A) : term2 A P.
Proof. exact (fun h0 : term3 A P => @lem1195121 A P h1 h0). Qed.
Lemma lem1195123 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (fun P : type1143 A => @lem1195122 A P h1). Qed.
Lemma lem1195124 {A : Type'} : term6 A.
Proof. exact (fun h0 : term0 A => @lem1195123 A h0). Qed.
Lemma lem1195125 {A : Type'} : term0 A.
Proof. exact (@lem1195124 A (@lem1071853 A)). Qed.
Lemma lem1195126 {A : Type'} (P : type1143 A) : term1 A P.
Proof. exact (@lem1195125 A P). Qed.
Lemma lem1195127 {A : Type'} (P : type1143 A) : (term1 A P) = (term2 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem1195129 {_27823 _27827 : Type'} (f : _27827 -> _27823) : term7 _27823 _27827 f.
Proof. exact (@lem1190062 _27823 _27827 f). Qed.
Lemma lem1195130 {_27823 _27827 : Type'} (f : _27827 -> _27823) : (term7 _27823 _27827 f) = (term8 _27823 _27827 f).
Proof. exact (eq_refl (term7 _27823 _27827 f)). Qed.
Lemma lem1195131 {_27823 _27827 : Type'} (f : _27827 -> _27823) : term8 _27823 _27827 f.
Proof. exact (EQ_MP (@lem1195130 _27823 _27827 f) (@lem1195129 _27823 _27827 f)). Qed.
Lemma lem1195132 {_27823 _27827 : Type'} (f : _27827 -> _27823) (l : list _27827) : term9 _27823 _27827 f l.
Proof. exact (@lem1195131 _27823 _27827 f l). Qed.
Lemma lem1195133 {_27823 _27827 : Type'} (f : _27827 -> _27823) (l : list _27827) : (term9 _27823 _27827 f l) = (((@List.map _27827 _27823 f l) = (@nil _27823)) = (l = (@nil _27827))).
Proof. exact (eq_refl (term9 _27823 _27827 f l)). Qed.
Lemma lem1195135 {A : Type'} (h : A) : term10 A h.
Proof. exact (@lem1111523 A h). Qed.
Lemma lem1195136 {A : Type'} (h : A) : (term10 A h) = (term11 A h).
Proof. exact (eq_refl (term10 A h)). Qed.
Lemma lem1195137 {A : Type'} (h : A) : term11 A h.
Proof. exact (EQ_MP (@lem1195136 A h) (@lem1195135 A h)). Qed.
Lemma lem1195138 {A : Type'} (h : A) (t : list A) : term12 A h t.
Proof. exact (@lem1195137 A h t). Qed.
Lemma lem1195139 {A : Type'} (h : A) (t : list A) : (term12 A h t) = (term13 A h t).
Proof. exact (eq_refl (term12 A h t)). Qed.
Lemma lem1195140 {A : Type'} (h : A) (t : list A) : term13 A h t.
Proof. exact (EQ_MP (@lem1195139 A h t) (@lem1195138 A h t)). Qed.
Lemma lem1195144 {A : Type'} (h : A) (t : list A) (h1 : (@cons A h t) = (@nil A)) : (@cons A h t) = (@nil A).
Proof. exact (h1). Qed.
Lemma lem1195145 {A : Type'} (h : A) (t : list A) (h1 : (@cons A h t) = (@nil A)) : (@nil A) = (@cons A h t).
Proof. exact (SYM (@lem1195144 A h t h1)). Qed.
Lemma lem1195146 {A : Type'} (h : A) (t : list A) (h1 : (@nil A) = (@cons A h t)) : (@nil A) = (@cons A h t).
Proof. exact (h1). Qed.
Lemma lem1195147 {A : Type'} (h : A) (t : list A) (h1 : (@nil A) = (@cons A h t)) : (@cons A h t) = (@nil A).
Proof. exact (SYM (@lem1195146 A h t h1)). Qed.
Lemma lem1195148 {A : Type'} (h : A) (t : list A) : ((@cons A h t) = (@nil A)) = ((@nil A) = (@cons A h t)).
Proof. exact (prop_ext (fun h1 : (@cons A h t) = (@nil A) => @lem1195145 A h t h1) (fun h1 : (@nil A) = (@cons A h t) => @lem1195147 A h t h1)). Qed.
Lemma lem1195149 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1195150 {A : Type'} (h : A) (t : list A) : (term13 A h t) = (term14 A h t).
Proof. exact (MK_COMB (@lem1195149) (@lem1195148 A h t)). Qed.
Lemma lem1195151 {A : Type'} (h : A) (t : list A) : term14 A h t.
Proof. exact (EQ_MP (@lem1195150 A h t) (@lem1195140 A h t)). Qed.
Lemma lem1195152 {A : Type'} (h : A) (t : list A) : term15 A h t.
Proof. exact (@lem82 ((@nil A) = (@cons A h t))). Qed.
Lemma lem1195154 {A : Type'} (h1' : A) : term16 A h1'.
Proof. exact (@lem1113436 A h1'). Qed.
Lemma lem1195155 {A : Type'} (h1' : A) : (term16 A h1') = (term17 A h1').
Proof. exact (eq_refl (term16 A h1')). Qed.
Lemma lem1195156 {A : Type'} (h1' : A) : term17 A h1'.
Proof. exact (EQ_MP (@lem1195155 A h1') (@lem1195154 A h1')). Qed.
Lemma lem1195157 {A : Type'} (h1' : A) (h2' : A) : term18 A h1' h2'.
Proof. exact (@lem1195156 A h1' h2'). Qed.
Lemma lem1195158 {A : Type'} (h1' : A) (h2' : A) : (term18 A h1' h2') = (term19 A h1' h2').
Proof. exact (eq_refl (term18 A h1' h2')). Qed.
Lemma lem1195159 {A : Type'} (h1' : A) (h2' : A) : term19 A h1' h2'.
Proof. exact (EQ_MP (@lem1195158 A h1' h2') (@lem1195157 A h1' h2')). Qed.
Lemma lem1195160 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) : term20 A h1' h2' t1.
Proof. exact (@lem1195159 A h1' h2' t1). Qed.
Lemma lem1195161 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) : (term20 A h1' h2' t1) = (term21 A h1' h2' t1).
Proof. exact (eq_refl (term20 A h1' h2' t1)). Qed.
Lemma lem1195162 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) : term21 A h1' h2' t1.
Proof. exact (EQ_MP (@lem1195161 A h1' h2' t1) (@lem1195160 A h1' h2' t1)). Qed.
Lemma lem1195163 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) (t2 : list A) : term22 A h1' h2' t1 t2.
Proof. exact (@lem1195162 A h1' h2' t1 t2). Qed.
Lemma lem1195164 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) (t2 : list A) : (term22 A h1' h2' t1 t2) = (((@cons A h1' t1) = (@cons A h2' t2)) = (term23 A h1' h2' t1 t2)).
Proof. exact (eq_refl (term22 A h1' h2' t1 t2)). Qed.
Lemma lem1195166 {A B : Type'} : term24 A B.
Proof. exact (proj2 (@lem1097797 A B)). Qed.
Lemma lem1195167 {A B : Type'} (f : A -> B) : term25 A B f.
Proof. exact (@lem1195166 A B f). Qed.
Lemma lem1195168 {A B : Type'} (f : A -> B) : (term25 A B f) = (term26 A B f).
Proof. exact (eq_refl (term25 A B f)). Qed.
Lemma lem1195169 {A B : Type'} (f : A -> B) : term26 A B f.
Proof. exact (EQ_MP (@lem1195168 A B f) (@lem1195167 A B f)). Qed.
Lemma lem1195170 {A B : Type'} (f : A -> B) (h : A) : term27 A B f h.
Proof. exact (@lem1195169 A B f h). Qed.
Lemma lem1195171 {A B : Type'} (h : A) (f : A -> B) : (term27 A B f h) = (term28 A B h f).
Proof. exact (eq_refl (term27 A B f h)). Qed.
Lemma lem1195172 {A B : Type'} (h : A) (f : A -> B) : term28 A B h f.
Proof. exact (EQ_MP (@lem1195171 A B h f) (@lem1195170 A B f h)). Qed.
Lemma lem1195173 {A B : Type'} (h : A) (f : A -> B) (t : list A) : term29 A B h f t.
Proof. exact (@lem1195172 A B h f t). Qed.
Lemma lem1195174 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term29 A B h f t) = ((term30 A B f h t) = (term31 A B h f t)).
Proof. exact (eq_refl (term29 A B h f t)). Qed.
Lemma lem1195176 {A B : Type'} : term32 A B.
Proof. exact (proj1 (@lem1097797 A B)). Qed.
Lemma lem1195177 {A B : Type'} (f : A -> B) : term33 A B f.
Proof. exact (@lem1195176 A B f). Qed.
Lemma lem1195178 {A B : Type'} (f : A -> B) : (term33 A B f) = ((@List.map A B f (@nil A)) = (@nil B)).
Proof. exact (eq_refl (term33 A B f)). Qed.
Lemma lem1195180 {A : Type'} (P : A -> Prop) : term34 A P.
Proof. exact (@lem6644 A P). Qed.
Lemma lem1195181 {A : Type'} (P : A -> Prop) : (term34 A P) = (term35 A P).
Proof. exact (eq_refl (term34 A P)). Qed.
Lemma lem1195182 {A : Type'} (P : A -> Prop) : term35 A P.
Proof. exact (EQ_MP (@lem1195181 A P) (@lem1195180 A P)). Qed.
Lemma lem1195183 {A : Type'} (P : A -> Prop) (Q : Prop) : term36 A P Q.
Proof. exact (@lem1195182 A P Q). Qed.
Lemma lem1195184 {A : Type'} (P : A -> Prop) (Q : Prop) : (term36 A P Q) = ((term37 A P Q) = (term38 A P Q)).
Proof. exact (eq_refl (term36 A P Q)). Qed.
Lemma lem1195186 {A B : Type'} (f : A -> B) (h1 : term39 A B f) : term39 A B f.
Proof. exact (h1). Qed.
Lemma lem1195187 {A B : Type'} (f : A -> B) (h1 : term40 A B f) : term40 A B f.
Proof. exact (h1). Qed.
Lemma lem1195188 {A B : Type'} (y : B) (f : A -> B) (h1 : term39 A B f) : term41 A B f y.
Proof. exact (@lem1195186 A B f h1 (@cons B y (@nil B))). Qed.
Lemma lem1195189 {A B : Type'} (f : A -> B) (y : B) : (term41 A B f y) = (term42 A B f y).
Proof. exact (eq_refl (term41 A B f y)). Qed.
Lemma lem1195190 {A B : Type'} (y : B) (f : A -> B) (h1 : term39 A B f) : term42 A B f y.
Proof. exact (EQ_MP (@lem1195189 A B f y) (@lem1195188 A B y f h1)). Qed.
Lemma lem1195192 {A : Type'} (P : A -> Prop) (Q : Prop) : (term37 A P Q) = (term38 A P Q).
Proof. exact (EQ_MP (@lem1195184 A P Q) (@lem1195183 A P Q)). Qed.
Lemma lem1195193 {A : Type'} (P : type1143 A) (Q : Prop) : (term43 A P Q) = (term44 A P Q).
Proof. exact (@lem1195192 (list A) P Q). Qed.
Lemma lem1195194 {A B : Type'} (f : A -> B) (y : B) : (term45 A B f y) = (term46 A B f y).
Proof. exact (@lem1195193 A (term47 A B f y) (term48 A B f y)). Qed.
Lemma lem1195195 {A B : Type'} (f : A -> B) (l : list A) (y : B) : (term49 A B f y l) = ((@List.map A B f l) = (@cons B y (@nil B))).
Proof. exact (eq_refl (term49 A B f y l)). Qed.
Lemma lem1195196 {A B : Type'} (f : A -> B) (y : B) : (term50 A B f y) = (term47 A B f y).
Proof. exact (fun_ext (fun l : list A => @lem1195195 A B f l y)). Qed.
Lemma lem1195197 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1195198 {A B : Type'} (f : A -> B) (y : B) : (term51 A B f y) = (term42 A B f y).
Proof. exact (MK_COMB (@lem1195197 A) (@lem1195196 A B f y)). Qed.
Lemma lem1195199 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1195200 {A B : Type'} (f : A -> B) (y : B) : (term52 A B f y) = (term53 A B f y).
Proof. exact (MK_COMB (@lem1195199) (@lem1195198 A B f y)). Qed.
Lemma lem1195201 {A B : Type'} (f : A -> B) (y : B) : (term48 A B f y) = (term48 A B f y).
Proof. exact (eq_refl (term48 A B f y)). Qed.
Lemma lem1195202 {A B : Type'} (f : A -> B) (y : B) : (term45 A B f y) = (term54 A B f y).
Proof. exact (MK_COMB (@lem1195200 A B f y) (@lem1195201 A B f y)). Qed.
Lemma lem1195203 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1195204 {A B : Type'} (f : A -> B) (y : B) : (term55 A B f y) = (term56 A B f y).
Proof. exact (MK_COMB (@lem1195203) (@lem1195202 A B f y)). Qed.
Lemma lem1195205 {A B : Type'} (f : A -> B) (l : list A) (y : B) : (term49 A B f y l) = ((@List.map A B f l) = (@cons B y (@nil B))).
Proof. exact (eq_refl (term49 A B f y l)). Qed.
Lemma lem1195206 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1195207 {A B : Type'} (f : A -> B) (l : list A) (y : B) : (term57 A B f y l) = (term58 A B f l y).
Proof. exact (MK_COMB (@lem1195206) (@lem1195205 A B f l y)). Qed.
Lemma lem1195208 {A B : Type'} (f : A -> B) (y : B) : (term48 A B f y) = (term48 A B f y).
Proof. exact (eq_refl (term48 A B f y)). Qed.
Lemma lem1195209 {A B : Type'} (l : list A) (f : A -> B) (y : B) : (term59 A B l f y) = (term60 A B l f y).
Proof. exact (MK_COMB (@lem1195207 A B f l y) (@lem1195208 A B f y)). Qed.
Lemma lem1195210 {A B : Type'} (f : A -> B) (y : B) : (term61 A B f y) = (term62 A B f y).
Proof. exact (fun_ext (fun l : list A => @lem1195209 A B l f y)). Qed.
Lemma lem1195211 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1195212 {A B : Type'} (f : A -> B) (y : B) : (term46 A B f y) = (term63 A B f y).
Proof. exact (MK_COMB (@lem1195211 A) (@lem1195210 A B f y)). Qed.
Lemma lem1195213 {A B : Type'} (f : A -> B) (y : B) : ((term45 A B f y) = (term46 A B f y)) = ((term54 A B f y) = (term63 A B f y)).
Proof. exact (MK_COMB (@lem1195204 A B f y) (@lem1195212 A B f y)). Qed.
Lemma lem1195214 {A B : Type'} (f : A -> B) (y : B) : (term54 A B f y) = (term63 A B f y).
Proof. exact (EQ_MP (@lem1195213 A B f y) (@lem1195194 A B f y)). Qed.
Lemma lem1195231 {A B : Type'} (f : A -> B) (y : B) : (term63 A B f y) = (term54 A B f y).
Proof. exact (SYM (@lem1195214 A B f y)). Qed.
Lemma lem1195233 {A : Type'} (P : type1143 A) : term2 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1195234 {A : Type'} (P : type1143 A) : term2 A P.
Proof. exact (@lem1195233 A P). Qed.
Lemma lem1195235 {A B : Type'} (f : A -> B) (y : B) : term64 A B f y.
Proof. exact (@lem1195234 A (term62 A B f y)). Qed.
Lemma lem1195236 {A B : Type'} (f : A -> B) (y : B) : (term65 A B f y) = (term66 A B f y).
Proof. exact (eq_refl (term65 A B f y)). Qed.
Lemma lem1195237 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1195238 {A B : Type'} (f : A -> B) (y : B) : (term67 A B f y) = (term68 A B f y).
Proof. exact (MK_COMB (@lem1195237) (@lem1195236 A B f y)). Qed.
Lemma lem1195239 {A B : Type'} (t : list A) (f : A -> B) (y : B) : (term69 A B f y t) = (term60 A B t f y).
Proof. exact (eq_refl (term69 A B f y t)). Qed.
Lemma lem1195240 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1195241 {A B : Type'} (t : list A) (f : A -> B) (y : B) : (term70 A B f y t) = (term71 A B t f y).
Proof. exact (MK_COMB (@lem1195240) (@lem1195239 A B t f y)). Qed.
Lemma lem1195242 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) : (term72 A B f y h t) = (term73 A B h t f y).
Proof. exact (eq_refl (term72 A B f y h t)). Qed.
Lemma lem1195243 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) : (term74 A B f y h t) = (term75 A B h t f y).
Proof. exact (MK_COMB (@lem1195241 A B t f y) (@lem1195242 A B h t f y)). Qed.
Lemma lem1195244 {A B : Type'} (h : A) (f : A -> B) (y : B) : (term76 A B f y h) = (term77 A B h f y).
Proof. exact (fun_ext (fun t : list A => @lem1195243 A B h t f y)). Qed.
Lemma lem1195245 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1195246 {A B : Type'} (h : A) (f : A -> B) (y : B) : (term78 A B f y h) = (term79 A B h f y).
Proof. exact (MK_COMB (@lem1195245 A) (@lem1195244 A B h f y)). Qed.
Lemma lem1195247 {A B : Type'} (f : A -> B) (y : B) : (term80 A B f y) = (term81 A B f y).
Proof. exact (fun_ext (fun h : A => @lem1195246 A B h f y)). Qed.
Lemma lem1195248 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1195249 {A B : Type'} (f : A -> B) (y : B) : (term82 A B f y) = (term83 A B f y).
Proof. exact (MK_COMB (@lem1195248 A) (@lem1195247 A B f y)). Qed.
Lemma lem1195250 {A B : Type'} (f : A -> B) (y : B) : (term84 A B f y) = (term85 A B f y).
Proof. exact (MK_COMB (@lem1195238 A B f y) (@lem1195249 A B f y)). Qed.
Lemma lem1195251 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1195252 {A B : Type'} (f : A -> B) (y : B) : (term86 A B f y) = (term87 A B f y).
Proof. exact (MK_COMB (@lem1195251) (@lem1195250 A B f y)). Qed.
Lemma lem1195253 {A B : Type'} (l : list A) (f : A -> B) (y : B) : (term69 A B f y l) = (term60 A B l f y).
Proof. exact (eq_refl (term69 A B f y l)). Qed.
Lemma lem1195254 {A B : Type'} (f : A -> B) (y : B) : (term88 A B f y) = (term62 A B f y).
Proof. exact (fun_ext (fun l : list A => @lem1195253 A B l f y)). Qed.
Lemma lem1195255 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1195256 {A B : Type'} (f : A -> B) (y : B) : (term89 A B f y) = (term63 A B f y).
Proof. exact (MK_COMB (@lem1195255 A) (@lem1195254 A B f y)). Qed.
Lemma lem1195257 {A B : Type'} (f : A -> B) (y : B) : (term64 A B f y) = (term90 A B f y).
Proof. exact (MK_COMB (@lem1195252 A B f y) (@lem1195256 A B f y)). Qed.
Lemma lem1195258 {A B : Type'} (f : A -> B) (y : B) : term90 A B f y.
Proof. exact (EQ_MP (@lem1195257 A B f y) (@lem1195235 A B f y)). Qed.
Lemma lem1195259 {A B : Type'} (t : list A) (f : A -> B) (y : B) (h1 : term60 A B t f y) : term60 A B t f y.
Proof. exact (h1). Qed.
Lemma lem1195267 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (@nil B).
Proof. exact (EQ_MP (@lem1195178 A B f) (@lem1195177 A B f)). Qed.
Lemma lem1195268 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (@nil B).
Proof. exact (@lem1195267 A B f). Qed.
Lemma lem1195269 {B : Type'} : (@eq (list B)) = (@eq (list B)).
Proof. exact (eq_refl (@eq (list B))). Qed.
Lemma lem1195270 {A B : Type'} (f : A -> B) : (term91 A B f) = (@eq (list B) (@nil B)).
Proof. exact (MK_COMB (@lem1195269 B) (@lem1195268 A B f)). Qed.
Lemma lem1195271 {B : Type'} (y : B) : (@cons B y (@nil B)) = (@cons B y (@nil B)).
Proof. exact (eq_refl (@cons B y (@nil B))). Qed.
Lemma lem1195272 {A B : Type'} (f : A -> B) (y : B) : ((@List.map A B f (@nil A)) = (@cons B y (@nil B))) = ((@nil B) = (@cons B y (@nil B))).
Proof. exact (MK_COMB (@lem1195270 A B f) (@lem1195271 B y)). Qed.
Lemma lem1195274 {A : Type'} (h : A) (t : list A) : ((@nil A) = (@cons A h t)) = False.
Proof. exact (@lem1195152 A h t (@lem1195151 A h t)). Qed.
Lemma lem1195275 {B : Type'} (h : B) (t : list B) : ((@nil B) = (@cons B h t)) = False.
Proof. exact (@lem1195274 B h t). Qed.
Lemma lem1195276 {B : Type'} (y : B) : ((@nil B) = (@cons B y (@nil B))) = False.
Proof. exact (@lem1195275 B y (@nil B)). Qed.
Lemma lem1195277 {A B : Type'} (f : A -> B) (y : B) : ((@List.map A B f (@nil A)) = (@cons B y (@nil B))) = False.
Proof. exact (TRANS (@lem1195272 A B f y) (@lem1195276 B y)). Qed.
Lemma lem1195278 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1195279 {A B : Type'} (f : A -> B) (y : B) : (term92 A B f y) = (imp False).
Proof. exact (MK_COMB (@lem1195278) (@lem1195277 A B f y)). Qed.
Lemma lem1195286 {A B : Type'} (f : A -> B) (y : B) : (term48 A B f y) = (term48 A B f y).
Proof. exact (eq_refl (term48 A B f y)). Qed.
Lemma lem1195287 {A B : Type'} (f : A -> B) (y : B) : (term66 A B f y) = (term93 A B f y).
Proof. exact (MK_COMB (@lem1195279 A B f y) (@lem1195286 A B f y)). Qed.
Lemma lem1195289 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1195290 {A B : Type'} (f : A -> B) (y : B) : (term93 A B f y) = True.
Proof. exact (@lem1195289 (term48 A B f y)). Qed.
Lemma lem1195291 {A B : Type'} (f : A -> B) (y : B) : (term66 A B f y) = True.
Proof. exact (TRANS (@lem1195287 A B f y) (@lem1195290 A B f y)). Qed.
Lemma lem1195292 {A B : Type'} (f : A -> B) (y : B) : True = (term66 A B f y).
Proof. exact (SYM (@lem1195291 A B f y)). Qed.
Lemma lem1195293 {A B : Type'} (f : A -> B) (y : B) : term66 A B f y.
Proof. exact (EQ_MP (@lem1195292 A B f y) (@lem0)). Qed.
Lemma lem1195301 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term30 A B f h t) = (term31 A B h f t).
Proof. exact (EQ_MP (@lem1195174 A B h f t) (@lem1195173 A B h f t)). Qed.
Lemma lem1195302 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term30 A B f h t) = (term31 A B h f t).
Proof. exact (@lem1195301 A B h f t). Qed.
Lemma lem1195303 {B : Type'} : (@eq (list B)) = (@eq (list B)).
Proof. exact (eq_refl (@eq (list B))). Qed.
Lemma lem1195304 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term94 A B f h t) = (term95 A B h f t).
Proof. exact (MK_COMB (@lem1195303 B) (@lem1195302 A B h f t)). Qed.
Lemma lem1195305 {B : Type'} (y : B) : (@cons B y (@nil B)) = (@cons B y (@nil B)).
Proof. exact (eq_refl (@cons B y (@nil B))). Qed.
Lemma lem1195306 {A B : Type'} (h : A) (f : A -> B) (t : list A) (y : B) : ((term30 A B f h t) = (@cons B y (@nil B))) = ((term31 A B h f t) = (@cons B y (@nil B))).
Proof. exact (MK_COMB (@lem1195304 A B h f t) (@lem1195305 B y)). Qed.
Lemma lem1195308 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) (t2 : list A) : ((@cons A h1' t1) = (@cons A h2' t2)) = (term23 A h1' h2' t1 t2).
Proof. exact (EQ_MP (@lem1195164 A h1' h2' t1 t2) (@lem1195163 A h1' h2' t1 t2)). Qed.
Lemma lem1195309 {B : Type'} (h1' : B) (h2' : B) (t1 : list B) (t2 : list B) : ((@cons B h1' t1) = (@cons B h2' t2)) = (term23 B h1' h2' t1 t2).
Proof. exact (@lem1195308 B h1' h2' t1 t2). Qed.
Lemma lem1195310 {A B : Type'} (h : A) (y : B) (f : A -> B) (t : list A) : ((term31 A B h f t) = (@cons B y (@nil B))) = (term96 A B h y f t).
Proof. exact (@lem1195309 B (f h) y (@List.map A B f t) (@nil B)). Qed.
Lemma lem1195316 {_27823 _27827 : Type'} (f : _27827 -> _27823) (l : list _27827) : ((@List.map _27827 _27823 f l) = (@nil _27823)) = (l = (@nil _27827)).
Proof. exact (EQ_MP (@lem1195133 _27823 _27827 f l) (@lem1195132 _27823 _27827 f l)). Qed.
Lemma lem1195317 {A B : Type'} (f : A -> B) (l : list A) : ((@List.map A B f l) = (@nil B)) = (l = (@nil A)).
Proof. exact (@lem1195316 B A f l). Qed.
Lemma lem1195318 {A B : Type'} (f : A -> B) (t : list A) : ((@List.map A B f t) = (@nil B)) = (t = (@nil A)).
Proof. exact (@lem1195317 A B f t). Qed.
Lemma lem1195321 {A B : Type'} (f : A -> B) (h : A) (y : B) : (term97 A B f h y) = (term97 A B f h y).
Proof. exact (eq_refl (term97 A B f h y)). Qed.
Lemma lem1195322 {A B : Type'} (f : A -> B) (h : A) (y : B) (t : list A) : (term96 A B h y f t) = (term98 A B f h y t).
Proof. exact (MK_COMB (@lem1195321 A B f h y) (@lem1195318 A B f t)). Qed.
Lemma lem1195325 {A B : Type'} (f : A -> B) (h : A) (y : B) (t : list A) : ((term31 A B h f t) = (@cons B y (@nil B))) = (term98 A B f h y t).
Proof. exact (TRANS (@lem1195310 A B h y f t) (@lem1195322 A B f h y t)). Qed.
Lemma lem1195326 {A B : Type'} (f : A -> B) (h : A) (y : B) (t : list A) : ((term30 A B f h t) = (@cons B y (@nil B))) = (term98 A B f h y t).
Proof. exact (TRANS (@lem1195306 A B h f t y) (@lem1195325 A B f h y t)). Qed.
Lemma lem1195327 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1195328 {A B : Type'} (f : A -> B) (h : A) (y : B) (t : list A) : (term99 A B f h t y) = (term100 A B f h y t).
Proof. exact (MK_COMB (@lem1195327) (@lem1195326 A B f h y t)). Qed.
Lemma lem1195335 {A B : Type'} (f : A -> B) (y : B) : (term48 A B f y) = (term48 A B f y).
Proof. exact (eq_refl (term48 A B f y)). Qed.
Lemma lem1195336 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) : (term73 A B h t f y) = (term101 A B h t f y).
Proof. exact (MK_COMB (@lem1195328 A B f h y t) (@lem1195335 A B f y)). Qed.
Lemma lem1195339 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) : (term101 A B h t f y) = (term73 A B h t f y).
Proof. exact (SYM (@lem1195336 A B h t f y)). Qed.
Lemma lem1195341 {A : Type'} (P : type1143 A) : term2 A P.
Proof. exact (EQ_MP (@lem1195127 A P) (@lem1195126 A P)). Qed.
Lemma lem1195342 {B : Type'} (P : type1143 B) : term2 B P.
Proof. exact (@lem1195341 B P). Qed.
Lemma lem1195343 {A B : Type'} (f : A -> B) : term102 A B f.
Proof. exact (@lem1195342 B (term103 A B f)). Qed.
Lemma lem1195344 {A B : Type'} (f : A -> B) : (term104 A B f) = (term105 A B f).
Proof. exact (eq_refl (term104 A B f)). Qed.
Lemma lem1195345 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1195346 {A B : Type'} (f : A -> B) : (term106 A B f) = (term107 A B f).
Proof. exact (MK_COMB (@lem1195345) (@lem1195344 A B f)). Qed.
Lemma lem1195347 {A B : Type'} (f : A -> B) (a1 : list B) : (term108 A B f a1) = (term109 A B f a1).
Proof. exact (eq_refl (term108 A B f a1)). Qed.
Lemma lem1195348 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1195349 {A B : Type'} (f : A -> B) (a1 : list B) : (term110 A B f a1) = (term111 A B f a1).
Proof. exact (MK_COMB (@lem1195348) (@lem1195347 A B f a1)). Qed.
Lemma lem1195350 {A B : Type'} (f : A -> B) (a0 : B) (a1 : list B) : (term112 A B f a0 a1) = (term113 A B f a0 a1).
Proof. exact (eq_refl (term112 A B f a0 a1)). Qed.
Lemma lem1195351 {A B : Type'} (f : A -> B) (a0 : B) (a1 : list B) : (term114 A B f a0 a1) = (term115 A B f a0 a1).
Proof. exact (MK_COMB (@lem1195349 A B f a1) (@lem1195350 A B f a0 a1)). Qed.
Lemma lem1195352 {A B : Type'} (f : A -> B) (a0 : B) : (term116 A B f a0) = (term117 A B f a0).
Proof. exact (fun_ext (fun a1 : list B => @lem1195351 A B f a0 a1)). Qed.
Lemma lem1195353 {B : Type'} : (@all (list B)) = (@all (list B)).
Proof. exact (eq_refl (@all (list B))). Qed.
Lemma lem1195354 {A B : Type'} (f : A -> B) (a0 : B) : (term118 A B f a0) = (term119 A B f a0).
Proof. exact (MK_COMB (@lem1195353 B) (@lem1195352 A B f a0)). Qed.
Lemma lem1195355 {A B : Type'} (f : A -> B) : (term120 A B f) = (term121 A B f).
Proof. exact (fun_ext (fun a0 : B => @lem1195354 A B f a0)). Qed.
Lemma lem1195356 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1195357 {A B : Type'} (f : A -> B) : (term122 A B f) = (term123 A B f).
Proof. exact (MK_COMB (@lem1195356 B) (@lem1195355 A B f)). Qed.
Lemma lem1195358 {A B : Type'} (f : A -> B) : (term124 A B f) = (term125 A B f).
Proof. exact (MK_COMB (@lem1195346 A B f) (@lem1195357 A B f)). Qed.
Lemma lem1195359 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1195360 {A B : Type'} (f : A -> B) : (term126 A B f) = (term127 A B f).
Proof. exact (MK_COMB (@lem1195359) (@lem1195358 A B f)). Qed.
Lemma lem1195361 {A B : Type'} (f : A -> B) (m : list B) : (term108 A B f m) = (term109 A B f m).
Proof. exact (eq_refl (term108 A B f m)). Qed.
Lemma lem1195362 {A B : Type'} (f : A -> B) : (term128 A B f) = (term103 A B f).
Proof. exact (fun_ext (fun m : list B => @lem1195361 A B f m)). Qed.
Lemma lem1195363 {B : Type'} : (@all (list B)) = (@all (list B)).
Proof. exact (eq_refl (@all (list B))). Qed.
Lemma lem1195364 {A B : Type'} (f : A -> B) : (term129 A B f) = (term39 A B f).
Proof. exact (MK_COMB (@lem1195363 B) (@lem1195362 A B f)). Qed.
Lemma lem1195365 {A B : Type'} (f : A -> B) : (term102 A B f) = (term130 A B f).
Proof. exact (MK_COMB (@lem1195360 A B f) (@lem1195364 A B f)). Qed.
Lemma lem1195366 {A B : Type'} (f : A -> B) : term130 A B f.
Proof. exact (EQ_MP (@lem1195365 A B f) (@lem1195343 A B f)). Qed.
Lemma lem1195368 (p : Prop) : p = (term131 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1195369 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) : (term101 A B h t f y) = (term132 A B h t f y).
Proof. exact (@lem1195368 (term101 A B h t f y)). Qed.
Lemma lem1195370 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) : (term132 A B h t f y) = (term101 A B h t f y).
Proof. exact (SYM (@lem1195369 A B h t f y)). Qed.
Lemma lem1195371 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term133 A B h t f y) : term133 A B h t f y.
Proof. exact (h1). Qed.
Lemma lem1195372 {A B : Type'} : term134 A B.
Proof. exact (@lem1097800 A B). Qed.
Lemma lem1195373 {A : Type'} : term135 A.
Proof. exact (@lem1097800 A A). Qed.
Lemma lem1195375 {B : Type'} : term135 B.
Proof. exact (@lem1097800 B B). Qed.
Lemma lem1195383 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term136 A B h t f y) : term136 A B h t f y.
Proof. exact (h1). Qed.
Lemma lem1195384 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) : term137 A B h t f y.
Proof. exact (fun h0 : term136 A B h t f y => @lem1195383 A B h t f y h0). Qed.
Lemma lem1195385 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term137 A B h t f y) : term137 A B h t f y.
Proof. exact (h1). Qed.
Lemma lem1195386 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term136 A B h t f y) : term136 A B h t f y.
Proof. exact (h1). Qed.
Lemma lem1195387 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term136 A B h t f y) (h2 : term137 A B h t f y) : term136 A B h t f y.
Proof. exact (@lem1195385 A B h t f y h2 (@lem1195386 A B h t f y h1)). Qed.
Lemma lem1195388 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term136 A B h t f y) : term138 A B h t f y.
Proof. exact (fun h0 : term137 A B h t f y => @lem1195387 A B h t f y h1 h0). Qed.
Lemma lem1195389 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term137 A B h t f y) : term137 A B h t f y.
Proof. exact (h1). Qed.
Lemma lem1195390 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term136 A B h t f y) (h2 : term137 A B h t f y) : term136 A B h t f y.
Proof. exact (@lem1195388 A B h t f y h1 (@lem1195389 A B h t f y h2)). Qed.
Lemma lem1195391 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term137 A B h t f y) : term137 A B h t f y.
Proof. exact (fun h0 : term136 A B h t f y => @lem1195390 A B h t f y h0 h1). Qed.
Lemma lem1195392 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) : term139 A B h t f y.
Proof. exact (fun h0 : term137 A B h t f y => @lem1195391 A B h t f y h0). Qed.
Lemma lem1195395 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) : term137 A B h t f y.
Proof. exact (@lem1195392 A B h t f y (@lem1195384 A B h t f y)). Qed.
Lemma lem1195396 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) : term137 A B h t f y.
Proof. exact (@lem1195395 A B h t f y). Qed.
Lemma lem1195472 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1195473 {B : Type'} : (term140 B) = (term141 B).
Proof. exact (@lem1195472 (term135 B)). Qed.
Lemma lem1195492 {A B : Type'} : (term142 A B) = (term142 A B).
Proof. exact (eq_refl (term142 A B)). Qed.
Lemma lem1195493 {A B : Type'} : (term143 A B) = (term144 A B).
Proof. exact (MK_COMB (@lem1195492 A B) (@lem1195473 B)). Qed.
Lemma lem1195496 {A : Type'} : (term145 A) = (term145 A).
Proof. exact (eq_refl (term145 A)). Qed.
Lemma lem1195497 {A B : Type'} : (term146 A B) = (term147 A B).
Proof. exact (MK_COMB (@lem1195496 A) (@lem1195493 A B)). Qed.
Lemma lem1195500 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) : (term148 A B h t f y) = (term148 A B h t f y).
Proof. exact (eq_refl (term148 A B h t f y)). Qed.
Lemma lem1195501 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) : (term149 A B h t f y) = (term150 A B h t f y).
Proof. exact (MK_COMB (@lem1195500 A B h t f y) (@lem1195497 A B)). Qed.
Lemma lem1195504 {A B : Type'} (t : list A) (f : A -> B) (y : B) : (term71 A B t f y) = (term71 A B t f y).
Proof. exact (eq_refl (term71 A B t f y)). Qed.
Lemma lem1195505 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) : (term136 A B h t f y) = (term151 A B h t f y).
Proof. exact (MK_COMB (@lem1195504 A B t f y) (@lem1195501 A B h t f y)). Qed.
Lemma lem1195508 {A B : Type'} (t : list A) (f : A -> B) (y : B) : (term152 A B t f y) = (term153 A B t f y).
Proof. exact (fun_ext (fun h : A => @lem1195505 A B h t f y)). Qed.
Lemma lem1195509 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1195510 {A B : Type'} (t : list A) (f : A -> B) (y : B) : (term154 A B t f y) = (term155 A B t f y).
Proof. exact (MK_COMB (@lem1195509 A) (@lem1195508 A B t f y)). Qed.
Lemma lem1195515 {A B : Type'} (f : A -> B) (y : B) : (term156 A B f y) = (term157 A B f y).
Proof. exact (fun_ext (fun t : list A => @lem1195510 A B t f y)). Qed.
Lemma lem1195516 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1195517 {A B : Type'} (f : A -> B) (y : B) : (term158 A B f y) = (term159 A B f y).
Proof. exact (MK_COMB (@lem1195516 A) (@lem1195515 A B f y)). Qed.
Lemma lem1195522 {A B : Type'} (y : B) : (term160 A B y) = (term161 A B y).
Proof. exact (fun_ext (fun f : A -> B => @lem1195517 A B f y)). Qed.
Lemma lem1195523 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem1195524 {A B : Type'} (y : B) : (term162 A B y) = (term163 A B y).
Proof. exact (MK_COMB (@lem1195523 A B) (@lem1195522 A B y)). Qed.
Lemma lem1195529 {A B : Type'} : (term164 A B) = (term165 A B).
Proof. exact (fun_ext (fun y : B => @lem1195524 A B y)). Qed.
Lemma lem1195530 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1195539 {A B : Type'} : (term166 A B) = (term167 A B).
Proof. exact (MK_COMB (@lem1195530 B) (@lem1195529 A B)). Qed.
Lemma lem1195540 {B : Type'} (h : B) (f : B -> B) (t : list B) : ((term168 B f h t) = (term169 B h f t)) = ((term168 B f h t) = (term169 B h f t)).
Proof. exact (eq_refl ((term168 B f h t) = (term169 B h f t))). Qed.
Lemma lem1195541 {B : Type'} (h : B) (f : B -> B) : (term170 B h f) = (term170 B h f).
Proof. exact (fun_ext (fun t : list B => @lem1195540 B h f t)). Qed.
Lemma lem1195542 {B : Type'} : (@all (list B)) = (@all (list B)).
Proof. exact (eq_refl (@all (list B))). Qed.
Lemma lem1195543 {B : Type'} (h : B) (f : B -> B) : (term171 B h f) = (term171 B h f).
Proof. exact (MK_COMB (@lem1195542 B) (@lem1195541 B h f)). Qed.
Lemma lem1195544 {B : Type'} (f : B -> B) : (term172 B f) = (term172 B f).
Proof. exact (fun_ext (fun h : B => @lem1195543 B h f)). Qed.
Lemma lem1195545 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1195546 {B : Type'} (f : B -> B) : (term173 B f) = (term173 B f).
Proof. exact (MK_COMB (@lem1195545 B) (@lem1195544 B f)). Qed.
Lemma lem1195547 {B : Type'} : (term174 B) = (term174 B).
Proof. exact (fun_ext (fun f : B -> B => @lem1195546 B f)). Qed.
Lemma lem1195548 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem1195549 {B : Type'} : (term175 B) = (term175 B).
Proof. exact (MK_COMB (@lem1195548 B) (@lem1195547 B)). Qed.
Lemma lem1195550 {B : Type'} (f : B -> B) : ((@List.map B B f (@nil B)) = (@nil B)) = ((@List.map B B f (@nil B)) = (@nil B)).
Proof. exact (eq_refl ((@List.map B B f (@nil B)) = (@nil B))). Qed.
Lemma lem1195551 {B : Type'} : (term176 B) = (term176 B).
Proof. exact (fun_ext (fun f : B -> B => @lem1195550 B f)). Qed.
Lemma lem1195552 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem1195553 {B : Type'} : (term177 B) = (term177 B).
Proof. exact (MK_COMB (@lem1195552 B) (@lem1195551 B)). Qed.
Lemma lem1195554 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1195555 {B : Type'} : (term178 B) = (term178 B).
Proof. exact (MK_COMB (@lem1195554) (@lem1195553 B)). Qed.
Lemma lem1195556 {B : Type'} : (term135 B) = (term135 B).
Proof. exact (MK_COMB (@lem1195555 B) (@lem1195549 B)). Qed.
Lemma lem1195557 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1195558 {B : Type'} : (term141 B) = (term141 B).
Proof. exact (MK_COMB (@lem1195557) (@lem1195556 B)). Qed.
Lemma lem1195559 {A B : Type'} (h : A) (f : A -> B) (t : list A) : ((term30 A B f h t) = (term31 A B h f t)) = ((term30 A B f h t) = (term31 A B h f t)).
Proof. exact (eq_refl ((term30 A B f h t) = (term31 A B h f t))). Qed.
Lemma lem1195560 {A B : Type'} (h : A) (f : A -> B) : (term179 A B h f) = (term179 A B h f).
Proof. exact (fun_ext (fun t : list A => @lem1195559 A B h f t)). Qed.
Lemma lem1195561 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1195562 {A B : Type'} (h : A) (f : A -> B) : (term28 A B h f) = (term28 A B h f).
Proof. exact (MK_COMB (@lem1195561 A) (@lem1195560 A B h f)). Qed.
Lemma lem1195563 {A B : Type'} (f : A -> B) : (term180 A B f) = (term180 A B f).
Proof. exact (fun_ext (fun h : A => @lem1195562 A B h f)). Qed.
Lemma lem1195564 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1195565 {A B : Type'} (f : A -> B) : (term26 A B f) = (term26 A B f).
Proof. exact (MK_COMB (@lem1195564 A) (@lem1195563 A B f)). Qed.
Lemma lem1195566 {A B : Type'} : (term181 A B) = (term181 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem1195565 A B f)). Qed.
Lemma lem1195567 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem1195568 {A B : Type'} : (term24 A B) = (term24 A B).
Proof. exact (MK_COMB (@lem1195567 A B) (@lem1195566 A B)). Qed.
Lemma lem1195569 {A B : Type'} (f : A -> B) : ((@List.map A B f (@nil A)) = (@nil B)) = ((@List.map A B f (@nil A)) = (@nil B)).
Proof. exact (eq_refl ((@List.map A B f (@nil A)) = (@nil B))). Qed.
Lemma lem1195570 {A B : Type'} : (term182 A B) = (term182 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem1195569 A B f)). Qed.
Lemma lem1195571 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem1195572 {A B : Type'} : (term32 A B) = (term32 A B).
Proof. exact (MK_COMB (@lem1195571 A B) (@lem1195570 A B)). Qed.
Lemma lem1195573 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1195574 {A B : Type'} : (term183 A B) = (term183 A B).
Proof. exact (MK_COMB (@lem1195573) (@lem1195572 A B)). Qed.
Lemma lem1195575 {A B : Type'} : (term134 A B) = (term134 A B).
Proof. exact (MK_COMB (@lem1195574 A B) (@lem1195568 A B)). Qed.
Lemma lem1195576 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1195577 {A B : Type'} : (term142 A B) = (term142 A B).
Proof. exact (MK_COMB (@lem1195576) (@lem1195575 A B)). Qed.
Lemma lem1195578 {A B : Type'} : (term144 A B) = (term144 A B).
Proof. exact (MK_COMB (@lem1195577 A B) (@lem1195558 B)). Qed.
Lemma lem1195579 {A : Type'} (h : A) (f : A -> A) (t : list A) : ((term168 A f h t) = (term169 A h f t)) = ((term168 A f h t) = (term169 A h f t)).
Proof. exact (eq_refl ((term168 A f h t) = (term169 A h f t))). Qed.
Lemma lem1195580 {A : Type'} (h : A) (f : A -> A) : (term170 A h f) = (term170 A h f).
Proof. exact (fun_ext (fun t : list A => @lem1195579 A h f t)). Qed.
Lemma lem1195581 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1195582 {A : Type'} (h : A) (f : A -> A) : (term171 A h f) = (term171 A h f).
Proof. exact (MK_COMB (@lem1195581 A) (@lem1195580 A h f)). Qed.
Lemma lem1195583 {A : Type'} (f : A -> A) : (term172 A f) = (term172 A f).
Proof. exact (fun_ext (fun h : A => @lem1195582 A h f)). Qed.
Lemma lem1195584 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1195585 {A : Type'} (f : A -> A) : (term173 A f) = (term173 A f).
Proof. exact (MK_COMB (@lem1195584 A) (@lem1195583 A f)). Qed.
Lemma lem1195586 {A : Type'} : (term174 A) = (term174 A).
Proof. exact (fun_ext (fun f : A -> A => @lem1195585 A f)). Qed.
Lemma lem1195587 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem1195588 {A : Type'} : (term175 A) = (term175 A).
Proof. exact (MK_COMB (@lem1195587 A) (@lem1195586 A)). Qed.
Lemma lem1195589 {A : Type'} (f : A -> A) : ((@List.map A A f (@nil A)) = (@nil A)) = ((@List.map A A f (@nil A)) = (@nil A)).
Proof. exact (eq_refl ((@List.map A A f (@nil A)) = (@nil A))). Qed.
Lemma lem1195590 {A : Type'} : (term176 A) = (term176 A).
Proof. exact (fun_ext (fun f : A -> A => @lem1195589 A f)). Qed.
Lemma lem1195591 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem1195592 {A : Type'} : (term177 A) = (term177 A).
Proof. exact (MK_COMB (@lem1195591 A) (@lem1195590 A)). Qed.
Lemma lem1195593 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1195594 {A : Type'} : (term178 A) = (term178 A).
Proof. exact (MK_COMB (@lem1195593) (@lem1195592 A)). Qed.
Lemma lem1195595 {A : Type'} : (term135 A) = (term135 A).
Proof. exact (MK_COMB (@lem1195594 A) (@lem1195588 A)). Qed.
Lemma lem1195596 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1195597 {A : Type'} : (term145 A) = (term145 A).
Proof. exact (MK_COMB (@lem1195596) (@lem1195595 A)). Qed.
Lemma lem1195598 {A B : Type'} : (term147 A B) = (term147 A B).
Proof. exact (MK_COMB (@lem1195597 A) (@lem1195578 A B)). Qed.
Lemma lem1195599 {A B : Type'} (f : A -> B) (x : A) (y : B) : ((f x) = y) = ((f x) = y).
Proof. exact (eq_refl ((f x) = y)). Qed.
Lemma lem1195600 {A B : Type'} (f : A -> B) (y : B) : (term184 A B f y) = (term184 A B f y).
Proof. exact (fun_ext (fun x : A => @lem1195599 A B f x y)). Qed.
Lemma lem1195601 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1195602 {A B : Type'} (f : A -> B) (y : B) : (term48 A B f y) = (term48 A B f y).
Proof. exact (MK_COMB (@lem1195601 A) (@lem1195600 A B f y)). Qed.
Lemma lem1195609 {A B : Type'} (f : A -> B) (h : A) (y : B) (t : list A) : (term100 A B f h y t) = (term100 A B f h y t).
Proof. exact (eq_refl (term100 A B f h y t)). Qed.
Lemma lem1195610 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) : (term101 A B h t f y) = (term101 A B h t f y).
Proof. exact (MK_COMB (@lem1195609 A B f h y t) (@lem1195602 A B f y)). Qed.
Lemma lem1195611 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1195612 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) : (term133 A B h t f y) = (term133 A B h t f y).
Proof. exact (MK_COMB (@lem1195611) (@lem1195610 A B h t f y)). Qed.
Lemma lem1195613 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1195614 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) : (term148 A B h t f y) = (term148 A B h t f y).
Proof. exact (MK_COMB (@lem1195613) (@lem1195612 A B h t f y)). Qed.
Lemma lem1195615 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) : (term150 A B h t f y) = (term150 A B h t f y).
Proof. exact (MK_COMB (@lem1195614 A B h t f y) (@lem1195598 A B)). Qed.
Lemma lem1195616 {A B : Type'} (f : A -> B) (x : A) (y : B) : ((f x) = y) = ((f x) = y).
Proof. exact (eq_refl ((f x) = y)). Qed.
Lemma lem1195617 {A B : Type'} (f : A -> B) (y : B) : (term184 A B f y) = (term184 A B f y).
Proof. exact (fun_ext (fun x : A => @lem1195616 A B f x y)). Qed.
Lemma lem1195618 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1195619 {A B : Type'} (f : A -> B) (y : B) : (term48 A B f y) = (term48 A B f y).
Proof. exact (MK_COMB (@lem1195618 A) (@lem1195617 A B f y)). Qed.
Lemma lem1195622 {A B : Type'} (f : A -> B) (t : list A) (y : B) : (term58 A B f t y) = (term58 A B f t y).
Proof. exact (eq_refl (term58 A B f t y)). Qed.
Lemma lem1195623 {A B : Type'} (t : list A) (f : A -> B) (y : B) : (term60 A B t f y) = (term60 A B t f y).
Proof. exact (MK_COMB (@lem1195622 A B f t y) (@lem1195619 A B f y)). Qed.
Lemma lem1195624 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1195625 {A B : Type'} (t : list A) (f : A -> B) (y : B) : (term71 A B t f y) = (term71 A B t f y).
Proof. exact (MK_COMB (@lem1195624) (@lem1195623 A B t f y)). Qed.
Lemma lem1195626 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) : (term151 A B h t f y) = (term151 A B h t f y).
Proof. exact (MK_COMB (@lem1195625 A B t f y) (@lem1195615 A B h t f y)). Qed.
Lemma lem1195627 {A B : Type'} (t : list A) (f : A -> B) (y : B) : (term153 A B t f y) = (term153 A B t f y).
Proof. exact (fun_ext (fun h : A => @lem1195626 A B h t f y)). Qed.
Lemma lem1195628 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1195629 {A B : Type'} (t : list A) (f : A -> B) (y : B) : (term155 A B t f y) = (term155 A B t f y).
Proof. exact (MK_COMB (@lem1195628 A) (@lem1195627 A B t f y)). Qed.
Lemma lem1195630 {A B : Type'} (f : A -> B) (y : B) : (term157 A B f y) = (term157 A B f y).
Proof. exact (fun_ext (fun t : list A => @lem1195629 A B t f y)). Qed.
Lemma lem1195631 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1195632 {A B : Type'} (f : A -> B) (y : B) : (term159 A B f y) = (term159 A B f y).
Proof. exact (MK_COMB (@lem1195631 A) (@lem1195630 A B f y)). Qed.
Lemma lem1195633 {A B : Type'} (y : B) : (term161 A B y) = (term161 A B y).
Proof. exact (fun_ext (fun f : A -> B => @lem1195632 A B f y)). Qed.
Lemma lem1195634 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem1195635 {A B : Type'} (y : B) : (term163 A B y) = (term163 A B y).
Proof. exact (MK_COMB (@lem1195634 A B) (@lem1195633 A B y)). Qed.
Lemma lem1195636 {A B : Type'} : (term165 A B) = (term165 A B).
Proof. exact (fun_ext (fun y : B => @lem1195635 A B y)). Qed.
Lemma lem1195637 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1195638 {A B : Type'} : (term167 A B) = (term167 A B).
Proof. exact (MK_COMB (@lem1195637 B) (@lem1195636 A B)). Qed.
Lemma lem1195769 {A B : Type'} : (term166 A B) = (term167 A B).
Proof. exact (TRANS (@lem1195539 A B) (@lem1195638 A B)). Qed.
Lemma lem1195770 {A B : Type'} : (term167 A B) = (term166 A B).
Proof. exact (SYM (@lem1195769 A B)). Qed.
Lemma lem1195771 {A B : Type'} (t : list A) (f : A -> B) (y : B) (h1 : term60 A B t f y) : term60 A B t f y.
Proof. exact (h1). Qed.
Lemma lem1195772 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term133 A B h t f y) : term133 A B h t f y.
Proof. exact (h1). Qed.
Lemma lem1195777 {A B : Type'} (f : A -> B) (x : A) (y : B) : ((f x) = y) = ((f x) = y).
Proof. exact (eq_refl ((f x) = y)). Qed.
Lemma lem1195778 {A B : Type'} (f : A -> B) (y : B) : (term184 A B f y) = (term184 A B f y).
Proof. exact (fun_ext (fun x : A => @lem1195777 A B f x y)). Qed.
Lemma lem1195779 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1195780 {A B : Type'} (f : A -> B) (y : B) : (term48 A B f y) = (term48 A B f y).
Proof. exact (MK_COMB (@lem1195779 A) (@lem1195778 A B f y)). Qed.
Lemma lem1195782 {A B : Type'} (f : A -> B) (t : list A) (y : B) : (term185 A B f t y) = (term185 A B f t y).
Proof. exact (eq_refl (term185 A B f t y)). Qed.
Lemma lem1195783 {A B : Type'} (t : list A) (f : A -> B) (y : B) : (term186 A B t f y) = (term186 A B t f y).
Proof. exact (MK_COMB (@lem1195782 A B f t y) (@lem1195780 A B f y)). Qed.
Lemma lem1195784 {A B : Type'} (t : list A) (f : A -> B) (y : B) : (term60 A B t f y) = (term186 A B t f y).
Proof. exact (@lem17265 ((@List.map A B f t) = (@cons B y (@nil B))) (term48 A B f y)). Qed.
Lemma lem1195785 {A B : Type'} (t : list A) (f : A -> B) (y : B) : (term60 A B t f y) = (term186 A B t f y).
Proof. exact (TRANS (@lem1195784 A B t f y) (@lem1195783 A B t f y)). Qed.
Lemma lem1195792 {A : Type'} (P : Prop) (Q : A -> Prop) : (term187 A P Q) = (term188 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1195793 {A : Type'} (P : Prop) (Q : A -> Prop) : (term187 A P Q) = (term188 A P Q).
Proof. exact (@lem1195792 A P Q). Qed.
Lemma lem1195794 {A B : Type'} (t : list A) (f : A -> B) (y : B) : (term189 A B t f y) = (term190 A B t f y).
Proof. exact (@lem1195793 A (term191 A B f t y) (term184 A B f y)). Qed.
Lemma lem1195795 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term192 A B f y x) = ((f x) = y).
Proof. exact (eq_refl (term192 A B f y x)). Qed.
Lemma lem1195796 {A B : Type'} (f : A -> B) (y : B) : (term193 A B f y) = (term184 A B f y).
Proof. exact (fun_ext (fun x : A => @lem1195795 A B f x y)). Qed.
Lemma lem1195797 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1195798 {A B : Type'} (f : A -> B) (y : B) : (term194 A B f y) = (term48 A B f y).
Proof. exact (MK_COMB (@lem1195797 A) (@lem1195796 A B f y)). Qed.
Lemma lem1195799 {A B : Type'} (f : A -> B) (t : list A) (y : B) : (term185 A B f t y) = (term185 A B f t y).
Proof. exact (eq_refl (term185 A B f t y)). Qed.
Lemma lem1195800 {A B : Type'} (t : list A) (f : A -> B) (y : B) : (term189 A B t f y) = (term186 A B t f y).
Proof. exact (MK_COMB (@lem1195799 A B f t y) (@lem1195798 A B f y)). Qed.
Lemma lem1195801 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1195802 {A B : Type'} (t : list A) (f : A -> B) (y : B) : (term195 A B t f y) = (term196 A B t f y).
Proof. exact (MK_COMB (@lem1195801) (@lem1195800 A B t f y)). Qed.
Lemma lem1195803 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term192 A B f y x) = ((f x) = y).
Proof. exact (eq_refl (term192 A B f y x)). Qed.
Lemma lem1195804 {A B : Type'} (f : A -> B) (t : list A) (y : B) : (term185 A B f t y) = (term185 A B f t y).
Proof. exact (eq_refl (term185 A B f t y)). Qed.
Lemma lem1195805 {A B : Type'} (t : list A) (f : A -> B) (x : A) (y : B) : (term197 A B t f y x) = (term198 A B t f x y).
Proof. exact (MK_COMB (@lem1195804 A B f t y) (@lem1195803 A B f x y)). Qed.
Lemma lem1195806 {A B : Type'} (t : list A) (f : A -> B) (y : B) : (term199 A B t f y) = (term200 A B t f y).
Proof. exact (fun_ext (fun x : A => @lem1195805 A B t f x y)). Qed.
Lemma lem1195807 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1195808 {A B : Type'} (t : list A) (f : A -> B) (y : B) : (term190 A B t f y) = (term201 A B t f y).
Proof. exact (MK_COMB (@lem1195807 A) (@lem1195806 A B t f y)). Qed.
Lemma lem1195809 {A B : Type'} (t : list A) (f : A -> B) (y : B) : ((term189 A B t f y) = (term190 A B t f y)) = ((term186 A B t f y) = (term201 A B t f y)).
Proof. exact (MK_COMB (@lem1195802 A B t f y) (@lem1195808 A B t f y)). Qed.
Lemma lem1195811 {A B : Type'} (t : list A) (f : A -> B) (y : B) : (term186 A B t f y) = (term201 A B t f y).
Proof. exact (EQ_MP (@lem1195809 A B t f y) (@lem1195794 A B t f y)). Qed.
Lemma lem1195812 {A B : Type'} (t : list A) (f : A -> B) (y : B) : (term60 A B t f y) = (term201 A B t f y).
Proof. exact (TRANS (@lem1195785 A B t f y) (@lem1195811 A B t f y)). Qed.
Lemma lem1195813 {A B : Type'} (t : list A) (f : A -> B) (y : B) (h1 : term60 A B t f y) : term201 A B t f y.
Proof. exact (EQ_MP (@lem1195812 A B t f y) (@lem1195771 A B t f y h1)). Qed.
Lemma lem1195820 {A : Type'} (P : A -> Prop) : (term202 A P) = (term203 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem1195821 {A B : Type'} (f : A -> B) (y : B) : (term204 A B f y) = (term205 A B f y).
Proof. exact (@lem1195820 A (term184 A B f y)). Qed.
Lemma lem1195822 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term192 A B f y x) = ((f x) = y).
Proof. exact (eq_refl (term192 A B f y x)). Qed.
Lemma lem1195823 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1195825 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term206 A B f y x) = (term207 A B f x y).
Proof. exact (MK_COMB (@lem1195823) (@lem1195822 A B f x y)). Qed.
Lemma lem1195826 {A B : Type'} (f : A -> B) (y : B) : (term208 A B f y) = (term209 A B f y).
Proof. exact (fun_ext (fun x : A => @lem1195825 A B f x y)). Qed.
Lemma lem1195827 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1195828 {A B : Type'} (f : A -> B) (y : B) : (term205 A B f y) = (term210 A B f y).
Proof. exact (MK_COMB (@lem1195827 A) (@lem1195826 A B f y)). Qed.
Lemma lem1195829 {A B : Type'} (f : A -> B) (y : B) : (term204 A B f y) = (term210 A B f y).
Proof. exact (TRANS (@lem1195821 A B f y) (@lem1195828 A B f y)). Qed.
Lemma lem1195831 {A B : Type'} (f : A -> B) (h : A) (y : B) (t : list A) : (term211 A B f h y t) = (term211 A B f h y t).
Proof. exact (eq_refl (term211 A B f h y t)). Qed.
Lemma lem1195832 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) : (term212 A B h t f y) = (term213 A B h t f y).
Proof. exact (MK_COMB (@lem1195831 A B f h y t) (@lem1195829 A B f y)). Qed.
Lemma lem1195833 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) : (term133 A B h t f y) = (term212 A B h t f y).
Proof. exact (@lem17362 (term98 A B f h y t) (term48 A B f y)). Qed.
Lemma lem1195842 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) : (term133 A B h t f y) = (term213 A B h t f y).
Proof. exact (TRANS (@lem1195833 A B h t f y) (@lem1195832 A B h t f y)). Qed.
Lemma lem1195843 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term133 A B h t f y) : term213 A B h t f y.
Proof. exact (EQ_MP (@lem1195842 A B h t f y) (@lem1195772 A B h t f y h1)). Qed.
Lemma lem1195958 {A B : Type'} (t : list A) (f : A -> B) (x : A) (y : B) (h1 : term198 A B t f x y) : term198 A B t f x y.
Proof. exact (h1). Qed.
Lemma lem1195959 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1195960 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem1195965 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1195967 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem1195965 A B f x). Qed.
Lemma lem1195968 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1195969 {A B : Type'} (f : A -> B) (x : A) : (term214 A B f x) = (term215 A B f x).
Proof. exact (MK_COMB (@lem1195960 B) (@lem1195967 A B f x)). Qed.
Lemma lem1195970 {A B : Type'} (f : A -> B) (x : A) (y : B) : ((f x) = y) = ((@I (A -> B) f x) = y).
Proof. exact (MK_COMB (@lem1195969 A B f x) (@lem1195968 B y)). Qed.
Lemma lem1195971 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term207 A B f x y) = (term216 A B f x y).
Proof. exact (MK_COMB (@lem1195959) (@lem1195970 A B f x y)). Qed.
Lemma lem1195972 {A B : Type'} (f : A -> B) (y : B) : (term209 A B f y) = (term217 A B f y).
Proof. exact (fun_ext (fun x : A => @lem1195971 A B f x y)). Qed.
Lemma lem1195973 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1195974 {A B : Type'} (f : A -> B) (y : B) : (term210 A B f y) = (term218 A B f y).
Proof. exact (MK_COMB (@lem1195973 A) (@lem1195972 A B f y)). Qed.
Lemma lem1195979 {A : Type'} (t : list A) : (t = (@nil A)) = (t = (@nil A)).
Proof. exact (eq_refl (t = (@nil A))). Qed.
Lemma lem1195980 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem1195985 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1195986 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem1195985 A B f x). Qed.
Lemma lem1195988 {A B : Type'} (f : A -> B) (h : A) : (f h) = (@I (A -> B) f h).
Proof. exact (@lem1195986 A B f h). Qed.
Lemma lem1195989 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1195990 {A B : Type'} (f : A -> B) (h : A) : (term214 A B f h) = (term215 A B f h).
Proof. exact (MK_COMB (@lem1195980 B) (@lem1195988 A B f h)). Qed.
Lemma lem1195991 {A B : Type'} (f : A -> B) (h : A) (y : B) : ((f h) = y) = ((@I (A -> B) f h) = y).
Proof. exact (MK_COMB (@lem1195990 A B f h) (@lem1195989 B y)). Qed.
Lemma lem1195992 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1195993 {A B : Type'} (f : A -> B) (h : A) (y : B) : (term97 A B f h y) = (term219 A B f h y).
Proof. exact (MK_COMB (@lem1195992) (@lem1195991 A B f h y)). Qed.
Lemma lem1195994 {A B : Type'} (f : A -> B) (h : A) (y : B) (t : list A) : (term98 A B f h y t) = (term220 A B f h y t).
Proof. exact (MK_COMB (@lem1195993 A B f h y) (@lem1195979 A t)). Qed.
Lemma lem1195995 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1195996 {A B : Type'} (f : A -> B) (h : A) (y : B) (t : list A) : (term211 A B f h y t) = (term221 A B f h y t).
Proof. exact (MK_COMB (@lem1195995) (@lem1195994 A B f h y t)). Qed.
Lemma lem1195997 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) : (term213 A B h t f y) = (term222 A B h t f y).
Proof. exact (MK_COMB (@lem1195996 A B f h y t) (@lem1195974 A B f y)). Qed.
Lemma lem1195998 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term133 A B h t f y) : term222 A B h t f y.
Proof. exact (EQ_MP (@lem1195997 A B h t f y) (@lem1195843 A B h t f y h1)). Qed.
Lemma lem1196338 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem1196343 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1196345 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem1196343 A B f x). Qed.
Lemma lem1196346 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1196347 {A B : Type'} (f : A -> B) (x : A) : (term214 A B f x) = (term215 A B f x).
Proof. exact (MK_COMB (@lem1196338 B) (@lem1196345 A B f x)). Qed.
Lemma lem1196348 {A B : Type'} (f : A -> B) (x : A) (y : B) : ((f x) = y) = ((@I (A -> B) f x) = y).
Proof. exact (MK_COMB (@lem1196347 A B f x) (@lem1196346 B y)). Qed.
Lemma lem1196349 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1196350 {B : Type'} : (@eq (list B)) = (@eq (list B)).
Proof. exact (eq_refl (@eq (list B))). Qed.
Lemma lem1196357 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1196358 {A B : Type'} (f : type540 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (list A) -> list B) f x).
Proof. exact (@lem1196357 (A -> B) (type1139 A B) f x). Qed.
Lemma lem1196359 {A B : Type'} (f : A -> B) : (@List.map A B f) = (@I ((A -> B) -> (list A) -> list B) (@List.map A B) f).
Proof. exact (@lem1196358 A B (@List.map A B) f). Qed.
Lemma lem1196360 {A : Type'} (t : list A) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1196361 {A B : Type'} (f : A -> B) (t : list A) : (@List.map A B f t) = (@I ((A -> B) -> (list A) -> list B) (@List.map A B) f t).
Proof. exact (MK_COMB (@lem1196359 A B f) (@lem1196360 A t)). Qed.
Lemma lem1196363 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1196364 {A B : Type'} (f : type1139 A B) (x : list A) : (f x) = (@I ((list A) -> list B) f x).
Proof. exact (@lem1196363 (list A) (list B) f x). Qed.
Lemma lem1196365 {A B : Type'} (f : A -> B) (t : list A) : (@I ((A -> B) -> (list A) -> list B) (@List.map A B) f t) = (term223 A B f t).
Proof. exact (@lem1196364 A B (@I ((A -> B) -> (list A) -> list B) (@List.map A B) f) t). Qed.
Lemma lem1196367 {A B : Type'} (f : A -> B) (t : list A) : (@List.map A B f t) = (term223 A B f t).
Proof. exact (TRANS (@lem1196361 A B f t) (@lem1196365 A B f t)). Qed.
Lemma lem1196374 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1196375 {B : Type'} (f : type1397 B) (x : B) : (f x) = (@I (B -> (list B) -> list B) f x).
Proof. exact (@lem1196374 B (type1138 B) f x). Qed.
Lemma lem1196376 {B : Type'} (y : B) : (@cons B y) = (@I (B -> (list B) -> list B) (@cons B) y).
Proof. exact (@lem1196375 B (@cons B) y). Qed.
Lemma lem1196377 {B : Type'} : (@nil B) = (@nil B).
Proof. exact (eq_refl (@nil B)). Qed.
Lemma lem1196378 {B : Type'} (y : B) : (@cons B y (@nil B)) = (@I (B -> (list B) -> list B) (@cons B) y (@nil B)).
Proof. exact (MK_COMB (@lem1196376 B y) (@lem1196377 B)). Qed.
Lemma lem1196380 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1196381 {B : Type'} (f : type1138 B) (x : list B) : (f x) = (@I ((list B) -> list B) f x).
Proof. exact (@lem1196380 (list B) (list B) f x). Qed.
Lemma lem1196382 {B : Type'} (y : B) : (@I (B -> (list B) -> list B) (@cons B) y (@nil B)) = (term224 B y).
Proof. exact (@lem1196381 B (@I (B -> (list B) -> list B) (@cons B) y) (@nil B)). Qed.
Lemma lem1196384 {B : Type'} (y : B) : (@cons B y (@nil B)) = (term224 B y).
Proof. exact (TRANS (@lem1196378 B y) (@lem1196382 B y)). Qed.
Lemma lem1196385 {A B : Type'} (f : A -> B) (t : list A) : (term225 A B f t) = (term226 A B f t).
Proof. exact (MK_COMB (@lem1196350 B) (@lem1196367 A B f t)). Qed.
Lemma lem1196386 {A B : Type'} (f : A -> B) (t : list A) (y : B) : ((@List.map A B f t) = (@cons B y (@nil B))) = ((term223 A B f t) = (term224 B y)).
Proof. exact (MK_COMB (@lem1196385 A B f t) (@lem1196384 B y)). Qed.
Lemma lem1196387 {A B : Type'} (f : A -> B) (t : list A) (y : B) : (term191 A B f t y) = (term227 A B f t y).
Proof. exact (MK_COMB (@lem1196349) (@lem1196386 A B f t y)). Qed.
Lemma lem1196388 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1196389 {A B : Type'} (f : A -> B) (t : list A) (y : B) : (term185 A B f t y) = (term228 A B f t y).
Proof. exact (MK_COMB (@lem1196388) (@lem1196387 A B f t y)). Qed.
Lemma lem1196390 {A B : Type'} (t : list A) (f : A -> B) (x : A) (y : B) : (term198 A B t f x y) = (term229 A B t f x y).
Proof. exact (MK_COMB (@lem1196389 A B f t y) (@lem1196348 A B f x y)). Qed.
Lemma lem1196391 {A B : Type'} (t : list A) (f : A -> B) (x : A) (y : B) (h1 : term198 A B t f x y) : term229 A B t f x y.
Proof. exact (EQ_MP (@lem1196390 A B t f x y) (@lem1195958 A B t f x y h1)). Qed.
Lemma lem1196398 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term133 A B h t f y) : term218 A B f y.
Proof. exact (proj2 (@lem1195998 A B h t f y h1)). Qed.
Lemma lem1196399 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term133 A B h t f y) : term220 A B f h y t.
Proof. exact (proj1 (@lem1195998 A B h t f y h1)). Qed.
Lemma lem1196465 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term216 A B f x y) = (term216 A B f x y).
Proof. exact (eq_refl (term216 A B f x y)). Qed.
Lemma lem1196466 {A B : Type'} (f : A -> B) (y : B) : (term217 A B f y) = (term217 A B f y).
Proof. exact (fun_ext (fun x : A => @lem1196465 A B f x y)). Qed.
Lemma lem1196467 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1196469 {A B : Type'} (f : A -> B) (y : B) : (term218 A B f y) = (term218 A B f y).
Proof. exact (MK_COMB (@lem1196467 A) (@lem1196466 A B f y)). Qed.
Lemma lem1196470 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term133 A B h t f y) : term218 A B f y.
Proof. exact (EQ_MP (@lem1196469 A B f y) (@lem1196398 A B h t f y h1)). Qed.
Lemma lem1196544 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term216 A B f x y) = (term216 A B f x y).
Proof. exact (eq_refl (term216 A B f x y)). Qed.
Lemma lem1196545 {A B : Type'} (f : A -> B) (y : B) : (term217 A B f y) = (term217 A B f y).
Proof. exact (fun_ext (fun x : A => @lem1196544 A B f x y)). Qed.
Lemma lem1196546 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1196548 {A B : Type'} (f : A -> B) (y : B) : (term218 A B f y) = (term218 A B f y).
Proof. exact (MK_COMB (@lem1196546 A) (@lem1196545 A B f y)). Qed.
Lemma lem1196549 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term133 A B h t f y) : term218 A B f y.
Proof. exact (EQ_MP (@lem1196548 A B f y) (@lem1196398 A B h t f y h1)). Qed.
Lemma lem1196561 {A B : Type'} (f : A -> B) (x : A) (y : B) (h1 : (@I (A -> B) f x) = y) : (@I (A -> B) f x) = y.
Proof. exact (h1). Qed.
Lemma lem1196598 {A B : Type'} (_21324 : A) (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term133 A B h t f y) : term230 A B f y _21324.
Proof. exact (@lem1196470 A B h t f y h1 _21324). Qed.
Lemma lem1196599 {A B : Type'} (f : A -> B) (_21324 : A) (y : B) : (term230 A B f y _21324) = (term216 A B f _21324 y).
Proof. exact (eq_refl (term230 A B f y _21324)). Qed.
Lemma lem1196637 {A B : Type'} (_21337 : A) (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term133 A B h t f y) : term230 A B f y _21337.
Proof. exact (@lem1196549 A B h t f y h1 _21337). Qed.
Lemma lem1196638 {A B : Type'} (f : A -> B) (_21337 : A) (y : B) : (term230 A B f y _21337) = (term216 A B f _21337 y).
Proof. exact (eq_refl (term230 A B f y _21337)). Qed.
Lemma lem1196673 {A B : Type'} (_21337 : A) (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term133 A B h t f y) : term216 A B f _21337 y.
Proof. exact (EQ_MP (@lem1196638 A B f _21337 y) (@lem1196637 A B _21337 h t f y h1)). Qed.
Lemma lem1196675 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term133 A B h t f y) : (@I (A -> B) f h) = y.
Proof. exact (proj1 (@lem1196399 A B h t f y h1)). Qed.
Lemma lem1196679 {A B : Type'} (f : A -> B) (x : A) (y : B) (h1 : (@I (A -> B) f x) = y) : (@I (A -> B) f x) = y.
Proof. exact (h1). Qed.
Lemma lem1196791 {A B : Type'} (_21324 : A) (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term133 A B h t f y) : term216 A B f _21324 y.
Proof. exact (EQ_MP (@lem1196599 A B f _21324 y) (@lem1196598 A B _21324 h t f y h1)). Qed.
Lemma lem1196805 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term133 A B h t f y) : (@I (A -> B) f h) = y.
Proof. exact (proj1 (@lem1196399 A B h t f y h1)). Qed.
Lemma lem1196819 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term133 A B h t f y) : y = (@I (A -> B) f h).
Proof. exact (SYM (@lem1196805 A B h t f y h1)). Qed.
Lemma lem1196918 {A B : Type'} (f : A -> B) (_21324 : A) : (term231 A B f _21324) = (term231 A B f _21324).
Proof. exact (eq_refl (term231 A B f _21324)). Qed.
Lemma lem1196919 {A B : Type'} (_21324 : A) (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term133 A B h t f y) : (term232 A B f _21324 y) = (term233 A B _21324 f h).
Proof. exact (MK_COMB (@lem1196918 A B f _21324) (@lem1196819 A B h t f y h1)). Qed.
Lemma lem1196920 {A B : Type'} (_21324 : A) (f : A -> B) (h : A) : (term233 A B _21324 f h) = (term234 A B _21324 f h).
Proof. exact (eq_refl (term233 A B _21324 f h)). Qed.
Lemma lem1196921 {A B : Type'} (f : A -> B) (_21324 : A) (y : B) : (term235 A B f _21324 y) = (term235 A B f _21324 y).
Proof. exact (eq_refl (term235 A B f _21324 y)). Qed.
Lemma lem1196922 {A B : Type'} (y : B) (_21324 : A) (f : A -> B) (h : A) : ((term232 A B f _21324 y) = (term233 A B _21324 f h)) = ((term232 A B f _21324 y) = (term234 A B _21324 f h)).
Proof. exact (MK_COMB (@lem1196921 A B f _21324 y) (@lem1196920 A B _21324 f h)). Qed.
Lemma lem1196923 {A B : Type'} (f : A -> B) (_21324 : A) (y : B) : (term232 A B f _21324 y) = (term216 A B f _21324 y).
Proof. exact (eq_refl (term232 A B f _21324 y)). Qed.
Lemma lem1196924 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1196925 {A B : Type'} (f : A -> B) (_21324 : A) (y : B) : (term235 A B f _21324 y) = (term236 A B f _21324 y).
Proof. exact (MK_COMB (@lem1196924) (@lem1196923 A B f _21324 y)). Qed.
Lemma lem1196926 {A B : Type'} (_21324 : A) (f : A -> B) (h : A) : (term234 A B _21324 f h) = (term234 A B _21324 f h).
Proof. exact (eq_refl (term234 A B _21324 f h)). Qed.
Lemma lem1196927 {A B : Type'} (y : B) (_21324 : A) (f : A -> B) (h : A) : ((term232 A B f _21324 y) = (term234 A B _21324 f h)) = ((term216 A B f _21324 y) = (term234 A B _21324 f h)).
Proof. exact (MK_COMB (@lem1196925 A B f _21324 y) (@lem1196926 A B _21324 f h)). Qed.
Lemma lem1196928 {A B : Type'} (y : B) (_21324 : A) (f : A -> B) (h : A) : ((term232 A B f _21324 y) = (term233 A B _21324 f h)) = ((term216 A B f _21324 y) = (term234 A B _21324 f h)).
Proof. exact (TRANS (@lem1196922 A B y _21324 f h) (@lem1196927 A B y _21324 f h)). Qed.
Lemma lem1196929 {A B : Type'} (_21324 : A) (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term133 A B h t f y) : (term216 A B f _21324 y) = (term234 A B _21324 f h).
Proof. exact (EQ_MP (@lem1196928 A B y _21324 f h) (@lem1196919 A B _21324 h t f y h1)). Qed.
Lemma lem1196930 {A B : Type'} (_21324 : A) (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term133 A B h t f y) : term234 A B _21324 f h.
Proof. exact (EQ_MP (@lem1196929 A B _21324 h t f y h1) (@lem1196791 A B _21324 h t f y h1)). Qed.
Lemma lem1196944 {A B : Type'} (f : A -> B) (x : A) (y : B) (h1 : (@I (A -> B) f x) = y) : y = (@I (A -> B) f x).
Proof. exact (SYM (@lem1196679 A B f x y h1)). Qed.
Lemma lem1197043 {A B : Type'} (f : A -> B) (_21337 : A) : (term231 A B f _21337) = (term231 A B f _21337).
Proof. exact (eq_refl (term231 A B f _21337)). Qed.
Lemma lem1197044 {A B : Type'} (_21337 : A) (f : A -> B) (x : A) (y : B) (h1 : (@I (A -> B) f x) = y) : (term232 A B f _21337 y) = (term233 A B _21337 f x).
Proof. exact (MK_COMB (@lem1197043 A B f _21337) (@lem1196944 A B f x y h1)). Qed.
Lemma lem1197045 {A B : Type'} (_21337 : A) (f : A -> B) (x : A) : (term233 A B _21337 f x) = (term234 A B _21337 f x).
Proof. exact (eq_refl (term233 A B _21337 f x)). Qed.
Lemma lem1197046 {A B : Type'} (f : A -> B) (_21337 : A) (y : B) : (term235 A B f _21337 y) = (term235 A B f _21337 y).
Proof. exact (eq_refl (term235 A B f _21337 y)). Qed.
Lemma lem1197047 {A B : Type'} (y : B) (_21337 : A) (f : A -> B) (x : A) : ((term232 A B f _21337 y) = (term233 A B _21337 f x)) = ((term232 A B f _21337 y) = (term234 A B _21337 f x)).
Proof. exact (MK_COMB (@lem1197046 A B f _21337 y) (@lem1197045 A B _21337 f x)). Qed.
Lemma lem1197048 {A B : Type'} (f : A -> B) (_21337 : A) (y : B) : (term232 A B f _21337 y) = (term216 A B f _21337 y).
Proof. exact (eq_refl (term232 A B f _21337 y)). Qed.
Lemma lem1197049 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1197050 {A B : Type'} (f : A -> B) (_21337 : A) (y : B) : (term235 A B f _21337 y) = (term236 A B f _21337 y).
Proof. exact (MK_COMB (@lem1197049) (@lem1197048 A B f _21337 y)). Qed.
Lemma lem1197051 {A B : Type'} (_21337 : A) (f : A -> B) (x : A) : (term234 A B _21337 f x) = (term234 A B _21337 f x).
Proof. exact (eq_refl (term234 A B _21337 f x)). Qed.
Lemma lem1197052 {A B : Type'} (y : B) (_21337 : A) (f : A -> B) (x : A) : ((term232 A B f _21337 y) = (term234 A B _21337 f x)) = ((term216 A B f _21337 y) = (term234 A B _21337 f x)).
Proof. exact (MK_COMB (@lem1197050 A B f _21337 y) (@lem1197051 A B _21337 f x)). Qed.
Lemma lem1197053 {A B : Type'} (y : B) (_21337 : A) (f : A -> B) (x : A) : ((term232 A B f _21337 y) = (term233 A B _21337 f x)) = ((term216 A B f _21337 y) = (term234 A B _21337 f x)).
Proof. exact (TRANS (@lem1197047 A B y _21337 f x) (@lem1197052 A B y _21337 f x)). Qed.
Lemma lem1197054 {A B : Type'} (_21337 : A) (f : A -> B) (x : A) (y : B) (h1 : (@I (A -> B) f x) = y) : (term216 A B f _21337 y) = (term234 A B _21337 f x).
Proof. exact (EQ_MP (@lem1197053 A B y _21337 f x) (@lem1197044 A B _21337 f x y h1)). Qed.
Lemma lem1197056 {A B : Type'} (f : A -> B) (h : A) : (term237 A B f h) = (term237 A B f h).
Proof. exact (eq_refl (term237 A B f h)). Qed.
Lemma lem1197057 {A B : Type'} (h : A) (f : A -> B) (x : A) (y : B) (h1 : (@I (A -> B) f x) = y) : (term238 A B f h y) = (term239 A B h f x).
Proof. exact (MK_COMB (@lem1197056 A B f h) (@lem1196944 A B f x y h1)). Qed.
Lemma lem1197058 {A B : Type'} (h : A) (f : A -> B) (x : A) : (term239 A B h f x) = ((@I (A -> B) f h) = (@I (A -> B) f x)).
Proof. exact (eq_refl (term239 A B h f x)). Qed.
Lemma lem1197059 {A B : Type'} (f : A -> B) (h : A) (y : B) : (term240 A B f h y) = (term240 A B f h y).
Proof. exact (eq_refl (term240 A B f h y)). Qed.
Lemma lem1197060 {A B : Type'} (y : B) (h : A) (f : A -> B) (x : A) : ((term238 A B f h y) = (term239 A B h f x)) = ((term238 A B f h y) = ((@I (A -> B) f h) = (@I (A -> B) f x))).
Proof. exact (MK_COMB (@lem1197059 A B f h y) (@lem1197058 A B h f x)). Qed.
Lemma lem1197061 {A B : Type'} (f : A -> B) (h : A) (y : B) : (term238 A B f h y) = ((@I (A -> B) f h) = y).
Proof. exact (eq_refl (term238 A B f h y)). Qed.
Lemma lem1197062 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1197063 {A B : Type'} (f : A -> B) (h : A) (y : B) : (term240 A B f h y) = (term241 A B f h y).
Proof. exact (MK_COMB (@lem1197062) (@lem1197061 A B f h y)). Qed.
Lemma lem1197064 {A B : Type'} (h : A) (f : A -> B) (x : A) : ((@I (A -> B) f h) = (@I (A -> B) f x)) = ((@I (A -> B) f h) = (@I (A -> B) f x)).
Proof. exact (eq_refl ((@I (A -> B) f h) = (@I (A -> B) f x))). Qed.
Lemma lem1197065 {A B : Type'} (y : B) (h : A) (f : A -> B) (x : A) : ((term238 A B f h y) = ((@I (A -> B) f h) = (@I (A -> B) f x))) = (((@I (A -> B) f h) = y) = ((@I (A -> B) f h) = (@I (A -> B) f x))).
Proof. exact (MK_COMB (@lem1197063 A B f h y) (@lem1197064 A B h f x)). Qed.
Lemma lem1197066 {A B : Type'} (y : B) (h : A) (f : A -> B) (x : A) : ((term238 A B f h y) = (term239 A B h f x)) = (((@I (A -> B) f h) = y) = ((@I (A -> B) f h) = (@I (A -> B) f x))).
Proof. exact (TRANS (@lem1197060 A B y h f x) (@lem1197065 A B y h f x)). Qed.
Lemma lem1197067 {A B : Type'} (h : A) (f : A -> B) (x : A) (y : B) (h1 : (@I (A -> B) f x) = y) : ((@I (A -> B) f h) = y) = ((@I (A -> B) f h) = (@I (A -> B) f x)).
Proof. exact (EQ_MP (@lem1197066 A B y h f x) (@lem1197057 A B h f x y h1)). Qed.
Lemma lem1197194 {A B : Type'} (_21337 : A) (h : A) (t : list A) (f : A -> B) (x : A) (y : B) (h1 : term133 A B h t f y) (h2 : (@I (A -> B) f x) = y) : term234 A B _21337 f x.
Proof. exact (EQ_MP (@lem1197054 A B _21337 f x y h2) (@lem1196673 A B _21337 h t f y h1)). Qed.
Lemma lem1197405 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem1197406 {B : Type'} (x : B) : x = x.
Proof. exact (@lem1197405 B x). Qed.
Lemma lem1197407 {A B : Type'} (f : A -> B) (h : A) : (@I (A -> B) f h) = (@I (A -> B) f h).
Proof. exact (@lem1197406 B (@I (A -> B) f h)). Qed.
Lemma lem1197408 {A B : Type'} (f : A -> B) (h : A) : term242 A B f h.
Proof. exact (fun h0 : term243 A B f h => @lem1197407 A B f h). Qed.
Lemma lem1197410 (p : Prop) : (term244 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1197411 {A B : Type'} (f : A -> B) (h : A) : (term242 A B f h) = ((@I (A -> B) f h) = (@I (A -> B) f h)).
Proof. exact (@lem1197410 ((@I (A -> B) f h) = (@I (A -> B) f h))). Qed.
Lemma lem1197412 {A B : Type'} (f : A -> B) (h : A) : (@I (A -> B) f h) = (@I (A -> B) f h).
Proof. exact (EQ_MP (@lem1197411 A B f h) (@lem1197408 A B f h)). Qed.
Lemma lem1197415 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1197417 {A B : Type'} (_21324 : A) (f : A -> B) (h : A) : (term234 A B _21324 f h) = (term245 A B _21324 f h).
Proof. exact (@lem1197415 ((@I (A -> B) f _21324) = (@I (A -> B) f h))). Qed.
Lemma lem1197420 {A B : Type'} (_21324 : A) (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term133 A B h t f y) : term245 A B _21324 f h.
Proof. exact (EQ_MP (@lem1197417 A B _21324 f h) (@lem1196930 A B _21324 h t f y h1)). Qed.
Lemma lem1197421 {A B : Type'} (_21324 : A) (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term133 A B h t f y) : term245 A B _21324 f h.
Proof. exact (@lem1197420 A B _21324 h t f y h1). Qed.
Lemma lem1197422 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term133 A B h t f y) : term246 A B f h.
Proof. exact (@lem1197421 A B h h t f y h1). Qed.
Lemma lem1197425 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term133 A B h t f y) : False.
Proof. exact (@lem1197422 A B h t f y h1 (@lem1197412 A B f h)). Qed.
Lemma lem1197426 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term133 A B h t f y) : term247.
Proof. exact (fun h0 : ~ False => @lem1197425 A B h t f y h1). Qed.
Lemma lem1197428 (p : Prop) : (term244 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1197429 : term247 = False.
Proof. exact (@lem1197428 False). Qed.
Lemma lem1197627 {A B : Type'} (h : A) (t : list A) (f : A -> B) (x : A) (y : B) (h1 : term133 A B h t f y) (h2 : (@I (A -> B) f x) = y) : (@I (A -> B) f h) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem1197067 A B h f x y h2) (@lem1196675 A B h t f y h1)). Qed.
Lemma lem1197628 {A B : Type'} (h : A) (t : list A) (f : A -> B) (x : A) (y : B) (h1 : term133 A B h t f y) (h2 : (@I (A -> B) f x) = y) : term248 A B h f x.
Proof. exact (fun h0 : term234 A B h f x => @lem1197627 A B h t f x y h1 h2). Qed.
Lemma lem1197630 (p : Prop) : (term244 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1197631 {A B : Type'} (h : A) (f : A -> B) (x : A) : (term248 A B h f x) = ((@I (A -> B) f h) = (@I (A -> B) f x)).
Proof. exact (@lem1197630 ((@I (A -> B) f h) = (@I (A -> B) f x))). Qed.
Lemma lem1197632 {A B : Type'} (h : A) (t : list A) (f : A -> B) (x : A) (y : B) (h1 : term133 A B h t f y) (h2 : (@I (A -> B) f x) = y) : (@I (A -> B) f h) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem1197631 A B h f x) (@lem1197628 A B h t f x y h1 h2)). Qed.
Lemma lem1197635 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1197637 {A B : Type'} (_21337 : A) (f : A -> B) (x : A) : (term234 A B _21337 f x) = (term245 A B _21337 f x).
Proof. exact (@lem1197635 ((@I (A -> B) f _21337) = (@I (A -> B) f x))). Qed.
Lemma lem1197640 {A B : Type'} (_21337 : A) (h : A) (t : list A) (f : A -> B) (x : A) (y : B) (h1 : term133 A B h t f y) (h2 : (@I (A -> B) f x) = y) : term245 A B _21337 f x.
Proof. exact (EQ_MP (@lem1197637 A B _21337 f x) (@lem1197194 A B _21337 h t f x y h1 h2)). Qed.
Lemma lem1197641 {A B : Type'} (_21337 : A) (h : A) (t : list A) (f : A -> B) (x : A) (y : B) (h1 : term133 A B h t f y) (h2 : (@I (A -> B) f x) = y) : term245 A B _21337 f x.
Proof. exact (@lem1197640 A B _21337 h t f x y h1 h2). Qed.
Lemma lem1197642 {A B : Type'} (h : A) (t : list A) (f : A -> B) (x : A) (y : B) (h1 : term133 A B h t f y) (h2 : (@I (A -> B) f x) = y) : term245 A B h f x.
Proof. exact (@lem1197641 A B h h t f x y h1 h2). Qed.
Lemma lem1197645 {A B : Type'} (h : A) (t : list A) (f : A -> B) (x : A) (y : B) (h1 : term133 A B h t f y) (h2 : (@I (A -> B) f x) = y) : False.
Proof. exact (@lem1197642 A B h t f x y h1 h2 (@lem1197632 A B h t f x y h1 h2)). Qed.
Lemma lem1197646 {A B : Type'} (h : A) (t : list A) (f : A -> B) (x : A) (y : B) (h1 : term133 A B h t f y) (h2 : (@I (A -> B) f x) = y) : term247.
Proof. exact (fun h0 : ~ False => @lem1197645 A B h t f x y h1 h2). Qed.
Lemma lem1197648 (p : Prop) : (term244 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1197649 : term247 = False.
Proof. exact (@lem1197648 False). Qed.
Lemma lem1197652 {A B : Type'} (h : A) (t : list A) (f : A -> B) (x : A) (y : B) (h1 : term133 A B h t f y) (h2 : (@I (A -> B) f x) = y) : False.
Proof. exact (EQ_MP (@lem1197649) (@lem1197646 A B h t f x y h1 h2)). Qed.
Lemma lem1197654 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term133 A B h t f y) : False.
Proof. exact (EQ_MP (@lem1197429) (@lem1197426 A B h t f y h1)). Qed.
Lemma lem1197655 {A B : Type'} (h : A) (t : list A) (f : A -> B) (x : A) (y : B) (h1 : term133 A B h t f y) (h2 : (@I (A -> B) f x) = y) : ((@I (A -> B) f x) = y) = False.
Proof. exact (prop_ext (fun h3 : (@I (A -> B) f x) = y => @lem1197652 A B h t f x y h1 h2) (fun h3 : False => @lem1196679 A B f x y h2)). Qed.
Lemma lem1197656 {A B : Type'} (h : A) (t : list A) (f : A -> B) (x : A) (y : B) (h1 : term133 A B h t f y) (h2 : (@I (A -> B) f x) = y) : False.
Proof. exact (EQ_MP (@lem1197655 A B h t f x y h1 h2) (@lem1196679 A B f x y h2)). Qed.
Lemma lem1197657 {A B : Type'} (h : A) (t : list A) (f : A -> B) (x : A) (y : B) (h1 : term133 A B h t f y) (h2 : (@I (A -> B) f x) = y) : ((@I (A -> B) f x) = y) = False.
Proof. exact (prop_ext (fun h3 : (@I (A -> B) f x) = y => @lem1197656 A B h t f x y h1 h2) (fun h3 : False => @lem1196561 A B f x y h2)). Qed.
Lemma lem1197658 {A B : Type'} (h : A) (t : list A) (f : A -> B) (x : A) (y : B) (h1 : term133 A B h t f y) (h2 : (@I (A -> B) f x) = y) : False.
Proof. exact (EQ_MP (@lem1197657 A B h t f x y h1 h2) (@lem1196561 A B f x y h2)). Qed.
Lemma lem1197659 {A B : Type'} (h : A) (t : list A) (f : A -> B) (x : A) (y : B) (h1 : term133 A B h t f y) (h2 : (@I (A -> B) f x) = y) : ((@I (A -> B) f x) = y) = False.
Proof. exact (prop_ext (fun h3 : (@I (A -> B) f x) = y => @lem1197658 A B h t f x y h1 h2) (fun h3 : False => @lem1196561 A B f x y h2)). Qed.
Lemma lem1197660 {A B : Type'} (h : A) (t : list A) (f : A -> B) (x : A) (y : B) (h1 : term133 A B h t f y) (h2 : (@I (A -> B) f x) = y) : False.
Proof. exact (EQ_MP (@lem1197659 A B h t f x y h1 h2) (@lem1196561 A B f x y h2)). Qed.
Lemma lem1197661 {A B : Type'} (h : A) (t : list A) (f : A -> B) (x : A) (y : B) (h1 : term133 A B h t f y) (h2 : term198 A B t f x y) : False.
Proof. exact (or_elim (@lem1196391 A B t f x y h2) (fun h0 : term227 A B f t y => @lem1197654 A B h t f y h1) (fun h0 : (@I (A -> B) f x) = y => @lem1197660 A B h t f x y h1 h0)). Qed.
Lemma lem1197662 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term133 A B h t f y) (h2 : term60 A B t f y) : False.
Proof. exact (ex_elim (@lem1195813 A B t f y h2) (fun x : A => fun h0 : term200 A B t f y x => @lem1197661 A B h t f x y h1 h0)). Qed.
Lemma lem1197663 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term133 A B h t f y) (h2 : term60 A B t f y) : term140 B.
Proof. exact (fun h0 : term135 B => @lem1197662 A B h t f y h1 h2). Qed.
Lemma lem1197664 {B : Type'} : (term140 B) = (term141 B).
Proof. exact (@lem69 (term135 B)). Qed.
Lemma lem1197665 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term133 A B h t f y) (h2 : term60 A B t f y) : term141 B.
Proof. exact (EQ_MP (@lem1197664 B) (@lem1197663 A B h t f y h1 h2)). Qed.
Lemma lem1197666 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term133 A B h t f y) (h2 : term60 A B t f y) : term144 A B.
Proof. exact (fun h0 : term134 A B => @lem1197665 A B h t f y h1 h2). Qed.
Lemma lem1197667 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term133 A B h t f y) (h2 : term60 A B t f y) : term147 A B.
Proof. exact (fun h0 : term135 A => @lem1197666 A B h t f y h1 h2). Qed.
Lemma lem1197668 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term60 A B t f y) : term150 A B h t f y.
Proof. exact (fun h0 : term133 A B h t f y => @lem1197667 A B h t f y h0 h1). Qed.
Lemma lem1197669 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) : term151 A B h t f y.
Proof. exact (fun h0 : term60 A B t f y => @lem1197668 A B h t f y h0). Qed.
Lemma lem1197674 {A B : Type'} (t : list A) (f : A -> B) (y : B) : term155 A B t f y.
Proof. exact (fun h : A => @lem1197669 A B h t f y). Qed.
Lemma lem1197679 {A B : Type'} (f : A -> B) (y : B) : term159 A B f y.
Proof. exact (fun t : list A => @lem1197674 A B t f y). Qed.
Lemma lem1197684 {A B : Type'} (y : B) : term163 A B y.
Proof. exact (fun f : A -> B => @lem1197679 A B f y). Qed.
Lemma lem1197689 {A B : Type'} : term167 A B.
Proof. exact (fun y : B => @lem1197684 A B y). Qed.
Lemma lem1197690 {A B : Type'} : term166 A B.
Proof. exact (EQ_MP (@lem1195770 A B) (@lem1197689 A B)). Qed.
Lemma lem1197691 {A B : Type'} (y : B) : term249 A B y.
Proof. exact (@lem1197690 A B y). Qed.
Lemma lem1197692 {A B : Type'} (y : B) : (term249 A B y) = (term162 A B y).
Proof. exact (eq_refl (term249 A B y)). Qed.
Lemma lem1197693 {A B : Type'} (y : B) : term162 A B y.
Proof. exact (EQ_MP (@lem1197692 A B y) (@lem1197691 A B y)). Qed.
Lemma lem1197694 {A B : Type'} (y : B) (f : A -> B) : term250 A B y f.
Proof. exact (@lem1197693 A B y f). Qed.
Lemma lem1197695 {A B : Type'} (f : A -> B) (y : B) : (term250 A B y f) = (term158 A B f y).
Proof. exact (eq_refl (term250 A B y f)). Qed.
Lemma lem1197696 {A B : Type'} (f : A -> B) (y : B) : term158 A B f y.
Proof. exact (EQ_MP (@lem1197695 A B f y) (@lem1197694 A B y f)). Qed.
Lemma lem1197697 {A B : Type'} (f : A -> B) (y : B) (t : list A) : term251 A B f y t.
Proof. exact (@lem1197696 A B f y t). Qed.
Lemma lem1197698 {A B : Type'} (t : list A) (f : A -> B) (y : B) : (term251 A B f y t) = (term154 A B t f y).
Proof. exact (eq_refl (term251 A B f y t)). Qed.
Lemma lem1197699 {A B : Type'} (t : list A) (f : A -> B) (y : B) : term154 A B t f y.
Proof. exact (EQ_MP (@lem1197698 A B t f y) (@lem1197697 A B f y t)). Qed.
Lemma lem1197700 {A B : Type'} (t : list A) (f : A -> B) (y : B) (h : A) : term252 A B t f y h.
Proof. exact (@lem1197699 A B t f y h). Qed.
Lemma lem1197701 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) : (term252 A B t f y h) = (term136 A B h t f y).
Proof. exact (eq_refl (term252 A B t f y h)). Qed.
Lemma lem1197702 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) : term136 A B h t f y.
Proof. exact (EQ_MP (@lem1197701 A B h t f y) (@lem1197700 A B t f y h)). Qed.
Lemma lem1197704 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) : term136 A B h t f y.
Proof. exact (@lem1195396 A B h t f y (@lem1197702 A B h t f y)). Qed.
Lemma lem1197705 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term60 A B t f y) : term149 A B h t f y.
Proof. exact (@lem1197704 A B h t f y (@lem1195259 A B t f y h1)). Qed.
Lemma lem1197706 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term133 A B h t f y) (h2 : term60 A B t f y) : term146 A B.
Proof. exact (@lem1197705 A B h t f y h2 (@lem1195371 A B h t f y h1)). Qed.
Lemma lem1197707 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term133 A B h t f y) (h2 : term60 A B t f y) : term143 A B.
Proof. exact (@lem1197706 A B h t f y h1 h2 (@lem1195373 A)). Qed.
Lemma lem1197708 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term133 A B h t f y) (h2 : term60 A B t f y) : term140 B.
Proof. exact (@lem1197707 A B h t f y h1 h2 (@lem1195372 A B)). Qed.
Lemma lem1197709 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term133 A B h t f y) (h2 : term60 A B t f y) : False.
Proof. exact (@lem1197708 A B h t f y h1 h2 (@lem1195375 B)). Qed.
Lemma lem1197710 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term133 A B h t f y) (h2 : term60 A B t f y) : (term133 A B h t f y) = False.
Proof. exact (prop_ext (fun h3 : term133 A B h t f y => @lem1197709 A B h t f y h1 h2) (fun h3 : False => @lem1195371 A B h t f y h1)). Qed.
Lemma lem1197711 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term133 A B h t f y) (h2 : term60 A B t f y) : False.
Proof. exact (EQ_MP (@lem1197710 A B h t f y h1 h2) (@lem1195371 A B h t f y h1)). Qed.
Lemma lem1197712 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term60 A B t f y) : term132 A B h t f y.
Proof. exact (fun h0 : term133 A B h t f y => @lem1197711 A B h t f y h0 h1). Qed.
Lemma lem1197713 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term60 A B t f y) : term101 A B h t f y.
Proof. exact (EQ_MP (@lem1195370 A B h t f y) (@lem1197712 A B h t f y h1)). Qed.
Lemma lem1197715 (p : Prop) : p = (term131 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1197716 {A B : Type'} (f : A -> B) : (term125 A B f) = (term253 A B f).
Proof. exact (@lem1197715 (term125 A B f)). Qed.
Lemma lem1197717 {A B : Type'} (f : A -> B) : (term253 A B f) = (term125 A B f).
Proof. exact (SYM (@lem1197716 A B f)). Qed.
Lemma lem1197718 {A B : Type'} (f : A -> B) (h1 : term254 A B f) : term254 A B f.
Proof. exact (h1). Qed.
Lemma lem1197719 {A B : Type'} : term134 A B.
Proof. exact (@lem1097800 A B). Qed.
Lemma lem1197721 {B : Type'} : term135 B.
Proof. exact (@lem1097800 B B). Qed.
Lemma lem1197727 {A B : Type'} (f : A -> B) (h1 : term255 A B f) : term255 A B f.
Proof. exact (h1). Qed.
Lemma lem1197728 {A B : Type'} (f : A -> B) : term256 A B f.
Proof. exact (fun h0 : term255 A B f => @lem1197727 A B f h0). Qed.
Lemma lem1197729 {A B : Type'} (f : A -> B) (h1 : term256 A B f) : term256 A B f.
Proof. exact (h1). Qed.
Lemma lem1197730 {A B : Type'} (f : A -> B) (h1 : term255 A B f) : term255 A B f.
Proof. exact (h1). Qed.
Lemma lem1197731 {A B : Type'} (f : A -> B) (h1 : term255 A B f) (h2 : term256 A B f) : term255 A B f.
Proof. exact (@lem1197729 A B f h2 (@lem1197730 A B f h1)). Qed.
Lemma lem1197732 {A B : Type'} (f : A -> B) (h1 : term255 A B f) : term257 A B f.
Proof. exact (fun h0 : term256 A B f => @lem1197731 A B f h1 h0). Qed.
Lemma lem1197733 {A B : Type'} (f : A -> B) (h1 : term256 A B f) : term256 A B f.
Proof. exact (h1). Qed.
Lemma lem1197734 {A B : Type'} (f : A -> B) (h1 : term255 A B f) (h2 : term256 A B f) : term255 A B f.
Proof. exact (@lem1197732 A B f h1 (@lem1197733 A B f h2)). Qed.
Lemma lem1197735 {A B : Type'} (f : A -> B) (h1 : term256 A B f) : term256 A B f.
Proof. exact (fun h0 : term255 A B f => @lem1197734 A B f h0 h1). Qed.
Lemma lem1197736 {A B : Type'} (f : A -> B) : term258 A B f.
Proof. exact (fun h0 : term256 A B f => @lem1197735 A B f h0). Qed.
Lemma lem1197739 {A B : Type'} (f : A -> B) : term256 A B f.
Proof. exact (@lem1197736 A B f (@lem1197728 A B f)). Qed.
Lemma lem1197740 {A B : Type'} (f : A -> B) : term256 A B f.
Proof. exact (@lem1197739 A B f). Qed.
Lemma lem1197802 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1197803 {B : Type'} : (term140 B) = (term141 B).
Proof. exact (@lem1197802 (term135 B)). Qed.
Lemma lem1197822 {A B : Type'} : (term142 A B) = (term142 A B).
Proof. exact (eq_refl (term142 A B)). Qed.
Lemma lem1197823 {A B : Type'} : (term143 A B) = (term144 A B).
Proof. exact (MK_COMB (@lem1197822 A B) (@lem1197803 B)). Qed.
Lemma lem1197826 {A B : Type'} (f : A -> B) : (term259 A B f) = (term259 A B f).
Proof. exact (eq_refl (term259 A B f)). Qed.
Lemma lem1197827 {A B : Type'} (f : A -> B) : (term260 A B f) = (term261 A B f).
Proof. exact (MK_COMB (@lem1197826 A B f) (@lem1197823 A B)). Qed.
Lemma lem1197830 {A B : Type'} (f : A -> B) : (term262 A B f) = (term262 A B f).
Proof. exact (eq_refl (term262 A B f)). Qed.
Lemma lem1197831 {A B : Type'} (f : A -> B) : (term255 A B f) = (term263 A B f).
Proof. exact (MK_COMB (@lem1197830 A B f) (@lem1197827 A B f)). Qed.
Lemma lem1197834 {A B : Type'} : (term264 A B) = (term265 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem1197831 A B f)). Qed.
Lemma lem1197835 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem1197844 {A B : Type'} : (term266 A B) = (term267 A B).
Proof. exact (MK_COMB (@lem1197835 A B) (@lem1197834 A B)). Qed.
Lemma lem1197845 {B : Type'} (h : B) (f : B -> B) (t : list B) : ((term168 B f h t) = (term169 B h f t)) = ((term168 B f h t) = (term169 B h f t)).
Proof. exact (eq_refl ((term168 B f h t) = (term169 B h f t))). Qed.
Lemma lem1197846 {B : Type'} (h : B) (f : B -> B) : (term170 B h f) = (term170 B h f).
Proof. exact (fun_ext (fun t : list B => @lem1197845 B h f t)). Qed.
Lemma lem1197847 {B : Type'} : (@all (list B)) = (@all (list B)).
Proof. exact (eq_refl (@all (list B))). Qed.
Lemma lem1197848 {B : Type'} (h : B) (f : B -> B) : (term171 B h f) = (term171 B h f).
Proof. exact (MK_COMB (@lem1197847 B) (@lem1197846 B h f)). Qed.
Lemma lem1197849 {B : Type'} (f : B -> B) : (term172 B f) = (term172 B f).
Proof. exact (fun_ext (fun h : B => @lem1197848 B h f)). Qed.
Lemma lem1197850 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1197851 {B : Type'} (f : B -> B) : (term173 B f) = (term173 B f).
Proof. exact (MK_COMB (@lem1197850 B) (@lem1197849 B f)). Qed.
Lemma lem1197852 {B : Type'} : (term174 B) = (term174 B).
Proof. exact (fun_ext (fun f : B -> B => @lem1197851 B f)). Qed.
Lemma lem1197853 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem1197854 {B : Type'} : (term175 B) = (term175 B).
Proof. exact (MK_COMB (@lem1197853 B) (@lem1197852 B)). Qed.
Lemma lem1197855 {B : Type'} (f : B -> B) : ((@List.map B B f (@nil B)) = (@nil B)) = ((@List.map B B f (@nil B)) = (@nil B)).
Proof. exact (eq_refl ((@List.map B B f (@nil B)) = (@nil B))). Qed.
Lemma lem1197856 {B : Type'} : (term176 B) = (term176 B).
Proof. exact (fun_ext (fun f : B -> B => @lem1197855 B f)). Qed.
Lemma lem1197857 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem1197858 {B : Type'} : (term177 B) = (term177 B).
Proof. exact (MK_COMB (@lem1197857 B) (@lem1197856 B)). Qed.
Lemma lem1197859 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1197860 {B : Type'} : (term178 B) = (term178 B).
Proof. exact (MK_COMB (@lem1197859) (@lem1197858 B)). Qed.
Lemma lem1197861 {B : Type'} : (term135 B) = (term135 B).
Proof. exact (MK_COMB (@lem1197860 B) (@lem1197854 B)). Qed.
Lemma lem1197862 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1197863 {B : Type'} : (term141 B) = (term141 B).
Proof. exact (MK_COMB (@lem1197862) (@lem1197861 B)). Qed.
Lemma lem1197864 {A B : Type'} (h : A) (f : A -> B) (t : list A) : ((term30 A B f h t) = (term31 A B h f t)) = ((term30 A B f h t) = (term31 A B h f t)).
Proof. exact (eq_refl ((term30 A B f h t) = (term31 A B h f t))). Qed.
Lemma lem1197865 {A B : Type'} (h : A) (f : A -> B) : (term179 A B h f) = (term179 A B h f).
Proof. exact (fun_ext (fun t : list A => @lem1197864 A B h f t)). Qed.
Lemma lem1197866 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1197867 {A B : Type'} (h : A) (f : A -> B) : (term28 A B h f) = (term28 A B h f).
Proof. exact (MK_COMB (@lem1197866 A) (@lem1197865 A B h f)). Qed.
Lemma lem1197868 {A B : Type'} (f : A -> B) : (term180 A B f) = (term180 A B f).
Proof. exact (fun_ext (fun h : A => @lem1197867 A B h f)). Qed.
Lemma lem1197869 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1197870 {A B : Type'} (f : A -> B) : (term26 A B f) = (term26 A B f).
Proof. exact (MK_COMB (@lem1197869 A) (@lem1197868 A B f)). Qed.
Lemma lem1197871 {A B : Type'} : (term181 A B) = (term181 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem1197870 A B f)). Qed.
Lemma lem1197872 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem1197873 {A B : Type'} : (term24 A B) = (term24 A B).
Proof. exact (MK_COMB (@lem1197872 A B) (@lem1197871 A B)). Qed.
Lemma lem1197874 {A B : Type'} (f : A -> B) : ((@List.map A B f (@nil A)) = (@nil B)) = ((@List.map A B f (@nil A)) = (@nil B)).
Proof. exact (eq_refl ((@List.map A B f (@nil A)) = (@nil B))). Qed.
Lemma lem1197875 {A B : Type'} : (term182 A B) = (term182 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem1197874 A B f)). Qed.
Lemma lem1197876 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem1197877 {A B : Type'} : (term32 A B) = (term32 A B).
Proof. exact (MK_COMB (@lem1197876 A B) (@lem1197875 A B)). Qed.
Lemma lem1197878 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1197879 {A B : Type'} : (term183 A B) = (term183 A B).
Proof. exact (MK_COMB (@lem1197878) (@lem1197877 A B)). Qed.
Lemma lem1197880 {A B : Type'} : (term134 A B) = (term134 A B).
Proof. exact (MK_COMB (@lem1197879 A B) (@lem1197873 A B)). Qed.
Lemma lem1197881 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1197882 {A B : Type'} : (term142 A B) = (term142 A B).
Proof. exact (MK_COMB (@lem1197881) (@lem1197880 A B)). Qed.
Lemma lem1197883 {A B : Type'} : (term144 A B) = (term144 A B).
Proof. exact (MK_COMB (@lem1197882 A B) (@lem1197863 B)). Qed.
Lemma lem1197884 {A B : Type'} (f : A -> B) (l : list A) (a0 : B) (a1 : list B) : ((@List.map A B f l) = (@cons B a0 a1)) = ((@List.map A B f l) = (@cons B a0 a1)).
Proof. exact (eq_refl ((@List.map A B f l) = (@cons B a0 a1))). Qed.
Lemma lem1197885 {A B : Type'} (f : A -> B) (a0 : B) (a1 : list B) : (term268 A B f a0 a1) = (term268 A B f a0 a1).
Proof. exact (fun_ext (fun l : list A => @lem1197884 A B f l a0 a1)). Qed.
Lemma lem1197886 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1197887 {A B : Type'} (f : A -> B) (a0 : B) (a1 : list B) : (term113 A B f a0 a1) = (term113 A B f a0 a1).
Proof. exact (MK_COMB (@lem1197886 A) (@lem1197885 A B f a0 a1)). Qed.
Lemma lem1197888 {A B : Type'} (f : A -> B) (l : list A) (a1 : list B) : ((@List.map A B f l) = a1) = ((@List.map A B f l) = a1).
Proof. exact (eq_refl ((@List.map A B f l) = a1)). Qed.
Lemma lem1197889 {A B : Type'} (f : A -> B) (a1 : list B) : (term269 A B f a1) = (term269 A B f a1).
Proof. exact (fun_ext (fun l : list A => @lem1197888 A B f l a1)). Qed.
Lemma lem1197890 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1197891 {A B : Type'} (f : A -> B) (a1 : list B) : (term109 A B f a1) = (term109 A B f a1).
Proof. exact (MK_COMB (@lem1197890 A) (@lem1197889 A B f a1)). Qed.
Lemma lem1197892 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1197893 {A B : Type'} (f : A -> B) (a1 : list B) : (term111 A B f a1) = (term111 A B f a1).
Proof. exact (MK_COMB (@lem1197892) (@lem1197891 A B f a1)). Qed.
Lemma lem1197894 {A B : Type'} (f : A -> B) (a0 : B) (a1 : list B) : (term115 A B f a0 a1) = (term115 A B f a0 a1).
Proof. exact (MK_COMB (@lem1197893 A B f a1) (@lem1197887 A B f a0 a1)). Qed.
Lemma lem1197895 {A B : Type'} (f : A -> B) (a0 : B) : (term117 A B f a0) = (term117 A B f a0).
Proof. exact (fun_ext (fun a1 : list B => @lem1197894 A B f a0 a1)). Qed.
Lemma lem1197896 {B : Type'} : (@all (list B)) = (@all (list B)).
Proof. exact (eq_refl (@all (list B))). Qed.
Lemma lem1197897 {A B : Type'} (f : A -> B) (a0 : B) : (term119 A B f a0) = (term119 A B f a0).
Proof. exact (MK_COMB (@lem1197896 B) (@lem1197895 A B f a0)). Qed.
Lemma lem1197898 {A B : Type'} (f : A -> B) : (term121 A B f) = (term121 A B f).
Proof. exact (fun_ext (fun a0 : B => @lem1197897 A B f a0)). Qed.
Lemma lem1197899 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1197900 {A B : Type'} (f : A -> B) : (term123 A B f) = (term123 A B f).
Proof. exact (MK_COMB (@lem1197899 B) (@lem1197898 A B f)). Qed.
Lemma lem1197901 {A B : Type'} (f : A -> B) (l : list A) : ((@List.map A B f l) = (@nil B)) = ((@List.map A B f l) = (@nil B)).
Proof. exact (eq_refl ((@List.map A B f l) = (@nil B))). Qed.
Lemma lem1197902 {A B : Type'} (f : A -> B) : (term270 A B f) = (term270 A B f).
Proof. exact (fun_ext (fun l : list A => @lem1197901 A B f l)). Qed.
Lemma lem1197903 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1197904 {A B : Type'} (f : A -> B) : (term105 A B f) = (term105 A B f).
Proof. exact (MK_COMB (@lem1197903 A) (@lem1197902 A B f)). Qed.
Lemma lem1197905 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1197906 {A B : Type'} (f : A -> B) : (term107 A B f) = (term107 A B f).
Proof. exact (MK_COMB (@lem1197905) (@lem1197904 A B f)). Qed.
Lemma lem1197907 {A B : Type'} (f : A -> B) : (term125 A B f) = (term125 A B f).
Proof. exact (MK_COMB (@lem1197906 A B f) (@lem1197900 A B f)). Qed.
Lemma lem1197908 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1197909 {A B : Type'} (f : A -> B) : (term254 A B f) = (term254 A B f).
Proof. exact (MK_COMB (@lem1197908) (@lem1197907 A B f)). Qed.
Lemma lem1197910 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1197911 {A B : Type'} (f : A -> B) : (term259 A B f) = (term259 A B f).
Proof. exact (MK_COMB (@lem1197910) (@lem1197909 A B f)). Qed.
Lemma lem1197912 {A B : Type'} (f : A -> B) : (term261 A B f) = (term261 A B f).
Proof. exact (MK_COMB (@lem1197911 A B f) (@lem1197883 A B)). Qed.
Lemma lem1197913 {A B : Type'} (f : A -> B) (x : A) (y : B) : ((f x) = y) = ((f x) = y).
Proof. exact (eq_refl ((f x) = y)). Qed.
Lemma lem1197914 {A B : Type'} (f : A -> B) (y : B) : (term184 A B f y) = (term184 A B f y).
Proof. exact (fun_ext (fun x : A => @lem1197913 A B f x y)). Qed.
Lemma lem1197915 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1197916 {A B : Type'} (f : A -> B) (y : B) : (term48 A B f y) = (term48 A B f y).
Proof. exact (MK_COMB (@lem1197915 A) (@lem1197914 A B f y)). Qed.
Lemma lem1197917 {A B : Type'} (f : A -> B) : (term271 A B f) = (term271 A B f).
Proof. exact (fun_ext (fun y : B => @lem1197916 A B f y)). Qed.
Lemma lem1197918 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1197919 {A B : Type'} (f : A -> B) : (term40 A B f) = (term40 A B f).
Proof. exact (MK_COMB (@lem1197918 B) (@lem1197917 A B f)). Qed.
Lemma lem1197920 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1197921 {A B : Type'} (f : A -> B) : (term262 A B f) = (term262 A B f).
Proof. exact (MK_COMB (@lem1197920) (@lem1197919 A B f)). Qed.
Lemma lem1197922 {A B : Type'} (f : A -> B) : (term263 A B f) = (term263 A B f).
Proof. exact (MK_COMB (@lem1197921 A B f) (@lem1197912 A B f)). Qed.
Lemma lem1197923 {A B : Type'} : (term265 A B) = (term265 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem1197922 A B f)). Qed.
Lemma lem1197924 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem1197925 {A B : Type'} : (term267 A B) = (term267 A B).
Proof. exact (MK_COMB (@lem1197924 A B) (@lem1197923 A B)). Qed.
Lemma lem1198038 {A B : Type'} : (term266 A B) = (term267 A B).
Proof. exact (TRANS (@lem1197844 A B) (@lem1197925 A B)). Qed.
Lemma lem1198039 {A B : Type'} : (term267 A B) = (term266 A B).
Proof. exact (SYM (@lem1198038 A B)). Qed.
Lemma lem1198040 {A B : Type'} (f : A -> B) (h1 : term40 A B f) : term40 A B f.
Proof. exact (h1). Qed.
Lemma lem1198041 {A B : Type'} (f : A -> B) (h1 : term254 A B f) : term254 A B f.
Proof. exact (h1). Qed.
Lemma lem1198042 {A B : Type'} (h1 : term134 A B) : term134 A B.
Proof. exact (h1). Qed.
Lemma lem1198044 {A B : Type'} (f : A -> B) (x : A) (y : B) : ((f x) = y) = ((f x) = y).
Proof. exact (eq_refl ((f x) = y)). Qed.
Lemma lem1198045 {A B : Type'} (f : A -> B) (y : B) : (term184 A B f y) = (term184 A B f y).
Proof. exact (fun_ext (fun x : A => @lem1198044 A B f x y)). Qed.
Lemma lem1198046 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1198047 {A B : Type'} (f : A -> B) (y : B) : (term48 A B f y) = (term48 A B f y).
Proof. exact (MK_COMB (@lem1198046 A) (@lem1198045 A B f y)). Qed.
Lemma lem1198048 {A B : Type'} (f : A -> B) : (term271 A B f) = (term271 A B f).
Proof. exact (fun_ext (fun y : B => @lem1198047 A B f y)). Qed.
Lemma lem1198049 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1198050 {A B : Type'} (f : A -> B) : (term40 A B f) = (term40 A B f).
Proof. exact (MK_COMB (@lem1198049 B) (@lem1198048 A B f)). Qed.
Lemma lem1198061 {A B : Type'} (P : type1413 A B) : (term272 A B P) = (term273 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem1198062 {A B : Type'} (P : type1470 A B) : (term274 A B P) = (term275 A B P).
Proof. exact (@lem1198061 B A P). Qed.
Lemma lem1198063 {A B : Type'} (f : A -> B) : (term276 A B f) = (term277 A B f).
Proof. exact (@lem1198062 A B (term278 A B f)). Qed.
Lemma lem1198064 {A B : Type'} (f : A -> B) (y : B) : (term279 A B f y) = (term184 A B f y).
Proof. exact (eq_refl (term279 A B f y)). Qed.
Lemma lem1198065 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1198066 {A B : Type'} (f : A -> B) (y : B) (x : A) : (term280 A B f y x) = (term192 A B f y x).
Proof. exact (MK_COMB (@lem1198064 A B f y) (@lem1198065 A x)). Qed.
Lemma lem1198067 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term192 A B f y x) = ((f x) = y).
Proof. exact (eq_refl (term192 A B f y x)). Qed.
Lemma lem1198068 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term280 A B f y x) = ((f x) = y).
Proof. exact (TRANS (@lem1198066 A B f y x) (@lem1198067 A B f x y)). Qed.
Lemma lem1198069 {A B : Type'} (f : A -> B) (y : B) : (term281 A B f y) = (term184 A B f y).
Proof. exact (fun_ext (fun x : A => @lem1198068 A B f x y)). Qed.
Lemma lem1198070 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1198071 {A B : Type'} (f : A -> B) (y : B) : (term282 A B f y) = (term48 A B f y).
Proof. exact (MK_COMB (@lem1198070 A) (@lem1198069 A B f y)). Qed.
Lemma lem1198072 {A B : Type'} (f : A -> B) : (term283 A B f) = (term271 A B f).
Proof. exact (fun_ext (fun y : B => @lem1198071 A B f y)). Qed.
Lemma lem1198073 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1198074 {A B : Type'} (f : A -> B) : (term276 A B f) = (term40 A B f).
Proof. exact (MK_COMB (@lem1198073 B) (@lem1198072 A B f)). Qed.
Lemma lem1198075 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1198076 {A B : Type'} (f : A -> B) : (term284 A B f) = (term285 A B f).
Proof. exact (MK_COMB (@lem1198075) (@lem1198074 A B f)). Qed.
Lemma lem1198077 {A B : Type'} (f : A -> B) (y : B) : (term279 A B f y) = (term184 A B f y).
Proof. exact (eq_refl (term279 A B f y)). Qed.
Lemma lem1198078 {A B : Type'} (x : B -> A) (y : B) : (x y) = (x y).
Proof. exact (eq_refl (x y)). Qed.
Lemma lem1198079 {A B : Type'} (f : A -> B) (x : B -> A) (y : B) : (term286 A B f x y) = (term287 A B f x y).
Proof. exact (MK_COMB (@lem1198077 A B f y) (@lem1198078 A B x y)). Qed.
Lemma lem1198080 {A B : Type'} (f : A -> B) (x : B -> A) (y : B) : (term287 A B f x y) = ((term288 A B f x y) = y).
Proof. exact (eq_refl (term287 A B f x y)). Qed.
Lemma lem1198081 {A B : Type'} (f : A -> B) (x : B -> A) (y : B) : (term286 A B f x y) = ((term288 A B f x y) = y).
Proof. exact (TRANS (@lem1198079 A B f x y) (@lem1198080 A B f x y)). Qed.
Lemma lem1198082 {A B : Type'} (f : A -> B) (x : B -> A) : (term289 A B f x) = (term290 A B f x).
Proof. exact (fun_ext (fun y : B => @lem1198081 A B f x y)). Qed.
Lemma lem1198083 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1198084 {A B : Type'} (f : A -> B) (x : B -> A) : (term291 A B f x) = (term292 A B f x).
Proof. exact (MK_COMB (@lem1198083 B) (@lem1198082 A B f x)). Qed.
Lemma lem1198085 {A B : Type'} (f : A -> B) : (term293 A B f) = (term294 A B f).
Proof. exact (fun_ext (fun x : B -> A => @lem1198084 A B f x)). Qed.
Lemma lem1198086 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem1198087 {A B : Type'} (f : A -> B) : (term277 A B f) = (term295 A B f).
Proof. exact (MK_COMB (@lem1198086 A B) (@lem1198085 A B f)). Qed.
Lemma lem1198088 {A B : Type'} (f : A -> B) : ((term276 A B f) = (term277 A B f)) = ((term40 A B f) = (term295 A B f)).
Proof. exact (MK_COMB (@lem1198076 A B f) (@lem1198087 A B f)). Qed.
Lemma lem1198090 {A B : Type'} (f : A -> B) : (term40 A B f) = (term295 A B f).
Proof. exact (EQ_MP (@lem1198088 A B f) (@lem1198063 A B f)). Qed.
Lemma lem1198091 {A B : Type'} (f : A -> B) : (term40 A B f) = (term295 A B f).
Proof. exact (TRANS (@lem1198050 A B f) (@lem1198090 A B f)). Qed.
Lemma lem1198092 {A B : Type'} (f : A -> B) (h1 : term40 A B f) : term295 A B f.
Proof. exact (EQ_MP (@lem1198091 A B f) (@lem1198040 A B f h1)). Qed.
Lemma lem1198094 {A : Type'} (P : type1143 A) : (term296 A P) = (term297 A P).
Proof. exact (@lem18394 (list A) P). Qed.
Lemma lem1198095 {A B : Type'} (f : A -> B) : (term298 A B f) = (term299 A B f).
Proof. exact (@lem1198094 A (term270 A B f)). Qed.
Lemma lem1198096 {A B : Type'} (f : A -> B) (l : list A) : (term300 A B f l) = ((@List.map A B f l) = (@nil B)).
Proof. exact (eq_refl (term300 A B f l)). Qed.
Lemma lem1198097 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1198099 {A B : Type'} (f : A -> B) (l : list A) : (term301 A B f l) = (term302 A B f l).
Proof. exact (MK_COMB (@lem1198097) (@lem1198096 A B f l)). Qed.
Lemma lem1198100 {A B : Type'} (f : A -> B) : (term303 A B f) = (term304 A B f).
Proof. exact (fun_ext (fun l : list A => @lem1198099 A B f l)). Qed.
Lemma lem1198101 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1198102 {A B : Type'} (f : A -> B) : (term299 A B f) = (term305 A B f).
Proof. exact (MK_COMB (@lem1198101 A) (@lem1198100 A B f)). Qed.
Lemma lem1198103 {A B : Type'} (f : A -> B) : (term298 A B f) = (term305 A B f).
Proof. exact (TRANS (@lem1198095 A B f) (@lem1198102 A B f)). Qed.
Lemma lem1198104 {A B : Type'} (f : A -> B) (l : list A) (a1 : list B) : ((@List.map A B f l) = a1) = ((@List.map A B f l) = a1).
Proof. exact (eq_refl ((@List.map A B f l) = a1)). Qed.
Lemma lem1198105 {A B : Type'} (f : A -> B) (a1 : list B) : (term269 A B f a1) = (term269 A B f a1).
Proof. exact (fun_ext (fun l : list A => @lem1198104 A B f l a1)). Qed.
Lemma lem1198106 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1198107 {A B : Type'} (f : A -> B) (a1 : list B) : (term109 A B f a1) = (term109 A B f a1).
Proof. exact (MK_COMB (@lem1198106 A) (@lem1198105 A B f a1)). Qed.
Lemma lem1198109 {A : Type'} (P : type1143 A) : (term296 A P) = (term297 A P).
Proof. exact (@lem18394 (list A) P). Qed.
Lemma lem1198110 {A B : Type'} (f : A -> B) (a0 : B) (a1 : list B) : (term306 A B f a0 a1) = (term307 A B f a0 a1).
Proof. exact (@lem1198109 A (term268 A B f a0 a1)). Qed.
Lemma lem1198111 {A B : Type'} (f : A -> B) (l : list A) (a0 : B) (a1 : list B) : (term308 A B f a0 a1 l) = ((@List.map A B f l) = (@cons B a0 a1)).
Proof. exact (eq_refl (term308 A B f a0 a1 l)). Qed.
Lemma lem1198112 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1198114 {A B : Type'} (f : A -> B) (l : list A) (a0 : B) (a1 : list B) : (term309 A B f a0 a1 l) = (term310 A B f l a0 a1).
Proof. exact (MK_COMB (@lem1198112) (@lem1198111 A B f l a0 a1)). Qed.
Lemma lem1198115 {A B : Type'} (f : A -> B) (a0 : B) (a1 : list B) : (term311 A B f a0 a1) = (term312 A B f a0 a1).
Proof. exact (fun_ext (fun l : list A => @lem1198114 A B f l a0 a1)). Qed.
Lemma lem1198116 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1198117 {A B : Type'} (f : A -> B) (a0 : B) (a1 : list B) : (term307 A B f a0 a1) = (term313 A B f a0 a1).
Proof. exact (MK_COMB (@lem1198116 A) (@lem1198115 A B f a0 a1)). Qed.
Lemma lem1198118 {A B : Type'} (f : A -> B) (a0 : B) (a1 : list B) : (term306 A B f a0 a1) = (term313 A B f a0 a1).
Proof. exact (TRANS (@lem1198110 A B f a0 a1) (@lem1198117 A B f a0 a1)). Qed.
Lemma lem1198119 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1198120 {A B : Type'} (f : A -> B) (a1 : list B) : (term314 A B f a1) = (term314 A B f a1).
Proof. exact (MK_COMB (@lem1198119) (@lem1198107 A B f a1)). Qed.
Lemma lem1198121 {A B : Type'} (f : A -> B) (a0 : B) (a1 : list B) : (term315 A B f a0 a1) = (term316 A B f a0 a1).
Proof. exact (MK_COMB (@lem1198120 A B f a1) (@lem1198118 A B f a0 a1)). Qed.
Lemma lem1198122 {A B : Type'} (f : A -> B) (a0 : B) (a1 : list B) : (term317 A B f a0 a1) = (term315 A B f a0 a1).
Proof. exact (@lem17362 (term109 A B f a1) (term113 A B f a0 a1)). Qed.
Lemma lem1198123 {A B : Type'} (f : A -> B) (a0 : B) (a1 : list B) : (term317 A B f a0 a1) = (term316 A B f a0 a1).
Proof. exact (TRANS (@lem1198122 A B f a0 a1) (@lem1198121 A B f a0 a1)). Qed.
Lemma lem1198124 {B : Type'} (P : type1143 B) : (term318 B P) = (term319 B P).
Proof. exact (@lem18392 (list B) P). Qed.
Lemma lem1198125 {A B : Type'} (f : A -> B) (a0 : B) : (term320 A B f a0) = (term321 A B f a0).
Proof. exact (@lem1198124 B (term117 A B f a0)). Qed.
Lemma lem1198126 {A B : Type'} (f : A -> B) (a0 : B) (a1 : list B) : (term322 A B f a0 a1) = (term115 A B f a0 a1).
Proof. exact (eq_refl (term322 A B f a0 a1)). Qed.
Lemma lem1198127 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1198128 {A B : Type'} (f : A -> B) (a0 : B) (a1 : list B) : (term323 A B f a0 a1) = (term317 A B f a0 a1).
Proof. exact (MK_COMB (@lem1198127) (@lem1198126 A B f a0 a1)). Qed.
Lemma lem1198129 {A B : Type'} (f : A -> B) (a0 : B) (a1 : list B) : (term323 A B f a0 a1) = (term316 A B f a0 a1).
Proof. exact (TRANS (@lem1198128 A B f a0 a1) (@lem1198123 A B f a0 a1)). Qed.
Lemma lem1198130 {A B : Type'} (f : A -> B) (a0 : B) : (term324 A B f a0) = (term325 A B f a0).
Proof. exact (fun_ext (fun a1 : list B => @lem1198129 A B f a0 a1)). Qed.
Lemma lem1198131 {B : Type'} : (@ex (list B)) = (@ex (list B)).
Proof. exact (eq_refl (@ex (list B))). Qed.
Lemma lem1198132 {A B : Type'} (f : A -> B) (a0 : B) : (term321 A B f a0) = (term326 A B f a0).
Proof. exact (MK_COMB (@lem1198131 B) (@lem1198130 A B f a0)). Qed.
Lemma lem1198133 {A B : Type'} (f : A -> B) (a0 : B) : (term320 A B f a0) = (term326 A B f a0).
Proof. exact (TRANS (@lem1198125 A B f a0) (@lem1198132 A B f a0)). Qed.
Lemma lem1198134 {B : Type'} (P : B -> Prop) : (term327 B P) = (term328 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem1198135 {A B : Type'} (f : A -> B) : (term329 A B f) = (term330 A B f).
Proof. exact (@lem1198134 B (term121 A B f)). Qed.
Lemma lem1198136 {A B : Type'} (f : A -> B) (a0 : B) : (term331 A B f a0) = (term119 A B f a0).
Proof. exact (eq_refl (term331 A B f a0)). Qed.
Lemma lem1198137 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1198138 {A B : Type'} (f : A -> B) (a0 : B) : (term332 A B f a0) = (term320 A B f a0).
Proof. exact (MK_COMB (@lem1198137) (@lem1198136 A B f a0)). Qed.
Lemma lem1198139 {A B : Type'} (f : A -> B) (a0 : B) : (term332 A B f a0) = (term326 A B f a0).
Proof. exact (TRANS (@lem1198138 A B f a0) (@lem1198133 A B f a0)). Qed.
Lemma lem1198140 {A B : Type'} (f : A -> B) : (term333 A B f) = (term334 A B f).
Proof. exact (fun_ext (fun a0 : B => @lem1198139 A B f a0)). Qed.
Lemma lem1198141 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem1198142 {A B : Type'} (f : A -> B) : (term330 A B f) = (term335 A B f).
Proof. exact (MK_COMB (@lem1198141 B) (@lem1198140 A B f)). Qed.
Lemma lem1198143 {A B : Type'} (f : A -> B) : (term329 A B f) = (term335 A B f).
Proof. exact (TRANS (@lem1198135 A B f) (@lem1198142 A B f)). Qed.
Lemma lem1198144 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1198145 {A B : Type'} (f : A -> B) : (term336 A B f) = (term337 A B f).
Proof. exact (MK_COMB (@lem1198144) (@lem1198103 A B f)). Qed.
Lemma lem1198146 {A B : Type'} (f : A -> B) : (term338 A B f) = (term339 A B f).
Proof. exact (MK_COMB (@lem1198145 A B f) (@lem1198143 A B f)). Qed.
Lemma lem1198147 {A B : Type'} (f : A -> B) : (term254 A B f) = (term338 A B f).
Proof. exact (@lem17045 (term105 A B f) (term123 A B f)). Qed.
Lemma lem1198148 {A B : Type'} (f : A -> B) : (term254 A B f) = (term339 A B f).
Proof. exact (TRANS (@lem1198147 A B f) (@lem1198146 A B f)). Qed.
Lemma lem1198215 {A : Type'} (P : A -> Prop) (Q : Prop) : (term340 A P Q) = (term341 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1198216 {A : Type'} (P : type1143 A) (Q : Prop) : (term342 A P Q) = (term343 A P Q).
Proof. exact (@lem1198215 (list A) P Q). Qed.
Lemma lem1198217 {A B : Type'} (f : A -> B) (a0 : B) (a1 : list B) : (term344 A B f a0 a1) = (term345 A B f a0 a1).
Proof. exact (@lem1198216 A (term269 A B f a1) (term313 A B f a0 a1)). Qed.
Lemma lem1198218 {A B : Type'} (f : A -> B) (l : list A) (a1 : list B) : (term346 A B f a1 l) = ((@List.map A B f l) = a1).
Proof. exact (eq_refl (term346 A B f a1 l)). Qed.
Lemma lem1198219 {A B : Type'} (f : A -> B) (a1 : list B) : (term347 A B f a1) = (term269 A B f a1).
Proof. exact (fun_ext (fun l : list A => @lem1198218 A B f l a1)). Qed.
Lemma lem1198220 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1198221 {A B : Type'} (f : A -> B) (a1 : list B) : (term348 A B f a1) = (term109 A B f a1).
Proof. exact (MK_COMB (@lem1198220 A) (@lem1198219 A B f a1)). Qed.
Lemma lem1198222 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1198223 {A B : Type'} (f : A -> B) (a1 : list B) : (term349 A B f a1) = (term314 A B f a1).
Proof. exact (MK_COMB (@lem1198222) (@lem1198221 A B f a1)). Qed.
Lemma lem1198224 {A B : Type'} (f : A -> B) (a0 : B) (a1 : list B) : (term313 A B f a0 a1) = (term313 A B f a0 a1).
Proof. exact (eq_refl (term313 A B f a0 a1)). Qed.
Lemma lem1198225 {A B : Type'} (f : A -> B) (a0 : B) (a1 : list B) : (term344 A B f a0 a1) = (term316 A B f a0 a1).
Proof. exact (MK_COMB (@lem1198223 A B f a1) (@lem1198224 A B f a0 a1)). Qed.
Lemma lem1198226 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1198227 {A B : Type'} (f : A -> B) (a0 : B) (a1 : list B) : (term350 A B f a0 a1) = (term351 A B f a0 a1).
Proof. exact (MK_COMB (@lem1198226) (@lem1198225 A B f a0 a1)). Qed.
Lemma lem1198228 {A B : Type'} (f : A -> B) (l : list A) (a1 : list B) : (term346 A B f a1 l) = ((@List.map A B f l) = a1).
Proof. exact (eq_refl (term346 A B f a1 l)). Qed.
Lemma lem1198229 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1198230 {A B : Type'} (f : A -> B) (l : list A) (a1 : list B) : (term352 A B f a1 l) = (term353 A B f l a1).
Proof. exact (MK_COMB (@lem1198229) (@lem1198228 A B f l a1)). Qed.
Lemma lem1198231 {A B : Type'} (f : A -> B) (a0 : B) (a1 : list B) : (term313 A B f a0 a1) = (term313 A B f a0 a1).
Proof. exact (eq_refl (term313 A B f a0 a1)). Qed.
Lemma lem1198232 {A B : Type'} (l : list A) (f : A -> B) (a0 : B) (a1 : list B) : (term354 A B l f a0 a1) = (term355 A B l f a0 a1).
Proof. exact (MK_COMB (@lem1198230 A B f l a1) (@lem1198231 A B f a0 a1)). Qed.
Lemma lem1198233 {A B : Type'} (f : A -> B) (a0 : B) (a1 : list B) : (term356 A B f a0 a1) = (term357 A B f a0 a1).
Proof. exact (fun_ext (fun l : list A => @lem1198232 A B l f a0 a1)). Qed.
Lemma lem1198234 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1198235 {A B : Type'} (f : A -> B) (a0 : B) (a1 : list B) : (term345 A B f a0 a1) = (term358 A B f a0 a1).
Proof. exact (MK_COMB (@lem1198234 A) (@lem1198233 A B f a0 a1)). Qed.
Lemma lem1198236 {A B : Type'} (f : A -> B) (a0 : B) (a1 : list B) : ((term344 A B f a0 a1) = (term345 A B f a0 a1)) = ((term316 A B f a0 a1) = (term358 A B f a0 a1)).
Proof. exact (MK_COMB (@lem1198227 A B f a0 a1) (@lem1198235 A B f a0 a1)). Qed.
Lemma lem1198237 {A B : Type'} (f : A -> B) (a0 : B) (a1 : list B) : (term316 A B f a0 a1) = (term358 A B f a0 a1).
Proof. exact (EQ_MP (@lem1198236 A B f a0 a1) (@lem1198217 A B f a0 a1)). Qed.
Lemma lem1198238 {A B : Type'} (f : A -> B) (a0 : B) : (term325 A B f a0) = (term359 A B f a0).
Proof. exact (fun_ext (fun a1 : list B => @lem1198237 A B f a0 a1)). Qed.
Lemma lem1198239 {B : Type'} : (@ex (list B)) = (@ex (list B)).
Proof. exact (eq_refl (@ex (list B))). Qed.
Lemma lem1198240 {A B : Type'} (f : A -> B) (a0 : B) : (term326 A B f a0) = (term360 A B f a0).
Proof. exact (MK_COMB (@lem1198239 B) (@lem1198238 A B f a0)). Qed.
Lemma lem1198241 {A B : Type'} (f : A -> B) : (term334 A B f) = (term361 A B f).
Proof. exact (fun_ext (fun a0 : B => @lem1198240 A B f a0)). Qed.
Lemma lem1198242 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem1198243 {A B : Type'} (f : A -> B) : (term335 A B f) = (term362 A B f).
Proof. exact (MK_COMB (@lem1198242 B) (@lem1198241 A B f)). Qed.
Lemma lem1198244 {A B : Type'} (f : A -> B) : (term337 A B f) = (term337 A B f).
Proof. exact (eq_refl (term337 A B f)). Qed.
Lemma lem1198245 {A B : Type'} (f : A -> B) : (term339 A B f) = (term363 A B f).
Proof. exact (MK_COMB (@lem1198244 A B f) (@lem1198243 A B f)). Qed.
Lemma lem1198247 {A : Type'} (P : Prop) (Q : A -> Prop) : (term187 A P Q) = (term188 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1198248 {B : Type'} (P : Prop) (Q : B -> Prop) : (term187 B P Q) = (term188 B P Q).
Proof. exact (@lem1198247 B P Q). Qed.
Lemma lem1198249 {A B : Type'} (f : A -> B) : (term364 A B f) = (term365 A B f).
Proof. exact (@lem1198248 B (term305 A B f) (term361 A B f)). Qed.
Lemma lem1198250 {A B : Type'} (f : A -> B) (a0 : B) : (term366 A B f a0) = (term360 A B f a0).
Proof. exact (eq_refl (term366 A B f a0)). Qed.
Lemma lem1198251 {A B : Type'} (f : A -> B) : (term367 A B f) = (term361 A B f).
Proof. exact (fun_ext (fun a0 : B => @lem1198250 A B f a0)). Qed.
Lemma lem1198252 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem1198253 {A B : Type'} (f : A -> B) : (term368 A B f) = (term362 A B f).
Proof. exact (MK_COMB (@lem1198252 B) (@lem1198251 A B f)). Qed.
Lemma lem1198254 {A B : Type'} (f : A -> B) : (term337 A B f) = (term337 A B f).
Proof. exact (eq_refl (term337 A B f)). Qed.
Lemma lem1198255 {A B : Type'} (f : A -> B) : (term364 A B f) = (term363 A B f).
Proof. exact (MK_COMB (@lem1198254 A B f) (@lem1198253 A B f)). Qed.
Lemma lem1198256 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1198257 {A B : Type'} (f : A -> B) : (term369 A B f) = (term370 A B f).
Proof. exact (MK_COMB (@lem1198256) (@lem1198255 A B f)). Qed.
Lemma lem1198258 {A B : Type'} (f : A -> B) (a0 : B) : (term366 A B f a0) = (term360 A B f a0).
Proof. exact (eq_refl (term366 A B f a0)). Qed.
Lemma lem1198259 {A B : Type'} (f : A -> B) : (term337 A B f) = (term337 A B f).
Proof. exact (eq_refl (term337 A B f)). Qed.
Lemma lem1198260 {A B : Type'} (f : A -> B) (a0 : B) : (term371 A B f a0) = (term372 A B f a0).
Proof. exact (MK_COMB (@lem1198259 A B f) (@lem1198258 A B f a0)). Qed.
Lemma lem1198261 {A B : Type'} (f : A -> B) : (term373 A B f) = (term374 A B f).
Proof. exact (fun_ext (fun a0 : B => @lem1198260 A B f a0)). Qed.
Lemma lem1198262 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem1198263 {A B : Type'} (f : A -> B) : (term365 A B f) = (term375 A B f).
Proof. exact (MK_COMB (@lem1198262 B) (@lem1198261 A B f)). Qed.
Lemma lem1198264 {A B : Type'} (f : A -> B) : ((term364 A B f) = (term365 A B f)) = ((term363 A B f) = (term375 A B f)).
Proof. exact (MK_COMB (@lem1198257 A B f) (@lem1198263 A B f)). Qed.
Lemma lem1198265 {A B : Type'} (f : A -> B) : (term363 A B f) = (term375 A B f).
Proof. exact (EQ_MP (@lem1198264 A B f) (@lem1198249 A B f)). Qed.
Lemma lem1198267 {A : Type'} (P : Prop) (Q : A -> Prop) : (term187 A P Q) = (term188 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1198268 {B : Type'} (P : Prop) (Q : type1143 B) : (term376 B P Q) = (term377 B P Q).
Proof. exact (@lem1198267 (list B) P Q). Qed.
Lemma lem1198269 {A B : Type'} (f : A -> B) (a0 : B) : (term378 A B f a0) = (term379 A B f a0).
Proof. exact (@lem1198268 B (term305 A B f) (term359 A B f a0)). Qed.
Lemma lem1198270 {A B : Type'} (f : A -> B) (a0 : B) (a1 : list B) : (term380 A B f a0 a1) = (term358 A B f a0 a1).
Proof. exact (eq_refl (term380 A B f a0 a1)). Qed.
Lemma lem1198271 {A B : Type'} (f : A -> B) (a0 : B) : (term381 A B f a0) = (term359 A B f a0).
Proof. exact (fun_ext (fun a1 : list B => @lem1198270 A B f a0 a1)). Qed.
Lemma lem1198272 {B : Type'} : (@ex (list B)) = (@ex (list B)).
Proof. exact (eq_refl (@ex (list B))). Qed.
Lemma lem1198273 {A B : Type'} (f : A -> B) (a0 : B) : (term382 A B f a0) = (term360 A B f a0).
Proof. exact (MK_COMB (@lem1198272 B) (@lem1198271 A B f a0)). Qed.
Lemma lem1198274 {A B : Type'} (f : A -> B) : (term337 A B f) = (term337 A B f).
Proof. exact (eq_refl (term337 A B f)). Qed.
Lemma lem1198275 {A B : Type'} (f : A -> B) (a0 : B) : (term378 A B f a0) = (term372 A B f a0).
Proof. exact (MK_COMB (@lem1198274 A B f) (@lem1198273 A B f a0)). Qed.
Lemma lem1198276 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1198277 {A B : Type'} (f : A -> B) (a0 : B) : (term383 A B f a0) = (term384 A B f a0).
Proof. exact (MK_COMB (@lem1198276) (@lem1198275 A B f a0)). Qed.
Lemma lem1198278 {A B : Type'} (f : A -> B) (a0 : B) (a1 : list B) : (term380 A B f a0 a1) = (term358 A B f a0 a1).
Proof. exact (eq_refl (term380 A B f a0 a1)). Qed.
Lemma lem1198279 {A B : Type'} (f : A -> B) : (term337 A B f) = (term337 A B f).
Proof. exact (eq_refl (term337 A B f)). Qed.
Lemma lem1198280 {A B : Type'} (f : A -> B) (a0 : B) (a1 : list B) : (term385 A B f a0 a1) = (term386 A B f a0 a1).
Proof. exact (MK_COMB (@lem1198279 A B f) (@lem1198278 A B f a0 a1)). Qed.
Lemma lem1198281 {A B : Type'} (f : A -> B) (a0 : B) : (term387 A B f a0) = (term388 A B f a0).
Proof. exact (fun_ext (fun a1 : list B => @lem1198280 A B f a0 a1)). Qed.
Lemma lem1198282 {B : Type'} : (@ex (list B)) = (@ex (list B)).
Proof. exact (eq_refl (@ex (list B))). Qed.
Lemma lem1198283 {A B : Type'} (f : A -> B) (a0 : B) : (term379 A B f a0) = (term389 A B f a0).
Proof. exact (MK_COMB (@lem1198282 B) (@lem1198281 A B f a0)). Qed.
Lemma lem1198284 {A B : Type'} (f : A -> B) (a0 : B) : ((term378 A B f a0) = (term379 A B f a0)) = ((term372 A B f a0) = (term389 A B f a0)).
Proof. exact (MK_COMB (@lem1198277 A B f a0) (@lem1198283 A B f a0)). Qed.
Lemma lem1198285 {A B : Type'} (f : A -> B) (a0 : B) : (term372 A B f a0) = (term389 A B f a0).
Proof. exact (EQ_MP (@lem1198284 A B f a0) (@lem1198269 A B f a0)). Qed.
Lemma lem1198287 {A : Type'} (P : Prop) (Q : A -> Prop) : (term187 A P Q) = (term188 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1198288 {A : Type'} (P : Prop) (Q : type1143 A) : (term376 A P Q) = (term377 A P Q).
Proof. exact (@lem1198287 (list A) P Q). Qed.
Lemma lem1198289 {A B : Type'} (f : A -> B) (a0 : B) (a1 : list B) : (term390 A B f a0 a1) = (term391 A B f a0 a1).
Proof. exact (@lem1198288 A (term305 A B f) (term357 A B f a0 a1)). Qed.
Lemma lem1198290 {A B : Type'} (l : list A) (f : A -> B) (a0 : B) (a1 : list B) : (term392 A B f a0 a1 l) = (term355 A B l f a0 a1).
Proof. exact (eq_refl (term392 A B f a0 a1 l)). Qed.
Lemma lem1198291 {A B : Type'} (f : A -> B) (a0 : B) (a1 : list B) : (term393 A B f a0 a1) = (term357 A B f a0 a1).
Proof. exact (fun_ext (fun l : list A => @lem1198290 A B l f a0 a1)). Qed.
Lemma lem1198292 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1198293 {A B : Type'} (f : A -> B) (a0 : B) (a1 : list B) : (term394 A B f a0 a1) = (term358 A B f a0 a1).
Proof. exact (MK_COMB (@lem1198292 A) (@lem1198291 A B f a0 a1)). Qed.
Lemma lem1198294 {A B : Type'} (f : A -> B) : (term337 A B f) = (term337 A B f).
Proof. exact (eq_refl (term337 A B f)). Qed.
Lemma lem1198295 {A B : Type'} (f : A -> B) (a0 : B) (a1 : list B) : (term390 A B f a0 a1) = (term386 A B f a0 a1).
Proof. exact (MK_COMB (@lem1198294 A B f) (@lem1198293 A B f a0 a1)). Qed.
Lemma lem1198296 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1198297 {A B : Type'} (f : A -> B) (a0 : B) (a1 : list B) : (term395 A B f a0 a1) = (term396 A B f a0 a1).
Proof. exact (MK_COMB (@lem1198296) (@lem1198295 A B f a0 a1)). Qed.
Lemma lem1198298 {A B : Type'} (l : list A) (f : A -> B) (a0 : B) (a1 : list B) : (term392 A B f a0 a1 l) = (term355 A B l f a0 a1).
Proof. exact (eq_refl (term392 A B f a0 a1 l)). Qed.
Lemma lem1198299 {A B : Type'} (f : A -> B) : (term337 A B f) = (term337 A B f).
Proof. exact (eq_refl (term337 A B f)). Qed.
Lemma lem1198300 {A B : Type'} (l : list A) (f : A -> B) (a0 : B) (a1 : list B) : (term397 A B f a0 a1 l) = (term398 A B l f a0 a1).
Proof. exact (MK_COMB (@lem1198299 A B f) (@lem1198298 A B l f a0 a1)). Qed.
Lemma lem1198301 {A B : Type'} (f : A -> B) (a0 : B) (a1 : list B) : (term399 A B f a0 a1) = (term400 A B f a0 a1).
Proof. exact (fun_ext (fun l : list A => @lem1198300 A B l f a0 a1)). Qed.
Lemma lem1198302 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1198303 {A B : Type'} (f : A -> B) (a0 : B) (a1 : list B) : (term391 A B f a0 a1) = (term401 A B f a0 a1).
Proof. exact (MK_COMB (@lem1198302 A) (@lem1198301 A B f a0 a1)). Qed.
Lemma lem1198304 {A B : Type'} (f : A -> B) (a0 : B) (a1 : list B) : ((term390 A B f a0 a1) = (term391 A B f a0 a1)) = ((term386 A B f a0 a1) = (term401 A B f a0 a1)).
Proof. exact (MK_COMB (@lem1198297 A B f a0 a1) (@lem1198303 A B f a0 a1)). Qed.
Lemma lem1198305 {A B : Type'} (f : A -> B) (a0 : B) (a1 : list B) : (term386 A B f a0 a1) = (term401 A B f a0 a1).
Proof. exact (EQ_MP (@lem1198304 A B f a0 a1) (@lem1198289 A B f a0 a1)). Qed.
Lemma lem1198306 {A B : Type'} (f : A -> B) (a0 : B) : (term388 A B f a0) = (term402 A B f a0).
Proof. exact (fun_ext (fun a1 : list B => @lem1198305 A B f a0 a1)). Qed.
Lemma lem1198307 {B : Type'} : (@ex (list B)) = (@ex (list B)).
Proof. exact (eq_refl (@ex (list B))). Qed.
Lemma lem1198308 {A B : Type'} (f : A -> B) (a0 : B) : (term389 A B f a0) = (term403 A B f a0).
Proof. exact (MK_COMB (@lem1198307 B) (@lem1198306 A B f a0)). Qed.
Lemma lem1198309 {A B : Type'} (f : A -> B) (a0 : B) : (term372 A B f a0) = (term403 A B f a0).
Proof. exact (TRANS (@lem1198285 A B f a0) (@lem1198308 A B f a0)). Qed.
Lemma lem1198310 {A B : Type'} (f : A -> B) : (term374 A B f) = (term404 A B f).
Proof. exact (fun_ext (fun a0 : B => @lem1198309 A B f a0)). Qed.
Lemma lem1198311 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem1198312 {A B : Type'} (f : A -> B) : (term375 A B f) = (term405 A B f).
Proof. exact (MK_COMB (@lem1198311 B) (@lem1198310 A B f)). Qed.
Lemma lem1198313 {A B : Type'} (f : A -> B) : (term363 A B f) = (term405 A B f).
Proof. exact (TRANS (@lem1198265 A B f) (@lem1198312 A B f)). Qed.
Lemma lem1198315 {A B : Type'} (f : A -> B) : (term339 A B f) = (term405 A B f).
Proof. exact (TRANS (@lem1198245 A B f) (@lem1198313 A B f)). Qed.
Lemma lem1198316 {A B : Type'} (f : A -> B) : (term254 A B f) = (term405 A B f).
Proof. exact (TRANS (@lem1198148 A B f) (@lem1198315 A B f)). Qed.
Lemma lem1198317 {A B : Type'} (f : A -> B) (h1 : term254 A B f) : term405 A B f.
Proof. exact (EQ_MP (@lem1198316 A B f) (@lem1198041 A B f h1)). Qed.
Lemma lem1198318 {A B : Type'} (f : A -> B) : ((@List.map A B f (@nil A)) = (@nil B)) = ((@List.map A B f (@nil A)) = (@nil B)).
Proof. exact (eq_refl ((@List.map A B f (@nil A)) = (@nil B))). Qed.
Lemma lem1198319 {A B : Type'} : (term182 A B) = (term182 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem1198318 A B f)). Qed.
Lemma lem1198320 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem1198321 {A B : Type'} : (term32 A B) = (term32 A B).
Proof. exact (MK_COMB (@lem1198320 A B) (@lem1198319 A B)). Qed.
Lemma lem1198322 {A B : Type'} (h : A) (f : A -> B) (t : list A) : ((term30 A B f h t) = (term31 A B h f t)) = ((term30 A B f h t) = (term31 A B h f t)).
Proof. exact (eq_refl ((term30 A B f h t) = (term31 A B h f t))). Qed.
Lemma lem1198323 {A B : Type'} (h : A) (f : A -> B) : (term179 A B h f) = (term179 A B h f).
Proof. exact (fun_ext (fun t : list A => @lem1198322 A B h f t)). Qed.
Lemma lem1198324 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1198325 {A B : Type'} (h : A) (f : A -> B) : (term28 A B h f) = (term28 A B h f).
Proof. exact (MK_COMB (@lem1198324 A) (@lem1198323 A B h f)). Qed.
Lemma lem1198326 {A B : Type'} (f : A -> B) : (term180 A B f) = (term180 A B f).
Proof. exact (fun_ext (fun h : A => @lem1198325 A B h f)). Qed.
Lemma lem1198327 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1198328 {A B : Type'} (f : A -> B) : (term26 A B f) = (term26 A B f).
Proof. exact (MK_COMB (@lem1198327 A) (@lem1198326 A B f)). Qed.
Lemma lem1198329 {A B : Type'} : (term181 A B) = (term181 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem1198328 A B f)). Qed.
Lemma lem1198330 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem1198331 {A B : Type'} : (term24 A B) = (term24 A B).
Proof. exact (MK_COMB (@lem1198330 A B) (@lem1198329 A B)). Qed.
Lemma lem1198332 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1198333 {A B : Type'} : (term183 A B) = (term183 A B).
Proof. exact (MK_COMB (@lem1198332) (@lem1198321 A B)). Qed.
Lemma lem1198354 {A B : Type'} : (term134 A B) = (term134 A B).
Proof. exact (MK_COMB (@lem1198333 A B) (@lem1198331 A B)). Qed.
Lemma lem1198355 {A B : Type'} (h1 : term134 A B) : term134 A B.
Proof. exact (EQ_MP (@lem1198354 A B) (@lem1198042 A B h1)). Qed.
Lemma lem1198394 {A B : Type'} (f : A -> B) (a0 : B) (h1 : term403 A B f a0) : term403 A B f a0.
Proof. exact (h1). Qed.
Lemma lem1198395 {A B : Type'} (f : A -> B) (a0 : B) (a1 : list B) (h1 : term401 A B f a0 a1) : term401 A B f a0 a1.
Proof. exact (h1). Qed.
Lemma lem1198396 {A B : Type'} (l : list A) (f : A -> B) (a0 : B) (a1 : list B) (h1 : term398 A B l f a0 a1) : term398 A B l f a0 a1.
Proof. exact (h1). Qed.
Lemma lem1198397 {A B : Type'} (f : A -> B) (x : B -> A) (h1 : term292 A B f x) : term292 A B f x.
Proof. exact (h1). Qed.
Lemma lem1198398 {B : Type'} : (@eq (list B)) = (@eq (list B)).
Proof. exact (eq_refl (@eq (list B))). Qed.
Lemma lem1198407 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1198408 {A : Type'} (f : type1397 A) (x : A) : (f x) = (@I (A -> (list A) -> list A) f x).
Proof. exact (@lem1198407 A (type1138 A) f x). Qed.
Lemma lem1198409 {A : Type'} (h : A) : (@cons A h) = (@I (A -> (list A) -> list A) (@cons A) h).
Proof. exact (@lem1198408 A (@cons A) h). Qed.
Lemma lem1198410 {A : Type'} (t : list A) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1198411 {A : Type'} (h : A) (t : list A) : (@cons A h t) = (@I (A -> (list A) -> list A) (@cons A) h t).
Proof. exact (MK_COMB (@lem1198409 A h) (@lem1198410 A t)). Qed.
Lemma lem1198413 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1198414 {A : Type'} (f : type1138 A) (x : list A) : (f x) = (@I ((list A) -> list A) f x).
Proof. exact (@lem1198413 (list A) (list A) f x). Qed.
Lemma lem1198415 {A : Type'} (h : A) (t : list A) : (@I (A -> (list A) -> list A) (@cons A) h t) = (term406 A h t).
Proof. exact (@lem1198414 A (@I (A -> (list A) -> list A) (@cons A) h) t). Qed.
Lemma lem1198417 {A : Type'} (h : A) (t : list A) : (@cons A h t) = (term406 A h t).
Proof. exact (TRANS (@lem1198411 A h t) (@lem1198415 A h t)). Qed.
Lemma lem1198418 {A B : Type'} (f : A -> B) : (@List.map A B f) = (@List.map A B f).
Proof. exact (eq_refl (@List.map A B f)). Qed.
Lemma lem1198419 {A B : Type'} (f : A -> B) (h : A) (t : list A) : (term30 A B f h t) = (term407 A B f h t).
Proof. exact (MK_COMB (@lem1198418 A B f) (@lem1198417 A h t)). Qed.
Lemma lem1198421 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1198422 {A B : Type'} (f : type540 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (list A) -> list B) f x).
Proof. exact (@lem1198421 (A -> B) (type1139 A B) f x). Qed.
Lemma lem1198423 {A B : Type'} (f : A -> B) : (@List.map A B f) = (@I ((A -> B) -> (list A) -> list B) (@List.map A B) f).
Proof. exact (@lem1198422 A B (@List.map A B) f). Qed.
Lemma lem1198424 {A : Type'} (h : A) (t : list A) : (term406 A h t) = (term406 A h t).
Proof. exact (eq_refl (term406 A h t)). Qed.
Lemma lem1198425 {A B : Type'} (f : A -> B) (h : A) (t : list A) : (term407 A B f h t) = (term408 A B f h t).
Proof. exact (MK_COMB (@lem1198423 A B f) (@lem1198424 A h t)). Qed.
Lemma lem1198427 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1198428 {A B : Type'} (f : type1139 A B) (x : list A) : (f x) = (@I ((list A) -> list B) f x).
Proof. exact (@lem1198427 (list A) (list B) f x). Qed.
Lemma lem1198429 {A B : Type'} (f : A -> B) (h : A) (t : list A) : (term408 A B f h t) = (term409 A B f h t).
Proof. exact (@lem1198428 A B (@I ((A -> B) -> (list A) -> list B) (@List.map A B) f) (term406 A h t)). Qed.
Lemma lem1198430 {A B : Type'} (f : A -> B) (h : A) (t : list A) : (term407 A B f h t) = (term409 A B f h t).
Proof. exact (TRANS (@lem1198425 A B f h t) (@lem1198429 A B f h t)). Qed.
Lemma lem1198431 {A B : Type'} (f : A -> B) (h : A) (t : list A) : (term30 A B f h t) = (term409 A B f h t).
Proof. exact (TRANS (@lem1198419 A B f h t) (@lem1198430 A B f h t)). Qed.
Lemma lem1198432 {B : Type'} : (@cons B) = (@cons B).
Proof. exact (eq_refl (@cons B)). Qed.
Lemma lem1198437 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1198438 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem1198437 A B f x). Qed.
Lemma lem1198440 {A B : Type'} (f : A -> B) (h : A) : (f h) = (@I (A -> B) f h).
Proof. exact (@lem1198438 A B f h). Qed.
Lemma lem1198447 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1198448 {A B : Type'} (f : type540 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (list A) -> list B) f x).
Proof. exact (@lem1198447 (A -> B) (type1139 A B) f x). Qed.
Lemma lem1198449 {A B : Type'} (f : A -> B) : (@List.map A B f) = (@I ((A -> B) -> (list A) -> list B) (@List.map A B) f).
Proof. exact (@lem1198448 A B (@List.map A B) f). Qed.
Lemma lem1198450 {A : Type'} (t : list A) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1198451 {A B : Type'} (f : A -> B) (t : list A) : (@List.map A B f t) = (@I ((A -> B) -> (list A) -> list B) (@List.map A B) f t).
Proof. exact (MK_COMB (@lem1198449 A B f) (@lem1198450 A t)). Qed.
Lemma lem1198453 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1198454 {A B : Type'} (f : type1139 A B) (x : list A) : (f x) = (@I ((list A) -> list B) f x).
Proof. exact (@lem1198453 (list A) (list B) f x). Qed.
Lemma lem1198455 {A B : Type'} (f : A -> B) (t : list A) : (@I ((A -> B) -> (list A) -> list B) (@List.map A B) f t) = (term223 A B f t).
Proof. exact (@lem1198454 A B (@I ((A -> B) -> (list A) -> list B) (@List.map A B) f) t). Qed.
Lemma lem1198457 {A B : Type'} (f : A -> B) (t : list A) : (@List.map A B f t) = (term223 A B f t).
Proof. exact (TRANS (@lem1198451 A B f t) (@lem1198455 A B f t)). Qed.
Lemma lem1198458 {A B : Type'} (f : A -> B) (h : A) : (term410 A B f h) = (term411 A B f h).
Proof. exact (MK_COMB (@lem1198432 B) (@lem1198440 A B f h)). Qed.
Lemma lem1198459 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term31 A B h f t) = (term412 A B h f t).
Proof. exact (MK_COMB (@lem1198458 A B f h) (@lem1198457 A B f t)). Qed.
Lemma lem1198461 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1198462 {B : Type'} (f : type1397 B) (x : B) : (f x) = (@I (B -> (list B) -> list B) f x).
Proof. exact (@lem1198461 B (type1138 B) f x). Qed.
Lemma lem1198463 {A B : Type'} (f : A -> B) (h : A) : (term411 A B f h) = (term413 A B f h).
Proof. exact (@lem1198462 B (@cons B) (@I (A -> B) f h)). Qed.
Lemma lem1198464 {A B : Type'} (f : A -> B) (t : list A) : (term223 A B f t) = (term223 A B f t).
Proof. exact (eq_refl (term223 A B f t)). Qed.
Lemma lem1198465 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term412 A B h f t) = (term414 A B h f t).
Proof. exact (MK_COMB (@lem1198463 A B f h) (@lem1198464 A B f t)). Qed.
Lemma lem1198467 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1198468 {B : Type'} (f : type1138 B) (x : list B) : (f x) = (@I ((list B) -> list B) f x).
Proof. exact (@lem1198467 (list B) (list B) f x). Qed.
Lemma lem1198469 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term414 A B h f t) = (term415 A B h f t).
Proof. exact (@lem1198468 B (term413 A B f h) (term223 A B f t)). Qed.
Lemma lem1198470 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term412 A B h f t) = (term415 A B h f t).
Proof. exact (TRANS (@lem1198465 A B h f t) (@lem1198469 A B h f t)). Qed.
Lemma lem1198471 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term31 A B h f t) = (term415 A B h f t).
Proof. exact (TRANS (@lem1198459 A B h f t) (@lem1198470 A B h f t)). Qed.
Lemma lem1198472 {A B : Type'} (f : A -> B) (h : A) (t : list A) : (term94 A B f h t) = (term416 A B f h t).
Proof. exact (MK_COMB (@lem1198398 B) (@lem1198431 A B f h t)). Qed.
Lemma lem1198473 {A B : Type'} (h : A) (f : A -> B) (t : list A) : ((term30 A B f h t) = (term31 A B h f t)) = ((term409 A B f h t) = (term415 A B h f t)).
Proof. exact (MK_COMB (@lem1198472 A B f h t) (@lem1198471 A B h f t)). Qed.
Lemma lem1198474 {A B : Type'} (h : A) (f : A -> B) : (term179 A B h f) = (term417 A B h f).
Proof. exact (fun_ext (fun t : list A => @lem1198473 A B h f t)). Qed.
Lemma lem1198475 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1198476 {A B : Type'} (h : A) (f : A -> B) : (term28 A B h f) = (term418 A B h f).
Proof. exact (MK_COMB (@lem1198475 A) (@lem1198474 A B h f)). Qed.
Lemma lem1198477 {A B : Type'} (f : A -> B) : (term180 A B f) = (term419 A B f).
Proof. exact (fun_ext (fun h : A => @lem1198476 A B h f)). Qed.
Lemma lem1198478 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1198479 {A B : Type'} (f : A -> B) : (term26 A B f) = (term420 A B f).
Proof. exact (MK_COMB (@lem1198478 A) (@lem1198477 A B f)). Qed.
Lemma lem1198480 {A B : Type'} : (term181 A B) = (term421 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem1198479 A B f)). Qed.
Lemma lem1198481 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem1198482 {A B : Type'} : (term24 A B) = (term422 A B).
Proof. exact (MK_COMB (@lem1198481 A B) (@lem1198480 A B)). Qed.
Lemma lem1198483 {B : Type'} : (@eq (list B)) = (@eq (list B)).
Proof. exact (eq_refl (@eq (list B))). Qed.
Lemma lem1198490 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1198491 {A B : Type'} (f : type540 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (list A) -> list B) f x).
Proof. exact (@lem1198490 (A -> B) (type1139 A B) f x). Qed.
Lemma lem1198492 {A B : Type'} (f : A -> B) : (@List.map A B f) = (@I ((A -> B) -> (list A) -> list B) (@List.map A B) f).
Proof. exact (@lem1198491 A B (@List.map A B) f). Qed.
Lemma lem1198493 {A : Type'} : (@nil A) = (@nil A).
Proof. exact (eq_refl (@nil A)). Qed.
Lemma lem1198494 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (@I ((A -> B) -> (list A) -> list B) (@List.map A B) f (@nil A)).
Proof. exact (MK_COMB (@lem1198492 A B f) (@lem1198493 A)). Qed.
Lemma lem1198496 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1198497 {A B : Type'} (f : type1139 A B) (x : list A) : (f x) = (@I ((list A) -> list B) f x).
Proof. exact (@lem1198496 (list A) (list B) f x). Qed.
Lemma lem1198498 {A B : Type'} (f : A -> B) : (@I ((A -> B) -> (list A) -> list B) (@List.map A B) f (@nil A)) = (term423 A B f).
Proof. exact (@lem1198497 A B (@I ((A -> B) -> (list A) -> list B) (@List.map A B) f) (@nil A)). Qed.
Lemma lem1198500 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (term423 A B f).
Proof. exact (TRANS (@lem1198494 A B f) (@lem1198498 A B f)). Qed.
Lemma lem1198501 {B : Type'} : (@nil B) = (@nil B).
Proof. exact (eq_refl (@nil B)). Qed.
Lemma lem1198502 {A B : Type'} (f : A -> B) : (term91 A B f) = (term424 A B f).
Proof. exact (MK_COMB (@lem1198483 B) (@lem1198500 A B f)). Qed.
Lemma lem1198503 {A B : Type'} (f : A -> B) : ((@List.map A B f (@nil A)) = (@nil B)) = ((term423 A B f) = (@nil B)).
Proof. exact (MK_COMB (@lem1198502 A B f) (@lem1198501 B)). Qed.
Lemma lem1198504 {A B : Type'} : (term182 A B) = (term425 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem1198503 A B f)). Qed.
Lemma lem1198505 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem1198506 {A B : Type'} : (term32 A B) = (term426 A B).
Proof. exact (MK_COMB (@lem1198505 A B) (@lem1198504 A B)). Qed.
Lemma lem1198507 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1198508 {A B : Type'} : (term183 A B) = (term427 A B).
Proof. exact (MK_COMB (@lem1198507) (@lem1198506 A B)). Qed.
Lemma lem1198509 {A B : Type'} : (term134 A B) = (term428 A B).
Proof. exact (MK_COMB (@lem1198508 A B) (@lem1198482 A B)). Qed.
Lemma lem1198510 {A B : Type'} (h1 : term134 A B) : term428 A B.
Proof. exact (EQ_MP (@lem1198509 A B) (@lem1198355 A B h1)). Qed.
Lemma lem1198624 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1198625 {B : Type'} : (@eq (list B)) = (@eq (list B)).
Proof. exact (eq_refl (@eq (list B))). Qed.
Lemma lem1198632 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1198633 {A B : Type'} (f : type540 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (list A) -> list B) f x).
Proof. exact (@lem1198632 (A -> B) (type1139 A B) f x). Qed.
Lemma lem1198634 {A B : Type'} (f : A -> B) : (@List.map A B f) = (@I ((A -> B) -> (list A) -> list B) (@List.map A B) f).
Proof. exact (@lem1198633 A B (@List.map A B) f). Qed.
Lemma lem1198635 {A : Type'} (l : list A) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem1198636 {A B : Type'} (f : A -> B) (l : list A) : (@List.map A B f l) = (@I ((A -> B) -> (list A) -> list B) (@List.map A B) f l).
Proof. exact (MK_COMB (@lem1198634 A B f) (@lem1198635 A l)). Qed.
Lemma lem1198638 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1198639 {A B : Type'} (f : type1139 A B) (x : list A) : (f x) = (@I ((list A) -> list B) f x).
Proof. exact (@lem1198638 (list A) (list B) f x). Qed.
Lemma lem1198640 {A B : Type'} (f : A -> B) (l : list A) : (@I ((A -> B) -> (list A) -> list B) (@List.map A B) f l) = (term223 A B f l).
Proof. exact (@lem1198639 A B (@I ((A -> B) -> (list A) -> list B) (@List.map A B) f) l). Qed.
Lemma lem1198642 {A B : Type'} (f : A -> B) (l : list A) : (@List.map A B f l) = (term223 A B f l).
Proof. exact (TRANS (@lem1198636 A B f l) (@lem1198640 A B f l)). Qed.
Lemma lem1198649 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1198650 {B : Type'} (f : type1397 B) (x : B) : (f x) = (@I (B -> (list B) -> list B) f x).
Proof. exact (@lem1198649 B (type1138 B) f x). Qed.
Lemma lem1198651 {B : Type'} (a0 : B) : (@cons B a0) = (@I (B -> (list B) -> list B) (@cons B) a0).
Proof. exact (@lem1198650 B (@cons B) a0). Qed.
Lemma lem1198652 {B : Type'} (a1 : list B) : a1 = a1.
Proof. exact (eq_refl a1). Qed.
Lemma lem1198653 {B : Type'} (a0 : B) (a1 : list B) : (@cons B a0 a1) = (@I (B -> (list B) -> list B) (@cons B) a0 a1).
Proof. exact (MK_COMB (@lem1198651 B a0) (@lem1198652 B a1)). Qed.
Lemma lem1198655 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1198656 {B : Type'} (f : type1138 B) (x : list B) : (f x) = (@I ((list B) -> list B) f x).
Proof. exact (@lem1198655 (list B) (list B) f x). Qed.
Lemma lem1198657 {B : Type'} (a0 : B) (a1 : list B) : (@I (B -> (list B) -> list B) (@cons B) a0 a1) = (term406 B a0 a1).
Proof. exact (@lem1198656 B (@I (B -> (list B) -> list B) (@cons B) a0) a1). Qed.
Lemma lem1198659 {B : Type'} (a0 : B) (a1 : list B) : (@cons B a0 a1) = (term406 B a0 a1).
Proof. exact (TRANS (@lem1198653 B a0 a1) (@lem1198657 B a0 a1)). Qed.
Lemma lem1198660 {A B : Type'} (f : A -> B) (l : list A) : (term225 A B f l) = (term226 A B f l).
Proof. exact (MK_COMB (@lem1198625 B) (@lem1198642 A B f l)). Qed.
Lemma lem1198661 {A B : Type'} (f : A -> B) (l : list A) (a0 : B) (a1 : list B) : ((@List.map A B f l) = (@cons B a0 a1)) = ((term223 A B f l) = (term406 B a0 a1)).
Proof. exact (MK_COMB (@lem1198660 A B f l) (@lem1198659 B a0 a1)). Qed.
Lemma lem1198662 {A B : Type'} (f : A -> B) (l : list A) (a0 : B) (a1 : list B) : (term310 A B f l a0 a1) = (term429 A B f l a0 a1).
Proof. exact (MK_COMB (@lem1198624) (@lem1198661 A B f l a0 a1)). Qed.
Lemma lem1198663 {A B : Type'} (f : A -> B) (a0 : B) (a1 : list B) : (term312 A B f a0 a1) = (term430 A B f a0 a1).
Proof. exact (fun_ext (fun l : list A => @lem1198662 A B f l a0 a1)). Qed.
Lemma lem1198664 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1198665 {A B : Type'} (f : A -> B) (a0 : B) (a1 : list B) : (term313 A B f a0 a1) = (term431 A B f a0 a1).
Proof. exact (MK_COMB (@lem1198664 A) (@lem1198663 A B f a0 a1)). Qed.
Lemma lem1198666 {B : Type'} : (@eq (list B)) = (@eq (list B)).
Proof. exact (eq_refl (@eq (list B))). Qed.
Lemma lem1198673 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1198674 {A B : Type'} (f : type540 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (list A) -> list B) f x).
Proof. exact (@lem1198673 (A -> B) (type1139 A B) f x). Qed.
Lemma lem1198675 {A B : Type'} (f : A -> B) : (@List.map A B f) = (@I ((A -> B) -> (list A) -> list B) (@List.map A B) f).
Proof. exact (@lem1198674 A B (@List.map A B) f). Qed.
Lemma lem1198676 {A : Type'} (l : list A) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem1198677 {A B : Type'} (f : A -> B) (l : list A) : (@List.map A B f l) = (@I ((A -> B) -> (list A) -> list B) (@List.map A B) f l).
Proof. exact (MK_COMB (@lem1198675 A B f) (@lem1198676 A l)). Qed.
Lemma lem1198679 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1198680 {A B : Type'} (f : type1139 A B) (x : list A) : (f x) = (@I ((list A) -> list B) f x).
Proof. exact (@lem1198679 (list A) (list B) f x). Qed.
Lemma lem1198681 {A B : Type'} (f : A -> B) (l : list A) : (@I ((A -> B) -> (list A) -> list B) (@List.map A B) f l) = (term223 A B f l).
Proof. exact (@lem1198680 A B (@I ((A -> B) -> (list A) -> list B) (@List.map A B) f) l). Qed.
Lemma lem1198683 {A B : Type'} (f : A -> B) (l : list A) : (@List.map A B f l) = (term223 A B f l).
Proof. exact (TRANS (@lem1198677 A B f l) (@lem1198681 A B f l)). Qed.
Lemma lem1198684 {B : Type'} (a1 : list B) : a1 = a1.
Proof. exact (eq_refl a1). Qed.
Lemma lem1198685 {A B : Type'} (f : A -> B) (l : list A) : (term225 A B f l) = (term226 A B f l).
Proof. exact (MK_COMB (@lem1198666 B) (@lem1198683 A B f l)). Qed.
Lemma lem1198686 {A B : Type'} (f : A -> B) (l : list A) (a1 : list B) : ((@List.map A B f l) = a1) = ((term223 A B f l) = a1).
Proof. exact (MK_COMB (@lem1198685 A B f l) (@lem1198684 B a1)). Qed.
Lemma lem1198687 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1198688 {A B : Type'} (f : A -> B) (l : list A) (a1 : list B) : (term353 A B f l a1) = (term432 A B f l a1).
Proof. exact (MK_COMB (@lem1198687) (@lem1198686 A B f l a1)). Qed.
Lemma lem1198689 {A B : Type'} (l : list A) (f : A -> B) (a0 : B) (a1 : list B) : (term355 A B l f a0 a1) = (term433 A B l f a0 a1).
Proof. exact (MK_COMB (@lem1198688 A B f l a1) (@lem1198665 A B f a0 a1)). Qed.
Lemma lem1198690 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1198691 {B : Type'} : (@eq (list B)) = (@eq (list B)).
Proof. exact (eq_refl (@eq (list B))). Qed.
Lemma lem1198698 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1198699 {A B : Type'} (f : type540 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (list A) -> list B) f x).
Proof. exact (@lem1198698 (A -> B) (type1139 A B) f x). Qed.
Lemma lem1198700 {A B : Type'} (f : A -> B) : (@List.map A B f) = (@I ((A -> B) -> (list A) -> list B) (@List.map A B) f).
Proof. exact (@lem1198699 A B (@List.map A B) f). Qed.
Lemma lem1198701 {A : Type'} (l : list A) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem1198702 {A B : Type'} (f : A -> B) (l : list A) : (@List.map A B f l) = (@I ((A -> B) -> (list A) -> list B) (@List.map A B) f l).
Proof. exact (MK_COMB (@lem1198700 A B f) (@lem1198701 A l)). Qed.
Lemma lem1198704 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1198705 {A B : Type'} (f : type1139 A B) (x : list A) : (f x) = (@I ((list A) -> list B) f x).
Proof. exact (@lem1198704 (list A) (list B) f x). Qed.
Lemma lem1198706 {A B : Type'} (f : A -> B) (l : list A) : (@I ((A -> B) -> (list A) -> list B) (@List.map A B) f l) = (term223 A B f l).
Proof. exact (@lem1198705 A B (@I ((A -> B) -> (list A) -> list B) (@List.map A B) f) l). Qed.
Lemma lem1198708 {A B : Type'} (f : A -> B) (l : list A) : (@List.map A B f l) = (term223 A B f l).
Proof. exact (TRANS (@lem1198702 A B f l) (@lem1198706 A B f l)). Qed.
Lemma lem1198709 {B : Type'} : (@nil B) = (@nil B).
Proof. exact (eq_refl (@nil B)). Qed.
Lemma lem1198710 {A B : Type'} (f : A -> B) (l : list A) : (term225 A B f l) = (term226 A B f l).
Proof. exact (MK_COMB (@lem1198691 B) (@lem1198708 A B f l)). Qed.
Lemma lem1198711 {A B : Type'} (f : A -> B) (l : list A) : ((@List.map A B f l) = (@nil B)) = ((term223 A B f l) = (@nil B)).
Proof. exact (MK_COMB (@lem1198710 A B f l) (@lem1198709 B)). Qed.
Lemma lem1198712 {A B : Type'} (f : A -> B) (l : list A) : (term302 A B f l) = (term434 A B f l).
Proof. exact (MK_COMB (@lem1198690) (@lem1198711 A B f l)). Qed.
Lemma lem1198713 {A B : Type'} (f : A -> B) : (term304 A B f) = (term435 A B f).
Proof. exact (fun_ext (fun l : list A => @lem1198712 A B f l)). Qed.
Lemma lem1198714 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1198715 {A B : Type'} (f : A -> B) : (term305 A B f) = (term436 A B f).
Proof. exact (MK_COMB (@lem1198714 A) (@lem1198713 A B f)). Qed.
Lemma lem1198716 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1198717 {A B : Type'} (f : A -> B) : (term337 A B f) = (term437 A B f).
Proof. exact (MK_COMB (@lem1198716) (@lem1198715 A B f)). Qed.
Lemma lem1198718 {A B : Type'} (l : list A) (f : A -> B) (a0 : B) (a1 : list B) : (term398 A B l f a0 a1) = (term438 A B l f a0 a1).
Proof. exact (MK_COMB (@lem1198717 A B f) (@lem1198689 A B l f a0 a1)). Qed.
Lemma lem1198719 {A B : Type'} (l : list A) (f : A -> B) (a0 : B) (a1 : list B) (h1 : term398 A B l f a0 a1) : term438 A B l f a0 a1.
Proof. exact (EQ_MP (@lem1198718 A B l f a0 a1) (@lem1198396 A B l f a0 a1 h1)). Qed.
Lemma lem1198720 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem1198721 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1198726 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1198727 {A B : Type'} (f : B -> A) (x : B) : (f x) = (@I (B -> A) f x).
Proof. exact (@lem1198726 B A f x). Qed.
Lemma lem1198729 {A B : Type'} (x : B -> A) (y : B) : (x y) = (@I (B -> A) x y).
Proof. exact (@lem1198727 A B x y). Qed.
Lemma lem1198730 {A B : Type'} (f : A -> B) (x : B -> A) (y : B) : (term288 A B f x y) = (term439 A B f x y).
Proof. exact (MK_COMB (@lem1198721 A B f) (@lem1198729 A B x y)). Qed.
Lemma lem1198732 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1198733 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem1198732 A B f x). Qed.
Lemma lem1198734 {A B : Type'} (f : A -> B) (x : B -> A) (y : B) : (term439 A B f x y) = (term440 A B f x y).
Proof. exact (@lem1198733 A B f (@I (B -> A) x y)). Qed.
Lemma lem1198735 {A B : Type'} (f : A -> B) (x : B -> A) (y : B) : (term288 A B f x y) = (term440 A B f x y).
Proof. exact (TRANS (@lem1198730 A B f x y) (@lem1198734 A B f x y)). Qed.
Lemma lem1198736 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1198737 {A B : Type'} (f : A -> B) (x : B -> A) (y : B) : (term441 A B f x y) = (term442 A B f x y).
Proof. exact (MK_COMB (@lem1198720 B) (@lem1198735 A B f x y)). Qed.
Lemma lem1198738 {A B : Type'} (f : A -> B) (x : B -> A) (y : B) : ((term288 A B f x y) = y) = ((term440 A B f x y) = y).
Proof. exact (MK_COMB (@lem1198737 A B f x y) (@lem1198736 B y)). Qed.
Lemma lem1198739 {A B : Type'} (f : A -> B) (x : B -> A) : (term290 A B f x) = (term443 A B f x).
Proof. exact (fun_ext (fun y : B => @lem1198738 A B f x y)). Qed.
Lemma lem1198740 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1198741 {A B : Type'} (f : A -> B) (x : B -> A) : (term292 A B f x) = (term444 A B f x).
Proof. exact (MK_COMB (@lem1198740 B) (@lem1198739 A B f x)). Qed.
Lemma lem1198742 {A B : Type'} (f : A -> B) (x : B -> A) (h1 : term292 A B f x) : term444 A B f x.
Proof. exact (EQ_MP (@lem1198741 A B f x) (@lem1198397 A B f x h1)). Qed.
Lemma lem1198745 {A B : Type'} (h1 : term134 A B) : term422 A B.
Proof. exact (proj2 (@lem1198510 A B h1)). Qed.
Lemma lem1198746 {A B : Type'} (h1 : term134 A B) : term426 A B.
Proof. exact (proj1 (@lem1198510 A B h1)). Qed.
Lemma lem1198747 {A B : Type'} (f : A -> B) (h1 : term436 A B f) : term436 A B f.
Proof. exact (h1). Qed.
Lemma lem1198748 {A B : Type'} (l : list A) (f : A -> B) (a0 : B) (a1 : list B) (h1 : term433 A B l f a0 a1) : term433 A B l f a0 a1.
Proof. exact (h1). Qed.
Lemma lem1198749 {A B : Type'} (l : list A) (f : A -> B) (a0 : B) (a1 : list B) (h1 : term433 A B l f a0 a1) : term431 A B f a0 a1.
Proof. exact (proj2 (@lem1198748 A B l f a0 a1 h1)). Qed.
Lemma lem1198779 {A B : Type'} (f : A -> B) : ((term423 A B f) = (@nil B)) = ((term423 A B f) = (@nil B)).
Proof. exact (eq_refl ((term423 A B f) = (@nil B))). Qed.
Lemma lem1198780 {A B : Type'} : (term425 A B) = (term425 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem1198779 A B f)). Qed.
Lemma lem1198781 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem1198783 {A B : Type'} : (term426 A B) = (term426 A B).
Proof. exact (MK_COMB (@lem1198781 A B) (@lem1198780 A B)). Qed.
Lemma lem1198784 {A B : Type'} (h1 : term134 A B) : term426 A B.
Proof. exact (EQ_MP (@lem1198783 A B) (@lem1198746 A B h1)). Qed.
Lemma lem1198799 {A B : Type'} (f : A -> B) (l : list A) : (term434 A B f l) = (term434 A B f l).
Proof. exact (eq_refl (term434 A B f l)). Qed.
Lemma lem1198800 {A B : Type'} (f : A -> B) : (term435 A B f) = (term435 A B f).
Proof. exact (fun_ext (fun l : list A => @lem1198799 A B f l)). Qed.
Lemma lem1198801 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1198803 {A B : Type'} (f : A -> B) : (term436 A B f) = (term436 A B f).
Proof. exact (MK_COMB (@lem1198801 A) (@lem1198800 A B f)). Qed.
Lemma lem1198804 {A B : Type'} (f : A -> B) (h1 : term436 A B f) : term436 A B f.
Proof. exact (EQ_MP (@lem1198803 A B f) (@lem1198747 A B f h1)). Qed.
Lemma lem1198806 {A B : Type'} (f : A -> B) (x : B -> A) (y : B) : ((term440 A B f x y) = y) = ((term440 A B f x y) = y).
Proof. exact (eq_refl ((term440 A B f x y) = y)). Qed.
Lemma lem1198807 {A B : Type'} (f : A -> B) (x : B -> A) : (term443 A B f x) = (term443 A B f x).
Proof. exact (fun_ext (fun y : B => @lem1198806 A B f x y)). Qed.
Lemma lem1198808 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1198810 {A B : Type'} (f : A -> B) (x : B -> A) : (term444 A B f x) = (term444 A B f x).
Proof. exact (MK_COMB (@lem1198808 B) (@lem1198807 A B f x)). Qed.
Lemma lem1198811 {A B : Type'} (f : A -> B) (x : B -> A) (h1 : term292 A B f x) : term444 A B f x.
Proof. exact (EQ_MP (@lem1198810 A B f x) (@lem1198742 A B f x h1)). Qed.
Lemma lem1198840 {A B : Type'} (h : A) (f : A -> B) (t : list A) : ((term409 A B f h t) = (term415 A B h f t)) = ((term409 A B f h t) = (term415 A B h f t)).
Proof. exact (eq_refl ((term409 A B f h t) = (term415 A B h f t))). Qed.
Lemma lem1198841 {A B : Type'} (h : A) (f : A -> B) : (term417 A B h f) = (term417 A B h f).
Proof. exact (fun_ext (fun t : list A => @lem1198840 A B h f t)). Qed.
Lemma lem1198842 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1198843 {A B : Type'} (h : A) (f : A -> B) : (term418 A B h f) = (term418 A B h f).
Proof. exact (MK_COMB (@lem1198842 A) (@lem1198841 A B h f)). Qed.
Lemma lem1198844 {A B : Type'} (f : A -> B) : (term419 A B f) = (term419 A B f).
Proof. exact (fun_ext (fun h : A => @lem1198843 A B h f)). Qed.
Lemma lem1198845 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1198846 {A B : Type'} (f : A -> B) : (term420 A B f) = (term420 A B f).
Proof. exact (MK_COMB (@lem1198845 A) (@lem1198844 A B f)). Qed.
Lemma lem1198847 {A B : Type'} : (term421 A B) = (term421 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem1198846 A B f)). Qed.
Lemma lem1198848 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem1198850 {A B : Type'} : (term422 A B) = (term422 A B).
Proof. exact (MK_COMB (@lem1198848 A B) (@lem1198847 A B)). Qed.
Lemma lem1198851 {A B : Type'} (h1 : term134 A B) : term422 A B.
Proof. exact (EQ_MP (@lem1198850 A B) (@lem1198745 A B h1)). Qed.
Lemma lem1198857 {A B : Type'} (f : A -> B) (l : list A) (a0 : B) (a1 : list B) : (term429 A B f l a0 a1) = (term429 A B f l a0 a1).
Proof. exact (eq_refl (term429 A B f l a0 a1)). Qed.
Lemma lem1198858 {A B : Type'} (f : A -> B) (a0 : B) (a1 : list B) : (term430 A B f a0 a1) = (term430 A B f a0 a1).
Proof. exact (fun_ext (fun l : list A => @lem1198857 A B f l a0 a1)). Qed.
Lemma lem1198859 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1198861 {A B : Type'} (f : A -> B) (a0 : B) (a1 : list B) : (term431 A B f a0 a1) = (term431 A B f a0 a1).
Proof. exact (MK_COMB (@lem1198859 A) (@lem1198858 A B f a0 a1)). Qed.
Lemma lem1198862 {A B : Type'} (l : list A) (f : A -> B) (a0 : B) (a1 : list B) (h1 : term433 A B l f a0 a1) : term431 A B f a0 a1.
Proof. exact (EQ_MP (@lem1198861 A B f a0 a1) (@lem1198749 A B l f a0 a1 h1)). Qed.
Lemma lem1198878 {A B : Type'} (_21507 : A -> B) (h1 : term134 A B) : term445 A B _21507.
Proof. exact (@lem1198784 A B h1 _21507). Qed.
Lemma lem1198879 {A B : Type'} (_21507 : A -> B) : (term445 A B _21507) = ((term423 A B _21507) = (@nil B)).
Proof. exact (eq_refl (term445 A B _21507)). Qed.
Lemma lem1198890 {A B : Type'} (_21511 : list A) (f : A -> B) (h1 : term436 A B f) : term446 A B f _21511.
Proof. exact (@lem1198804 A B f h1 _21511). Qed.
Lemma lem1198891 {A B : Type'} (f : A -> B) (_21511 : list A) : (term446 A B f _21511) = (term434 A B f _21511).
Proof. exact (eq_refl (term446 A B f _21511)). Qed.
Lemma lem1198893 {A B : Type'} (_21512 : B) (f : A -> B) (x : B -> A) (h1 : term292 A B f x) : term447 A B f x _21512.
Proof. exact (@lem1198811 A B f x h1 _21512). Qed.
Lemma lem1198894 {A B : Type'} (f : A -> B) (x : B -> A) (_21512 : B) : (term447 A B f x _21512) = ((term440 A B f x _21512) = _21512).
Proof. exact (eq_refl (term447 A B f x _21512)). Qed.
Lemma lem1198911 {A B : Type'} (_21518 : A -> B) (h1 : term134 A B) : term448 A B _21518.
Proof. exact (@lem1198851 A B h1 _21518). Qed.
Lemma lem1198912 {A B : Type'} (_21518 : A -> B) : (term448 A B _21518) = (term420 A B _21518).
Proof. exact (eq_refl (term448 A B _21518)). Qed.
Lemma lem1198913 {A B : Type'} (_21518 : A -> B) (h1 : term134 A B) : term420 A B _21518.
Proof. exact (EQ_MP (@lem1198912 A B _21518) (@lem1198911 A B _21518 h1)). Qed.
Lemma lem1198914 {A B : Type'} (_21518 : A -> B) (_21519 : A) (h1 : term134 A B) : term449 A B _21518 _21519.
Proof. exact (@lem1198913 A B _21518 h1 _21519). Qed.
Lemma lem1198915 {A B : Type'} (_21519 : A) (_21518 : A -> B) : (term449 A B _21518 _21519) = (term418 A B _21519 _21518).
Proof. exact (eq_refl (term449 A B _21518 _21519)). Qed.
Lemma lem1198916 {A B : Type'} (_21519 : A) (_21518 : A -> B) (h1 : term134 A B) : term418 A B _21519 _21518.
Proof. exact (EQ_MP (@lem1198915 A B _21519 _21518) (@lem1198914 A B _21518 _21519 h1)). Qed.
Lemma lem1198917 {A B : Type'} (_21519 : A) (_21518 : A -> B) (_21520 : list A) (h1 : term134 A B) : term450 A B _21519 _21518 _21520.
Proof. exact (@lem1198916 A B _21519 _21518 h1 _21520). Qed.
Lemma lem1198918 {A B : Type'} (_21519 : A) (_21518 : A -> B) (_21520 : list A) : (term450 A B _21519 _21518 _21520) = ((term409 A B _21518 _21519 _21520) = (term415 A B _21519 _21518 _21520)).
Proof. exact (eq_refl (term450 A B _21519 _21518 _21520)). Qed.
Lemma lem1198920 {A B : Type'} (_21521 : list A) (l : list A) (f : A -> B) (a0 : B) (a1 : list B) (h1 : term433 A B l f a0 a1) : term451 A B f a0 a1 _21521.
Proof. exact (@lem1198862 A B l f a0 a1 h1 _21521). Qed.
Lemma lem1198921 {A B : Type'} (f : A -> B) (_21521 : list A) (a0 : B) (a1 : list B) : (term451 A B f a0 a1 _21521) = (term429 A B f _21521 a0 a1).
Proof. exact (eq_refl (term451 A B f a0 a1 _21521)). Qed.
Lemma lem1198934 {A B : Type'} (_21511 : list A) (f : A -> B) (h1 : term436 A B f) : term434 A B f _21511.
Proof. exact (EQ_MP (@lem1198891 A B f _21511) (@lem1198890 A B _21511 f h1)). Qed.
Lemma lem1198946 {A B : Type'} (l : list A) (f : A -> B) (a0 : B) (a1 : list B) (h1 : term433 A B l f a0 a1) : (term223 A B f l) = a1.
Proof. exact (proj1 (@lem1198748 A B l f a0 a1 h1)). Qed.
Lemma lem1198948 {A B : Type'} (_21521 : list A) (l : list A) (f : A -> B) (a0 : B) (a1 : list B) (h1 : term433 A B l f a0 a1) : term429 A B f _21521 a0 a1.
Proof. exact (EQ_MP (@lem1198921 A B f _21521 a0 a1) (@lem1198920 A B _21521 l f a0 a1 h1)). Qed.
Lemma lem1198949 {A B : Type'} (l : list A) (f : A -> B) (a0 : B) (a1 : list B) (h1 : term433 A B l f a0 a1) : a1 = (term223 A B f l).
Proof. exact (SYM (@lem1198946 A B l f a0 a1 h1)). Qed.
Lemma lem1199034 {A B : Type'} (f : A -> B) (_21521 : list A) (a0 : B) : (term452 A B f _21521 a0) = (term452 A B f _21521 a0).
Proof. exact (eq_refl (term452 A B f _21521 a0)). Qed.
Lemma lem1199035 {A B : Type'} (_21521 : list A) (l : list A) (f : A -> B) (a0 : B) (a1 : list B) (h1 : term433 A B l f a0 a1) : (term453 A B f _21521 a0 a1) = (term454 A B _21521 a0 f l).
Proof. exact (MK_COMB (@lem1199034 A B f _21521 a0) (@lem1198949 A B l f a0 a1 h1)). Qed.
Lemma lem1199036 {A B : Type'} (_21521 : list A) (a0 : B) (f : A -> B) (l : list A) : (term454 A B _21521 a0 f l) = (term455 A B _21521 a0 f l).
Proof. exact (eq_refl (term454 A B _21521 a0 f l)). Qed.
Lemma lem1199037 {A B : Type'} (f : A -> B) (_21521 : list A) (a0 : B) (a1 : list B) : (term456 A B f _21521 a0 a1) = (term456 A B f _21521 a0 a1).
Proof. exact (eq_refl (term456 A B f _21521 a0 a1)). Qed.
Lemma lem1199038 {A B : Type'} (a1 : list B) (_21521 : list A) (a0 : B) (f : A -> B) (l : list A) : ((term453 A B f _21521 a0 a1) = (term454 A B _21521 a0 f l)) = ((term453 A B f _21521 a0 a1) = (term455 A B _21521 a0 f l)).
Proof. exact (MK_COMB (@lem1199037 A B f _21521 a0 a1) (@lem1199036 A B _21521 a0 f l)). Qed.
Lemma lem1199039 {A B : Type'} (f : A -> B) (_21521 : list A) (a0 : B) (a1 : list B) : (term453 A B f _21521 a0 a1) = (term429 A B f _21521 a0 a1).
Proof. exact (eq_refl (term453 A B f _21521 a0 a1)). Qed.
Lemma lem1199040 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1199041 {A B : Type'} (f : A -> B) (_21521 : list A) (a0 : B) (a1 : list B) : (term456 A B f _21521 a0 a1) = (term457 A B f _21521 a0 a1).
Proof. exact (MK_COMB (@lem1199040) (@lem1199039 A B f _21521 a0 a1)). Qed.
Lemma lem1199042 {A B : Type'} (_21521 : list A) (a0 : B) (f : A -> B) (l : list A) : (term455 A B _21521 a0 f l) = (term455 A B _21521 a0 f l).
Proof. exact (eq_refl (term455 A B _21521 a0 f l)). Qed.
Lemma lem1199043 {A B : Type'} (a1 : list B) (_21521 : list A) (a0 : B) (f : A -> B) (l : list A) : ((term453 A B f _21521 a0 a1) = (term455 A B _21521 a0 f l)) = ((term429 A B f _21521 a0 a1) = (term455 A B _21521 a0 f l)).
Proof. exact (MK_COMB (@lem1199041 A B f _21521 a0 a1) (@lem1199042 A B _21521 a0 f l)). Qed.
Lemma lem1199044 {A B : Type'} (a1 : list B) (_21521 : list A) (a0 : B) (f : A -> B) (l : list A) : ((term453 A B f _21521 a0 a1) = (term454 A B _21521 a0 f l)) = ((term429 A B f _21521 a0 a1) = (term455 A B _21521 a0 f l)).
Proof. exact (TRANS (@lem1199038 A B a1 _21521 a0 f l) (@lem1199043 A B a1 _21521 a0 f l)). Qed.
Lemma lem1199045 {A B : Type'} (_21521 : list A) (l : list A) (f : A -> B) (a0 : B) (a1 : list B) (h1 : term433 A B l f a0 a1) : (term429 A B f _21521 a0 a1) = (term455 A B _21521 a0 f l).
Proof. exact (EQ_MP (@lem1199044 A B a1 _21521 a0 f l) (@lem1199035 A B _21521 l f a0 a1 h1)). Qed.
Lemma lem1199046 {A B : Type'} (_21521 : list A) (l : list A) (f : A -> B) (a0 : B) (a1 : list B) (h1 : term433 A B l f a0 a1) : term455 A B _21521 a0 f l.
Proof. exact (EQ_MP (@lem1199045 A B _21521 l f a0 a1 h1) (@lem1198948 A B _21521 l f a0 a1 h1)). Qed.
Lemma lem1199226 {A B : Type'} (_21507 : A -> B) (h1 : term134 A B) : (term423 A B _21507) = (@nil B).
Proof. exact (EQ_MP (@lem1198879 A B _21507) (@lem1198878 A B _21507 h1)). Qed.
Lemma lem1199227 {A B : Type'} (_21507 : A -> B) (h1 : term134 A B) : (term423 A B _21507) = (@nil B).
Proof. exact (@lem1199226 A B _21507 h1). Qed.
Lemma lem1199228 {A B : Type'} (f : A -> B) (h1 : term134 A B) : (term423 A B f) = (@nil B).
Proof. exact (@lem1199227 A B f h1). Qed.
Lemma lem1199229 {A B : Type'} (f : A -> B) (h1 : term134 A B) : term458 A B f.
Proof. exact (fun h0 : term459 A B f => @lem1199228 A B f h1). Qed.
Lemma lem1199231 (p : Prop) : (term244 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1199232 {A B : Type'} (f : A -> B) : (term458 A B f) = ((term423 A B f) = (@nil B)).
Proof. exact (@lem1199231 ((term423 A B f) = (@nil B))). Qed.
Lemma lem1199233 {A B : Type'} (f : A -> B) (h1 : term134 A B) : (term423 A B f) = (@nil B).
Proof. exact (EQ_MP (@lem1199232 A B f) (@lem1199229 A B f h1)). Qed.
Lemma lem1199236 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1199238 {A B : Type'} (f : A -> B) (_21511 : list A) : (term434 A B f _21511) = (term460 A B f _21511).
Proof. exact (@lem1199236 ((term223 A B f _21511) = (@nil B))). Qed.
Lemma lem1199241 {A B : Type'} (_21511 : list A) (f : A -> B) (h1 : term436 A B f) : term460 A B f _21511.
Proof. exact (EQ_MP (@lem1199238 A B f _21511) (@lem1198934 A B _21511 f h1)). Qed.
Lemma lem1199242 {A B : Type'} (_21511 : list A) (f : A -> B) (h1 : term436 A B f) : term460 A B f _21511.
Proof. exact (@lem1199241 A B _21511 f h1). Qed.
Lemma lem1199243 {A B : Type'} (f : A -> B) (h1 : term436 A B f) : term461 A B f.
Proof. exact (@lem1199242 A B (@nil A) f h1). Qed.
Lemma lem1199246 {A B : Type'} (f : A -> B) (h1 : term436 A B f) (h2 : term134 A B) : False.
Proof. exact (@lem1199243 A B f h1 (@lem1199233 A B f h2)). Qed.
Lemma lem1199247 {A B : Type'} (f : A -> B) (h1 : term436 A B f) (h2 : term134 A B) : term247.
Proof. exact (fun h0 : ~ False => @lem1199246 A B f h1 h2). Qed.
Lemma lem1199249 (p : Prop) : (term244 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1199250 : term247 = False.
Proof. exact (@lem1199249 False). Qed.
Lemma lem1199251 {A B : Type'} (f : A -> B) (h1 : term436 A B f) (h2 : term134 A B) : False.
Proof. exact (EQ_MP (@lem1199250) (@lem1199247 A B f h1 h2)). Qed.
Lemma lem1199327 {B : Type'} : (@I (B -> (list B) -> list B)) = (@I (B -> (list B) -> list B)).
Proof. exact (eq_refl (@I (B -> (list B) -> list B))). Qed.
Lemma lem1199328 {B : Type'} (_21596 : type1397 B) (_21598 : type1397 B) (h1 : _21596 = _21598) : _21596 = _21598.
Proof. exact (h1). Qed.
Lemma lem1199329 {B : Type'} (_21597 : B) (_21599 : B) (h1 : _21597 = _21599) : _21597 = _21599.
Proof. exact (h1). Qed.
Lemma lem1199330 {B : Type'} (_21596 : type1397 B) (_21598 : type1397 B) (h1 : _21596 = _21598) : (@I (B -> (list B) -> list B) _21596) = (@I (B -> (list B) -> list B) _21598).
Proof. exact (MK_COMB (@lem1199327 B) (@lem1199328 B _21596 _21598 h1)). Qed.
Lemma lem1199331 {B : Type'} (_21597 : B) (_21599 : B) (_21596 : type1397 B) (_21598 : type1397 B) (h1 : _21597 = _21599) (h2 : _21596 = _21598) : (@I (B -> (list B) -> list B) _21596 _21597) = (@I (B -> (list B) -> list B) _21598 _21599).
Proof. exact (MK_COMB (@lem1199330 B _21596 _21598 h2) (@lem1199329 B _21597 _21599 h1)). Qed.
Lemma lem1199332 {B : Type'} (_21596 : type1397 B) (_21598 : type1397 B) (_21597 : B) (_21599 : B) (h1 : _21597 = _21599) : term462 B _21596 _21597 _21598 _21599.
Proof. exact (fun h0 : _21596 = _21598 => @lem1199331 B _21597 _21599 _21596 _21598 h1 h0). Qed.
Lemma lem1199334 (a : Prop) (b : Prop) : (a -> b) = (term463 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1199335 {B : Type'} (_21596 : type1397 B) (_21597 : B) (_21598 : type1397 B) (_21599 : B) : (term462 B _21596 _21597 _21598 _21599) = (term464 B _21596 _21597 _21598 _21599).
Proof. exact (@lem1199334 (_21596 = _21598) ((@I (B -> (list B) -> list B) _21596 _21597) = (@I (B -> (list B) -> list B) _21598 _21599))). Qed.
Lemma lem1199336 {B : Type'} (_21596 : type1397 B) (_21598 : type1397 B) (_21597 : B) (_21599 : B) (h1 : _21597 = _21599) : term464 B _21596 _21597 _21598 _21599.
Proof. exact (EQ_MP (@lem1199335 B _21596 _21597 _21598 _21599) (@lem1199332 B _21596 _21598 _21597 _21599 h1)). Qed.
Lemma lem1199337 {B : Type'} (_21596 : type1397 B) (_21597 : B) (_21598 : type1397 B) (_21599 : B) : term465 B _21596 _21597 _21598 _21599.
Proof. exact (fun h0 : _21597 = _21599 => @lem1199336 B _21596 _21598 _21597 _21599 h0). Qed.
Lemma lem1199339 (a : Prop) (b : Prop) : (a -> b) = (term463 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1199340 {B : Type'} (_21596 : type1397 B) (_21597 : B) (_21598 : type1397 B) (_21599 : B) : (term465 B _21596 _21597 _21598 _21599) = (term466 B _21596 _21597 _21598 _21599).
Proof. exact (@lem1199339 (_21597 = _21599) (term464 B _21596 _21597 _21598 _21599)). Qed.
Lemma lem1199341 {B : Type'} (_21596 : type1397 B) (_21597 : B) (_21598 : type1397 B) (_21599 : B) : term466 B _21596 _21597 _21598 _21599.
Proof. exact (EQ_MP (@lem1199340 B _21596 _21597 _21598 _21599) (@lem1199337 B _21596 _21597 _21598 _21599)). Qed.
Lemma lem1199357 {B : Type'} : (@I ((list B) -> list B)) = (@I ((list B) -> list B)).
Proof. exact (eq_refl (@I ((list B) -> list B))). Qed.
Lemma lem1199358 {B : Type'} (_21604 : type1138 B) (_21606 : type1138 B) (h1 : _21604 = _21606) : _21604 = _21606.
Proof. exact (h1). Qed.
Lemma lem1199359 {B : Type'} (_21605 : list B) (_21607 : list B) (h1 : _21605 = _21607) : _21605 = _21607.
Proof. exact (h1). Qed.
Lemma lem1199360 {B : Type'} (_21604 : type1138 B) (_21606 : type1138 B) (h1 : _21604 = _21606) : (@I ((list B) -> list B) _21604) = (@I ((list B) -> list B) _21606).
Proof. exact (MK_COMB (@lem1199357 B) (@lem1199358 B _21604 _21606 h1)). Qed.
Lemma lem1199361 {B : Type'} (_21604 : type1138 B) (_21606 : type1138 B) (_21605 : list B) (_21607 : list B) (h1 : _21604 = _21606) (h2 : _21605 = _21607) : (@I ((list B) -> list B) _21604 _21605) = (@I ((list B) -> list B) _21606 _21607).
Proof. exact (MK_COMB (@lem1199360 B _21604 _21606 h1) (@lem1199359 B _21605 _21607 h2)). Qed.
Lemma lem1199362 {B : Type'} (_21605 : list B) (_21607 : list B) (_21604 : type1138 B) (_21606 : type1138 B) (h1 : _21604 = _21606) : term467 B _21604 _21605 _21606 _21607.
Proof. exact (fun h0 : _21605 = _21607 => @lem1199361 B _21604 _21606 _21605 _21607 h1 h0). Qed.
Lemma lem1199364 (a : Prop) (b : Prop) : (a -> b) = (term463 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1199365 {B : Type'} (_21604 : type1138 B) (_21605 : list B) (_21606 : type1138 B) (_21607 : list B) : (term467 B _21604 _21605 _21606 _21607) = (term468 B _21604 _21605 _21606 _21607).
Proof. exact (@lem1199364 (_21605 = _21607) ((@I ((list B) -> list B) _21604 _21605) = (@I ((list B) -> list B) _21606 _21607))). Qed.
Lemma lem1199366 {B : Type'} (_21605 : list B) (_21607 : list B) (_21604 : type1138 B) (_21606 : type1138 B) (h1 : _21604 = _21606) : term468 B _21604 _21605 _21606 _21607.
Proof. exact (EQ_MP (@lem1199365 B _21604 _21605 _21606 _21607) (@lem1199362 B _21605 _21607 _21604 _21606 h1)). Qed.
Lemma lem1199367 {B : Type'} (_21604 : type1138 B) (_21605 : list B) (_21606 : type1138 B) (_21607 : list B) : term469 B _21604 _21605 _21606 _21607.
Proof. exact (fun h0 : _21604 = _21606 => @lem1199366 B _21605 _21607 _21604 _21606 h0). Qed.
Lemma lem1199369 (a : Prop) (b : Prop) : (a -> b) = (term463 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1199370 {B : Type'} (_21604 : type1138 B) (_21605 : list B) (_21606 : type1138 B) (_21607 : list B) : (term469 B _21604 _21605 _21606 _21607) = (term470 B _21604 _21605 _21606 _21607).
Proof. exact (@lem1199369 (_21604 = _21606) (term468 B _21604 _21605 _21606 _21607)). Qed.
Lemma lem1199371 {B : Type'} (_21604 : type1138 B) (_21605 : list B) (_21606 : type1138 B) (_21607 : list B) : term470 B _21604 _21605 _21606 _21607.
Proof. exact (EQ_MP (@lem1199370 B _21604 _21605 _21606 _21607) (@lem1199367 B _21604 _21605 _21606 _21607)). Qed.
Lemma lem1199411 {B : Type'} (x : list B) (y : list B) (z : list B) : term471 B x y z.
Proof. exact (@lem21385 (list B) x y z). Qed.
Lemma lem1199431 {A B : Type'} (_21519 : A) (_21518 : A -> B) (_21520 : list A) (h1 : term134 A B) : (term409 A B _21518 _21519 _21520) = (term415 A B _21519 _21518 _21520).
Proof. exact (EQ_MP (@lem1198918 A B _21519 _21518 _21520) (@lem1198917 A B _21519 _21518 _21520 h1)). Qed.
Lemma lem1199432 {A B : Type'} (_21519 : A) (_21518 : A -> B) (_21520 : list A) (h1 : term134 A B) : (term409 A B _21518 _21519 _21520) = (term415 A B _21519 _21518 _21520).
Proof. exact (@lem1199431 A B _21519 _21518 _21520 h1). Qed.
Lemma lem1199433 {A B : Type'} (x : B -> A) (a0 : B) (f : A -> B) (l : list A) (h1 : term134 A B) : (term472 A B f x a0 l) = (term473 A B x a0 f l).
Proof. exact (@lem1199432 A B (@I (B -> A) x a0) f l h1). Qed.
Lemma lem1199434 {A B : Type'} (x : B -> A) (a0 : B) (f : A -> B) (l : list A) (h1 : term134 A B) : term474 A B x a0 f l.
Proof. exact (fun h0 : term475 A B x a0 f l => @lem1199433 A B x a0 f l h1). Qed.
Lemma lem1199436 (p : Prop) : (term244 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1199437 {A B : Type'} (x : B -> A) (a0 : B) (f : A -> B) (l : list A) : (term474 A B x a0 f l) = ((term472 A B f x a0 l) = (term473 A B x a0 f l)).
Proof. exact (@lem1199436 ((term472 A B f x a0 l) = (term473 A B x a0 f l))). Qed.
Lemma lem1199438 {A B : Type'} (x : B -> A) (a0 : B) (f : A -> B) (l : list A) (h1 : term134 A B) : (term472 A B f x a0 l) = (term473 A B x a0 f l).
Proof. exact (EQ_MP (@lem1199437 A B x a0 f l) (@lem1199434 A B x a0 f l h1)). Qed.
Lemma lem1199440 {B : Type'} (x : list B) : x = x.
Proof. exact (@lem21386 (list B) x). Qed.
Lemma lem1199441 {B : Type'} (x : list B) : x = x.
Proof. exact (@lem1199440 B x). Qed.
Lemma lem1199442 {A B : Type'} (f : A -> B) (x : B -> A) (a0 : B) (l : list A) : (term472 A B f x a0 l) = (term472 A B f x a0 l).
Proof. exact (@lem1199441 B (term472 A B f x a0 l)). Qed.
Lemma lem1199443 {A B : Type'} (f : A -> B) (x : B -> A) (a0 : B) (l : list A) : term476 A B f x a0 l.
Proof. exact (fun h0 : term477 A B f x a0 l => @lem1199442 A B f x a0 l). Qed.
Lemma lem1199445 (p : Prop) : (term244 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1199446 {A B : Type'} (f : A -> B) (x : B -> A) (a0 : B) (l : list A) : (term476 A B f x a0 l) = ((term472 A B f x a0 l) = (term472 A B f x a0 l)).
Proof. exact (@lem1199445 ((term472 A B f x a0 l) = (term472 A B f x a0 l))). Qed.
Lemma lem1199447 {A B : Type'} (f : A -> B) (x : B -> A) (a0 : B) (l : list A) : (term472 A B f x a0 l) = (term472 A B f x a0 l).
Proof. exact (EQ_MP (@lem1199446 A B f x a0 l) (@lem1199443 A B f x a0 l)). Qed.
Lemma lem1199465 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1199466 {B : Type'} (y : list B) (x : list B) (z : list B) : (term478 B x y z) = (term479 B y x z).
Proof. exact (@lem1199465 (y = z) (term480 B x z)). Qed.
Lemma lem1199476 {B : Type'} (x : list B) (y : list B) : (term481 B x y) = (term481 B x y).
Proof. exact (eq_refl (term481 B x y)). Qed.
Lemma lem1199477 {B : Type'} (y : list B) (x : list B) (z : list B) : (term471 B x y z) = (term482 B y x z).
Proof. exact (MK_COMB (@lem1199476 B x y) (@lem1199466 B y x z)). Qed.
Lemma lem1199481 (q : Prop) (p : Prop) (r : Prop) : (term483 p q r) = (term483 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1199482 {B : Type'} (y : list B) (x : list B) (z : list B) : (term482 B y x z) = (term484 B y x z).
Proof. exact (@lem1199481 (y = z) (term480 B x y) (term480 B x z)). Qed.
Lemma lem1199504 {B : Type'} (y : list B) (x : list B) (z : list B) : (term471 B x y z) = (term484 B y x z).
Proof. exact (TRANS (@lem1199477 B y x z) (@lem1199482 B y x z)). Qed.
Lemma lem1199505 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1199506 {B : Type'} (y : list B) (x : list B) (z : list B) : (term485 B x y z) = (term486 B y x z).
Proof. exact (MK_COMB (@lem1199505) (@lem1199504 B y x z)). Qed.
Lemma lem1199528 {B : Type'} (y : list B) (x : list B) (z : list B) : (term484 B y x z) = (term484 B y x z).
Proof. exact (eq_refl (term484 B y x z)). Qed.
Lemma lem1199529 {B : Type'} (y : list B) (x : list B) (z : list B) : ((term471 B x y z) = (term484 B y x z)) = ((term484 B y x z) = (term484 B y x z)).
Proof. exact (MK_COMB (@lem1199506 B y x z) (@lem1199528 B y x z)). Qed.
Lemma lem1199531 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1199532 (x : Prop) : (x = x) = True.
Proof. exact (@lem1199531 Prop x). Qed.
Lemma lem1199533 {B : Type'} (y : list B) (x : list B) (z : list B) : ((term484 B y x z) = (term484 B y x z)) = True.
Proof. exact (@lem1199532 (term484 B y x z)). Qed.
Lemma lem1199534 {B : Type'} (y : list B) (x : list B) (z : list B) : ((term471 B x y z) = (term484 B y x z)) = True.
Proof. exact (TRANS (@lem1199529 B y x z) (@lem1199533 B y x z)). Qed.
Lemma lem1199535 {B : Type'} (y : list B) (x : list B) (z : list B) : True = ((term471 B x y z) = (term484 B y x z)).
Proof. exact (SYM (@lem1199534 B y x z)). Qed.
Lemma lem1199536 {B : Type'} (y : list B) (x : list B) (z : list B) : (term471 B x y z) = (term484 B y x z).
Proof. exact (EQ_MP (@lem1199535 B y x z) (@lem0)). Qed.
Lemma lem1199537 {B : Type'} (y : list B) (x : list B) (z : list B) : term484 B y x z.
Proof. exact (EQ_MP (@lem1199536 B y x z) (@lem1199411 B x y z)). Qed.
Lemma lem1199539 (b : Prop) (a : Prop) : (a \/ b) = (term487 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1199540 {B : Type'} (x : list B) (y : list B) (z : list B) : (term484 B y x z) = (term488 B x y z).
Proof. exact (@lem1199539 (term489 B y x z) (y = z)). Qed.
Lemma lem1199542 (a : Prop) (b : Prop) : (term490 a b) = (term491 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1199543 {B : Type'} (y : list B) (x : list B) (z : list B) : (term492 B y x z) = (term493 B y x z).
Proof. exact (@lem1199542 (term480 B x y) (term480 B x z)). Qed.
Lemma lem1199545 (a : Prop) : (term494 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1199546 {B : Type'} (x : list B) (y : list B) : (term495 B x y) = (x = y).
Proof. exact (@lem1199545 (x = y)). Qed.
Lemma lem1199547 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1199548 {B : Type'} (x : list B) (y : list B) : (term496 B x y) = (term497 B x y).
Proof. exact (MK_COMB (@lem1199547) (@lem1199546 B x y)). Qed.
Lemma lem1199550 (a : Prop) : (term494 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1199551 {B : Type'} (x : list B) (z : list B) : (term495 B x z) = (x = z).
Proof. exact (@lem1199550 (x = z)). Qed.
Lemma lem1199552 {B : Type'} (y : list B) (x : list B) (z : list B) : (term493 B y x z) = (term498 B y x z).
Proof. exact (MK_COMB (@lem1199548 B x y) (@lem1199551 B x z)). Qed.
Lemma lem1199553 {B : Type'} (y : list B) (x : list B) (z : list B) : (term492 B y x z) = (term498 B y x z).
Proof. exact (TRANS (@lem1199543 B y x z) (@lem1199552 B y x z)). Qed.
Lemma lem1199554 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1199555 {B : Type'} (y : list B) (x : list B) (z : list B) : (term499 B y x z) = (term500 B y x z).
Proof. exact (MK_COMB (@lem1199554) (@lem1199553 B y x z)). Qed.
Lemma lem1199556 {B : Type'} (y : list B) (z : list B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1199557 {B : Type'} (x : list B) (y : list B) (z : list B) : (term488 B x y z) = (term501 B x y z).
Proof. exact (MK_COMB (@lem1199555 B y x z) (@lem1199556 B y z)). Qed.
Lemma lem1199558 {B : Type'} (x : list B) (y : list B) (z : list B) : (term484 B y x z) = (term501 B x y z).
Proof. exact (TRANS (@lem1199540 B x y z) (@lem1199557 B x y z)). Qed.
Lemma lem1199560 {A B : Type'} (f : A -> B) (x : B -> A) (a0 : B) (l : list A) (h1 : term134 A B) : term502 A B f x a0 l.
Proof. exact (conj (@lem1199438 A B x a0 f l h1) (@lem1199447 A B f x a0 l)). Qed.
Lemma lem1199562 {B : Type'} (x : list B) (y : list B) (z : list B) : term501 B x y z.
Proof. exact (EQ_MP (@lem1199558 B x y z) (@lem1199537 B y x z)). Qed.
Lemma lem1199563 {B : Type'} (x : list B) (y : list B) (z : list B) : term501 B x y z.
Proof. exact (@lem1199562 B x y z). Qed.
Lemma lem1199564 {A B : Type'} (f : A -> B) (x : B -> A) (a0 : B) (l : list A) : term503 A B f x a0 l.
Proof. exact (@lem1199563 B (term472 A B f x a0 l) (term473 A B x a0 f l) (term472 A B f x a0 l)). Qed.
Lemma lem1199567 {A B : Type'} (f : A -> B) (x : B -> A) (a0 : B) (l : list A) (h1 : term134 A B) : (term473 A B x a0 f l) = (term472 A B f x a0 l).
Proof. exact (@lem1199564 A B f x a0 l (@lem1199560 A B f x a0 l h1)). Qed.
Lemma lem1199568 {A B : Type'} (f : A -> B) (x : B -> A) (a0 : B) (l : list A) (h1 : term134 A B) : (term473 A B x a0 f l) = (term472 A B f x a0 l).
Proof. exact (@lem1199567 A B f x a0 l h1). Qed.
Lemma lem1199569 {A B : Type'} (f : A -> B) (x : B -> A) (a0 : B) (l : list A) (h1 : term134 A B) : term504 A B f x a0 l.
Proof. exact (fun h0 : term505 A B f x a0 l => @lem1199568 A B f x a0 l h1). Qed.
Lemma lem1199571 (p : Prop) : (term244 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1199572 {A B : Type'} (f : A -> B) (x : B -> A) (a0 : B) (l : list A) : (term504 A B f x a0 l) = ((term473 A B x a0 f l) = (term472 A B f x a0 l)).
Proof. exact (@lem1199571 ((term473 A B x a0 f l) = (term472 A B f x a0 l))). Qed.
Lemma lem1199573 {A B : Type'} (f : A -> B) (x : B -> A) (a0 : B) (l : list A) (h1 : term134 A B) : (term473 A B x a0 f l) = (term472 A B f x a0 l).
Proof. exact (EQ_MP (@lem1199572 A B f x a0 l) (@lem1199569 A B f x a0 l h1)). Qed.
Lemma lem1199575 {A B : Type'} (_21512 : B) (f : A -> B) (x : B -> A) (h1 : term292 A B f x) : (term440 A B f x _21512) = _21512.
Proof. exact (EQ_MP (@lem1198894 A B f x _21512) (@lem1198893 A B _21512 f x h1)). Qed.
Lemma lem1199576 {A B : Type'} (_21512 : B) (f : A -> B) (x : B -> A) (h1 : term292 A B f x) : (term440 A B f x _21512) = _21512.
Proof. exact (@lem1199575 A B _21512 f x h1). Qed.
Lemma lem1199577 {A B : Type'} (a0 : B) (f : A -> B) (x : B -> A) (h1 : term292 A B f x) : (term440 A B f x a0) = a0.
Proof. exact (@lem1199576 A B a0 f x h1). Qed.
Lemma lem1199578 {A B : Type'} (a0 : B) (f : A -> B) (x : B -> A) (h1 : term292 A B f x) : term506 A B f x a0.
Proof. exact (fun h0 : term507 A B f x a0 => @lem1199577 A B a0 f x h1). Qed.
Lemma lem1199580 (p : Prop) : (term244 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1199581 {A B : Type'} (f : A -> B) (x : B -> A) (a0 : B) : (term506 A B f x a0) = ((term440 A B f x a0) = a0).
Proof. exact (@lem1199580 ((term440 A B f x a0) = a0)). Qed.
Lemma lem1199582 {A B : Type'} (a0 : B) (f : A -> B) (x : B -> A) (h1 : term292 A B f x) : (term440 A B f x a0) = a0.
Proof. exact (EQ_MP (@lem1199581 A B f x a0) (@lem1199578 A B a0 f x h1)). Qed.
Lemma lem1199584 {B : Type'} (x : type1397 B) : x = x.
Proof. exact (@lem21386 (type1397 B) x). Qed.
Lemma lem1199585 {B : Type'} (x : type1397 B) : x = x.
Proof. exact (@lem1199584 B x). Qed.
Lemma lem1199586 {B : Type'} : (@cons B) = (@cons B).
Proof. exact (@lem1199585 B (@cons B)). Qed.
Lemma lem1199587 {B : Type'} : term508 B.
Proof. exact (fun h0 : term509 B => @lem1199586 B). Qed.
Lemma lem1199589 (p : Prop) : (term244 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1199590 {B : Type'} : (term508 B) = ((@cons B) = (@cons B)).
Proof. exact (@lem1199589 ((@cons B) = (@cons B))). Qed.
Lemma lem1199591 {B : Type'} : (@cons B) = (@cons B).
Proof. exact (EQ_MP (@lem1199590 B) (@lem1199587 B)). Qed.
Lemma lem1199609 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1199610 {B : Type'} (_21597 : B) (_21599 : B) (_21596 : type1397 B) (_21598 : type1397 B) : (term464 B _21596 _21597 _21598 _21599) = (term510 B _21597 _21599 _21596 _21598).
Proof. exact (@lem1199609 ((@I (B -> (list B) -> list B) _21596 _21597) = (@I (B -> (list B) -> list B) _21598 _21599)) (term511 B _21596 _21598)). Qed.
Lemma lem1199620 {B : Type'} (_21597 : B) (_21599 : B) : (term512 B _21597 _21599) = (term512 B _21597 _21599).
Proof. exact (eq_refl (term512 B _21597 _21599)). Qed.
Lemma lem1199621 {B : Type'} (_21597 : B) (_21599 : B) (_21596 : type1397 B) (_21598 : type1397 B) : (term466 B _21596 _21597 _21598 _21599) = (term513 B _21597 _21599 _21596 _21598).
Proof. exact (MK_COMB (@lem1199620 B _21597 _21599) (@lem1199610 B _21597 _21599 _21596 _21598)). Qed.
Lemma lem1199625 (q : Prop) (p : Prop) (r : Prop) : (term483 p q r) = (term483 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1199626 {B : Type'} (_21597 : B) (_21599 : B) (_21596 : type1397 B) (_21598 : type1397 B) : (term513 B _21597 _21599 _21596 _21598) = (term514 B _21597 _21599 _21596 _21598).
Proof. exact (@lem1199625 ((@I (B -> (list B) -> list B) _21596 _21597) = (@I (B -> (list B) -> list B) _21598 _21599)) (term515 B _21597 _21599) (term511 B _21596 _21598)). Qed.
Lemma lem1199648 {B : Type'} (_21597 : B) (_21599 : B) (_21596 : type1397 B) (_21598 : type1397 B) : (term466 B _21596 _21597 _21598 _21599) = (term514 B _21597 _21599 _21596 _21598).
Proof. exact (TRANS (@lem1199621 B _21597 _21599 _21596 _21598) (@lem1199626 B _21597 _21599 _21596 _21598)). Qed.
Lemma lem1199649 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1199650 {B : Type'} (_21597 : B) (_21599 : B) (_21596 : type1397 B) (_21598 : type1397 B) : (term516 B _21596 _21597 _21598 _21599) = (term517 B _21597 _21599 _21596 _21598).
Proof. exact (MK_COMB (@lem1199649) (@lem1199648 B _21597 _21599 _21596 _21598)). Qed.
Lemma lem1199672 {B : Type'} (_21597 : B) (_21599 : B) (_21596 : type1397 B) (_21598 : type1397 B) : (term514 B _21597 _21599 _21596 _21598) = (term514 B _21597 _21599 _21596 _21598).
Proof. exact (eq_refl (term514 B _21597 _21599 _21596 _21598)). Qed.
Lemma lem1199673 {B : Type'} (_21597 : B) (_21599 : B) (_21596 : type1397 B) (_21598 : type1397 B) : ((term466 B _21596 _21597 _21598 _21599) = (term514 B _21597 _21599 _21596 _21598)) = ((term514 B _21597 _21599 _21596 _21598) = (term514 B _21597 _21599 _21596 _21598)).
Proof. exact (MK_COMB (@lem1199650 B _21597 _21599 _21596 _21598) (@lem1199672 B _21597 _21599 _21596 _21598)). Qed.
Lemma lem1199675 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1199676 (x : Prop) : (x = x) = True.
Proof. exact (@lem1199675 Prop x). Qed.
Lemma lem1199677 {B : Type'} (_21597 : B) (_21599 : B) (_21596 : type1397 B) (_21598 : type1397 B) : ((term514 B _21597 _21599 _21596 _21598) = (term514 B _21597 _21599 _21596 _21598)) = True.
Proof. exact (@lem1199676 (term514 B _21597 _21599 _21596 _21598)). Qed.
Lemma lem1199678 {B : Type'} (_21597 : B) (_21599 : B) (_21596 : type1397 B) (_21598 : type1397 B) : ((term466 B _21596 _21597 _21598 _21599) = (term514 B _21597 _21599 _21596 _21598)) = True.
Proof. exact (TRANS (@lem1199673 B _21597 _21599 _21596 _21598) (@lem1199677 B _21597 _21599 _21596 _21598)). Qed.
Lemma lem1199679 {B : Type'} (_21597 : B) (_21599 : B) (_21596 : type1397 B) (_21598 : type1397 B) : True = ((term466 B _21596 _21597 _21598 _21599) = (term514 B _21597 _21599 _21596 _21598)).
Proof. exact (SYM (@lem1199678 B _21597 _21599 _21596 _21598)). Qed.
Lemma lem1199680 {B : Type'} (_21597 : B) (_21599 : B) (_21596 : type1397 B) (_21598 : type1397 B) : (term466 B _21596 _21597 _21598 _21599) = (term514 B _21597 _21599 _21596 _21598).
Proof. exact (EQ_MP (@lem1199679 B _21597 _21599 _21596 _21598) (@lem0)). Qed.
Lemma lem1199681 {B : Type'} (_21597 : B) (_21599 : B) (_21596 : type1397 B) (_21598 : type1397 B) : term514 B _21597 _21599 _21596 _21598.
Proof. exact (EQ_MP (@lem1199680 B _21597 _21599 _21596 _21598) (@lem1199341 B _21596 _21597 _21598 _21599)). Qed.
Lemma lem1199683 (b : Prop) (a : Prop) : (a \/ b) = (term487 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1199684 {B : Type'} (_21596 : type1397 B) (_21597 : B) (_21598 : type1397 B) (_21599 : B) : (term514 B _21597 _21599 _21596 _21598) = (term518 B _21596 _21597 _21598 _21599).
Proof. exact (@lem1199683 (term519 B _21597 _21599 _21596 _21598) ((@I (B -> (list B) -> list B) _21596 _21597) = (@I (B -> (list B) -> list B) _21598 _21599))). Qed.
Lemma lem1199686 (a : Prop) (b : Prop) : (term490 a b) = (term491 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1199687 {B : Type'} (_21597 : B) (_21599 : B) (_21596 : type1397 B) (_21598 : type1397 B) : (term520 B _21597 _21599 _21596 _21598) = (term521 B _21597 _21599 _21596 _21598).
Proof. exact (@lem1199686 (term515 B _21597 _21599) (term511 B _21596 _21598)). Qed.
Lemma lem1199689 (a : Prop) : (term494 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1199690 {B : Type'} (_21597 : B) (_21599 : B) : (term522 B _21597 _21599) = (_21597 = _21599).
Proof. exact (@lem1199689 (_21597 = _21599)). Qed.
Lemma lem1199691 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1199692 {B : Type'} (_21597 : B) (_21599 : B) : (term523 B _21597 _21599) = (term524 B _21597 _21599).
Proof. exact (MK_COMB (@lem1199691) (@lem1199690 B _21597 _21599)). Qed.
Lemma lem1199694 (a : Prop) : (term494 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1199695 {B : Type'} (_21596 : type1397 B) (_21598 : type1397 B) : (term525 B _21596 _21598) = (_21596 = _21598).
Proof. exact (@lem1199694 (_21596 = _21598)). Qed.
Lemma lem1199696 {B : Type'} (_21597 : B) (_21599 : B) (_21596 : type1397 B) (_21598 : type1397 B) : (term521 B _21597 _21599 _21596 _21598) = (term526 B _21597 _21599 _21596 _21598).
Proof. exact (MK_COMB (@lem1199692 B _21597 _21599) (@lem1199695 B _21596 _21598)). Qed.
Lemma lem1199697 {B : Type'} (_21597 : B) (_21599 : B) (_21596 : type1397 B) (_21598 : type1397 B) : (term520 B _21597 _21599 _21596 _21598) = (term526 B _21597 _21599 _21596 _21598).
Proof. exact (TRANS (@lem1199687 B _21597 _21599 _21596 _21598) (@lem1199696 B _21597 _21599 _21596 _21598)). Qed.
Lemma lem1199698 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1199699 {B : Type'} (_21597 : B) (_21599 : B) (_21596 : type1397 B) (_21598 : type1397 B) : (term527 B _21597 _21599 _21596 _21598) = (term528 B _21597 _21599 _21596 _21598).
Proof. exact (MK_COMB (@lem1199698) (@lem1199697 B _21597 _21599 _21596 _21598)). Qed.
Lemma lem1199700 {B : Type'} (_21596 : type1397 B) (_21597 : B) (_21598 : type1397 B) (_21599 : B) : ((@I (B -> (list B) -> list B) _21596 _21597) = (@I (B -> (list B) -> list B) _21598 _21599)) = ((@I (B -> (list B) -> list B) _21596 _21597) = (@I (B -> (list B) -> list B) _21598 _21599)).
Proof. exact (eq_refl ((@I (B -> (list B) -> list B) _21596 _21597) = (@I (B -> (list B) -> list B) _21598 _21599))). Qed.
Lemma lem1199701 {B : Type'} (_21596 : type1397 B) (_21597 : B) (_21598 : type1397 B) (_21599 : B) : (term518 B _21596 _21597 _21598 _21599) = (term529 B _21596 _21597 _21598 _21599).
Proof. exact (MK_COMB (@lem1199699 B _21597 _21599 _21596 _21598) (@lem1199700 B _21596 _21597 _21598 _21599)). Qed.
Lemma lem1199702 {B : Type'} (_21596 : type1397 B) (_21597 : B) (_21598 : type1397 B) (_21599 : B) : (term514 B _21597 _21599 _21596 _21598) = (term529 B _21596 _21597 _21598 _21599).
Proof. exact (TRANS (@lem1199684 B _21596 _21597 _21598 _21599) (@lem1199701 B _21596 _21597 _21598 _21599)). Qed.
Lemma lem1199704 {A B : Type'} (a0 : B) (f : A -> B) (x : B -> A) (h1 : term292 A B f x) : term530 A B f x a0.
Proof. exact (conj (@lem1199582 A B a0 f x h1) (@lem1199591 B)). Qed.
Lemma lem1199706 {B : Type'} (_21596 : type1397 B) (_21597 : B) (_21598 : type1397 B) (_21599 : B) : term529 B _21596 _21597 _21598 _21599.
Proof. exact (EQ_MP (@lem1199702 B _21596 _21597 _21598 _21599) (@lem1199681 B _21597 _21599 _21596 _21598)). Qed.
Lemma lem1199707 {B : Type'} (_21596 : type1397 B) (_21597 : B) (_21598 : type1397 B) (_21599 : B) : term529 B _21596 _21597 _21598 _21599.
Proof. exact (@lem1199706 B _21596 _21597 _21598 _21599). Qed.
Lemma lem1199708 {A B : Type'} (f : A -> B) (x : B -> A) (a0 : B) : term531 A B f x a0.
Proof. exact (@lem1199707 B (@cons B) (term440 A B f x a0) (@cons B) a0). Qed.
Lemma lem1199711 {A B : Type'} (a0 : B) (f : A -> B) (x : B -> A) (h1 : term292 A B f x) : (term532 A B f x a0) = (@I (B -> (list B) -> list B) (@cons B) a0).
Proof. exact (@lem1199708 A B f x a0 (@lem1199704 A B a0 f x h1)). Qed.
Lemma lem1199712 {A B : Type'} (a0 : B) (f : A -> B) (x : B -> A) (h1 : term292 A B f x) : (term532 A B f x a0) = (@I (B -> (list B) -> list B) (@cons B) a0).
Proof. exact (@lem1199711 A B a0 f x h1). Qed.
Lemma lem1199713 {A B : Type'} (a0 : B) (f : A -> B) (x : B -> A) (h1 : term292 A B f x) : term533 A B f x a0.
Proof. exact (fun h0 : term534 A B f x a0 => @lem1199712 A B a0 f x h1). Qed.
Lemma lem1199715 (p : Prop) : (term244 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1199716 {A B : Type'} (f : A -> B) (x : B -> A) (a0 : B) : (term533 A B f x a0) = ((term532 A B f x a0) = (@I (B -> (list B) -> list B) (@cons B) a0)).
Proof. exact (@lem1199715 ((term532 A B f x a0) = (@I (B -> (list B) -> list B) (@cons B) a0))). Qed.
Lemma lem1199717 {A B : Type'} (a0 : B) (f : A -> B) (x : B -> A) (h1 : term292 A B f x) : (term532 A B f x a0) = (@I (B -> (list B) -> list B) (@cons B) a0).
Proof. exact (EQ_MP (@lem1199716 A B f x a0) (@lem1199713 A B a0 f x h1)). Qed.
Lemma lem1199719 {B : Type'} (x : list B) : x = x.
Proof. exact (@lem21386 (list B) x). Qed.
Lemma lem1199720 {B : Type'} (x : list B) : x = x.
Proof. exact (@lem1199719 B x). Qed.
Lemma lem1199721 {A B : Type'} (f : A -> B) (l : list A) : (term223 A B f l) = (term223 A B f l).
Proof. exact (@lem1199720 B (term223 A B f l)). Qed.
Lemma lem1199722 {A B : Type'} (f : A -> B) (l : list A) : term535 A B f l.
Proof. exact (fun h0 : term536 A B f l => @lem1199721 A B f l). Qed.
Lemma lem1199724 (p : Prop) : (term244 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1199725 {A B : Type'} (f : A -> B) (l : list A) : (term535 A B f l) = ((term223 A B f l) = (term223 A B f l)).
Proof. exact (@lem1199724 ((term223 A B f l) = (term223 A B f l))). Qed.
Lemma lem1199726 {A B : Type'} (f : A -> B) (l : list A) : (term223 A B f l) = (term223 A B f l).
Proof. exact (EQ_MP (@lem1199725 A B f l) (@lem1199722 A B f l)). Qed.
Lemma lem1199744 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1199745 {B : Type'} (_21604 : type1138 B) (_21606 : type1138 B) (_21605 : list B) (_21607 : list B) : (term468 B _21604 _21605 _21606 _21607) = (term537 B _21604 _21606 _21605 _21607).
Proof. exact (@lem1199744 ((@I ((list B) -> list B) _21604 _21605) = (@I ((list B) -> list B) _21606 _21607)) (term480 B _21605 _21607)). Qed.
Lemma lem1199755 {B : Type'} (_21604 : type1138 B) (_21606 : type1138 B) : (term538 B _21604 _21606) = (term538 B _21604 _21606).
Proof. exact (eq_refl (term538 B _21604 _21606)). Qed.
Lemma lem1199756 {B : Type'} (_21604 : type1138 B) (_21606 : type1138 B) (_21605 : list B) (_21607 : list B) : (term470 B _21604 _21605 _21606 _21607) = (term539 B _21604 _21606 _21605 _21607).
Proof. exact (MK_COMB (@lem1199755 B _21604 _21606) (@lem1199745 B _21604 _21606 _21605 _21607)). Qed.
Lemma lem1199760 (q : Prop) (p : Prop) (r : Prop) : (term483 p q r) = (term483 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1199761 {B : Type'} (_21604 : type1138 B) (_21606 : type1138 B) (_21605 : list B) (_21607 : list B) : (term539 B _21604 _21606 _21605 _21607) = (term540 B _21604 _21606 _21605 _21607).
Proof. exact (@lem1199760 ((@I ((list B) -> list B) _21604 _21605) = (@I ((list B) -> list B) _21606 _21607)) (term541 B _21604 _21606) (term480 B _21605 _21607)). Qed.
Lemma lem1199783 {B : Type'} (_21604 : type1138 B) (_21606 : type1138 B) (_21605 : list B) (_21607 : list B) : (term470 B _21604 _21605 _21606 _21607) = (term540 B _21604 _21606 _21605 _21607).
Proof. exact (TRANS (@lem1199756 B _21604 _21606 _21605 _21607) (@lem1199761 B _21604 _21606 _21605 _21607)). Qed.
Lemma lem1199784 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1199785 {B : Type'} (_21604 : type1138 B) (_21606 : type1138 B) (_21605 : list B) (_21607 : list B) : (term542 B _21604 _21605 _21606 _21607) = (term543 B _21604 _21606 _21605 _21607).
Proof. exact (MK_COMB (@lem1199784) (@lem1199783 B _21604 _21606 _21605 _21607)). Qed.
Lemma lem1199807 {B : Type'} (_21604 : type1138 B) (_21606 : type1138 B) (_21605 : list B) (_21607 : list B) : (term540 B _21604 _21606 _21605 _21607) = (term540 B _21604 _21606 _21605 _21607).
Proof. exact (eq_refl (term540 B _21604 _21606 _21605 _21607)). Qed.
Lemma lem1199808 {B : Type'} (_21604 : type1138 B) (_21606 : type1138 B) (_21605 : list B) (_21607 : list B) : ((term470 B _21604 _21605 _21606 _21607) = (term540 B _21604 _21606 _21605 _21607)) = ((term540 B _21604 _21606 _21605 _21607) = (term540 B _21604 _21606 _21605 _21607)).
Proof. exact (MK_COMB (@lem1199785 B _21604 _21606 _21605 _21607) (@lem1199807 B _21604 _21606 _21605 _21607)). Qed.
Lemma lem1199810 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1199811 (x : Prop) : (x = x) = True.
Proof. exact (@lem1199810 Prop x). Qed.
Lemma lem1199812 {B : Type'} (_21604 : type1138 B) (_21606 : type1138 B) (_21605 : list B) (_21607 : list B) : ((term540 B _21604 _21606 _21605 _21607) = (term540 B _21604 _21606 _21605 _21607)) = True.
Proof. exact (@lem1199811 (term540 B _21604 _21606 _21605 _21607)). Qed.
Lemma lem1199813 {B : Type'} (_21604 : type1138 B) (_21606 : type1138 B) (_21605 : list B) (_21607 : list B) : ((term470 B _21604 _21605 _21606 _21607) = (term540 B _21604 _21606 _21605 _21607)) = True.
Proof. exact (TRANS (@lem1199808 B _21604 _21606 _21605 _21607) (@lem1199812 B _21604 _21606 _21605 _21607)). Qed.
Lemma lem1199814 {B : Type'} (_21604 : type1138 B) (_21606 : type1138 B) (_21605 : list B) (_21607 : list B) : True = ((term470 B _21604 _21605 _21606 _21607) = (term540 B _21604 _21606 _21605 _21607)).
Proof. exact (SYM (@lem1199813 B _21604 _21606 _21605 _21607)). Qed.
Lemma lem1199815 {B : Type'} (_21604 : type1138 B) (_21606 : type1138 B) (_21605 : list B) (_21607 : list B) : (term470 B _21604 _21605 _21606 _21607) = (term540 B _21604 _21606 _21605 _21607).
Proof. exact (EQ_MP (@lem1199814 B _21604 _21606 _21605 _21607) (@lem0)). Qed.
Lemma lem1199816 {B : Type'} (_21604 : type1138 B) (_21606 : type1138 B) (_21605 : list B) (_21607 : list B) : term540 B _21604 _21606 _21605 _21607.
Proof. exact (EQ_MP (@lem1199815 B _21604 _21606 _21605 _21607) (@lem1199371 B _21604 _21605 _21606 _21607)). Qed.
Lemma lem1199818 (b : Prop) (a : Prop) : (a \/ b) = (term487 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1199819 {B : Type'} (_21604 : type1138 B) (_21605 : list B) (_21606 : type1138 B) (_21607 : list B) : (term540 B _21604 _21606 _21605 _21607) = (term544 B _21604 _21605 _21606 _21607).
Proof. exact (@lem1199818 (term545 B _21604 _21606 _21605 _21607) ((@I ((list B) -> list B) _21604 _21605) = (@I ((list B) -> list B) _21606 _21607))). Qed.
Lemma lem1199821 (a : Prop) (b : Prop) : (term490 a b) = (term491 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1199822 {B : Type'} (_21604 : type1138 B) (_21606 : type1138 B) (_21605 : list B) (_21607 : list B) : (term546 B _21604 _21606 _21605 _21607) = (term547 B _21604 _21606 _21605 _21607).
Proof. exact (@lem1199821 (term541 B _21604 _21606) (term480 B _21605 _21607)). Qed.
Lemma lem1199824 (a : Prop) : (term494 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1199825 {B : Type'} (_21604 : type1138 B) (_21606 : type1138 B) : (term548 B _21604 _21606) = (_21604 = _21606).
Proof. exact (@lem1199824 (_21604 = _21606)). Qed.
Lemma lem1199826 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1199827 {B : Type'} (_21604 : type1138 B) (_21606 : type1138 B) : (term549 B _21604 _21606) = (term550 B _21604 _21606).
Proof. exact (MK_COMB (@lem1199826) (@lem1199825 B _21604 _21606)). Qed.
Lemma lem1199829 (a : Prop) : (term494 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1199830 {B : Type'} (_21605 : list B) (_21607 : list B) : (term495 B _21605 _21607) = (_21605 = _21607).
Proof. exact (@lem1199829 (_21605 = _21607)). Qed.
Lemma lem1199831 {B : Type'} (_21604 : type1138 B) (_21606 : type1138 B) (_21605 : list B) (_21607 : list B) : (term547 B _21604 _21606 _21605 _21607) = (term551 B _21604 _21606 _21605 _21607).
Proof. exact (MK_COMB (@lem1199827 B _21604 _21606) (@lem1199830 B _21605 _21607)). Qed.
Lemma lem1199832 {B : Type'} (_21604 : type1138 B) (_21606 : type1138 B) (_21605 : list B) (_21607 : list B) : (term546 B _21604 _21606 _21605 _21607) = (term551 B _21604 _21606 _21605 _21607).
Proof. exact (TRANS (@lem1199822 B _21604 _21606 _21605 _21607) (@lem1199831 B _21604 _21606 _21605 _21607)). Qed.
Lemma lem1199833 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1199834 {B : Type'} (_21604 : type1138 B) (_21606 : type1138 B) (_21605 : list B) (_21607 : list B) : (term552 B _21604 _21606 _21605 _21607) = (term553 B _21604 _21606 _21605 _21607).
Proof. exact (MK_COMB (@lem1199833) (@lem1199832 B _21604 _21606 _21605 _21607)). Qed.
Lemma lem1199835 {B : Type'} (_21604 : type1138 B) (_21605 : list B) (_21606 : type1138 B) (_21607 : list B) : ((@I ((list B) -> list B) _21604 _21605) = (@I ((list B) -> list B) _21606 _21607)) = ((@I ((list B) -> list B) _21604 _21605) = (@I ((list B) -> list B) _21606 _21607)).
Proof. exact (eq_refl ((@I ((list B) -> list B) _21604 _21605) = (@I ((list B) -> list B) _21606 _21607))). Qed.
Lemma lem1199836 {B : Type'} (_21604 : type1138 B) (_21605 : list B) (_21606 : type1138 B) (_21607 : list B) : (term544 B _21604 _21605 _21606 _21607) = (term554 B _21604 _21605 _21606 _21607).
Proof. exact (MK_COMB (@lem1199834 B _21604 _21606 _21605 _21607) (@lem1199835 B _21604 _21605 _21606 _21607)). Qed.
Lemma lem1199837 {B : Type'} (_21604 : type1138 B) (_21605 : list B) (_21606 : type1138 B) (_21607 : list B) : (term540 B _21604 _21606 _21605 _21607) = (term554 B _21604 _21605 _21606 _21607).
Proof. exact (TRANS (@lem1199819 B _21604 _21605 _21606 _21607) (@lem1199836 B _21604 _21605 _21606 _21607)). Qed.
Lemma lem1199839 {A B : Type'} (a0 : B) (l : list A) (f : A -> B) (x : B -> A) (h1 : term292 A B f x) : term555 A B x a0 f l.
Proof. exact (conj (@lem1199717 A B a0 f x h1) (@lem1199726 A B f l)). Qed.
Lemma lem1199841 {B : Type'} (_21604 : type1138 B) (_21605 : list B) (_21606 : type1138 B) (_21607 : list B) : term554 B _21604 _21605 _21606 _21607.
Proof. exact (EQ_MP (@lem1199837 B _21604 _21605 _21606 _21607) (@lem1199816 B _21604 _21606 _21605 _21607)). Qed.
Lemma lem1199842 {B : Type'} (_21604 : type1138 B) (_21605 : list B) (_21606 : type1138 B) (_21607 : list B) : term554 B _21604 _21605 _21606 _21607.
Proof. exact (@lem1199841 B _21604 _21605 _21606 _21607). Qed.
Lemma lem1199843 {A B : Type'} (x : B -> A) (a0 : B) (f : A -> B) (l : list A) : term556 A B x a0 f l.
Proof. exact (@lem1199842 B (term532 A B f x a0) (term223 A B f l) (@I (B -> (list B) -> list B) (@cons B) a0) (term223 A B f l)). Qed.
Lemma lem1199846 {A B : Type'} (a0 : B) (l : list A) (f : A -> B) (x : B -> A) (h1 : term292 A B f x) : (term473 A B x a0 f l) = (term557 A B a0 f l).
Proof. exact (@lem1199843 A B x a0 f l (@lem1199839 A B a0 l f x h1)). Qed.
Lemma lem1199847 {A B : Type'} (a0 : B) (l : list A) (f : A -> B) (x : B -> A) (h1 : term292 A B f x) : (term473 A B x a0 f l) = (term557 A B a0 f l).
Proof. exact (@lem1199846 A B a0 l f x h1). Qed.
Lemma lem1199848 {A B : Type'} (a0 : B) (l : list A) (f : A -> B) (x : B -> A) (h1 : term292 A B f x) : term558 A B x a0 f l.
Proof. exact (fun h0 : term559 A B x a0 f l => @lem1199847 A B a0 l f x h1). Qed.
Lemma lem1199850 (p : Prop) : (term244 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1199851 {A B : Type'} (x : B -> A) (a0 : B) (f : A -> B) (l : list A) : (term558 A B x a0 f l) = ((term473 A B x a0 f l) = (term557 A B a0 f l)).
Proof. exact (@lem1199850 ((term473 A B x a0 f l) = (term557 A B a0 f l))). Qed.
Lemma lem1199852 {A B : Type'} (a0 : B) (l : list A) (f : A -> B) (x : B -> A) (h1 : term292 A B f x) : (term473 A B x a0 f l) = (term557 A B a0 f l).
Proof. exact (EQ_MP (@lem1199851 A B x a0 f l) (@lem1199848 A B a0 l f x h1)). Qed.
Lemma lem1199853 {A B : Type'} (a0 : B) (l : list A) (f : A -> B) (x : B -> A) (h1 : term292 A B f x) (h2 : term134 A B) : term560 A B x a0 f l.
Proof. exact (conj (@lem1199573 A B f x a0 l h2) (@lem1199852 A B a0 l f x h1)). Qed.
Lemma lem1199855 {B : Type'} (x : list B) (y : list B) (z : list B) : term501 B x y z.
Proof. exact (EQ_MP (@lem1199558 B x y z) (@lem1199537 B y x z)). Qed.
Lemma lem1199856 {B : Type'} (x : list B) (y : list B) (z : list B) : term501 B x y z.
Proof. exact (@lem1199855 B x y z). Qed.
Lemma lem1199857 {A B : Type'} (x : B -> A) (a0 : B) (f : A -> B) (l : list A) : term561 A B x a0 f l.
Proof. exact (@lem1199856 B (term473 A B x a0 f l) (term472 A B f x a0 l) (term557 A B a0 f l)). Qed.
Lemma lem1199860 {A B : Type'} (a0 : B) (l : list A) (f : A -> B) (x : B -> A) (h1 : term292 A B f x) (h2 : term134 A B) : (term472 A B f x a0 l) = (term557 A B a0 f l).
Proof. exact (@lem1199857 A B x a0 f l (@lem1199853 A B a0 l f x h1 h2)). Qed.
Lemma lem1199861 {A B : Type'} (a0 : B) (l : list A) (f : A -> B) (x : B -> A) (h1 : term292 A B f x) (h2 : term134 A B) : (term472 A B f x a0 l) = (term557 A B a0 f l).
Proof. exact (@lem1199860 A B a0 l f x h1 h2). Qed.
Lemma lem1199862 {A B : Type'} (a0 : B) (l : list A) (f : A -> B) (x : B -> A) (h1 : term292 A B f x) (h2 : term134 A B) : term562 A B x a0 f l.
Proof. exact (fun h0 : term563 A B x a0 f l => @lem1199861 A B a0 l f x h1 h2). Qed.
Lemma lem1199864 (p : Prop) : (term244 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1199865 {A B : Type'} (x : B -> A) (a0 : B) (f : A -> B) (l : list A) : (term562 A B x a0 f l) = ((term472 A B f x a0 l) = (term557 A B a0 f l)).
Proof. exact (@lem1199864 ((term472 A B f x a0 l) = (term557 A B a0 f l))). Qed.
Lemma lem1199866 {A B : Type'} (a0 : B) (l : list A) (f : A -> B) (x : B -> A) (h1 : term292 A B f x) (h2 : term134 A B) : (term472 A B f x a0 l) = (term557 A B a0 f l).
Proof. exact (EQ_MP (@lem1199865 A B x a0 f l) (@lem1199862 A B a0 l f x h1 h2)). Qed.
Lemma lem1199869 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1199871 {A B : Type'} (_21521 : list A) (a0 : B) (f : A -> B) (l : list A) : (term455 A B _21521 a0 f l) = (term564 A B _21521 a0 f l).
Proof. exact (@lem1199869 ((term223 A B f _21521) = (term557 A B a0 f l))). Qed.
Lemma lem1199874 {A B : Type'} (_21521 : list A) (l : list A) (f : A -> B) (a0 : B) (a1 : list B) (h1 : term433 A B l f a0 a1) : term564 A B _21521 a0 f l.
Proof. exact (EQ_MP (@lem1199871 A B _21521 a0 f l) (@lem1199046 A B _21521 l f a0 a1 h1)). Qed.
Lemma lem1199875 {A B : Type'} (_21521 : list A) (l : list A) (f : A -> B) (a0 : B) (a1 : list B) (h1 : term433 A B l f a0 a1) : term564 A B _21521 a0 f l.
Proof. exact (@lem1199874 A B _21521 l f a0 a1 h1). Qed.
Lemma lem1199876 {A B : Type'} (x : B -> A) (l : list A) (f : A -> B) (a0 : B) (a1 : list B) (h1 : term433 A B l f a0 a1) : term565 A B x a0 f l.
Proof. exact (@lem1199875 A B (term566 A B x a0 l) l f a0 a1 h1). Qed.
Lemma lem1199879 {A B : Type'} (x : B -> A) (l : list A) (f : A -> B) (a0 : B) (a1 : list B) (h1 : term292 A B f x) (h2 : term134 A B) (h3 : term433 A B l f a0 a1) : False.
Proof. exact (@lem1199876 A B x l f a0 a1 h3 (@lem1199866 A B a0 l f x h1 h2)). Qed.
Lemma lem1199880 {A B : Type'} (x : B -> A) (l : list A) (f : A -> B) (a0 : B) (a1 : list B) (h1 : term292 A B f x) (h2 : term134 A B) (h3 : term433 A B l f a0 a1) : term247.
Proof. exact (fun h0 : ~ False => @lem1199879 A B x l f a0 a1 h1 h2 h3). Qed.
Lemma lem1199882 (p : Prop) : (term244 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1199883 : term247 = False.
Proof. exact (@lem1199882 False). Qed.
Lemma lem1199885 {A B : Type'} (x : B -> A) (l : list A) (f : A -> B) (a0 : B) (a1 : list B) (h1 : term292 A B f x) (h2 : term134 A B) (h3 : term433 A B l f a0 a1) : False.
Proof. exact (EQ_MP (@lem1199883) (@lem1199880 A B x l f a0 a1 h1 h2 h3)). Qed.
Lemma lem1199886 {A B : Type'} (f : A -> B) (h1 : term436 A B f) (h2 : term134 A B) : (term436 A B f) = False.
Proof. exact (prop_ext (fun h3 : term436 A B f => @lem1199251 A B f h1 h2) (fun h3 : False => @lem1198804 A B f h1)). Qed.
Lemma lem1199887 {A B : Type'} (f : A -> B) (h1 : term436 A B f) (h2 : term134 A B) : False.
Proof. exact (EQ_MP (@lem1199886 A B f h1 h2) (@lem1198804 A B f h1)). Qed.
Lemma lem1199888 {A B : Type'} (x : B -> A) (l : list A) (f : A -> B) (a0 : B) (a1 : list B) (h1 : term292 A B f x) (h2 : term134 A B) (h3 : term398 A B l f a0 a1) : False.
Proof. exact (or_elim (@lem1198719 A B l f a0 a1 h3) (fun h0 : term436 A B f => @lem1199887 A B f h0 h2) (fun h0 : term433 A B l f a0 a1 => @lem1199885 A B x l f a0 a1 h1 h2 h0)). Qed.
Lemma lem1199889 {A B : Type'} (l : list A) (f : A -> B) (a0 : B) (a1 : list B) (h1 : term40 A B f) (h2 : term134 A B) (h3 : term398 A B l f a0 a1) : False.
Proof. exact (ex_elim (@lem1198092 A B f h1) (fun x : B -> A => fun h0 : term294 A B f x => @lem1199888 A B x l f a0 a1 h0 h2 h3)). Qed.
Lemma lem1199890 {A B : Type'} (f : A -> B) (a0 : B) (a1 : list B) (h1 : term40 A B f) (h2 : term401 A B f a0 a1) (h3 : term134 A B) : False.
Proof. exact (ex_elim (@lem1198395 A B f a0 a1 h2) (fun l : list A => fun h0 : term400 A B f a0 a1 l => @lem1199889 A B l f a0 a1 h1 h3 h0)). Qed.
Lemma lem1199891 {A B : Type'} (f : A -> B) (a0 : B) (h1 : term40 A B f) (h2 : term403 A B f a0) (h3 : term134 A B) : False.
Proof. exact (ex_elim (@lem1198394 A B f a0 h2) (fun a1 : list B => fun h0 : term402 A B f a0 a1 => @lem1199890 A B f a0 a1 h1 h0 h3)). Qed.
Lemma lem1199892 {A B : Type'} (f : A -> B) (h1 : term40 A B f) (h2 : term254 A B f) (h3 : term134 A B) : False.
Proof. exact (ex_elim (@lem1198317 A B f h2) (fun a0 : B => fun h0 : term404 A B f a0 => @lem1199891 A B f a0 h1 h0 h3)). Qed.
Lemma lem1199893 {A B : Type'} (f : A -> B) (h1 : term40 A B f) (h2 : term254 A B f) (h3 : term134 A B) : (term134 A B) = False.
Proof. exact (prop_ext (fun h4 : term134 A B => @lem1199892 A B f h1 h2 h3) (fun h4 : False => @lem1198355 A B h3)). Qed.
Lemma lem1199894 {A B : Type'} (f : A -> B) (h1 : term40 A B f) (h2 : term254 A B f) (h3 : term134 A B) : False.
Proof. exact (EQ_MP (@lem1199893 A B f h1 h2 h3) (@lem1198355 A B h3)). Qed.
Lemma lem1199895 {A B : Type'} (f : A -> B) (h1 : term40 A B f) (h2 : term254 A B f) (h3 : term134 A B) : term140 B.
Proof. exact (fun h0 : term135 B => @lem1199894 A B f h1 h2 h3). Qed.
Lemma lem1199896 {B : Type'} : (term140 B) = (term141 B).
Proof. exact (@lem69 (term135 B)). Qed.
Lemma lem1199897 {A B : Type'} (f : A -> B) (h1 : term40 A B f) (h2 : term254 A B f) (h3 : term134 A B) : term141 B.
Proof. exact (EQ_MP (@lem1199896 B) (@lem1199895 A B f h1 h2 h3)). Qed.
Lemma lem1199898 {A B : Type'} (f : A -> B) (h1 : term40 A B f) (h2 : term254 A B f) : term144 A B.
Proof. exact (fun h0 : term134 A B => @lem1199897 A B f h1 h2 h0). Qed.
Lemma lem1199899 {A B : Type'} (f : A -> B) (h1 : term40 A B f) : term261 A B f.
Proof. exact (fun h0 : term254 A B f => @lem1199898 A B f h1 h0). Qed.
Lemma lem1199900 {A B : Type'} (f : A -> B) : term263 A B f.
Proof. exact (fun h0 : term40 A B f => @lem1199899 A B f h0). Qed.
Lemma lem1199905 {A B : Type'} : term267 A B.
Proof. exact (fun f : A -> B => @lem1199900 A B f). Qed.
Lemma lem1199906 {A B : Type'} : term266 A B.
Proof. exact (EQ_MP (@lem1198039 A B) (@lem1199905 A B)). Qed.
Lemma lem1199907 {A B : Type'} (f : A -> B) : term567 A B f.
Proof. exact (@lem1199906 A B f). Qed.
Lemma lem1199908 {A B : Type'} (f : A -> B) : (term567 A B f) = (term255 A B f).
Proof. exact (eq_refl (term567 A B f)). Qed.
Lemma lem1199909 {A B : Type'} (f : A -> B) : term255 A B f.
Proof. exact (EQ_MP (@lem1199908 A B f) (@lem1199907 A B f)). Qed.
Lemma lem1199911 {A B : Type'} (f : A -> B) : term255 A B f.
Proof. exact (@lem1197740 A B f (@lem1199909 A B f)). Qed.
Lemma lem1199912 {A B : Type'} (f : A -> B) (h1 : term40 A B f) : term260 A B f.
Proof. exact (@lem1199911 A B f (@lem1195187 A B f h1)). Qed.
Lemma lem1199913 {A B : Type'} (f : A -> B) (h1 : term40 A B f) (h2 : term254 A B f) : term143 A B.
Proof. exact (@lem1199912 A B f h1 (@lem1197718 A B f h2)). Qed.
Lemma lem1199914 {A B : Type'} (f : A -> B) (h1 : term40 A B f) (h2 : term254 A B f) : term140 B.
Proof. exact (@lem1199913 A B f h1 h2 (@lem1197719 A B)). Qed.
Lemma lem1199915 {A B : Type'} (f : A -> B) (h1 : term40 A B f) (h2 : term254 A B f) : False.
Proof. exact (@lem1199914 A B f h1 h2 (@lem1197721 B)). Qed.
Lemma lem1199916 {A B : Type'} (f : A -> B) (h1 : term40 A B f) (h2 : term254 A B f) : (term254 A B f) = False.
Proof. exact (prop_ext (fun h3 : term254 A B f => @lem1199915 A B f h1 h2) (fun h3 : False => @lem1197718 A B f h2)). Qed.
Lemma lem1199917 {A B : Type'} (f : A -> B) (h1 : term40 A B f) (h2 : term254 A B f) : False.
Proof. exact (EQ_MP (@lem1199916 A B f h1 h2) (@lem1197718 A B f h2)). Qed.
Lemma lem1199918 {A B : Type'} (f : A -> B) (h1 : term40 A B f) : term253 A B f.
Proof. exact (fun h0 : term254 A B f => @lem1199917 A B f h1 h0). Qed.
Lemma lem1199919 {A B : Type'} (f : A -> B) (h1 : term40 A B f) : term125 A B f.
Proof. exact (EQ_MP (@lem1197717 A B f) (@lem1199918 A B f h1)). Qed.
Lemma lem1199920 {A B : Type'} (f : A -> B) (h1 : term40 A B f) : term39 A B f.
Proof. exact (@lem1195366 A B f (@lem1199919 A B f h1)). Qed.
Lemma lem1199921 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) (h1 : term60 A B t f y) : term73 A B h t f y.
Proof. exact (EQ_MP (@lem1195339 A B h t f y) (@lem1197713 A B h t f y h1)). Qed.
Lemma lem1199922 {A B : Type'} (h : A) (t : list A) (f : A -> B) (y : B) : term75 A B h t f y.
Proof. exact (fun h0 : term60 A B t f y => @lem1199921 A B h t f y h0). Qed.
Lemma lem1199927 {A B : Type'} (h : A) (f : A -> B) (y : B) : term79 A B h f y.
Proof. exact (fun t : list A => @lem1199922 A B h t f y). Qed.
Lemma lem1199932 {A B : Type'} (f : A -> B) (y : B) : term83 A B f y.
Proof. exact (fun h : A => @lem1199927 A B h f y). Qed.
Lemma lem1199933 {A B : Type'} (f : A -> B) (y : B) : term85 A B f y.
Proof. exact (conj (@lem1195293 A B f y) (@lem1199932 A B f y)). Qed.
Lemma lem1199934 {A B : Type'} (f : A -> B) (y : B) : term63 A B f y.
Proof. exact (@lem1195258 A B f y (@lem1199933 A B f y)). Qed.
Lemma lem1199935 {A B : Type'} (f : A -> B) (y : B) : term54 A B f y.
Proof. exact (EQ_MP (@lem1195231 A B f y) (@lem1199934 A B f y)). Qed.
Lemma lem1199936 {A B : Type'} (y : B) (f : A -> B) (h1 : term39 A B f) : term48 A B f y.
Proof. exact (@lem1199935 A B f y (@lem1195190 A B y f h1)). Qed.
Lemma lem1199941 {A B : Type'} (f : A -> B) (h1 : term39 A B f) : term40 A B f.
Proof. exact (fun y : B => @lem1199936 A B y f h1). Qed.
Lemma lem1199942 {A B : Type'} (f : A -> B) : term568 A B f.
Proof. exact (fun h0 : term40 A B f => @lem1199920 A B f h0). Qed.
Lemma lem1199943 {A B : Type'} (f : A -> B) : term569 A B f.
Proof. exact (fun h0 : term39 A B f => @lem1199941 A B f h0). Qed.
Lemma lem1199944 {A B : Type'} (f : A -> B) : term570 A B f.
Proof. exact (conj (@lem1199943 A B f) (@lem1199942 A B f)). Qed.
Lemma lem1199945 {A B : Type'} (f : A -> B) : (term570 A B f) = ((term39 A B f) = (term40 A B f)).
Proof. exact (@lem32 (term39 A B f) (term40 A B f)). Qed.
Lemma lem1199946 {A B : Type'} (f : A -> B) : (term39 A B f) = (term40 A B f).
Proof. exact (EQ_MP (@lem1199945 A B f) (@lem1199944 A B f)). Qed.
Lemma lem1199951 {A B : Type'} : term571 A B.
Proof. exact (fun f : A -> B => @lem1199946 A B f). Qed.
