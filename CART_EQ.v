Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CART_EQ_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import ETA_AX_spec.
Require Import FORALL_FINITE_INDEX_spec.
Require Import FUN_EQ_THM_spec.
Require Import finite_index_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16462_spec.
Require Import thm16474_spec.
Require Import thm17646_spec.
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
Require Import thm69_spec.
Require Import thm7614851_spec.
Lemma lem7616165 {A B : Type'} (f : A -> B) (g : A -> B) (h1 : (f = g) = (term0 A B f g)) : (f = g) = (term0 A B f g).
Proof. exact (h1). Qed.
Lemma lem7616166 {A B : Type'} (f : A -> B) (g : A -> B) (h1 : (f = g) = (term0 A B f g)) : (term0 A B f g) = (f = g).
Proof. exact (SYM (@lem7616165 A B f g h1)). Qed.
Lemma lem7616167 {A B : Type'} (f : A -> B) (g : A -> B) (h1 : (term0 A B f g) = (f = g)) : (term0 A B f g) = (f = g).
Proof. exact (h1). Qed.
Lemma lem7616168 {A B : Type'} (f : A -> B) (g : A -> B) (h1 : (term0 A B f g) = (f = g)) : (f = g) = (term0 A B f g).
Proof. exact (SYM (@lem7616167 A B f g h1)). Qed.
Lemma lem7616169 {A B : Type'} (f : A -> B) (g : A -> B) : ((f = g) = (term0 A B f g)) = ((term0 A B f g) = (f = g)).
Proof. exact (prop_ext (fun h1 : (f = g) = (term0 A B f g) => @lem7616166 A B f g h1) (fun h1 : (term0 A B f g) = (f = g) => @lem7616168 A B f g h1)). Qed.
Lemma lem7616170 {A B : Type'} (f : A -> B) : (term1 A B f) = (term2 A B f).
Proof. exact (fun_ext (fun g : A -> B => @lem7616169 A B f g)). Qed.
Lemma lem7616171 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem7616172 {A B : Type'} (f : A -> B) : (term3 A B f) = (term4 A B f).
Proof. exact (MK_COMB (@lem7616171 A B) (@lem7616170 A B f)). Qed.
Lemma lem7616173 {A B : Type'} : (term5 A B) = (term6 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem7616172 A B f)). Qed.
Lemma lem7616174 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem7616175 {A B : Type'} : (term7 A B) = (term8 A B).
Proof. exact (MK_COMB (@lem7616174 A B) (@lem7616173 A B)). Qed.
Lemma lem7616176 {A B : Type'} : term8 A B.
Proof. exact (EQ_MP (@lem7616175 A B) (@lem9220 A B)). Qed.
Lemma lem7616177 {A B : Type'} (t : A -> B) : term9 A B t.
Proof. exact (@lem9121 A B t). Qed.
Lemma lem7616178 {A B : Type'} (t : A -> B) : (term9 A B t) = ((term10 A B t) = t).
Proof. exact (eq_refl (term9 A B t)). Qed.
Lemma lem7616179 {A B : Type'} (t : A -> B) : (term10 A B t) = t.
Proof. exact (EQ_MP (@lem7616178 A B t) (@lem7616177 A B t)). Qed.
Lemma lem7616180 {A B : Type'} (f : A -> B) : term11 A B f.
Proof. exact (@lem7616176 A B f). Qed.
Lemma lem7616181 {A B : Type'} (f : A -> B) : (term11 A B f) = (term4 A B f).
Proof. exact (eq_refl (term11 A B f)). Qed.
Lemma lem7616182 {A B : Type'} (f : A -> B) : term4 A B f.
Proof. exact (EQ_MP (@lem7616181 A B f) (@lem7616180 A B f)). Qed.
Lemma lem7616183 {A B : Type'} (f : A -> B) (g : A -> B) : term12 A B f g.
Proof. exact (@lem7616182 A B f g). Qed.
Lemma lem7616184 {A B : Type'} (f : A -> B) (g : A -> B) : (term12 A B f g) = ((term0 A B f g) = (f = g)).
Proof. exact (eq_refl (term12 A B f g)). Qed.
Lemma lem7616186 {N : Type'} (P : type33 N) (h1 : (term13 N P) = (term14 N P)) : (term13 N P) = (term14 N P).
Proof. exact (h1). Qed.
Lemma lem7616187 {N : Type'} (P : type33 N) (h1 : (term13 N P) = (term14 N P)) : (term14 N P) = (term13 N P).
Proof. exact (SYM (@lem7616186 N P h1)). Qed.
Lemma lem7616188 {N : Type'} (P : type33 N) (h1 : (term14 N P) = (term13 N P)) : (term14 N P) = (term13 N P).
Proof. exact (h1). Qed.
Lemma lem7616189 {N : Type'} (P : type33 N) (h1 : (term14 N P) = (term13 N P)) : (term13 N P) = (term14 N P).
Proof. exact (SYM (@lem7616188 N P h1)). Qed.
Lemma lem7616190 {N : Type'} (P : type33 N) : ((term13 N P) = (term14 N P)) = ((term14 N P) = (term13 N P)).
Proof. exact (prop_ext (fun h1 : (term13 N P) = (term14 N P) => @lem7616187 N P h1) (fun h1 : (term14 N P) = (term13 N P) => @lem7616189 N P h1)). Qed.
Lemma lem7616192 {_139760 _139770 : Type'} (x : cart _139760 _139770) : term15 _139760 _139770 x.
Proof. exact (@lem7616152 _139760 _139770 x). Qed.
Lemma lem7616193 {_139760 _139770 : Type'} (x : cart _139760 _139770) : (term15 _139760 _139770 x) = (term16 _139760 _139770 x).
Proof. exact (eq_refl (term15 _139760 _139770 x)). Qed.
Lemma lem7616194 {_139760 _139770 : Type'} (x : cart _139760 _139770) : term16 _139760 _139770 x.
Proof. exact (EQ_MP (@lem7616193 _139760 _139770 x) (@lem7616192 _139760 _139770 x)). Qed.
Lemma lem7616195 {_139760 _139770 : Type'} (x : cart _139760 _139770) (i : nat) : term17 _139760 _139770 x i.
Proof. exact (@lem7616194 _139760 _139770 x i). Qed.
Lemma lem7616196 {_139760 _139770 : Type'} (x : cart _139760 _139770) (i : nat) : (term17 _139760 _139770 x i) = ((@dollar _139760 _139770 x i) = (term18 _139760 _139770 x i)).
Proof. exact (eq_refl (term17 _139760 _139770 x i)). Qed.
Lemma lem7616231 {_139760 _139770 : Type'} (x : cart _139760 _139770) (i : nat) : (@dollar _139760 _139770 x i) = (term18 _139760 _139770 x i).
Proof. exact (EQ_MP (@lem7616196 _139760 _139770 x i) (@lem7616195 _139760 _139770 x i)). Qed.
Lemma lem7616232 {A B : Type'} (x : cart A B) (i : nat) : (@dollar A B x i) = (term18 A B x i).
Proof. exact (@lem7616231 A B x i). Qed.
Lemma lem7616233 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem7616234 {A B : Type'} (x : cart A B) (i : nat) : (term19 A B x i) = (term20 A B x i).
Proof. exact (MK_COMB (@lem7616233 A) (@lem7616232 A B x i)). Qed.
Lemma lem7616236 {_139760 _139770 : Type'} (x : cart _139760 _139770) (i : nat) : (@dollar _139760 _139770 x i) = (term18 _139760 _139770 x i).
Proof. exact (EQ_MP (@lem7616196 _139760 _139770 x i) (@lem7616195 _139760 _139770 x i)). Qed.
Lemma lem7616237 {A B : Type'} (x : cart A B) (i : nat) : (@dollar A B x i) = (term18 A B x i).
Proof. exact (@lem7616236 A B x i). Qed.
Lemma lem7616238 {A B : Type'} (y : cart A B) (i : nat) : (@dollar A B y i) = (term18 A B y i).
Proof. exact (@lem7616237 A B y i). Qed.
Lemma lem7616239 {A B : Type'} (x : cart A B) (y : cart A B) (i : nat) : ((@dollar A B x i) = (@dollar A B y i)) = ((term18 A B x i) = (term18 A B y i)).
Proof. exact (MK_COMB (@lem7616234 A B x i) (@lem7616238 A B y i)). Qed.
Lemma lem7616242 {B : Type'} (i : nat) : (term21 B i) = (term21 B i).
Proof. exact (eq_refl (term21 B i)). Qed.
Lemma lem7616243 {A B : Type'} (x : cart A B) (y : cart A B) (i : nat) : (term22 A B x y i) = (term23 A B x y i).
Proof. exact (MK_COMB (@lem7616242 B i) (@lem7616239 A B x y i)). Qed.
Lemma lem7616246 {A B : Type'} (x : cart A B) (y : cart A B) : (term24 A B x y) = (term25 A B x y).
Proof. exact (fun_ext (fun i : nat => @lem7616243 A B x y i)). Qed.
Lemma lem7616247 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7616248 {A B : Type'} (x : cart A B) (y : cart A B) : (term26 A B x y) = (term27 A B x y).
Proof. exact (MK_COMB (@lem7616247) (@lem7616246 A B x y)). Qed.
Lemma lem7616250 {N : Type'} (P : type33 N) : (term14 N P) = (term13 N P).
Proof. exact (EQ_MP (@lem7616190 N P) (@lem7614824 N P)). Qed.
Lemma lem7616251 {B : Type'} (P : type33 B) : (term14 B P) = (term13 B P).
Proof. exact (@lem7616250 B P). Qed.
Lemma lem7616252 {A B : Type'} (x : cart A B) (y : cart A B) : (term28 A B x y) = (term29 A B x y).
Proof. exact (@lem7616251 B (term30 A B x y)). Qed.
Lemma lem7616253 {A B : Type'} (x : cart A B) (y : cart A B) (i : nat) : (term31 A B x y i) = ((term18 A B x i) = (term18 A B y i)).
Proof. exact (eq_refl (term31 A B x y i)). Qed.
Lemma lem7616254 {B : Type'} (i : nat) : (term21 B i) = (term21 B i).
Proof. exact (eq_refl (term21 B i)). Qed.
Lemma lem7616255 {A B : Type'} (x : cart A B) (y : cart A B) (i : nat) : (term32 A B x y i) = (term23 A B x y i).
Proof. exact (MK_COMB (@lem7616254 B i) (@lem7616253 A B x y i)). Qed.
Lemma lem7616256 {A B : Type'} (x : cart A B) (y : cart A B) : (term33 A B x y) = (term25 A B x y).
Proof. exact (fun_ext (fun i : nat => @lem7616255 A B x y i)). Qed.
Lemma lem7616257 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7616258 {A B : Type'} (x : cart A B) (y : cart A B) : (term28 A B x y) = (term27 A B x y).
Proof. exact (MK_COMB (@lem7616257) (@lem7616256 A B x y)). Qed.
Lemma lem7616259 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7616260 {A B : Type'} (x : cart A B) (y : cart A B) : (term34 A B x y) = (term35 A B x y).
Proof. exact (MK_COMB (@lem7616259) (@lem7616258 A B x y)). Qed.
Lemma lem7616261 {A B : Type'} (x : cart A B) (y : cart A B) (k : finite_image B) : (term36 A B x y k) = ((@dest_cart A B x k) = (@dest_cart A B y k)).
Proof. exact (eq_refl (term36 A B x y k)). Qed.
Lemma lem7616262 {A B : Type'} (x : cart A B) (y : cart A B) : (term37 A B x y) = (term30 A B x y).
Proof. exact (fun_ext (fun k : finite_image B => @lem7616261 A B x y k)). Qed.
Lemma lem7616263 {B : Type'} : (@all (finite_image B)) = (@all (finite_image B)).
Proof. exact (eq_refl (@all (finite_image B))). Qed.
Lemma lem7616264 {A B : Type'} (x : cart A B) (y : cart A B) : (term29 A B x y) = (term38 A B x y).
Proof. exact (MK_COMB (@lem7616263 B) (@lem7616262 A B x y)). Qed.
Lemma lem7616265 {A B : Type'} (x : cart A B) (y : cart A B) : ((term28 A B x y) = (term29 A B x y)) = ((term27 A B x y) = (term38 A B x y)).
Proof. exact (MK_COMB (@lem7616260 A B x y) (@lem7616264 A B x y)). Qed.
Lemma lem7616266 {A B : Type'} (x : cart A B) (y : cart A B) : (term27 A B x y) = (term38 A B x y).
Proof. exact (EQ_MP (@lem7616265 A B x y) (@lem7616252 A B x y)). Qed.
Lemma lem7616273 {A B : Type'} (x : cart A B) (y : cart A B) : (term26 A B x y) = (term38 A B x y).
Proof. exact (TRANS (@lem7616248 A B x y) (@lem7616266 A B x y)). Qed.
Lemma lem7616274 {A B : Type'} (x : cart A B) (y : cart A B) : (term39 A B x y) = (term39 A B x y).
Proof. exact (eq_refl (term39 A B x y)). Qed.
Lemma lem7616275 {A B : Type'} (x : cart A B) (y : cart A B) : ((x = y) = (term26 A B x y)) = ((x = y) = (term38 A B x y)).
Proof. exact (MK_COMB (@lem7616274 A B x y) (@lem7616273 A B x y)). Qed.
Lemma lem7616278 {A B : Type'} (x : cart A B) (y : cart A B) : ((x = y) = (term38 A B x y)) = ((x = y) = (term26 A B x y)).
Proof. exact (SYM (@lem7616275 A B x y)). Qed.
Lemma lem7616284 {A B : Type'} (f : A -> B) (g : A -> B) : (term0 A B f g) = (f = g).
Proof. exact (EQ_MP (@lem7616184 A B f g) (@lem7616183 A B f g)). Qed.
Lemma lem7616285 {A B : Type'} (f : type35 A B) (g : type35 A B) : (term40 A B f g) = (f = g).
Proof. exact (@lem7616284 (finite_image B) A f g). Qed.
Lemma lem7616286 {A B : Type'} (x : cart A B) (y : cart A B) : (term41 A B x y) = ((term42 A B x) = (term42 A B y)).
Proof. exact (@lem7616285 A B (term42 A B x) (term42 A B y)). Qed.
Lemma lem7616287 {A B : Type'} (x : cart A B) (k : finite_image B) : (term43 A B x k) = (@dest_cart A B x k).
Proof. exact (eq_refl (term43 A B x k)). Qed.
Lemma lem7616288 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem7616289 {A B : Type'} (x : cart A B) (k : finite_image B) : (term44 A B x k) = (term45 A B x k).
Proof. exact (MK_COMB (@lem7616288 A) (@lem7616287 A B x k)). Qed.
Lemma lem7616290 {A B : Type'} (y : cart A B) (k : finite_image B) : (term43 A B y k) = (@dest_cart A B y k).
Proof. exact (eq_refl (term43 A B y k)). Qed.
Lemma lem7616291 {A B : Type'} (x : cart A B) (y : cart A B) (k : finite_image B) : ((term43 A B x k) = (term43 A B y k)) = ((@dest_cart A B x k) = (@dest_cart A B y k)).
Proof. exact (MK_COMB (@lem7616289 A B x k) (@lem7616290 A B y k)). Qed.
Lemma lem7616292 {A B : Type'} (x : cart A B) (y : cart A B) : (term46 A B x y) = (term30 A B x y).
Proof. exact (fun_ext (fun k : finite_image B => @lem7616291 A B x y k)). Qed.
Lemma lem7616293 {B : Type'} : (@all (finite_image B)) = (@all (finite_image B)).
Proof. exact (eq_refl (@all (finite_image B))). Qed.
Lemma lem7616294 {A B : Type'} (x : cart A B) (y : cart A B) : (term41 A B x y) = (term38 A B x y).
Proof. exact (MK_COMB (@lem7616293 B) (@lem7616292 A B x y)). Qed.
Lemma lem7616295 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7616296 {A B : Type'} (x : cart A B) (y : cart A B) : (term47 A B x y) = (term48 A B x y).
Proof. exact (MK_COMB (@lem7616295) (@lem7616294 A B x y)). Qed.
Lemma lem7616297 {A B : Type'} (x : cart A B) (y : cart A B) : ((term42 A B x) = (term42 A B y)) = ((term42 A B x) = (term42 A B y)).
Proof. exact (eq_refl ((term42 A B x) = (term42 A B y))). Qed.
Lemma lem7616298 {A B : Type'} (x : cart A B) (y : cart A B) : ((term41 A B x y) = ((term42 A B x) = (term42 A B y))) = ((term38 A B x y) = ((term42 A B x) = (term42 A B y))).
Proof. exact (MK_COMB (@lem7616296 A B x y) (@lem7616297 A B x y)). Qed.
Lemma lem7616299 {A B : Type'} (x : cart A B) (y : cart A B) : (term38 A B x y) = ((term42 A B x) = (term42 A B y)).
Proof. exact (EQ_MP (@lem7616298 A B x y) (@lem7616286 A B x y)). Qed.
Lemma lem7616302 {A B : Type'} (t : type35 A B) : (term49 A B t) = t.
Proof. exact (@lem7616179 (finite_image B) A t). Qed.
Lemma lem7616303 {A B : Type'} (x : cart A B) : (term42 A B x) = (@dest_cart A B x).
Proof. exact (@lem7616302 A B (@dest_cart A B x)). Qed.
Lemma lem7616304 {A B : Type'} : (@eq ((finite_image B) -> A)) = (@eq ((finite_image B) -> A)).
Proof. exact (eq_refl (@eq ((finite_image B) -> A))). Qed.
Lemma lem7616305 {A B : Type'} (x : cart A B) : (term50 A B x) = (term51 A B x).
Proof. exact (MK_COMB (@lem7616304 A B) (@lem7616303 A B x)). Qed.
Lemma lem7616306 {A B : Type'} (t : type35 A B) : (term49 A B t) = t.
Proof. exact (@lem7616179 (finite_image B) A t). Qed.
Lemma lem7616307 {A B : Type'} (y : cart A B) : (term42 A B y) = (@dest_cart A B y).
Proof. exact (@lem7616306 A B (@dest_cart A B y)). Qed.
Lemma lem7616308 {A B : Type'} (x : cart A B) (y : cart A B) : ((term42 A B x) = (term42 A B y)) = ((@dest_cart A B x) = (@dest_cart A B y)).
Proof. exact (MK_COMB (@lem7616305 A B x) (@lem7616307 A B y)). Qed.
Lemma lem7616311 {A B : Type'} (x : cart A B) (y : cart A B) : (term38 A B x y) = ((@dest_cart A B x) = (@dest_cart A B y)).
Proof. exact (TRANS (@lem7616299 A B x y) (@lem7616308 A B x y)). Qed.
Lemma lem7616312 {A B : Type'} (x : cart A B) (y : cart A B) : (term39 A B x y) = (term39 A B x y).
Proof. exact (eq_refl (term39 A B x y)). Qed.
Lemma lem7616313 {A B : Type'} (x : cart A B) (y : cart A B) : ((x = y) = (term38 A B x y)) = ((x = y) = ((@dest_cart A B x) = (@dest_cart A B y))).
Proof. exact (MK_COMB (@lem7616312 A B x y) (@lem7616311 A B x y)). Qed.
Lemma lem7616316 {A B : Type'} (x : cart A B) (y : cart A B) : ((x = y) = ((@dest_cart A B x) = (@dest_cart A B y))) = ((x = y) = (term38 A B x y)).
Proof. exact (SYM (@lem7616313 A B x y)). Qed.
Lemma lem7616318 (p : Prop) : p = (term52 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7616319 {A B : Type'} (x : cart A B) (y : cart A B) : ((x = y) = ((@dest_cart A B x) = (@dest_cart A B y))) = (term53 A B x y).
Proof. exact (@lem7616318 ((x = y) = ((@dest_cart A B x) = (@dest_cart A B y)))). Qed.
Lemma lem7616320 {A B : Type'} (x : cart A B) (y : cart A B) : (term53 A B x y) = ((x = y) = ((@dest_cart A B x) = (@dest_cart A B y))).
Proof. exact (SYM (@lem7616319 A B x y)). Qed.
Lemma lem7616321 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term54 A B x y) : term54 A B x y.
Proof. exact (h1). Qed.
Lemma lem7616322 {A B : Type'} : term55 A B.
Proof. exact (@lem7614851 A B). Qed.
Lemma lem7616327 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term56 A B x y) : term56 A B x y.
Proof. exact (h1). Qed.
Lemma lem7616328 {A B : Type'} (x : cart A B) (y : cart A B) : term57 A B x y.
Proof. exact (fun h0 : term56 A B x y => @lem7616327 A B x y h0). Qed.
Lemma lem7616329 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term57 A B x y) : term57 A B x y.
Proof. exact (h1). Qed.
Lemma lem7616330 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term56 A B x y) : term56 A B x y.
Proof. exact (h1). Qed.
Lemma lem7616331 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term56 A B x y) (h2 : term57 A B x y) : term56 A B x y.
Proof. exact (@lem7616329 A B x y h2 (@lem7616330 A B x y h1)). Qed.
Lemma lem7616332 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term56 A B x y) : term58 A B x y.
Proof. exact (fun h0 : term57 A B x y => @lem7616331 A B x y h1 h0). Qed.
Lemma lem7616333 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term57 A B x y) : term57 A B x y.
Proof. exact (h1). Qed.
Lemma lem7616334 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term56 A B x y) (h2 : term57 A B x y) : term56 A B x y.
Proof. exact (@lem7616332 A B x y h1 (@lem7616333 A B x y h2)). Qed.
Lemma lem7616335 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term57 A B x y) : term57 A B x y.
Proof. exact (fun h0 : term56 A B x y => @lem7616334 A B x y h0 h1). Qed.
Lemma lem7616336 {A B : Type'} (x : cart A B) (y : cart A B) : term59 A B x y.
Proof. exact (fun h0 : term57 A B x y => @lem7616335 A B x y h0). Qed.
Lemma lem7616339 {A B : Type'} (x : cart A B) (y : cart A B) : term57 A B x y.
Proof. exact (@lem7616336 A B x y (@lem7616328 A B x y)). Qed.
Lemma lem7616340 {A B : Type'} (x : cart A B) (y : cart A B) : term57 A B x y.
Proof. exact (@lem7616339 A B x y). Qed.
Lemma lem7616352 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7616353 {A B : Type'} : (term60 A B) = (term61 A B).
Proof. exact (@lem7616352 (term55 A B)). Qed.
Lemma lem7616365 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem16462 t)). Qed.
Lemma lem7616366 {A B : Type'} (r : type35 A B) : (True = ((term62 A B r) = r)) = ((term62 A B r) = r).
Proof. exact (@lem7616365 ((term62 A B r) = r)). Qed.
Lemma lem7616367 {A B : Type'} : (term63 A B) = (term64 A B).
Proof. exact (fun_ext (fun r : type35 A B => @lem7616366 A B r)). Qed.
Lemma lem7616368 {A B : Type'} : (@all ((finite_image B) -> A)) = (@all ((finite_image B) -> A)).
Proof. exact (eq_refl (@all ((finite_image B) -> A))). Qed.
Lemma lem7616369 {A B : Type'} : (term65 A B) = (term66 A B).
Proof. exact (MK_COMB (@lem7616368 A B) (@lem7616367 A B)). Qed.
Lemma lem7616374 {A B : Type'} : (term67 A B) = (term67 A B).
Proof. exact (eq_refl (term67 A B)). Qed.
Lemma lem7616375 {A B : Type'} : (term55 A B) = (term68 A B).
Proof. exact (MK_COMB (@lem7616374 A B) (@lem7616369 A B)). Qed.
Lemma lem7616378 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7616379 {A B : Type'} : (term61 A B) = (term69 A B).
Proof. exact (MK_COMB (@lem7616378) (@lem7616375 A B)). Qed.
Lemma lem7616380 {A B : Type'} : (term60 A B) = (term69 A B).
Proof. exact (TRANS (@lem7616353 A B) (@lem7616379 A B)). Qed.
Lemma lem7616381 {A B : Type'} (x : cart A B) (y : cart A B) : (term70 A B x y) = (term70 A B x y).
Proof. exact (eq_refl (term70 A B x y)). Qed.
Lemma lem7616382 {A B : Type'} (x : cart A B) (y : cart A B) : (term56 A B x y) = (term71 A B x y).
Proof. exact (MK_COMB (@lem7616381 A B x y) (@lem7616380 A B)). Qed.
Lemma lem7616385 {A B : Type'} (y : cart A B) : (term72 A B y) = (term73 A B y).
Proof. exact (fun_ext (fun x : cart A B => @lem7616382 A B x y)). Qed.
Lemma lem7616386 {A B : Type'} : (@all (cart A B)) = (@all (cart A B)).
Proof. exact (eq_refl (@all (cart A B))). Qed.
Lemma lem7616387 {A B : Type'} (y : cart A B) : (term74 A B y) = (term75 A B y).
Proof. exact (MK_COMB (@lem7616386 A B) (@lem7616385 A B y)). Qed.
Lemma lem7616392 {A B : Type'} : (term76 A B) = (term77 A B).
Proof. exact (fun_ext (fun y : cart A B => @lem7616387 A B y)). Qed.
Lemma lem7616393 {A B : Type'} : (@all (cart A B)) = (@all (cart A B)).
Proof. exact (eq_refl (@all (cart A B))). Qed.
Lemma lem7616402 {A B : Type'} : (term78 A B) = (term79 A B).
Proof. exact (MK_COMB (@lem7616393 A B) (@lem7616392 A B)). Qed.
Lemma lem7616403 {A B : Type'} (r : type35 A B) : ((term62 A B r) = r) = ((term62 A B r) = r).
Proof. exact (eq_refl ((term62 A B r) = r)). Qed.
Lemma lem7616404 {A B : Type'} : (term64 A B) = (term64 A B).
Proof. exact (fun_ext (fun r : type35 A B => @lem7616403 A B r)). Qed.
Lemma lem7616405 {A B : Type'} : (@all ((finite_image B) -> A)) = (@all ((finite_image B) -> A)).
Proof. exact (eq_refl (@all ((finite_image B) -> A))). Qed.
Lemma lem7616406 {A B : Type'} : (term66 A B) = (term66 A B).
Proof. exact (MK_COMB (@lem7616405 A B) (@lem7616404 A B)). Qed.
Lemma lem7616407 {A B : Type'} (a : cart A B) : ((term80 A B a) = a) = ((term80 A B a) = a).
Proof. exact (eq_refl ((term80 A B a) = a)). Qed.
Lemma lem7616408 {A B : Type'} : (term81 A B) = (term81 A B).
Proof. exact (fun_ext (fun a : cart A B => @lem7616407 A B a)). Qed.
Lemma lem7616409 {A B : Type'} : (@all (cart A B)) = (@all (cart A B)).
Proof. exact (eq_refl (@all (cart A B))). Qed.
Lemma lem7616410 {A B : Type'} : (term82 A B) = (term82 A B).
Proof. exact (MK_COMB (@lem7616409 A B) (@lem7616408 A B)). Qed.
Lemma lem7616411 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7616412 {A B : Type'} : (term67 A B) = (term67 A B).
Proof. exact (MK_COMB (@lem7616411) (@lem7616410 A B)). Qed.
Lemma lem7616413 {A B : Type'} : (term68 A B) = (term68 A B).
Proof. exact (MK_COMB (@lem7616412 A B) (@lem7616406 A B)). Qed.
Lemma lem7616414 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7616415 {A B : Type'} : (term69 A B) = (term69 A B).
Proof. exact (MK_COMB (@lem7616414) (@lem7616413 A B)). Qed.
Lemma lem7616424 {A B : Type'} (x : cart A B) (y : cart A B) : (term70 A B x y) = (term70 A B x y).
Proof. exact (eq_refl (term70 A B x y)). Qed.
Lemma lem7616425 {A B : Type'} (x : cart A B) (y : cart A B) : (term71 A B x y) = (term71 A B x y).
Proof. exact (MK_COMB (@lem7616424 A B x y) (@lem7616415 A B)). Qed.
Lemma lem7616426 {A B : Type'} (y : cart A B) : (term73 A B y) = (term73 A B y).
Proof. exact (fun_ext (fun x : cart A B => @lem7616425 A B x y)). Qed.
Lemma lem7616427 {A B : Type'} : (@all (cart A B)) = (@all (cart A B)).
Proof. exact (eq_refl (@all (cart A B))). Qed.
Lemma lem7616428 {A B : Type'} (y : cart A B) : (term75 A B y) = (term75 A B y).
Proof. exact (MK_COMB (@lem7616427 A B) (@lem7616426 A B y)). Qed.
Lemma lem7616429 {A B : Type'} : (term77 A B) = (term77 A B).
Proof. exact (fun_ext (fun y : cart A B => @lem7616428 A B y)). Qed.
Lemma lem7616430 {A B : Type'} : (@all (cart A B)) = (@all (cart A B)).
Proof. exact (eq_refl (@all (cart A B))). Qed.
Lemma lem7616431 {A B : Type'} : (term79 A B) = (term79 A B).
Proof. exact (MK_COMB (@lem7616430 A B) (@lem7616429 A B)). Qed.
Lemma lem7616462 {A B : Type'} : (term78 A B) = (term79 A B).
Proof. exact (TRANS (@lem7616402 A B) (@lem7616431 A B)). Qed.
Lemma lem7616463 {A B : Type'} : (term79 A B) = (term78 A B).
Proof. exact (SYM (@lem7616462 A B)). Qed.
Lemma lem7616464 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term54 A B x y) : term54 A B x y.
Proof. exact (h1). Qed.
Lemma lem7616465 {A B : Type'} (h1 : term68 A B) : term68 A B.
Proof. exact (h1). Qed.
Lemma lem7616484 {A B : Type'} (x : cart A B) (y : cart A B) : (term54 A B x y) = (term83 A B x y).
Proof. exact (@lem17646 (x = y) ((@dest_cart A B x) = (@dest_cart A B y))). Qed.
Lemma lem7616486 {A B : Type'} (a : cart A B) : ((term80 A B a) = a) = ((term80 A B a) = a).
Proof. exact (eq_refl ((term80 A B a) = a)). Qed.
Lemma lem7616487 {A B : Type'} : (term81 A B) = (term81 A B).
Proof. exact (fun_ext (fun a : cart A B => @lem7616486 A B a)). Qed.
Lemma lem7616488 {A B : Type'} : (@all (cart A B)) = (@all (cart A B)).
Proof. exact (eq_refl (@all (cart A B))). Qed.
Lemma lem7616489 {A B : Type'} : (term82 A B) = (term82 A B).
Proof. exact (MK_COMB (@lem7616488 A B) (@lem7616487 A B)). Qed.
Lemma lem7616490 {A B : Type'} (r : type35 A B) : ((term62 A B r) = r) = ((term62 A B r) = r).
Proof. exact (eq_refl ((term62 A B r) = r)). Qed.
Lemma lem7616491 {A B : Type'} : (term64 A B) = (term64 A B).
Proof. exact (fun_ext (fun r : type35 A B => @lem7616490 A B r)). Qed.
Lemma lem7616492 {A B : Type'} : (@all ((finite_image B) -> A)) = (@all ((finite_image B) -> A)).
Proof. exact (eq_refl (@all ((finite_image B) -> A))). Qed.
Lemma lem7616493 {A B : Type'} : (term66 A B) = (term66 A B).
Proof. exact (MK_COMB (@lem7616492 A B) (@lem7616491 A B)). Qed.
Lemma lem7616494 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7616495 {A B : Type'} : (term67 A B) = (term67 A B).
Proof. exact (MK_COMB (@lem7616494) (@lem7616489 A B)). Qed.
Lemma lem7616508 {A B : Type'} : (term68 A B) = (term68 A B).
Proof. exact (MK_COMB (@lem7616495 A B) (@lem7616493 A B)). Qed.
Lemma lem7616509 {A B : Type'} (h1 : term68 A B) : term68 A B.
Proof. exact (EQ_MP (@lem7616508 A B) (@lem7616465 A B h1)). Qed.
Lemma lem7616551 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term54 A B x y) : term83 A B x y.
Proof. exact (EQ_MP (@lem7616484 A B x y) (@lem7616464 A B x y h1)). Qed.
Lemma lem7616560 {A B : Type'} (r : type35 A B) : ((term62 A B r) = r) = ((term62 A B r) = r).
Proof. exact (eq_refl ((term62 A B r) = r)). Qed.
Lemma lem7616561 {A B : Type'} : (term64 A B) = (term64 A B).
Proof. exact (fun_ext (fun r : type35 A B => @lem7616560 A B r)). Qed.
Lemma lem7616562 {A B : Type'} : (@all ((finite_image B) -> A)) = (@all ((finite_image B) -> A)).
Proof. exact (eq_refl (@all ((finite_image B) -> A))). Qed.
Lemma lem7616563 {A B : Type'} : (term66 A B) = (term66 A B).
Proof. exact (MK_COMB (@lem7616562 A B) (@lem7616561 A B)). Qed.
Lemma lem7616572 {A B : Type'} (a : cart A B) : ((term80 A B a) = a) = ((term80 A B a) = a).
Proof. exact (eq_refl ((term80 A B a) = a)). Qed.
Lemma lem7616573 {A B : Type'} : (term81 A B) = (term81 A B).
Proof. exact (fun_ext (fun a : cart A B => @lem7616572 A B a)). Qed.
Lemma lem7616574 {A B : Type'} : (@all (cart A B)) = (@all (cart A B)).
Proof. exact (eq_refl (@all (cart A B))). Qed.
Lemma lem7616575 {A B : Type'} : (term82 A B) = (term82 A B).
Proof. exact (MK_COMB (@lem7616574 A B) (@lem7616573 A B)). Qed.
Lemma lem7616576 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7616577 {A B : Type'} : (term67 A B) = (term67 A B).
Proof. exact (MK_COMB (@lem7616576) (@lem7616575 A B)). Qed.
Lemma lem7616578 {A B : Type'} : (term68 A B) = (term68 A B).
Proof. exact (MK_COMB (@lem7616577 A B) (@lem7616563 A B)). Qed.
Lemma lem7616579 {A B : Type'} (h1 : term68 A B) : term68 A B.
Proof. exact (EQ_MP (@lem7616578 A B) (@lem7616509 A B h1)). Qed.
Lemma lem7616581 {A B : Type'} (h1 : term68 A B) : term82 A B.
Proof. exact (proj1 (@lem7616579 A B h1)). Qed.
Lemma lem7616582 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term84 A B x y) : term84 A B x y.
Proof. exact (h1). Qed.
Lemma lem7616583 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term85 A B x y) : term85 A B x y.
Proof. exact (h1). Qed.
Lemma lem7616611 {A B : Type'} (a : cart A B) : ((term80 A B a) = a) = ((term80 A B a) = a).
Proof. exact (eq_refl ((term80 A B a) = a)). Qed.
Lemma lem7616612 {A B : Type'} : (term81 A B) = (term81 A B).
Proof. exact (fun_ext (fun a : cart A B => @lem7616611 A B a)). Qed.
Lemma lem7616613 {A B : Type'} : (@all (cart A B)) = (@all (cart A B)).
Proof. exact (eq_refl (@all (cart A B))). Qed.
Lemma lem7616615 {A B : Type'} : (term82 A B) = (term82 A B).
Proof. exact (MK_COMB (@lem7616613 A B) (@lem7616612 A B)). Qed.
Lemma lem7616616 {A B : Type'} (h1 : term68 A B) : term82 A B.
Proof. exact (EQ_MP (@lem7616615 A B) (@lem7616581 A B h1)). Qed.
Lemma lem7616638 {A B : Type'} (_98047 : cart A B) (h1 : term68 A B) : term86 A B _98047.
Proof. exact (@lem7616616 A B h1 _98047). Qed.
Lemma lem7616639 {A B : Type'} (_98047 : cart A B) : (term86 A B _98047) = ((term80 A B _98047) = _98047).
Proof. exact (eq_refl (term86 A B _98047)). Qed.
Lemma lem7616649 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term84 A B x y) : x = y.
Proof. exact (proj1 (@lem7616582 A B x y h1)). Qed.
Lemma lem7616651 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term84 A B x y) : term87 A B x y.
Proof. exact (proj2 (@lem7616582 A B x y h1)). Qed.
Lemma lem7616657 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term85 A B x y) : term88 A B x y.
Proof. exact (proj1 (@lem7616583 A B x y h1)). Qed.
Lemma lem7616702 {A B : Type'} (y : cart A B) : (term89 A B y) = (term89 A B y).
Proof. exact (eq_refl (term89 A B y)). Qed.
Lemma lem7616703 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term84 A B x y) : (term90 A B y x) = (term91 A B y).
Proof. exact (MK_COMB (@lem7616702 A B y) (@lem7616649 A B x y h1)). Qed.
Lemma lem7616704 {A B : Type'} (y : cart A B) : (term91 A B y) = (term92 A B y).
Proof. exact (eq_refl (term91 A B y)). Qed.
Lemma lem7616705 {A B : Type'} (y : cart A B) (x : cart A B) : (term93 A B y x) = (term93 A B y x).
Proof. exact (eq_refl (term93 A B y x)). Qed.
Lemma lem7616706 {A B : Type'} (x : cart A B) (y : cart A B) : ((term90 A B y x) = (term91 A B y)) = ((term90 A B y x) = (term92 A B y)).
Proof. exact (MK_COMB (@lem7616705 A B y x) (@lem7616704 A B y)). Qed.
Lemma lem7616707 {A B : Type'} (x : cart A B) (y : cart A B) : (term90 A B y x) = (term87 A B x y).
Proof. exact (eq_refl (term90 A B y x)). Qed.
Lemma lem7616708 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7616709 {A B : Type'} (x : cart A B) (y : cart A B) : (term93 A B y x) = (term94 A B x y).
Proof. exact (MK_COMB (@lem7616708) (@lem7616707 A B x y)). Qed.
Lemma lem7616710 {A B : Type'} (y : cart A B) : (term92 A B y) = (term92 A B y).
Proof. exact (eq_refl (term92 A B y)). Qed.
Lemma lem7616711 {A B : Type'} (x : cart A B) (y : cart A B) : ((term90 A B y x) = (term92 A B y)) = ((term87 A B x y) = (term92 A B y)).
Proof. exact (MK_COMB (@lem7616709 A B x y) (@lem7616710 A B y)). Qed.
Lemma lem7616712 {A B : Type'} (x : cart A B) (y : cart A B) : ((term90 A B y x) = (term91 A B y)) = ((term87 A B x y) = (term92 A B y)).
Proof. exact (TRANS (@lem7616706 A B x y) (@lem7616711 A B x y)). Qed.
Lemma lem7616713 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term84 A B x y) : (term87 A B x y) = (term92 A B y).
Proof. exact (EQ_MP (@lem7616712 A B x y) (@lem7616703 A B x y h1)). Qed.
Lemma lem7616714 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term84 A B x y) : term92 A B y.
Proof. exact (EQ_MP (@lem7616713 A B x y h1) (@lem7616651 A B x y h1)). Qed.
Lemma lem7616736 {A B : Type'} (x : type35 A B) : x = x.
Proof. exact (@lem21386 (type35 A B) x). Qed.
Lemma lem7616737 {A B : Type'} (x : type35 A B) : x = x.
Proof. exact (@lem7616736 A B x). Qed.
Lemma lem7616738 {A B : Type'} (y : cart A B) : (@dest_cart A B y) = (@dest_cart A B y).
Proof. exact (@lem7616737 A B (@dest_cart A B y)). Qed.
Lemma lem7616739 {A B : Type'} (y : cart A B) : term95 A B y.
Proof. exact (fun h0 : term92 A B y => @lem7616738 A B y). Qed.
Lemma lem7616741 (p : Prop) : (term96 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7616742 {A B : Type'} (y : cart A B) : (term95 A B y) = ((@dest_cart A B y) = (@dest_cart A B y)).
Proof. exact (@lem7616741 ((@dest_cart A B y) = (@dest_cart A B y))). Qed.
Lemma lem7616743 {A B : Type'} (y : cart A B) : (@dest_cart A B y) = (@dest_cart A B y).
Proof. exact (EQ_MP (@lem7616742 A B y) (@lem7616739 A B y)). Qed.
Lemma lem7616746 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7616748 {A B : Type'} (y : cart A B) : (term92 A B y) = (term97 A B y).
Proof. exact (@lem7616746 ((@dest_cart A B y) = (@dest_cart A B y))). Qed.
Lemma lem7616751 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term84 A B x y) : term97 A B y.
Proof. exact (EQ_MP (@lem7616748 A B y) (@lem7616714 A B x y h1)). Qed.
Lemma lem7616754 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term84 A B x y) : False.
Proof. exact (@lem7616751 A B x y h1 (@lem7616743 A B y)). Qed.
Lemma lem7616755 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term84 A B x y) : term98.
Proof. exact (fun h0 : ~ False => @lem7616754 A B x y h1). Qed.
Lemma lem7616757 (p : Prop) : (term96 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7616758 : term98 = False.
Proof. exact (@lem7616757 False). Qed.
Lemma lem7616768 {A B : Type'} : (@mk_cart A B) = (@mk_cart A B).
Proof. exact (eq_refl (@mk_cart A B)). Qed.
Lemma lem7616769 {A B : Type'} (_98063 : type35 A B) (_98064 : type35 A B) (h1 : _98063 = _98064) : _98063 = _98064.
Proof. exact (h1). Qed.
Lemma lem7616770 {A B : Type'} (_98063 : type35 A B) (_98064 : type35 A B) (h1 : _98063 = _98064) : (@mk_cart A B _98063) = (@mk_cart A B _98064).
Proof. exact (MK_COMB (@lem7616768 A B) (@lem7616769 A B _98063 _98064 h1)). Qed.
Lemma lem7616771 {A B : Type'} (_98063 : type35 A B) (_98064 : type35 A B) : term99 A B _98063 _98064.
Proof. exact (fun h0 : _98063 = _98064 => @lem7616770 A B _98063 _98064 h0). Qed.
Lemma lem7616773 (a : Prop) (b : Prop) : (a -> b) = (term100 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem7616774 {A B : Type'} (_98063 : type35 A B) (_98064 : type35 A B) : (term99 A B _98063 _98064) = (term101 A B _98063 _98064).
Proof. exact (@lem7616773 (_98063 = _98064) ((@mk_cart A B _98063) = (@mk_cart A B _98064))). Qed.
Lemma lem7616775 {A B : Type'} (_98063 : type35 A B) (_98064 : type35 A B) : term101 A B _98063 _98064.
Proof. exact (EQ_MP (@lem7616774 A B _98063 _98064) (@lem7616771 A B _98063 _98064)). Qed.
Lemma lem7616777 {A B : Type'} (x : cart A B) (y : cart A B) (z : cart A B) : term102 A B x y z.
Proof. exact (@lem21385 (cart A B) x y z). Qed.
Lemma lem7616781 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term85 A B x y) : (@dest_cart A B x) = (@dest_cart A B y).
Proof. exact (proj2 (@lem7616583 A B x y h1)). Qed.
Lemma lem7616782 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term85 A B x y) : term103 A B x y.
Proof. exact (fun h0 : term87 A B x y => @lem7616781 A B x y h1). Qed.
Lemma lem7616784 (p : Prop) : (term96 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7616785 {A B : Type'} (x : cart A B) (y : cart A B) : (term103 A B x y) = ((@dest_cart A B x) = (@dest_cart A B y)).
Proof. exact (@lem7616784 ((@dest_cart A B x) = (@dest_cart A B y))). Qed.
Lemma lem7616786 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term85 A B x y) : (@dest_cart A B x) = (@dest_cart A B y).
Proof. exact (EQ_MP (@lem7616785 A B x y) (@lem7616782 A B x y h1)). Qed.
Lemma lem7616792 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7616793 {A B : Type'} (_98063 : type35 A B) (_98064 : type35 A B) : (term101 A B _98063 _98064) = (term104 A B _98063 _98064).
Proof. exact (@lem7616792 ((@mk_cart A B _98063) = (@mk_cart A B _98064)) (term105 A B _98063 _98064)). Qed.
Lemma lem7616803 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7616804 {A B : Type'} (_98063 : type35 A B) (_98064 : type35 A B) : (term106 A B _98063 _98064) = (term107 A B _98063 _98064).
Proof. exact (MK_COMB (@lem7616803) (@lem7616793 A B _98063 _98064)). Qed.
Lemma lem7616814 {A B : Type'} (_98063 : type35 A B) (_98064 : type35 A B) : (term104 A B _98063 _98064) = (term104 A B _98063 _98064).
Proof. exact (eq_refl (term104 A B _98063 _98064)). Qed.
Lemma lem7616815 {A B : Type'} (_98063 : type35 A B) (_98064 : type35 A B) : ((term101 A B _98063 _98064) = (term104 A B _98063 _98064)) = ((term104 A B _98063 _98064) = (term104 A B _98063 _98064)).
Proof. exact (MK_COMB (@lem7616804 A B _98063 _98064) (@lem7616814 A B _98063 _98064)). Qed.
Lemma lem7616817 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7616818 (x : Prop) : (x = x) = True.
Proof. exact (@lem7616817 Prop x). Qed.
Lemma lem7616819 {A B : Type'} (_98063 : type35 A B) (_98064 : type35 A B) : ((term104 A B _98063 _98064) = (term104 A B _98063 _98064)) = True.
Proof. exact (@lem7616818 (term104 A B _98063 _98064)). Qed.
Lemma lem7616820 {A B : Type'} (_98063 : type35 A B) (_98064 : type35 A B) : ((term101 A B _98063 _98064) = (term104 A B _98063 _98064)) = True.
Proof. exact (TRANS (@lem7616815 A B _98063 _98064) (@lem7616819 A B _98063 _98064)). Qed.
Lemma lem7616821 {A B : Type'} (_98063 : type35 A B) (_98064 : type35 A B) : True = ((term101 A B _98063 _98064) = (term104 A B _98063 _98064)).
Proof. exact (SYM (@lem7616820 A B _98063 _98064)). Qed.
Lemma lem7616822 {A B : Type'} (_98063 : type35 A B) (_98064 : type35 A B) : (term101 A B _98063 _98064) = (term104 A B _98063 _98064).
Proof. exact (EQ_MP (@lem7616821 A B _98063 _98064) (@lem0)). Qed.
Lemma lem7616823 {A B : Type'} (_98063 : type35 A B) (_98064 : type35 A B) : term104 A B _98063 _98064.
Proof. exact (EQ_MP (@lem7616822 A B _98063 _98064) (@lem7616775 A B _98063 _98064)). Qed.
Lemma lem7616825 (b : Prop) (a : Prop) : (a \/ b) = (term108 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7616826 {A B : Type'} (_98063 : type35 A B) (_98064 : type35 A B) : (term104 A B _98063 _98064) = (term109 A B _98063 _98064).
Proof. exact (@lem7616825 (term105 A B _98063 _98064) ((@mk_cart A B _98063) = (@mk_cart A B _98064))). Qed.
Lemma lem7616828 (a : Prop) : (term110 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7616829 {A B : Type'} (_98063 : type35 A B) (_98064 : type35 A B) : (term111 A B _98063 _98064) = (_98063 = _98064).
Proof. exact (@lem7616828 (_98063 = _98064)). Qed.
Lemma lem7616830 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7616831 {A B : Type'} (_98063 : type35 A B) (_98064 : type35 A B) : (term112 A B _98063 _98064) = (term113 A B _98063 _98064).
Proof. exact (MK_COMB (@lem7616830) (@lem7616829 A B _98063 _98064)). Qed.
Lemma lem7616832 {A B : Type'} (_98063 : type35 A B) (_98064 : type35 A B) : ((@mk_cart A B _98063) = (@mk_cart A B _98064)) = ((@mk_cart A B _98063) = (@mk_cart A B _98064)).
Proof. exact (eq_refl ((@mk_cart A B _98063) = (@mk_cart A B _98064))). Qed.
Lemma lem7616833 {A B : Type'} (_98063 : type35 A B) (_98064 : type35 A B) : (term109 A B _98063 _98064) = (term99 A B _98063 _98064).
Proof. exact (MK_COMB (@lem7616831 A B _98063 _98064) (@lem7616832 A B _98063 _98064)). Qed.
Lemma lem7616834 {A B : Type'} (_98063 : type35 A B) (_98064 : type35 A B) : (term104 A B _98063 _98064) = (term99 A B _98063 _98064).
Proof. exact (TRANS (@lem7616826 A B _98063 _98064) (@lem7616833 A B _98063 _98064)). Qed.
Lemma lem7616837 {A B : Type'} (_98063 : type35 A B) (_98064 : type35 A B) : term99 A B _98063 _98064.
Proof. exact (EQ_MP (@lem7616834 A B _98063 _98064) (@lem7616823 A B _98063 _98064)). Qed.
Lemma lem7616838 {A B : Type'} (_98063 : type35 A B) (_98064 : type35 A B) : term99 A B _98063 _98064.
Proof. exact (@lem7616837 A B _98063 _98064). Qed.
Lemma lem7616839 {A B : Type'} (x : cart A B) (y : cart A B) : term114 A B x y.
Proof. exact (@lem7616838 A B (@dest_cart A B x) (@dest_cart A B y)). Qed.
Lemma lem7616842 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term85 A B x y) : (term80 A B x) = (term80 A B y).
Proof. exact (@lem7616839 A B x y (@lem7616786 A B x y h1)). Qed.
Lemma lem7616843 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term85 A B x y) : term115 A B x y.
Proof. exact (fun h0 : term116 A B x y => @lem7616842 A B x y h1). Qed.
Lemma lem7616845 (p : Prop) : (term96 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7616846 {A B : Type'} (x : cart A B) (y : cart A B) : (term115 A B x y) = ((term80 A B x) = (term80 A B y)).
Proof. exact (@lem7616845 ((term80 A B x) = (term80 A B y))). Qed.
Lemma lem7616847 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term85 A B x y) : (term80 A B x) = (term80 A B y).
Proof. exact (EQ_MP (@lem7616846 A B x y) (@lem7616843 A B x y h1)). Qed.
Lemma lem7616849 {A B : Type'} (_98047 : cart A B) (h1 : term68 A B) : (term80 A B _98047) = _98047.
Proof. exact (EQ_MP (@lem7616639 A B _98047) (@lem7616638 A B _98047 h1)). Qed.
Lemma lem7616850 {A B : Type'} (_98047 : cart A B) (h1 : term68 A B) : (term80 A B _98047) = _98047.
Proof. exact (@lem7616849 A B _98047 h1). Qed.
Lemma lem7616851 {A B : Type'} (x : cart A B) (h1 : term68 A B) : (term80 A B x) = x.
Proof. exact (@lem7616850 A B x h1). Qed.
Lemma lem7616852 {A B : Type'} (x : cart A B) (h1 : term68 A B) : term117 A B x.
Proof. exact (fun h0 : term118 A B x => @lem7616851 A B x h1). Qed.
Lemma lem7616854 (p : Prop) : (term96 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7616855 {A B : Type'} (x : cart A B) : (term117 A B x) = ((term80 A B x) = x).
Proof. exact (@lem7616854 ((term80 A B x) = x)). Qed.
Lemma lem7616856 {A B : Type'} (x : cart A B) (h1 : term68 A B) : (term80 A B x) = x.
Proof. exact (EQ_MP (@lem7616855 A B x) (@lem7616852 A B x h1)). Qed.
Lemma lem7616874 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7616875 {A B : Type'} (y : cart A B) (x : cart A B) (z : cart A B) : (term119 A B x y z) = (term120 A B y x z).
Proof. exact (@lem7616874 (y = z) (term88 A B x z)). Qed.
Lemma lem7616885 {A B : Type'} (x : cart A B) (y : cart A B) : (term121 A B x y) = (term121 A B x y).
Proof. exact (eq_refl (term121 A B x y)). Qed.
Lemma lem7616886 {A B : Type'} (y : cart A B) (x : cart A B) (z : cart A B) : (term102 A B x y z) = (term122 A B y x z).
Proof. exact (MK_COMB (@lem7616885 A B x y) (@lem7616875 A B y x z)). Qed.
Lemma lem7616890 (q : Prop) (p : Prop) (r : Prop) : (term123 p q r) = (term123 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7616891 {A B : Type'} (y : cart A B) (x : cart A B) (z : cart A B) : (term122 A B y x z) = (term124 A B y x z).
Proof. exact (@lem7616890 (y = z) (term88 A B x y) (term88 A B x z)). Qed.
Lemma lem7616913 {A B : Type'} (y : cart A B) (x : cart A B) (z : cart A B) : (term102 A B x y z) = (term124 A B y x z).
Proof. exact (TRANS (@lem7616886 A B y x z) (@lem7616891 A B y x z)). Qed.
Lemma lem7616914 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7616915 {A B : Type'} (y : cart A B) (x : cart A B) (z : cart A B) : (term125 A B x y z) = (term126 A B y x z).
Proof. exact (MK_COMB (@lem7616914) (@lem7616913 A B y x z)). Qed.
Lemma lem7616937 {A B : Type'} (y : cart A B) (x : cart A B) (z : cart A B) : (term124 A B y x z) = (term124 A B y x z).
Proof. exact (eq_refl (term124 A B y x z)). Qed.
Lemma lem7616938 {A B : Type'} (y : cart A B) (x : cart A B) (z : cart A B) : ((term102 A B x y z) = (term124 A B y x z)) = ((term124 A B y x z) = (term124 A B y x z)).
Proof. exact (MK_COMB (@lem7616915 A B y x z) (@lem7616937 A B y x z)). Qed.
Lemma lem7616940 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7616941 (x : Prop) : (x = x) = True.
Proof. exact (@lem7616940 Prop x). Qed.
Lemma lem7616942 {A B : Type'} (y : cart A B) (x : cart A B) (z : cart A B) : ((term124 A B y x z) = (term124 A B y x z)) = True.
Proof. exact (@lem7616941 (term124 A B y x z)). Qed.
Lemma lem7616943 {A B : Type'} (y : cart A B) (x : cart A B) (z : cart A B) : ((term102 A B x y z) = (term124 A B y x z)) = True.
Proof. exact (TRANS (@lem7616938 A B y x z) (@lem7616942 A B y x z)). Qed.
Lemma lem7616944 {A B : Type'} (y : cart A B) (x : cart A B) (z : cart A B) : True = ((term102 A B x y z) = (term124 A B y x z)).
Proof. exact (SYM (@lem7616943 A B y x z)). Qed.
Lemma lem7616945 {A B : Type'} (y : cart A B) (x : cart A B) (z : cart A B) : (term102 A B x y z) = (term124 A B y x z).
Proof. exact (EQ_MP (@lem7616944 A B y x z) (@lem0)). Qed.
Lemma lem7616946 {A B : Type'} (y : cart A B) (x : cart A B) (z : cart A B) : term124 A B y x z.
Proof. exact (EQ_MP (@lem7616945 A B y x z) (@lem7616777 A B x y z)). Qed.
Lemma lem7616948 (b : Prop) (a : Prop) : (a \/ b) = (term108 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7616949 {A B : Type'} (x : cart A B) (y : cart A B) (z : cart A B) : (term124 A B y x z) = (term127 A B x y z).
Proof. exact (@lem7616948 (term128 A B y x z) (y = z)). Qed.
Lemma lem7616951 (a : Prop) (b : Prop) : (term129 a b) = (term130 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7616952 {A B : Type'} (y : cart A B) (x : cart A B) (z : cart A B) : (term131 A B y x z) = (term132 A B y x z).
Proof. exact (@lem7616951 (term88 A B x y) (term88 A B x z)). Qed.
Lemma lem7616954 (a : Prop) : (term110 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7616955 {A B : Type'} (x : cart A B) (y : cart A B) : (term133 A B x y) = (x = y).
Proof. exact (@lem7616954 (x = y)). Qed.
Lemma lem7616956 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7616957 {A B : Type'} (x : cart A B) (y : cart A B) : (term134 A B x y) = (term135 A B x y).
Proof. exact (MK_COMB (@lem7616956) (@lem7616955 A B x y)). Qed.
Lemma lem7616959 (a : Prop) : (term110 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7616960 {A B : Type'} (x : cart A B) (z : cart A B) : (term133 A B x z) = (x = z).
Proof. exact (@lem7616959 (x = z)). Qed.
Lemma lem7616961 {A B : Type'} (y : cart A B) (x : cart A B) (z : cart A B) : (term132 A B y x z) = (term136 A B y x z).
Proof. exact (MK_COMB (@lem7616957 A B x y) (@lem7616960 A B x z)). Qed.
Lemma lem7616962 {A B : Type'} (y : cart A B) (x : cart A B) (z : cart A B) : (term131 A B y x z) = (term136 A B y x z).
Proof. exact (TRANS (@lem7616952 A B y x z) (@lem7616961 A B y x z)). Qed.
Lemma lem7616963 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7616964 {A B : Type'} (y : cart A B) (x : cart A B) (z : cart A B) : (term137 A B y x z) = (term138 A B y x z).
Proof. exact (MK_COMB (@lem7616963) (@lem7616962 A B y x z)). Qed.
Lemma lem7616965 {A B : Type'} (y : cart A B) (z : cart A B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem7616966 {A B : Type'} (x : cart A B) (y : cart A B) (z : cart A B) : (term127 A B x y z) = (term139 A B x y z).
Proof. exact (MK_COMB (@lem7616964 A B y x z) (@lem7616965 A B y z)). Qed.
Lemma lem7616967 {A B : Type'} (x : cart A B) (y : cart A B) (z : cart A B) : (term124 A B y x z) = (term139 A B x y z).
Proof. exact (TRANS (@lem7616949 A B x y z) (@lem7616966 A B x y z)). Qed.
Lemma lem7616969 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term68 A B) (h2 : term85 A B x y) : term140 A B y x.
Proof. exact (conj (@lem7616847 A B x y h2) (@lem7616856 A B x h1)). Qed.
Lemma lem7616971 {A B : Type'} (x : cart A B) (y : cart A B) (z : cart A B) : term139 A B x y z.
Proof. exact (EQ_MP (@lem7616967 A B x y z) (@lem7616946 A B y x z)). Qed.
Lemma lem7616972 {A B : Type'} (x : cart A B) (y : cart A B) (z : cart A B) : term139 A B x y z.
Proof. exact (@lem7616971 A B x y z). Qed.
Lemma lem7616973 {A B : Type'} (y : cart A B) (x : cart A B) : term141 A B y x.
Proof. exact (@lem7616972 A B (term80 A B x) (term80 A B y) x). Qed.
Lemma lem7616976 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term68 A B) (h2 : term85 A B x y) : (term80 A B y) = x.
Proof. exact (@lem7616973 A B y x (@lem7616969 A B x y h1 h2)). Qed.
Lemma lem7616977 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term68 A B) (h2 : term85 A B x y) : term142 A B y x.
Proof. exact (fun h0 : term143 A B y x => @lem7616976 A B x y h1 h2). Qed.
Lemma lem7616979 (p : Prop) : (term96 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7616980 {A B : Type'} (y : cart A B) (x : cart A B) : (term142 A B y x) = ((term80 A B y) = x).
Proof. exact (@lem7616979 ((term80 A B y) = x)). Qed.
Lemma lem7616981 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term68 A B) (h2 : term85 A B x y) : (term80 A B y) = x.
Proof. exact (EQ_MP (@lem7616980 A B y x) (@lem7616977 A B x y h1 h2)). Qed.
Lemma lem7616983 {A B : Type'} (_98047 : cart A B) (h1 : term68 A B) : (term80 A B _98047) = _98047.
Proof. exact (EQ_MP (@lem7616639 A B _98047) (@lem7616638 A B _98047 h1)). Qed.
Lemma lem7616984 {A B : Type'} (_98047 : cart A B) (h1 : term68 A B) : (term80 A B _98047) = _98047.
Proof. exact (@lem7616983 A B _98047 h1). Qed.
Lemma lem7616985 {A B : Type'} (y : cart A B) (h1 : term68 A B) : (term80 A B y) = y.
Proof. exact (@lem7616984 A B y h1). Qed.
Lemma lem7616986 {A B : Type'} (y : cart A B) (h1 : term68 A B) : term117 A B y.
Proof. exact (fun h0 : term118 A B y => @lem7616985 A B y h1). Qed.
Lemma lem7616988 (p : Prop) : (term96 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7616989 {A B : Type'} (y : cart A B) : (term117 A B y) = ((term80 A B y) = y).
Proof. exact (@lem7616988 ((term80 A B y) = y)). Qed.
Lemma lem7616990 {A B : Type'} (y : cart A B) (h1 : term68 A B) : (term80 A B y) = y.
Proof. exact (EQ_MP (@lem7616989 A B y) (@lem7616986 A B y h1)). Qed.
Lemma lem7616991 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term68 A B) (h2 : term85 A B x y) : term144 A B x y.
Proof. exact (conj (@lem7616981 A B x y h1 h2) (@lem7616990 A B y h1)). Qed.
Lemma lem7616993 {A B : Type'} (x : cart A B) (y : cart A B) (z : cart A B) : term139 A B x y z.
Proof. exact (EQ_MP (@lem7616967 A B x y z) (@lem7616946 A B y x z)). Qed.
Lemma lem7616994 {A B : Type'} (x : cart A B) (y : cart A B) (z : cart A B) : term139 A B x y z.
Proof. exact (@lem7616993 A B x y z). Qed.
Lemma lem7616995 {A B : Type'} (x : cart A B) (y : cart A B) : term145 A B x y.
Proof. exact (@lem7616994 A B (term80 A B y) x y). Qed.
Lemma lem7616998 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term68 A B) (h2 : term85 A B x y) : x = y.
Proof. exact (@lem7616995 A B x y (@lem7616991 A B x y h1 h2)). Qed.
Lemma lem7616999 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term68 A B) (h2 : term85 A B x y) : term146 A B x y.
Proof. exact (fun h0 : term88 A B x y => @lem7616998 A B x y h1 h2). Qed.
Lemma lem7617001 (p : Prop) : (term96 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7617002 {A B : Type'} (x : cart A B) (y : cart A B) : (term146 A B x y) = (x = y).
Proof. exact (@lem7617001 (x = y)). Qed.
Lemma lem7617003 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term68 A B) (h2 : term85 A B x y) : x = y.
Proof. exact (EQ_MP (@lem7617002 A B x y) (@lem7616999 A B x y h1 h2)). Qed.
Lemma lem7617006 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7617008 {A B : Type'} (x : cart A B) (y : cart A B) : (term88 A B x y) = (term147 A B x y).
Proof. exact (@lem7617006 (x = y)). Qed.
Lemma lem7617011 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term85 A B x y) : term147 A B x y.
Proof. exact (EQ_MP (@lem7617008 A B x y) (@lem7616657 A B x y h1)). Qed.
Lemma lem7617014 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term68 A B) (h2 : term85 A B x y) : False.
Proof. exact (@lem7617011 A B x y h2 (@lem7617003 A B x y h1 h2)). Qed.
Lemma lem7617015 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term68 A B) (h2 : term85 A B x y) : term98.
Proof. exact (fun h0 : ~ False => @lem7617014 A B x y h1 h2). Qed.
Lemma lem7617017 (p : Prop) : (term96 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7617018 : term98 = False.
Proof. exact (@lem7617017 False). Qed.
Lemma lem7617019 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term68 A B) (h2 : term85 A B x y) : False.
Proof. exact (EQ_MP (@lem7617018) (@lem7617015 A B x y h1 h2)). Qed.
Lemma lem7617020 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term84 A B x y) : False.
Proof. exact (EQ_MP (@lem7616758) (@lem7616755 A B x y h1)). Qed.
Lemma lem7617021 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term54 A B x y) (h2 : term68 A B) : False.
Proof. exact (or_elim (@lem7616551 A B x y h1) (fun h0 : term84 A B x y => @lem7617020 A B x y h0) (fun h0 : term85 A B x y => @lem7617019 A B x y h2 h0)). Qed.
Lemma lem7617022 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term54 A B x y) (h2 : term68 A B) : (term68 A B) = False.
Proof. exact (prop_ext (fun h3 : term68 A B => @lem7617021 A B x y h1 h2) (fun h3 : False => @lem7616579 A B h2)). Qed.
Lemma lem7617023 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term54 A B x y) (h2 : term68 A B) : False.
Proof. exact (EQ_MP (@lem7617022 A B x y h1 h2) (@lem7616579 A B h2)). Qed.
Lemma lem7617024 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term54 A B x y) (h2 : term68 A B) : (term68 A B) = False.
Proof. exact (prop_ext (fun h3 : term68 A B => @lem7617023 A B x y h1 h2) (fun h3 : False => @lem7616509 A B h2)). Qed.
Lemma lem7617025 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term54 A B x y) (h2 : term68 A B) : False.
Proof. exact (EQ_MP (@lem7617024 A B x y h1 h2) (@lem7616509 A B h2)). Qed.
Lemma lem7617026 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term54 A B x y) : term148 A B.
Proof. exact (fun h0 : term68 A B => @lem7617025 A B x y h1 h0). Qed.
Lemma lem7617027 {A B : Type'} : (term148 A B) = (term69 A B).
Proof. exact (@lem69 (term68 A B)). Qed.
Lemma lem7617028 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term54 A B x y) : term69 A B.
Proof. exact (EQ_MP (@lem7617027 A B) (@lem7617026 A B x y h1)). Qed.
Lemma lem7617029 {A B : Type'} (x : cart A B) (y : cart A B) : term71 A B x y.
Proof. exact (fun h0 : term54 A B x y => @lem7617028 A B x y h0). Qed.
Lemma lem7617034 {A B : Type'} (y : cart A B) : term75 A B y.
Proof. exact (fun x : cart A B => @lem7617029 A B x y). Qed.
Lemma lem7617039 {A B : Type'} : term79 A B.
Proof. exact (fun y : cart A B => @lem7617034 A B y). Qed.
Lemma lem7617040 {A B : Type'} : term78 A B.
Proof. exact (EQ_MP (@lem7616463 A B) (@lem7617039 A B)). Qed.
Lemma lem7617041 {A B : Type'} (y : cart A B) : term149 A B y.
Proof. exact (@lem7617040 A B y). Qed.
Lemma lem7617042 {A B : Type'} (y : cart A B) : (term149 A B y) = (term74 A B y).
Proof. exact (eq_refl (term149 A B y)). Qed.
Lemma lem7617043 {A B : Type'} (y : cart A B) : term74 A B y.
Proof. exact (EQ_MP (@lem7617042 A B y) (@lem7617041 A B y)). Qed.
Lemma lem7617044 {A B : Type'} (y : cart A B) (x : cart A B) : term150 A B y x.
Proof. exact (@lem7617043 A B y x). Qed.
Lemma lem7617045 {A B : Type'} (x : cart A B) (y : cart A B) : (term150 A B y x) = (term56 A B x y).
Proof. exact (eq_refl (term150 A B y x)). Qed.
Lemma lem7617046 {A B : Type'} (x : cart A B) (y : cart A B) : term56 A B x y.
Proof. exact (EQ_MP (@lem7617045 A B x y) (@lem7617044 A B y x)). Qed.
Lemma lem7617048 {A B : Type'} (x : cart A B) (y : cart A B) : term56 A B x y.
Proof. exact (@lem7616340 A B x y (@lem7617046 A B x y)). Qed.
Lemma lem7617049 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term54 A B x y) : term60 A B.
Proof. exact (@lem7617048 A B x y (@lem7616321 A B x y h1)). Qed.
Lemma lem7617050 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term54 A B x y) : False.
Proof. exact (@lem7617049 A B x y h1 (@lem7616322 A B)). Qed.
Lemma lem7617051 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term54 A B x y) : (term54 A B x y) = False.
Proof. exact (prop_ext (fun h2 : term54 A B x y => @lem7617050 A B x y h1) (fun h2 : False => @lem7616321 A B x y h1)). Qed.
Lemma lem7617052 {A B : Type'} (x : cart A B) (y : cart A B) (h1 : term54 A B x y) : False.
Proof. exact (EQ_MP (@lem7617051 A B x y h1) (@lem7616321 A B x y h1)). Qed.
Lemma lem7617053 {A B : Type'} (x : cart A B) (y : cart A B) : term53 A B x y.
Proof. exact (fun h0 : term54 A B x y => @lem7617052 A B x y h0). Qed.
Lemma lem7617054 {A B : Type'} (x : cart A B) (y : cart A B) : (x = y) = ((@dest_cart A B x) = (@dest_cart A B y)).
Proof. exact (EQ_MP (@lem7616320 A B x y) (@lem7617053 A B x y)). Qed.
Lemma lem7617055 {A B : Type'} (x : cart A B) (y : cart A B) : (x = y) = (term38 A B x y).
Proof. exact (EQ_MP (@lem7616316 A B x y) (@lem7617054 A B x y)). Qed.
Lemma lem7617056 {A B : Type'} (x : cart A B) (y : cart A B) : (x = y) = (term26 A B x y).
Proof. exact (EQ_MP (@lem7616278 A B x y) (@lem7617055 A B x y)). Qed.
Lemma lem7617061 {A B : Type'} (x : cart A B) : term151 A B x.
Proof. exact (fun y : cart A B => @lem7617056 A B x y). Qed.
Lemma lem7617066 {A B : Type'} : term152 A B.
Proof. exact (fun x : cart A B => @lem7617061 A B x). Qed.
