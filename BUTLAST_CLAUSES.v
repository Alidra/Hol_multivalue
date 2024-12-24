Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import BUTLAST_CLAUSES_term_abbrevs.
Require Import NOT_CONS_NIL_spec.
Require Import thm0_spec.
Require Import thm1098917_spec.
Require Import thm1098923_spec.
Require Import thm1098924_spec.
Require Import thm12653_spec.
Require Import thm15249_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm82_spec.
Lemma lem1200147 {A : Type'} (h : A) : term0 A h.
Proof. exact (@lem1111523 A h). Qed.
Lemma lem1200148 {A : Type'} (h : A) : (term0 A h) = (term1 A h).
Proof. exact (eq_refl (term0 A h)). Qed.
Lemma lem1200149 {A : Type'} (h : A) : term1 A h.
Proof. exact (EQ_MP (@lem1200148 A h) (@lem1200147 A h)). Qed.
Lemma lem1200150 {A : Type'} (h : A) (t : list A) : term2 A h t.
Proof. exact (@lem1200149 A h t). Qed.
Lemma lem1200151 {A : Type'} (h : A) (t : list A) : (term2 A h t) = (term3 A h t).
Proof. exact (eq_refl (term2 A h t)). Qed.
Lemma lem1200152 {A : Type'} (h : A) (t : list A) : term3 A h t.
Proof. exact (EQ_MP (@lem1200151 A h t) (@lem1200150 A h t)). Qed.
Lemma lem1200153 {A : Type'} (h : A) (t : list A) : term4 A h t.
Proof. exact (@lem82 ((@cons A h t) = (@nil A))). Qed.
Lemma lem1200173 {_25251 : Type'} : (@List.removelast _25251 (@nil _25251)) = (@nil _25251).
Proof. exact (proj1 (@lem1098917 _25251)). Qed.
Lemma lem1200174 {A : Type'} : (@List.removelast A (@nil A)) = (@nil A).
Proof. exact (@lem1200173 A). Qed.
Lemma lem1200175 {A : Type'} : (@eq (list A)) = (@eq (list A)).
Proof. exact (eq_refl (@eq (list A))). Qed.
Lemma lem1200176 {A : Type'} : (term5 A) = (@eq (list A) (@nil A)).
Proof. exact (MK_COMB (@lem1200175 A) (@lem1200174 A)). Qed.
Lemma lem1200177 {A : Type'} : (@nil A) = (@nil A).
Proof. exact (eq_refl (@nil A)). Qed.
Lemma lem1200178 {A : Type'} : ((@List.removelast A (@nil A)) = (@nil A)) = ((@nil A) = (@nil A)).
Proof. exact (MK_COMB (@lem1200176 A) (@lem1200177 A)). Qed.
Lemma lem1200180 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1200181 {A : Type'} (x : list A) : (x = x) = True.
Proof. exact (@lem1200180 (list A) x). Qed.
Lemma lem1200182 {A : Type'} : ((@nil A) = (@nil A)) = True.
Proof. exact (@lem1200181 A (@nil A)). Qed.
Lemma lem1200183 {A : Type'} : ((@List.removelast A (@nil A)) = (@nil A)) = True.
Proof. exact (TRANS (@lem1200178 A) (@lem1200182 A)). Qed.
Lemma lem1200184 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1200185 {A : Type'} : (term6 A) = (and True).
Proof. exact (MK_COMB (@lem1200184) (@lem1200183 A)). Qed.
Lemma lem1200195 {_25251 : Type'} (h : _25251) (t : list _25251) : (term7 _25251 h t) = (term8 _25251 h t).
Proof. exact (EQ_MP (@lem1098924 _25251 h t) (@lem1098923 _25251 h t)). Qed.
Lemma lem1200196 {A : Type'} (h : A) (t : list A) : (term7 A h t) = (term8 A h t).
Proof. exact (@lem1200195 A h t). Qed.
Lemma lem1200197 {A : Type'} (a : A) : (term9 A a) = (term10 A a).
Proof. exact (@lem1200196 A a (@nil A)). Qed.
Lemma lem1200199 {_2975 _2982 : Type'} (x : _2982) (z : _2975) (y : _2975) : (term11 _2975 _2982 x y z) = y.
Proof. exact (EQ_MP (@lem15249 _2975 _2982 x z y) (@lem0)). Qed.
Lemma lem1200200 {A : Type'} (x : list A) (z : list A) (y : list A) : (term12 A x y z) = y.
Proof. exact (@lem1200199 (list A) (list A) x z y). Qed.
Lemma lem1200201 {A : Type'} (a : A) : (term10 A a) = (@nil A).
Proof. exact (@lem1200200 A (@nil A) (term13 A a) (@nil A)). Qed.
Lemma lem1200202 {A : Type'} (a : A) : (term9 A a) = (@nil A).
Proof. exact (TRANS (@lem1200197 A a) (@lem1200201 A a)). Qed.
Lemma lem1200203 {A : Type'} : (@eq (list A)) = (@eq (list A)).
Proof. exact (eq_refl (@eq (list A))). Qed.
Lemma lem1200204 {A : Type'} (a : A) : (term14 A a) = (@eq (list A) (@nil A)).
Proof. exact (MK_COMB (@lem1200203 A) (@lem1200202 A a)). Qed.
Lemma lem1200205 {A : Type'} : (@nil A) = (@nil A).
Proof. exact (eq_refl (@nil A)). Qed.
Lemma lem1200206 {A : Type'} (a : A) : ((term9 A a) = (@nil A)) = ((@nil A) = (@nil A)).
Proof. exact (MK_COMB (@lem1200204 A a) (@lem1200205 A)). Qed.
Lemma lem1200208 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1200209 {A : Type'} (x : list A) : (x = x) = True.
Proof. exact (@lem1200208 (list A) x). Qed.
Lemma lem1200210 {A : Type'} : ((@nil A) = (@nil A)) = True.
Proof. exact (@lem1200209 A (@nil A)). Qed.
Lemma lem1200211 {A : Type'} (a : A) : ((term9 A a) = (@nil A)) = True.
Proof. exact (TRANS (@lem1200206 A a) (@lem1200210 A)). Qed.
Lemma lem1200212 {A : Type'} : (term15 A) = (term16 A).
Proof. exact (fun_ext (fun a : A => @lem1200211 A a)). Qed.
Lemma lem1200213 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1200214 {A : Type'} : (term17 A) = (term18 A).
Proof. exact (MK_COMB (@lem1200213 A) (@lem1200212 A)). Qed.
Lemma lem1200216 {A : Type'} (t : Prop) : (term19 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1200217 {A : Type'} (t : Prop) : (term19 A t) = t.
Proof. exact (@lem1200216 A t). Qed.
Lemma lem1200218 {A : Type'} : (term18 A) = True.
Proof. exact (@lem1200217 A True). Qed.
Lemma lem1200219 {A : Type'} : (term17 A) = True.
Proof. exact (TRANS (@lem1200214 A) (@lem1200218 A)). Qed.
Lemma lem1200220 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1200221 {A : Type'} : (term20 A) = (and True).
Proof. exact (MK_COMB (@lem1200220) (@lem1200219 A)). Qed.
Lemma lem1200237 {_25251 : Type'} (h : _25251) (t : list _25251) : (term7 _25251 h t) = (term8 _25251 h t).
Proof. exact (EQ_MP (@lem1098924 _25251 h t) (@lem1098923 _25251 h t)). Qed.
Lemma lem1200238 {A : Type'} (h : A) (t : list A) : (term7 A h t) = (term8 A h t).
Proof. exact (@lem1200237 A h t). Qed.
Lemma lem1200239 {A : Type'} (a : A) (h : A) (t : list A) : (term21 A a h t) = (term22 A a h t).
Proof. exact (@lem1200238 A a (@cons A h t)). Qed.
Lemma lem1200243 {A : Type'} (h : A) (t : list A) : ((@cons A h t) = (@nil A)) = False.
Proof. exact (@lem1200153 A h t (@lem1200152 A h t)). Qed.
Lemma lem1200244 {A : Type'} (h : A) (t : list A) : ((@cons A h t) = (@nil A)) = False.
Proof. exact (@lem1200243 A h t). Qed.
Lemma lem1200245 {A : Type'} : (@COND (list A)) = (@COND (list A)).
Proof. exact (eq_refl (@COND (list A))). Qed.
Lemma lem1200246 {A : Type'} (h : A) (t : list A) : (term23 A h t) = (@COND (list A) False).
Proof. exact (MK_COMB (@lem1200245 A) (@lem1200244 A h t)). Qed.
Lemma lem1200247 {A : Type'} : (@nil A) = (@nil A).
Proof. exact (eq_refl (@nil A)). Qed.
Lemma lem1200248 {A : Type'} (h : A) (t : list A) : (term24 A h t) = (@COND (list A) False (@nil A)).
Proof. exact (MK_COMB (@lem1200246 A h t) (@lem1200247 A)). Qed.
Lemma lem1200250 {_25251 : Type'} (h : _25251) (t : list _25251) : (term7 _25251 h t) = (term8 _25251 h t).
Proof. exact (EQ_MP (@lem1098924 _25251 h t) (@lem1098923 _25251 h t)). Qed.
Lemma lem1200251 {A : Type'} (h : A) (t : list A) : (term7 A h t) = (term8 A h t).
Proof. exact (@lem1200250 A h t). Qed.
Lemma lem1200256 {A : Type'} (a : A) : (@cons A a) = (@cons A a).
Proof. exact (eq_refl (@cons A a)). Qed.
Lemma lem1200257 {A : Type'} (a : A) (h : A) (t : list A) : (term25 A a h t) = (term26 A a h t).
Proof. exact (MK_COMB (@lem1200256 A a) (@lem1200251 A h t)). Qed.
Lemma lem1200258 {A : Type'} (a : A) (h : A) (t : list A) : (term22 A a h t) = (term27 A a h t).
Proof. exact (MK_COMB (@lem1200248 A h t) (@lem1200257 A a h t)). Qed.
Lemma lem1200260 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1200261 {A : Type'} (t1 : list A) (t2 : list A) : (@COND (list A) False t1 t2) = t2.
Proof. exact (@lem1200260 (list A) t1 t2). Qed.
Lemma lem1200262 {A : Type'} (a : A) (h : A) (t : list A) : (term27 A a h t) = (term26 A a h t).
Proof. exact (@lem1200261 A (@nil A) (term26 A a h t)). Qed.
Lemma lem1200267 {A : Type'} (a : A) (h : A) (t : list A) : (term22 A a h t) = (term26 A a h t).
Proof. exact (TRANS (@lem1200258 A a h t) (@lem1200262 A a h t)). Qed.
Lemma lem1200268 {A : Type'} (a : A) (h : A) (t : list A) : (term21 A a h t) = (term26 A a h t).
Proof. exact (TRANS (@lem1200239 A a h t) (@lem1200267 A a h t)). Qed.
Lemma lem1200269 {A : Type'} : (@eq (list A)) = (@eq (list A)).
Proof. exact (eq_refl (@eq (list A))). Qed.
Lemma lem1200270 {A : Type'} (a : A) (h : A) (t : list A) : (term28 A a h t) = (term29 A a h t).
Proof. exact (MK_COMB (@lem1200269 A) (@lem1200268 A a h t)). Qed.
Lemma lem1200272 {_25251 : Type'} (h : _25251) (t : list _25251) : (term7 _25251 h t) = (term8 _25251 h t).
Proof. exact (EQ_MP (@lem1098924 _25251 h t) (@lem1098923 _25251 h t)). Qed.
Lemma lem1200273 {A : Type'} (h : A) (t : list A) : (term7 A h t) = (term8 A h t).
Proof. exact (@lem1200272 A h t). Qed.
Lemma lem1200278 {A : Type'} (a : A) : (@cons A a) = (@cons A a).
Proof. exact (eq_refl (@cons A a)). Qed.
Lemma lem1200279 {A : Type'} (a : A) (h : A) (t : list A) : (term25 A a h t) = (term26 A a h t).
Proof. exact (MK_COMB (@lem1200278 A a) (@lem1200273 A h t)). Qed.
Lemma lem1200280 {A : Type'} (a : A) (h : A) (t : list A) : ((term21 A a h t) = (term25 A a h t)) = ((term26 A a h t) = (term26 A a h t)).
Proof. exact (MK_COMB (@lem1200270 A a h t) (@lem1200279 A a h t)). Qed.
Lemma lem1200282 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1200283 {A : Type'} (x : list A) : (x = x) = True.
Proof. exact (@lem1200282 (list A) x). Qed.
Lemma lem1200284 {A : Type'} (a : A) (h : A) (t : list A) : ((term26 A a h t) = (term26 A a h t)) = True.
Proof. exact (@lem1200283 A (term26 A a h t)). Qed.
Lemma lem1200285 {A : Type'} (a : A) (h : A) (t : list A) : ((term21 A a h t) = (term25 A a h t)) = True.
Proof. exact (TRANS (@lem1200280 A a h t) (@lem1200284 A a h t)). Qed.
Lemma lem1200286 {A : Type'} (a : A) (h : A) : (term30 A a h) = (term31 A).
Proof. exact (fun_ext (fun t : list A => @lem1200285 A a h t)). Qed.
Lemma lem1200287 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1200288 {A : Type'} (a : A) (h : A) : (term32 A a h) = (term33 A).
Proof. exact (MK_COMB (@lem1200287 A) (@lem1200286 A a h)). Qed.
Lemma lem1200290 {A : Type'} (t : Prop) : (term19 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1200291 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (@lem1200290 (list A) t). Qed.
Lemma lem1200292 {A : Type'} : (term33 A) = True.
Proof. exact (@lem1200291 A True). Qed.
Lemma lem1200293 {A : Type'} (a : A) (h : A) : (term32 A a h) = True.
Proof. exact (TRANS (@lem1200288 A a h) (@lem1200292 A)). Qed.
Lemma lem1200294 {A : Type'} (a : A) : (term35 A a) = (term16 A).
Proof. exact (fun_ext (fun h : A => @lem1200293 A a h)). Qed.
Lemma lem1200295 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1200296 {A : Type'} (a : A) : (term36 A a) = (term18 A).
Proof. exact (MK_COMB (@lem1200295 A) (@lem1200294 A a)). Qed.
Lemma lem1200298 {A : Type'} (t : Prop) : (term19 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1200299 {A : Type'} (t : Prop) : (term19 A t) = t.
Proof. exact (@lem1200298 A t). Qed.
Lemma lem1200300 {A : Type'} : (term18 A) = True.
Proof. exact (@lem1200299 A True). Qed.
Lemma lem1200301 {A : Type'} (a : A) : (term36 A a) = True.
Proof. exact (TRANS (@lem1200296 A a) (@lem1200300 A)). Qed.
Lemma lem1200302 {A : Type'} : (term37 A) = (term16 A).
Proof. exact (fun_ext (fun a : A => @lem1200301 A a)). Qed.
Lemma lem1200303 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1200304 {A : Type'} : (term38 A) = (term18 A).
Proof. exact (MK_COMB (@lem1200303 A) (@lem1200302 A)). Qed.
Lemma lem1200306 {A : Type'} (t : Prop) : (term19 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1200307 {A : Type'} (t : Prop) : (term19 A t) = t.
Proof. exact (@lem1200306 A t). Qed.
Lemma lem1200308 {A : Type'} : (term18 A) = True.
Proof. exact (@lem1200307 A True). Qed.
Lemma lem1200309 {A : Type'} : (term38 A) = True.
Proof. exact (TRANS (@lem1200304 A) (@lem1200308 A)). Qed.
Lemma lem1200310 {A : Type'} : (term39 A) = (True /\ True).
Proof. exact (MK_COMB (@lem1200221 A) (@lem1200309 A)). Qed.
Lemma lem1200312 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1200313 : (True /\ True) = True.
Proof. exact (@lem1200312 True). Qed.
Lemma lem1200314 {A : Type'} : (term39 A) = True.
Proof. exact (TRANS (@lem1200310 A) (@lem1200313)). Qed.
Lemma lem1200315 {A : Type'} : (term40 A) = (True /\ True).
Proof. exact (MK_COMB (@lem1200185 A) (@lem1200314 A)). Qed.
Lemma lem1200317 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1200318 : (True /\ True) = True.
Proof. exact (@lem1200317 True). Qed.
Lemma lem1200319 {A : Type'} : (term40 A) = True.
Proof. exact (TRANS (@lem1200315 A) (@lem1200318)). Qed.
Lemma lem1200320 {A : Type'} : True = (term40 A).
Proof. exact (SYM (@lem1200319 A)). Qed.
Lemma lem1200321 {A : Type'} : term40 A.
Proof. exact (EQ_MP (@lem1200320 A) (@lem0)). Qed.
