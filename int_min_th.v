Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import int_min_th_term_abbrevs.
Require Import int_min_spec.
Require Import real_min_spec.
Require Import thm0_spec.
Require Import thm13473_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm2267744_spec.
Require Import thm2267745_spec.
Lemma lem2293160 (m : real) : term0 m.
Proof. exact (@lem1346200 m). Qed.
Lemma lem2293161 (m : real) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem2293162 (m : real) : term1 m.
Proof. exact (EQ_MP (@lem2293161 m) (@lem2293160 m)). Qed.
Lemma lem2293163 (m : real) (n : real) : term2 m n.
Proof. exact (@lem2293162 m n). Qed.
Lemma lem2293164 (m : real) (n : real) : (term2 m n) = ((real_min m n) = (term3 m n)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem2293166 (x : int) : term4 x.
Proof. exact (@lem2293159 x). Qed.
Lemma lem2293167 (x : int) : (term4 x) = (term5 x).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem2293168 (x : int) : term5 x.
Proof. exact (EQ_MP (@lem2293167 x) (@lem2293166 x)). Qed.
Lemma lem2293169 (x : int) (y : int) : term6 x y.
Proof. exact (@lem2293168 x y). Qed.
Lemma lem2293170 (x : int) (y : int) : (term6 x y) = ((int_min x y) = (term7 x y)).
Proof. exact (eq_refl (term6 x y)). Qed.
Lemma lem2293175 (x : int) (y : int) : (int_min x y) = (term7 x y).
Proof. exact (EQ_MP (@lem2293170 x y) (@lem2293169 x y)). Qed.
Lemma lem2293177 (m : real) (n : real) : (real_min m n) = (term3 m n).
Proof. exact (EQ_MP (@lem2293164 m n) (@lem2293163 m n)). Qed.
Lemma lem2293178 (x : int) (y : int) : (term8 x y) = (term9 x y).
Proof. exact (@lem2293177 (real_of_int x) (real_of_int y)). Qed.
Lemma lem2293179 : int_of_real = int_of_real.
Proof. exact (eq_refl int_of_real). Qed.
Lemma lem2293180 (x : int) (y : int) : (term7 x y) = (term10 x y).
Proof. exact (MK_COMB (@lem2293179) (@lem2293178 x y)). Qed.
Lemma lem2293181 (x : int) (y : int) : (int_min x y) = (term10 x y).
Proof. exact (TRANS (@lem2293175 x y) (@lem2293180 x y)). Qed.
Lemma lem2293182 : real_of_int = real_of_int.
Proof. exact (eq_refl real_of_int). Qed.
Lemma lem2293183 (x : int) (y : int) : (term11 x y) = (term12 x y).
Proof. exact (MK_COMB (@lem2293182) (@lem2293181 x y)). Qed.
Lemma lem2293184 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2293185 (x : int) (y : int) : (term13 x y) = (term14 x y).
Proof. exact (MK_COMB (@lem2293184) (@lem2293183 x y)). Qed.
Lemma lem2293187 (m : real) (n : real) : (real_min m n) = (term3 m n).
Proof. exact (EQ_MP (@lem2293164 m n) (@lem2293163 m n)). Qed.
Lemma lem2293188 (x : int) (y : int) : (term8 x y) = (term9 x y).
Proof. exact (@lem2293187 (real_of_int x) (real_of_int y)). Qed.
Lemma lem2293189 (x : int) (y : int) : ((term11 x y) = (term8 x y)) = ((term12 x y) = (term9 x y)).
Proof. exact (MK_COMB (@lem2293185 x y) (@lem2293188 x y)). Qed.
Lemma lem2293192 (x : int) (y : int) : ((term12 x y) = (term9 x y)) = ((term11 x y) = (term8 x y)).
Proof. exact (SYM (@lem2293189 x y)). Qed.
Lemma lem2293193 (_474 : real) (_475 : Prop) (_476 : real -> Prop) (_477 : real) : (term15 _476 _475 _474 _477) = (term16 _474 _475 _476 _477).
Proof. exact (@lem13473 real _474 _475 _476 _477). Qed.
Lemma lem2293194 (_474 : real) (_475 : Prop) (_477 : real) : (term17 _475 _474 _477) = (term18 _474 _475 _477).
Proof. exact (@lem2293193 _474 _475 term19 _477). Qed.
Lemma lem2293195 (x : int) (y : int) : (term20 x y) = (term21 x y).
Proof. exact (@lem2293194 (real_of_int x) (term22 x y) (real_of_int y)). Qed.
Lemma lem2293196 (y : int) : (term23 y) = ((term24 y) = (real_of_int y)).
Proof. exact (eq_refl (term23 y)). Qed.
Lemma lem2293197 (x : int) (y : int) : (term25 x y) = (term25 x y).
Proof. exact (eq_refl (term25 x y)). Qed.
Lemma lem2293198 (x : int) (y : int) : (term26 x y) = (term27 x y).
Proof. exact (MK_COMB (@lem2293197 x y) (@lem2293196 y)). Qed.
Lemma lem2293199 (x : int) : (term23 x) = ((term24 x) = (real_of_int x)).
Proof. exact (eq_refl (term23 x)). Qed.
Lemma lem2293200 (x : int) (y : int) : (term28 x y) = (term28 x y).
Proof. exact (eq_refl (term28 x y)). Qed.
Lemma lem2293201 (y : int) (x : int) : (term29 y x) = (term30 y x).
Proof. exact (MK_COMB (@lem2293200 x y) (@lem2293199 x)). Qed.
Lemma lem2293202 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2293203 (y : int) (x : int) : (term31 y x) = (term32 y x).
Proof. exact (MK_COMB (@lem2293202) (@lem2293201 y x)). Qed.
Lemma lem2293204 (x : int) (y : int) : (term21 x y) = (term33 x y).
Proof. exact (MK_COMB (@lem2293203 y x) (@lem2293198 x y)). Qed.
Lemma lem2293205 (x : int) (y : int) : (term20 x y) = ((term12 x y) = (term9 x y)).
Proof. exact (eq_refl (term20 x y)). Qed.
Lemma lem2293206 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2293207 (x : int) (y : int) : (term34 x y) = (term35 x y).
Proof. exact (MK_COMB (@lem2293206) (@lem2293205 x y)). Qed.
Lemma lem2293208 (x : int) (y : int) : ((term20 x y) = (term21 x y)) = (((term12 x y) = (term9 x y)) = (term33 x y)).
Proof. exact (MK_COMB (@lem2293207 x y) (@lem2293204 x y)). Qed.
Lemma lem2293209 (x : int) (y : int) : ((term12 x y) = (term9 x y)) = (term33 x y).
Proof. exact (EQ_MP (@lem2293208 x y) (@lem2293195 x y)). Qed.
Lemma lem2293210 (x : int) (y : int) : (term33 x y) = ((term12 x y) = (term9 x y)).
Proof. exact (SYM (@lem2293209 x y)). Qed.
Lemma lem2293248 (a : int) : (term36 a) = a.
Proof. exact (EQ_MP (@lem2267745 a) (@lem2267744 a)). Qed.
Lemma lem2293249 (x : int) : (term36 x) = x.
Proof. exact (@lem2293248 x). Qed.
Lemma lem2293250 : real_of_int = real_of_int.
Proof. exact (eq_refl real_of_int). Qed.
Lemma lem2293251 (x : int) : (term24 x) = (real_of_int x).
Proof. exact (MK_COMB (@lem2293250) (@lem2293249 x)). Qed.
Lemma lem2293252 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2293253 (x : int) : (term37 x) = (term38 x).
Proof. exact (MK_COMB (@lem2293252) (@lem2293251 x)). Qed.
Lemma lem2293254 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2293255 (x : int) : ((term24 x) = (real_of_int x)) = ((real_of_int x) = (real_of_int x)).
Proof. exact (MK_COMB (@lem2293253 x) (@lem2293254 x)). Qed.
Lemma lem2293257 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2293258 (x : real) : (x = x) = True.
Proof. exact (@lem2293257 real x). Qed.
Lemma lem2293259 (x : int) : ((real_of_int x) = (real_of_int x)) = True.
Proof. exact (@lem2293258 (real_of_int x)). Qed.
Lemma lem2293260 (x : int) : ((term24 x) = (real_of_int x)) = True.
Proof. exact (TRANS (@lem2293255 x) (@lem2293259 x)). Qed.
Lemma lem2293261 (x : int) : True = ((term24 x) = (real_of_int x)).
Proof. exact (SYM (@lem2293260 x)). Qed.
Lemma lem2293266 (a : int) : (term36 a) = a.
Proof. exact (EQ_MP (@lem2267745 a) (@lem2267744 a)). Qed.
Lemma lem2293267 (y : int) : (term36 y) = y.
Proof. exact (@lem2293266 y). Qed.
Lemma lem2293268 : real_of_int = real_of_int.
Proof. exact (eq_refl real_of_int). Qed.
Lemma lem2293269 (y : int) : (term24 y) = (real_of_int y).
Proof. exact (MK_COMB (@lem2293268) (@lem2293267 y)). Qed.
Lemma lem2293270 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2293271 (y : int) : (term37 y) = (term38 y).
Proof. exact (MK_COMB (@lem2293270) (@lem2293269 y)). Qed.
Lemma lem2293272 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2293273 (y : int) : ((term24 y) = (real_of_int y)) = ((real_of_int y) = (real_of_int y)).
Proof. exact (MK_COMB (@lem2293271 y) (@lem2293272 y)). Qed.
Lemma lem2293275 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2293276 (x : real) : (x = x) = True.
Proof. exact (@lem2293275 real x). Qed.
Lemma lem2293277 (y : int) : ((real_of_int y) = (real_of_int y)) = True.
Proof. exact (@lem2293276 (real_of_int y)). Qed.
Lemma lem2293278 (y : int) : ((term24 y) = (real_of_int y)) = True.
Proof. exact (TRANS (@lem2293273 y) (@lem2293277 y)). Qed.
Lemma lem2293279 (y : int) : True = ((term24 y) = (real_of_int y)).
Proof. exact (SYM (@lem2293278 y)). Qed.
Lemma lem2293281 (y : int) : (term24 y) = (real_of_int y).
Proof. exact (EQ_MP (@lem2293279 y) (@lem0)). Qed.
Lemma lem2293282 (x : int) (y : int) : term27 x y.
Proof. exact (fun h0 : term39 x y => @lem2293281 y). Qed.
Lemma lem2293283 (x : int) : (term24 x) = (real_of_int x).
Proof. exact (EQ_MP (@lem2293261 x) (@lem0)). Qed.
Lemma lem2293284 (y : int) (x : int) : term30 y x.
Proof. exact (fun h0 : term22 x y => @lem2293283 x). Qed.
Lemma lem2293285 (x : int) (y : int) : term33 x y.
Proof. exact (conj (@lem2293284 y x) (@lem2293282 x y)). Qed.
Lemma lem2293286 (x : int) (y : int) : (term12 x y) = (term9 x y).
Proof. exact (EQ_MP (@lem2293210 x y) (@lem2293285 x y)). Qed.
Lemma lem2293287 (x : int) (y : int) : (term11 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2293192 x y) (@lem2293286 x y)). Qed.
Lemma lem2293292 (x : int) : term40 x.
Proof. exact (fun y : int => @lem2293287 x y). Qed.
Lemma lem2293297 : term41.
Proof. exact (fun x : int => @lem2293292 x). Qed.
