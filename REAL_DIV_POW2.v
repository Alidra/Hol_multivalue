Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_DIV_POW2_term_abbrevs.
Require Import LT_IMP_LE_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_LE_spec.
Require Import REAL_INV_DIV_spec.
Require Import REAL_INV_INV_spec.
Require Import REAL_POW_SUB_spec.
Require Import thm0_spec.
Require Import thm13473_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem1641072 (m : nat) : term0 m.
Proof. exact (@lem98439 m). Qed.
Lemma lem1641073 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1641074 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem1641073 m) (@lem1641072 m)). Qed.
Lemma lem1641075 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem1641074 m n). Qed.
Lemma lem1641076 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1641078 (m : nat) : term4 m.
Proof. exact (@lem97961 m). Qed.
Lemma lem1641079 (m : nat) : (term4 m) = (term5 m).
Proof. exact (eq_refl (term4 m)). Qed.
Lemma lem1641080 (m : nat) : term5 m.
Proof. exact (EQ_MP (@lem1641079 m) (@lem1641078 m)). Qed.
Lemma lem1641081 (m : nat) (n : nat) : term6 m n.
Proof. exact (@lem1641080 m n). Qed.
Lemma lem1641082 (n : nat) (m : nat) : (term6 m n) = ((term7 m n) = (Peano.lt n m)).
Proof. exact (eq_refl (term6 m n)). Qed.
Lemma lem1641084 (x : real) : term8 x.
Proof. exact (@lem1595376 x). Qed.
Lemma lem1641085 (x : real) : (term8 x) = (term9 x).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem1641086 (x : real) : term9 x.
Proof. exact (EQ_MP (@lem1641085 x) (@lem1641084 x)). Qed.
Lemma lem1641087 (x : real) (y : real) : term10 x y.
Proof. exact (@lem1641086 x y). Qed.
Lemma lem1641088 (y : real) (x : real) : (term10 x y) = ((term11 x y) = (real_div y x)).
Proof. exact (eq_refl (term10 x y)). Qed.
Lemma lem1641091 (x : real) (h1 : (term12 x) = x) : (term12 x) = x.
Proof. exact (h1). Qed.
Lemma lem1641092 (x : real) (h1 : (term12 x) = x) : x = (term12 x).
Proof. exact (SYM (@lem1641091 x h1)). Qed.
Lemma lem1641093 (x : real) (h1 : x = (term12 x)) : x = (term12 x).
Proof. exact (h1). Qed.
Lemma lem1641094 (x : real) (h1 : x = (term12 x)) : (term12 x) = x.
Proof. exact (SYM (@lem1641093 x h1)). Qed.
Lemma lem1641095 (x : real) : ((term12 x) = x) = (x = (term12 x)).
Proof. exact (prop_ext (fun h1 : (term12 x) = x => @lem1641092 x h1) (fun h1 : x = (term12 x) => @lem1641094 x h1)). Qed.
Lemma lem1641096 : term13 = term14.
Proof. exact (fun_ext (fun x : real => @lem1641095 x)). Qed.
Lemma lem1641097 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1641098 : term15 = term16.
Proof. exact (MK_COMB (@lem1641097) (@lem1641096)). Qed.
Lemma lem1641099 : term16.
Proof. exact (EQ_MP (@lem1641098) (@lem1587920)). Qed.
Lemma lem1641100 (x : real) : term17 x.
Proof. exact (@lem1641099 x). Qed.
Lemma lem1641101 (x : real) : (term17 x) = (x = (term12 x)).
Proof. exact (eq_refl (term17 x)). Qed.
Lemma lem1641103 (x : real) (h1 : term18 x) : term18 x.
Proof. exact (h1). Qed.
Lemma lem1641104 (_474 : real) (_475 : Prop) (_476 : real -> Prop) (_477 : real) : (term19 _476 _475 _474 _477) = (term20 _474 _475 _476 _477).
Proof. exact (@lem13473 real _474 _475 _476 _477). Qed.
Lemma lem1641105 (_474 : real) (_475 : Prop) (m : nat) (x : real) (n : nat) (_477 : real) : (term21 m x n _475 _474 _477) = (term22 _474 _475 m x n _477).
Proof. exact (@lem1641104 _474 _475 (term23 m x n) _477). Qed.
Lemma lem1641106 (x : real) (n : nat) (m : nat) : (term24 x n m) = (term25 x n m).
Proof. exact (@lem1641105 (term26 x m n) (Peano.le n m) m x n (term27 x n m)). Qed.
Lemma lem1641107 (x : real) (n : nat) (m : nat) : (term28 x n m) = ((term29 m x n) = (term27 x n m)).
Proof. exact (eq_refl (term28 x n m)). Qed.
Lemma lem1641108 (n : nat) (m : nat) : (term30 n m) = (term30 n m).
Proof. exact (eq_refl (term30 n m)). Qed.
Lemma lem1641109 (x : real) (n : nat) (m : nat) : (term31 x n m) = (term32 x n m).
Proof. exact (MK_COMB (@lem1641108 n m) (@lem1641107 x n m)). Qed.
Lemma lem1641110 (x : real) (m : nat) (n : nat) : (term33 x m n) = ((term29 m x n) = (term26 x m n)).
Proof. exact (eq_refl (term33 x m n)). Qed.
Lemma lem1641111 (n : nat) (m : nat) : (term34 n m) = (term34 n m).
Proof. exact (eq_refl (term34 n m)). Qed.
Lemma lem1641112 (x : real) (m : nat) (n : nat) : (term35 x m n) = (term36 x m n).
Proof. exact (MK_COMB (@lem1641111 n m) (@lem1641110 x m n)). Qed.
Lemma lem1641113 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1641114 (x : real) (m : nat) (n : nat) : (term37 x m n) = (term38 x m n).
Proof. exact (MK_COMB (@lem1641113) (@lem1641112 x m n)). Qed.
Lemma lem1641115 (x : real) (n : nat) (m : nat) : (term25 x n m) = (term39 x n m).
Proof. exact (MK_COMB (@lem1641114 x m n) (@lem1641109 x n m)). Qed.
Lemma lem1641116 (x : real) (n : nat) (m : nat) : (term24 x n m) = ((term29 m x n) = (term40 x n m)).
Proof. exact (eq_refl (term24 x n m)). Qed.
Lemma lem1641117 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1641118 (x : real) (n : nat) (m : nat) : (term41 x n m) = (term42 x n m).
Proof. exact (MK_COMB (@lem1641117) (@lem1641116 x n m)). Qed.
Lemma lem1641119 (x : real) (n : nat) (m : nat) : ((term24 x n m) = (term25 x n m)) = (((term29 m x n) = (term40 x n m)) = (term39 x n m)).
Proof. exact (MK_COMB (@lem1641118 x n m) (@lem1641115 x n m)). Qed.
Lemma lem1641120 (x : real) (n : nat) (m : nat) : ((term29 m x n) = (term40 x n m)) = (term39 x n m).
Proof. exact (EQ_MP (@lem1641119 x n m) (@lem1641106 x n m)). Qed.
Lemma lem1641121 (x : real) (n : nat) (m : nat) : (term39 x n m) = ((term29 m x n) = (term40 x n m)).
Proof. exact (SYM (@lem1641120 x n m)). Qed.
Lemma lem1641122 (n : nat) (m : nat) (h1 : Peano.le n m) : Peano.le n m.
Proof. exact (h1). Qed.
Lemma lem1641139 (n : nat) (m : nat) (h1 : term7 n m) : term7 n m.
Proof. exact (h1). Qed.
Lemma lem1641194 (x : real) : term43 x.
Proof. exact (@lem1598415 x). Qed.
Lemma lem1641195 (x : real) : (term43 x) = (term44 x).
Proof. exact (eq_refl (term43 x)). Qed.
Lemma lem1641196 (x : real) : term44 x.
Proof. exact (EQ_MP (@lem1641195 x) (@lem1641194 x)). Qed.
Lemma lem1641197 (x : real) (m : nat) : term45 x m.
Proof. exact (@lem1641196 x m). Qed.
Lemma lem1641198 (x : real) (m : nat) : (term45 x m) = (term46 x m).
Proof. exact (eq_refl (term45 x m)). Qed.
Lemma lem1641199 (x : real) (m : nat) : term46 x m.
Proof. exact (EQ_MP (@lem1641198 x m) (@lem1641197 x m)). Qed.
Lemma lem1641200 (x : real) (m : nat) (n : nat) : term47 x m n.
Proof. exact (@lem1641199 x m n). Qed.
Lemma lem1641201 (n : nat) (x : real) (m : nat) : (term47 x m n) = (term48 n x m).
Proof. exact (eq_refl (term47 x m n)). Qed.
Lemma lem1641202 (n : nat) (x : real) (m : nat) : term48 n x m.
Proof. exact (EQ_MP (@lem1641201 n x m) (@lem1641200 x m n)). Qed.
Lemma lem1641203 (x : real) (m : nat) (n : nat) (h1 : term49 x m n) : term49 x m n.
Proof. exact (h1). Qed.
Lemma lem1641204 (x : real) (m : nat) (n : nat) (h1 : term49 x m n) : (term26 x n m) = (term29 n x m).
Proof. exact (@lem1641202 n x m (@lem1641203 x m n h1)). Qed.
Lemma lem1641210 (x : real) : term50 x.
Proof. exact (@lem82 (x = term51)). Qed.
Lemma lem1641223 (n : nat) (m : nat) : (Peano.le n m) = ((Peano.le n m) = True).
Proof. exact (@lem7 (Peano.le n m)). Qed.
Lemma lem1641228 (n : nat) (x : real) (m : nat) : term48 n x m.
Proof. exact (fun h0 : term49 x m n => @lem1641204 x m n h0). Qed.
Lemma lem1641229 (m : nat) (x : real) (n : nat) : term48 m x n.
Proof. exact (@lem1641228 m x n). Qed.
Lemma lem1641233 (x : real) (h1 : term18 x) : (x = term51) = False.
Proof. exact (@lem1641210 x (@lem1641103 x h1)). Qed.
Lemma lem1641234 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1641235 (x : real) (h1 : term18 x) : (term18 x) = (~ False).
Proof. exact (MK_COMB (@lem1641234) (@lem1641233 x h1)). Qed.
Lemma lem1641237 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1641238 (x : real) (h1 : term18 x) : (term18 x) = True.
Proof. exact (TRANS (@lem1641235 x h1) (@lem1641237)). Qed.
Lemma lem1641239 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1641240 (x : real) (h1 : term18 x) : (term52 x) = (and True).
Proof. exact (MK_COMB (@lem1641239) (@lem1641238 x h1)). Qed.
Lemma lem1641242 (n : nat) (m : nat) (h1 : Peano.le n m) : (Peano.le n m) = True.
Proof. exact (EQ_MP (@lem1641223 n m) (@lem1641122 n m h1)). Qed.
Lemma lem1641243 (x : real) (n : nat) (m : nat) (h1 : term18 x) (h2 : Peano.le n m) : (term49 x n m) = (True /\ True).
Proof. exact (MK_COMB (@lem1641240 x h1) (@lem1641242 n m h2)). Qed.
Lemma lem1641245 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1641246 : (True /\ True) = True.
Proof. exact (@lem1641245 True). Qed.
Lemma lem1641247 (x : real) (n : nat) (m : nat) (h1 : term18 x) (h2 : Peano.le n m) : (term49 x n m) = True.
Proof. exact (TRANS (@lem1641243 x n m h1 h2) (@lem1641246)). Qed.
Lemma lem1641248 (x : real) (n : nat) (m : nat) (h1 : term18 x) (h2 : Peano.le n m) : True = (term49 x n m).
Proof. exact (SYM (@lem1641247 x n m h1 h2)). Qed.
Lemma lem1641249 (x : real) (n : nat) (m : nat) (h1 : term18 x) (h2 : Peano.le n m) : term49 x n m.
Proof. exact (EQ_MP (@lem1641248 x n m h1 h2) (@lem0)). Qed.
Lemma lem1641250 (x : real) (n : nat) (m : nat) (h1 : term18 x) (h2 : Peano.le n m) : (term26 x m n) = (term29 m x n).
Proof. exact (@lem1641229 m x n (@lem1641249 x n m h1 h2)). Qed.
Lemma lem1641251 (m : nat) (x : real) (n : nat) : (term53 m x n) = (term53 m x n).
Proof. exact (eq_refl (term53 m x n)). Qed.
Lemma lem1641252 (x : real) (n : nat) (m : nat) (h1 : term18 x) (h2 : Peano.le n m) : ((term29 m x n) = (term26 x m n)) = ((term29 m x n) = (term29 m x n)).
Proof. exact (MK_COMB (@lem1641251 m x n) (@lem1641250 x n m h1 h2)). Qed.
Lemma lem1641254 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1641255 (x : real) : (x = x) = True.
Proof. exact (@lem1641254 real x). Qed.
Lemma lem1641256 (m : nat) (x : real) (n : nat) : ((term29 m x n) = (term29 m x n)) = True.
Proof. exact (@lem1641255 (term29 m x n)). Qed.
Lemma lem1641257 (x : real) (n : nat) (m : nat) (h1 : term18 x) (h2 : Peano.le n m) : ((term29 m x n) = (term26 x m n)) = True.
Proof. exact (TRANS (@lem1641252 x n m h1 h2) (@lem1641256 m x n)). Qed.
Lemma lem1641258 (x : real) (n : nat) (m : nat) (h1 : term18 x) (h2 : Peano.le n m) : True = ((term29 m x n) = (term26 x m n)).
Proof. exact (SYM (@lem1641257 x n m h1 h2)). Qed.
Lemma lem1641316 (x : real) : x = (term12 x).
Proof. exact (EQ_MP (@lem1641101 x) (@lem1641100 x)). Qed.
Lemma lem1641317 (m : nat) (x : real) (n : nat) : (term29 m x n) = (term54 m x n).
Proof. exact (@lem1641316 (term29 m x n)). Qed.
Lemma lem1641318 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1641319 (m : nat) (x : real) (n : nat) : (term53 m x n) = (term55 m x n).
Proof. exact (MK_COMB (@lem1641318) (@lem1641317 m x n)). Qed.
Lemma lem1641320 (x : real) (n : nat) (m : nat) : (term27 x n m) = (term27 x n m).
Proof. exact (eq_refl (term27 x n m)). Qed.
Lemma lem1641321 (x : real) (n : nat) (m : nat) : ((term29 m x n) = (term27 x n m)) = ((term54 m x n) = (term27 x n m)).
Proof. exact (MK_COMB (@lem1641319 m x n) (@lem1641320 x n m)). Qed.
Lemma lem1641322 (x : real) (n : nat) (m : nat) : ((term54 m x n) = (term27 x n m)) = ((term29 m x n) = (term27 x n m)).
Proof. exact (SYM (@lem1641321 x n m)). Qed.
Lemma lem1641323 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem1641327 (y : real) (x : real) : (term11 x y) = (real_div y x).
Proof. exact (EQ_MP (@lem1641088 y x) (@lem1641087 x y)). Qed.
Lemma lem1641328 (n : nat) (x : real) (m : nat) : (term56 m x n) = (term29 n x m).
Proof. exact (@lem1641327 (real_pow x n) (real_pow x m)). Qed.
Lemma lem1641329 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1641330 (n : nat) (x : real) (m : nat) : (term57 m x n) = (term53 n x m).
Proof. exact (MK_COMB (@lem1641329) (@lem1641328 n x m)). Qed.
Lemma lem1641331 (x : real) (n : nat) (m : nat) : (term26 x n m) = (term26 x n m).
Proof. exact (eq_refl (term26 x n m)). Qed.
Lemma lem1641332 (x : real) (n : nat) (m : nat) : ((term56 m x n) = (term26 x n m)) = ((term29 n x m) = (term26 x n m)).
Proof. exact (MK_COMB (@lem1641330 n x m) (@lem1641331 x n m)). Qed.
Lemma lem1641335 (x : real) (n : nat) (m : nat) : ((term29 n x m) = (term26 x n m)) = ((term56 m x n) = (term26 x n m)).
Proof. exact (SYM (@lem1641332 x n m)). Qed.
Lemma lem1641339 (n : nat) (m : nat) : (term7 m n) = (Peano.lt n m).
Proof. exact (EQ_MP (@lem1641082 n m) (@lem1641081 m n)). Qed.
Lemma lem1641340 (m : nat) (n : nat) : (term7 n m) = (Peano.lt m n).
Proof. exact (@lem1641339 m n). Qed.
Lemma lem1641341 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1641342 (m : nat) (n : nat) : (term30 n m) = (term58 m n).
Proof. exact (MK_COMB (@lem1641341) (@lem1641340 m n)). Qed.
Lemma lem1641345 (x : real) (n : nat) (m : nat) : ((term29 n x m) = (term26 x n m)) = ((term29 n x m) = (term26 x n m)).
Proof. exact (eq_refl ((term29 n x m) = (term26 x n m))). Qed.
Lemma lem1641346 (x : real) (n : nat) (m : nat) : (term59 x n m) = (term60 x n m).
Proof. exact (MK_COMB (@lem1641342 m n) (@lem1641345 x n m)). Qed.
Lemma lem1641349 (x : real) (n : nat) (m : nat) : (term60 x n m) = (term59 x n m).
Proof. exact (SYM (@lem1641346 x n m)). Qed.
Lemma lem1641350 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem1641352 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem1641076 m n) (@lem1641075 m n)). Qed.
Lemma lem1641353 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.le m n.
Proof. exact (@lem1641352 m n (@lem1641350 m n h1)). Qed.
Lemma lem1641354 (x : real) : term43 x.
Proof. exact (@lem1598415 x). Qed.
Lemma lem1641355 (x : real) : (term43 x) = (term44 x).
Proof. exact (eq_refl (term43 x)). Qed.
Lemma lem1641356 (x : real) : term44 x.
Proof. exact (EQ_MP (@lem1641355 x) (@lem1641354 x)). Qed.
Lemma lem1641357 (x : real) (m : nat) : term45 x m.
Proof. exact (@lem1641356 x m). Qed.
Lemma lem1641358 (x : real) (m : nat) : (term45 x m) = (term46 x m).
Proof. exact (eq_refl (term45 x m)). Qed.
Lemma lem1641359 (x : real) (m : nat) : term46 x m.
Proof. exact (EQ_MP (@lem1641358 x m) (@lem1641357 x m)). Qed.
Lemma lem1641360 (x : real) (m : nat) (n : nat) : term47 x m n.
Proof. exact (@lem1641359 x m n). Qed.
Lemma lem1641361 (n : nat) (x : real) (m : nat) : (term47 x m n) = (term48 n x m).
Proof. exact (eq_refl (term47 x m n)). Qed.
Lemma lem1641362 (n : nat) (x : real) (m : nat) : term48 n x m.
Proof. exact (EQ_MP (@lem1641361 n x m) (@lem1641360 x m n)). Qed.
Lemma lem1641363 (x : real) (m : nat) (n : nat) (h1 : term49 x m n) : term49 x m n.
Proof. exact (h1). Qed.
Lemma lem1641364 (x : real) (m : nat) (n : nat) (h1 : term49 x m n) : (term26 x n m) = (term29 n x m).
Proof. exact (@lem1641362 n x m (@lem1641363 x m n h1)). Qed.
Lemma lem1641370 (x : real) : term50 x.
Proof. exact (@lem82 (x = term51)). Qed.
Lemma lem1641386 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term61 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1641387 (p : Prop) (q : Prop) (p' : Prop) : term62 p q p'.
Proof. exact (fun q' : Prop => @lem1641386 p q p' q'). Qed.
Lemma lem1641388 (p : Prop) (q : Prop) : term63 p q.
Proof. exact (fun p' : Prop => @lem1641387 p q p'). Qed.
Lemma lem1641389 (x : real) (n : nat) (m : nat) : term64 x n m.
Proof. exact (@lem1641388 (Peano.le m n) ((term29 n x m) = (term26 x n m))). Qed.
Lemma lem1641390 (x : real) (n : nat) (m : nat) (p' : Prop) : term65 x n m p'.
Proof. exact (@lem1641389 x n m p'). Qed.
Lemma lem1641391 (x : real) (n : nat) (m : nat) (p' : Prop) : (term65 x n m p') = (term66 x n m p').
Proof. exact (eq_refl (term65 x n m p')). Qed.
Lemma lem1641392 (x : real) (n : nat) (m : nat) (p' : Prop) : term66 x n m p'.
Proof. exact (EQ_MP (@lem1641391 x n m p') (@lem1641390 x n m p')). Qed.
Lemma lem1641393 (x : real) (n : nat) (m : nat) (p' : Prop) (q' : Prop) : term67 x n m p' q'.
Proof. exact (@lem1641392 x n m p' q'). Qed.
Lemma lem1641394 (x : real) (n : nat) (m : nat) (p' : Prop) (q' : Prop) : (term67 x n m p' q') = (term68 x n m p' q').
Proof. exact (eq_refl (term67 x n m p' q')). Qed.
Lemma lem1641395 (x : real) (n : nat) (m : nat) (p' : Prop) (q' : Prop) : term68 x n m p' q'.
Proof. exact (EQ_MP (@lem1641394 x n m p' q') (@lem1641393 x n m p' q')). Qed.
Lemma lem1641396 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem1641397 (x : real) (m : nat) (n : nat) (q' : Prop) : term69 x m n q'.
Proof. exact (@lem1641395 x n m (Peano.le m n) q'). Qed.
Lemma lem1641398 (x : real) (m : nat) (n : nat) (q' : Prop) : term70 x m n q'.
Proof. exact (@lem1641397 x m n q' (@lem1641396 m n)). Qed.
Lemma lem1641399 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem1641400 (m : nat) (n : nat) : (Peano.le m n) = ((Peano.le m n) = True).
Proof. exact (@lem7 (Peano.le m n)). Qed.
Lemma lem1641405 (n : nat) (x : real) (m : nat) : term48 n x m.
Proof. exact (fun h0 : term49 x m n => @lem1641364 x m n h0). Qed.
Lemma lem1641409 (x : real) (h1 : term18 x) : (x = term51) = False.
Proof. exact (@lem1641370 x (@lem1641103 x h1)). Qed.
Lemma lem1641410 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1641411 (x : real) (h1 : term18 x) : (term18 x) = (~ False).
Proof. exact (MK_COMB (@lem1641410) (@lem1641409 x h1)). Qed.
Lemma lem1641413 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1641414 (x : real) (h1 : term18 x) : (term18 x) = True.
Proof. exact (TRANS (@lem1641411 x h1) (@lem1641413)). Qed.
Lemma lem1641415 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1641416 (x : real) (h1 : term18 x) : (term52 x) = (and True).
Proof. exact (MK_COMB (@lem1641415) (@lem1641414 x h1)). Qed.
Lemma lem1641418 (m : nat) (n : nat) (h1 : Peano.le m n) : (Peano.le m n) = True.
Proof. exact (EQ_MP (@lem1641400 m n) (@lem1641399 m n h1)). Qed.
Lemma lem1641419 (x : real) (m : nat) (n : nat) (h1 : term18 x) (h2 : Peano.le m n) : (term49 x m n) = (True /\ True).
Proof. exact (MK_COMB (@lem1641416 x h1) (@lem1641418 m n h2)). Qed.
Lemma lem1641421 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1641422 : (True /\ True) = True.
Proof. exact (@lem1641421 True). Qed.
Lemma lem1641423 (x : real) (m : nat) (n : nat) (h1 : term18 x) (h2 : Peano.le m n) : (term49 x m n) = True.
Proof. exact (TRANS (@lem1641419 x m n h1 h2) (@lem1641422)). Qed.
Lemma lem1641424 (x : real) (m : nat) (n : nat) (h1 : term18 x) (h2 : Peano.le m n) : True = (term49 x m n).
Proof. exact (SYM (@lem1641423 x m n h1 h2)). Qed.
Lemma lem1641425 (x : real) (m : nat) (n : nat) (h1 : term18 x) (h2 : Peano.le m n) : term49 x m n.
Proof. exact (EQ_MP (@lem1641424 x m n h1 h2) (@lem0)). Qed.
Lemma lem1641426 (x : real) (m : nat) (n : nat) (h1 : term18 x) (h2 : Peano.le m n) : (term26 x n m) = (term29 n x m).
Proof. exact (@lem1641405 n x m (@lem1641425 x m n h1 h2)). Qed.
Lemma lem1641427 (n : nat) (x : real) (m : nat) : (term53 n x m) = (term53 n x m).
Proof. exact (eq_refl (term53 n x m)). Qed.
Lemma lem1641428 (x : real) (m : nat) (n : nat) (h1 : term18 x) (h2 : Peano.le m n) : ((term29 n x m) = (term26 x n m)) = ((term29 n x m) = (term29 n x m)).
Proof. exact (MK_COMB (@lem1641427 n x m) (@lem1641426 x m n h1 h2)). Qed.
Lemma lem1641430 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1641431 (x : real) : (x = x) = True.
Proof. exact (@lem1641430 real x). Qed.
Lemma lem1641432 (n : nat) (x : real) (m : nat) : ((term29 n x m) = (term29 n x m)) = True.
Proof. exact (@lem1641431 (term29 n x m)). Qed.
Lemma lem1641433 (x : real) (m : nat) (n : nat) (h1 : term18 x) (h2 : Peano.le m n) : ((term29 n x m) = (term26 x n m)) = True.
Proof. exact (TRANS (@lem1641428 x m n h1 h2) (@lem1641432 n x m)). Qed.
Lemma lem1641434 (n : nat) (m : nat) (x : real) (h1 : term18 x) : term71 x n m.
Proof. exact (fun h0 : Peano.le m n => @lem1641433 x m n h1 h0). Qed.
Lemma lem1641435 (x : real) (m : nat) (n : nat) : term72 x m n.
Proof. exact (@lem1641398 x m n True). Qed.
Lemma lem1641436 (m : nat) (n : nat) (x : real) (h1 : term18 x) : (term36 x n m) = (term73 m n).
Proof. exact (@lem1641435 x m n (@lem1641434 n m x h1)). Qed.
Lemma lem1641438 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1641439 (m : nat) (n : nat) : (term73 m n) = True.
Proof. exact (@lem1641438 (Peano.le m n)). Qed.
Lemma lem1641440 (n : nat) (m : nat) (x : real) (h1 : term18 x) : (term36 x n m) = True.
Proof. exact (TRANS (@lem1641436 m n x h1) (@lem1641439 m n)). Qed.
Lemma lem1641441 (n : nat) (m : nat) (x : real) (h1 : term18 x) : True = (term36 x n m).
Proof. exact (SYM (@lem1641440 n m x h1)). Qed.
Lemma lem1641442 (n : nat) (m : nat) (x : real) (h1 : term18 x) : term36 x n m.
Proof. exact (EQ_MP (@lem1641441 n m x h1) (@lem0)). Qed.
Lemma lem1641443 (x : real) (m : nat) (n : nat) (h1 : term18 x) (h2 : Peano.lt m n) : (term29 n x m) = (term26 x n m).
Proof. exact (@lem1641442 n m x h1 (@lem1641353 m n h2)). Qed.
Lemma lem1641444 (n : nat) (m : nat) (x : real) (h1 : term18 x) : term60 x n m.
Proof. exact (fun h0 : Peano.lt m n => @lem1641443 x m n h1 h0). Qed.
Lemma lem1641445 (n : nat) (m : nat) (x : real) (h1 : term18 x) : term59 x n m.
Proof. exact (EQ_MP (@lem1641349 x n m) (@lem1641444 n m x h1)). Qed.
Lemma lem1641446 (n : nat) (m : nat) (x : real) (h1 : term7 n m) (h2 : term18 x) : (term29 n x m) = (term26 x n m).
Proof. exact (@lem1641445 n m x h2 (@lem1641139 n m h1)). Qed.
Lemma lem1641447 (n : nat) (m : nat) (x : real) (h1 : term7 n m) (h2 : term18 x) : (term56 m x n) = (term26 x n m).
Proof. exact (EQ_MP (@lem1641335 x n m) (@lem1641446 n m x h1 h2)). Qed.
Lemma lem1641448 (n : nat) (m : nat) (x : real) (h1 : term7 n m) (h2 : term18 x) : (term54 m x n) = (term27 x n m).
Proof. exact (MK_COMB (@lem1641323) (@lem1641447 n m x h1 h2)). Qed.
Lemma lem1641453 (n : nat) (m : nat) (x : real) (h1 : term7 n m) (h2 : term18 x) : (term29 m x n) = (term27 x n m).
Proof. exact (EQ_MP (@lem1641322 x n m) (@lem1641448 n m x h1 h2)). Qed.
Lemma lem1641454 (n : nat) (m : nat) (x : real) (h1 : term7 n m) (h2 : term18 x) : (term7 n m) = ((term29 m x n) = (term27 x n m)).
Proof. exact (prop_ext (fun h3 : term7 n m => @lem1641453 n m x h1 h2) (fun h3 : (term29 m x n) = (term27 x n m) => @lem1641139 n m h1)). Qed.
Lemma lem1641455 (n : nat) (m : nat) (x : real) (h1 : term7 n m) (h2 : term18 x) : (term29 m x n) = (term27 x n m).
Proof. exact (EQ_MP (@lem1641454 n m x h1 h2) (@lem1641139 n m h1)). Qed.
Lemma lem1641456 (n : nat) (m : nat) (x : real) (h1 : term18 x) : term32 x n m.
Proof. exact (fun h0 : term7 n m => @lem1641455 n m x h0 h1). Qed.
Lemma lem1641457 (x : real) (n : nat) (m : nat) (h1 : term18 x) (h2 : Peano.le n m) : (term29 m x n) = (term26 x m n).
Proof. exact (EQ_MP (@lem1641258 x n m h1 h2) (@lem0)). Qed.
Lemma lem1641458 (x : real) (n : nat) (m : nat) (h1 : term18 x) (h2 : Peano.le n m) : (Peano.le n m) = ((term29 m x n) = (term26 x m n)).
Proof. exact (prop_ext (fun h3 : Peano.le n m => @lem1641457 x n m h1 h2) (fun h3 : (term29 m x n) = (term26 x m n) => @lem1641122 n m h2)). Qed.
Lemma lem1641459 (x : real) (n : nat) (m : nat) (h1 : term18 x) (h2 : Peano.le n m) : (term29 m x n) = (term26 x m n).
Proof. exact (EQ_MP (@lem1641458 x n m h1 h2) (@lem1641122 n m h2)). Qed.
Lemma lem1641460 (m : nat) (n : nat) (x : real) (h1 : term18 x) : term36 x m n.
Proof. exact (fun h0 : Peano.le n m => @lem1641459 x n m h1 h0). Qed.
Lemma lem1641461 (n : nat) (m : nat) (x : real) (h1 : term18 x) : term39 x n m.
Proof. exact (conj (@lem1641460 m n x h1) (@lem1641456 n m x h1)). Qed.
Lemma lem1641462 (n : nat) (m : nat) (x : real) (h1 : term18 x) : (term29 m x n) = (term40 x n m).
Proof. exact (EQ_MP (@lem1641121 x n m) (@lem1641461 n m x h1)). Qed.
Lemma lem1641463 (n : nat) (m : nat) (x : real) (h1 : term18 x) : (term18 x) = ((term29 m x n) = (term40 x n m)).
Proof. exact (prop_ext (fun h2 : term18 x => @lem1641462 n m x h1) (fun h2 : (term29 m x n) = (term40 x n m) => @lem1641103 x h1)). Qed.
Lemma lem1641464 (n : nat) (m : nat) (x : real) (h1 : term18 x) : (term29 m x n) = (term40 x n m).
Proof. exact (EQ_MP (@lem1641463 n m x h1) (@lem1641103 x h1)). Qed.
Lemma lem1641465 (x : real) (n : nat) (m : nat) : term74 x n m.
Proof. exact (fun h0 : term18 x => @lem1641464 n m x h0). Qed.
Lemma lem1641470 (x : real) (m : nat) : term75 x m.
Proof. exact (fun n : nat => @lem1641465 x n m). Qed.
Lemma lem1641475 (x : real) : term76 x.
Proof. exact (fun m : nat => @lem1641470 x m). Qed.
Lemma lem1641480 : term77.
Proof. exact (fun x : real => @lem1641475 x). Qed.
