Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IMAGE_SNDCART_PCROSS_term_abbrevs.
Require Import CONJ_SYM_spec.
Require Import EXTENSION_spec.
Require Import IMAGE_CLAUSES_spec.
Require Import IN_IMAGE_spec.
Require Import PCROSS_EMPTY_spec.
Require Import SNDCART_PASTECART_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm13473_spec.
Require Import thm16433_spec.
Require Import thm16434_spec.
Require Import thm16439_spec.
Require Import thm16440_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm8004099_spec.
Lemma lem8035217 {A M N : Type'} (x : cart A M) : term0 A M N x.
Proof. exact (@lem7648197 A M N x). Qed.
Lemma lem8035218 {A M N : Type'} (x : cart A M) : (term0 A M N x) = (term1 A M N x).
Proof. exact (eq_refl (term0 A M N x)). Qed.
Lemma lem8035219 {A M N : Type'} (x : cart A M) : term1 A M N x.
Proof. exact (EQ_MP (@lem8035218 A M N x) (@lem8035217 A M N x)). Qed.
Lemma lem8035220 {A M N : Type'} (x : cart A M) (y : cart A N) : term2 A M N x y.
Proof. exact (@lem8035219 A M N x y). Qed.
Lemma lem8035221 {A M N : Type'} (x : cart A M) (y : cart A N) : (term2 A M N x y) = ((term3 A M N x y) = y).
Proof. exact (eq_refl (term2 A M N x y)). Qed.
Lemma lem8035223 (t1 : Prop) : term4 t1.
Proof. exact (@lem539 t1). Qed.
Lemma lem8035224 (t1 : Prop) : (term4 t1) = (term5 t1).
Proof. exact (eq_refl (term4 t1)). Qed.
Lemma lem8035225 (t1 : Prop) : term5 t1.
Proof. exact (EQ_MP (@lem8035224 t1) (@lem8035223 t1)). Qed.
Lemma lem8035226 (t1 : Prop) (t2 : Prop) : term6 t1 t2.
Proof. exact (@lem8035225 t1 t2). Qed.
Lemma lem8035227 (t2 : Prop) (t1 : Prop) : (term6 t1 t2) = ((t1 /\ t2) = (t2 /\ t1)).
Proof. exact (eq_refl (term6 t1 t2)). Qed.
Lemma lem8035229 {A B : Type'} (y : B) : term7 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem8035230 {A B : Type'} (y : B) : (term7 A B y) = (term8 A B y).
Proof. exact (eq_refl (term7 A B y)). Qed.
Lemma lem8035231 {A B : Type'} (y : B) : term8 A B y.
Proof. exact (EQ_MP (@lem8035230 A B y) (@lem8035229 A B y)). Qed.
Lemma lem8035232 {A B : Type'} (y : B) (s : A -> Prop) : term9 A B y s.
Proof. exact (@lem8035231 A B y s). Qed.
Lemma lem8035233 {A B : Type'} (y : B) (s : A -> Prop) : (term9 A B y s) = (term10 A B y s).
Proof. exact (eq_refl (term9 A B y s)). Qed.
Lemma lem8035234 {A B : Type'} (y : B) (s : A -> Prop) : term10 A B y s.
Proof. exact (EQ_MP (@lem8035233 A B y s) (@lem8035232 A B y s)). Qed.
Lemma lem8035235 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term11 A B y s f.
Proof. exact (@lem8035234 A B y s f). Qed.
Lemma lem8035236 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term11 A B y s f) = ((term12 A B y f s) = (term13 A B y f s)).
Proof. exact (eq_refl (term11 A B y s f)). Qed.
Lemma lem8035238 {A : Type'} (s : A -> Prop) : term14 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem8035239 {A : Type'} (s : A -> Prop) : (term14 A s) = (term15 A s).
Proof. exact (eq_refl (term14 A s)). Qed.
Lemma lem8035240 {A : Type'} (s : A -> Prop) : term15 A s.
Proof. exact (EQ_MP (@lem8035239 A s) (@lem8035238 A s)). Qed.
Lemma lem8035241 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term16 A s t.
Proof. exact (@lem8035240 A s t). Qed.
Lemma lem8035242 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term16 A s t) = ((s = t) = (term17 A s t)).
Proof. exact (eq_refl (term16 A s t)). Qed.
Lemma lem8035244 {N : Type'} (_474 : type30 N) (_475 : Prop) (_476 : type58 N) (_477 : type30 N) : (term18 N _476 _475 _474 _477) = (term19 N _474 _475 _476 _477).
Proof. exact (@lem13473 (type30 N) _474 _475 _476 _477). Qed.
Lemma lem8035245 {M N : Type'} (_474 : type30 N) (_475 : Prop) (s : type30 M) (t : type30 N) (_477 : type30 N) : (term20 M N s t _475 _474 _477) = (term21 M N _474 _475 s t _477).
Proof. exact (@lem8035244 N _474 _475 (term22 M N s t) _477). Qed.
Lemma lem8035246 {M N : Type'} (s : type30 M) (t : type30 N) : (term23 M N s t) = (term24 M N s t).
Proof. exact (@lem8035245 M N (@EMPTY (cart real N)) (s = (@EMPTY (cart real M))) s t t). Qed.
Lemma lem8035247 {M N : Type'} (s : type30 M) (t : type30 N) : (term25 M N s t) = ((term26 M N s t) = t).
Proof. exact (eq_refl (term25 M N s t)). Qed.
Lemma lem8035248 {M : Type'} (s : type30 M) : (term27 M s) = (term27 M s).
Proof. exact (eq_refl (term27 M s)). Qed.
Lemma lem8035249 {M N : Type'} (s : type30 M) (t : type30 N) : (term28 M N s t) = (term29 M N s t).
Proof. exact (MK_COMB (@lem8035248 M s) (@lem8035247 M N s t)). Qed.
Lemma lem8035250 {M N : Type'} (s : type30 M) (t : type30 N) : (term30 M N s t) = ((term26 M N s t) = (@EMPTY (cart real N))).
Proof. exact (eq_refl (term30 M N s t)). Qed.
Lemma lem8035251 {M : Type'} (s : type30 M) : (term31 M s) = (term31 M s).
Proof. exact (eq_refl (term31 M s)). Qed.
Lemma lem8035252 {M N : Type'} (s : type30 M) (t : type30 N) : (term32 M N s t) = (term33 M N s t).
Proof. exact (MK_COMB (@lem8035251 M s) (@lem8035250 M N s t)). Qed.
Lemma lem8035253 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8035254 {M N : Type'} (s : type30 M) (t : type30 N) : (term34 M N s t) = (term35 M N s t).
Proof. exact (MK_COMB (@lem8035253) (@lem8035252 M N s t)). Qed.
Lemma lem8035255 {M N : Type'} (s : type30 M) (t : type30 N) : (term24 M N s t) = (term36 M N s t).
Proof. exact (MK_COMB (@lem8035254 M N s t) (@lem8035249 M N s t)). Qed.
Lemma lem8035256 {M N : Type'} (s : type30 M) (t : type30 N) : (term23 M N s t) = ((term26 M N s t) = (term37 M N s t)).
Proof. exact (eq_refl (term23 M N s t)). Qed.
Lemma lem8035257 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8035258 {M N : Type'} (s : type30 M) (t : type30 N) : (term38 M N s t) = (term39 M N s t).
Proof. exact (MK_COMB (@lem8035257) (@lem8035256 M N s t)). Qed.
Lemma lem8035259 {M N : Type'} (s : type30 M) (t : type30 N) : ((term23 M N s t) = (term24 M N s t)) = (((term26 M N s t) = (term37 M N s t)) = (term36 M N s t)).
Proof. exact (MK_COMB (@lem8035258 M N s t) (@lem8035255 M N s t)). Qed.
Lemma lem8035260 {M N : Type'} (s : type30 M) (t : type30 N) : ((term26 M N s t) = (term37 M N s t)) = (term36 M N s t).
Proof. exact (EQ_MP (@lem8035259 M N s t) (@lem8035246 M N s t)). Qed.
Lemma lem8035261 {M N : Type'} (s : type30 M) (t : type30 N) : (term36 M N s t) = ((term26 M N s t) = (term37 M N s t)).
Proof. exact (SYM (@lem8035260 M N s t)). Qed.
Lemma lem8035262 {M : Type'} (s : type30 M) (h1 : s = (@EMPTY (cart real M))) : s = (@EMPTY (cart real M)).
Proof. exact (h1). Qed.
Lemma lem8035279 {M : Type'} (s : type30 M) (h1 : term40 M s) : term40 M s.
Proof. exact (h1). Qed.
Lemma lem8035298 {_141994 _141995 _141996 : Type'} : term41 _141994 _141995 _141996.
Proof. exact (proj2 (@lem8005965 Prop Prop Prop _141994 _141995 _141996)). Qed.
Lemma lem8035299 {_141994 _141995 _141996 : Type'} (t : type24 _141994 _141996) : term42 _141994 _141995 _141996 t.
Proof. exact (@lem8035298 _141994 _141995 _141996 t). Qed.
Lemma lem8035300 {_141994 _141995 _141996 : Type'} (t : type24 _141994 _141996) : (term42 _141994 _141995 _141996 t) = ((@PCROSS _141994 _141995 _141996 (@EMPTY (cart _141994 _141995)) t) = (@EMPTY (cart _141994 (finite_sum _141995 _141996)))).
Proof. exact (eq_refl (term42 _141994 _141995 _141996 t)). Qed.
Lemma lem8035309 {M : Type'} (s : type30 M) (h1 : s = (@EMPTY (cart real M))) : s = (@EMPTY (cart real M)).
Proof. exact (h1). Qed.
Lemma lem8035310 {M N : Type'} : (@PCROSS real M N) = (@PCROSS real M N).
Proof. exact (eq_refl (@PCROSS real M N)). Qed.
Lemma lem8035311 {M N : Type'} (s : type30 M) (h1 : s = (@EMPTY (cart real M))) : (@PCROSS real M N s) = (@PCROSS real M N (@EMPTY (cart real M))).
Proof. exact (MK_COMB (@lem8035310 M N) (@lem8035309 M s h1)). Qed.
Lemma lem8035312 {N : Type'} (t : type30 N) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem8035313 {M N : Type'} (t : type30 N) (s : type30 M) (h1 : s = (@EMPTY (cart real M))) : (@PCROSS real M N s t) = (@PCROSS real M N (@EMPTY (cart real M)) t).
Proof. exact (MK_COMB (@lem8035311 M N s h1) (@lem8035312 N t)). Qed.
Lemma lem8035315 {_141994 _141995 _141996 : Type'} (t : type24 _141994 _141996) : (@PCROSS _141994 _141995 _141996 (@EMPTY (cart _141994 _141995)) t) = (@EMPTY (cart _141994 (finite_sum _141995 _141996))).
Proof. exact (EQ_MP (@lem8035300 _141994 _141995 _141996 t) (@lem8035299 _141994 _141995 _141996 t)). Qed.
Lemma lem8035316 {M N : Type'} (t : type30 N) : (@PCROSS real M N (@EMPTY (cart real M)) t) = (@EMPTY (cart real (finite_sum M N))).
Proof. exact (@lem8035315 real M N t). Qed.
Lemma lem8035317 {M N : Type'} (t : type30 N) (s : type30 M) (h1 : s = (@EMPTY (cart real M))) : (@PCROSS real M N s t) = (@EMPTY (cart real (finite_sum M N))).
Proof. exact (TRANS (@lem8035313 M N t s h1) (@lem8035316 M N t)). Qed.
Lemma lem8035318 {M N : Type'} : (@IMAGE (cart real (finite_sum M N)) (cart real N) (@sndcart real M N)) = (@IMAGE (cart real (finite_sum M N)) (cart real N) (@sndcart real M N)).
Proof. exact (eq_refl (@IMAGE (cart real (finite_sum M N)) (cart real N) (@sndcart real M N))). Qed.
Lemma lem8035319 {M N : Type'} (t : type30 N) (s : type30 M) (h1 : s = (@EMPTY (cart real M))) : (term26 M N s t) = (@IMAGE (cart real (finite_sum M N)) (cart real N) (@sndcart real M N) (@EMPTY (cart real (finite_sum M N)))).
Proof. exact (MK_COMB (@lem8035318 M N) (@lem8035317 M N t s h1)). Qed.
Lemma lem8035321 {_87477 _87481 : Type'} (f : _87477 -> _87481) : (@IMAGE _87477 _87481 f (@EMPTY _87477)) = (@EMPTY _87481).
Proof. exact (proj1 (@lem3366870 _87477 _87481 (@el _87477) f (@el (_87477 -> Prop)))). Qed.
Lemma lem8035322 {M N : Type'} (f : type28 M N) : (@IMAGE (cart real (finite_sum M N)) (cart real N) f (@EMPTY (cart real (finite_sum M N)))) = (@EMPTY (cart real N)).
Proof. exact (@lem8035321 (type5 M N) (cart real N) f). Qed.
Lemma lem8035323 {M N : Type'} : (@IMAGE (cart real (finite_sum M N)) (cart real N) (@sndcart real M N) (@EMPTY (cart real (finite_sum M N)))) = (@EMPTY (cart real N)).
Proof. exact (@lem8035322 M N (@sndcart real M N)). Qed.
Lemma lem8035324 {M N : Type'} (t : type30 N) (s : type30 M) (h1 : s = (@EMPTY (cart real M))) : (term26 M N s t) = (@EMPTY (cart real N)).
Proof. exact (TRANS (@lem8035319 M N t s h1) (@lem8035323 M N)). Qed.
Lemma lem8035325 {N : Type'} : (@eq ((cart real N) -> Prop)) = (@eq ((cart real N) -> Prop)).
Proof. exact (eq_refl (@eq ((cart real N) -> Prop))). Qed.
Lemma lem8035326 {M N : Type'} (t : type30 N) (s : type30 M) (h1 : s = (@EMPTY (cart real M))) : (term43 M N s t) = (@eq ((cart real N) -> Prop) (@EMPTY (cart real N))).
Proof. exact (MK_COMB (@lem8035325 N) (@lem8035324 M N t s h1)). Qed.
Lemma lem8035327 {N : Type'} : (@EMPTY (cart real N)) = (@EMPTY (cart real N)).
Proof. exact (eq_refl (@EMPTY (cart real N))). Qed.
Lemma lem8035328 {M N : Type'} (t : type30 N) (s : type30 M) (h1 : s = (@EMPTY (cart real M))) : ((term26 M N s t) = (@EMPTY (cart real N))) = ((@EMPTY (cart real N)) = (@EMPTY (cart real N))).
Proof. exact (MK_COMB (@lem8035326 M N t s h1) (@lem8035327 N)). Qed.
Lemma lem8035330 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem8035331 {N : Type'} (x : type30 N) : (x = x) = True.
Proof. exact (@lem8035330 (type30 N) x). Qed.
Lemma lem8035332 {N : Type'} : ((@EMPTY (cart real N)) = (@EMPTY (cart real N))) = True.
Proof. exact (@lem8035331 N (@EMPTY (cart real N))). Qed.
Lemma lem8035333 {M N : Type'} (t : type30 N) (s : type30 M) (h1 : s = (@EMPTY (cart real M))) : ((term26 M N s t) = (@EMPTY (cart real N))) = True.
Proof. exact (TRANS (@lem8035328 M N t s h1) (@lem8035332 N)). Qed.
Lemma lem8035334 {M N : Type'} (t : type30 N) (s : type30 M) (h1 : s = (@EMPTY (cart real M))) : True = ((term26 M N s t) = (@EMPTY (cart real N))).
Proof. exact (SYM (@lem8035333 M N t s h1)). Qed.
Lemma lem8035366 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term17 A s t).
Proof. exact (EQ_MP (@lem8035242 A s t) (@lem8035241 A s t)). Qed.
Lemma lem8035367 {N : Type'} (s : type30 N) (t : type30 N) : (s = t) = (term44 N s t).
Proof. exact (@lem8035366 (cart real N) s t). Qed.
Lemma lem8035368 {M N : Type'} (s : type30 M) (t : type30 N) : ((term26 M N s t) = t) = (term45 M N s t).
Proof. exact (@lem8035367 N (term26 M N s t) t). Qed.
Lemma lem8035378 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term12 A B y f s) = (term13 A B y f s).
Proof. exact (EQ_MP (@lem8035236 A B y f s) (@lem8035235 A B y s f)). Qed.
Lemma lem8035379 {M N : Type'} (y : cart real N) (f : type28 M N) (s : type29 M N) : (term46 M N y f s) = (term47 M N y f s).
Proof. exact (@lem8035378 (type5 M N) (cart real N) y f s). Qed.
Lemma lem8035380 {M N : Type'} (x : cart real N) (s : type30 M) (t : type30 N) : (term48 M N x s t) = (term49 M N x s t).
Proof. exact (@lem8035379 M N x (@sndcart real M N) (@PCROSS real M N s t)). Qed.
Lemma lem8035391 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8035392 {M N : Type'} (x : cart real N) (s : type30 M) (t : type30 N) : (term50 M N x s t) = (term51 M N x s t).
Proof. exact (MK_COMB (@lem8035391) (@lem8035380 M N x s t)). Qed.
Lemma lem8035393 {N : Type'} (x : cart real N) (t : type30 N) : (@IN (cart real N) x t) = (@IN (cart real N) x t).
Proof. exact (eq_refl (@IN (cart real N) x t)). Qed.
Lemma lem8035394 {M N : Type'} (s : type30 M) (x : cart real N) (t : type30 N) : ((term48 M N x s t) = (@IN (cart real N) x t)) = ((term49 M N x s t) = (@IN (cart real N) x t)).
Proof. exact (MK_COMB (@lem8035392 M N x s t) (@lem8035393 N x t)). Qed.
Lemma lem8035399 {M N : Type'} (s : type30 M) (t : type30 N) : (term52 M N s t) = (term53 M N s t).
Proof. exact (fun_ext (fun x : cart real N => @lem8035394 M N s x t)). Qed.
Lemma lem8035400 {N : Type'} : (@all (cart real N)) = (@all (cart real N)).
Proof. exact (eq_refl (@all (cart real N))). Qed.
Lemma lem8035401 {M N : Type'} (s : type30 M) (t : type30 N) : (term45 M N s t) = (term54 M N s t).
Proof. exact (MK_COMB (@lem8035400 N) (@lem8035399 M N s t)). Qed.
Lemma lem8035406 {M N : Type'} (s : type30 M) (t : type30 N) : ((term26 M N s t) = t) = (term54 M N s t).
Proof. exact (TRANS (@lem8035368 M N s t) (@lem8035401 M N s t)). Qed.
Lemma lem8035407 {M N : Type'} (s : type30 M) (t : type30 N) : (term54 M N s t) = ((term26 M N s t) = t).
Proof. exact (SYM (@lem8035406 M N s t)). Qed.
Lemma lem8035421 (t2 : Prop) (t1 : Prop) : (t1 /\ t2) = (t2 /\ t1).
Proof. exact (EQ_MP (@lem8035227 t2 t1) (@lem8035226 t1 t2)). Qed.
Lemma lem8035422 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) (x' : type5 M N) : (term55 M N x x' s t) = (term56 M N s t x x').
Proof. exact (@lem8035421 (term57 M N x' s t) (x = (@sndcart real M N x'))). Qed.
Lemma lem8035423 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term58 M N x s t) = (term59 M N s t x).
Proof. exact (fun_ext (fun x' : type5 M N => @lem8035422 M N s t x x')). Qed.
Lemma lem8035424 {M N : Type'} : (@ex (cart real (finite_sum M N))) = (@ex (cart real (finite_sum M N))).
Proof. exact (eq_refl (@ex (cart real (finite_sum M N)))). Qed.
Lemma lem8035425 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term49 M N x s t) = (term60 M N s t x).
Proof. exact (MK_COMB (@lem8035424 M N) (@lem8035423 M N s t x)). Qed.
Lemma lem8035426 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8035427 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term51 M N x s t) = (term61 M N s t x).
Proof. exact (MK_COMB (@lem8035426) (@lem8035425 M N s t x)). Qed.
Lemma lem8035428 {N : Type'} (x : cart real N) (t : type30 N) : (@IN (cart real N) x t) = (@IN (cart real N) x t).
Proof. exact (eq_refl (@IN (cart real N) x t)). Qed.
Lemma lem8035429 {M N : Type'} (s : type30 M) (x : cart real N) (t : type30 N) : ((term49 M N x s t) = (@IN (cart real N) x t)) = ((term60 M N s t x) = (@IN (cart real N) x t)).
Proof. exact (MK_COMB (@lem8035427 M N s t x) (@lem8035428 N x t)). Qed.
Lemma lem8035430 {M N : Type'} (s : type30 M) (t : type30 N) : (term53 M N s t) = (term62 M N s t).
Proof. exact (fun_ext (fun x : cart real N => @lem8035429 M N s x t)). Qed.
Lemma lem8035431 {N : Type'} : (@all (cart real N)) = (@all (cart real N)).
Proof. exact (eq_refl (@all (cart real N))). Qed.
Lemma lem8035432 {M N : Type'} (s : type30 M) (t : type30 N) : (term54 M N s t) = (term63 M N s t).
Proof. exact (MK_COMB (@lem8035431 N) (@lem8035430 M N s t)). Qed.
Lemma lem8035433 {M N : Type'} (s : type30 M) (t : type30 N) : (term63 M N s t) = (term54 M N s t).
Proof. exact (SYM (@lem8035432 M N s t)). Qed.
Lemma lem8035441 {_141895 _141896 _141897 : Type'} (s : type24 _141895 _141896) (t : type24 _141895 _141897) (P : type16 _141895 _141896 _141897) : (term64 _141895 _141896 _141897 s t P) = (term65 _141895 _141896 _141897 s t P).
Proof. exact (EQ_MP (@lem8004099 _141895 _141896 _141897 s t P) (@lem0)). Qed.
Lemma lem8035442 {M N : Type'} (s : type30 M) (t : type30 N) (P : type29 M N) : (term66 M N s t P) = (term67 M N s t P).
Proof. exact (@lem8035441 real M N s t P). Qed.
Lemma lem8035443 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term68 M N s t x) = (term69 M N s t x).
Proof. exact (@lem8035442 M N s t (term70 M N x)). Qed.
Lemma lem8035444 {M N : Type'} (x : cart real N) (x' : type5 M N) : (term71 M N x x') = (x = (@sndcart real M N x')).
Proof. exact (eq_refl (term71 M N x x')). Qed.
Lemma lem8035445 {M N : Type'} (x : type5 M N) (s : type30 M) (t : type30 N) : (term72 M N x s t) = (term72 M N x s t).
Proof. exact (eq_refl (term72 M N x s t)). Qed.
Lemma lem8035446 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) (x' : type5 M N) : (term73 M N s t x x') = (term56 M N s t x x').
Proof. exact (MK_COMB (@lem8035445 M N x' s t) (@lem8035444 M N x x')). Qed.
Lemma lem8035447 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term74 M N s t x) = (term59 M N s t x).
Proof. exact (fun_ext (fun x' : type5 M N => @lem8035446 M N s t x x')). Qed.
Lemma lem8035448 {M N : Type'} : (@ex (cart real (finite_sum M N))) = (@ex (cart real (finite_sum M N))).
Proof. exact (eq_refl (@ex (cart real (finite_sum M N)))). Qed.
Lemma lem8035449 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term68 M N s t x) = (term60 M N s t x).
Proof. exact (MK_COMB (@lem8035448 M N) (@lem8035447 M N s t x)). Qed.
Lemma lem8035450 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8035451 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term75 M N s t x) = (term61 M N s t x).
Proof. exact (MK_COMB (@lem8035450) (@lem8035449 M N s t x)). Qed.
Lemma lem8035452 {M N : Type'} (x : cart real N) (x' : cart real M) (y : cart real N) : (term76 M N x x' y) = (x = (term77 M N x' y)).
Proof. exact (eq_refl (term76 M N x x' y)). Qed.
Lemma lem8035453 {N : Type'} (y : cart real N) (t : type30 N) : (term78 N y t) = (term78 N y t).
Proof. exact (eq_refl (term78 N y t)). Qed.
Lemma lem8035454 {M N : Type'} (t : type30 N) (x : cart real N) (x' : cart real M) (y : cart real N) : (term79 M N t x x' y) = (term80 M N t x x' y).
Proof. exact (MK_COMB (@lem8035453 N y t) (@lem8035452 M N x x' y)). Qed.
Lemma lem8035455 {M : Type'} (x : cart real M) (s : type30 M) : (term78 M x s) = (term78 M x s).
Proof. exact (eq_refl (term78 M x s)). Qed.
Lemma lem8035456 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) (x' : cart real M) (y : cart real N) : (term81 M N s t x x' y) = (term82 M N s t x x' y).
Proof. exact (MK_COMB (@lem8035455 M x' s) (@lem8035454 M N t x x' y)). Qed.
Lemma lem8035457 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) (x' : cart real M) : (term83 M N s t x x') = (term84 M N s t x x').
Proof. exact (fun_ext (fun y : cart real N => @lem8035456 M N s t x x' y)). Qed.
Lemma lem8035458 {N : Type'} : (@ex (cart real N)) = (@ex (cart real N)).
Proof. exact (eq_refl (@ex (cart real N))). Qed.
Lemma lem8035459 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) (x' : cart real M) : (term85 M N s t x x') = (term86 M N s t x x').
Proof. exact (MK_COMB (@lem8035458 N) (@lem8035457 M N s t x x')). Qed.
Lemma lem8035460 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term87 M N s t x) = (term88 M N s t x).
Proof. exact (fun_ext (fun x' : cart real M => @lem8035459 M N s t x x')). Qed.
Lemma lem8035461 {M : Type'} : (@ex (cart real M)) = (@ex (cart real M)).
Proof. exact (eq_refl (@ex (cart real M))). Qed.
Lemma lem8035462 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term69 M N s t x) = (term89 M N s t x).
Proof. exact (MK_COMB (@lem8035461 M) (@lem8035460 M N s t x)). Qed.
Lemma lem8035463 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : ((term68 M N s t x) = (term69 M N s t x)) = ((term60 M N s t x) = (term89 M N s t x)).
Proof. exact (MK_COMB (@lem8035451 M N s t x) (@lem8035462 M N s t x)). Qed.
Lemma lem8035464 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term60 M N s t x) = (term89 M N s t x).
Proof. exact (EQ_MP (@lem8035463 M N s t x) (@lem8035443 M N s t x)). Qed.
Lemma lem8035480 {A M N : Type'} (x : cart A M) (y : cart A N) : (term3 A M N x y) = y.
Proof. exact (EQ_MP (@lem8035221 A M N x y) (@lem8035220 A M N x y)). Qed.
Lemma lem8035481 {M N : Type'} (x : cart real M) (y : cart real N) : (term77 M N x y) = y.
Proof. exact (@lem8035480 real M N x y). Qed.
Lemma lem8035482 {N : Type'} (x : cart real N) : (@eq (cart real N) x) = (@eq (cart real N) x).
Proof. exact (eq_refl (@eq (cart real N) x)). Qed.
Lemma lem8035483 {M N : Type'} (x : cart real M) (x' : cart real N) (y : cart real N) : (x' = (term77 M N x y)) = (x' = y).
Proof. exact (MK_COMB (@lem8035482 N x') (@lem8035481 M N x y)). Qed.
Lemma lem8035486 {N : Type'} (y : cart real N) (t : type30 N) : (term78 N y t) = (term78 N y t).
Proof. exact (eq_refl (term78 N y t)). Qed.
Lemma lem8035487 {M N : Type'} (x : cart real M) (t : type30 N) (x' : cart real N) (y : cart real N) : (term80 M N t x' x y) = (term90 N t x' y).
Proof. exact (MK_COMB (@lem8035486 N y t) (@lem8035483 M N x x' y)). Qed.
Lemma lem8035490 {M : Type'} (x : cart real M) (s : type30 M) : (term78 M x s) = (term78 M x s).
Proof. exact (eq_refl (term78 M x s)). Qed.
Lemma lem8035491 {M N : Type'} (x : cart real M) (s : type30 M) (t : type30 N) (x' : cart real N) (y : cart real N) : (term82 M N s t x' x y) = (term91 M N x s t x' y).
Proof. exact (MK_COMB (@lem8035490 M x s) (@lem8035487 M N x t x' y)). Qed.
Lemma lem8035494 {M N : Type'} (x : cart real M) (s : type30 M) (t : type30 N) (x' : cart real N) : (term84 M N s t x' x) = (term92 M N x s t x').
Proof. exact (fun_ext (fun y : cart real N => @lem8035491 M N x s t x' y)). Qed.
Lemma lem8035495 {N : Type'} : (@ex (cart real N)) = (@ex (cart real N)).
Proof. exact (eq_refl (@ex (cart real N))). Qed.
Lemma lem8035496 {M N : Type'} (x : cart real M) (s : type30 M) (t : type30 N) (x' : cart real N) : (term86 M N s t x' x) = (term93 M N x s t x').
Proof. exact (MK_COMB (@lem8035495 N) (@lem8035494 M N x s t x')). Qed.
Lemma lem8035501 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term88 M N s t x) = (term94 M N s t x).
Proof. exact (fun_ext (fun x' : cart real M => @lem8035496 M N x' s t x)). Qed.
Lemma lem8035502 {M : Type'} : (@ex (cart real M)) = (@ex (cart real M)).
Proof. exact (eq_refl (@ex (cart real M))). Qed.
Lemma lem8035503 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term89 M N s t x) = (term95 M N s t x).
Proof. exact (MK_COMB (@lem8035502 M) (@lem8035501 M N s t x)). Qed.
Lemma lem8035508 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term60 M N s t x) = (term95 M N s t x).
Proof. exact (TRANS (@lem8035464 M N s t x) (@lem8035503 M N s t x)). Qed.
Lemma lem8035509 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8035510 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term61 M N s t x) = (term96 M N s t x).
Proof. exact (MK_COMB (@lem8035509) (@lem8035508 M N s t x)). Qed.
Lemma lem8035511 {N : Type'} (x : cart real N) (t : type30 N) : (@IN (cart real N) x t) = (@IN (cart real N) x t).
Proof. exact (eq_refl (@IN (cart real N) x t)). Qed.
Lemma lem8035512 {M N : Type'} (s : type30 M) (x : cart real N) (t : type30 N) : ((term60 M N s t x) = (@IN (cart real N) x t)) = ((term95 M N s t x) = (@IN (cart real N) x t)).
Proof. exact (MK_COMB (@lem8035510 M N s t x) (@lem8035511 N x t)). Qed.
Lemma lem8035515 {M N : Type'} (s : type30 M) (t : type30 N) : (term62 M N s t) = (term97 M N s t).
Proof. exact (fun_ext (fun x : cart real N => @lem8035512 M N s x t)). Qed.
Lemma lem8035516 {N : Type'} : (@all (cart real N)) = (@all (cart real N)).
Proof. exact (eq_refl (@all (cart real N))). Qed.
Lemma lem8035517 {M N : Type'} (s : type30 M) (t : type30 N) : (term63 M N s t) = (term98 M N s t).
Proof. exact (MK_COMB (@lem8035516 N) (@lem8035515 M N s t)). Qed.
Lemma lem8035522 {M N : Type'} (s : type30 M) (t : type30 N) : (term98 M N s t) = (term63 M N s t).
Proof. exact (SYM (@lem8035517 M N s t)). Qed.
Lemma lem8035538 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term17 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem8035539 {M : Type'} (s : type30 M) (t : type30 M) : (s = t) = (term44 M s t).
Proof. exact (@lem8035538 (cart real M) s t). Qed.
Lemma lem8035540 {M : Type'} (s : type30 M) : (s = (@EMPTY (cart real M))) = (term99 M s).
Proof. exact (@lem8035539 M s (@EMPTY (cart real M))). Qed.
Lemma lem8035549 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8035550 {M : Type'} (s : type30 M) : (term40 M s) = (term100 M s).
Proof. exact (MK_COMB (@lem8035549) (@lem8035540 M s)). Qed.
Lemma lem8035551 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8035552 {M : Type'} (s : type30 M) : (term27 M s) = (term101 M s).
Proof. exact (MK_COMB (@lem8035551) (@lem8035550 M s)). Qed.
Lemma lem8035577 {M N : Type'} (s : type30 M) (t : type30 N) : (term98 M N s t) = (term98 M N s t).
Proof. exact (eq_refl (term98 M N s t)). Qed.
Lemma lem8035578 {M N : Type'} (s : type30 M) (t : type30 N) : (term102 M N s t) = (term103 M N s t).
Proof. exact (MK_COMB (@lem8035552 M s) (@lem8035577 M N s t)). Qed.
Lemma lem8035581 {M N : Type'} (s : type30 M) (t : type30 N) : (term103 M N s t) = (term102 M N s t).
Proof. exact (SYM (@lem8035578 M N s t)). Qed.
Lemma lem8035591 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8035592 {M : Type'} (P : type30 M) (x : cart real M) : (@IN (cart real M) x P) = (P x).
Proof. exact (@lem8035591 (cart real M) P x). Qed.
Lemma lem8035593 {M : Type'} (s : type30 M) (x : cart real M) : (@IN (cart real M) x s) = (s x).
Proof. exact (@lem8035592 M s x). Qed.
Lemma lem8035594 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8035595 {M : Type'} (s : type30 M) (x : cart real M) : (term104 M x s) = (term105 M s x).
Proof. exact (MK_COMB (@lem8035594) (@lem8035593 M s x)). Qed.
Lemma lem8035597 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem8035598 {M : Type'} (x : cart real M) : (@IN (cart real M) x (@EMPTY (cart real M))) = False.
Proof. exact (@lem8035597 (cart real M) x). Qed.
Lemma lem8035599 {M : Type'} (s : type30 M) (x : cart real M) : ((@IN (cart real M) x s) = (@IN (cart real M) x (@EMPTY (cart real M)))) = ((s x) = False).
Proof. exact (MK_COMB (@lem8035595 M s x) (@lem8035598 M x)). Qed.
Lemma lem8035601 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem8035602 {M : Type'} (s : type30 M) (x : cart real M) : ((s x) = False) = (term106 M s x).
Proof. exact (@lem8035601 (s x)). Qed.
Lemma lem8035603 {M : Type'} (s : type30 M) (x : cart real M) : ((@IN (cart real M) x s) = (@IN (cart real M) x (@EMPTY (cart real M)))) = (term106 M s x).
Proof. exact (TRANS (@lem8035599 M s x) (@lem8035602 M s x)). Qed.
Lemma lem8035604 {M : Type'} (s : type30 M) : (term107 M s) = (term108 M s).
Proof. exact (fun_ext (fun x : cart real M => @lem8035603 M s x)). Qed.
Lemma lem8035605 {M : Type'} : (@all (cart real M)) = (@all (cart real M)).
Proof. exact (eq_refl (@all (cart real M))). Qed.
Lemma lem8035606 {M : Type'} (s : type30 M) : (term99 M s) = (term109 M s).
Proof. exact (MK_COMB (@lem8035605 M) (@lem8035604 M s)). Qed.
Lemma lem8035611 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8035612 {M : Type'} (s : type30 M) : (term100 M s) = (term110 M s).
Proof. exact (MK_COMB (@lem8035611) (@lem8035606 M s)). Qed.
Lemma lem8035613 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8035614 {M : Type'} (s : type30 M) : (term101 M s) = (term111 M s).
Proof. exact (MK_COMB (@lem8035613) (@lem8035612 M s)). Qed.
Lemma lem8035632 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8035633 {M : Type'} (P : type30 M) (x : cart real M) : (@IN (cart real M) x P) = (P x).
Proof. exact (@lem8035632 (cart real M) P x). Qed.
Lemma lem8035634 {M : Type'} (s : type30 M) (x : cart real M) : (@IN (cart real M) x s) = (s x).
Proof. exact (@lem8035633 M s x). Qed.
Lemma lem8035635 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8035636 {M : Type'} (s : type30 M) (x : cart real M) : (term78 M x s) = (term112 M s x).
Proof. exact (MK_COMB (@lem8035635) (@lem8035634 M s x)). Qed.
Lemma lem8035640 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8035641 {N : Type'} (P : type30 N) (x : cart real N) : (@IN (cart real N) x P) = (P x).
Proof. exact (@lem8035640 (cart real N) P x). Qed.
Lemma lem8035642 {N : Type'} (t : type30 N) (y : cart real N) : (@IN (cart real N) y t) = (t y).
Proof. exact (@lem8035641 N t y). Qed.
Lemma lem8035643 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8035644 {N : Type'} (t : type30 N) (y : cart real N) : (term78 N y t) = (term112 N t y).
Proof. exact (MK_COMB (@lem8035643) (@lem8035642 N t y)). Qed.
Lemma lem8035647 {N : Type'} (x : cart real N) (y : cart real N) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem8035648 {N : Type'} (t : type30 N) (x : cart real N) (y : cart real N) : (term90 N t x y) = (term113 N t x y).
Proof. exact (MK_COMB (@lem8035644 N t y) (@lem8035647 N x y)). Qed.
Lemma lem8035651 {M N : Type'} (s : type30 M) (x : cart real M) (t : type30 N) (x' : cart real N) (y : cart real N) : (term91 M N x s t x' y) = (term114 M N s x t x' y).
Proof. exact (MK_COMB (@lem8035636 M s x) (@lem8035648 N t x' y)). Qed.
Lemma lem8035654 {M N : Type'} (s : type30 M) (x : cart real M) (t : type30 N) (x' : cart real N) : (term92 M N x s t x') = (term115 M N s x t x').
Proof. exact (fun_ext (fun y : cart real N => @lem8035651 M N s x t x' y)). Qed.
Lemma lem8035655 {N : Type'} : (@ex (cart real N)) = (@ex (cart real N)).
Proof. exact (eq_refl (@ex (cart real N))). Qed.
Lemma lem8035656 {M N : Type'} (s : type30 M) (x : cart real M) (t : type30 N) (x' : cart real N) : (term93 M N x s t x') = (term116 M N s x t x').
Proof. exact (MK_COMB (@lem8035655 N) (@lem8035654 M N s x t x')). Qed.
Lemma lem8035661 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term94 M N s t x) = (term117 M N s t x).
Proof. exact (fun_ext (fun x' : cart real M => @lem8035656 M N s x' t x)). Qed.
Lemma lem8035662 {M : Type'} : (@ex (cart real M)) = (@ex (cart real M)).
Proof. exact (eq_refl (@ex (cart real M))). Qed.
Lemma lem8035663 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term95 M N s t x) = (term118 M N s t x).
Proof. exact (MK_COMB (@lem8035662 M) (@lem8035661 M N s t x)). Qed.
Lemma lem8035668 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8035669 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term96 M N s t x) = (term119 M N s t x).
Proof. exact (MK_COMB (@lem8035668) (@lem8035663 M N s t x)). Qed.
Lemma lem8035671 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8035672 {N : Type'} (P : type30 N) (x : cart real N) : (@IN (cart real N) x P) = (P x).
Proof. exact (@lem8035671 (cart real N) P x). Qed.
Lemma lem8035673 {N : Type'} (t : type30 N) (x : cart real N) : (@IN (cart real N) x t) = (t x).
Proof. exact (@lem8035672 N t x). Qed.
Lemma lem8035674 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : ((term95 M N s t x) = (@IN (cart real N) x t)) = ((term118 M N s t x) = (t x)).
Proof. exact (MK_COMB (@lem8035669 M N s t x) (@lem8035673 N t x)). Qed.
Lemma lem8035677 {M N : Type'} (s : type30 M) (t : type30 N) : (term97 M N s t) = (term120 M N s t).
Proof. exact (fun_ext (fun x : cart real N => @lem8035674 M N s t x)). Qed.
Lemma lem8035678 {N : Type'} : (@all (cart real N)) = (@all (cart real N)).
Proof. exact (eq_refl (@all (cart real N))). Qed.
Lemma lem8035679 {M N : Type'} (s : type30 M) (t : type30 N) : (term98 M N s t) = (term121 M N s t).
Proof. exact (MK_COMB (@lem8035678 N) (@lem8035677 M N s t)). Qed.
Lemma lem8035684 {M N : Type'} (s : type30 M) (t : type30 N) : (term103 M N s t) = (term122 M N s t).
Proof. exact (MK_COMB (@lem8035614 M s) (@lem8035679 M N s t)). Qed.
Lemma lem8035687 {M N : Type'} (s : type30 M) (t : type30 N) : (term122 M N s t) = (term103 M N s t).
Proof. exact (SYM (@lem8035684 M N s t)). Qed.
Lemma lem8035689 (p : Prop) : p = (term123 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8035690 {M N : Type'} (s : type30 M) (t : type30 N) : (term122 M N s t) = (term124 M N s t).
Proof. exact (@lem8035689 (term122 M N s t)). Qed.
Lemma lem8035691 {M N : Type'} (s : type30 M) (t : type30 N) : (term124 M N s t) = (term122 M N s t).
Proof. exact (SYM (@lem8035690 M N s t)). Qed.
Lemma lem8035692 {M N : Type'} (s : type30 M) (t : type30 N) (h1 : term125 M N s t) : term125 M N s t.
Proof. exact (h1). Qed.
Lemma lem8035695 {M N : Type'} (s : type30 M) (t : type30 N) (h1 : term124 M N s t) : term124 M N s t.
Proof. exact (h1). Qed.
Lemma lem8035696 {M N : Type'} (s : type30 M) (t : type30 N) : term126 M N s t.
Proof. exact (fun h0 : term124 M N s t => @lem8035695 M N s t h0). Qed.
Lemma lem8035697 {M N : Type'} (s : type30 M) (t : type30 N) (h1 : term126 M N s t) : term126 M N s t.
Proof. exact (h1). Qed.
Lemma lem8035698 {M N : Type'} (s : type30 M) (t : type30 N) (h1 : term124 M N s t) : term124 M N s t.
Proof. exact (h1). Qed.
Lemma lem8035699 {M N : Type'} (s : type30 M) (t : type30 N) (h1 : term124 M N s t) (h2 : term126 M N s t) : term124 M N s t.
Proof. exact (@lem8035697 M N s t h2 (@lem8035698 M N s t h1)). Qed.
Lemma lem8035700 {M N : Type'} (s : type30 M) (t : type30 N) (h1 : term124 M N s t) : term127 M N s t.
Proof. exact (fun h0 : term126 M N s t => @lem8035699 M N s t h1 h0). Qed.
Lemma lem8035701 {M N : Type'} (s : type30 M) (t : type30 N) (h1 : term126 M N s t) : term126 M N s t.
Proof. exact (h1). Qed.
Lemma lem8035702 {M N : Type'} (s : type30 M) (t : type30 N) (h1 : term124 M N s t) (h2 : term126 M N s t) : term124 M N s t.
Proof. exact (@lem8035700 M N s t h1 (@lem8035701 M N s t h2)). Qed.
Lemma lem8035703 {M N : Type'} (s : type30 M) (t : type30 N) (h1 : term126 M N s t) : term126 M N s t.
Proof. exact (fun h0 : term124 M N s t => @lem8035702 M N s t h0 h1). Qed.
Lemma lem8035704 {M N : Type'} (s : type30 M) (t : type30 N) : term128 M N s t.
Proof. exact (fun h0 : term126 M N s t => @lem8035703 M N s t h0). Qed.
Lemma lem8035707 {M N : Type'} (s : type30 M) (t : type30 N) : term126 M N s t.
Proof. exact (@lem8035704 M N s t (@lem8035696 M N s t)). Qed.
Lemma lem8035708 {M N : Type'} (s : type30 M) (t : type30 N) : term126 M N s t.
Proof. exact (@lem8035707 M N s t). Qed.
Lemma lem8035718 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem8035719 {M N : Type'} (s : type30 M) (t : type30 N) : (term124 M N s t) = (term129 M N s t).
Proof. exact (@lem8035718 (term125 M N s t)). Qed.
Lemma lem8035721 (t : Prop) : (term130 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem8035722 {M N : Type'} (s : type30 M) (t : type30 N) : (term129 M N s t) = (term122 M N s t).
Proof. exact (@lem8035721 (term122 M N s t)). Qed.
Lemma lem8035725 {M N : Type'} (s : type30 M) (t : type30 N) : (term124 M N s t) = (term122 M N s t).
Proof. exact (TRANS (@lem8035719 M N s t) (@lem8035722 M N s t)). Qed.
Lemma lem8035739 {A : Type'} (P : Prop) (Q : A -> Prop) : (term131 A P Q) = (term132 A P Q).
Proof. exact (EQ_MP (@lem16434 A P Q) (@lem16433 A P Q)). Qed.
Lemma lem8035740 {N : Type'} (P : Prop) (Q : type30 N) : (term133 N P Q) = (term134 N P Q).
Proof. exact (@lem8035739 (cart real N) P Q). Qed.
Lemma lem8035741 {M N : Type'} (s : type30 M) (x : cart real M) (t : type30 N) (x' : cart real N) : (term135 M N s x t x') = (term136 M N s x t x').
Proof. exact (@lem8035740 N (s x) (term137 N t x')). Qed.
Lemma lem8035742 {N : Type'} (t : type30 N) (x : cart real N) (y : cart real N) : (term138 N t x y) = (term113 N t x y).
Proof. exact (eq_refl (term138 N t x y)). Qed.
Lemma lem8035743 {M : Type'} (s : type30 M) (x : cart real M) : (term112 M s x) = (term112 M s x).
Proof. exact (eq_refl (term112 M s x)). Qed.
Lemma lem8035744 {M N : Type'} (s : type30 M) (x : cart real M) (t : type30 N) (x' : cart real N) (y : cart real N) : (term139 M N s x t x' y) = (term114 M N s x t x' y).
Proof. exact (MK_COMB (@lem8035743 M s x) (@lem8035742 N t x' y)). Qed.
Lemma lem8035745 {M N : Type'} (s : type30 M) (x : cart real M) (t : type30 N) (x' : cart real N) : (term140 M N s x t x') = (term115 M N s x t x').
Proof. exact (fun_ext (fun y : cart real N => @lem8035744 M N s x t x' y)). Qed.
Lemma lem8035746 {N : Type'} : (@ex (cart real N)) = (@ex (cart real N)).
Proof. exact (eq_refl (@ex (cart real N))). Qed.
Lemma lem8035747 {M N : Type'} (s : type30 M) (x : cart real M) (t : type30 N) (x' : cart real N) : (term135 M N s x t x') = (term116 M N s x t x').
Proof. exact (MK_COMB (@lem8035746 N) (@lem8035745 M N s x t x')). Qed.
Lemma lem8035748 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8035749 {M N : Type'} (s : type30 M) (x : cart real M) (t : type30 N) (x' : cart real N) : (term141 M N s x t x') = (term142 M N s x t x').
Proof. exact (MK_COMB (@lem8035748) (@lem8035747 M N s x t x')). Qed.
Lemma lem8035750 {N : Type'} (t : type30 N) (x : cart real N) (y : cart real N) : (term138 N t x y) = (term113 N t x y).
Proof. exact (eq_refl (term138 N t x y)). Qed.
Lemma lem8035751 {N : Type'} (t : type30 N) (x : cart real N) : (term143 N t x) = (term137 N t x).
Proof. exact (fun_ext (fun y : cart real N => @lem8035750 N t x y)). Qed.
Lemma lem8035752 {N : Type'} : (@ex (cart real N)) = (@ex (cart real N)).
Proof. exact (eq_refl (@ex (cart real N))). Qed.
Lemma lem8035753 {N : Type'} (t : type30 N) (x : cart real N) : (term144 N t x) = (term145 N t x).
Proof. exact (MK_COMB (@lem8035752 N) (@lem8035751 N t x)). Qed.
Lemma lem8035754 {M : Type'} (s : type30 M) (x : cart real M) : (term112 M s x) = (term112 M s x).
Proof. exact (eq_refl (term112 M s x)). Qed.
Lemma lem8035755 {M N : Type'} (s : type30 M) (x : cart real M) (t : type30 N) (x' : cart real N) : (term136 M N s x t x') = (term146 M N s x t x').
Proof. exact (MK_COMB (@lem8035754 M s x) (@lem8035753 N t x')). Qed.
Lemma lem8035756 {M N : Type'} (s : type30 M) (x : cart real M) (t : type30 N) (x' : cart real N) : ((term135 M N s x t x') = (term136 M N s x t x')) = ((term116 M N s x t x') = (term146 M N s x t x')).
Proof. exact (MK_COMB (@lem8035749 M N s x t x') (@lem8035755 M N s x t x')). Qed.
Lemma lem8035757 {M N : Type'} (s : type30 M) (x : cart real M) (t : type30 N) (x' : cart real N) : (term116 M N s x t x') = (term146 M N s x t x').
Proof. exact (EQ_MP (@lem8035756 M N s x t x') (@lem8035741 M N s x t x')). Qed.
Lemma lem8035790 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term117 M N s t x) = (term147 M N s t x).
Proof. exact (fun_ext (fun x' : cart real M => @lem8035757 M N s x' t x)). Qed.
Lemma lem8035791 {M : Type'} : (@ex (cart real M)) = (@ex (cart real M)).
Proof. exact (eq_refl (@ex (cart real M))). Qed.
Lemma lem8035792 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term118 M N s t x) = (term148 M N s t x).
Proof. exact (MK_COMB (@lem8035791 M) (@lem8035790 M N s t x)). Qed.
Lemma lem8035814 {A : Type'} (P : A -> Prop) (Q : Prop) : (term149 A P Q) = (term150 A P Q).
Proof. exact (EQ_MP (@lem16440 A P Q) (@lem16439 A P Q)). Qed.
Lemma lem8035815 {M : Type'} (P : type30 M) (Q : Prop) : (term151 M P Q) = (term152 M P Q).
Proof. exact (@lem8035814 (cart real M) P Q). Qed.
Lemma lem8035816 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term148 M N s t x) = (term153 M N s t x).
Proof. exact (@lem8035815 M s (term145 N t x)). Qed.
Lemma lem8035853 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term118 M N s t x) = (term153 M N s t x).
Proof. exact (TRANS (@lem8035792 M N s t x) (@lem8035816 M N s t x)). Qed.
Lemma lem8035854 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8035855 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term119 M N s t x) = (term154 M N s t x).
Proof. exact (MK_COMB (@lem8035854) (@lem8035853 M N s t x)). Qed.
Lemma lem8035856 {N : Type'} (t : type30 N) (x : cart real N) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem8035857 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : ((term118 M N s t x) = (t x)) = ((term153 M N s t x) = (t x)).
Proof. exact (MK_COMB (@lem8035855 M N s t x) (@lem8035856 N t x)). Qed.
Lemma lem8035858 {M N : Type'} (s : type30 M) (t : type30 N) : (term120 M N s t) = (term155 M N s t).
Proof. exact (fun_ext (fun x : cart real N => @lem8035857 M N s t x)). Qed.
Lemma lem8035859 {N : Type'} : (@all (cart real N)) = (@all (cart real N)).
Proof. exact (eq_refl (@all (cart real N))). Qed.
Lemma lem8035860 {M N : Type'} (s : type30 M) (t : type30 N) : (term121 M N s t) = (term156 M N s t).
Proof. exact (MK_COMB (@lem8035859 N) (@lem8035858 M N s t)). Qed.
Lemma lem8035865 {M : Type'} (s : type30 M) : (term111 M s) = (term111 M s).
Proof. exact (eq_refl (term111 M s)). Qed.
Lemma lem8035866 {M N : Type'} (s : type30 M) (t : type30 N) : (term122 M N s t) = (term157 M N s t).
Proof. exact (MK_COMB (@lem8035865 M s) (@lem8035860 M N s t)). Qed.
Lemma lem8035869 {M N : Type'} (s : type30 M) (t : type30 N) : (term124 M N s t) = (term157 M N s t).
Proof. exact (TRANS (@lem8035725 M N s t) (@lem8035866 M N s t)). Qed.
Lemma lem8035870 {M N : Type'} (t : type30 N) : (term158 M N t) = (term159 M N t).
Proof. exact (fun_ext (fun s : type30 M => @lem8035869 M N s t)). Qed.
Lemma lem8035871 {M : Type'} : (@all ((cart real M) -> Prop)) = (@all ((cart real M) -> Prop)).
Proof. exact (eq_refl (@all ((cart real M) -> Prop))). Qed.
Lemma lem8035872 {M N : Type'} (t : type30 N) : (term160 M N t) = (term161 M N t).
Proof. exact (MK_COMB (@lem8035871 M) (@lem8035870 M N t)). Qed.
Lemma lem8035877 {M N : Type'} : (term162 M N) = (term163 M N).
Proof. exact (fun_ext (fun t : type30 N => @lem8035872 M N t)). Qed.
Lemma lem8035878 {N : Type'} : (@all ((cart real N) -> Prop)) = (@all ((cart real N) -> Prop)).
Proof. exact (eq_refl (@all ((cart real N) -> Prop))). Qed.
Lemma lem8035887 {M N : Type'} : (term164 M N) = (term165 M N).
Proof. exact (MK_COMB (@lem8035878 N) (@lem8035877 M N)). Qed.
Lemma lem8035888 {N : Type'} (t : type30 N) (x : cart real N) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem8035893 {N : Type'} (t : type30 N) (x : cart real N) (y : cart real N) : (term113 N t x y) = (term113 N t x y).
Proof. exact (eq_refl (term113 N t x y)). Qed.
Lemma lem8035894 {N : Type'} (t : type30 N) (x : cart real N) : (term137 N t x) = (term137 N t x).
Proof. exact (fun_ext (fun y : cart real N => @lem8035893 N t x y)). Qed.
Lemma lem8035895 {N : Type'} : (@ex (cart real N)) = (@ex (cart real N)).
Proof. exact (eq_refl (@ex (cart real N))). Qed.
Lemma lem8035896 {N : Type'} (t : type30 N) (x : cart real N) : (term145 N t x) = (term145 N t x).
Proof. exact (MK_COMB (@lem8035895 N) (@lem8035894 N t x)). Qed.
Lemma lem8035897 {M : Type'} (s : type30 M) (x : cart real M) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem8035898 {M : Type'} (s : type30 M) : (term166 M s) = (term166 M s).
Proof. exact (fun_ext (fun x : cart real M => @lem8035897 M s x)). Qed.
Lemma lem8035899 {M : Type'} : (@ex (cart real M)) = (@ex (cart real M)).
Proof. exact (eq_refl (@ex (cart real M))). Qed.
Lemma lem8035900 {M : Type'} (s : type30 M) : (term167 M s) = (term167 M s).
Proof. exact (MK_COMB (@lem8035899 M) (@lem8035898 M s)). Qed.
Lemma lem8035901 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8035902 {M : Type'} (s : type30 M) : (term168 M s) = (term168 M s).
Proof. exact (MK_COMB (@lem8035901) (@lem8035900 M s)). Qed.
Lemma lem8035903 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term153 M N s t x) = (term153 M N s t x).
Proof. exact (MK_COMB (@lem8035902 M s) (@lem8035896 N t x)). Qed.
Lemma lem8035904 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8035905 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term154 M N s t x) = (term154 M N s t x).
Proof. exact (MK_COMB (@lem8035904) (@lem8035903 M N s t x)). Qed.
Lemma lem8035906 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : ((term153 M N s t x) = (t x)) = ((term153 M N s t x) = (t x)).
Proof. exact (MK_COMB (@lem8035905 M N s t x) (@lem8035888 N t x)). Qed.
Lemma lem8035907 {M N : Type'} (s : type30 M) (t : type30 N) : (term155 M N s t) = (term155 M N s t).
Proof. exact (fun_ext (fun x : cart real N => @lem8035906 M N s t x)). Qed.
Lemma lem8035908 {N : Type'} : (@all (cart real N)) = (@all (cart real N)).
Proof. exact (eq_refl (@all (cart real N))). Qed.
Lemma lem8035909 {M N : Type'} (s : type30 M) (t : type30 N) : (term156 M N s t) = (term156 M N s t).
Proof. exact (MK_COMB (@lem8035908 N) (@lem8035907 M N s t)). Qed.
Lemma lem8035912 {M : Type'} (s : type30 M) (x : cart real M) : (term106 M s x) = (term106 M s x).
Proof. exact (eq_refl (term106 M s x)). Qed.
Lemma lem8035913 {M : Type'} (s : type30 M) : (term108 M s) = (term108 M s).
Proof. exact (fun_ext (fun x : cart real M => @lem8035912 M s x)). Qed.
Lemma lem8035914 {M : Type'} : (@all (cart real M)) = (@all (cart real M)).
Proof. exact (eq_refl (@all (cart real M))). Qed.
Lemma lem8035915 {M : Type'} (s : type30 M) : (term109 M s) = (term109 M s).
Proof. exact (MK_COMB (@lem8035914 M) (@lem8035913 M s)). Qed.
Lemma lem8035916 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8035917 {M : Type'} (s : type30 M) : (term110 M s) = (term110 M s).
Proof. exact (MK_COMB (@lem8035916) (@lem8035915 M s)). Qed.
Lemma lem8035918 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8035919 {M : Type'} (s : type30 M) : (term111 M s) = (term111 M s).
Proof. exact (MK_COMB (@lem8035918) (@lem8035917 M s)). Qed.
Lemma lem8035920 {M N : Type'} (s : type30 M) (t : type30 N) : (term157 M N s t) = (term157 M N s t).
Proof. exact (MK_COMB (@lem8035919 M s) (@lem8035909 M N s t)). Qed.
Lemma lem8035921 {M N : Type'} (t : type30 N) : (term159 M N t) = (term159 M N t).
Proof. exact (fun_ext (fun s : type30 M => @lem8035920 M N s t)). Qed.
Lemma lem8035922 {M : Type'} : (@all ((cart real M) -> Prop)) = (@all ((cart real M) -> Prop)).
Proof. exact (eq_refl (@all ((cart real M) -> Prop))). Qed.
Lemma lem8035923 {M N : Type'} (t : type30 N) : (term161 M N t) = (term161 M N t).
Proof. exact (MK_COMB (@lem8035922 M) (@lem8035921 M N t)). Qed.
Lemma lem8035924 {M N : Type'} : (term163 M N) = (term163 M N).
Proof. exact (fun_ext (fun t : type30 N => @lem8035923 M N t)). Qed.
Lemma lem8035925 {N : Type'} : (@all ((cart real N) -> Prop)) = (@all ((cart real N) -> Prop)).
Proof. exact (eq_refl (@all ((cart real N) -> Prop))). Qed.
Lemma lem8035926 {M N : Type'} : (term165 M N) = (term165 M N).
Proof. exact (MK_COMB (@lem8035925 N) (@lem8035924 M N)). Qed.
Lemma lem8035971 {M N : Type'} : (term164 M N) = (term165 M N).
Proof. exact (TRANS (@lem8035887 M N) (@lem8035926 M N)). Qed.
Lemma lem8035972 {M N : Type'} : (term165 M N) = (term164 M N).
Proof. exact (SYM (@lem8035971 M N)). Qed.
Lemma lem8035973 {M : Type'} (s : type30 M) (h1 : term110 M s) : term110 M s.
Proof. exact (h1). Qed.
Lemma lem8035975 (p : Prop) : p = (term123 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8035976 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : ((term153 M N s t x) = (t x)) = (term169 M N s t x).
Proof. exact (@lem8035975 ((term153 M N s t x) = (t x))). Qed.
Lemma lem8035977 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term169 M N s t x) = ((term153 M N s t x) = (t x)).
Proof. exact (SYM (@lem8035976 M N s t x)). Qed.
Lemma lem8035978 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) (h1 : term170 M N s t x) : term170 M N s t x.
Proof. exact (h1). Qed.
Lemma lem8035981 {M : Type'} (s : type30 M) (x : cart real M) : (term171 M s x) = (s x).
Proof. exact (@lem16933 (s x)). Qed.
Lemma lem8035982 {M : Type'} (P : type30 M) : (term172 M P) = (term173 M P).
Proof. exact (@lem18392 (cart real M) P). Qed.
Lemma lem8035983 {M : Type'} (s : type30 M) : (term110 M s) = (term174 M s).
Proof. exact (@lem8035982 M (term108 M s)). Qed.
Lemma lem8035984 {M : Type'} (s : type30 M) (x : cart real M) : (term175 M s x) = (term106 M s x).
Proof. exact (eq_refl (term175 M s x)). Qed.
Lemma lem8035985 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8035986 {M : Type'} (s : type30 M) (x : cart real M) : (term176 M s x) = (term171 M s x).
Proof. exact (MK_COMB (@lem8035985) (@lem8035984 M s x)). Qed.
Lemma lem8035987 {M : Type'} (s : type30 M) (x : cart real M) : (term176 M s x) = (s x).
Proof. exact (TRANS (@lem8035986 M s x) (@lem8035981 M s x)). Qed.
Lemma lem8035988 {M : Type'} (s : type30 M) : (term177 M s) = (term166 M s).
Proof. exact (fun_ext (fun x : cart real M => @lem8035987 M s x)). Qed.
Lemma lem8035989 {M : Type'} : (@ex (cart real M)) = (@ex (cart real M)).
Proof. exact (eq_refl (@ex (cart real M))). Qed.
Lemma lem8035990 {M : Type'} (s : type30 M) : (term174 M s) = (term167 M s).
Proof. exact (MK_COMB (@lem8035989 M) (@lem8035988 M s)). Qed.
Lemma lem8035999 {M : Type'} (s : type30 M) : (term110 M s) = (term167 M s).
Proof. exact (TRANS (@lem8035983 M s) (@lem8035990 M s)). Qed.
Lemma lem8036000 {M : Type'} (s : type30 M) (h1 : term110 M s) : term167 M s.
Proof. exact (EQ_MP (@lem8035999 M s) (@lem8035973 M s h1)). Qed.
Lemma lem8036002 {M : Type'} (s : type30 M) (x : cart real M) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem8036003 {M : Type'} (P : type30 M) : (term178 M P) = (term109 M P).
Proof. exact (@lem18394 (cart real M) P). Qed.
Lemma lem8036004 {M : Type'} (s : type30 M) : (term179 M s) = (term180 M s).
Proof. exact (@lem8036003 M (term166 M s)). Qed.
Lemma lem8036005 {M : Type'} (s : type30 M) (x : cart real M) : (term181 M s x) = (s x).
Proof. exact (eq_refl (term181 M s x)). Qed.
Lemma lem8036006 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8036008 {M : Type'} (s : type30 M) (x : cart real M) : (term182 M s x) = (term106 M s x).
Proof. exact (MK_COMB (@lem8036006) (@lem8036005 M s x)). Qed.
Lemma lem8036009 {M : Type'} (s : type30 M) : (term183 M s) = (term108 M s).
Proof. exact (fun_ext (fun x : cart real M => @lem8036008 M s x)). Qed.
Lemma lem8036010 {M : Type'} : (@all (cart real M)) = (@all (cart real M)).
Proof. exact (eq_refl (@all (cart real M))). Qed.
Lemma lem8036011 {M : Type'} (s : type30 M) : (term180 M s) = (term109 M s).
Proof. exact (MK_COMB (@lem8036010 M) (@lem8036009 M s)). Qed.
Lemma lem8036012 {M : Type'} (s : type30 M) : (term179 M s) = (term109 M s).
Proof. exact (TRANS (@lem8036004 M s) (@lem8036011 M s)). Qed.
Lemma lem8036013 {M : Type'} (s : type30 M) : (term166 M s) = (term166 M s).
Proof. exact (fun_ext (fun x : cart real M => @lem8036002 M s x)). Qed.
Lemma lem8036014 {M : Type'} : (@ex (cart real M)) = (@ex (cart real M)).
Proof. exact (eq_refl (@ex (cart real M))). Qed.
Lemma lem8036015 {M : Type'} (s : type30 M) : (term167 M s) = (term167 M s).
Proof. exact (MK_COMB (@lem8036014 M) (@lem8036013 M s)). Qed.
Lemma lem8036024 {N : Type'} (t : type30 N) (x : cart real N) (y : cart real N) : (term184 N t x y) = (term185 N t x y).
Proof. exact (@lem17045 (t y) (x = y)). Qed.
Lemma lem8036027 {N : Type'} (t : type30 N) (x : cart real N) (y : cart real N) : (term113 N t x y) = (term113 N t x y).
Proof. exact (eq_refl (term113 N t x y)). Qed.
Lemma lem8036028 {N : Type'} (P : type30 N) : (term178 N P) = (term109 N P).
Proof. exact (@lem18394 (cart real N) P). Qed.
Lemma lem8036029 {N : Type'} (t : type30 N) (x : cart real N) : (term186 N t x) = (term187 N t x).
Proof. exact (@lem8036028 N (term137 N t x)). Qed.
Lemma lem8036030 {N : Type'} (t : type30 N) (x : cart real N) (y : cart real N) : (term138 N t x y) = (term113 N t x y).
Proof. exact (eq_refl (term138 N t x y)). Qed.
Lemma lem8036031 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8036032 {N : Type'} (t : type30 N) (x : cart real N) (y : cart real N) : (term188 N t x y) = (term184 N t x y).
Proof. exact (MK_COMB (@lem8036031) (@lem8036030 N t x y)). Qed.
Lemma lem8036033 {N : Type'} (t : type30 N) (x : cart real N) (y : cart real N) : (term188 N t x y) = (term185 N t x y).
Proof. exact (TRANS (@lem8036032 N t x y) (@lem8036024 N t x y)). Qed.
Lemma lem8036034 {N : Type'} (t : type30 N) (x : cart real N) : (term189 N t x) = (term190 N t x).
Proof. exact (fun_ext (fun y : cart real N => @lem8036033 N t x y)). Qed.
Lemma lem8036035 {N : Type'} : (@all (cart real N)) = (@all (cart real N)).
Proof. exact (eq_refl (@all (cart real N))). Qed.
Lemma lem8036036 {N : Type'} (t : type30 N) (x : cart real N) : (term187 N t x) = (term191 N t x).
Proof. exact (MK_COMB (@lem8036035 N) (@lem8036034 N t x)). Qed.
Lemma lem8036037 {N : Type'} (t : type30 N) (x : cart real N) : (term186 N t x) = (term191 N t x).
Proof. exact (TRANS (@lem8036029 N t x) (@lem8036036 N t x)). Qed.
Lemma lem8036038 {N : Type'} (t : type30 N) (x : cart real N) : (term137 N t x) = (term137 N t x).
Proof. exact (fun_ext (fun y : cart real N => @lem8036027 N t x y)). Qed.
Lemma lem8036039 {N : Type'} : (@ex (cart real N)) = (@ex (cart real N)).
Proof. exact (eq_refl (@ex (cart real N))). Qed.
Lemma lem8036040 {N : Type'} (t : type30 N) (x : cart real N) : (term145 N t x) = (term145 N t x).
Proof. exact (MK_COMB (@lem8036039 N) (@lem8036038 N t x)). Qed.
Lemma lem8036041 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8036042 {M : Type'} (s : type30 M) : (term192 M s) = (term193 M s).
Proof. exact (MK_COMB (@lem8036041) (@lem8036012 M s)). Qed.
Lemma lem8036043 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term194 M N s t x) = (term195 M N s t x).
Proof. exact (MK_COMB (@lem8036042 M s) (@lem8036037 N t x)). Qed.
Lemma lem8036044 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term196 M N s t x) = (term194 M N s t x).
Proof. exact (@lem17045 (term167 M s) (term145 N t x)). Qed.
Lemma lem8036045 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term196 M N s t x) = (term195 M N s t x).
Proof. exact (TRANS (@lem8036044 M N s t x) (@lem8036043 M N s t x)). Qed.
Lemma lem8036046 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8036047 {M : Type'} (s : type30 M) : (term168 M s) = (term168 M s).
Proof. exact (MK_COMB (@lem8036046) (@lem8036015 M s)). Qed.
Lemma lem8036048 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term153 M N s t x) = (term153 M N s t x).
Proof. exact (MK_COMB (@lem8036047 M s) (@lem8036040 N t x)). Qed.
Lemma lem8036049 {N : Type'} (t : type30 N) (x : cart real N) : (term106 N t x) = (term106 N t x).
Proof. exact (eq_refl (term106 N t x)). Qed.
Lemma lem8036050 {N : Type'} (t : type30 N) (x : cart real N) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem8036051 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8036052 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term197 M N s t x) = (term198 M N s t x).
Proof. exact (MK_COMB (@lem8036051) (@lem8036045 M N s t x)). Qed.
Lemma lem8036053 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term199 M N s t x) = (term200 M N s t x).
Proof. exact (MK_COMB (@lem8036052 M N s t x) (@lem8036050 N t x)). Qed.
Lemma lem8036054 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8036055 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term201 M N s t x) = (term201 M N s t x).
Proof. exact (MK_COMB (@lem8036054) (@lem8036048 M N s t x)). Qed.
Lemma lem8036056 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term202 M N s t x) = (term202 M N s t x).
Proof. exact (MK_COMB (@lem8036055 M N s t x) (@lem8036049 N t x)). Qed.
Lemma lem8036057 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8036058 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term203 M N s t x) = (term203 M N s t x).
Proof. exact (MK_COMB (@lem8036057) (@lem8036056 M N s t x)). Qed.
Lemma lem8036059 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term204 M N s t x) = (term205 M N s t x).
Proof. exact (MK_COMB (@lem8036058 M N s t x) (@lem8036053 M N s t x)). Qed.
Lemma lem8036060 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term170 M N s t x) = (term204 M N s t x).
Proof. exact (@lem17646 (term153 M N s t x) (t x)). Qed.
Lemma lem8036061 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term170 M N s t x) = (term205 M N s t x).
Proof. exact (TRANS (@lem8036060 M N s t x) (@lem8036059 M N s t x)). Qed.
Lemma lem8036148 {A : Type'} (P : A -> Prop) (Q : Prop) : (term150 A P Q) = (term149 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem8036149 {M : Type'} (P : type30 M) (Q : Prop) : (term152 M P Q) = (term151 M P Q).
Proof. exact (@lem8036148 (cart real M) P Q). Qed.
Lemma lem8036150 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term153 M N s t x) = (term148 M N s t x).
Proof. exact (@lem8036149 M s (term145 N t x)). Qed.
Lemma lem8036152 {A : Type'} (P : Prop) (Q : A -> Prop) : (term132 A P Q) = (term131 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem8036153 {N : Type'} (P : Prop) (Q : type30 N) : (term134 N P Q) = (term133 N P Q).
Proof. exact (@lem8036152 (cart real N) P Q). Qed.
Lemma lem8036154 {M N : Type'} (s : type30 M) (x : cart real M) (t : type30 N) (x' : cart real N) : (term136 M N s x t x') = (term135 M N s x t x').
Proof. exact (@lem8036153 N (s x) (term137 N t x')). Qed.
Lemma lem8036155 {N : Type'} (t : type30 N) (x : cart real N) (y : cart real N) : (term138 N t x y) = (term113 N t x y).
Proof. exact (eq_refl (term138 N t x y)). Qed.
Lemma lem8036156 {N : Type'} (t : type30 N) (x : cart real N) : (term143 N t x) = (term137 N t x).
Proof. exact (fun_ext (fun y : cart real N => @lem8036155 N t x y)). Qed.
Lemma lem8036157 {N : Type'} : (@ex (cart real N)) = (@ex (cart real N)).
Proof. exact (eq_refl (@ex (cart real N))). Qed.
Lemma lem8036158 {N : Type'} (t : type30 N) (x : cart real N) : (term144 N t x) = (term145 N t x).
Proof. exact (MK_COMB (@lem8036157 N) (@lem8036156 N t x)). Qed.
Lemma lem8036159 {M : Type'} (s : type30 M) (x : cart real M) : (term112 M s x) = (term112 M s x).
Proof. exact (eq_refl (term112 M s x)). Qed.
Lemma lem8036160 {M N : Type'} (s : type30 M) (x : cart real M) (t : type30 N) (x' : cart real N) : (term136 M N s x t x') = (term146 M N s x t x').
Proof. exact (MK_COMB (@lem8036159 M s x) (@lem8036158 N t x')). Qed.
Lemma lem8036161 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8036162 {M N : Type'} (s : type30 M) (x : cart real M) (t : type30 N) (x' : cart real N) : (term206 M N s x t x') = (term207 M N s x t x').
Proof. exact (MK_COMB (@lem8036161) (@lem8036160 M N s x t x')). Qed.
Lemma lem8036163 {N : Type'} (t : type30 N) (x : cart real N) (y : cart real N) : (term138 N t x y) = (term113 N t x y).
Proof. exact (eq_refl (term138 N t x y)). Qed.
Lemma lem8036164 {M : Type'} (s : type30 M) (x : cart real M) : (term112 M s x) = (term112 M s x).
Proof. exact (eq_refl (term112 M s x)). Qed.
Lemma lem8036165 {M N : Type'} (s : type30 M) (x : cart real M) (t : type30 N) (x' : cart real N) (y : cart real N) : (term139 M N s x t x' y) = (term114 M N s x t x' y).
Proof. exact (MK_COMB (@lem8036164 M s x) (@lem8036163 N t x' y)). Qed.
Lemma lem8036166 {M N : Type'} (s : type30 M) (x : cart real M) (t : type30 N) (x' : cart real N) : (term140 M N s x t x') = (term115 M N s x t x').
Proof. exact (fun_ext (fun y : cart real N => @lem8036165 M N s x t x' y)). Qed.
Lemma lem8036167 {N : Type'} : (@ex (cart real N)) = (@ex (cart real N)).
Proof. exact (eq_refl (@ex (cart real N))). Qed.
Lemma lem8036168 {M N : Type'} (s : type30 M) (x : cart real M) (t : type30 N) (x' : cart real N) : (term135 M N s x t x') = (term116 M N s x t x').
Proof. exact (MK_COMB (@lem8036167 N) (@lem8036166 M N s x t x')). Qed.
Lemma lem8036169 {M N : Type'} (s : type30 M) (x : cart real M) (t : type30 N) (x' : cart real N) : ((term136 M N s x t x') = (term135 M N s x t x')) = ((term146 M N s x t x') = (term116 M N s x t x')).
Proof. exact (MK_COMB (@lem8036162 M N s x t x') (@lem8036168 M N s x t x')). Qed.
Lemma lem8036170 {M N : Type'} (s : type30 M) (x : cart real M) (t : type30 N) (x' : cart real N) : (term146 M N s x t x') = (term116 M N s x t x').
Proof. exact (EQ_MP (@lem8036169 M N s x t x') (@lem8036154 M N s x t x')). Qed.
Lemma lem8036171 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term147 M N s t x) = (term117 M N s t x).
Proof. exact (fun_ext (fun x' : cart real M => @lem8036170 M N s x' t x)). Qed.
Lemma lem8036172 {M : Type'} : (@ex (cart real M)) = (@ex (cart real M)).
Proof. exact (eq_refl (@ex (cart real M))). Qed.
Lemma lem8036173 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term148 M N s t x) = (term118 M N s t x).
Proof. exact (MK_COMB (@lem8036172 M) (@lem8036171 M N s t x)). Qed.
Lemma lem8036174 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term153 M N s t x) = (term118 M N s t x).
Proof. exact (TRANS (@lem8036150 M N s t x) (@lem8036173 M N s t x)). Qed.
Lemma lem8036175 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8036176 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term201 M N s t x) = (term208 M N s t x).
Proof. exact (MK_COMB (@lem8036175) (@lem8036174 M N s t x)). Qed.
Lemma lem8036177 {N : Type'} (t : type30 N) (x : cart real N) : (term106 N t x) = (term106 N t x).
Proof. exact (eq_refl (term106 N t x)). Qed.
Lemma lem8036178 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term202 M N s t x) = (term209 M N s t x).
Proof. exact (MK_COMB (@lem8036176 M N s t x) (@lem8036177 N t x)). Qed.
Lemma lem8036180 {A : Type'} (P : A -> Prop) (Q : Prop) : (term150 A P Q) = (term149 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem8036181 {M : Type'} (P : type30 M) (Q : Prop) : (term152 M P Q) = (term151 M P Q).
Proof. exact (@lem8036180 (cart real M) P Q). Qed.
Lemma lem8036182 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term210 M N s t x) = (term211 M N s t x).
Proof. exact (@lem8036181 M (term117 M N s t x) (term106 N t x)). Qed.
Lemma lem8036183 {M N : Type'} (s : type30 M) (x : cart real M) (t : type30 N) (x' : cart real N) : (term212 M N s t x' x) = (term116 M N s x t x').
Proof. exact (eq_refl (term212 M N s t x' x)). Qed.
Lemma lem8036184 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term213 M N s t x) = (term117 M N s t x).
Proof. exact (fun_ext (fun x' : cart real M => @lem8036183 M N s x' t x)). Qed.
Lemma lem8036185 {M : Type'} : (@ex (cart real M)) = (@ex (cart real M)).
Proof. exact (eq_refl (@ex (cart real M))). Qed.
Lemma lem8036186 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term214 M N s t x) = (term118 M N s t x).
Proof. exact (MK_COMB (@lem8036185 M) (@lem8036184 M N s t x)). Qed.
Lemma lem8036187 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8036188 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term215 M N s t x) = (term208 M N s t x).
Proof. exact (MK_COMB (@lem8036187) (@lem8036186 M N s t x)). Qed.
Lemma lem8036189 {N : Type'} (t : type30 N) (x : cart real N) : (term106 N t x) = (term106 N t x).
Proof. exact (eq_refl (term106 N t x)). Qed.
Lemma lem8036190 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term210 M N s t x) = (term209 M N s t x).
Proof. exact (MK_COMB (@lem8036188 M N s t x) (@lem8036189 N t x)). Qed.
Lemma lem8036191 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8036192 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term216 M N s t x) = (term217 M N s t x).
Proof. exact (MK_COMB (@lem8036191) (@lem8036190 M N s t x)). Qed.
Lemma lem8036193 {M N : Type'} (s : type30 M) (x : cart real M) (t : type30 N) (x' : cart real N) : (term212 M N s t x' x) = (term116 M N s x t x').
Proof. exact (eq_refl (term212 M N s t x' x)). Qed.
Lemma lem8036194 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8036195 {M N : Type'} (s : type30 M) (x : cart real M) (t : type30 N) (x' : cart real N) : (term218 M N s t x' x) = (term219 M N s x t x').
Proof. exact (MK_COMB (@lem8036194) (@lem8036193 M N s x t x')). Qed.
Lemma lem8036196 {N : Type'} (t : type30 N) (x : cart real N) : (term106 N t x) = (term106 N t x).
Proof. exact (eq_refl (term106 N t x)). Qed.
Lemma lem8036197 {M N : Type'} (s : type30 M) (x : cart real M) (t : type30 N) (x' : cart real N) : (term220 M N s x t x') = (term221 M N s x t x').
Proof. exact (MK_COMB (@lem8036195 M N s x t x') (@lem8036196 N t x')). Qed.
Lemma lem8036198 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term222 M N s t x) = (term223 M N s t x).
Proof. exact (fun_ext (fun x' : cart real M => @lem8036197 M N s x' t x)). Qed.
Lemma lem8036199 {M : Type'} : (@ex (cart real M)) = (@ex (cart real M)).
Proof. exact (eq_refl (@ex (cart real M))). Qed.
Lemma lem8036200 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term211 M N s t x) = (term224 M N s t x).
Proof. exact (MK_COMB (@lem8036199 M) (@lem8036198 M N s t x)). Qed.
Lemma lem8036201 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : ((term210 M N s t x) = (term211 M N s t x)) = ((term209 M N s t x) = (term224 M N s t x)).
Proof. exact (MK_COMB (@lem8036192 M N s t x) (@lem8036200 M N s t x)). Qed.
Lemma lem8036202 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term209 M N s t x) = (term224 M N s t x).
Proof. exact (EQ_MP (@lem8036201 M N s t x) (@lem8036182 M N s t x)). Qed.
Lemma lem8036204 {A : Type'} (P : A -> Prop) (Q : Prop) : (term150 A P Q) = (term149 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem8036205 {N : Type'} (P : type30 N) (Q : Prop) : (term152 N P Q) = (term151 N P Q).
Proof. exact (@lem8036204 (cart real N) P Q). Qed.
Lemma lem8036206 {M N : Type'} (s : type30 M) (x : cart real M) (t : type30 N) (x' : cart real N) : (term225 M N s x t x') = (term226 M N s x t x').
Proof. exact (@lem8036205 N (term115 M N s x t x') (term106 N t x')). Qed.
Lemma lem8036207 {M N : Type'} (s : type30 M) (x : cart real M) (t : type30 N) (x' : cart real N) (y : cart real N) : (term227 M N s x t x' y) = (term114 M N s x t x' y).
Proof. exact (eq_refl (term227 M N s x t x' y)). Qed.
Lemma lem8036208 {M N : Type'} (s : type30 M) (x : cart real M) (t : type30 N) (x' : cart real N) : (term228 M N s x t x') = (term115 M N s x t x').
Proof. exact (fun_ext (fun y : cart real N => @lem8036207 M N s x t x' y)). Qed.
Lemma lem8036209 {N : Type'} : (@ex (cart real N)) = (@ex (cart real N)).
Proof. exact (eq_refl (@ex (cart real N))). Qed.
Lemma lem8036210 {M N : Type'} (s : type30 M) (x : cart real M) (t : type30 N) (x' : cart real N) : (term229 M N s x t x') = (term116 M N s x t x').
Proof. exact (MK_COMB (@lem8036209 N) (@lem8036208 M N s x t x')). Qed.
Lemma lem8036211 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8036212 {M N : Type'} (s : type30 M) (x : cart real M) (t : type30 N) (x' : cart real N) : (term230 M N s x t x') = (term219 M N s x t x').
Proof. exact (MK_COMB (@lem8036211) (@lem8036210 M N s x t x')). Qed.
Lemma lem8036213 {N : Type'} (t : type30 N) (x : cart real N) : (term106 N t x) = (term106 N t x).
Proof. exact (eq_refl (term106 N t x)). Qed.
Lemma lem8036214 {M N : Type'} (s : type30 M) (x : cart real M) (t : type30 N) (x' : cart real N) : (term225 M N s x t x') = (term221 M N s x t x').
Proof. exact (MK_COMB (@lem8036212 M N s x t x') (@lem8036213 N t x')). Qed.
Lemma lem8036215 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8036216 {M N : Type'} (s : type30 M) (x : cart real M) (t : type30 N) (x' : cart real N) : (term231 M N s x t x') = (term232 M N s x t x').
Proof. exact (MK_COMB (@lem8036215) (@lem8036214 M N s x t x')). Qed.
Lemma lem8036217 {M N : Type'} (s : type30 M) (x : cart real M) (t : type30 N) (x' : cart real N) (y : cart real N) : (term227 M N s x t x' y) = (term114 M N s x t x' y).
Proof. exact (eq_refl (term227 M N s x t x' y)). Qed.
Lemma lem8036218 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8036219 {M N : Type'} (s : type30 M) (x : cart real M) (t : type30 N) (x' : cart real N) (y : cart real N) : (term233 M N s x t x' y) = (term234 M N s x t x' y).
Proof. exact (MK_COMB (@lem8036218) (@lem8036217 M N s x t x' y)). Qed.
Lemma lem8036220 {N : Type'} (t : type30 N) (x : cart real N) : (term106 N t x) = (term106 N t x).
Proof. exact (eq_refl (term106 N t x)). Qed.
Lemma lem8036221 {M N : Type'} (s : type30 M) (x : cart real M) (y : cart real N) (t : type30 N) (x' : cart real N) : (term235 M N s x y t x') = (term236 M N s x y t x').
Proof. exact (MK_COMB (@lem8036219 M N s x t x' y) (@lem8036220 N t x')). Qed.
Lemma lem8036222 {M N : Type'} (s : type30 M) (x : cart real M) (t : type30 N) (x' : cart real N) : (term237 M N s x t x') = (term238 M N s x t x').
Proof. exact (fun_ext (fun y : cart real N => @lem8036221 M N s x y t x')). Qed.
Lemma lem8036223 {N : Type'} : (@ex (cart real N)) = (@ex (cart real N)).
Proof. exact (eq_refl (@ex (cart real N))). Qed.
Lemma lem8036224 {M N : Type'} (s : type30 M) (x : cart real M) (t : type30 N) (x' : cart real N) : (term226 M N s x t x') = (term239 M N s x t x').
Proof. exact (MK_COMB (@lem8036223 N) (@lem8036222 M N s x t x')). Qed.
Lemma lem8036225 {M N : Type'} (s : type30 M) (x : cart real M) (t : type30 N) (x' : cart real N) : ((term225 M N s x t x') = (term226 M N s x t x')) = ((term221 M N s x t x') = (term239 M N s x t x')).
Proof. exact (MK_COMB (@lem8036216 M N s x t x') (@lem8036224 M N s x t x')). Qed.
Lemma lem8036226 {M N : Type'} (s : type30 M) (x : cart real M) (t : type30 N) (x' : cart real N) : (term221 M N s x t x') = (term239 M N s x t x').
Proof. exact (EQ_MP (@lem8036225 M N s x t x') (@lem8036206 M N s x t x')). Qed.
Lemma lem8036227 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term223 M N s t x) = (term240 M N s t x).
Proof. exact (fun_ext (fun x' : cart real M => @lem8036226 M N s x' t x)). Qed.
Lemma lem8036228 {M : Type'} : (@ex (cart real M)) = (@ex (cart real M)).
Proof. exact (eq_refl (@ex (cart real M))). Qed.
Lemma lem8036229 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term224 M N s t x) = (term241 M N s t x).
Proof. exact (MK_COMB (@lem8036228 M) (@lem8036227 M N s t x)). Qed.
Lemma lem8036230 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term209 M N s t x) = (term241 M N s t x).
Proof. exact (TRANS (@lem8036202 M N s t x) (@lem8036229 M N s t x)). Qed.
Lemma lem8036231 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term202 M N s t x) = (term241 M N s t x).
Proof. exact (TRANS (@lem8036178 M N s t x) (@lem8036230 M N s t x)). Qed.
Lemma lem8036232 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8036233 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term203 M N s t x) = (term242 M N s t x).
Proof. exact (MK_COMB (@lem8036232) (@lem8036231 M N s t x)). Qed.
Lemma lem8036234 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term200 M N s t x) = (term200 M N s t x).
Proof. exact (eq_refl (term200 M N s t x)). Qed.
Lemma lem8036235 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term205 M N s t x) = (term243 M N s t x).
Proof. exact (MK_COMB (@lem8036233 M N s t x) (@lem8036234 M N s t x)). Qed.
Lemma lem8036237 {A : Type'} (P : A -> Prop) (Q : Prop) : (term244 A P Q) = (term245 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem8036238 {M : Type'} (P : type30 M) (Q : Prop) : (term246 M P Q) = (term247 M P Q).
Proof. exact (@lem8036237 (cart real M) P Q). Qed.
Lemma lem8036239 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term248 M N s t x) = (term249 M N s t x).
Proof. exact (@lem8036238 M (term240 M N s t x) (term200 M N s t x)). Qed.
Lemma lem8036240 {M N : Type'} (s : type30 M) (x : cart real M) (t : type30 N) (x' : cart real N) : (term250 M N s t x' x) = (term239 M N s x t x').
Proof. exact (eq_refl (term250 M N s t x' x)). Qed.
Lemma lem8036241 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term251 M N s t x) = (term240 M N s t x).
Proof. exact (fun_ext (fun x' : cart real M => @lem8036240 M N s x' t x)). Qed.
Lemma lem8036242 {M : Type'} : (@ex (cart real M)) = (@ex (cart real M)).
Proof. exact (eq_refl (@ex (cart real M))). Qed.
Lemma lem8036243 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term252 M N s t x) = (term241 M N s t x).
Proof. exact (MK_COMB (@lem8036242 M) (@lem8036241 M N s t x)). Qed.
Lemma lem8036244 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8036245 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term253 M N s t x) = (term242 M N s t x).
Proof. exact (MK_COMB (@lem8036244) (@lem8036243 M N s t x)). Qed.
Lemma lem8036246 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term200 M N s t x) = (term200 M N s t x).
Proof. exact (eq_refl (term200 M N s t x)). Qed.
Lemma lem8036247 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term248 M N s t x) = (term243 M N s t x).
Proof. exact (MK_COMB (@lem8036245 M N s t x) (@lem8036246 M N s t x)). Qed.
Lemma lem8036248 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8036249 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term254 M N s t x) = (term255 M N s t x).
Proof. exact (MK_COMB (@lem8036248) (@lem8036247 M N s t x)). Qed.
Lemma lem8036250 {M N : Type'} (s : type30 M) (x : cart real M) (t : type30 N) (x' : cart real N) : (term250 M N s t x' x) = (term239 M N s x t x').
Proof. exact (eq_refl (term250 M N s t x' x)). Qed.
Lemma lem8036251 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8036252 {M N : Type'} (s : type30 M) (x : cart real M) (t : type30 N) (x' : cart real N) : (term256 M N s t x' x) = (term257 M N s x t x').
Proof. exact (MK_COMB (@lem8036251) (@lem8036250 M N s x t x')). Qed.
Lemma lem8036253 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term200 M N s t x) = (term200 M N s t x).
Proof. exact (eq_refl (term200 M N s t x)). Qed.
Lemma lem8036254 {M N : Type'} (x : cart real M) (s : type30 M) (t : type30 N) (x' : cart real N) : (term258 M N x s t x') = (term259 M N x s t x').
Proof. exact (MK_COMB (@lem8036252 M N s x t x') (@lem8036253 M N s t x')). Qed.
Lemma lem8036255 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term260 M N s t x) = (term261 M N s t x).
Proof. exact (fun_ext (fun x' : cart real M => @lem8036254 M N x' s t x)). Qed.
Lemma lem8036256 {M : Type'} : (@ex (cart real M)) = (@ex (cart real M)).
Proof. exact (eq_refl (@ex (cart real M))). Qed.
Lemma lem8036257 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term249 M N s t x) = (term262 M N s t x).
Proof. exact (MK_COMB (@lem8036256 M) (@lem8036255 M N s t x)). Qed.
Lemma lem8036258 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : ((term248 M N s t x) = (term249 M N s t x)) = ((term243 M N s t x) = (term262 M N s t x)).
Proof. exact (MK_COMB (@lem8036249 M N s t x) (@lem8036257 M N s t x)). Qed.
Lemma lem8036259 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term243 M N s t x) = (term262 M N s t x).
Proof. exact (EQ_MP (@lem8036258 M N s t x) (@lem8036239 M N s t x)). Qed.
Lemma lem8036261 {A : Type'} (P : A -> Prop) (Q : Prop) : (term244 A P Q) = (term245 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem8036262 {N : Type'} (P : type30 N) (Q : Prop) : (term246 N P Q) = (term247 N P Q).
Proof. exact (@lem8036261 (cart real N) P Q). Qed.
Lemma lem8036263 {M N : Type'} (x : cart real M) (s : type30 M) (t : type30 N) (x' : cart real N) : (term263 M N x s t x') = (term264 M N x s t x').
Proof. exact (@lem8036262 N (term238 M N s x t x') (term200 M N s t x')). Qed.
Lemma lem8036264 {M N : Type'} (s : type30 M) (x : cart real M) (y : cart real N) (t : type30 N) (x' : cart real N) : (term265 M N s x t x' y) = (term236 M N s x y t x').
Proof. exact (eq_refl (term265 M N s x t x' y)). Qed.
Lemma lem8036265 {M N : Type'} (s : type30 M) (x : cart real M) (t : type30 N) (x' : cart real N) : (term266 M N s x t x') = (term238 M N s x t x').
Proof. exact (fun_ext (fun y : cart real N => @lem8036264 M N s x y t x')). Qed.
Lemma lem8036266 {N : Type'} : (@ex (cart real N)) = (@ex (cart real N)).
Proof. exact (eq_refl (@ex (cart real N))). Qed.
Lemma lem8036267 {M N : Type'} (s : type30 M) (x : cart real M) (t : type30 N) (x' : cart real N) : (term267 M N s x t x') = (term239 M N s x t x').
Proof. exact (MK_COMB (@lem8036266 N) (@lem8036265 M N s x t x')). Qed.
Lemma lem8036268 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8036269 {M N : Type'} (s : type30 M) (x : cart real M) (t : type30 N) (x' : cart real N) : (term268 M N s x t x') = (term257 M N s x t x').
Proof. exact (MK_COMB (@lem8036268) (@lem8036267 M N s x t x')). Qed.
Lemma lem8036270 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term200 M N s t x) = (term200 M N s t x).
Proof. exact (eq_refl (term200 M N s t x)). Qed.
Lemma lem8036271 {M N : Type'} (x : cart real M) (s : type30 M) (t : type30 N) (x' : cart real N) : (term263 M N x s t x') = (term259 M N x s t x').
Proof. exact (MK_COMB (@lem8036269 M N s x t x') (@lem8036270 M N s t x')). Qed.
Lemma lem8036272 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8036273 {M N : Type'} (x : cart real M) (s : type30 M) (t : type30 N) (x' : cart real N) : (term269 M N x s t x') = (term270 M N x s t x').
Proof. exact (MK_COMB (@lem8036272) (@lem8036271 M N x s t x')). Qed.
Lemma lem8036274 {M N : Type'} (s : type30 M) (x : cart real M) (y : cart real N) (t : type30 N) (x' : cart real N) : (term265 M N s x t x' y) = (term236 M N s x y t x').
Proof. exact (eq_refl (term265 M N s x t x' y)). Qed.
Lemma lem8036275 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8036276 {M N : Type'} (s : type30 M) (x : cart real M) (y : cart real N) (t : type30 N) (x' : cart real N) : (term271 M N s x t x' y) = (term272 M N s x y t x').
Proof. exact (MK_COMB (@lem8036275) (@lem8036274 M N s x y t x')). Qed.
Lemma lem8036277 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term200 M N s t x) = (term200 M N s t x).
Proof. exact (eq_refl (term200 M N s t x)). Qed.
Lemma lem8036278 {M N : Type'} (x : cart real M) (y : cart real N) (s : type30 M) (t : type30 N) (x' : cart real N) : (term273 M N x y s t x') = (term274 M N x y s t x').
Proof. exact (MK_COMB (@lem8036276 M N s x y t x') (@lem8036277 M N s t x')). Qed.
Lemma lem8036279 {M N : Type'} (x : cart real M) (s : type30 M) (t : type30 N) (x' : cart real N) : (term275 M N x s t x') = (term276 M N x s t x').
Proof. exact (fun_ext (fun y : cart real N => @lem8036278 M N x y s t x')). Qed.
Lemma lem8036280 {N : Type'} : (@ex (cart real N)) = (@ex (cart real N)).
Proof. exact (eq_refl (@ex (cart real N))). Qed.
Lemma lem8036281 {M N : Type'} (x : cart real M) (s : type30 M) (t : type30 N) (x' : cart real N) : (term264 M N x s t x') = (term277 M N x s t x').
Proof. exact (MK_COMB (@lem8036280 N) (@lem8036279 M N x s t x')). Qed.
Lemma lem8036282 {M N : Type'} (x : cart real M) (s : type30 M) (t : type30 N) (x' : cart real N) : ((term263 M N x s t x') = (term264 M N x s t x')) = ((term259 M N x s t x') = (term277 M N x s t x')).
Proof. exact (MK_COMB (@lem8036273 M N x s t x') (@lem8036281 M N x s t x')). Qed.
Lemma lem8036283 {M N : Type'} (x : cart real M) (s : type30 M) (t : type30 N) (x' : cart real N) : (term259 M N x s t x') = (term277 M N x s t x').
Proof. exact (EQ_MP (@lem8036282 M N x s t x') (@lem8036263 M N x s t x')). Qed.
Lemma lem8036284 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term261 M N s t x) = (term278 M N s t x).
Proof. exact (fun_ext (fun x' : cart real M => @lem8036283 M N x' s t x)). Qed.
Lemma lem8036285 {M : Type'} : (@ex (cart real M)) = (@ex (cart real M)).
Proof. exact (eq_refl (@ex (cart real M))). Qed.
Lemma lem8036286 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term262 M N s t x) = (term279 M N s t x).
Proof. exact (MK_COMB (@lem8036285 M) (@lem8036284 M N s t x)). Qed.
Lemma lem8036287 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term243 M N s t x) = (term279 M N s t x).
Proof. exact (TRANS (@lem8036259 M N s t x) (@lem8036286 M N s t x)). Qed.
Lemma lem8036289 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term205 M N s t x) = (term279 M N s t x).
Proof. exact (TRANS (@lem8036235 M N s t x) (@lem8036287 M N s t x)). Qed.
Lemma lem8036290 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term170 M N s t x) = (term279 M N s t x).
Proof. exact (TRANS (@lem8036061 M N s t x) (@lem8036289 M N s t x)). Qed.
Lemma lem8036291 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) (h1 : term170 M N s t x) : term279 M N s t x.
Proof. exact (EQ_MP (@lem8036290 M N s t x) (@lem8035978 M N s t x h1)). Qed.
Lemma lem8036292 {M N : Type'} (x' : cart real M) (s : type30 M) (t : type30 N) (x : cart real N) (h1 : term277 M N x' s t x) : term277 M N x' s t x.
Proof. exact (h1). Qed.
Lemma lem8036293 {M N : Type'} (x' : cart real M) (y : cart real N) (s : type30 M) (t : type30 N) (x : cart real N) (h1 : term274 M N x' y s t x) : term274 M N x' y s t x.
Proof. exact (h1). Qed.
Lemma lem8036297 {N : Type'} (t : type30 N) (x : cart real N) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem8036312 {N : Type'} (t : type30 N) (x : cart real N) (y : cart real N) : (term185 N t x y) = (term185 N t x y).
Proof. exact (eq_refl (term185 N t x y)). Qed.
Lemma lem8036313 {N : Type'} (t : type30 N) (x : cart real N) : (term190 N t x) = (term190 N t x).
Proof. exact (fun_ext (fun y : cart real N => @lem8036312 N t x y)). Qed.
Lemma lem8036314 {N : Type'} : (@all (cart real N)) = (@all (cart real N)).
Proof. exact (eq_refl (@all (cart real N))). Qed.
Lemma lem8036315 {N : Type'} (t : type30 N) (x : cart real N) : (term191 N t x) = (term191 N t x).
Proof. exact (MK_COMB (@lem8036314 N) (@lem8036313 N t x)). Qed.
Lemma lem8036320 {M : Type'} (s : type30 M) (x : cart real M) : (term106 M s x) = (term106 M s x).
Proof. exact (eq_refl (term106 M s x)). Qed.
Lemma lem8036321 {M : Type'} (s : type30 M) : (term108 M s) = (term108 M s).
Proof. exact (fun_ext (fun x : cart real M => @lem8036320 M s x)). Qed.
Lemma lem8036322 {M : Type'} : (@all (cart real M)) = (@all (cart real M)).
Proof. exact (eq_refl (@all (cart real M))). Qed.
Lemma lem8036323 {M : Type'} (s : type30 M) : (term109 M s) = (term109 M s).
Proof. exact (MK_COMB (@lem8036322 M) (@lem8036321 M s)). Qed.
Lemma lem8036324 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8036325 {M : Type'} (s : type30 M) : (term193 M s) = (term193 M s).
Proof. exact (MK_COMB (@lem8036324) (@lem8036323 M s)). Qed.
Lemma lem8036326 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term195 M N s t x) = (term195 M N s t x).
Proof. exact (MK_COMB (@lem8036325 M s) (@lem8036315 N t x)). Qed.
Lemma lem8036327 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8036328 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term198 M N s t x) = (term198 M N s t x).
Proof. exact (MK_COMB (@lem8036327) (@lem8036326 M N s t x)). Qed.
Lemma lem8036329 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) : (term200 M N s t x) = (term200 M N s t x).
Proof. exact (MK_COMB (@lem8036328 M N s t x) (@lem8036297 N t x)). Qed.
Lemma lem8036356 {M N : Type'} (s : type30 M) (x' : cart real M) (y : cart real N) (t : type30 N) (x : cart real N) : (term272 M N s x' y t x) = (term272 M N s x' y t x).
Proof. exact (eq_refl (term272 M N s x' y t x)). Qed.
Lemma lem8036357 {M N : Type'} (x' : cart real M) (y : cart real N) (s : type30 M) (t : type30 N) (x : cart real N) : (term274 M N x' y s t x) = (term274 M N x' y s t x).
Proof. exact (MK_COMB (@lem8036356 M N s x' y t x) (@lem8036329 M N s t x)). Qed.
Lemma lem8036358 {M N : Type'} (x' : cart real M) (y : cart real N) (s : type30 M) (t : type30 N) (x : cart real N) (h1 : term274 M N x' y s t x) : term274 M N x' y s t x.
Proof. exact (EQ_MP (@lem8036357 M N x' y s t x) (@lem8036293 M N x' y s t x h1)). Qed.
Lemma lem8036362 {M : Type'} (s : type30 M) (x'' : cart real M) (h1 : s x'') : s x''.
Proof. exact (h1). Qed.
Lemma lem8036363 {M N : Type'} (s : type30 M) (x' : cart real M) (y : cart real N) (t : type30 N) (x : cart real N) (h1 : term236 M N s x' y t x) : term236 M N s x' y t x.
Proof. exact (h1). Qed.
Lemma lem8036364 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) (h1 : term200 M N s t x) : term200 M N s t x.
Proof. exact (h1). Qed.
Lemma lem8036366 {M N : Type'} (s : type30 M) (x' : cart real M) (y : cart real N) (t : type30 N) (x : cart real N) (h1 : term236 M N s x' y t x) : term114 M N s x' t x y.
Proof. exact (proj1 (@lem8036363 M N s x' y t x h1)). Qed.
Lemma lem8036367 {M N : Type'} (s : type30 M) (x' : cart real M) (y : cart real N) (t : type30 N) (x : cart real N) (h1 : term236 M N s x' y t x) : term113 N t x y.
Proof. exact (proj2 (@lem8036366 M N s x' y t x h1)). Qed.
Lemma lem8036372 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) (h1 : term200 M N s t x) : term195 M N s t x.
Proof. exact (proj1 (@lem8036364 M N s t x h1)). Qed.
Lemma lem8036373 {M : Type'} (s : type30 M) (h1 : term109 M s) : term109 M s.
Proof. exact (h1). Qed.
Lemma lem8036374 {N : Type'} (t : type30 N) (x : cart real N) (h1 : term191 N t x) : term191 N t x.
Proof. exact (h1). Qed.
Lemma lem8036398 {M : Type'} (s : type30 M) (x'' : cart real M) (h1 : s x'') : s x''.
Proof. exact (h1). Qed.
Lemma lem8036404 {M : Type'} (s : type30 M) (x : cart real M) : (term106 M s x) = (term106 M s x).
Proof. exact (eq_refl (term106 M s x)). Qed.
Lemma lem8036405 {M : Type'} (s : type30 M) : (term108 M s) = (term108 M s).
Proof. exact (fun_ext (fun x : cart real M => @lem8036404 M s x)). Qed.
Lemma lem8036406 {M : Type'} : (@all (cart real M)) = (@all (cart real M)).
Proof. exact (eq_refl (@all (cart real M))). Qed.
Lemma lem8036408 {M : Type'} (s : type30 M) : (term109 M s) = (term109 M s).
Proof. exact (MK_COMB (@lem8036406 M) (@lem8036405 M s)). Qed.
Lemma lem8036409 {M : Type'} (s : type30 M) (h1 : term109 M s) : term109 M s.
Proof. exact (EQ_MP (@lem8036408 M s) (@lem8036373 M s h1)). Qed.
Lemma lem8036425 {N : Type'} (t : type30 N) (x : cart real N) (y : cart real N) : (term185 N t x y) = (term185 N t x y).
Proof. exact (eq_refl (term185 N t x y)). Qed.
Lemma lem8036426 {N : Type'} (t : type30 N) (x : cart real N) : (term190 N t x) = (term190 N t x).
Proof. exact (fun_ext (fun y : cart real N => @lem8036425 N t x y)). Qed.
Lemma lem8036427 {N : Type'} : (@all (cart real N)) = (@all (cart real N)).
Proof. exact (eq_refl (@all (cart real N))). Qed.
Lemma lem8036429 {N : Type'} (t : type30 N) (x : cart real N) : (term191 N t x) = (term191 N t x).
Proof. exact (MK_COMB (@lem8036427 N) (@lem8036426 N t x)). Qed.
Lemma lem8036430 {N : Type'} (t : type30 N) (x : cart real N) (h1 : term191 N t x) : term191 N t x.
Proof. exact (EQ_MP (@lem8036429 N t x) (@lem8036374 N t x h1)). Qed.
Lemma lem8036431 {M : Type'} (_106097 : cart real M) (s : type30 M) (h1 : term109 M s) : term175 M s _106097.
Proof. exact (@lem8036409 M s h1 _106097). Qed.
Lemma lem8036432 {M : Type'} (s : type30 M) (_106097 : cart real M) : (term175 M s _106097) = (term106 M s _106097).
Proof. exact (eq_refl (term175 M s _106097)). Qed.
Lemma lem8036434 {N : Type'} (_106098 : cart real N) (t : type30 N) (x : cart real N) (h1 : term191 N t x) : term280 N t x _106098.
Proof. exact (@lem8036430 N t x h1 _106098). Qed.
Lemma lem8036435 {N : Type'} (t : type30 N) (x : cart real N) (_106098 : cart real N) : (term280 N t x _106098) = (term185 N t x _106098).
Proof. exact (eq_refl (term280 N t x _106098)). Qed.
Lemma lem8036440 {M N : Type'} (s : type30 M) (x' : cart real M) (y : cart real N) (t : type30 N) (x : cart real N) (h1 : term236 M N s x' y t x) : term106 N t x.
Proof. exact (proj2 (@lem8036363 M N s x' y t x h1)). Qed.
Lemma lem8036446 {M N : Type'} (s : type30 M) (x' : cart real M) (y : cart real N) (t : type30 N) (x : cart real N) (h1 : term236 M N s x' y t x) : x = y.
Proof. exact (proj2 (@lem8036367 M N s x' y t x h1)). Qed.
Lemma lem8036448 {M : Type'} (s : type30 M) (x'' : cart real M) (h1 : s x'') : s x''.
Proof. exact (h1). Qed.
Lemma lem8036452 {M : Type'} (_106097 : cart real M) (s : type30 M) (h1 : term109 M s) : term106 M s _106097.
Proof. exact (EQ_MP (@lem8036432 M s _106097) (@lem8036431 M _106097 s h1)). Qed.
Lemma lem8036462 {N : Type'} (_106098 : cart real N) (t : type30 N) (x : cart real N) (h1 : term191 N t x) : term185 N t x _106098.
Proof. exact (EQ_MP (@lem8036435 N t x _106098) (@lem8036434 N _106098 t x h1)). Qed.
Lemma lem8036491 {N : Type'} (t : type30 N) : (term108 N t) = (term108 N t).
Proof. exact (eq_refl (term108 N t)). Qed.
Lemma lem8036492 {M N : Type'} (s : type30 M) (x' : cart real M) (y : cart real N) (t : type30 N) (x : cart real N) (h1 : term236 M N s x' y t x) : (term175 N t x) = (term175 N t y).
Proof. exact (MK_COMB (@lem8036491 N t) (@lem8036446 M N s x' y t x h1)). Qed.
Lemma lem8036493 {N : Type'} (t : type30 N) (y : cart real N) : (term175 N t y) = (term106 N t y).
Proof. exact (eq_refl (term175 N t y)). Qed.
Lemma lem8036494 {N : Type'} (t : type30 N) (x : cart real N) : (term281 N t x) = (term281 N t x).
Proof. exact (eq_refl (term281 N t x)). Qed.
Lemma lem8036495 {N : Type'} (x : cart real N) (t : type30 N) (y : cart real N) : ((term175 N t x) = (term175 N t y)) = ((term175 N t x) = (term106 N t y)).
Proof. exact (MK_COMB (@lem8036494 N t x) (@lem8036493 N t y)). Qed.
Lemma lem8036496 {N : Type'} (t : type30 N) (x : cart real N) : (term175 N t x) = (term106 N t x).
Proof. exact (eq_refl (term175 N t x)). Qed.
Lemma lem8036497 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8036498 {N : Type'} (t : type30 N) (x : cart real N) : (term281 N t x) = (term282 N t x).
Proof. exact (MK_COMB (@lem8036497) (@lem8036496 N t x)). Qed.
Lemma lem8036499 {N : Type'} (t : type30 N) (y : cart real N) : (term106 N t y) = (term106 N t y).
Proof. exact (eq_refl (term106 N t y)). Qed.
Lemma lem8036500 {N : Type'} (x : cart real N) (t : type30 N) (y : cart real N) : ((term175 N t x) = (term106 N t y)) = ((term106 N t x) = (term106 N t y)).
Proof. exact (MK_COMB (@lem8036498 N t x) (@lem8036499 N t y)). Qed.
Lemma lem8036501 {N : Type'} (x : cart real N) (t : type30 N) (y : cart real N) : ((term175 N t x) = (term175 N t y)) = ((term106 N t x) = (term106 N t y)).
Proof. exact (TRANS (@lem8036495 N x t y) (@lem8036500 N x t y)). Qed.
Lemma lem8036502 {M N : Type'} (s : type30 M) (x' : cart real M) (y : cart real N) (t : type30 N) (x : cart real N) (h1 : term236 M N s x' y t x) : (term106 N t x) = (term106 N t y).
Proof. exact (EQ_MP (@lem8036501 N x t y) (@lem8036492 M N s x' y t x h1)). Qed.
Lemma lem8036503 {M N : Type'} (s : type30 M) (x' : cart real M) (y : cart real N) (t : type30 N) (x : cart real N) (h1 : term236 M N s x' y t x) : term106 N t y.
Proof. exact (EQ_MP (@lem8036502 M N s x' y t x h1) (@lem8036440 M N s x' y t x h1)). Qed.
Lemma lem8036533 {M N : Type'} (s : type30 M) (x' : cart real M) (y : cart real N) (t : type30 N) (x : cart real N) (h1 : term236 M N s x' y t x) : t y.
Proof. exact (proj1 (@lem8036367 M N s x' y t x h1)). Qed.
Lemma lem8036534 {M N : Type'} (s : type30 M) (x' : cart real M) (y : cart real N) (t : type30 N) (x : cart real N) (h1 : term236 M N s x' y t x) : term283 N t y.
Proof. exact (fun h0 : term106 N t y => @lem8036533 M N s x' y t x h1). Qed.
Lemma lem8036536 (p : Prop) : (term284 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8036537 {N : Type'} (t : type30 N) (y : cart real N) : (term283 N t y) = (t y).
Proof. exact (@lem8036536 (t y)). Qed.
Lemma lem8036538 {M N : Type'} (s : type30 M) (x' : cart real M) (y : cart real N) (t : type30 N) (x : cart real N) (h1 : term236 M N s x' y t x) : t y.
Proof. exact (EQ_MP (@lem8036537 N t y) (@lem8036534 M N s x' y t x h1)). Qed.
Lemma lem8036541 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8036543 {N : Type'} (t : type30 N) (y : cart real N) : (term106 N t y) = (term285 N t y).
Proof. exact (@lem8036541 (t y)). Qed.
Lemma lem8036546 {M N : Type'} (s : type30 M) (x' : cart real M) (y : cart real N) (t : type30 N) (x : cart real N) (h1 : term236 M N s x' y t x) : term285 N t y.
Proof. exact (EQ_MP (@lem8036543 N t y) (@lem8036503 M N s x' y t x h1)). Qed.
Lemma lem8036549 {M N : Type'} (s : type30 M) (x' : cart real M) (y : cart real N) (t : type30 N) (x : cart real N) (h1 : term236 M N s x' y t x) : False.
Proof. exact (@lem8036546 M N s x' y t x h1 (@lem8036538 M N s x' y t x h1)). Qed.
Lemma lem8036550 {M N : Type'} (s : type30 M) (x' : cart real M) (y : cart real N) (t : type30 N) (x : cart real N) (h1 : term236 M N s x' y t x) : term286.
Proof. exact (fun h0 : ~ False => @lem8036549 M N s x' y t x h1). Qed.
Lemma lem8036552 (p : Prop) : (term284 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8036553 : term286 = False.
Proof. exact (@lem8036552 False). Qed.
Lemma lem8036556 {M : Type'} (s : type30 M) (x'' : cart real M) (h1 : s x'') : s x''.
Proof. exact (h1). Qed.
Lemma lem8036557 {M : Type'} (s : type30 M) (x'' : cart real M) (h1 : s x'') : term283 M s x''.
Proof. exact (fun h0 : term106 M s x'' => @lem8036556 M s x'' h1). Qed.
Lemma lem8036559 (p : Prop) : (term284 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8036560 {M : Type'} (s : type30 M) (x'' : cart real M) : (term283 M s x'') = (s x'').
Proof. exact (@lem8036559 (s x'')). Qed.
Lemma lem8036561 {M : Type'} (s : type30 M) (x'' : cart real M) (h1 : s x'') : s x''.
Proof. exact (EQ_MP (@lem8036560 M s x'') (@lem8036557 M s x'' h1)). Qed.
Lemma lem8036564 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8036566 {M : Type'} (s : type30 M) (_106097 : cart real M) : (term106 M s _106097) = (term285 M s _106097).
Proof. exact (@lem8036564 (s _106097)). Qed.
Lemma lem8036569 {M : Type'} (_106097 : cart real M) (s : type30 M) (h1 : term109 M s) : term285 M s _106097.
Proof. exact (EQ_MP (@lem8036566 M s _106097) (@lem8036452 M _106097 s h1)). Qed.
Lemma lem8036570 {M : Type'} (_106097 : cart real M) (s : type30 M) (h1 : term109 M s) : term285 M s _106097.
Proof. exact (@lem8036569 M _106097 s h1). Qed.
Lemma lem8036571 {M : Type'} (x'' : cart real M) (s : type30 M) (h1 : term109 M s) : term285 M s x''.
Proof. exact (@lem8036570 M x'' s h1). Qed.
Lemma lem8036574 {M : Type'} (s : type30 M) (x'' : cart real M) (h1 : term109 M s) (h2 : s x'') : False.
Proof. exact (@lem8036571 M x'' s h1 (@lem8036561 M s x'' h2)). Qed.
Lemma lem8036575 {M : Type'} (s : type30 M) (x'' : cart real M) (h1 : term109 M s) (h2 : s x'') : term286.
Proof. exact (fun h0 : ~ False => @lem8036574 M s x'' h1 h2). Qed.
Lemma lem8036577 (p : Prop) : (term284 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8036578 : term286 = False.
Proof. exact (@lem8036577 False). Qed.
Lemma lem8036579 {M : Type'} (s : type30 M) (x'' : cart real M) (h1 : term109 M s) (h2 : s x'') : False.
Proof. exact (EQ_MP (@lem8036578) (@lem8036575 M s x'' h1 h2)). Qed.
Lemma lem8036609 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) (h1 : term200 M N s t x) : t x.
Proof. exact (proj2 (@lem8036364 M N s t x h1)). Qed.
Lemma lem8036610 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) (h1 : term200 M N s t x) : term283 N t x.
Proof. exact (fun h0 : term106 N t x => @lem8036609 M N s t x h1). Qed.
Lemma lem8036612 (p : Prop) : (term284 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8036613 {N : Type'} (t : type30 N) (x : cart real N) : (term283 N t x) = (t x).
Proof. exact (@lem8036612 (t x)). Qed.
Lemma lem8036614 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) (h1 : term200 M N s t x) : t x.
Proof. exact (EQ_MP (@lem8036613 N t x) (@lem8036610 M N s t x h1)). Qed.
Lemma lem8036616 {N : Type'} (x : cart real N) : x = x.
Proof. exact (@lem21386 (cart real N) x). Qed.
Lemma lem8036617 {N : Type'} (x : cart real N) : x = x.
Proof. exact (@lem8036616 N x). Qed.
Lemma lem8036618 {N : Type'} (x : cart real N) : term287 N x.
Proof. exact (fun h0 : term288 N x => @lem8036617 N x). Qed.
Lemma lem8036620 (p : Prop) : (term284 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8036621 {N : Type'} (x : cart real N) : (term287 N x) = (x = x).
Proof. exact (@lem8036620 (x = x)). Qed.
Lemma lem8036622 {N : Type'} (x : cart real N) : x = x.
Proof. exact (EQ_MP (@lem8036621 N x) (@lem8036618 N x)). Qed.
Lemma lem8036624 (a : Prop) (b : Prop) : (term289 a b) = (term290 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem8036625 {N : Type'} (t : type30 N) (x : cart real N) (_106098 : cart real N) : (term185 N t x _106098) = (term184 N t x _106098).
Proof. exact (@lem8036624 (t _106098) (x = _106098)). Qed.
Lemma lem8036627 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8036628 {N : Type'} (t : type30 N) (x : cart real N) (_106098 : cart real N) : (term184 N t x _106098) = (term291 N t x _106098).
Proof. exact (@lem8036627 (term113 N t x _106098)). Qed.
Lemma lem8036629 {N : Type'} (t : type30 N) (x : cart real N) (_106098 : cart real N) : (term185 N t x _106098) = (term291 N t x _106098).
Proof. exact (TRANS (@lem8036625 N t x _106098) (@lem8036628 N t x _106098)). Qed.
Lemma lem8036631 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) (h1 : term200 M N s t x) : term292 N t x.
Proof. exact (conj (@lem8036614 M N s t x h1) (@lem8036622 N x)). Qed.
Lemma lem8036633 {N : Type'} (_106098 : cart real N) (t : type30 N) (x : cart real N) (h1 : term191 N t x) : term291 N t x _106098.
Proof. exact (EQ_MP (@lem8036629 N t x _106098) (@lem8036462 N _106098 t x h1)). Qed.
Lemma lem8036634 {N : Type'} (_106098 : cart real N) (t : type30 N) (x : cart real N) (h1 : term191 N t x) : term291 N t x _106098.
Proof. exact (@lem8036633 N _106098 t x h1). Qed.
Lemma lem8036635 {N : Type'} (t : type30 N) (x : cart real N) (h1 : term191 N t x) : term293 N t x.
Proof. exact (@lem8036634 N x t x h1). Qed.
Lemma lem8036638 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) (h1 : term191 N t x) (h2 : term200 M N s t x) : False.
Proof. exact (@lem8036635 N t x h1 (@lem8036631 M N s t x h2)). Qed.
Lemma lem8036639 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) (h1 : term191 N t x) (h2 : term200 M N s t x) : term286.
Proof. exact (fun h0 : ~ False => @lem8036638 M N s t x h1 h2). Qed.
Lemma lem8036641 (p : Prop) : (term284 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8036642 : term286 = False.
Proof. exact (@lem8036641 False). Qed.
Lemma lem8036643 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) (h1 : term191 N t x) (h2 : term200 M N s t x) : False.
Proof. exact (EQ_MP (@lem8036642) (@lem8036639 M N s t x h1 h2)). Qed.
Lemma lem8036644 {M N : Type'} (s : type30 M) (x' : cart real M) (y : cart real N) (t : type30 N) (x : cart real N) (h1 : term236 M N s x' y t x) : False.
Proof. exact (EQ_MP (@lem8036553) (@lem8036550 M N s x' y t x h1)). Qed.
Lemma lem8036645 {M : Type'} (s : type30 M) (x'' : cart real M) (h1 : term109 M s) (h2 : s x'') : (s x'') = False.
Proof. exact (prop_ext (fun h3 : s x'' => @lem8036579 M s x'' h1 h2) (fun h3 : False => @lem8036448 M s x'' h2)). Qed.
Lemma lem8036646 {M : Type'} (s : type30 M) (x'' : cart real M) (h1 : term109 M s) (h2 : s x'') : False.
Proof. exact (EQ_MP (@lem8036645 M s x'' h1 h2) (@lem8036448 M s x'' h2)). Qed.
Lemma lem8036647 {M : Type'} (s : type30 M) (x'' : cart real M) (h1 : term109 M s) (h2 : s x'') : (s x'') = False.
Proof. exact (prop_ext (fun h3 : s x'' => @lem8036646 M s x'' h1 h2) (fun h3 : False => @lem8036398 M s x'' h2)). Qed.
Lemma lem8036648 {M : Type'} (s : type30 M) (x'' : cart real M) (h1 : term109 M s) (h2 : s x'') : False.
Proof. exact (EQ_MP (@lem8036647 M s x'' h1 h2) (@lem8036398 M s x'' h2)). Qed.
Lemma lem8036649 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) (h1 : term191 N t x) (h2 : term200 M N s t x) : (term191 N t x) = False.
Proof. exact (prop_ext (fun h3 : term191 N t x => @lem8036643 M N s t x h1 h2) (fun h3 : False => @lem8036430 N t x h1)). Qed.
Lemma lem8036650 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) (h1 : term191 N t x) (h2 : term200 M N s t x) : False.
Proof. exact (EQ_MP (@lem8036649 M N s t x h1 h2) (@lem8036430 N t x h1)). Qed.
Lemma lem8036651 {M : Type'} (s : type30 M) (x'' : cart real M) (h1 : term109 M s) (h2 : s x'') : (term109 M s) = False.
Proof. exact (prop_ext (fun h3 : term109 M s => @lem8036648 M s x'' h1 h2) (fun h3 : False => @lem8036409 M s h1)). Qed.
Lemma lem8036652 {M : Type'} (s : type30 M) (x'' : cart real M) (h1 : term109 M s) (h2 : s x'') : False.
Proof. exact (EQ_MP (@lem8036651 M s x'' h1 h2) (@lem8036409 M s h1)). Qed.
Lemma lem8036653 {M : Type'} (s : type30 M) (x'' : cart real M) (h1 : term109 M s) (h2 : s x'') : (s x'') = False.
Proof. exact (prop_ext (fun h3 : s x'' => @lem8036652 M s x'' h1 h2) (fun h3 : False => @lem8036398 M s x'' h2)). Qed.
Lemma lem8036654 {M : Type'} (s : type30 M) (x'' : cart real M) (h1 : term109 M s) (h2 : s x'') : False.
Proof. exact (EQ_MP (@lem8036653 M s x'' h1 h2) (@lem8036398 M s x'' h2)). Qed.
Lemma lem8036655 {M N : Type'} (x'' : cart real M) (s : type30 M) (t : type30 N) (x : cart real N) (h1 : s x'') (h2 : term200 M N s t x) : False.
Proof. exact (or_elim (@lem8036372 M N s t x h2) (fun h0 : term109 M s => @lem8036654 M s x'' h0 h1) (fun h0 : term191 N t x => @lem8036650 M N s t x h0 h2)). Qed.
Lemma lem8036656 {M N : Type'} (x'' : cart real M) (x' : cart real M) (y : cart real N) (s : type30 M) (t : type30 N) (x : cart real N) (h1 : s x'') (h2 : term274 M N x' y s t x) : False.
Proof. exact (or_elim (@lem8036358 M N x' y s t x h2) (fun h0 : term236 M N s x' y t x => @lem8036644 M N s x' y t x h0) (fun h0 : term200 M N s t x => @lem8036655 M N x'' s t x h1 h0)). Qed.
Lemma lem8036657 {M N : Type'} (x'' : cart real M) (x' : cart real M) (y : cart real N) (s : type30 M) (t : type30 N) (x : cart real N) (h1 : s x'') (h2 : term274 M N x' y s t x) : (s x'') = False.
Proof. exact (prop_ext (fun h3 : s x'' => @lem8036656 M N x'' x' y s t x h1 h2) (fun h3 : False => @lem8036362 M s x'' h1)). Qed.
Lemma lem8036658 {M N : Type'} (x'' : cart real M) (x' : cart real M) (y : cart real N) (s : type30 M) (t : type30 N) (x : cart real N) (h1 : s x'') (h2 : term274 M N x' y s t x) : False.
Proof. exact (EQ_MP (@lem8036657 M N x'' x' y s t x h1 h2) (@lem8036362 M s x'' h1)). Qed.
Lemma lem8036659 {M N : Type'} (x'' : cart real M) (x' : cart real M) (y : cart real N) (s : type30 M) (t : type30 N) (x : cart real N) (h1 : s x'') (h2 : term274 M N x' y s t x) : (term274 M N x' y s t x) = False.
Proof. exact (prop_ext (fun h3 : term274 M N x' y s t x => @lem8036658 M N x'' x' y s t x h1 h2) (fun h3 : False => @lem8036358 M N x' y s t x h2)). Qed.
Lemma lem8036660 {M N : Type'} (x'' : cart real M) (x' : cart real M) (y : cart real N) (s : type30 M) (t : type30 N) (x : cart real N) (h1 : s x'') (h2 : term274 M N x' y s t x) : False.
Proof. exact (EQ_MP (@lem8036659 M N x'' x' y s t x h1 h2) (@lem8036358 M N x' y s t x h2)). Qed.
Lemma lem8036661 {M N : Type'} (x' : cart real M) (y : cart real N) (s : type30 M) (t : type30 N) (x : cart real N) (h1 : term110 M s) (h2 : term274 M N x' y s t x) : False.
Proof. exact (ex_elim (@lem8036000 M s h1) (fun x'' : cart real M => fun h0 : term166 M s x'' => @lem8036660 M N x'' x' y s t x h0 h2)). Qed.
Lemma lem8036662 {M N : Type'} (x' : cart real M) (t : type30 N) (x : cart real N) (s : type30 M) (h1 : term277 M N x' s t x) (h2 : term110 M s) : False.
Proof. exact (ex_elim (@lem8036292 M N x' s t x h1) (fun y : cart real N => fun h0 : term276 M N x' s t x y => @lem8036661 M N x' y s t x h2 h0)). Qed.
Lemma lem8036663 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) (h1 : term110 M s) (h2 : term170 M N s t x) : False.
Proof. exact (ex_elim (@lem8036291 M N s t x h2) (fun x' : cart real M => fun h0 : term278 M N s t x x' => @lem8036662 M N x' t x s h0 h1)). Qed.
Lemma lem8036664 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) (h1 : term110 M s) (h2 : term170 M N s t x) : (term170 M N s t x) = False.
Proof. exact (prop_ext (fun h3 : term170 M N s t x => @lem8036663 M N s t x h1 h2) (fun h3 : False => @lem8035978 M N s t x h2)). Qed.
Lemma lem8036665 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real N) (h1 : term110 M s) (h2 : term170 M N s t x) : False.
Proof. exact (EQ_MP (@lem8036664 M N s t x h1 h2) (@lem8035978 M N s t x h2)). Qed.
Lemma lem8036666 {M N : Type'} (t : type30 N) (x : cart real N) (s : type30 M) (h1 : term110 M s) : term169 M N s t x.
Proof. exact (fun h0 : term170 M N s t x => @lem8036665 M N s t x h1 h0). Qed.
Lemma lem8036667 {M N : Type'} (t : type30 N) (x : cart real N) (s : type30 M) (h1 : term110 M s) : (term153 M N s t x) = (t x).
Proof. exact (EQ_MP (@lem8035977 M N s t x) (@lem8036666 M N t x s h1)). Qed.
Lemma lem8036672 {M N : Type'} (t : type30 N) (s : type30 M) (h1 : term110 M s) : term156 M N s t.
Proof. exact (fun x : cart real N => @lem8036667 M N t x s h1). Qed.
Lemma lem8036673 {M N : Type'} (s : type30 M) (t : type30 N) : term157 M N s t.
Proof. exact (fun h0 : term110 M s => @lem8036672 M N t s h0). Qed.
Lemma lem8036678 {M N : Type'} (t : type30 N) : term161 M N t.
Proof. exact (fun s : type30 M => @lem8036673 M N s t). Qed.
Lemma lem8036683 {M N : Type'} : term165 M N.
Proof. exact (fun t : type30 N => @lem8036678 M N t). Qed.
Lemma lem8036684 {M N : Type'} : term164 M N.
Proof. exact (EQ_MP (@lem8035972 M N) (@lem8036683 M N)). Qed.
Lemma lem8036685 {M N : Type'} (t : type30 N) : term294 M N t.
Proof. exact (@lem8036684 M N t). Qed.
Lemma lem8036686 {M N : Type'} (t : type30 N) : (term294 M N t) = (term160 M N t).
Proof. exact (eq_refl (term294 M N t)). Qed.
Lemma lem8036687 {M N : Type'} (t : type30 N) : term160 M N t.
Proof. exact (EQ_MP (@lem8036686 M N t) (@lem8036685 M N t)). Qed.
Lemma lem8036688 {M N : Type'} (t : type30 N) (s : type30 M) : term295 M N t s.
Proof. exact (@lem8036687 M N t s). Qed.
Lemma lem8036689 {M N : Type'} (s : type30 M) (t : type30 N) : (term295 M N t s) = (term124 M N s t).
Proof. exact (eq_refl (term295 M N t s)). Qed.
Lemma lem8036690 {M N : Type'} (s : type30 M) (t : type30 N) : term124 M N s t.
Proof. exact (EQ_MP (@lem8036689 M N s t) (@lem8036688 M N t s)). Qed.
Lemma lem8036692 {M N : Type'} (s : type30 M) (t : type30 N) : term124 M N s t.
Proof. exact (@lem8035708 M N s t (@lem8036690 M N s t)). Qed.
Lemma lem8036693 {M N : Type'} (s : type30 M) (t : type30 N) (h1 : term125 M N s t) : False.
Proof. exact (@lem8036692 M N s t (@lem8035692 M N s t h1)). Qed.
Lemma lem8036694 {M N : Type'} (s : type30 M) (t : type30 N) (h1 : term125 M N s t) : (term125 M N s t) = False.
Proof. exact (prop_ext (fun h2 : term125 M N s t => @lem8036693 M N s t h1) (fun h2 : False => @lem8035692 M N s t h1)). Qed.
Lemma lem8036695 {M N : Type'} (s : type30 M) (t : type30 N) (h1 : term125 M N s t) : False.
Proof. exact (EQ_MP (@lem8036694 M N s t h1) (@lem8035692 M N s t h1)). Qed.
Lemma lem8036696 {M N : Type'} (s : type30 M) (t : type30 N) : term124 M N s t.
Proof. exact (fun h0 : term125 M N s t => @lem8036695 M N s t h0). Qed.
Lemma lem8036697 {M N : Type'} (s : type30 M) (t : type30 N) : term122 M N s t.
Proof. exact (EQ_MP (@lem8035691 M N s t) (@lem8036696 M N s t)). Qed.
Lemma lem8036698 {M N : Type'} (s : type30 M) (t : type30 N) : term103 M N s t.
Proof. exact (EQ_MP (@lem8035687 M N s t) (@lem8036697 M N s t)). Qed.
Lemma lem8036699 {M N : Type'} (s : type30 M) (t : type30 N) : term102 M N s t.
Proof. exact (EQ_MP (@lem8035581 M N s t) (@lem8036698 M N s t)). Qed.
Lemma lem8036700 {M N : Type'} (t : type30 N) (s : type30 M) (h1 : term40 M s) : term98 M N s t.
Proof. exact (@lem8036699 M N s t (@lem8035279 M s h1)). Qed.
Lemma lem8036701 {M N : Type'} (t : type30 N) (s : type30 M) (h1 : term40 M s) : term63 M N s t.
Proof. exact (EQ_MP (@lem8035522 M N s t) (@lem8036700 M N t s h1)). Qed.
Lemma lem8036702 {M N : Type'} (t : type30 N) (s : type30 M) (h1 : term40 M s) : term54 M N s t.
Proof. exact (EQ_MP (@lem8035433 M N s t) (@lem8036701 M N t s h1)). Qed.
Lemma lem8036705 {M N : Type'} (t : type30 N) (s : type30 M) (h1 : term40 M s) : (term26 M N s t) = t.
Proof. exact (EQ_MP (@lem8035407 M N s t) (@lem8036702 M N t s h1)). Qed.
Lemma lem8036706 {M N : Type'} (t : type30 N) (s : type30 M) (h1 : term40 M s) : (term40 M s) = ((term26 M N s t) = t).
Proof. exact (prop_ext (fun h2 : term40 M s => @lem8036705 M N t s h1) (fun h2 : (term26 M N s t) = t => @lem8035279 M s h1)). Qed.
Lemma lem8036707 {M N : Type'} (t : type30 N) (s : type30 M) (h1 : term40 M s) : (term26 M N s t) = t.
Proof. exact (EQ_MP (@lem8036706 M N t s h1) (@lem8035279 M s h1)). Qed.
Lemma lem8036708 {M N : Type'} (s : type30 M) (t : type30 N) : term29 M N s t.
Proof. exact (fun h0 : term40 M s => @lem8036707 M N t s h0). Qed.
Lemma lem8036709 {M N : Type'} (t : type30 N) (s : type30 M) (h1 : s = (@EMPTY (cart real M))) : (term26 M N s t) = (@EMPTY (cart real N)).
Proof. exact (EQ_MP (@lem8035334 M N t s h1) (@lem0)). Qed.
Lemma lem8036710 {M N : Type'} (t : type30 N) (s : type30 M) (h1 : s = (@EMPTY (cart real M))) : (s = (@EMPTY (cart real M))) = ((term26 M N s t) = (@EMPTY (cart real N))).
Proof. exact (prop_ext (fun h2 : s = (@EMPTY (cart real M)) => @lem8036709 M N t s h1) (fun h2 : (term26 M N s t) = (@EMPTY (cart real N)) => @lem8035262 M s h1)). Qed.
Lemma lem8036711 {M N : Type'} (t : type30 N) (s : type30 M) (h1 : s = (@EMPTY (cart real M))) : (term26 M N s t) = (@EMPTY (cart real N)).
Proof. exact (EQ_MP (@lem8036710 M N t s h1) (@lem8035262 M s h1)). Qed.
Lemma lem8036712 {M N : Type'} (s : type30 M) (t : type30 N) : term33 M N s t.
Proof. exact (fun h0 : s = (@EMPTY (cart real M)) => @lem8036711 M N t s h0). Qed.
Lemma lem8036713 {M N : Type'} (s : type30 M) (t : type30 N) : term36 M N s t.
Proof. exact (conj (@lem8036712 M N s t) (@lem8036708 M N s t)). Qed.
Lemma lem8036714 {M N : Type'} (s : type30 M) (t : type30 N) : (term26 M N s t) = (term37 M N s t).
Proof. exact (EQ_MP (@lem8035261 M N s t) (@lem8036713 M N s t)). Qed.
Lemma lem8036719 {M N : Type'} (s : type30 M) : term296 M N s.
Proof. exact (fun t : type30 N => @lem8036714 M N s t). Qed.
Lemma lem8036724 {M N : Type'} : term297 M N.
Proof. exact (fun s : type30 M => @lem8036719 M N s). Qed.
