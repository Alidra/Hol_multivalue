Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LAST_EL_term_abbrevs.
Require Import EL_CONS_spec.
Require Import LENGTH_EQ_NIL_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import SUC_SUB1_spec.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1097080_spec.
Require Import thm1098347_spec.
Require Import thm1098348_spec.
Require Import thm12653_spec.
Require Import thm13473_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1822_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm82_spec.
Lemma lem1206268 (n : nat) : term0 n.
Proof. exact (@lem137156 n). Qed.
Lemma lem1206269 (n : nat) : (term0 n) = ((term1 n) = n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem1206271 {A : Type'} : term2 A.
Proof. exact (proj2 (@lem1097080 A)). Qed.
Lemma lem1206272 {A : Type'} (h : A) : term3 A h.
Proof. exact (@lem1206271 A h). Qed.
Lemma lem1206273 {A : Type'} (h : A) : (term3 A h) = (term4 A h).
Proof. exact (eq_refl (term3 A h)). Qed.
Lemma lem1206274 {A : Type'} (h : A) : term4 A h.
Proof. exact (EQ_MP (@lem1206273 A h) (@lem1206272 A h)). Qed.
Lemma lem1206275 {A : Type'} (h : A) (t : list A) : term5 A h t.
Proof. exact (@lem1206274 A h t). Qed.
Lemma lem1206276 {A : Type'} (h : A) (t : list A) : (term5 A h t) = ((term6 A h t) = (term7 A t)).
Proof. exact (eq_refl (term5 A h t)). Qed.
Lemma lem1206280 {A : Type'} (P : type1143 A) : term8 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1206281 {_28274 : Type'} (P : type1143 _28274) : term8 _28274 P.
Proof. exact (@lem1206280 _28274 P). Qed.
Lemma lem1206282 {_28274 : Type'} : term9 _28274.
Proof. exact (@lem1206281 _28274 (term10 _28274)). Qed.
Lemma lem1206283 {_28274 : Type'} : (term11 _28274) = (term12 _28274).
Proof. exact (eq_refl (term11 _28274)). Qed.
Lemma lem1206284 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1206285 {_28274 : Type'} : (term13 _28274) = (term14 _28274).
Proof. exact (MK_COMB (@lem1206284) (@lem1206283 _28274)). Qed.
Lemma lem1206286 {_28274 : Type'} (t : list _28274) : (term15 _28274 t) = (term16 _28274 t).
Proof. exact (eq_refl (term15 _28274 t)). Qed.
Lemma lem1206287 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1206288 {_28274 : Type'} (t : list _28274) : (term17 _28274 t) = (term18 _28274 t).
Proof. exact (MK_COMB (@lem1206287) (@lem1206286 _28274 t)). Qed.
Lemma lem1206289 {_28274 : Type'} (h : _28274) (t : list _28274) : (term19 _28274 h t) = (term20 _28274 h t).
Proof. exact (eq_refl (term19 _28274 h t)). Qed.
Lemma lem1206290 {_28274 : Type'} (h : _28274) (t : list _28274) : (term21 _28274 h t) = (term22 _28274 h t).
Proof. exact (MK_COMB (@lem1206288 _28274 t) (@lem1206289 _28274 h t)). Qed.
Lemma lem1206291 {_28274 : Type'} (h : _28274) : (term23 _28274 h) = (term24 _28274 h).
Proof. exact (fun_ext (fun t : list _28274 => @lem1206290 _28274 h t)). Qed.
Lemma lem1206292 {_28274 : Type'} : (@all (list _28274)) = (@all (list _28274)).
Proof. exact (eq_refl (@all (list _28274))). Qed.
Lemma lem1206293 {_28274 : Type'} (h : _28274) : (term25 _28274 h) = (term26 _28274 h).
Proof. exact (MK_COMB (@lem1206292 _28274) (@lem1206291 _28274 h)). Qed.
Lemma lem1206294 {_28274 : Type'} : (term27 _28274) = (term28 _28274).
Proof. exact (fun_ext (fun h : _28274 => @lem1206293 _28274 h)). Qed.
Lemma lem1206295 {_28274 : Type'} : (@all _28274) = (@all _28274).
Proof. exact (eq_refl (@all _28274)). Qed.
Lemma lem1206296 {_28274 : Type'} : (term29 _28274) = (term30 _28274).
Proof. exact (MK_COMB (@lem1206295 _28274) (@lem1206294 _28274)). Qed.
Lemma lem1206297 {_28274 : Type'} : (term31 _28274) = (term32 _28274).
Proof. exact (MK_COMB (@lem1206285 _28274) (@lem1206296 _28274)). Qed.
Lemma lem1206298 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1206299 {_28274 : Type'} : (term33 _28274) = (term34 _28274).
Proof. exact (MK_COMB (@lem1206298) (@lem1206297 _28274)). Qed.
Lemma lem1206300 {_28274 : Type'} (l : list _28274) : (term15 _28274 l) = (term16 _28274 l).
Proof. exact (eq_refl (term15 _28274 l)). Qed.
Lemma lem1206301 {_28274 : Type'} : (term35 _28274) = (term10 _28274).
Proof. exact (fun_ext (fun l : list _28274 => @lem1206300 _28274 l)). Qed.
Lemma lem1206302 {_28274 : Type'} : (@all (list _28274)) = (@all (list _28274)).
Proof. exact (eq_refl (@all (list _28274))). Qed.
Lemma lem1206303 {_28274 : Type'} : (term36 _28274) = (term37 _28274).
Proof. exact (MK_COMB (@lem1206302 _28274) (@lem1206301 _28274)). Qed.
Lemma lem1206304 {_28274 : Type'} : (term9 _28274) = (term38 _28274).
Proof. exact (MK_COMB (@lem1206299 _28274) (@lem1206303 _28274)). Qed.
Lemma lem1206305 {_28274 : Type'} : term38 _28274.
Proof. exact (EQ_MP (@lem1206304 _28274) (@lem1206282 _28274)). Qed.
Lemma lem1206306 {_28274 : Type'} (t : list _28274) (h1 : term16 _28274 t) : term16 _28274 t.
Proof. exact (h1). Qed.
Lemma lem1206310 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1206311 {_28274 : Type'} (x : list _28274) : (x = x) = True.
Proof. exact (@lem1206310 (list _28274) x). Qed.
Lemma lem1206312 {_28274 : Type'} : ((@nil _28274) = (@nil _28274)) = True.
Proof. exact (@lem1206311 _28274 (@nil _28274)). Qed.
Lemma lem1206313 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1206314 {_28274 : Type'} : (term39 _28274) = (~ True).
Proof. exact (MK_COMB (@lem1206313) (@lem1206312 _28274)). Qed.
Lemma lem1206316 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1206317 {_28274 : Type'} : (term39 _28274) = False.
Proof. exact (TRANS (@lem1206314 _28274) (@lem1206316)). Qed.
Lemma lem1206318 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1206319 {_28274 : Type'} : (term40 _28274) = (imp False).
Proof. exact (MK_COMB (@lem1206318) (@lem1206317 _28274)). Qed.
Lemma lem1206323 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1206324 {_28274 : Type'} : (@List.length _28274 (@nil _28274)) = (NUMERAL 0).
Proof. exact (@lem1206323 _28274). Qed.
Lemma lem1206325 : Nat.sub = Nat.sub.
Proof. exact (eq_refl Nat.sub). Qed.
Lemma lem1206326 {_28274 : Type'} : (term41 _28274) = term42.
Proof. exact (MK_COMB (@lem1206325) (@lem1206324 _28274)). Qed.
Lemma lem1206327 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem1206328 {_28274 : Type'} : (term44 _28274) = term45.
Proof. exact (MK_COMB (@lem1206326 _28274) (@lem1206327)). Qed.
Lemma lem1206329 {_28274 : Type'} : (@EL _28274) = (@EL _28274).
Proof. exact (eq_refl (@EL _28274)). Qed.
Lemma lem1206330 {_28274 : Type'} : (term46 _28274) = (term47 _28274).
Proof. exact (MK_COMB (@lem1206329 _28274) (@lem1206328 _28274)). Qed.
Lemma lem1206331 {_28274 : Type'} : (@nil _28274) = (@nil _28274).
Proof. exact (eq_refl (@nil _28274)). Qed.
Lemma lem1206332 {_28274 : Type'} : (term48 _28274) = (term49 _28274).
Proof. exact (MK_COMB (@lem1206330 _28274) (@lem1206331 _28274)). Qed.
Lemma lem1206333 {_28274 : Type'} : (term50 _28274) = (term50 _28274).
Proof. exact (eq_refl (term50 _28274)). Qed.
Lemma lem1206334 {_28274 : Type'} : ((@LAST _28274 (@nil _28274)) = (term48 _28274)) = ((@LAST _28274 (@nil _28274)) = (term49 _28274)).
Proof. exact (MK_COMB (@lem1206333 _28274) (@lem1206332 _28274)). Qed.
Lemma lem1206337 {_28274 : Type'} : (term12 _28274) = (term51 _28274).
Proof. exact (MK_COMB (@lem1206319 _28274) (@lem1206334 _28274)). Qed.
Lemma lem1206339 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1206340 {_28274 : Type'} : (term51 _28274) = True.
Proof. exact (@lem1206339 ((@LAST _28274 (@nil _28274)) = (term49 _28274))). Qed.
Lemma lem1206341 {_28274 : Type'} : (term12 _28274) = True.
Proof. exact (TRANS (@lem1206337 _28274) (@lem1206340 _28274)). Qed.
Lemma lem1206342 {_28274 : Type'} : True = (term12 _28274).
Proof. exact (SYM (@lem1206341 _28274)). Qed.
Lemma lem1206343 {_28274 : Type'} : term12 _28274.
Proof. exact (EQ_MP (@lem1206342 _28274) (@lem0)). Qed.
Lemma lem1206351 {A : Type'} (h : A) (t : list A) : (term52 A h t) = (term53 A h t).
Proof. exact (EQ_MP (@lem1098348 A h t) (@lem1098347 A h t)). Qed.
Lemma lem1206352 {_28274 : Type'} (h : _28274) (t : list _28274) : (term52 _28274 h t) = (term53 _28274 h t).
Proof. exact (@lem1206351 _28274 h t). Qed.
Lemma lem1206357 {_28274 : Type'} : (@eq _28274) = (@eq _28274).
Proof. exact (eq_refl (@eq _28274)). Qed.
Lemma lem1206358 {_28274 : Type'} (h : _28274) (t : list _28274) : (term54 _28274 h t) = (term55 _28274 h t).
Proof. exact (MK_COMB (@lem1206357 _28274) (@lem1206352 _28274 h t)). Qed.
Lemma lem1206360 {A : Type'} (h : A) (t : list A) : (term6 A h t) = (term7 A t).
Proof. exact (EQ_MP (@lem1206276 A h t) (@lem1206275 A h t)). Qed.
Lemma lem1206361 {_28274 : Type'} (h : _28274) (t : list _28274) : (term6 _28274 h t) = (term7 _28274 t).
Proof. exact (@lem1206360 _28274 h t). Qed.
Lemma lem1206362 : Nat.sub = Nat.sub.
Proof. exact (eq_refl Nat.sub). Qed.
Lemma lem1206363 {_28274 : Type'} (h : _28274) (t : list _28274) : (term56 _28274 h t) = (term57 _28274 t).
Proof. exact (MK_COMB (@lem1206362) (@lem1206361 _28274 h t)). Qed.
Lemma lem1206364 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem1206365 {_28274 : Type'} (h : _28274) (t : list _28274) : (term58 _28274 h t) = (term59 _28274 t).
Proof. exact (MK_COMB (@lem1206363 _28274 h t) (@lem1206364)). Qed.
Lemma lem1206367 (n : nat) : (term1 n) = n.
Proof. exact (EQ_MP (@lem1206269 n) (@lem1206268 n)). Qed.
Lemma lem1206368 {_28274 : Type'} (t : list _28274) : (term59 _28274 t) = (@List.length _28274 t).
Proof. exact (@lem1206367 (@List.length _28274 t)). Qed.
Lemma lem1206369 {_28274 : Type'} (h : _28274) (t : list _28274) : (term58 _28274 h t) = (@List.length _28274 t).
Proof. exact (TRANS (@lem1206365 _28274 h t) (@lem1206368 _28274 t)). Qed.
Lemma lem1206370 {_28274 : Type'} : (@EL _28274) = (@EL _28274).
Proof. exact (eq_refl (@EL _28274)). Qed.
Lemma lem1206371 {_28274 : Type'} (h : _28274) (t : list _28274) : (term60 _28274 h t) = (term61 _28274 t).
Proof. exact (MK_COMB (@lem1206370 _28274) (@lem1206369 _28274 h t)). Qed.
Lemma lem1206372 {_28274 : Type'} (h : _28274) (t : list _28274) : (@cons _28274 h t) = (@cons _28274 h t).
Proof. exact (eq_refl (@cons _28274 h t)). Qed.
Lemma lem1206373 {_28274 : Type'} (h : _28274) (t : list _28274) : (term62 _28274 h t) = (term63 _28274 h t).
Proof. exact (MK_COMB (@lem1206371 _28274 h t) (@lem1206372 _28274 h t)). Qed.
Lemma lem1206374 {_28274 : Type'} (h : _28274) (t : list _28274) : ((term52 _28274 h t) = (term62 _28274 h t)) = ((term53 _28274 h t) = (term63 _28274 h t)).
Proof. exact (MK_COMB (@lem1206358 _28274 h t) (@lem1206373 _28274 h t)). Qed.
Lemma lem1206377 {_28274 : Type'} (h : _28274) (t : list _28274) : (term64 _28274 h t) = (term64 _28274 h t).
Proof. exact (eq_refl (term64 _28274 h t)). Qed.
Lemma lem1206378 {_28274 : Type'} (h : _28274) (t : list _28274) : (term20 _28274 h t) = (term65 _28274 h t).
Proof. exact (MK_COMB (@lem1206377 _28274 h t) (@lem1206374 _28274 h t)). Qed.
Lemma lem1206381 {_28274 : Type'} (h : _28274) (t : list _28274) : (term65 _28274 h t) = (term20 _28274 h t).
Proof. exact (SYM (@lem1206378 _28274 h t)). Qed.
Lemma lem1206383 {_28274 : Type'} (_474 : _28274) (_475 : Prop) (_476 : _28274 -> Prop) (_477 : _28274) : (term66 _28274 _476 _475 _474 _477) = (term67 _28274 _474 _475 _476 _477).
Proof. exact (@lem13473 _28274 _474 _475 _476 _477). Qed.
Lemma lem1206384 {_28274 : Type'} (_474 : _28274) (_475 : Prop) (h : _28274) (t : list _28274) (_477 : _28274) : (term68 _28274 h t _475 _474 _477) = (term69 _28274 _474 _475 h t _477).
Proof. exact (@lem1206383 _28274 _474 _475 (term70 _28274 h t) _477). Qed.
Lemma lem1206385 {_28274 : Type'} (h : _28274) (t : list _28274) : (term71 _28274 h t) = (term72 _28274 h t).
Proof. exact (@lem1206384 _28274 h (t = (@nil _28274)) h t (@LAST _28274 t)). Qed.
Lemma lem1206386 {_28274 : Type'} (h : _28274) (t : list _28274) : (term73 _28274 h t) = ((@LAST _28274 t) = (term63 _28274 h t)).
Proof. exact (eq_refl (term73 _28274 h t)). Qed.
Lemma lem1206387 {_28274 : Type'} (t : list _28274) : (term74 _28274 t) = (term74 _28274 t).
Proof. exact (eq_refl (term74 _28274 t)). Qed.
Lemma lem1206388 {_28274 : Type'} (h : _28274) (t : list _28274) : (term75 _28274 h t) = (term76 _28274 h t).
Proof. exact (MK_COMB (@lem1206387 _28274 t) (@lem1206386 _28274 h t)). Qed.
Lemma lem1206389 {_28274 : Type'} (h : _28274) (t : list _28274) : (term77 _28274 t h) = (h = (term63 _28274 h t)).
Proof. exact (eq_refl (term77 _28274 t h)). Qed.
Lemma lem1206390 {_28274 : Type'} (t : list _28274) : (term78 _28274 t) = (term78 _28274 t).
Proof. exact (eq_refl (term78 _28274 t)). Qed.
Lemma lem1206391 {_28274 : Type'} (h : _28274) (t : list _28274) : (term79 _28274 t h) = (term80 _28274 h t).
Proof. exact (MK_COMB (@lem1206390 _28274 t) (@lem1206389 _28274 h t)). Qed.
Lemma lem1206392 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1206393 {_28274 : Type'} (h : _28274) (t : list _28274) : (term81 _28274 t h) = (term82 _28274 h t).
Proof. exact (MK_COMB (@lem1206392) (@lem1206391 _28274 h t)). Qed.
Lemma lem1206394 {_28274 : Type'} (h : _28274) (t : list _28274) : (term72 _28274 h t) = (term83 _28274 h t).
Proof. exact (MK_COMB (@lem1206393 _28274 h t) (@lem1206388 _28274 h t)). Qed.
Lemma lem1206395 {_28274 : Type'} (h : _28274) (t : list _28274) : (term71 _28274 h t) = ((term53 _28274 h t) = (term63 _28274 h t)).
Proof. exact (eq_refl (term71 _28274 h t)). Qed.
Lemma lem1206396 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1206397 {_28274 : Type'} (h : _28274) (t : list _28274) : (term84 _28274 h t) = (term85 _28274 h t).
Proof. exact (MK_COMB (@lem1206396) (@lem1206395 _28274 h t)). Qed.
Lemma lem1206398 {_28274 : Type'} (h : _28274) (t : list _28274) : ((term71 _28274 h t) = (term72 _28274 h t)) = (((term53 _28274 h t) = (term63 _28274 h t)) = (term83 _28274 h t)).
Proof. exact (MK_COMB (@lem1206397 _28274 h t) (@lem1206394 _28274 h t)). Qed.
Lemma lem1206399 {_28274 : Type'} (h : _28274) (t : list _28274) : ((term53 _28274 h t) = (term63 _28274 h t)) = (term83 _28274 h t).
Proof. exact (EQ_MP (@lem1206398 _28274 h t) (@lem1206385 _28274 h t)). Qed.
Lemma lem1206400 {_28274 : Type'} (h : _28274) (t : list _28274) : (term83 _28274 h t) = ((term53 _28274 h t) = (term63 _28274 h t)).
Proof. exact (SYM (@lem1206399 _28274 h t)). Qed.
Lemma lem1206401 {_28274 : Type'} (t : list _28274) (h1 : t = (@nil _28274)) : t = (@nil _28274).
Proof. exact (h1). Qed.
Lemma lem1206418 {_28274 : Type'} (t : list _28274) (h1 : term86 _28274 t) : term86 _28274 t.
Proof. exact (h1). Qed.
Lemma lem1206435 {A : Type'} (l : list A) : term87 A l.
Proof. exact (@lem1117066 A l). Qed.
Lemma lem1206436 {A : Type'} (l : list A) : (term87 A l) = (((@List.length A l) = (NUMERAL 0)) = (l = (@nil A))).
Proof. exact (eq_refl (term87 A l)). Qed.
Lemma lem1206438 {_28249 : Type'} (n : nat) : term88 _28249 n.
Proof. exact (@lem1206267 _28249 n). Qed.
Lemma lem1206439 {_28249 : Type'} (n : nat) : (term88 _28249 n) = (term89 _28249 n).
Proof. exact (eq_refl (term88 _28249 n)). Qed.
Lemma lem1206440 {_28249 : Type'} (n : nat) : term89 _28249 n.
Proof. exact (EQ_MP (@lem1206439 _28249 n) (@lem1206438 _28249 n)). Qed.
Lemma lem1206441 {_28249 : Type'} (n : nat) (h : _28249) : term90 _28249 n h.
Proof. exact (@lem1206440 _28249 n h). Qed.
Lemma lem1206442 {_28249 : Type'} (h : _28249) (n : nat) : (term90 _28249 n h) = (term91 _28249 h n).
Proof. exact (eq_refl (term90 _28249 n h)). Qed.
Lemma lem1206443 {_28249 : Type'} (h : _28249) (n : nat) : term91 _28249 h n.
Proof. exact (EQ_MP (@lem1206442 _28249 h n) (@lem1206441 _28249 n h)). Qed.
Lemma lem1206444 {_28249 : Type'} (h : _28249) (n : nat) (t : list _28249) : term92 _28249 h n t.
Proof. exact (@lem1206443 _28249 h n t). Qed.
Lemma lem1206445 {_28249 : Type'} (h : _28249) (n : nat) (t : list _28249) : (term92 _28249 h n t) = ((term93 _28249 n h t) = (term94 _28249 h n t)).
Proof. exact (eq_refl (term92 _28249 h n t)). Qed.
Lemma lem1206480 {_28249 : Type'} (h : _28249) (n : nat) (t : list _28249) : (term93 _28249 n h t) = (term94 _28249 h n t).
Proof. exact (EQ_MP (@lem1206445 _28249 h n t) (@lem1206444 _28249 h n t)). Qed.
Lemma lem1206481 {_28274 : Type'} (h : _28274) (n : nat) (t : list _28274) : (term93 _28274 n h t) = (term94 _28274 h n t).
Proof. exact (@lem1206480 _28274 h n t). Qed.
Lemma lem1206482 {_28274 : Type'} (h : _28274) (t : list _28274) : (term63 _28274 h t) = (term95 _28274 h t).
Proof. exact (@lem1206481 _28274 h (@List.length _28274 t) t). Qed.
Lemma lem1206486 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term96 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem1206487 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term97 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem1206486 _2963 g t e g' t' e'). Qed.
Lemma lem1206488 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term98 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem1206487 _2963 g t e g' t'). Qed.
Lemma lem1206489 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term99 _2963 g t e.
Proof. exact (fun g' : Prop => @lem1206488 _2963 g t e g'). Qed.
Lemma lem1206490 {_28274 : Type'} (g : Prop) (t : _28274) (e : _28274) : term99 _28274 g t e.
Proof. exact (@lem1206489 _28274 g t e). Qed.
Lemma lem1206491 {_28274 : Type'} (h : _28274) (t : list _28274) : term100 _28274 h t.
Proof. exact (@lem1206490 _28274 ((@List.length _28274 t) = (NUMERAL 0)) h (term101 _28274 t)). Qed.
Lemma lem1206492 {_28274 : Type'} (h : _28274) (t : list _28274) (g' : Prop) : term102 _28274 h t g'.
Proof. exact (@lem1206491 _28274 h t g'). Qed.
Lemma lem1206493 {_28274 : Type'} (h : _28274) (t : list _28274) (g' : Prop) : (term102 _28274 h t g') = (term103 _28274 h t g').
Proof. exact (eq_refl (term102 _28274 h t g')). Qed.
Lemma lem1206494 {_28274 : Type'} (h : _28274) (t : list _28274) (g' : Prop) : term103 _28274 h t g'.
Proof. exact (EQ_MP (@lem1206493 _28274 h t g') (@lem1206492 _28274 h t g')). Qed.
Lemma lem1206495 {_28274 : Type'} (h : _28274) (t : list _28274) (g' : Prop) (t' : _28274) : term104 _28274 h t g' t'.
Proof. exact (@lem1206494 _28274 h t g' t'). Qed.
Lemma lem1206496 {_28274 : Type'} (h : _28274) (t : list _28274) (g' : Prop) (t' : _28274) : (term104 _28274 h t g' t') = (term105 _28274 h t g' t').
Proof. exact (eq_refl (term104 _28274 h t g' t')). Qed.
Lemma lem1206497 {_28274 : Type'} (h : _28274) (t : list _28274) (g' : Prop) (t' : _28274) : term105 _28274 h t g' t'.
Proof. exact (EQ_MP (@lem1206496 _28274 h t g' t') (@lem1206495 _28274 h t g' t')). Qed.
Lemma lem1206498 {_28274 : Type'} (h : _28274) (t : list _28274) (g' : Prop) (t' : _28274) (e' : _28274) : term106 _28274 h t g' t' e'.
Proof. exact (@lem1206497 _28274 h t g' t' e'). Qed.
Lemma lem1206499 {_28274 : Type'} (h : _28274) (t : list _28274) (g' : Prop) (t' : _28274) (e' : _28274) : (term106 _28274 h t g' t' e') = (term107 _28274 h t g' t' e').
Proof. exact (eq_refl (term106 _28274 h t g' t' e')). Qed.
Lemma lem1206500 {_28274 : Type'} (h : _28274) (t : list _28274) (g' : Prop) (t' : _28274) (e' : _28274) : term107 _28274 h t g' t' e'.
Proof. exact (EQ_MP (@lem1206499 _28274 h t g' t' e') (@lem1206498 _28274 h t g' t' e')). Qed.
Lemma lem1206502 {A : Type'} (l : list A) : ((@List.length A l) = (NUMERAL 0)) = (l = (@nil A)).
Proof. exact (EQ_MP (@lem1206436 A l) (@lem1206435 A l)). Qed.
Lemma lem1206503 {_28274 : Type'} (l : list _28274) : ((@List.length _28274 l) = (NUMERAL 0)) = (l = (@nil _28274)).
Proof. exact (@lem1206502 _28274 l). Qed.
Lemma lem1206504 {_28274 : Type'} (t : list _28274) : ((@List.length _28274 t) = (NUMERAL 0)) = (t = (@nil _28274)).
Proof. exact (@lem1206503 _28274 t). Qed.
Lemma lem1206508 {_28274 : Type'} (t : list _28274) (h1 : t = (@nil _28274)) : t = (@nil _28274).
Proof. exact (h1). Qed.
Lemma lem1206509 {_28274 : Type'} : (@eq (list _28274)) = (@eq (list _28274)).
Proof. exact (eq_refl (@eq (list _28274))). Qed.
Lemma lem1206510 {_28274 : Type'} (t : list _28274) (h1 : t = (@nil _28274)) : (@eq (list _28274) t) = (@eq (list _28274) (@nil _28274)).
Proof. exact (MK_COMB (@lem1206509 _28274) (@lem1206508 _28274 t h1)). Qed.
Lemma lem1206511 {_28274 : Type'} : (@nil _28274) = (@nil _28274).
Proof. exact (eq_refl (@nil _28274)). Qed.
Lemma lem1206512 {_28274 : Type'} (t : list _28274) (h1 : t = (@nil _28274)) : (t = (@nil _28274)) = ((@nil _28274) = (@nil _28274)).
Proof. exact (MK_COMB (@lem1206510 _28274 t h1) (@lem1206511 _28274)). Qed.
Lemma lem1206514 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1206515 {_28274 : Type'} (x : list _28274) : (x = x) = True.
Proof. exact (@lem1206514 (list _28274) x). Qed.
Lemma lem1206516 {_28274 : Type'} : ((@nil _28274) = (@nil _28274)) = True.
Proof. exact (@lem1206515 _28274 (@nil _28274)). Qed.
Lemma lem1206517 {_28274 : Type'} (t : list _28274) (h1 : t = (@nil _28274)) : (t = (@nil _28274)) = True.
Proof. exact (TRANS (@lem1206512 _28274 t h1) (@lem1206516 _28274)). Qed.
Lemma lem1206518 {_28274 : Type'} (t : list _28274) (h1 : t = (@nil _28274)) : ((@List.length _28274 t) = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem1206504 _28274 t) (@lem1206517 _28274 t h1)). Qed.
Lemma lem1206519 {_28274 : Type'} (h : _28274) (t : list _28274) (t' : _28274) (e' : _28274) : term108 _28274 h t t' e'.
Proof. exact (@lem1206500 _28274 h t True t' e'). Qed.
Lemma lem1206520 {_28274 : Type'} (h : _28274) (t' : _28274) (e' : _28274) (t : list _28274) (h1 : t = (@nil _28274)) : term109 _28274 h t t' e'.
Proof. exact (@lem1206519 _28274 h t t' e' (@lem1206518 _28274 t h1)). Qed.
Lemma lem1206526 {_28274 : Type'} (h : _28274) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1206527 {_28274 : Type'} (h : _28274) : term110 _28274 h.
Proof. exact (fun h0 : True => @lem1206526 _28274 h). Qed.
Lemma lem1206528 {_28274 : Type'} (h : _28274) (e' : _28274) (t : list _28274) (h1 : t = (@nil _28274)) : term111 _28274 t h e'.
Proof. exact (@lem1206520 _28274 h h e' t h1). Qed.
Lemma lem1206529 {_28274 : Type'} (h : _28274) (e' : _28274) (t : list _28274) (h1 : t = (@nil _28274)) : term112 _28274 t h e'.
Proof. exact (@lem1206528 _28274 h e' t h1 (@lem1206527 _28274 h)). Qed.
Lemma lem1206534 {_28274 : Type'} (t : list _28274) (h1 : t = (@nil _28274)) : t = (@nil _28274).
Proof. exact (h1). Qed.
Lemma lem1206535 {_28274 : Type'} : (@List.length _28274) = (@List.length _28274).
Proof. exact (eq_refl (@List.length _28274)). Qed.
Lemma lem1206536 {_28274 : Type'} (t : list _28274) (h1 : t = (@nil _28274)) : (@List.length _28274 t) = (@List.length _28274 (@nil _28274)).
Proof. exact (MK_COMB (@lem1206535 _28274) (@lem1206534 _28274 t h1)). Qed.
Lemma lem1206538 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1206539 {_28274 : Type'} : (@List.length _28274 (@nil _28274)) = (NUMERAL 0).
Proof. exact (@lem1206538 _28274). Qed.
Lemma lem1206540 {_28274 : Type'} (t : list _28274) (h1 : t = (@nil _28274)) : (@List.length _28274 t) = (NUMERAL 0).
Proof. exact (TRANS (@lem1206536 _28274 t h1) (@lem1206539 _28274)). Qed.
Lemma lem1206541 : Nat.sub = Nat.sub.
Proof. exact (eq_refl Nat.sub). Qed.
Lemma lem1206542 {_28274 : Type'} (t : list _28274) (h1 : t = (@nil _28274)) : (term113 _28274 t) = term42.
Proof. exact (MK_COMB (@lem1206541) (@lem1206540 _28274 t h1)). Qed.
Lemma lem1206543 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem1206544 {_28274 : Type'} (t : list _28274) (h1 : t = (@nil _28274)) : (term114 _28274 t) = term45.
Proof. exact (MK_COMB (@lem1206542 _28274 t h1) (@lem1206543)). Qed.
Lemma lem1206545 {_28274 : Type'} : (@EL _28274) = (@EL _28274).
Proof. exact (eq_refl (@EL _28274)). Qed.
Lemma lem1206546 {_28274 : Type'} (t : list _28274) (h1 : t = (@nil _28274)) : (term115 _28274 t) = (term47 _28274).
Proof. exact (MK_COMB (@lem1206545 _28274) (@lem1206544 _28274 t h1)). Qed.
Lemma lem1206548 {_28274 : Type'} (t : list _28274) (h1 : t = (@nil _28274)) : t = (@nil _28274).
Proof. exact (h1). Qed.
Lemma lem1206549 {_28274 : Type'} (t : list _28274) (h1 : t = (@nil _28274)) : (term101 _28274 t) = (term49 _28274).
Proof. exact (MK_COMB (@lem1206546 _28274 t h1) (@lem1206548 _28274 t h1)). Qed.
Lemma lem1206550 {_28274 : Type'} (t : list _28274) (h1 : t = (@nil _28274)) : term116 _28274 t.
Proof. exact (fun h0 : ~ True => @lem1206549 _28274 t h1). Qed.
Lemma lem1206551 {_28274 : Type'} (h : _28274) (t : list _28274) (h1 : t = (@nil _28274)) : term117 _28274 t h.
Proof. exact (@lem1206529 _28274 h (term49 _28274) t h1). Qed.
Lemma lem1206552 {_28274 : Type'} (h : _28274) (t : list _28274) (h1 : t = (@nil _28274)) : (term95 _28274 h t) = (term118 _28274 h).
Proof. exact (@lem1206551 _28274 h t h1 (@lem1206550 _28274 t h1)). Qed.
Lemma lem1206554 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1206555 {_28274 : Type'} (t2 : _28274) (t1 : _28274) : (@COND _28274 True t1 t2) = t1.
Proof. exact (@lem1206554 _28274 t2 t1). Qed.
Lemma lem1206556 {_28274 : Type'} (h : _28274) : (term118 _28274 h) = h.
Proof. exact (@lem1206555 _28274 (term49 _28274) h). Qed.
Lemma lem1206557 {_28274 : Type'} (h : _28274) (t : list _28274) (h1 : t = (@nil _28274)) : (term95 _28274 h t) = h.
Proof. exact (TRANS (@lem1206552 _28274 h t h1) (@lem1206556 _28274 h)). Qed.
Lemma lem1206558 {_28274 : Type'} (h : _28274) (t : list _28274) (h1 : t = (@nil _28274)) : (term63 _28274 h t) = h.
Proof. exact (TRANS (@lem1206482 _28274 h t) (@lem1206557 _28274 h t h1)). Qed.
Lemma lem1206559 {_28274 : Type'} (h : _28274) : (@eq _28274 h) = (@eq _28274 h).
Proof. exact (eq_refl (@eq _28274 h)). Qed.
Lemma lem1206560 {_28274 : Type'} (h : _28274) (t : list _28274) (h1 : t = (@nil _28274)) : (h = (term63 _28274 h t)) = (h = h).
Proof. exact (MK_COMB (@lem1206559 _28274 h) (@lem1206558 _28274 h t h1)). Qed.
Lemma lem1206562 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1206563 {_28274 : Type'} (x : _28274) : (x = x) = True.
Proof. exact (@lem1206562 _28274 x). Qed.
Lemma lem1206564 {_28274 : Type'} (h : _28274) : (h = h) = True.
Proof. exact (@lem1206563 _28274 h). Qed.
Lemma lem1206565 {_28274 : Type'} (h : _28274) (t : list _28274) (h1 : t = (@nil _28274)) : (h = (term63 _28274 h t)) = True.
Proof. exact (TRANS (@lem1206560 _28274 h t h1) (@lem1206564 _28274 h)). Qed.
Lemma lem1206566 {_28274 : Type'} (h : _28274) (t : list _28274) (h1 : t = (@nil _28274)) : True = (h = (term63 _28274 h t)).
Proof. exact (SYM (@lem1206565 _28274 h t h1)). Qed.
Lemma lem1206568 {A : Type'} (l : list A) : term87 A l.
Proof. exact (@lem1117066 A l). Qed.
Lemma lem1206569 {A : Type'} (l : list A) : (term87 A l) = (((@List.length A l) = (NUMERAL 0)) = (l = (@nil A))).
Proof. exact (eq_refl (term87 A l)). Qed.
Lemma lem1206571 {_28249 : Type'} (n : nat) : term88 _28249 n.
Proof. exact (@lem1206267 _28249 n). Qed.
Lemma lem1206572 {_28249 : Type'} (n : nat) : (term88 _28249 n) = (term89 _28249 n).
Proof. exact (eq_refl (term88 _28249 n)). Qed.
Lemma lem1206573 {_28249 : Type'} (n : nat) : term89 _28249 n.
Proof. exact (EQ_MP (@lem1206572 _28249 n) (@lem1206571 _28249 n)). Qed.
Lemma lem1206574 {_28249 : Type'} (n : nat) (h : _28249) : term90 _28249 n h.
Proof. exact (@lem1206573 _28249 n h). Qed.
Lemma lem1206575 {_28249 : Type'} (h : _28249) (n : nat) : (term90 _28249 n h) = (term91 _28249 h n).
Proof. exact (eq_refl (term90 _28249 n h)). Qed.
Lemma lem1206576 {_28249 : Type'} (h : _28249) (n : nat) : term91 _28249 h n.
Proof. exact (EQ_MP (@lem1206575 _28249 h n) (@lem1206574 _28249 n h)). Qed.
Lemma lem1206577 {_28249 : Type'} (h : _28249) (n : nat) (t : list _28249) : term92 _28249 h n t.
Proof. exact (@lem1206576 _28249 h n t). Qed.
Lemma lem1206578 {_28249 : Type'} (h : _28249) (n : nat) (t : list _28249) : (term92 _28249 h n t) = ((term93 _28249 n h t) = (term94 _28249 h n t)).
Proof. exact (eq_refl (term92 _28249 h n t)). Qed.
Lemma lem1206590 {_28274 : Type'} (t : list _28274) (h1 : term86 _28274 t) : term86 _28274 t.
Proof. exact (h1). Qed.
Lemma lem1206591 {_28274 : Type'} (t : list _28274) (h1 : term86 _28274 t) (h2 : term16 _28274 t) : (@LAST _28274 t) = (term101 _28274 t).
Proof. exact (@lem1206306 _28274 t h2 (@lem1206590 _28274 t h1)). Qed.
Lemma lem1206610 {_28274 : Type'} (t : list _28274) : term119 _28274 t.
Proof. exact (@lem82 (t = (@nil _28274))). Qed.
Lemma lem1206626 {_28274 : Type'} (t : list _28274) (h1 : term16 _28274 t) : term16 _28274 t.
Proof. exact (fun h0 : term86 _28274 t => @lem1206591 _28274 t h0 h1). Qed.
Lemma lem1206628 {_28274 : Type'} (t : list _28274) (h1 : term86 _28274 t) : (t = (@nil _28274)) = False.
Proof. exact (@lem1206610 _28274 t (@lem1206418 _28274 t h1)). Qed.
Lemma lem1206629 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1206630 {_28274 : Type'} (t : list _28274) (h1 : term86 _28274 t) : (term86 _28274 t) = (~ False).
Proof. exact (MK_COMB (@lem1206629) (@lem1206628 _28274 t h1)). Qed.
Lemma lem1206632 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1206633 {_28274 : Type'} (t : list _28274) (h1 : term86 _28274 t) : (term86 _28274 t) = True.
Proof. exact (TRANS (@lem1206630 _28274 t h1) (@lem1206632)). Qed.
Lemma lem1206634 {_28274 : Type'} (t : list _28274) (h1 : term86 _28274 t) : True = (term86 _28274 t).
Proof. exact (SYM (@lem1206633 _28274 t h1)). Qed.
Lemma lem1206635 {_28274 : Type'} (t : list _28274) (h1 : term86 _28274 t) : term86 _28274 t.
Proof. exact (EQ_MP (@lem1206634 _28274 t h1) (@lem0)). Qed.
Lemma lem1206636 {_28274 : Type'} (t : list _28274) (h1 : term86 _28274 t) (h2 : term16 _28274 t) : (@LAST _28274 t) = (term101 _28274 t).
Proof. exact (@lem1206626 _28274 t h2 (@lem1206635 _28274 t h1)). Qed.
Lemma lem1206637 {_28274 : Type'} : (@eq _28274) = (@eq _28274).
Proof. exact (eq_refl (@eq _28274)). Qed.
Lemma lem1206638 {_28274 : Type'} (t : list _28274) (h1 : term86 _28274 t) (h2 : term16 _28274 t) : (term120 _28274 t) = (term121 _28274 t).
Proof. exact (MK_COMB (@lem1206637 _28274) (@lem1206636 _28274 t h1 h2)). Qed.
Lemma lem1206640 {_28249 : Type'} (h : _28249) (n : nat) (t : list _28249) : (term93 _28249 n h t) = (term94 _28249 h n t).
Proof. exact (EQ_MP (@lem1206578 _28249 h n t) (@lem1206577 _28249 h n t)). Qed.
Lemma lem1206641 {_28274 : Type'} (h : _28274) (n : nat) (t : list _28274) : (term93 _28274 n h t) = (term94 _28274 h n t).
Proof. exact (@lem1206640 _28274 h n t). Qed.
Lemma lem1206642 {_28274 : Type'} (h : _28274) (t : list _28274) : (term63 _28274 h t) = (term95 _28274 h t).
Proof. exact (@lem1206641 _28274 h (@List.length _28274 t) t). Qed.
Lemma lem1206646 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term96 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem1206647 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term97 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem1206646 _2963 g t e g' t' e'). Qed.
Lemma lem1206648 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term98 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem1206647 _2963 g t e g' t'). Qed.
Lemma lem1206649 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term99 _2963 g t e.
Proof. exact (fun g' : Prop => @lem1206648 _2963 g t e g'). Qed.
Lemma lem1206650 {_28274 : Type'} (g : Prop) (t : _28274) (e : _28274) : term99 _28274 g t e.
Proof. exact (@lem1206649 _28274 g t e). Qed.
Lemma lem1206651 {_28274 : Type'} (h : _28274) (t : list _28274) : term100 _28274 h t.
Proof. exact (@lem1206650 _28274 ((@List.length _28274 t) = (NUMERAL 0)) h (term101 _28274 t)). Qed.
Lemma lem1206652 {_28274 : Type'} (h : _28274) (t : list _28274) (g' : Prop) : term102 _28274 h t g'.
Proof. exact (@lem1206651 _28274 h t g'). Qed.
Lemma lem1206653 {_28274 : Type'} (h : _28274) (t : list _28274) (g' : Prop) : (term102 _28274 h t g') = (term103 _28274 h t g').
Proof. exact (eq_refl (term102 _28274 h t g')). Qed.
Lemma lem1206654 {_28274 : Type'} (h : _28274) (t : list _28274) (g' : Prop) : term103 _28274 h t g'.
Proof. exact (EQ_MP (@lem1206653 _28274 h t g') (@lem1206652 _28274 h t g')). Qed.
Lemma lem1206655 {_28274 : Type'} (h : _28274) (t : list _28274) (g' : Prop) (t' : _28274) : term104 _28274 h t g' t'.
Proof. exact (@lem1206654 _28274 h t g' t'). Qed.
Lemma lem1206656 {_28274 : Type'} (h : _28274) (t : list _28274) (g' : Prop) (t' : _28274) : (term104 _28274 h t g' t') = (term105 _28274 h t g' t').
Proof. exact (eq_refl (term104 _28274 h t g' t')). Qed.
Lemma lem1206657 {_28274 : Type'} (h : _28274) (t : list _28274) (g' : Prop) (t' : _28274) : term105 _28274 h t g' t'.
Proof. exact (EQ_MP (@lem1206656 _28274 h t g' t') (@lem1206655 _28274 h t g' t')). Qed.
Lemma lem1206658 {_28274 : Type'} (h : _28274) (t : list _28274) (g' : Prop) (t' : _28274) (e' : _28274) : term106 _28274 h t g' t' e'.
Proof. exact (@lem1206657 _28274 h t g' t' e'). Qed.
Lemma lem1206659 {_28274 : Type'} (h : _28274) (t : list _28274) (g' : Prop) (t' : _28274) (e' : _28274) : (term106 _28274 h t g' t' e') = (term107 _28274 h t g' t' e').
Proof. exact (eq_refl (term106 _28274 h t g' t' e')). Qed.
Lemma lem1206660 {_28274 : Type'} (h : _28274) (t : list _28274) (g' : Prop) (t' : _28274) (e' : _28274) : term107 _28274 h t g' t' e'.
Proof. exact (EQ_MP (@lem1206659 _28274 h t g' t' e') (@lem1206658 _28274 h t g' t' e')). Qed.
Lemma lem1206662 {A : Type'} (l : list A) : ((@List.length A l) = (NUMERAL 0)) = (l = (@nil A)).
Proof. exact (EQ_MP (@lem1206569 A l) (@lem1206568 A l)). Qed.
Lemma lem1206663 {_28274 : Type'} (l : list _28274) : ((@List.length _28274 l) = (NUMERAL 0)) = (l = (@nil _28274)).
Proof. exact (@lem1206662 _28274 l). Qed.
Lemma lem1206664 {_28274 : Type'} (t : list _28274) : ((@List.length _28274 t) = (NUMERAL 0)) = (t = (@nil _28274)).
Proof. exact (@lem1206663 _28274 t). Qed.
Lemma lem1206666 {_28274 : Type'} (t : list _28274) (h1 : term86 _28274 t) : (t = (@nil _28274)) = False.
Proof. exact (@lem1206610 _28274 t (@lem1206418 _28274 t h1)). Qed.
Lemma lem1206667 {_28274 : Type'} (t : list _28274) (h1 : term86 _28274 t) : ((@List.length _28274 t) = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem1206664 _28274 t) (@lem1206666 _28274 t h1)). Qed.
Lemma lem1206668 {_28274 : Type'} (h : _28274) (t : list _28274) (t' : _28274) (e' : _28274) : term122 _28274 h t t' e'.
Proof. exact (@lem1206660 _28274 h t False t' e'). Qed.
Lemma lem1206669 {_28274 : Type'} (h : _28274) (t' : _28274) (e' : _28274) (t : list _28274) (h1 : term86 _28274 t) : term123 _28274 h t t' e'.
Proof. exact (@lem1206668 _28274 h t t' e' (@lem1206667 _28274 t h1)). Qed.
Lemma lem1206673 {_28274 : Type'} (h : _28274) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1206674 {_28274 : Type'} (h : _28274) : term124 _28274 h.
Proof. exact (fun h0 : False => @lem1206673 _28274 h). Qed.
Lemma lem1206675 {_28274 : Type'} (h : _28274) (e' : _28274) (t : list _28274) (h1 : term86 _28274 t) : term125 _28274 t h e'.
Proof. exact (@lem1206669 _28274 h h e' t h1). Qed.
Lemma lem1206676 {_28274 : Type'} (h : _28274) (e' : _28274) (t : list _28274) (h1 : term86 _28274 t) : term126 _28274 t h e'.
Proof. exact (@lem1206675 _28274 h e' t h1 (@lem1206674 _28274 h)). Qed.
Lemma lem1206682 {_28274 : Type'} (t : list _28274) : (term101 _28274 t) = (term101 _28274 t).
Proof. exact (eq_refl (term101 _28274 t)). Qed.
Lemma lem1206683 {_28274 : Type'} (t : list _28274) : term127 _28274 t.
Proof. exact (fun h0 : ~ False => @lem1206682 _28274 t). Qed.
Lemma lem1206684 {_28274 : Type'} (h : _28274) (t : list _28274) (h1 : term86 _28274 t) : term128 _28274 h t.
Proof. exact (@lem1206676 _28274 h (term101 _28274 t) t h1). Qed.
Lemma lem1206685 {_28274 : Type'} (h : _28274) (t : list _28274) (h1 : term86 _28274 t) : (term95 _28274 h t) = (term129 _28274 h t).
Proof. exact (@lem1206684 _28274 h t h1 (@lem1206683 _28274 t)). Qed.
Lemma lem1206687 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1206688 {_28274 : Type'} (t1 : _28274) (t2 : _28274) : (@COND _28274 False t1 t2) = t2.
Proof. exact (@lem1206687 _28274 t1 t2). Qed.
Lemma lem1206689 {_28274 : Type'} (h : _28274) (t : list _28274) : (term129 _28274 h t) = (term101 _28274 t).
Proof. exact (@lem1206688 _28274 h (term101 _28274 t)). Qed.
Lemma lem1206690 {_28274 : Type'} (h : _28274) (t : list _28274) (h1 : term86 _28274 t) : (term95 _28274 h t) = (term101 _28274 t).
Proof. exact (TRANS (@lem1206685 _28274 h t h1) (@lem1206689 _28274 h t)). Qed.
Lemma lem1206691 {_28274 : Type'} (h : _28274) (t : list _28274) (h1 : term86 _28274 t) : (term63 _28274 h t) = (term101 _28274 t).
Proof. exact (TRANS (@lem1206642 _28274 h t) (@lem1206690 _28274 h t h1)). Qed.
Lemma lem1206692 {_28274 : Type'} (h : _28274) (t : list _28274) (h1 : term86 _28274 t) (h2 : term16 _28274 t) : ((@LAST _28274 t) = (term63 _28274 h t)) = ((term101 _28274 t) = (term101 _28274 t)).
Proof. exact (MK_COMB (@lem1206638 _28274 t h1 h2) (@lem1206691 _28274 h t h1)). Qed.
Lemma lem1206694 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1206695 {_28274 : Type'} (x : _28274) : (x = x) = True.
Proof. exact (@lem1206694 _28274 x). Qed.
Lemma lem1206696 {_28274 : Type'} (t : list _28274) : ((term101 _28274 t) = (term101 _28274 t)) = True.
Proof. exact (@lem1206695 _28274 (term101 _28274 t)). Qed.
Lemma lem1206697 {_28274 : Type'} (h : _28274) (t : list _28274) (h1 : term86 _28274 t) (h2 : term16 _28274 t) : ((@LAST _28274 t) = (term63 _28274 h t)) = True.
Proof. exact (TRANS (@lem1206692 _28274 h t h1 h2) (@lem1206696 _28274 t)). Qed.
Lemma lem1206698 {_28274 : Type'} (h : _28274) (t : list _28274) (h1 : term86 _28274 t) (h2 : term16 _28274 t) : True = ((@LAST _28274 t) = (term63 _28274 h t)).
Proof. exact (SYM (@lem1206697 _28274 h t h1 h2)). Qed.
Lemma lem1206700 {_28274 : Type'} (h : _28274) (t : list _28274) (h1 : term86 _28274 t) (h2 : term16 _28274 t) : (@LAST _28274 t) = (term63 _28274 h t).
Proof. exact (EQ_MP (@lem1206698 _28274 h t h1 h2) (@lem0)). Qed.
Lemma lem1206701 {_28274 : Type'} (h : _28274) (t : list _28274) (h1 : term86 _28274 t) (h2 : term16 _28274 t) : (term86 _28274 t) = ((@LAST _28274 t) = (term63 _28274 h t)).
Proof. exact (prop_ext (fun h3 : term86 _28274 t => @lem1206700 _28274 h t h1 h2) (fun h3 : (@LAST _28274 t) = (term63 _28274 h t) => @lem1206418 _28274 t h1)). Qed.
Lemma lem1206702 {_28274 : Type'} (h : _28274) (t : list _28274) (h1 : term86 _28274 t) (h2 : term16 _28274 t) : (@LAST _28274 t) = (term63 _28274 h t).
Proof. exact (EQ_MP (@lem1206701 _28274 h t h1 h2) (@lem1206418 _28274 t h1)). Qed.
Lemma lem1206703 {_28274 : Type'} (h : _28274) (t : list _28274) (h1 : term16 _28274 t) : term76 _28274 h t.
Proof. exact (fun h0 : term86 _28274 t => @lem1206702 _28274 h t h0 h1). Qed.
Lemma lem1206704 {_28274 : Type'} (h : _28274) (t : list _28274) (h1 : t = (@nil _28274)) : h = (term63 _28274 h t).
Proof. exact (EQ_MP (@lem1206566 _28274 h t h1) (@lem0)). Qed.
Lemma lem1206705 {_28274 : Type'} (h : _28274) (t : list _28274) (h1 : t = (@nil _28274)) : (t = (@nil _28274)) = (h = (term63 _28274 h t)).
Proof. exact (prop_ext (fun h2 : t = (@nil _28274) => @lem1206704 _28274 h t h1) (fun h2 : h = (term63 _28274 h t) => @lem1206401 _28274 t h1)). Qed.
Lemma lem1206706 {_28274 : Type'} (h : _28274) (t : list _28274) (h1 : t = (@nil _28274)) : h = (term63 _28274 h t).
Proof. exact (EQ_MP (@lem1206705 _28274 h t h1) (@lem1206401 _28274 t h1)). Qed.
Lemma lem1206707 {_28274 : Type'} (h : _28274) (t : list _28274) : term80 _28274 h t.
Proof. exact (fun h0 : t = (@nil _28274) => @lem1206706 _28274 h t h0). Qed.
Lemma lem1206708 {_28274 : Type'} (h : _28274) (t : list _28274) (h1 : term16 _28274 t) : term83 _28274 h t.
Proof. exact (conj (@lem1206707 _28274 h t) (@lem1206703 _28274 h t h1)). Qed.
Lemma lem1206709 {_28274 : Type'} (h : _28274) (t : list _28274) (h1 : term16 _28274 t) : (term53 _28274 h t) = (term63 _28274 h t).
Proof. exact (EQ_MP (@lem1206400 _28274 h t) (@lem1206708 _28274 h t h1)). Qed.
Lemma lem1206710 {_28274 : Type'} (h : _28274) (t : list _28274) (h1 : term16 _28274 t) : term65 _28274 h t.
Proof. exact (fun h0 : term130 _28274 h t => @lem1206709 _28274 h t h1). Qed.
Lemma lem1206711 {_28274 : Type'} (h : _28274) (t : list _28274) (h1 : term16 _28274 t) : term20 _28274 h t.
Proof. exact (EQ_MP (@lem1206381 _28274 h t) (@lem1206710 _28274 h t h1)). Qed.
Lemma lem1206712 {_28274 : Type'} (h : _28274) (t : list _28274) : term22 _28274 h t.
Proof. exact (fun h0 : term16 _28274 t => @lem1206711 _28274 h t h0). Qed.
Lemma lem1206717 {_28274 : Type'} (h : _28274) : term26 _28274 h.
Proof. exact (fun t : list _28274 => @lem1206712 _28274 h t). Qed.
Lemma lem1206722 {_28274 : Type'} : term30 _28274.
Proof. exact (fun h : _28274 => @lem1206717 _28274 h). Qed.
Lemma lem1206723 {_28274 : Type'} : term32 _28274.
Proof. exact (conj (@lem1206343 _28274) (@lem1206722 _28274)). Qed.
Lemma lem1206724 {_28274 : Type'} : term37 _28274.
Proof. exact (@lem1206305 _28274 (@lem1206723 _28274)). Qed.
