Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NOT_EX_term_abbrevs.
Require Import DE_MORGAN_THM_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1100834_spec.
Require Import thm1100835_spec.
Require Import thm1100843_spec.
Require Import thm1100844_spec.
Require Import thm1101587_spec.
Require Import thm1101588_spec.
Require Import thm1101596_spec.
Require Import thm1101597_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1855_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1123318 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1123319 {_26368 : Type'} (P : type1143 _26368) : term0 _26368 P.
Proof. exact (@lem1123318 _26368 P). Qed.
Lemma lem1123320 {_26368 : Type'} (P : _26368 -> Prop) : term1 _26368 P.
Proof. exact (@lem1123319 _26368 (term2 _26368 P)). Qed.
Lemma lem1123321 {_26368 : Type'} (P : _26368 -> Prop) : (term3 _26368 P) = ((term4 _26368 P) = (term5 _26368 P)).
Proof. exact (eq_refl (term3 _26368 P)). Qed.
Lemma lem1123322 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1123323 {_26368 : Type'} (P : _26368 -> Prop) : (term6 _26368 P) = (term7 _26368 P).
Proof. exact (MK_COMB (@lem1123322) (@lem1123321 _26368 P)). Qed.
Lemma lem1123324 {_26368 : Type'} (P : _26368 -> Prop) (t : list _26368) : (term8 _26368 P t) = ((term9 _26368 P t) = (term10 _26368 P t)).
Proof. exact (eq_refl (term8 _26368 P t)). Qed.
Lemma lem1123325 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1123326 {_26368 : Type'} (P : _26368 -> Prop) (t : list _26368) : (term11 _26368 P t) = (term12 _26368 P t).
Proof. exact (MK_COMB (@lem1123325) (@lem1123324 _26368 P t)). Qed.
Lemma lem1123327 {_26368 : Type'} (P : _26368 -> Prop) (h : _26368) (t : list _26368) : (term13 _26368 P h t) = ((term14 _26368 P h t) = (term15 _26368 P h t)).
Proof. exact (eq_refl (term13 _26368 P h t)). Qed.
Lemma lem1123328 {_26368 : Type'} (P : _26368 -> Prop) (h : _26368) (t : list _26368) : (term16 _26368 P h t) = (term17 _26368 P h t).
Proof. exact (MK_COMB (@lem1123326 _26368 P t) (@lem1123327 _26368 P h t)). Qed.
Lemma lem1123329 {_26368 : Type'} (P : _26368 -> Prop) (h : _26368) : (term18 _26368 P h) = (term19 _26368 P h).
Proof. exact (fun_ext (fun t : list _26368 => @lem1123328 _26368 P h t)). Qed.
Lemma lem1123330 {_26368 : Type'} : (@all (list _26368)) = (@all (list _26368)).
Proof. exact (eq_refl (@all (list _26368))). Qed.
Lemma lem1123331 {_26368 : Type'} (P : _26368 -> Prop) (h : _26368) : (term20 _26368 P h) = (term21 _26368 P h).
Proof. exact (MK_COMB (@lem1123330 _26368) (@lem1123329 _26368 P h)). Qed.
Lemma lem1123332 {_26368 : Type'} (P : _26368 -> Prop) : (term22 _26368 P) = (term23 _26368 P).
Proof. exact (fun_ext (fun h : _26368 => @lem1123331 _26368 P h)). Qed.
Lemma lem1123333 {_26368 : Type'} : (@all _26368) = (@all _26368).
Proof. exact (eq_refl (@all _26368)). Qed.
Lemma lem1123334 {_26368 : Type'} (P : _26368 -> Prop) : (term24 _26368 P) = (term25 _26368 P).
Proof. exact (MK_COMB (@lem1123333 _26368) (@lem1123332 _26368 P)). Qed.
Lemma lem1123335 {_26368 : Type'} (P : _26368 -> Prop) : (term26 _26368 P) = (term27 _26368 P).
Proof. exact (MK_COMB (@lem1123323 _26368 P) (@lem1123334 _26368 P)). Qed.
Lemma lem1123336 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1123337 {_26368 : Type'} (P : _26368 -> Prop) : (term28 _26368 P) = (term29 _26368 P).
Proof. exact (MK_COMB (@lem1123336) (@lem1123335 _26368 P)). Qed.
Lemma lem1123338 {_26368 : Type'} (P : _26368 -> Prop) (l : list _26368) : (term8 _26368 P l) = ((term9 _26368 P l) = (term10 _26368 P l)).
Proof. exact (eq_refl (term8 _26368 P l)). Qed.
Lemma lem1123339 {_26368 : Type'} (P : _26368 -> Prop) : (term30 _26368 P) = (term2 _26368 P).
Proof. exact (fun_ext (fun l : list _26368 => @lem1123338 _26368 P l)). Qed.
Lemma lem1123340 {_26368 : Type'} : (@all (list _26368)) = (@all (list _26368)).
Proof. exact (eq_refl (@all (list _26368))). Qed.
Lemma lem1123341 {_26368 : Type'} (P : _26368 -> Prop) : (term31 _26368 P) = (term32 _26368 P).
Proof. exact (MK_COMB (@lem1123340 _26368) (@lem1123339 _26368 P)). Qed.
Lemma lem1123342 {_26368 : Type'} (P : _26368 -> Prop) : (term1 _26368 P) = (term33 _26368 P).
Proof. exact (MK_COMB (@lem1123337 _26368 P) (@lem1123341 _26368 P)). Qed.
Lemma lem1123343 {_26368 : Type'} (P : _26368 -> Prop) : term33 _26368 P.
Proof. exact (EQ_MP (@lem1123342 _26368 P) (@lem1123320 _26368 P)). Qed.
Lemma lem1123360 {_25328 : Type'} (P : _25328 -> Prop) : (@EX _25328 P (@nil _25328)) = False.
Proof. exact (EQ_MP (@lem1101588 _25328 P) (@lem1101587 _25328 P)). Qed.
Lemma lem1123361 {_26368 : Type'} (P : _26368 -> Prop) : (@EX _26368 P (@nil _26368)) = False.
Proof. exact (@lem1123360 _26368 P). Qed.
Lemma lem1123362 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1123363 {_26368 : Type'} (P : _26368 -> Prop) : (term4 _26368 P) = (~ False).
Proof. exact (MK_COMB (@lem1123362) (@lem1123361 _26368 P)). Qed.
Lemma lem1123365 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1123366 {_26368 : Type'} (P : _26368 -> Prop) : (term4 _26368 P) = True.
Proof. exact (TRANS (@lem1123363 _26368 P) (@lem1123365)). Qed.
Lemma lem1123367 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1123368 {_26368 : Type'} (P : _26368 -> Prop) : (term34 _26368 P) = (@eq Prop True).
Proof. exact (MK_COMB (@lem1123367) (@lem1123366 _26368 P)). Qed.
Lemma lem1123370 {_25307 : Type'} (P : _25307 -> Prop) : (@List.Forall _25307 P (@nil _25307)) = True.
Proof. exact (EQ_MP (@lem1100835 _25307 P) (@lem1100834 _25307 P)). Qed.
Lemma lem1123371 {_26368 : Type'} (P : _26368 -> Prop) : (@List.Forall _26368 P (@nil _26368)) = True.
Proof. exact (@lem1123370 _26368 P). Qed.
Lemma lem1123372 {_26368 : Type'} (P : _26368 -> Prop) : (term5 _26368 P) = True.
Proof. exact (@lem1123371 _26368 (term35 _26368 P)). Qed.
Lemma lem1123373 {_26368 : Type'} (P : _26368 -> Prop) : ((term4 _26368 P) = (term5 _26368 P)) = (True = True).
Proof. exact (MK_COMB (@lem1123368 _26368 P) (@lem1123372 _26368 P)). Qed.
Lemma lem1123375 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1123376 : (True = True) = True.
Proof. exact (@lem1123375 True). Qed.
Lemma lem1123377 {_26368 : Type'} (P : _26368 -> Prop) : ((term4 _26368 P) = (term5 _26368 P)) = True.
Proof. exact (TRANS (@lem1123373 _26368 P) (@lem1123376)). Qed.
Lemma lem1123378 {_26368 : Type'} (P : _26368 -> Prop) : True = ((term4 _26368 P) = (term5 _26368 P)).
Proof. exact (SYM (@lem1123377 _26368 P)). Qed.
Lemma lem1123379 {_26368 : Type'} (P : _26368 -> Prop) : (term4 _26368 P) = (term5 _26368 P).
Proof. exact (EQ_MP (@lem1123378 _26368 P) (@lem0)). Qed.
Lemma lem1123380 (t1 : Prop) : term36 t1.
Proof. exact (@lem10089 t1). Qed.
Lemma lem1123381 (t1 : Prop) : (term36 t1) = (term37 t1).
Proof. exact (eq_refl (term36 t1)). Qed.
Lemma lem1123382 (t1 : Prop) : term37 t1.
Proof. exact (EQ_MP (@lem1123381 t1) (@lem1123380 t1)). Qed.
Lemma lem1123383 (t1 : Prop) (t2 : Prop) : term38 t1 t2.
Proof. exact (@lem1123382 t1 t2). Qed.
Lemma lem1123384 (t1 : Prop) (t2 : Prop) : (term38 t1 t2) = (term39 t1 t2).
Proof. exact (eq_refl (term38 t1 t2)). Qed.
Lemma lem1123385 (t1 : Prop) (t2 : Prop) : term39 t1 t2.
Proof. exact (EQ_MP (@lem1123384 t1 t2) (@lem1123383 t1 t2)). Qed.
Lemma lem1123395 {_25328 : Type'} (h : _25328) (P : _25328 -> Prop) (t : list _25328) : (term40 _25328 P h t) = (term41 _25328 h P t).
Proof. exact (EQ_MP (@lem1101597 _25328 h P t) (@lem1101596 _25328 h P t)). Qed.
Lemma lem1123396 {_26368 : Type'} (h : _26368) (P : _26368 -> Prop) (t : list _26368) : (term40 _26368 P h t) = (term41 _26368 h P t).
Proof. exact (@lem1123395 _26368 h P t). Qed.
Lemma lem1123399 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1123400 {_26368 : Type'} (h : _26368) (P : _26368 -> Prop) (t : list _26368) : (term14 _26368 P h t) = (term42 _26368 h P t).
Proof. exact (MK_COMB (@lem1123399) (@lem1123396 _26368 h P t)). Qed.
Lemma lem1123402 (t1 : Prop) (t2 : Prop) : (term43 t1 t2) = (term44 t1 t2).
Proof. exact (proj2 (@lem1123385 t1 t2)). Qed.
Lemma lem1123403 {_26368 : Type'} (h : _26368) (P : _26368 -> Prop) (t : list _26368) : (term42 _26368 h P t) = (term45 _26368 h P t).
Proof. exact (@lem1123402 (P h) (@EX _26368 P t)). Qed.
Lemma lem1123407 {_26368 : Type'} (P : _26368 -> Prop) (t : list _26368) (h1 : (term9 _26368 P t) = (term10 _26368 P t)) : (term9 _26368 P t) = (term10 _26368 P t).
Proof. exact (h1). Qed.
Lemma lem1123408 {_26368 : Type'} (P : _26368 -> Prop) (h : _26368) : (term46 _26368 P h) = (term46 _26368 P h).
Proof. exact (eq_refl (term46 _26368 P h)). Qed.
Lemma lem1123409 {_26368 : Type'} (h : _26368) (P : _26368 -> Prop) (t : list _26368) (h1 : (term9 _26368 P t) = (term10 _26368 P t)) : (term45 _26368 h P t) = (term47 _26368 h P t).
Proof. exact (MK_COMB (@lem1123408 _26368 P h) (@lem1123407 _26368 P t h1)). Qed.
Lemma lem1123412 {_26368 : Type'} (h : _26368) (P : _26368 -> Prop) (t : list _26368) (h1 : (term9 _26368 P t) = (term10 _26368 P t)) : (term42 _26368 h P t) = (term47 _26368 h P t).
Proof. exact (TRANS (@lem1123403 _26368 h P t) (@lem1123409 _26368 h P t h1)). Qed.
Lemma lem1123413 {_26368 : Type'} (h : _26368) (P : _26368 -> Prop) (t : list _26368) (h1 : (term9 _26368 P t) = (term10 _26368 P t)) : (term14 _26368 P h t) = (term47 _26368 h P t).
Proof. exact (TRANS (@lem1123400 _26368 h P t) (@lem1123412 _26368 h P t h1)). Qed.
Lemma lem1123414 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1123415 {_26368 : Type'} (h : _26368) (P : _26368 -> Prop) (t : list _26368) (h1 : (term9 _26368 P t) = (term10 _26368 P t)) : (term48 _26368 P h t) = (term49 _26368 h P t).
Proof. exact (MK_COMB (@lem1123414) (@lem1123413 _26368 h P t h1)). Qed.
Lemma lem1123417 {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) (t : list _25307) : (term50 _25307 P h t) = (term51 _25307 h P t).
Proof. exact (EQ_MP (@lem1100844 _25307 h P t) (@lem1100843 _25307 h P t)). Qed.
Lemma lem1123418 {_26368 : Type'} (h : _26368) (P : _26368 -> Prop) (t : list _26368) : (term50 _26368 P h t) = (term51 _26368 h P t).
Proof. exact (@lem1123417 _26368 h P t). Qed.
Lemma lem1123419 {_26368 : Type'} (h : _26368) (P : _26368 -> Prop) (t : list _26368) : (term15 _26368 P h t) = (term52 _26368 h P t).
Proof. exact (@lem1123418 _26368 h (term35 _26368 P) t). Qed.
Lemma lem1123423 {A B : Type'} (f : A -> B) (y : A) : (term53 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1123424 {_26368 : Type'} (f : _26368 -> Prop) (y : _26368) : (term54 _26368 f y) = (f y).
Proof. exact (@lem1123423 _26368 Prop f y). Qed.
Lemma lem1123425 {_26368 : Type'} (P : _26368 -> Prop) (h : _26368) : (term55 _26368 P h) = (term56 _26368 P h).
Proof. exact (@lem1123424 _26368 (term35 _26368 P) h). Qed.
Lemma lem1123426 {_26368 : Type'} (P : _26368 -> Prop) (x : _26368) : (term56 _26368 P x) = (term57 _26368 P x).
Proof. exact (eq_refl (term56 _26368 P x)). Qed.
Lemma lem1123427 {_26368 : Type'} (P : _26368 -> Prop) : (term58 _26368 P) = (term35 _26368 P).
Proof. exact (fun_ext (fun x : _26368 => @lem1123426 _26368 P x)). Qed.
Lemma lem1123428 {_26368 : Type'} (h : _26368) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1123429 {_26368 : Type'} (P : _26368 -> Prop) (h : _26368) : (term55 _26368 P h) = (term56 _26368 P h).
Proof. exact (MK_COMB (@lem1123427 _26368 P) (@lem1123428 _26368 h)). Qed.
Lemma lem1123430 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1123431 {_26368 : Type'} (P : _26368 -> Prop) (h : _26368) : (term59 _26368 P h) = (term60 _26368 P h).
Proof. exact (MK_COMB (@lem1123430) (@lem1123429 _26368 P h)). Qed.
Lemma lem1123432 {_26368 : Type'} (P : _26368 -> Prop) (h : _26368) : (term56 _26368 P h) = (term57 _26368 P h).
Proof. exact (eq_refl (term56 _26368 P h)). Qed.
Lemma lem1123433 {_26368 : Type'} (P : _26368 -> Prop) (h : _26368) : ((term55 _26368 P h) = (term56 _26368 P h)) = ((term56 _26368 P h) = (term57 _26368 P h)).
Proof. exact (MK_COMB (@lem1123431 _26368 P h) (@lem1123432 _26368 P h)). Qed.
Lemma lem1123434 {_26368 : Type'} (P : _26368 -> Prop) (h : _26368) : (term56 _26368 P h) = (term57 _26368 P h).
Proof. exact (EQ_MP (@lem1123433 _26368 P h) (@lem1123425 _26368 P h)). Qed.
Lemma lem1123435 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1123436 {_26368 : Type'} (P : _26368 -> Prop) (h : _26368) : (term61 _26368 P h) = (term46 _26368 P h).
Proof. exact (MK_COMB (@lem1123435) (@lem1123434 _26368 P h)). Qed.
Lemma lem1123437 {_26368 : Type'} (P : _26368 -> Prop) (t : list _26368) : (term10 _26368 P t) = (term10 _26368 P t).
Proof. exact (eq_refl (term10 _26368 P t)). Qed.
Lemma lem1123438 {_26368 : Type'} (h : _26368) (P : _26368 -> Prop) (t : list _26368) : (term52 _26368 h P t) = (term47 _26368 h P t).
Proof. exact (MK_COMB (@lem1123436 _26368 P h) (@lem1123437 _26368 P t)). Qed.
Lemma lem1123441 {_26368 : Type'} (h : _26368) (P : _26368 -> Prop) (t : list _26368) : (term15 _26368 P h t) = (term47 _26368 h P t).
Proof. exact (TRANS (@lem1123419 _26368 h P t) (@lem1123438 _26368 h P t)). Qed.
Lemma lem1123442 {_26368 : Type'} (h : _26368) (P : _26368 -> Prop) (t : list _26368) (h1 : (term9 _26368 P t) = (term10 _26368 P t)) : ((term14 _26368 P h t) = (term15 _26368 P h t)) = ((term47 _26368 h P t) = (term47 _26368 h P t)).
Proof. exact (MK_COMB (@lem1123415 _26368 h P t h1) (@lem1123441 _26368 h P t)). Qed.
Lemma lem1123444 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1123445 (x : Prop) : (x = x) = True.
Proof. exact (@lem1123444 Prop x). Qed.
Lemma lem1123446 {_26368 : Type'} (h : _26368) (P : _26368 -> Prop) (t : list _26368) : ((term47 _26368 h P t) = (term47 _26368 h P t)) = True.
Proof. exact (@lem1123445 (term47 _26368 h P t)). Qed.
Lemma lem1123447 {_26368 : Type'} (h : _26368) (P : _26368 -> Prop) (t : list _26368) (h1 : (term9 _26368 P t) = (term10 _26368 P t)) : ((term14 _26368 P h t) = (term15 _26368 P h t)) = True.
Proof. exact (TRANS (@lem1123442 _26368 h P t h1) (@lem1123446 _26368 h P t)). Qed.
Lemma lem1123448 {_26368 : Type'} (h : _26368) (P : _26368 -> Prop) (t : list _26368) (h1 : (term9 _26368 P t) = (term10 _26368 P t)) : True = ((term14 _26368 P h t) = (term15 _26368 P h t)).
Proof. exact (SYM (@lem1123447 _26368 h P t h1)). Qed.
Lemma lem1123449 {_26368 : Type'} (h : _26368) (P : _26368 -> Prop) (t : list _26368) (h1 : (term9 _26368 P t) = (term10 _26368 P t)) : (term14 _26368 P h t) = (term15 _26368 P h t).
Proof. exact (EQ_MP (@lem1123448 _26368 h P t h1) (@lem0)). Qed.
Lemma lem1123450 {_26368 : Type'} (P : _26368 -> Prop) (h : _26368) (t : list _26368) : term17 _26368 P h t.
Proof. exact (fun h0 : (term9 _26368 P t) = (term10 _26368 P t) => @lem1123449 _26368 h P t h0). Qed.
Lemma lem1123455 {_26368 : Type'} (P : _26368 -> Prop) (h : _26368) : term21 _26368 P h.
Proof. exact (fun t : list _26368 => @lem1123450 _26368 P h t). Qed.
Lemma lem1123460 {_26368 : Type'} (P : _26368 -> Prop) : term25 _26368 P.
Proof. exact (fun h : _26368 => @lem1123455 _26368 P h). Qed.
Lemma lem1123461 {_26368 : Type'} (P : _26368 -> Prop) : term27 _26368 P.
Proof. exact (conj (@lem1123379 _26368 P) (@lem1123460 _26368 P)). Qed.
Lemma lem1123462 {_26368 : Type'} (P : _26368 -> Prop) : term32 _26368 P.
Proof. exact (@lem1123343 _26368 P (@lem1123461 _26368 P)). Qed.
Lemma lem1123467 {_26368 : Type'} : term62 _26368.
Proof. exact (fun P : _26368 -> Prop => @lem1123462 _26368 P). Qed.
