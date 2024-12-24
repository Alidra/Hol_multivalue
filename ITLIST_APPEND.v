Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ITLIST_APPEND_term_abbrevs.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1095962_spec.
Require Import thm1102427_spec.
Require Import thm1102428_spec.
Require Import thm1102439_spec.
Require Import thm1102440_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1129354 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1129355 {_26627 : Type'} (P : type1143 _26627) : term0 _26627 P.
Proof. exact (@lem1129354 _26627 P). Qed.
Lemma lem1129356 {_26617 _26627 : Type'} (f : type1467 _26617 _26627) (a : _26617) : term1 _26617 _26627 f a.
Proof. exact (@lem1129355 _26627 (term2 _26617 _26627 f a)). Qed.
Lemma lem1129357 {_26617 _26627 : Type'} (f : type1467 _26617 _26627) (a : _26617) : (term3 _26617 _26627 f a) = (term4 _26617 _26627 f a).
Proof. exact (eq_refl (term3 _26617 _26627 f a)). Qed.
Lemma lem1129358 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1129359 {_26617 _26627 : Type'} (f : type1467 _26617 _26627) (a : _26617) : (term5 _26617 _26627 f a) = (term6 _26617 _26627 f a).
Proof. exact (MK_COMB (@lem1129358) (@lem1129357 _26617 _26627 f a)). Qed.
Lemma lem1129360 {_26617 _26627 : Type'} (t : list _26627) (f : type1467 _26617 _26627) (a : _26617) : (term7 _26617 _26627 f a t) = (term8 _26617 _26627 t f a).
Proof. exact (eq_refl (term7 _26617 _26627 f a t)). Qed.
Lemma lem1129361 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1129362 {_26617 _26627 : Type'} (t : list _26627) (f : type1467 _26617 _26627) (a : _26617) : (term9 _26617 _26627 f a t) = (term10 _26617 _26627 t f a).
Proof. exact (MK_COMB (@lem1129361) (@lem1129360 _26617 _26627 t f a)). Qed.
Lemma lem1129363 {_26617 _26627 : Type'} (h : _26627) (t : list _26627) (f : type1467 _26617 _26627) (a : _26617) : (term11 _26617 _26627 f a h t) = (term12 _26617 _26627 h t f a).
Proof. exact (eq_refl (term11 _26617 _26627 f a h t)). Qed.
Lemma lem1129364 {_26617 _26627 : Type'} (h : _26627) (t : list _26627) (f : type1467 _26617 _26627) (a : _26617) : (term13 _26617 _26627 f a h t) = (term14 _26617 _26627 h t f a).
Proof. exact (MK_COMB (@lem1129362 _26617 _26627 t f a) (@lem1129363 _26617 _26627 h t f a)). Qed.
Lemma lem1129365 {_26617 _26627 : Type'} (h : _26627) (f : type1467 _26617 _26627) (a : _26617) : (term15 _26617 _26627 f a h) = (term16 _26617 _26627 h f a).
Proof. exact (fun_ext (fun t : list _26627 => @lem1129364 _26617 _26627 h t f a)). Qed.
Lemma lem1129366 {_26627 : Type'} : (@all (list _26627)) = (@all (list _26627)).
Proof. exact (eq_refl (@all (list _26627))). Qed.
Lemma lem1129367 {_26617 _26627 : Type'} (h : _26627) (f : type1467 _26617 _26627) (a : _26617) : (term17 _26617 _26627 f a h) = (term18 _26617 _26627 h f a).
Proof. exact (MK_COMB (@lem1129366 _26627) (@lem1129365 _26617 _26627 h f a)). Qed.
Lemma lem1129368 {_26617 _26627 : Type'} (f : type1467 _26617 _26627) (a : _26617) : (term19 _26617 _26627 f a) = (term20 _26617 _26627 f a).
Proof. exact (fun_ext (fun h : _26627 => @lem1129367 _26617 _26627 h f a)). Qed.
Lemma lem1129369 {_26627 : Type'} : (@all _26627) = (@all _26627).
Proof. exact (eq_refl (@all _26627)). Qed.
Lemma lem1129370 {_26617 _26627 : Type'} (f : type1467 _26617 _26627) (a : _26617) : (term21 _26617 _26627 f a) = (term22 _26617 _26627 f a).
Proof. exact (MK_COMB (@lem1129369 _26627) (@lem1129368 _26617 _26627 f a)). Qed.
Lemma lem1129371 {_26617 _26627 : Type'} (f : type1467 _26617 _26627) (a : _26617) : (term23 _26617 _26627 f a) = (term24 _26617 _26627 f a).
Proof. exact (MK_COMB (@lem1129359 _26617 _26627 f a) (@lem1129370 _26617 _26627 f a)). Qed.
Lemma lem1129372 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1129373 {_26617 _26627 : Type'} (f : type1467 _26617 _26627) (a : _26617) : (term25 _26617 _26627 f a) = (term26 _26617 _26627 f a).
Proof. exact (MK_COMB (@lem1129372) (@lem1129371 _26617 _26627 f a)). Qed.
Lemma lem1129374 {_26617 _26627 : Type'} (l1 : list _26627) (f : type1467 _26617 _26627) (a : _26617) : (term7 _26617 _26627 f a l1) = (term8 _26617 _26627 l1 f a).
Proof. exact (eq_refl (term7 _26617 _26627 f a l1)). Qed.
Lemma lem1129375 {_26617 _26627 : Type'} (f : type1467 _26617 _26627) (a : _26617) : (term27 _26617 _26627 f a) = (term2 _26617 _26627 f a).
Proof. exact (fun_ext (fun l1 : list _26627 => @lem1129374 _26617 _26627 l1 f a)). Qed.
Lemma lem1129376 {_26627 : Type'} : (@all (list _26627)) = (@all (list _26627)).
Proof. exact (eq_refl (@all (list _26627))). Qed.
Lemma lem1129377 {_26617 _26627 : Type'} (f : type1467 _26617 _26627) (a : _26617) : (term28 _26617 _26627 f a) = (term29 _26617 _26627 f a).
Proof. exact (MK_COMB (@lem1129376 _26627) (@lem1129375 _26617 _26627 f a)). Qed.
Lemma lem1129378 {_26617 _26627 : Type'} (f : type1467 _26617 _26627) (a : _26617) : (term1 _26617 _26627 f a) = (term30 _26617 _26627 f a).
Proof. exact (MK_COMB (@lem1129373 _26617 _26627 f a) (@lem1129377 _26617 _26627 f a)). Qed.
Lemma lem1129379 {_26617 _26627 : Type'} (f : type1467 _26617 _26627) (a : _26617) : term30 _26617 _26627 f a.
Proof. exact (EQ_MP (@lem1129378 _26617 _26627 f a) (@lem1129356 _26617 _26627 f a)). Qed.
Lemma lem1129380 {_26617 _26627 : Type'} (t : list _26627) (f : type1467 _26617 _26627) (a : _26617) (h1 : term8 _26617 _26627 t f a) : term8 _26617 _26627 t f a.
Proof. exact (h1). Qed.
Lemma lem1129391 {A : Type'} : term31 A.
Proof. exact (proj1 (@lem1095962 A)). Qed.
Lemma lem1129392 {A : Type'} (l : list A) : term32 A l.
Proof. exact (@lem1129391 A l). Qed.
Lemma lem1129393 {A : Type'} (l : list A) : (term32 A l) = ((@List.app A (@nil A) l) = l).
Proof. exact (eq_refl (term32 A l)). Qed.
Lemma lem1129404 {A : Type'} (l : list A) : (@List.app A (@nil A) l) = l.
Proof. exact (EQ_MP (@lem1129393 A l) (@lem1129392 A l)). Qed.
Lemma lem1129405 {_26627 : Type'} (l : list _26627) : (@List.app _26627 (@nil _26627) l) = l.
Proof. exact (@lem1129404 _26627 l). Qed.
Lemma lem1129406 {_26627 : Type'} (l2 : list _26627) : (@List.app _26627 (@nil _26627) l2) = l2.
Proof. exact (@lem1129405 _26627 l2). Qed.
Lemma lem1129407 {_26617 _26627 : Type'} (f : type1467 _26617 _26627) : (@ITLIST _26617 _26627 f) = (@ITLIST _26617 _26627 f).
Proof. exact (eq_refl (@ITLIST _26617 _26627 f)). Qed.
Lemma lem1129408 {_26617 _26627 : Type'} (f : type1467 _26617 _26627) (l2 : list _26627) : (term33 _26617 _26627 f l2) = (@ITLIST _26617 _26627 f l2).
Proof. exact (MK_COMB (@lem1129407 _26617 _26627 f) (@lem1129406 _26627 l2)). Qed.
Lemma lem1129409 {_26617 : Type'} (a : _26617) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1129410 {_26617 _26627 : Type'} (f : type1467 _26617 _26627) (l2 : list _26627) (a : _26617) : (term34 _26617 _26627 f l2 a) = (@ITLIST _26617 _26627 f l2 a).
Proof. exact (MK_COMB (@lem1129408 _26617 _26627 f l2) (@lem1129409 _26617 a)). Qed.
Lemma lem1129411 {_26617 : Type'} : (@eq _26617) = (@eq _26617).
Proof. exact (eq_refl (@eq _26617)). Qed.
Lemma lem1129412 {_26617 _26627 : Type'} (f : type1467 _26617 _26627) (l2 : list _26627) (a : _26617) : (term35 _26617 _26627 f l2 a) = (term36 _26617 _26627 f l2 a).
Proof. exact (MK_COMB (@lem1129411 _26617) (@lem1129410 _26617 _26627 f l2 a)). Qed.
Lemma lem1129414 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) (b : _25350) : (@ITLIST _25350 _25351 f (@nil _25351) b) = b.
Proof. exact (EQ_MP (@lem1102428 _25350 _25351 f b) (@lem1102427 _25350 _25351 f b)). Qed.
Lemma lem1129415 {_26617 _26627 : Type'} (f : type1467 _26617 _26627) (b : _26617) : (@ITLIST _26617 _26627 f (@nil _26627) b) = b.
Proof. exact (@lem1129414 _26617 _26627 f b). Qed.
Lemma lem1129416 {_26617 _26627 : Type'} (f : type1467 _26617 _26627) (l2 : list _26627) (a : _26617) : (term37 _26617 _26627 f l2 a) = (@ITLIST _26617 _26627 f l2 a).
Proof. exact (@lem1129415 _26617 _26627 f (@ITLIST _26617 _26627 f l2 a)). Qed.
Lemma lem1129417 {_26617 _26627 : Type'} (f : type1467 _26617 _26627) (l2 : list _26627) (a : _26617) : ((term34 _26617 _26627 f l2 a) = (term37 _26617 _26627 f l2 a)) = ((@ITLIST _26617 _26627 f l2 a) = (@ITLIST _26617 _26627 f l2 a)).
Proof. exact (MK_COMB (@lem1129412 _26617 _26627 f l2 a) (@lem1129416 _26617 _26627 f l2 a)). Qed.
Lemma lem1129419 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1129420 {_26617 : Type'} (x : _26617) : (x = x) = True.
Proof. exact (@lem1129419 _26617 x). Qed.
Lemma lem1129421 {_26617 _26627 : Type'} (f : type1467 _26617 _26627) (l2 : list _26627) (a : _26617) : ((@ITLIST _26617 _26627 f l2 a) = (@ITLIST _26617 _26627 f l2 a)) = True.
Proof. exact (@lem1129420 _26617 (@ITLIST _26617 _26627 f l2 a)). Qed.
Lemma lem1129422 {_26617 _26627 : Type'} (f : type1467 _26617 _26627) (l2 : list _26627) (a : _26617) : ((term34 _26617 _26627 f l2 a) = (term37 _26617 _26627 f l2 a)) = True.
Proof. exact (TRANS (@lem1129417 _26617 _26627 f l2 a) (@lem1129421 _26617 _26627 f l2 a)). Qed.
Lemma lem1129423 {_26617 _26627 : Type'} (f : type1467 _26617 _26627) (a : _26617) : (term38 _26617 _26627 f a) = (term39 _26627).
Proof. exact (fun_ext (fun l2 : list _26627 => @lem1129422 _26617 _26627 f l2 a)). Qed.
Lemma lem1129424 {_26627 : Type'} : (@all (list _26627)) = (@all (list _26627)).
Proof. exact (eq_refl (@all (list _26627))). Qed.
Lemma lem1129425 {_26617 _26627 : Type'} (f : type1467 _26617 _26627) (a : _26617) : (term4 _26617 _26627 f a) = (term40 _26627).
Proof. exact (MK_COMB (@lem1129424 _26627) (@lem1129423 _26617 _26627 f a)). Qed.
Lemma lem1129427 {A : Type'} (t : Prop) : (term41 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1129428 {_26627 : Type'} (t : Prop) : (term42 _26627 t) = t.
Proof. exact (@lem1129427 (list _26627) t). Qed.
Lemma lem1129429 {_26627 : Type'} : (term40 _26627) = True.
Proof. exact (@lem1129428 _26627 True). Qed.
Lemma lem1129430 {_26617 _26627 : Type'} (f : type1467 _26617 _26627) (a : _26617) : (term4 _26617 _26627 f a) = True.
Proof. exact (TRANS (@lem1129425 _26617 _26627 f a) (@lem1129429 _26627)). Qed.
Lemma lem1129431 {_26617 _26627 : Type'} (f : type1467 _26617 _26627) (a : _26617) : True = (term4 _26617 _26627 f a).
Proof. exact (SYM (@lem1129430 _26617 _26627 f a)). Qed.
Lemma lem1129432 {_26617 _26627 : Type'} (f : type1467 _26617 _26627) (a : _26617) : term4 _26617 _26627 f a.
Proof. exact (EQ_MP (@lem1129431 _26617 _26627 f a) (@lem0)). Qed.
Lemma lem1129433 {A : Type'} : term43 A.
Proof. exact (proj2 (@lem1095962 A)). Qed.
Lemma lem1129434 {A : Type'} (h : A) : term44 A h.
Proof. exact (@lem1129433 A h). Qed.
Lemma lem1129435 {A : Type'} (h : A) : (term44 A h) = (term45 A h).
Proof. exact (eq_refl (term44 A h)). Qed.
Lemma lem1129436 {A : Type'} (h : A) : term45 A h.
Proof. exact (EQ_MP (@lem1129435 A h) (@lem1129434 A h)). Qed.
Lemma lem1129437 {A : Type'} (h : A) (t : list A) : term46 A h t.
Proof. exact (@lem1129436 A h t). Qed.
Lemma lem1129438 {A : Type'} (h : A) (t : list A) : (term46 A h t) = (term47 A h t).
Proof. exact (eq_refl (term46 A h t)). Qed.
Lemma lem1129439 {A : Type'} (h : A) (t : list A) : term47 A h t.
Proof. exact (EQ_MP (@lem1129438 A h t) (@lem1129437 A h t)). Qed.
Lemma lem1129440 {A : Type'} (h : A) (t : list A) (l : list A) : term48 A h t l.
Proof. exact (@lem1129439 A h t l). Qed.
Lemma lem1129441 {A : Type'} (h : A) (t : list A) (l : list A) : (term48 A h t l) = ((term49 A h t l) = (term50 A h t l)).
Proof. exact (eq_refl (term48 A h t l)). Qed.
Lemma lem1129449 {_26617 _26627 : Type'} (l2 : list _26627) (t : list _26627) (f : type1467 _26617 _26627) (a : _26617) (h1 : term8 _26617 _26627 t f a) : term51 _26617 _26627 t f a l2.
Proof. exact (@lem1129380 _26617 _26627 t f a h1 l2). Qed.
Lemma lem1129450 {_26617 _26627 : Type'} (t : list _26627) (f : type1467 _26617 _26627) (l2 : list _26627) (a : _26617) : (term51 _26617 _26627 t f a l2) = ((term52 _26617 _26627 f t l2 a) = (term53 _26617 _26627 t f l2 a)).
Proof. exact (eq_refl (term51 _26617 _26627 t f a l2)). Qed.
Lemma lem1129459 {A : Type'} (h : A) (t : list A) (l : list A) : (term49 A h t l) = (term50 A h t l).
Proof. exact (EQ_MP (@lem1129441 A h t l) (@lem1129440 A h t l)). Qed.
Lemma lem1129460 {_26627 : Type'} (h : _26627) (t : list _26627) (l : list _26627) : (term49 _26627 h t l) = (term50 _26627 h t l).
Proof. exact (@lem1129459 _26627 h t l). Qed.
Lemma lem1129461 {_26627 : Type'} (h : _26627) (t : list _26627) (l2 : list _26627) : (term49 _26627 h t l2) = (term50 _26627 h t l2).
Proof. exact (@lem1129460 _26627 h t l2). Qed.
Lemma lem1129462 {_26617 _26627 : Type'} (f : type1467 _26617 _26627) : (@ITLIST _26617 _26627 f) = (@ITLIST _26617 _26627 f).
Proof. exact (eq_refl (@ITLIST _26617 _26627 f)). Qed.
Lemma lem1129463 {_26617 _26627 : Type'} (f : type1467 _26617 _26627) (h : _26627) (t : list _26627) (l2 : list _26627) : (term54 _26617 _26627 f h t l2) = (term55 _26617 _26627 f h t l2).
Proof. exact (MK_COMB (@lem1129462 _26617 _26627 f) (@lem1129461 _26627 h t l2)). Qed.
Lemma lem1129464 {_26617 : Type'} (a : _26617) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1129465 {_26617 _26627 : Type'} (f : type1467 _26617 _26627) (h : _26627) (t : list _26627) (l2 : list _26627) (a : _26617) : (term56 _26617 _26627 f h t l2 a) = (term57 _26617 _26627 f h t l2 a).
Proof. exact (MK_COMB (@lem1129463 _26617 _26627 f h t l2) (@lem1129464 _26617 a)). Qed.
Lemma lem1129467 {_25350 _25351 : Type'} (h : _25351) (f : type1467 _25350 _25351) (t : list _25351) (b : _25350) : (term58 _25350 _25351 f h t b) = (term59 _25350 _25351 h f t b).
Proof. exact (EQ_MP (@lem1102440 _25350 _25351 h f t b) (@lem1102439 _25350 _25351 h f t b)). Qed.
Lemma lem1129468 {_26617 _26627 : Type'} (h : _26627) (f : type1467 _26617 _26627) (t : list _26627) (b : _26617) : (term58 _26617 _26627 f h t b) = (term59 _26617 _26627 h f t b).
Proof. exact (@lem1129467 _26617 _26627 h f t b). Qed.
Lemma lem1129469 {_26617 _26627 : Type'} (h : _26627) (f : type1467 _26617 _26627) (t : list _26627) (l2 : list _26627) (a : _26617) : (term57 _26617 _26627 f h t l2 a) = (term60 _26617 _26627 h f t l2 a).
Proof. exact (@lem1129468 _26617 _26627 h f (@List.app _26627 t l2) a). Qed.
Lemma lem1129471 {_26617 _26627 : Type'} (l2 : list _26627) (t : list _26627) (f : type1467 _26617 _26627) (a : _26617) (h1 : term8 _26617 _26627 t f a) : (term52 _26617 _26627 f t l2 a) = (term53 _26617 _26627 t f l2 a).
Proof. exact (EQ_MP (@lem1129450 _26617 _26627 t f l2 a) (@lem1129449 _26617 _26627 l2 t f a h1)). Qed.
Lemma lem1129472 {_26617 _26627 : Type'} (l2 : list _26627) (t : list _26627) (f : type1467 _26617 _26627) (a : _26617) (h1 : term8 _26617 _26627 t f a) : (term52 _26617 _26627 f t l2 a) = (term53 _26617 _26627 t f l2 a).
Proof. exact (@lem1129471 _26617 _26627 l2 t f a h1). Qed.
Lemma lem1129473 {_26617 _26627 : Type'} (f : type1467 _26617 _26627) (h : _26627) : (f h) = (f h).
Proof. exact (eq_refl (f h)). Qed.
Lemma lem1129474 {_26617 _26627 : Type'} (h : _26627) (l2 : list _26627) (t : list _26627) (f : type1467 _26617 _26627) (a : _26617) (h1 : term8 _26617 _26627 t f a) : (term60 _26617 _26627 h f t l2 a) = (term61 _26617 _26627 h t f l2 a).
Proof. exact (MK_COMB (@lem1129473 _26617 _26627 f h) (@lem1129472 _26617 _26627 l2 t f a h1)). Qed.
Lemma lem1129475 {_26617 _26627 : Type'} (h : _26627) (l2 : list _26627) (t : list _26627) (f : type1467 _26617 _26627) (a : _26617) (h1 : term8 _26617 _26627 t f a) : (term57 _26617 _26627 f h t l2 a) = (term61 _26617 _26627 h t f l2 a).
Proof. exact (TRANS (@lem1129469 _26617 _26627 h f t l2 a) (@lem1129474 _26617 _26627 h l2 t f a h1)). Qed.
Lemma lem1129476 {_26617 _26627 : Type'} (h : _26627) (l2 : list _26627) (t : list _26627) (f : type1467 _26617 _26627) (a : _26617) (h1 : term8 _26617 _26627 t f a) : (term56 _26617 _26627 f h t l2 a) = (term61 _26617 _26627 h t f l2 a).
Proof. exact (TRANS (@lem1129465 _26617 _26627 f h t l2 a) (@lem1129475 _26617 _26627 h l2 t f a h1)). Qed.
Lemma lem1129477 {_26617 : Type'} : (@eq _26617) = (@eq _26617).
Proof. exact (eq_refl (@eq _26617)). Qed.
Lemma lem1129478 {_26617 _26627 : Type'} (h : _26627) (l2 : list _26627) (t : list _26627) (f : type1467 _26617 _26627) (a : _26617) (h1 : term8 _26617 _26627 t f a) : (term62 _26617 _26627 f h t l2 a) = (term63 _26617 _26627 h t f l2 a).
Proof. exact (MK_COMB (@lem1129477 _26617) (@lem1129476 _26617 _26627 h l2 t f a h1)). Qed.
Lemma lem1129480 {_25350 _25351 : Type'} (h : _25351) (f : type1467 _25350 _25351) (t : list _25351) (b : _25350) : (term58 _25350 _25351 f h t b) = (term59 _25350 _25351 h f t b).
Proof. exact (EQ_MP (@lem1102440 _25350 _25351 h f t b) (@lem1102439 _25350 _25351 h f t b)). Qed.
Lemma lem1129481 {_26617 _26627 : Type'} (h : _26627) (f : type1467 _26617 _26627) (t : list _26627) (b : _26617) : (term58 _26617 _26627 f h t b) = (term59 _26617 _26627 h f t b).
Proof. exact (@lem1129480 _26617 _26627 h f t b). Qed.
Lemma lem1129482 {_26617 _26627 : Type'} (h : _26627) (t : list _26627) (f : type1467 _26617 _26627) (l2 : list _26627) (a : _26617) : (term64 _26617 _26627 h t f l2 a) = (term61 _26617 _26627 h t f l2 a).
Proof. exact (@lem1129481 _26617 _26627 h f t (@ITLIST _26617 _26627 f l2 a)). Qed.
Lemma lem1129483 {_26617 _26627 : Type'} (h : _26627) (l2 : list _26627) (t : list _26627) (f : type1467 _26617 _26627) (a : _26617) (h1 : term8 _26617 _26627 t f a) : ((term56 _26617 _26627 f h t l2 a) = (term64 _26617 _26627 h t f l2 a)) = ((term61 _26617 _26627 h t f l2 a) = (term61 _26617 _26627 h t f l2 a)).
Proof. exact (MK_COMB (@lem1129478 _26617 _26627 h l2 t f a h1) (@lem1129482 _26617 _26627 h t f l2 a)). Qed.
Lemma lem1129485 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1129486 {_26617 : Type'} (x : _26617) : (x = x) = True.
Proof. exact (@lem1129485 _26617 x). Qed.
Lemma lem1129487 {_26617 _26627 : Type'} (h : _26627) (t : list _26627) (f : type1467 _26617 _26627) (l2 : list _26627) (a : _26617) : ((term61 _26617 _26627 h t f l2 a) = (term61 _26617 _26627 h t f l2 a)) = True.
Proof. exact (@lem1129486 _26617 (term61 _26617 _26627 h t f l2 a)). Qed.
Lemma lem1129488 {_26617 _26627 : Type'} (h : _26627) (l2 : list _26627) (t : list _26627) (f : type1467 _26617 _26627) (a : _26617) (h1 : term8 _26617 _26627 t f a) : ((term56 _26617 _26627 f h t l2 a) = (term64 _26617 _26627 h t f l2 a)) = True.
Proof. exact (TRANS (@lem1129483 _26617 _26627 h l2 t f a h1) (@lem1129487 _26617 _26627 h t f l2 a)). Qed.
Lemma lem1129489 {_26617 _26627 : Type'} (h : _26627) (t : list _26627) (f : type1467 _26617 _26627) (a : _26617) (h1 : term8 _26617 _26627 t f a) : (term65 _26617 _26627 h t f a) = (term39 _26627).
Proof. exact (fun_ext (fun l2 : list _26627 => @lem1129488 _26617 _26627 h l2 t f a h1)). Qed.
Lemma lem1129490 {_26627 : Type'} : (@all (list _26627)) = (@all (list _26627)).
Proof. exact (eq_refl (@all (list _26627))). Qed.
Lemma lem1129491 {_26617 _26627 : Type'} (h : _26627) (t : list _26627) (f : type1467 _26617 _26627) (a : _26617) (h1 : term8 _26617 _26627 t f a) : (term12 _26617 _26627 h t f a) = (term40 _26627).
Proof. exact (MK_COMB (@lem1129490 _26627) (@lem1129489 _26617 _26627 h t f a h1)). Qed.
Lemma lem1129493 {A : Type'} (t : Prop) : (term41 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1129494 {_26627 : Type'} (t : Prop) : (term42 _26627 t) = t.
Proof. exact (@lem1129493 (list _26627) t). Qed.
Lemma lem1129495 {_26627 : Type'} : (term40 _26627) = True.
Proof. exact (@lem1129494 _26627 True). Qed.
Lemma lem1129496 {_26617 _26627 : Type'} (h : _26627) (t : list _26627) (f : type1467 _26617 _26627) (a : _26617) (h1 : term8 _26617 _26627 t f a) : (term12 _26617 _26627 h t f a) = True.
Proof. exact (TRANS (@lem1129491 _26617 _26627 h t f a h1) (@lem1129495 _26627)). Qed.
Lemma lem1129497 {_26617 _26627 : Type'} (h : _26627) (t : list _26627) (f : type1467 _26617 _26627) (a : _26617) (h1 : term8 _26617 _26627 t f a) : True = (term12 _26617 _26627 h t f a).
Proof. exact (SYM (@lem1129496 _26617 _26627 h t f a h1)). Qed.
Lemma lem1129498 {_26617 _26627 : Type'} (h : _26627) (t : list _26627) (f : type1467 _26617 _26627) (a : _26617) (h1 : term8 _26617 _26627 t f a) : term12 _26617 _26627 h t f a.
Proof. exact (EQ_MP (@lem1129497 _26617 _26627 h t f a h1) (@lem0)). Qed.
Lemma lem1129499 {_26617 _26627 : Type'} (h : _26627) (t : list _26627) (f : type1467 _26617 _26627) (a : _26617) : term14 _26617 _26627 h t f a.
Proof. exact (fun h0 : term8 _26617 _26627 t f a => @lem1129498 _26617 _26627 h t f a h0). Qed.
Lemma lem1129504 {_26617 _26627 : Type'} (h : _26627) (f : type1467 _26617 _26627) (a : _26617) : term18 _26617 _26627 h f a.
Proof. exact (fun t : list _26627 => @lem1129499 _26617 _26627 h t f a). Qed.
Lemma lem1129509 {_26617 _26627 : Type'} (f : type1467 _26617 _26627) (a : _26617) : term22 _26617 _26627 f a.
Proof. exact (fun h : _26627 => @lem1129504 _26617 _26627 h f a). Qed.
Lemma lem1129510 {_26617 _26627 : Type'} (f : type1467 _26617 _26627) (a : _26617) : term24 _26617 _26627 f a.
Proof. exact (conj (@lem1129432 _26617 _26627 f a) (@lem1129509 _26617 _26627 f a)). Qed.
Lemma lem1129511 {_26617 _26627 : Type'} (f : type1467 _26617 _26627) (a : _26617) : term29 _26617 _26627 f a.
Proof. exact (@lem1129379 _26617 _26627 f a (@lem1129510 _26617 _26627 f a)). Qed.
Lemma lem1129516 {_26617 _26627 : Type'} (f : type1467 _26617 _26627) : term66 _26617 _26627 f.
Proof. exact (fun a : _26617 => @lem1129511 _26617 _26627 f a). Qed.
Lemma lem1129521 {_26617 _26627 : Type'} : term67 _26617 _26627.
Proof. exact (fun f : type1467 _26617 _26627 => @lem1129516 _26617 _26627 f). Qed.
