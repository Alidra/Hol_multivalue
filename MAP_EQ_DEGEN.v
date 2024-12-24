Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MAP_EQ_DEGEN_term_abbrevs.
Require Import CONS_11_spec.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1097797_spec.
Require Import thm1100834_spec.
Require Import thm1100835_spec.
Require Import thm1100843_spec.
Require Import thm1100844_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Lemma lem1128392 {A : Type'} (h1' : A) : term0 A h1'.
Proof. exact (@lem1113436 A h1'). Qed.
Lemma lem1128393 {A : Type'} (h1' : A) : (term0 A h1') = (term1 A h1').
Proof. exact (eq_refl (term0 A h1')). Qed.
Lemma lem1128394 {A : Type'} (h1' : A) : term1 A h1'.
Proof. exact (EQ_MP (@lem1128393 A h1') (@lem1128392 A h1')). Qed.
Lemma lem1128395 {A : Type'} (h1' : A) (h2' : A) : term2 A h1' h2'.
Proof. exact (@lem1128394 A h1' h2'). Qed.
Lemma lem1128396 {A : Type'} (h1' : A) (h2' : A) : (term2 A h1' h2') = (term3 A h1' h2').
Proof. exact (eq_refl (term2 A h1' h2')). Qed.
Lemma lem1128397 {A : Type'} (h1' : A) (h2' : A) : term3 A h1' h2'.
Proof. exact (EQ_MP (@lem1128396 A h1' h2') (@lem1128395 A h1' h2')). Qed.
Lemma lem1128398 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) : term4 A h1' h2' t1.
Proof. exact (@lem1128397 A h1' h2' t1). Qed.
Lemma lem1128399 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) : (term4 A h1' h2' t1) = (term5 A h1' h2' t1).
Proof. exact (eq_refl (term4 A h1' h2' t1)). Qed.
Lemma lem1128400 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) : term5 A h1' h2' t1.
Proof. exact (EQ_MP (@lem1128399 A h1' h2' t1) (@lem1128398 A h1' h2' t1)). Qed.
Lemma lem1128401 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) (t2 : list A) : term6 A h1' h2' t1 t2.
Proof. exact (@lem1128400 A h1' h2' t1 t2). Qed.
Lemma lem1128402 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) (t2 : list A) : (term6 A h1' h2' t1 t2) = (((@cons A h1' t1) = (@cons A h2' t2)) = (term7 A h1' h2' t1 t2)).
Proof. exact (eq_refl (term6 A h1' h2' t1 t2)). Qed.
Lemma lem1128404 {A B : Type'} : term8 A B.
Proof. exact (proj2 (@lem1097797 A B)). Qed.
Lemma lem1128405 {A B : Type'} (f : A -> B) : term9 A B f.
Proof. exact (@lem1128404 A B f). Qed.
Lemma lem1128406 {A B : Type'} (f : A -> B) : (term9 A B f) = (term10 A B f).
Proof. exact (eq_refl (term9 A B f)). Qed.
Lemma lem1128407 {A B : Type'} (f : A -> B) : term10 A B f.
Proof. exact (EQ_MP (@lem1128406 A B f) (@lem1128405 A B f)). Qed.
Lemma lem1128408 {A B : Type'} (f : A -> B) (h : A) : term11 A B f h.
Proof. exact (@lem1128407 A B f h). Qed.
Lemma lem1128409 {A B : Type'} (h : A) (f : A -> B) : (term11 A B f h) = (term12 A B h f).
Proof. exact (eq_refl (term11 A B f h)). Qed.
Lemma lem1128410 {A B : Type'} (h : A) (f : A -> B) : term12 A B h f.
Proof. exact (EQ_MP (@lem1128409 A B h f) (@lem1128408 A B f h)). Qed.
Lemma lem1128411 {A B : Type'} (h : A) (f : A -> B) (t : list A) : term13 A B h f t.
Proof. exact (@lem1128410 A B h f t). Qed.
Lemma lem1128412 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term13 A B h f t) = ((term14 A B f h t) = (term15 A B h f t)).
Proof. exact (eq_refl (term13 A B h f t)). Qed.
Lemma lem1128414 {A B : Type'} : term16 A B.
Proof. exact (proj1 (@lem1097797 A B)). Qed.
Lemma lem1128415 {A B : Type'} (f : A -> B) : term17 A B f.
Proof. exact (@lem1128414 A B f). Qed.
Lemma lem1128416 {A B : Type'} (f : A -> B) : (term17 A B f) = ((@List.map A B f (@nil A)) = (@nil B)).
Proof. exact (eq_refl (term17 A B f)). Qed.
Lemma lem1128421 {A : Type'} (P : type1143 A) : term18 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1128422 {_26546 : Type'} (P : type1143 _26546) : term18 _26546 P.
Proof. exact (@lem1128421 _26546 P). Qed.
Lemma lem1128423 {_26546 : Type'} : term19 _26546.
Proof. exact (@lem1128422 _26546 (term20 _26546)). Qed.
Lemma lem1128424 {_26546 : Type'} : (term21 _26546) = (term22 _26546).
Proof. exact (eq_refl (term21 _26546)). Qed.
Lemma lem1128425 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1128426 {_26546 : Type'} : (term23 _26546) = (term24 _26546).
Proof. exact (MK_COMB (@lem1128425) (@lem1128424 _26546)). Qed.
Lemma lem1128427 {_26546 : Type'} (t : list _26546) : (term25 _26546 t) = (term26 _26546 t).
Proof. exact (eq_refl (term25 _26546 t)). Qed.
Lemma lem1128428 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1128429 {_26546 : Type'} (t : list _26546) : (term27 _26546 t) = (term28 _26546 t).
Proof. exact (MK_COMB (@lem1128428) (@lem1128427 _26546 t)). Qed.
Lemma lem1128430 {_26546 : Type'} (h : _26546) (t : list _26546) : (term29 _26546 h t) = (term30 _26546 h t).
Proof. exact (eq_refl (term29 _26546 h t)). Qed.
Lemma lem1128431 {_26546 : Type'} (h : _26546) (t : list _26546) : (term31 _26546 h t) = (term32 _26546 h t).
Proof. exact (MK_COMB (@lem1128429 _26546 t) (@lem1128430 _26546 h t)). Qed.
Lemma lem1128432 {_26546 : Type'} (h : _26546) : (term33 _26546 h) = (term34 _26546 h).
Proof. exact (fun_ext (fun t : list _26546 => @lem1128431 _26546 h t)). Qed.
Lemma lem1128433 {_26546 : Type'} : (@all (list _26546)) = (@all (list _26546)).
Proof. exact (eq_refl (@all (list _26546))). Qed.
Lemma lem1128434 {_26546 : Type'} (h : _26546) : (term35 _26546 h) = (term36 _26546 h).
Proof. exact (MK_COMB (@lem1128433 _26546) (@lem1128432 _26546 h)). Qed.
Lemma lem1128435 {_26546 : Type'} : (term37 _26546) = (term38 _26546).
Proof. exact (fun_ext (fun h : _26546 => @lem1128434 _26546 h)). Qed.
Lemma lem1128436 {_26546 : Type'} : (@all _26546) = (@all _26546).
Proof. exact (eq_refl (@all _26546)). Qed.
Lemma lem1128437 {_26546 : Type'} : (term39 _26546) = (term40 _26546).
Proof. exact (MK_COMB (@lem1128436 _26546) (@lem1128435 _26546)). Qed.
Lemma lem1128438 {_26546 : Type'} : (term41 _26546) = (term42 _26546).
Proof. exact (MK_COMB (@lem1128426 _26546) (@lem1128437 _26546)). Qed.
Lemma lem1128439 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1128440 {_26546 : Type'} : (term43 _26546) = (term44 _26546).
Proof. exact (MK_COMB (@lem1128439) (@lem1128438 _26546)). Qed.
Lemma lem1128441 {_26546 : Type'} (l : list _26546) : (term25 _26546 l) = (term26 _26546 l).
Proof. exact (eq_refl (term25 _26546 l)). Qed.
Lemma lem1128442 {_26546 : Type'} : (term45 _26546) = (term20 _26546).
Proof. exact (fun_ext (fun l : list _26546 => @lem1128441 _26546 l)). Qed.
Lemma lem1128443 {_26546 : Type'} : (@all (list _26546)) = (@all (list _26546)).
Proof. exact (eq_refl (@all (list _26546))). Qed.
Lemma lem1128444 {_26546 : Type'} : (term46 _26546) = (term47 _26546).
Proof. exact (MK_COMB (@lem1128443 _26546) (@lem1128442 _26546)). Qed.
Lemma lem1128445 {_26546 : Type'} : (term19 _26546) = (term48 _26546).
Proof. exact (MK_COMB (@lem1128440 _26546) (@lem1128444 _26546)). Qed.
Lemma lem1128446 {_26546 : Type'} : term48 _26546.
Proof. exact (EQ_MP (@lem1128445 _26546) (@lem1128423 _26546)). Qed.
Lemma lem1128447 {_26546 : Type'} (t : list _26546) (h1 : term26 _26546 t) : term26 _26546 t.
Proof. exact (h1). Qed.
Lemma lem1128455 {_25307 : Type'} (P : _25307 -> Prop) : (@List.Forall _25307 P (@nil _25307)) = True.
Proof. exact (EQ_MP (@lem1100835 _25307 P) (@lem1100834 _25307 P)). Qed.
Lemma lem1128456 {_26546 : Type'} (P : _26546 -> Prop) : (@List.Forall _26546 P (@nil _26546)) = True.
Proof. exact (@lem1128455 _26546 P). Qed.
Lemma lem1128457 {_26546 : Type'} (f : _26546 -> _26546) : (term49 _26546 f) = True.
Proof. exact (@lem1128456 _26546 (term50 _26546 f)). Qed.
Lemma lem1128458 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1128459 {_26546 : Type'} (f : _26546 -> _26546) : (term51 _26546 f) = (imp True).
Proof. exact (MK_COMB (@lem1128458) (@lem1128457 _26546 f)). Qed.
Lemma lem1128463 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (@nil B).
Proof. exact (EQ_MP (@lem1128416 A B f) (@lem1128415 A B f)). Qed.
Lemma lem1128464 {_26546 : Type'} (f : _26546 -> _26546) : (@List.map _26546 _26546 f (@nil _26546)) = (@nil _26546).
Proof. exact (@lem1128463 _26546 _26546 f). Qed.
Lemma lem1128465 {_26546 : Type'} : (@eq (list _26546)) = (@eq (list _26546)).
Proof. exact (eq_refl (@eq (list _26546))). Qed.
Lemma lem1128466 {_26546 : Type'} (f : _26546 -> _26546) : (term52 _26546 f) = (@eq (list _26546) (@nil _26546)).
Proof. exact (MK_COMB (@lem1128465 _26546) (@lem1128464 _26546 f)). Qed.
Lemma lem1128467 {_26546 : Type'} : (@nil _26546) = (@nil _26546).
Proof. exact (eq_refl (@nil _26546)). Qed.
Lemma lem1128468 {_26546 : Type'} (f : _26546 -> _26546) : ((@List.map _26546 _26546 f (@nil _26546)) = (@nil _26546)) = ((@nil _26546) = (@nil _26546)).
Proof. exact (MK_COMB (@lem1128466 _26546 f) (@lem1128467 _26546)). Qed.
Lemma lem1128470 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1128471 {_26546 : Type'} (x : list _26546) : (x = x) = True.
Proof. exact (@lem1128470 (list _26546) x). Qed.
Lemma lem1128472 {_26546 : Type'} : ((@nil _26546) = (@nil _26546)) = True.
Proof. exact (@lem1128471 _26546 (@nil _26546)). Qed.
Lemma lem1128473 {_26546 : Type'} (f : _26546 -> _26546) : ((@List.map _26546 _26546 f (@nil _26546)) = (@nil _26546)) = True.
Proof. exact (TRANS (@lem1128468 _26546 f) (@lem1128472 _26546)). Qed.
Lemma lem1128474 {_26546 : Type'} (f : _26546 -> _26546) : (term53 _26546 f) = (True -> True).
Proof. exact (MK_COMB (@lem1128459 _26546 f) (@lem1128473 _26546 f)). Qed.
Lemma lem1128476 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1128477 : (True -> True) = True.
Proof. exact (@lem1128476 True). Qed.
Lemma lem1128478 {_26546 : Type'} (f : _26546 -> _26546) : (term53 _26546 f) = True.
Proof. exact (TRANS (@lem1128474 _26546 f) (@lem1128477)). Qed.
Lemma lem1128479 {_26546 : Type'} : (term54 _26546) = (term55 _26546).
Proof. exact (fun_ext (fun f : _26546 -> _26546 => @lem1128478 _26546 f)). Qed.
Lemma lem1128480 {_26546 : Type'} : (@all (_26546 -> _26546)) = (@all (_26546 -> _26546)).
Proof. exact (eq_refl (@all (_26546 -> _26546))). Qed.
Lemma lem1128481 {_26546 : Type'} : (term22 _26546) = (term56 _26546).
Proof. exact (MK_COMB (@lem1128480 _26546) (@lem1128479 _26546)). Qed.
Lemma lem1128483 {A : Type'} (t : Prop) : (term57 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1128484 {_26546 : Type'} (t : Prop) : (term58 _26546 t) = t.
Proof. exact (@lem1128483 (_26546 -> _26546) t). Qed.
Lemma lem1128485 {_26546 : Type'} : (term56 _26546) = True.
Proof. exact (@lem1128484 _26546 True). Qed.
Lemma lem1128486 {_26546 : Type'} : (term22 _26546) = True.
Proof. exact (TRANS (@lem1128481 _26546) (@lem1128485 _26546)). Qed.
Lemma lem1128487 {_26546 : Type'} : True = (term22 _26546).
Proof. exact (SYM (@lem1128486 _26546)). Qed.
Lemma lem1128488 {_26546 : Type'} : term22 _26546.
Proof. exact (EQ_MP (@lem1128487 _26546) (@lem0)). Qed.
Lemma lem1128496 {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) (t : list _25307) : (term59 _25307 P h t) = (term60 _25307 h P t).
Proof. exact (EQ_MP (@lem1100844 _25307 h P t) (@lem1100843 _25307 h P t)). Qed.
Lemma lem1128497 {_26546 : Type'} (h : _26546) (P : _26546 -> Prop) (t : list _26546) : (term59 _26546 P h t) = (term60 _26546 h P t).
Proof. exact (@lem1128496 _26546 h P t). Qed.
Lemma lem1128498 {_26546 : Type'} (h : _26546) (f : _26546 -> _26546) (t : list _26546) : (term61 _26546 f h t) = (term62 _26546 h f t).
Proof. exact (@lem1128497 _26546 h (term50 _26546 f) t). Qed.
Lemma lem1128502 {A B : Type'} (f : A -> B) (y : A) : (term63 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1128503 {_26546 : Type'} (f : _26546 -> Prop) (y : _26546) : (term64 _26546 f y) = (f y).
Proof. exact (@lem1128502 _26546 Prop f y). Qed.
Lemma lem1128504 {_26546 : Type'} (f : _26546 -> _26546) (h : _26546) : (term65 _26546 f h) = (term66 _26546 f h).
Proof. exact (@lem1128503 _26546 (term50 _26546 f) h). Qed.
Lemma lem1128505 {_26546 : Type'} (f : _26546 -> _26546) (x : _26546) : (term66 _26546 f x) = ((f x) = x).
Proof. exact (eq_refl (term66 _26546 f x)). Qed.
Lemma lem1128506 {_26546 : Type'} (f : _26546 -> _26546) : (term67 _26546 f) = (term50 _26546 f).
Proof. exact (fun_ext (fun x : _26546 => @lem1128505 _26546 f x)). Qed.
Lemma lem1128507 {_26546 : Type'} (h : _26546) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1128508 {_26546 : Type'} (f : _26546 -> _26546) (h : _26546) : (term65 _26546 f h) = (term66 _26546 f h).
Proof. exact (MK_COMB (@lem1128506 _26546 f) (@lem1128507 _26546 h)). Qed.
Lemma lem1128509 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1128510 {_26546 : Type'} (f : _26546 -> _26546) (h : _26546) : (term68 _26546 f h) = (term69 _26546 f h).
Proof. exact (MK_COMB (@lem1128509) (@lem1128508 _26546 f h)). Qed.
Lemma lem1128511 {_26546 : Type'} (f : _26546 -> _26546) (h : _26546) : (term66 _26546 f h) = ((f h) = h).
Proof. exact (eq_refl (term66 _26546 f h)). Qed.
Lemma lem1128512 {_26546 : Type'} (f : _26546 -> _26546) (h : _26546) : ((term65 _26546 f h) = (term66 _26546 f h)) = ((term66 _26546 f h) = ((f h) = h)).
Proof. exact (MK_COMB (@lem1128510 _26546 f h) (@lem1128511 _26546 f h)). Qed.
Lemma lem1128513 {_26546 : Type'} (f : _26546 -> _26546) (h : _26546) : (term66 _26546 f h) = ((f h) = h).
Proof. exact (EQ_MP (@lem1128512 _26546 f h) (@lem1128504 _26546 f h)). Qed.
Lemma lem1128516 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1128517 {_26546 : Type'} (f : _26546 -> _26546) (h : _26546) : (term70 _26546 f h) = (term71 _26546 f h).
Proof. exact (MK_COMB (@lem1128516) (@lem1128513 _26546 f h)). Qed.
Lemma lem1128520 {_26546 : Type'} (f : _26546 -> _26546) (t : list _26546) : (term72 _26546 f t) = (term72 _26546 f t).
Proof. exact (eq_refl (term72 _26546 f t)). Qed.
Lemma lem1128521 {_26546 : Type'} (h : _26546) (f : _26546 -> _26546) (t : list _26546) : (term62 _26546 h f t) = (term73 _26546 h f t).
Proof. exact (MK_COMB (@lem1128517 _26546 f h) (@lem1128520 _26546 f t)). Qed.
Lemma lem1128524 {_26546 : Type'} (h : _26546) (f : _26546 -> _26546) (t : list _26546) : (term61 _26546 f h t) = (term73 _26546 h f t).
Proof. exact (TRANS (@lem1128498 _26546 h f t) (@lem1128521 _26546 h f t)). Qed.
Lemma lem1128525 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1128526 {_26546 : Type'} (h : _26546) (f : _26546 -> _26546) (t : list _26546) : (term74 _26546 f h t) = (term75 _26546 h f t).
Proof. exact (MK_COMB (@lem1128525) (@lem1128524 _26546 h f t)). Qed.
Lemma lem1128530 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term14 A B f h t) = (term15 A B h f t).
Proof. exact (EQ_MP (@lem1128412 A B h f t) (@lem1128411 A B h f t)). Qed.
Lemma lem1128531 {_26546 : Type'} (h : _26546) (f : _26546 -> _26546) (t : list _26546) : (term76 _26546 f h t) = (term77 _26546 h f t).
Proof. exact (@lem1128530 _26546 _26546 h f t). Qed.
Lemma lem1128532 {_26546 : Type'} : (@eq (list _26546)) = (@eq (list _26546)).
Proof. exact (eq_refl (@eq (list _26546))). Qed.
Lemma lem1128533 {_26546 : Type'} (h : _26546) (f : _26546 -> _26546) (t : list _26546) : (term78 _26546 f h t) = (term79 _26546 h f t).
Proof. exact (MK_COMB (@lem1128532 _26546) (@lem1128531 _26546 h f t)). Qed.
Lemma lem1128534 {_26546 : Type'} (h : _26546) (t : list _26546) : (@cons _26546 h t) = (@cons _26546 h t).
Proof. exact (eq_refl (@cons _26546 h t)). Qed.
Lemma lem1128535 {_26546 : Type'} (f : _26546 -> _26546) (h : _26546) (t : list _26546) : ((term76 _26546 f h t) = (@cons _26546 h t)) = ((term77 _26546 h f t) = (@cons _26546 h t)).
Proof. exact (MK_COMB (@lem1128533 _26546 h f t) (@lem1128534 _26546 h t)). Qed.
Lemma lem1128537 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) (t2 : list A) : ((@cons A h1' t1) = (@cons A h2' t2)) = (term7 A h1' h2' t1 t2).
Proof. exact (EQ_MP (@lem1128402 A h1' h2' t1 t2) (@lem1128401 A h1' h2' t1 t2)). Qed.
Lemma lem1128538 {_26546 : Type'} (h1' : _26546) (h2' : _26546) (t1 : list _26546) (t2 : list _26546) : ((@cons _26546 h1' t1) = (@cons _26546 h2' t2)) = (term7 _26546 h1' h2' t1 t2).
Proof. exact (@lem1128537 _26546 h1' h2' t1 t2). Qed.
Lemma lem1128539 {_26546 : Type'} (h : _26546) (f : _26546 -> _26546) (t : list _26546) : ((term77 _26546 h f t) = (@cons _26546 h t)) = (term80 _26546 h f t).
Proof. exact (@lem1128538 _26546 (f h) h (@List.map _26546 _26546 f t) t). Qed.
Lemma lem1128546 {_26546 : Type'} (h : _26546) (f : _26546 -> _26546) (t : list _26546) : ((term76 _26546 f h t) = (@cons _26546 h t)) = (term80 _26546 h f t).
Proof. exact (TRANS (@lem1128535 _26546 f h t) (@lem1128539 _26546 h f t)). Qed.
Lemma lem1128547 {_26546 : Type'} (h : _26546) (f : _26546 -> _26546) (t : list _26546) : (term81 _26546 f h t) = (term82 _26546 h f t).
Proof. exact (MK_COMB (@lem1128526 _26546 h f t) (@lem1128546 _26546 h f t)). Qed.
Lemma lem1128550 {_26546 : Type'} (h : _26546) (t : list _26546) : (term83 _26546 h t) = (term84 _26546 h t).
Proof. exact (fun_ext (fun f : _26546 -> _26546 => @lem1128547 _26546 h f t)). Qed.
Lemma lem1128551 {_26546 : Type'} : (@all (_26546 -> _26546)) = (@all (_26546 -> _26546)).
Proof. exact (eq_refl (@all (_26546 -> _26546))). Qed.
Lemma lem1128552 {_26546 : Type'} (h : _26546) (t : list _26546) : (term30 _26546 h t) = (term85 _26546 h t).
Proof. exact (MK_COMB (@lem1128551 _26546) (@lem1128550 _26546 h t)). Qed.
Lemma lem1128557 {_26546 : Type'} (h : _26546) (t : list _26546) : (term85 _26546 h t) = (term30 _26546 h t).
Proof. exact (SYM (@lem1128552 _26546 h t)). Qed.
Lemma lem1128558 {_26546 : Type'} (h : _26546) (f : _26546 -> _26546) (t : list _26546) (h1 : term73 _26546 h f t) : term73 _26546 h f t.
Proof. exact (h1). Qed.
Lemma lem1128559 {_26546 : Type'} (f : _26546 -> _26546) (t : list _26546) (h1 : term72 _26546 f t) : term72 _26546 f t.
Proof. exact (h1). Qed.
Lemma lem1128560 {_26546 : Type'} (f : _26546 -> _26546) (h : _26546) (h1 : (f h) = h) : (f h) = h.
Proof. exact (h1). Qed.
Lemma lem1128571 {_26546 : Type'} (f : _26546 -> _26546) (h : _26546) (h1 : (f h) = h) : (f h) = h.
Proof. exact (h1). Qed.
Lemma lem1128572 {_26546 : Type'} : (@eq _26546) = (@eq _26546).
Proof. exact (eq_refl (@eq _26546)). Qed.
Lemma lem1128573 {_26546 : Type'} (f : _26546 -> _26546) (h : _26546) (h1 : (f h) = h) : (term86 _26546 f h) = (@eq _26546 h).
Proof. exact (MK_COMB (@lem1128572 _26546) (@lem1128571 _26546 f h h1)). Qed.
Lemma lem1128574 {_26546 : Type'} (h : _26546) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1128575 {_26546 : Type'} (f : _26546 -> _26546) (h : _26546) (h1 : (f h) = h) : ((f h) = h) = (h = h).
Proof. exact (MK_COMB (@lem1128573 _26546 f h h1) (@lem1128574 _26546 h)). Qed.
Lemma lem1128577 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1128578 {_26546 : Type'} (x : _26546) : (x = x) = True.
Proof. exact (@lem1128577 _26546 x). Qed.
Lemma lem1128579 {_26546 : Type'} (h : _26546) : (h = h) = True.
Proof. exact (@lem1128578 _26546 h). Qed.
Lemma lem1128580 {_26546 : Type'} (f : _26546 -> _26546) (h : _26546) (h1 : (f h) = h) : ((f h) = h) = True.
Proof. exact (TRANS (@lem1128575 _26546 f h h1) (@lem1128579 _26546 h)). Qed.
Lemma lem1128581 {_26546 : Type'} (f : _26546 -> _26546) (h : _26546) (h1 : (f h) = h) : True = ((f h) = h).
Proof. exact (SYM (@lem1128580 _26546 f h h1)). Qed.
Lemma lem1128582 {_26546 : Type'} (f : _26546 -> _26546) (h : _26546) (h1 : (f h) = h) : (f h) = h.
Proof. exact (EQ_MP (@lem1128581 _26546 f h h1) (@lem0)). Qed.
Lemma lem1128594 {_26546 : Type'} (t : list _26546) (h1 : term26 _26546 t) : term26 _26546 t.
Proof. exact (h1). Qed.
Lemma lem1128595 {_26546 : Type'} (f : _26546 -> _26546) (t : list _26546) (h1 : term26 _26546 t) : term87 _26546 t f.
Proof. exact (@lem1128594 _26546 t h1 f). Qed.
Lemma lem1128596 {_26546 : Type'} (f : _26546 -> _26546) (t : list _26546) : (term87 _26546 t f) = (term88 _26546 f t).
Proof. exact (eq_refl (term87 _26546 t f)). Qed.
Lemma lem1128597 {_26546 : Type'} (f : _26546 -> _26546) (t : list _26546) (h1 : term26 _26546 t) : term88 _26546 f t.
Proof. exact (EQ_MP (@lem1128596 _26546 f t) (@lem1128595 _26546 f t h1)). Qed.
Lemma lem1128598 {_26546 : Type'} (f : _26546 -> _26546) (t : list _26546) (h1 : term72 _26546 f t) : term72 _26546 f t.
Proof. exact (h1). Qed.
Lemma lem1128599 {_26546 : Type'} (f : _26546 -> _26546) (t : list _26546) (h1 : term26 _26546 t) (h2 : term72 _26546 f t) : (@List.map _26546 _26546 f t) = t.
Proof. exact (@lem1128597 _26546 f t h1 (@lem1128598 _26546 f t h2)). Qed.
Lemma lem1128600 {_26546 : Type'} (f : _26546 -> _26546) (t : list _26546) (h1 : term72 _26546 f t) : term89 _26546 f t.
Proof. exact (fun h0 : term26 _26546 t => @lem1128599 _26546 f t h0 h1). Qed.
Lemma lem1128601 {_26546 : Type'} (t : list _26546) (h1 : term26 _26546 t) : term26 _26546 t.
Proof. exact (h1). Qed.
Lemma lem1128602 {_26546 : Type'} (f : _26546 -> _26546) (t : list _26546) (h1 : term26 _26546 t) (h2 : term72 _26546 f t) : (@List.map _26546 _26546 f t) = t.
Proof. exact (@lem1128600 _26546 f t h2 (@lem1128601 _26546 t h1)). Qed.
Lemma lem1128603 {_26546 : Type'} (f : _26546 -> _26546) (t : list _26546) (h1 : term26 _26546 t) : term88 _26546 f t.
Proof. exact (fun h0 : term72 _26546 f t => @lem1128602 _26546 f t h1 h0). Qed.
Lemma lem1128604 {_26546 : Type'} (t : list _26546) (h1 : term26 _26546 t) : term26 _26546 t.
Proof. exact (fun f : _26546 -> _26546 => @lem1128603 _26546 f t h1). Qed.
Lemma lem1128605 {_26546 : Type'} (t : list _26546) : term90 _26546 t.
Proof. exact (fun h0 : term26 _26546 t => @lem1128604 _26546 t h0). Qed.
Lemma lem1128606 {_26546 : Type'} (t : list _26546) (h1 : term26 _26546 t) : term26 _26546 t.
Proof. exact (@lem1128605 _26546 t (@lem1128447 _26546 t h1)). Qed.
Lemma lem1128607 {_26546 : Type'} (f : _26546 -> _26546) (t : list _26546) (h1 : term26 _26546 t) : term87 _26546 t f.
Proof. exact (@lem1128606 _26546 t h1 f). Qed.
Lemma lem1128608 {_26546 : Type'} (f : _26546 -> _26546) (t : list _26546) : (term87 _26546 t f) = (term88 _26546 f t).
Proof. exact (eq_refl (term87 _26546 t f)). Qed.
Lemma lem1128611 {_26546 : Type'} (f : _26546 -> _26546) (t : list _26546) (h1 : term26 _26546 t) : term88 _26546 f t.
Proof. exact (EQ_MP (@lem1128608 _26546 f t) (@lem1128607 _26546 f t h1)). Qed.
Lemma lem1128612 {_26546 : Type'} (f : _26546 -> _26546) (t : list _26546) (h1 : term26 _26546 t) : term88 _26546 f t.
Proof. exact (@lem1128611 _26546 f t h1). Qed.
Lemma lem1128618 {_26546 : Type'} (f : _26546 -> _26546) (t : list _26546) : (term72 _26546 f t) = ((term72 _26546 f t) = True).
Proof. exact (@lem7 (term72 _26546 f t)). Qed.
Lemma lem1128621 {_26546 : Type'} (f : _26546 -> _26546) (t : list _26546) (h1 : term72 _26546 f t) : (term72 _26546 f t) = True.
Proof. exact (EQ_MP (@lem1128618 _26546 f t) (@lem1128559 _26546 f t h1)). Qed.
Lemma lem1128622 {_26546 : Type'} (f : _26546 -> _26546) (t : list _26546) (h1 : term72 _26546 f t) : (term72 _26546 f t) = True.
Proof. exact (@lem1128621 _26546 f t h1). Qed.
Lemma lem1128623 {_26546 : Type'} (f : _26546 -> _26546) (t : list _26546) (h1 : term72 _26546 f t) : True = (term72 _26546 f t).
Proof. exact (SYM (@lem1128622 _26546 f t h1)). Qed.
Lemma lem1128624 {_26546 : Type'} (f : _26546 -> _26546) (t : list _26546) (h1 : term72 _26546 f t) : term72 _26546 f t.
Proof. exact (EQ_MP (@lem1128623 _26546 f t h1) (@lem0)). Qed.
Lemma lem1128626 {_26546 : Type'} (f : _26546 -> _26546) (t : list _26546) (h1 : term26 _26546 t) (h2 : term72 _26546 f t) : (@List.map _26546 _26546 f t) = t.
Proof. exact (@lem1128612 _26546 f t h1 (@lem1128624 _26546 f t h2)). Qed.
Lemma lem1128627 {_26546 : Type'} (h : _26546) (f : _26546 -> _26546) (t : list _26546) (h1 : term26 _26546 t) (h2 : (f h) = h) (h3 : term72 _26546 f t) : term80 _26546 h f t.
Proof. exact (conj (@lem1128582 _26546 f h h2) (@lem1128626 _26546 f t h1 h3)). Qed.
Lemma lem1128628 {_26546 : Type'} (h : _26546) (f : _26546 -> _26546) (t : list _26546) (h1 : term73 _26546 h f t) : term72 _26546 f t.
Proof. exact (proj2 (@lem1128558 _26546 h f t h1)). Qed.
Lemma lem1128629 {_26546 : Type'} (h : _26546) (f : _26546 -> _26546) (t : list _26546) (h1 : term73 _26546 h f t) : (f h) = h.
Proof. exact (proj1 (@lem1128558 _26546 h f t h1)). Qed.
Lemma lem1128630 {_26546 : Type'} (h : _26546) (f : _26546 -> _26546) (t : list _26546) (h1 : term26 _26546 t) (h2 : (f h) = h) (h3 : term72 _26546 f t) : (term72 _26546 f t) = (term80 _26546 h f t).
Proof. exact (prop_ext (fun h4 : term72 _26546 f t => @lem1128627 _26546 h f t h1 h2 h3) (fun h4 : term80 _26546 h f t => @lem1128559 _26546 f t h3)). Qed.
Lemma lem1128631 {_26546 : Type'} (h : _26546) (f : _26546 -> _26546) (t : list _26546) (h1 : term26 _26546 t) (h2 : (f h) = h) (h3 : term72 _26546 f t) : term80 _26546 h f t.
Proof. exact (EQ_MP (@lem1128630 _26546 h f t h1 h2 h3) (@lem1128559 _26546 f t h3)). Qed.
Lemma lem1128632 {_26546 : Type'} (h : _26546) (f : _26546 -> _26546) (t : list _26546) (h1 : term26 _26546 t) (h2 : (f h) = h) (h3 : term72 _26546 f t) : ((f h) = h) = (term80 _26546 h f t).
Proof. exact (prop_ext (fun h4 : (f h) = h => @lem1128631 _26546 h f t h1 h2 h3) (fun h4 : term80 _26546 h f t => @lem1128560 _26546 f h h2)). Qed.
Lemma lem1128633 {_26546 : Type'} (h : _26546) (f : _26546 -> _26546) (t : list _26546) (h1 : term26 _26546 t) (h2 : (f h) = h) (h3 : term72 _26546 f t) : term80 _26546 h f t.
Proof. exact (EQ_MP (@lem1128632 _26546 h f t h1 h2 h3) (@lem1128560 _26546 f h h2)). Qed.
Lemma lem1128634 {_26546 : Type'} (t : list _26546) (f : _26546 -> _26546) (h : _26546) (h1 : term26 _26546 t) (h2 : term73 _26546 h f t) (h3 : (f h) = h) : (term72 _26546 f t) = (term80 _26546 h f t).
Proof. exact (prop_ext (fun h4 : term72 _26546 f t => @lem1128633 _26546 h f t h1 h3 h4) (fun h4 : term80 _26546 h f t => @lem1128628 _26546 h f t h2)). Qed.
Lemma lem1128635 {_26546 : Type'} (t : list _26546) (f : _26546 -> _26546) (h : _26546) (h1 : term26 _26546 t) (h2 : term73 _26546 h f t) (h3 : (f h) = h) : term80 _26546 h f t.
Proof. exact (EQ_MP (@lem1128634 _26546 t f h h1 h2 h3) (@lem1128628 _26546 h f t h2)). Qed.
Lemma lem1128636 {_26546 : Type'} (h : _26546) (f : _26546 -> _26546) (t : list _26546) (h1 : term26 _26546 t) (h2 : term73 _26546 h f t) : ((f h) = h) = (term80 _26546 h f t).
Proof. exact (prop_ext (fun h3 : (f h) = h => @lem1128635 _26546 t f h h1 h2 h3) (fun h3 : term80 _26546 h f t => @lem1128629 _26546 h f t h2)). Qed.
Lemma lem1128637 {_26546 : Type'} (h : _26546) (f : _26546 -> _26546) (t : list _26546) (h1 : term26 _26546 t) (h2 : term73 _26546 h f t) : term80 _26546 h f t.
Proof. exact (EQ_MP (@lem1128636 _26546 h f t h1 h2) (@lem1128629 _26546 h f t h2)). Qed.
Lemma lem1128638 {_26546 : Type'} (h : _26546) (f : _26546 -> _26546) (t : list _26546) (h1 : term26 _26546 t) : term82 _26546 h f t.
Proof. exact (fun h0 : term73 _26546 h f t => @lem1128637 _26546 h f t h1 h0). Qed.
Lemma lem1128643 {_26546 : Type'} (h : _26546) (t : list _26546) (h1 : term26 _26546 t) : term85 _26546 h t.
Proof. exact (fun f : _26546 -> _26546 => @lem1128638 _26546 h f t h1). Qed.
Lemma lem1128644 {_26546 : Type'} (h : _26546) (t : list _26546) (h1 : term26 _26546 t) : term30 _26546 h t.
Proof. exact (EQ_MP (@lem1128557 _26546 h t) (@lem1128643 _26546 h t h1)). Qed.
Lemma lem1128645 {_26546 : Type'} (h : _26546) (t : list _26546) : term32 _26546 h t.
Proof. exact (fun h0 : term26 _26546 t => @lem1128644 _26546 h t h0). Qed.
Lemma lem1128650 {_26546 : Type'} (h : _26546) : term36 _26546 h.
Proof. exact (fun t : list _26546 => @lem1128645 _26546 h t). Qed.
Lemma lem1128655 {_26546 : Type'} : term40 _26546.
Proof. exact (fun h : _26546 => @lem1128650 _26546 h). Qed.
Lemma lem1128656 {_26546 : Type'} : term42 _26546.
Proof. exact (conj (@lem1128488 _26546) (@lem1128655 _26546)). Qed.
Lemma lem1128657 {_26546 : Type'} : term47 _26546.
Proof. exact (@lem1128446 _26546 (@lem1128656 _26546)). Qed.
