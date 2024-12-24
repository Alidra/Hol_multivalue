Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NOT_ALL_term_abbrevs.
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
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1123469 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1123470 {_26390 : Type'} (P : type1143 _26390) : term0 _26390 P.
Proof. exact (@lem1123469 _26390 P). Qed.
Lemma lem1123471 {_26390 : Type'} (P : _26390 -> Prop) : term1 _26390 P.
Proof. exact (@lem1123470 _26390 (term2 _26390 P)). Qed.
Lemma lem1123472 {_26390 : Type'} (P : _26390 -> Prop) : (term3 _26390 P) = ((term4 _26390 P) = (term5 _26390 P)).
Proof. exact (eq_refl (term3 _26390 P)). Qed.
Lemma lem1123473 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1123474 {_26390 : Type'} (P : _26390 -> Prop) : (term6 _26390 P) = (term7 _26390 P).
Proof. exact (MK_COMB (@lem1123473) (@lem1123472 _26390 P)). Qed.
Lemma lem1123475 {_26390 : Type'} (P : _26390 -> Prop) (t : list _26390) : (term8 _26390 P t) = ((term9 _26390 P t) = (term10 _26390 P t)).
Proof. exact (eq_refl (term8 _26390 P t)). Qed.
Lemma lem1123476 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1123477 {_26390 : Type'} (P : _26390 -> Prop) (t : list _26390) : (term11 _26390 P t) = (term12 _26390 P t).
Proof. exact (MK_COMB (@lem1123476) (@lem1123475 _26390 P t)). Qed.
Lemma lem1123478 {_26390 : Type'} (P : _26390 -> Prop) (h : _26390) (t : list _26390) : (term13 _26390 P h t) = ((term14 _26390 P h t) = (term15 _26390 P h t)).
Proof. exact (eq_refl (term13 _26390 P h t)). Qed.
Lemma lem1123479 {_26390 : Type'} (P : _26390 -> Prop) (h : _26390) (t : list _26390) : (term16 _26390 P h t) = (term17 _26390 P h t).
Proof. exact (MK_COMB (@lem1123477 _26390 P t) (@lem1123478 _26390 P h t)). Qed.
Lemma lem1123480 {_26390 : Type'} (P : _26390 -> Prop) (h : _26390) : (term18 _26390 P h) = (term19 _26390 P h).
Proof. exact (fun_ext (fun t : list _26390 => @lem1123479 _26390 P h t)). Qed.
Lemma lem1123481 {_26390 : Type'} : (@all (list _26390)) = (@all (list _26390)).
Proof. exact (eq_refl (@all (list _26390))). Qed.
Lemma lem1123482 {_26390 : Type'} (P : _26390 -> Prop) (h : _26390) : (term20 _26390 P h) = (term21 _26390 P h).
Proof. exact (MK_COMB (@lem1123481 _26390) (@lem1123480 _26390 P h)). Qed.
Lemma lem1123483 {_26390 : Type'} (P : _26390 -> Prop) : (term22 _26390 P) = (term23 _26390 P).
Proof. exact (fun_ext (fun h : _26390 => @lem1123482 _26390 P h)). Qed.
Lemma lem1123484 {_26390 : Type'} : (@all _26390) = (@all _26390).
Proof. exact (eq_refl (@all _26390)). Qed.
Lemma lem1123485 {_26390 : Type'} (P : _26390 -> Prop) : (term24 _26390 P) = (term25 _26390 P).
Proof. exact (MK_COMB (@lem1123484 _26390) (@lem1123483 _26390 P)). Qed.
Lemma lem1123486 {_26390 : Type'} (P : _26390 -> Prop) : (term26 _26390 P) = (term27 _26390 P).
Proof. exact (MK_COMB (@lem1123474 _26390 P) (@lem1123485 _26390 P)). Qed.
Lemma lem1123487 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1123488 {_26390 : Type'} (P : _26390 -> Prop) : (term28 _26390 P) = (term29 _26390 P).
Proof. exact (MK_COMB (@lem1123487) (@lem1123486 _26390 P)). Qed.
Lemma lem1123489 {_26390 : Type'} (P : _26390 -> Prop) (l : list _26390) : (term8 _26390 P l) = ((term9 _26390 P l) = (term10 _26390 P l)).
Proof. exact (eq_refl (term8 _26390 P l)). Qed.
Lemma lem1123490 {_26390 : Type'} (P : _26390 -> Prop) : (term30 _26390 P) = (term2 _26390 P).
Proof. exact (fun_ext (fun l : list _26390 => @lem1123489 _26390 P l)). Qed.
Lemma lem1123491 {_26390 : Type'} : (@all (list _26390)) = (@all (list _26390)).
Proof. exact (eq_refl (@all (list _26390))). Qed.
Lemma lem1123492 {_26390 : Type'} (P : _26390 -> Prop) : (term31 _26390 P) = (term32 _26390 P).
Proof. exact (MK_COMB (@lem1123491 _26390) (@lem1123490 _26390 P)). Qed.
Lemma lem1123493 {_26390 : Type'} (P : _26390 -> Prop) : (term1 _26390 P) = (term33 _26390 P).
Proof. exact (MK_COMB (@lem1123488 _26390 P) (@lem1123492 _26390 P)). Qed.
Lemma lem1123494 {_26390 : Type'} (P : _26390 -> Prop) : term33 _26390 P.
Proof. exact (EQ_MP (@lem1123493 _26390 P) (@lem1123471 _26390 P)). Qed.
Lemma lem1123511 {_25307 : Type'} (P : _25307 -> Prop) : (@List.Forall _25307 P (@nil _25307)) = True.
Proof. exact (EQ_MP (@lem1100835 _25307 P) (@lem1100834 _25307 P)). Qed.
Lemma lem1123512 {_26390 : Type'} (P : _26390 -> Prop) : (@List.Forall _26390 P (@nil _26390)) = True.
Proof. exact (@lem1123511 _26390 P). Qed.
Lemma lem1123513 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1123514 {_26390 : Type'} (P : _26390 -> Prop) : (term4 _26390 P) = (~ True).
Proof. exact (MK_COMB (@lem1123513) (@lem1123512 _26390 P)). Qed.
Lemma lem1123516 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1123517 {_26390 : Type'} (P : _26390 -> Prop) : (term4 _26390 P) = False.
Proof. exact (TRANS (@lem1123514 _26390 P) (@lem1123516)). Qed.
Lemma lem1123518 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1123519 {_26390 : Type'} (P : _26390 -> Prop) : (term34 _26390 P) = (@eq Prop False).
Proof. exact (MK_COMB (@lem1123518) (@lem1123517 _26390 P)). Qed.
Lemma lem1123521 {_25328 : Type'} (P : _25328 -> Prop) : (@EX _25328 P (@nil _25328)) = False.
Proof. exact (EQ_MP (@lem1101588 _25328 P) (@lem1101587 _25328 P)). Qed.
Lemma lem1123522 {_26390 : Type'} (P : _26390 -> Prop) : (@EX _26390 P (@nil _26390)) = False.
Proof. exact (@lem1123521 _26390 P). Qed.
Lemma lem1123523 {_26390 : Type'} (P : _26390 -> Prop) : (term5 _26390 P) = False.
Proof. exact (@lem1123522 _26390 (term35 _26390 P)). Qed.
Lemma lem1123524 {_26390 : Type'} (P : _26390 -> Prop) : ((term4 _26390 P) = (term5 _26390 P)) = (False = False).
Proof. exact (MK_COMB (@lem1123519 _26390 P) (@lem1123523 _26390 P)). Qed.
Lemma lem1123526 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem1123527 : (False = False) = (~ False).
Proof. exact (@lem1123526 False). Qed.
Lemma lem1123529 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1123530 : (False = False) = True.
Proof. exact (TRANS (@lem1123527) (@lem1123529)). Qed.
Lemma lem1123531 {_26390 : Type'} (P : _26390 -> Prop) : ((term4 _26390 P) = (term5 _26390 P)) = True.
Proof. exact (TRANS (@lem1123524 _26390 P) (@lem1123530)). Qed.
Lemma lem1123532 {_26390 : Type'} (P : _26390 -> Prop) : True = ((term4 _26390 P) = (term5 _26390 P)).
Proof. exact (SYM (@lem1123531 _26390 P)). Qed.
Lemma lem1123533 {_26390 : Type'} (P : _26390 -> Prop) : (term4 _26390 P) = (term5 _26390 P).
Proof. exact (EQ_MP (@lem1123532 _26390 P) (@lem0)). Qed.
Lemma lem1123534 (t1 : Prop) : term36 t1.
Proof. exact (@lem10089 t1). Qed.
Lemma lem1123535 (t1 : Prop) : (term36 t1) = (term37 t1).
Proof. exact (eq_refl (term36 t1)). Qed.
Lemma lem1123536 (t1 : Prop) : term37 t1.
Proof. exact (EQ_MP (@lem1123535 t1) (@lem1123534 t1)). Qed.
Lemma lem1123537 (t1 : Prop) (t2 : Prop) : term38 t1 t2.
Proof. exact (@lem1123536 t1 t2). Qed.
Lemma lem1123538 (t1 : Prop) (t2 : Prop) : (term38 t1 t2) = (term39 t1 t2).
Proof. exact (eq_refl (term38 t1 t2)). Qed.
Lemma lem1123539 (t1 : Prop) (t2 : Prop) : term39 t1 t2.
Proof. exact (EQ_MP (@lem1123538 t1 t2) (@lem1123537 t1 t2)). Qed.
Lemma lem1123549 {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) (t : list _25307) : (term40 _25307 P h t) = (term41 _25307 h P t).
Proof. exact (EQ_MP (@lem1100844 _25307 h P t) (@lem1100843 _25307 h P t)). Qed.
Lemma lem1123550 {_26390 : Type'} (h : _26390) (P : _26390 -> Prop) (t : list _26390) : (term40 _26390 P h t) = (term41 _26390 h P t).
Proof. exact (@lem1123549 _26390 h P t). Qed.
Lemma lem1123553 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1123554 {_26390 : Type'} (h : _26390) (P : _26390 -> Prop) (t : list _26390) : (term14 _26390 P h t) = (term42 _26390 h P t).
Proof. exact (MK_COMB (@lem1123553) (@lem1123550 _26390 h P t)). Qed.
Lemma lem1123556 (t1 : Prop) (t2 : Prop) : (term43 t1 t2) = (term44 t1 t2).
Proof. exact (proj1 (@lem1123539 t1 t2)). Qed.
Lemma lem1123557 {_26390 : Type'} (h : _26390) (P : _26390 -> Prop) (t : list _26390) : (term42 _26390 h P t) = (term45 _26390 h P t).
Proof. exact (@lem1123556 (P h) (@List.Forall _26390 P t)). Qed.
Lemma lem1123561 {_26390 : Type'} (P : _26390 -> Prop) (t : list _26390) (h1 : (term9 _26390 P t) = (term10 _26390 P t)) : (term9 _26390 P t) = (term10 _26390 P t).
Proof. exact (h1). Qed.
Lemma lem1123562 {_26390 : Type'} (P : _26390 -> Prop) (h : _26390) : (term46 _26390 P h) = (term46 _26390 P h).
Proof. exact (eq_refl (term46 _26390 P h)). Qed.
Lemma lem1123563 {_26390 : Type'} (h : _26390) (P : _26390 -> Prop) (t : list _26390) (h1 : (term9 _26390 P t) = (term10 _26390 P t)) : (term45 _26390 h P t) = (term47 _26390 h P t).
Proof. exact (MK_COMB (@lem1123562 _26390 P h) (@lem1123561 _26390 P t h1)). Qed.
Lemma lem1123566 {_26390 : Type'} (h : _26390) (P : _26390 -> Prop) (t : list _26390) (h1 : (term9 _26390 P t) = (term10 _26390 P t)) : (term42 _26390 h P t) = (term47 _26390 h P t).
Proof. exact (TRANS (@lem1123557 _26390 h P t) (@lem1123563 _26390 h P t h1)). Qed.
Lemma lem1123567 {_26390 : Type'} (h : _26390) (P : _26390 -> Prop) (t : list _26390) (h1 : (term9 _26390 P t) = (term10 _26390 P t)) : (term14 _26390 P h t) = (term47 _26390 h P t).
Proof. exact (TRANS (@lem1123554 _26390 h P t) (@lem1123566 _26390 h P t h1)). Qed.
Lemma lem1123568 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1123569 {_26390 : Type'} (h : _26390) (P : _26390 -> Prop) (t : list _26390) (h1 : (term9 _26390 P t) = (term10 _26390 P t)) : (term48 _26390 P h t) = (term49 _26390 h P t).
Proof. exact (MK_COMB (@lem1123568) (@lem1123567 _26390 h P t h1)). Qed.
Lemma lem1123571 {_25328 : Type'} (h : _25328) (P : _25328 -> Prop) (t : list _25328) : (term50 _25328 P h t) = (term51 _25328 h P t).
Proof. exact (EQ_MP (@lem1101597 _25328 h P t) (@lem1101596 _25328 h P t)). Qed.
Lemma lem1123572 {_26390 : Type'} (h : _26390) (P : _26390 -> Prop) (t : list _26390) : (term50 _26390 P h t) = (term51 _26390 h P t).
Proof. exact (@lem1123571 _26390 h P t). Qed.
Lemma lem1123573 {_26390 : Type'} (h : _26390) (P : _26390 -> Prop) (t : list _26390) : (term15 _26390 P h t) = (term52 _26390 h P t).
Proof. exact (@lem1123572 _26390 h (term35 _26390 P) t). Qed.
Lemma lem1123577 {A B : Type'} (f : A -> B) (y : A) : (term53 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1123578 {_26390 : Type'} (f : _26390 -> Prop) (y : _26390) : (term54 _26390 f y) = (f y).
Proof. exact (@lem1123577 _26390 Prop f y). Qed.
Lemma lem1123579 {_26390 : Type'} (P : _26390 -> Prop) (h : _26390) : (term55 _26390 P h) = (term56 _26390 P h).
Proof. exact (@lem1123578 _26390 (term35 _26390 P) h). Qed.
Lemma lem1123580 {_26390 : Type'} (P : _26390 -> Prop) (x : _26390) : (term56 _26390 P x) = (term57 _26390 P x).
Proof. exact (eq_refl (term56 _26390 P x)). Qed.
Lemma lem1123581 {_26390 : Type'} (P : _26390 -> Prop) : (term58 _26390 P) = (term35 _26390 P).
Proof. exact (fun_ext (fun x : _26390 => @lem1123580 _26390 P x)). Qed.
Lemma lem1123582 {_26390 : Type'} (h : _26390) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1123583 {_26390 : Type'} (P : _26390 -> Prop) (h : _26390) : (term55 _26390 P h) = (term56 _26390 P h).
Proof. exact (MK_COMB (@lem1123581 _26390 P) (@lem1123582 _26390 h)). Qed.
Lemma lem1123584 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1123585 {_26390 : Type'} (P : _26390 -> Prop) (h : _26390) : (term59 _26390 P h) = (term60 _26390 P h).
Proof. exact (MK_COMB (@lem1123584) (@lem1123583 _26390 P h)). Qed.
Lemma lem1123586 {_26390 : Type'} (P : _26390 -> Prop) (h : _26390) : (term56 _26390 P h) = (term57 _26390 P h).
Proof. exact (eq_refl (term56 _26390 P h)). Qed.
Lemma lem1123587 {_26390 : Type'} (P : _26390 -> Prop) (h : _26390) : ((term55 _26390 P h) = (term56 _26390 P h)) = ((term56 _26390 P h) = (term57 _26390 P h)).
Proof. exact (MK_COMB (@lem1123585 _26390 P h) (@lem1123586 _26390 P h)). Qed.
Lemma lem1123588 {_26390 : Type'} (P : _26390 -> Prop) (h : _26390) : (term56 _26390 P h) = (term57 _26390 P h).
Proof. exact (EQ_MP (@lem1123587 _26390 P h) (@lem1123579 _26390 P h)). Qed.
Lemma lem1123589 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1123590 {_26390 : Type'} (P : _26390 -> Prop) (h : _26390) : (term61 _26390 P h) = (term46 _26390 P h).
Proof. exact (MK_COMB (@lem1123589) (@lem1123588 _26390 P h)). Qed.
Lemma lem1123591 {_26390 : Type'} (P : _26390 -> Prop) (t : list _26390) : (term10 _26390 P t) = (term10 _26390 P t).
Proof. exact (eq_refl (term10 _26390 P t)). Qed.
Lemma lem1123592 {_26390 : Type'} (h : _26390) (P : _26390 -> Prop) (t : list _26390) : (term52 _26390 h P t) = (term47 _26390 h P t).
Proof. exact (MK_COMB (@lem1123590 _26390 P h) (@lem1123591 _26390 P t)). Qed.
Lemma lem1123595 {_26390 : Type'} (h : _26390) (P : _26390 -> Prop) (t : list _26390) : (term15 _26390 P h t) = (term47 _26390 h P t).
Proof. exact (TRANS (@lem1123573 _26390 h P t) (@lem1123592 _26390 h P t)). Qed.
Lemma lem1123596 {_26390 : Type'} (h : _26390) (P : _26390 -> Prop) (t : list _26390) (h1 : (term9 _26390 P t) = (term10 _26390 P t)) : ((term14 _26390 P h t) = (term15 _26390 P h t)) = ((term47 _26390 h P t) = (term47 _26390 h P t)).
Proof. exact (MK_COMB (@lem1123569 _26390 h P t h1) (@lem1123595 _26390 h P t)). Qed.
Lemma lem1123598 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1123599 (x : Prop) : (x = x) = True.
Proof. exact (@lem1123598 Prop x). Qed.
Lemma lem1123600 {_26390 : Type'} (h : _26390) (P : _26390 -> Prop) (t : list _26390) : ((term47 _26390 h P t) = (term47 _26390 h P t)) = True.
Proof. exact (@lem1123599 (term47 _26390 h P t)). Qed.
Lemma lem1123601 {_26390 : Type'} (h : _26390) (P : _26390 -> Prop) (t : list _26390) (h1 : (term9 _26390 P t) = (term10 _26390 P t)) : ((term14 _26390 P h t) = (term15 _26390 P h t)) = True.
Proof. exact (TRANS (@lem1123596 _26390 h P t h1) (@lem1123600 _26390 h P t)). Qed.
Lemma lem1123602 {_26390 : Type'} (h : _26390) (P : _26390 -> Prop) (t : list _26390) (h1 : (term9 _26390 P t) = (term10 _26390 P t)) : True = ((term14 _26390 P h t) = (term15 _26390 P h t)).
Proof. exact (SYM (@lem1123601 _26390 h P t h1)). Qed.
Lemma lem1123603 {_26390 : Type'} (h : _26390) (P : _26390 -> Prop) (t : list _26390) (h1 : (term9 _26390 P t) = (term10 _26390 P t)) : (term14 _26390 P h t) = (term15 _26390 P h t).
Proof. exact (EQ_MP (@lem1123602 _26390 h P t h1) (@lem0)). Qed.
Lemma lem1123604 {_26390 : Type'} (P : _26390 -> Prop) (h : _26390) (t : list _26390) : term17 _26390 P h t.
Proof. exact (fun h0 : (term9 _26390 P t) = (term10 _26390 P t) => @lem1123603 _26390 h P t h0). Qed.
Lemma lem1123609 {_26390 : Type'} (P : _26390 -> Prop) (h : _26390) : term21 _26390 P h.
Proof. exact (fun t : list _26390 => @lem1123604 _26390 P h t). Qed.
Lemma lem1123614 {_26390 : Type'} (P : _26390 -> Prop) : term25 _26390 P.
Proof. exact (fun h : _26390 => @lem1123609 _26390 P h). Qed.
Lemma lem1123615 {_26390 : Type'} (P : _26390 -> Prop) : term27 _26390 P.
Proof. exact (conj (@lem1123533 _26390 P) (@lem1123614 _26390 P)). Qed.
Lemma lem1123616 {_26390 : Type'} (P : _26390 -> Prop) : term32 _26390 P.
Proof. exact (@lem1123494 _26390 P (@lem1123615 _26390 P)). Qed.
Lemma lem1123621 {_26390 : Type'} : term62 _26390.
Proof. exact (fun P : _26390 -> Prop => @lem1123616 _26390 P). Qed.
