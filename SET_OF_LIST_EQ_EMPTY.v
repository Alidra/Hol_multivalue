Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SET_OF_LIST_EQ_EMPTY_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_CONS_NIL_spec.
Require Import NOT_INSERT_EMPTY_spec.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4785464_spec.
Require Import thm4785470_spec.
Require Import thm4785471_spec.
Require Import thm82_spec.
Lemma lem4790438 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3278799 A x). Qed.
Lemma lem4790439 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem4790440 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem4790439 A x) (@lem4790438 A x)). Qed.
Lemma lem4790441 {A : Type'} (x : A) (s : A -> Prop) : term2 A x s.
Proof. exact (@lem4790440 A x s). Qed.
Lemma lem4790442 {A : Type'} (x : A) (s : A -> Prop) : (term2 A x s) = (term3 A x s).
Proof. exact (eq_refl (term2 A x s)). Qed.
Lemma lem4790443 {A : Type'} (x : A) (s : A -> Prop) : term3 A x s.
Proof. exact (EQ_MP (@lem4790442 A x s) (@lem4790441 A x s)). Qed.
Lemma lem4790444 {A : Type'} (x : A) (s : A -> Prop) : term4 A x s.
Proof. exact (@lem82 ((@INSERT A x s) = (@EMPTY A))). Qed.
Lemma lem4790457 {A : Type'} (h : A) : term5 A h.
Proof. exact (@lem1111523 A h). Qed.
Lemma lem4790458 {A : Type'} (h : A) : (term5 A h) = (term6 A h).
Proof. exact (eq_refl (term5 A h)). Qed.
Lemma lem4790459 {A : Type'} (h : A) : term6 A h.
Proof. exact (EQ_MP (@lem4790458 A h) (@lem4790457 A h)). Qed.
Lemma lem4790460 {A : Type'} (h : A) (t : list A) : term7 A h t.
Proof. exact (@lem4790459 A h t). Qed.
Lemma lem4790461 {A : Type'} (h : A) (t : list A) : (term7 A h t) = (term8 A h t).
Proof. exact (eq_refl (term7 A h t)). Qed.
Lemma lem4790462 {A : Type'} (h : A) (t : list A) : term8 A h t.
Proof. exact (EQ_MP (@lem4790461 A h t) (@lem4790460 A h t)). Qed.
Lemma lem4790463 {A : Type'} (h : A) (t : list A) : term9 A h t.
Proof. exact (@lem82 ((@cons A h t) = (@nil A))). Qed.
Lemma lem4790479 {A : Type'} (P : type1143 A) : term10 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem4790480 {_110450 : Type'} (P : type1143 _110450) : term10 _110450 P.
Proof. exact (@lem4790479 _110450 P). Qed.
Lemma lem4790481 {_110450 : Type'} : term11 _110450.
Proof. exact (@lem4790480 _110450 (term12 _110450)). Qed.
Lemma lem4790482 {_110450 : Type'} : (term13 _110450) = (((@set_of_list _110450 (@nil _110450)) = (@EMPTY _110450)) = ((@nil _110450) = (@nil _110450))).
Proof. exact (eq_refl (term13 _110450)). Qed.
Lemma lem4790483 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4790484 {_110450 : Type'} : (term14 _110450) = (term15 _110450).
Proof. exact (MK_COMB (@lem4790483) (@lem4790482 _110450)). Qed.
Lemma lem4790485 {_110450 : Type'} (t : list _110450) : (term16 _110450 t) = (((@set_of_list _110450 t) = (@EMPTY _110450)) = (t = (@nil _110450))).
Proof. exact (eq_refl (term16 _110450 t)). Qed.
Lemma lem4790486 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4790487 {_110450 : Type'} (t : list _110450) : (term17 _110450 t) = (term18 _110450 t).
Proof. exact (MK_COMB (@lem4790486) (@lem4790485 _110450 t)). Qed.
Lemma lem4790488 {_110450 : Type'} (h : _110450) (t : list _110450) : (term19 _110450 h t) = (((term20 _110450 h t) = (@EMPTY _110450)) = ((@cons _110450 h t) = (@nil _110450))).
Proof. exact (eq_refl (term19 _110450 h t)). Qed.
Lemma lem4790489 {_110450 : Type'} (h : _110450) (t : list _110450) : (term21 _110450 h t) = (term22 _110450 h t).
Proof. exact (MK_COMB (@lem4790487 _110450 t) (@lem4790488 _110450 h t)). Qed.
Lemma lem4790490 {_110450 : Type'} (h : _110450) : (term23 _110450 h) = (term24 _110450 h).
Proof. exact (fun_ext (fun t : list _110450 => @lem4790489 _110450 h t)). Qed.
Lemma lem4790491 {_110450 : Type'} : (@all (list _110450)) = (@all (list _110450)).
Proof. exact (eq_refl (@all (list _110450))). Qed.
Lemma lem4790492 {_110450 : Type'} (h : _110450) : (term25 _110450 h) = (term26 _110450 h).
Proof. exact (MK_COMB (@lem4790491 _110450) (@lem4790490 _110450 h)). Qed.
Lemma lem4790493 {_110450 : Type'} : (term27 _110450) = (term28 _110450).
Proof. exact (fun_ext (fun h : _110450 => @lem4790492 _110450 h)). Qed.
Lemma lem4790494 {_110450 : Type'} : (@all _110450) = (@all _110450).
Proof. exact (eq_refl (@all _110450)). Qed.
Lemma lem4790495 {_110450 : Type'} : (term29 _110450) = (term30 _110450).
Proof. exact (MK_COMB (@lem4790494 _110450) (@lem4790493 _110450)). Qed.
Lemma lem4790496 {_110450 : Type'} : (term31 _110450) = (term32 _110450).
Proof. exact (MK_COMB (@lem4790484 _110450) (@lem4790495 _110450)). Qed.
Lemma lem4790497 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4790498 {_110450 : Type'} : (term33 _110450) = (term34 _110450).
Proof. exact (MK_COMB (@lem4790497) (@lem4790496 _110450)). Qed.
Lemma lem4790499 {_110450 : Type'} (l : list _110450) : (term16 _110450 l) = (((@set_of_list _110450 l) = (@EMPTY _110450)) = (l = (@nil _110450))).
Proof. exact (eq_refl (term16 _110450 l)). Qed.
Lemma lem4790500 {_110450 : Type'} : (term35 _110450) = (term12 _110450).
Proof. exact (fun_ext (fun l : list _110450 => @lem4790499 _110450 l)). Qed.
Lemma lem4790501 {_110450 : Type'} : (@all (list _110450)) = (@all (list _110450)).
Proof. exact (eq_refl (@all (list _110450))). Qed.
Lemma lem4790502 {_110450 : Type'} : (term36 _110450) = (term37 _110450).
Proof. exact (MK_COMB (@lem4790501 _110450) (@lem4790500 _110450)). Qed.
Lemma lem4790503 {_110450 : Type'} : (term11 _110450) = (term38 _110450).
Proof. exact (MK_COMB (@lem4790498 _110450) (@lem4790502 _110450)). Qed.
Lemma lem4790504 {_110450 : Type'} : term38 _110450.
Proof. exact (EQ_MP (@lem4790503 _110450) (@lem4790481 _110450)). Qed.
Lemma lem4790511 {A : Type'} : (@set_of_list A (@nil A)) = (@EMPTY A).
Proof. exact (proj1 (@lem4785464 A)). Qed.
Lemma lem4790512 {_110450 : Type'} : (@set_of_list _110450 (@nil _110450)) = (@EMPTY _110450).
Proof. exact (@lem4790511 _110450). Qed.
Lemma lem4790513 {_110450 : Type'} : (@eq (_110450 -> Prop)) = (@eq (_110450 -> Prop)).
Proof. exact (eq_refl (@eq (_110450 -> Prop))). Qed.
Lemma lem4790514 {_110450 : Type'} : (term39 _110450) = (@eq (_110450 -> Prop) (@EMPTY _110450)).
Proof. exact (MK_COMB (@lem4790513 _110450) (@lem4790512 _110450)). Qed.
Lemma lem4790515 {_110450 : Type'} : (@EMPTY _110450) = (@EMPTY _110450).
Proof. exact (eq_refl (@EMPTY _110450)). Qed.
Lemma lem4790516 {_110450 : Type'} : ((@set_of_list _110450 (@nil _110450)) = (@EMPTY _110450)) = ((@EMPTY _110450) = (@EMPTY _110450)).
Proof. exact (MK_COMB (@lem4790514 _110450) (@lem4790515 _110450)). Qed.
Lemma lem4790518 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4790519 {_110450 : Type'} (x : _110450 -> Prop) : (x = x) = True.
Proof. exact (@lem4790518 (_110450 -> Prop) x). Qed.
Lemma lem4790520 {_110450 : Type'} : ((@EMPTY _110450) = (@EMPTY _110450)) = True.
Proof. exact (@lem4790519 _110450 (@EMPTY _110450)). Qed.
Lemma lem4790521 {_110450 : Type'} : ((@set_of_list _110450 (@nil _110450)) = (@EMPTY _110450)) = True.
Proof. exact (TRANS (@lem4790516 _110450) (@lem4790520 _110450)). Qed.
Lemma lem4790522 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4790523 {_110450 : Type'} : (term40 _110450) = (@eq Prop True).
Proof. exact (MK_COMB (@lem4790522) (@lem4790521 _110450)). Qed.
Lemma lem4790525 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4790526 {_110450 : Type'} (x : list _110450) : (x = x) = True.
Proof. exact (@lem4790525 (list _110450) x). Qed.
Lemma lem4790527 {_110450 : Type'} : ((@nil _110450) = (@nil _110450)) = True.
Proof. exact (@lem4790526 _110450 (@nil _110450)). Qed.
Lemma lem4790528 {_110450 : Type'} : (((@set_of_list _110450 (@nil _110450)) = (@EMPTY _110450)) = ((@nil _110450) = (@nil _110450))) = (True = True).
Proof. exact (MK_COMB (@lem4790523 _110450) (@lem4790527 _110450)). Qed.
Lemma lem4790530 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem4790531 : (True = True) = True.
Proof. exact (@lem4790530 True). Qed.
Lemma lem4790532 {_110450 : Type'} : (((@set_of_list _110450 (@nil _110450)) = (@EMPTY _110450)) = ((@nil _110450) = (@nil _110450))) = True.
Proof. exact (TRANS (@lem4790528 _110450) (@lem4790531)). Qed.
Lemma lem4790533 {_110450 : Type'} : True = (((@set_of_list _110450 (@nil _110450)) = (@EMPTY _110450)) = ((@nil _110450) = (@nil _110450))).
Proof. exact (SYM (@lem4790532 _110450)). Qed.
Lemma lem4790534 {_110450 : Type'} : ((@set_of_list _110450 (@nil _110450)) = (@EMPTY _110450)) = ((@nil _110450) = (@nil _110450)).
Proof. exact (EQ_MP (@lem4790533 _110450) (@lem0)). Qed.
Lemma lem4790540 {A : Type'} (h : A) (t : list A) : (term20 A h t) = (term41 A h t).
Proof. exact (EQ_MP (@lem4785471 A h t) (@lem4785470 A h t)). Qed.
Lemma lem4790541 {_110450 : Type'} (h : _110450) (t : list _110450) : (term20 _110450 h t) = (term41 _110450 h t).
Proof. exact (@lem4790540 _110450 h t). Qed.
Lemma lem4790542 {_110450 : Type'} : (@eq (_110450 -> Prop)) = (@eq (_110450 -> Prop)).
Proof. exact (eq_refl (@eq (_110450 -> Prop))). Qed.
Lemma lem4790543 {_110450 : Type'} (h : _110450) (t : list _110450) : (term42 _110450 h t) = (term43 _110450 h t).
Proof. exact (MK_COMB (@lem4790542 _110450) (@lem4790541 _110450 h t)). Qed.
Lemma lem4790544 {_110450 : Type'} : (@EMPTY _110450) = (@EMPTY _110450).
Proof. exact (eq_refl (@EMPTY _110450)). Qed.
Lemma lem4790545 {_110450 : Type'} (h : _110450) (t : list _110450) : ((term20 _110450 h t) = (@EMPTY _110450)) = ((term41 _110450 h t) = (@EMPTY _110450)).
Proof. exact (MK_COMB (@lem4790543 _110450 h t) (@lem4790544 _110450)). Qed.
Lemma lem4790547 {A : Type'} (x : A) (s : A -> Prop) : ((@INSERT A x s) = (@EMPTY A)) = False.
Proof. exact (@lem4790444 A x s (@lem4790443 A x s)). Qed.
Lemma lem4790548 {_110450 : Type'} (x : _110450) (s : _110450 -> Prop) : ((@INSERT _110450 x s) = (@EMPTY _110450)) = False.
Proof. exact (@lem4790547 _110450 x s). Qed.
Lemma lem4790549 {_110450 : Type'} (h : _110450) (t : list _110450) : ((term41 _110450 h t) = (@EMPTY _110450)) = False.
Proof. exact (@lem4790548 _110450 h (@set_of_list _110450 t)). Qed.
Lemma lem4790550 {_110450 : Type'} (h : _110450) (t : list _110450) : ((term20 _110450 h t) = (@EMPTY _110450)) = False.
Proof. exact (TRANS (@lem4790545 _110450 h t) (@lem4790549 _110450 h t)). Qed.
Lemma lem4790551 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4790552 {_110450 : Type'} (h : _110450) (t : list _110450) : (term44 _110450 h t) = (@eq Prop False).
Proof. exact (MK_COMB (@lem4790551) (@lem4790550 _110450 h t)). Qed.
Lemma lem4790554 {A : Type'} (h : A) (t : list A) : ((@cons A h t) = (@nil A)) = False.
Proof. exact (@lem4790463 A h t (@lem4790462 A h t)). Qed.
Lemma lem4790555 {_110450 : Type'} (h : _110450) (t : list _110450) : ((@cons _110450 h t) = (@nil _110450)) = False.
Proof. exact (@lem4790554 _110450 h t). Qed.
Lemma lem4790556 {_110450 : Type'} (h : _110450) (t : list _110450) : (((term20 _110450 h t) = (@EMPTY _110450)) = ((@cons _110450 h t) = (@nil _110450))) = (False = False).
Proof. exact (MK_COMB (@lem4790552 _110450 h t) (@lem4790555 _110450 h t)). Qed.
Lemma lem4790558 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem4790559 : (False = False) = (~ False).
Proof. exact (@lem4790558 False). Qed.
Lemma lem4790561 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4790562 : (False = False) = True.
Proof. exact (TRANS (@lem4790559) (@lem4790561)). Qed.
Lemma lem4790563 {_110450 : Type'} (h : _110450) (t : list _110450) : (((term20 _110450 h t) = (@EMPTY _110450)) = ((@cons _110450 h t) = (@nil _110450))) = True.
Proof. exact (TRANS (@lem4790556 _110450 h t) (@lem4790562)). Qed.
Lemma lem4790564 {_110450 : Type'} (h : _110450) (t : list _110450) : True = (((term20 _110450 h t) = (@EMPTY _110450)) = ((@cons _110450 h t) = (@nil _110450))).
Proof. exact (SYM (@lem4790563 _110450 h t)). Qed.
Lemma lem4790565 {_110450 : Type'} (h : _110450) (t : list _110450) : ((term20 _110450 h t) = (@EMPTY _110450)) = ((@cons _110450 h t) = (@nil _110450)).
Proof. exact (EQ_MP (@lem4790564 _110450 h t) (@lem0)). Qed.
Lemma lem4790566 {_110450 : Type'} (h : _110450) (t : list _110450) : term22 _110450 h t.
Proof. exact (fun h0 : ((@set_of_list _110450 t) = (@EMPTY _110450)) = (t = (@nil _110450)) => @lem4790565 _110450 h t). Qed.
Lemma lem4790571 {_110450 : Type'} (h : _110450) : term26 _110450 h.
Proof. exact (fun t : list _110450 => @lem4790566 _110450 h t). Qed.
Lemma lem4790576 {_110450 : Type'} : term30 _110450.
Proof. exact (fun h : _110450 => @lem4790571 _110450 h). Qed.
Lemma lem4790577 {_110450 : Type'} : term32 _110450.
Proof. exact (conj (@lem4790534 _110450) (@lem4790576 _110450)). Qed.
Lemma lem4790578 {_110450 : Type'} : term37 _110450.
Proof. exact (@lem4790504 _110450 (@lem4790577 _110450)). Qed.
