Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IN_SET_OF_LIST_term_abbrevs.
Require Import IN_INSERT_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1103191_spec.
Require Import thm1103192_spec.
Require Import thm1103200_spec.
Require Import thm1103201_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17160_spec.
Require Import thm17500_spec.
Require Import thm17646_spec.
Require Import thm1857_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm4785464_spec.
Require Import thm4785470_spec.
Require Import thm4785471_spec.
Require Import thm82_spec.
Lemma lem4788514 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem4788515 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem4788516 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem4788515 A x) (@lem4788514 A x)). Qed.
Lemma lem4788517 {A : Type'} (x : A) : term2 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem4788519 {A : Type'} (x : A) : term3 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem4788520 {A : Type'} (x : A) : (term3 A x) = (term4 A x).
Proof. exact (eq_refl (term3 A x)). Qed.
Lemma lem4788521 {A : Type'} (x : A) : term4 A x.
Proof. exact (EQ_MP (@lem4788520 A x) (@lem4788519 A x)). Qed.
Lemma lem4788522 {A : Type'} (x : A) (y : A) : term5 A x y.
Proof. exact (@lem4788521 A x y). Qed.
Lemma lem4788523 {A : Type'} (y : A) (x : A) : (term5 A x y) = (term6 A y x).
Proof. exact (eq_refl (term5 A x y)). Qed.
Lemma lem4788524 {A : Type'} (y : A) (x : A) : term6 A y x.
Proof. exact (EQ_MP (@lem4788523 A y x) (@lem4788522 A x y)). Qed.
Lemma lem4788525 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term7 A y x s.
Proof. exact (@lem4788524 A y x s). Qed.
Lemma lem4788526 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term7 A y x s) = ((term8 A x y s) = (term9 A y x s)).
Proof. exact (eq_refl (term7 A y x s)). Qed.
Lemma lem4788529 {A : Type'} (P : type1143 A) : term10 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem4788530 {_110384 : Type'} (P : type1143 _110384) : term10 _110384 P.
Proof. exact (@lem4788529 _110384 P). Qed.
Lemma lem4788531 {_110384 : Type'} (x : _110384) : term11 _110384 x.
Proof. exact (@lem4788530 _110384 (term12 _110384 x)). Qed.
Lemma lem4788532 {_110384 : Type'} (x : _110384) : (term13 _110384 x) = ((term14 _110384 x) = (@List.In _110384 x (@nil _110384))).
Proof. exact (eq_refl (term13 _110384 x)). Qed.
Lemma lem4788533 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4788534 {_110384 : Type'} (x : _110384) : (term15 _110384 x) = (term16 _110384 x).
Proof. exact (MK_COMB (@lem4788533) (@lem4788532 _110384 x)). Qed.
Lemma lem4788535 {_110384 : Type'} (x : _110384) (t : list _110384) : (term17 _110384 x t) = ((term18 _110384 x t) = (@List.In _110384 x t)).
Proof. exact (eq_refl (term17 _110384 x t)). Qed.
Lemma lem4788536 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4788537 {_110384 : Type'} (x : _110384) (t : list _110384) : (term19 _110384 x t) = (term20 _110384 x t).
Proof. exact (MK_COMB (@lem4788536) (@lem4788535 _110384 x t)). Qed.
Lemma lem4788538 {_110384 : Type'} (x : _110384) (h : _110384) (t : list _110384) : (term21 _110384 x h t) = ((term22 _110384 x h t) = (term23 _110384 x h t)).
Proof. exact (eq_refl (term21 _110384 x h t)). Qed.
Lemma lem4788539 {_110384 : Type'} (x : _110384) (h : _110384) (t : list _110384) : (term24 _110384 x h t) = (term25 _110384 x h t).
Proof. exact (MK_COMB (@lem4788537 _110384 x t) (@lem4788538 _110384 x h t)). Qed.
Lemma lem4788540 {_110384 : Type'} (x : _110384) (h : _110384) : (term26 _110384 x h) = (term27 _110384 x h).
Proof. exact (fun_ext (fun t : list _110384 => @lem4788539 _110384 x h t)). Qed.
Lemma lem4788541 {_110384 : Type'} : (@all (list _110384)) = (@all (list _110384)).
Proof. exact (eq_refl (@all (list _110384))). Qed.
Lemma lem4788542 {_110384 : Type'} (x : _110384) (h : _110384) : (term28 _110384 x h) = (term29 _110384 x h).
Proof. exact (MK_COMB (@lem4788541 _110384) (@lem4788540 _110384 x h)). Qed.
Lemma lem4788543 {_110384 : Type'} (x : _110384) : (term30 _110384 x) = (term31 _110384 x).
Proof. exact (fun_ext (fun h : _110384 => @lem4788542 _110384 x h)). Qed.
Lemma lem4788544 {_110384 : Type'} : (@all _110384) = (@all _110384).
Proof. exact (eq_refl (@all _110384)). Qed.
Lemma lem4788545 {_110384 : Type'} (x : _110384) : (term32 _110384 x) = (term33 _110384 x).
Proof. exact (MK_COMB (@lem4788544 _110384) (@lem4788543 _110384 x)). Qed.
Lemma lem4788546 {_110384 : Type'} (x : _110384) : (term34 _110384 x) = (term35 _110384 x).
Proof. exact (MK_COMB (@lem4788534 _110384 x) (@lem4788545 _110384 x)). Qed.
Lemma lem4788547 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4788548 {_110384 : Type'} (x : _110384) : (term36 _110384 x) = (term37 _110384 x).
Proof. exact (MK_COMB (@lem4788547) (@lem4788546 _110384 x)). Qed.
Lemma lem4788549 {_110384 : Type'} (x : _110384) (l : list _110384) : (term17 _110384 x l) = ((term18 _110384 x l) = (@List.In _110384 x l)).
Proof. exact (eq_refl (term17 _110384 x l)). Qed.
Lemma lem4788550 {_110384 : Type'} (x : _110384) : (term38 _110384 x) = (term12 _110384 x).
Proof. exact (fun_ext (fun l : list _110384 => @lem4788549 _110384 x l)). Qed.
Lemma lem4788551 {_110384 : Type'} : (@all (list _110384)) = (@all (list _110384)).
Proof. exact (eq_refl (@all (list _110384))). Qed.
Lemma lem4788552 {_110384 : Type'} (x : _110384) : (term39 _110384 x) = (term40 _110384 x).
Proof. exact (MK_COMB (@lem4788551 _110384) (@lem4788550 _110384 x)). Qed.
Lemma lem4788553 {_110384 : Type'} (x : _110384) : (term11 _110384 x) = (term41 _110384 x).
Proof. exact (MK_COMB (@lem4788548 _110384 x) (@lem4788552 _110384 x)). Qed.
Lemma lem4788554 {_110384 : Type'} (x : _110384) : term41 _110384 x.
Proof. exact (EQ_MP (@lem4788553 _110384 x) (@lem4788531 _110384 x)). Qed.
Lemma lem4788555 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : (term18 _110384 x t) = (@List.In _110384 x t)) : (term18 _110384 x t) = (@List.In _110384 x t).
Proof. exact (h1). Qed.
Lemma lem4788559 {A : Type'} : (@set_of_list A (@nil A)) = (@EMPTY A).
Proof. exact (proj1 (@lem4785464 A)). Qed.
Lemma lem4788560 {_110384 : Type'} : (@set_of_list _110384 (@nil _110384)) = (@EMPTY _110384).
Proof. exact (@lem4788559 _110384). Qed.
Lemma lem4788561 {_110384 : Type'} (x : _110384) : (@IN _110384 x) = (@IN _110384 x).
Proof. exact (eq_refl (@IN _110384 x)). Qed.
Lemma lem4788562 {_110384 : Type'} (x : _110384) : (term14 _110384 x) = (@IN _110384 x (@EMPTY _110384)).
Proof. exact (MK_COMB (@lem4788561 _110384 x) (@lem4788560 _110384)). Qed.
Lemma lem4788564 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4788517 A x (@lem4788516 A x)). Qed.
Lemma lem4788565 {_110384 : Type'} (x : _110384) : (@IN _110384 x (@EMPTY _110384)) = False.
Proof. exact (@lem4788564 _110384 x). Qed.
Lemma lem4788566 {_110384 : Type'} (x : _110384) : (term14 _110384 x) = False.
Proof. exact (TRANS (@lem4788562 _110384 x) (@lem4788565 _110384 x)). Qed.
Lemma lem4788567 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4788568 {_110384 : Type'} (x : _110384) : (term42 _110384 x) = (@eq Prop False).
Proof. exact (MK_COMB (@lem4788567) (@lem4788566 _110384 x)). Qed.
Lemma lem4788570 {_25376 : Type'} (x : _25376) : (@List.In _25376 x (@nil _25376)) = False.
Proof. exact (EQ_MP (@lem1103192 _25376 x) (@lem1103191 _25376 x)). Qed.
Lemma lem4788571 {_110384 : Type'} (x : _110384) : (@List.In _110384 x (@nil _110384)) = False.
Proof. exact (@lem4788570 _110384 x). Qed.
Lemma lem4788572 {_110384 : Type'} (x : _110384) : ((term14 _110384 x) = (@List.In _110384 x (@nil _110384))) = (False = False).
Proof. exact (MK_COMB (@lem4788568 _110384 x) (@lem4788571 _110384 x)). Qed.
Lemma lem4788574 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem4788575 : (False = False) = (~ False).
Proof. exact (@lem4788574 False). Qed.
Lemma lem4788577 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4788578 : (False = False) = True.
Proof. exact (TRANS (@lem4788575) (@lem4788577)). Qed.
Lemma lem4788579 {_110384 : Type'} (x : _110384) : ((term14 _110384 x) = (@List.In _110384 x (@nil _110384))) = True.
Proof. exact (TRANS (@lem4788572 _110384 x) (@lem4788578)). Qed.
Lemma lem4788580 {_110384 : Type'} (x : _110384) : True = ((term14 _110384 x) = (@List.In _110384 x (@nil _110384))).
Proof. exact (SYM (@lem4788579 _110384 x)). Qed.
Lemma lem4788581 {_110384 : Type'} (x : _110384) : (term14 _110384 x) = (@List.In _110384 x (@nil _110384)).
Proof. exact (EQ_MP (@lem4788580 _110384 x) (@lem0)). Qed.
Lemma lem4788585 {A : Type'} (h : A) (t : list A) : (term43 A h t) = (term44 A h t).
Proof. exact (EQ_MP (@lem4785471 A h t) (@lem4785470 A h t)). Qed.
Lemma lem4788586 {_110384 : Type'} (h : _110384) (t : list _110384) : (term43 _110384 h t) = (term44 _110384 h t).
Proof. exact (@lem4788585 _110384 h t). Qed.
Lemma lem4788587 {_110384 : Type'} (x : _110384) : (@IN _110384 x) = (@IN _110384 x).
Proof. exact (eq_refl (@IN _110384 x)). Qed.
Lemma lem4788588 {_110384 : Type'} (x : _110384) (h : _110384) (t : list _110384) : (term22 _110384 x h t) = (term45 _110384 x h t).
Proof. exact (MK_COMB (@lem4788587 _110384 x) (@lem4788586 _110384 h t)). Qed.
Lemma lem4788590 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term8 A x y s) = (term9 A y x s).
Proof. exact (EQ_MP (@lem4788526 A y x s) (@lem4788525 A y x s)). Qed.
Lemma lem4788591 {_110384 : Type'} (y : _110384) (x : _110384) (s : _110384 -> Prop) : (term8 _110384 x y s) = (term9 _110384 y x s).
Proof. exact (@lem4788590 _110384 y x s). Qed.
Lemma lem4788592 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) : (term45 _110384 x h t) = (term46 _110384 h x t).
Proof. exact (@lem4788591 _110384 h x (@set_of_list _110384 t)). Qed.
Lemma lem4788597 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) : (term22 _110384 x h t) = (term46 _110384 h x t).
Proof. exact (TRANS (@lem4788588 _110384 x h t) (@lem4788592 _110384 h x t)). Qed.
Lemma lem4788598 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4788599 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) : (term47 _110384 x h t) = (term48 _110384 h x t).
Proof. exact (MK_COMB (@lem4788598) (@lem4788597 _110384 h x t)). Qed.
Lemma lem4788601 {_25376 : Type'} (h : _25376) (x : _25376) (t : list _25376) : (term23 _25376 x h t) = (term49 _25376 h x t).
Proof. exact (EQ_MP (@lem1103201 _25376 h x t) (@lem1103200 _25376 h x t)). Qed.
Lemma lem4788602 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) : (term23 _110384 x h t) = (term49 _110384 h x t).
Proof. exact (@lem4788601 _110384 h x t). Qed.
Lemma lem4788607 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) : ((term22 _110384 x h t) = (term23 _110384 x h t)) = ((term46 _110384 h x t) = (term49 _110384 h x t)).
Proof. exact (MK_COMB (@lem4788599 _110384 h x t) (@lem4788602 _110384 h x t)). Qed.
Lemma lem4788610 {_110384 : Type'} (x : _110384) (h : _110384) (t : list _110384) : ((term46 _110384 h x t) = (term49 _110384 h x t)) = ((term22 _110384 x h t) = (term23 _110384 x h t)).
Proof. exact (SYM (@lem4788607 _110384 h x t)). Qed.
Lemma lem4788612 (p : Prop) : p = (term50 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4788613 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) : ((term46 _110384 h x t) = (term49 _110384 h x t)) = (term51 _110384 h x t).
Proof. exact (@lem4788612 ((term46 _110384 h x t) = (term49 _110384 h x t))). Qed.
Lemma lem4788614 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) : (term51 _110384 h x t) = ((term46 _110384 h x t) = (term49 _110384 h x t)).
Proof. exact (SYM (@lem4788613 _110384 h x t)). Qed.
Lemma lem4788615 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : term52 _110384 h x t) : term52 _110384 h x t.
Proof. exact (h1). Qed.
Lemma lem4788618 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : term53 _110384 h x t) : term53 _110384 h x t.
Proof. exact (h1). Qed.
Lemma lem4788619 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) : term54 _110384 h x t.
Proof. exact (fun h0 : term53 _110384 h x t => @lem4788618 _110384 h x t h0). Qed.
Lemma lem4788620 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : term54 _110384 h x t) : term54 _110384 h x t.
Proof. exact (h1). Qed.
Lemma lem4788621 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : term53 _110384 h x t) : term53 _110384 h x t.
Proof. exact (h1). Qed.
Lemma lem4788622 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : term53 _110384 h x t) (h2 : term54 _110384 h x t) : term53 _110384 h x t.
Proof. exact (@lem4788620 _110384 h x t h2 (@lem4788621 _110384 h x t h1)). Qed.
Lemma lem4788623 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : term53 _110384 h x t) : term55 _110384 h x t.
Proof. exact (fun h0 : term54 _110384 h x t => @lem4788622 _110384 h x t h1 h0). Qed.
Lemma lem4788624 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : term54 _110384 h x t) : term54 _110384 h x t.
Proof. exact (h1). Qed.
Lemma lem4788625 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : term53 _110384 h x t) (h2 : term54 _110384 h x t) : term53 _110384 h x t.
Proof. exact (@lem4788623 _110384 h x t h1 (@lem4788624 _110384 h x t h2)). Qed.
Lemma lem4788626 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : term54 _110384 h x t) : term54 _110384 h x t.
Proof. exact (fun h0 : term53 _110384 h x t => @lem4788625 _110384 h x t h0 h1). Qed.
Lemma lem4788627 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) : term56 _110384 h x t.
Proof. exact (fun h0 : term54 _110384 h x t => @lem4788626 _110384 h x t h0). Qed.
Lemma lem4788630 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) : term54 _110384 h x t.
Proof. exact (@lem4788627 _110384 h x t (@lem4788619 _110384 h x t)). Qed.
Lemma lem4788631 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) : term54 _110384 h x t.
Proof. exact (@lem4788630 _110384 h x t). Qed.
Lemma lem4788647 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4788648 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) : (term51 _110384 h x t) = (term57 _110384 h x t).
Proof. exact (@lem4788647 (term52 _110384 h x t)). Qed.
Lemma lem4788650 (t : Prop) : (term58 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4788651 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) : (term57 _110384 h x t) = ((term46 _110384 h x t) = (term49 _110384 h x t)).
Proof. exact (@lem4788650 ((term46 _110384 h x t) = (term49 _110384 h x t))). Qed.
Lemma lem4788652 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) : (term51 _110384 h x t) = ((term46 _110384 h x t) = (term49 _110384 h x t)).
Proof. exact (TRANS (@lem4788648 _110384 h x t) (@lem4788651 _110384 h x t)). Qed.
Lemma lem4788657 {_110384 : Type'} (x : _110384) (t : list _110384) : (term20 _110384 x t) = (term20 _110384 x t).
Proof. exact (eq_refl (term20 _110384 x t)). Qed.
Lemma lem4788658 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) : (term53 _110384 h x t) = (term59 _110384 h x t).
Proof. exact (MK_COMB (@lem4788657 _110384 x t) (@lem4788652 _110384 h x t)). Qed.
Lemma lem4788661 {_110384 : Type'} (x : _110384) (t : list _110384) : (term60 _110384 x t) = (term61 _110384 x t).
Proof. exact (fun_ext (fun h : _110384 => @lem4788658 _110384 h x t)). Qed.
Lemma lem4788662 {_110384 : Type'} : (@all _110384) = (@all _110384).
Proof. exact (eq_refl (@all _110384)). Qed.
Lemma lem4788663 {_110384 : Type'} (x : _110384) (t : list _110384) : (term62 _110384 x t) = (term63 _110384 x t).
Proof. exact (MK_COMB (@lem4788662 _110384) (@lem4788661 _110384 x t)). Qed.
Lemma lem4788668 {_110384 : Type'} (t : list _110384) : (term64 _110384 t) = (term65 _110384 t).
Proof. exact (fun_ext (fun x : _110384 => @lem4788663 _110384 x t)). Qed.
Lemma lem4788669 {_110384 : Type'} : (@all _110384) = (@all _110384).
Proof. exact (eq_refl (@all _110384)). Qed.
Lemma lem4788670 {_110384 : Type'} (t : list _110384) : (term66 _110384 t) = (term67 _110384 t).
Proof. exact (MK_COMB (@lem4788669 _110384) (@lem4788668 _110384 t)). Qed.
Lemma lem4788675 {_110384 : Type'} : (term68 _110384) = (term69 _110384).
Proof. exact (fun_ext (fun t : list _110384 => @lem4788670 _110384 t)). Qed.
Lemma lem4788676 {_110384 : Type'} : (@all (list _110384)) = (@all (list _110384)).
Proof. exact (eq_refl (@all (list _110384))). Qed.
Lemma lem4788685 {_110384 : Type'} : (term70 _110384) = (term71 _110384).
Proof. exact (MK_COMB (@lem4788676 _110384) (@lem4788675 _110384)). Qed.
Lemma lem4788706 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) : (term59 _110384 h x t) = (term59 _110384 h x t).
Proof. exact (eq_refl (term59 _110384 h x t)). Qed.
Lemma lem4788707 {_110384 : Type'} (x : _110384) (t : list _110384) : (term61 _110384 x t) = (term61 _110384 x t).
Proof. exact (fun_ext (fun h : _110384 => @lem4788706 _110384 h x t)). Qed.
Lemma lem4788708 {_110384 : Type'} : (@all _110384) = (@all _110384).
Proof. exact (eq_refl (@all _110384)). Qed.
Lemma lem4788709 {_110384 : Type'} (x : _110384) (t : list _110384) : (term63 _110384 x t) = (term63 _110384 x t).
Proof. exact (MK_COMB (@lem4788708 _110384) (@lem4788707 _110384 x t)). Qed.
Lemma lem4788710 {_110384 : Type'} (t : list _110384) : (term65 _110384 t) = (term65 _110384 t).
Proof. exact (fun_ext (fun x : _110384 => @lem4788709 _110384 x t)). Qed.
Lemma lem4788711 {_110384 : Type'} : (@all _110384) = (@all _110384).
Proof. exact (eq_refl (@all _110384)). Qed.
Lemma lem4788712 {_110384 : Type'} (t : list _110384) : (term67 _110384 t) = (term67 _110384 t).
Proof. exact (MK_COMB (@lem4788711 _110384) (@lem4788710 _110384 t)). Qed.
Lemma lem4788713 {_110384 : Type'} : (term69 _110384) = (term69 _110384).
Proof. exact (fun_ext (fun t : list _110384 => @lem4788712 _110384 t)). Qed.
Lemma lem4788714 {_110384 : Type'} : (@all (list _110384)) = (@all (list _110384)).
Proof. exact (eq_refl (@all (list _110384))). Qed.
Lemma lem4788715 {_110384 : Type'} : (term71 _110384) = (term71 _110384).
Proof. exact (MK_COMB (@lem4788714 _110384) (@lem4788713 _110384)). Qed.
Lemma lem4788742 {_110384 : Type'} : (term70 _110384) = (term71 _110384).
Proof. exact (TRANS (@lem4788685 _110384) (@lem4788715 _110384)). Qed.
Lemma lem4788743 {_110384 : Type'} : (term71 _110384) = (term70 _110384).
Proof. exact (SYM (@lem4788742 _110384)). Qed.
Lemma lem4788744 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : (term18 _110384 x t) = (@List.In _110384 x t)) : (term18 _110384 x t) = (@List.In _110384 x t).
Proof. exact (h1). Qed.
Lemma lem4788746 (p : Prop) : p = (term50 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4788747 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) : ((term46 _110384 h x t) = (term49 _110384 h x t)) = (term51 _110384 h x t).
Proof. exact (@lem4788746 ((term46 _110384 h x t) = (term49 _110384 h x t))). Qed.
Lemma lem4788748 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) : (term51 _110384 h x t) = ((term46 _110384 h x t) = (term49 _110384 h x t)).
Proof. exact (SYM (@lem4788747 _110384 h x t)). Qed.
Lemma lem4788749 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : term52 _110384 h x t) : term52 _110384 h x t.
Proof. exact (h1). Qed.
Lemma lem4788768 {_110384 : Type'} (x : _110384) (t : list _110384) : ((term18 _110384 x t) = (@List.In _110384 x t)) = (term72 _110384 x t).
Proof. exact (@lem17500 (term18 _110384 x t) (@List.In _110384 x t)). Qed.
Lemma lem4788778 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) : (term73 _110384 h x t) = (term74 _110384 h x t).
Proof. exact (@lem17160 (x = h) (term18 _110384 x t)). Qed.
Lemma lem4788790 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) : (term75 _110384 h x t) = (term76 _110384 h x t).
Proof. exact (@lem17160 (x = h) (@List.In _110384 x t)). Qed.
Lemma lem4788793 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) : (term49 _110384 h x t) = (term49 _110384 h x t).
Proof. exact (eq_refl (term49 _110384 h x t)). Qed.
Lemma lem4788794 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4788795 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) : (term77 _110384 h x t) = (term78 _110384 h x t).
Proof. exact (MK_COMB (@lem4788794) (@lem4788778 _110384 h x t)). Qed.
Lemma lem4788796 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) : (term79 _110384 h x t) = (term80 _110384 h x t).
Proof. exact (MK_COMB (@lem4788795 _110384 h x t) (@lem4788793 _110384 h x t)). Qed.
Lemma lem4788798 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) : (term81 _110384 h x t) = (term81 _110384 h x t).
Proof. exact (eq_refl (term81 _110384 h x t)). Qed.
Lemma lem4788799 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) : (term82 _110384 h x t) = (term83 _110384 h x t).
Proof. exact (MK_COMB (@lem4788798 _110384 h x t) (@lem4788790 _110384 h x t)). Qed.
Lemma lem4788800 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4788801 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) : (term84 _110384 h x t) = (term85 _110384 h x t).
Proof. exact (MK_COMB (@lem4788800) (@lem4788799 _110384 h x t)). Qed.
Lemma lem4788802 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) : (term86 _110384 h x t) = (term87 _110384 h x t).
Proof. exact (MK_COMB (@lem4788801 _110384 h x t) (@lem4788796 _110384 h x t)). Qed.
Lemma lem4788803 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) : (term52 _110384 h x t) = (term86 _110384 h x t).
Proof. exact (@lem17646 (term46 _110384 h x t) (term49 _110384 h x t)). Qed.
Lemma lem4788808 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) : (term52 _110384 h x t) = (term87 _110384 h x t).
Proof. exact (TRANS (@lem4788803 _110384 h x t) (@lem4788802 _110384 h x t)). Qed.
Lemma lem4788847 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : (term18 _110384 x t) = (@List.In _110384 x t)) : term72 _110384 x t.
Proof. exact (EQ_MP (@lem4788768 _110384 x t) (@lem4788744 _110384 x t h1)). Qed.
Lemma lem4788921 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : term52 _110384 h x t) : term87 _110384 h x t.
Proof. exact (EQ_MP (@lem4788808 _110384 h x t) (@lem4788749 _110384 h x t h1)). Qed.
Lemma lem4788922 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : term83 _110384 h x t) : term83 _110384 h x t.
Proof. exact (h1). Qed.
Lemma lem4788923 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : term80 _110384 h x t) : term80 _110384 h x t.
Proof. exact (h1). Qed.
Lemma lem4788924 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : term83 _110384 h x t) : term76 _110384 h x t.
Proof. exact (proj2 (@lem4788922 _110384 h x t h1)). Qed.
Lemma lem4788925 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : term83 _110384 h x t) : term46 _110384 h x t.
Proof. exact (proj1 (@lem4788922 _110384 h x t h1)). Qed.
Lemma lem4788930 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : term88 _110384 x t) : term88 _110384 x t.
Proof. exact (h1). Qed.
Lemma lem4788936 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : term88 _110384 x t) : term88 _110384 x t.
Proof. exact (h1). Qed.
Lemma lem4788937 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : term89 _110384 x t) : term89 _110384 x t.
Proof. exact (h1). Qed.
Lemma lem4788942 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : term80 _110384 h x t) : term49 _110384 h x t.
Proof. exact (proj2 (@lem4788923 _110384 h x t h1)). Qed.
Lemma lem4788943 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : term80 _110384 h x t) : term74 _110384 h x t.
Proof. exact (proj1 (@lem4788923 _110384 h x t h1)). Qed.
Lemma lem4788948 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : term88 _110384 x t) : term88 _110384 x t.
Proof. exact (h1). Qed.
Lemma lem4788954 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : term88 _110384 x t) : term88 _110384 x t.
Proof. exact (h1). Qed.
Lemma lem4788955 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : term89 _110384 x t) : term89 _110384 x t.
Proof. exact (h1). Qed.
Lemma lem4788971 {_110384 : Type'} (x : _110384) (h : _110384) (h1 : x = h) : x = h.
Proof. exact (h1). Qed.
Lemma lem4788991 {_110384 : Type'} (x : _110384) (h : _110384) (h1 : x = h) : x = h.
Proof. exact (h1). Qed.
Lemma lem4789031 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : term18 _110384 x t) : term18 _110384 x t.
Proof. exact (h1). Qed.
Lemma lem4789051 {_110384 : Type'} (x : _110384) (h : _110384) (h1 : x = h) : x = h.
Proof. exact (h1). Qed.
Lemma lem4789071 {_110384 : Type'} (x : _110384) (h : _110384) (h1 : x = h) : x = h.
Proof. exact (h1). Qed.
Lemma lem4789111 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : @List.In _110384 x t) : @List.In _110384 x t.
Proof. exact (h1). Qed.
Lemma lem4789123 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : term83 _110384 h x t) : term90 _110384 x t.
Proof. exact (proj2 (@lem4788924 _110384 h x t h1)). Qed.
Lemma lem4789125 {_110384 : Type'} (x : _110384) (h : _110384) (h1 : x = h) : x = h.
Proof. exact (h1). Qed.
Lemma lem4789129 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : term88 _110384 x t) : @List.In _110384 x t.
Proof. exact (proj2 (@lem4788930 _110384 x t h1)). Qed.
Lemma lem4789131 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : term83 _110384 h x t) : term91 _110384 x h.
Proof. exact (proj1 (@lem4788924 _110384 h x t h1)). Qed.
Lemma lem4789135 {_110384 : Type'} (x : _110384) (h : _110384) (h1 : x = h) : x = h.
Proof. exact (h1). Qed.
Lemma lem4789143 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : term83 _110384 h x t) : term90 _110384 x t.
Proof. exact (proj2 (@lem4788924 _110384 h x t h1)). Qed.
Lemma lem4789155 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : term18 _110384 x t) : term18 _110384 x t.
Proof. exact (h1). Qed.
Lemma lem4789157 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : term89 _110384 x t) : term92 _110384 x t.
Proof. exact (proj1 (@lem4788937 _110384 x t h1)). Qed.
Lemma lem4789163 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : term80 _110384 h x t) : term92 _110384 x t.
Proof. exact (proj2 (@lem4788943 _110384 h x t h1)). Qed.
Lemma lem4789165 {_110384 : Type'} (x : _110384) (h : _110384) (h1 : x = h) : x = h.
Proof. exact (h1). Qed.
Lemma lem4789167 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : term88 _110384 x t) : term18 _110384 x t.
Proof. exact (proj1 (@lem4788948 _110384 x t h1)). Qed.
Lemma lem4789171 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : term80 _110384 h x t) : term91 _110384 x h.
Proof. exact (proj1 (@lem4788943 _110384 h x t h1)). Qed.
Lemma lem4789175 {_110384 : Type'} (x : _110384) (h : _110384) (h1 : x = h) : x = h.
Proof. exact (h1). Qed.
Lemma lem4789183 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : term80 _110384 h x t) : term92 _110384 x t.
Proof. exact (proj2 (@lem4788943 _110384 h x t h1)). Qed.
Lemma lem4789195 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : @List.In _110384 x t) : @List.In _110384 x t.
Proof. exact (h1). Qed.
Lemma lem4789199 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : term89 _110384 x t) : term90 _110384 x t.
Proof. exact (proj2 (@lem4788955 _110384 x t h1)). Qed.
Lemma lem4789227 {_110384 : Type'} (t : list _110384) : (term93 _110384 t) = (term93 _110384 t).
Proof. exact (eq_refl (term93 _110384 t)). Qed.
Lemma lem4789228 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : x = h) : (term94 _110384 t x) = (term94 _110384 t h).
Proof. exact (MK_COMB (@lem4789227 _110384 t) (@lem4789125 _110384 x h h1)). Qed.
Lemma lem4789229 {_110384 : Type'} (h : _110384) (t : list _110384) : (term94 _110384 t h) = (term90 _110384 h t).
Proof. exact (eq_refl (term94 _110384 t h)). Qed.
Lemma lem4789230 {_110384 : Type'} (t : list _110384) (x : _110384) : (term95 _110384 t x) = (term95 _110384 t x).
Proof. exact (eq_refl (term95 _110384 t x)). Qed.
Lemma lem4789231 {_110384 : Type'} (x : _110384) (h : _110384) (t : list _110384) : ((term94 _110384 t x) = (term94 _110384 t h)) = ((term94 _110384 t x) = (term90 _110384 h t)).
Proof. exact (MK_COMB (@lem4789230 _110384 t x) (@lem4789229 _110384 h t)). Qed.
Lemma lem4789232 {_110384 : Type'} (x : _110384) (t : list _110384) : (term94 _110384 t x) = (term90 _110384 x t).
Proof. exact (eq_refl (term94 _110384 t x)). Qed.
Lemma lem4789233 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4789234 {_110384 : Type'} (x : _110384) (t : list _110384) : (term95 _110384 t x) = (term96 _110384 x t).
Proof. exact (MK_COMB (@lem4789233) (@lem4789232 _110384 x t)). Qed.
Lemma lem4789235 {_110384 : Type'} (h : _110384) (t : list _110384) : (term90 _110384 h t) = (term90 _110384 h t).
Proof. exact (eq_refl (term90 _110384 h t)). Qed.
Lemma lem4789236 {_110384 : Type'} (x : _110384) (h : _110384) (t : list _110384) : ((term94 _110384 t x) = (term90 _110384 h t)) = ((term90 _110384 x t) = (term90 _110384 h t)).
Proof. exact (MK_COMB (@lem4789234 _110384 x t) (@lem4789235 _110384 h t)). Qed.
Lemma lem4789237 {_110384 : Type'} (x : _110384) (h : _110384) (t : list _110384) : ((term94 _110384 t x) = (term94 _110384 t h)) = ((term90 _110384 x t) = (term90 _110384 h t)).
Proof. exact (TRANS (@lem4789231 _110384 x h t) (@lem4789236 _110384 x h t)). Qed.
Lemma lem4789238 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : x = h) : (term90 _110384 x t) = (term90 _110384 h t).
Proof. exact (EQ_MP (@lem4789237 _110384 x h t) (@lem4789228 _110384 t x h h1)). Qed.
Lemma lem4789239 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term83 _110384 h x t) (h2 : x = h) : term90 _110384 h t.
Proof. exact (EQ_MP (@lem4789238 _110384 t x h h2) (@lem4789123 _110384 h x t h1)). Qed.
Lemma lem4789253 {_110384 : Type'} (t : list _110384) : (term97 _110384 t) = (term97 _110384 t).
Proof. exact (eq_refl (term97 _110384 t)). Qed.
Lemma lem4789254 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : x = h) : (term98 _110384 t x) = (term98 _110384 t h).
Proof. exact (MK_COMB (@lem4789253 _110384 t) (@lem4789125 _110384 x h h1)). Qed.
Lemma lem4789255 {_110384 : Type'} (h : _110384) (t : list _110384) : (term98 _110384 t h) = (@List.In _110384 h t).
Proof. exact (eq_refl (term98 _110384 t h)). Qed.
Lemma lem4789256 {_110384 : Type'} (t : list _110384) (x : _110384) : (term99 _110384 t x) = (term99 _110384 t x).
Proof. exact (eq_refl (term99 _110384 t x)). Qed.
Lemma lem4789257 {_110384 : Type'} (x : _110384) (h : _110384) (t : list _110384) : ((term98 _110384 t x) = (term98 _110384 t h)) = ((term98 _110384 t x) = (@List.In _110384 h t)).
Proof. exact (MK_COMB (@lem4789256 _110384 t x) (@lem4789255 _110384 h t)). Qed.
Lemma lem4789258 {_110384 : Type'} (x : _110384) (t : list _110384) : (term98 _110384 t x) = (@List.In _110384 x t).
Proof. exact (eq_refl (term98 _110384 t x)). Qed.
Lemma lem4789259 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4789260 {_110384 : Type'} (x : _110384) (t : list _110384) : (term99 _110384 t x) = (term100 _110384 x t).
Proof. exact (MK_COMB (@lem4789259) (@lem4789258 _110384 x t)). Qed.
Lemma lem4789261 {_110384 : Type'} (h : _110384) (t : list _110384) : (@List.In _110384 h t) = (@List.In _110384 h t).
Proof. exact (eq_refl (@List.In _110384 h t)). Qed.
Lemma lem4789262 {_110384 : Type'} (x : _110384) (h : _110384) (t : list _110384) : ((term98 _110384 t x) = (@List.In _110384 h t)) = ((@List.In _110384 x t) = (@List.In _110384 h t)).
Proof. exact (MK_COMB (@lem4789260 _110384 x t) (@lem4789261 _110384 h t)). Qed.
Lemma lem4789263 {_110384 : Type'} (x : _110384) (h : _110384) (t : list _110384) : ((term98 _110384 t x) = (term98 _110384 t h)) = ((@List.In _110384 x t) = (@List.In _110384 h t)).
Proof. exact (TRANS (@lem4789257 _110384 x h t) (@lem4789262 _110384 x h t)). Qed.
Lemma lem4789264 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : x = h) : (@List.In _110384 x t) = (@List.In _110384 h t).
Proof. exact (EQ_MP (@lem4789263 _110384 x h t) (@lem4789254 _110384 t x h h1)). Qed.
Lemma lem4789280 {_110384 : Type'} (h : _110384) : (term101 _110384 h) = (term101 _110384 h).
Proof. exact (eq_refl (term101 _110384 h)). Qed.
Lemma lem4789281 {_110384 : Type'} (x : _110384) (h : _110384) (h1 : x = h) : (term102 _110384 h x) = (term103 _110384 h).
Proof. exact (MK_COMB (@lem4789280 _110384 h) (@lem4789135 _110384 x h h1)). Qed.
Lemma lem4789282 {_110384 : Type'} (h : _110384) : (term103 _110384 h) = (term104 _110384 h).
Proof. exact (eq_refl (term103 _110384 h)). Qed.
Lemma lem4789283 {_110384 : Type'} (h : _110384) (x : _110384) : (term105 _110384 h x) = (term105 _110384 h x).
Proof. exact (eq_refl (term105 _110384 h x)). Qed.
Lemma lem4789284 {_110384 : Type'} (x : _110384) (h : _110384) : ((term102 _110384 h x) = (term103 _110384 h)) = ((term102 _110384 h x) = (term104 _110384 h)).
Proof. exact (MK_COMB (@lem4789283 _110384 h x) (@lem4789282 _110384 h)). Qed.
Lemma lem4789285 {_110384 : Type'} (x : _110384) (h : _110384) : (term102 _110384 h x) = (term91 _110384 x h).
Proof. exact (eq_refl (term102 _110384 h x)). Qed.
Lemma lem4789286 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4789287 {_110384 : Type'} (x : _110384) (h : _110384) : (term105 _110384 h x) = (term106 _110384 x h).
Proof. exact (MK_COMB (@lem4789286) (@lem4789285 _110384 x h)). Qed.
Lemma lem4789288 {_110384 : Type'} (h : _110384) : (term104 _110384 h) = (term104 _110384 h).
Proof. exact (eq_refl (term104 _110384 h)). Qed.
Lemma lem4789289 {_110384 : Type'} (x : _110384) (h : _110384) : ((term102 _110384 h x) = (term104 _110384 h)) = ((term91 _110384 x h) = (term104 _110384 h)).
Proof. exact (MK_COMB (@lem4789287 _110384 x h) (@lem4789288 _110384 h)). Qed.
Lemma lem4789290 {_110384 : Type'} (x : _110384) (h : _110384) : ((term102 _110384 h x) = (term103 _110384 h)) = ((term91 _110384 x h) = (term104 _110384 h)).
Proof. exact (TRANS (@lem4789284 _110384 x h) (@lem4789289 _110384 x h)). Qed.
Lemma lem4789291 {_110384 : Type'} (x : _110384) (h : _110384) (h1 : x = h) : (term91 _110384 x h) = (term104 _110384 h).
Proof. exact (EQ_MP (@lem4789290 _110384 x h) (@lem4789281 _110384 x h h1)). Qed.
Lemma lem4789292 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term83 _110384 h x t) (h2 : x = h) : term104 _110384 h.
Proof. exact (EQ_MP (@lem4789291 _110384 x h h2) (@lem4789131 _110384 h x t h1)). Qed.
Lemma lem4789359 {_110384 : Type'} (t : list _110384) : (term107 _110384 t) = (term107 _110384 t).
Proof. exact (eq_refl (term107 _110384 t)). Qed.
Lemma lem4789360 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : x = h) : (term108 _110384 t x) = (term108 _110384 t h).
Proof. exact (MK_COMB (@lem4789359 _110384 t) (@lem4789165 _110384 x h h1)). Qed.
Lemma lem4789361 {_110384 : Type'} (h : _110384) (t : list _110384) : (term108 _110384 t h) = (term92 _110384 h t).
Proof. exact (eq_refl (term108 _110384 t h)). Qed.
Lemma lem4789362 {_110384 : Type'} (t : list _110384) (x : _110384) : (term109 _110384 t x) = (term109 _110384 t x).
Proof. exact (eq_refl (term109 _110384 t x)). Qed.
Lemma lem4789363 {_110384 : Type'} (x : _110384) (h : _110384) (t : list _110384) : ((term108 _110384 t x) = (term108 _110384 t h)) = ((term108 _110384 t x) = (term92 _110384 h t)).
Proof. exact (MK_COMB (@lem4789362 _110384 t x) (@lem4789361 _110384 h t)). Qed.
Lemma lem4789364 {_110384 : Type'} (x : _110384) (t : list _110384) : (term108 _110384 t x) = (term92 _110384 x t).
Proof. exact (eq_refl (term108 _110384 t x)). Qed.
Lemma lem4789365 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4789366 {_110384 : Type'} (x : _110384) (t : list _110384) : (term109 _110384 t x) = (term110 _110384 x t).
Proof. exact (MK_COMB (@lem4789365) (@lem4789364 _110384 x t)). Qed.
Lemma lem4789367 {_110384 : Type'} (h : _110384) (t : list _110384) : (term92 _110384 h t) = (term92 _110384 h t).
Proof. exact (eq_refl (term92 _110384 h t)). Qed.
Lemma lem4789368 {_110384 : Type'} (x : _110384) (h : _110384) (t : list _110384) : ((term108 _110384 t x) = (term92 _110384 h t)) = ((term92 _110384 x t) = (term92 _110384 h t)).
Proof. exact (MK_COMB (@lem4789366 _110384 x t) (@lem4789367 _110384 h t)). Qed.
Lemma lem4789369 {_110384 : Type'} (x : _110384) (h : _110384) (t : list _110384) : ((term108 _110384 t x) = (term108 _110384 t h)) = ((term92 _110384 x t) = (term92 _110384 h t)).
Proof. exact (TRANS (@lem4789363 _110384 x h t) (@lem4789368 _110384 x h t)). Qed.
Lemma lem4789370 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : x = h) : (term92 _110384 x t) = (term92 _110384 h t).
Proof. exact (EQ_MP (@lem4789369 _110384 x h t) (@lem4789360 _110384 t x h h1)). Qed.
Lemma lem4789371 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term80 _110384 h x t) (h2 : x = h) : term92 _110384 h t.
Proof. exact (EQ_MP (@lem4789370 _110384 t x h h2) (@lem4789163 _110384 h x t h1)). Qed.
Lemma lem4789372 {_110384 : Type'} (t : list _110384) : (term111 _110384 t) = (term111 _110384 t).
Proof. exact (eq_refl (term111 _110384 t)). Qed.
Lemma lem4789373 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : x = h) : (term112 _110384 t x) = (term112 _110384 t h).
Proof. exact (MK_COMB (@lem4789372 _110384 t) (@lem4789165 _110384 x h h1)). Qed.
Lemma lem4789374 {_110384 : Type'} (h : _110384) (t : list _110384) : (term112 _110384 t h) = (term18 _110384 h t).
Proof. exact (eq_refl (term112 _110384 t h)). Qed.
Lemma lem4789375 {_110384 : Type'} (t : list _110384) (x : _110384) : (term113 _110384 t x) = (term113 _110384 t x).
Proof. exact (eq_refl (term113 _110384 t x)). Qed.
Lemma lem4789376 {_110384 : Type'} (x : _110384) (h : _110384) (t : list _110384) : ((term112 _110384 t x) = (term112 _110384 t h)) = ((term112 _110384 t x) = (term18 _110384 h t)).
Proof. exact (MK_COMB (@lem4789375 _110384 t x) (@lem4789374 _110384 h t)). Qed.
Lemma lem4789377 {_110384 : Type'} (x : _110384) (t : list _110384) : (term112 _110384 t x) = (term18 _110384 x t).
Proof. exact (eq_refl (term112 _110384 t x)). Qed.
Lemma lem4789378 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4789379 {_110384 : Type'} (x : _110384) (t : list _110384) : (term113 _110384 t x) = (term114 _110384 x t).
Proof. exact (MK_COMB (@lem4789378) (@lem4789377 _110384 x t)). Qed.
Lemma lem4789380 {_110384 : Type'} (h : _110384) (t : list _110384) : (term18 _110384 h t) = (term18 _110384 h t).
Proof. exact (eq_refl (term18 _110384 h t)). Qed.
Lemma lem4789381 {_110384 : Type'} (x : _110384) (h : _110384) (t : list _110384) : ((term112 _110384 t x) = (term18 _110384 h t)) = ((term18 _110384 x t) = (term18 _110384 h t)).
Proof. exact (MK_COMB (@lem4789379 _110384 x t) (@lem4789380 _110384 h t)). Qed.
Lemma lem4789382 {_110384 : Type'} (x : _110384) (h : _110384) (t : list _110384) : ((term112 _110384 t x) = (term112 _110384 t h)) = ((term18 _110384 x t) = (term18 _110384 h t)).
Proof. exact (TRANS (@lem4789376 _110384 x h t) (@lem4789381 _110384 x h t)). Qed.
Lemma lem4789383 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : x = h) : (term18 _110384 x t) = (term18 _110384 h t).
Proof. exact (EQ_MP (@lem4789382 _110384 x h t) (@lem4789373 _110384 t x h h1)). Qed.
Lemma lem4789412 {_110384 : Type'} (h : _110384) : (term101 _110384 h) = (term101 _110384 h).
Proof. exact (eq_refl (term101 _110384 h)). Qed.
Lemma lem4789413 {_110384 : Type'} (x : _110384) (h : _110384) (h1 : x = h) : (term102 _110384 h x) = (term103 _110384 h).
Proof. exact (MK_COMB (@lem4789412 _110384 h) (@lem4789175 _110384 x h h1)). Qed.
Lemma lem4789414 {_110384 : Type'} (h : _110384) : (term103 _110384 h) = (term104 _110384 h).
Proof. exact (eq_refl (term103 _110384 h)). Qed.
Lemma lem4789415 {_110384 : Type'} (h : _110384) (x : _110384) : (term105 _110384 h x) = (term105 _110384 h x).
Proof. exact (eq_refl (term105 _110384 h x)). Qed.
Lemma lem4789416 {_110384 : Type'} (x : _110384) (h : _110384) : ((term102 _110384 h x) = (term103 _110384 h)) = ((term102 _110384 h x) = (term104 _110384 h)).
Proof. exact (MK_COMB (@lem4789415 _110384 h x) (@lem4789414 _110384 h)). Qed.
Lemma lem4789417 {_110384 : Type'} (x : _110384) (h : _110384) : (term102 _110384 h x) = (term91 _110384 x h).
Proof. exact (eq_refl (term102 _110384 h x)). Qed.
Lemma lem4789418 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4789419 {_110384 : Type'} (x : _110384) (h : _110384) : (term105 _110384 h x) = (term106 _110384 x h).
Proof. exact (MK_COMB (@lem4789418) (@lem4789417 _110384 x h)). Qed.
Lemma lem4789420 {_110384 : Type'} (h : _110384) : (term104 _110384 h) = (term104 _110384 h).
Proof. exact (eq_refl (term104 _110384 h)). Qed.
Lemma lem4789421 {_110384 : Type'} (x : _110384) (h : _110384) : ((term102 _110384 h x) = (term104 _110384 h)) = ((term91 _110384 x h) = (term104 _110384 h)).
Proof. exact (MK_COMB (@lem4789419 _110384 x h) (@lem4789420 _110384 h)). Qed.
Lemma lem4789422 {_110384 : Type'} (x : _110384) (h : _110384) : ((term102 _110384 h x) = (term103 _110384 h)) = ((term91 _110384 x h) = (term104 _110384 h)).
Proof. exact (TRANS (@lem4789416 _110384 x h) (@lem4789421 _110384 x h)). Qed.
Lemma lem4789423 {_110384 : Type'} (x : _110384) (h : _110384) (h1 : x = h) : (term91 _110384 x h) = (term104 _110384 h).
Proof. exact (EQ_MP (@lem4789422 _110384 x h) (@lem4789413 _110384 x h h1)). Qed.
Lemma lem4789424 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term80 _110384 h x t) (h2 : x = h) : term104 _110384 h.
Proof. exact (EQ_MP (@lem4789423 _110384 x h h2) (@lem4789171 _110384 h x t h1)). Qed.
Lemma lem4789517 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term88 _110384 x t) (h2 : x = h) : @List.In _110384 h t.
Proof. exact (EQ_MP (@lem4789264 _110384 t x h h2) (@lem4789129 _110384 x t h1)). Qed.
Lemma lem4789518 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term88 _110384 x t) (h2 : x = h) : term115 _110384 h t.
Proof. exact (fun h0 : term90 _110384 h t => @lem4789517 _110384 t x h h1 h2). Qed.
Lemma lem4789520 (p : Prop) : (term116 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4789521 {_110384 : Type'} (h : _110384) (t : list _110384) : (term115 _110384 h t) = (@List.In _110384 h t).
Proof. exact (@lem4789520 (@List.In _110384 h t)). Qed.
Lemma lem4789522 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term88 _110384 x t) (h2 : x = h) : @List.In _110384 h t.
Proof. exact (EQ_MP (@lem4789521 _110384 h t) (@lem4789518 _110384 t x h h1 h2)). Qed.
Lemma lem4789525 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4789527 {_110384 : Type'} (h : _110384) (t : list _110384) : (term90 _110384 h t) = (term117 _110384 h t).
Proof. exact (@lem4789525 (@List.In _110384 h t)). Qed.
Lemma lem4789530 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term83 _110384 h x t) (h2 : x = h) : term117 _110384 h t.
Proof. exact (EQ_MP (@lem4789527 _110384 h t) (@lem4789239 _110384 t x h h1 h2)). Qed.
Lemma lem4789533 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term88 _110384 x t) (h2 : term83 _110384 h x t) (h3 : x = h) : False.
Proof. exact (@lem4789530 _110384 t x h h2 h3 (@lem4789522 _110384 t x h h1 h3)). Qed.
Lemma lem4789534 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term88 _110384 x t) (h2 : term83 _110384 h x t) (h3 : x = h) : term118.
Proof. exact (fun h0 : ~ False => @lem4789533 _110384 t x h h1 h2 h3). Qed.
Lemma lem4789536 (p : Prop) : (term116 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4789537 : term118 = False.
Proof. exact (@lem4789536 False). Qed.
Lemma lem4789592 {_110384 : Type'} (x : _110384) : x = x.
Proof. exact (@lem21386 _110384 x). Qed.
Lemma lem4789593 {_110384 : Type'} (x : _110384) : x = x.
Proof. exact (@lem4789592 _110384 x). Qed.
Lemma lem4789594 {_110384 : Type'} (h : _110384) : h = h.
Proof. exact (@lem4789593 _110384 h). Qed.
Lemma lem4789595 {_110384 : Type'} (h : _110384) : term119 _110384 h.
Proof. exact (fun h0 : term104 _110384 h => @lem4789594 _110384 h). Qed.
Lemma lem4789597 (p : Prop) : (term116 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4789598 {_110384 : Type'} (h : _110384) : (term119 _110384 h) = (h = h).
Proof. exact (@lem4789597 (h = h)). Qed.
Lemma lem4789599 {_110384 : Type'} (h : _110384) : h = h.
Proof. exact (EQ_MP (@lem4789598 _110384 h) (@lem4789595 _110384 h)). Qed.
Lemma lem4789602 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4789604 {_110384 : Type'} (h : _110384) : (term104 _110384 h) = (term120 _110384 h).
Proof. exact (@lem4789602 (h = h)). Qed.
Lemma lem4789607 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term83 _110384 h x t) (h2 : x = h) : term120 _110384 h.
Proof. exact (EQ_MP (@lem4789604 _110384 h) (@lem4789292 _110384 t x h h1 h2)). Qed.
Lemma lem4789610 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term83 _110384 h x t) (h2 : x = h) : False.
Proof. exact (@lem4789607 _110384 t x h h1 h2 (@lem4789599 _110384 h)). Qed.
Lemma lem4789611 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term83 _110384 h x t) (h2 : x = h) : term118.
Proof. exact (fun h0 : ~ False => @lem4789610 _110384 t x h h1 h2). Qed.
Lemma lem4789613 (p : Prop) : (term116 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4789614 : term118 = False.
Proof. exact (@lem4789613 False). Qed.
Lemma lem4789669 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : term88 _110384 x t) : @List.In _110384 x t.
Proof. exact (proj2 (@lem4788936 _110384 x t h1)). Qed.
Lemma lem4789670 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : term88 _110384 x t) : term115 _110384 x t.
Proof. exact (fun h0 : term90 _110384 x t => @lem4789669 _110384 x t h1). Qed.
Lemma lem4789672 (p : Prop) : (term116 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4789673 {_110384 : Type'} (x : _110384) (t : list _110384) : (term115 _110384 x t) = (@List.In _110384 x t).
Proof. exact (@lem4789672 (@List.In _110384 x t)). Qed.
Lemma lem4789674 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : term88 _110384 x t) : @List.In _110384 x t.
Proof. exact (EQ_MP (@lem4789673 _110384 x t) (@lem4789670 _110384 x t h1)). Qed.
Lemma lem4789677 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4789679 {_110384 : Type'} (x : _110384) (t : list _110384) : (term90 _110384 x t) = (term117 _110384 x t).
Proof. exact (@lem4789677 (@List.In _110384 x t)). Qed.
Lemma lem4789682 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : term83 _110384 h x t) : term117 _110384 x t.
Proof. exact (EQ_MP (@lem4789679 _110384 x t) (@lem4789143 _110384 h x t h1)). Qed.
Lemma lem4789685 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : term88 _110384 x t) (h2 : term83 _110384 h x t) : False.
Proof. exact (@lem4789682 _110384 h x t h2 (@lem4789674 _110384 x t h1)). Qed.
Lemma lem4789686 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : term88 _110384 x t) (h2 : term83 _110384 h x t) : term118.
Proof. exact (fun h0 : ~ False => @lem4789685 _110384 h x t h1 h2). Qed.
Lemma lem4789688 (p : Prop) : (term116 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4789689 : term118 = False.
Proof. exact (@lem4789688 False). Qed.
Lemma lem4789690 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : term88 _110384 x t) (h2 : term83 _110384 h x t) : False.
Proof. exact (EQ_MP (@lem4789689) (@lem4789686 _110384 h x t h1 h2)). Qed.
Lemma lem4789744 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : term18 _110384 x t) : term18 _110384 x t.
Proof. exact (h1). Qed.
Lemma lem4789745 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : term18 _110384 x t) : term121 _110384 x t.
Proof. exact (fun h0 : term92 _110384 x t => @lem4789744 _110384 x t h1). Qed.
Lemma lem4789747 (p : Prop) : (term116 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4789748 {_110384 : Type'} (x : _110384) (t : list _110384) : (term121 _110384 x t) = (term18 _110384 x t).
Proof. exact (@lem4789747 (term18 _110384 x t)). Qed.
Lemma lem4789749 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : term18 _110384 x t) : term18 _110384 x t.
Proof. exact (EQ_MP (@lem4789748 _110384 x t) (@lem4789745 _110384 x t h1)). Qed.
Lemma lem4789752 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4789754 {_110384 : Type'} (x : _110384) (t : list _110384) : (term92 _110384 x t) = (term122 _110384 x t).
Proof. exact (@lem4789752 (term18 _110384 x t)). Qed.
Lemma lem4789757 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : term89 _110384 x t) : term122 _110384 x t.
Proof. exact (EQ_MP (@lem4789754 _110384 x t) (@lem4789157 _110384 x t h1)). Qed.
Lemma lem4789760 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : term89 _110384 x t) (h2 : term18 _110384 x t) : False.
Proof. exact (@lem4789757 _110384 x t h1 (@lem4789749 _110384 x t h2)). Qed.
Lemma lem4789761 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : term89 _110384 x t) (h2 : term18 _110384 x t) : term118.
Proof. exact (fun h0 : ~ False => @lem4789760 _110384 x t h1 h2). Qed.
Lemma lem4789763 (p : Prop) : (term116 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4789764 : term118 = False.
Proof. exact (@lem4789763 False). Qed.
Lemma lem4789765 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : term89 _110384 x t) (h2 : term18 _110384 x t) : False.
Proof. exact (EQ_MP (@lem4789764) (@lem4789761 _110384 x t h1 h2)). Qed.
Lemma lem4789819 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term88 _110384 x t) (h2 : x = h) : term18 _110384 h t.
Proof. exact (EQ_MP (@lem4789383 _110384 t x h h2) (@lem4789167 _110384 x t h1)). Qed.
Lemma lem4789820 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term88 _110384 x t) (h2 : x = h) : term121 _110384 h t.
Proof. exact (fun h0 : term92 _110384 h t => @lem4789819 _110384 t x h h1 h2). Qed.
Lemma lem4789822 (p : Prop) : (term116 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4789823 {_110384 : Type'} (h : _110384) (t : list _110384) : (term121 _110384 h t) = (term18 _110384 h t).
Proof. exact (@lem4789822 (term18 _110384 h t)). Qed.
Lemma lem4789824 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term88 _110384 x t) (h2 : x = h) : term18 _110384 h t.
Proof. exact (EQ_MP (@lem4789823 _110384 h t) (@lem4789820 _110384 t x h h1 h2)). Qed.
Lemma lem4789827 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4789829 {_110384 : Type'} (h : _110384) (t : list _110384) : (term92 _110384 h t) = (term122 _110384 h t).
Proof. exact (@lem4789827 (term18 _110384 h t)). Qed.
Lemma lem4789832 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term80 _110384 h x t) (h2 : x = h) : term122 _110384 h t.
Proof. exact (EQ_MP (@lem4789829 _110384 h t) (@lem4789371 _110384 t x h h1 h2)). Qed.
Lemma lem4789835 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term80 _110384 h x t) (h2 : term88 _110384 x t) (h3 : x = h) : False.
Proof. exact (@lem4789832 _110384 t x h h1 h3 (@lem4789824 _110384 t x h h2 h3)). Qed.
Lemma lem4789836 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term80 _110384 h x t) (h2 : term88 _110384 x t) (h3 : x = h) : term118.
Proof. exact (fun h0 : ~ False => @lem4789835 _110384 t x h h1 h2 h3). Qed.
Lemma lem4789838 (p : Prop) : (term116 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4789839 : term118 = False.
Proof. exact (@lem4789838 False). Qed.
Lemma lem4789894 {_110384 : Type'} (x : _110384) : x = x.
Proof. exact (@lem21386 _110384 x). Qed.
Lemma lem4789895 {_110384 : Type'} (x : _110384) : x = x.
Proof. exact (@lem4789894 _110384 x). Qed.
Lemma lem4789896 {_110384 : Type'} (h : _110384) : h = h.
Proof. exact (@lem4789895 _110384 h). Qed.
Lemma lem4789897 {_110384 : Type'} (h : _110384) : term119 _110384 h.
Proof. exact (fun h0 : term104 _110384 h => @lem4789896 _110384 h). Qed.
Lemma lem4789899 (p : Prop) : (term116 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4789900 {_110384 : Type'} (h : _110384) : (term119 _110384 h) = (h = h).
Proof. exact (@lem4789899 (h = h)). Qed.
Lemma lem4789901 {_110384 : Type'} (h : _110384) : h = h.
Proof. exact (EQ_MP (@lem4789900 _110384 h) (@lem4789897 _110384 h)). Qed.
Lemma lem4789904 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4789906 {_110384 : Type'} (h : _110384) : (term104 _110384 h) = (term120 _110384 h).
Proof. exact (@lem4789904 (h = h)). Qed.
Lemma lem4789909 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term80 _110384 h x t) (h2 : x = h) : term120 _110384 h.
Proof. exact (EQ_MP (@lem4789906 _110384 h) (@lem4789424 _110384 t x h h1 h2)). Qed.
Lemma lem4789912 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term80 _110384 h x t) (h2 : x = h) : False.
Proof. exact (@lem4789909 _110384 t x h h1 h2 (@lem4789901 _110384 h)). Qed.
Lemma lem4789913 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term80 _110384 h x t) (h2 : x = h) : term118.
Proof. exact (fun h0 : ~ False => @lem4789912 _110384 t x h h1 h2). Qed.
Lemma lem4789915 (p : Prop) : (term116 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4789916 : term118 = False.
Proof. exact (@lem4789915 False). Qed.
Lemma lem4789971 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : term88 _110384 x t) : term18 _110384 x t.
Proof. exact (proj1 (@lem4788954 _110384 x t h1)). Qed.
Lemma lem4789972 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : term88 _110384 x t) : term121 _110384 x t.
Proof. exact (fun h0 : term92 _110384 x t => @lem4789971 _110384 x t h1). Qed.
Lemma lem4789974 (p : Prop) : (term116 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4789975 {_110384 : Type'} (x : _110384) (t : list _110384) : (term121 _110384 x t) = (term18 _110384 x t).
Proof. exact (@lem4789974 (term18 _110384 x t)). Qed.
Lemma lem4789976 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : term88 _110384 x t) : term18 _110384 x t.
Proof. exact (EQ_MP (@lem4789975 _110384 x t) (@lem4789972 _110384 x t h1)). Qed.
Lemma lem4789979 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4789981 {_110384 : Type'} (x : _110384) (t : list _110384) : (term92 _110384 x t) = (term122 _110384 x t).
Proof. exact (@lem4789979 (term18 _110384 x t)). Qed.
Lemma lem4789984 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : term80 _110384 h x t) : term122 _110384 x t.
Proof. exact (EQ_MP (@lem4789981 _110384 x t) (@lem4789183 _110384 h x t h1)). Qed.
Lemma lem4789987 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : term80 _110384 h x t) (h2 : term88 _110384 x t) : False.
Proof. exact (@lem4789984 _110384 h x t h1 (@lem4789976 _110384 x t h2)). Qed.
Lemma lem4789988 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : term80 _110384 h x t) (h2 : term88 _110384 x t) : term118.
Proof. exact (fun h0 : ~ False => @lem4789987 _110384 h x t h1 h2). Qed.
Lemma lem4789990 (p : Prop) : (term116 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4789991 : term118 = False.
Proof. exact (@lem4789990 False). Qed.
Lemma lem4789992 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : term80 _110384 h x t) (h2 : term88 _110384 x t) : False.
Proof. exact (EQ_MP (@lem4789991) (@lem4789988 _110384 h x t h1 h2)). Qed.
Lemma lem4790046 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : @List.In _110384 x t) : @List.In _110384 x t.
Proof. exact (h1). Qed.
Lemma lem4790047 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : @List.In _110384 x t) : term115 _110384 x t.
Proof. exact (fun h0 : term90 _110384 x t => @lem4790046 _110384 x t h1). Qed.
Lemma lem4790049 (p : Prop) : (term116 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4790050 {_110384 : Type'} (x : _110384) (t : list _110384) : (term115 _110384 x t) = (@List.In _110384 x t).
Proof. exact (@lem4790049 (@List.In _110384 x t)). Qed.
Lemma lem4790051 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : @List.In _110384 x t) : @List.In _110384 x t.
Proof. exact (EQ_MP (@lem4790050 _110384 x t) (@lem4790047 _110384 x t h1)). Qed.
Lemma lem4790054 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4790056 {_110384 : Type'} (x : _110384) (t : list _110384) : (term90 _110384 x t) = (term117 _110384 x t).
Proof. exact (@lem4790054 (@List.In _110384 x t)). Qed.
Lemma lem4790059 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : term89 _110384 x t) : term117 _110384 x t.
Proof. exact (EQ_MP (@lem4790056 _110384 x t) (@lem4789199 _110384 x t h1)). Qed.
Lemma lem4790062 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : term89 _110384 x t) (h2 : @List.In _110384 x t) : False.
Proof. exact (@lem4790059 _110384 x t h1 (@lem4790051 _110384 x t h2)). Qed.
Lemma lem4790063 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : term89 _110384 x t) (h2 : @List.In _110384 x t) : term118.
Proof. exact (fun h0 : ~ False => @lem4790062 _110384 x t h1 h2). Qed.
Lemma lem4790065 (p : Prop) : (term116 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4790066 : term118 = False.
Proof. exact (@lem4790065 False). Qed.
Lemma lem4790067 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : term89 _110384 x t) (h2 : @List.In _110384 x t) : False.
Proof. exact (EQ_MP (@lem4790066) (@lem4790063 _110384 x t h1 h2)). Qed.
Lemma lem4790068 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term80 _110384 h x t) (h2 : x = h) : False.
Proof. exact (EQ_MP (@lem4789916) (@lem4789913 _110384 t x h h1 h2)). Qed.
Lemma lem4790069 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term80 _110384 h x t) (h2 : term88 _110384 x t) (h3 : x = h) : False.
Proof. exact (EQ_MP (@lem4789839) (@lem4789836 _110384 t x h h1 h2 h3)). Qed.
Lemma lem4790070 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term83 _110384 h x t) (h2 : x = h) : False.
Proof. exact (EQ_MP (@lem4789614) (@lem4789611 _110384 t x h h1 h2)). Qed.
Lemma lem4790071 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term88 _110384 x t) (h2 : term83 _110384 h x t) (h3 : x = h) : False.
Proof. exact (EQ_MP (@lem4789537) (@lem4789534 _110384 t x h h1 h2 h3)). Qed.
Lemma lem4790072 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : term89 _110384 x t) (h2 : @List.In _110384 x t) : (@List.In _110384 x t) = False.
Proof. exact (prop_ext (fun h3 : @List.In _110384 x t => @lem4790067 _110384 x t h1 h2) (fun h3 : False => @lem4789195 _110384 x t h2)). Qed.
Lemma lem4790073 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : term89 _110384 x t) (h2 : @List.In _110384 x t) : False.
Proof. exact (EQ_MP (@lem4790072 _110384 x t h1 h2) (@lem4789195 _110384 x t h2)). Qed.
Lemma lem4790074 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term80 _110384 h x t) (h2 : x = h) : (x = h) = False.
Proof. exact (prop_ext (fun h3 : x = h => @lem4790068 _110384 t x h h1 h2) (fun h3 : False => @lem4789175 _110384 x h h2)). Qed.
Lemma lem4790075 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term80 _110384 h x t) (h2 : x = h) : False.
Proof. exact (EQ_MP (@lem4790074 _110384 t x h h1 h2) (@lem4789175 _110384 x h h2)). Qed.
Lemma lem4790076 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term80 _110384 h x t) (h2 : term88 _110384 x t) (h3 : x = h) : (x = h) = False.
Proof. exact (prop_ext (fun h4 : x = h => @lem4790069 _110384 t x h h1 h2 h3) (fun h4 : False => @lem4789165 _110384 x h h3)). Qed.
Lemma lem4790077 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term80 _110384 h x t) (h2 : term88 _110384 x t) (h3 : x = h) : False.
Proof. exact (EQ_MP (@lem4790076 _110384 t x h h1 h2 h3) (@lem4789165 _110384 x h h3)). Qed.
Lemma lem4790078 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : term89 _110384 x t) (h2 : term18 _110384 x t) : (term18 _110384 x t) = False.
Proof. exact (prop_ext (fun h3 : term18 _110384 x t => @lem4789765 _110384 x t h1 h2) (fun h3 : False => @lem4789155 _110384 x t h2)). Qed.
Lemma lem4790079 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : term89 _110384 x t) (h2 : term18 _110384 x t) : False.
Proof. exact (EQ_MP (@lem4790078 _110384 x t h1 h2) (@lem4789155 _110384 x t h2)). Qed.
Lemma lem4790080 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term83 _110384 h x t) (h2 : x = h) : (x = h) = False.
Proof. exact (prop_ext (fun h3 : x = h => @lem4790070 _110384 t x h h1 h2) (fun h3 : False => @lem4789135 _110384 x h h2)). Qed.
Lemma lem4790081 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term83 _110384 h x t) (h2 : x = h) : False.
Proof. exact (EQ_MP (@lem4790080 _110384 t x h h1 h2) (@lem4789135 _110384 x h h2)). Qed.
Lemma lem4790082 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term88 _110384 x t) (h2 : term83 _110384 h x t) (h3 : x = h) : (x = h) = False.
Proof. exact (prop_ext (fun h4 : x = h => @lem4790071 _110384 t x h h1 h2 h3) (fun h4 : False => @lem4789125 _110384 x h h3)). Qed.
Lemma lem4790083 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term88 _110384 x t) (h2 : term83 _110384 h x t) (h3 : x = h) : False.
Proof. exact (EQ_MP (@lem4790082 _110384 t x h h1 h2 h3) (@lem4789125 _110384 x h h3)). Qed.
Lemma lem4790084 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : term89 _110384 x t) (h2 : @List.In _110384 x t) : (@List.In _110384 x t) = False.
Proof. exact (prop_ext (fun h3 : @List.In _110384 x t => @lem4790073 _110384 x t h1 h2) (fun h3 : False => @lem4789111 _110384 x t h2)). Qed.
Lemma lem4790085 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : term89 _110384 x t) (h2 : @List.In _110384 x t) : False.
Proof. exact (EQ_MP (@lem4790084 _110384 x t h1 h2) (@lem4789111 _110384 x t h2)). Qed.
Lemma lem4790086 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term80 _110384 h x t) (h2 : x = h) : (x = h) = False.
Proof. exact (prop_ext (fun h3 : x = h => @lem4790075 _110384 t x h h1 h2) (fun h3 : False => @lem4789071 _110384 x h h2)). Qed.
Lemma lem4790087 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term80 _110384 h x t) (h2 : x = h) : False.
Proof. exact (EQ_MP (@lem4790086 _110384 t x h h1 h2) (@lem4789071 _110384 x h h2)). Qed.
Lemma lem4790088 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term80 _110384 h x t) (h2 : term88 _110384 x t) (h3 : x = h) : (x = h) = False.
Proof. exact (prop_ext (fun h4 : x = h => @lem4790077 _110384 t x h h1 h2 h3) (fun h4 : False => @lem4789051 _110384 x h h3)). Qed.
Lemma lem4790089 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term80 _110384 h x t) (h2 : term88 _110384 x t) (h3 : x = h) : False.
Proof. exact (EQ_MP (@lem4790088 _110384 t x h h1 h2 h3) (@lem4789051 _110384 x h h3)). Qed.
Lemma lem4790090 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : term89 _110384 x t) (h2 : term18 _110384 x t) : (term18 _110384 x t) = False.
Proof. exact (prop_ext (fun h3 : term18 _110384 x t => @lem4790079 _110384 x t h1 h2) (fun h3 : False => @lem4789031 _110384 x t h2)). Qed.
Lemma lem4790091 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : term89 _110384 x t) (h2 : term18 _110384 x t) : False.
Proof. exact (EQ_MP (@lem4790090 _110384 x t h1 h2) (@lem4789031 _110384 x t h2)). Qed.
Lemma lem4790092 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term83 _110384 h x t) (h2 : x = h) : (x = h) = False.
Proof. exact (prop_ext (fun h3 : x = h => @lem4790081 _110384 t x h h1 h2) (fun h3 : False => @lem4788991 _110384 x h h2)). Qed.
Lemma lem4790093 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term83 _110384 h x t) (h2 : x = h) : False.
Proof. exact (EQ_MP (@lem4790092 _110384 t x h h1 h2) (@lem4788991 _110384 x h h2)). Qed.
Lemma lem4790094 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term88 _110384 x t) (h2 : term83 _110384 h x t) (h3 : x = h) : (x = h) = False.
Proof. exact (prop_ext (fun h4 : x = h => @lem4790083 _110384 t x h h1 h2 h3) (fun h4 : False => @lem4788971 _110384 x h h3)). Qed.
Lemma lem4790095 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term88 _110384 x t) (h2 : term83 _110384 h x t) (h3 : x = h) : False.
Proof. exact (EQ_MP (@lem4790094 _110384 t x h h1 h2 h3) (@lem4788971 _110384 x h h3)). Qed.
Lemma lem4790096 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : term89 _110384 x t) (h2 : @List.In _110384 x t) : (@List.In _110384 x t) = False.
Proof. exact (prop_ext (fun h3 : @List.In _110384 x t => @lem4790085 _110384 x t h1 h2) (fun h3 : False => @lem4789111 _110384 x t h2)). Qed.
Lemma lem4790097 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : term89 _110384 x t) (h2 : @List.In _110384 x t) : False.
Proof. exact (EQ_MP (@lem4790096 _110384 x t h1 h2) (@lem4789111 _110384 x t h2)). Qed.
Lemma lem4790098 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term80 _110384 h x t) (h2 : x = h) : (x = h) = False.
Proof. exact (prop_ext (fun h3 : x = h => @lem4790087 _110384 t x h h1 h2) (fun h3 : False => @lem4789071 _110384 x h h2)). Qed.
Lemma lem4790099 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term80 _110384 h x t) (h2 : x = h) : False.
Proof. exact (EQ_MP (@lem4790098 _110384 t x h h1 h2) (@lem4789071 _110384 x h h2)). Qed.
Lemma lem4790100 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term80 _110384 h x t) (h2 : term88 _110384 x t) (h3 : x = h) : (x = h) = False.
Proof. exact (prop_ext (fun h4 : x = h => @lem4790089 _110384 t x h h1 h2 h3) (fun h4 : False => @lem4789051 _110384 x h h3)). Qed.
Lemma lem4790101 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term80 _110384 h x t) (h2 : term88 _110384 x t) (h3 : x = h) : False.
Proof. exact (EQ_MP (@lem4790100 _110384 t x h h1 h2 h3) (@lem4789051 _110384 x h h3)). Qed.
Lemma lem4790102 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : term89 _110384 x t) (h2 : term18 _110384 x t) : (term18 _110384 x t) = False.
Proof. exact (prop_ext (fun h3 : term18 _110384 x t => @lem4790091 _110384 x t h1 h2) (fun h3 : False => @lem4789031 _110384 x t h2)). Qed.
Lemma lem4790103 {_110384 : Type'} (x : _110384) (t : list _110384) (h1 : term89 _110384 x t) (h2 : term18 _110384 x t) : False.
Proof. exact (EQ_MP (@lem4790102 _110384 x t h1 h2) (@lem4789031 _110384 x t h2)). Qed.
Lemma lem4790104 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term83 _110384 h x t) (h2 : x = h) : (x = h) = False.
Proof. exact (prop_ext (fun h3 : x = h => @lem4790093 _110384 t x h h1 h2) (fun h3 : False => @lem4788991 _110384 x h h2)). Qed.
Lemma lem4790105 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term83 _110384 h x t) (h2 : x = h) : False.
Proof. exact (EQ_MP (@lem4790104 _110384 t x h h1 h2) (@lem4788991 _110384 x h h2)). Qed.
Lemma lem4790106 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term88 _110384 x t) (h2 : term83 _110384 h x t) (h3 : x = h) : (x = h) = False.
Proof. exact (prop_ext (fun h4 : x = h => @lem4790095 _110384 t x h h1 h2 h3) (fun h4 : False => @lem4788971 _110384 x h h3)). Qed.
Lemma lem4790107 {_110384 : Type'} (t : list _110384) (x : _110384) (h : _110384) (h1 : term88 _110384 x t) (h2 : term83 _110384 h x t) (h3 : x = h) : False.
Proof. exact (EQ_MP (@lem4790106 _110384 t x h h1 h2 h3) (@lem4788971 _110384 x h h3)). Qed.
Lemma lem4790108 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : term80 _110384 h x t) (h2 : (term18 _110384 x t) = (@List.In _110384 x t)) (h3 : @List.In _110384 x t) : False.
Proof. exact (or_elim (@lem4788847 _110384 x t h2) (fun h0 : term88 _110384 x t => @lem4789992 _110384 h x t h1 h0) (fun h0 : term89 _110384 x t => @lem4790097 _110384 x t h0 h3)). Qed.
Lemma lem4790109 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : term80 _110384 h x t) (h2 : x = h) (h3 : (term18 _110384 x t) = (@List.In _110384 x t)) : False.
Proof. exact (or_elim (@lem4788847 _110384 x t h3) (fun h0 : term88 _110384 x t => @lem4790101 _110384 t x h h1 h0 h2) (fun h0 : term89 _110384 x t => @lem4790099 _110384 t x h h1 h2)). Qed.
Lemma lem4790110 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : term80 _110384 h x t) (h2 : (term18 _110384 x t) = (@List.In _110384 x t)) : False.
Proof. exact (or_elim (@lem4788942 _110384 h x t h1) (fun h0 : x = h => @lem4790109 _110384 h x t h1 h0 h2) (fun h0 : @List.In _110384 x t => @lem4790108 _110384 h x t h1 h2 h0)). Qed.
Lemma lem4790111 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : term83 _110384 h x t) (h2 : (term18 _110384 x t) = (@List.In _110384 x t)) (h3 : term18 _110384 x t) : False.
Proof. exact (or_elim (@lem4788847 _110384 x t h2) (fun h0 : term88 _110384 x t => @lem4789690 _110384 h x t h0 h1) (fun h0 : term89 _110384 x t => @lem4790103 _110384 x t h0 h3)). Qed.
Lemma lem4790112 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : term83 _110384 h x t) (h2 : x = h) (h3 : (term18 _110384 x t) = (@List.In _110384 x t)) : False.
Proof. exact (or_elim (@lem4788847 _110384 x t h3) (fun h0 : term88 _110384 x t => @lem4790107 _110384 t x h h0 h1 h2) (fun h0 : term89 _110384 x t => @lem4790105 _110384 t x h h1 h2)). Qed.
Lemma lem4790113 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : term83 _110384 h x t) (h2 : (term18 _110384 x t) = (@List.In _110384 x t)) : False.
Proof. exact (or_elim (@lem4788925 _110384 h x t h1) (fun h0 : x = h => @lem4790112 _110384 h x t h1 h0 h2) (fun h0 : term18 _110384 x t => @lem4790111 _110384 h x t h1 h2 h0)). Qed.
Lemma lem4790114 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : term52 _110384 h x t) (h2 : (term18 _110384 x t) = (@List.In _110384 x t)) : False.
Proof. exact (or_elim (@lem4788921 _110384 h x t h1) (fun h0 : term83 _110384 h x t => @lem4790113 _110384 h x t h0 h2) (fun h0 : term80 _110384 h x t => @lem4790110 _110384 h x t h0 h2)). Qed.
Lemma lem4790115 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : term52 _110384 h x t) (h2 : (term18 _110384 x t) = (@List.In _110384 x t)) : (term52 _110384 h x t) = False.
Proof. exact (prop_ext (fun h3 : term52 _110384 h x t => @lem4790114 _110384 h x t h1 h2) (fun h3 : False => @lem4788749 _110384 h x t h1)). Qed.
Lemma lem4790116 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : term52 _110384 h x t) (h2 : (term18 _110384 x t) = (@List.In _110384 x t)) : False.
Proof. exact (EQ_MP (@lem4790115 _110384 h x t h1 h2) (@lem4788749 _110384 h x t h1)). Qed.
Lemma lem4790117 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : (term18 _110384 x t) = (@List.In _110384 x t)) : term51 _110384 h x t.
Proof. exact (fun h0 : term52 _110384 h x t => @lem4790116 _110384 h x t h0 h1). Qed.
Lemma lem4790118 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : (term18 _110384 x t) = (@List.In _110384 x t)) : (term46 _110384 h x t) = (term49 _110384 h x t).
Proof. exact (EQ_MP (@lem4788748 _110384 h x t) (@lem4790117 _110384 h x t h1)). Qed.
Lemma lem4790119 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) : term59 _110384 h x t.
Proof. exact (fun h0 : (term18 _110384 x t) = (@List.In _110384 x t) => @lem4790118 _110384 h x t h0). Qed.
Lemma lem4790124 {_110384 : Type'} (x : _110384) (t : list _110384) : term63 _110384 x t.
Proof. exact (fun h : _110384 => @lem4790119 _110384 h x t). Qed.
Lemma lem4790129 {_110384 : Type'} (t : list _110384) : term67 _110384 t.
Proof. exact (fun x : _110384 => @lem4790124 _110384 x t). Qed.
Lemma lem4790134 {_110384 : Type'} : term71 _110384.
Proof. exact (fun t : list _110384 => @lem4790129 _110384 t). Qed.
Lemma lem4790135 {_110384 : Type'} : term70 _110384.
Proof. exact (EQ_MP (@lem4788743 _110384) (@lem4790134 _110384)). Qed.
Lemma lem4790136 {_110384 : Type'} (t : list _110384) : term123 _110384 t.
Proof. exact (@lem4790135 _110384 t). Qed.
Lemma lem4790137 {_110384 : Type'} (t : list _110384) : (term123 _110384 t) = (term66 _110384 t).
Proof. exact (eq_refl (term123 _110384 t)). Qed.
Lemma lem4790138 {_110384 : Type'} (t : list _110384) : term66 _110384 t.
Proof. exact (EQ_MP (@lem4790137 _110384 t) (@lem4790136 _110384 t)). Qed.
Lemma lem4790139 {_110384 : Type'} (t : list _110384) (x : _110384) : term124 _110384 t x.
Proof. exact (@lem4790138 _110384 t x). Qed.
Lemma lem4790140 {_110384 : Type'} (x : _110384) (t : list _110384) : (term124 _110384 t x) = (term62 _110384 x t).
Proof. exact (eq_refl (term124 _110384 t x)). Qed.
Lemma lem4790141 {_110384 : Type'} (x : _110384) (t : list _110384) : term62 _110384 x t.
Proof. exact (EQ_MP (@lem4790140 _110384 x t) (@lem4790139 _110384 t x)). Qed.
Lemma lem4790142 {_110384 : Type'} (x : _110384) (t : list _110384) (h : _110384) : term125 _110384 x t h.
Proof. exact (@lem4790141 _110384 x t h). Qed.
Lemma lem4790143 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) : (term125 _110384 x t h) = (term53 _110384 h x t).
Proof. exact (eq_refl (term125 _110384 x t h)). Qed.
Lemma lem4790144 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) : term53 _110384 h x t.
Proof. exact (EQ_MP (@lem4790143 _110384 h x t) (@lem4790142 _110384 x t h)). Qed.
Lemma lem4790146 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) : term53 _110384 h x t.
Proof. exact (@lem4788631 _110384 h x t (@lem4790144 _110384 h x t)). Qed.
Lemma lem4790147 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : (term18 _110384 x t) = (@List.In _110384 x t)) : term51 _110384 h x t.
Proof. exact (@lem4790146 _110384 h x t (@lem4788555 _110384 x t h1)). Qed.
Lemma lem4790148 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : term52 _110384 h x t) (h2 : (term18 _110384 x t) = (@List.In _110384 x t)) : False.
Proof. exact (@lem4790147 _110384 h x t h2 (@lem4788615 _110384 h x t h1)). Qed.
Lemma lem4790149 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : term52 _110384 h x t) (h2 : (term18 _110384 x t) = (@List.In _110384 x t)) : (term52 _110384 h x t) = False.
Proof. exact (prop_ext (fun h3 : term52 _110384 h x t => @lem4790148 _110384 h x t h1 h2) (fun h3 : False => @lem4788615 _110384 h x t h1)). Qed.
Lemma lem4790150 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : term52 _110384 h x t) (h2 : (term18 _110384 x t) = (@List.In _110384 x t)) : False.
Proof. exact (EQ_MP (@lem4790149 _110384 h x t h1 h2) (@lem4788615 _110384 h x t h1)). Qed.
Lemma lem4790151 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : (term18 _110384 x t) = (@List.In _110384 x t)) : term51 _110384 h x t.
Proof. exact (fun h0 : term52 _110384 h x t => @lem4790150 _110384 h x t h0 h1). Qed.
Lemma lem4790152 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : (term18 _110384 x t) = (@List.In _110384 x t)) : (term46 _110384 h x t) = (term49 _110384 h x t).
Proof. exact (EQ_MP (@lem4788614 _110384 h x t) (@lem4790151 _110384 h x t h1)). Qed.
Lemma lem4790153 {_110384 : Type'} (h : _110384) (x : _110384) (t : list _110384) (h1 : (term18 _110384 x t) = (@List.In _110384 x t)) : (term22 _110384 x h t) = (term23 _110384 x h t).
Proof. exact (EQ_MP (@lem4788610 _110384 x h t) (@lem4790152 _110384 h x t h1)). Qed.
Lemma lem4790154 {_110384 : Type'} (x : _110384) (h : _110384) (t : list _110384) : term25 _110384 x h t.
Proof. exact (fun h0 : (term18 _110384 x t) = (@List.In _110384 x t) => @lem4790153 _110384 h x t h0). Qed.
Lemma lem4790159 {_110384 : Type'} (x : _110384) (h : _110384) : term29 _110384 x h.
Proof. exact (fun t : list _110384 => @lem4790154 _110384 x h t). Qed.
Lemma lem4790164 {_110384 : Type'} (x : _110384) : term33 _110384 x.
Proof. exact (fun h : _110384 => @lem4790159 _110384 x h). Qed.
Lemma lem4790165 {_110384 : Type'} (x : _110384) : term35 _110384 x.
Proof. exact (conj (@lem4788581 _110384 x) (@lem4790164 _110384 x)). Qed.
Lemma lem4790166 {_110384 : Type'} (x : _110384) : term40 _110384 x.
Proof. exact (@lem4788554 _110384 x (@lem4790165 _110384 x)). Qed.
Lemma lem4790171 {_110384 : Type'} : term126 _110384.
Proof. exact (fun x : _110384 => @lem4790166 _110384 x). Qed.
