Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1073632_term_abbrevs.
Require Import list_RECURSION_spec.
Require Import thm1073375_spec.
Require Import thm1073376_spec.
Require Import thm32_spec.
Lemma lem1073531 {A : Type'} (_17538 : type1140 A) (h1 : term0 A _17538) : term0 A _17538.
Proof. exact (h1). Qed.
Lemma lem1073532 {A : Type'} (a0 : A) (_17538 : type1140 A) (h1 : term0 A _17538) : term1 A _17538 a0.
Proof. exact (@lem1073531 A _17538 h1 a0). Qed.
Lemma lem1073533 {A : Type'} (_17538 : type1140 A) (a0 : A) : (term1 A _17538 a0) = (term2 A _17538 a0).
Proof. exact (eq_refl (term1 A _17538 a0)). Qed.
Lemma lem1073534 {A : Type'} (a0 : A) (_17538 : type1140 A) (h1 : term0 A _17538) : term2 A _17538 a0.
Proof. exact (EQ_MP (@lem1073533 A _17538 a0) (@lem1073532 A a0 _17538 h1)). Qed.
Lemma lem1073535 {A : Type'} (a0 : A) (a1 : list A) (_17538 : type1140 A) (h1 : term0 A _17538) : term3 A _17538 a0 a1.
Proof. exact (@lem1073534 A a0 _17538 h1 a1). Qed.
Lemma lem1073536 {A : Type'} (_17538 : type1140 A) (a0 : A) (a1 : list A) : (term3 A _17538 a0 a1) = ((term4 A _17538 a0 a1) = (@pair A (list A) a0 a1)).
Proof. exact (eq_refl (term3 A _17538 a0 a1)). Qed.
Lemma lem1073537 {A : Type'} (a0 : A) (a1 : list A) (_17538 : type1140 A) (h1 : term0 A _17538) : (term4 A _17538 a0 a1) = (@pair A (list A) a0 a1).
Proof. exact (EQ_MP (@lem1073536 A _17538 a0 a1) (@lem1073535 A a0 a1 _17538 h1)). Qed.
Lemma lem1073538 {A : Type'} (a0 : A) (_17538 : type1140 A) (h1 : term0 A _17538) : term2 A _17538 a0.
Proof. exact (fun a1 : list A => @lem1073537 A a0 a1 _17538 h1). Qed.
Lemma lem1073539 {A : Type'} (_17538 : type1140 A) (h1 : term0 A _17538) : term0 A _17538.
Proof. exact (fun a0 : A => @lem1073538 A a0 _17538 h1). Qed.
Lemma lem1073540 {A : Type'} (_17538 : type1140 A) (h1 : term0 A _17538) : term0 A _17538.
Proof. exact (h1). Qed.
Lemma lem1073541 {A : Type'} (_17538 : type1140 A) : (term0 A _17538) = (term0 A _17538).
Proof. exact (prop_ext (fun h1 : term0 A _17538 => @lem1073539 A _17538 h1) (fun h1 : term0 A _17538 => @lem1073540 A _17538 h1)). Qed.
Lemma lem1073542 {A : Type'} (_17538 : type1140 A) (h1 : term0 A _17538) : term0 A _17538.
Proof. exact (EQ_MP (@lem1073541 A _17538) (@lem1073540 A _17538 h1)). Qed.
Lemma lem1073543 {A Z : Type'} (NIL' : Z) : term5 A Z NIL'.
Proof. exact (@lem1072128 A Z NIL'). Qed.
Lemma lem1073544 {A Z : Type'} (NIL' : Z) : (term5 A Z NIL') = (term6 A Z NIL').
Proof. exact (eq_refl (term5 A Z NIL')). Qed.
Lemma lem1073545 {A Z : Type'} (NIL' : Z) : term6 A Z NIL'.
Proof. exact (EQ_MP (@lem1073544 A Z NIL') (@lem1073543 A Z NIL')). Qed.
Lemma lem1073546 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term7 A Z NIL' CONS'.
Proof. exact (@lem1073545 A Z NIL' CONS'). Qed.
Lemma lem1073547 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : (term7 A Z NIL' CONS') = (term8 A Z NIL' CONS').
Proof. exact (eq_refl (term7 A Z NIL' CONS')). Qed.
Lemma lem1073548 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term8 A Z NIL' CONS'.
Proof. exact (EQ_MP (@lem1073547 A Z NIL' CONS') (@lem1073546 A Z NIL' CONS')). Qed.
Lemma lem1073549 {A : Type'} (NIL' : type1654 A) (CONS' : type1392 A) : term9 A NIL' CONS'.
Proof. exact (@lem1073548 A (type1654 A) NIL' CONS'). Qed.
Lemma lem1073550 {A : Type'} (NIL' : type1654 A) : term10 A NIL'.
Proof. exact (@lem1073549 A NIL' (term11 A)). Qed.
Lemma lem1073551 {A : Type'} (a0 : A) : (term12 A a0) = (term13 A a0).
Proof. exact (eq_refl (term12 A a0)). Qed.
Lemma lem1073552 {A : Type'} (a1 : list A) : a1 = a1.
Proof. exact (eq_refl a1). Qed.
Lemma lem1073553 {A : Type'} (a0 : A) (a1 : list A) : (term14 A a0 a1) = (term15 A a0 a1).
Proof. exact (MK_COMB (@lem1073551 A a0) (@lem1073552 A a1)). Qed.
Lemma lem1073554 {A : Type'} (a0 : A) (a1 : list A) : (term15 A a0 a1) = (term16 A a0 a1).
Proof. exact (eq_refl (term15 A a0 a1)). Qed.
Lemma lem1073555 {A : Type'} (a0 : A) (a1 : list A) : (term14 A a0 a1) = (term16 A a0 a1).
Proof. exact (TRANS (@lem1073553 A a0 a1) (@lem1073554 A a0 a1)). Qed.
Lemma lem1073556 {A : Type'} (fn : type1140 A) (a1 : list A) : (fn a1) = (fn a1).
Proof. exact (eq_refl (fn a1)). Qed.
Lemma lem1073557 {A : Type'} (a0 : A) (fn : type1140 A) (a1 : list A) : (term17 A a0 fn a1) = (term18 A a0 fn a1).
Proof. exact (MK_COMB (@lem1073555 A a0 a1) (@lem1073556 A fn a1)). Qed.
Lemma lem1073558 {A : Type'} (fn : type1140 A) (a0 : A) (a1 : list A) : (term18 A a0 fn a1) = (@pair A (list A) a0 a1).
Proof. exact (eq_refl (term18 A a0 fn a1)). Qed.
Lemma lem1073559 {A : Type'} (fn : type1140 A) (a0 : A) (a1 : list A) : (term17 A a0 fn a1) = (@pair A (list A) a0 a1).
Proof. exact (TRANS (@lem1073557 A a0 fn a1) (@lem1073558 A fn a0 a1)). Qed.
Lemma lem1073560 {A : Type'} (fn : type1140 A) (a0 : A) (a1 : list A) : (term19 A fn a0 a1) = (term19 A fn a0 a1).
Proof. exact (eq_refl (term19 A fn a0 a1)). Qed.
Lemma lem1073561 {A : Type'} (fn : type1140 A) (a0 : A) (a1 : list A) : ((term4 A fn a0 a1) = (term17 A a0 fn a1)) = ((term4 A fn a0 a1) = (@pair A (list A) a0 a1)).
Proof. exact (MK_COMB (@lem1073560 A fn a0 a1) (@lem1073559 A fn a0 a1)). Qed.
Lemma lem1073562 {A : Type'} (fn : type1140 A) (a0 : A) : (term20 A a0 fn) = (term21 A fn a0).
Proof. exact (fun_ext (fun a1 : list A => @lem1073561 A fn a0 a1)). Qed.
Lemma lem1073563 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1073564 {A : Type'} (fn : type1140 A) (a0 : A) : (term22 A a0 fn) = (term2 A fn a0).
Proof. exact (MK_COMB (@lem1073563 A) (@lem1073562 A fn a0)). Qed.
Lemma lem1073565 {A : Type'} (fn : type1140 A) : (term23 A fn) = (term24 A fn).
Proof. exact (fun_ext (fun a0 : A => @lem1073564 A fn a0)). Qed.
Lemma lem1073566 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1073567 {A : Type'} (fn : type1140 A) : (term25 A fn) = (term0 A fn).
Proof. exact (MK_COMB (@lem1073566 A) (@lem1073565 A fn)). Qed.
Lemma lem1073568 {A : Type'} (fn : type1140 A) (NIL' : type1654 A) : (term26 A fn NIL') = (term26 A fn NIL').
Proof. exact (eq_refl (term26 A fn NIL')). Qed.
Lemma lem1073569 {A : Type'} (NIL' : type1654 A) (fn : type1140 A) : (term27 A NIL' fn) = (term28 A NIL' fn).
Proof. exact (MK_COMB (@lem1073568 A fn NIL') (@lem1073567 A fn)). Qed.
Lemma lem1073570 {A : Type'} (NIL' : type1654 A) : (term29 A NIL') = (term30 A NIL').
Proof. exact (fun_ext (fun fn : type1140 A => @lem1073569 A NIL' fn)). Qed.
Lemma lem1073571 {A : Type'} : (@ex ((list A) -> prod A (list A))) = (@ex ((list A) -> prod A (list A))).
Proof. exact (eq_refl (@ex ((list A) -> prod A (list A)))). Qed.
Lemma lem1073572 {A : Type'} (NIL' : type1654 A) : (term10 A NIL') = (term31 A NIL').
Proof. exact (MK_COMB (@lem1073571 A) (@lem1073570 A NIL')). Qed.
Lemma lem1073573 {A : Type'} (NIL' : type1654 A) : term31 A NIL'.
Proof. exact (EQ_MP (@lem1073572 A NIL') (@lem1073550 A NIL')). Qed.
Lemma lem1073574 {A : Type'} (NIL' : type1654 A) (_17538 : type1140 A) (h1 : term28 A NIL' _17538) : term28 A NIL' _17538.
Proof. exact (h1). Qed.
Lemma lem1073575 {A : Type'} (NIL' : type1654 A) (_17538 : type1140 A) (h1 : term28 A NIL' _17538) : term0 A _17538.
Proof. exact (proj2 (@lem1073574 A NIL' _17538 h1)). Qed.
Lemma lem1073577 {A : Type'} (NIL' : type1654 A) (_17538 : type1140 A) (h1 : term28 A NIL' _17538) : term32 A.
Proof. exact (ex_intro (term33 A) _17538 (@lem1073575 A NIL' _17538 h1)). Qed.
Lemma lem1073578 {A : Type'} (NIL' : type1654 A) (h1 : term31 A NIL') : term31 A NIL'.
Proof. exact (h1). Qed.
Lemma lem1073579 {A : Type'} (NIL' : type1654 A) (h1 : term31 A NIL') : term32 A.
Proof. exact (ex_elim (@lem1073578 A NIL' h1) (fun _17538 : type1140 A => fun h0 : term30 A NIL' _17538 => @lem1073577 A NIL' _17538 h0)). Qed.
Lemma lem1073580 {A : Type'} (NIL' : type1654 A) : (term31 A NIL') = (term32 A).
Proof. exact (prop_ext (fun h1 : term31 A NIL' => @lem1073579 A NIL' h1) (fun h1 : term32 A => @lem1073573 A NIL')). Qed.
Lemma lem1073581 {A : Type'} : term32 A.
Proof. exact (EQ_MP (@lem1073580 A (@el (prod A (list A)))) (@lem1073573 A (@el (prod A (list A))))). Qed.
Lemma lem1073582 {A : Type'} (_17538 : type1140 A) (h1 : term0 A _17538) : term32 A.
Proof. exact (ex_intro (term33 A) _17538 (@lem1073542 A _17538 h1)). Qed.
Lemma lem1073583 {A : Type'} (h1 : term32 A) : term32 A.
Proof. exact (h1). Qed.
Lemma lem1073584 {A : Type'} (h1 : term32 A) : term32 A.
Proof. exact (ex_elim (@lem1073583 A h1) (fun _17538 : type1140 A => fun h0 : term33 A _17538 => @lem1073582 A _17538 h0)). Qed.
Lemma lem1073585 {A : Type'} : (term32 A) = (term32 A).
Proof. exact (prop_ext (fun h1 : term32 A => @lem1073584 A h1) (fun h1 : term32 A => @lem1073581 A)). Qed.
Lemma lem1073586 {A : Type'} : term32 A.
Proof. exact (EQ_MP (@lem1073585 A) (@lem1073581 A)). Qed.
Lemma lem1073589 {A : Type'} (_17538 : type1140 A) (h1 : term0 A _17538) : term0 A _17538.
Proof. exact (h1). Qed.
Lemma lem1073590 {A : Type'} (_17538 : type1140 A) (h1 : term0 A _17538) : term32 A.
Proof. exact (ex_intro (term33 A) _17538 (@lem1073589 A _17538 h1)). Qed.
Lemma lem1073591 {A : Type'} (h1 : term32 A) : term32 A.
Proof. exact (h1). Qed.
Lemma lem1073592 {A : Type'} (h1 : term32 A) : term32 A.
Proof. exact (ex_elim (@lem1073591 A h1) (fun _17538 : type1140 A => fun h0 : term33 A _17538 => @lem1073590 A _17538 h0)). Qed.
Lemma lem1073593 {A : Type'} : (term32 A) = (term32 A).
Proof. exact (prop_ext (fun h1 : term32 A => @lem1073592 A h1) (fun h1 : term32 A => @lem1073586 A)). Qed.
Lemma lem1073594 {A : Type'} : term32 A.
Proof. exact (EQ_MP (@lem1073593 A) (@lem1073586 A)). Qed.
Lemma lem1073595 {A : Type'} (a0 : A) (a1 : list A) (a0' : A) (a1' : list A) (h1 : (@cons A a0 a1) = (@cons A a0' a1')) : (@cons A a0 a1) = (@cons A a0' a1').
Proof. exact (h1). Qed.
Lemma lem1073596 {A : Type'} (_17538 : type1140 A) : _17538 = _17538.
Proof. exact (eq_refl _17538). Qed.
Lemma lem1073597 {A : Type'} (_17538 : type1140 A) (a0 : A) (a1 : list A) (a0' : A) (a1' : list A) (h1 : (@cons A a0 a1) = (@cons A a0' a1')) : (term4 A _17538 a0 a1) = (term4 A _17538 a0' a1').
Proof. exact (MK_COMB (@lem1073596 A _17538) (@lem1073595 A a0 a1 a0' a1' h1)). Qed.
Lemma lem1073598 {A : Type'} (_17538 : type1140 A) (h1 : term0 A _17538) : term0 A _17538.
Proof. exact (h1). Qed.
Lemma lem1073599 {A : Type'} (a0 : A) (_17538 : type1140 A) (h1 : term0 A _17538) : term1 A _17538 a0.
Proof. exact (@lem1073598 A _17538 h1 a0). Qed.
Lemma lem1073600 {A : Type'} (_17538 : type1140 A) (a0 : A) : (term1 A _17538 a0) = (term2 A _17538 a0).
Proof. exact (eq_refl (term1 A _17538 a0)). Qed.
Lemma lem1073601 {A : Type'} (a0 : A) (_17538 : type1140 A) (h1 : term0 A _17538) : term2 A _17538 a0.
Proof. exact (EQ_MP (@lem1073600 A _17538 a0) (@lem1073599 A a0 _17538 h1)). Qed.
Lemma lem1073602 {A : Type'} (a0 : A) (a1 : list A) (_17538 : type1140 A) (h1 : term0 A _17538) : term3 A _17538 a0 a1.
Proof. exact (@lem1073601 A a0 _17538 h1 a1). Qed.
Lemma lem1073603 {A : Type'} (_17538 : type1140 A) (a0 : A) (a1 : list A) : (term3 A _17538 a0 a1) = ((term4 A _17538 a0 a1) = (@pair A (list A) a0 a1)).
Proof. exact (eq_refl (term3 A _17538 a0 a1)). Qed.
Lemma lem1073604 {A : Type'} (a0 : A) (a1 : list A) (_17538 : type1140 A) (h1 : term0 A _17538) : (term4 A _17538 a0 a1) = (@pair A (list A) a0 a1).
Proof. exact (EQ_MP (@lem1073603 A _17538 a0 a1) (@lem1073602 A a0 a1 _17538 h1)). Qed.
Lemma lem1073605 {A : Type'} (a0' : A) (a1' : list A) (_17538 : type1140 A) (h1 : term0 A _17538) : (term4 A _17538 a0' a1') = (@pair A (list A) a0' a1').
Proof. exact (@lem1073604 A a0' a1' _17538 h1). Qed.
Lemma lem1073606 {A : Type'} (a0 : A) (a1 : list A) (_17538 : type1140 A) (h1 : term0 A _17538) : (@pair A (list A) a0 a1) = (term4 A _17538 a0 a1).
Proof. exact (SYM (@lem1073604 A a0 a1 _17538 h1)). Qed.
Lemma lem1073607 {A : Type'} (_17538 : type1140 A) (a0 : A) (a1 : list A) (a0' : A) (a1' : list A) (h1 : term0 A _17538) (h2 : (@cons A a0 a1) = (@cons A a0' a1')) : (@pair A (list A) a0 a1) = (term4 A _17538 a0' a1').
Proof. exact (TRANS (@lem1073606 A a0 a1 _17538 h1) (@lem1073597 A _17538 a0 a1 a0' a1' h2)). Qed.
Lemma lem1073608 {A : Type'} (_17538 : type1140 A) (a0 : A) (a1 : list A) (a0' : A) (a1' : list A) (h1 : term0 A _17538) (h2 : (@cons A a0 a1) = (@cons A a0' a1')) : (@pair A (list A) a0 a1) = (@pair A (list A) a0' a1').
Proof. exact (TRANS (@lem1073607 A _17538 a0 a1 a0' a1' h1 h2) (@lem1073605 A a0' a1' _17538 h1)). Qed.
Lemma lem1073610 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : ((@pair A B x y) = (@pair A B a b)) = (term34 A B x a y b).
Proof. exact (EQ_MP (@lem1073376 A B x a y b) (@lem1073375 A B x a y b)). Qed.
Lemma lem1073611 {A : Type'} (x : A) (a : A) (y : list A) (b : list A) : ((@pair A (list A) x y) = (@pair A (list A) a b)) = (term35 A x a y b).
Proof. exact (@lem1073610 A (list A) x a y b). Qed.
Lemma lem1073612 {A : Type'} (a0 : A) (a0' : A) (a1 : list A) (a1' : list A) : ((@pair A (list A) a0 a1) = (@pair A (list A) a0' a1')) = (term35 A a0 a0' a1 a1').
Proof. exact (@lem1073611 A a0 a0' a1 a1'). Qed.
Lemma lem1073613 {A : Type'} (_17538 : type1140 A) (a0 : A) (a1 : list A) (a0' : A) (a1' : list A) (h1 : term0 A _17538) (h2 : (@cons A a0 a1) = (@cons A a0' a1')) : term35 A a0 a0' a1 a1'.
Proof. exact (EQ_MP (@lem1073612 A a0 a0' a1 a1') (@lem1073608 A _17538 a0 a1 a0' a1' h1 h2)). Qed.
Lemma lem1073614 {A : Type'} : (@cons A) = (@cons A).
Proof. exact (eq_refl (@cons A)). Qed.
Lemma lem1073615 {A : Type'} (a0 : A) (a0' : A) (a1 : list A) (a1' : list A) (h1 : term35 A a0 a0' a1 a1') : term35 A a0 a0' a1 a1'.
Proof. exact (h1). Qed.
Lemma lem1073616 {A : Type'} (a0 : A) (a0' : A) (a1 : list A) (a1' : list A) (h1 : term35 A a0 a0' a1 a1') : a1 = a1'.
Proof. exact (proj2 (@lem1073615 A a0 a0' a1 a1' h1)). Qed.
Lemma lem1073617 {A : Type'} (a0 : A) (a0' : A) (a1 : list A) (a1' : list A) (h1 : term35 A a0 a0' a1 a1') : a0 = a0'.
Proof. exact (proj1 (@lem1073615 A a0 a0' a1 a1' h1)). Qed.
Lemma lem1073618 {A : Type'} (a0 : A) (a0' : A) (a1 : list A) (a1' : list A) (h1 : term35 A a0 a0' a1 a1') : (@cons A a0) = (@cons A a0').
Proof. exact (MK_COMB (@lem1073614 A) (@lem1073617 A a0 a0' a1 a1' h1)). Qed.
Lemma lem1073619 {A : Type'} (a0 : A) (a0' : A) (a1 : list A) (a1' : list A) (h1 : term35 A a0 a0' a1 a1') : (@cons A a0 a1) = (@cons A a0' a1').
Proof. exact (MK_COMB (@lem1073618 A a0 a0' a1 a1' h1) (@lem1073616 A a0 a0' a1 a1' h1)). Qed.
Lemma lem1073620 {A : Type'} (a0 : A) (a1 : list A) (a0' : A) (a1' : list A) : term36 A a0 a1 a0' a1'.
Proof. exact (fun h0 : term35 A a0 a0' a1 a1' => @lem1073619 A a0 a0' a1 a1' h0). Qed.
Lemma lem1073621 {A : Type'} (a0 : A) (a0' : A) (a1 : list A) (a1' : list A) (_17538 : type1140 A) (h1 : term0 A _17538) : term37 A a0 a0' a1 a1'.
Proof. exact (fun h0 : (@cons A a0 a1) = (@cons A a0' a1') => @lem1073613 A _17538 a0 a1 a0' a1' h1 h0). Qed.
Lemma lem1073622 {A : Type'} (a0 : A) (a1 : list A) (a0' : A) (a1' : list A) (_17538 : type1140 A) (h1 : term0 A _17538) : term38 A a0 a1 a0' a1'.
Proof. exact (conj (@lem1073621 A a0 a0' a1 a1' _17538 h1) (@lem1073620 A a0 a1 a0' a1')). Qed.
Lemma lem1073623 {A : Type'} (a0 : A) (a0' : A) (a1 : list A) (a1' : list A) : (term38 A a0 a1 a0' a1') = (((@cons A a0 a1) = (@cons A a0' a1')) = (term35 A a0 a0' a1 a1')).
Proof. exact (@lem32 ((@cons A a0 a1) = (@cons A a0' a1')) (term35 A a0 a0' a1 a1')). Qed.
Lemma lem1073624 {A : Type'} (a0 : A) (a0' : A) (a1 : list A) (a1' : list A) (_17538 : type1140 A) (h1 : term0 A _17538) : ((@cons A a0 a1) = (@cons A a0' a1')) = (term35 A a0 a0' a1 a1').
Proof. exact (EQ_MP (@lem1073623 A a0 a0' a1 a1') (@lem1073622 A a0 a1 a0' a1' _17538 h1)). Qed.
Lemma lem1073625 {A : Type'} (a0 : A) (a0' : A) (a1 : list A) (_17538 : type1140 A) (h1 : term0 A _17538) : term39 A a0 a0' a1.
Proof. exact (fun a1' : list A => @lem1073624 A a0 a0' a1 a1' _17538 h1). Qed.
Lemma lem1073626 {A : Type'} (a0 : A) (a1 : list A) (_17538 : type1140 A) (h1 : term0 A _17538) : term40 A a0 a1.
Proof. exact (fun a0' : A => @lem1073625 A a0 a0' a1 _17538 h1). Qed.
Lemma lem1073627 {A : Type'} (a0 : A) (_17538 : type1140 A) (h1 : term0 A _17538) : term41 A a0.
Proof. exact (fun a1 : list A => @lem1073626 A a0 a1 _17538 h1). Qed.
Lemma lem1073628 {A : Type'} (_17538 : type1140 A) (h1 : term0 A _17538) : term42 A.
Proof. exact (fun a0 : A => @lem1073627 A a0 _17538 h1). Qed.
Lemma lem1073629 {A : Type'} (h1 : term32 A) : term32 A.
Proof. exact (h1). Qed.
Lemma lem1073630 {A : Type'} (h1 : term32 A) : term42 A.
Proof. exact (ex_elim (@lem1073629 A h1) (fun _17538 : type1140 A => fun h0 : term33 A _17538 => @lem1073628 A _17538 h0)). Qed.
Lemma lem1073631 {A : Type'} : (term32 A) = (term42 A).
Proof. exact (prop_ext (fun h1 : term32 A => @lem1073630 A h1) (fun h1 : term42 A => @lem1073594 A)). Qed.
Lemma lem1073632 {A : Type'} : term42 A.
Proof. exact (EQ_MP (@lem1073631 A) (@lem1073594 A)). Qed.
