Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import TREAL_MUL_SYM_EQ_term_abbrevs.
Require Import FORALL_PAIR_THM_spec.
Require Import thm0_spec.
Require Import thm1320004_spec.
Require Import thm1320617_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import treal_mul_spec.
Lemma lem1327522 (x : hreal) : term0 x.
Proof. exact (@lem1320004 x). Qed.
Lemma lem1327523 (x : hreal) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1327524 (x : hreal) : term1 x.
Proof. exact (EQ_MP (@lem1327523 x) (@lem1327522 x)). Qed.
Lemma lem1327525 (x : hreal) (y : hreal) : term2 x y.
Proof. exact (@lem1327524 x y). Qed.
Lemma lem1327526 (y : hreal) (x : hreal) : (term2 x y) = ((hreal_add x y) = (hreal_add y x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1327528 (x : hreal) : term3 x.
Proof. exact (@lem1320617 x). Qed.
Lemma lem1327529 (x : hreal) : (term3 x) = (term4 x).
Proof. exact (eq_refl (term3 x)). Qed.
Lemma lem1327530 (x : hreal) : term4 x.
Proof. exact (EQ_MP (@lem1327529 x) (@lem1327528 x)). Qed.
Lemma lem1327531 (x : hreal) (y : hreal) : term5 x y.
Proof. exact (@lem1327530 x y). Qed.
Lemma lem1327532 (y : hreal) (x : hreal) : (term5 x y) = ((hreal_mul x y) = (hreal_mul y x)).
Proof. exact (eq_refl (term5 x y)). Qed.
Lemma lem1327534 (x1 : hreal) : term6 x1.
Proof. exact (@lem1324372 x1). Qed.
Lemma lem1327535 (x1 : hreal) : (term6 x1) = (term7 x1).
Proof. exact (eq_refl (term6 x1)). Qed.
Lemma lem1327536 (x1 : hreal) : term7 x1.
Proof. exact (EQ_MP (@lem1327535 x1) (@lem1327534 x1)). Qed.
Lemma lem1327537 (x1 : hreal) (y2 : hreal) : term8 x1 y2.
Proof. exact (@lem1327536 x1 y2). Qed.
Lemma lem1327538 (x1 : hreal) (y2 : hreal) : (term8 x1 y2) = (term9 x1 y2).
Proof. exact (eq_refl (term8 x1 y2)). Qed.
Lemma lem1327539 (x1 : hreal) (y2 : hreal) : term9 x1 y2.
Proof. exact (EQ_MP (@lem1327538 x1 y2) (@lem1327537 x1 y2)). Qed.
Lemma lem1327540 (x1 : hreal) (y2 : hreal) (y1 : hreal) : term10 x1 y2 y1.
Proof. exact (@lem1327539 x1 y2 y1). Qed.
Lemma lem1327541 (x1 : hreal) (y2 : hreal) (y1 : hreal) : (term10 x1 y2 y1) = (term11 x1 y2 y1).
Proof. exact (eq_refl (term10 x1 y2 y1)). Qed.
Lemma lem1327542 (x1 : hreal) (y2 : hreal) (y1 : hreal) : term11 x1 y2 y1.
Proof. exact (EQ_MP (@lem1327541 x1 y2 y1) (@lem1327540 x1 y2 y1)). Qed.
Lemma lem1327543 (x1 : hreal) (y2 : hreal) (y1 : hreal) (x2 : hreal) : term12 x1 y2 y1 x2.
Proof. exact (@lem1327542 x1 y2 y1 x2). Qed.
Lemma lem1327544 (x1 : hreal) (y2 : hreal) (y1 : hreal) (x2 : hreal) : (term12 x1 y2 y1 x2) = ((term13 x1 y1 x2 y2) = (term14 x1 y2 y1 x2)).
Proof. exact (eq_refl (term12 x1 y2 y1 x2)). Qed.
Lemma lem1327546 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term15 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem1327547 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term15 _5106 _5107 P) = ((term16 _5106 _5107 P) = (term17 _5106 _5107 P)).
Proof. exact (eq_refl (term15 _5106 _5107 P)). Qed.
Lemma lem1327554 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term16 _5106 _5107 P) = (term17 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1327547 _5106 _5107 P) (@lem1327546 _5106 _5107 P)). Qed.
Lemma lem1327555 (P : type1233) : (term18 P) = (term19 P).
Proof. exact (@lem1327554 hreal hreal P). Qed.
Lemma lem1327556 : term20 = term21.
Proof. exact (@lem1327555 term22). Qed.
Lemma lem1327557 (x : prod hreal hreal) : (term23 x) = (term24 x).
Proof. exact (eq_refl (term23 x)). Qed.
Lemma lem1327558 : term25 = term22.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1327557 x)). Qed.
Lemma lem1327559 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1327560 : term20 = term26.
Proof. exact (MK_COMB (@lem1327559) (@lem1327558)). Qed.
Lemma lem1327561 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1327562 : term27 = term28.
Proof. exact (MK_COMB (@lem1327561) (@lem1327560)). Qed.
Lemma lem1327563 (p1 : hreal) (p2 : hreal) : (term29 p1 p2) = (term30 p1 p2).
Proof. exact (eq_refl (term29 p1 p2)). Qed.
Lemma lem1327564 (p1 : hreal) : (term31 p1) = (term32 p1).
Proof. exact (fun_ext (fun p2 : hreal => @lem1327563 p1 p2)). Qed.
Lemma lem1327565 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1327566 (p1 : hreal) : (term33 p1) = (term34 p1).
Proof. exact (MK_COMB (@lem1327565) (@lem1327564 p1)). Qed.
Lemma lem1327567 : term35 = term36.
Proof. exact (fun_ext (fun p1 : hreal => @lem1327566 p1)). Qed.
Lemma lem1327568 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1327569 : term21 = term37.
Proof. exact (MK_COMB (@lem1327568) (@lem1327567)). Qed.
Lemma lem1327570 : (term20 = term21) = (term26 = term37).
Proof. exact (MK_COMB (@lem1327562) (@lem1327569)). Qed.
Lemma lem1327571 : term26 = term37.
Proof. exact (EQ_MP (@lem1327570) (@lem1327556)). Qed.
Lemma lem1327589 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term16 _5106 _5107 P) = (term17 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1327547 _5106 _5107 P) (@lem1327546 _5106 _5107 P)). Qed.
Lemma lem1327590 (P : type1233) : (term18 P) = (term19 P).
Proof. exact (@lem1327589 hreal hreal P). Qed.
Lemma lem1327591 (p1 : hreal) (p2 : hreal) : (term38 p1 p2) = (term39 p1 p2).
Proof. exact (@lem1327590 (term40 p1 p2)). Qed.
Lemma lem1327592 (y : prod hreal hreal) (p1 : hreal) (p2 : hreal) : (term41 p1 p2 y) = ((term42 p1 p2 y) = (term43 y p1 p2)).
Proof. exact (eq_refl (term41 p1 p2 y)). Qed.
Lemma lem1327593 (p1 : hreal) (p2 : hreal) : (term44 p1 p2) = (term40 p1 p2).
Proof. exact (fun_ext (fun y : prod hreal hreal => @lem1327592 y p1 p2)). Qed.
Lemma lem1327594 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1327595 (p1 : hreal) (p2 : hreal) : (term38 p1 p2) = (term30 p1 p2).
Proof. exact (MK_COMB (@lem1327594) (@lem1327593 p1 p2)). Qed.
Lemma lem1327596 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1327597 (p1 : hreal) (p2 : hreal) : (term45 p1 p2) = (term46 p1 p2).
Proof. exact (MK_COMB (@lem1327596) (@lem1327595 p1 p2)). Qed.
Lemma lem1327598 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term47 p1 p2 p1' p2') = ((term13 p1 p2 p1' p2') = (term13 p1' p2' p1 p2)).
Proof. exact (eq_refl (term47 p1 p2 p1' p2')). Qed.
Lemma lem1327599 (p1' : hreal) (p1 : hreal) (p2 : hreal) : (term48 p1 p2 p1') = (term49 p1' p1 p2).
Proof. exact (fun_ext (fun p2' : hreal => @lem1327598 p1' p2' p1 p2)). Qed.
Lemma lem1327600 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1327601 (p1' : hreal) (p1 : hreal) (p2 : hreal) : (term50 p1 p2 p1') = (term51 p1' p1 p2).
Proof. exact (MK_COMB (@lem1327600) (@lem1327599 p1' p1 p2)). Qed.
Lemma lem1327602 (p1 : hreal) (p2 : hreal) : (term52 p1 p2) = (term53 p1 p2).
Proof. exact (fun_ext (fun p1' : hreal => @lem1327601 p1' p1 p2)). Qed.
Lemma lem1327603 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1327604 (p1 : hreal) (p2 : hreal) : (term39 p1 p2) = (term54 p1 p2).
Proof. exact (MK_COMB (@lem1327603) (@lem1327602 p1 p2)). Qed.
Lemma lem1327605 (p1 : hreal) (p2 : hreal) : ((term38 p1 p2) = (term39 p1 p2)) = ((term30 p1 p2) = (term54 p1 p2)).
Proof. exact (MK_COMB (@lem1327597 p1 p2) (@lem1327604 p1 p2)). Qed.
Lemma lem1327606 (p1 : hreal) (p2 : hreal) : (term30 p1 p2) = (term54 p1 p2).
Proof. exact (EQ_MP (@lem1327605 p1 p2) (@lem1327591 p1 p2)). Qed.
Lemma lem1327622 (x1 : hreal) (y2 : hreal) (y1 : hreal) (x2 : hreal) : (term13 x1 y1 x2 y2) = (term14 x1 y2 y1 x2).
Proof. exact (EQ_MP (@lem1327544 x1 y2 y1 x2) (@lem1327543 x1 y2 y1 x2)). Qed.
Lemma lem1327623 (p1 : hreal) (p2' : hreal) (p2 : hreal) (p1' : hreal) : (term13 p1 p2 p1' p2') = (term14 p1 p2' p2 p1').
Proof. exact (@lem1327622 p1 p2' p2 p1'). Qed.
Lemma lem1327640 (y : hreal) (x : hreal) : (hreal_mul x y) = (hreal_mul y x).
Proof. exact (EQ_MP (@lem1327532 y x) (@lem1327531 x y)). Qed.
Lemma lem1327641 (p1' : hreal) (p2 : hreal) : (hreal_mul p2 p1') = (hreal_mul p1' p2).
Proof. exact (@lem1327640 p1' p2). Qed.
Lemma lem1327645 (p1 : hreal) (p2' : hreal) : (term55 p1 p2') = (term55 p1 p2').
Proof. exact (eq_refl (term55 p1 p2')). Qed.
Lemma lem1327646 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : (term56 p1 p2' p2 p1') = (term56 p1 p2' p1' p2).
Proof. exact (MK_COMB (@lem1327645 p1 p2') (@lem1327641 p1' p2)). Qed.
Lemma lem1327650 (p1 : hreal) (p1' : hreal) (p2 : hreal) (p2' : hreal) : (term57 p1 p1' p2 p2') = (term57 p1 p1' p2 p2').
Proof. exact (eq_refl (term57 p1 p1' p2 p2')). Qed.
Lemma lem1327651 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : (term14 p1 p2' p2 p1') = (term58 p1 p2' p1' p2).
Proof. exact (MK_COMB (@lem1327650 p1 p1' p2 p2') (@lem1327646 p1 p2' p1' p2)). Qed.
Lemma lem1327652 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : (term13 p1 p2 p1' p2') = (term58 p1 p2' p1' p2).
Proof. exact (TRANS (@lem1327623 p1 p2' p2 p1') (@lem1327651 p1 p2' p1' p2)). Qed.
Lemma lem1327653 : (@eq (prod hreal hreal)) = (@eq (prod hreal hreal)).
Proof. exact (eq_refl (@eq (prod hreal hreal))). Qed.
Lemma lem1327654 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : (term59 p1 p2 p1' p2') = (term60 p1 p2' p1' p2).
Proof. exact (MK_COMB (@lem1327653) (@lem1327652 p1 p2' p1' p2)). Qed.
Lemma lem1327656 (x1 : hreal) (y2 : hreal) (y1 : hreal) (x2 : hreal) : (term13 x1 y1 x2 y2) = (term14 x1 y2 y1 x2).
Proof. exact (EQ_MP (@lem1327544 x1 y2 y1 x2) (@lem1327543 x1 y2 y1 x2)). Qed.
Lemma lem1327657 (p1' : hreal) (p2 : hreal) (p2' : hreal) (p1 : hreal) : (term13 p1' p2' p1 p2) = (term14 p1' p2 p2' p1).
Proof. exact (@lem1327656 p1' p2 p2' p1). Qed.
Lemma lem1327662 (y : hreal) (x : hreal) : (hreal_mul x y) = (hreal_mul y x).
Proof. exact (EQ_MP (@lem1327532 y x) (@lem1327531 x y)). Qed.
Lemma lem1327663 (p1 : hreal) (p1' : hreal) : (hreal_mul p1' p1) = (hreal_mul p1 p1').
Proof. exact (@lem1327662 p1 p1'). Qed.
Lemma lem1327667 : hreal_add = hreal_add.
Proof. exact (eq_refl hreal_add). Qed.
Lemma lem1327668 (p1 : hreal) (p1' : hreal) : (term55 p1' p1) = (term55 p1 p1').
Proof. exact (MK_COMB (@lem1327667) (@lem1327663 p1 p1')). Qed.
Lemma lem1327670 (y : hreal) (x : hreal) : (hreal_mul x y) = (hreal_mul y x).
Proof. exact (EQ_MP (@lem1327532 y x) (@lem1327531 x y)). Qed.
Lemma lem1327671 (p2 : hreal) (p2' : hreal) : (hreal_mul p2' p2) = (hreal_mul p2 p2').
Proof. exact (@lem1327670 p2 p2'). Qed.
Lemma lem1327675 (p1 : hreal) (p1' : hreal) (p2 : hreal) (p2' : hreal) : (term56 p1' p1 p2' p2) = (term56 p1 p1' p2 p2').
Proof. exact (MK_COMB (@lem1327668 p1 p1') (@lem1327671 p2 p2')). Qed.
Lemma lem1327679 : (@pair hreal hreal) = (@pair hreal hreal).
Proof. exact (eq_refl (@pair hreal hreal)). Qed.
Lemma lem1327680 (p1 : hreal) (p1' : hreal) (p2 : hreal) (p2' : hreal) : (term57 p1' p1 p2' p2) = (term57 p1 p1' p2 p2').
Proof. exact (MK_COMB (@lem1327679) (@lem1327675 p1 p1' p2 p2')). Qed.
Lemma lem1327688 (y : hreal) (x : hreal) : (hreal_mul x y) = (hreal_mul y x).
Proof. exact (EQ_MP (@lem1327532 y x) (@lem1327531 x y)). Qed.
Lemma lem1327689 (p1 : hreal) (p2' : hreal) : (hreal_mul p2' p1) = (hreal_mul p1 p2').
Proof. exact (@lem1327688 p1 p2'). Qed.
Lemma lem1327693 (p1' : hreal) (p2 : hreal) : (term55 p1' p2) = (term55 p1' p2).
Proof. exact (eq_refl (term55 p1' p2)). Qed.
Lemma lem1327694 (p1' : hreal) (p2 : hreal) (p1 : hreal) (p2' : hreal) : (term56 p1' p2 p2' p1) = (term56 p1' p2 p1 p2').
Proof. exact (MK_COMB (@lem1327693 p1' p2) (@lem1327689 p1 p2')). Qed.
Lemma lem1327696 (y : hreal) (x : hreal) : (hreal_add x y) = (hreal_add y x).
Proof. exact (EQ_MP (@lem1327526 y x) (@lem1327525 x y)). Qed.
Lemma lem1327697 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : (term56 p1' p2 p1 p2') = (term56 p1 p2' p1' p2).
Proof. exact (@lem1327696 (hreal_mul p1 p2') (hreal_mul p1' p2)). Qed.
Lemma lem1327707 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : (term56 p1' p2 p2' p1) = (term56 p1 p2' p1' p2).
Proof. exact (TRANS (@lem1327694 p1' p2 p1 p2') (@lem1327697 p1 p2' p1' p2)). Qed.
Lemma lem1327708 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : (term14 p1' p2 p2' p1) = (term58 p1 p2' p1' p2).
Proof. exact (MK_COMB (@lem1327680 p1 p1' p2 p2') (@lem1327707 p1 p2' p1' p2)). Qed.
Lemma lem1327709 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : (term13 p1' p2' p1 p2) = (term58 p1 p2' p1' p2).
Proof. exact (TRANS (@lem1327657 p1' p2 p2' p1) (@lem1327708 p1 p2' p1' p2)). Qed.
Lemma lem1327710 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : ((term13 p1 p2 p1' p2') = (term13 p1' p2' p1 p2)) = ((term58 p1 p2' p1' p2) = (term58 p1 p2' p1' p2)).
Proof. exact (MK_COMB (@lem1327654 p1 p2' p1' p2) (@lem1327709 p1 p2' p1' p2)). Qed.
Lemma lem1327712 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1327713 (x : prod hreal hreal) : (x = x) = True.
Proof. exact (@lem1327712 (prod hreal hreal) x). Qed.
Lemma lem1327714 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : ((term58 p1 p2' p1' p2) = (term58 p1 p2' p1' p2)) = True.
Proof. exact (@lem1327713 (term58 p1 p2' p1' p2)). Qed.
Lemma lem1327715 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : ((term13 p1 p2 p1' p2') = (term13 p1' p2' p1 p2)) = True.
Proof. exact (TRANS (@lem1327710 p1 p2' p1' p2) (@lem1327714 p1 p2' p1' p2)). Qed.
Lemma lem1327716 (p1' : hreal) (p1 : hreal) (p2 : hreal) : (term49 p1' p1 p2) = term61.
Proof. exact (fun_ext (fun p2' : hreal => @lem1327715 p1' p2' p1 p2)). Qed.
Lemma lem1327717 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1327718 (p1' : hreal) (p1 : hreal) (p2 : hreal) : (term51 p1' p1 p2) = term62.
Proof. exact (MK_COMB (@lem1327717) (@lem1327716 p1' p1 p2)). Qed.
Lemma lem1327720 {A : Type'} (t : Prop) : (term63 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1327721 (t : Prop) : (term64 t) = t.
Proof. exact (@lem1327720 hreal t). Qed.
Lemma lem1327722 : term62 = True.
Proof. exact (@lem1327721 True). Qed.
Lemma lem1327723 (p1' : hreal) (p1 : hreal) (p2 : hreal) : (term51 p1' p1 p2) = True.
Proof. exact (TRANS (@lem1327718 p1' p1 p2) (@lem1327722)). Qed.
Lemma lem1327724 (p1 : hreal) (p2 : hreal) : (term53 p1 p2) = term61.
Proof. exact (fun_ext (fun p1' : hreal => @lem1327723 p1' p1 p2)). Qed.
Lemma lem1327725 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1327726 (p1 : hreal) (p2 : hreal) : (term54 p1 p2) = term62.
Proof. exact (MK_COMB (@lem1327725) (@lem1327724 p1 p2)). Qed.
Lemma lem1327728 {A : Type'} (t : Prop) : (term63 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1327729 (t : Prop) : (term64 t) = t.
Proof. exact (@lem1327728 hreal t). Qed.
Lemma lem1327730 : term62 = True.
Proof. exact (@lem1327729 True). Qed.
Lemma lem1327731 (p1 : hreal) (p2 : hreal) : (term54 p1 p2) = True.
Proof. exact (TRANS (@lem1327726 p1 p2) (@lem1327730)). Qed.
Lemma lem1327732 (p1 : hreal) (p2 : hreal) : (term30 p1 p2) = True.
Proof. exact (TRANS (@lem1327606 p1 p2) (@lem1327731 p1 p2)). Qed.
Lemma lem1327733 (p1 : hreal) : (term32 p1) = term61.
Proof. exact (fun_ext (fun p2 : hreal => @lem1327732 p1 p2)). Qed.
Lemma lem1327734 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1327735 (p1 : hreal) : (term34 p1) = term62.
Proof. exact (MK_COMB (@lem1327734) (@lem1327733 p1)). Qed.
Lemma lem1327737 {A : Type'} (t : Prop) : (term63 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1327738 (t : Prop) : (term64 t) = t.
Proof. exact (@lem1327737 hreal t). Qed.
Lemma lem1327739 : term62 = True.
Proof. exact (@lem1327738 True). Qed.
Lemma lem1327740 (p1 : hreal) : (term34 p1) = True.
Proof. exact (TRANS (@lem1327735 p1) (@lem1327739)). Qed.
Lemma lem1327741 : term36 = term61.
Proof. exact (fun_ext (fun p1 : hreal => @lem1327740 p1)). Qed.
Lemma lem1327742 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1327743 : term37 = term62.
Proof. exact (MK_COMB (@lem1327742) (@lem1327741)). Qed.
Lemma lem1327745 {A : Type'} (t : Prop) : (term63 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1327746 (t : Prop) : (term64 t) = t.
Proof. exact (@lem1327745 hreal t). Qed.
Lemma lem1327747 : term62 = True.
Proof. exact (@lem1327746 True). Qed.
Lemma lem1327748 : term37 = True.
Proof. exact (TRANS (@lem1327743) (@lem1327747)). Qed.
Lemma lem1327749 : term26 = True.
Proof. exact (TRANS (@lem1327571) (@lem1327748)). Qed.
Lemma lem1327750 : True = term26.
Proof. exact (SYM (@lem1327749)). Qed.
Lemma lem1327751 : term26.
Proof. exact (EQ_MP (@lem1327750) (@lem0)). Qed.
