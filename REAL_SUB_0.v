Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SUB_0_term_abbrevs.
Require Import REAL_NOT_LT_spec.
Require Import REAL_SUB_LE_spec.
Require Import REAL_SUB_LT_spec.
Require Import thm0_spec.
Require Import thm1339379_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1376538 (x : real) : term0 x.
Proof. exact (@lem1376537 x). Qed.
Lemma lem1376539 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1376540 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1376539 x) (@lem1376538 x)). Qed.
Lemma lem1376541 (x : real) (y : real) : term2 x y.
Proof. exact (@lem1376540 x y). Qed.
Lemma lem1376542 (y : real) (x : real) : (term2 x y) = ((term3 x y) = (real_le y x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1376544 (x : real) : term4 x.
Proof. exact (@lem1376486 x). Qed.
Lemma lem1376545 (x : real) : (term4 x) = (term5 x).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem1376546 (x : real) : term5 x.
Proof. exact (EQ_MP (@lem1376545 x) (@lem1376544 x)). Qed.
Lemma lem1376547 (x : real) (y : real) : term6 x y.
Proof. exact (@lem1376546 x y). Qed.
Lemma lem1376548 (y : real) (x : real) : (term6 x y) = ((term7 x y) = (real_lt y x)).
Proof. exact (eq_refl (term6 x y)). Qed.
Lemma lem1376550 (x : real) : term8 x.
Proof. exact (@lem1374224 x). Qed.
Lemma lem1376551 (x : real) : (term8 x) = (term9 x).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem1376552 (x : real) : term9 x.
Proof. exact (EQ_MP (@lem1376551 x) (@lem1376550 x)). Qed.
Lemma lem1376553 (x : real) (y : real) : term10 x y.
Proof. exact (@lem1376552 x y). Qed.
Lemma lem1376554 (y : real) (x : real) : (term10 x y) = ((term11 x y) = (real_le y x)).
Proof. exact (eq_refl (term10 x y)). Qed.
Lemma lem1376558 (y : real) (x : real) (h1 : (term3 x y) = (real_le y x)) : (term3 x y) = (real_le y x).
Proof. exact (h1). Qed.
Lemma lem1376559 (y : real) (x : real) (h1 : (term3 x y) = (real_le y x)) : (real_le y x) = (term3 x y).
Proof. exact (SYM (@lem1376558 y x h1)). Qed.
Lemma lem1376560 (x : real) (y : real) (h1 : (real_le y x) = (term3 x y)) : (real_le y x) = (term3 x y).
Proof. exact (h1). Qed.
Lemma lem1376561 (x : real) (y : real) (h1 : (real_le y x) = (term3 x y)) : (term3 x y) = (real_le y x).
Proof. exact (SYM (@lem1376560 x y h1)). Qed.
Lemma lem1376562 (x : real) (y : real) : ((term3 x y) = (real_le y x)) = ((real_le y x) = (term3 x y)).
Proof. exact (prop_ext (fun h1 : (term3 x y) = (real_le y x) => @lem1376559 y x h1) (fun h1 : (real_le y x) = (term3 x y) => @lem1376561 x y h1)). Qed.
Lemma lem1376563 (x : real) : (term12 x) = (term13 x).
Proof. exact (fun_ext (fun y : real => @lem1376562 x y)). Qed.
Lemma lem1376564 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1376565 (x : real) : (term1 x) = (term14 x).
Proof. exact (MK_COMB (@lem1376564) (@lem1376563 x)). Qed.
Lemma lem1376566 : term15 = term16.
Proof. exact (fun_ext (fun x : real => @lem1376565 x)). Qed.
Lemma lem1376567 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1376568 : term17 = term18.
Proof. exact (MK_COMB (@lem1376567) (@lem1376566)). Qed.
Lemma lem1376569 : term18.
Proof. exact (EQ_MP (@lem1376568) (@lem1376537)). Qed.
Lemma lem1376570 (x : real) : term19 x.
Proof. exact (@lem1376569 x). Qed.
Lemma lem1376571 (x : real) : (term19 x) = (term14 x).
Proof. exact (eq_refl (term19 x)). Qed.
Lemma lem1376572 (x : real) : term14 x.
Proof. exact (EQ_MP (@lem1376571 x) (@lem1376570 x)). Qed.
Lemma lem1376573 (x : real) (y : real) : term20 x y.
Proof. exact (@lem1376572 x y). Qed.
Lemma lem1376574 (x : real) (y : real) : (term20 x y) = ((real_le y x) = (term3 x y)).
Proof. exact (eq_refl (term20 x y)). Qed.
Lemma lem1376578 (x : real) (y : real) (h1 : (term21 y x) = (x = y)) : (term21 y x) = (x = y).
Proof. exact (h1). Qed.
Lemma lem1376579 (x : real) (y : real) (h1 : (term21 y x) = (x = y)) : (x = y) = (term21 y x).
Proof. exact (SYM (@lem1376578 x y h1)). Qed.
Lemma lem1376580 (y : real) (x : real) (h1 : (x = y) = (term21 y x)) : (x = y) = (term21 y x).
Proof. exact (h1). Qed.
Lemma lem1376581 (y : real) (x : real) (h1 : (x = y) = (term21 y x)) : (term21 y x) = (x = y).
Proof. exact (SYM (@lem1376580 y x h1)). Qed.
Lemma lem1376582 (y : real) (x : real) : ((term21 y x) = (x = y)) = ((x = y) = (term21 y x)).
Proof. exact (prop_ext (fun h1 : (term21 y x) = (x = y) => @lem1376579 x y h1) (fun h1 : (x = y) = (term21 y x) => @lem1376581 y x h1)). Qed.
Lemma lem1376583 (x : real) : (term22 x) = (term23 x).
Proof. exact (fun_ext (fun y : real => @lem1376582 y x)). Qed.
Lemma lem1376584 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1376585 (x : real) : (term24 x) = (term25 x).
Proof. exact (MK_COMB (@lem1376584) (@lem1376583 x)). Qed.
Lemma lem1376586 : term26 = term27.
Proof. exact (fun_ext (fun x : real => @lem1376585 x)). Qed.
Lemma lem1376587 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1376588 : term28 = term29.
Proof. exact (MK_COMB (@lem1376587) (@lem1376586)). Qed.
Lemma lem1376589 : term29.
Proof. exact (EQ_MP (@lem1376588) (@lem1339379)). Qed.
Lemma lem1376590 (x : real) : term30 x.
Proof. exact (@lem1376589 x). Qed.
Lemma lem1376591 (x : real) : (term30 x) = (term25 x).
Proof. exact (eq_refl (term30 x)). Qed.
Lemma lem1376592 (x : real) : term25 x.
Proof. exact (EQ_MP (@lem1376591 x) (@lem1376590 x)). Qed.
Lemma lem1376593 (x : real) (y : real) : term31 x y.
Proof. exact (@lem1376592 x y). Qed.
Lemma lem1376594 (y : real) (x : real) : (term31 x y) = ((x = y) = (term21 y x)).
Proof. exact (eq_refl (term31 x y)). Qed.
Lemma lem1376603 (y : real) (x : real) : (x = y) = (term21 y x).
Proof. exact (EQ_MP (@lem1376594 y x) (@lem1376593 x y)). Qed.
Lemma lem1376604 (x : real) (y : real) : ((real_sub x y) = term32) = (term33 x y).
Proof. exact (@lem1376603 term32 (real_sub x y)). Qed.
Lemma lem1376607 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1376608 (x : real) (y : real) : (term34 x y) = (term35 x y).
Proof. exact (MK_COMB (@lem1376607) (@lem1376604 x y)). Qed.
Lemma lem1376612 (y : real) (x : real) : (x = y) = (term21 y x).
Proof. exact (EQ_MP (@lem1376594 y x) (@lem1376593 x y)). Qed.
Lemma lem1376615 (y : real) (x : real) : (((real_sub x y) = term32) = (x = y)) = ((term33 x y) = (term21 y x)).
Proof. exact (MK_COMB (@lem1376608 x y) (@lem1376612 y x)). Qed.
Lemma lem1376620 (x : real) (y : real) : ((term33 x y) = (term21 y x)) = (((real_sub x y) = term32) = (x = y)).
Proof. exact (SYM (@lem1376615 y x)). Qed.
Lemma lem1376622 (x : real) (y : real) : (real_le y x) = (term3 x y).
Proof. exact (EQ_MP (@lem1376574 x y) (@lem1376573 x y)). Qed.
Lemma lem1376623 (x : real) (y : real) : (term36 x y) = (term37 x y).
Proof. exact (@lem1376622 term32 (real_sub x y)). Qed.
Lemma lem1376624 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1376625 (x : real) (y : real) : (term38 x y) = (term39 x y).
Proof. exact (MK_COMB (@lem1376624) (@lem1376623 x y)). Qed.
Lemma lem1376626 (x : real) (y : real) : (term11 x y) = (term11 x y).
Proof. exact (eq_refl (term11 x y)). Qed.
Lemma lem1376627 (x : real) (y : real) : (term33 x y) = (term40 x y).
Proof. exact (MK_COMB (@lem1376625 x y) (@lem1376626 x y)). Qed.
Lemma lem1376628 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1376629 (x : real) (y : real) : (term35 x y) = (term41 x y).
Proof. exact (MK_COMB (@lem1376628) (@lem1376627 x y)). Qed.
Lemma lem1376630 (y : real) (x : real) : (term21 y x) = (term21 y x).
Proof. exact (eq_refl (term21 y x)). Qed.
Lemma lem1376631 (y : real) (x : real) : ((term33 x y) = (term21 y x)) = ((term40 x y) = (term21 y x)).
Proof. exact (MK_COMB (@lem1376629 x y) (@lem1376630 y x)). Qed.
Lemma lem1376632 (y : real) (x : real) : ((term40 x y) = (term21 y x)) = ((term33 x y) = (term21 y x)).
Proof. exact (SYM (@lem1376631 y x)). Qed.
Lemma lem1376638 (y : real) (x : real) : (term7 x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1376548 y x) (@lem1376547 x y)). Qed.
Lemma lem1376639 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1376640 (y : real) (x : real) : (term37 x y) = (term3 y x).
Proof. exact (MK_COMB (@lem1376639) (@lem1376638 y x)). Qed.
Lemma lem1376641 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1376642 (y : real) (x : real) : (term39 x y) = (term42 y x).
Proof. exact (MK_COMB (@lem1376641) (@lem1376640 y x)). Qed.
Lemma lem1376644 (y : real) (x : real) : (term11 x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1376554 y x) (@lem1376553 x y)). Qed.
Lemma lem1376645 (y : real) (x : real) : (term40 x y) = (term43 y x).
Proof. exact (MK_COMB (@lem1376642 y x) (@lem1376644 y x)). Qed.
Lemma lem1376648 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1376649 (y : real) (x : real) : (term41 x y) = (term44 y x).
Proof. exact (MK_COMB (@lem1376648) (@lem1376645 y x)). Qed.
Lemma lem1376652 (y : real) (x : real) : (term21 y x) = (term21 y x).
Proof. exact (eq_refl (term21 y x)). Qed.
Lemma lem1376653 (y : real) (x : real) : ((term40 x y) = (term21 y x)) = ((term43 y x) = (term21 y x)).
Proof. exact (MK_COMB (@lem1376649 y x) (@lem1376652 y x)). Qed.
Lemma lem1376656 (y : real) (x : real) : ((term43 y x) = (term21 y x)) = ((term40 x y) = (term21 y x)).
Proof. exact (SYM (@lem1376653 y x)). Qed.
Lemma lem1376662 (y : real) (x : real) : (term3 x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1376542 y x) (@lem1376541 x y)). Qed.
Lemma lem1376663 (x : real) (y : real) : (term3 y x) = (real_le x y).
Proof. exact (@lem1376662 x y). Qed.
Lemma lem1376664 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1376665 (x : real) (y : real) : (term42 y x) = (term45 x y).
Proof. exact (MK_COMB (@lem1376664) (@lem1376663 x y)). Qed.
Lemma lem1376666 (y : real) (x : real) : (real_le y x) = (real_le y x).
Proof. exact (eq_refl (real_le y x)). Qed.
Lemma lem1376667 (y : real) (x : real) : (term43 y x) = (term21 y x).
Proof. exact (MK_COMB (@lem1376665 x y) (@lem1376666 y x)). Qed.
Lemma lem1376670 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1376671 (y : real) (x : real) : (term44 y x) = (term46 y x).
Proof. exact (MK_COMB (@lem1376670) (@lem1376667 y x)). Qed.
Lemma lem1376674 (y : real) (x : real) : (term21 y x) = (term21 y x).
Proof. exact (eq_refl (term21 y x)). Qed.
Lemma lem1376675 (y : real) (x : real) : ((term43 y x) = (term21 y x)) = ((term21 y x) = (term21 y x)).
Proof. exact (MK_COMB (@lem1376671 y x) (@lem1376674 y x)). Qed.
Lemma lem1376677 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1376678 (x : Prop) : (x = x) = True.
Proof. exact (@lem1376677 Prop x). Qed.
Lemma lem1376679 (y : real) (x : real) : ((term21 y x) = (term21 y x)) = True.
Proof. exact (@lem1376678 (term21 y x)). Qed.
Lemma lem1376680 (y : real) (x : real) : ((term43 y x) = (term21 y x)) = True.
Proof. exact (TRANS (@lem1376675 y x) (@lem1376679 y x)). Qed.
Lemma lem1376681 (y : real) (x : real) : True = ((term43 y x) = (term21 y x)).
Proof. exact (SYM (@lem1376680 y x)). Qed.
Lemma lem1376682 (y : real) (x : real) : (term43 y x) = (term21 y x).
Proof. exact (EQ_MP (@lem1376681 y x) (@lem0)). Qed.
Lemma lem1376683 (y : real) (x : real) : (term40 x y) = (term21 y x).
Proof. exact (EQ_MP (@lem1376656 y x) (@lem1376682 y x)). Qed.
Lemma lem1376684 (y : real) (x : real) : (term33 x y) = (term21 y x).
Proof. exact (EQ_MP (@lem1376632 y x) (@lem1376683 y x)). Qed.
Lemma lem1376685 (x : real) (y : real) : ((real_sub x y) = term32) = (x = y).
Proof. exact (EQ_MP (@lem1376620 x y) (@lem1376684 y x)). Qed.
Lemma lem1376690 (x : real) : term47 x.
Proof. exact (fun y : real => @lem1376685 x y). Qed.
Lemma lem1376695 : term48.
Proof. exact (fun x : real => @lem1376690 x). Qed.
