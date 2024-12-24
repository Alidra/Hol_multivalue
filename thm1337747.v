Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1337747_term_abbrevs.
Require Import TREAL_ADD_WELLDEF_spec.
Require Import TREAL_EQ_REFL_spec.
Require Import TREAL_EQ_TRANS_spec.
Require Import thm1337493_spec.
Require Import thm32_spec.
Require Import thm9127_spec.
Lemma lem1337629 : real_add = term0.
Proof. exact (@real_add_def). Qed.
Lemma lem1337630 (x1 : real) : x1 = x1.
Proof. exact (eq_refl x1). Qed.
Lemma lem1337631 (x1 : real) : (real_add x1) = (term1 x1).
Proof. exact (MK_COMB (@lem1337629) (@lem1337630 x1)). Qed.
Lemma lem1337632 (x1 : real) : (term1 x1) = (term2 x1).
Proof. exact (eq_refl (term1 x1)). Qed.
Lemma lem1337633 (x1 : real) : (term3 x1) = (term3 x1).
Proof. exact (eq_refl (term3 x1)). Qed.
Lemma lem1337634 (x1 : real) : ((real_add x1) = (term1 x1)) = ((real_add x1) = (term2 x1)).
Proof. exact (MK_COMB (@lem1337633 x1) (@lem1337632 x1)). Qed.
Lemma lem1337635 (x1 : real) : (real_add x1) = (term2 x1).
Proof. exact (EQ_MP (@lem1337634 x1) (@lem1337631 x1)). Qed.
Lemma lem1337636 (y1 : real) : y1 = y1.
Proof. exact (eq_refl y1). Qed.
Lemma lem1337637 (x1 : real) (y1 : real) : (real_add x1 y1) = (term4 x1 y1).
Proof. exact (MK_COMB (@lem1337635 x1) (@lem1337636 y1)). Qed.
Lemma lem1337638 (x1 : real) (y1 : real) : (term4 x1 y1) = (term5 x1 y1).
Proof. exact (eq_refl (term4 x1 y1)). Qed.
Lemma lem1337639 (x1 : real) (y1 : real) : (term6 x1 y1) = (term6 x1 y1).
Proof. exact (eq_refl (term6 x1 y1)). Qed.
Lemma lem1337640 (x1 : real) (y1 : real) : ((real_add x1 y1) = (term4 x1 y1)) = ((real_add x1 y1) = (term5 x1 y1)).
Proof. exact (MK_COMB (@lem1337639 x1 y1) (@lem1337638 x1 y1)). Qed.
Lemma lem1337641 (x1 : real) (y1 : real) : (real_add x1 y1) = (term5 x1 y1).
Proof. exact (EQ_MP (@lem1337640 x1 y1) (@lem1337637 x1 y1)). Qed.
Lemma lem1337642 (x : prod hreal hreal) : (term7 x) = ((term8 x) = (treal_eq x)).
Proof. exact (@lem1337493 (treal_eq x)). Qed.
Lemma lem1337643 (x : prod hreal hreal) : (treal_eq x) = (treal_eq x).
Proof. exact (eq_refl (treal_eq x)). Qed.
Lemma lem1337644 (x : prod hreal hreal) : term7 x.
Proof. exact (ex_intro (term9 x) x (@lem1337643 x)). Qed.
Lemma lem1337645 (x : prod hreal hreal) : (term8 x) = (treal_eq x).
Proof. exact (EQ_MP (@lem1337642 x) (@lem1337644 x)). Qed.
Lemma lem1337646 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term10 x1 y1) = (term11 x1 y1).
Proof. exact (@lem1337641 (term12 x1) (term12 y1)). Qed.
Lemma lem1337647 (x1 : prod hreal hreal) : (term8 x1) = (treal_eq x1).
Proof. exact (@lem1337645 x1). Qed.
Lemma lem1337648 (y1 : prod hreal hreal) : (term8 y1) = (treal_eq y1).
Proof. exact (@lem1337645 y1). Qed.
Lemma lem1337649 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term13 x1 y1) = (term13 x1 y1).
Proof. exact (eq_refl (term13 x1 y1)). Qed.
Lemma lem1337650 (y1 : prod hreal hreal) (x1 : prod hreal hreal) : (term14 y1 x1) = (term15 y1 x1).
Proof. exact (MK_COMB (@lem1337649 x1 y1) (@lem1337647 x1)). Qed.
Lemma lem1337651 (y1 : prod hreal hreal) (x1 : prod hreal hreal) : (term15 y1 x1) = (term16 y1 x1).
Proof. exact (eq_refl (term15 y1 x1)). Qed.
Lemma lem1337652 (y1 : prod hreal hreal) (x1 : prod hreal hreal) : (term17 y1 x1) = (term17 y1 x1).
Proof. exact (eq_refl (term17 y1 x1)). Qed.
Lemma lem1337653 (y1 : prod hreal hreal) (x1 : prod hreal hreal) : ((term14 y1 x1) = (term15 y1 x1)) = ((term14 y1 x1) = (term16 y1 x1)).
Proof. exact (MK_COMB (@lem1337652 y1 x1) (@lem1337651 y1 x1)). Qed.
Lemma lem1337654 (y1 : prod hreal hreal) (x1 : prod hreal hreal) : (term14 y1 x1) = (term18 y1 x1).
Proof. exact (eq_refl (term14 y1 x1)). Qed.
Lemma lem1337655 : (@eq (((prod hreal hreal) -> Prop) -> Prop)) = (@eq (((prod hreal hreal) -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq (((prod hreal hreal) -> Prop) -> Prop))). Qed.
Lemma lem1337656 (y1 : prod hreal hreal) (x1 : prod hreal hreal) : (term17 y1 x1) = (term19 y1 x1).
Proof. exact (MK_COMB (@lem1337655) (@lem1337654 y1 x1)). Qed.
Lemma lem1337657 (y1 : prod hreal hreal) (x1 : prod hreal hreal) : (term16 y1 x1) = (term16 y1 x1).
Proof. exact (eq_refl (term16 y1 x1)). Qed.
Lemma lem1337658 (y1 : prod hreal hreal) (x1 : prod hreal hreal) : ((term14 y1 x1) = (term16 y1 x1)) = ((term18 y1 x1) = (term16 y1 x1)).
Proof. exact (MK_COMB (@lem1337656 y1 x1) (@lem1337657 y1 x1)). Qed.
Lemma lem1337659 (y1 : prod hreal hreal) (x1 : prod hreal hreal) : ((term14 y1 x1) = (term15 y1 x1)) = ((term18 y1 x1) = (term16 y1 x1)).
Proof. exact (TRANS (@lem1337653 y1 x1) (@lem1337658 y1 x1)). Qed.
Lemma lem1337660 (y1 : prod hreal hreal) (x1 : prod hreal hreal) : (term18 y1 x1) = (term16 y1 x1).
Proof. exact (EQ_MP (@lem1337659 y1 x1) (@lem1337650 y1 x1)). Qed.
Lemma lem1337661 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term20 x1 y1) = (term21 x1 y1).
Proof. exact (MK_COMB (@lem1337660 y1 x1) (@lem1337648 y1)). Qed.
Lemma lem1337662 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term21 x1 y1) = ((term10 x1 y1) = (term22 x1 y1)).
Proof. exact (eq_refl (term21 x1 y1)). Qed.
Lemma lem1337663 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term23 x1 y1) = (term23 x1 y1).
Proof. exact (eq_refl (term23 x1 y1)). Qed.
Lemma lem1337664 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : ((term20 x1 y1) = (term21 x1 y1)) = ((term20 x1 y1) = ((term10 x1 y1) = (term22 x1 y1))).
Proof. exact (MK_COMB (@lem1337663 x1 y1) (@lem1337662 x1 y1)). Qed.
Lemma lem1337665 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term20 x1 y1) = ((term10 x1 y1) = (term11 x1 y1)).
Proof. exact (eq_refl (term20 x1 y1)). Qed.
Lemma lem1337666 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1337667 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term23 x1 y1) = (term24 x1 y1).
Proof. exact (MK_COMB (@lem1337666) (@lem1337665 x1 y1)). Qed.
Lemma lem1337668 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : ((term10 x1 y1) = (term22 x1 y1)) = ((term10 x1 y1) = (term22 x1 y1)).
Proof. exact (eq_refl ((term10 x1 y1) = (term22 x1 y1))). Qed.
Lemma lem1337669 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : ((term20 x1 y1) = ((term10 x1 y1) = (term22 x1 y1))) = (((term10 x1 y1) = (term11 x1 y1)) = ((term10 x1 y1) = (term22 x1 y1))).
Proof. exact (MK_COMB (@lem1337667 x1 y1) (@lem1337668 x1 y1)). Qed.
Lemma lem1337670 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : ((term20 x1 y1) = (term21 x1 y1)) = (((term10 x1 y1) = (term11 x1 y1)) = ((term10 x1 y1) = (term22 x1 y1))).
Proof. exact (TRANS (@lem1337664 x1 y1) (@lem1337669 x1 y1)). Qed.
Lemma lem1337671 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : ((term10 x1 y1) = (term11 x1 y1)) = ((term10 x1 y1) = (term22 x1 y1)).
Proof. exact (EQ_MP (@lem1337670 x1 y1) (@lem1337661 x1 y1)). Qed.
Lemma lem1337672 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term10 x1 y1) = (term22 x1 y1).
Proof. exact (EQ_MP (@lem1337671 x1 y1) (@lem1337646 x1 y1)). Qed.
Lemma lem1337673 (u : prod hreal hreal) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (y1 : prod hreal hreal) (y1' : prod hreal hreal) (h1 : term25 u x1 x1' y1 y1') : term25 u x1 x1' y1 y1'.
Proof. exact (h1). Qed.
Lemma lem1337674 (u : prod hreal hreal) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (y1 : prod hreal hreal) (y1' : prod hreal hreal) (h1 : term25 u x1 x1' y1 y1') : term26 x1 x1' y1 y1'.
Proof. exact (proj2 (@lem1337673 u x1 x1' y1 y1' h1)). Qed.
Lemma lem1337675 (u : prod hreal hreal) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (y1 : prod hreal hreal) (y1' : prod hreal hreal) (h1 : term25 u x1 x1' y1 y1') : term27 x1' y1' u.
Proof. exact (proj1 (@lem1337673 u x1 x1' y1 y1' h1)). Qed.
Lemma lem1337676 (u : prod hreal hreal) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (y1 : prod hreal hreal) (y1' : prod hreal hreal) (h1 : term25 u x1 x1' y1 y1') : treal_eq y1 y1'.
Proof. exact (proj2 (@lem1337674 u x1 x1' y1 y1' h1)). Qed.
Lemma lem1337677 (u : prod hreal hreal) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (y1 : prod hreal hreal) (y1' : prod hreal hreal) (h1 : term25 u x1 x1' y1 y1') : treal_eq x1 x1'.
Proof. exact (proj1 (@lem1337674 u x1 x1' y1 y1' h1)). Qed.
Lemma lem1337678 (u : prod hreal hreal) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (y1 : prod hreal hreal) (y1' : prod hreal hreal) (h1 : term25 u x1 x1' y1 y1') : term26 x1 x1' y1 y1'.
Proof. exact (conj (@lem1337677 u x1 x1' y1 y1' h1) (@lem1337676 u x1 x1' y1 y1' h1)). Qed.
Lemma lem1337679 (x1 : prod hreal hreal) : term28 x1.
Proof. exact (@lem1333561 x1). Qed.
Lemma lem1337680 (x1 : prod hreal hreal) : (term28 x1) = (term29 x1).
Proof. exact (eq_refl (term28 x1)). Qed.
Lemma lem1337681 (x1 : prod hreal hreal) : term29 x1.
Proof. exact (EQ_MP (@lem1337680 x1) (@lem1337679 x1)). Qed.
Lemma lem1337682 (x1 : prod hreal hreal) (x2 : prod hreal hreal) : term30 x1 x2.
Proof. exact (@lem1337681 x1 x2). Qed.
Lemma lem1337683 (x1 : prod hreal hreal) (x2 : prod hreal hreal) : (term30 x1 x2) = (term31 x1 x2).
Proof. exact (eq_refl (term30 x1 x2)). Qed.
Lemma lem1337684 (x1 : prod hreal hreal) (x2 : prod hreal hreal) : term31 x1 x2.
Proof. exact (EQ_MP (@lem1337683 x1 x2) (@lem1337682 x1 x2)). Qed.
Lemma lem1337685 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y1 : prod hreal hreal) : term32 x1 x2 y1.
Proof. exact (@lem1337684 x1 x2 y1). Qed.
Lemma lem1337686 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (x2 : prod hreal hreal) : (term32 x1 x2 y1) = (term33 x1 y1 x2).
Proof. exact (eq_refl (term32 x1 x2 y1)). Qed.
Lemma lem1337687 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (x2 : prod hreal hreal) : term33 x1 y1 x2.
Proof. exact (EQ_MP (@lem1337686 x1 y1 x2) (@lem1337685 x1 x2 y1)). Qed.
Lemma lem1337688 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (x2 : prod hreal hreal) (y2 : prod hreal hreal) : term34 x1 y1 x2 y2.
Proof. exact (@lem1337687 x1 y1 x2 y2). Qed.
Lemma lem1337689 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (x2 : prod hreal hreal) (y2 : prod hreal hreal) : (term34 x1 y1 x2 y2) = (term35 x1 y1 x2 y2).
Proof. exact (eq_refl (term34 x1 y1 x2 y2)). Qed.
Lemma lem1337692 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (x2 : prod hreal hreal) (y2 : prod hreal hreal) : term35 x1 y1 x2 y2.
Proof. exact (EQ_MP (@lem1337689 x1 y1 x2 y2) (@lem1337688 x1 y1 x2 y2)). Qed.
Lemma lem1337693 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (x1' : prod hreal hreal) (y1' : prod hreal hreal) : term35 x1 y1 x1' y1'.
Proof. exact (@lem1337692 x1 y1 x1' y1'). Qed.
Lemma lem1337694 (u : prod hreal hreal) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (y1 : prod hreal hreal) (y1' : prod hreal hreal) (h1 : term25 u x1 x1' y1 y1') : term36 x1 y1 x1' y1'.
Proof. exact (@lem1337693 x1 y1 x1' y1' (@lem1337678 u x1 x1' y1 y1' h1)). Qed.
Lemma lem1337695 (u : prod hreal hreal) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (y1 : prod hreal hreal) (y1' : prod hreal hreal) (h1 : term25 u x1 x1' y1 y1') : term37 x1 y1 x1' y1' u.
Proof. exact (conj (@lem1337694 u x1 x1' y1 y1' h1) (@lem1337675 u x1 x1' y1 y1' h1)). Qed.
Lemma lem1337696 (x : prod hreal hreal) : term38 x.
Proof. exact (@lem1326778 x). Qed.
Lemma lem1337697 (x : prod hreal hreal) : (term38 x) = (term39 x).
Proof. exact (eq_refl (term38 x)). Qed.
Lemma lem1337698 (x : prod hreal hreal) : term39 x.
Proof. exact (EQ_MP (@lem1337697 x) (@lem1337696 x)). Qed.
Lemma lem1337699 (x : prod hreal hreal) (y : prod hreal hreal) : term40 x y.
Proof. exact (@lem1337698 x y). Qed.
Lemma lem1337700 (y : prod hreal hreal) (x : prod hreal hreal) : (term40 x y) = (term41 y x).
Proof. exact (eq_refl (term40 x y)). Qed.
Lemma lem1337701 (y : prod hreal hreal) (x : prod hreal hreal) : term41 y x.
Proof. exact (EQ_MP (@lem1337700 y x) (@lem1337699 x y)). Qed.
Lemma lem1337702 (y : prod hreal hreal) (x : prod hreal hreal) (z : prod hreal hreal) : term42 y x z.
Proof. exact (@lem1337701 y x z). Qed.
Lemma lem1337703 (y : prod hreal hreal) (x : prod hreal hreal) (z : prod hreal hreal) : (term42 y x z) = (term43 y x z).
Proof. exact (eq_refl (term42 y x z)). Qed.
Lemma lem1337706 (y : prod hreal hreal) (x : prod hreal hreal) (z : prod hreal hreal) : term43 y x z.
Proof. exact (EQ_MP (@lem1337703 y x z) (@lem1337702 y x z)). Qed.
Lemma lem1337707 (x1' : prod hreal hreal) (y1' : prod hreal hreal) (x1 : prod hreal hreal) (y1 : prod hreal hreal) (u : prod hreal hreal) : term44 x1' y1' x1 y1 u.
Proof. exact (@lem1337706 (treal_add x1' y1') (treal_add x1 y1) u). Qed.
Lemma lem1337708 (u : prod hreal hreal) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (y1 : prod hreal hreal) (y1' : prod hreal hreal) (h1 : term25 u x1 x1' y1 y1') : term27 x1 y1 u.
Proof. exact (@lem1337707 x1' y1' x1 y1 u (@lem1337695 u x1 x1' y1 y1' h1)). Qed.
Lemma lem1337709 (u : prod hreal hreal) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (y1 : prod hreal hreal) (h1 : term45 u x1 x1' y1) : term45 u x1 x1' y1.
Proof. exact (h1). Qed.
Lemma lem1337710 (u : prod hreal hreal) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (y1 : prod hreal hreal) (h1 : term45 u x1 x1' y1) : term27 x1 y1 u.
Proof. exact (ex_elim (@lem1337709 u x1 x1' y1 h1) (fun y1' : prod hreal hreal => fun h0 : term46 u x1 x1' y1 y1' => @lem1337708 u x1 x1' y1 y1' h0)). Qed.
Lemma lem1337711 (u : prod hreal hreal) (x1 : prod hreal hreal) (y1 : prod hreal hreal) (h1 : term47 u x1 y1) : term47 u x1 y1.
Proof. exact (h1). Qed.
Lemma lem1337712 (u : prod hreal hreal) (x1 : prod hreal hreal) (y1 : prod hreal hreal) (h1 : term47 u x1 y1) : term27 x1 y1 u.
Proof. exact (ex_elim (@lem1337711 u x1 y1 h1) (fun x1' : prod hreal hreal => fun h0 : term48 u x1 y1 x1' => @lem1337710 u x1 x1' y1 h0)). Qed.
Lemma lem1337713 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (u : prod hreal hreal) (h1 : term27 x1 y1 u) : term27 x1 y1 u.
Proof. exact (h1). Qed.
Lemma lem1337714 (x1 : prod hreal hreal) : term49 x1.
Proof. exact (@lem1326193 x1). Qed.
Lemma lem1337715 (x1 : prod hreal hreal) : (term49 x1) = (treal_eq x1 x1).
Proof. exact (eq_refl (term49 x1)). Qed.
Lemma lem1337716 (x1 : prod hreal hreal) : treal_eq x1 x1.
Proof. exact (EQ_MP (@lem1337715 x1) (@lem1337714 x1)). Qed.
Lemma lem1337717 (y1 : prod hreal hreal) : term49 y1.
Proof. exact (@lem1326193 y1). Qed.
Lemma lem1337718 (y1 : prod hreal hreal) : (term49 y1) = (treal_eq y1 y1).
Proof. exact (eq_refl (term49 y1)). Qed.
Lemma lem1337719 (y1 : prod hreal hreal) : treal_eq y1 y1.
Proof. exact (EQ_MP (@lem1337718 y1) (@lem1337717 y1)). Qed.
Lemma lem1337720 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : term50 x1 y1.
Proof. exact (conj (@lem1337716 x1) (@lem1337719 y1)). Qed.
Lemma lem1337721 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (u : prod hreal hreal) (h1 : term27 x1 y1 u) : term51 u x1 y1.
Proof. exact (conj (@lem1337713 x1 y1 u h1) (@lem1337720 x1 y1)). Qed.
Lemma lem1337722 (u : prod hreal hreal) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (y1 : prod hreal hreal) (y1' : prod hreal hreal) (h1 : term25 u x1 x1' y1 y1') : term25 u x1 x1' y1 y1'.
Proof. exact (h1). Qed.
Lemma lem1337723 (u : prod hreal hreal) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (y1 : prod hreal hreal) (y1' : prod hreal hreal) (h1 : term25 u x1 x1' y1 y1') : term45 u x1 x1' y1.
Proof. exact (ex_intro (term46 u x1 x1' y1) y1' (@lem1337722 u x1 x1' y1 y1' h1)). Qed.
Lemma lem1337724 (u : prod hreal hreal) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (y1 : prod hreal hreal) (y1' : prod hreal hreal) (h1 : term25 u x1 x1' y1 y1') : term47 u x1 y1.
Proof. exact (ex_intro (term48 u x1 y1) x1' (@lem1337723 u x1 x1' y1 y1' h1)). Qed.
Lemma lem1337727 (x1' : prod hreal hreal) (y1' : prod hreal hreal) (u : prod hreal hreal) (x1 : prod hreal hreal) (y1 : prod hreal hreal) : term52 x1' y1' u x1 y1.
Proof. exact (fun h0 : term25 u x1 x1' y1 y1' => @lem1337724 u x1 x1' y1 y1' h0). Qed.
Lemma lem1337728 (u : prod hreal hreal) (x1 : prod hreal hreal) (y1 : prod hreal hreal) : term53 u x1 y1.
Proof. exact (@lem1337727 x1 y1 u x1 y1). Qed.
Lemma lem1337729 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (u : prod hreal hreal) (h1 : term27 x1 y1 u) : term47 u x1 y1.
Proof. exact (@lem1337728 u x1 y1 (@lem1337721 x1 y1 u h1)). Qed.
Lemma lem1337730 (u : prod hreal hreal) (x1 : prod hreal hreal) (y1 : prod hreal hreal) : term54 u x1 y1.
Proof. exact (fun h0 : term27 x1 y1 u => @lem1337729 x1 y1 u h0). Qed.
Lemma lem1337731 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (u : prod hreal hreal) : term55 x1 y1 u.
Proof. exact (fun h0 : term47 u x1 y1 => @lem1337712 u x1 y1 h0). Qed.
Lemma lem1337732 (u : prod hreal hreal) (x1 : prod hreal hreal) (y1 : prod hreal hreal) : term56 u x1 y1.
Proof. exact (conj (@lem1337731 x1 y1 u) (@lem1337730 u x1 y1)). Qed.
Lemma lem1337733 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (u : prod hreal hreal) : (term56 u x1 y1) = ((term47 u x1 y1) = (term27 x1 y1 u)).
Proof. exact (@lem32 (term47 u x1 y1) (term27 x1 y1 u)). Qed.
Lemma lem1337734 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (u : prod hreal hreal) : (term47 u x1 y1) = (term27 x1 y1 u).
Proof. exact (EQ_MP (@lem1337733 x1 y1 u) (@lem1337732 u x1 y1)). Qed.
Lemma lem1337735 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term57 x1 y1) = (term58 x1 y1).
Proof. exact (fun_ext (fun u : prod hreal hreal => @lem1337734 x1 y1 u)). Qed.
Lemma lem1337736 : mk_real = mk_real.
Proof. exact (eq_refl mk_real). Qed.
Lemma lem1337737 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term22 x1 y1) = (term59 x1 y1).
Proof. exact (MK_COMB (@lem1337736) (@lem1337735 x1 y1)). Qed.
Lemma lem1337738 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term10 x1 y1) = (term59 x1 y1).
Proof. exact (TRANS (@lem1337672 x1 y1) (@lem1337737 x1 y1)). Qed.
Lemma lem1337739 (t : type1233) : (term60 t) = t.
Proof. exact (@lem9127 (prod hreal hreal) Prop t). Qed.
Lemma lem1337742 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term58 x1 y1) = (term61 x1 y1).
Proof. exact (@lem1337739 (term61 x1 y1)). Qed.
Lemma lem1337743 : mk_real = mk_real.
Proof. exact (eq_refl mk_real). Qed.
Lemma lem1337744 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term59 x1 y1) = (term62 x1 y1).
Proof. exact (MK_COMB (@lem1337743) (@lem1337742 x1 y1)). Qed.
Lemma lem1337745 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term63 x1 y1) = (term63 x1 y1).
Proof. exact (eq_refl (term63 x1 y1)). Qed.
Lemma lem1337746 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : ((term10 x1 y1) = (term59 x1 y1)) = ((term10 x1 y1) = (term62 x1 y1)).
Proof. exact (MK_COMB (@lem1337745 x1 y1) (@lem1337744 x1 y1)). Qed.
Lemma lem1337747 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term10 x1 y1) = (term62 x1 y1).
Proof. exact (EQ_MP (@lem1337746 x1 y1) (@lem1337738 x1 y1)). Qed.
