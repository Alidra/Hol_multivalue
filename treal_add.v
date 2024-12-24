Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import treal_add_term_abbrevs.
Require Import FST_spec.
Require Import SND_spec.
Lemma lem1323702 : treal_add = term0.
Proof. exact (@treal_add_def). Qed.
Lemma lem1323703 (_23608 : prod hreal hreal) : _23608 = _23608.
Proof. exact (eq_refl _23608). Qed.
Lemma lem1323704 (_23608 : prod hreal hreal) : (treal_add _23608) = (term1 _23608).
Proof. exact (MK_COMB (@lem1323702) (@lem1323703 _23608)). Qed.
Lemma lem1323705 (_23608 : prod hreal hreal) : (term1 _23608) = (term2 _23608).
Proof. exact (eq_refl (term1 _23608)). Qed.
Lemma lem1323706 (_23608 : prod hreal hreal) : (treal_add _23608) = (term2 _23608).
Proof. exact (TRANS (@lem1323704 _23608) (@lem1323705 _23608)). Qed.
Lemma lem1323707 (_23609 : prod hreal hreal) : _23609 = _23609.
Proof. exact (eq_refl _23609). Qed.
Lemma lem1323708 (_23608 : prod hreal hreal) (_23609 : prod hreal hreal) : (treal_add _23608 _23609) = (term3 _23608 _23609).
Proof. exact (MK_COMB (@lem1323706 _23608) (@lem1323707 _23609)). Qed.
Lemma lem1323709 (_23608 : prod hreal hreal) (_23609 : prod hreal hreal) : (term3 _23608 _23609) = (term4 _23608 _23609).
Proof. exact (eq_refl (term3 _23608 _23609)). Qed.
Lemma lem1323710 (_23608 : prod hreal hreal) (_23609 : prod hreal hreal) : (treal_add _23608 _23609) = (term4 _23608 _23609).
Proof. exact (TRANS (@lem1323708 _23608 _23609) (@lem1323709 _23608 _23609)). Qed.
Lemma lem1323711 (_23608 : prod hreal hreal) : term5 _23608.
Proof. exact (fun _23609 : prod hreal hreal => @lem1323710 _23608 _23609). Qed.
Lemma lem1323712 : term6.
Proof. exact (fun _23608 : prod hreal hreal => @lem1323711 _23608). Qed.
Lemma lem1323713 (_23608 : prod hreal hreal) : term7 _23608.
Proof. exact (@lem1323712 _23608). Qed.
Lemma lem1323714 (_23608 : prod hreal hreal) : (term7 _23608) = (term5 _23608).
Proof. exact (eq_refl (term7 _23608)). Qed.
Lemma lem1323715 (_23608 : prod hreal hreal) : term5 _23608.
Proof. exact (EQ_MP (@lem1323714 _23608) (@lem1323713 _23608)). Qed.
Lemma lem1323716 (_23608 : prod hreal hreal) (_23609 : prod hreal hreal) : term8 _23608 _23609.
Proof. exact (@lem1323715 _23608 _23609). Qed.
Lemma lem1323717 (_23608 : prod hreal hreal) (_23609 : prod hreal hreal) : (term8 _23608 _23609) = ((treal_add _23608 _23609) = (term4 _23608 _23609)).
Proof. exact (eq_refl (term8 _23608 _23609)). Qed.
Lemma lem1323718 (_23608 : prod hreal hreal) (_23609 : prod hreal hreal) : (treal_add _23608 _23609) = (term4 _23608 _23609).
Proof. exact (EQ_MP (@lem1323717 _23608 _23609) (@lem1323716 _23608 _23609)). Qed.
Lemma lem1323719 (x1 : hreal) (y1 : hreal) (x2 : hreal) (y2 : hreal) : (term9 x1 y1 x2 y2) = (term10 x1 y1 x2 y2).
Proof. exact (@lem1323718 (@pair hreal hreal x1 y1) (@pair hreal hreal x2 y2)). Qed.
Lemma lem1323720 {A B : Type'} (x : A) : term11 A B x.
Proof. exact (@lem48019 A B x). Qed.
Lemma lem1323721 {A B : Type'} (x : A) : (term11 A B x) = (term12 A B x).
Proof. exact (eq_refl (term11 A B x)). Qed.
Lemma lem1323722 {A B : Type'} (x : A) : term12 A B x.
Proof. exact (EQ_MP (@lem1323721 A B x) (@lem1323720 A B x)). Qed.
Lemma lem1323723 {A B : Type'} (x : A) (y : B) : term13 A B x y.
Proof. exact (@lem1323722 A B x y). Qed.
Lemma lem1323724 {A B : Type'} (x : A) (y : B) : (term13 A B x y) = ((term14 A B x y) = y).
Proof. exact (eq_refl (term13 A B x y)). Qed.
Lemma lem1323726 {A B : Type'} (x : A) : term15 A B x.
Proof. exact (@lem47827 A B x). Qed.
Lemma lem1323727 {A B : Type'} (x : A) : (term15 A B x) = (term16 A B x).
Proof. exact (eq_refl (term15 A B x)). Qed.
Lemma lem1323728 {A B : Type'} (x : A) : term16 A B x.
Proof. exact (EQ_MP (@lem1323727 A B x) (@lem1323726 A B x)). Qed.
Lemma lem1323729 {A B : Type'} (x : A) (y : B) : term17 A B x y.
Proof. exact (@lem1323728 A B x y). Qed.
Lemma lem1323730 {A B : Type'} (y : B) (x : A) : (term17 A B x y) = ((term18 A B x y) = x).
Proof. exact (eq_refl (term17 A B x y)). Qed.
Lemma lem1323733 {A B : Type'} (y : B) (x : A) : (term18 A B x y) = x.
Proof. exact (EQ_MP (@lem1323730 A B y x) (@lem1323729 A B x y)). Qed.
Lemma lem1323734 (y : hreal) (x : hreal) : (term19 x y) = x.
Proof. exact (@lem1323733 hreal hreal y x). Qed.
Lemma lem1323735 (y1 : hreal) (x1 : hreal) : (term19 x1 y1) = x1.
Proof. exact (@lem1323734 y1 x1). Qed.
Lemma lem1323736 (x1 : hreal) (y1 : hreal) : x1 = (term19 x1 y1).
Proof. exact (SYM (@lem1323735 y1 x1)). Qed.
Lemma lem1323738 {A B : Type'} (x : A) (y : B) : (term14 A B x y) = y.
Proof. exact (EQ_MP (@lem1323724 A B x y) (@lem1323723 A B x y)). Qed.
Lemma lem1323739 (x : hreal) (y : hreal) : (term20 x y) = y.
Proof. exact (@lem1323738 hreal hreal x y). Qed.
Lemma lem1323740 (x1 : hreal) (y1 : hreal) : (term20 x1 y1) = y1.
Proof. exact (@lem1323739 x1 y1). Qed.
Lemma lem1323741 (x1 : hreal) (y1 : hreal) : y1 = (term20 x1 y1).
Proof. exact (SYM (@lem1323740 x1 y1)). Qed.
Lemma lem1323743 {A B : Type'} (y : B) (x : A) : (term18 A B x y) = x.
Proof. exact (EQ_MP (@lem1323730 A B y x) (@lem1323729 A B x y)). Qed.
Lemma lem1323744 (y : hreal) (x : hreal) : (term19 x y) = x.
Proof. exact (@lem1323743 hreal hreal y x). Qed.
Lemma lem1323745 (y2 : hreal) (x2 : hreal) : (term19 x2 y2) = x2.
Proof. exact (@lem1323744 y2 x2). Qed.
Lemma lem1323746 (x2 : hreal) (y2 : hreal) : x2 = (term19 x2 y2).
Proof. exact (SYM (@lem1323745 y2 x2)). Qed.
Lemma lem1323748 {A B : Type'} (x : A) (y : B) : (term14 A B x y) = y.
Proof. exact (EQ_MP (@lem1323724 A B x y) (@lem1323723 A B x y)). Qed.
Lemma lem1323749 (x : hreal) (y : hreal) : (term20 x y) = y.
Proof. exact (@lem1323748 hreal hreal x y). Qed.
Lemma lem1323750 (x2 : hreal) (y2 : hreal) : (term20 x2 y2) = y2.
Proof. exact (@lem1323749 x2 y2). Qed.
Lemma lem1323751 (x2 : hreal) (y2 : hreal) : y2 = (term20 x2 y2).
Proof. exact (SYM (@lem1323750 x2 y2)). Qed.
Lemma lem1323752 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem1323753 (x1 : hreal) (y1 : hreal) : (term22 x1) = (term23 x1 y1).
Proof. exact (MK_COMB (@lem1323752) (@lem1323736 x1 y1)). Qed.
Lemma lem1323754 (x1 : hreal) (y1 : hreal) : (term23 x1 y1) = (term24 x1 y1).
Proof. exact (eq_refl (term23 x1 y1)). Qed.
Lemma lem1323755 (x1 : hreal) : (term25 x1) = (term25 x1).
Proof. exact (eq_refl (term25 x1)). Qed.
Lemma lem1323756 (x1 : hreal) (y1 : hreal) : ((term22 x1) = (term23 x1 y1)) = ((term22 x1) = (term24 x1 y1)).
Proof. exact (MK_COMB (@lem1323755 x1) (@lem1323754 x1 y1)). Qed.
Lemma lem1323757 (x1 : hreal) : (term22 x1) = (term26 x1).
Proof. exact (eq_refl (term22 x1)). Qed.
Lemma lem1323758 : (@eq (hreal -> hreal -> hreal -> prod hreal hreal)) = (@eq (hreal -> hreal -> hreal -> prod hreal hreal)).
Proof. exact (eq_refl (@eq (hreal -> hreal -> hreal -> prod hreal hreal))). Qed.
Lemma lem1323759 (x1 : hreal) : (term25 x1) = (term27 x1).
Proof. exact (MK_COMB (@lem1323758) (@lem1323757 x1)). Qed.
Lemma lem1323760 (x1 : hreal) (y1 : hreal) : (term24 x1 y1) = (term24 x1 y1).
Proof. exact (eq_refl (term24 x1 y1)). Qed.
Lemma lem1323761 (x1 : hreal) (y1 : hreal) : ((term22 x1) = (term24 x1 y1)) = ((term26 x1) = (term24 x1 y1)).
Proof. exact (MK_COMB (@lem1323759 x1) (@lem1323760 x1 y1)). Qed.
Lemma lem1323762 (x1 : hreal) (y1 : hreal) : ((term22 x1) = (term23 x1 y1)) = ((term26 x1) = (term24 x1 y1)).
Proof. exact (TRANS (@lem1323756 x1 y1) (@lem1323761 x1 y1)). Qed.
Lemma lem1323763 (x1 : hreal) (y1 : hreal) : (term26 x1) = (term24 x1 y1).
Proof. exact (EQ_MP (@lem1323762 x1 y1) (@lem1323753 x1 y1)). Qed.
Lemma lem1323764 (x1 : hreal) (y1 : hreal) : (term28 x1 y1) = (term29 x1 y1).
Proof. exact (MK_COMB (@lem1323763 x1 y1) (@lem1323741 x1 y1)). Qed.
Lemma lem1323765 (x1 : hreal) (y1 : hreal) : (term29 x1 y1) = (term30 x1 y1).
Proof. exact (eq_refl (term29 x1 y1)). Qed.
Lemma lem1323766 (x1 : hreal) (y1 : hreal) : (term31 x1 y1) = (term31 x1 y1).
Proof. exact (eq_refl (term31 x1 y1)). Qed.
Lemma lem1323767 (x1 : hreal) (y1 : hreal) : ((term28 x1 y1) = (term29 x1 y1)) = ((term28 x1 y1) = (term30 x1 y1)).
Proof. exact (MK_COMB (@lem1323766 x1 y1) (@lem1323765 x1 y1)). Qed.
Lemma lem1323768 (x1 : hreal) (y1 : hreal) : (term28 x1 y1) = (term32 x1 y1).
Proof. exact (eq_refl (term28 x1 y1)). Qed.
Lemma lem1323769 : (@eq (hreal -> hreal -> prod hreal hreal)) = (@eq (hreal -> hreal -> prod hreal hreal)).
Proof. exact (eq_refl (@eq (hreal -> hreal -> prod hreal hreal))). Qed.
Lemma lem1323770 (x1 : hreal) (y1 : hreal) : (term31 x1 y1) = (term33 x1 y1).
Proof. exact (MK_COMB (@lem1323769) (@lem1323768 x1 y1)). Qed.
Lemma lem1323771 (x1 : hreal) (y1 : hreal) : (term30 x1 y1) = (term30 x1 y1).
Proof. exact (eq_refl (term30 x1 y1)). Qed.
Lemma lem1323772 (x1 : hreal) (y1 : hreal) : ((term28 x1 y1) = (term30 x1 y1)) = ((term32 x1 y1) = (term30 x1 y1)).
Proof. exact (MK_COMB (@lem1323770 x1 y1) (@lem1323771 x1 y1)). Qed.
Lemma lem1323773 (x1 : hreal) (y1 : hreal) : ((term28 x1 y1) = (term29 x1 y1)) = ((term32 x1 y1) = (term30 x1 y1)).
Proof. exact (TRANS (@lem1323767 x1 y1) (@lem1323772 x1 y1)). Qed.
Lemma lem1323774 (x1 : hreal) (y1 : hreal) : (term32 x1 y1) = (term30 x1 y1).
Proof. exact (EQ_MP (@lem1323773 x1 y1) (@lem1323764 x1 y1)). Qed.
Lemma lem1323775 (x1 : hreal) (y1 : hreal) (x2 : hreal) (y2 : hreal) : (term34 x1 y1 x2) = (term35 x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem1323774 x1 y1) (@lem1323746 x2 y2)). Qed.
Lemma lem1323776 (x2 : hreal) (y2 : hreal) (x1 : hreal) (y1 : hreal) : (term35 x1 y1 x2 y2) = (term36 x2 y2 x1 y1).
Proof. exact (eq_refl (term35 x1 y1 x2 y2)). Qed.
Lemma lem1323777 (x1 : hreal) (y1 : hreal) (x2 : hreal) : (term37 x1 y1 x2) = (term37 x1 y1 x2).
Proof. exact (eq_refl (term37 x1 y1 x2)). Qed.
Lemma lem1323778 (x2 : hreal) (y2 : hreal) (x1 : hreal) (y1 : hreal) : ((term34 x1 y1 x2) = (term35 x1 y1 x2 y2)) = ((term34 x1 y1 x2) = (term36 x2 y2 x1 y1)).
Proof. exact (MK_COMB (@lem1323777 x1 y1 x2) (@lem1323776 x2 y2 x1 y1)). Qed.
Lemma lem1323779 (x1 : hreal) (x2 : hreal) (y1 : hreal) : (term34 x1 y1 x2) = (term38 x1 x2 y1).
Proof. exact (eq_refl (term34 x1 y1 x2)). Qed.
Lemma lem1323780 : (@eq (hreal -> prod hreal hreal)) = (@eq (hreal -> prod hreal hreal)).
Proof. exact (eq_refl (@eq (hreal -> prod hreal hreal))). Qed.
Lemma lem1323781 (x1 : hreal) (x2 : hreal) (y1 : hreal) : (term37 x1 y1 x2) = (term39 x1 x2 y1).
Proof. exact (MK_COMB (@lem1323780) (@lem1323779 x1 x2 y1)). Qed.
Lemma lem1323782 (x2 : hreal) (y2 : hreal) (x1 : hreal) (y1 : hreal) : (term36 x2 y2 x1 y1) = (term36 x2 y2 x1 y1).
Proof. exact (eq_refl (term36 x2 y2 x1 y1)). Qed.
Lemma lem1323783 (x2 : hreal) (y2 : hreal) (x1 : hreal) (y1 : hreal) : ((term34 x1 y1 x2) = (term36 x2 y2 x1 y1)) = ((term38 x1 x2 y1) = (term36 x2 y2 x1 y1)).
Proof. exact (MK_COMB (@lem1323781 x1 x2 y1) (@lem1323782 x2 y2 x1 y1)). Qed.
Lemma lem1323784 (x2 : hreal) (y2 : hreal) (x1 : hreal) (y1 : hreal) : ((term34 x1 y1 x2) = (term35 x1 y1 x2 y2)) = ((term38 x1 x2 y1) = (term36 x2 y2 x1 y1)).
Proof. exact (TRANS (@lem1323778 x2 y2 x1 y1) (@lem1323783 x2 y2 x1 y1)). Qed.
Lemma lem1323785 (x2 : hreal) (y2 : hreal) (x1 : hreal) (y1 : hreal) : (term38 x1 x2 y1) = (term36 x2 y2 x1 y1).
Proof. exact (EQ_MP (@lem1323784 x2 y2 x1 y1) (@lem1323775 x1 y1 x2 y2)). Qed.
Lemma lem1323786 (x1 : hreal) (y1 : hreal) (x2 : hreal) (y2 : hreal) : (term40 x1 x2 y1 y2) = (term41 x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem1323785 x2 y2 x1 y1) (@lem1323751 x2 y2)). Qed.
Lemma lem1323787 (x1 : hreal) (y1 : hreal) (x2 : hreal) (y2 : hreal) : (term41 x1 y1 x2 y2) = (term10 x1 y1 x2 y2).
Proof. exact (eq_refl (term41 x1 y1 x2 y2)). Qed.
Lemma lem1323788 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) : (term42 x1 x2 y1 y2) = (term42 x1 x2 y1 y2).
Proof. exact (eq_refl (term42 x1 x2 y1 y2)). Qed.
Lemma lem1323789 (x1 : hreal) (y1 : hreal) (x2 : hreal) (y2 : hreal) : ((term40 x1 x2 y1 y2) = (term41 x1 y1 x2 y2)) = ((term40 x1 x2 y1 y2) = (term10 x1 y1 x2 y2)).
Proof. exact (MK_COMB (@lem1323788 x1 x2 y1 y2) (@lem1323787 x1 y1 x2 y2)). Qed.
Lemma lem1323790 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) : (term40 x1 x2 y1 y2) = (term43 x1 x2 y1 y2).
Proof. exact (eq_refl (term40 x1 x2 y1 y2)). Qed.
Lemma lem1323791 : (@eq (prod hreal hreal)) = (@eq (prod hreal hreal)).
Proof. exact (eq_refl (@eq (prod hreal hreal))). Qed.
Lemma lem1323792 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) : (term42 x1 x2 y1 y2) = (term44 x1 x2 y1 y2).
Proof. exact (MK_COMB (@lem1323791) (@lem1323790 x1 x2 y1 y2)). Qed.
Lemma lem1323793 (x1 : hreal) (y1 : hreal) (x2 : hreal) (y2 : hreal) : (term10 x1 y1 x2 y2) = (term10 x1 y1 x2 y2).
Proof. exact (eq_refl (term10 x1 y1 x2 y2)). Qed.
Lemma lem1323794 (x1 : hreal) (y1 : hreal) (x2 : hreal) (y2 : hreal) : ((term40 x1 x2 y1 y2) = (term10 x1 y1 x2 y2)) = ((term43 x1 x2 y1 y2) = (term10 x1 y1 x2 y2)).
Proof. exact (MK_COMB (@lem1323792 x1 x2 y1 y2) (@lem1323793 x1 y1 x2 y2)). Qed.
Lemma lem1323795 (x1 : hreal) (y1 : hreal) (x2 : hreal) (y2 : hreal) : ((term40 x1 x2 y1 y2) = (term41 x1 y1 x2 y2)) = ((term43 x1 x2 y1 y2) = (term10 x1 y1 x2 y2)).
Proof. exact (TRANS (@lem1323789 x1 y1 x2 y2) (@lem1323794 x1 y1 x2 y2)). Qed.
Lemma lem1323796 (x1 : hreal) (y1 : hreal) (x2 : hreal) (y2 : hreal) : (term43 x1 x2 y1 y2) = (term10 x1 y1 x2 y2).
Proof. exact (EQ_MP (@lem1323795 x1 y1 x2 y2) (@lem1323786 x1 y1 x2 y2)). Qed.
Lemma lem1323797 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) : (term10 x1 y1 x2 y2) = (term43 x1 x2 y1 y2).
Proof. exact (SYM (@lem1323796 x1 y1 x2 y2)). Qed.
Lemma lem1323798 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) : (term9 x1 y1 x2 y2) = (term43 x1 x2 y1 y2).
Proof. exact (TRANS (@lem1323719 x1 y1 x2 y2) (@lem1323797 x1 x2 y1 y2)). Qed.
Lemma lem1323799 (x1 : hreal) (x2 : hreal) (y1 : hreal) : term45 x1 x2 y1.
Proof. exact (fun y2 : hreal => @lem1323798 x1 x2 y1 y2). Qed.
Lemma lem1323800 (x1 : hreal) (x2 : hreal) : term46 x1 x2.
Proof. exact (fun y1 : hreal => @lem1323799 x1 x2 y1). Qed.
Lemma lem1323801 (x1 : hreal) : term47 x1.
Proof. exact (fun x2 : hreal => @lem1323800 x1 x2). Qed.
Lemma lem1323802 : term48.
Proof. exact (fun x1 : hreal => @lem1323801 x1). Qed.
