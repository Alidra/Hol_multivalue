Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import TREAL_INV_0_term_abbrevs.
Require Import thm0_spec.
Require Import thm15249_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import treal_eq_spec.
Require Import treal_inv_spec.
Require Import treal_of_num_spec.
Lemma lem1331692 (n : nat) : term0 n.
Proof. exact (@lem1322742 n). Qed.
Lemma lem1331693 (n : nat) : (term0 n) = ((treal_of_num n) = (term1 n)).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem1331695 (x1 : hreal) : term2 x1.
Proof. exact (@lem1326116 x1). Qed.
Lemma lem1331696 (x1 : hreal) : (term2 x1) = (term3 x1).
Proof. exact (eq_refl (term2 x1)). Qed.
Lemma lem1331697 (x1 : hreal) : term3 x1.
Proof. exact (EQ_MP (@lem1331696 x1) (@lem1331695 x1)). Qed.
Lemma lem1331698 (x1 : hreal) (y2 : hreal) : term4 x1 y2.
Proof. exact (@lem1331697 x1 y2). Qed.
Lemma lem1331699 (x1 : hreal) (y2 : hreal) : (term4 x1 y2) = (term5 x1 y2).
Proof. exact (eq_refl (term4 x1 y2)). Qed.
Lemma lem1331700 (x1 : hreal) (y2 : hreal) : term5 x1 y2.
Proof. exact (EQ_MP (@lem1331699 x1 y2) (@lem1331698 x1 y2)). Qed.
Lemma lem1331701 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term6 x1 y2 x2.
Proof. exact (@lem1331700 x1 y2 x2). Qed.
Lemma lem1331702 (x1 : hreal) (y2 : hreal) (x2 : hreal) : (term6 x1 y2 x2) = (term7 x1 y2 x2).
Proof. exact (eq_refl (term6 x1 y2 x2)). Qed.
Lemma lem1331703 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term7 x1 y2 x2.
Proof. exact (EQ_MP (@lem1331702 x1 y2 x2) (@lem1331701 x1 y2 x2)). Qed.
Lemma lem1331704 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : term8 x1 y2 x2 y1.
Proof. exact (@lem1331703 x1 y2 x2 y1). Qed.
Lemma lem1331705 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term8 x1 y2 x2 y1) = ((term9 x1 y1 x2 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1))).
Proof. exact (eq_refl (term8 x1 y2 x2 y1)). Qed.
Lemma lem1331707 (y : hreal) : term10 y.
Proof. exact (@lem1325510 y). Qed.
Lemma lem1331708 (y : hreal) : (term10 y) = (term11 y).
Proof. exact (eq_refl (term10 y)). Qed.
Lemma lem1331709 (y : hreal) : term11 y.
Proof. exact (EQ_MP (@lem1331708 y) (@lem1331707 y)). Qed.
Lemma lem1331710 (y : hreal) (x : hreal) : term12 y x.
Proof. exact (@lem1331709 y x). Qed.
Lemma lem1331711 (y : hreal) (x : hreal) : (term12 y x) = ((term13 x y) = (term14 y x)).
Proof. exact (eq_refl (term12 y x)). Qed.
Lemma lem1331714 (n : nat) : (treal_of_num n) = (term1 n).
Proof. exact (EQ_MP (@lem1331693 n) (@lem1331692 n)). Qed.
Lemma lem1331715 : term15 = term16.
Proof. exact (@lem1331714 (NUMERAL 0)). Qed.
Lemma lem1331716 : treal_inv = treal_inv.
Proof. exact (eq_refl treal_inv). Qed.
Lemma lem1331717 : term17 = term18.
Proof. exact (MK_COMB (@lem1331716) (@lem1331715)). Qed.
Lemma lem1331719 (y : hreal) (x : hreal) : (term13 x y) = (term14 y x).
Proof. exact (EQ_MP (@lem1331711 y x) (@lem1331710 y x)). Qed.
Lemma lem1331720 : term18 = term19.
Proof. exact (@lem1331719 term20 term20). Qed.
Lemma lem1331722 {_2975 _2982 : Type'} (x : _2982) (z : _2975) (y : _2975) : (term21 _2975 _2982 x y z) = y.
Proof. exact (EQ_MP (@lem15249 _2975 _2982 x z y) (@lem0)). Qed.
Lemma lem1331723 (x : hreal) (z : prod hreal hreal) (y : prod hreal hreal) : (term22 x y z) = y.
Proof. exact (@lem1331722 (prod hreal hreal) hreal x z y). Qed.
Lemma lem1331724 : term19 = term16.
Proof. exact (@lem1331723 term20 term23 term16). Qed.
Lemma lem1331725 : term18 = term16.
Proof. exact (TRANS (@lem1331720) (@lem1331724)). Qed.
Lemma lem1331726 : term17 = term16.
Proof. exact (TRANS (@lem1331717) (@lem1331725)). Qed.
Lemma lem1331727 : treal_eq = treal_eq.
Proof. exact (eq_refl treal_eq). Qed.
Lemma lem1331728 : term24 = term25.
Proof. exact (MK_COMB (@lem1331727) (@lem1331726)). Qed.
Lemma lem1331730 (n : nat) : (treal_of_num n) = (term1 n).
Proof. exact (EQ_MP (@lem1331693 n) (@lem1331692 n)). Qed.
Lemma lem1331731 : term15 = term16.
Proof. exact (@lem1331730 (NUMERAL 0)). Qed.
Lemma lem1331732 : term26 = term27.
Proof. exact (MK_COMB (@lem1331728) (@lem1331731)). Qed.
Lemma lem1331734 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term9 x1 y1 x2 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1)).
Proof. exact (EQ_MP (@lem1331705 x1 y2 x2 y1) (@lem1331704 x1 y2 x2 y1)). Qed.
Lemma lem1331735 : term27 = (term28 = term28).
Proof. exact (@lem1331734 term20 term20 term20 term20). Qed.
Lemma lem1331737 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1331738 (x : hreal) : (x = x) = True.
Proof. exact (@lem1331737 hreal x). Qed.
Lemma lem1331739 : (term28 = term28) = True.
Proof. exact (@lem1331738 term28). Qed.
Lemma lem1331740 : term27 = True.
Proof. exact (TRANS (@lem1331735) (@lem1331739)). Qed.
Lemma lem1331741 : term26 = True.
Proof. exact (TRANS (@lem1331732) (@lem1331740)). Qed.
Lemma lem1331742 : True = term26.
Proof. exact (SYM (@lem1331741)). Qed.
Lemma lem1331743 : term26.
Proof. exact (EQ_MP (@lem1331742) (@lem0)). Qed.
