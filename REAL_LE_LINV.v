Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_LINV_term_abbrevs.
Require Import REAL_INV_INV_spec.
Require Import REAL_LE_INV2_spec.
Require Import REAL_LT_INV_spec.
Require Import thm0_spec.
Require Import thm1820_spec.
Require Import thm1823_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Lemma lem1632665 (y : real) : term0 y.
Proof. exact (@lem1632440 (real_inv y)). Qed.
Lemma lem1632666 (y : real) : (term0 y) = (term1 y).
Proof. exact (eq_refl (term0 y)). Qed.
Lemma lem1632667 (y : real) : term1 y.
Proof. exact (EQ_MP (@lem1632666 y) (@lem1632665 y)). Qed.
Lemma lem1632668 (y : real) (x : real) : term2 y x.
Proof. exact (@lem1632667 y x). Qed.
Lemma lem1632669 (x : real) (y : real) : (term2 y x) = (term3 x y).
Proof. exact (eq_refl (term2 y x)). Qed.
Lemma lem1632670 (x : real) (y : real) : term3 x y.
Proof. exact (EQ_MP (@lem1632669 x y) (@lem1632668 y x)). Qed.
Lemma lem1632671 (y : real) : term4 y.
Proof. exact (@lem1589984 y). Qed.
Lemma lem1632672 (y : real) : (term4 y) = (term5 y).
Proof. exact (eq_refl (term4 y)). Qed.
Lemma lem1632673 (y : real) : term5 y.
Proof. exact (EQ_MP (@lem1632672 y) (@lem1632671 y)). Qed.
Lemma lem1632674 (y : real) (x : real) (h1 : term6 y x) : term6 y x.
Proof. exact (h1). Qed.
Lemma lem1632675 (y : real) (x : real) (h1 : term7 y x) : term7 y x.
Proof. exact (h1). Qed.
Lemma lem1632676 (y : real) (h1 : term8 y) : term8 y.
Proof. exact (h1). Qed.
Lemma lem1632677 (y : real) : (term8 y) = ((term8 y) = True).
Proof. exact (@lem7 (term8 y)). Qed.
Lemma lem1632686 (y : real) (h1 : term8 y) : (term8 y) = True.
Proof. exact (EQ_MP (@lem1632677 y) (@lem1632676 y h1)). Qed.
Lemma lem1632687 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1632688 (y : real) (h1 : term8 y) : (term9 y) = (imp True).
Proof. exact (MK_COMB (@lem1632687) (@lem1632686 y h1)). Qed.
Lemma lem1632689 (y : real) : (term10 y) = (term10 y).
Proof. exact (eq_refl (term10 y)). Qed.
Lemma lem1632690 (y : real) (h1 : term8 y) : (term5 y) = (term11 y).
Proof. exact (MK_COMB (@lem1632688 y h1) (@lem1632689 y)). Qed.
Lemma lem1632692 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1632693 (y : real) : (term11 y) = (term10 y).
Proof. exact (@lem1632692 (term10 y)). Qed.
Lemma lem1632694 (y : real) (h1 : term8 y) : (term5 y) = (term10 y).
Proof. exact (TRANS (@lem1632690 y h1) (@lem1632693 y)). Qed.
Lemma lem1632695 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1632696 (y : real) (h1 : term8 y) : (term12 y) = (term13 y).
Proof. exact (MK_COMB (@lem1632695) (@lem1632694 y h1)). Qed.
Lemma lem1632697 (x : real) (y : real) : (term7 x y) = (term7 x y).
Proof. exact (eq_refl (term7 x y)). Qed.
Lemma lem1632698 (x : real) (y : real) (h1 : term8 y) : (term14 x y) = (term15 x y).
Proof. exact (MK_COMB (@lem1632696 y h1) (@lem1632697 x y)). Qed.
Lemma lem1632701 (x : real) (y : real) (h1 : term8 y) : (term15 x y) = (term14 x y).
Proof. exact (SYM (@lem1632698 x y h1)). Qed.
Lemma lem1632702 (y : real) (h1 : term10 y) : term10 y.
Proof. exact (h1). Qed.
Lemma lem1632703 (x : real) : term16 x.
Proof. exact (@lem1587920 x). Qed.
Lemma lem1632704 (x : real) : (term16 x) = ((term17 x) = x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1632708 (y : real) (x : real) : (term7 y x) = ((term7 y x) = True).
Proof. exact (@lem7 (term7 y x)). Qed.
Lemma lem1632710 (y : real) : (term10 y) = ((term10 y) = True).
Proof. exact (@lem7 (term10 y)). Qed.
Lemma lem1632719 (y : real) (h1 : term10 y) : (term10 y) = True.
Proof. exact (EQ_MP (@lem1632710 y) (@lem1632702 y h1)). Qed.
Lemma lem1632720 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1632721 (y : real) (h1 : term10 y) : (term18 y) = (and True).
Proof. exact (MK_COMB (@lem1632720) (@lem1632719 y h1)). Qed.
Lemma lem1632723 (y : real) (x : real) (h1 : term7 y x) : (term7 y x) = True.
Proof. exact (EQ_MP (@lem1632708 y x) (@lem1632675 y x h1)). Qed.
Lemma lem1632724 (x : real) (y : real) (h1 : term7 y x) (h2 : term10 y) : (term19 y x) = (True /\ True).
Proof. exact (MK_COMB (@lem1632721 y h2) (@lem1632723 y x h1)). Qed.
Lemma lem1632726 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1632727 : (True /\ True) = True.
Proof. exact (@lem1632726 True). Qed.
Lemma lem1632728 (x : real) (y : real) (h1 : term7 y x) (h2 : term10 y) : (term19 y x) = True.
Proof. exact (TRANS (@lem1632724 x y h1 h2) (@lem1632727)). Qed.
Lemma lem1632729 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1632730 (x : real) (y : real) (h1 : term7 y x) (h2 : term10 y) : (term20 y x) = (imp True).
Proof. exact (MK_COMB (@lem1632729) (@lem1632728 x y h1 h2)). Qed.
Lemma lem1632732 (x : real) : (term17 x) = x.
Proof. exact (EQ_MP (@lem1632704 x) (@lem1632703 x)). Qed.
Lemma lem1632733 (y : real) : (term17 y) = y.
Proof. exact (@lem1632732 y). Qed.
Lemma lem1632734 (x : real) : (term21 x) = (term21 x).
Proof. exact (eq_refl (term21 x)). Qed.
Lemma lem1632735 (x : real) (y : real) : (term22 x y) = (term7 x y).
Proof. exact (MK_COMB (@lem1632734 x) (@lem1632733 y)). Qed.
Lemma lem1632736 (x : real) (y : real) (h1 : term7 y x) (h2 : term10 y) : (term3 x y) = (term23 x y).
Proof. exact (MK_COMB (@lem1632730 x y h1 h2) (@lem1632735 x y)). Qed.
Lemma lem1632738 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1632739 (x : real) (y : real) : (term23 x y) = (term7 x y).
Proof. exact (@lem1632738 (term7 x y)). Qed.
Lemma lem1632740 (x : real) (y : real) (h1 : term7 y x) (h2 : term10 y) : (term3 x y) = (term7 x y).
Proof. exact (TRANS (@lem1632736 x y h1 h2) (@lem1632739 x y)). Qed.
Lemma lem1632741 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1632742 (x : real) (y : real) (h1 : term7 y x) (h2 : term10 y) : (term24 x y) = (term25 x y).
Proof. exact (MK_COMB (@lem1632741) (@lem1632740 x y h1 h2)). Qed.
Lemma lem1632743 (x : real) (y : real) : (term7 x y) = (term7 x y).
Proof. exact (eq_refl (term7 x y)). Qed.
Lemma lem1632744 (x : real) (y : real) (h1 : term7 y x) (h2 : term10 y) : (term26 x y) = (term27 x y).
Proof. exact (MK_COMB (@lem1632742 x y h1 h2) (@lem1632743 x y)). Qed.
Lemma lem1632746 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem1632747 (x : real) (y : real) : (term27 x y) = True.
Proof. exact (@lem1632746 (term7 x y)). Qed.
Lemma lem1632748 (x : real) (y : real) (h1 : term7 y x) (h2 : term10 y) : (term26 x y) = True.
Proof. exact (TRANS (@lem1632744 x y h1 h2) (@lem1632747 x y)). Qed.
Lemma lem1632749 (x : real) (y : real) (h1 : term7 y x) (h2 : term10 y) : True = (term26 x y).
Proof. exact (SYM (@lem1632748 x y h1 h2)). Qed.
Lemma lem1632750 (x : real) (y : real) (h1 : term7 y x) (h2 : term10 y) : term26 x y.
Proof. exact (EQ_MP (@lem1632749 x y h1 h2) (@lem0)). Qed.
Lemma lem1632751 (x : real) (y : real) (h1 : term7 y x) (h2 : term10 y) : term7 x y.
Proof. exact (@lem1632750 x y h1 h2 (@lem1632670 x y)). Qed.
Lemma lem1632752 (y : real) (x : real) (h1 : term7 y x) : term15 x y.
Proof. exact (fun h0 : term10 y => @lem1632751 x y h1 h0). Qed.
Lemma lem1632753 (x : real) (y : real) (h1 : term7 y x) (h2 : term8 y) : term14 x y.
Proof. exact (EQ_MP (@lem1632701 x y h2) (@lem1632752 y x h1)). Qed.
Lemma lem1632754 (x : real) (y : real) (h1 : term7 y x) (h2 : term8 y) : term7 x y.
Proof. exact (@lem1632753 x y h1 h2 (@lem1632673 y)). Qed.
Lemma lem1632755 (y : real) (x : real) (h1 : term6 y x) : term7 y x.
Proof. exact (proj2 (@lem1632674 y x h1)). Qed.
Lemma lem1632756 (y : real) (x : real) (h1 : term6 y x) : term8 y.
Proof. exact (proj1 (@lem1632674 y x h1)). Qed.
Lemma lem1632757 (x : real) (y : real) (h1 : term7 y x) (h2 : term8 y) : (term7 y x) = (term7 x y).
Proof. exact (prop_ext (fun h3 : term7 y x => @lem1632754 x y h1 h2) (fun h3 : term7 x y => @lem1632675 y x h1)). Qed.
Lemma lem1632758 (x : real) (y : real) (h1 : term7 y x) (h2 : term8 y) : term7 x y.
Proof. exact (EQ_MP (@lem1632757 x y h1 h2) (@lem1632675 y x h1)). Qed.
Lemma lem1632759 (x : real) (y : real) (h1 : term7 y x) (h2 : term8 y) : (term8 y) = (term7 x y).
Proof. exact (prop_ext (fun h3 : term8 y => @lem1632758 x y h1 h2) (fun h3 : term7 x y => @lem1632676 y h2)). Qed.
Lemma lem1632760 (x : real) (y : real) (h1 : term7 y x) (h2 : term8 y) : term7 x y.
Proof. exact (EQ_MP (@lem1632759 x y h1 h2) (@lem1632676 y h2)). Qed.
Lemma lem1632761 (x : real) (y : real) (h1 : term6 y x) (h2 : term8 y) : (term7 y x) = (term7 x y).
Proof. exact (prop_ext (fun h3 : term7 y x => @lem1632760 x y h3 h2) (fun h3 : term7 x y => @lem1632755 y x h1)). Qed.
Lemma lem1632762 (x : real) (y : real) (h1 : term6 y x) (h2 : term8 y) : term7 x y.
Proof. exact (EQ_MP (@lem1632761 x y h1 h2) (@lem1632755 y x h1)). Qed.
Lemma lem1632763 (y : real) (x : real) (h1 : term6 y x) : (term8 y) = (term7 x y).
Proof. exact (prop_ext (fun h2 : term8 y => @lem1632762 x y h1 h2) (fun h2 : term7 x y => @lem1632756 y x h1)). Qed.
Lemma lem1632764 (y : real) (x : real) (h1 : term6 y x) : term7 x y.
Proof. exact (EQ_MP (@lem1632763 y x h1) (@lem1632756 y x h1)). Qed.
Lemma lem1632765 (x : real) (y : real) : term28 x y.
Proof. exact (fun h0 : term6 y x => @lem1632764 y x h0). Qed.
Lemma lem1632770 (x : real) : term29 x.
Proof. exact (fun y : real => @lem1632765 x y). Qed.
Lemma lem1632775 : term30.
Proof. exact (fun x : real => @lem1632770 x). Qed.
