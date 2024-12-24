Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_RINV_term_abbrevs.
Require Import REAL_INV_INV_spec.
Require Import REAL_LE_INV2_spec.
Require Import REAL_LT_INV_spec.
Require Import thm0_spec.
Require Import thm1820_spec.
Require Import thm1823_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Lemma lem1632776 (x : real) : term0 x.
Proof. exact (@lem1632440 x). Qed.
Lemma lem1632777 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1632778 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1632777 x) (@lem1632776 x)). Qed.
Lemma lem1632779 (x : real) (y : real) : term2 x y.
Proof. exact (@lem1632778 x (real_inv y)). Qed.
Lemma lem1632780 (y : real) (x : real) : (term2 x y) = (term3 y x).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1632781 (y : real) (x : real) : term3 y x.
Proof. exact (EQ_MP (@lem1632780 y x) (@lem1632779 x y)). Qed.
Lemma lem1632782 (x : real) : term4 x.
Proof. exact (@lem1589984 x). Qed.
Lemma lem1632783 (x : real) : (term4 x) = (term5 x).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem1632784 (x : real) : term5 x.
Proof. exact (EQ_MP (@lem1632783 x) (@lem1632782 x)). Qed.
Lemma lem1632785 (x : real) (y : real) (h1 : term6 x y) : term6 x y.
Proof. exact (h1). Qed.
Lemma lem1632786 (x : real) (y : real) (h1 : term7 x y) : term7 x y.
Proof. exact (h1). Qed.
Lemma lem1632787 (x : real) (h1 : term8 x) : term8 x.
Proof. exact (h1). Qed.
Lemma lem1632788 (x : real) : (term8 x) = ((term8 x) = True).
Proof. exact (@lem7 (term8 x)). Qed.
Lemma lem1632797 (x : real) (h1 : term8 x) : (term8 x) = True.
Proof. exact (EQ_MP (@lem1632788 x) (@lem1632787 x h1)). Qed.
Lemma lem1632798 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1632799 (x : real) (h1 : term8 x) : (term9 x) = (imp True).
Proof. exact (MK_COMB (@lem1632798) (@lem1632797 x h1)). Qed.
Lemma lem1632800 (x : real) : (term10 x) = (term10 x).
Proof. exact (eq_refl (term10 x)). Qed.
Lemma lem1632801 (x : real) (h1 : term8 x) : (term5 x) = (term11 x).
Proof. exact (MK_COMB (@lem1632799 x h1) (@lem1632800 x)). Qed.
Lemma lem1632803 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1632804 (x : real) : (term11 x) = (term10 x).
Proof. exact (@lem1632803 (term10 x)). Qed.
Lemma lem1632805 (x : real) (h1 : term8 x) : (term5 x) = (term10 x).
Proof. exact (TRANS (@lem1632801 x h1) (@lem1632804 x)). Qed.
Lemma lem1632806 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1632807 (x : real) (h1 : term8 x) : (term12 x) = (term13 x).
Proof. exact (MK_COMB (@lem1632806) (@lem1632805 x h1)). Qed.
Lemma lem1632808 (y : real) (x : real) : (term7 y x) = (term7 y x).
Proof. exact (eq_refl (term7 y x)). Qed.
Lemma lem1632809 (y : real) (x : real) (h1 : term8 x) : (term14 y x) = (term15 y x).
Proof. exact (MK_COMB (@lem1632807 x h1) (@lem1632808 y x)). Qed.
Lemma lem1632812 (y : real) (x : real) (h1 : term8 x) : (term15 y x) = (term14 y x).
Proof. exact (SYM (@lem1632809 y x h1)). Qed.
Lemma lem1632814 (x : real) : term16 x.
Proof. exact (@lem1587920 x). Qed.
Lemma lem1632815 (x : real) : (term16 x) = ((term17 x) = x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1632817 (x : real) : (term8 x) = ((term8 x) = True).
Proof. exact (@lem7 (term8 x)). Qed.
Lemma lem1632819 (x : real) (y : real) : (term7 x y) = ((term7 x y) = True).
Proof. exact (@lem7 (term7 x y)). Qed.
Lemma lem1632830 (x : real) (h1 : term8 x) : (term8 x) = True.
Proof. exact (EQ_MP (@lem1632817 x) (@lem1632787 x h1)). Qed.
Lemma lem1632831 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1632832 (x : real) (h1 : term8 x) : (term18 x) = (and True).
Proof. exact (MK_COMB (@lem1632831) (@lem1632830 x h1)). Qed.
Lemma lem1632834 (x : real) (y : real) (h1 : term7 x y) : (term7 x y) = True.
Proof. exact (EQ_MP (@lem1632819 x y) (@lem1632786 x y h1)). Qed.
Lemma lem1632835 (y : real) (x : real) (h1 : term7 x y) (h2 : term8 x) : (term6 x y) = (True /\ True).
Proof. exact (MK_COMB (@lem1632832 x h2) (@lem1632834 x y h1)). Qed.
Lemma lem1632837 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1632838 : (True /\ True) = True.
Proof. exact (@lem1632837 True). Qed.
Lemma lem1632839 (y : real) (x : real) (h1 : term7 x y) (h2 : term8 x) : (term6 x y) = True.
Proof. exact (TRANS (@lem1632835 y x h1 h2) (@lem1632838)). Qed.
Lemma lem1632840 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1632841 (y : real) (x : real) (h1 : term7 x y) (h2 : term8 x) : (term19 x y) = (imp True).
Proof. exact (MK_COMB (@lem1632840) (@lem1632839 y x h1 h2)). Qed.
Lemma lem1632843 (x : real) : (term17 x) = x.
Proof. exact (EQ_MP (@lem1632815 x) (@lem1632814 x)). Qed.
Lemma lem1632844 (y : real) : (term17 y) = y.
Proof. exact (@lem1632843 y). Qed.
Lemma lem1632845 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1632846 (y : real) : (term20 y) = (real_le y).
Proof. exact (MK_COMB (@lem1632845) (@lem1632844 y)). Qed.
Lemma lem1632847 (x : real) : (real_inv x) = (real_inv x).
Proof. exact (eq_refl (real_inv x)). Qed.
Lemma lem1632848 (y : real) (x : real) : (term21 y x) = (term7 y x).
Proof. exact (MK_COMB (@lem1632846 y) (@lem1632847 x)). Qed.
Lemma lem1632849 (y : real) (x : real) (h1 : term7 x y) (h2 : term8 x) : (term3 y x) = (term22 y x).
Proof. exact (MK_COMB (@lem1632841 y x h1 h2) (@lem1632848 y x)). Qed.
Lemma lem1632851 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1632852 (y : real) (x : real) : (term22 y x) = (term7 y x).
Proof. exact (@lem1632851 (term7 y x)). Qed.
Lemma lem1632853 (y : real) (x : real) (h1 : term7 x y) (h2 : term8 x) : (term3 y x) = (term7 y x).
Proof. exact (TRANS (@lem1632849 y x h1 h2) (@lem1632852 y x)). Qed.
Lemma lem1632854 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1632855 (y : real) (x : real) (h1 : term7 x y) (h2 : term8 x) : (term23 y x) = (term24 y x).
Proof. exact (MK_COMB (@lem1632854) (@lem1632853 y x h1 h2)). Qed.
Lemma lem1632856 (y : real) (x : real) : (term7 y x) = (term7 y x).
Proof. exact (eq_refl (term7 y x)). Qed.
Lemma lem1632857 (y : real) (x : real) (h1 : term7 x y) (h2 : term8 x) : (term25 y x) = (term26 y x).
Proof. exact (MK_COMB (@lem1632855 y x h1 h2) (@lem1632856 y x)). Qed.
Lemma lem1632859 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem1632860 (y : real) (x : real) : (term26 y x) = True.
Proof. exact (@lem1632859 (term7 y x)). Qed.
Lemma lem1632861 (y : real) (x : real) (h1 : term7 x y) (h2 : term8 x) : (term25 y x) = True.
Proof. exact (TRANS (@lem1632857 y x h1 h2) (@lem1632860 y x)). Qed.
Lemma lem1632862 (y : real) (x : real) (h1 : term7 x y) (h2 : term8 x) : True = (term25 y x).
Proof. exact (SYM (@lem1632861 y x h1 h2)). Qed.
Lemma lem1632863 (y : real) (x : real) (h1 : term7 x y) (h2 : term8 x) : term25 y x.
Proof. exact (EQ_MP (@lem1632862 y x h1 h2) (@lem0)). Qed.
Lemma lem1632864 (y : real) (x : real) (h1 : term7 x y) (h2 : term8 x) : term7 y x.
Proof. exact (@lem1632863 y x h1 h2 (@lem1632781 y x)). Qed.
Lemma lem1632865 (y : real) (x : real) (h1 : term7 x y) (h2 : term8 x) : term15 y x.
Proof. exact (fun h0 : term10 x => @lem1632864 y x h1 h2). Qed.
Lemma lem1632866 (y : real) (x : real) (h1 : term7 x y) (h2 : term8 x) : term14 y x.
Proof. exact (EQ_MP (@lem1632812 y x h2) (@lem1632865 y x h1 h2)). Qed.
Lemma lem1632867 (y : real) (x : real) (h1 : term7 x y) (h2 : term8 x) : term7 y x.
Proof. exact (@lem1632866 y x h1 h2 (@lem1632784 x)). Qed.
Lemma lem1632868 (x : real) (y : real) (h1 : term6 x y) : term7 x y.
Proof. exact (proj2 (@lem1632785 x y h1)). Qed.
Lemma lem1632869 (x : real) (y : real) (h1 : term6 x y) : term8 x.
Proof. exact (proj1 (@lem1632785 x y h1)). Qed.
Lemma lem1632870 (y : real) (x : real) (h1 : term7 x y) (h2 : term8 x) : (term7 x y) = (term7 y x).
Proof. exact (prop_ext (fun h3 : term7 x y => @lem1632867 y x h1 h2) (fun h3 : term7 y x => @lem1632786 x y h1)). Qed.
Lemma lem1632871 (y : real) (x : real) (h1 : term7 x y) (h2 : term8 x) : term7 y x.
Proof. exact (EQ_MP (@lem1632870 y x h1 h2) (@lem1632786 x y h1)). Qed.
Lemma lem1632872 (y : real) (x : real) (h1 : term7 x y) (h2 : term8 x) : (term8 x) = (term7 y x).
Proof. exact (prop_ext (fun h3 : term8 x => @lem1632871 y x h1 h2) (fun h3 : term7 y x => @lem1632787 x h2)). Qed.
Lemma lem1632873 (y : real) (x : real) (h1 : term7 x y) (h2 : term8 x) : term7 y x.
Proof. exact (EQ_MP (@lem1632872 y x h1 h2) (@lem1632787 x h2)). Qed.
Lemma lem1632874 (y : real) (x : real) (h1 : term6 x y) (h2 : term8 x) : (term7 x y) = (term7 y x).
Proof. exact (prop_ext (fun h3 : term7 x y => @lem1632873 y x h3 h2) (fun h3 : term7 y x => @lem1632868 x y h1)). Qed.
Lemma lem1632875 (y : real) (x : real) (h1 : term6 x y) (h2 : term8 x) : term7 y x.
Proof. exact (EQ_MP (@lem1632874 y x h1 h2) (@lem1632868 x y h1)). Qed.
Lemma lem1632876 (x : real) (y : real) (h1 : term6 x y) : (term8 x) = (term7 y x).
Proof. exact (prop_ext (fun h2 : term8 x => @lem1632875 y x h1 h2) (fun h2 : term7 y x => @lem1632869 x y h1)). Qed.
Lemma lem1632877 (x : real) (y : real) (h1 : term6 x y) : term7 y x.
Proof. exact (EQ_MP (@lem1632876 x y h1) (@lem1632869 x y h1)). Qed.
Lemma lem1632878 (y : real) (x : real) : term27 y x.
Proof. exact (fun h0 : term6 x y => @lem1632877 x y h0). Qed.
Lemma lem1632883 (x : real) : term28 x.
Proof. exact (fun y : real => @lem1632878 y x). Qed.
Lemma lem1632888 : term29.
Proof. exact (fun x : real => @lem1632883 x). Qed.
