Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import one_term_abbrevs.
Require Import thm0_spec.
Require Import thm15721_spec.
Require Import thm15730_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1856_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Lemma lem15735 : term0.
Proof. exact (fun a : unit => @lem15721 a). Qed.
Lemma lem15737 (a : unit) (h1 : (term1 a) = a) : (term1 a) = a.
Proof. exact (h1). Qed.
Lemma lem15738 (a : unit) (h1 : (term1 a) = a) : a = (term1 a).
Proof. exact (SYM (@lem15737 a h1)). Qed.
Lemma lem15739 (a : unit) (h1 : a = (term1 a)) : a = (term1 a).
Proof. exact (h1). Qed.
Lemma lem15740 (a : unit) (h1 : a = (term1 a)) : (term1 a) = a.
Proof. exact (SYM (@lem15739 a h1)). Qed.
Lemma lem15741 (a : unit) : ((term1 a) = a) = (a = (term1 a)).
Proof. exact (prop_ext (fun h1 : (term1 a) = a => @lem15738 a h1) (fun h1 : a = (term1 a) => @lem15740 a h1)). Qed.
Lemma lem15742 : term2 = term3.
Proof. exact (fun_ext (fun a : unit => @lem15741 a)). Qed.
Lemma lem15743 : (@all unit) = (@all unit).
Proof. exact (eq_refl (@all unit)). Qed.
Lemma lem15744 : term0 = term4.
Proof. exact (MK_COMB (@lem15743) (@lem15742)). Qed.
Lemma lem15745 : term4.
Proof. exact (EQ_MP (@lem15744) (@lem15735)). Qed.
Lemma lem15746 (a : unit) : term5 a.
Proof. exact (@lem15745 a). Qed.
Lemma lem15747 (a : unit) : (term5 a) = (a = (term1 a)).
Proof. exact (eq_refl (term5 a)). Qed.
Lemma lem15749 : term0.
Proof. exact (fun a : unit => @lem15721 a). Qed.
Lemma lem15750 (a : unit) : term6 a.
Proof. exact (@lem15749 a). Qed.
Lemma lem15751 (a : unit) : (term6 a) = ((term1 a) = a).
Proof. exact (eq_refl (term6 a)). Qed.
Lemma lem15753 : term7.
Proof. exact (fun r : Prop => @lem15730 r). Qed.
Lemma lem15754 (a : unit) : term8 a.
Proof. exact (@lem15753 (one_REP a)). Qed.
Lemma lem15755 (a : unit) : (term8 a) = ((one_REP a) = ((term9 a) = (one_REP a))).
Proof. exact (eq_refl (term8 a)). Qed.
Lemma lem15756 (a : unit) : (one_REP a) = ((term9 a) = (one_REP a)).
Proof. exact (EQ_MP (@lem15755 a) (@lem15754 a)). Qed.
Lemma lem15757 : term10.
Proof. exact (fun a : unit => @lem15756 a). Qed.
Lemma lem15769 (a : unit) : (term1 a) = a.
Proof. exact (EQ_MP (@lem15751 a) (@lem15750 a)). Qed.
Lemma lem15770 : one_REP = one_REP.
Proof. exact (eq_refl one_REP). Qed.
Lemma lem15771 (a : unit) : (term9 a) = (one_REP a).
Proof. exact (MK_COMB (@lem15770) (@lem15769 a)). Qed.
Lemma lem15772 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem15773 (a : unit) : (term11 a) = (term12 a).
Proof. exact (MK_COMB (@lem15772) (@lem15771 a)). Qed.
Lemma lem15774 (a : unit) : (one_REP a) = (one_REP a).
Proof. exact (eq_refl (one_REP a)). Qed.
Lemma lem15775 (a : unit) : ((term9 a) = (one_REP a)) = ((one_REP a) = (one_REP a)).
Proof. exact (MK_COMB (@lem15773 a) (@lem15774 a)). Qed.
Lemma lem15777 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem15778 (x : Prop) : (x = x) = True.
Proof. exact (@lem15777 Prop x). Qed.
Lemma lem15779 (a : unit) : ((one_REP a) = (one_REP a)) = True.
Proof. exact (@lem15778 (one_REP a)). Qed.
Lemma lem15780 (a : unit) : ((term9 a) = (one_REP a)) = True.
Proof. exact (TRANS (@lem15775 a) (@lem15779 a)). Qed.
Lemma lem15781 (a : unit) : (term12 a) = (term12 a).
Proof. exact (eq_refl (term12 a)). Qed.
Lemma lem15782 (a : unit) : ((one_REP a) = ((term9 a) = (one_REP a))) = ((one_REP a) = True).
Proof. exact (MK_COMB (@lem15781 a) (@lem15780 a)). Qed.
Lemma lem15784 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem15785 (a : unit) : ((one_REP a) = True) = (one_REP a).
Proof. exact (@lem15784 (one_REP a)). Qed.
Lemma lem15786 (a : unit) : ((one_REP a) = ((term9 a) = (one_REP a))) = (one_REP a).
Proof. exact (TRANS (@lem15782 a) (@lem15785 a)). Qed.
Lemma lem15787 : term13 = term14.
Proof. exact (fun_ext (fun a : unit => @lem15786 a)). Qed.
Lemma lem15788 : (@all unit) = (@all unit).
Proof. exact (eq_refl (@all unit)). Qed.
Lemma lem15789 : term10 = term15.
Proof. exact (MK_COMB (@lem15788) (@lem15787)). Qed.
Lemma lem15794 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem15795 : term16 = term17.
Proof. exact (MK_COMB (@lem15794) (@lem15789)). Qed.
Lemma lem15802 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem15803 : term19 = term20.
Proof. exact (MK_COMB (@lem15795) (@lem15802)). Qed.
Lemma lem15806 : term20 = term19.
Proof. exact (SYM (@lem15803)). Qed.
Lemma lem15807 (h1 : term15) : term15.
Proof. exact (h1). Qed.
Lemma lem15827 (a : unit) : a = (term1 a).
Proof. exact (EQ_MP (@lem15747 a) (@lem15746 a)). Qed.
Lemma lem15828 (v : unit) : v = (term1 v).
Proof. exact (@lem15827 v). Qed.
Lemma lem15829 : (@eq unit) = (@eq unit).
Proof. exact (eq_refl (@eq unit)). Qed.
Lemma lem15830 (v : unit) : (@eq unit v) = (term21 v).
Proof. exact (MK_COMB (@lem15829) (@lem15828 v)). Qed.
Lemma lem15832 (a : unit) : a = (term1 a).
Proof. exact (EQ_MP (@lem15747 a) (@lem15746 a)). Qed.
Lemma lem15833 : tt = term22.
Proof. exact (@lem15832 tt). Qed.
Lemma lem15834 (v : unit) : (v = tt) = ((term1 v) = term22).
Proof. exact (MK_COMB (@lem15830 v) (@lem15833)). Qed.
Lemma lem15835 : term23 = term24.
Proof. exact (fun_ext (fun v : unit => @lem15834 v)). Qed.
Lemma lem15836 : (@all unit) = (@all unit).
Proof. exact (eq_refl (@all unit)). Qed.
Lemma lem15837 : term18 = term25.
Proof. exact (MK_COMB (@lem15836) (@lem15835)). Qed.
Lemma lem15838 : term25 = term18.
Proof. exact (SYM (@lem15837)). Qed.
Lemma lem15839 (a : unit) (h1 : term15) : term26 a.
Proof. exact (@lem15807 h1 a). Qed.
Lemma lem15840 (a : unit) : (term26 a) = (one_REP a).
Proof. exact (eq_refl (term26 a)). Qed.
Lemma lem15841 (a : unit) (h1 : term15) : one_REP a.
Proof. exact (EQ_MP (@lem15840 a) (@lem15839 a h1)). Qed.
Lemma lem15842 (a : unit) : (one_REP a) = ((one_REP a) = True).
Proof. exact (@lem7 (one_REP a)). Qed.
Lemma lem15851 (a : unit) (h1 : term15) : (one_REP a) = True.
Proof. exact (EQ_MP (@lem15842 a) (@lem15841 a h1)). Qed.
Lemma lem15852 (v : unit) (h1 : term15) : (one_REP v) = True.
Proof. exact (@lem15851 v h1). Qed.
Lemma lem15853 : one_ABS = one_ABS.
Proof. exact (eq_refl one_ABS). Qed.
Lemma lem15854 (v : unit) (h1 : term15) : (term1 v) = (one_ABS True).
Proof. exact (MK_COMB (@lem15853) (@lem15852 v h1)). Qed.
Lemma lem15855 : (@eq unit) = (@eq unit).
Proof. exact (eq_refl (@eq unit)). Qed.
Lemma lem15856 (v : unit) (h1 : term15) : (term21 v) = term27.
Proof. exact (MK_COMB (@lem15855) (@lem15854 v h1)). Qed.
Lemma lem15858 (a : unit) (h1 : term15) : (one_REP a) = True.
Proof. exact (EQ_MP (@lem15842 a) (@lem15841 a h1)). Qed.
Lemma lem15859 (h1 : term15) : (one_REP tt) = True.
Proof. exact (@lem15858 tt h1). Qed.
Lemma lem15860 : one_ABS = one_ABS.
Proof. exact (eq_refl one_ABS). Qed.
Lemma lem15861 (h1 : term15) : term22 = (one_ABS True).
Proof. exact (MK_COMB (@lem15860) (@lem15859 h1)). Qed.
Lemma lem15862 (v : unit) (h1 : term15) : ((term1 v) = term22) = ((one_ABS True) = (one_ABS True)).
Proof. exact (MK_COMB (@lem15856 v h1) (@lem15861 h1)). Qed.
Lemma lem15864 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem15865 (x : unit) : (x = x) = True.
Proof. exact (@lem15864 unit x). Qed.
Lemma lem15866 : ((one_ABS True) = (one_ABS True)) = True.
Proof. exact (@lem15865 (one_ABS True)). Qed.
Lemma lem15867 (v : unit) (h1 : term15) : ((term1 v) = term22) = True.
Proof. exact (TRANS (@lem15862 v h1) (@lem15866)). Qed.
Lemma lem15868 (h1 : term15) : term24 = term28.
Proof. exact (fun_ext (fun v : unit => @lem15867 v h1)). Qed.
Lemma lem15869 : (@all unit) = (@all unit).
Proof. exact (eq_refl (@all unit)). Qed.
Lemma lem15870 (h1 : term15) : term25 = term29.
Proof. exact (MK_COMB (@lem15869) (@lem15868 h1)). Qed.
Lemma lem15872 {A : Type'} (t : Prop) : (term30 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem15873 (t : Prop) : (term31 t) = t.
Proof. exact (@lem15872 unit t). Qed.
Lemma lem15874 : term29 = True.
Proof. exact (@lem15873 True). Qed.
Lemma lem15875 (h1 : term15) : term25 = True.
Proof. exact (TRANS (@lem15870 h1) (@lem15874)). Qed.
Lemma lem15876 (h1 : term15) : True = term25.
Proof. exact (SYM (@lem15875 h1)). Qed.
Lemma lem15877 (h1 : term15) : term25.
Proof. exact (EQ_MP (@lem15876 h1) (@lem0)). Qed.
Lemma lem15878 (h1 : term15) : term18.
Proof. exact (EQ_MP (@lem15838) (@lem15877 h1)). Qed.
Lemma lem15879 : term20.
Proof. exact (fun h0 : term15 => @lem15878 h0). Qed.
Lemma lem15880 : term19.
Proof. exact (EQ_MP (@lem15806) (@lem15879)). Qed.
Lemma lem15881 : term18.
Proof. exact (@lem15880 (@lem15757)). Qed.
