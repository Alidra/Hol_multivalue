Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_SQUARE_term_abbrevs.
Require Import REAL_LE_NEGTOTAL_spec.
Require Import REAL_MUL_LNEG_spec.
Require Import REAL_MUL_RNEG_spec.
Require Import REAL_NEG_NEG_spec.
Require Import thm0_spec.
Require Import thm1340049_spec.
Require Import thm1823_spec.
Lemma lem1382821 (x : real) : term0 x.
Proof. exact (@lem1358662 x). Qed.
Lemma lem1382822 (x : real) : (term0 x) = ((term1 x) = x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1382824 (x : real) : term2 x.
Proof. exact (@lem1360282 x). Qed.
Lemma lem1382825 (x : real) : (term2 x) = (term3 x).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem1382826 (x : real) : term3 x.
Proof. exact (EQ_MP (@lem1382825 x) (@lem1382824 x)). Qed.
Lemma lem1382827 (x : real) (y : real) : term4 x y.
Proof. exact (@lem1382826 x y). Qed.
Lemma lem1382828 (x : real) (y : real) : (term4 x y) = ((term5 x y) = (term6 x y)).
Proof. exact (eq_refl (term4 x y)). Qed.
Lemma lem1382830 (x : real) : term7 x.
Proof. exact (@lem1360913 x). Qed.
Lemma lem1382831 (x : real) : (term7 x) = (term8 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem1382832 (x : real) : term8 x.
Proof. exact (EQ_MP (@lem1382831 x) (@lem1382830 x)). Qed.
Lemma lem1382833 (x : real) (y : real) : term9 x y.
Proof. exact (@lem1382832 x y). Qed.
Lemma lem1382834 (x : real) (y : real) : (term9 x y) = ((term10 x y) = (term6 x y)).
Proof. exact (eq_refl (term9 x y)). Qed.
Lemma lem1382836 (x : real) : term11 x.
Proof. exact (@lem1382820 x). Qed.
Lemma lem1382837 (x : real) : (term11 x) = (term12 x).
Proof. exact (eq_refl (term11 x)). Qed.
Lemma lem1382838 (x : real) : term12 x.
Proof. exact (EQ_MP (@lem1382837 x) (@lem1382836 x)). Qed.
Lemma lem1382839 (x : real) (h1 : term13 x) : term13 x.
Proof. exact (h1). Qed.
Lemma lem1382840 (x : real) (h1 : term14 x) : term14 x.
Proof. exact (h1). Qed.
Lemma lem1382841 (x : real) (h1 : term13 x) : term15 x.
Proof. exact (conj (@lem1382839 x h1) (@lem1382839 x h1)). Qed.
Lemma lem1382842 (x : real) : term16 x.
Proof. exact (@lem1340049 x). Qed.
Lemma lem1382843 (x : real) : (term16 x) = (term17 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1382844 (x : real) : term17 x.
Proof. exact (EQ_MP (@lem1382843 x) (@lem1382842 x)). Qed.
Lemma lem1382845 (x : real) (y : real) : term18 x y.
Proof. exact (@lem1382844 x y). Qed.
Lemma lem1382846 (x : real) (y : real) : (term18 x y) = (term19 x y).
Proof. exact (eq_refl (term18 x y)). Qed.
Lemma lem1382849 (x : real) (y : real) : term19 x y.
Proof. exact (EQ_MP (@lem1382846 x y) (@lem1382845 x y)). Qed.
Lemma lem1382850 (x : real) : term20 x.
Proof. exact (@lem1382849 x x). Qed.
Lemma lem1382851 (x : real) (h1 : term13 x) : term21 x.
Proof. exact (@lem1382850 x (@lem1382841 x h1)). Qed.
Lemma lem1382852 (x : real) (h1 : term14 x) : term22 x.
Proof. exact (conj (@lem1382840 x h1) (@lem1382840 x h1)). Qed.
Lemma lem1382853 (x : real) : term16 x.
Proof. exact (@lem1340049 x). Qed.
Lemma lem1382854 (x : real) : (term16 x) = (term17 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1382855 (x : real) : term17 x.
Proof. exact (EQ_MP (@lem1382854 x) (@lem1382853 x)). Qed.
Lemma lem1382856 (x : real) (y : real) : term18 x y.
Proof. exact (@lem1382855 x y). Qed.
Lemma lem1382857 (x : real) (y : real) : (term18 x y) = (term19 x y).
Proof. exact (eq_refl (term18 x y)). Qed.
Lemma lem1382860 (x : real) (y : real) : term19 x y.
Proof. exact (EQ_MP (@lem1382857 x y) (@lem1382856 x y)). Qed.
Lemma lem1382861 (x : real) : term23 x.
Proof. exact (@lem1382860 (real_neg x) (real_neg x)). Qed.
Lemma lem1382862 (x : real) (h1 : term14 x) : term24 x.
Proof. exact (@lem1382861 x (@lem1382852 x h1)). Qed.
Lemma lem1382864 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem1382865 (x : real) : (term25 x) = True.
Proof. exact (@lem1382864 (term21 x)). Qed.
Lemma lem1382866 (x : real) : True = (term25 x).
Proof. exact (SYM (@lem1382865 x)). Qed.
Lemma lem1382867 (x : real) : term25 x.
Proof. exact (EQ_MP (@lem1382866 x) (@lem0)). Qed.
Lemma lem1382871 (x : real) (y : real) : (term10 x y) = (term6 x y).
Proof. exact (EQ_MP (@lem1382834 x y) (@lem1382833 x y)). Qed.
Lemma lem1382872 (x : real) : (term26 x) = (term27 x).
Proof. exact (@lem1382871 x (real_neg x)). Qed.
Lemma lem1382874 (x : real) (y : real) : (term5 x y) = (term6 x y).
Proof. exact (EQ_MP (@lem1382828 x y) (@lem1382827 x y)). Qed.
Lemma lem1382875 (x : real) : (term28 x) = (term29 x).
Proof. exact (@lem1382874 x x). Qed.
Lemma lem1382876 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1382877 (x : real) : (term27 x) = (term30 x).
Proof. exact (MK_COMB (@lem1382876) (@lem1382875 x)). Qed.
Lemma lem1382879 (x : real) : (term1 x) = x.
Proof. exact (EQ_MP (@lem1382822 x) (@lem1382821 x)). Qed.
Lemma lem1382880 (x : real) : (term30 x) = (real_mul x x).
Proof. exact (@lem1382879 (real_mul x x)). Qed.
Lemma lem1382881 (x : real) : (term27 x) = (real_mul x x).
Proof. exact (TRANS (@lem1382877 x) (@lem1382880 x)). Qed.
Lemma lem1382882 (x : real) : (term26 x) = (real_mul x x).
Proof. exact (TRANS (@lem1382872 x) (@lem1382881 x)). Qed.
Lemma lem1382883 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem1382884 (x : real) : (term24 x) = (term21 x).
Proof. exact (MK_COMB (@lem1382883) (@lem1382882 x)). Qed.
Lemma lem1382885 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1382886 (x : real) : (term32 x) = (term33 x).
Proof. exact (MK_COMB (@lem1382885) (@lem1382884 x)). Qed.
Lemma lem1382887 (x : real) : (term21 x) = (term21 x).
Proof. exact (eq_refl (term21 x)). Qed.
Lemma lem1382888 (x : real) : (term34 x) = (term25 x).
Proof. exact (MK_COMB (@lem1382886 x) (@lem1382887 x)). Qed.
Lemma lem1382890 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem1382891 (x : real) : (term25 x) = True.
Proof. exact (@lem1382890 (term21 x)). Qed.
Lemma lem1382892 (x : real) : (term34 x) = True.
Proof. exact (TRANS (@lem1382888 x) (@lem1382891 x)). Qed.
Lemma lem1382893 (x : real) : True = (term34 x).
Proof. exact (SYM (@lem1382892 x)). Qed.
Lemma lem1382894 (x : real) : term34 x.
Proof. exact (EQ_MP (@lem1382893 x) (@lem0)). Qed.
Lemma lem1382895 (x : real) (h1 : term14 x) : term21 x.
Proof. exact (@lem1382894 x (@lem1382862 x h1)). Qed.
Lemma lem1382896 (x : real) (h1 : term13 x) : term21 x.
Proof. exact (@lem1382867 x (@lem1382851 x h1)). Qed.
Lemma lem1382897 (x : real) : term21 x.
Proof. exact (or_elim (@lem1382838 x) (fun h0 : term13 x => @lem1382896 x h0) (fun h0 : term14 x => @lem1382895 x h0)). Qed.
Lemma lem1382902 : term35.
Proof. exact (fun x : real => @lem1382897 x). Qed.
