Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_EQ_LCANCEL_IMP_term_abbrevs.
Require Import REAL_EQ_RCANCEL_IMP_spec.
Require Import thm1338712_spec.
Lemma lem1640772 (x : real) : term0 x.
Proof. exact (@lem1338712 x). Qed.
Lemma lem1640773 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1640774 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1640773 x) (@lem1640772 x)). Qed.
Lemma lem1640775 (x : real) (y : real) : term2 x y.
Proof. exact (@lem1640774 x y). Qed.
Lemma lem1640776 (y : real) (x : real) : (term2 x y) = ((real_mul x y) = (real_mul y x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1640799 (y : real) (x : real) : (real_mul x y) = (real_mul y x).
Proof. exact (EQ_MP (@lem1640776 y x) (@lem1640775 x y)). Qed.
Lemma lem1640800 (x : real) (z : real) : (real_mul z x) = (real_mul x z).
Proof. exact (@lem1640799 x z). Qed.
Lemma lem1640801 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1640802 (x : real) (z : real) : (term3 z x) = (term3 x z).
Proof. exact (MK_COMB (@lem1640801) (@lem1640800 x z)). Qed.
Lemma lem1640804 (y : real) (x : real) : (real_mul x y) = (real_mul y x).
Proof. exact (EQ_MP (@lem1640776 y x) (@lem1640775 x y)). Qed.
Lemma lem1640805 (y : real) (z : real) : (real_mul z y) = (real_mul y z).
Proof. exact (@lem1640804 y z). Qed.
Lemma lem1640806 (x : real) (y : real) (z : real) : ((real_mul z x) = (real_mul z y)) = ((real_mul x z) = (real_mul y z)).
Proof. exact (MK_COMB (@lem1640802 x z) (@lem1640805 y z)). Qed.
Lemma lem1640807 (z : real) : (term4 z) = (term4 z).
Proof. exact (eq_refl (term4 z)). Qed.
Lemma lem1640808 (x : real) (y : real) (z : real) : (term5 x z y) = (term6 x y z).
Proof. exact (MK_COMB (@lem1640807 z) (@lem1640806 x y z)). Qed.
Lemma lem1640809 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1640810 (x : real) (y : real) (z : real) : (term7 x z y) = (term8 x y z).
Proof. exact (MK_COMB (@lem1640809) (@lem1640808 x y z)). Qed.
Lemma lem1640813 (x : real) (y : real) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem1640814 (z : real) (x : real) (y : real) : (term9 z x y) = (term10 z x y).
Proof. exact (MK_COMB (@lem1640810 x y z) (@lem1640813 x y)). Qed.
Lemma lem1640815 (x : real) (y : real) : (term11 x y) = (term12 x y).
Proof. exact (fun_ext (fun z : real => @lem1640814 z x y)). Qed.
Lemma lem1640816 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1640817 (x : real) (y : real) : (term13 x y) = (term14 x y).
Proof. exact (MK_COMB (@lem1640816) (@lem1640815 x y)). Qed.
Lemma lem1640818 (x : real) : (term15 x) = (term16 x).
Proof. exact (fun_ext (fun y : real => @lem1640817 x y)). Qed.
Lemma lem1640819 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1640820 (x : real) : (term17 x) = (term18 x).
Proof. exact (MK_COMB (@lem1640819) (@lem1640818 x)). Qed.
Lemma lem1640821 : term19 = term20.
Proof. exact (fun_ext (fun x : real => @lem1640820 x)). Qed.
Lemma lem1640822 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1640823 : term21 = term22.
Proof. exact (MK_COMB (@lem1640822) (@lem1640821)). Qed.
Lemma lem1640824 : term22 = term21.
Proof. exact (SYM (@lem1640823)). Qed.
Lemma lem1640825 (x : real) : term23 x.
Proof. exact (@lem1640771 x). Qed.
Lemma lem1640826 (x : real) : (term23 x) = (term18 x).
Proof. exact (eq_refl (term23 x)). Qed.
Lemma lem1640827 (x : real) : term18 x.
Proof. exact (EQ_MP (@lem1640826 x) (@lem1640825 x)). Qed.
Lemma lem1640828 (x : real) (y : real) : term24 x y.
Proof. exact (@lem1640827 x y). Qed.
Lemma lem1640829 (x : real) (y : real) : (term24 x y) = (term14 x y).
Proof. exact (eq_refl (term24 x y)). Qed.
Lemma lem1640830 (x : real) (y : real) : term14 x y.
Proof. exact (EQ_MP (@lem1640829 x y) (@lem1640828 x y)). Qed.
Lemma lem1640831 (x : real) (y : real) (z : real) : term25 x y z.
Proof. exact (@lem1640830 x y z). Qed.
Lemma lem1640832 (z : real) (x : real) (y : real) : (term25 x y z) = (term10 z x y).
Proof. exact (eq_refl (term25 x y z)). Qed.
Lemma lem1640835 (z : real) (x : real) (y : real) : term10 z x y.
Proof. exact (EQ_MP (@lem1640832 z x y) (@lem1640831 x y z)). Qed.
Lemma lem1640840 (x : real) (y : real) : term14 x y.
Proof. exact (fun z : real => @lem1640835 z x y). Qed.
Lemma lem1640845 (x : real) : term18 x.
Proof. exact (fun y : real => @lem1640840 x y). Qed.
Lemma lem1640850 : term22.
Proof. exact (fun x : real => @lem1640845 x). Qed.
Lemma lem1640851 : term21.
Proof. exact (EQ_MP (@lem1640824) (@lem1640850)). Qed.
