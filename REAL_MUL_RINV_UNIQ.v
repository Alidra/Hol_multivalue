Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_MUL_RINV_UNIQ_term_abbrevs.
Require Import REAL_MUL_LINV_UNIQ_spec.
Require Import thm1338712_spec.
Lemma lem1587739 (x : real) : term0 x.
Proof. exact (@lem1338712 x). Qed.
Lemma lem1587740 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1587741 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1587740 x) (@lem1587739 x)). Qed.
Lemma lem1587742 (x : real) (y : real) : term2 x y.
Proof. exact (@lem1587741 x y). Qed.
Lemma lem1587743 (y : real) (x : real) : (term2 x y) = ((real_mul x y) = (real_mul y x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1587760 (y : real) (x : real) : (real_mul x y) = (real_mul y x).
Proof. exact (EQ_MP (@lem1587743 y x) (@lem1587742 x y)). Qed.
Lemma lem1587761 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1587762 (y : real) (x : real) : (term3 x y) = (term3 y x).
Proof. exact (MK_COMB (@lem1587761) (@lem1587760 y x)). Qed.
Lemma lem1587763 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1587764 (y : real) (x : real) : ((real_mul x y) = term4) = ((real_mul y x) = term4).
Proof. exact (MK_COMB (@lem1587762 y x) (@lem1587763)). Qed.
Lemma lem1587765 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1587766 (y : real) (x : real) : (term5 x y) = (term5 y x).
Proof. exact (MK_COMB (@lem1587765) (@lem1587764 y x)). Qed.
Lemma lem1587769 (x : real) (y : real) : ((real_inv x) = y) = ((real_inv x) = y).
Proof. exact (eq_refl ((real_inv x) = y)). Qed.
Lemma lem1587770 (x : real) (y : real) : (term6 x y) = (term7 x y).
Proof. exact (MK_COMB (@lem1587766 y x) (@lem1587769 x y)). Qed.
Lemma lem1587771 (x : real) : (term8 x) = (term9 x).
Proof. exact (fun_ext (fun y : real => @lem1587770 x y)). Qed.
Lemma lem1587772 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1587773 (x : real) : (term10 x) = (term11 x).
Proof. exact (MK_COMB (@lem1587772) (@lem1587771 x)). Qed.
Lemma lem1587774 : term12 = term13.
Proof. exact (fun_ext (fun x : real => @lem1587773 x)). Qed.
Lemma lem1587775 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1587776 : term14 = term15.
Proof. exact (MK_COMB (@lem1587775) (@lem1587774)). Qed.
Lemma lem1587777 : term15 = term14.
Proof. exact (SYM (@lem1587776)). Qed.
Lemma lem1587778 (x : real) : term16 x.
Proof. exact (@lem1587738 x). Qed.
Lemma lem1587779 (x : real) : (term16 x) = (term17 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1587780 (x : real) : term17 x.
Proof. exact (EQ_MP (@lem1587779 x) (@lem1587778 x)). Qed.
Lemma lem1587781 (x : real) (y : real) : term18 x y.
Proof. exact (@lem1587780 x y). Qed.
Lemma lem1587782 (y : real) (x : real) : (term18 x y) = (term7 y x).
Proof. exact (eq_refl (term18 x y)). Qed.
Lemma lem1587785 (y : real) (x : real) : term7 y x.
Proof. exact (EQ_MP (@lem1587782 y x) (@lem1587781 x y)). Qed.
Lemma lem1587786 (x : real) (y : real) : term7 x y.
Proof. exact (@lem1587785 x y). Qed.
Lemma lem1587791 (x : real) : term11 x.
Proof. exact (fun y : real => @lem1587786 x y). Qed.
Lemma lem1587796 : term15.
Proof. exact (fun x : real => @lem1587791 x). Qed.
Lemma lem1587797 : term14.
Proof. exact (EQ_MP (@lem1587777) (@lem1587796)). Qed.
