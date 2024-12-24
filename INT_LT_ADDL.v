Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LT_ADDL_term_abbrevs.
Require Import REAL_LT_ADDL_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2303772 (x : int) : term0 x.
Proof. exact (@lem1511839 (real_of_int x)). Qed.
Lemma lem2303773 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2303774 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2303773 x) (@lem2303772 x)). Qed.
Lemma lem2303775 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2303774 x (real_of_int y)). Qed.
Lemma lem2303776 (y : int) (x : int) : (term2 x y) = ((term3 x y) = (term4 x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2303777 (y : int) (x : int) : (term3 x y) = (term4 x).
Proof. exact (EQ_MP (@lem2303776 y x) (@lem2303775 x y)). Qed.
Lemma lem2303779 (x : int) (y : int) : (term5 x y) = (term6 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2303780 (y : int) : (term7 y) = (term7 y).
Proof. exact (eq_refl (term7 y)). Qed.
Lemma lem2303781 (x : int) (y : int) : (term3 x y) = (term8 x y).
Proof. exact (MK_COMB (@lem2303780 y) (@lem2303779 x y)). Qed.
Lemma lem2303783 (x : int) (y : int) : (term9 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2303784 (x : int) (y : int) : (term8 x y) = (term10 x y).
Proof. exact (@lem2303783 y (int_add x y)). Qed.
Lemma lem2303785 (x : int) (y : int) : (term3 x y) = (term10 x y).
Proof. exact (TRANS (@lem2303781 x y) (@lem2303784 x y)). Qed.
Lemma lem2303786 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2303787 (x : int) (y : int) : (term11 x y) = (term12 x y).
Proof. exact (MK_COMB (@lem2303786) (@lem2303785 x y)). Qed.
Lemma lem2303789 (n : nat) : (real_of_num n) = (term13 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2303790 : term14 = term15.
Proof. exact (@lem2303789 (NUMERAL 0)). Qed.
Lemma lem2303791 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2303792 : term16 = term17.
Proof. exact (MK_COMB (@lem2303791) (@lem2303790)). Qed.
Lemma lem2303793 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2303794 (x : int) : (term4 x) = (term18 x).
Proof. exact (MK_COMB (@lem2303792) (@lem2303793 x)). Qed.
Lemma lem2303796 (x : int) (y : int) : (term9 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2303797 (x : int) : (term18 x) = (term19 x).
Proof. exact (@lem2303796 term20 x). Qed.
Lemma lem2303798 (x : int) : (term4 x) = (term19 x).
Proof. exact (TRANS (@lem2303794 x) (@lem2303797 x)). Qed.
Lemma lem2303799 (y : int) (x : int) : ((term3 x y) = (term4 x)) = ((term10 x y) = (term19 x)).
Proof. exact (MK_COMB (@lem2303787 x y) (@lem2303798 x)). Qed.
Lemma lem2303800 (y : int) (x : int) : (term10 x y) = (term19 x).
Proof. exact (EQ_MP (@lem2303799 y x) (@lem2303777 y x)). Qed.
Lemma lem2303801 (x : int) : term21 x.
Proof. exact (fun y : int => @lem2303800 y x). Qed.
Lemma lem2303802 : term22.
Proof. exact (fun x : int => @lem2303801 x). Qed.
