Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LT_ADD1_term_abbrevs.
Require Import REAL_LT_ADD1_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2303701 (x : int) : term0 x.
Proof. exact (@lem1504643 (real_of_int x)). Qed.
Lemma lem2303702 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2303703 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2303702 x) (@lem2303701 x)). Qed.
Lemma lem2303704 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2303703 x (real_of_int y)). Qed.
Lemma lem2303705 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2303706 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2303705 x y) (@lem2303704 x y)). Qed.
Lemma lem2303708 (x : int) (y : int) : (term4 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2303709 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2303710 (x : int) (y : int) : (term5 x y) = (term6 x y).
Proof. exact (MK_COMB (@lem2303709) (@lem2303708 x y)). Qed.
Lemma lem2303712 (n : nat) : (real_of_num n) = (term7 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2303713 : term8 = term9.
Proof. exact (@lem2303712 term10). Qed.
Lemma lem2303714 (y : int) : (term11 y) = (term11 y).
Proof. exact (eq_refl (term11 y)). Qed.
Lemma lem2303715 (y : int) : (term12 y) = (term13 y).
Proof. exact (MK_COMB (@lem2303714 y) (@lem2303713)). Qed.
Lemma lem2303717 (x : int) (y : int) : (term14 x y) = (term15 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2303718 (y : int) : (term13 y) = (term16 y).
Proof. exact (@lem2303717 y term17). Qed.
Lemma lem2303719 (y : int) : (term12 y) = (term16 y).
Proof. exact (TRANS (@lem2303715 y) (@lem2303718 y)). Qed.
Lemma lem2303720 (x : int) : (term18 x) = (term18 x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem2303721 (x : int) (y : int) : (term19 x y) = (term20 x y).
Proof. exact (MK_COMB (@lem2303720 x) (@lem2303719 y)). Qed.
Lemma lem2303723 (x : int) (y : int) : (term21 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2303724 (x : int) (y : int) : (term20 x y) = (term22 x y).
Proof. exact (@lem2303723 x (term23 y)). Qed.
Lemma lem2303725 (x : int) (y : int) : (term19 x y) = (term22 x y).
Proof. exact (TRANS (@lem2303721 x y) (@lem2303724 x y)). Qed.
Lemma lem2303726 (x : int) (y : int) : (term3 x y) = (term24 x y).
Proof. exact (MK_COMB (@lem2303710 x y) (@lem2303725 x y)). Qed.
Lemma lem2303727 (x : int) (y : int) : term24 x y.
Proof. exact (EQ_MP (@lem2303726 x y) (@lem2303706 x y)). Qed.
Lemma lem2303728 (x : int) : term25 x.
Proof. exact (fun y : int => @lem2303727 x y). Qed.
Lemma lem2303729 : term26.
Proof. exact (fun x : int => @lem2303728 x). Qed.
