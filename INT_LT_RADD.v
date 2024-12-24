Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LT_RADD_term_abbrevs.
Require Import REAL_LT_RADD_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2304693 (x : int) : term0 x.
Proof. exact (@lem1493598 (real_of_int x)). Qed.
Lemma lem2304694 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2304695 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2304694 x) (@lem2304693 x)). Qed.
Lemma lem2304696 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2304695 x (real_of_int y)). Qed.
Lemma lem2304697 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2304698 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2304697 x y) (@lem2304696 x y)). Qed.
Lemma lem2304699 (x : int) (y : int) (z : int) : term4 x y z.
Proof. exact (@lem2304698 x y (real_of_int z)). Qed.
Lemma lem2304700 (z : int) (x : int) (y : int) : (term4 x y z) = ((term5 x y z) = (term6 x y)).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem2304701 (z : int) (x : int) (y : int) : (term5 x y z) = (term6 x y).
Proof. exact (EQ_MP (@lem2304700 z x y) (@lem2304699 x y z)). Qed.
Lemma lem2304703 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2304704 (x : int) (z : int) : (term7 x z) = (term8 x z).
Proof. exact (@lem2304703 x z). Qed.
Lemma lem2304705 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2304706 (x : int) (z : int) : (term9 x z) = (term10 x z).
Proof. exact (MK_COMB (@lem2304705) (@lem2304704 x z)). Qed.
Lemma lem2304708 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2304709 (y : int) (z : int) : (term7 y z) = (term8 y z).
Proof. exact (@lem2304708 y z). Qed.
Lemma lem2304710 (x : int) (y : int) (z : int) : (term5 x y z) = (term11 x y z).
Proof. exact (MK_COMB (@lem2304706 x z) (@lem2304709 y z)). Qed.
Lemma lem2304712 (x : int) (y : int) : (term6 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304713 (x : int) (y : int) (z : int) : (term11 x y z) = (term12 x y z).
Proof. exact (@lem2304712 (int_add x z) (int_add y z)). Qed.
Lemma lem2304714 (x : int) (y : int) (z : int) : (term5 x y z) = (term12 x y z).
Proof. exact (TRANS (@lem2304710 x y z) (@lem2304713 x y z)). Qed.
Lemma lem2304715 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2304716 (x : int) (y : int) (z : int) : (term13 x y z) = (term14 x y z).
Proof. exact (MK_COMB (@lem2304715) (@lem2304714 x y z)). Qed.
Lemma lem2304718 (x : int) (y : int) : (term6 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304719 (z : int) (x : int) (y : int) : ((term5 x y z) = (term6 x y)) = ((term12 x y z) = (int_lt x y)).
Proof. exact (MK_COMB (@lem2304716 x y z) (@lem2304718 x y)). Qed.
Lemma lem2304720 (z : int) (x : int) (y : int) : (term12 x y z) = (int_lt x y).
Proof. exact (EQ_MP (@lem2304719 z x y) (@lem2304701 z x y)). Qed.
Lemma lem2304721 (x : int) (y : int) : term15 x y.
Proof. exact (fun z : int => @lem2304720 z x y). Qed.
Lemma lem2304722 (x : int) : term16 x.
Proof. exact (fun y : int => @lem2304721 x y). Qed.
Lemma lem2304723 : term17.
Proof. exact (fun x : int => @lem2304722 x). Qed.
