Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_EQ_MUL_RCANCEL_term_abbrevs.
Require Import REAL_EQ_MUL_RCANCEL_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2301712 (x : int) : term0 x.
Proof. exact (@lem1587429 (real_of_int x)). Qed.
Lemma lem2301713 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2301714 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2301713 x) (@lem2301712 x)). Qed.
Lemma lem2301715 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2301714 x (real_of_int y)). Qed.
Lemma lem2301716 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2301717 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2301716 x y) (@lem2301715 x y)). Qed.
Lemma lem2301718 (x : int) (y : int) (z : int) : term4 x y z.
Proof. exact (@lem2301717 x y (real_of_int z)). Qed.
Lemma lem2301719 (x : int) (y : int) (z : int) : (term4 x y z) = (((term5 x z) = (term5 y z)) = (term6 x y z)).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem2301720 (x : int) (y : int) (z : int) : ((term5 x z) = (term5 y z)) = (term6 x y z).
Proof. exact (EQ_MP (@lem2301719 x y z) (@lem2301718 x y z)). Qed.
Lemma lem2301722 (x : int) (y : int) : (term5 x y) = (term7 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2301723 (x : int) (z : int) : (term5 x z) = (term7 x z).
Proof. exact (@lem2301722 x z). Qed.
Lemma lem2301724 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2301725 (x : int) (z : int) : (term8 x z) = (term9 x z).
Proof. exact (MK_COMB (@lem2301724) (@lem2301723 x z)). Qed.
Lemma lem2301727 (x : int) (y : int) : (term5 x y) = (term7 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2301728 (y : int) (z : int) : (term5 y z) = (term7 y z).
Proof. exact (@lem2301727 y z). Qed.
Lemma lem2301729 (x : int) (y : int) (z : int) : ((term5 x z) = (term5 y z)) = ((term7 x z) = (term7 y z)).
Proof. exact (MK_COMB (@lem2301725 x z) (@lem2301728 y z)). Qed.
Lemma lem2301731 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301732 (x : int) (y : int) (z : int) : ((term7 x z) = (term7 y z)) = ((int_mul x z) = (int_mul y z)).
Proof. exact (@lem2301731 (int_mul x z) (int_mul y z)). Qed.
Lemma lem2301733 (x : int) (y : int) (z : int) : ((term5 x z) = (term5 y z)) = ((int_mul x z) = (int_mul y z)).
Proof. exact (TRANS (@lem2301729 x y z) (@lem2301732 x y z)). Qed.
Lemma lem2301734 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2301735 (x : int) (y : int) (z : int) : (term10 x y z) = (term11 x y z).
Proof. exact (MK_COMB (@lem2301734) (@lem2301733 x y z)). Qed.
Lemma lem2301737 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301738 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2301739 (x : int) (y : int) : (term12 x y) = (term13 x y).
Proof. exact (MK_COMB (@lem2301738) (@lem2301737 x y)). Qed.
Lemma lem2301741 (n : nat) : (real_of_num n) = (term14 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2301742 : term15 = term16.
Proof. exact (@lem2301741 (NUMERAL 0)). Qed.
Lemma lem2301743 (z : int) : (term17 z) = (term17 z).
Proof. exact (eq_refl (term17 z)). Qed.
Lemma lem2301744 (z : int) : ((real_of_int z) = term15) = ((real_of_int z) = term16).
Proof. exact (MK_COMB (@lem2301743 z) (@lem2301742)). Qed.
Lemma lem2301746 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301747 (z : int) : ((real_of_int z) = term16) = (z = term18).
Proof. exact (@lem2301746 z term18). Qed.
Lemma lem2301748 (z : int) : ((real_of_int z) = term15) = (z = term18).
Proof. exact (TRANS (@lem2301744 z) (@lem2301747 z)). Qed.
Lemma lem2301749 (x : int) (y : int) (z : int) : (term6 x y z) = (term19 x y z).
Proof. exact (MK_COMB (@lem2301739 x y) (@lem2301748 z)). Qed.
Lemma lem2301750 (x : int) (y : int) (z : int) : (((term5 x z) = (term5 y z)) = (term6 x y z)) = (((int_mul x z) = (int_mul y z)) = (term19 x y z)).
Proof. exact (MK_COMB (@lem2301735 x y z) (@lem2301749 x y z)). Qed.
Lemma lem2301751 (x : int) (y : int) (z : int) : ((int_mul x z) = (int_mul y z)) = (term19 x y z).
Proof. exact (EQ_MP (@lem2301750 x y z) (@lem2301720 x y z)). Qed.
Lemma lem2301752 (x : int) (y : int) : term20 x y.
Proof. exact (fun z : int => @lem2301751 x y z). Qed.
Lemma lem2301753 (x : int) : term21 x.
Proof. exact (fun y : int => @lem2301752 x y). Qed.
Lemma lem2301754 : term22.
Proof. exact (fun x : int => @lem2301753 x). Qed.
