Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1337872_term_abbrevs.
Require Import TREAL_EQ_REFL_spec.
Require Import TREAL_EQ_TRANS_spec.
Require Import TREAL_MUL_WELLDEF_spec.
Require Import thm1337493_spec.
Require Import thm32_spec.
Require Import thm9127_spec.
Lemma lem1337754 : real_mul = term0.
Proof. exact (@real_mul_def). Qed.
Lemma lem1337755 (x1 : real) : x1 = x1.
Proof. exact (eq_refl x1). Qed.
Lemma lem1337756 (x1 : real) : (real_mul x1) = (term1 x1).
Proof. exact (MK_COMB (@lem1337754) (@lem1337755 x1)). Qed.
Lemma lem1337757 (x1 : real) : (term1 x1) = (term2 x1).
Proof. exact (eq_refl (term1 x1)). Qed.
Lemma lem1337758 (x1 : real) : (term3 x1) = (term3 x1).
Proof. exact (eq_refl (term3 x1)). Qed.
Lemma lem1337759 (x1 : real) : ((real_mul x1) = (term1 x1)) = ((real_mul x1) = (term2 x1)).
Proof. exact (MK_COMB (@lem1337758 x1) (@lem1337757 x1)). Qed.
Lemma lem1337760 (x1 : real) : (real_mul x1) = (term2 x1).
Proof. exact (EQ_MP (@lem1337759 x1) (@lem1337756 x1)). Qed.
Lemma lem1337761 (y1 : real) : y1 = y1.
Proof. exact (eq_refl y1). Qed.
Lemma lem1337762 (x1 : real) (y1 : real) : (real_mul x1 y1) = (term4 x1 y1).
Proof. exact (MK_COMB (@lem1337760 x1) (@lem1337761 y1)). Qed.
Lemma lem1337763 (x1 : real) (y1 : real) : (term4 x1 y1) = (term5 x1 y1).
Proof. exact (eq_refl (term4 x1 y1)). Qed.
Lemma lem1337764 (x1 : real) (y1 : real) : (term6 x1 y1) = (term6 x1 y1).
Proof. exact (eq_refl (term6 x1 y1)). Qed.
Lemma lem1337765 (x1 : real) (y1 : real) : ((real_mul x1 y1) = (term4 x1 y1)) = ((real_mul x1 y1) = (term5 x1 y1)).
Proof. exact (MK_COMB (@lem1337764 x1 y1) (@lem1337763 x1 y1)). Qed.
Lemma lem1337766 (x1 : real) (y1 : real) : (real_mul x1 y1) = (term5 x1 y1).
Proof. exact (EQ_MP (@lem1337765 x1 y1) (@lem1337762 x1 y1)). Qed.
Lemma lem1337767 (x : prod hreal hreal) : (term7 x) = ((term8 x) = (treal_eq x)).
Proof. exact (@lem1337493 (treal_eq x)). Qed.
Lemma lem1337768 (x : prod hreal hreal) : (treal_eq x) = (treal_eq x).
Proof. exact (eq_refl (treal_eq x)). Qed.
Lemma lem1337769 (x : prod hreal hreal) : term7 x.
Proof. exact (ex_intro (term9 x) x (@lem1337768 x)). Qed.
Lemma lem1337770 (x : prod hreal hreal) : (term8 x) = (treal_eq x).
Proof. exact (EQ_MP (@lem1337767 x) (@lem1337769 x)). Qed.
Lemma lem1337771 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term10 x1 y1) = (term11 x1 y1).
Proof. exact (@lem1337766 (term12 x1) (term12 y1)). Qed.
Lemma lem1337772 (x1 : prod hreal hreal) : (term8 x1) = (treal_eq x1).
Proof. exact (@lem1337770 x1). Qed.
Lemma lem1337773 (y1 : prod hreal hreal) : (term8 y1) = (treal_eq y1).
Proof. exact (@lem1337770 y1). Qed.
Lemma lem1337774 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term13 x1 y1) = (term13 x1 y1).
Proof. exact (eq_refl (term13 x1 y1)). Qed.
Lemma lem1337775 (y1 : prod hreal hreal) (x1 : prod hreal hreal) : (term14 y1 x1) = (term15 y1 x1).
Proof. exact (MK_COMB (@lem1337774 x1 y1) (@lem1337772 x1)). Qed.
Lemma lem1337776 (y1 : prod hreal hreal) (x1 : prod hreal hreal) : (term15 y1 x1) = (term16 y1 x1).
Proof. exact (eq_refl (term15 y1 x1)). Qed.
Lemma lem1337777 (y1 : prod hreal hreal) (x1 : prod hreal hreal) : (term17 y1 x1) = (term17 y1 x1).
Proof. exact (eq_refl (term17 y1 x1)). Qed.
Lemma lem1337778 (y1 : prod hreal hreal) (x1 : prod hreal hreal) : ((term14 y1 x1) = (term15 y1 x1)) = ((term14 y1 x1) = (term16 y1 x1)).
Proof. exact (MK_COMB (@lem1337777 y1 x1) (@lem1337776 y1 x1)). Qed.
Lemma lem1337779 (y1 : prod hreal hreal) (x1 : prod hreal hreal) : (term14 y1 x1) = (term18 y1 x1).
Proof. exact (eq_refl (term14 y1 x1)). Qed.
Lemma lem1337780 : (@eq (((prod hreal hreal) -> Prop) -> Prop)) = (@eq (((prod hreal hreal) -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq (((prod hreal hreal) -> Prop) -> Prop))). Qed.
Lemma lem1337781 (y1 : prod hreal hreal) (x1 : prod hreal hreal) : (term17 y1 x1) = (term19 y1 x1).
Proof. exact (MK_COMB (@lem1337780) (@lem1337779 y1 x1)). Qed.
Lemma lem1337782 (y1 : prod hreal hreal) (x1 : prod hreal hreal) : (term16 y1 x1) = (term16 y1 x1).
Proof. exact (eq_refl (term16 y1 x1)). Qed.
Lemma lem1337783 (y1 : prod hreal hreal) (x1 : prod hreal hreal) : ((term14 y1 x1) = (term16 y1 x1)) = ((term18 y1 x1) = (term16 y1 x1)).
Proof. exact (MK_COMB (@lem1337781 y1 x1) (@lem1337782 y1 x1)). Qed.
Lemma lem1337784 (y1 : prod hreal hreal) (x1 : prod hreal hreal) : ((term14 y1 x1) = (term15 y1 x1)) = ((term18 y1 x1) = (term16 y1 x1)).
Proof. exact (TRANS (@lem1337778 y1 x1) (@lem1337783 y1 x1)). Qed.
Lemma lem1337785 (y1 : prod hreal hreal) (x1 : prod hreal hreal) : (term18 y1 x1) = (term16 y1 x1).
Proof. exact (EQ_MP (@lem1337784 y1 x1) (@lem1337775 y1 x1)). Qed.
Lemma lem1337786 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term20 x1 y1) = (term21 x1 y1).
Proof. exact (MK_COMB (@lem1337785 y1 x1) (@lem1337773 y1)). Qed.
Lemma lem1337787 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term21 x1 y1) = ((term10 x1 y1) = (term22 x1 y1)).
Proof. exact (eq_refl (term21 x1 y1)). Qed.
Lemma lem1337788 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term23 x1 y1) = (term23 x1 y1).
Proof. exact (eq_refl (term23 x1 y1)). Qed.
Lemma lem1337789 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : ((term20 x1 y1) = (term21 x1 y1)) = ((term20 x1 y1) = ((term10 x1 y1) = (term22 x1 y1))).
Proof. exact (MK_COMB (@lem1337788 x1 y1) (@lem1337787 x1 y1)). Qed.
Lemma lem1337790 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term20 x1 y1) = ((term10 x1 y1) = (term11 x1 y1)).
Proof. exact (eq_refl (term20 x1 y1)). Qed.
Lemma lem1337791 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1337792 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term23 x1 y1) = (term24 x1 y1).
Proof. exact (MK_COMB (@lem1337791) (@lem1337790 x1 y1)). Qed.
Lemma lem1337793 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : ((term10 x1 y1) = (term22 x1 y1)) = ((term10 x1 y1) = (term22 x1 y1)).
Proof. exact (eq_refl ((term10 x1 y1) = (term22 x1 y1))). Qed.
Lemma lem1337794 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : ((term20 x1 y1) = ((term10 x1 y1) = (term22 x1 y1))) = (((term10 x1 y1) = (term11 x1 y1)) = ((term10 x1 y1) = (term22 x1 y1))).
Proof. exact (MK_COMB (@lem1337792 x1 y1) (@lem1337793 x1 y1)). Qed.
Lemma lem1337795 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : ((term20 x1 y1) = (term21 x1 y1)) = (((term10 x1 y1) = (term11 x1 y1)) = ((term10 x1 y1) = (term22 x1 y1))).
Proof. exact (TRANS (@lem1337789 x1 y1) (@lem1337794 x1 y1)). Qed.
Lemma lem1337796 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : ((term10 x1 y1) = (term11 x1 y1)) = ((term10 x1 y1) = (term22 x1 y1)).
Proof. exact (EQ_MP (@lem1337795 x1 y1) (@lem1337786 x1 y1)). Qed.
Lemma lem1337797 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term10 x1 y1) = (term22 x1 y1).
Proof. exact (EQ_MP (@lem1337796 x1 y1) (@lem1337771 x1 y1)). Qed.
Lemma lem1337798 (u : prod hreal hreal) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (y1 : prod hreal hreal) (y1' : prod hreal hreal) (h1 : term25 u x1 x1' y1 y1') : term25 u x1 x1' y1 y1'.
Proof. exact (h1). Qed.
Lemma lem1337799 (u : prod hreal hreal) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (y1 : prod hreal hreal) (y1' : prod hreal hreal) (h1 : term25 u x1 x1' y1 y1') : term26 x1 x1' y1 y1'.
Proof. exact (proj2 (@lem1337798 u x1 x1' y1 y1' h1)). Qed.
Lemma lem1337800 (u : prod hreal hreal) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (y1 : prod hreal hreal) (y1' : prod hreal hreal) (h1 : term25 u x1 x1' y1 y1') : term27 x1' y1' u.
Proof. exact (proj1 (@lem1337798 u x1 x1' y1 y1' h1)). Qed.
Lemma lem1337801 (u : prod hreal hreal) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (y1 : prod hreal hreal) (y1' : prod hreal hreal) (h1 : term25 u x1 x1' y1 y1') : treal_eq y1 y1'.
Proof. exact (proj2 (@lem1337799 u x1 x1' y1 y1' h1)). Qed.
Lemma lem1337802 (u : prod hreal hreal) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (y1 : prod hreal hreal) (y1' : prod hreal hreal) (h1 : term25 u x1 x1' y1 y1') : treal_eq x1 x1'.
Proof. exact (proj1 (@lem1337799 u x1 x1' y1 y1' h1)). Qed.
Lemma lem1337803 (u : prod hreal hreal) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (y1 : prod hreal hreal) (y1' : prod hreal hreal) (h1 : term25 u x1 x1' y1 y1') : term26 x1 x1' y1 y1'.
Proof. exact (conj (@lem1337802 u x1 x1' y1 y1' h1) (@lem1337801 u x1 x1' y1 y1' h1)). Qed.
Lemma lem1337804 (x1 : prod hreal hreal) : term28 x1.
Proof. exact (@lem1334178 x1). Qed.
Lemma lem1337805 (x1 : prod hreal hreal) : (term28 x1) = (term29 x1).
Proof. exact (eq_refl (term28 x1)). Qed.
Lemma lem1337806 (x1 : prod hreal hreal) : term29 x1.
Proof. exact (EQ_MP (@lem1337805 x1) (@lem1337804 x1)). Qed.
Lemma lem1337807 (x1 : prod hreal hreal) (x2 : prod hreal hreal) : term30 x1 x2.
Proof. exact (@lem1337806 x1 x2). Qed.
Lemma lem1337808 (x1 : prod hreal hreal) (x2 : prod hreal hreal) : (term30 x1 x2) = (term31 x1 x2).
Proof. exact (eq_refl (term30 x1 x2)). Qed.
Lemma lem1337809 (x1 : prod hreal hreal) (x2 : prod hreal hreal) : term31 x1 x2.
Proof. exact (EQ_MP (@lem1337808 x1 x2) (@lem1337807 x1 x2)). Qed.
Lemma lem1337810 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y1 : prod hreal hreal) : term32 x1 x2 y1.
Proof. exact (@lem1337809 x1 x2 y1). Qed.
Lemma lem1337811 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (x2 : prod hreal hreal) : (term32 x1 x2 y1) = (term33 x1 y1 x2).
Proof. exact (eq_refl (term32 x1 x2 y1)). Qed.
Lemma lem1337812 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (x2 : prod hreal hreal) : term33 x1 y1 x2.
Proof. exact (EQ_MP (@lem1337811 x1 y1 x2) (@lem1337810 x1 x2 y1)). Qed.
Lemma lem1337813 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (x2 : prod hreal hreal) (y2 : prod hreal hreal) : term34 x1 y1 x2 y2.
Proof. exact (@lem1337812 x1 y1 x2 y2). Qed.
Lemma lem1337814 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (x2 : prod hreal hreal) (y2 : prod hreal hreal) : (term34 x1 y1 x2 y2) = (term35 x1 y1 x2 y2).
Proof. exact (eq_refl (term34 x1 y1 x2 y2)). Qed.
Lemma lem1337817 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (x2 : prod hreal hreal) (y2 : prod hreal hreal) : term35 x1 y1 x2 y2.
Proof. exact (EQ_MP (@lem1337814 x1 y1 x2 y2) (@lem1337813 x1 y1 x2 y2)). Qed.
Lemma lem1337818 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (x1' : prod hreal hreal) (y1' : prod hreal hreal) : term35 x1 y1 x1' y1'.
Proof. exact (@lem1337817 x1 y1 x1' y1'). Qed.
Lemma lem1337819 (u : prod hreal hreal) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (y1 : prod hreal hreal) (y1' : prod hreal hreal) (h1 : term25 u x1 x1' y1 y1') : term36 x1 y1 x1' y1'.
Proof. exact (@lem1337818 x1 y1 x1' y1' (@lem1337803 u x1 x1' y1 y1' h1)). Qed.
Lemma lem1337820 (u : prod hreal hreal) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (y1 : prod hreal hreal) (y1' : prod hreal hreal) (h1 : term25 u x1 x1' y1 y1') : term37 x1 y1 x1' y1' u.
Proof. exact (conj (@lem1337819 u x1 x1' y1 y1' h1) (@lem1337800 u x1 x1' y1 y1' h1)). Qed.
Lemma lem1337821 (x : prod hreal hreal) : term38 x.
Proof. exact (@lem1326778 x). Qed.
Lemma lem1337822 (x : prod hreal hreal) : (term38 x) = (term39 x).
Proof. exact (eq_refl (term38 x)). Qed.
Lemma lem1337823 (x : prod hreal hreal) : term39 x.
Proof. exact (EQ_MP (@lem1337822 x) (@lem1337821 x)). Qed.
Lemma lem1337824 (x : prod hreal hreal) (y : prod hreal hreal) : term40 x y.
Proof. exact (@lem1337823 x y). Qed.
Lemma lem1337825 (y : prod hreal hreal) (x : prod hreal hreal) : (term40 x y) = (term41 y x).
Proof. exact (eq_refl (term40 x y)). Qed.
Lemma lem1337826 (y : prod hreal hreal) (x : prod hreal hreal) : term41 y x.
Proof. exact (EQ_MP (@lem1337825 y x) (@lem1337824 x y)). Qed.
Lemma lem1337827 (y : prod hreal hreal) (x : prod hreal hreal) (z : prod hreal hreal) : term42 y x z.
Proof. exact (@lem1337826 y x z). Qed.
Lemma lem1337828 (y : prod hreal hreal) (x : prod hreal hreal) (z : prod hreal hreal) : (term42 y x z) = (term43 y x z).
Proof. exact (eq_refl (term42 y x z)). Qed.
Lemma lem1337831 (y : prod hreal hreal) (x : prod hreal hreal) (z : prod hreal hreal) : term43 y x z.
Proof. exact (EQ_MP (@lem1337828 y x z) (@lem1337827 y x z)). Qed.
Lemma lem1337832 (x1' : prod hreal hreal) (y1' : prod hreal hreal) (x1 : prod hreal hreal) (y1 : prod hreal hreal) (u : prod hreal hreal) : term44 x1' y1' x1 y1 u.
Proof. exact (@lem1337831 (treal_mul x1' y1') (treal_mul x1 y1) u). Qed.
Lemma lem1337833 (u : prod hreal hreal) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (y1 : prod hreal hreal) (y1' : prod hreal hreal) (h1 : term25 u x1 x1' y1 y1') : term27 x1 y1 u.
Proof. exact (@lem1337832 x1' y1' x1 y1 u (@lem1337820 u x1 x1' y1 y1' h1)). Qed.
Lemma lem1337834 (u : prod hreal hreal) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (y1 : prod hreal hreal) (h1 : term45 u x1 x1' y1) : term45 u x1 x1' y1.
Proof. exact (h1). Qed.
Lemma lem1337835 (u : prod hreal hreal) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (y1 : prod hreal hreal) (h1 : term45 u x1 x1' y1) : term27 x1 y1 u.
Proof. exact (ex_elim (@lem1337834 u x1 x1' y1 h1) (fun y1' : prod hreal hreal => fun h0 : term46 u x1 x1' y1 y1' => @lem1337833 u x1 x1' y1 y1' h0)). Qed.
Lemma lem1337836 (u : prod hreal hreal) (x1 : prod hreal hreal) (y1 : prod hreal hreal) (h1 : term47 u x1 y1) : term47 u x1 y1.
Proof. exact (h1). Qed.
Lemma lem1337837 (u : prod hreal hreal) (x1 : prod hreal hreal) (y1 : prod hreal hreal) (h1 : term47 u x1 y1) : term27 x1 y1 u.
Proof. exact (ex_elim (@lem1337836 u x1 y1 h1) (fun x1' : prod hreal hreal => fun h0 : term48 u x1 y1 x1' => @lem1337835 u x1 x1' y1 h0)). Qed.
Lemma lem1337838 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (u : prod hreal hreal) (h1 : term27 x1 y1 u) : term27 x1 y1 u.
Proof. exact (h1). Qed.
Lemma lem1337839 (x1 : prod hreal hreal) : term49 x1.
Proof. exact (@lem1326193 x1). Qed.
Lemma lem1337840 (x1 : prod hreal hreal) : (term49 x1) = (treal_eq x1 x1).
Proof. exact (eq_refl (term49 x1)). Qed.
Lemma lem1337841 (x1 : prod hreal hreal) : treal_eq x1 x1.
Proof. exact (EQ_MP (@lem1337840 x1) (@lem1337839 x1)). Qed.
Lemma lem1337842 (y1 : prod hreal hreal) : term49 y1.
Proof. exact (@lem1326193 y1). Qed.
Lemma lem1337843 (y1 : prod hreal hreal) : (term49 y1) = (treal_eq y1 y1).
Proof. exact (eq_refl (term49 y1)). Qed.
Lemma lem1337844 (y1 : prod hreal hreal) : treal_eq y1 y1.
Proof. exact (EQ_MP (@lem1337843 y1) (@lem1337842 y1)). Qed.
Lemma lem1337845 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : term50 x1 y1.
Proof. exact (conj (@lem1337841 x1) (@lem1337844 y1)). Qed.
Lemma lem1337846 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (u : prod hreal hreal) (h1 : term27 x1 y1 u) : term51 u x1 y1.
Proof. exact (conj (@lem1337838 x1 y1 u h1) (@lem1337845 x1 y1)). Qed.
Lemma lem1337847 (u : prod hreal hreal) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (y1 : prod hreal hreal) (y1' : prod hreal hreal) (h1 : term25 u x1 x1' y1 y1') : term25 u x1 x1' y1 y1'.
Proof. exact (h1). Qed.
Lemma lem1337848 (u : prod hreal hreal) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (y1 : prod hreal hreal) (y1' : prod hreal hreal) (h1 : term25 u x1 x1' y1 y1') : term45 u x1 x1' y1.
Proof. exact (ex_intro (term46 u x1 x1' y1) y1' (@lem1337847 u x1 x1' y1 y1' h1)). Qed.
Lemma lem1337849 (u : prod hreal hreal) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (y1 : prod hreal hreal) (y1' : prod hreal hreal) (h1 : term25 u x1 x1' y1 y1') : term47 u x1 y1.
Proof. exact (ex_intro (term48 u x1 y1) x1' (@lem1337848 u x1 x1' y1 y1' h1)). Qed.
Lemma lem1337852 (x1' : prod hreal hreal) (y1' : prod hreal hreal) (u : prod hreal hreal) (x1 : prod hreal hreal) (y1 : prod hreal hreal) : term52 x1' y1' u x1 y1.
Proof. exact (fun h0 : term25 u x1 x1' y1 y1' => @lem1337849 u x1 x1' y1 y1' h0). Qed.
Lemma lem1337853 (u : prod hreal hreal) (x1 : prod hreal hreal) (y1 : prod hreal hreal) : term53 u x1 y1.
Proof. exact (@lem1337852 x1 y1 u x1 y1). Qed.
Lemma lem1337854 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (u : prod hreal hreal) (h1 : term27 x1 y1 u) : term47 u x1 y1.
Proof. exact (@lem1337853 u x1 y1 (@lem1337846 x1 y1 u h1)). Qed.
Lemma lem1337855 (u : prod hreal hreal) (x1 : prod hreal hreal) (y1 : prod hreal hreal) : term54 u x1 y1.
Proof. exact (fun h0 : term27 x1 y1 u => @lem1337854 x1 y1 u h0). Qed.
Lemma lem1337856 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (u : prod hreal hreal) : term55 x1 y1 u.
Proof. exact (fun h0 : term47 u x1 y1 => @lem1337837 u x1 y1 h0). Qed.
Lemma lem1337857 (u : prod hreal hreal) (x1 : prod hreal hreal) (y1 : prod hreal hreal) : term56 u x1 y1.
Proof. exact (conj (@lem1337856 x1 y1 u) (@lem1337855 u x1 y1)). Qed.
Lemma lem1337858 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (u : prod hreal hreal) : (term56 u x1 y1) = ((term47 u x1 y1) = (term27 x1 y1 u)).
Proof. exact (@lem32 (term47 u x1 y1) (term27 x1 y1 u)). Qed.
Lemma lem1337859 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (u : prod hreal hreal) : (term47 u x1 y1) = (term27 x1 y1 u).
Proof. exact (EQ_MP (@lem1337858 x1 y1 u) (@lem1337857 u x1 y1)). Qed.
Lemma lem1337860 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term57 x1 y1) = (term58 x1 y1).
Proof. exact (fun_ext (fun u : prod hreal hreal => @lem1337859 x1 y1 u)). Qed.
Lemma lem1337861 : mk_real = mk_real.
Proof. exact (eq_refl mk_real). Qed.
Lemma lem1337862 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term22 x1 y1) = (term59 x1 y1).
Proof. exact (MK_COMB (@lem1337861) (@lem1337860 x1 y1)). Qed.
Lemma lem1337863 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term10 x1 y1) = (term59 x1 y1).
Proof. exact (TRANS (@lem1337797 x1 y1) (@lem1337862 x1 y1)). Qed.
Lemma lem1337864 (t : type1233) : (term60 t) = t.
Proof. exact (@lem9127 (prod hreal hreal) Prop t). Qed.
Lemma lem1337867 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term58 x1 y1) = (term61 x1 y1).
Proof. exact (@lem1337864 (term61 x1 y1)). Qed.
Lemma lem1337868 : mk_real = mk_real.
Proof. exact (eq_refl mk_real). Qed.
Lemma lem1337869 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term59 x1 y1) = (term62 x1 y1).
Proof. exact (MK_COMB (@lem1337868) (@lem1337867 x1 y1)). Qed.
Lemma lem1337870 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term63 x1 y1) = (term63 x1 y1).
Proof. exact (eq_refl (term63 x1 y1)). Qed.
Lemma lem1337871 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : ((term10 x1 y1) = (term59 x1 y1)) = ((term10 x1 y1) = (term62 x1 y1)).
Proof. exact (MK_COMB (@lem1337870 x1 y1) (@lem1337869 x1 y1)). Qed.
Lemma lem1337872 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term10 x1 y1) = (term62 x1 y1).
Proof. exact (EQ_MP (@lem1337871 x1 y1) (@lem1337863 x1 y1)). Qed.
