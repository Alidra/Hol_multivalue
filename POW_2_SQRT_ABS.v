Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import POW_2_SQRT_ABS_term_abbrevs.
Require Import REAL_ABS_MUL_spec.
Require Import REAL_ABS_POS_spec.
Require Import REAL_LE_SQUARE_spec.
Require Import REAL_POW_2_spec.
Require Import SQRT_UNIQUE_spec.
Require Import real_abs_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Lemma lem1902756 (x : real) : term0 x.
Proof. exact (@lem1382902 x). Qed.
Lemma lem1902757 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1902758 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1902757 x) (@lem1902756 x)). Qed.
Lemma lem1902759 (x : real) : (term1 x) = ((term1 x) = True).
Proof. exact (@lem7 (term1 x)). Qed.
Lemma lem1902761 (x : real) : term2 x.
Proof. exact (@lem1343359 x). Qed.
Lemma lem1902762 (x : real) : (term2 x) = ((real_abs x) = (term3 x)).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem1902766 (x : real) (y : real) (h1 : (term4 x y) = (term5 x y)) : (term4 x y) = (term5 x y).
Proof. exact (h1). Qed.
Lemma lem1902767 (x : real) (y : real) (h1 : (term4 x y) = (term5 x y)) : (term5 x y) = (term4 x y).
Proof. exact (SYM (@lem1902766 x y h1)). Qed.
Lemma lem1902768 (x : real) (y : real) (h1 : (term5 x y) = (term4 x y)) : (term5 x y) = (term4 x y).
Proof. exact (h1). Qed.
Lemma lem1902769 (x : real) (y : real) (h1 : (term5 x y) = (term4 x y)) : (term4 x y) = (term5 x y).
Proof. exact (SYM (@lem1902768 x y h1)). Qed.
Lemma lem1902770 (x : real) (y : real) : ((term4 x y) = (term5 x y)) = ((term5 x y) = (term4 x y)).
Proof. exact (prop_ext (fun h1 : (term4 x y) = (term5 x y) => @lem1902767 x y h1) (fun h1 : (term5 x y) = (term4 x y) => @lem1902769 x y h1)). Qed.
Lemma lem1902771 (x : real) : (term6 x) = (term7 x).
Proof. exact (fun_ext (fun y : real => @lem1902770 x y)). Qed.
Lemma lem1902772 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1902773 (x : real) : (term8 x) = (term9 x).
Proof. exact (MK_COMB (@lem1902772) (@lem1902771 x)). Qed.
Lemma lem1902774 : term10 = term11.
Proof. exact (fun_ext (fun x : real => @lem1902773 x)). Qed.
Lemma lem1902775 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1902776 : term12 = term13.
Proof. exact (MK_COMB (@lem1902775) (@lem1902774)). Qed.
Lemma lem1902777 : term13.
Proof. exact (EQ_MP (@lem1902776) (@lem1582313)). Qed.
Lemma lem1902778 (x : real) : term14 x.
Proof. exact (@lem1902777 x). Qed.
Lemma lem1902779 (x : real) : (term14 x) = (term9 x).
Proof. exact (eq_refl (term14 x)). Qed.
Lemma lem1902780 (x : real) : term9 x.
Proof. exact (EQ_MP (@lem1902779 x) (@lem1902778 x)). Qed.
Lemma lem1902781 (x : real) (y : real) : term15 x y.
Proof. exact (@lem1902780 x y). Qed.
Lemma lem1902782 (x : real) (y : real) : (term15 x y) = ((term5 x y) = (term4 x y)).
Proof. exact (eq_refl (term15 x y)). Qed.
Lemma lem1902784 (x : real) : term16 x.
Proof. exact (@lem1383497 x). Qed.
Lemma lem1902785 (x : real) : (term16 x) = ((term17 x) = (real_mul x x)).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1902787 (x : real) : term18 x.
Proof. exact (@lem1532076 x). Qed.
Lemma lem1902788 (x : real) : (term18 x) = (term19 x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem1902789 (x : real) : term19 x.
Proof. exact (EQ_MP (@lem1902788 x) (@lem1902787 x)). Qed.
Lemma lem1902790 (x : real) : (term19 x) = ((term19 x) = True).
Proof. exact (@lem7 (term19 x)). Qed.
Lemma lem1902792 (h1 : term20) : term20.
Proof. exact (h1). Qed.
Lemma lem1902793 (x : real) (h1 : term20) : term21 x.
Proof. exact (@lem1902792 h1 x). Qed.
Lemma lem1902794 (x : real) : (term21 x) = (term22 x).
Proof. exact (eq_refl (term21 x)). Qed.
Lemma lem1902795 (x : real) (h1 : term20) : term22 x.
Proof. exact (EQ_MP (@lem1902794 x) (@lem1902793 x h1)). Qed.
Lemma lem1902796 (x : real) (y : real) (h1 : term20) : term23 x y.
Proof. exact (@lem1902795 x h1 y). Qed.
Lemma lem1902797 (x : real) (y : real) : (term23 x y) = (term24 x y).
Proof. exact (eq_refl (term23 x y)). Qed.
Lemma lem1902798 (x : real) (y : real) (h1 : term20) : term24 x y.
Proof. exact (EQ_MP (@lem1902797 x y) (@lem1902796 x y h1)). Qed.
Lemma lem1902799 (y : real) (x : real) (h1 : term25 y x) : term25 y x.
Proof. exact (h1). Qed.
Lemma lem1902800 (y : real) (x : real) (h1 : term20) (h2 : term25 y x) : (sqrt x) = y.
Proof. exact (@lem1902798 x y h1 (@lem1902799 y x h2)). Qed.
Lemma lem1902801 (y : real) (x : real) (h1 : term25 y x) : term26 x y.
Proof. exact (fun h0 : term20 => @lem1902800 y x h0 h1). Qed.
Lemma lem1902802 (h1 : term20) : term20.
Proof. exact (h1). Qed.
Lemma lem1902803 (y : real) (x : real) (h1 : term20) (h2 : term25 y x) : (sqrt x) = y.
Proof. exact (@lem1902801 y x h2 (@lem1902802 h1)). Qed.
Lemma lem1902804 (x : real) (y : real) (h1 : term20) : term24 x y.
Proof. exact (fun h0 : term25 y x => @lem1902803 y x h1 h0). Qed.
Lemma lem1902805 (x : real) (h1 : term20) : term22 x.
Proof. exact (fun y : real => @lem1902804 x y h1). Qed.
Lemma lem1902806 (h1 : term20) : term20.
Proof. exact (fun x : real => @lem1902805 x h1). Qed.
Lemma lem1902807 : term27.
Proof. exact (fun h0 : term20 => @lem1902806 h0). Qed.
Lemma lem1902808 : term20.
Proof. exact (@lem1902807 (@lem1900060)). Qed.
Lemma lem1902809 (x : real) : term21 x.
Proof. exact (@lem1902808 x). Qed.
Lemma lem1902810 (x : real) : (term21 x) = (term22 x).
Proof. exact (eq_refl (term21 x)). Qed.
Lemma lem1902811 (x : real) : term22 x.
Proof. exact (EQ_MP (@lem1902810 x) (@lem1902809 x)). Qed.
Lemma lem1902812 (x : real) (y : real) : term23 x y.
Proof. exact (@lem1902811 x y). Qed.
Lemma lem1902813 (x : real) (y : real) : (term23 x y) = (term24 x y).
Proof. exact (eq_refl (term23 x y)). Qed.
Lemma lem1902816 (x : real) (y : real) : term24 x y.
Proof. exact (EQ_MP (@lem1902813 x y) (@lem1902812 x y)). Qed.
Lemma lem1902817 (x : real) : term28 x.
Proof. exact (@lem1902816 (term17 x) (real_abs x)). Qed.
Lemma lem1902821 (x : real) : (term19 x) = True.
Proof. exact (EQ_MP (@lem1902790 x) (@lem1902789 x)). Qed.
Lemma lem1902822 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1902823 (x : real) : (term29 x) = (and True).
Proof. exact (MK_COMB (@lem1902822) (@lem1902821 x)). Qed.
Lemma lem1902827 (x : real) : (term17 x) = (real_mul x x).
Proof. exact (EQ_MP (@lem1902785 x) (@lem1902784 x)). Qed.
Lemma lem1902828 (x : real) : (term30 x) = (term31 x).
Proof. exact (@lem1902827 (real_abs x)). Qed.
Lemma lem1902830 (x : real) (y : real) : (term5 x y) = (term4 x y).
Proof. exact (EQ_MP (@lem1902782 x y) (@lem1902781 x y)). Qed.
Lemma lem1902831 (x : real) : (term31 x) = (term32 x).
Proof. exact (@lem1902830 x x). Qed.
Lemma lem1902832 (x : real) : (term30 x) = (term32 x).
Proof. exact (TRANS (@lem1902828 x) (@lem1902831 x)). Qed.
Lemma lem1902833 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1902834 (x : real) : (term33 x) = (term34 x).
Proof. exact (MK_COMB (@lem1902833) (@lem1902832 x)). Qed.
Lemma lem1902836 (x : real) : (term17 x) = (real_mul x x).
Proof. exact (EQ_MP (@lem1902785 x) (@lem1902784 x)). Qed.
Lemma lem1902837 (x : real) : ((term30 x) = (term17 x)) = ((term32 x) = (real_mul x x)).
Proof. exact (MK_COMB (@lem1902834 x) (@lem1902836 x)). Qed.
Lemma lem1902840 (x : real) : (term35 x) = (term36 x).
Proof. exact (MK_COMB (@lem1902823 x) (@lem1902837 x)). Qed.
Lemma lem1902842 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1902843 (x : real) : (term36 x) = ((term32 x) = (real_mul x x)).
Proof. exact (@lem1902842 ((term32 x) = (real_mul x x))). Qed.
Lemma lem1902846 (x : real) : (term35 x) = ((term32 x) = (real_mul x x)).
Proof. exact (TRANS (@lem1902840 x) (@lem1902843 x)). Qed.
Lemma lem1902847 (x : real) : ((term32 x) = (real_mul x x)) = (term35 x).
Proof. exact (SYM (@lem1902846 x)). Qed.
Lemma lem1902851 (x : real) : (real_abs x) = (term3 x).
Proof. exact (EQ_MP (@lem1902762 x) (@lem1902761 x)). Qed.
Lemma lem1902852 (x : real) : (term32 x) = (term37 x).
Proof. exact (@lem1902851 (real_mul x x)). Qed.
Lemma lem1902854 (x : real) : (term1 x) = True.
Proof. exact (EQ_MP (@lem1902759 x) (@lem1902758 x)). Qed.
Lemma lem1902855 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1902856 (x : real) : (term38 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1902855) (@lem1902854 x)). Qed.
Lemma lem1902857 (x : real) : (real_mul x x) = (real_mul x x).
Proof. exact (eq_refl (real_mul x x)). Qed.
Lemma lem1902858 (x : real) : (term39 x) = (term40 x).
Proof. exact (MK_COMB (@lem1902856 x) (@lem1902857 x)). Qed.
Lemma lem1902859 (x : real) : (term41 x) = (term41 x).
Proof. exact (eq_refl (term41 x)). Qed.
Lemma lem1902860 (x : real) : (term37 x) = (term42 x).
Proof. exact (MK_COMB (@lem1902858 x) (@lem1902859 x)). Qed.
Lemma lem1902862 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1902863 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1902862 real t2 t1). Qed.
Lemma lem1902864 (x : real) : (term42 x) = (real_mul x x).
Proof. exact (@lem1902863 (term41 x) (real_mul x x)). Qed.
Lemma lem1902865 (x : real) : (term37 x) = (real_mul x x).
Proof. exact (TRANS (@lem1902860 x) (@lem1902864 x)). Qed.
Lemma lem1902866 (x : real) : (term32 x) = (real_mul x x).
Proof. exact (TRANS (@lem1902852 x) (@lem1902865 x)). Qed.
Lemma lem1902867 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1902868 (x : real) : (term34 x) = (term43 x).
Proof. exact (MK_COMB (@lem1902867) (@lem1902866 x)). Qed.
Lemma lem1902869 (x : real) : (real_mul x x) = (real_mul x x).
Proof. exact (eq_refl (real_mul x x)). Qed.
Lemma lem1902870 (x : real) : ((term32 x) = (real_mul x x)) = ((real_mul x x) = (real_mul x x)).
Proof. exact (MK_COMB (@lem1902868 x) (@lem1902869 x)). Qed.
Lemma lem1902872 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1902873 (x : real) : (x = x) = True.
Proof. exact (@lem1902872 real x). Qed.
Lemma lem1902874 (x : real) : ((real_mul x x) = (real_mul x x)) = True.
Proof. exact (@lem1902873 (real_mul x x)). Qed.
Lemma lem1902875 (x : real) : ((term32 x) = (real_mul x x)) = True.
Proof. exact (TRANS (@lem1902870 x) (@lem1902874 x)). Qed.
Lemma lem1902876 (x : real) : True = ((term32 x) = (real_mul x x)).
Proof. exact (SYM (@lem1902875 x)). Qed.
Lemma lem1902877 (x : real) : (term32 x) = (real_mul x x).
Proof. exact (EQ_MP (@lem1902876 x) (@lem0)). Qed.
Lemma lem1902878 (x : real) : term35 x.
Proof. exact (EQ_MP (@lem1902847 x) (@lem1902877 x)). Qed.
Lemma lem1902879 (x : real) : (term44 x) = (real_abs x).
Proof. exact (@lem1902817 x (@lem1902878 x)). Qed.
Lemma lem1902884 : term45.
Proof. exact (fun x : real => @lem1902879 x). Qed.
