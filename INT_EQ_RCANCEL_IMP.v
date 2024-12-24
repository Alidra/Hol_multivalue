Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_EQ_RCANCEL_IMP_term_abbrevs.
Require Import REAL_EQ_RCANCEL_IMP_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2301781 (x : int) : term0 x.
Proof. exact (@lem1640771 (real_of_int x)). Qed.
Lemma lem2301782 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2301783 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2301782 x) (@lem2301781 x)). Qed.
Lemma lem2301784 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2301783 x (real_of_int y)). Qed.
Lemma lem2301785 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2301786 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2301785 x y) (@lem2301784 x y)). Qed.
Lemma lem2301787 (x : int) (y : int) (z : int) : term4 x y z.
Proof. exact (@lem2301786 x y (real_of_int z)). Qed.
Lemma lem2301788 (z : int) (x : int) (y : int) : (term4 x y z) = (term5 z x y).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem2301789 (z : int) (x : int) (y : int) : term5 z x y.
Proof. exact (EQ_MP (@lem2301788 z x y) (@lem2301787 x y z)). Qed.
Lemma lem2301791 (n : nat) : (real_of_num n) = (term6 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2301792 : term7 = term8.
Proof. exact (@lem2301791 (NUMERAL 0)). Qed.
Lemma lem2301793 (z : int) : (term9 z) = (term9 z).
Proof. exact (eq_refl (term9 z)). Qed.
Lemma lem2301794 (z : int) : ((real_of_int z) = term7) = ((real_of_int z) = term8).
Proof. exact (MK_COMB (@lem2301793 z) (@lem2301792)). Qed.
Lemma lem2301796 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301797 (z : int) : ((real_of_int z) = term8) = (z = term10).
Proof. exact (@lem2301796 z term10). Qed.
Lemma lem2301798 (z : int) : ((real_of_int z) = term7) = (z = term10).
Proof. exact (TRANS (@lem2301794 z) (@lem2301797 z)). Qed.
Lemma lem2301799 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2301800 (z : int) : (term11 z) = (term12 z).
Proof. exact (MK_COMB (@lem2301799) (@lem2301798 z)). Qed.
Lemma lem2301801 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2301802 (z : int) : (term13 z) = (term14 z).
Proof. exact (MK_COMB (@lem2301801) (@lem2301800 z)). Qed.
Lemma lem2301804 (x : int) (y : int) : (term15 x y) = (term16 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2301805 (x : int) (z : int) : (term15 x z) = (term16 x z).
Proof. exact (@lem2301804 x z). Qed.
Lemma lem2301806 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2301807 (x : int) (z : int) : (term17 x z) = (term18 x z).
Proof. exact (MK_COMB (@lem2301806) (@lem2301805 x z)). Qed.
Lemma lem2301809 (x : int) (y : int) : (term15 x y) = (term16 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2301810 (y : int) (z : int) : (term15 y z) = (term16 y z).
Proof. exact (@lem2301809 y z). Qed.
Lemma lem2301811 (x : int) (y : int) (z : int) : ((term15 x z) = (term15 y z)) = ((term16 x z) = (term16 y z)).
Proof. exact (MK_COMB (@lem2301807 x z) (@lem2301810 y z)). Qed.
Lemma lem2301813 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301814 (x : int) (y : int) (z : int) : ((term16 x z) = (term16 y z)) = ((int_mul x z) = (int_mul y z)).
Proof. exact (@lem2301813 (int_mul x z) (int_mul y z)). Qed.
Lemma lem2301815 (x : int) (y : int) (z : int) : ((term15 x z) = (term15 y z)) = ((int_mul x z) = (int_mul y z)).
Proof. exact (TRANS (@lem2301811 x y z) (@lem2301814 x y z)). Qed.
Lemma lem2301816 (x : int) (y : int) (z : int) : (term19 x y z) = (term20 x y z).
Proof. exact (MK_COMB (@lem2301802 z) (@lem2301815 x y z)). Qed.
Lemma lem2301817 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2301818 (x : int) (y : int) (z : int) : (term21 x y z) = (term22 x y z).
Proof. exact (MK_COMB (@lem2301817) (@lem2301816 x y z)). Qed.
Lemma lem2301820 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301821 (z : int) (x : int) (y : int) : (term5 z x y) = (term23 z x y).
Proof. exact (MK_COMB (@lem2301818 x y z) (@lem2301820 x y)). Qed.
Lemma lem2301822 (z : int) (x : int) (y : int) : term23 z x y.
Proof. exact (EQ_MP (@lem2301821 z x y) (@lem2301789 z x y)). Qed.
Lemma lem2301823 (x : int) (y : int) : term24 x y.
Proof. exact (fun z : int => @lem2301822 z x y). Qed.
Lemma lem2301824 (x : int) : term25 x.
Proof. exact (fun y : int => @lem2301823 x y). Qed.
Lemma lem2301825 : term26.
Proof. exact (fun x : int => @lem2301824 x). Qed.
