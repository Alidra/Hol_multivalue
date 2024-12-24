Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2305893_term_abbrevs.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Require Import thm2305813_spec.
Lemma lem2305853 (m : real) (n : real) (p : real) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem2305813 n m p)). Qed.
Lemma lem2305854 (m : real) (n : real) : term2 m n.
Proof. exact (fun p : real => @lem2305853 m n p). Qed.
Lemma lem2305855 (m : real) : term3 m.
Proof. exact (fun n : real => @lem2305854 m n). Qed.
Lemma lem2305856 : term4.
Proof. exact (fun m : real => @lem2305855 m). Qed.
Lemma lem2305857 (m : int) : term5 m.
Proof. exact (@lem2305856 (real_of_int m)). Qed.
Lemma lem2305858 (m : int) : (term5 m) = (term6 m).
Proof. exact (eq_refl (term5 m)). Qed.
Lemma lem2305859 (m : int) : term6 m.
Proof. exact (EQ_MP (@lem2305858 m) (@lem2305857 m)). Qed.
Lemma lem2305860 (m : int) (n : int) : term7 m n.
Proof. exact (@lem2305859 m (real_of_int n)). Qed.
Lemma lem2305861 (m : int) (n : int) : (term7 m n) = (term8 m n).
Proof. exact (eq_refl (term7 m n)). Qed.
Lemma lem2305862 (m : int) (n : int) : term8 m n.
Proof. exact (EQ_MP (@lem2305861 m n) (@lem2305860 m n)). Qed.
Lemma lem2305863 (m : int) (n : int) (p : int) : term9 m n p.
Proof. exact (@lem2305862 m n (real_of_int p)). Qed.
Lemma lem2305864 (m : int) (n : int) (p : int) : (term9 m n p) = ((term10 m n p) = (term11 m n p)).
Proof. exact (eq_refl (term9 m n p)). Qed.
Lemma lem2305865 (m : int) (n : int) (p : int) : (term10 m n p) = (term11 m n p).
Proof. exact (EQ_MP (@lem2305864 m n p) (@lem2305863 m n p)). Qed.
Lemma lem2305867 (x : int) (y : int) : (term12 x y) = (term13 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2305868 (m : int) (n : int) : (term12 m n) = (term13 m n).
Proof. exact (@lem2305867 m n). Qed.
Lemma lem2305869 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2305870 (m : int) (n : int) : (term14 m n) = (term15 m n).
Proof. exact (MK_COMB (@lem2305869) (@lem2305868 m n)). Qed.
Lemma lem2305871 (p : int) : (real_of_int p) = (real_of_int p).
Proof. exact (eq_refl (real_of_int p)). Qed.
Lemma lem2305872 (m : int) (n : int) (p : int) : (term10 m n p) = (term16 m n p).
Proof. exact (MK_COMB (@lem2305870 m n) (@lem2305871 p)). Qed.
Lemma lem2305874 (x : int) (y : int) : (term12 x y) = (term13 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2305875 (m : int) (n : int) (p : int) : (term16 m n p) = (term17 m n p).
Proof. exact (@lem2305874 (int_mul m n) p). Qed.
Lemma lem2305876 (m : int) (n : int) (p : int) : (term10 m n p) = (term17 m n p).
Proof. exact (TRANS (@lem2305872 m n p) (@lem2305875 m n p)). Qed.
Lemma lem2305877 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2305878 (m : int) (n : int) (p : int) : (term18 m n p) = (term19 m n p).
Proof. exact (MK_COMB (@lem2305877) (@lem2305876 m n p)). Qed.
Lemma lem2305880 (x : int) (y : int) : (term12 x y) = (term13 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2305881 (n : int) (p : int) : (term12 n p) = (term13 n p).
Proof. exact (@lem2305880 n p). Qed.
Lemma lem2305882 (m : int) : (term20 m) = (term20 m).
Proof. exact (eq_refl (term20 m)). Qed.
Lemma lem2305883 (m : int) (n : int) (p : int) : (term11 m n p) = (term21 m n p).
Proof. exact (MK_COMB (@lem2305882 m) (@lem2305881 n p)). Qed.
Lemma lem2305885 (x : int) (y : int) : (term12 x y) = (term13 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2305886 (m : int) (n : int) (p : int) : (term21 m n p) = (term22 m n p).
Proof. exact (@lem2305885 m (int_mul n p)). Qed.
Lemma lem2305887 (m : int) (n : int) (p : int) : (term11 m n p) = (term22 m n p).
Proof. exact (TRANS (@lem2305883 m n p) (@lem2305886 m n p)). Qed.
Lemma lem2305888 (m : int) (n : int) (p : int) : ((term10 m n p) = (term11 m n p)) = ((term17 m n p) = (term22 m n p)).
Proof. exact (MK_COMB (@lem2305878 m n p) (@lem2305887 m n p)). Qed.
Lemma lem2305890 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2305891 (m : int) (n : int) (p : int) : ((term17 m n p) = (term22 m n p)) = ((term23 m n p) = (term24 m n p)).
Proof. exact (@lem2305890 (term23 m n p) (term24 m n p)). Qed.
Lemma lem2305892 (m : int) (n : int) (p : int) : ((term10 m n p) = (term11 m n p)) = ((term23 m n p) = (term24 m n p)).
Proof. exact (TRANS (@lem2305888 m n p) (@lem2305891 m n p)). Qed.
Lemma lem2305893 (m : int) (n : int) (p : int) : (term23 m n p) = (term24 m n p).
Proof. exact (EQ_MP (@lem2305892 m n p) (@lem2305865 m n p)). Qed.
