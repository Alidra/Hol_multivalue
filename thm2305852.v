Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2305852_term_abbrevs.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Require Import thm2305813_spec.
Lemma lem2305814 (n : real) (m : real) (p : real) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem2305813 n m p)). Qed.
Lemma lem2305815 (n : real) (m : real) : term1 n m.
Proof. exact (fun p : real => @lem2305814 n m p). Qed.
Lemma lem2305816 (n : real) : term2 n.
Proof. exact (fun m : real => @lem2305815 n m). Qed.
Lemma lem2305817 : term3.
Proof. exact (fun n : real => @lem2305816 n). Qed.
Lemma lem2305818 (n : int) : term4 n.
Proof. exact (@lem2305817 (real_of_int n)). Qed.
Lemma lem2305819 (n : int) : (term4 n) = (term5 n).
Proof. exact (eq_refl (term4 n)). Qed.
Lemma lem2305820 (n : int) : term5 n.
Proof. exact (EQ_MP (@lem2305819 n) (@lem2305818 n)). Qed.
Lemma lem2305821 (n : int) (m : int) : term6 n m.
Proof. exact (@lem2305820 n (real_of_int m)). Qed.
Lemma lem2305822 (n : int) (m : int) : (term6 n m) = (term7 n m).
Proof. exact (eq_refl (term6 n m)). Qed.
Lemma lem2305823 (n : int) (m : int) : term7 n m.
Proof. exact (EQ_MP (@lem2305822 n m) (@lem2305821 n m)). Qed.
Lemma lem2305824 (n : int) (m : int) (p : int) : term8 n m p.
Proof. exact (@lem2305823 n m (real_of_int p)). Qed.
Lemma lem2305825 (n : int) (m : int) (p : int) : (term8 n m p) = ((term9 m n p) = (term9 n m p)).
Proof. exact (eq_refl (term8 n m p)). Qed.
Lemma lem2305826 (n : int) (m : int) (p : int) : (term9 m n p) = (term9 n m p).
Proof. exact (EQ_MP (@lem2305825 n m p) (@lem2305824 n m p)). Qed.
Lemma lem2305828 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2305829 (n : int) (p : int) : (term10 n p) = (term11 n p).
Proof. exact (@lem2305828 n p). Qed.
Lemma lem2305830 (m : int) : (term12 m) = (term12 m).
Proof. exact (eq_refl (term12 m)). Qed.
Lemma lem2305831 (m : int) (n : int) (p : int) : (term9 m n p) = (term13 m n p).
Proof. exact (MK_COMB (@lem2305830 m) (@lem2305829 n p)). Qed.
Lemma lem2305833 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2305834 (m : int) (n : int) (p : int) : (term13 m n p) = (term14 m n p).
Proof. exact (@lem2305833 m (int_mul n p)). Qed.
Lemma lem2305835 (m : int) (n : int) (p : int) : (term9 m n p) = (term14 m n p).
Proof. exact (TRANS (@lem2305831 m n p) (@lem2305834 m n p)). Qed.
Lemma lem2305836 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2305837 (m : int) (n : int) (p : int) : (term15 m n p) = (term16 m n p).
Proof. exact (MK_COMB (@lem2305836) (@lem2305835 m n p)). Qed.
Lemma lem2305839 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2305840 (m : int) (p : int) : (term10 m p) = (term11 m p).
Proof. exact (@lem2305839 m p). Qed.
Lemma lem2305841 (n : int) : (term12 n) = (term12 n).
Proof. exact (eq_refl (term12 n)). Qed.
Lemma lem2305842 (n : int) (m : int) (p : int) : (term9 n m p) = (term13 n m p).
Proof. exact (MK_COMB (@lem2305841 n) (@lem2305840 m p)). Qed.
Lemma lem2305844 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2305845 (n : int) (m : int) (p : int) : (term13 n m p) = (term14 n m p).
Proof. exact (@lem2305844 n (int_mul m p)). Qed.
Lemma lem2305846 (n : int) (m : int) (p : int) : (term9 n m p) = (term14 n m p).
Proof. exact (TRANS (@lem2305842 n m p) (@lem2305845 n m p)). Qed.
Lemma lem2305847 (n : int) (m : int) (p : int) : ((term9 m n p) = (term9 n m p)) = ((term14 m n p) = (term14 n m p)).
Proof. exact (MK_COMB (@lem2305837 m n p) (@lem2305846 n m p)). Qed.
Lemma lem2305849 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2305850 (n : int) (m : int) (p : int) : ((term14 m n p) = (term14 n m p)) = ((term17 m n p) = (term17 n m p)).
Proof. exact (@lem2305849 (term17 m n p) (term17 n m p)). Qed.
Lemma lem2305851 (n : int) (m : int) (p : int) : ((term9 m n p) = (term9 n m p)) = ((term17 m n p) = (term17 n m p)).
Proof. exact (TRANS (@lem2305847 n m p) (@lem2305850 n m p)). Qed.
Lemma lem2305852 (n : int) (m : int) (p : int) : (term17 m n p) = (term17 n m p).
Proof. exact (EQ_MP (@lem2305851 n m p) (@lem2305826 n m p)). Qed.
