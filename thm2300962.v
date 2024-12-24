Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2300962_term_abbrevs.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Require Import thm2300923_spec.
Lemma lem2300924 (n : real) (m : real) (p : real) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem2300923 n m p)). Qed.
Lemma lem2300925 (n : real) (m : real) : term1 n m.
Proof. exact (fun p : real => @lem2300924 n m p). Qed.
Lemma lem2300926 (n : real) : term2 n.
Proof. exact (fun m : real => @lem2300925 n m). Qed.
Lemma lem2300927 : term3.
Proof. exact (fun n : real => @lem2300926 n). Qed.
Lemma lem2300928 (n : int) : term4 n.
Proof. exact (@lem2300927 (real_of_int n)). Qed.
Lemma lem2300929 (n : int) : (term4 n) = (term5 n).
Proof. exact (eq_refl (term4 n)). Qed.
Lemma lem2300930 (n : int) : term5 n.
Proof. exact (EQ_MP (@lem2300929 n) (@lem2300928 n)). Qed.
Lemma lem2300931 (n : int) (m : int) : term6 n m.
Proof. exact (@lem2300930 n (real_of_int m)). Qed.
Lemma lem2300932 (n : int) (m : int) : (term6 n m) = (term7 n m).
Proof. exact (eq_refl (term6 n m)). Qed.
Lemma lem2300933 (n : int) (m : int) : term7 n m.
Proof. exact (EQ_MP (@lem2300932 n m) (@lem2300931 n m)). Qed.
Lemma lem2300934 (n : int) (m : int) (p : int) : term8 n m p.
Proof. exact (@lem2300933 n m (real_of_int p)). Qed.
Lemma lem2300935 (n : int) (m : int) (p : int) : (term8 n m p) = ((term9 m n p) = (term9 n m p)).
Proof. exact (eq_refl (term8 n m p)). Qed.
Lemma lem2300936 (n : int) (m : int) (p : int) : (term9 m n p) = (term9 n m p).
Proof. exact (EQ_MP (@lem2300935 n m p) (@lem2300934 n m p)). Qed.
Lemma lem2300938 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2300939 (n : int) (p : int) : (term10 n p) = (term11 n p).
Proof. exact (@lem2300938 n p). Qed.
Lemma lem2300940 (m : int) : (term12 m) = (term12 m).
Proof. exact (eq_refl (term12 m)). Qed.
Lemma lem2300941 (m : int) (n : int) (p : int) : (term9 m n p) = (term13 m n p).
Proof. exact (MK_COMB (@lem2300940 m) (@lem2300939 n p)). Qed.
Lemma lem2300943 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2300944 (m : int) (n : int) (p : int) : (term13 m n p) = (term14 m n p).
Proof. exact (@lem2300943 m (int_add n p)). Qed.
Lemma lem2300945 (m : int) (n : int) (p : int) : (term9 m n p) = (term14 m n p).
Proof. exact (TRANS (@lem2300941 m n p) (@lem2300944 m n p)). Qed.
Lemma lem2300946 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2300947 (m : int) (n : int) (p : int) : (term15 m n p) = (term16 m n p).
Proof. exact (MK_COMB (@lem2300946) (@lem2300945 m n p)). Qed.
Lemma lem2300949 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2300950 (m : int) (p : int) : (term10 m p) = (term11 m p).
Proof. exact (@lem2300949 m p). Qed.
Lemma lem2300951 (n : int) : (term12 n) = (term12 n).
Proof. exact (eq_refl (term12 n)). Qed.
Lemma lem2300952 (n : int) (m : int) (p : int) : (term9 n m p) = (term13 n m p).
Proof. exact (MK_COMB (@lem2300951 n) (@lem2300950 m p)). Qed.
Lemma lem2300954 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2300955 (n : int) (m : int) (p : int) : (term13 n m p) = (term14 n m p).
Proof. exact (@lem2300954 n (int_add m p)). Qed.
Lemma lem2300956 (n : int) (m : int) (p : int) : (term9 n m p) = (term14 n m p).
Proof. exact (TRANS (@lem2300952 n m p) (@lem2300955 n m p)). Qed.
Lemma lem2300957 (n : int) (m : int) (p : int) : ((term9 m n p) = (term9 n m p)) = ((term14 m n p) = (term14 n m p)).
Proof. exact (MK_COMB (@lem2300947 m n p) (@lem2300956 n m p)). Qed.
Lemma lem2300959 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2300960 (n : int) (m : int) (p : int) : ((term14 m n p) = (term14 n m p)) = ((term17 m n p) = (term17 n m p)).
Proof. exact (@lem2300959 (term17 m n p) (term17 n m p)). Qed.
Lemma lem2300961 (n : int) (m : int) (p : int) : ((term9 m n p) = (term9 n m p)) = ((term17 m n p) = (term17 n m p)).
Proof. exact (TRANS (@lem2300957 n m p) (@lem2300960 n m p)). Qed.
Lemma lem2300962 (n : int) (m : int) (p : int) : (term17 m n p) = (term17 n m p).
Proof. exact (EQ_MP (@lem2300961 n m p) (@lem2300936 n m p)). Qed.
