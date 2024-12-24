Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2301003_term_abbrevs.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Require Import thm2300923_spec.
Lemma lem2300963 (m : real) (n : real) (p : real) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem2300923 n m p)). Qed.
Lemma lem2300964 (m : real) (n : real) : term2 m n.
Proof. exact (fun p : real => @lem2300963 m n p). Qed.
Lemma lem2300965 (m : real) : term3 m.
Proof. exact (fun n : real => @lem2300964 m n). Qed.
Lemma lem2300966 : term4.
Proof. exact (fun m : real => @lem2300965 m). Qed.
Lemma lem2300967 (m : int) : term5 m.
Proof. exact (@lem2300966 (real_of_int m)). Qed.
Lemma lem2300968 (m : int) : (term5 m) = (term6 m).
Proof. exact (eq_refl (term5 m)). Qed.
Lemma lem2300969 (m : int) : term6 m.
Proof. exact (EQ_MP (@lem2300968 m) (@lem2300967 m)). Qed.
Lemma lem2300970 (m : int) (n : int) : term7 m n.
Proof. exact (@lem2300969 m (real_of_int n)). Qed.
Lemma lem2300971 (m : int) (n : int) : (term7 m n) = (term8 m n).
Proof. exact (eq_refl (term7 m n)). Qed.
Lemma lem2300972 (m : int) (n : int) : term8 m n.
Proof. exact (EQ_MP (@lem2300971 m n) (@lem2300970 m n)). Qed.
Lemma lem2300973 (m : int) (n : int) (p : int) : term9 m n p.
Proof. exact (@lem2300972 m n (real_of_int p)). Qed.
Lemma lem2300974 (m : int) (n : int) (p : int) : (term9 m n p) = ((term10 m n p) = (term11 m n p)).
Proof. exact (eq_refl (term9 m n p)). Qed.
Lemma lem2300975 (m : int) (n : int) (p : int) : (term10 m n p) = (term11 m n p).
Proof. exact (EQ_MP (@lem2300974 m n p) (@lem2300973 m n p)). Qed.
Lemma lem2300977 (x : int) (y : int) : (term12 x y) = (term13 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2300978 (m : int) (n : int) : (term12 m n) = (term13 m n).
Proof. exact (@lem2300977 m n). Qed.
Lemma lem2300979 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2300980 (m : int) (n : int) : (term14 m n) = (term15 m n).
Proof. exact (MK_COMB (@lem2300979) (@lem2300978 m n)). Qed.
Lemma lem2300981 (p : int) : (real_of_int p) = (real_of_int p).
Proof. exact (eq_refl (real_of_int p)). Qed.
Lemma lem2300982 (m : int) (n : int) (p : int) : (term10 m n p) = (term16 m n p).
Proof. exact (MK_COMB (@lem2300980 m n) (@lem2300981 p)). Qed.
Lemma lem2300984 (x : int) (y : int) : (term12 x y) = (term13 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2300985 (m : int) (n : int) (p : int) : (term16 m n p) = (term17 m n p).
Proof. exact (@lem2300984 (int_add m n) p). Qed.
Lemma lem2300986 (m : int) (n : int) (p : int) : (term10 m n p) = (term17 m n p).
Proof. exact (TRANS (@lem2300982 m n p) (@lem2300985 m n p)). Qed.
Lemma lem2300987 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2300988 (m : int) (n : int) (p : int) : (term18 m n p) = (term19 m n p).
Proof. exact (MK_COMB (@lem2300987) (@lem2300986 m n p)). Qed.
Lemma lem2300990 (x : int) (y : int) : (term12 x y) = (term13 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2300991 (n : int) (p : int) : (term12 n p) = (term13 n p).
Proof. exact (@lem2300990 n p). Qed.
Lemma lem2300992 (m : int) : (term20 m) = (term20 m).
Proof. exact (eq_refl (term20 m)). Qed.
Lemma lem2300993 (m : int) (n : int) (p : int) : (term11 m n p) = (term21 m n p).
Proof. exact (MK_COMB (@lem2300992 m) (@lem2300991 n p)). Qed.
Lemma lem2300995 (x : int) (y : int) : (term12 x y) = (term13 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2300996 (m : int) (n : int) (p : int) : (term21 m n p) = (term22 m n p).
Proof. exact (@lem2300995 m (int_add n p)). Qed.
Lemma lem2300997 (m : int) (n : int) (p : int) : (term11 m n p) = (term22 m n p).
Proof. exact (TRANS (@lem2300993 m n p) (@lem2300996 m n p)). Qed.
Lemma lem2300998 (m : int) (n : int) (p : int) : ((term10 m n p) = (term11 m n p)) = ((term17 m n p) = (term22 m n p)).
Proof. exact (MK_COMB (@lem2300988 m n p) (@lem2300997 m n p)). Qed.
Lemma lem2301000 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301001 (m : int) (n : int) (p : int) : ((term17 m n p) = (term22 m n p)) = ((term23 m n p) = (term24 m n p)).
Proof. exact (@lem2301000 (term23 m n p) (term24 m n p)). Qed.
Lemma lem2301002 (m : int) (n : int) (p : int) : ((term10 m n p) = (term11 m n p)) = ((term23 m n p) = (term24 m n p)).
Proof. exact (TRANS (@lem2300998 m n p) (@lem2301001 m n p)). Qed.
Lemma lem2301003 (m : int) (n : int) (p : int) : (term23 m n p) = (term24 m n p).
Proof. exact (EQ_MP (@lem2301002 m n p) (@lem2300975 m n p)). Qed.
