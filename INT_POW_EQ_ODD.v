Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_POW_EQ_ODD_term_abbrevs.
Require Import REAL_POW_EQ_ODD_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2308056 (n : nat) : term0 n.
Proof. exact (@lem1666511 n). Qed.
Lemma lem2308057 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem2308058 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem2308057 n) (@lem2308056 n)). Qed.
Lemma lem2308059 (n : nat) (x : int) : term2 n x.
Proof. exact (@lem2308058 n (real_of_int x)). Qed.
Lemma lem2308060 (n : nat) (x : int) : (term2 n x) = (term3 n x).
Proof. exact (eq_refl (term2 n x)). Qed.
Lemma lem2308061 (n : nat) (x : int) : term3 n x.
Proof. exact (EQ_MP (@lem2308060 n x) (@lem2308059 n x)). Qed.
Lemma lem2308062 (n : nat) (x : int) (y : int) : term4 n x y.
Proof. exact (@lem2308061 n x (real_of_int y)). Qed.
Lemma lem2308063 (n : nat) (x : int) (y : int) : (term4 n x y) = (term5 n x y).
Proof. exact (eq_refl (term4 n x y)). Qed.
Lemma lem2308064 (n : nat) (x : int) (y : int) : term5 n x y.
Proof. exact (EQ_MP (@lem2308063 n x y) (@lem2308062 n x y)). Qed.
Lemma lem2308066 (x : int) (n : nat) : (term6 x n) = (term7 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2308067 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2308068 (x : int) (n : nat) : (term8 x n) = (term9 x n).
Proof. exact (MK_COMB (@lem2308067) (@lem2308066 x n)). Qed.
Lemma lem2308070 (x : int) (n : nat) : (term6 x n) = (term7 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2308071 (y : int) (n : nat) : (term6 y n) = (term7 y n).
Proof. exact (@lem2308070 y n). Qed.
Lemma lem2308072 (x : int) (y : int) (n : nat) : ((term6 x n) = (term6 y n)) = ((term7 x n) = (term7 y n)).
Proof. exact (MK_COMB (@lem2308068 x n) (@lem2308071 y n)). Qed.
Lemma lem2308074 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2308075 (x : int) (y : int) (n : nat) : ((term7 x n) = (term7 y n)) = ((int_pow x n) = (int_pow y n)).
Proof. exact (@lem2308074 (int_pow x n) (int_pow y n)). Qed.
Lemma lem2308076 (x : int) (y : int) (n : nat) : ((term6 x n) = (term6 y n)) = ((int_pow x n) = (int_pow y n)).
Proof. exact (TRANS (@lem2308072 x y n) (@lem2308075 x y n)). Qed.
Lemma lem2308077 (n : nat) : (term10 n) = (term10 n).
Proof. exact (eq_refl (term10 n)). Qed.
Lemma lem2308078 (x : int) (y : int) (n : nat) : (term11 x y n) = (term12 x y n).
Proof. exact (MK_COMB (@lem2308077 n) (@lem2308076 x y n)). Qed.
Lemma lem2308079 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2308080 (x : int) (y : int) (n : nat) : (term13 x y n) = (term14 x y n).
Proof. exact (MK_COMB (@lem2308079) (@lem2308078 x y n)). Qed.
Lemma lem2308082 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2308083 (n : nat) (x : int) (y : int) : (term5 n x y) = (term15 n x y).
Proof. exact (MK_COMB (@lem2308080 x y n) (@lem2308082 x y)). Qed.
Lemma lem2308084 (n : nat) (x : int) (y : int) : term15 n x y.
Proof. exact (EQ_MP (@lem2308083 n x y) (@lem2308064 n x y)). Qed.
Lemma lem2308085 (n : nat) (x : int) : term16 n x.
Proof. exact (fun y : int => @lem2308084 n x y). Qed.
Lemma lem2308086 (n : nat) : term17 n.
Proof. exact (fun x : int => @lem2308085 n x). Qed.
Lemma lem2308087 : term18.
Proof. exact (fun n : nat => @lem2308086 n). Qed.
