Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_SUB_ADD2_term_abbrevs.
Require Import REAL_SUB_ADD2_spec.
Require Import thm2299897_spec.
Require Import thm2299898_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2310127 (x : int) : term0 x.
Proof. exact (@lem1505085 (real_of_int x)). Qed.
Lemma lem2310128 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2310129 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2310128 x) (@lem2310127 x)). Qed.
Lemma lem2310130 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2310129 x (real_of_int y)). Qed.
Lemma lem2310131 (y : int) (x : int) : (term2 x y) = ((term3 x y) = (real_of_int x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2310132 (y : int) (x : int) : (term3 x y) = (real_of_int x).
Proof. exact (EQ_MP (@lem2310131 y x) (@lem2310130 x y)). Qed.
Lemma lem2310134 (x : int) (y : int) : (term4 x y) = (term5 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2310135 (y : int) : (term6 y) = (term6 y).
Proof. exact (eq_refl (term6 y)). Qed.
Lemma lem2310136 (x : int) (y : int) : (term3 x y) = (term7 x y).
Proof. exact (MK_COMB (@lem2310135 y) (@lem2310134 x y)). Qed.
Lemma lem2310138 (x : int) (y : int) : (term8 x y) = (term9 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2310139 (x : int) (y : int) : (term7 x y) = (term10 x y).
Proof. exact (@lem2310138 y (int_sub x y)). Qed.
Lemma lem2310140 (x : int) (y : int) : (term3 x y) = (term10 x y).
Proof. exact (TRANS (@lem2310136 x y) (@lem2310139 x y)). Qed.
Lemma lem2310141 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2310142 (x : int) (y : int) : (term11 x y) = (term12 x y).
Proof. exact (MK_COMB (@lem2310141) (@lem2310140 x y)). Qed.
Lemma lem2310143 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2310144 (y : int) (x : int) : ((term3 x y) = (real_of_int x)) = ((term10 x y) = (real_of_int x)).
Proof. exact (MK_COMB (@lem2310142 x y) (@lem2310143 x)). Qed.
Lemma lem2310146 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2310147 (y : int) (x : int) : ((term10 x y) = (real_of_int x)) = ((term13 x y) = x).
Proof. exact (@lem2310146 (term13 x y) x). Qed.
Lemma lem2310148 (y : int) (x : int) : ((term3 x y) = (real_of_int x)) = ((term13 x y) = x).
Proof. exact (TRANS (@lem2310144 y x) (@lem2310147 y x)). Qed.
Lemma lem2310149 (y : int) (x : int) : (term13 x y) = x.
Proof. exact (EQ_MP (@lem2310148 y x) (@lem2310132 y x)). Qed.
Lemma lem2310150 (x : int) : term14 x.
Proof. exact (fun y : int => @lem2310149 y x). Qed.
Lemma lem2310151 : term15.
Proof. exact (fun x : int => @lem2310150 x). Qed.
