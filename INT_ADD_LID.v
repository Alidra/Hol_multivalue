Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_ADD_LID_term_abbrevs.
Require Import thm1338512_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2301109 (x : int) : term0 x.
Proof. exact (@lem1338512 (real_of_int x)). Qed.
Lemma lem2301110 (x : int) : (term0 x) = ((term1 x) = (real_of_int x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2301111 (x : int) : (term1 x) = (real_of_int x).
Proof. exact (EQ_MP (@lem2301110 x) (@lem2301109 x)). Qed.
Lemma lem2301113 (n : nat) : (real_of_num n) = (term2 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2301114 : term3 = term4.
Proof. exact (@lem2301113 (NUMERAL 0)). Qed.
Lemma lem2301115 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2301116 : term5 = term6.
Proof. exact (MK_COMB (@lem2301115) (@lem2301114)). Qed.
Lemma lem2301117 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2301118 (x : int) : (term1 x) = (term7 x).
Proof. exact (MK_COMB (@lem2301116) (@lem2301117 x)). Qed.
Lemma lem2301120 (x : int) (y : int) : (term8 x y) = (term9 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2301121 (x : int) : (term7 x) = (term10 x).
Proof. exact (@lem2301120 term11 x). Qed.
Lemma lem2301122 (x : int) : (term1 x) = (term10 x).
Proof. exact (TRANS (@lem2301118 x) (@lem2301121 x)). Qed.
Lemma lem2301123 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2301124 (x : int) : (term12 x) = (term13 x).
Proof. exact (MK_COMB (@lem2301123) (@lem2301122 x)). Qed.
Lemma lem2301125 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2301126 (x : int) : ((term1 x) = (real_of_int x)) = ((term10 x) = (real_of_int x)).
Proof. exact (MK_COMB (@lem2301124 x) (@lem2301125 x)). Qed.
Lemma lem2301128 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301129 (x : int) : ((term10 x) = (real_of_int x)) = ((term14 x) = x).
Proof. exact (@lem2301128 (term14 x) x). Qed.
Lemma lem2301130 (x : int) : ((term1 x) = (real_of_int x)) = ((term14 x) = x).
Proof. exact (TRANS (@lem2301126 x) (@lem2301129 x)). Qed.
Lemma lem2301131 (x : int) : (term14 x) = x.
Proof. exact (EQ_MP (@lem2301130 x) (@lem2301111 x)). Qed.
Lemma lem2301132 : term15.
Proof. exact (fun x : int => @lem2301131 x). Qed.
