Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_NEG_MINUS1_term_abbrevs.
Require Import REAL_NEG_MINUS1_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2306582 (x : int) : term0 x.
Proof. exact (@lem1509128 (real_of_int x)). Qed.
Lemma lem2306583 (x : int) : (term0 x) = ((term1 x) = (term2 x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2306584 (x : int) : (term1 x) = (term2 x).
Proof. exact (EQ_MP (@lem2306583 x) (@lem2306582 x)). Qed.
Lemma lem2306586 (x : int) : (term1 x) = (term3 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2306587 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2306588 (x : int) : (term4 x) = (term5 x).
Proof. exact (MK_COMB (@lem2306587) (@lem2306586 x)). Qed.
Lemma lem2306590 (n : nat) : (real_of_num n) = (term6 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306591 : term7 = term8.
Proof. exact (@lem2306590 term9). Qed.
Lemma lem2306592 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2306593 : term10 = term11.
Proof. exact (MK_COMB (@lem2306592) (@lem2306591)). Qed.
Lemma lem2306595 (x : int) : (term1 x) = (term3 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2306596 : term11 = term12.
Proof. exact (@lem2306595 term13). Qed.
Lemma lem2306597 : term10 = term12.
Proof. exact (TRANS (@lem2306593) (@lem2306596)). Qed.
Lemma lem2306598 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2306599 : term14 = term15.
Proof. exact (MK_COMB (@lem2306598) (@lem2306597)). Qed.
Lemma lem2306600 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2306601 (x : int) : (term2 x) = (term16 x).
Proof. exact (MK_COMB (@lem2306599) (@lem2306600 x)). Qed.
Lemma lem2306603 (x : int) (y : int) : (term17 x y) = (term18 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2306604 (x : int) : (term16 x) = (term19 x).
Proof. exact (@lem2306603 term20 x). Qed.
Lemma lem2306605 (x : int) : (term2 x) = (term19 x).
Proof. exact (TRANS (@lem2306601 x) (@lem2306604 x)). Qed.
Lemma lem2306606 (x : int) : ((term1 x) = (term2 x)) = ((term3 x) = (term19 x)).
Proof. exact (MK_COMB (@lem2306588 x) (@lem2306605 x)). Qed.
Lemma lem2306608 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2306609 (x : int) : ((term3 x) = (term19 x)) = ((int_neg x) = (term21 x)).
Proof. exact (@lem2306608 (int_neg x) (term21 x)). Qed.
Lemma lem2306610 (x : int) : ((term1 x) = (term2 x)) = ((int_neg x) = (term21 x)).
Proof. exact (TRANS (@lem2306606 x) (@lem2306609 x)). Qed.
Lemma lem2306611 (x : int) : (int_neg x) = (term21 x).
Proof. exact (EQ_MP (@lem2306610 x) (@lem2306584 x)). Qed.
Lemma lem2306612 : term22.
Proof. exact (fun x : int => @lem2306611 x). Qed.
