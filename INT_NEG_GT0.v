Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_NEG_GT0_term_abbrevs.
Require Import REAL_NEG_GT0_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2306457 (x : int) : term0 x.
Proof. exact (@lem1497248 (real_of_int x)). Qed.
Lemma lem2306458 (x : int) : (term0 x) = ((term1 x) = (term2 x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2306459 (x : int) : (term1 x) = (term2 x).
Proof. exact (EQ_MP (@lem2306458 x) (@lem2306457 x)). Qed.
Lemma lem2306461 (n : nat) : (real_of_num n) = (term3 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306462 : term4 = term5.
Proof. exact (@lem2306461 (NUMERAL 0)). Qed.
Lemma lem2306463 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2306464 : term6 = term7.
Proof. exact (MK_COMB (@lem2306463) (@lem2306462)). Qed.
Lemma lem2306466 (x : int) : (term8 x) = (term9 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2306467 (x : int) : (term1 x) = (term10 x).
Proof. exact (MK_COMB (@lem2306464) (@lem2306466 x)). Qed.
Lemma lem2306469 (x : int) (y : int) : (term11 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2306470 (x : int) : (term10 x) = (term12 x).
Proof. exact (@lem2306469 term13 (int_neg x)). Qed.
Lemma lem2306471 (x : int) : (term1 x) = (term12 x).
Proof. exact (TRANS (@lem2306467 x) (@lem2306470 x)). Qed.
Lemma lem2306472 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2306473 (x : int) : (term14 x) = (term15 x).
Proof. exact (MK_COMB (@lem2306472) (@lem2306471 x)). Qed.
Lemma lem2306475 (n : nat) : (real_of_num n) = (term3 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306476 : term4 = term5.
Proof. exact (@lem2306475 (NUMERAL 0)). Qed.
Lemma lem2306477 (x : int) : (term16 x) = (term16 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem2306478 (x : int) : (term2 x) = (term17 x).
Proof. exact (MK_COMB (@lem2306477 x) (@lem2306476)). Qed.
Lemma lem2306480 (x : int) (y : int) : (term11 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2306481 (x : int) : (term17 x) = (term18 x).
Proof. exact (@lem2306480 x term13). Qed.
Lemma lem2306482 (x : int) : (term2 x) = (term18 x).
Proof. exact (TRANS (@lem2306478 x) (@lem2306481 x)). Qed.
Lemma lem2306483 (x : int) : ((term1 x) = (term2 x)) = ((term12 x) = (term18 x)).
Proof. exact (MK_COMB (@lem2306473 x) (@lem2306482 x)). Qed.
Lemma lem2306484 (x : int) : (term12 x) = (term18 x).
Proof. exact (EQ_MP (@lem2306483 x) (@lem2306459 x)). Qed.
Lemma lem2306485 : term19.
Proof. exact (fun x : int => @lem2306484 x). Qed.
