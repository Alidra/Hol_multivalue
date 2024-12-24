Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_NEG_LE0_term_abbrevs.
Require Import REAL_NEG_LE0_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2306486 (x : int) : term0 x.
Proof. exact (@lem1497765 (real_of_int x)). Qed.
Lemma lem2306487 (x : int) : (term0 x) = ((term1 x) = (term2 x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2306488 (x : int) : (term1 x) = (term2 x).
Proof. exact (EQ_MP (@lem2306487 x) (@lem2306486 x)). Qed.
Lemma lem2306490 (x : int) : (term3 x) = (term4 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2306491 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2306492 (x : int) : (term5 x) = (term6 x).
Proof. exact (MK_COMB (@lem2306491) (@lem2306490 x)). Qed.
Lemma lem2306494 (n : nat) : (real_of_num n) = (term7 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306495 : term8 = term9.
Proof. exact (@lem2306494 (NUMERAL 0)). Qed.
Lemma lem2306496 (x : int) : (term1 x) = (term10 x).
Proof. exact (MK_COMB (@lem2306492 x) (@lem2306495)). Qed.
Lemma lem2306498 (x : int) (y : int) : (term11 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2306499 (x : int) : (term10 x) = (term12 x).
Proof. exact (@lem2306498 (int_neg x) term13). Qed.
Lemma lem2306500 (x : int) : (term1 x) = (term12 x).
Proof. exact (TRANS (@lem2306496 x) (@lem2306499 x)). Qed.
Lemma lem2306501 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2306502 (x : int) : (term14 x) = (term15 x).
Proof. exact (MK_COMB (@lem2306501) (@lem2306500 x)). Qed.
Lemma lem2306504 (n : nat) : (real_of_num n) = (term7 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306505 : term8 = term9.
Proof. exact (@lem2306504 (NUMERAL 0)). Qed.
Lemma lem2306506 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2306507 : term16 = term17.
Proof. exact (MK_COMB (@lem2306506) (@lem2306505)). Qed.
Lemma lem2306508 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2306509 (x : int) : (term2 x) = (term18 x).
Proof. exact (MK_COMB (@lem2306507) (@lem2306508 x)). Qed.
Lemma lem2306511 (x : int) (y : int) : (term11 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2306512 (x : int) : (term18 x) = (term19 x).
Proof. exact (@lem2306511 term13 x). Qed.
Lemma lem2306513 (x : int) : (term2 x) = (term19 x).
Proof. exact (TRANS (@lem2306509 x) (@lem2306512 x)). Qed.
Lemma lem2306514 (x : int) : ((term1 x) = (term2 x)) = ((term12 x) = (term19 x)).
Proof. exact (MK_COMB (@lem2306502 x) (@lem2306513 x)). Qed.
Lemma lem2306515 (x : int) : (term12 x) = (term19 x).
Proof. exact (EQ_MP (@lem2306514 x) (@lem2306488 x)). Qed.
Lemma lem2306516 : term20.
Proof. exact (fun x : int => @lem2306515 x). Qed.
