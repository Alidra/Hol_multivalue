Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LE_LNEG_term_abbrevs.
Require Import REAL_LE_LNEG_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2302577 (x : int) : term0 x.
Proof. exact (@lem1362225 (real_of_int x)). Qed.
Lemma lem2302578 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2302579 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2302578 x) (@lem2302577 x)). Qed.
Lemma lem2302580 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2302579 x (real_of_int y)). Qed.
Lemma lem2302581 (x : int) (y : int) : (term2 x y) = ((term3 x y) = (term4 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2302582 (x : int) (y : int) : (term3 x y) = (term4 x y).
Proof. exact (EQ_MP (@lem2302581 x y) (@lem2302580 x y)). Qed.
Lemma lem2302584 (x : int) : (term5 x) = (term6 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2302585 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2302586 (x : int) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem2302585) (@lem2302584 x)). Qed.
Lemma lem2302587 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2302588 (x : int) (y : int) : (term3 x y) = (term9 x y).
Proof. exact (MK_COMB (@lem2302586 x) (@lem2302587 y)). Qed.
Lemma lem2302590 (x : int) (y : int) : (term10 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302591 (x : int) (y : int) : (term9 x y) = (term11 x y).
Proof. exact (@lem2302590 (int_neg x) y). Qed.
Lemma lem2302592 (x : int) (y : int) : (term3 x y) = (term11 x y).
Proof. exact (TRANS (@lem2302588 x y) (@lem2302591 x y)). Qed.
Lemma lem2302593 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2302594 (x : int) (y : int) : (term12 x y) = (term13 x y).
Proof. exact (MK_COMB (@lem2302593) (@lem2302592 x y)). Qed.
Lemma lem2302596 (n : nat) : (real_of_num n) = (term14 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2302597 : term15 = term16.
Proof. exact (@lem2302596 (NUMERAL 0)). Qed.
Lemma lem2302598 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2302599 : term17 = term18.
Proof. exact (MK_COMB (@lem2302598) (@lem2302597)). Qed.
Lemma lem2302601 (x : int) (y : int) : (term19 x y) = (term20 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2302602 (x : int) (y : int) : (term4 x y) = (term21 x y).
Proof. exact (MK_COMB (@lem2302599) (@lem2302601 x y)). Qed.
Lemma lem2302604 (x : int) (y : int) : (term10 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302605 (x : int) (y : int) : (term21 x y) = (term22 x y).
Proof. exact (@lem2302604 term23 (int_add x y)). Qed.
Lemma lem2302606 (x : int) (y : int) : (term4 x y) = (term22 x y).
Proof. exact (TRANS (@lem2302602 x y) (@lem2302605 x y)). Qed.
Lemma lem2302607 (x : int) (y : int) : ((term3 x y) = (term4 x y)) = ((term11 x y) = (term22 x y)).
Proof. exact (MK_COMB (@lem2302594 x y) (@lem2302606 x y)). Qed.
Lemma lem2302608 (x : int) (y : int) : (term11 x y) = (term22 x y).
Proof. exact (EQ_MP (@lem2302607 x y) (@lem2302582 x y)). Qed.
Lemma lem2302609 (x : int) : term24 x.
Proof. exact (fun y : int => @lem2302608 x y). Qed.
Lemma lem2302610 : term25.
Proof. exact (fun x : int => @lem2302609 x). Qed.
