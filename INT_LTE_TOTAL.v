Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LTE_TOTAL_term_abbrevs.
Require Import REAL_LTE_TOTAL_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2303594 (x : int) : term0 x.
Proof. exact (@lem1368041 (real_of_int x)). Qed.
Lemma lem2303595 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2303596 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2303595 x) (@lem2303594 x)). Qed.
Lemma lem2303597 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2303596 x (real_of_int y)). Qed.
Lemma lem2303598 (y : int) (x : int) : (term2 x y) = (term3 y x).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2303599 (y : int) (x : int) : term3 y x.
Proof. exact (EQ_MP (@lem2303598 y x) (@lem2303597 x y)). Qed.
Lemma lem2303601 (x : int) (y : int) : (term4 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2303602 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2303603 (x : int) (y : int) : (term5 x y) = (term6 x y).
Proof. exact (MK_COMB (@lem2303602) (@lem2303601 x y)). Qed.
Lemma lem2303605 (x : int) (y : int) : (term7 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2303606 (y : int) (x : int) : (term7 y x) = (int_le y x).
Proof. exact (@lem2303605 y x). Qed.
Lemma lem2303607 (y : int) (x : int) : (term3 y x) = (term8 y x).
Proof. exact (MK_COMB (@lem2303603 x y) (@lem2303606 y x)). Qed.
Lemma lem2303608 (y : int) (x : int) : term8 y x.
Proof. exact (EQ_MP (@lem2303607 y x) (@lem2303599 y x)). Qed.
Lemma lem2303609 (x : int) : term9 x.
Proof. exact (fun y : int => @lem2303608 y x). Qed.
Lemma lem2303610 : term10.
Proof. exact (fun x : int => @lem2303609 x). Qed.
