Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LET_TOTAL_term_abbrevs.
Require Import REAL_LET_TOTAL_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2302115 (x : int) : term0 x.
Proof. exact (@lem1368147 (real_of_int x)). Qed.
Lemma lem2302116 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2302117 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2302116 x) (@lem2302115 x)). Qed.
Lemma lem2302118 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2302117 x (real_of_int y)). Qed.
Lemma lem2302119 (y : int) (x : int) : (term2 x y) = (term3 y x).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2302120 (y : int) (x : int) : term3 y x.
Proof. exact (EQ_MP (@lem2302119 y x) (@lem2302118 x y)). Qed.
Lemma lem2302122 (x : int) (y : int) : (term4 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302123 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2302124 (x : int) (y : int) : (term5 x y) = (term6 x y).
Proof. exact (MK_COMB (@lem2302123) (@lem2302122 x y)). Qed.
Lemma lem2302126 (x : int) (y : int) : (term7 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2302127 (y : int) (x : int) : (term7 y x) = (int_lt y x).
Proof. exact (@lem2302126 y x). Qed.
Lemma lem2302128 (y : int) (x : int) : (term3 y x) = (term8 y x).
Proof. exact (MK_COMB (@lem2302124 x y) (@lem2302127 y x)). Qed.
Lemma lem2302129 (y : int) (x : int) : term8 y x.
Proof. exact (EQ_MP (@lem2302128 y x) (@lem2302120 y x)). Qed.
Lemma lem2302130 (x : int) : term9 x.
Proof. exact (fun y : int => @lem2302129 y x). Qed.
Lemma lem2302131 : term10.
Proof. exact (fun x : int => @lem2302130 x). Qed.
