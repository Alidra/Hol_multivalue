Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LET_ANTISYM_term_abbrevs.
Require Import REAL_LET_ANTISYM_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2302096 (x : int) : term0 x.
Proof. exact (@lem1496214 (real_of_int x)). Qed.
Lemma lem2302097 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2302098 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2302097 x) (@lem2302096 x)). Qed.
Lemma lem2302099 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2302098 x (real_of_int y)). Qed.
Lemma lem2302100 (y : int) (x : int) : (term2 x y) = (term3 y x).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2302101 (y : int) (x : int) : term3 y x.
Proof. exact (EQ_MP (@lem2302100 y x) (@lem2302099 x y)). Qed.
Lemma lem2302103 (x : int) (y : int) : (term4 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302104 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2302105 (x : int) (y : int) : (term5 x y) = (term6 x y).
Proof. exact (MK_COMB (@lem2302104) (@lem2302103 x y)). Qed.
Lemma lem2302107 (x : int) (y : int) : (term7 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2302108 (y : int) (x : int) : (term7 y x) = (int_lt y x).
Proof. exact (@lem2302107 y x). Qed.
Lemma lem2302109 (y : int) (x : int) : (term8 y x) = (term9 y x).
Proof. exact (MK_COMB (@lem2302105 x y) (@lem2302108 y x)). Qed.
Lemma lem2302110 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2302111 (y : int) (x : int) : (term3 y x) = (term10 y x).
Proof. exact (MK_COMB (@lem2302110) (@lem2302109 y x)). Qed.
Lemma lem2302112 (y : int) (x : int) : term10 y x.
Proof. exact (EQ_MP (@lem2302111 y x) (@lem2302101 y x)). Qed.
Lemma lem2302113 (x : int) : term11 x.
Proof. exact (fun y : int => @lem2302112 y x). Qed.
Lemma lem2302114 : term12.
Proof. exact (fun x : int => @lem2302113 x). Qed.
