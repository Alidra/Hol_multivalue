Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LT_GT_term_abbrevs.
Require Import REAL_LT_GT_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2303972 (x : int) : term0 x.
Proof. exact (@lem1494162 (real_of_int x)). Qed.
Lemma lem2303973 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2303974 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2303973 x) (@lem2303972 x)). Qed.
Lemma lem2303975 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2303974 x (real_of_int y)). Qed.
Lemma lem2303976 (y : int) (x : int) : (term2 x y) = (term3 y x).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2303977 (y : int) (x : int) : term3 y x.
Proof. exact (EQ_MP (@lem2303976 y x) (@lem2303975 x y)). Qed.
Lemma lem2303979 (x : int) (y : int) : (term4 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2303980 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2303981 (x : int) (y : int) : (term5 x y) = (term6 x y).
Proof. exact (MK_COMB (@lem2303980) (@lem2303979 x y)). Qed.
Lemma lem2303983 (x : int) (y : int) : (term4 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2303984 (y : int) (x : int) : (term4 y x) = (int_lt y x).
Proof. exact (@lem2303983 y x). Qed.
Lemma lem2303985 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2303986 (y : int) (x : int) : (term7 y x) = (term8 y x).
Proof. exact (MK_COMB (@lem2303985) (@lem2303984 y x)). Qed.
Lemma lem2303987 (y : int) (x : int) : (term3 y x) = (term9 y x).
Proof. exact (MK_COMB (@lem2303981 x y) (@lem2303986 y x)). Qed.
Lemma lem2303988 (y : int) (x : int) : term9 y x.
Proof. exact (EQ_MP (@lem2303987 y x) (@lem2303977 y x)). Qed.
Lemma lem2303989 (x : int) : term10 x.
Proof. exact (fun y : int => @lem2303988 y x). Qed.
Lemma lem2303990 : term11.
Proof. exact (fun x : int => @lem2303989 x). Qed.
