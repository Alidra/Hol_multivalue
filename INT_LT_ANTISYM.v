Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LT_ANTISYM_term_abbrevs.
Require Import REAL_LT_ANTISYM_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2303953 (x : int) : term0 x.
Proof. exact (@lem1493879 (real_of_int x)). Qed.
Lemma lem2303954 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2303955 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2303954 x) (@lem2303953 x)). Qed.
Lemma lem2303956 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2303955 x (real_of_int y)). Qed.
Lemma lem2303957 (y : int) (x : int) : (term2 x y) = (term3 y x).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2303958 (y : int) (x : int) : term3 y x.
Proof. exact (EQ_MP (@lem2303957 y x) (@lem2303956 x y)). Qed.
Lemma lem2303960 (x : int) (y : int) : (term4 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2303961 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2303962 (x : int) (y : int) : (term5 x y) = (term6 x y).
Proof. exact (MK_COMB (@lem2303961) (@lem2303960 x y)). Qed.
Lemma lem2303964 (x : int) (y : int) : (term4 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2303965 (y : int) (x : int) : (term4 y x) = (int_lt y x).
Proof. exact (@lem2303964 y x). Qed.
Lemma lem2303966 (y : int) (x : int) : (term7 y x) = (term8 y x).
Proof. exact (MK_COMB (@lem2303962 x y) (@lem2303965 y x)). Qed.
Lemma lem2303967 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2303968 (y : int) (x : int) : (term3 y x) = (term9 y x).
Proof. exact (MK_COMB (@lem2303967) (@lem2303966 y x)). Qed.
Lemma lem2303969 (y : int) (x : int) : term9 y x.
Proof. exact (EQ_MP (@lem2303968 y x) (@lem2303958 y x)). Qed.
Lemma lem2303970 (x : int) : term10 x.
Proof. exact (fun y : int => @lem2303969 y x). Qed.
Lemma lem2303971 : term11.
Proof. exact (fun x : int => @lem2303970 x). Qed.
