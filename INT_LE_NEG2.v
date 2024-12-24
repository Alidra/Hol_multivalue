Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LE_NEG2_term_abbrevs.
Require Import REAL_LE_NEG2_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2302918 (x : int) : term0 x.
Proof. exact (@lem1362291 (real_of_int x)). Qed.
Lemma lem2302919 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2302920 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2302919 x) (@lem2302918 x)). Qed.
Lemma lem2302921 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2302920 x (real_of_int y)). Qed.
Lemma lem2302922 (y : int) (x : int) : (term2 x y) = ((term3 x y) = (term4 y x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2302923 (y : int) (x : int) : (term3 x y) = (term4 y x).
Proof. exact (EQ_MP (@lem2302922 y x) (@lem2302921 x y)). Qed.
Lemma lem2302925 (x : int) : (term5 x) = (term6 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2302926 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2302927 (x : int) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem2302926) (@lem2302925 x)). Qed.
Lemma lem2302929 (x : int) : (term5 x) = (term6 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2302930 (y : int) : (term5 y) = (term6 y).
Proof. exact (@lem2302929 y). Qed.
Lemma lem2302931 (x : int) (y : int) : (term3 x y) = (term9 x y).
Proof. exact (MK_COMB (@lem2302927 x) (@lem2302930 y)). Qed.
Lemma lem2302933 (x : int) (y : int) : (term4 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302934 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (@lem2302933 (int_neg x) (int_neg y)). Qed.
Lemma lem2302935 (x : int) (y : int) : (term3 x y) = (term10 x y).
Proof. exact (TRANS (@lem2302931 x y) (@lem2302934 x y)). Qed.
Lemma lem2302936 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2302937 (x : int) (y : int) : (term11 x y) = (term12 x y).
Proof. exact (MK_COMB (@lem2302936) (@lem2302935 x y)). Qed.
Lemma lem2302939 (x : int) (y : int) : (term4 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302940 (y : int) (x : int) : (term4 y x) = (int_le y x).
Proof. exact (@lem2302939 y x). Qed.
Lemma lem2302941 (y : int) (x : int) : ((term3 x y) = (term4 y x)) = ((term10 x y) = (int_le y x)).
Proof. exact (MK_COMB (@lem2302937 x y) (@lem2302940 y x)). Qed.
Lemma lem2302942 (y : int) (x : int) : (term10 x y) = (int_le y x).
Proof. exact (EQ_MP (@lem2302941 y x) (@lem2302923 y x)). Qed.
Lemma lem2302943 (x : int) : term13 x.
Proof. exact (fun y : int => @lem2302942 y x). Qed.
Lemma lem2302944 : term14.
Proof. exact (fun x : int => @lem2302943 x). Qed.
