Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_SUB_LE_term_abbrevs.
Require Import REAL_SUB_LE_spec.
Require Import thm2299897_spec.
Require Import thm2299898_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2310193 (x : int) : term0 x.
Proof. exact (@lem1374224 (real_of_int x)). Qed.
Lemma lem2310194 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2310195 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2310194 x) (@lem2310193 x)). Qed.
Lemma lem2310196 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2310195 x (real_of_int y)). Qed.
Lemma lem2310197 (y : int) (x : int) : (term2 x y) = ((term3 x y) = (term4 y x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2310198 (y : int) (x : int) : (term3 x y) = (term4 y x).
Proof. exact (EQ_MP (@lem2310197 y x) (@lem2310196 x y)). Qed.
Lemma lem2310200 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2310201 : term6 = term7.
Proof. exact (@lem2310200 (NUMERAL 0)). Qed.
Lemma lem2310202 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2310203 : term8 = term9.
Proof. exact (MK_COMB (@lem2310202) (@lem2310201)). Qed.
Lemma lem2310205 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2310206 (x : int) (y : int) : (term3 x y) = (term12 x y).
Proof. exact (MK_COMB (@lem2310203) (@lem2310205 x y)). Qed.
Lemma lem2310208 (x : int) (y : int) : (term4 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2310209 (x : int) (y : int) : (term12 x y) = (term13 x y).
Proof. exact (@lem2310208 term14 (int_sub x y)). Qed.
Lemma lem2310210 (x : int) (y : int) : (term3 x y) = (term13 x y).
Proof. exact (TRANS (@lem2310206 x y) (@lem2310209 x y)). Qed.
Lemma lem2310211 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2310212 (x : int) (y : int) : (term15 x y) = (term16 x y).
Proof. exact (MK_COMB (@lem2310211) (@lem2310210 x y)). Qed.
Lemma lem2310214 (x : int) (y : int) : (term4 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2310215 (y : int) (x : int) : (term4 y x) = (int_le y x).
Proof. exact (@lem2310214 y x). Qed.
Lemma lem2310216 (y : int) (x : int) : ((term3 x y) = (term4 y x)) = ((term13 x y) = (int_le y x)).
Proof. exact (MK_COMB (@lem2310212 x y) (@lem2310215 y x)). Qed.
Lemma lem2310217 (y : int) (x : int) : (term13 x y) = (int_le y x).
Proof. exact (EQ_MP (@lem2310216 y x) (@lem2310198 y x)). Qed.
Lemma lem2310218 (x : int) : term17 x.
Proof. exact (fun y : int => @lem2310217 y x). Qed.
Lemma lem2310219 : term18.
Proof. exact (fun x : int => @lem2310218 x). Qed.
