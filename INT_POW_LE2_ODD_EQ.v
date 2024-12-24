Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_POW_LE2_ODD_EQ_term_abbrevs.
Require Import REAL_POW_LE2_ODD_EQ_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2308302 (n : nat) : term0 n.
Proof. exact (@lem1665172 n). Qed.
Lemma lem2308303 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem2308304 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem2308303 n) (@lem2308302 n)). Qed.
Lemma lem2308305 (n : nat) (x : int) : term2 n x.
Proof. exact (@lem2308304 n (real_of_int x)). Qed.
Lemma lem2308306 (n : nat) (x : int) : (term2 n x) = (term3 n x).
Proof. exact (eq_refl (term2 n x)). Qed.
Lemma lem2308307 (n : nat) (x : int) : term3 n x.
Proof. exact (EQ_MP (@lem2308306 n x) (@lem2308305 n x)). Qed.
Lemma lem2308308 (n : nat) (x : int) (y : int) : term4 n x y.
Proof. exact (@lem2308307 n x (real_of_int y)). Qed.
Lemma lem2308309 (n : nat) (x : int) (y : int) : (term4 n x y) = (term5 n x y).
Proof. exact (eq_refl (term4 n x y)). Qed.
Lemma lem2308310 (n : nat) (x : int) (y : int) : term5 n x y.
Proof. exact (EQ_MP (@lem2308309 n x y) (@lem2308308 n x y)). Qed.
Lemma lem2308312 (x : int) (n : nat) : (term6 x n) = (term7 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2308313 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2308314 (x : int) (n : nat) : (term8 x n) = (term9 x n).
Proof. exact (MK_COMB (@lem2308313) (@lem2308312 x n)). Qed.
Lemma lem2308316 (x : int) (n : nat) : (term6 x n) = (term7 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2308317 (y : int) (n : nat) : (term6 y n) = (term7 y n).
Proof. exact (@lem2308316 y n). Qed.
Lemma lem2308318 (x : int) (y : int) (n : nat) : (term10 x y n) = (term11 x y n).
Proof. exact (MK_COMB (@lem2308314 x n) (@lem2308317 y n)). Qed.
Lemma lem2308320 (x : int) (y : int) : (term12 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2308321 (x : int) (y : int) (n : nat) : (term11 x y n) = (term13 x y n).
Proof. exact (@lem2308320 (int_pow x n) (int_pow y n)). Qed.
Lemma lem2308322 (x : int) (y : int) (n : nat) : (term10 x y n) = (term13 x y n).
Proof. exact (TRANS (@lem2308318 x y n) (@lem2308321 x y n)). Qed.
Lemma lem2308323 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2308324 (x : int) (y : int) (n : nat) : (term14 x y n) = (term15 x y n).
Proof. exact (MK_COMB (@lem2308323) (@lem2308322 x y n)). Qed.
Lemma lem2308326 (x : int) (y : int) : (term12 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2308327 (n : nat) (x : int) (y : int) : ((term10 x y n) = (term12 x y)) = ((term13 x y n) = (int_le x y)).
Proof. exact (MK_COMB (@lem2308324 x y n) (@lem2308326 x y)). Qed.
Lemma lem2308328 (n : nat) : (term16 n) = (term16 n).
Proof. exact (eq_refl (term16 n)). Qed.
Lemma lem2308329 (n : nat) (x : int) (y : int) : (term5 n x y) = (term17 n x y).
Proof. exact (MK_COMB (@lem2308328 n) (@lem2308327 n x y)). Qed.
Lemma lem2308330 (n : nat) (x : int) (y : int) : term17 n x y.
Proof. exact (EQ_MP (@lem2308329 n x y) (@lem2308310 n x y)). Qed.
Lemma lem2308331 (n : nat) (x : int) : term18 n x.
Proof. exact (fun y : int => @lem2308330 n x y). Qed.
Lemma lem2308332 (n : nat) : term19 n.
Proof. exact (fun x : int => @lem2308331 n x). Qed.
Lemma lem2308333 : term20.
Proof. exact (fun n : nat => @lem2308332 n). Qed.
