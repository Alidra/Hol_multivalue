Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_MUL_RZERO_term_abbrevs.
Require Import REAL_MUL_RZERO_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2306267 (x : int) : term0 x.
Proof. exact (@lem1356740 (real_of_int x)). Qed.
Lemma lem2306268 (x : int) : (term0 x) = ((term1 x) = term2).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2306269 (x : int) : (term1 x) = term2.
Proof. exact (EQ_MP (@lem2306268 x) (@lem2306267 x)). Qed.
Lemma lem2306271 (n : nat) : (real_of_num n) = (term3 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306272 : term2 = term4.
Proof. exact (@lem2306271 (NUMERAL 0)). Qed.
Lemma lem2306273 (x : int) : (term5 x) = (term5 x).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem2306274 (x : int) : (term1 x) = (term6 x).
Proof. exact (MK_COMB (@lem2306273 x) (@lem2306272)). Qed.
Lemma lem2306276 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2306277 (x : int) : (term6 x) = (term9 x).
Proof. exact (@lem2306276 x term10). Qed.
Lemma lem2306278 (x : int) : (term1 x) = (term9 x).
Proof. exact (TRANS (@lem2306274 x) (@lem2306277 x)). Qed.
Lemma lem2306279 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2306280 (x : int) : (term11 x) = (term12 x).
Proof. exact (MK_COMB (@lem2306279) (@lem2306278 x)). Qed.
Lemma lem2306282 (n : nat) : (real_of_num n) = (term3 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306283 : term2 = term4.
Proof. exact (@lem2306282 (NUMERAL 0)). Qed.
Lemma lem2306284 (x : int) : ((term1 x) = term2) = ((term9 x) = term4).
Proof. exact (MK_COMB (@lem2306280 x) (@lem2306283)). Qed.
Lemma lem2306286 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2306287 (x : int) : ((term9 x) = term4) = ((term13 x) = term10).
Proof. exact (@lem2306286 (term13 x) term10). Qed.
Lemma lem2306288 (x : int) : ((term1 x) = term2) = ((term13 x) = term10).
Proof. exact (TRANS (@lem2306284 x) (@lem2306287 x)). Qed.
Lemma lem2306289 (x : int) : (term13 x) = term10.
Proof. exact (EQ_MP (@lem2306288 x) (@lem2306269 x)). Qed.
Lemma lem2306290 : term14.
Proof. exact (fun x : int => @lem2306289 x). Qed.
