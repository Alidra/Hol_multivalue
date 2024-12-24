Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_SUB_LZERO_term_abbrevs.
Require Import REAL_SUB_LZERO_spec.
Require Import thm2299897_spec.
Require Import thm2299898_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2310281 (x : int) : term0 x.
Proof. exact (@lem1517830 (real_of_int x)). Qed.
Lemma lem2310282 (x : int) : (term0 x) = ((term1 x) = (term2 x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2310283 (x : int) : (term1 x) = (term2 x).
Proof. exact (EQ_MP (@lem2310282 x) (@lem2310281 x)). Qed.
Lemma lem2310285 (n : nat) : (real_of_num n) = (term3 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2310286 : term4 = term5.
Proof. exact (@lem2310285 (NUMERAL 0)). Qed.
Lemma lem2310287 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2310288 : term6 = term7.
Proof. exact (MK_COMB (@lem2310287) (@lem2310286)). Qed.
Lemma lem2310289 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2310290 (x : int) : (term1 x) = (term8 x).
Proof. exact (MK_COMB (@lem2310288) (@lem2310289 x)). Qed.
Lemma lem2310292 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2310293 (x : int) : (term8 x) = (term11 x).
Proof. exact (@lem2310292 term12 x). Qed.
Lemma lem2310294 (x : int) : (term1 x) = (term11 x).
Proof. exact (TRANS (@lem2310290 x) (@lem2310293 x)). Qed.
Lemma lem2310295 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2310296 (x : int) : (term13 x) = (term14 x).
Proof. exact (MK_COMB (@lem2310295) (@lem2310294 x)). Qed.
Lemma lem2310298 (x : int) : (term2 x) = (term15 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2310299 (x : int) : ((term1 x) = (term2 x)) = ((term11 x) = (term15 x)).
Proof. exact (MK_COMB (@lem2310296 x) (@lem2310298 x)). Qed.
Lemma lem2310301 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2310302 (x : int) : ((term11 x) = (term15 x)) = ((term16 x) = (int_neg x)).
Proof. exact (@lem2310301 (term16 x) (int_neg x)). Qed.
Lemma lem2310303 (x : int) : ((term1 x) = (term2 x)) = ((term16 x) = (int_neg x)).
Proof. exact (TRANS (@lem2310299 x) (@lem2310302 x)). Qed.
Lemma lem2310304 (x : int) : (term16 x) = (int_neg x).
Proof. exact (EQ_MP (@lem2310303 x) (@lem2310283 x)). Qed.
Lemma lem2310305 : term17.
Proof. exact (fun x : int => @lem2310304 x). Qed.
