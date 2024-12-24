Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_ABS_CASES_term_abbrevs.
Require Import REAL_ABS_CASES_spec.
Require Import thm2299891_spec.
Require Import thm2299892_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2300296 (x : int) : term0 x.
Proof. exact (@lem1540867 (real_of_int x)). Qed.
Lemma lem2300297 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2300298 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2300297 x) (@lem2300296 x)). Qed.
Lemma lem2300300 (n : nat) : (real_of_num n) = (term2 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2300301 : term3 = term4.
Proof. exact (@lem2300300 (NUMERAL 0)). Qed.
Lemma lem2300302 (x : int) : (term5 x) = (term5 x).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem2300303 (x : int) : ((real_of_int x) = term3) = ((real_of_int x) = term4).
Proof. exact (MK_COMB (@lem2300302 x) (@lem2300301)). Qed.
Lemma lem2300305 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2300306 (x : int) : ((real_of_int x) = term4) = (x = term6).
Proof. exact (@lem2300305 x term6). Qed.
Lemma lem2300307 (x : int) : ((real_of_int x) = term3) = (x = term6).
Proof. exact (TRANS (@lem2300303 x) (@lem2300306 x)). Qed.
Lemma lem2300308 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2300309 (x : int) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem2300308) (@lem2300307 x)). Qed.
Lemma lem2300311 (n : nat) : (real_of_num n) = (term2 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2300312 : term3 = term4.
Proof. exact (@lem2300311 (NUMERAL 0)). Qed.
Lemma lem2300313 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2300314 : term9 = term10.
Proof. exact (MK_COMB (@lem2300313) (@lem2300312)). Qed.
Lemma lem2300316 (x : int) : (term11 x) = (term12 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2300317 (x : int) : (term13 x) = (term14 x).
Proof. exact (MK_COMB (@lem2300314) (@lem2300316 x)). Qed.
Lemma lem2300319 (x : int) (y : int) : (term15 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2300320 (x : int) : (term14 x) = (term16 x).
Proof. exact (@lem2300319 term6 (int_abs x)). Qed.
Lemma lem2300321 (x : int) : (term13 x) = (term16 x).
Proof. exact (TRANS (@lem2300317 x) (@lem2300320 x)). Qed.
Lemma lem2300322 (x : int) : (term1 x) = (term17 x).
Proof. exact (MK_COMB (@lem2300309 x) (@lem2300321 x)). Qed.
Lemma lem2300323 (x : int) : term17 x.
Proof. exact (EQ_MP (@lem2300322 x) (@lem2300298 x)). Qed.
Lemma lem2300324 : term18.
Proof. exact (fun x : int => @lem2300323 x). Qed.
