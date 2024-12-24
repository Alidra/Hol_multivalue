Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_SGN_CASES_term_abbrevs.
Require Import REAL_SGN_CASES_spec.
Require Import thm2299900_spec.
Require Import thm2299901_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2309298 (x : int) : term0 x.
Proof. exact (@lem1740648 (real_of_int x)). Qed.
Lemma lem2309299 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2309300 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2309299 x) (@lem2309298 x)). Qed.
Lemma lem2309302 (x : int) : (term2 x) = (term3 x).
Proof. exact (EQ_MP (@lem2299901 x) (@lem2299900 x)). Qed.
Lemma lem2309303 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2309304 (x : int) : (term4 x) = (term5 x).
Proof. exact (MK_COMB (@lem2309303) (@lem2309302 x)). Qed.
Lemma lem2309306 (n : nat) : (real_of_num n) = (term6 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2309307 : term7 = term8.
Proof. exact (@lem2309306 (NUMERAL 0)). Qed.
Lemma lem2309308 (x : int) : ((term2 x) = term7) = ((term3 x) = term8).
Proof. exact (MK_COMB (@lem2309304 x) (@lem2309307)). Qed.
Lemma lem2309310 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2309311 (x : int) : ((term3 x) = term8) = ((int_sgn x) = term9).
Proof. exact (@lem2309310 (int_sgn x) term9). Qed.
Lemma lem2309312 (x : int) : ((term2 x) = term7) = ((int_sgn x) = term9).
Proof. exact (TRANS (@lem2309308 x) (@lem2309311 x)). Qed.
Lemma lem2309313 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2309314 (x : int) : (term10 x) = (term11 x).
Proof. exact (MK_COMB (@lem2309313) (@lem2309312 x)). Qed.
Lemma lem2309316 (x : int) : (term2 x) = (term3 x).
Proof. exact (EQ_MP (@lem2299901 x) (@lem2299900 x)). Qed.
Lemma lem2309317 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2309318 (x : int) : (term4 x) = (term5 x).
Proof. exact (MK_COMB (@lem2309317) (@lem2309316 x)). Qed.
Lemma lem2309320 (n : nat) : (real_of_num n) = (term6 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2309321 : term12 = term13.
Proof. exact (@lem2309320 term14). Qed.
Lemma lem2309322 (x : int) : ((term2 x) = term12) = ((term3 x) = term13).
Proof. exact (MK_COMB (@lem2309318 x) (@lem2309321)). Qed.
Lemma lem2309324 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2309325 (x : int) : ((term3 x) = term13) = ((int_sgn x) = term15).
Proof. exact (@lem2309324 (int_sgn x) term15). Qed.
Lemma lem2309326 (x : int) : ((term2 x) = term12) = ((int_sgn x) = term15).
Proof. exact (TRANS (@lem2309322 x) (@lem2309325 x)). Qed.
Lemma lem2309327 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2309328 (x : int) : (term16 x) = (term17 x).
Proof. exact (MK_COMB (@lem2309327) (@lem2309326 x)). Qed.
Lemma lem2309330 (x : int) : (term2 x) = (term3 x).
Proof. exact (EQ_MP (@lem2299901 x) (@lem2299900 x)). Qed.
Lemma lem2309331 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2309332 (x : int) : (term4 x) = (term5 x).
Proof. exact (MK_COMB (@lem2309331) (@lem2309330 x)). Qed.
Lemma lem2309334 (n : nat) : (real_of_num n) = (term6 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2309335 : term12 = term13.
Proof. exact (@lem2309334 term14). Qed.
Lemma lem2309336 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2309337 : term18 = term19.
Proof. exact (MK_COMB (@lem2309336) (@lem2309335)). Qed.
Lemma lem2309339 (x : int) : (term20 x) = (term21 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2309340 : term19 = term22.
Proof. exact (@lem2309339 term15). Qed.
Lemma lem2309341 : term18 = term22.
Proof. exact (TRANS (@lem2309337) (@lem2309340)). Qed.
Lemma lem2309342 (x : int) : ((term2 x) = term18) = ((term3 x) = term22).
Proof. exact (MK_COMB (@lem2309332 x) (@lem2309341)). Qed.
Lemma lem2309344 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2309345 (x : int) : ((term3 x) = term22) = ((int_sgn x) = term23).
Proof. exact (@lem2309344 (int_sgn x) term23). Qed.
Lemma lem2309346 (x : int) : ((term2 x) = term18) = ((int_sgn x) = term23).
Proof. exact (TRANS (@lem2309342 x) (@lem2309345 x)). Qed.
Lemma lem2309347 (x : int) : (term24 x) = (term25 x).
Proof. exact (MK_COMB (@lem2309328 x) (@lem2309346 x)). Qed.
Lemma lem2309348 (x : int) : (term1 x) = (term26 x).
Proof. exact (MK_COMB (@lem2309314 x) (@lem2309347 x)). Qed.
Lemma lem2309349 (x : int) : term26 x.
Proof. exact (EQ_MP (@lem2309348 x) (@lem2309300 x)). Qed.
Lemma lem2309350 : term27.
Proof. exact (fun x : int => @lem2309349 x). Qed.
