Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_ADD_RINV_term_abbrevs.
Require Import REAL_ADD_RINV_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2301223 (x : int) : term0 x.
Proof. exact (@lem1353037 (real_of_int x)). Qed.
Lemma lem2301224 (x : int) : (term0 x) = ((term1 x) = term2).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2301225 (x : int) : (term1 x) = term2.
Proof. exact (EQ_MP (@lem2301224 x) (@lem2301223 x)). Qed.
Lemma lem2301227 (x : int) : (term3 x) = (term4 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2301228 (x : int) : (term5 x) = (term5 x).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem2301229 (x : int) : (term1 x) = (term6 x).
Proof. exact (MK_COMB (@lem2301228 x) (@lem2301227 x)). Qed.
Lemma lem2301231 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2301232 (x : int) : (term6 x) = (term9 x).
Proof. exact (@lem2301231 x (int_neg x)). Qed.
Lemma lem2301233 (x : int) : (term1 x) = (term9 x).
Proof. exact (TRANS (@lem2301229 x) (@lem2301232 x)). Qed.
Lemma lem2301234 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2301235 (x : int) : (term10 x) = (term11 x).
Proof. exact (MK_COMB (@lem2301234) (@lem2301233 x)). Qed.
Lemma lem2301237 (n : nat) : (real_of_num n) = (term12 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2301238 : term2 = term13.
Proof. exact (@lem2301237 (NUMERAL 0)). Qed.
Lemma lem2301239 (x : int) : ((term1 x) = term2) = ((term9 x) = term13).
Proof. exact (MK_COMB (@lem2301235 x) (@lem2301238)). Qed.
Lemma lem2301241 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301242 (x : int) : ((term9 x) = term13) = ((term14 x) = term15).
Proof. exact (@lem2301241 (term14 x) term15). Qed.
Lemma lem2301243 (x : int) : ((term1 x) = term2) = ((term14 x) = term15).
Proof. exact (TRANS (@lem2301239 x) (@lem2301242 x)). Qed.
Lemma lem2301244 (x : int) : (term14 x) = term15.
Proof. exact (EQ_MP (@lem2301243 x) (@lem2301225 x)). Qed.
Lemma lem2301245 : term16.
Proof. exact (fun x : int => @lem2301244 x). Qed.
