Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LE_ADDR_term_abbrevs.
Require Import REAL_LE_ADDR_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2302295 (x : int) : term0 x.
Proof. exact (@lem1509970 (real_of_int x)). Qed.
Lemma lem2302296 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2302297 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2302296 x) (@lem2302295 x)). Qed.
Lemma lem2302298 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2302297 x (real_of_int y)). Qed.
Lemma lem2302299 (x : int) (y : int) : (term2 x y) = ((term3 x y) = (term4 y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2302300 (x : int) (y : int) : (term3 x y) = (term4 y).
Proof. exact (EQ_MP (@lem2302299 x y) (@lem2302298 x y)). Qed.
Lemma lem2302302 (x : int) (y : int) : (term5 x y) = (term6 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2302303 (x : int) : (term7 x) = (term7 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem2302304 (x : int) (y : int) : (term3 x y) = (term8 x y).
Proof. exact (MK_COMB (@lem2302303 x) (@lem2302302 x y)). Qed.
Lemma lem2302306 (x : int) (y : int) : (term9 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302307 (x : int) (y : int) : (term8 x y) = (term10 x y).
Proof. exact (@lem2302306 x (int_add x y)). Qed.
Lemma lem2302308 (x : int) (y : int) : (term3 x y) = (term10 x y).
Proof. exact (TRANS (@lem2302304 x y) (@lem2302307 x y)). Qed.
Lemma lem2302309 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2302310 (x : int) (y : int) : (term11 x y) = (term12 x y).
Proof. exact (MK_COMB (@lem2302309) (@lem2302308 x y)). Qed.
Lemma lem2302312 (n : nat) : (real_of_num n) = (term13 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2302313 : term14 = term15.
Proof. exact (@lem2302312 (NUMERAL 0)). Qed.
Lemma lem2302314 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2302315 : term16 = term17.
Proof. exact (MK_COMB (@lem2302314) (@lem2302313)). Qed.
Lemma lem2302316 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2302317 (y : int) : (term4 y) = (term18 y).
Proof. exact (MK_COMB (@lem2302315) (@lem2302316 y)). Qed.
Lemma lem2302319 (x : int) (y : int) : (term9 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302320 (y : int) : (term18 y) = (term19 y).
Proof. exact (@lem2302319 term20 y). Qed.
Lemma lem2302321 (y : int) : (term4 y) = (term19 y).
Proof. exact (TRANS (@lem2302317 y) (@lem2302320 y)). Qed.
Lemma lem2302322 (x : int) (y : int) : ((term3 x y) = (term4 y)) = ((term10 x y) = (term19 y)).
Proof. exact (MK_COMB (@lem2302310 x y) (@lem2302321 y)). Qed.
Lemma lem2302323 (x : int) (y : int) : (term10 x y) = (term19 y).
Proof. exact (EQ_MP (@lem2302322 x y) (@lem2302300 x y)). Qed.
Lemma lem2302324 (x : int) : term21 x.
Proof. exact (fun y : int => @lem2302323 x y). Qed.
Lemma lem2302325 : term22.
Proof. exact (fun x : int => @lem2302324 x). Qed.
