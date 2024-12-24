Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_POW_2_term_abbrevs.
Require Import REAL_MUL_RID_spec.
Require Import thm0_spec.
Require Import thm1005477_spec.
Require Import thm1344310_spec.
Require Import thm1344311_spec.
Require Import thm1344313_spec.
Require Import thm1344314_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm912739_spec.
Require Import thm912741_spec.
Lemma lem1383410 (x : real) : term0 x.
Proof. exact (@lem1383409 x). Qed.
Lemma lem1383411 (x : real) : (term0 x) = ((term1 x) = x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1383413 (x : real) : term2 x.
Proof. exact (EQ_MP (@lem1344314 x) (@lem1344313 x)). Qed.
Lemma lem1383414 (x : real) (n : nat) : term3 x n.
Proof. exact (@lem1383413 x n). Qed.
Lemma lem1383415 (x : real) (n : nat) : (term3 x n) = ((term4 x n) = (term5 x n)).
Proof. exact (eq_refl (term3 x n)). Qed.
Lemma lem1383418 : term6 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1383419 : (term6 = (BIT1 0)) = (term7 = term8).
Proof. exact (@lem1005477 0 (BIT1 0)). Qed.
Lemma lem1383420 : term7 = term8.
Proof. exact (EQ_MP (@lem1383419) (@lem1383418)). Qed.
Lemma lem1383422 : term9 = term10.
Proof. exact (@lem912741). Qed.
Lemma lem1383423 : (term9 = term10) = (term11 = term12).
Proof. exact (@lem1005477 (BIT1 0) term10). Qed.
Lemma lem1383424 : term11 = term12.
Proof. exact (EQ_MP (@lem1383423) (@lem1383422)). Qed.
Lemma lem1383433 : term12 = term11.
Proof. exact (SYM (@lem1383424)). Qed.
Lemma lem1383435 : term8 = term7.
Proof. exact (SYM (@lem1383420)). Qed.
Lemma lem1383436 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem1383437 : term11 = term13.
Proof. exact (MK_COMB (@lem1383436) (@lem1383435)). Qed.
Lemma lem1383438 : term12 = term13.
Proof. exact (TRANS (@lem1383433) (@lem1383437)). Qed.
Lemma lem1383439 (x : real) : (real_pow x) = (real_pow x).
Proof. exact (eq_refl (real_pow x)). Qed.
Lemma lem1383440 (x : real) : (term14 x) = (term15 x).
Proof. exact (MK_COMB (@lem1383439 x) (@lem1383438)). Qed.
Lemma lem1383441 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1383442 (x : real) : (term16 x) = (term17 x).
Proof. exact (MK_COMB (@lem1383441) (@lem1383440 x)). Qed.
Lemma lem1383443 (x : real) : (real_mul x x) = (real_mul x x).
Proof. exact (eq_refl (real_mul x x)). Qed.
Lemma lem1383444 (x : real) : ((term14 x) = (real_mul x x)) = ((term15 x) = (real_mul x x)).
Proof. exact (MK_COMB (@lem1383442 x) (@lem1383443 x)). Qed.
Lemma lem1383447 : term18 = term19.
Proof. exact (fun_ext (fun x : real => @lem1383444 x)). Qed.
Lemma lem1383448 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1383449 : term20 = term21.
Proof. exact (MK_COMB (@lem1383448) (@lem1383447)). Qed.
Lemma lem1383454 : term21 = term20.
Proof. exact (SYM (@lem1383449)). Qed.
Lemma lem1383462 (x : real) (n : nat) : (term4 x n) = (term5 x n).
Proof. exact (EQ_MP (@lem1383415 x n) (@lem1383414 x n)). Qed.
Lemma lem1383463 (x : real) : (term15 x) = (term22 x).
Proof. exact (@lem1383462 x term7). Qed.
Lemma lem1383465 (x : real) (n : nat) : (term4 x n) = (term5 x n).
Proof. exact (EQ_MP (@lem1383415 x n) (@lem1383414 x n)). Qed.
Lemma lem1383466 (x : real) : (term23 x) = (term24 x).
Proof. exact (@lem1383465 x (NUMERAL 0)). Qed.
Lemma lem1383468 (x : real) : (term25 x) = term26.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem1383469 (x : real) : (real_mul x) = (real_mul x).
Proof. exact (eq_refl (real_mul x)). Qed.
Lemma lem1383470 (x : real) : (term24 x) = (term1 x).
Proof. exact (MK_COMB (@lem1383469 x) (@lem1383468 x)). Qed.
Lemma lem1383472 (x : real) : (term1 x) = x.
Proof. exact (EQ_MP (@lem1383411 x) (@lem1383410 x)). Qed.
Lemma lem1383473 (x : real) : (term24 x) = x.
Proof. exact (TRANS (@lem1383470 x) (@lem1383472 x)). Qed.
Lemma lem1383474 (x : real) : (term23 x) = x.
Proof. exact (TRANS (@lem1383466 x) (@lem1383473 x)). Qed.
Lemma lem1383475 (x : real) : (real_mul x) = (real_mul x).
Proof. exact (eq_refl (real_mul x)). Qed.
Lemma lem1383476 (x : real) : (term22 x) = (real_mul x x).
Proof. exact (MK_COMB (@lem1383475 x) (@lem1383474 x)). Qed.
Lemma lem1383477 (x : real) : (term15 x) = (real_mul x x).
Proof. exact (TRANS (@lem1383463 x) (@lem1383476 x)). Qed.
Lemma lem1383478 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1383479 (x : real) : (term17 x) = (term27 x).
Proof. exact (MK_COMB (@lem1383478) (@lem1383477 x)). Qed.
Lemma lem1383480 (x : real) : (real_mul x x) = (real_mul x x).
Proof. exact (eq_refl (real_mul x x)). Qed.
Lemma lem1383481 (x : real) : ((term15 x) = (real_mul x x)) = ((real_mul x x) = (real_mul x x)).
Proof. exact (MK_COMB (@lem1383479 x) (@lem1383480 x)). Qed.
Lemma lem1383483 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1383484 (x : real) : (x = x) = True.
Proof. exact (@lem1383483 real x). Qed.
Lemma lem1383485 (x : real) : ((real_mul x x) = (real_mul x x)) = True.
Proof. exact (@lem1383484 (real_mul x x)). Qed.
Lemma lem1383486 (x : real) : ((term15 x) = (real_mul x x)) = True.
Proof. exact (TRANS (@lem1383481 x) (@lem1383485 x)). Qed.
Lemma lem1383487 : term19 = term28.
Proof. exact (fun_ext (fun x : real => @lem1383486 x)). Qed.
Lemma lem1383488 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1383489 : term21 = term29.
Proof. exact (MK_COMB (@lem1383488) (@lem1383487)). Qed.
Lemma lem1383491 {A : Type'} (t : Prop) : (term30 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1383492 (t : Prop) : (term31 t) = t.
Proof. exact (@lem1383491 real t). Qed.
Lemma lem1383493 : term29 = True.
Proof. exact (@lem1383492 True). Qed.
Lemma lem1383494 : term21 = True.
Proof. exact (TRANS (@lem1383489) (@lem1383493)). Qed.
Lemma lem1383495 : True = term21.
Proof. exact (SYM (@lem1383494)). Qed.
Lemma lem1383496 : term21.
Proof. exact (EQ_MP (@lem1383495) (@lem0)). Qed.
Lemma lem1383497 : term20.
Proof. exact (EQ_MP (@lem1383454) (@lem1383496)). Qed.
