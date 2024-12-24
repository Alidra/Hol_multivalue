Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_MUL_ASSOC_term_abbrevs.
Require Import NADD_EQ_REFL_spec.
Require Import NADD_MUL_spec.
Require Import nadd_mul_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm7_spec.
Lemma lem1278400 (x : nadd) : term0 x.
Proof. exact (@lem1267990 x). Qed.
Lemma lem1278401 (x : nadd) : (term0 x) = (nadd_eq x x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1278402 (x : nadd) : nadd_eq x x.
Proof. exact (EQ_MP (@lem1278401 x) (@lem1278400 x)). Qed.
Lemma lem1278403 (x : nadd) : (nadd_eq x x) = ((nadd_eq x x) = True).
Proof. exact (@lem7 (nadd_eq x x)). Qed.
Lemma lem1278405 (x : nadd) : term1 x.
Proof. exact (@lem1277879 x). Qed.
Lemma lem1278406 (x : nadd) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1278407 (x : nadd) : term2 x.
Proof. exact (EQ_MP (@lem1278406 x) (@lem1278405 x)). Qed.
Lemma lem1278408 (x : nadd) (y : nadd) : term3 x y.
Proof. exact (@lem1278407 x y). Qed.
Lemma lem1278409 (x : nadd) (y : nadd) : (term3 x y) = ((term4 x y) = (term5 x y)).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem1278411 (x : nadd) : term6 x.
Proof. exact (@lem1276766 x). Qed.
Lemma lem1278412 (x : nadd) : (term6 x) = (term7 x).
Proof. exact (eq_refl (term6 x)). Qed.
Lemma lem1278413 (x : nadd) : term7 x.
Proof. exact (EQ_MP (@lem1278412 x) (@lem1278411 x)). Qed.
Lemma lem1278414 (x : nadd) (y : nadd) : term8 x y.
Proof. exact (@lem1278413 x y). Qed.
Lemma lem1278415 (x : nadd) (y : nadd) : (term8 x y) = ((nadd_mul x y) = (term9 x y)).
Proof. exact (eq_refl (term8 x y)). Qed.
Lemma lem1278418 (x : nadd) (y : nadd) : (nadd_mul x y) = (term9 x y).
Proof. exact (EQ_MP (@lem1278415 x y) (@lem1278414 x y)). Qed.
Lemma lem1278419 (x : nadd) (y : nadd) (z : nadd) : (term10 x y z) = (term11 x y z).
Proof. exact (@lem1278418 x (nadd_mul y z)). Qed.
Lemma lem1278420 : nadd_eq = nadd_eq.
Proof. exact (eq_refl nadd_eq). Qed.
Lemma lem1278421 (x : nadd) (y : nadd) (z : nadd) : (term12 x y z) = (term13 x y z).
Proof. exact (MK_COMB (@lem1278420) (@lem1278419 x y z)). Qed.
Lemma lem1278423 (x : nadd) (y : nadd) : (nadd_mul x y) = (term9 x y).
Proof. exact (EQ_MP (@lem1278415 x y) (@lem1278414 x y)). Qed.
Lemma lem1278424 (x : nadd) (y : nadd) (z : nadd) : (term14 x y z) = (term15 x y z).
Proof. exact (@lem1278423 (nadd_mul x y) z). Qed.
Lemma lem1278425 (x : nadd) (y : nadd) (z : nadd) : (term16 x y z) = (term17 x y z).
Proof. exact (MK_COMB (@lem1278421 x y z) (@lem1278424 x y z)). Qed.
Lemma lem1278426 (x : nadd) (y : nadd) (z : nadd) : (term17 x y z) = (term16 x y z).
Proof. exact (SYM (@lem1278425 x y z)). Qed.
Lemma lem1278430 (x : nadd) (y : nadd) : (term4 x y) = (term5 x y).
Proof. exact (EQ_MP (@lem1278409 x y) (@lem1278408 x y)). Qed.
Lemma lem1278431 (y : nadd) (z : nadd) : (term4 y z) = (term5 y z).
Proof. exact (@lem1278430 y z). Qed.
Lemma lem1278432 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1278433 (y : nadd) (z : nadd) (n : nat) : (term18 y z n) = (term19 y z n).
Proof. exact (MK_COMB (@lem1278431 y z) (@lem1278432 n)). Qed.
Lemma lem1278435 {A B : Type'} (f : A -> B) (y : A) : (term20 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1278436 (f : nat -> nat) (y : nat) : (term21 f y) = (f y).
Proof. exact (@lem1278435 nat nat f y). Qed.
Lemma lem1278437 (y : nadd) (z : nadd) (n : nat) : (term22 y z n) = (term19 y z n).
Proof. exact (@lem1278436 (term5 y z) n). Qed.
Lemma lem1278438 (y : nadd) (z : nadd) (n : nat) : (term19 y z n) = (term23 y z n).
Proof. exact (eq_refl (term19 y z n)). Qed.
Lemma lem1278439 (y : nadd) (z : nadd) : (term24 y z) = (term5 y z).
Proof. exact (fun_ext (fun n : nat => @lem1278438 y z n)). Qed.
Lemma lem1278440 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1278441 (y : nadd) (z : nadd) (n : nat) : (term22 y z n) = (term19 y z n).
Proof. exact (MK_COMB (@lem1278439 y z) (@lem1278440 n)). Qed.
Lemma lem1278442 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1278443 (y : nadd) (z : nadd) (n : nat) : (term25 y z n) = (term26 y z n).
Proof. exact (MK_COMB (@lem1278442) (@lem1278441 y z n)). Qed.
Lemma lem1278444 (y : nadd) (z : nadd) (n : nat) : (term19 y z n) = (term23 y z n).
Proof. exact (eq_refl (term19 y z n)). Qed.
Lemma lem1278445 (y : nadd) (z : nadd) (n : nat) : ((term22 y z n) = (term19 y z n)) = ((term19 y z n) = (term23 y z n)).
Proof. exact (MK_COMB (@lem1278443 y z n) (@lem1278444 y z n)). Qed.
Lemma lem1278446 (y : nadd) (z : nadd) (n : nat) : (term19 y z n) = (term23 y z n).
Proof. exact (EQ_MP (@lem1278445 y z n) (@lem1278437 y z n)). Qed.
Lemma lem1278447 (y : nadd) (z : nadd) (n : nat) : (term18 y z n) = (term23 y z n).
Proof. exact (TRANS (@lem1278433 y z n) (@lem1278446 y z n)). Qed.
Lemma lem1278448 (x : nadd) : (dest_nadd x) = (dest_nadd x).
Proof. exact (eq_refl (dest_nadd x)). Qed.
Lemma lem1278449 (x : nadd) (y : nadd) (z : nadd) (n : nat) : (term27 x y z n) = (term28 x y z n).
Proof. exact (MK_COMB (@lem1278448 x) (@lem1278447 y z n)). Qed.
Lemma lem1278450 (x : nadd) (y : nadd) (z : nadd) : (term29 x y z) = (term30 x y z).
Proof. exact (fun_ext (fun n : nat => @lem1278449 x y z n)). Qed.
Lemma lem1278451 : mk_nadd = mk_nadd.
Proof. exact (eq_refl mk_nadd). Qed.
Lemma lem1278452 (x : nadd) (y : nadd) (z : nadd) : (term11 x y z) = (term31 x y z).
Proof. exact (MK_COMB (@lem1278451) (@lem1278450 x y z)). Qed.
Lemma lem1278453 : nadd_eq = nadd_eq.
Proof. exact (eq_refl nadd_eq). Qed.
Lemma lem1278454 (x : nadd) (y : nadd) (z : nadd) : (term13 x y z) = (term32 x y z).
Proof. exact (MK_COMB (@lem1278453) (@lem1278452 x y z)). Qed.
Lemma lem1278456 (x : nadd) (y : nadd) : (term4 x y) = (term5 x y).
Proof. exact (EQ_MP (@lem1278409 x y) (@lem1278408 x y)). Qed.
Lemma lem1278457 (z : nadd) (n : nat) : (dest_nadd z n) = (dest_nadd z n).
Proof. exact (eq_refl (dest_nadd z n)). Qed.
Lemma lem1278458 (x : nadd) (y : nadd) (z : nadd) (n : nat) : (term33 x y z n) = (term34 x y z n).
Proof. exact (MK_COMB (@lem1278456 x y) (@lem1278457 z n)). Qed.
Lemma lem1278460 {A B : Type'} (f : A -> B) (y : A) : (term20 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1278461 (f : nat -> nat) (y : nat) : (term21 f y) = (f y).
Proof. exact (@lem1278460 nat nat f y). Qed.
Lemma lem1278462 (x : nadd) (y : nadd) (z : nadd) (n : nat) : (term35 x y z n) = (term34 x y z n).
Proof. exact (@lem1278461 (term5 x y) (dest_nadd z n)). Qed.
Lemma lem1278463 (x : nadd) (y : nadd) (n : nat) : (term19 x y n) = (term23 x y n).
Proof. exact (eq_refl (term19 x y n)). Qed.
Lemma lem1278464 (x : nadd) (y : nadd) : (term24 x y) = (term5 x y).
Proof. exact (fun_ext (fun n : nat => @lem1278463 x y n)). Qed.
Lemma lem1278465 (z : nadd) (n : nat) : (dest_nadd z n) = (dest_nadd z n).
Proof. exact (eq_refl (dest_nadd z n)). Qed.
Lemma lem1278466 (x : nadd) (y : nadd) (z : nadd) (n : nat) : (term35 x y z n) = (term34 x y z n).
Proof. exact (MK_COMB (@lem1278464 x y) (@lem1278465 z n)). Qed.
Lemma lem1278467 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1278468 (x : nadd) (y : nadd) (z : nadd) (n : nat) : (term36 x y z n) = (term37 x y z n).
Proof. exact (MK_COMB (@lem1278467) (@lem1278466 x y z n)). Qed.
Lemma lem1278469 (x : nadd) (y : nadd) (z : nadd) (n : nat) : (term34 x y z n) = (term28 x y z n).
Proof. exact (eq_refl (term34 x y z n)). Qed.
Lemma lem1278470 (x : nadd) (y : nadd) (z : nadd) (n : nat) : ((term35 x y z n) = (term34 x y z n)) = ((term34 x y z n) = (term28 x y z n)).
Proof. exact (MK_COMB (@lem1278468 x y z n) (@lem1278469 x y z n)). Qed.
Lemma lem1278471 (x : nadd) (y : nadd) (z : nadd) (n : nat) : (term34 x y z n) = (term28 x y z n).
Proof. exact (EQ_MP (@lem1278470 x y z n) (@lem1278462 x y z n)). Qed.
Lemma lem1278472 (x : nadd) (y : nadd) (z : nadd) (n : nat) : (term33 x y z n) = (term28 x y z n).
Proof. exact (TRANS (@lem1278458 x y z n) (@lem1278471 x y z n)). Qed.
Lemma lem1278473 (x : nadd) (y : nadd) (z : nadd) : (term38 x y z) = (term30 x y z).
Proof. exact (fun_ext (fun n : nat => @lem1278472 x y z n)). Qed.
Lemma lem1278474 : mk_nadd = mk_nadd.
Proof. exact (eq_refl mk_nadd). Qed.
Lemma lem1278475 (x : nadd) (y : nadd) (z : nadd) : (term15 x y z) = (term31 x y z).
Proof. exact (MK_COMB (@lem1278474) (@lem1278473 x y z)). Qed.
Lemma lem1278476 (x : nadd) (y : nadd) (z : nadd) : (term17 x y z) = (term39 x y z).
Proof. exact (MK_COMB (@lem1278454 x y z) (@lem1278475 x y z)). Qed.
Lemma lem1278478 (x : nadd) : (nadd_eq x x) = True.
Proof. exact (EQ_MP (@lem1278403 x) (@lem1278402 x)). Qed.
Lemma lem1278479 (x : nadd) (y : nadd) (z : nadd) : (term39 x y z) = True.
Proof. exact (@lem1278478 (term31 x y z)). Qed.
Lemma lem1278480 (x : nadd) (y : nadd) (z : nadd) : (term17 x y z) = True.
Proof. exact (TRANS (@lem1278476 x y z) (@lem1278479 x y z)). Qed.
Lemma lem1278481 (x : nadd) (y : nadd) (z : nadd) : True = (term17 x y z).
Proof. exact (SYM (@lem1278480 x y z)). Qed.
Lemma lem1278482 (x : nadd) (y : nadd) (z : nadd) : term17 x y z.
Proof. exact (EQ_MP (@lem1278481 x y z) (@lem0)). Qed.
Lemma lem1278483 (x : nadd) (y : nadd) (z : nadd) : term16 x y z.
Proof. exact (EQ_MP (@lem1278426 x y z) (@lem1278482 x y z)). Qed.
Lemma lem1278488 (x : nadd) (y : nadd) : term40 x y.
Proof. exact (fun z : nadd => @lem1278483 x y z). Qed.
Lemma lem1278493 (x : nadd) : term41 x.
Proof. exact (fun y : nadd => @lem1278488 x y). Qed.
Lemma lem1278498 : term42.
Proof. exact (fun x : nadd => @lem1278493 x). Qed.
