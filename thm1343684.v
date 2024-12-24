Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1343684_term_abbrevs.
Require Import BETA_THM_spec.
Require Import SKOLEM_THM_spec.
Require Import thm75635_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem1343435 {A B : Type'} (f : A -> B) : term0 A B f.
Proof. exact (@lem421 A B f). Qed.
Lemma lem1343436 {A B : Type'} (f : A -> B) : (term0 A B f) = (term1 A B f).
Proof. exact (eq_refl (term0 A B f)). Qed.
Lemma lem1343437 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (EQ_MP (@lem1343436 A B f) (@lem1343435 A B f)). Qed.
Lemma lem1343438 {A B : Type'} (f : A -> B) (y : A) : term2 A B f y.
Proof. exact (@lem1343437 A B f y). Qed.
Lemma lem1343439 {A B : Type'} (f : A -> B) (y : A) : (term2 A B f y) = ((term3 A B f y) = (f y)).
Proof. exact (eq_refl (term2 A B f y)). Qed.
Lemma lem1343442 (real_pow' : type1623) (_23954 : type1608) (h1 : real_pow' = (term4 _23954)) : real_pow' = (term4 _23954).
Proof. exact (h1). Qed.
Lemma lem1343443 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1343444 (x : real) (real_pow' : type1623) (_23954 : type1608) (h1 : real_pow' = (term4 _23954)) : (real_pow' x) = (term5 _23954 x).
Proof. exact (MK_COMB (@lem1343442 real_pow' _23954 h1) (@lem1343443 x)). Qed.
Lemma lem1343446 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1343439 A B f y) (@lem1343438 A B f y)). Qed.
Lemma lem1343447 (f : type1623) (y : real) : (term6 f y) = (f y).
Proof. exact (@lem1343446 real (nat -> real) f y). Qed.
Lemma lem1343448 (_23954 : type1608) (x : real) : (term7 _23954 x) = (term5 _23954 x).
Proof. exact (@lem1343447 (term4 _23954) x). Qed.
Lemma lem1343449 (_23954 : type1608) (_23952 : real) : (term5 _23954 _23952) = (term8 _23954 _23952).
Proof. exact (eq_refl (term5 _23954 _23952)). Qed.
Lemma lem1343450 (_23954 : type1608) : (term9 _23954) = (term4 _23954).
Proof. exact (fun_ext (fun _23952 : real => @lem1343449 _23954 _23952)). Qed.
Lemma lem1343451 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1343452 (_23954 : type1608) (x : real) : (term7 _23954 x) = (term5 _23954 x).
Proof. exact (MK_COMB (@lem1343450 _23954) (@lem1343451 x)). Qed.
Lemma lem1343453 : (@eq (nat -> real)) = (@eq (nat -> real)).
Proof. exact (eq_refl (@eq (nat -> real))). Qed.
Lemma lem1343454 (_23954 : type1608) (x : real) : (term10 _23954 x) = (term11 _23954 x).
Proof. exact (MK_COMB (@lem1343453) (@lem1343452 _23954 x)). Qed.
Lemma lem1343455 (_23954 : type1608) (x : real) : (term5 _23954 x) = (term8 _23954 x).
Proof. exact (eq_refl (term5 _23954 x)). Qed.
Lemma lem1343456 (_23954 : type1608) (x : real) : ((term7 _23954 x) = (term5 _23954 x)) = ((term5 _23954 x) = (term8 _23954 x)).
Proof. exact (MK_COMB (@lem1343454 _23954 x) (@lem1343455 _23954 x)). Qed.
Lemma lem1343457 (_23954 : type1608) (x : real) : (term5 _23954 x) = (term8 _23954 x).
Proof. exact (EQ_MP (@lem1343456 _23954 x) (@lem1343448 _23954 x)). Qed.
Lemma lem1343458 (x : real) (real_pow' : type1623) (_23954 : type1608) (h1 : real_pow' = (term4 _23954)) : (real_pow' x) = (term8 _23954 x).
Proof. exact (TRANS (@lem1343444 x real_pow' _23954 h1) (@lem1343457 _23954 x)). Qed.
Lemma lem1343459 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1343460 (x : real) (real_pow' : type1623) (_23954 : type1608) (h1 : real_pow' = (term4 _23954)) : (term12 real_pow' x) = (term13 _23954 x).
Proof. exact (MK_COMB (@lem1343458 x real_pow' _23954 h1) (@lem1343459)). Qed.
Lemma lem1343462 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1343439 A B f y) (@lem1343438 A B f y)). Qed.
Lemma lem1343463 (f : nat -> real) (y : nat) : (term14 f y) = (f y).
Proof. exact (@lem1343462 nat real f y). Qed.
Lemma lem1343464 (_23954 : type1608) (x : real) : (term15 _23954 x) = (term13 _23954 x).
Proof. exact (@lem1343463 (term8 _23954 x) (NUMERAL 0)). Qed.
Lemma lem1343465 (_23954 : type1608) (_23953 : nat) (x : real) : (term16 _23954 x _23953) = (_23954 _23953 x).
Proof. exact (eq_refl (term16 _23954 x _23953)). Qed.
Lemma lem1343466 (_23954 : type1608) (x : real) : (term17 _23954 x) = (term8 _23954 x).
Proof. exact (fun_ext (fun _23953 : nat => @lem1343465 _23954 _23953 x)). Qed.
Lemma lem1343467 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1343468 (_23954 : type1608) (x : real) : (term15 _23954 x) = (term13 _23954 x).
Proof. exact (MK_COMB (@lem1343466 _23954 x) (@lem1343467)). Qed.
Lemma lem1343469 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1343470 (_23954 : type1608) (x : real) : (term18 _23954 x) = (term19 _23954 x).
Proof. exact (MK_COMB (@lem1343469) (@lem1343468 _23954 x)). Qed.
Lemma lem1343471 (_23954 : type1608) (x : real) : (term13 _23954 x) = (term20 _23954 x).
Proof. exact (eq_refl (term13 _23954 x)). Qed.
Lemma lem1343472 (_23954 : type1608) (x : real) : ((term15 _23954 x) = (term13 _23954 x)) = ((term13 _23954 x) = (term20 _23954 x)).
Proof. exact (MK_COMB (@lem1343470 _23954 x) (@lem1343471 _23954 x)). Qed.
Lemma lem1343473 (_23954 : type1608) (x : real) : (term13 _23954 x) = (term20 _23954 x).
Proof. exact (EQ_MP (@lem1343472 _23954 x) (@lem1343464 _23954 x)). Qed.
Lemma lem1343474 (x : real) (real_pow' : type1623) (_23954 : type1608) (h1 : real_pow' = (term4 _23954)) : (term12 real_pow' x) = (term20 _23954 x).
Proof. exact (TRANS (@lem1343460 x real_pow' _23954 h1) (@lem1343473 _23954 x)). Qed.
Lemma lem1343475 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1343476 (x : real) (real_pow' : type1623) (_23954 : type1608) (h1 : real_pow' = (term4 _23954)) : (term21 real_pow' x) = (term22 _23954 x).
Proof. exact (MK_COMB (@lem1343475) (@lem1343474 x real_pow' _23954 h1)). Qed.
Lemma lem1343477 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem1343478 (x : real) (real_pow' : type1623) (_23954 : type1608) (h1 : real_pow' = (term4 _23954)) : ((term12 real_pow' x) = term23) = ((term20 _23954 x) = term23).
Proof. exact (MK_COMB (@lem1343476 x real_pow' _23954 h1) (@lem1343477)). Qed.
Lemma lem1343479 (real_pow' : type1623) (_23954 : type1608) (h1 : real_pow' = (term4 _23954)) : (term24 real_pow') = (term25 _23954).
Proof. exact (fun_ext (fun x : real => @lem1343478 x real_pow' _23954 h1)). Qed.
Lemma lem1343480 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1343481 (real_pow' : type1623) (_23954 : type1608) (h1 : real_pow' = (term4 _23954)) : (term26 real_pow') = (term27 _23954).
Proof. exact (MK_COMB (@lem1343480) (@lem1343479 real_pow' _23954 h1)). Qed.
Lemma lem1343482 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1343483 (real_pow' : type1623) (_23954 : type1608) (h1 : real_pow' = (term4 _23954)) : (term28 real_pow') = (term29 _23954).
Proof. exact (MK_COMB (@lem1343482) (@lem1343481 real_pow' _23954 h1)). Qed.
Lemma lem1343485 (real_pow' : type1623) (_23954 : type1608) (h1 : real_pow' = (term4 _23954)) : real_pow' = (term4 _23954).
Proof. exact (h1). Qed.
Lemma lem1343486 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1343487 (x : real) (real_pow' : type1623) (_23954 : type1608) (h1 : real_pow' = (term4 _23954)) : (real_pow' x) = (term5 _23954 x).
Proof. exact (MK_COMB (@lem1343485 real_pow' _23954 h1) (@lem1343486 x)). Qed.
Lemma lem1343489 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1343439 A B f y) (@lem1343438 A B f y)). Qed.
Lemma lem1343490 (f : type1623) (y : real) : (term6 f y) = (f y).
Proof. exact (@lem1343489 real (nat -> real) f y). Qed.
Lemma lem1343491 (_23954 : type1608) (x : real) : (term7 _23954 x) = (term5 _23954 x).
Proof. exact (@lem1343490 (term4 _23954) x). Qed.
Lemma lem1343492 (_23954 : type1608) (_23952 : real) : (term5 _23954 _23952) = (term8 _23954 _23952).
Proof. exact (eq_refl (term5 _23954 _23952)). Qed.
Lemma lem1343493 (_23954 : type1608) : (term9 _23954) = (term4 _23954).
Proof. exact (fun_ext (fun _23952 : real => @lem1343492 _23954 _23952)). Qed.
Lemma lem1343494 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1343495 (_23954 : type1608) (x : real) : (term7 _23954 x) = (term5 _23954 x).
Proof. exact (MK_COMB (@lem1343493 _23954) (@lem1343494 x)). Qed.
Lemma lem1343496 : (@eq (nat -> real)) = (@eq (nat -> real)).
Proof. exact (eq_refl (@eq (nat -> real))). Qed.
Lemma lem1343497 (_23954 : type1608) (x : real) : (term10 _23954 x) = (term11 _23954 x).
Proof. exact (MK_COMB (@lem1343496) (@lem1343495 _23954 x)). Qed.
Lemma lem1343498 (_23954 : type1608) (x : real) : (term5 _23954 x) = (term8 _23954 x).
Proof. exact (eq_refl (term5 _23954 x)). Qed.
Lemma lem1343499 (_23954 : type1608) (x : real) : ((term7 _23954 x) = (term5 _23954 x)) = ((term5 _23954 x) = (term8 _23954 x)).
Proof. exact (MK_COMB (@lem1343497 _23954 x) (@lem1343498 _23954 x)). Qed.
Lemma lem1343500 (_23954 : type1608) (x : real) : (term5 _23954 x) = (term8 _23954 x).
Proof. exact (EQ_MP (@lem1343499 _23954 x) (@lem1343491 _23954 x)). Qed.
Lemma lem1343501 (x : real) (real_pow' : type1623) (_23954 : type1608) (h1 : real_pow' = (term4 _23954)) : (real_pow' x) = (term8 _23954 x).
Proof. exact (TRANS (@lem1343487 x real_pow' _23954 h1) (@lem1343500 _23954 x)). Qed.
Lemma lem1343502 (n : nat) : (S n) = (S n).
Proof. exact (eq_refl (S n)). Qed.
Lemma lem1343503 (x : real) (n : nat) (real_pow' : type1623) (_23954 : type1608) (h1 : real_pow' = (term4 _23954)) : (term30 real_pow' x n) = (term31 _23954 x n).
Proof. exact (MK_COMB (@lem1343501 x real_pow' _23954 h1) (@lem1343502 n)). Qed.
Lemma lem1343505 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1343439 A B f y) (@lem1343438 A B f y)). Qed.
Lemma lem1343506 (f : nat -> real) (y : nat) : (term14 f y) = (f y).
Proof. exact (@lem1343505 nat real f y). Qed.
Lemma lem1343507 (_23954 : type1608) (x : real) (n : nat) : (term32 _23954 x n) = (term31 _23954 x n).
Proof. exact (@lem1343506 (term8 _23954 x) (S n)). Qed.
Lemma lem1343508 (_23954 : type1608) (_23953 : nat) (x : real) : (term16 _23954 x _23953) = (_23954 _23953 x).
Proof. exact (eq_refl (term16 _23954 x _23953)). Qed.
Lemma lem1343509 (_23954 : type1608) (x : real) : (term17 _23954 x) = (term8 _23954 x).
Proof. exact (fun_ext (fun _23953 : nat => @lem1343508 _23954 _23953 x)). Qed.
Lemma lem1343510 (n : nat) : (S n) = (S n).
Proof. exact (eq_refl (S n)). Qed.
Lemma lem1343511 (_23954 : type1608) (x : real) (n : nat) : (term32 _23954 x n) = (term31 _23954 x n).
Proof. exact (MK_COMB (@lem1343509 _23954 x) (@lem1343510 n)). Qed.
Lemma lem1343512 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1343513 (_23954 : type1608) (x : real) (n : nat) : (term33 _23954 x n) = (term34 _23954 x n).
Proof. exact (MK_COMB (@lem1343512) (@lem1343511 _23954 x n)). Qed.
Lemma lem1343514 (_23954 : type1608) (n : nat) (x : real) : (term31 _23954 x n) = (term35 _23954 n x).
Proof. exact (eq_refl (term31 _23954 x n)). Qed.
Lemma lem1343515 (_23954 : type1608) (n : nat) (x : real) : ((term32 _23954 x n) = (term31 _23954 x n)) = ((term31 _23954 x n) = (term35 _23954 n x)).
Proof. exact (MK_COMB (@lem1343513 _23954 x n) (@lem1343514 _23954 n x)). Qed.
Lemma lem1343516 (_23954 : type1608) (n : nat) (x : real) : (term31 _23954 x n) = (term35 _23954 n x).
Proof. exact (EQ_MP (@lem1343515 _23954 n x) (@lem1343507 _23954 x n)). Qed.
Lemma lem1343517 (n : nat) (x : real) (real_pow' : type1623) (_23954 : type1608) (h1 : real_pow' = (term4 _23954)) : (term30 real_pow' x n) = (term35 _23954 n x).
Proof. exact (TRANS (@lem1343503 x n real_pow' _23954 h1) (@lem1343516 _23954 n x)). Qed.
Lemma lem1343518 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1343519 (n : nat) (x : real) (real_pow' : type1623) (_23954 : type1608) (h1 : real_pow' = (term4 _23954)) : (term36 real_pow' x n) = (term37 _23954 n x).
Proof. exact (MK_COMB (@lem1343518) (@lem1343517 n x real_pow' _23954 h1)). Qed.
Lemma lem1343521 (real_pow' : type1623) (_23954 : type1608) (h1 : real_pow' = (term4 _23954)) : real_pow' = (term4 _23954).
Proof. exact (h1). Qed.
Lemma lem1343522 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1343523 (x : real) (real_pow' : type1623) (_23954 : type1608) (h1 : real_pow' = (term4 _23954)) : (real_pow' x) = (term5 _23954 x).
Proof. exact (MK_COMB (@lem1343521 real_pow' _23954 h1) (@lem1343522 x)). Qed.
Lemma lem1343525 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1343439 A B f y) (@lem1343438 A B f y)). Qed.
Lemma lem1343526 (f : type1623) (y : real) : (term6 f y) = (f y).
Proof. exact (@lem1343525 real (nat -> real) f y). Qed.
Lemma lem1343527 (_23954 : type1608) (x : real) : (term7 _23954 x) = (term5 _23954 x).
Proof. exact (@lem1343526 (term4 _23954) x). Qed.
Lemma lem1343528 (_23954 : type1608) (_23952 : real) : (term5 _23954 _23952) = (term8 _23954 _23952).
Proof. exact (eq_refl (term5 _23954 _23952)). Qed.
Lemma lem1343529 (_23954 : type1608) : (term9 _23954) = (term4 _23954).
Proof. exact (fun_ext (fun _23952 : real => @lem1343528 _23954 _23952)). Qed.
Lemma lem1343530 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1343531 (_23954 : type1608) (x : real) : (term7 _23954 x) = (term5 _23954 x).
Proof. exact (MK_COMB (@lem1343529 _23954) (@lem1343530 x)). Qed.
Lemma lem1343532 : (@eq (nat -> real)) = (@eq (nat -> real)).
Proof. exact (eq_refl (@eq (nat -> real))). Qed.
Lemma lem1343533 (_23954 : type1608) (x : real) : (term10 _23954 x) = (term11 _23954 x).
Proof. exact (MK_COMB (@lem1343532) (@lem1343531 _23954 x)). Qed.
Lemma lem1343534 (_23954 : type1608) (x : real) : (term5 _23954 x) = (term8 _23954 x).
Proof. exact (eq_refl (term5 _23954 x)). Qed.
Lemma lem1343535 (_23954 : type1608) (x : real) : ((term7 _23954 x) = (term5 _23954 x)) = ((term5 _23954 x) = (term8 _23954 x)).
Proof. exact (MK_COMB (@lem1343533 _23954 x) (@lem1343534 _23954 x)). Qed.
Lemma lem1343536 (_23954 : type1608) (x : real) : (term5 _23954 x) = (term8 _23954 x).
Proof. exact (EQ_MP (@lem1343535 _23954 x) (@lem1343527 _23954 x)). Qed.
Lemma lem1343537 (x : real) (real_pow' : type1623) (_23954 : type1608) (h1 : real_pow' = (term4 _23954)) : (real_pow' x) = (term8 _23954 x).
Proof. exact (TRANS (@lem1343523 x real_pow' _23954 h1) (@lem1343536 _23954 x)). Qed.
Lemma lem1343538 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1343539 (x : real) (n : nat) (real_pow' : type1623) (_23954 : type1608) (h1 : real_pow' = (term4 _23954)) : (real_pow' x n) = (term16 _23954 x n).
Proof. exact (MK_COMB (@lem1343537 x real_pow' _23954 h1) (@lem1343538 n)). Qed.
Lemma lem1343541 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1343439 A B f y) (@lem1343438 A B f y)). Qed.
Lemma lem1343542 (f : nat -> real) (y : nat) : (term14 f y) = (f y).
Proof. exact (@lem1343541 nat real f y). Qed.
Lemma lem1343543 (_23954 : type1608) (x : real) (n : nat) : (term38 _23954 x n) = (term16 _23954 x n).
Proof. exact (@lem1343542 (term8 _23954 x) n). Qed.
Lemma lem1343544 (_23954 : type1608) (_23953 : nat) (x : real) : (term16 _23954 x _23953) = (_23954 _23953 x).
Proof. exact (eq_refl (term16 _23954 x _23953)). Qed.
Lemma lem1343545 (_23954 : type1608) (x : real) : (term17 _23954 x) = (term8 _23954 x).
Proof. exact (fun_ext (fun _23953 : nat => @lem1343544 _23954 _23953 x)). Qed.
Lemma lem1343546 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1343547 (_23954 : type1608) (x : real) (n : nat) : (term38 _23954 x n) = (term16 _23954 x n).
Proof. exact (MK_COMB (@lem1343545 _23954 x) (@lem1343546 n)). Qed.
Lemma lem1343548 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1343549 (_23954 : type1608) (x : real) (n : nat) : (term39 _23954 x n) = (term40 _23954 x n).
Proof. exact (MK_COMB (@lem1343548) (@lem1343547 _23954 x n)). Qed.
Lemma lem1343550 (_23954 : type1608) (n : nat) (x : real) : (term16 _23954 x n) = (_23954 n x).
Proof. exact (eq_refl (term16 _23954 x n)). Qed.
Lemma lem1343551 (_23954 : type1608) (n : nat) (x : real) : ((term38 _23954 x n) = (term16 _23954 x n)) = ((term16 _23954 x n) = (_23954 n x)).
Proof. exact (MK_COMB (@lem1343549 _23954 x n) (@lem1343550 _23954 n x)). Qed.
Lemma lem1343552 (_23954 : type1608) (n : nat) (x : real) : (term16 _23954 x n) = (_23954 n x).
Proof. exact (EQ_MP (@lem1343551 _23954 n x) (@lem1343543 _23954 x n)). Qed.
Lemma lem1343553 (n : nat) (x : real) (real_pow' : type1623) (_23954 : type1608) (h1 : real_pow' = (term4 _23954)) : (real_pow' x n) = (_23954 n x).
Proof. exact (TRANS (@lem1343539 x n real_pow' _23954 h1) (@lem1343552 _23954 n x)). Qed.
Lemma lem1343554 (x : real) : (real_mul x) = (real_mul x).
Proof. exact (eq_refl (real_mul x)). Qed.
Lemma lem1343555 (n : nat) (x : real) (real_pow' : type1623) (_23954 : type1608) (h1 : real_pow' = (term4 _23954)) : (term41 real_pow' x n) = (term42 _23954 n x).
Proof. exact (MK_COMB (@lem1343554 x) (@lem1343553 n x real_pow' _23954 h1)). Qed.
Lemma lem1343556 (n : nat) (x : real) (real_pow' : type1623) (_23954 : type1608) (h1 : real_pow' = (term4 _23954)) : ((term30 real_pow' x n) = (term41 real_pow' x n)) = ((term35 _23954 n x) = (term42 _23954 n x)).
Proof. exact (MK_COMB (@lem1343519 n x real_pow' _23954 h1) (@lem1343555 n x real_pow' _23954 h1)). Qed.
Lemma lem1343557 (x : real) (real_pow' : type1623) (_23954 : type1608) (h1 : real_pow' = (term4 _23954)) : (term43 real_pow' x) = (term44 _23954 x).
Proof. exact (fun_ext (fun n : nat => @lem1343556 n x real_pow' _23954 h1)). Qed.
Lemma lem1343558 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1343559 (x : real) (real_pow' : type1623) (_23954 : type1608) (h1 : real_pow' = (term4 _23954)) : (term45 real_pow' x) = (term46 _23954 x).
Proof. exact (MK_COMB (@lem1343558) (@lem1343557 x real_pow' _23954 h1)). Qed.
Lemma lem1343560 (real_pow' : type1623) (_23954 : type1608) (h1 : real_pow' = (term4 _23954)) : (term47 real_pow') = (term48 _23954).
Proof. exact (fun_ext (fun x : real => @lem1343559 x real_pow' _23954 h1)). Qed.
Lemma lem1343561 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1343562 (real_pow' : type1623) (_23954 : type1608) (h1 : real_pow' = (term4 _23954)) : (term49 real_pow') = (term50 _23954).
Proof. exact (MK_COMB (@lem1343561) (@lem1343560 real_pow' _23954 h1)). Qed.
Lemma lem1343563 (real_pow' : type1623) (_23954 : type1608) (h1 : real_pow' = (term4 _23954)) : (term51 real_pow') = (term52 _23954).
Proof. exact (MK_COMB (@lem1343483 real_pow' _23954 h1) (@lem1343562 real_pow' _23954 h1)). Qed.
Lemma lem1343564 (_23954 : type1608) (h1 : (term53 _23954) = term54) : (term53 _23954) = term54.
Proof. exact (h1). Qed.
Lemma lem1343565 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1343566 (x : real) (_23954 : type1608) (h1 : (term53 _23954) = term54) : (term20 _23954 x) = (term55 x).
Proof. exact (MK_COMB (@lem1343564 _23954 h1) (@lem1343565 x)). Qed.
Lemma lem1343567 (x : real) : (term55 x) = term23.
Proof. exact (eq_refl (term55 x)). Qed.
Lemma lem1343568 (_23954 : type1608) (x : real) : (term22 _23954 x) = (term22 _23954 x).
Proof. exact (eq_refl (term22 _23954 x)). Qed.
Lemma lem1343569 (_23954 : type1608) (x : real) : ((term20 _23954 x) = (term55 x)) = ((term20 _23954 x) = term23).
Proof. exact (MK_COMB (@lem1343568 _23954 x) (@lem1343567 x)). Qed.
Lemma lem1343570 (x : real) (_23954 : type1608) (h1 : (term53 _23954) = term54) : (term20 _23954 x) = term23.
Proof. exact (EQ_MP (@lem1343569 _23954 x) (@lem1343566 x _23954 h1)). Qed.
Lemma lem1343571 (_23954 : type1608) (h1 : (term53 _23954) = term54) : term27 _23954.
Proof. exact (fun x : real => @lem1343570 x _23954 h1). Qed.
Lemma lem1343572 (_23954 : type1608) (h1 : term56 _23954) : term56 _23954.
Proof. exact (h1). Qed.
Lemma lem1343573 (n : nat) (_23954 : type1608) (h1 : term56 _23954) : term57 _23954 n.
Proof. exact (@lem1343572 _23954 h1 n). Qed.
Lemma lem1343574 (_23954 : type1608) (n : nat) : (term57 _23954 n) = ((term58 _23954 n) = (term59 _23954 n)).
Proof. exact (eq_refl (term57 _23954 n)). Qed.
Lemma lem1343575 (n : nat) (_23954 : type1608) (h1 : term56 _23954) : (term58 _23954 n) = (term59 _23954 n).
Proof. exact (EQ_MP (@lem1343574 _23954 n) (@lem1343573 n _23954 h1)). Qed.
Lemma lem1343576 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1343577 (n : nat) (x : real) (_23954 : type1608) (h1 : term56 _23954) : (term35 _23954 n x) = (term60 _23954 n x).
Proof. exact (MK_COMB (@lem1343575 n _23954 h1) (@lem1343576 x)). Qed.
Lemma lem1343578 (_23954 : type1608) (n : nat) (x : real) : (term60 _23954 n x) = (term42 _23954 n x).
Proof. exact (eq_refl (term60 _23954 n x)). Qed.
Lemma lem1343579 (_23954 : type1608) (n : nat) (x : real) : (term37 _23954 n x) = (term37 _23954 n x).
Proof. exact (eq_refl (term37 _23954 n x)). Qed.
Lemma lem1343580 (_23954 : type1608) (n : nat) (x : real) : ((term35 _23954 n x) = (term60 _23954 n x)) = ((term35 _23954 n x) = (term42 _23954 n x)).
Proof. exact (MK_COMB (@lem1343579 _23954 n x) (@lem1343578 _23954 n x)). Qed.
Lemma lem1343581 (n : nat) (x : real) (_23954 : type1608) (h1 : term56 _23954) : (term35 _23954 n x) = (term42 _23954 n x).
Proof. exact (EQ_MP (@lem1343580 _23954 n x) (@lem1343577 n x _23954 h1)). Qed.
Lemma lem1343582 (x : real) (_23954 : type1608) (h1 : term56 _23954) : term46 _23954 x.
Proof. exact (fun n : nat => @lem1343581 n x _23954 h1). Qed.
Lemma lem1343583 (_23954 : type1608) (h1 : term56 _23954) : term50 _23954.
Proof. exact (fun x : real => @lem1343582 x _23954 h1). Qed.
Lemma lem1343584 (_23954 : type1608) (h1 : term61 _23954) : term61 _23954.
Proof. exact (h1). Qed.
Lemma lem1343585 (_23954 : type1608) (h1 : term61 _23954) : term56 _23954.
Proof. exact (proj2 (@lem1343584 _23954 h1)). Qed.
Lemma lem1343586 (_23954 : type1608) (h1 : term61 _23954) : (term53 _23954) = term54.
Proof. exact (proj1 (@lem1343584 _23954 h1)). Qed.
Lemma lem1343587 (_23954 : type1608) (h1 : term61 _23954) : ((term53 _23954) = term54) = (term27 _23954).
Proof. exact (prop_ext (fun h2 : (term53 _23954) = term54 => @lem1343571 _23954 h2) (fun h2 : term27 _23954 => @lem1343586 _23954 h1)). Qed.
Lemma lem1343588 (_23954 : type1608) (h1 : term61 _23954) : term27 _23954.
Proof. exact (EQ_MP (@lem1343587 _23954 h1) (@lem1343586 _23954 h1)). Qed.
Lemma lem1343589 (_23954 : type1608) (h1 : term61 _23954) : (term56 _23954) = (term50 _23954).
Proof. exact (prop_ext (fun h2 : term56 _23954 => @lem1343583 _23954 h2) (fun h2 : term50 _23954 => @lem1343585 _23954 h1)). Qed.
Lemma lem1343590 (_23954 : type1608) (h1 : term61 _23954) : term50 _23954.
Proof. exact (EQ_MP (@lem1343589 _23954 h1) (@lem1343585 _23954 h1)). Qed.
Lemma lem1343591 (_23954 : type1608) (h1 : term61 _23954) : term52 _23954.
Proof. exact (conj (@lem1343588 _23954 h1) (@lem1343590 _23954 h1)). Qed.
Lemma lem1343592 {A : Type'} (e : A) : term62 A e.
Proof. exact (@lem75635 A e). Qed.
Lemma lem1343593 {A : Type'} (e : A) : (term62 A e) = (term63 A e).
Proof. exact (eq_refl (term62 A e)). Qed.
Lemma lem1343594 {A : Type'} (e : A) : term63 A e.
Proof. exact (EQ_MP (@lem1343593 A e) (@lem1343592 A e)). Qed.
Lemma lem1343595 {A : Type'} (e : A) (f : type1423 A) : term64 A e f.
Proof. exact (@lem1343594 A e f). Qed.
Lemma lem1343596 {A : Type'} (e : A) (f : type1423 A) : (term64 A e f) = (term65 A e f).
Proof. exact (eq_refl (term64 A e f)). Qed.
Lemma lem1343597 {A : Type'} (e : A) (f : type1423 A) : term65 A e f.
Proof. exact (EQ_MP (@lem1343596 A e f) (@lem1343595 A e f)). Qed.
Lemma lem1343598 (e : real -> real) (f : type1027) : term66 e f.
Proof. exact (@lem1343597 (real -> real) e f). Qed.
Lemma lem1343599 : term67.
Proof. exact (@lem1343598 term54 term68). Qed.
Lemma lem1343600 (fn : type1608) (n : nat) : (term69 fn n) = (term70 fn n).
Proof. exact (eq_refl (term69 fn n)). Qed.
Lemma lem1343601 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1343602 (fn : type1608) (n : nat) : (term71 fn n) = (term72 fn n).
Proof. exact (MK_COMB (@lem1343600 fn n) (@lem1343601 n)). Qed.
Lemma lem1343603 (fn : type1608) (n : nat) : (term72 fn n) = (term59 fn n).
Proof. exact (eq_refl (term72 fn n)). Qed.
Lemma lem1343604 (fn : type1608) (n : nat) : (term71 fn n) = (term59 fn n).
Proof. exact (TRANS (@lem1343602 fn n) (@lem1343603 fn n)). Qed.
Lemma lem1343605 (fn : type1608) (n : nat) : (term73 fn n) = (term73 fn n).
Proof. exact (eq_refl (term73 fn n)). Qed.
Lemma lem1343606 (fn : type1608) (n : nat) : ((term58 fn n) = (term71 fn n)) = ((term58 fn n) = (term59 fn n)).
Proof. exact (MK_COMB (@lem1343605 fn n) (@lem1343604 fn n)). Qed.
Lemma lem1343607 (fn : type1608) : (term74 fn) = (term75 fn).
Proof. exact (fun_ext (fun n : nat => @lem1343606 fn n)). Qed.
Lemma lem1343608 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1343609 (fn : type1608) : (term76 fn) = (term56 fn).
Proof. exact (MK_COMB (@lem1343608) (@lem1343607 fn)). Qed.
Lemma lem1343610 (fn : type1608) : (term77 fn) = (term77 fn).
Proof. exact (eq_refl (term77 fn)). Qed.
Lemma lem1343611 (fn : type1608) : (term78 fn) = (term61 fn).
Proof. exact (MK_COMB (@lem1343610 fn) (@lem1343609 fn)). Qed.
Lemma lem1343612 : term79 = term80.
Proof. exact (fun_ext (fun fn : type1608 => @lem1343611 fn)). Qed.
Lemma lem1343613 : (@ex (nat -> real -> real)) = (@ex (nat -> real -> real)).
Proof. exact (eq_refl (@ex (nat -> real -> real))). Qed.
Lemma lem1343614 : term67 = term81.
Proof. exact (MK_COMB (@lem1343613) (@lem1343612)). Qed.
Lemma lem1343615 : term81.
Proof. exact (EQ_MP (@lem1343614) (@lem1343599)). Qed.
Lemma lem1343616 (_23954 : type1608) (h1 : term61 _23954) : term61 _23954.
Proof. exact (h1). Qed.
Lemma lem1343617 (_23954 : type1608) (h1 : term61 _23954) : term56 _23954.
Proof. exact (proj2 (@lem1343616 _23954 h1)). Qed.
Lemma lem1343618 (_23954 : type1608) (h1 : term61 _23954) : (term53 _23954) = term54.
Proof. exact (proj1 (@lem1343616 _23954 h1)). Qed.
Lemma lem1343619 (_23954 : type1608) (h1 : term61 _23954) : term61 _23954.
Proof. exact (conj (@lem1343618 _23954 h1) (@lem1343617 _23954 h1)). Qed.
Lemma lem1343620 (_23954 : type1608) (h1 : term61 _23954) : term81.
Proof. exact (ex_intro term80 _23954 (@lem1343619 _23954 h1)). Qed.
Lemma lem1343621 (h1 : term81) : term81.
Proof. exact (h1). Qed.
Lemma lem1343622 (h1 : term81) : term81.
Proof. exact (ex_elim (@lem1343621 h1) (fun _23954 : type1608 => fun h0 : term80 _23954 => @lem1343620 _23954 h0)). Qed.
Lemma lem1343623 : term81 = term81.
Proof. exact (prop_ext (fun h1 : term81 => @lem1343622 h1) (fun h1 : term81 => @lem1343615)). Qed.
Lemma lem1343624 : term81.
Proof. exact (EQ_MP (@lem1343623) (@lem1343615)). Qed.
Lemma lem1343625 (_23954 : type1608) (h1 : term61 _23954) : term82.
Proof. exact (ex_intro term83 _23954 (@lem1343591 _23954 h1)). Qed.
Lemma lem1343626 (h1 : term81) : term81.
Proof. exact (h1). Qed.
Lemma lem1343627 (h1 : term81) : term82.
Proof. exact (ex_elim (@lem1343626 h1) (fun _23954 : type1608 => fun h0 : term80 _23954 => @lem1343625 _23954 h0)). Qed.
Lemma lem1343628 : term81 = term82.
Proof. exact (prop_ext (fun h1 : term81 => @lem1343627 h1) (fun h1 : term82 => @lem1343624)). Qed.
Lemma lem1343629 : term82.
Proof. exact (EQ_MP (@lem1343628) (@lem1343624)). Qed.
Lemma lem1343630 (_23954 : type1608) (h1 : term52 _23954) : term52 _23954.
Proof. exact (h1). Qed.
Lemma lem1343631 (real_pow' : type1623) (_23954 : type1608) (h1 : real_pow' = (term4 _23954)) : (term52 _23954) = (term51 real_pow').
Proof. exact (SYM (@lem1343563 real_pow' _23954 h1)). Qed.
Lemma lem1343632 (real_pow' : type1623) (_23954 : type1608) (h1 : term52 _23954) (h2 : real_pow' = (term4 _23954)) : term51 real_pow'.
Proof. exact (EQ_MP (@lem1343631 real_pow' _23954 h2) (@lem1343630 _23954 h1)). Qed.
Lemma lem1343633 (real_pow' : type1623) (_23954 : type1608) (h1 : term52 _23954) (h2 : real_pow' = (term4 _23954)) : term84.
Proof. exact (ex_intro term85 real_pow' (@lem1343632 real_pow' _23954 h1 h2)). Qed.
Lemma lem1343634 (_23954 : type1608) : (term4 _23954) = (term4 _23954).
Proof. exact (eq_refl (term4 _23954)). Qed.
Lemma lem1343635 (real_pow' : type1623) (_23954 : type1608) (h1 : term52 _23954) : term86 real_pow' _23954.
Proof. exact (fun h0 : real_pow' = (term4 _23954) => @lem1343633 real_pow' _23954 h1 h0). Qed.
Lemma lem1343636 (_23954 : type1608) (h1 : term52 _23954) : term87 _23954.
Proof. exact (@lem1343635 (term4 _23954) _23954 h1). Qed.
Lemma lem1343637 (_23954 : type1608) (h1 : term52 _23954) : term84.
Proof. exact (@lem1343636 _23954 h1 (@lem1343634 _23954)). Qed.
Lemma lem1343638 (h1 : term82) : term82.
Proof. exact (h1). Qed.
Lemma lem1343639 (h1 : term82) : term84.
Proof. exact (ex_elim (@lem1343638 h1) (fun _23954 : type1608 => fun h0 : term83 _23954 => @lem1343637 _23954 h0)). Qed.
Lemma lem1343640 : term82 = term84.
Proof. exact (prop_ext (fun h1 : term82 => @lem1343639 h1) (fun h1 : term84 => @lem1343629)). Qed.
Lemma lem1343641 : term84.
Proof. exact (EQ_MP (@lem1343640) (@lem1343629)). Qed.
Lemma lem1343642 : term88.
Proof. exact (fun _23958 : type1669 => @lem1343641). Qed.
Lemma lem1343643 {A B : Type'} (P : type1413 A B) : term89 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem1343644 {A B : Type'} (P : type1413 A B) : (term89 A B P) = ((term90 A B P) = (term91 A B P)).
Proof. exact (eq_refl (term89 A B P)). Qed.
Lemma lem1343647 {A B : Type'} (P : type1413 A B) : (term90 A B P) = (term91 A B P).
Proof. exact (EQ_MP (@lem1343644 A B P) (@lem1343643 A B P)). Qed.
Lemma lem1343648 (P : type1247) : (term92 P) = (term93 P).
Proof. exact (@lem1343647 type1669 type1623 P). Qed.
Lemma lem1343649 : term94 = term95.
Proof. exact (@lem1343648 term96). Qed.
Lemma lem1343650 (_23958 : type1669) : (term97 _23958) = term85.
Proof. exact (eq_refl (term97 _23958)). Qed.
Lemma lem1343651 (real_pow' : type1623) : real_pow' = real_pow'.
Proof. exact (eq_refl real_pow'). Qed.
Lemma lem1343652 (_23958 : type1669) (real_pow' : type1623) : (term98 _23958 real_pow') = (term99 real_pow').
Proof. exact (MK_COMB (@lem1343650 _23958) (@lem1343651 real_pow')). Qed.
Lemma lem1343653 (real_pow' : type1623) : (term99 real_pow') = (term51 real_pow').
Proof. exact (eq_refl (term99 real_pow')). Qed.
Lemma lem1343654 (_23958 : type1669) (real_pow' : type1623) : (term98 _23958 real_pow') = (term51 real_pow').
Proof. exact (TRANS (@lem1343652 _23958 real_pow') (@lem1343653 real_pow')). Qed.
Lemma lem1343655 (_23958 : type1669) : (term100 _23958) = term85.
Proof. exact (fun_ext (fun real_pow' : type1623 => @lem1343654 _23958 real_pow')). Qed.
Lemma lem1343656 : (@ex (real -> nat -> real)) = (@ex (real -> nat -> real)).
Proof. exact (eq_refl (@ex (real -> nat -> real))). Qed.
Lemma lem1343657 (_23958 : type1669) : (term101 _23958) = term84.
Proof. exact (MK_COMB (@lem1343656) (@lem1343655 _23958)). Qed.
Lemma lem1343658 : term102 = term103.
Proof. exact (fun_ext (fun _23958 : type1669 => @lem1343657 _23958)). Qed.
Lemma lem1343659 : (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) = (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))). Qed.
Lemma lem1343660 : term94 = term88.
Proof. exact (MK_COMB (@lem1343659) (@lem1343658)). Qed.
Lemma lem1343661 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1343662 : term104 = term105.
Proof. exact (MK_COMB (@lem1343661) (@lem1343660)). Qed.
Lemma lem1343663 (_23958 : type1669) : (term97 _23958) = term85.
Proof. exact (eq_refl (term97 _23958)). Qed.
Lemma lem1343664 (real_pow' : type1250) (_23958 : type1669) : (real_pow' _23958) = (real_pow' _23958).
Proof. exact (eq_refl (real_pow' _23958)). Qed.
Lemma lem1343665 (real_pow' : type1250) (_23958 : type1669) : (term106 real_pow' _23958) = (term107 real_pow' _23958).
Proof. exact (MK_COMB (@lem1343663 _23958) (@lem1343664 real_pow' _23958)). Qed.
Lemma lem1343666 (real_pow' : type1250) (_23958 : type1669) : (term107 real_pow' _23958) = (term108 real_pow' _23958).
Proof. exact (eq_refl (term107 real_pow' _23958)). Qed.
Lemma lem1343667 (real_pow' : type1250) (_23958 : type1669) : (term106 real_pow' _23958) = (term108 real_pow' _23958).
Proof. exact (TRANS (@lem1343665 real_pow' _23958) (@lem1343666 real_pow' _23958)). Qed.
Lemma lem1343668 (real_pow' : type1250) : (term109 real_pow') = (term110 real_pow').
Proof. exact (fun_ext (fun _23958 : type1669 => @lem1343667 real_pow' _23958)). Qed.
Lemma lem1343669 : (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) = (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))). Qed.
Lemma lem1343670 (real_pow' : type1250) : (term111 real_pow') = (term112 real_pow').
Proof. exact (MK_COMB (@lem1343669) (@lem1343668 real_pow')). Qed.
Lemma lem1343671 : term113 = term114.
Proof. exact (fun_ext (fun real_pow' : type1250 => @lem1343670 real_pow')). Qed.
Lemma lem1343672 : (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> real -> nat -> real)) = (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> real -> nat -> real)).
Proof. exact (eq_refl (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> real -> nat -> real))). Qed.
Lemma lem1343673 : term95 = term115.
Proof. exact (MK_COMB (@lem1343672) (@lem1343671)). Qed.
Lemma lem1343674 : (term94 = term95) = (term88 = term115).
Proof. exact (MK_COMB (@lem1343662) (@lem1343673)). Qed.
Lemma lem1343675 : term88 = term115.
Proof. exact (EQ_MP (@lem1343674) (@lem1343649)). Qed.
Lemma lem1343676 : term115.
Proof. exact (EQ_MP (@lem1343675) (@lem1343642)). Qed.
Lemma lem1343678 {A : Type'} : (@ex A) = (term116 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem1343679 : (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> real -> nat -> real)) = term117.
Proof. exact (@lem1343678 type1250). Qed.
Lemma lem1343680 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem1343681 : term115 = term118.
Proof. exact (MK_COMB (@lem1343679) (@lem1343680)). Qed.
Lemma lem1343682 : term118 = term119.
Proof. exact (eq_refl term118). Qed.
Lemma lem1343683 : term115 = term119.
Proof. exact (TRANS (@lem1343681) (@lem1343682)). Qed.
Lemma lem1343684 : term119.
Proof. exact (EQ_MP (@lem1343683) (@lem1343676)). Qed.
