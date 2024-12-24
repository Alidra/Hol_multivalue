Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_LCANCEL_IMP_term_abbrevs.
Require Import REAL_LT_IMP_NZ_spec.
Require Import REAL_LT_INV_spec.
Require Import REAL_LT_LMUL_spec.
Require Import thm0_spec.
Require Import thm1338912_spec.
Require Import thm1338986_spec.
Require Import thm1340174_spec.
Require Import thm1823_spec.
Lemma lem1598416 (x : real) : term0 x.
Proof. exact (@lem1523977 x). Qed.
Lemma lem1598417 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1598419 (x : real) : term2 x.
Proof. exact (@lem1340174 x). Qed.
Lemma lem1598420 (x : real) : (term2 x) = (term3 x).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem1598422 (x : real) : term4 x.
Proof. exact (@lem1584766 x). Qed.
Lemma lem1598423 (x : real) : (term4 x) = (term5 x).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem1598424 (x : real) : term5 x.
Proof. exact (EQ_MP (@lem1598423 x) (@lem1598422 x)). Qed.
Lemma lem1598425 (x : real) (y : real) : term6 x y.
Proof. exact (@lem1598424 x y). Qed.
Lemma lem1598426 (y : real) (x : real) : (term6 x y) = (term7 y x).
Proof. exact (eq_refl (term6 x y)). Qed.
Lemma lem1598427 (y : real) (x : real) : term7 y x.
Proof. exact (EQ_MP (@lem1598426 y x) (@lem1598425 x y)). Qed.
Lemma lem1598428 (y : real) (x : real) (z : real) : term8 y x z.
Proof. exact (@lem1598427 y x z). Qed.
Lemma lem1598429 (y : real) (x : real) (z : real) : (term8 y x z) = (term9 y x z).
Proof. exact (eq_refl (term8 y x z)). Qed.
Lemma lem1598431 (x : real) : term10 x.
Proof. exact (@lem1589984 x). Qed.
Lemma lem1598432 (x : real) : (term10 x) = (term11 x).
Proof. exact (eq_refl (term10 x)). Qed.
Lemma lem1598434 (y : real) (x : real) (z : real) (h1 : term12 y x z) : term12 y x z.
Proof. exact (h1). Qed.
Lemma lem1598435 (y : real) (x : real) (z : real) (h1 : term12 y x z) : term13 x.
Proof. exact (proj1 (@lem1598434 y x z h1)). Qed.
Lemma lem1598436 (y : real) (x : real) (z : real) (h1 : term12 y x z) : term12 y x z.
Proof. exact (h1). Qed.
Lemma lem1598437 (y : real) (x : real) (z : real) (h1 : term12 y x z) : term14 y x z.
Proof. exact (proj2 (@lem1598436 y x z h1)). Qed.
Lemma lem1598438 (y : real) (x : real) (z : real) (h1 : term12 y x z) : term13 x.
Proof. exact (proj1 (@lem1598436 y x z h1)). Qed.
Lemma lem1598440 (x : real) : term11 x.
Proof. exact (EQ_MP (@lem1598432 x) (@lem1598431 x)). Qed.
Lemma lem1598441 (y : real) (x : real) (z : real) (h1 : term12 y x z) : term15 x.
Proof. exact (@lem1598440 x (@lem1598438 y x z h1)). Qed.
Lemma lem1598442 (y : real) (x : real) (z : real) (h1 : term12 y x z) : term16 y x z.
Proof. exact (conj (@lem1598441 y x z h1) (@lem1598437 y x z h1)). Qed.
Lemma lem1598443 (y : real) (x : real) (z : real) (h1 : term16 y x z) : term16 y x z.
Proof. exact (h1). Qed.
Lemma lem1598445 (y : real) (x : real) (z : real) : term9 y x z.
Proof. exact (EQ_MP (@lem1598429 y x z) (@lem1598428 y x z)). Qed.
Lemma lem1598446 (y : real) (x : real) (z : real) : term17 y x z.
Proof. exact (@lem1598445 (real_mul x y) (real_inv x) (real_mul x z)). Qed.
Lemma lem1598447 (y : real) (x : real) (z : real) (h1 : term16 y x z) : term18 y x z.
Proof. exact (@lem1598446 y x z (@lem1598443 y x z h1)). Qed.
Lemma lem1598449 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1598417 x) (@lem1598416 x)). Qed.
Lemma lem1598450 (y : real) (x : real) (z : real) (h1 : term12 y x z) : term19 x.
Proof. exact (@lem1598449 x (@lem1598435 y x z h1)). Qed.
Lemma lem1598452 (x : real) : term3 x.
Proof. exact (EQ_MP (@lem1598420 x) (@lem1598419 x)). Qed.
Lemma lem1598454 (x : real) : term20 x.
Proof. exact (@lem1338986 x). Qed.
Lemma lem1598455 (x : real) : (term20 x) = ((term21 x) = x).
Proof. exact (eq_refl (term20 x)). Qed.
Lemma lem1598457 (x : real) : term22 x.
Proof. exact (@lem1338912 x). Qed.
Lemma lem1598458 (x : real) : (term22 x) = (term23 x).
Proof. exact (eq_refl (term22 x)). Qed.
Lemma lem1598459 (x : real) : term23 x.
Proof. exact (EQ_MP (@lem1598458 x) (@lem1598457 x)). Qed.
Lemma lem1598460 (x : real) (y : real) : term24 x y.
Proof. exact (@lem1598459 x y). Qed.
Lemma lem1598461 (x : real) (y : real) : (term24 x y) = (term25 x y).
Proof. exact (eq_refl (term24 x y)). Qed.
Lemma lem1598462 (x : real) (y : real) : term25 x y.
Proof. exact (EQ_MP (@lem1598461 x y) (@lem1598460 x y)). Qed.
Lemma lem1598463 (x : real) (y : real) (z : real) : term26 x y z.
Proof. exact (@lem1598462 x y z). Qed.
Lemma lem1598464 (x : real) (y : real) (z : real) : (term26 x y z) = ((term27 x y z) = (term28 x y z)).
Proof. exact (eq_refl (term26 x y z)). Qed.
Lemma lem1598469 (x : real) (y : real) (z : real) : (term27 x y z) = (term28 x y z).
Proof. exact (EQ_MP (@lem1598464 x y z) (@lem1598463 x y z)). Qed.
Lemma lem1598470 (x : real) (y : real) : (term29 x y) = (term30 x y).
Proof. exact (@lem1598469 (real_inv x) x y). Qed.
Lemma lem1598472 (y : real) (x : real) (z : real) (h1 : term12 y x z) : (term31 x) = term32.
Proof. exact (@lem1598452 x (@lem1598450 y x z h1)). Qed.
Lemma lem1598473 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1598474 (y : real) (x : real) (z : real) (h1 : term12 y x z) : (term33 x) = term34.
Proof. exact (MK_COMB (@lem1598473) (@lem1598472 y x z h1)). Qed.
Lemma lem1598475 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1598476 (y : real) (x : real) (z : real) (h1 : term12 y x z) : (term30 x y) = (term21 y).
Proof. exact (MK_COMB (@lem1598474 y x z h1) (@lem1598475 y)). Qed.
Lemma lem1598478 (x : real) : (term21 x) = x.
Proof. exact (EQ_MP (@lem1598455 x) (@lem1598454 x)). Qed.
Lemma lem1598479 (y : real) : (term21 y) = y.
Proof. exact (@lem1598478 y). Qed.
Lemma lem1598480 (y : real) (x : real) (z : real) (h1 : term12 y x z) : (term30 x y) = y.
Proof. exact (TRANS (@lem1598476 y x z h1) (@lem1598479 y)). Qed.
Lemma lem1598481 (y : real) (x : real) (z : real) (h1 : term12 y x z) : (term29 x y) = y.
Proof. exact (TRANS (@lem1598470 x y) (@lem1598480 y x z h1)). Qed.
Lemma lem1598482 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1598483 (y : real) (x : real) (z : real) (h1 : term12 y x z) : (term35 x y) = (real_lt y).
Proof. exact (MK_COMB (@lem1598482) (@lem1598481 y x z h1)). Qed.
Lemma lem1598485 (x : real) (y : real) (z : real) : (term27 x y z) = (term28 x y z).
Proof. exact (EQ_MP (@lem1598464 x y z) (@lem1598463 x y z)). Qed.
Lemma lem1598486 (x : real) (z : real) : (term29 x z) = (term30 x z).
Proof. exact (@lem1598485 (real_inv x) x z). Qed.
Lemma lem1598488 (y : real) (x : real) (z : real) (h1 : term12 y x z) : (term31 x) = term32.
Proof. exact (@lem1598452 x (@lem1598450 y x z h1)). Qed.
Lemma lem1598489 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1598490 (y : real) (x : real) (z : real) (h1 : term12 y x z) : (term33 x) = term34.
Proof. exact (MK_COMB (@lem1598489) (@lem1598488 y x z h1)). Qed.
Lemma lem1598491 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1598492 (y : real) (x : real) (z : real) (h1 : term12 y x z) : (term30 x z) = (term21 z).
Proof. exact (MK_COMB (@lem1598490 y x z h1) (@lem1598491 z)). Qed.
Lemma lem1598494 (x : real) : (term21 x) = x.
Proof. exact (EQ_MP (@lem1598455 x) (@lem1598454 x)). Qed.
Lemma lem1598495 (z : real) : (term21 z) = z.
Proof. exact (@lem1598494 z). Qed.
Lemma lem1598496 (y : real) (x : real) (z : real) (h1 : term12 y x z) : (term30 x z) = z.
Proof. exact (TRANS (@lem1598492 y x z h1) (@lem1598495 z)). Qed.
Lemma lem1598497 (y : real) (x : real) (z : real) (h1 : term12 y x z) : (term29 x z) = z.
Proof. exact (TRANS (@lem1598486 x z) (@lem1598496 y x z h1)). Qed.
Lemma lem1598498 (y : real) (x : real) (z : real) (h1 : term12 y x z) : (term18 y x z) = (real_lt y z).
Proof. exact (MK_COMB (@lem1598483 y x z h1) (@lem1598497 y x z h1)). Qed.
Lemma lem1598499 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1598500 (y : real) (x : real) (z : real) (h1 : term12 y x z) : (term36 y x z) = (term37 y z).
Proof. exact (MK_COMB (@lem1598499) (@lem1598498 y x z h1)). Qed.
Lemma lem1598501 (y : real) (z : real) : (real_lt y z) = (real_lt y z).
Proof. exact (eq_refl (real_lt y z)). Qed.
Lemma lem1598502 (y : real) (x : real) (z : real) (h1 : term12 y x z) : (term38 x y z) = (term39 y z).
Proof. exact (MK_COMB (@lem1598500 y x z h1) (@lem1598501 y z)). Qed.
Lemma lem1598504 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem1598505 (y : real) (z : real) : (term39 y z) = True.
Proof. exact (@lem1598504 (real_lt y z)). Qed.
Lemma lem1598506 (y : real) (x : real) (z : real) (h1 : term12 y x z) : (term38 x y z) = True.
Proof. exact (TRANS (@lem1598502 y x z h1) (@lem1598505 y z)). Qed.
Lemma lem1598507 (y : real) (x : real) (z : real) (h1 : term12 y x z) : True = (term38 x y z).
Proof. exact (SYM (@lem1598506 y x z h1)). Qed.
Lemma lem1598508 (y : real) (x : real) (z : real) (h1 : term12 y x z) : term38 x y z.
Proof. exact (EQ_MP (@lem1598507 y x z h1) (@lem0)). Qed.
Lemma lem1598509 (y : real) (x : real) (z : real) (h1 : term12 y x z) (h2 : term16 y x z) : real_lt y z.
Proof. exact (@lem1598508 y x z h1 (@lem1598447 y x z h2)). Qed.
Lemma lem1598510 (y : real) (x : real) (z : real) (h1 : term12 y x z) : term40 x y z.
Proof. exact (fun h0 : term16 y x z => @lem1598509 y x z h1 h0). Qed.
Lemma lem1598511 (y : real) (x : real) (z : real) (h1 : term12 y x z) : real_lt y z.
Proof. exact (@lem1598510 y x z h1 (@lem1598442 y x z h1)). Qed.
Lemma lem1598512 (x : real) (y : real) (z : real) : term41 x y z.
Proof. exact (fun h0 : term12 y x z => @lem1598511 y x z h0). Qed.
Lemma lem1598513 (y : real) (x : real) (z : real) (h1 : term12 y x z) : real_lt y z.
Proof. exact (@lem1598512 x y z (@lem1598434 y x z h1)). Qed.
Lemma lem1598514 (x : real) (y : real) (z : real) : term41 x y z.
Proof. exact (fun h0 : term12 y x z => @lem1598513 y x z h0). Qed.
Lemma lem1598519 (x : real) (y : real) : term42 x y.
Proof. exact (fun z : real => @lem1598514 x y z). Qed.
Lemma lem1598524 (x : real) : term43 x.
Proof. exact (fun y : real => @lem1598519 x y). Qed.
Lemma lem1598529 : term44.
Proof. exact (fun x : real => @lem1598524 x). Qed.
