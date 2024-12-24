Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SQRT_LT_0_term_abbrevs.
Require Import REAL_SGN_EQ_spec.
Require Import REAL_SGN_SQRT_spec.
Require Import real_gt_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1947448 (x : real) (h1 : ((real_sgn x) = term0) = (x = term0)) : ((real_sgn x) = term0) = (x = term0).
Proof. exact (h1). Qed.
Lemma lem1947449 (x : real) (h1 : ((real_sgn x) = term0) = (x = term0)) : (x = term0) = ((real_sgn x) = term0).
Proof. exact (SYM (@lem1947448 x h1)). Qed.
Lemma lem1947450 (x : real) (h1 : (x = term0) = ((real_sgn x) = term0)) : (x = term0) = ((real_sgn x) = term0).
Proof. exact (h1). Qed.
Lemma lem1947451 (x : real) (h1 : (x = term0) = ((real_sgn x) = term0)) : ((real_sgn x) = term0) = (x = term0).
Proof. exact (SYM (@lem1947450 x h1)). Qed.
Lemma lem1947452 (x : real) : (((real_sgn x) = term0) = (x = term0)) = ((x = term0) = ((real_sgn x) = term0)).
Proof. exact (prop_ext (fun h1 : ((real_sgn x) = term0) = (x = term0) => @lem1947449 x h1) (fun h1 : (x = term0) = ((real_sgn x) = term0) => @lem1947451 x h1)). Qed.
Lemma lem1947453 : term1 = term2.
Proof. exact (fun_ext (fun x : real => @lem1947452 x)). Qed.
Lemma lem1947454 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1947455 : term3 = term4.
Proof. exact (MK_COMB (@lem1947454) (@lem1947453)). Qed.
Lemma lem1947456 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1947457 : term5 = term6.
Proof. exact (MK_COMB (@lem1947456) (@lem1947455)). Qed.
Lemma lem1947460 (x : real) (h1 : ((real_sgn x) = term7) = (term8 x)) : ((real_sgn x) = term7) = (term8 x).
Proof. exact (h1). Qed.
Lemma lem1947461 (x : real) (h1 : ((real_sgn x) = term7) = (term8 x)) : (term8 x) = ((real_sgn x) = term7).
Proof. exact (SYM (@lem1947460 x h1)). Qed.
Lemma lem1947462 (x : real) (h1 : (term8 x) = ((real_sgn x) = term7)) : (term8 x) = ((real_sgn x) = term7).
Proof. exact (h1). Qed.
Lemma lem1947463 (x : real) (h1 : (term8 x) = ((real_sgn x) = term7)) : ((real_sgn x) = term7) = (term8 x).
Proof. exact (SYM (@lem1947462 x h1)). Qed.
Lemma lem1947464 (x : real) : (((real_sgn x) = term7) = (term8 x)) = ((term8 x) = ((real_sgn x) = term7)).
Proof. exact (prop_ext (fun h1 : ((real_sgn x) = term7) = (term8 x) => @lem1947461 x h1) (fun h1 : (term8 x) = ((real_sgn x) = term7) => @lem1947463 x h1)). Qed.
Lemma lem1947465 : term9 = term10.
Proof. exact (fun_ext (fun x : real => @lem1947464 x)). Qed.
Lemma lem1947466 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1947467 : term11 = term12.
Proof. exact (MK_COMB (@lem1947466) (@lem1947465)). Qed.
Lemma lem1947468 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1947469 : term13 = term14.
Proof. exact (MK_COMB (@lem1947468) (@lem1947467)). Qed.
Lemma lem1947471 (x : real) (h1 : ((real_sgn x) = term15) = (term16 x)) : ((real_sgn x) = term15) = (term16 x).
Proof. exact (h1). Qed.
Lemma lem1947472 (x : real) (h1 : ((real_sgn x) = term15) = (term16 x)) : (term16 x) = ((real_sgn x) = term15).
Proof. exact (SYM (@lem1947471 x h1)). Qed.
Lemma lem1947473 (x : real) (h1 : (term16 x) = ((real_sgn x) = term15)) : (term16 x) = ((real_sgn x) = term15).
Proof. exact (h1). Qed.
Lemma lem1947474 (x : real) (h1 : (term16 x) = ((real_sgn x) = term15)) : ((real_sgn x) = term15) = (term16 x).
Proof. exact (SYM (@lem1947473 x h1)). Qed.
Lemma lem1947475 (x : real) : (((real_sgn x) = term15) = (term16 x)) = ((term16 x) = ((real_sgn x) = term15)).
Proof. exact (prop_ext (fun h1 : ((real_sgn x) = term15) = (term16 x) => @lem1947472 x h1) (fun h1 : (term16 x) = ((real_sgn x) = term15) => @lem1947474 x h1)). Qed.
Lemma lem1947476 : term17 = term18.
Proof. exact (fun_ext (fun x : real => @lem1947475 x)). Qed.
Lemma lem1947477 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1947478 : term19 = term20.
Proof. exact (MK_COMB (@lem1947477) (@lem1947476)). Qed.
Lemma lem1947479 : term21 = term22.
Proof. exact (MK_COMB (@lem1947469) (@lem1947478)). Qed.
Lemma lem1947480 : term23 = term24.
Proof. exact (MK_COMB (@lem1947457) (@lem1947479)). Qed.
Lemma lem1947481 : term24.
Proof. exact (EQ_MP (@lem1947480) (@lem1740125)). Qed.
Lemma lem1947484 (y : real) (x : real) (h1 : (real_gt x y) = (real_lt y x)) : (real_gt x y) = (real_lt y x).
Proof. exact (h1). Qed.
Lemma lem1947485 (y : real) (x : real) (h1 : (real_gt x y) = (real_lt y x)) : (real_lt y x) = (real_gt x y).
Proof. exact (SYM (@lem1947484 y x h1)). Qed.
Lemma lem1947486 (x : real) (y : real) (h1 : (real_lt y x) = (real_gt x y)) : (real_lt y x) = (real_gt x y).
Proof. exact (h1). Qed.
Lemma lem1947487 (x : real) (y : real) (h1 : (real_lt y x) = (real_gt x y)) : (real_gt x y) = (real_lt y x).
Proof. exact (SYM (@lem1947486 x y h1)). Qed.
Lemma lem1947488 (x : real) (y : real) : ((real_gt x y) = (real_lt y x)) = ((real_lt y x) = (real_gt x y)).
Proof. exact (prop_ext (fun h1 : (real_gt x y) = (real_lt y x) => @lem1947485 y x h1) (fun h1 : (real_lt y x) = (real_gt x y) => @lem1947487 x y h1)). Qed.
Lemma lem1947489 (y : real) : (term25 y) = (term26 y).
Proof. exact (fun_ext (fun x : real => @lem1947488 x y)). Qed.
Lemma lem1947490 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1947491 (y : real) : (term27 y) = (term28 y).
Proof. exact (MK_COMB (@lem1947490) (@lem1947489 y)). Qed.
Lemma lem1947492 : term29 = term30.
Proof. exact (fun_ext (fun y : real => @lem1947491 y)). Qed.
Lemma lem1947493 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1947494 : term31 = term32.
Proof. exact (MK_COMB (@lem1947493) (@lem1947492)). Qed.
Lemma lem1947495 : term32.
Proof. exact (EQ_MP (@lem1947494) (@lem1342768)). Qed.
Lemma lem1947496 (x : real) : term33 x.
Proof. exact (@lem1921867 x). Qed.
Lemma lem1947497 (x : real) : (term33 x) = ((term34 x) = (real_sgn x)).
Proof. exact (eq_refl (term33 x)). Qed.
Lemma lem1947499 : term22.
Proof. exact (proj2 (@lem1947481)). Qed.
Lemma lem1947504 : term12.
Proof. exact (proj1 (@lem1947499)). Qed.
Lemma lem1947505 (x : real) : term35 x.
Proof. exact (@lem1947504 x). Qed.
Lemma lem1947506 (x : real) : (term35 x) = ((term8 x) = ((real_sgn x) = term7)).
Proof. exact (eq_refl (term35 x)). Qed.
Lemma lem1947512 (y : real) : term36 y.
Proof. exact (@lem1947495 y). Qed.
Lemma lem1947513 (y : real) : (term36 y) = (term28 y).
Proof. exact (eq_refl (term36 y)). Qed.
Lemma lem1947514 (y : real) : term28 y.
Proof. exact (EQ_MP (@lem1947513 y) (@lem1947512 y)). Qed.
Lemma lem1947515 (y : real) (x : real) : term37 y x.
Proof. exact (@lem1947514 y x). Qed.
Lemma lem1947516 (x : real) (y : real) : (term37 y x) = ((real_lt y x) = (real_gt x y)).
Proof. exact (eq_refl (term37 y x)). Qed.
Lemma lem1947525 (x : real) (y : real) : (real_lt y x) = (real_gt x y).
Proof. exact (EQ_MP (@lem1947516 x y) (@lem1947515 y x)). Qed.
Lemma lem1947526 (x : real) : (term38 x) = (term39 x).
Proof. exact (@lem1947525 (sqrt x) term0). Qed.
Lemma lem1947528 (x : real) : (term8 x) = ((real_sgn x) = term7).
Proof. exact (EQ_MP (@lem1947506 x) (@lem1947505 x)). Qed.
Lemma lem1947529 (x : real) : (term39 x) = ((term34 x) = term7).
Proof. exact (@lem1947528 (sqrt x)). Qed.
Lemma lem1947532 (x : real) : (term38 x) = ((term34 x) = term7).
Proof. exact (TRANS (@lem1947526 x) (@lem1947529 x)). Qed.
Lemma lem1947534 (x : real) : (term34 x) = (real_sgn x).
Proof. exact (EQ_MP (@lem1947497 x) (@lem1947496 x)). Qed.
Lemma lem1947535 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1947536 (x : real) : (term40 x) = (term41 x).
Proof. exact (MK_COMB (@lem1947535) (@lem1947534 x)). Qed.
Lemma lem1947537 : term7 = term7.
Proof. exact (eq_refl term7). Qed.
Lemma lem1947538 (x : real) : ((term34 x) = term7) = ((real_sgn x) = term7).
Proof. exact (MK_COMB (@lem1947536 x) (@lem1947537)). Qed.
Lemma lem1947541 (x : real) : (term38 x) = ((real_sgn x) = term7).
Proof. exact (TRANS (@lem1947532 x) (@lem1947538 x)). Qed.
Lemma lem1947542 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1947543 (x : real) : (term42 x) = (term43 x).
Proof. exact (MK_COMB (@lem1947542) (@lem1947541 x)). Qed.
Lemma lem1947545 (x : real) (y : real) : (real_lt y x) = (real_gt x y).
Proof. exact (EQ_MP (@lem1947516 x y) (@lem1947515 y x)). Qed.
Lemma lem1947546 (x : real) : (term44 x) = (term8 x).
Proof. exact (@lem1947545 x term0). Qed.
Lemma lem1947548 (x : real) : (term8 x) = ((real_sgn x) = term7).
Proof. exact (EQ_MP (@lem1947506 x) (@lem1947505 x)). Qed.
Lemma lem1947551 (x : real) : (term44 x) = ((real_sgn x) = term7).
Proof. exact (TRANS (@lem1947546 x) (@lem1947548 x)). Qed.
Lemma lem1947552 (x : real) : ((term38 x) = (term44 x)) = (((real_sgn x) = term7) = ((real_sgn x) = term7)).
Proof. exact (MK_COMB (@lem1947543 x) (@lem1947551 x)). Qed.
Lemma lem1947554 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1947555 (x : Prop) : (x = x) = True.
Proof. exact (@lem1947554 Prop x). Qed.
Lemma lem1947556 (x : real) : (((real_sgn x) = term7) = ((real_sgn x) = term7)) = True.
Proof. exact (@lem1947555 ((real_sgn x) = term7)). Qed.
Lemma lem1947557 (x : real) : ((term38 x) = (term44 x)) = True.
Proof. exact (TRANS (@lem1947552 x) (@lem1947556 x)). Qed.
Lemma lem1947558 : term45 = term46.
Proof. exact (fun_ext (fun x : real => @lem1947557 x)). Qed.
Lemma lem1947559 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1947560 : term47 = term48.
Proof. exact (MK_COMB (@lem1947559) (@lem1947558)). Qed.
Lemma lem1947562 {A : Type'} (t : Prop) : (term49 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1947563 (t : Prop) : (term50 t) = t.
Proof. exact (@lem1947562 real t). Qed.
Lemma lem1947564 : term48 = True.
Proof. exact (@lem1947563 True). Qed.
Lemma lem1947565 : term47 = True.
Proof. exact (TRANS (@lem1947560) (@lem1947564)). Qed.
Lemma lem1947566 : True = term47.
Proof. exact (SYM (@lem1947565)). Qed.
Lemma lem1947567 : term47.
Proof. exact (EQ_MP (@lem1947566) (@lem0)). Qed.
