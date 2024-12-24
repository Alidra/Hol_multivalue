Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_LINV_term_abbrevs.
Require Import REAL_INV_INV_spec.
Require Import REAL_LT_INV_spec.
Require Import REAL_LT_INV2_spec.
Require Import thm0_spec.
Require Import thm1820_spec.
Require Import thm1823_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Lemma lem1632441 (y : real) : term0 y.
Proof. exact (@lem1632194 (real_inv y)). Qed.
Lemma lem1632442 (y : real) : (term0 y) = (term1 y).
Proof. exact (eq_refl (term0 y)). Qed.
Lemma lem1632443 (y : real) : term1 y.
Proof. exact (EQ_MP (@lem1632442 y) (@lem1632441 y)). Qed.
Lemma lem1632444 (y : real) (x : real) : term2 y x.
Proof. exact (@lem1632443 y x). Qed.
Lemma lem1632445 (x : real) (y : real) : (term2 y x) = (term3 x y).
Proof. exact (eq_refl (term2 y x)). Qed.
Lemma lem1632446 (x : real) (y : real) : term3 x y.
Proof. exact (EQ_MP (@lem1632445 x y) (@lem1632444 y x)). Qed.
Lemma lem1632447 (y : real) : term4 y.
Proof. exact (@lem1589984 y). Qed.
Lemma lem1632448 (y : real) : (term4 y) = (term5 y).
Proof. exact (eq_refl (term4 y)). Qed.
Lemma lem1632449 (y : real) : term5 y.
Proof. exact (EQ_MP (@lem1632448 y) (@lem1632447 y)). Qed.
Lemma lem1632450 (y : real) (x : real) (h1 : term6 y x) : term6 y x.
Proof. exact (h1). Qed.
Lemma lem1632451 (y : real) (x : real) (h1 : term7 y x) : term7 y x.
Proof. exact (h1). Qed.
Lemma lem1632452 (y : real) (h1 : term8 y) : term8 y.
Proof. exact (h1). Qed.
Lemma lem1632453 (y : real) : (term8 y) = ((term8 y) = True).
Proof. exact (@lem7 (term8 y)). Qed.
Lemma lem1632462 (y : real) (h1 : term8 y) : (term8 y) = True.
Proof. exact (EQ_MP (@lem1632453 y) (@lem1632452 y h1)). Qed.
Lemma lem1632463 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1632464 (y : real) (h1 : term8 y) : (term9 y) = (imp True).
Proof. exact (MK_COMB (@lem1632463) (@lem1632462 y h1)). Qed.
Lemma lem1632465 (y : real) : (term10 y) = (term10 y).
Proof. exact (eq_refl (term10 y)). Qed.
Lemma lem1632466 (y : real) (h1 : term8 y) : (term5 y) = (term11 y).
Proof. exact (MK_COMB (@lem1632464 y h1) (@lem1632465 y)). Qed.
Lemma lem1632468 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1632469 (y : real) : (term11 y) = (term10 y).
Proof. exact (@lem1632468 (term10 y)). Qed.
Lemma lem1632470 (y : real) (h1 : term8 y) : (term5 y) = (term10 y).
Proof. exact (TRANS (@lem1632466 y h1) (@lem1632469 y)). Qed.
Lemma lem1632471 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1632472 (y : real) (h1 : term8 y) : (term12 y) = (term13 y).
Proof. exact (MK_COMB (@lem1632471) (@lem1632470 y h1)). Qed.
Lemma lem1632473 (x : real) (y : real) : (term7 x y) = (term7 x y).
Proof. exact (eq_refl (term7 x y)). Qed.
Lemma lem1632474 (x : real) (y : real) (h1 : term8 y) : (term14 x y) = (term15 x y).
Proof. exact (MK_COMB (@lem1632472 y h1) (@lem1632473 x y)). Qed.
Lemma lem1632477 (x : real) (y : real) (h1 : term8 y) : (term15 x y) = (term14 x y).
Proof. exact (SYM (@lem1632474 x y h1)). Qed.
Lemma lem1632478 (y : real) (h1 : term10 y) : term10 y.
Proof. exact (h1). Qed.
Lemma lem1632479 (x : real) : term16 x.
Proof. exact (@lem1587920 x). Qed.
Lemma lem1632480 (x : real) : (term16 x) = ((term17 x) = x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1632484 (y : real) (x : real) : (term7 y x) = ((term7 y x) = True).
Proof. exact (@lem7 (term7 y x)). Qed.
Lemma lem1632486 (y : real) : (term10 y) = ((term10 y) = True).
Proof. exact (@lem7 (term10 y)). Qed.
Lemma lem1632495 (y : real) (h1 : term10 y) : (term10 y) = True.
Proof. exact (EQ_MP (@lem1632486 y) (@lem1632478 y h1)). Qed.
Lemma lem1632496 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1632497 (y : real) (h1 : term10 y) : (term18 y) = (and True).
Proof. exact (MK_COMB (@lem1632496) (@lem1632495 y h1)). Qed.
Lemma lem1632499 (y : real) (x : real) (h1 : term7 y x) : (term7 y x) = True.
Proof. exact (EQ_MP (@lem1632484 y x) (@lem1632451 y x h1)). Qed.
Lemma lem1632500 (x : real) (y : real) (h1 : term7 y x) (h2 : term10 y) : (term19 y x) = (True /\ True).
Proof. exact (MK_COMB (@lem1632497 y h2) (@lem1632499 y x h1)). Qed.
Lemma lem1632502 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1632503 : (True /\ True) = True.
Proof. exact (@lem1632502 True). Qed.
Lemma lem1632504 (x : real) (y : real) (h1 : term7 y x) (h2 : term10 y) : (term19 y x) = True.
Proof. exact (TRANS (@lem1632500 x y h1 h2) (@lem1632503)). Qed.
Lemma lem1632505 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1632506 (x : real) (y : real) (h1 : term7 y x) (h2 : term10 y) : (term20 y x) = (imp True).
Proof. exact (MK_COMB (@lem1632505) (@lem1632504 x y h1 h2)). Qed.
Lemma lem1632508 (x : real) : (term17 x) = x.
Proof. exact (EQ_MP (@lem1632480 x) (@lem1632479 x)). Qed.
Lemma lem1632509 (y : real) : (term17 y) = y.
Proof. exact (@lem1632508 y). Qed.
Lemma lem1632510 (x : real) : (term21 x) = (term21 x).
Proof. exact (eq_refl (term21 x)). Qed.
Lemma lem1632511 (x : real) (y : real) : (term22 x y) = (term7 x y).
Proof. exact (MK_COMB (@lem1632510 x) (@lem1632509 y)). Qed.
Lemma lem1632512 (x : real) (y : real) (h1 : term7 y x) (h2 : term10 y) : (term3 x y) = (term23 x y).
Proof. exact (MK_COMB (@lem1632506 x y h1 h2) (@lem1632511 x y)). Qed.
Lemma lem1632514 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1632515 (x : real) (y : real) : (term23 x y) = (term7 x y).
Proof. exact (@lem1632514 (term7 x y)). Qed.
Lemma lem1632516 (x : real) (y : real) (h1 : term7 y x) (h2 : term10 y) : (term3 x y) = (term7 x y).
Proof. exact (TRANS (@lem1632512 x y h1 h2) (@lem1632515 x y)). Qed.
Lemma lem1632517 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1632518 (x : real) (y : real) (h1 : term7 y x) (h2 : term10 y) : (term24 x y) = (term25 x y).
Proof. exact (MK_COMB (@lem1632517) (@lem1632516 x y h1 h2)). Qed.
Lemma lem1632519 (x : real) (y : real) : (term7 x y) = (term7 x y).
Proof. exact (eq_refl (term7 x y)). Qed.
Lemma lem1632520 (x : real) (y : real) (h1 : term7 y x) (h2 : term10 y) : (term26 x y) = (term27 x y).
Proof. exact (MK_COMB (@lem1632518 x y h1 h2) (@lem1632519 x y)). Qed.
Lemma lem1632522 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem1632523 (x : real) (y : real) : (term27 x y) = True.
Proof. exact (@lem1632522 (term7 x y)). Qed.
Lemma lem1632524 (x : real) (y : real) (h1 : term7 y x) (h2 : term10 y) : (term26 x y) = True.
Proof. exact (TRANS (@lem1632520 x y h1 h2) (@lem1632523 x y)). Qed.
Lemma lem1632525 (x : real) (y : real) (h1 : term7 y x) (h2 : term10 y) : True = (term26 x y).
Proof. exact (SYM (@lem1632524 x y h1 h2)). Qed.
Lemma lem1632526 (x : real) (y : real) (h1 : term7 y x) (h2 : term10 y) : term26 x y.
Proof. exact (EQ_MP (@lem1632525 x y h1 h2) (@lem0)). Qed.
Lemma lem1632527 (x : real) (y : real) (h1 : term7 y x) (h2 : term10 y) : term7 x y.
Proof. exact (@lem1632526 x y h1 h2 (@lem1632446 x y)). Qed.
Lemma lem1632528 (y : real) (x : real) (h1 : term7 y x) : term15 x y.
Proof. exact (fun h0 : term10 y => @lem1632527 x y h1 h0). Qed.
Lemma lem1632529 (x : real) (y : real) (h1 : term7 y x) (h2 : term8 y) : term14 x y.
Proof. exact (EQ_MP (@lem1632477 x y h2) (@lem1632528 y x h1)). Qed.
Lemma lem1632530 (x : real) (y : real) (h1 : term7 y x) (h2 : term8 y) : term7 x y.
Proof. exact (@lem1632529 x y h1 h2 (@lem1632449 y)). Qed.
Lemma lem1632531 (y : real) (x : real) (h1 : term6 y x) : term7 y x.
Proof. exact (proj2 (@lem1632450 y x h1)). Qed.
Lemma lem1632532 (y : real) (x : real) (h1 : term6 y x) : term8 y.
Proof. exact (proj1 (@lem1632450 y x h1)). Qed.
Lemma lem1632533 (x : real) (y : real) (h1 : term7 y x) (h2 : term8 y) : (term7 y x) = (term7 x y).
Proof. exact (prop_ext (fun h3 : term7 y x => @lem1632530 x y h1 h2) (fun h3 : term7 x y => @lem1632451 y x h1)). Qed.
Lemma lem1632534 (x : real) (y : real) (h1 : term7 y x) (h2 : term8 y) : term7 x y.
Proof. exact (EQ_MP (@lem1632533 x y h1 h2) (@lem1632451 y x h1)). Qed.
Lemma lem1632535 (x : real) (y : real) (h1 : term7 y x) (h2 : term8 y) : (term8 y) = (term7 x y).
Proof. exact (prop_ext (fun h3 : term8 y => @lem1632534 x y h1 h2) (fun h3 : term7 x y => @lem1632452 y h2)). Qed.
Lemma lem1632536 (x : real) (y : real) (h1 : term7 y x) (h2 : term8 y) : term7 x y.
Proof. exact (EQ_MP (@lem1632535 x y h1 h2) (@lem1632452 y h2)). Qed.
Lemma lem1632537 (x : real) (y : real) (h1 : term6 y x) (h2 : term8 y) : (term7 y x) = (term7 x y).
Proof. exact (prop_ext (fun h3 : term7 y x => @lem1632536 x y h3 h2) (fun h3 : term7 x y => @lem1632531 y x h1)). Qed.
Lemma lem1632538 (x : real) (y : real) (h1 : term6 y x) (h2 : term8 y) : term7 x y.
Proof. exact (EQ_MP (@lem1632537 x y h1 h2) (@lem1632531 y x h1)). Qed.
Lemma lem1632539 (y : real) (x : real) (h1 : term6 y x) : (term8 y) = (term7 x y).
Proof. exact (prop_ext (fun h2 : term8 y => @lem1632538 x y h1 h2) (fun h2 : term7 x y => @lem1632532 y x h1)). Qed.
Lemma lem1632540 (y : real) (x : real) (h1 : term6 y x) : term7 x y.
Proof. exact (EQ_MP (@lem1632539 y x h1) (@lem1632532 y x h1)). Qed.
Lemma lem1632541 (x : real) (y : real) : term28 x y.
Proof. exact (fun h0 : term6 y x => @lem1632540 y x h0). Qed.
Lemma lem1632546 (x : real) : term29 x.
Proof. exact (fun y : real => @lem1632541 x y). Qed.
Lemma lem1632551 : term30.
Proof. exact (fun x : real => @lem1632546 x). Qed.
