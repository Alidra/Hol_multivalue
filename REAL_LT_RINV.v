Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_RINV_term_abbrevs.
Require Import REAL_INV_INV_spec.
Require Import REAL_LT_INV_spec.
Require Import REAL_LT_INV2_spec.
Require Import thm0_spec.
Require Import thm1820_spec.
Require Import thm1823_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Lemma lem1632552 (x : real) : term0 x.
Proof. exact (@lem1632194 x). Qed.
Lemma lem1632553 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1632554 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1632553 x) (@lem1632552 x)). Qed.
Lemma lem1632555 (x : real) (y : real) : term2 x y.
Proof. exact (@lem1632554 x (real_inv y)). Qed.
Lemma lem1632556 (y : real) (x : real) : (term2 x y) = (term3 y x).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1632557 (y : real) (x : real) : term3 y x.
Proof. exact (EQ_MP (@lem1632556 y x) (@lem1632555 x y)). Qed.
Lemma lem1632558 (x : real) : term4 x.
Proof. exact (@lem1589984 x). Qed.
Lemma lem1632559 (x : real) : (term4 x) = (term5 x).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem1632560 (x : real) : term5 x.
Proof. exact (EQ_MP (@lem1632559 x) (@lem1632558 x)). Qed.
Lemma lem1632561 (x : real) (y : real) (h1 : term6 x y) : term6 x y.
Proof. exact (h1). Qed.
Lemma lem1632562 (x : real) (y : real) (h1 : term7 x y) : term7 x y.
Proof. exact (h1). Qed.
Lemma lem1632563 (x : real) (h1 : term8 x) : term8 x.
Proof. exact (h1). Qed.
Lemma lem1632564 (x : real) : (term8 x) = ((term8 x) = True).
Proof. exact (@lem7 (term8 x)). Qed.
Lemma lem1632573 (x : real) (h1 : term8 x) : (term8 x) = True.
Proof. exact (EQ_MP (@lem1632564 x) (@lem1632563 x h1)). Qed.
Lemma lem1632574 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1632575 (x : real) (h1 : term8 x) : (term9 x) = (imp True).
Proof. exact (MK_COMB (@lem1632574) (@lem1632573 x h1)). Qed.
Lemma lem1632576 (x : real) : (term10 x) = (term10 x).
Proof. exact (eq_refl (term10 x)). Qed.
Lemma lem1632577 (x : real) (h1 : term8 x) : (term5 x) = (term11 x).
Proof. exact (MK_COMB (@lem1632575 x h1) (@lem1632576 x)). Qed.
Lemma lem1632579 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1632580 (x : real) : (term11 x) = (term10 x).
Proof. exact (@lem1632579 (term10 x)). Qed.
Lemma lem1632581 (x : real) (h1 : term8 x) : (term5 x) = (term10 x).
Proof. exact (TRANS (@lem1632577 x h1) (@lem1632580 x)). Qed.
Lemma lem1632582 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1632583 (x : real) (h1 : term8 x) : (term12 x) = (term13 x).
Proof. exact (MK_COMB (@lem1632582) (@lem1632581 x h1)). Qed.
Lemma lem1632584 (y : real) (x : real) : (term7 y x) = (term7 y x).
Proof. exact (eq_refl (term7 y x)). Qed.
Lemma lem1632585 (y : real) (x : real) (h1 : term8 x) : (term14 y x) = (term15 y x).
Proof. exact (MK_COMB (@lem1632583 x h1) (@lem1632584 y x)). Qed.
Lemma lem1632588 (y : real) (x : real) (h1 : term8 x) : (term15 y x) = (term14 y x).
Proof. exact (SYM (@lem1632585 y x h1)). Qed.
Lemma lem1632590 (x : real) : term16 x.
Proof. exact (@lem1587920 x). Qed.
Lemma lem1632591 (x : real) : (term16 x) = ((term17 x) = x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1632593 (x : real) : (term8 x) = ((term8 x) = True).
Proof. exact (@lem7 (term8 x)). Qed.
Lemma lem1632595 (x : real) (y : real) : (term7 x y) = ((term7 x y) = True).
Proof. exact (@lem7 (term7 x y)). Qed.
Lemma lem1632606 (x : real) (h1 : term8 x) : (term8 x) = True.
Proof. exact (EQ_MP (@lem1632593 x) (@lem1632563 x h1)). Qed.
Lemma lem1632607 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1632608 (x : real) (h1 : term8 x) : (term18 x) = (and True).
Proof. exact (MK_COMB (@lem1632607) (@lem1632606 x h1)). Qed.
Lemma lem1632610 (x : real) (y : real) (h1 : term7 x y) : (term7 x y) = True.
Proof. exact (EQ_MP (@lem1632595 x y) (@lem1632562 x y h1)). Qed.
Lemma lem1632611 (y : real) (x : real) (h1 : term7 x y) (h2 : term8 x) : (term6 x y) = (True /\ True).
Proof. exact (MK_COMB (@lem1632608 x h2) (@lem1632610 x y h1)). Qed.
Lemma lem1632613 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1632614 : (True /\ True) = True.
Proof. exact (@lem1632613 True). Qed.
Lemma lem1632615 (y : real) (x : real) (h1 : term7 x y) (h2 : term8 x) : (term6 x y) = True.
Proof. exact (TRANS (@lem1632611 y x h1 h2) (@lem1632614)). Qed.
Lemma lem1632616 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1632617 (y : real) (x : real) (h1 : term7 x y) (h2 : term8 x) : (term19 x y) = (imp True).
Proof. exact (MK_COMB (@lem1632616) (@lem1632615 y x h1 h2)). Qed.
Lemma lem1632619 (x : real) : (term17 x) = x.
Proof. exact (EQ_MP (@lem1632591 x) (@lem1632590 x)). Qed.
Lemma lem1632620 (y : real) : (term17 y) = y.
Proof. exact (@lem1632619 y). Qed.
Lemma lem1632621 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1632622 (y : real) : (term20 y) = (real_lt y).
Proof. exact (MK_COMB (@lem1632621) (@lem1632620 y)). Qed.
Lemma lem1632623 (x : real) : (real_inv x) = (real_inv x).
Proof. exact (eq_refl (real_inv x)). Qed.
Lemma lem1632624 (y : real) (x : real) : (term21 y x) = (term7 y x).
Proof. exact (MK_COMB (@lem1632622 y) (@lem1632623 x)). Qed.
Lemma lem1632625 (y : real) (x : real) (h1 : term7 x y) (h2 : term8 x) : (term3 y x) = (term22 y x).
Proof. exact (MK_COMB (@lem1632617 y x h1 h2) (@lem1632624 y x)). Qed.
Lemma lem1632627 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1632628 (y : real) (x : real) : (term22 y x) = (term7 y x).
Proof. exact (@lem1632627 (term7 y x)). Qed.
Lemma lem1632629 (y : real) (x : real) (h1 : term7 x y) (h2 : term8 x) : (term3 y x) = (term7 y x).
Proof. exact (TRANS (@lem1632625 y x h1 h2) (@lem1632628 y x)). Qed.
Lemma lem1632630 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1632631 (y : real) (x : real) (h1 : term7 x y) (h2 : term8 x) : (term23 y x) = (term24 y x).
Proof. exact (MK_COMB (@lem1632630) (@lem1632629 y x h1 h2)). Qed.
Lemma lem1632632 (y : real) (x : real) : (term7 y x) = (term7 y x).
Proof. exact (eq_refl (term7 y x)). Qed.
Lemma lem1632633 (y : real) (x : real) (h1 : term7 x y) (h2 : term8 x) : (term25 y x) = (term26 y x).
Proof. exact (MK_COMB (@lem1632631 y x h1 h2) (@lem1632632 y x)). Qed.
Lemma lem1632635 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem1632636 (y : real) (x : real) : (term26 y x) = True.
Proof. exact (@lem1632635 (term7 y x)). Qed.
Lemma lem1632637 (y : real) (x : real) (h1 : term7 x y) (h2 : term8 x) : (term25 y x) = True.
Proof. exact (TRANS (@lem1632633 y x h1 h2) (@lem1632636 y x)). Qed.
Lemma lem1632638 (y : real) (x : real) (h1 : term7 x y) (h2 : term8 x) : True = (term25 y x).
Proof. exact (SYM (@lem1632637 y x h1 h2)). Qed.
Lemma lem1632639 (y : real) (x : real) (h1 : term7 x y) (h2 : term8 x) : term25 y x.
Proof. exact (EQ_MP (@lem1632638 y x h1 h2) (@lem0)). Qed.
Lemma lem1632640 (y : real) (x : real) (h1 : term7 x y) (h2 : term8 x) : term7 y x.
Proof. exact (@lem1632639 y x h1 h2 (@lem1632557 y x)). Qed.
Lemma lem1632641 (y : real) (x : real) (h1 : term7 x y) (h2 : term8 x) : term15 y x.
Proof. exact (fun h0 : term10 x => @lem1632640 y x h1 h2). Qed.
Lemma lem1632642 (y : real) (x : real) (h1 : term7 x y) (h2 : term8 x) : term14 y x.
Proof. exact (EQ_MP (@lem1632588 y x h2) (@lem1632641 y x h1 h2)). Qed.
Lemma lem1632643 (y : real) (x : real) (h1 : term7 x y) (h2 : term8 x) : term7 y x.
Proof. exact (@lem1632642 y x h1 h2 (@lem1632560 x)). Qed.
Lemma lem1632644 (x : real) (y : real) (h1 : term6 x y) : term7 x y.
Proof. exact (proj2 (@lem1632561 x y h1)). Qed.
Lemma lem1632645 (x : real) (y : real) (h1 : term6 x y) : term8 x.
Proof. exact (proj1 (@lem1632561 x y h1)). Qed.
Lemma lem1632646 (y : real) (x : real) (h1 : term7 x y) (h2 : term8 x) : (term7 x y) = (term7 y x).
Proof. exact (prop_ext (fun h3 : term7 x y => @lem1632643 y x h1 h2) (fun h3 : term7 y x => @lem1632562 x y h1)). Qed.
Lemma lem1632647 (y : real) (x : real) (h1 : term7 x y) (h2 : term8 x) : term7 y x.
Proof. exact (EQ_MP (@lem1632646 y x h1 h2) (@lem1632562 x y h1)). Qed.
Lemma lem1632648 (y : real) (x : real) (h1 : term7 x y) (h2 : term8 x) : (term8 x) = (term7 y x).
Proof. exact (prop_ext (fun h3 : term8 x => @lem1632647 y x h1 h2) (fun h3 : term7 y x => @lem1632563 x h2)). Qed.
Lemma lem1632649 (y : real) (x : real) (h1 : term7 x y) (h2 : term8 x) : term7 y x.
Proof. exact (EQ_MP (@lem1632648 y x h1 h2) (@lem1632563 x h2)). Qed.
Lemma lem1632650 (y : real) (x : real) (h1 : term6 x y) (h2 : term8 x) : (term7 x y) = (term7 y x).
Proof. exact (prop_ext (fun h3 : term7 x y => @lem1632649 y x h3 h2) (fun h3 : term7 y x => @lem1632644 x y h1)). Qed.
Lemma lem1632651 (y : real) (x : real) (h1 : term6 x y) (h2 : term8 x) : term7 y x.
Proof. exact (EQ_MP (@lem1632650 y x h1 h2) (@lem1632644 x y h1)). Qed.
Lemma lem1632652 (x : real) (y : real) (h1 : term6 x y) : (term8 x) = (term7 y x).
Proof. exact (prop_ext (fun h2 : term8 x => @lem1632651 y x h1 h2) (fun h2 : term7 y x => @lem1632645 x y h1)). Qed.
Lemma lem1632653 (x : real) (y : real) (h1 : term6 x y) : term7 y x.
Proof. exact (EQ_MP (@lem1632652 x y h1) (@lem1632645 x y h1)). Qed.
Lemma lem1632654 (y : real) (x : real) : term27 y x.
Proof. exact (fun h0 : term6 x y => @lem1632653 x y h0). Qed.
Lemma lem1632659 (x : real) : term28 x.
Proof. exact (fun y : real => @lem1632654 y x). Qed.
Lemma lem1632664 : term29.
Proof. exact (fun x : real => @lem1632659 x). Qed.
