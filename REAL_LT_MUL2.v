Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_MUL2_term_abbrevs.
Require Import REAL_LET_TRANS_spec.
Require Import REAL_LE_LMUL_spec.
Require Import REAL_LT_IMP_LE_spec.
Require Import REAL_LT_RMUL_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Lemma lem1630541 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1630542 (x : real) (h1 : term0) : term1 x.
Proof. exact (@lem1630541 h1 x). Qed.
Lemma lem1630543 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1630544 (x : real) (h1 : term0) : term2 x.
Proof. exact (EQ_MP (@lem1630543 x) (@lem1630542 x h1)). Qed.
Lemma lem1630545 (x : real) (y : real) (h1 : term0) : term3 x y.
Proof. exact (@lem1630544 x h1 y). Qed.
Lemma lem1630546 (y : real) (x : real) : (term3 x y) = (term4 y x).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem1630547 (y : real) (x : real) (h1 : term0) : term4 y x.
Proof. exact (EQ_MP (@lem1630546 y x) (@lem1630545 x y h1)). Qed.
Lemma lem1630548 (y : real) (x : real) (z : real) (h1 : term0) : term5 y x z.
Proof. exact (@lem1630547 y x h1 z). Qed.
Lemma lem1630549 (y : real) (x : real) (z : real) : (term5 y x z) = (term6 y x z).
Proof. exact (eq_refl (term5 y x z)). Qed.
Lemma lem1630550 (y : real) (x : real) (z : real) (h1 : term0) : term6 y x z.
Proof. exact (EQ_MP (@lem1630549 y x z) (@lem1630548 y x z h1)). Qed.
Lemma lem1630551 (x : real) (y : real) (z : real) (h1 : term7 x y z) : term7 x y z.
Proof. exact (h1). Qed.
Lemma lem1630552 (x : real) (y : real) (z : real) (h1 : term0) (h2 : term7 x y z) : real_lt x z.
Proof. exact (@lem1630550 y x z h1 (@lem1630551 x y z h2)). Qed.
Lemma lem1630553 (x : real) (y : real) (z : real) (h1 : term7 x y z) : term8 x z.
Proof. exact (fun h0 : term0 => @lem1630552 x y z h0 h1). Qed.
Lemma lem1630554 (x : real) (z : real) (h1 : term9 x z) : term9 x z.
Proof. exact (h1). Qed.
Lemma lem1630555 (x : real) (z : real) (h1 : term9 x z) : term8 x z.
Proof. exact (ex_elim (@lem1630554 x z h1) (fun y : real => fun h0 : term10 x z y => @lem1630553 x y z h0)). Qed.
Lemma lem1630556 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1630557 (x : real) (z : real) (h1 : term0) (h2 : term9 x z) : real_lt x z.
Proof. exact (@lem1630555 x z h2 (@lem1630556 h1)). Qed.
Lemma lem1630558 (x : real) (z : real) (h1 : term0) : term11 x z.
Proof. exact (fun h0 : term9 x z => @lem1630557 x z h1 h0). Qed.
Lemma lem1630559 (x : real) (h1 : term0) : term12 x.
Proof. exact (fun z : real => @lem1630558 x z h1). Qed.
Lemma lem1630560 (h1 : term0) : term13.
Proof. exact (fun x : real => @lem1630559 x h1). Qed.
Lemma lem1630561 : term14.
Proof. exact (fun h0 : term0 => @lem1630560 h0). Qed.
Lemma lem1630562 : term13.
Proof. exact (@lem1630561 (@lem1371386)). Qed.
Lemma lem1630563 (x : real) : term15 x.
Proof. exact (@lem1630562 x). Qed.
Lemma lem1630564 (x : real) : (term15 x) = (term12 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1630565 (x : real) : term12 x.
Proof. exact (EQ_MP (@lem1630564 x) (@lem1630563 x)). Qed.
Lemma lem1630566 (x : real) (z : real) : term16 x z.
Proof. exact (@lem1630565 x z). Qed.
Lemma lem1630567 (x : real) (z : real) : (term16 x z) = (term11 x z).
Proof. exact (eq_refl (term16 x z)). Qed.
Lemma lem1630569 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem1630570 (x : real) (h1 : term17) : term18 x.
Proof. exact (@lem1630569 h1 x). Qed.
Lemma lem1630571 (x : real) : (term18 x) = (term19 x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem1630572 (x : real) (h1 : term17) : term19 x.
Proof. exact (EQ_MP (@lem1630571 x) (@lem1630570 x h1)). Qed.
Lemma lem1630573 (x : real) (y : real) (h1 : term17) : term20 x y.
Proof. exact (@lem1630572 x h1 y). Qed.
Lemma lem1630574 (x : real) (y : real) : (term20 x y) = (term21 x y).
Proof. exact (eq_refl (term20 x y)). Qed.
Lemma lem1630575 (x : real) (y : real) (h1 : term17) : term21 x y.
Proof. exact (EQ_MP (@lem1630574 x y) (@lem1630573 x y h1)). Qed.
Lemma lem1630576 (x : real) (y : real) (h1 : real_lt x y) : real_lt x y.
Proof. exact (h1). Qed.
Lemma lem1630577 (x : real) (y : real) (h1 : term17) (h2 : real_lt x y) : real_le x y.
Proof. exact (@lem1630575 x y h1 (@lem1630576 x y h2)). Qed.
Lemma lem1630578 (x : real) (y : real) (h1 : real_lt x y) : term22 x y.
Proof. exact (fun h0 : term17 => @lem1630577 x y h0 h1). Qed.
Lemma lem1630579 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem1630580 (x : real) (y : real) (h1 : term17) (h2 : real_lt x y) : real_le x y.
Proof. exact (@lem1630578 x y h2 (@lem1630579 h1)). Qed.
Lemma lem1630581 (x : real) (y : real) (h1 : term17) : term21 x y.
Proof. exact (fun h0 : real_lt x y => @lem1630580 x y h1 h0). Qed.
Lemma lem1630582 (x : real) (h1 : term17) : term19 x.
Proof. exact (fun y : real => @lem1630581 x y h1). Qed.
Lemma lem1630583 (h1 : term17) : term17.
Proof. exact (fun x : real => @lem1630582 x h1). Qed.
Lemma lem1630584 : term23.
Proof. exact (fun h0 : term17 => @lem1630583 h0). Qed.
Lemma lem1630585 : term17.
Proof. exact (@lem1630584 (@lem1369133)). Qed.
Lemma lem1630586 (x : real) : term18 x.
Proof. exact (@lem1630585 x). Qed.
Lemma lem1630587 (x : real) : (term18 x) = (term19 x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem1630588 (x : real) : term19 x.
Proof. exact (EQ_MP (@lem1630587 x) (@lem1630586 x)). Qed.
Lemma lem1630589 (x : real) (y : real) : term20 x y.
Proof. exact (@lem1630588 x y). Qed.
Lemma lem1630590 (x : real) (y : real) : (term20 x y) = (term21 x y).
Proof. exact (eq_refl (term20 x y)). Qed.
Lemma lem1630592 (h1 : term24) : term24.
Proof. exact (h1). Qed.
Lemma lem1630593 (x : real) (h1 : term24) : term25 x.
Proof. exact (@lem1630592 h1 x). Qed.
Lemma lem1630594 (x : real) : (term25 x) = (term26 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem1630595 (x : real) (h1 : term24) : term26 x.
Proof. exact (EQ_MP (@lem1630594 x) (@lem1630593 x h1)). Qed.
Lemma lem1630596 (x : real) (y : real) (h1 : term24) : term27 x y.
Proof. exact (@lem1630595 x h1 y). Qed.
Lemma lem1630597 (x : real) (y : real) : (term27 x y) = (term28 x y).
Proof. exact (eq_refl (term27 x y)). Qed.
Lemma lem1630598 (x : real) (y : real) (h1 : term24) : term28 x y.
Proof. exact (EQ_MP (@lem1630597 x y) (@lem1630596 x y h1)). Qed.
Lemma lem1630599 (x : real) (y : real) (z : real) (h1 : term24) : term29 x y z.
Proof. exact (@lem1630598 x y h1 z). Qed.
Lemma lem1630600 (x : real) (y : real) (z : real) : (term29 x y z) = (term30 x y z).
Proof. exact (eq_refl (term29 x y z)). Qed.
Lemma lem1630601 (x : real) (y : real) (z : real) (h1 : term24) : term30 x y z.
Proof. exact (EQ_MP (@lem1630600 x y z) (@lem1630599 x y z h1)). Qed.
Lemma lem1630602 (x : real) (y : real) (z : real) (h1 : term31 x y z) : term31 x y z.
Proof. exact (h1). Qed.
Lemma lem1630603 (x : real) (y : real) (z : real) (h1 : term24) (h2 : term31 x y z) : term32 x y z.
Proof. exact (@lem1630601 x y z h1 (@lem1630602 x y z h2)). Qed.
Lemma lem1630604 (x : real) (y : real) (z : real) (h1 : term31 x y z) : term33 x y z.
Proof. exact (fun h0 : term24 => @lem1630603 x y z h0 h1). Qed.
Lemma lem1630605 (h1 : term24) : term24.
Proof. exact (h1). Qed.
Lemma lem1630606 (x : real) (y : real) (z : real) (h1 : term24) (h2 : term31 x y z) : term32 x y z.
Proof. exact (@lem1630604 x y z h2 (@lem1630605 h1)). Qed.
Lemma lem1630607 (x : real) (y : real) (z : real) (h1 : term24) : term30 x y z.
Proof. exact (fun h0 : term31 x y z => @lem1630606 x y z h1 h0). Qed.
Lemma lem1630608 (x : real) (y : real) (h1 : term24) : term28 x y.
Proof. exact (fun z : real => @lem1630607 x y z h1). Qed.
Lemma lem1630609 (x : real) (h1 : term24) : term26 x.
Proof. exact (fun y : real => @lem1630608 x y h1). Qed.
Lemma lem1630610 (h1 : term24) : term24.
Proof. exact (fun x : real => @lem1630609 x h1). Qed.
Lemma lem1630611 : term34.
Proof. exact (fun h0 : term24 => @lem1630610 h0). Qed.
Lemma lem1630612 : term24.
Proof. exact (@lem1630611 (@lem1585785)). Qed.
Lemma lem1630613 (x : real) : term25 x.
Proof. exact (@lem1630612 x). Qed.
Lemma lem1630614 (x : real) : (term25 x) = (term26 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem1630615 (x : real) : term26 x.
Proof. exact (EQ_MP (@lem1630614 x) (@lem1630613 x)). Qed.
Lemma lem1630616 (x : real) (y : real) : term27 x y.
Proof. exact (@lem1630615 x y). Qed.
Lemma lem1630617 (x : real) (y : real) : (term27 x y) = (term28 x y).
Proof. exact (eq_refl (term27 x y)). Qed.
Lemma lem1630618 (x : real) (y : real) : term28 x y.
Proof. exact (EQ_MP (@lem1630617 x y) (@lem1630616 x y)). Qed.
Lemma lem1630619 (x : real) (y : real) (z : real) : term29 x y z.
Proof. exact (@lem1630618 x y z). Qed.
Lemma lem1630620 (x : real) (y : real) (z : real) : (term29 x y z) = (term30 x y z).
Proof. exact (eq_refl (term29 x y z)). Qed.
Lemma lem1630622 (h1 : term35) : term35.
Proof. exact (h1). Qed.
Lemma lem1630623 (x : real) (h1 : term35) : term36 x.
Proof. exact (@lem1630622 h1 x). Qed.
Lemma lem1630624 (x : real) : (term36 x) = (term37 x).
Proof. exact (eq_refl (term36 x)). Qed.
Lemma lem1630625 (x : real) (h1 : term35) : term37 x.
Proof. exact (EQ_MP (@lem1630624 x) (@lem1630623 x h1)). Qed.
Lemma lem1630626 (x : real) (y : real) (h1 : term35) : term38 x y.
Proof. exact (@lem1630625 x h1 y). Qed.
Lemma lem1630627 (y : real) (x : real) : (term38 x y) = (term39 y x).
Proof. exact (eq_refl (term38 x y)). Qed.
Lemma lem1630628 (y : real) (x : real) (h1 : term35) : term39 y x.
Proof. exact (EQ_MP (@lem1630627 y x) (@lem1630626 x y h1)). Qed.
Lemma lem1630629 (y : real) (x : real) (z : real) (h1 : term35) : term40 y x z.
Proof. exact (@lem1630628 y x h1 z). Qed.
Lemma lem1630630 (y : real) (x : real) (z : real) : (term40 y x z) = (term41 y x z).
Proof. exact (eq_refl (term40 y x z)). Qed.
Lemma lem1630631 (y : real) (x : real) (z : real) (h1 : term35) : term41 y x z.
Proof. exact (EQ_MP (@lem1630630 y x z) (@lem1630629 y x z h1)). Qed.
Lemma lem1630632 (x : real) (y : real) (z : real) (h1 : term42 x y z) : term42 x y z.
Proof. exact (h1). Qed.
Lemma lem1630633 (x : real) (y : real) (z : real) (h1 : term35) (h2 : term42 x y z) : term43 y x z.
Proof. exact (@lem1630631 y x z h1 (@lem1630632 x y z h2)). Qed.
Lemma lem1630634 (x : real) (y : real) (z : real) (h1 : term42 x y z) : term44 y x z.
Proof. exact (fun h0 : term35 => @lem1630633 x y z h0 h1). Qed.
Lemma lem1630635 (h1 : term35) : term35.
Proof. exact (h1). Qed.
Lemma lem1630636 (x : real) (y : real) (z : real) (h1 : term35) (h2 : term42 x y z) : term43 y x z.
Proof. exact (@lem1630634 x y z h2 (@lem1630635 h1)). Qed.
Lemma lem1630637 (y : real) (x : real) (z : real) (h1 : term35) : term41 y x z.
Proof. exact (fun h0 : term42 x y z => @lem1630636 x y z h1 h0). Qed.
Lemma lem1630638 (y : real) (x : real) (h1 : term35) : term39 y x.
Proof. exact (fun z : real => @lem1630637 y x z h1). Qed.
Lemma lem1630639 (y : real) (h1 : term35) : term45 y.
Proof. exact (fun x : real => @lem1630638 y x h1). Qed.
Lemma lem1630640 (h1 : term35) : term46.
Proof. exact (fun y : real => @lem1630639 y h1). Qed.
Lemma lem1630641 : term47.
Proof. exact (fun h0 : term35 => @lem1630640 h0). Qed.
Lemma lem1630642 : term46.
Proof. exact (@lem1630641 (@lem1583207)). Qed.
Lemma lem1630643 (y : real) : term48 y.
Proof. exact (@lem1630642 y). Qed.
Lemma lem1630644 (y : real) : (term48 y) = (term45 y).
Proof. exact (eq_refl (term48 y)). Qed.
Lemma lem1630645 (y : real) : term45 y.
Proof. exact (EQ_MP (@lem1630644 y) (@lem1630643 y)). Qed.
Lemma lem1630646 (y : real) (x : real) : term49 y x.
Proof. exact (@lem1630645 y x). Qed.
Lemma lem1630647 (y : real) (x : real) : (term49 y x) = (term39 y x).
Proof. exact (eq_refl (term49 y x)). Qed.
Lemma lem1630648 (y : real) (x : real) : term39 y x.
Proof. exact (EQ_MP (@lem1630647 y x) (@lem1630646 y x)). Qed.
Lemma lem1630649 (y : real) (x : real) (z : real) : term40 y x z.
Proof. exact (@lem1630648 y x z). Qed.
Lemma lem1630650 (y : real) (x : real) (z : real) : (term40 y x z) = (term41 y x z).
Proof. exact (eq_refl (term40 y x z)). Qed.
Lemma lem1630652 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1630653 (x : real) (h1 : term0) : term1 x.
Proof. exact (@lem1630652 h1 x). Qed.
Lemma lem1630654 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1630655 (x : real) (h1 : term0) : term2 x.
Proof. exact (EQ_MP (@lem1630654 x) (@lem1630653 x h1)). Qed.
Lemma lem1630656 (x : real) (y : real) (h1 : term0) : term3 x y.
Proof. exact (@lem1630655 x h1 y). Qed.
Lemma lem1630657 (y : real) (x : real) : (term3 x y) = (term4 y x).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem1630658 (y : real) (x : real) (h1 : term0) : term4 y x.
Proof. exact (EQ_MP (@lem1630657 y x) (@lem1630656 x y h1)). Qed.
Lemma lem1630659 (y : real) (x : real) (z : real) (h1 : term0) : term5 y x z.
Proof. exact (@lem1630658 y x h1 z). Qed.
Lemma lem1630660 (y : real) (x : real) (z : real) : (term5 y x z) = (term6 y x z).
Proof. exact (eq_refl (term5 y x z)). Qed.
Lemma lem1630661 (y : real) (x : real) (z : real) (h1 : term0) : term6 y x z.
Proof. exact (EQ_MP (@lem1630660 y x z) (@lem1630659 y x z h1)). Qed.
Lemma lem1630662 (x : real) (y : real) (z : real) (h1 : term7 x y z) : term7 x y z.
Proof. exact (h1). Qed.
Lemma lem1630663 (x : real) (y : real) (z : real) (h1 : term0) (h2 : term7 x y z) : real_lt x z.
Proof. exact (@lem1630661 y x z h1 (@lem1630662 x y z h2)). Qed.
Lemma lem1630664 (x : real) (y : real) (z : real) (h1 : term7 x y z) : term8 x z.
Proof. exact (fun h0 : term0 => @lem1630663 x y z h0 h1). Qed.
Lemma lem1630665 (x : real) (z : real) (h1 : term9 x z) : term9 x z.
Proof. exact (h1). Qed.
Lemma lem1630666 (x : real) (z : real) (h1 : term9 x z) : term8 x z.
Proof. exact (ex_elim (@lem1630665 x z h1) (fun y : real => fun h0 : term10 x z y => @lem1630664 x y z h0)). Qed.
Lemma lem1630667 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1630668 (x : real) (z : real) (h1 : term0) (h2 : term9 x z) : real_lt x z.
Proof. exact (@lem1630666 x z h2 (@lem1630667 h1)). Qed.
Lemma lem1630669 (x : real) (z : real) (h1 : term0) : term11 x z.
Proof. exact (fun h0 : term9 x z => @lem1630668 x z h1 h0). Qed.
Lemma lem1630670 (x : real) (h1 : term0) : term12 x.
Proof. exact (fun z : real => @lem1630669 x z h1). Qed.
Lemma lem1630671 (h1 : term0) : term13.
Proof. exact (fun x : real => @lem1630670 x h1). Qed.
Lemma lem1630672 : term14.
Proof. exact (fun h0 : term0 => @lem1630671 h0). Qed.
Lemma lem1630673 : term13.
Proof. exact (@lem1630672 (@lem1371386)). Qed.
Lemma lem1630674 (x : real) : term15 x.
Proof. exact (@lem1630673 x). Qed.
Lemma lem1630675 (x : real) : (term15 x) = (term12 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1630676 (x : real) : term12 x.
Proof. exact (EQ_MP (@lem1630675 x) (@lem1630674 x)). Qed.
Lemma lem1630677 (x : real) (z : real) : term16 x z.
Proof. exact (@lem1630676 x z). Qed.
Lemma lem1630678 (x : real) (z : real) : (term16 x z) = (term11 x z).
Proof. exact (eq_refl (term16 x z)). Qed.
Lemma lem1630680 (w : real) (x : real) (y : real) (z : real) (h1 : term50 w x y z) : term50 w x y z.
Proof. exact (h1). Qed.
Lemma lem1630681 (w : real) (x : real) (y : real) (z : real) (h1 : term51 w x y z) : term51 w x y z.
Proof. exact (h1). Qed.
Lemma lem1630682 (w : real) (h1 : term52 w) : term52 w.
Proof. exact (h1). Qed.
Lemma lem1630683 (y : real) (z : real) (h1 : term53 y z) : term53 y z.
Proof. exact (h1). Qed.
Lemma lem1630684 (w : real) (x : real) (h1 : real_lt w x) : real_lt w x.
Proof. exact (h1). Qed.
Lemma lem1630685 (y : real) (z : real) (h1 : real_lt y z) : real_lt y z.
Proof. exact (h1). Qed.
Lemma lem1630686 (y : real) (h1 : term52 y) : term52 y.
Proof. exact (h1). Qed.
Lemma lem1630688 (x : real) (z : real) : term11 x z.
Proof. exact (EQ_MP (@lem1630678 x z) (@lem1630677 x z)). Qed.
Lemma lem1630689 (w : real) (y : real) (x : real) (z : real) : term54 w y x z.
Proof. exact (@lem1630688 (real_mul w y) (real_mul x z)). Qed.
Lemma lem1630691 (y : real) (x : real) (z : real) : term41 y x z.
Proof. exact (EQ_MP (@lem1630650 y x z) (@lem1630649 y x z)). Qed.
Lemma lem1630692 (y : real) (w : real) (z : real) : term41 y w z.
Proof. exact (@lem1630691 y w z). Qed.
Lemma lem1630694 (x : real) (y : real) (z : real) : term30 x y z.
Proof. exact (EQ_MP (@lem1630620 x y z) (@lem1630619 x y z)). Qed.
Lemma lem1630695 (w : real) (x : real) (z : real) : term30 w x z.
Proof. exact (@lem1630694 w x z). Qed.
Lemma lem1630696 (w : real) : (term52 w) = ((term52 w) = True).
Proof. exact (@lem7 (term52 w)). Qed.
Lemma lem1630707 (w : real) (h1 : term52 w) : (term52 w) = True.
Proof. exact (EQ_MP (@lem1630696 w) (@lem1630682 w h1)). Qed.
Lemma lem1630708 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1630709 (w : real) (h1 : term52 w) : (term55 w) = (and True).
Proof. exact (MK_COMB (@lem1630708) (@lem1630707 w h1)). Qed.
Lemma lem1630710 (y : real) (z : real) : (real_le y z) = (real_le y z).
Proof. exact (eq_refl (real_le y z)). Qed.
Lemma lem1630711 (y : real) (z : real) (w : real) (h1 : term52 w) : (term42 w y z) = (term56 y z).
Proof. exact (MK_COMB (@lem1630709 w h1) (@lem1630710 y z)). Qed.
Lemma lem1630713 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1630714 (y : real) (z : real) : (term56 y z) = (real_le y z).
Proof. exact (@lem1630713 (real_le y z)). Qed.
Lemma lem1630715 (y : real) (z : real) (w : real) (h1 : term52 w) : (term42 w y z) = (real_le y z).
Proof. exact (TRANS (@lem1630711 y z w h1) (@lem1630714 y z)). Qed.
Lemma lem1630716 (y : real) (z : real) (w : real) (h1 : term52 w) : (real_le y z) = (term42 w y z).
Proof. exact (SYM (@lem1630715 y z w h1)). Qed.
Lemma lem1630719 (w : real) (x : real) : (real_lt w x) = ((real_lt w x) = True).
Proof. exact (@lem7 (real_lt w x)). Qed.
Lemma lem1630728 (w : real) (x : real) (h1 : real_lt w x) : (real_lt w x) = True.
Proof. exact (EQ_MP (@lem1630719 w x) (@lem1630684 w x h1)). Qed.
Lemma lem1630729 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1630730 (w : real) (x : real) (h1 : real_lt w x) : (term57 w x) = (and True).
Proof. exact (MK_COMB (@lem1630729) (@lem1630728 w x h1)). Qed.
Lemma lem1630731 (z : real) : (term58 z) = (term58 z).
Proof. exact (eq_refl (term58 z)). Qed.
Lemma lem1630732 (z : real) (w : real) (x : real) (h1 : real_lt w x) : (term31 w x z) = (term59 z).
Proof. exact (MK_COMB (@lem1630730 w x h1) (@lem1630731 z)). Qed.
Lemma lem1630734 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1630735 (z : real) : (term59 z) = (term58 z).
Proof. exact (@lem1630734 (term58 z)). Qed.
Lemma lem1630736 (z : real) (w : real) (x : real) (h1 : real_lt w x) : (term31 w x z) = (term58 z).
Proof. exact (TRANS (@lem1630732 z w x h1) (@lem1630735 z)). Qed.
Lemma lem1630737 (z : real) (w : real) (x : real) (h1 : real_lt w x) : (term58 z) = (term31 w x z).
Proof. exact (SYM (@lem1630736 z w x h1)). Qed.
Lemma lem1630739 (x : real) (y : real) : term21 x y.
Proof. exact (EQ_MP (@lem1630590 x y) (@lem1630589 x y)). Qed.
Lemma lem1630740 (y : real) (z : real) : term21 y z.
Proof. exact (@lem1630739 y z). Qed.
Lemma lem1630747 (y : real) (z : real) : (real_lt y z) = ((real_lt y z) = True).
Proof. exact (@lem7 (real_lt y z)). Qed.
Lemma lem1630750 (y : real) (z : real) (h1 : real_lt y z) : (real_lt y z) = True.
Proof. exact (EQ_MP (@lem1630747 y z) (@lem1630685 y z h1)). Qed.
Lemma lem1630751 (y : real) (z : real) (h1 : real_lt y z) : True = (real_lt y z).
Proof. exact (SYM (@lem1630750 y z h1)). Qed.
Lemma lem1630752 (y : real) (z : real) (h1 : real_lt y z) : real_lt y z.
Proof. exact (EQ_MP (@lem1630751 y z h1) (@lem0)). Qed.
Lemma lem1630753 (y : real) (z : real) (h1 : real_lt y z) : real_le y z.
Proof. exact (@lem1630740 y z (@lem1630752 y z h1)). Qed.
Lemma lem1630755 (x : real) (z : real) : term11 x z.
Proof. exact (EQ_MP (@lem1630567 x z) (@lem1630566 x z)). Qed.
Lemma lem1630756 (z : real) : term60 z.
Proof. exact (@lem1630755 term61 z). Qed.
Lemma lem1630761 (y : real) : (term52 y) = ((term52 y) = True).
Proof. exact (@lem7 (term52 y)). Qed.
Lemma lem1630763 (y : real) (z : real) : (real_lt y z) = ((real_lt y z) = True).
Proof. exact (@lem7 (real_lt y z)). Qed.
Lemma lem1630768 (y : real) (h1 : term52 y) : (term52 y) = True.
Proof. exact (EQ_MP (@lem1630761 y) (@lem1630686 y h1)). Qed.
Lemma lem1630769 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1630770 (y : real) (h1 : term52 y) : (term55 y) = (and True).
Proof. exact (MK_COMB (@lem1630769) (@lem1630768 y h1)). Qed.
Lemma lem1630772 (y : real) (z : real) (h1 : real_lt y z) : (real_lt y z) = True.
Proof. exact (EQ_MP (@lem1630763 y z) (@lem1630685 y z h1)). Qed.
Lemma lem1630773 (y : real) (z : real) (h1 : term52 y) (h2 : real_lt y z) : (term53 y z) = (True /\ True).
Proof. exact (MK_COMB (@lem1630770 y h1) (@lem1630772 y z h2)). Qed.
Lemma lem1630775 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1630776 : (True /\ True) = True.
Proof. exact (@lem1630775 True). Qed.
Lemma lem1630777 (y : real) (z : real) (h1 : term52 y) (h2 : real_lt y z) : (term53 y z) = True.
Proof. exact (TRANS (@lem1630773 y z h1 h2) (@lem1630776)). Qed.
Lemma lem1630778 (y : real) (z : real) (h1 : term52 y) (h2 : real_lt y z) : True = (term53 y z).
Proof. exact (SYM (@lem1630777 y z h1 h2)). Qed.
Lemma lem1630779 (y : real) (z : real) (h1 : term52 y) (h2 : real_lt y z) : term53 y z.
Proof. exact (EQ_MP (@lem1630778 y z h1 h2) (@lem0)). Qed.
Lemma lem1630780 (y : real) (z : real) (h1 : term52 y) (h2 : real_lt y z) : term62 z.
Proof. exact (ex_intro (term63 z) y (@lem1630779 y z h1 h2)). Qed.
Lemma lem1630781 (y : real) (z : real) (h1 : term52 y) (h2 : real_lt y z) : term58 z.
Proof. exact (@lem1630756 z (@lem1630780 y z h1 h2)). Qed.
Lemma lem1630782 (w : real) (x : real) (y : real) (z : real) (h1 : term52 y) (h2 : real_lt w x) (h3 : real_lt y z) : term31 w x z.
Proof. exact (EQ_MP (@lem1630737 z w x h2) (@lem1630781 y z h1 h3)). Qed.
Lemma lem1630783 (w : real) (y : real) (z : real) (h1 : term52 w) (h2 : real_lt y z) : term42 w y z.
Proof. exact (EQ_MP (@lem1630716 y z w h1) (@lem1630753 y z h2)). Qed.
Lemma lem1630784 (w : real) (x : real) (y : real) (z : real) (h1 : term52 y) (h2 : real_lt w x) (h3 : real_lt y z) : term32 w x z.
Proof. exact (@lem1630695 w x z (@lem1630782 w x y z h1 h2 h3)). Qed.
Lemma lem1630785 (w : real) (y : real) (z : real) (h1 : term52 w) (h2 : real_lt y z) : term43 y w z.
Proof. exact (@lem1630692 y w z (@lem1630783 w y z h1 h2)). Qed.
Lemma lem1630786 (w : real) (x : real) (y : real) (z : real) (h1 : term52 w) (h2 : term52 y) (h3 : real_lt w x) (h4 : real_lt y z) : term64 y w x z.
Proof. exact (conj (@lem1630785 w y z h1 h4) (@lem1630784 w x y z h2 h3 h4)). Qed.
Lemma lem1630787 (w : real) (x : real) (y : real) (z : real) (h1 : term52 w) (h2 : term52 y) (h3 : real_lt w x) (h4 : real_lt y z) : term65 w y x z.
Proof. exact (ex_intro (term66 w y x z) (real_mul w z) (@lem1630786 w x y z h1 h2 h3 h4)). Qed.
Lemma lem1630788 (w : real) (x : real) (y : real) (z : real) (h1 : term52 w) (h2 : term52 y) (h3 : real_lt w x) (h4 : real_lt y z) : term67 w y x z.
Proof. exact (@lem1630689 w y x z (@lem1630787 w x y z h1 h2 h3 h4)). Qed.
Lemma lem1630789 (w : real) (x : real) (y : real) (z : real) (h1 : term50 w x y z) : term51 w x y z.
Proof. exact (proj2 (@lem1630680 w x y z h1)). Qed.
Lemma lem1630790 (w : real) (x : real) (y : real) (z : real) (h1 : term50 w x y z) : term52 w.
Proof. exact (proj1 (@lem1630680 w x y z h1)). Qed.
Lemma lem1630791 (w : real) (x : real) (y : real) (z : real) (h1 : term51 w x y z) : term53 y z.
Proof. exact (proj2 (@lem1630681 w x y z h1)). Qed.
Lemma lem1630792 (w : real) (x : real) (y : real) (z : real) (h1 : term51 w x y z) : real_lt w x.
Proof. exact (proj1 (@lem1630681 w x y z h1)). Qed.
Lemma lem1630793 (y : real) (z : real) (h1 : term53 y z) : real_lt y z.
Proof. exact (proj2 (@lem1630683 y z h1)). Qed.
Lemma lem1630794 (y : real) (z : real) (h1 : term53 y z) : term52 y.
Proof. exact (proj1 (@lem1630683 y z h1)). Qed.
Lemma lem1630795 (w : real) (x : real) (y : real) (z : real) (h1 : term52 w) (h2 : term52 y) (h3 : real_lt w x) (h4 : real_lt y z) : (real_lt y z) = (term67 w y x z).
Proof. exact (prop_ext (fun h5 : real_lt y z => @lem1630788 w x y z h1 h2 h3 h4) (fun h5 : term67 w y x z => @lem1630685 y z h4)). Qed.
Lemma lem1630796 (w : real) (x : real) (y : real) (z : real) (h1 : term52 w) (h2 : term52 y) (h3 : real_lt w x) (h4 : real_lt y z) : term67 w y x z.
Proof. exact (EQ_MP (@lem1630795 w x y z h1 h2 h3 h4) (@lem1630685 y z h4)). Qed.
Lemma lem1630797 (w : real) (x : real) (y : real) (z : real) (h1 : term52 w) (h2 : term52 y) (h3 : real_lt w x) (h4 : real_lt y z) : (term52 y) = (term67 w y x z).
Proof. exact (prop_ext (fun h5 : term52 y => @lem1630796 w x y z h1 h2 h3 h4) (fun h5 : term67 w y x z => @lem1630686 y h2)). Qed.
Lemma lem1630798 (w : real) (x : real) (y : real) (z : real) (h1 : term52 w) (h2 : term52 y) (h3 : real_lt w x) (h4 : real_lt y z) : term67 w y x z.
Proof. exact (EQ_MP (@lem1630797 w x y z h1 h2 h3 h4) (@lem1630686 y h2)). Qed.
Lemma lem1630799 (z : real) (y : real) (w : real) (x : real) (h1 : term53 y z) (h2 : term52 w) (h3 : term52 y) (h4 : real_lt w x) : (real_lt y z) = (term67 w y x z).
Proof. exact (prop_ext (fun h5 : real_lt y z => @lem1630798 w x y z h2 h3 h4 h5) (fun h5 : term67 w y x z => @lem1630793 y z h1)). Qed.
Lemma lem1630800 (z : real) (y : real) (w : real) (x : real) (h1 : term53 y z) (h2 : term52 w) (h3 : term52 y) (h4 : real_lt w x) : term67 w y x z.
Proof. exact (EQ_MP (@lem1630799 z y w x h1 h2 h3 h4) (@lem1630793 y z h1)). Qed.
Lemma lem1630801 (y : real) (z : real) (w : real) (x : real) (h1 : term53 y z) (h2 : term52 w) (h3 : real_lt w x) : (term52 y) = (term67 w y x z).
Proof. exact (prop_ext (fun h4 : term52 y => @lem1630800 z y w x h1 h2 h4 h3) (fun h4 : term67 w y x z => @lem1630794 y z h1)). Qed.
Lemma lem1630802 (y : real) (z : real) (w : real) (x : real) (h1 : term53 y z) (h2 : term52 w) (h3 : real_lt w x) : term67 w y x z.
Proof. exact (EQ_MP (@lem1630801 y z w x h1 h2 h3) (@lem1630794 y z h1)). Qed.
Lemma lem1630803 (y : real) (z : real) (w : real) (x : real) (h1 : term53 y z) (h2 : term52 w) (h3 : real_lt w x) : (real_lt w x) = (term67 w y x z).
Proof. exact (prop_ext (fun h4 : real_lt w x => @lem1630802 y z w x h1 h2 h3) (fun h4 : term67 w y x z => @lem1630684 w x h3)). Qed.
Lemma lem1630804 (y : real) (z : real) (w : real) (x : real) (h1 : term53 y z) (h2 : term52 w) (h3 : real_lt w x) : term67 w y x z.
Proof. exact (EQ_MP (@lem1630803 y z w x h1 h2 h3) (@lem1630684 w x h3)). Qed.
Lemma lem1630805 (y : real) (z : real) (w : real) (x : real) (h1 : term51 w x y z) (h2 : term52 w) (h3 : real_lt w x) : (term53 y z) = (term67 w y x z).
Proof. exact (prop_ext (fun h4 : term53 y z => @lem1630804 y z w x h4 h2 h3) (fun h4 : term67 w y x z => @lem1630791 w x y z h1)). Qed.
Lemma lem1630806 (y : real) (z : real) (w : real) (x : real) (h1 : term51 w x y z) (h2 : term52 w) (h3 : real_lt w x) : term67 w y x z.
Proof. exact (EQ_MP (@lem1630805 y z w x h1 h2 h3) (@lem1630791 w x y z h1)). Qed.
Lemma lem1630807 (x : real) (y : real) (z : real) (w : real) (h1 : term51 w x y z) (h2 : term52 w) : (real_lt w x) = (term67 w y x z).
Proof. exact (prop_ext (fun h3 : real_lt w x => @lem1630806 y z w x h1 h2 h3) (fun h3 : term67 w y x z => @lem1630792 w x y z h1)). Qed.
Lemma lem1630808 (x : real) (y : real) (z : real) (w : real) (h1 : term51 w x y z) (h2 : term52 w) : term67 w y x z.
Proof. exact (EQ_MP (@lem1630807 x y z w h1 h2) (@lem1630792 w x y z h1)). Qed.
Lemma lem1630809 (x : real) (y : real) (z : real) (w : real) (h1 : term51 w x y z) (h2 : term52 w) : (term52 w) = (term67 w y x z).
Proof. exact (prop_ext (fun h3 : term52 w => @lem1630808 x y z w h1 h2) (fun h3 : term67 w y x z => @lem1630682 w h2)). Qed.
Lemma lem1630810 (x : real) (y : real) (z : real) (w : real) (h1 : term51 w x y z) (h2 : term52 w) : term67 w y x z.
Proof. exact (EQ_MP (@lem1630809 x y z w h1 h2) (@lem1630682 w h2)). Qed.
Lemma lem1630811 (x : real) (y : real) (z : real) (w : real) (h1 : term50 w x y z) (h2 : term52 w) : (term51 w x y z) = (term67 w y x z).
Proof. exact (prop_ext (fun h3 : term51 w x y z => @lem1630810 x y z w h3 h2) (fun h3 : term67 w y x z => @lem1630789 w x y z h1)). Qed.
Lemma lem1630812 (x : real) (y : real) (z : real) (w : real) (h1 : term50 w x y z) (h2 : term52 w) : term67 w y x z.
Proof. exact (EQ_MP (@lem1630811 x y z w h1 h2) (@lem1630789 w x y z h1)). Qed.
Lemma lem1630813 (w : real) (x : real) (y : real) (z : real) (h1 : term50 w x y z) : (term52 w) = (term67 w y x z).
Proof. exact (prop_ext (fun h2 : term52 w => @lem1630812 x y z w h1 h2) (fun h2 : term67 w y x z => @lem1630790 w x y z h1)). Qed.
Lemma lem1630814 (w : real) (x : real) (y : real) (z : real) (h1 : term50 w x y z) : term67 w y x z.
Proof. exact (EQ_MP (@lem1630813 w x y z h1) (@lem1630790 w x y z h1)). Qed.
Lemma lem1630815 (w : real) (y : real) (x : real) (z : real) : term68 w y x z.
Proof. exact (fun h0 : term50 w x y z => @lem1630814 w x y z h0). Qed.
Lemma lem1630820 (w : real) (y : real) (x : real) : term69 w y x.
Proof. exact (fun z : real => @lem1630815 w y x z). Qed.
Lemma lem1630825 (w : real) (x : real) : term70 w x.
Proof. exact (fun y : real => @lem1630820 w y x). Qed.
Lemma lem1630830 (w : real) : term71 w.
Proof. exact (fun x : real => @lem1630825 w x). Qed.
Lemma lem1630835 : term72.
Proof. exact (fun w : real => @lem1630830 w). Qed.
