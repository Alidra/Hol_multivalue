Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HAS_SIZE_FINITE_IMAGE_term_abbrevs.
Require Import DIMINDEX_UNIV_spec.
Require Import DISJ_ACI_spec.
Require Import HAS_SIZE_IMAGE_INJ_spec.
Require Import HAS_SIZE_NUMSEG_1_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm1843_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm7603491_spec.
Require Import thm7603578_spec.
Require Import thm7604549_spec.
Lemma lem7604561 (n : nat) : term0 n.
Proof. exact (@lem5400760 n). Qed.
Lemma lem7604562 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem7604563 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem7604562 n) (@lem7604561 n)). Qed.
Lemma lem7604564 (n : nat) : (term1 n) = ((term1 n) = True).
Proof. exact (@lem7 (term1 n)). Qed.
Lemma lem7604566 {A : Type'} (s : A -> Prop) : term2 A s.
Proof. exact (@lem7594688 A s). Qed.
Lemma lem7604567 {A : Type'} (s : A -> Prop) : (term2 A s) = ((@dimindex A s) = (@dimindex A (@UNIV A))).
Proof. exact (eq_refl (term2 A s)). Qed.
Lemma lem7604569 {A B : Type'} (h1 : term3 A B) : term3 A B.
Proof. exact (h1). Qed.
Lemma lem7604570 {A B : Type'} (f : A -> B) (h1 : term3 A B) : term4 A B f.
Proof. exact (@lem7604569 A B h1 f). Qed.
Lemma lem7604571 {A B : Type'} (f : A -> B) : (term4 A B f) = (term5 A B f).
Proof. exact (eq_refl (term4 A B f)). Qed.
Lemma lem7604572 {A B : Type'} (f : A -> B) (h1 : term3 A B) : term5 A B f.
Proof. exact (EQ_MP (@lem7604571 A B f) (@lem7604570 A B f h1)). Qed.
Lemma lem7604573 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term3 A B) : term6 A B f s.
Proof. exact (@lem7604572 A B f h1 s). Qed.
Lemma lem7604574 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term6 A B f s) = (term7 A B f s).
Proof. exact (eq_refl (term6 A B f s)). Qed.
Lemma lem7604575 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term3 A B) : term7 A B f s.
Proof. exact (EQ_MP (@lem7604574 A B f s) (@lem7604573 A B f s h1)). Qed.
Lemma lem7604576 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term3 A B) : term8 A B f s n.
Proof. exact (@lem7604575 A B f s h1 n). Qed.
Lemma lem7604577 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term8 A B f s n) = (term9 A B f s n).
Proof. exact (eq_refl (term8 A B f s n)). Qed.
Lemma lem7604578 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term3 A B) : term9 A B f s n.
Proof. exact (EQ_MP (@lem7604577 A B f s n) (@lem7604576 A B f s n h1)). Qed.
Lemma lem7604579 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term10 A B f s n) : term10 A B f s n.
Proof. exact (h1). Qed.
Lemma lem7604580 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term3 A B) (h2 : term10 A B f s n) : term11 A B f s n.
Proof. exact (@lem7604578 A B f s n h1 (@lem7604579 A B f s n h2)). Qed.
Lemma lem7604581 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term10 A B f s n) : term12 A B f s n.
Proof. exact (fun h0 : term3 A B => @lem7604580 A B f s n h0 h1). Qed.
Lemma lem7604582 {A B : Type'} (h1 : term3 A B) : term3 A B.
Proof. exact (h1). Qed.
Lemma lem7604583 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term3 A B) (h2 : term10 A B f s n) : term11 A B f s n.
Proof. exact (@lem7604581 A B f s n h2 (@lem7604582 A B h1)). Qed.
Lemma lem7604584 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term3 A B) : term9 A B f s n.
Proof. exact (fun h0 : term10 A B f s n => @lem7604583 A B f s n h1 h0). Qed.
Lemma lem7604585 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term3 A B) : term7 A B f s.
Proof. exact (fun n : nat => @lem7604584 A B f s n h1). Qed.
Lemma lem7604586 {A B : Type'} (f : A -> B) (h1 : term3 A B) : term5 A B f.
Proof. exact (fun s : A -> Prop => @lem7604585 A B f s h1). Qed.
Lemma lem7604587 {A B : Type'} (h1 : term3 A B) : term3 A B.
Proof. exact (fun f : A -> B => @lem7604586 A B f h1). Qed.
Lemma lem7604588 {A B : Type'} : term13 A B.
Proof. exact (fun h0 : term3 A B => @lem7604587 A B h0). Qed.
Lemma lem7604589 {A B : Type'} : term3 A B.
Proof. exact (@lem7604588 A B (@lem4004559 A B)). Qed.
Lemma lem7604590 {A B : Type'} (f : A -> B) : term4 A B f.
Proof. exact (@lem7604589 A B f). Qed.
Lemma lem7604591 {A B : Type'} (f : A -> B) : (term4 A B f) = (term5 A B f).
Proof. exact (eq_refl (term4 A B f)). Qed.
Lemma lem7604592 {A B : Type'} (f : A -> B) : term5 A B f.
Proof. exact (EQ_MP (@lem7604591 A B f) (@lem7604590 A B f)). Qed.
Lemma lem7604593 {A B : Type'} (f : A -> B) (s : A -> Prop) : term6 A B f s.
Proof. exact (@lem7604592 A B f s). Qed.
Lemma lem7604594 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term6 A B f s) = (term7 A B f s).
Proof. exact (eq_refl (term6 A B f s)). Qed.
Lemma lem7604595 {A B : Type'} (f : A -> B) (s : A -> Prop) : term7 A B f s.
Proof. exact (EQ_MP (@lem7604594 A B f s) (@lem7604593 A B f s)). Qed.
Lemma lem7604596 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : term8 A B f s n.
Proof. exact (@lem7604595 A B f s n). Qed.
Lemma lem7604597 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term8 A B f s n) = (term9 A B f s n).
Proof. exact (eq_refl (term8 A B f s n)). Qed.
Lemma lem7604600 {A : Type'} : (@UNIV (finite_image A)) = (term14 A).
Proof. exact (EQ_MP (@lem7603578 A) (@lem7604549 A)). Qed.
Lemma lem7604603 {A : Type'} : (@HAS_SIZE (finite_image A)) = (@HAS_SIZE (finite_image A)).
Proof. exact (eq_refl (@HAS_SIZE (finite_image A))). Qed.
Lemma lem7604604 {A : Type'} : (@HAS_SIZE (finite_image A) (@UNIV (finite_image A))) = (term15 A).
Proof. exact (MK_COMB (@lem7604603 A) (@lem7604600 A)). Qed.
Lemma lem7604607 {A : Type'} (s : A -> Prop) : (@dimindex A s) = (@dimindex A s).
Proof. exact (eq_refl (@dimindex A s)). Qed.
Lemma lem7604608 {A : Type'} (s : A -> Prop) : (term16 A s) = (term17 A s).
Proof. exact (MK_COMB (@lem7604604 A) (@lem7604607 A s)). Qed.
Lemma lem7604611 {A : Type'} (s : A -> Prop) : (term17 A s) = (term16 A s).
Proof. exact (SYM (@lem7604608 A s)). Qed.
Lemma lem7604613 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : term9 A B f s n.
Proof. exact (EQ_MP (@lem7604597 A B f s n) (@lem7604596 A B f s n)). Qed.
Lemma lem7604614 {A : Type'} (f : type1557 A) (s : nat -> Prop) (n : nat) : term18 A f s n.
Proof. exact (@lem7604613 nat (finite_image A) f s n). Qed.
Lemma lem7604615 {A : Type'} (s : A -> Prop) : term19 A s.
Proof. exact (@lem7604614 A (@finite_index A) (term20 A) (@dimindex A s)). Qed.
Lemma lem7604631 {A : Type'} (s : A -> Prop) : (@dimindex A s) = (@dimindex A (@UNIV A)).
Proof. exact (EQ_MP (@lem7604567 A s) (@lem7604566 A s)). Qed.
Lemma lem7604632 {A : Type'} (s : A -> Prop) : (@dimindex A s) = (@dimindex A (@UNIV A)).
Proof. exact (@lem7604631 A s). Qed.
Lemma lem7604633 {A : Type'} : (@dimindex A (@UNIV A)) = (@dimindex A (@UNIV A)).
Proof. exact (@lem7604632 A (@UNIV A)). Qed.
Lemma lem7604634 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem7604635 {A : Type'} : (term20 A) = (term20 A).
Proof. exact (MK_COMB (@lem7604634) (@lem7604633 A)). Qed.
Lemma lem7604636 (x : nat) : (@IN nat x) = (@IN nat x).
Proof. exact (eq_refl (@IN nat x)). Qed.
Lemma lem7604637 {A : Type'} (x : nat) : (term22 A x) = (term22 A x).
Proof. exact (MK_COMB (@lem7604636 x) (@lem7604635 A)). Qed.
Lemma lem7604638 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7604639 {A : Type'} (x : nat) : (term23 A x) = (term23 A x).
Proof. exact (MK_COMB (@lem7604638) (@lem7604637 A x)). Qed.
Lemma lem7604643 {A : Type'} (s : A -> Prop) : (@dimindex A s) = (@dimindex A (@UNIV A)).
Proof. exact (EQ_MP (@lem7604567 A s) (@lem7604566 A s)). Qed.
Lemma lem7604644 {A : Type'} (s : A -> Prop) : (@dimindex A s) = (@dimindex A (@UNIV A)).
Proof. exact (@lem7604643 A s). Qed.
Lemma lem7604645 {A : Type'} : (@dimindex A (@UNIV A)) = (@dimindex A (@UNIV A)).
Proof. exact (@lem7604644 A (@UNIV A)). Qed.
Lemma lem7604646 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem7604647 {A : Type'} : (term20 A) = (term20 A).
Proof. exact (MK_COMB (@lem7604646) (@lem7604645 A)). Qed.
Lemma lem7604648 (y : nat) : (@IN nat y) = (@IN nat y).
Proof. exact (eq_refl (@IN nat y)). Qed.
Lemma lem7604649 {A : Type'} (y : nat) : (term22 A y) = (term22 A y).
Proof. exact (MK_COMB (@lem7604648 y) (@lem7604647 A)). Qed.
Lemma lem7604650 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7604651 {A : Type'} (y : nat) : (term23 A y) = (term23 A y).
Proof. exact (MK_COMB (@lem7604650) (@lem7604649 A y)). Qed.
Lemma lem7604654 {A : Type'} (x : nat) (y : nat) : ((@finite_index A x) = (@finite_index A y)) = ((@finite_index A x) = (@finite_index A y)).
Proof. exact (eq_refl ((@finite_index A x) = (@finite_index A y))). Qed.
Lemma lem7604655 {A : Type'} (x : nat) (y : nat) : (term24 A x y) = (term24 A x y).
Proof. exact (MK_COMB (@lem7604651 A y) (@lem7604654 A x y)). Qed.
Lemma lem7604656 {A : Type'} (x : nat) (y : nat) : (term25 A x y) = (term25 A x y).
Proof. exact (MK_COMB (@lem7604639 A x) (@lem7604655 A x y)). Qed.
Lemma lem7604657 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7604658 {A : Type'} (x : nat) (y : nat) : (term26 A x y) = (term26 A x y).
Proof. exact (MK_COMB (@lem7604657) (@lem7604656 A x y)). Qed.
Lemma lem7604661 (x : nat) (y : nat) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem7604662 {A : Type'} (x : nat) (y : nat) : (term27 A x y) = (term27 A x y).
Proof. exact (MK_COMB (@lem7604658 A x y) (@lem7604661 x y)). Qed.
Lemma lem7604663 {A : Type'} (x : nat) : (term28 A x) = (term28 A x).
Proof. exact (fun_ext (fun y : nat => @lem7604662 A x y)). Qed.
Lemma lem7604664 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7604665 {A : Type'} (x : nat) : (term29 A x) = (term29 A x).
Proof. exact (MK_COMB (@lem7604664) (@lem7604663 A x)). Qed.
Lemma lem7604666 {A : Type'} : (term30 A) = (term30 A).
Proof. exact (fun_ext (fun x : nat => @lem7604665 A x)). Qed.
Lemma lem7604667 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7604668 {A : Type'} : (term31 A) = (term31 A).
Proof. exact (MK_COMB (@lem7604667) (@lem7604666 A)). Qed.
Lemma lem7604669 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7604670 {A : Type'} : (term32 A) = (term32 A).
Proof. exact (MK_COMB (@lem7604669) (@lem7604668 A)). Qed.
Lemma lem7604672 {A : Type'} (s : A -> Prop) : (@dimindex A s) = (@dimindex A (@UNIV A)).
Proof. exact (EQ_MP (@lem7604567 A s) (@lem7604566 A s)). Qed.
Lemma lem7604673 {A : Type'} (s : A -> Prop) : (@dimindex A s) = (@dimindex A (@UNIV A)).
Proof. exact (@lem7604672 A s). Qed.
Lemma lem7604674 {A : Type'} : (@dimindex A (@UNIV A)) = (@dimindex A (@UNIV A)).
Proof. exact (@lem7604673 A (@UNIV A)). Qed.
Lemma lem7604675 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem7604676 {A : Type'} : (term20 A) = (term20 A).
Proof. exact (MK_COMB (@lem7604675) (@lem7604674 A)). Qed.
Lemma lem7604677 : (@HAS_SIZE nat) = (@HAS_SIZE nat).
Proof. exact (eq_refl (@HAS_SIZE nat)). Qed.
Lemma lem7604678 {A : Type'} : (term33 A) = (term33 A).
Proof. exact (MK_COMB (@lem7604677) (@lem7604676 A)). Qed.
Lemma lem7604680 {A : Type'} (s : A -> Prop) : (@dimindex A s) = (@dimindex A (@UNIV A)).
Proof. exact (EQ_MP (@lem7604567 A s) (@lem7604566 A s)). Qed.
Lemma lem7604681 {A : Type'} (s : A -> Prop) : (@dimindex A s) = (@dimindex A (@UNIV A)).
Proof. exact (@lem7604680 A s). Qed.
Lemma lem7604682 {A : Type'} (s : A -> Prop) : (term34 A s) = (term35 A).
Proof. exact (MK_COMB (@lem7604678 A) (@lem7604681 A s)). Qed.
Lemma lem7604683 {A : Type'} (s : A -> Prop) : (term36 A s) = (term37 A).
Proof. exact (MK_COMB (@lem7604670 A) (@lem7604682 A s)). Qed.
Lemma lem7604684 {A : Type'} (s : A -> Prop) : (term37 A) = (term36 A s).
Proof. exact (SYM (@lem7604683 A s)). Qed.
Lemma lem7604706 (n : nat) : (term1 n) = True.
Proof. exact (EQ_MP (@lem7604564 n) (@lem7604563 n)). Qed.
Lemma lem7604707 {A : Type'} : (term35 A) = True.
Proof. exact (@lem7604706 (@dimindex A (@UNIV A))). Qed.
Lemma lem7604708 {A : Type'} : (term32 A) = (term32 A).
Proof. exact (eq_refl (term32 A)). Qed.
Lemma lem7604709 {A : Type'} : (term37 A) = (term38 A).
Proof. exact (MK_COMB (@lem7604708 A) (@lem7604707 A)). Qed.
Lemma lem7604711 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem7604712 {A : Type'} : (term38 A) = (term31 A).
Proof. exact (@lem7604711 (term31 A)). Qed.
Lemma lem7604731 {A : Type'} : (term37 A) = (term31 A).
Proof. exact (TRANS (@lem7604709 A) (@lem7604712 A)). Qed.
Lemma lem7604732 {A : Type'} : (term31 A) = (term37 A).
Proof. exact (SYM (@lem7604731 A)). Qed.
Lemma lem7604734 (p : Prop) : p = (term39 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7604735 {A : Type'} : (term31 A) = (term40 A).
Proof. exact (@lem7604734 (term31 A)). Qed.
Lemma lem7604736 {A : Type'} : (term40 A) = (term31 A).
Proof. exact (SYM (@lem7604735 A)). Qed.
Lemma lem7604737 {A : Type'} (h1 : term41 A) : term41 A.
Proof. exact (h1). Qed.
Lemma lem7604738 {A : Type'} : term42 A.
Proof. exact (@lem7603491 A). Qed.
Lemma lem7604744 {A : Type'} (h1 : term43 A) : term43 A.
Proof. exact (h1). Qed.
Lemma lem7604745 {A : Type'} : term44 A.
Proof. exact (fun h0 : term43 A => @lem7604744 A h0). Qed.
Lemma lem7604746 {A : Type'} (h1 : term44 A) : term44 A.
Proof. exact (h1). Qed.
Lemma lem7604747 {A : Type'} (h1 : term43 A) : term43 A.
Proof. exact (h1). Qed.
Lemma lem7604748 {A : Type'} (h1 : term43 A) (h2 : term44 A) : term43 A.
Proof. exact (@lem7604746 A h2 (@lem7604747 A h1)). Qed.
Lemma lem7604749 {A : Type'} (h1 : term43 A) : term45 A.
Proof. exact (fun h0 : term44 A => @lem7604748 A h1 h0). Qed.
Lemma lem7604750 {A : Type'} (h1 : term44 A) : term44 A.
Proof. exact (h1). Qed.
Lemma lem7604751 {A : Type'} (h1 : term43 A) (h2 : term44 A) : term43 A.
Proof. exact (@lem7604749 A h1 (@lem7604750 A h2)). Qed.
Lemma lem7604752 {A : Type'} (h1 : term44 A) : term44 A.
Proof. exact (fun h0 : term43 A => @lem7604751 A h0 h1). Qed.
Lemma lem7604753 {A : Type'} : term46 A.
Proof. exact (fun h0 : term44 A => @lem7604752 A h0). Qed.
Lemma lem7604756 {A : Type'} : term44 A.
Proof. exact (@lem7604753 A (@lem7604745 A)). Qed.
Lemma lem7604757 {A : Type'} : term44 A.
Proof. exact (@lem7604756 A). Qed.
Lemma lem7604775 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7604776 {A : Type'} : (term47 A) = (term48 A).
Proof. exact (@lem7604775 (term42 A)). Qed.
Lemma lem7604787 {A : Type'} : (term49 A) = (term49 A).
Proof. exact (eq_refl (term49 A)). Qed.
Lemma lem7604794 {A : Type'} : (term43 A) = (term50 A).
Proof. exact (MK_COMB (@lem7604787 A) (@lem7604776 A)). Qed.
Lemma lem7604799 {A : Type'} (r : nat) : ((term22 A r) = ((term51 A r) = r)) = ((term22 A r) = ((term51 A r) = r)).
Proof. exact (eq_refl ((term22 A r) = ((term51 A r) = r))). Qed.
Lemma lem7604800 {A : Type'} : (term52 A) = (term52 A).
Proof. exact (fun_ext (fun r : nat => @lem7604799 A r)). Qed.
Lemma lem7604801 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7604802 {A : Type'} : (term53 A) = (term53 A).
Proof. exact (MK_COMB (@lem7604801) (@lem7604800 A)). Qed.
Lemma lem7604803 {A : Type'} (a : finite_image A) : ((term54 A a) = a) = ((term54 A a) = a).
Proof. exact (eq_refl ((term54 A a) = a)). Qed.
Lemma lem7604804 {A : Type'} : (term55 A) = (term55 A).
Proof. exact (fun_ext (fun a : finite_image A => @lem7604803 A a)). Qed.
Lemma lem7604805 {A : Type'} : (@all (finite_image A)) = (@all (finite_image A)).
Proof. exact (eq_refl (@all (finite_image A))). Qed.
Lemma lem7604806 {A : Type'} : (term56 A) = (term56 A).
Proof. exact (MK_COMB (@lem7604805 A) (@lem7604804 A)). Qed.
Lemma lem7604807 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7604808 {A : Type'} : (term57 A) = (term57 A).
Proof. exact (MK_COMB (@lem7604807) (@lem7604806 A)). Qed.
Lemma lem7604809 {A : Type'} : (term42 A) = (term42 A).
Proof. exact (MK_COMB (@lem7604808 A) (@lem7604802 A)). Qed.
Lemma lem7604810 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7604811 {A : Type'} : (term48 A) = (term48 A).
Proof. exact (MK_COMB (@lem7604810) (@lem7604809 A)). Qed.
Lemma lem7604824 {A : Type'} (x : nat) (y : nat) : (term27 A x y) = (term27 A x y).
Proof. exact (eq_refl (term27 A x y)). Qed.
Lemma lem7604825 {A : Type'} (x : nat) : (term28 A x) = (term28 A x).
Proof. exact (fun_ext (fun y : nat => @lem7604824 A x y)). Qed.
Lemma lem7604826 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7604827 {A : Type'} (x : nat) : (term29 A x) = (term29 A x).
Proof. exact (MK_COMB (@lem7604826) (@lem7604825 A x)). Qed.
Lemma lem7604828 {A : Type'} : (term30 A) = (term30 A).
Proof. exact (fun_ext (fun x : nat => @lem7604827 A x)). Qed.
Lemma lem7604829 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7604830 {A : Type'} : (term31 A) = (term31 A).
Proof. exact (MK_COMB (@lem7604829) (@lem7604828 A)). Qed.
Lemma lem7604831 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7604832 {A : Type'} : (term41 A) = (term41 A).
Proof. exact (MK_COMB (@lem7604831) (@lem7604830 A)). Qed.
Lemma lem7604833 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7604834 {A : Type'} : (term49 A) = (term49 A).
Proof. exact (MK_COMB (@lem7604833) (@lem7604832 A)). Qed.
Lemma lem7604835 {A : Type'} : (term50 A) = (term50 A).
Proof. exact (MK_COMB (@lem7604834 A) (@lem7604811 A)). Qed.
Lemma lem7604872 {A : Type'} : (term43 A) = (term50 A).
Proof. exact (TRANS (@lem7604794 A) (@lem7604835 A)). Qed.
Lemma lem7604873 {A : Type'} : (term50 A) = (term43 A).
Proof. exact (SYM (@lem7604872 A)). Qed.
Lemma lem7604874 {A : Type'} (h1 : term41 A) : term41 A.
Proof. exact (h1). Qed.
Lemma lem7604875 {A : Type'} (h1 : term42 A) : term42 A.
Proof. exact (h1). Qed.
Lemma lem7604890 {A : Type'} (x : nat) (y : nat) : (term58 A x y) = (term59 A x y).
Proof. exact (@lem17362 (term25 A x y) (x = y)). Qed.
Lemma lem7604891 (P : nat -> Prop) : (term60 P) = (term61 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem7604892 {A : Type'} (x : nat) : (term62 A x) = (term63 A x).
Proof. exact (@lem7604891 (term28 A x)). Qed.
Lemma lem7604893 {A : Type'} (x : nat) (y : nat) : (term64 A x y) = (term27 A x y).
Proof. exact (eq_refl (term64 A x y)). Qed.
Lemma lem7604894 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7604895 {A : Type'} (x : nat) (y : nat) : (term65 A x y) = (term58 A x y).
Proof. exact (MK_COMB (@lem7604894) (@lem7604893 A x y)). Qed.
Lemma lem7604896 {A : Type'} (x : nat) (y : nat) : (term65 A x y) = (term59 A x y).
Proof. exact (TRANS (@lem7604895 A x y) (@lem7604890 A x y)). Qed.
Lemma lem7604897 {A : Type'} (x : nat) : (term66 A x) = (term67 A x).
Proof. exact (fun_ext (fun y : nat => @lem7604896 A x y)). Qed.
Lemma lem7604898 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7604899 {A : Type'} (x : nat) : (term63 A x) = (term68 A x).
Proof. exact (MK_COMB (@lem7604898) (@lem7604897 A x)). Qed.
Lemma lem7604900 {A : Type'} (x : nat) : (term62 A x) = (term68 A x).
Proof. exact (TRANS (@lem7604892 A x) (@lem7604899 A x)). Qed.
Lemma lem7604901 (P : nat -> Prop) : (term60 P) = (term61 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem7604902 {A : Type'} : (term41 A) = (term69 A).
Proof. exact (@lem7604901 (term30 A)). Qed.
Lemma lem7604903 {A : Type'} (x : nat) : (term70 A x) = (term29 A x).
Proof. exact (eq_refl (term70 A x)). Qed.
Lemma lem7604904 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7604905 {A : Type'} (x : nat) : (term71 A x) = (term62 A x).
Proof. exact (MK_COMB (@lem7604904) (@lem7604903 A x)). Qed.
Lemma lem7604906 {A : Type'} (x : nat) : (term71 A x) = (term68 A x).
Proof. exact (TRANS (@lem7604905 A x) (@lem7604900 A x)). Qed.
Lemma lem7604907 {A : Type'} : (term72 A) = (term73 A).
Proof. exact (fun_ext (fun x : nat => @lem7604906 A x)). Qed.
Lemma lem7604908 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7604909 {A : Type'} : (term69 A) = (term74 A).
Proof. exact (MK_COMB (@lem7604908) (@lem7604907 A)). Qed.
Lemma lem7604966 {A : Type'} : (term41 A) = (term74 A).
Proof. exact (TRANS (@lem7604902 A) (@lem7604909 A)). Qed.
Lemma lem7604967 {A : Type'} (h1 : term41 A) : term74 A.
Proof. exact (EQ_MP (@lem7604966 A) (@lem7604874 A h1)). Qed.
Lemma lem7604968 {A : Type'} (a : finite_image A) : ((term54 A a) = a) = ((term54 A a) = a).
Proof. exact (eq_refl ((term54 A a) = a)). Qed.
Lemma lem7604969 {A : Type'} : (term55 A) = (term55 A).
Proof. exact (fun_ext (fun a : finite_image A => @lem7604968 A a)). Qed.
Lemma lem7604970 {A : Type'} : (@all (finite_image A)) = (@all (finite_image A)).
Proof. exact (eq_refl (@all (finite_image A))). Qed.
Lemma lem7604971 {A : Type'} : (term56 A) = (term56 A).
Proof. exact (MK_COMB (@lem7604970 A) (@lem7604969 A)). Qed.
Lemma lem7604986 {A : Type'} (r : nat) : ((term22 A r) = ((term51 A r) = r)) = (term75 A r).
Proof. exact (@lem17784 (term22 A r) ((term51 A r) = r)). Qed.
Lemma lem7604987 {A : Type'} : (term52 A) = (term76 A).
Proof. exact (fun_ext (fun r : nat => @lem7604986 A r)). Qed.
Lemma lem7604988 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7604989 {A : Type'} : (term53 A) = (term77 A).
Proof. exact (MK_COMB (@lem7604988) (@lem7604987 A)). Qed.
Lemma lem7604990 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7604991 {A : Type'} : (term57 A) = (term57 A).
Proof. exact (MK_COMB (@lem7604990) (@lem7604971 A)). Qed.
Lemma lem7604992 {A : Type'} : (term42 A) = (term78 A).
Proof. exact (MK_COMB (@lem7604991 A) (@lem7604989 A)). Qed.
Lemma lem7604998 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term79 A P Q) = (term80 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7604999 (P : nat -> Prop) (Q : nat -> Prop) : (term81 P Q) = (term82 P Q).
Proof. exact (@lem7604998 nat P Q). Qed.
Lemma lem7605000 {A : Type'} : (term83 A) = (term84 A).
Proof. exact (@lem7604999 (term85 A) (term86 A)). Qed.
Lemma lem7605001 {A : Type'} (r : nat) : (term87 A r) = (term88 A r).
Proof. exact (eq_refl (term87 A r)). Qed.
Lemma lem7605002 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7605003 {A : Type'} (r : nat) : (term89 A r) = (term90 A r).
Proof. exact (MK_COMB (@lem7605002) (@lem7605001 A r)). Qed.
Lemma lem7605004 {A : Type'} (r : nat) : (term91 A r) = (term92 A r).
Proof. exact (eq_refl (term91 A r)). Qed.
Lemma lem7605005 {A : Type'} (r : nat) : (term93 A r) = (term75 A r).
Proof. exact (MK_COMB (@lem7605003 A r) (@lem7605004 A r)). Qed.
Lemma lem7605006 {A : Type'} : (term94 A) = (term76 A).
Proof. exact (fun_ext (fun r : nat => @lem7605005 A r)). Qed.
Lemma lem7605007 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7605008 {A : Type'} : (term83 A) = (term77 A).
Proof. exact (MK_COMB (@lem7605007) (@lem7605006 A)). Qed.
Lemma lem7605009 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7605010 {A : Type'} : (term95 A) = (term96 A).
Proof. exact (MK_COMB (@lem7605009) (@lem7605008 A)). Qed.
Lemma lem7605011 {A : Type'} (r : nat) : (term87 A r) = (term88 A r).
Proof. exact (eq_refl (term87 A r)). Qed.
Lemma lem7605012 {A : Type'} : (term97 A) = (term85 A).
Proof. exact (fun_ext (fun r : nat => @lem7605011 A r)). Qed.
Lemma lem7605013 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7605014 {A : Type'} : (term98 A) = (term99 A).
Proof. exact (MK_COMB (@lem7605013) (@lem7605012 A)). Qed.
Lemma lem7605015 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7605016 {A : Type'} : (term100 A) = (term101 A).
Proof. exact (MK_COMB (@lem7605015) (@lem7605014 A)). Qed.
Lemma lem7605017 {A : Type'} (r : nat) : (term91 A r) = (term92 A r).
Proof. exact (eq_refl (term91 A r)). Qed.
Lemma lem7605018 {A : Type'} : (term102 A) = (term86 A).
Proof. exact (fun_ext (fun r : nat => @lem7605017 A r)). Qed.
Lemma lem7605019 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7605020 {A : Type'} : (term103 A) = (term104 A).
Proof. exact (MK_COMB (@lem7605019) (@lem7605018 A)). Qed.
Lemma lem7605021 {A : Type'} : (term84 A) = (term105 A).
Proof. exact (MK_COMB (@lem7605016 A) (@lem7605020 A)). Qed.
Lemma lem7605022 {A : Type'} : ((term83 A) = (term84 A)) = ((term77 A) = (term105 A)).
Proof. exact (MK_COMB (@lem7605010 A) (@lem7605021 A)). Qed.
Lemma lem7605023 {A : Type'} : (term77 A) = (term105 A).
Proof. exact (EQ_MP (@lem7605022 A) (@lem7605000 A)). Qed.
Lemma lem7605120 {A : Type'} : (term57 A) = (term57 A).
Proof. exact (eq_refl (term57 A)). Qed.
Lemma lem7605123 {A : Type'} : (term78 A) = (term106 A).
Proof. exact (MK_COMB (@lem7605120 A) (@lem7605023 A)). Qed.
Lemma lem7605124 {A : Type'} : (term42 A) = (term106 A).
Proof. exact (TRANS (@lem7604992 A) (@lem7605123 A)). Qed.
Lemma lem7605125 {A : Type'} (h1 : term42 A) : term106 A.
Proof. exact (EQ_MP (@lem7605124 A) (@lem7604875 A h1)). Qed.
Lemma lem7605126 {A : Type'} (x : nat) (h1 : term68 A x) : term68 A x.
Proof. exact (h1). Qed.
Lemma lem7605156 {A : Type'} (r : nat) : (term92 A r) = (term92 A r).
Proof. exact (eq_refl (term92 A r)). Qed.
Lemma lem7605157 {A : Type'} : (term86 A) = (term86 A).
Proof. exact (fun_ext (fun r : nat => @lem7605156 A r)). Qed.
Lemma lem7605158 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7605159 {A : Type'} : (term104 A) = (term104 A).
Proof. exact (MK_COMB (@lem7605158) (@lem7605157 A)). Qed.
Lemma lem7605188 {A : Type'} (r : nat) : (term88 A r) = (term88 A r).
Proof. exact (eq_refl (term88 A r)). Qed.
Lemma lem7605189 {A : Type'} : (term85 A) = (term85 A).
Proof. exact (fun_ext (fun r : nat => @lem7605188 A r)). Qed.
Lemma lem7605190 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7605191 {A : Type'} : (term99 A) = (term99 A).
Proof. exact (MK_COMB (@lem7605190) (@lem7605189 A)). Qed.
Lemma lem7605192 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7605193 {A : Type'} : (term101 A) = (term101 A).
Proof. exact (MK_COMB (@lem7605192) (@lem7605191 A)). Qed.
Lemma lem7605194 {A : Type'} : (term105 A) = (term105 A).
Proof. exact (MK_COMB (@lem7605193 A) (@lem7605159 A)). Qed.
Lemma lem7605203 {A : Type'} (a : finite_image A) : ((term54 A a) = a) = ((term54 A a) = a).
Proof. exact (eq_refl ((term54 A a) = a)). Qed.
Lemma lem7605204 {A : Type'} : (term55 A) = (term55 A).
Proof. exact (fun_ext (fun a : finite_image A => @lem7605203 A a)). Qed.
Lemma lem7605205 {A : Type'} : (@all (finite_image A)) = (@all (finite_image A)).
Proof. exact (eq_refl (@all (finite_image A))). Qed.
Lemma lem7605206 {A : Type'} : (term56 A) = (term56 A).
Proof. exact (MK_COMB (@lem7605205 A) (@lem7605204 A)). Qed.
Lemma lem7605207 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7605208 {A : Type'} : (term57 A) = (term57 A).
Proof. exact (MK_COMB (@lem7605207) (@lem7605206 A)). Qed.
Lemma lem7605209 {A : Type'} : (term106 A) = (term106 A).
Proof. exact (MK_COMB (@lem7605208 A) (@lem7605194 A)). Qed.
Lemma lem7605210 {A : Type'} (h1 : term42 A) : term106 A.
Proof. exact (EQ_MP (@lem7605209 A) (@lem7605125 A h1)). Qed.
Lemma lem7605266 {A : Type'} (x : nat) (y : nat) (h1 : term59 A x y) : term59 A x y.
Proof. exact (h1). Qed.
Lemma lem7605268 {A : Type'} (x : nat) (y : nat) (h1 : term59 A x y) : term25 A x y.
Proof. exact (proj1 (@lem7605266 A x y h1)). Qed.
Lemma lem7605269 {A : Type'} (x : nat) (y : nat) (h1 : term59 A x y) : term24 A x y.
Proof. exact (proj2 (@lem7605268 A x y h1)). Qed.
Lemma lem7605273 {A : Type'} (h1 : term42 A) : term105 A.
Proof. exact (proj2 (@lem7605210 A h1)). Qed.
Lemma lem7605275 {A : Type'} (h1 : term42 A) : term104 A.
Proof. exact (proj2 (@lem7605273 A h1)). Qed.
Lemma lem7605320 {A : Type'} (r : nat) : (term92 A r) = (term92 A r).
Proof. exact (eq_refl (term92 A r)). Qed.
Lemma lem7605321 {A : Type'} : (term86 A) = (term86 A).
Proof. exact (fun_ext (fun r : nat => @lem7605320 A r)). Qed.
Lemma lem7605322 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7605324 {A : Type'} : (term104 A) = (term104 A).
Proof. exact (MK_COMB (@lem7605322) (@lem7605321 A)). Qed.
Lemma lem7605325 {A : Type'} (h1 : term42 A) : term104 A.
Proof. exact (EQ_MP (@lem7605324 A) (@lem7605275 A h1)). Qed.
Lemma lem7605332 {A : Type'} (_97790 : nat) (h1 : term42 A) : term91 A _97790.
Proof. exact (@lem7605325 A h1 _97790). Qed.
Lemma lem7605333 {A : Type'} (_97790 : nat) : (term91 A _97790) = (term92 A _97790).
Proof. exact (eq_refl (term91 A _97790)). Qed.
Lemma lem7605336 {A : Type'} (x : nat) (y : nat) (h1 : term59 A x y) : term107 x y.
Proof. exact (proj2 (@lem7605266 A x y h1)). Qed.
Lemma lem7605356 {A : Type'} (_97790 : nat) (h1 : term42 A) : term92 A _97790.
Proof. exact (EQ_MP (@lem7605333 A _97790) (@lem7605332 A _97790 h1)). Qed.
Lemma lem7605376 {A : Type'} : (@dest_finite_image A) = (@dest_finite_image A).
Proof. exact (eq_refl (@dest_finite_image A)). Qed.
Lemma lem7605377 {A : Type'} (_97795 : finite_image A) (_97796 : finite_image A) (h1 : _97795 = _97796) : _97795 = _97796.
Proof. exact (h1). Qed.
Lemma lem7605378 {A : Type'} (_97795 : finite_image A) (_97796 : finite_image A) (h1 : _97795 = _97796) : (@dest_finite_image A _97795) = (@dest_finite_image A _97796).
Proof. exact (MK_COMB (@lem7605376 A) (@lem7605377 A _97795 _97796 h1)). Qed.
Lemma lem7605379 {A : Type'} (_97795 : finite_image A) (_97796 : finite_image A) : term108 A _97795 _97796.
Proof. exact (fun h0 : _97795 = _97796 => @lem7605378 A _97795 _97796 h0). Qed.
Lemma lem7605381 (a : Prop) (b : Prop) : (a -> b) = (term109 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem7605382 {A : Type'} (_97795 : finite_image A) (_97796 : finite_image A) : (term108 A _97795 _97796) = (term110 A _97795 _97796).
Proof. exact (@lem7605381 (_97795 = _97796) ((@dest_finite_image A _97795) = (@dest_finite_image A _97796))). Qed.
Lemma lem7605383 {A : Type'} (_97795 : finite_image A) (_97796 : finite_image A) : term110 A _97795 _97796.
Proof. exact (EQ_MP (@lem7605382 A _97795 _97796) (@lem7605379 A _97795 _97796)). Qed.
Lemma lem7605434 (x : nat) (y : nat) (z : nat) : term111 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem7605440 {A : Type'} (x : nat) (y : nat) (h1 : term59 A x y) : (@finite_index A x) = (@finite_index A y).
Proof. exact (proj2 (@lem7605269 A x y h1)). Qed.
Lemma lem7605441 {A : Type'} (x : nat) (y : nat) (h1 : term59 A x y) : term112 A x y.
Proof. exact (fun h0 : term113 A x y => @lem7605440 A x y h1). Qed.
Lemma lem7605443 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7605444 {A : Type'} (x : nat) (y : nat) : (term112 A x y) = ((@finite_index A x) = (@finite_index A y)).
Proof. exact (@lem7605443 ((@finite_index A x) = (@finite_index A y))). Qed.
Lemma lem7605445 {A : Type'} (x : nat) (y : nat) (h1 : term59 A x y) : (@finite_index A x) = (@finite_index A y).
Proof. exact (EQ_MP (@lem7605444 A x y) (@lem7605441 A x y h1)). Qed.
Lemma lem7605451 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7605452 {A : Type'} (_97795 : finite_image A) (_97796 : finite_image A) : (term110 A _97795 _97796) = (term115 A _97795 _97796).
Proof. exact (@lem7605451 ((@dest_finite_image A _97795) = (@dest_finite_image A _97796)) (term116 A _97795 _97796)). Qed.
Lemma lem7605462 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7605463 {A : Type'} (_97795 : finite_image A) (_97796 : finite_image A) : (term117 A _97795 _97796) = (term118 A _97795 _97796).
Proof. exact (MK_COMB (@lem7605462) (@lem7605452 A _97795 _97796)). Qed.
Lemma lem7605473 {A : Type'} (_97795 : finite_image A) (_97796 : finite_image A) : (term115 A _97795 _97796) = (term115 A _97795 _97796).
Proof. exact (eq_refl (term115 A _97795 _97796)). Qed.
Lemma lem7605474 {A : Type'} (_97795 : finite_image A) (_97796 : finite_image A) : ((term110 A _97795 _97796) = (term115 A _97795 _97796)) = ((term115 A _97795 _97796) = (term115 A _97795 _97796)).
Proof. exact (MK_COMB (@lem7605463 A _97795 _97796) (@lem7605473 A _97795 _97796)). Qed.
Lemma lem7605476 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7605477 (x : Prop) : (x = x) = True.
Proof. exact (@lem7605476 Prop x). Qed.
Lemma lem7605478 {A : Type'} (_97795 : finite_image A) (_97796 : finite_image A) : ((term115 A _97795 _97796) = (term115 A _97795 _97796)) = True.
Proof. exact (@lem7605477 (term115 A _97795 _97796)). Qed.
Lemma lem7605479 {A : Type'} (_97795 : finite_image A) (_97796 : finite_image A) : ((term110 A _97795 _97796) = (term115 A _97795 _97796)) = True.
Proof. exact (TRANS (@lem7605474 A _97795 _97796) (@lem7605478 A _97795 _97796)). Qed.
Lemma lem7605480 {A : Type'} (_97795 : finite_image A) (_97796 : finite_image A) : True = ((term110 A _97795 _97796) = (term115 A _97795 _97796)).
Proof. exact (SYM (@lem7605479 A _97795 _97796)). Qed.
Lemma lem7605481 {A : Type'} (_97795 : finite_image A) (_97796 : finite_image A) : (term110 A _97795 _97796) = (term115 A _97795 _97796).
Proof. exact (EQ_MP (@lem7605480 A _97795 _97796) (@lem0)). Qed.
Lemma lem7605482 {A : Type'} (_97795 : finite_image A) (_97796 : finite_image A) : term115 A _97795 _97796.
Proof. exact (EQ_MP (@lem7605481 A _97795 _97796) (@lem7605383 A _97795 _97796)). Qed.
Lemma lem7605484 (b : Prop) (a : Prop) : (a \/ b) = (term119 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7605485 {A : Type'} (_97795 : finite_image A) (_97796 : finite_image A) : (term115 A _97795 _97796) = (term120 A _97795 _97796).
Proof. exact (@lem7605484 (term116 A _97795 _97796) ((@dest_finite_image A _97795) = (@dest_finite_image A _97796))). Qed.
Lemma lem7605487 (a : Prop) : (term121 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7605488 {A : Type'} (_97795 : finite_image A) (_97796 : finite_image A) : (term122 A _97795 _97796) = (_97795 = _97796).
Proof. exact (@lem7605487 (_97795 = _97796)). Qed.
Lemma lem7605489 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7605490 {A : Type'} (_97795 : finite_image A) (_97796 : finite_image A) : (term123 A _97795 _97796) = (term124 A _97795 _97796).
Proof. exact (MK_COMB (@lem7605489) (@lem7605488 A _97795 _97796)). Qed.
Lemma lem7605491 {A : Type'} (_97795 : finite_image A) (_97796 : finite_image A) : ((@dest_finite_image A _97795) = (@dest_finite_image A _97796)) = ((@dest_finite_image A _97795) = (@dest_finite_image A _97796)).
Proof. exact (eq_refl ((@dest_finite_image A _97795) = (@dest_finite_image A _97796))). Qed.
Lemma lem7605492 {A : Type'} (_97795 : finite_image A) (_97796 : finite_image A) : (term120 A _97795 _97796) = (term108 A _97795 _97796).
Proof. exact (MK_COMB (@lem7605490 A _97795 _97796) (@lem7605491 A _97795 _97796)). Qed.
Lemma lem7605493 {A : Type'} (_97795 : finite_image A) (_97796 : finite_image A) : (term115 A _97795 _97796) = (term108 A _97795 _97796).
Proof. exact (TRANS (@lem7605485 A _97795 _97796) (@lem7605492 A _97795 _97796)). Qed.
Lemma lem7605496 {A : Type'} (_97795 : finite_image A) (_97796 : finite_image A) : term108 A _97795 _97796.
Proof. exact (EQ_MP (@lem7605493 A _97795 _97796) (@lem7605482 A _97795 _97796)). Qed.
Lemma lem7605497 {A : Type'} (_97795 : finite_image A) (_97796 : finite_image A) : term108 A _97795 _97796.
Proof. exact (@lem7605496 A _97795 _97796). Qed.
Lemma lem7605498 {A : Type'} (x : nat) (y : nat) : term125 A x y.
Proof. exact (@lem7605497 A (@finite_index A x) (@finite_index A y)). Qed.
Lemma lem7605501 {A : Type'} (x : nat) (y : nat) (h1 : term59 A x y) : (term51 A x) = (term51 A y).
Proof. exact (@lem7605498 A x y (@lem7605445 A x y h1)). Qed.
Lemma lem7605502 {A : Type'} (x : nat) (y : nat) (h1 : term59 A x y) : term126 A x y.
Proof. exact (fun h0 : term127 A x y => @lem7605501 A x y h1). Qed.
Lemma lem7605504 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7605505 {A : Type'} (x : nat) (y : nat) : (term126 A x y) = ((term51 A x) = (term51 A y)).
Proof. exact (@lem7605504 ((term51 A x) = (term51 A y))). Qed.
Lemma lem7605506 {A : Type'} (x : nat) (y : nat) (h1 : term59 A x y) : (term51 A x) = (term51 A y).
Proof. exact (EQ_MP (@lem7605505 A x y) (@lem7605502 A x y h1)). Qed.
Lemma lem7605508 {A : Type'} (x : nat) (y : nat) (h1 : term59 A x y) : term22 A x.
Proof. exact (proj1 (@lem7605268 A x y h1)). Qed.
Lemma lem7605509 {A : Type'} (x : nat) (y : nat) (h1 : term59 A x y) : term128 A x.
Proof. exact (fun h0 : term129 A x => @lem7605508 A x y h1). Qed.
Lemma lem7605511 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7605512 {A : Type'} (x : nat) : (term128 A x) = (term22 A x).
Proof. exact (@lem7605511 (term22 A x)). Qed.
Lemma lem7605513 {A : Type'} (x : nat) (y : nat) (h1 : term59 A x y) : term22 A x.
Proof. exact (EQ_MP (@lem7605512 A x) (@lem7605509 A x y h1)). Qed.
Lemma lem7605519 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7605520 {A : Type'} (_97790 : nat) : (term92 A _97790) = (term130 A _97790).
Proof. exact (@lem7605519 ((term51 A _97790) = _97790) (term129 A _97790)). Qed.
Lemma lem7605528 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7605529 {A : Type'} (_97790 : nat) : (term131 A _97790) = (term132 A _97790).
Proof. exact (MK_COMB (@lem7605528) (@lem7605520 A _97790)). Qed.
Lemma lem7605537 {A : Type'} (_97790 : nat) : (term130 A _97790) = (term130 A _97790).
Proof. exact (eq_refl (term130 A _97790)). Qed.
Lemma lem7605538 {A : Type'} (_97790 : nat) : ((term92 A _97790) = (term130 A _97790)) = ((term130 A _97790) = (term130 A _97790)).
Proof. exact (MK_COMB (@lem7605529 A _97790) (@lem7605537 A _97790)). Qed.
Lemma lem7605540 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7605541 (x : Prop) : (x = x) = True.
Proof. exact (@lem7605540 Prop x). Qed.
Lemma lem7605542 {A : Type'} (_97790 : nat) : ((term130 A _97790) = (term130 A _97790)) = True.
Proof. exact (@lem7605541 (term130 A _97790)). Qed.
Lemma lem7605543 {A : Type'} (_97790 : nat) : ((term92 A _97790) = (term130 A _97790)) = True.
Proof. exact (TRANS (@lem7605538 A _97790) (@lem7605542 A _97790)). Qed.
Lemma lem7605544 {A : Type'} (_97790 : nat) : True = ((term92 A _97790) = (term130 A _97790)).
Proof. exact (SYM (@lem7605543 A _97790)). Qed.
Lemma lem7605545 {A : Type'} (_97790 : nat) : (term92 A _97790) = (term130 A _97790).
Proof. exact (EQ_MP (@lem7605544 A _97790) (@lem0)). Qed.
Lemma lem7605546 {A : Type'} (_97790 : nat) (h1 : term42 A) : term130 A _97790.
Proof. exact (EQ_MP (@lem7605545 A _97790) (@lem7605356 A _97790 h1)). Qed.
Lemma lem7605548 (b : Prop) (a : Prop) : (a \/ b) = (term119 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7605549 {A : Type'} (_97790 : nat) : (term130 A _97790) = (term133 A _97790).
Proof. exact (@lem7605548 (term129 A _97790) ((term51 A _97790) = _97790)). Qed.
Lemma lem7605551 (a : Prop) : (term121 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7605552 {A : Type'} (_97790 : nat) : (term134 A _97790) = (term22 A _97790).
Proof. exact (@lem7605551 (term22 A _97790)). Qed.
Lemma lem7605553 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7605554 {A : Type'} (_97790 : nat) : (term135 A _97790) = (term136 A _97790).
Proof. exact (MK_COMB (@lem7605553) (@lem7605552 A _97790)). Qed.
Lemma lem7605555 {A : Type'} (_97790 : nat) : ((term51 A _97790) = _97790) = ((term51 A _97790) = _97790).
Proof. exact (eq_refl ((term51 A _97790) = _97790)). Qed.
Lemma lem7605556 {A : Type'} (_97790 : nat) : (term133 A _97790) = (term137 A _97790).
Proof. exact (MK_COMB (@lem7605554 A _97790) (@lem7605555 A _97790)). Qed.
Lemma lem7605557 {A : Type'} (_97790 : nat) : (term130 A _97790) = (term137 A _97790).
Proof. exact (TRANS (@lem7605549 A _97790) (@lem7605556 A _97790)). Qed.
Lemma lem7605560 {A : Type'} (_97790 : nat) (h1 : term42 A) : term137 A _97790.
Proof. exact (EQ_MP (@lem7605557 A _97790) (@lem7605546 A _97790 h1)). Qed.
Lemma lem7605561 {A : Type'} (x : nat) (h1 : term42 A) : term137 A x.
Proof. exact (@lem7605560 A x h1). Qed.
Lemma lem7605564 {A : Type'} (x : nat) (y : nat) (h1 : term42 A) (h2 : term59 A x y) : (term51 A x) = x.
Proof. exact (@lem7605561 A x h1 (@lem7605513 A x y h2)). Qed.
Lemma lem7605565 {A : Type'} (x : nat) (y : nat) (h1 : term42 A) (h2 : term59 A x y) : term138 A x.
Proof. exact (fun h0 : term139 A x => @lem7605564 A x y h1 h2). Qed.
Lemma lem7605567 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7605568 {A : Type'} (x : nat) : (term138 A x) = ((term51 A x) = x).
Proof. exact (@lem7605567 ((term51 A x) = x)). Qed.
Lemma lem7605569 {A : Type'} (x : nat) (y : nat) (h1 : term42 A) (h2 : term59 A x y) : (term51 A x) = x.
Proof. exact (EQ_MP (@lem7605568 A x) (@lem7605565 A x y h1 h2)). Qed.
Lemma lem7605587 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7605588 (y : nat) (x : nat) (z : nat) : (term140 x y z) = (term141 y x z).
Proof. exact (@lem7605587 (y = z) (term107 x z)). Qed.
Lemma lem7605598 (x : nat) (y : nat) : (term142 x y) = (term142 x y).
Proof. exact (eq_refl (term142 x y)). Qed.
Lemma lem7605599 (y : nat) (x : nat) (z : nat) : (term111 x y z) = (term143 y x z).
Proof. exact (MK_COMB (@lem7605598 x y) (@lem7605588 y x z)). Qed.
Lemma lem7605603 (q : Prop) (p : Prop) (r : Prop) : (term144 p q r) = (term144 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7605604 (y : nat) (x : nat) (z : nat) : (term143 y x z) = (term145 y x z).
Proof. exact (@lem7605603 (y = z) (term107 x y) (term107 x z)). Qed.
Lemma lem7605626 (y : nat) (x : nat) (z : nat) : (term111 x y z) = (term145 y x z).
Proof. exact (TRANS (@lem7605599 y x z) (@lem7605604 y x z)). Qed.
Lemma lem7605627 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7605628 (y : nat) (x : nat) (z : nat) : (term146 x y z) = (term147 y x z).
Proof. exact (MK_COMB (@lem7605627) (@lem7605626 y x z)). Qed.
Lemma lem7605650 (y : nat) (x : nat) (z : nat) : (term145 y x z) = (term145 y x z).
Proof. exact (eq_refl (term145 y x z)). Qed.
Lemma lem7605651 (y : nat) (x : nat) (z : nat) : ((term111 x y z) = (term145 y x z)) = ((term145 y x z) = (term145 y x z)).
Proof. exact (MK_COMB (@lem7605628 y x z) (@lem7605650 y x z)). Qed.
Lemma lem7605653 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7605654 (x : Prop) : (x = x) = True.
Proof. exact (@lem7605653 Prop x). Qed.
Lemma lem7605655 (y : nat) (x : nat) (z : nat) : ((term145 y x z) = (term145 y x z)) = True.
Proof. exact (@lem7605654 (term145 y x z)). Qed.
Lemma lem7605656 (y : nat) (x : nat) (z : nat) : ((term111 x y z) = (term145 y x z)) = True.
Proof. exact (TRANS (@lem7605651 y x z) (@lem7605655 y x z)). Qed.
Lemma lem7605657 (y : nat) (x : nat) (z : nat) : True = ((term111 x y z) = (term145 y x z)).
Proof. exact (SYM (@lem7605656 y x z)). Qed.
Lemma lem7605658 (y : nat) (x : nat) (z : nat) : (term111 x y z) = (term145 y x z).
Proof. exact (EQ_MP (@lem7605657 y x z) (@lem0)). Qed.
Lemma lem7605659 (y : nat) (x : nat) (z : nat) : term145 y x z.
Proof. exact (EQ_MP (@lem7605658 y x z) (@lem7605434 x y z)). Qed.
Lemma lem7605661 (b : Prop) (a : Prop) : (a \/ b) = (term119 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7605662 (x : nat) (y : nat) (z : nat) : (term145 y x z) = (term148 x y z).
Proof. exact (@lem7605661 (term149 y x z) (y = z)). Qed.
Lemma lem7605664 (a : Prop) (b : Prop) : (term150 a b) = (term151 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7605665 (y : nat) (x : nat) (z : nat) : (term152 y x z) = (term153 y x z).
Proof. exact (@lem7605664 (term107 x y) (term107 x z)). Qed.
Lemma lem7605667 (a : Prop) : (term121 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7605668 (x : nat) (y : nat) : (term154 x y) = (x = y).
Proof. exact (@lem7605667 (x = y)). Qed.
Lemma lem7605669 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7605670 (x : nat) (y : nat) : (term155 x y) = (term156 x y).
Proof. exact (MK_COMB (@lem7605669) (@lem7605668 x y)). Qed.
Lemma lem7605672 (a : Prop) : (term121 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7605673 (x : nat) (z : nat) : (term154 x z) = (x = z).
Proof. exact (@lem7605672 (x = z)). Qed.
Lemma lem7605674 (y : nat) (x : nat) (z : nat) : (term153 y x z) = (term157 y x z).
Proof. exact (MK_COMB (@lem7605670 x y) (@lem7605673 x z)). Qed.
Lemma lem7605675 (y : nat) (x : nat) (z : nat) : (term152 y x z) = (term157 y x z).
Proof. exact (TRANS (@lem7605665 y x z) (@lem7605674 y x z)). Qed.
Lemma lem7605676 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7605677 (y : nat) (x : nat) (z : nat) : (term158 y x z) = (term159 y x z).
Proof. exact (MK_COMB (@lem7605676) (@lem7605675 y x z)). Qed.
Lemma lem7605678 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem7605679 (x : nat) (y : nat) (z : nat) : (term148 x y z) = (term160 x y z).
Proof. exact (MK_COMB (@lem7605677 y x z) (@lem7605678 y z)). Qed.
Lemma lem7605680 (x : nat) (y : nat) (z : nat) : (term145 y x z) = (term160 x y z).
Proof. exact (TRANS (@lem7605662 x y z) (@lem7605679 x y z)). Qed.
Lemma lem7605682 {A : Type'} (x : nat) (y : nat) (h1 : term42 A) (h2 : term59 A x y) : term161 A y x.
Proof. exact (conj (@lem7605506 A x y h2) (@lem7605569 A x y h1 h2)). Qed.
Lemma lem7605684 (x : nat) (y : nat) (z : nat) : term160 x y z.
Proof. exact (EQ_MP (@lem7605680 x y z) (@lem7605659 y x z)). Qed.
Lemma lem7605685 {A : Type'} (y : nat) (x : nat) : term162 A y x.
Proof. exact (@lem7605684 (term51 A x) (term51 A y) x). Qed.
Lemma lem7605688 {A : Type'} (x : nat) (y : nat) (h1 : term42 A) (h2 : term59 A x y) : (term51 A y) = x.
Proof. exact (@lem7605685 A y x (@lem7605682 A x y h1 h2)). Qed.
Lemma lem7605689 {A : Type'} (x : nat) (y : nat) (h1 : term42 A) (h2 : term59 A x y) : term163 A y x.
Proof. exact (fun h0 : term164 A y x => @lem7605688 A x y h1 h2). Qed.
Lemma lem7605691 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7605692 {A : Type'} (y : nat) (x : nat) : (term163 A y x) = ((term51 A y) = x).
Proof. exact (@lem7605691 ((term51 A y) = x)). Qed.
Lemma lem7605693 {A : Type'} (x : nat) (y : nat) (h1 : term42 A) (h2 : term59 A x y) : (term51 A y) = x.
Proof. exact (EQ_MP (@lem7605692 A y x) (@lem7605689 A x y h1 h2)). Qed.
Lemma lem7605695 {A : Type'} (x : nat) (y : nat) (h1 : term59 A x y) : term22 A y.
Proof. exact (proj1 (@lem7605269 A x y h1)). Qed.
Lemma lem7605696 {A : Type'} (x : nat) (y : nat) (h1 : term59 A x y) : term128 A y.
Proof. exact (fun h0 : term129 A y => @lem7605695 A x y h1). Qed.
Lemma lem7605698 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7605699 {A : Type'} (y : nat) : (term128 A y) = (term22 A y).
Proof. exact (@lem7605698 (term22 A y)). Qed.
Lemma lem7605700 {A : Type'} (x : nat) (y : nat) (h1 : term59 A x y) : term22 A y.
Proof. exact (EQ_MP (@lem7605699 A y) (@lem7605696 A x y h1)). Qed.
Lemma lem7605702 {A : Type'} (_97790 : nat) (h1 : term42 A) : term137 A _97790.
Proof. exact (EQ_MP (@lem7605557 A _97790) (@lem7605546 A _97790 h1)). Qed.
Lemma lem7605703 {A : Type'} (y : nat) (h1 : term42 A) : term137 A y.
Proof. exact (@lem7605702 A y h1). Qed.
Lemma lem7605706 {A : Type'} (x : nat) (y : nat) (h1 : term42 A) (h2 : term59 A x y) : (term51 A y) = y.
Proof. exact (@lem7605703 A y h1 (@lem7605700 A x y h2)). Qed.
Lemma lem7605707 {A : Type'} (x : nat) (y : nat) (h1 : term42 A) (h2 : term59 A x y) : term138 A y.
Proof. exact (fun h0 : term139 A y => @lem7605706 A x y h1 h2). Qed.
Lemma lem7605709 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7605710 {A : Type'} (y : nat) : (term138 A y) = ((term51 A y) = y).
Proof. exact (@lem7605709 ((term51 A y) = y)). Qed.
Lemma lem7605711 {A : Type'} (x : nat) (y : nat) (h1 : term42 A) (h2 : term59 A x y) : (term51 A y) = y.
Proof. exact (EQ_MP (@lem7605710 A y) (@lem7605707 A x y h1 h2)). Qed.
Lemma lem7605712 {A : Type'} (x : nat) (y : nat) (h1 : term42 A) (h2 : term59 A x y) : term165 A x y.
Proof. exact (conj (@lem7605693 A x y h1 h2) (@lem7605711 A x y h1 h2)). Qed.
Lemma lem7605714 (x : nat) (y : nat) (z : nat) : term160 x y z.
Proof. exact (EQ_MP (@lem7605680 x y z) (@lem7605659 y x z)). Qed.
Lemma lem7605715 {A : Type'} (x : nat) (y : nat) : term166 A x y.
Proof. exact (@lem7605714 (term51 A y) x y). Qed.
Lemma lem7605718 {A : Type'} (x : nat) (y : nat) (h1 : term42 A) (h2 : term59 A x y) : x = y.
Proof. exact (@lem7605715 A x y (@lem7605712 A x y h1 h2)). Qed.
Lemma lem7605719 {A : Type'} (x : nat) (y : nat) (h1 : term42 A) (h2 : term59 A x y) : term167 x y.
Proof. exact (fun h0 : term107 x y => @lem7605718 A x y h1 h2). Qed.
Lemma lem7605721 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7605722 (x : nat) (y : nat) : (term167 x y) = (x = y).
Proof. exact (@lem7605721 (x = y)). Qed.
Lemma lem7605723 {A : Type'} (x : nat) (y : nat) (h1 : term42 A) (h2 : term59 A x y) : x = y.
Proof. exact (EQ_MP (@lem7605722 x y) (@lem7605719 A x y h1 h2)). Qed.
Lemma lem7605726 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7605728 (x : nat) (y : nat) : (term107 x y) = (term168 x y).
Proof. exact (@lem7605726 (x = y)). Qed.
Lemma lem7605731 {A : Type'} (x : nat) (y : nat) (h1 : term59 A x y) : term168 x y.
Proof. exact (EQ_MP (@lem7605728 x y) (@lem7605336 A x y h1)). Qed.
Lemma lem7605734 {A : Type'} (x : nat) (y : nat) (h1 : term42 A) (h2 : term59 A x y) : False.
Proof. exact (@lem7605731 A x y h2 (@lem7605723 A x y h1 h2)). Qed.
Lemma lem7605735 {A : Type'} (x : nat) (y : nat) (h1 : term42 A) (h2 : term59 A x y) : term169.
Proof. exact (fun h0 : ~ False => @lem7605734 A x y h1 h2). Qed.
Lemma lem7605737 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7605738 : term169 = False.
Proof. exact (@lem7605737 False). Qed.
Lemma lem7605739 {A : Type'} (x : nat) (y : nat) (h1 : term42 A) (h2 : term59 A x y) : False.
Proof. exact (EQ_MP (@lem7605738) (@lem7605735 A x y h1 h2)). Qed.
Lemma lem7605740 {A : Type'} (x : nat) (y : nat) (h1 : term42 A) (h2 : term59 A x y) : (term59 A x y) = False.
Proof. exact (prop_ext (fun h3 : term59 A x y => @lem7605739 A x y h1 h2) (fun h3 : False => @lem7605266 A x y h2)). Qed.
Lemma lem7605741 {A : Type'} (x : nat) (y : nat) (h1 : term42 A) (h2 : term59 A x y) : False.
Proof. exact (EQ_MP (@lem7605740 A x y h1 h2) (@lem7605266 A x y h2)). Qed.
Lemma lem7605742 {A : Type'} (x : nat) (h1 : term68 A x) (h2 : term42 A) : False.
Proof. exact (ex_elim (@lem7605126 A x h1) (fun y : nat => fun h0 : term67 A x y => @lem7605741 A x y h2 h0)). Qed.
Lemma lem7605743 {A : Type'} (h1 : term41 A) (h2 : term42 A) : False.
Proof. exact (ex_elim (@lem7604967 A h1) (fun x : nat => fun h0 : term73 A x => @lem7605742 A x h0 h2)). Qed.
Lemma lem7605744 {A : Type'} (h1 : term41 A) : term47 A.
Proof. exact (fun h0 : term42 A => @lem7605743 A h1 h0). Qed.
Lemma lem7605745 {A : Type'} : (term47 A) = (term48 A).
Proof. exact (@lem69 (term42 A)). Qed.
Lemma lem7605746 {A : Type'} (h1 : term41 A) : term48 A.
Proof. exact (EQ_MP (@lem7605745 A) (@lem7605744 A h1)). Qed.
Lemma lem7605747 {A : Type'} : term50 A.
Proof. exact (fun h0 : term41 A => @lem7605746 A h0). Qed.
Lemma lem7605748 {A : Type'} : term43 A.
Proof. exact (EQ_MP (@lem7604873 A) (@lem7605747 A)). Qed.
Lemma lem7605750 {A : Type'} : term43 A.
Proof. exact (@lem7604757 A (@lem7605748 A)). Qed.
Lemma lem7605751 {A : Type'} (h1 : term41 A) : term47 A.
Proof. exact (@lem7605750 A (@lem7604737 A h1)). Qed.
Lemma lem7605752 {A : Type'} (h1 : term41 A) : False.
Proof. exact (@lem7605751 A h1 (@lem7604738 A)). Qed.
Lemma lem7605753 {A : Type'} (h1 : term41 A) : (term41 A) = False.
Proof. exact (prop_ext (fun h2 : term41 A => @lem7605752 A h1) (fun h2 : False => @lem7604737 A h1)). Qed.
Lemma lem7605754 {A : Type'} (h1 : term41 A) : False.
Proof. exact (EQ_MP (@lem7605753 A h1) (@lem7604737 A h1)). Qed.
Lemma lem7605755 {A : Type'} : term40 A.
Proof. exact (fun h0 : term41 A => @lem7605754 A h0). Qed.
Lemma lem7605756 {A : Type'} : term31 A.
Proof. exact (EQ_MP (@lem7604736 A) (@lem7605755 A)). Qed.
Lemma lem7605757 {A : Type'} : term37 A.
Proof. exact (EQ_MP (@lem7604732 A) (@lem7605756 A)). Qed.
Lemma lem7605758 {A : Type'} (s : A -> Prop) : term36 A s.
Proof. exact (EQ_MP (@lem7604684 A s) (@lem7605757 A)). Qed.
Lemma lem7605759 {A : Type'} (s : A -> Prop) : term17 A s.
Proof. exact (@lem7604615 A s (@lem7605758 A s)). Qed.
Lemma lem7605760 {A : Type'} (s : A -> Prop) : term16 A s.
Proof. exact (EQ_MP (@lem7604611 A s) (@lem7605759 A s)). Qed.
Lemma lem7605765 {A : Type'} : term170 A.
Proof. exact (fun s : A -> Prop => @lem7605760 A s). Qed.
