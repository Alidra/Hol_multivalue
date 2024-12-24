Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_BOUND_LT_term_abbrevs.
Require Import LE_REFL_spec.
Require Import LTE_TRANS_spec.
Require Import NSUM_CONST_spec.
Require Import NSUM_LT_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm7_spec.
Lemma lem6974611 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem6974612 {A : Type'} (f : A -> nat) (h1 : term0 A) : term1 A f.
Proof. exact (@lem6974611 A h1 f). Qed.
Lemma lem6974613 {A : Type'} (f : A -> nat) : (term1 A f) = (term2 A f).
Proof. exact (eq_refl (term1 A f)). Qed.
Lemma lem6974614 {A : Type'} (f : A -> nat) (h1 : term0 A) : term2 A f.
Proof. exact (EQ_MP (@lem6974613 A f) (@lem6974612 A f h1)). Qed.
Lemma lem6974615 {A : Type'} (f : A -> nat) (g : A -> nat) (h1 : term0 A) : term3 A f g.
Proof. exact (@lem6974614 A f h1 g). Qed.
Lemma lem6974616 {A : Type'} (f : A -> nat) (g : A -> nat) : (term3 A f g) = (term4 A f g).
Proof. exact (eq_refl (term3 A f g)). Qed.
Lemma lem6974617 {A : Type'} (f : A -> nat) (g : A -> nat) (h1 : term0 A) : term4 A f g.
Proof. exact (EQ_MP (@lem6974616 A f g) (@lem6974615 A f g h1)). Qed.
Lemma lem6974618 {A : Type'} (f : A -> nat) (g : A -> nat) (s : A -> Prop) (h1 : term0 A) : term5 A f g s.
Proof. exact (@lem6974617 A f g h1 s). Qed.
Lemma lem6974619 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term5 A f g s) = (term6 A f s g).
Proof. exact (eq_refl (term5 A f g s)). Qed.
Lemma lem6974620 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term0 A) : term6 A f s g.
Proof. exact (EQ_MP (@lem6974619 A f s g) (@lem6974618 A f g s h1)). Qed.
Lemma lem6974621 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term7 A s f g) : term7 A s f g.
Proof. exact (h1). Qed.
Lemma lem6974622 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term0 A) (h2 : term7 A s f g) : term8 A f s g.
Proof. exact (@lem6974620 A f s g h1 (@lem6974621 A s f g h2)). Qed.
Lemma lem6974623 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term7 A s f g) : term9 A f s g.
Proof. exact (fun h0 : term0 A => @lem6974622 A s f g h0 h1). Qed.
Lemma lem6974624 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem6974625 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term0 A) (h2 : term7 A s f g) : term8 A f s g.
Proof. exact (@lem6974623 A s f g h2 (@lem6974624 A h1)). Qed.
Lemma lem6974626 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) (h1 : term0 A) : term6 A f s g.
Proof. exact (fun h0 : term7 A s f g => @lem6974625 A s f g h1 h0). Qed.
Lemma lem6974627 {A : Type'} (f : A -> nat) (s : A -> Prop) (h1 : term0 A) : term10 A f s.
Proof. exact (fun g : A -> nat => @lem6974626 A f s g h1). Qed.
Lemma lem6974628 {A : Type'} (f : A -> nat) (h1 : term0 A) : term11 A f.
Proof. exact (fun s : A -> Prop => @lem6974627 A f s h1). Qed.
Lemma lem6974629 {A : Type'} (h1 : term0 A) : term12 A.
Proof. exact (fun f : A -> nat => @lem6974628 A f h1). Qed.
Lemma lem6974630 {A : Type'} : term13 A.
Proof. exact (fun h0 : term0 A => @lem6974629 A h0). Qed.
Lemma lem6974631 {A : Type'} : term12 A.
Proof. exact (@lem6974630 A (@lem6934233 A)). Qed.
Lemma lem6974632 {A : Type'} (f : A -> nat) : term14 A f.
Proof. exact (@lem6974631 A f). Qed.
Lemma lem6974633 {A : Type'} (f : A -> nat) : (term14 A f) = (term11 A f).
Proof. exact (eq_refl (term14 A f)). Qed.
Lemma lem6974634 {A : Type'} (f : A -> nat) : term11 A f.
Proof. exact (EQ_MP (@lem6974633 A f) (@lem6974632 A f)). Qed.
Lemma lem6974635 {A : Type'} (f : A -> nat) (s : A -> Prop) : term15 A f s.
Proof. exact (@lem6974634 A f s). Qed.
Lemma lem6974636 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term15 A f s) = (term10 A f s).
Proof. exact (eq_refl (term15 A f s)). Qed.
Lemma lem6974637 {A : Type'} (f : A -> nat) (s : A -> Prop) : term10 A f s.
Proof. exact (EQ_MP (@lem6974636 A f s) (@lem6974635 A f s)). Qed.
Lemma lem6974638 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : term16 A f s g.
Proof. exact (@lem6974637 A f s g). Qed.
Lemma lem6974639 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term16 A f s g) = (term6 A f s g).
Proof. exact (eq_refl (term16 A f s g)). Qed.
Lemma lem6974641 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem6974642 (m : nat) (h1 : term17) : term18 m.
Proof. exact (@lem6974641 h1 m). Qed.
Lemma lem6974643 (m : nat) : (term18 m) = (term19 m).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem6974644 (m : nat) (h1 : term17) : term19 m.
Proof. exact (EQ_MP (@lem6974643 m) (@lem6974642 m h1)). Qed.
Lemma lem6974645 (m : nat) (n : nat) (h1 : term17) : term20 m n.
Proof. exact (@lem6974644 m h1 n). Qed.
Lemma lem6974646 (n : nat) (m : nat) : (term20 m n) = (term21 n m).
Proof. exact (eq_refl (term20 m n)). Qed.
Lemma lem6974647 (n : nat) (m : nat) (h1 : term17) : term21 n m.
Proof. exact (EQ_MP (@lem6974646 n m) (@lem6974645 m n h1)). Qed.
Lemma lem6974648 (n : nat) (m : nat) (p : nat) (h1 : term17) : term22 n m p.
Proof. exact (@lem6974647 n m h1 p). Qed.
Lemma lem6974649 (n : nat) (m : nat) (p : nat) : (term22 n m p) = (term23 n m p).
Proof. exact (eq_refl (term22 n m p)). Qed.
Lemma lem6974650 (n : nat) (m : nat) (p : nat) (h1 : term17) : term23 n m p.
Proof. exact (EQ_MP (@lem6974649 n m p) (@lem6974648 n m p h1)). Qed.
Lemma lem6974651 (m : nat) (n : nat) (p : nat) (h1 : term24 m n p) : term24 m n p.
Proof. exact (h1). Qed.
Lemma lem6974652 (m : nat) (n : nat) (p : nat) (h1 : term17) (h2 : term24 m n p) : Peano.lt m p.
Proof. exact (@lem6974650 n m p h1 (@lem6974651 m n p h2)). Qed.
Lemma lem6974653 (m : nat) (n : nat) (p : nat) (h1 : term24 m n p) : term25 m p.
Proof. exact (fun h0 : term17 => @lem6974652 m n p h0 h1). Qed.
Lemma lem6974654 (m : nat) (p : nat) (h1 : term26 m p) : term26 m p.
Proof. exact (h1). Qed.
Lemma lem6974655 (m : nat) (p : nat) (h1 : term26 m p) : term25 m p.
Proof. exact (ex_elim (@lem6974654 m p h1) (fun n : nat => fun h0 : term27 m p n => @lem6974653 m n p h0)). Qed.
Lemma lem6974656 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem6974657 (m : nat) (p : nat) (h1 : term17) (h2 : term26 m p) : Peano.lt m p.
Proof. exact (@lem6974655 m p h2 (@lem6974656 h1)). Qed.
Lemma lem6974658 (m : nat) (p : nat) (h1 : term17) : term28 m p.
Proof. exact (fun h0 : term26 m p => @lem6974657 m p h1 h0). Qed.
Lemma lem6974659 (m : nat) (h1 : term17) : term29 m.
Proof. exact (fun p : nat => @lem6974658 m p h1). Qed.
Lemma lem6974660 (h1 : term17) : term30.
Proof. exact (fun m : nat => @lem6974659 m h1). Qed.
Lemma lem6974661 : term31.
Proof. exact (fun h0 : term17 => @lem6974660 h0). Qed.
Lemma lem6974662 : term30.
Proof. exact (@lem6974661 (@lem95941)). Qed.
Lemma lem6974663 (m : nat) : term32 m.
Proof. exact (@lem6974662 m). Qed.
Lemma lem6974664 (m : nat) : (term32 m) = (term29 m).
Proof. exact (eq_refl (term32 m)). Qed.
Lemma lem6974665 (m : nat) : term29 m.
Proof. exact (EQ_MP (@lem6974664 m) (@lem6974663 m)). Qed.
Lemma lem6974666 (m : nat) (p : nat) : term33 m p.
Proof. exact (@lem6974665 m p). Qed.
Lemma lem6974667 (m : nat) (p : nat) : (term33 m p) = (term28 m p).
Proof. exact (eq_refl (term33 m p)). Qed.
Lemma lem6974669 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term34 A s f b) : term34 A s f b.
Proof. exact (h1). Qed.
Lemma lem6974670 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term35 A s f b) : term35 A s f b.
Proof. exact (h1). Qed.
Lemma lem6974671 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem6974672 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term36 A s f b) : term36 A s f b.
Proof. exact (h1). Qed.
Lemma lem6974673 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term37 A s f b) : term37 A s f b.
Proof. exact (h1). Qed.
Lemma lem6974674 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (b : nat) (h1 : term38 A s f x b) : term38 A s f x b.
Proof. exact (h1). Qed.
Lemma lem6974675 {A : Type'} (f : A -> nat) (x : A) (b : nat) (h1 : term39 A f x b) : term39 A f x b.
Proof. exact (h1). Qed.
Lemma lem6974676 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem6974678 (m : nat) (p : nat) : term28 m p.
Proof. exact (EQ_MP (@lem6974667 m p) (@lem6974666 m p)). Qed.
Lemma lem6974679 {A : Type'} (f : A -> nat) (s : A -> Prop) (b : nat) : term40 A f s b.
Proof. exact (@lem6974678 (@nsum A s f) (term41 A s b)). Qed.
Lemma lem6974681 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : term6 A f s g.
Proof. exact (EQ_MP (@lem6974639 A f s g) (@lem6974638 A f s g)). Qed.
Lemma lem6974682 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : term6 A f s g.
Proof. exact (@lem6974681 A f s g). Qed.
Lemma lem6974683 {A : Type'} (f : A -> nat) (s : A -> Prop) (b : nat) : term42 A f s b.
Proof. exact (@lem6974682 A f s (term43 A b)). Qed.
Lemma lem6974684 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem6974686 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term37 A s f b) : term44 A s f b x.
Proof. exact (@lem6974673 A s f b h1 x). Qed.
Lemma lem6974687 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (b : nat) : (term44 A s f b x) = (term45 A s f x b).
Proof. exact (eq_refl (term44 A s f b x)). Qed.
Lemma lem6974688 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term37 A s f b) : term45 A s f x b.
Proof. exact (EQ_MP (@lem6974687 A s f x b) (@lem6974686 A x s f b h1)). Qed.
Lemma lem6974689 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (b : nat) : (term45 A s f x b) = ((term45 A s f x b) = True).
Proof. exact (@lem7 (term45 A s f x b)). Qed.
Lemma lem6974698 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem6974684 A s) (@lem6974671 A s h1)). Qed.
Lemma lem6974699 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6974700 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term46 A s) = (and True).
Proof. exact (MK_COMB (@lem6974699) (@lem6974698 A s h1)). Qed.
Lemma lem6974736 {A B : Type'} (f : A -> B) (y : A) : (term47 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem6974737 {A : Type'} (f : A -> nat) (y : A) : (term48 A f y) = (f y).
Proof. exact (@lem6974736 A nat f y). Qed.
Lemma lem6974738 {A : Type'} (b : nat) (_92874 : A) : (term49 A b _92874) = (term50 A b _92874).
Proof. exact (@lem6974737 A (term43 A b) _92874). Qed.
Lemma lem6974739 {A : Type'} (x : A) (b : nat) : (term50 A b x) = b.
Proof. exact (eq_refl (term50 A b x)). Qed.
Lemma lem6974740 {A : Type'} (b : nat) : (term51 A b) = (term43 A b).
Proof. exact (fun_ext (fun x : A => @lem6974739 A x b)). Qed.
Lemma lem6974741 {A : Type'} (_92874 : A) : _92874 = _92874.
Proof. exact (eq_refl _92874). Qed.
Lemma lem6974742 {A : Type'} (b : nat) (_92874 : A) : (term49 A b _92874) = (term50 A b _92874).
Proof. exact (MK_COMB (@lem6974740 A b) (@lem6974741 A _92874)). Qed.
Lemma lem6974743 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6974744 {A : Type'} (b : nat) (_92874 : A) : (term52 A b _92874) = (term53 A b _92874).
Proof. exact (MK_COMB (@lem6974743) (@lem6974742 A b _92874)). Qed.
Lemma lem6974745 {A : Type'} (_92874 : A) (b : nat) : (term50 A b _92874) = b.
Proof. exact (eq_refl (term50 A b _92874)). Qed.
Lemma lem6974746 {A : Type'} (_92874 : A) (b : nat) : ((term49 A b _92874) = (term50 A b _92874)) = ((term50 A b _92874) = b).
Proof. exact (MK_COMB (@lem6974744 A b _92874) (@lem6974745 A _92874 b)). Qed.
Lemma lem6974747 {A : Type'} (_92874 : A) (b : nat) : (term50 A b _92874) = b.
Proof. exact (EQ_MP (@lem6974746 A _92874 b) (@lem6974738 A b _92874)). Qed.
Lemma lem6974748 {A : Type'} (f : A -> nat) (_92874 : A) : (term54 A f _92874) = (term54 A f _92874).
Proof. exact (eq_refl (term54 A f _92874)). Qed.
Lemma lem6974749 {A : Type'} (f : A -> nat) (_92874 : A) (b : nat) : (term55 A f b _92874) = (term56 A f _92874 b).
Proof. exact (MK_COMB (@lem6974748 A f _92874) (@lem6974747 A _92874 b)). Qed.
Lemma lem6974750 {A : Type'} (_92874 : A) (s : A -> Prop) : (term57 A _92874 s) = (term57 A _92874 s).
Proof. exact (eq_refl (term57 A _92874 s)). Qed.
Lemma lem6974751 {A : Type'} (s : A -> Prop) (f : A -> nat) (_92874 : A) (b : nat) : (term58 A s f b _92874) = (term45 A s f _92874 b).
Proof. exact (MK_COMB (@lem6974750 A _92874 s) (@lem6974749 A f _92874 b)). Qed.
Lemma lem6974753 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term37 A s f b) : (term45 A s f x b) = True.
Proof. exact (EQ_MP (@lem6974689 A s f x b) (@lem6974688 A x s f b h1)). Qed.
Lemma lem6974754 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term37 A s f b) : (term45 A s f x b) = True.
Proof. exact (@lem6974753 A x s f b h1). Qed.
Lemma lem6974755 {A : Type'} (_92874 : A) (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term37 A s f b) : (term45 A s f _92874 b) = True.
Proof. exact (@lem6974754 A _92874 s f b h1). Qed.
Lemma lem6974756 {A : Type'} (_92874 : A) (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term37 A s f b) : (term58 A s f b _92874) = True.
Proof. exact (TRANS (@lem6974751 A s f _92874 b) (@lem6974755 A _92874 s f b h1)). Qed.
Lemma lem6974759 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term37 A s f b) : (term59 A s f b) = (term60 A).
Proof. exact (fun_ext (fun _92874 : A => @lem6974756 A _92874 s f b h1)). Qed.
Lemma lem6974760 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6974761 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term37 A s f b) : (term61 A s f b) = (term62 A).
Proof. exact (MK_COMB (@lem6974760 A) (@lem6974759 A s f b h1)). Qed.
Lemma lem6974763 {A : Type'} (t : Prop) : (term63 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6974764 {A : Type'} (t : Prop) : (term63 A t) = t.
Proof. exact (@lem6974763 A t). Qed.
Lemma lem6974765 {A : Type'} : (term62 A) = True.
Proof. exact (@lem6974764 A True). Qed.
Lemma lem6974766 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term37 A s f b) : (term61 A s f b) = True.
Proof. exact (TRANS (@lem6974761 A s f b h1) (@lem6974765 A)). Qed.
Lemma lem6974767 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6974768 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term37 A s f b) : (term64 A s f b) = (and True).
Proof. exact (MK_COMB (@lem6974767) (@lem6974766 A s f b h1)). Qed.
Lemma lem6974805 {A B : Type'} (f : A -> B) (y : A) : (term47 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem6974806 {A : Type'} (f : A -> nat) (y : A) : (term48 A f y) = (f y).
Proof. exact (@lem6974805 A nat f y). Qed.
Lemma lem6974807 {A : Type'} (b : nat) (_92875 : A) : (term49 A b _92875) = (term50 A b _92875).
Proof. exact (@lem6974806 A (term43 A b) _92875). Qed.
Lemma lem6974808 {A : Type'} (x : A) (b : nat) : (term50 A b x) = b.
Proof. exact (eq_refl (term50 A b x)). Qed.
Lemma lem6974809 {A : Type'} (b : nat) : (term51 A b) = (term43 A b).
Proof. exact (fun_ext (fun x : A => @lem6974808 A x b)). Qed.
Lemma lem6974810 {A : Type'} (_92875 : A) : _92875 = _92875.
Proof. exact (eq_refl _92875). Qed.
Lemma lem6974811 {A : Type'} (b : nat) (_92875 : A) : (term49 A b _92875) = (term50 A b _92875).
Proof. exact (MK_COMB (@lem6974809 A b) (@lem6974810 A _92875)). Qed.
Lemma lem6974812 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6974813 {A : Type'} (b : nat) (_92875 : A) : (term52 A b _92875) = (term53 A b _92875).
Proof. exact (MK_COMB (@lem6974812) (@lem6974811 A b _92875)). Qed.
Lemma lem6974814 {A : Type'} (_92875 : A) (b : nat) : (term50 A b _92875) = b.
Proof. exact (eq_refl (term50 A b _92875)). Qed.
Lemma lem6974815 {A : Type'} (_92875 : A) (b : nat) : ((term49 A b _92875) = (term50 A b _92875)) = ((term50 A b _92875) = b).
Proof. exact (MK_COMB (@lem6974813 A b _92875) (@lem6974814 A _92875 b)). Qed.
Lemma lem6974816 {A : Type'} (_92875 : A) (b : nat) : (term50 A b _92875) = b.
Proof. exact (EQ_MP (@lem6974815 A _92875 b) (@lem6974807 A b _92875)). Qed.
Lemma lem6974817 {A : Type'} (f : A -> nat) (_92875 : A) : (term65 A f _92875) = (term65 A f _92875).
Proof. exact (eq_refl (term65 A f _92875)). Qed.
Lemma lem6974818 {A : Type'} (f : A -> nat) (_92875 : A) (b : nat) : (term66 A f b _92875) = (term39 A f _92875 b).
Proof. exact (MK_COMB (@lem6974817 A f _92875) (@lem6974816 A _92875 b)). Qed.
Lemma lem6974819 {A : Type'} (_92875 : A) (s : A -> Prop) : (term67 A _92875 s) = (term67 A _92875 s).
Proof. exact (eq_refl (term67 A _92875 s)). Qed.
Lemma lem6974820 {A : Type'} (s : A -> Prop) (f : A -> nat) (_92875 : A) (b : nat) : (term68 A s f b _92875) = (term38 A s f _92875 b).
Proof. exact (MK_COMB (@lem6974819 A _92875 s) (@lem6974818 A f _92875 b)). Qed.
Lemma lem6974825 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term69 A s f b) = (term70 A s f b).
Proof. exact (fun_ext (fun _92875 : A => @lem6974820 A s f _92875 b)). Qed.
Lemma lem6974826 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6974827 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term71 A s f b) = (term36 A s f b).
Proof. exact (MK_COMB (@lem6974826 A) (@lem6974825 A s f b)). Qed.
Lemma lem6974832 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term37 A s f b) : (term72 A s f b) = (term73 A s f b).
Proof. exact (MK_COMB (@lem6974768 A s f b h1) (@lem6974827 A s f b)). Qed.
Lemma lem6974834 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6974835 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term73 A s f b) = (term36 A s f b).
Proof. exact (@lem6974834 (term36 A s f b)). Qed.
Lemma lem6974855 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term37 A s f b) : (term72 A s f b) = (term36 A s f b).
Proof. exact (TRANS (@lem6974832 A s f b h1) (@lem6974835 A s f b)). Qed.
Lemma lem6974856 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term37 A s f b) (h2 : @FINITE A s) : (term74 A s f b) = (term73 A s f b).
Proof. exact (MK_COMB (@lem6974700 A s h2) (@lem6974855 A s f b h1)). Qed.
Lemma lem6974858 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6974859 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term73 A s f b) = (term36 A s f b).
Proof. exact (@lem6974858 (term36 A s f b)). Qed.
Lemma lem6974879 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term37 A s f b) (h2 : @FINITE A s) : (term74 A s f b) = (term36 A s f b).
Proof. exact (TRANS (@lem6974856 A f b s h1 h2) (@lem6974859 A s f b)). Qed.
Lemma lem6974880 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term37 A s f b) (h2 : @FINITE A s) : (term36 A s f b) = (term74 A s f b).
Proof. exact (SYM (@lem6974879 A f b s h1 h2)). Qed.
Lemma lem6974882 (p : Prop) : p = (term75 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6974883 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term36 A s f b) = (term76 A s f b).
Proof. exact (@lem6974882 (term36 A s f b)). Qed.
Lemma lem6974884 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term76 A s f b) = (term36 A s f b).
Proof. exact (SYM (@lem6974883 A s f b)). Qed.
Lemma lem6974885 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term77 A s f b) : term77 A s f b.
Proof. exact (h1). Qed.
Lemma lem6974888 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term78 A x s f b) : term78 A x s f b.
Proof. exact (h1). Qed.
Lemma lem6974889 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : term79 A x s f b.
Proof. exact (fun h0 : term78 A x s f b => @lem6974888 A x s f b h0). Qed.
Lemma lem6974890 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term79 A x s f b) : term79 A x s f b.
Proof. exact (h1). Qed.
Lemma lem6974891 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term78 A x s f b) : term78 A x s f b.
Proof. exact (h1). Qed.
Lemma lem6974892 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term78 A x s f b) (h2 : term79 A x s f b) : term78 A x s f b.
Proof. exact (@lem6974890 A x s f b h2 (@lem6974891 A x s f b h1)). Qed.
Lemma lem6974893 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term78 A x s f b) : term80 A x s f b.
Proof. exact (fun h0 : term79 A x s f b => @lem6974892 A x s f b h1 h0). Qed.
Lemma lem6974894 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term79 A x s f b) : term79 A x s f b.
Proof. exact (h1). Qed.
Lemma lem6974895 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term78 A x s f b) (h2 : term79 A x s f b) : term78 A x s f b.
Proof. exact (@lem6974893 A x s f b h1 (@lem6974894 A x s f b h2)). Qed.
Lemma lem6974896 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term79 A x s f b) : term79 A x s f b.
Proof. exact (fun h0 : term78 A x s f b => @lem6974895 A x s f b h0 h1). Qed.
Lemma lem6974897 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : term81 A x s f b.
Proof. exact (fun h0 : term79 A x s f b => @lem6974896 A x s f b h0). Qed.
Lemma lem6974900 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : term79 A x s f b.
Proof. exact (@lem6974897 A x s f b (@lem6974889 A x s f b)). Qed.
Lemma lem6974901 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : term79 A x s f b.
Proof. exact (@lem6974900 A x s f b). Qed.
Lemma lem6974933 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem6974934 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term76 A s f b) = (term82 A s f b).
Proof. exact (@lem6974933 (term77 A s f b)). Qed.
Lemma lem6974936 (t : Prop) : (term83 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem6974937 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term82 A s f b) = (term36 A s f b).
Proof. exact (@lem6974936 (term36 A s f b)). Qed.
Lemma lem6974986 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term76 A s f b) = (term36 A s f b).
Proof. exact (TRANS (@lem6974934 A s f b) (@lem6974937 A s f b)). Qed.
Lemma lem6974989 {A : Type'} (f : A -> nat) (x : A) (b : nat) : (term84 A f x b) = (term84 A f x b).
Proof. exact (eq_refl (term84 A f x b)). Qed.
Lemma lem6974990 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term85 A x s f b) = (term86 A x s f b).
Proof. exact (MK_COMB (@lem6974989 A f x b) (@lem6974986 A s f b)). Qed.
Lemma lem6974993 {A : Type'} (x : A) (s : A -> Prop) : (term57 A x s) = (term57 A x s).
Proof. exact (eq_refl (term57 A x s)). Qed.
Lemma lem6974994 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term87 A x s f b) = (term88 A x s f b).
Proof. exact (MK_COMB (@lem6974993 A x s) (@lem6974990 A x s f b)). Qed.
Lemma lem6974997 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term89 A s f b) = (term89 A s f b).
Proof. exact (eq_refl (term89 A s f b)). Qed.
Lemma lem6974998 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term90 A x s f b) = (term91 A x s f b).
Proof. exact (MK_COMB (@lem6974997 A s f b) (@lem6974994 A x s f b)). Qed.
Lemma lem6975001 {A : Type'} (s : A -> Prop) : (term92 A s) = (term92 A s).
Proof. exact (eq_refl (term92 A s)). Qed.
Lemma lem6975002 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term78 A x s f b) = (term93 A x s f b).
Proof. exact (MK_COMB (@lem6975001 A s) (@lem6974998 A x s f b)). Qed.
Lemma lem6975005 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term94 A s f b) = (term95 A s f b).
Proof. exact (fun_ext (fun x : A => @lem6975002 A x s f b)). Qed.
Lemma lem6975006 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6975007 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term96 A s f b) = (term97 A s f b).
Proof. exact (MK_COMB (@lem6975006 A) (@lem6975005 A s f b)). Qed.
Lemma lem6975012 {A : Type'} (f : A -> nat) (b : nat) : (term98 A f b) = (term99 A f b).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6975007 A s f b)). Qed.
Lemma lem6975013 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6975014 {A : Type'} (f : A -> nat) (b : nat) : (term100 A f b) = (term101 A f b).
Proof. exact (MK_COMB (@lem6975013 A) (@lem6975012 A f b)). Qed.
Lemma lem6975019 {A : Type'} (b : nat) : (term102 A b) = (term103 A b).
Proof. exact (fun_ext (fun f : A -> nat => @lem6975014 A f b)). Qed.
Lemma lem6975020 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6975021 {A : Type'} (b : nat) : (term104 A b) = (term105 A b).
Proof. exact (MK_COMB (@lem6975020 A) (@lem6975019 A b)). Qed.
Lemma lem6975026 {A : Type'} : (term106 A) = (term107 A).
Proof. exact (fun_ext (fun b : nat => @lem6975021 A b)). Qed.
Lemma lem6975027 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6975036 {A : Type'} : (term108 A) = (term109 A).
Proof. exact (MK_COMB (@lem6975027) (@lem6975026 A)). Qed.
Lemma lem6975041 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (b : nat) : (term38 A s f x b) = (term38 A s f x b).
Proof. exact (eq_refl (term38 A s f x b)). Qed.
Lemma lem6975042 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term70 A s f b) = (term70 A s f b).
Proof. exact (fun_ext (fun x : A => @lem6975041 A s f x b)). Qed.
Lemma lem6975043 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6975044 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term36 A s f b) = (term36 A s f b).
Proof. exact (MK_COMB (@lem6975043 A) (@lem6975042 A s f b)). Qed.
Lemma lem6975047 {A : Type'} (f : A -> nat) (x : A) (b : nat) : (term84 A f x b) = (term84 A f x b).
Proof. exact (eq_refl (term84 A f x b)). Qed.
Lemma lem6975048 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term86 A x s f b) = (term86 A x s f b).
Proof. exact (MK_COMB (@lem6975047 A f x b) (@lem6975044 A s f b)). Qed.
Lemma lem6975051 {A : Type'} (x : A) (s : A -> Prop) : (term57 A x s) = (term57 A x s).
Proof. exact (eq_refl (term57 A x s)). Qed.
Lemma lem6975052 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term88 A x s f b) = (term88 A x s f b).
Proof. exact (MK_COMB (@lem6975051 A x s) (@lem6975048 A x s f b)). Qed.
Lemma lem6975057 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (b : nat) : (term45 A s f x b) = (term45 A s f x b).
Proof. exact (eq_refl (term45 A s f x b)). Qed.
Lemma lem6975058 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term110 A s f b) = (term110 A s f b).
Proof. exact (fun_ext (fun x : A => @lem6975057 A s f x b)). Qed.
Lemma lem6975059 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6975060 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term37 A s f b) = (term37 A s f b).
Proof. exact (MK_COMB (@lem6975059 A) (@lem6975058 A s f b)). Qed.
Lemma lem6975061 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6975062 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term89 A s f b) = (term89 A s f b).
Proof. exact (MK_COMB (@lem6975061) (@lem6975060 A s f b)). Qed.
Lemma lem6975063 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term91 A x s f b) = (term91 A x s f b).
Proof. exact (MK_COMB (@lem6975062 A s f b) (@lem6975052 A x s f b)). Qed.
Lemma lem6975066 {A : Type'} (s : A -> Prop) : (term92 A s) = (term92 A s).
Proof. exact (eq_refl (term92 A s)). Qed.
Lemma lem6975067 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term93 A x s f b) = (term93 A x s f b).
Proof. exact (MK_COMB (@lem6975066 A s) (@lem6975063 A x s f b)). Qed.
Lemma lem6975068 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term95 A s f b) = (term95 A s f b).
Proof. exact (fun_ext (fun x : A => @lem6975067 A x s f b)). Qed.
Lemma lem6975069 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6975070 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term97 A s f b) = (term97 A s f b).
Proof. exact (MK_COMB (@lem6975069 A) (@lem6975068 A s f b)). Qed.
Lemma lem6975071 {A : Type'} (f : A -> nat) (b : nat) : (term99 A f b) = (term99 A f b).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6975070 A s f b)). Qed.
Lemma lem6975072 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6975073 {A : Type'} (f : A -> nat) (b : nat) : (term101 A f b) = (term101 A f b).
Proof. exact (MK_COMB (@lem6975072 A) (@lem6975071 A f b)). Qed.
Lemma lem6975074 {A : Type'} (b : nat) : (term103 A b) = (term103 A b).
Proof. exact (fun_ext (fun f : A -> nat => @lem6975073 A f b)). Qed.
Lemma lem6975075 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6975076 {A : Type'} (b : nat) : (term105 A b) = (term105 A b).
Proof. exact (MK_COMB (@lem6975075 A) (@lem6975074 A b)). Qed.
Lemma lem6975077 {A : Type'} : (term107 A) = (term107 A).
Proof. exact (fun_ext (fun b : nat => @lem6975076 A b)). Qed.
Lemma lem6975078 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6975079 {A : Type'} : (term109 A) = (term109 A).
Proof. exact (MK_COMB (@lem6975078) (@lem6975077 A)). Qed.
Lemma lem6975130 {A : Type'} : (term108 A) = (term109 A).
Proof. exact (TRANS (@lem6975036 A) (@lem6975079 A)). Qed.
Lemma lem6975131 {A : Type'} : (term109 A) = (term108 A).
Proof. exact (SYM (@lem6975130 A)). Qed.
Lemma lem6975137 (p : Prop) : p = (term75 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6975138 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term36 A s f b) = (term76 A s f b).
Proof. exact (@lem6975137 (term36 A s f b)). Qed.
Lemma lem6975139 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term76 A s f b) = (term36 A s f b).
Proof. exact (SYM (@lem6975138 A s f b)). Qed.
Lemma lem6975140 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term77 A s f b) : term77 A s f b.
Proof. exact (h1). Qed.
Lemma lem6975215 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem6975221 {A : Type'} (f : A -> nat) (x : A) (b : nat) (h1 : term39 A f x b) : term39 A f x b.
Proof. exact (h1). Qed.
Lemma lem6975228 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (b : nat) : (term111 A s f x b) = (term112 A s f x b).
Proof. exact (@lem17045 (@IN A x s) (term39 A f x b)). Qed.
Lemma lem6975229 {A : Type'} (P : A -> Prop) : (term113 A P) = (term114 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem6975230 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term77 A s f b) = (term115 A s f b).
Proof. exact (@lem6975229 A (term70 A s f b)). Qed.
Lemma lem6975231 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (b : nat) : (term116 A s f b x) = (term38 A s f x b).
Proof. exact (eq_refl (term116 A s f b x)). Qed.
Lemma lem6975232 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6975233 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (b : nat) : (term117 A s f b x) = (term111 A s f x b).
Proof. exact (MK_COMB (@lem6975232) (@lem6975231 A s f x b)). Qed.
Lemma lem6975234 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (b : nat) : (term117 A s f b x) = (term112 A s f x b).
Proof. exact (TRANS (@lem6975233 A s f x b) (@lem6975228 A s f x b)). Qed.
Lemma lem6975235 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term118 A s f b) = (term119 A s f b).
Proof. exact (fun_ext (fun x : A => @lem6975234 A s f x b)). Qed.
Lemma lem6975236 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6975237 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term115 A s f b) = (term120 A s f b).
Proof. exact (MK_COMB (@lem6975236 A) (@lem6975235 A s f b)). Qed.
Lemma lem6975290 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term77 A s f b) = (term120 A s f b).
Proof. exact (TRANS (@lem6975230 A s f b) (@lem6975237 A s f b)). Qed.
Lemma lem6975291 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term77 A s f b) : term120 A s f b.
Proof. exact (EQ_MP (@lem6975290 A s f b) (@lem6975140 A s f b h1)). Qed.
Lemma lem6975322 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem6975330 {A : Type'} (f : A -> nat) (x : A) (b : nat) (h1 : term39 A f x b) : term39 A f x b.
Proof. exact (h1). Qed.
Lemma lem6975349 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (b : nat) : (term112 A s f x b) = (term112 A s f x b).
Proof. exact (eq_refl (term112 A s f x b)). Qed.
Lemma lem6975350 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term119 A s f b) = (term119 A s f b).
Proof. exact (fun_ext (fun x : A => @lem6975349 A s f x b)). Qed.
Lemma lem6975351 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6975352 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term120 A s f b) = (term120 A s f b).
Proof. exact (MK_COMB (@lem6975351 A) (@lem6975350 A s f b)). Qed.
Lemma lem6975353 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term77 A s f b) : term120 A s f b.
Proof. exact (EQ_MP (@lem6975352 A s f b) (@lem6975291 A s f b h1)). Qed.
Lemma lem6975374 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem6975378 {A : Type'} (f : A -> nat) (x : A) (b : nat) (h1 : term39 A f x b) : term39 A f x b.
Proof. exact (h1). Qed.
Lemma lem6975386 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (b : nat) : (term112 A s f x b) = (term112 A s f x b).
Proof. exact (eq_refl (term112 A s f x b)). Qed.
Lemma lem6975387 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term119 A s f b) = (term119 A s f b).
Proof. exact (fun_ext (fun x : A => @lem6975386 A s f x b)). Qed.
Lemma lem6975388 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6975390 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term120 A s f b) = (term120 A s f b).
Proof. exact (MK_COMB (@lem6975388 A) (@lem6975387 A s f b)). Qed.
Lemma lem6975391 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term77 A s f b) : term120 A s f b.
Proof. exact (EQ_MP (@lem6975390 A s f b) (@lem6975353 A s f b h1)). Qed.
Lemma lem6975395 {A : Type'} (_92879 : A) (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term77 A s f b) : term121 A s f b _92879.
Proof. exact (@lem6975391 A s f b h1 _92879). Qed.
Lemma lem6975396 {A : Type'} (s : A -> Prop) (f : A -> nat) (_92879 : A) (b : nat) : (term121 A s f b _92879) = (term112 A s f _92879 b).
Proof. exact (eq_refl (term121 A s f b _92879)). Qed.
Lemma lem6975407 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem6975409 {A : Type'} (f : A -> nat) (x : A) (b : nat) (h1 : term39 A f x b) : term39 A f x b.
Proof. exact (h1). Qed.
Lemma lem6975415 {A : Type'} (_92879 : A) (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term77 A s f b) : term112 A s f _92879 b.
Proof. exact (EQ_MP (@lem6975396 A s f _92879 b) (@lem6975395 A _92879 s f b h1)). Qed.
Lemma lem6975417 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem6975418 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : term122 A x s.
Proof. exact (fun h0 : term123 A x s => @lem6975417 A x s h1). Qed.
Lemma lem6975420 (p : Prop) : (term124 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6975421 {A : Type'} (x : A) (s : A -> Prop) : (term122 A x s) = (@IN A x s).
Proof. exact (@lem6975420 (@IN A x s)). Qed.
Lemma lem6975422 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (EQ_MP (@lem6975421 A x s) (@lem6975418 A x s h1)). Qed.
Lemma lem6975424 {A : Type'} (f : A -> nat) (x : A) (b : nat) (h1 : term39 A f x b) : term39 A f x b.
Proof. exact (h1). Qed.
Lemma lem6975425 {A : Type'} (f : A -> nat) (x : A) (b : nat) (h1 : term39 A f x b) : term125 A f x b.
Proof. exact (fun h0 : term126 A f x b => @lem6975424 A f x b h1). Qed.
Lemma lem6975427 (p : Prop) : (term124 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6975428 {A : Type'} (f : A -> nat) (x : A) (b : nat) : (term125 A f x b) = (term39 A f x b).
Proof. exact (@lem6975427 (term39 A f x b)). Qed.
Lemma lem6975429 {A : Type'} (f : A -> nat) (x : A) (b : nat) (h1 : term39 A f x b) : term39 A f x b.
Proof. exact (EQ_MP (@lem6975428 A f x b) (@lem6975425 A f x b h1)). Qed.
Lemma lem6975431 (a : Prop) (b : Prop) : (term127 a b) = (term128 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem6975432 {A : Type'} (s : A -> Prop) (f : A -> nat) (_92879 : A) (b : nat) : (term112 A s f _92879 b) = (term111 A s f _92879 b).
Proof. exact (@lem6975431 (@IN A _92879 s) (term39 A f _92879 b)). Qed.
Lemma lem6975434 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6975435 {A : Type'} (s : A -> Prop) (f : A -> nat) (_92879 : A) (b : nat) : (term111 A s f _92879 b) = (term129 A s f _92879 b).
Proof. exact (@lem6975434 (term38 A s f _92879 b)). Qed.
Lemma lem6975436 {A : Type'} (s : A -> Prop) (f : A -> nat) (_92879 : A) (b : nat) : (term112 A s f _92879 b) = (term129 A s f _92879 b).
Proof. exact (TRANS (@lem6975432 A s f _92879 b) (@lem6975435 A s f _92879 b)). Qed.
Lemma lem6975438 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term39 A f x b) (h2 : @IN A x s) : term38 A s f x b.
Proof. exact (conj (@lem6975422 A x s h2) (@lem6975429 A f x b h1)). Qed.
Lemma lem6975440 {A : Type'} (_92879 : A) (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term77 A s f b) : term129 A s f _92879 b.
Proof. exact (EQ_MP (@lem6975436 A s f _92879 b) (@lem6975415 A _92879 s f b h1)). Qed.
Lemma lem6975441 {A : Type'} (_92879 : A) (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term77 A s f b) : term129 A s f _92879 b.
Proof. exact (@lem6975440 A _92879 s f b h1). Qed.
Lemma lem6975442 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term77 A s f b) : term129 A s f x b.
Proof. exact (@lem6975441 A x s f b h1). Qed.
Lemma lem6975445 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term77 A s f b) (h2 : term39 A f x b) (h3 : @IN A x s) : False.
Proof. exact (@lem6975442 A x s f b h1 (@lem6975438 A f b x s h2 h3)). Qed.
Lemma lem6975446 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term77 A s f b) (h2 : term39 A f x b) (h3 : @IN A x s) : term130.
Proof. exact (fun h0 : ~ False => @lem6975445 A f b x s h1 h2 h3). Qed.
Lemma lem6975448 (p : Prop) : (term124 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6975449 : term130 = False.
Proof. exact (@lem6975448 False). Qed.
Lemma lem6975450 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term77 A s f b) (h2 : term39 A f x b) (h3 : @IN A x s) : False.
Proof. exact (EQ_MP (@lem6975449) (@lem6975446 A f b x s h1 h2 h3)). Qed.
Lemma lem6975451 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term77 A s f b) (h2 : term39 A f x b) (h3 : @IN A x s) : (term39 A f x b) = False.
Proof. exact (prop_ext (fun h4 : term39 A f x b => @lem6975450 A f b x s h1 h2 h3) (fun h4 : False => @lem6975409 A f x b h2)). Qed.
Lemma lem6975452 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term77 A s f b) (h2 : term39 A f x b) (h3 : @IN A x s) : False.
Proof. exact (EQ_MP (@lem6975451 A f b x s h1 h2 h3) (@lem6975409 A f x b h2)). Qed.
Lemma lem6975453 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term77 A s f b) (h2 : term39 A f x b) (h3 : @IN A x s) : (@IN A x s) = False.
Proof. exact (prop_ext (fun h4 : @IN A x s => @lem6975452 A f b x s h1 h2 h3) (fun h4 : False => @lem6975407 A x s h3)). Qed.
Lemma lem6975454 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term77 A s f b) (h2 : term39 A f x b) (h3 : @IN A x s) : False.
Proof. exact (EQ_MP (@lem6975453 A f b x s h1 h2 h3) (@lem6975407 A x s h3)). Qed.
Lemma lem6975455 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term77 A s f b) (h2 : term39 A f x b) (h3 : @IN A x s) : (term39 A f x b) = False.
Proof. exact (prop_ext (fun h4 : term39 A f x b => @lem6975454 A f b x s h1 h2 h3) (fun h4 : False => @lem6975378 A f x b h2)). Qed.
Lemma lem6975456 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term77 A s f b) (h2 : term39 A f x b) (h3 : @IN A x s) : False.
Proof. exact (EQ_MP (@lem6975455 A f b x s h1 h2 h3) (@lem6975378 A f x b h2)). Qed.
Lemma lem6975457 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term77 A s f b) (h2 : term39 A f x b) (h3 : @IN A x s) : (@IN A x s) = False.
Proof. exact (prop_ext (fun h4 : @IN A x s => @lem6975456 A f b x s h1 h2 h3) (fun h4 : False => @lem6975374 A x s h3)). Qed.
Lemma lem6975458 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term77 A s f b) (h2 : term39 A f x b) (h3 : @IN A x s) : False.
Proof. exact (EQ_MP (@lem6975457 A f b x s h1 h2 h3) (@lem6975374 A x s h3)). Qed.
Lemma lem6975459 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term77 A s f b) (h2 : term39 A f x b) (h3 : @IN A x s) : (term39 A f x b) = False.
Proof. exact (prop_ext (fun h4 : term39 A f x b => @lem6975458 A f b x s h1 h2 h3) (fun h4 : False => @lem6975378 A f x b h2)). Qed.
Lemma lem6975460 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term77 A s f b) (h2 : term39 A f x b) (h3 : @IN A x s) : False.
Proof. exact (EQ_MP (@lem6975459 A f b x s h1 h2 h3) (@lem6975378 A f x b h2)). Qed.
Lemma lem6975461 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term77 A s f b) (h2 : term39 A f x b) (h3 : @IN A x s) : (@IN A x s) = False.
Proof. exact (prop_ext (fun h4 : @IN A x s => @lem6975460 A f b x s h1 h2 h3) (fun h4 : False => @lem6975374 A x s h3)). Qed.
Lemma lem6975462 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term77 A s f b) (h2 : term39 A f x b) (h3 : @IN A x s) : False.
Proof. exact (EQ_MP (@lem6975461 A f b x s h1 h2 h3) (@lem6975374 A x s h3)). Qed.
Lemma lem6975463 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term77 A s f b) (h2 : term39 A f x b) (h3 : @IN A x s) : (term39 A f x b) = False.
Proof. exact (prop_ext (fun h4 : term39 A f x b => @lem6975462 A f b x s h1 h2 h3) (fun h4 : False => @lem6975330 A f x b h2)). Qed.
Lemma lem6975464 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term77 A s f b) (h2 : term39 A f x b) (h3 : @IN A x s) : False.
Proof. exact (EQ_MP (@lem6975463 A f b x s h1 h2 h3) (@lem6975330 A f x b h2)). Qed.
Lemma lem6975465 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term77 A s f b) (h2 : term39 A f x b) (h3 : @IN A x s) : (@IN A x s) = False.
Proof. exact (prop_ext (fun h4 : @IN A x s => @lem6975464 A f b x s h1 h2 h3) (fun h4 : False => @lem6975322 A x s h3)). Qed.
Lemma lem6975466 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term77 A s f b) (h2 : term39 A f x b) (h3 : @IN A x s) : False.
Proof. exact (EQ_MP (@lem6975465 A f b x s h1 h2 h3) (@lem6975322 A x s h3)). Qed.
Lemma lem6975467 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term77 A s f b) (h2 : term39 A f x b) (h3 : @IN A x s) : (term39 A f x b) = False.
Proof. exact (prop_ext (fun h4 : term39 A f x b => @lem6975466 A f b x s h1 h2 h3) (fun h4 : False => @lem6975221 A f x b h2)). Qed.
Lemma lem6975468 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term77 A s f b) (h2 : term39 A f x b) (h3 : @IN A x s) : False.
Proof. exact (EQ_MP (@lem6975467 A f b x s h1 h2 h3) (@lem6975221 A f x b h2)). Qed.
Lemma lem6975469 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term77 A s f b) (h2 : term39 A f x b) (h3 : @IN A x s) : (@IN A x s) = False.
Proof. exact (prop_ext (fun h4 : @IN A x s => @lem6975468 A f b x s h1 h2 h3) (fun h4 : False => @lem6975215 A x s h3)). Qed.
Lemma lem6975470 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term77 A s f b) (h2 : term39 A f x b) (h3 : @IN A x s) : False.
Proof. exact (EQ_MP (@lem6975469 A f b x s h1 h2 h3) (@lem6975215 A x s h3)). Qed.
Lemma lem6975471 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term77 A s f b) (h2 : term39 A f x b) (h3 : @IN A x s) : (term77 A s f b) = False.
Proof. exact (prop_ext (fun h4 : term77 A s f b => @lem6975470 A f b x s h1 h2 h3) (fun h4 : False => @lem6975140 A s f b h1)). Qed.
Lemma lem6975472 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term77 A s f b) (h2 : term39 A f x b) (h3 : @IN A x s) : False.
Proof. exact (EQ_MP (@lem6975471 A f b x s h1 h2 h3) (@lem6975140 A s f b h1)). Qed.
Lemma lem6975473 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term39 A f x b) (h2 : @IN A x s) : term76 A s f b.
Proof. exact (fun h0 : term77 A s f b => @lem6975472 A f b x s h0 h1 h2). Qed.
Lemma lem6975474 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term39 A f x b) (h2 : @IN A x s) : term36 A s f b.
Proof. exact (EQ_MP (@lem6975139 A s f b) (@lem6975473 A f b x s h1 h2)). Qed.
Lemma lem6975475 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : @IN A x s) : term86 A x s f b.
Proof. exact (fun h0 : term39 A f x b => @lem6975474 A f b x s h0 h1). Qed.
Lemma lem6975476 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : term88 A x s f b.
Proof. exact (fun h0 : @IN A x s => @lem6975475 A f b x s h0). Qed.
Lemma lem6975477 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : term91 A x s f b.
Proof. exact (fun h0 : term37 A s f b => @lem6975476 A x s f b). Qed.
Lemma lem6975478 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : term93 A x s f b.
Proof. exact (fun h0 : @FINITE A s => @lem6975477 A x s f b). Qed.
Lemma lem6975483 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : term97 A s f b.
Proof. exact (fun x : A => @lem6975478 A x s f b). Qed.
Lemma lem6975488 {A : Type'} (f : A -> nat) (b : nat) : term101 A f b.
Proof. exact (fun s : A -> Prop => @lem6975483 A s f b). Qed.
Lemma lem6975493 {A : Type'} (b : nat) : term105 A b.
Proof. exact (fun f : A -> nat => @lem6975488 A f b). Qed.
Lemma lem6975498 {A : Type'} : term109 A.
Proof. exact (fun b : nat => @lem6975493 A b). Qed.
Lemma lem6975499 {A : Type'} : term108 A.
Proof. exact (EQ_MP (@lem6975131 A) (@lem6975498 A)). Qed.
Lemma lem6975500 {A : Type'} (b : nat) : term131 A b.
Proof. exact (@lem6975499 A b). Qed.
Lemma lem6975501 {A : Type'} (b : nat) : (term131 A b) = (term104 A b).
Proof. exact (eq_refl (term131 A b)). Qed.
Lemma lem6975502 {A : Type'} (b : nat) : term104 A b.
Proof. exact (EQ_MP (@lem6975501 A b) (@lem6975500 A b)). Qed.
Lemma lem6975503 {A : Type'} (b : nat) (f : A -> nat) : term132 A b f.
Proof. exact (@lem6975502 A b f). Qed.
Lemma lem6975504 {A : Type'} (f : A -> nat) (b : nat) : (term132 A b f) = (term100 A f b).
Proof. exact (eq_refl (term132 A b f)). Qed.
Lemma lem6975505 {A : Type'} (f : A -> nat) (b : nat) : term100 A f b.
Proof. exact (EQ_MP (@lem6975504 A f b) (@lem6975503 A b f)). Qed.
Lemma lem6975506 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) : term133 A f b s.
Proof. exact (@lem6975505 A f b s). Qed.
Lemma lem6975507 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term133 A f b s) = (term96 A s f b).
Proof. exact (eq_refl (term133 A f b s)). Qed.
Lemma lem6975508 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : term96 A s f b.
Proof. exact (EQ_MP (@lem6975507 A s f b) (@lem6975506 A f b s)). Qed.
Lemma lem6975509 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (x : A) : term134 A s f b x.
Proof. exact (@lem6975508 A s f b x). Qed.
Lemma lem6975510 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term134 A s f b x) = (term78 A x s f b).
Proof. exact (eq_refl (term134 A s f b x)). Qed.
Lemma lem6975511 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : term78 A x s f b.
Proof. exact (EQ_MP (@lem6975510 A x s f b) (@lem6975509 A s f b x)). Qed.
Lemma lem6975513 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : term78 A x s f b.
Proof. exact (@lem6974901 A x s f b (@lem6975511 A x s f b)). Qed.
Lemma lem6975514 {A : Type'} (x : A) (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : @FINITE A s) : term90 A x s f b.
Proof. exact (@lem6975513 A x s f b (@lem6974671 A s h1)). Qed.
Lemma lem6975515 {A : Type'} (x : A) (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term37 A s f b) (h2 : @FINITE A s) : term87 A x s f b.
Proof. exact (@lem6975514 A x f b s h2 (@lem6974673 A s f b h1)). Qed.
Lemma lem6975516 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term37 A s f b) (h2 : @FINITE A s) (h3 : @IN A x s) : term85 A x s f b.
Proof. exact (@lem6975515 A x f b s h1 h2 (@lem6974676 A x s h3)). Qed.
Lemma lem6975517 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term37 A s f b) (h2 : @FINITE A s) (h3 : term39 A f x b) (h4 : @IN A x s) : term76 A s f b.
Proof. exact (@lem6975516 A f b x s h1 h2 h4 (@lem6974675 A f x b h3)). Qed.
Lemma lem6975518 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term37 A s f b) (h2 : @FINITE A s) (h3 : term77 A s f b) (h4 : term39 A f x b) (h5 : @IN A x s) : False.
Proof. exact (@lem6975517 A f b x s h1 h2 h4 h5 (@lem6974885 A s f b h3)). Qed.
Lemma lem6975519 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term37 A s f b) (h2 : @FINITE A s) (h3 : term77 A s f b) (h4 : term39 A f x b) (h5 : @IN A x s) : (term77 A s f b) = False.
Proof. exact (prop_ext (fun h6 : term77 A s f b => @lem6975518 A f b x s h1 h2 h3 h4 h5) (fun h6 : False => @lem6974885 A s f b h3)). Qed.
Lemma lem6975520 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term37 A s f b) (h2 : @FINITE A s) (h3 : term77 A s f b) (h4 : term39 A f x b) (h5 : @IN A x s) : False.
Proof. exact (EQ_MP (@lem6975519 A f b x s h1 h2 h3 h4 h5) (@lem6974885 A s f b h3)). Qed.
Lemma lem6975521 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term37 A s f b) (h2 : @FINITE A s) (h3 : term39 A f x b) (h4 : @IN A x s) : term76 A s f b.
Proof. exact (fun h0 : term77 A s f b => @lem6975520 A f b x s h1 h2 h0 h3 h4). Qed.
Lemma lem6975522 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term37 A s f b) (h2 : @FINITE A s) (h3 : term39 A f x b) (h4 : @IN A x s) : term36 A s f b.
Proof. exact (EQ_MP (@lem6974884 A s f b) (@lem6975521 A f b x s h1 h2 h3 h4)). Qed.
Lemma lem6975523 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term37 A s f b) (h2 : @FINITE A s) (h3 : term39 A f x b) (h4 : @IN A x s) : term74 A s f b.
Proof. exact (EQ_MP (@lem6974880 A f b s h1 h2) (@lem6975522 A f b x s h1 h2 h3 h4)). Qed.
Lemma lem6975524 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term37 A s f b) (h2 : @FINITE A s) (h3 : term39 A f x b) (h4 : @IN A x s) : term135 A f s b.
Proof. exact (@lem6974683 A f s b (@lem6975523 A f b x s h1 h2 h3 h4)). Qed.
Lemma lem6975525 (n : nat) : term136 n.
Proof. exact (@lem91603 n). Qed.
Lemma lem6975526 (n : nat) : (term136 n) = (Peano.le n n).
Proof. exact (eq_refl (term136 n)). Qed.
Lemma lem6975527 (n : nat) : Peano.le n n.
Proof. exact (EQ_MP (@lem6975526 n) (@lem6975525 n)). Qed.
Lemma lem6975528 (n : nat) : (Peano.le n n) = ((Peano.le n n) = True).
Proof. exact (@lem7 (Peano.le n n)). Qed.
Lemma lem6975530 {_127196 : Type'} (c : nat) : term137 _127196 c.
Proof. exact (@lem6940531 _127196 c). Qed.
Lemma lem6975531 {_127196 : Type'} (c : nat) : (term137 _127196 c) = (term138 _127196 c).
Proof. exact (eq_refl (term137 _127196 c)). Qed.
Lemma lem6975532 {_127196 : Type'} (c : nat) : term138 _127196 c.
Proof. exact (EQ_MP (@lem6975531 _127196 c) (@lem6975530 _127196 c)). Qed.
Lemma lem6975533 {_127196 : Type'} (c : nat) (s : _127196 -> Prop) : term139 _127196 c s.
Proof. exact (@lem6975532 _127196 c s). Qed.
Lemma lem6975534 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : (term139 _127196 c s) = (term140 _127196 s c).
Proof. exact (eq_refl (term139 _127196 c s)). Qed.
Lemma lem6975535 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : term140 _127196 s c.
Proof. exact (EQ_MP (@lem6975534 _127196 s c) (@lem6975533 _127196 c s)). Qed.
Lemma lem6975536 {_127196 : Type'} (s : _127196 -> Prop) (h1 : @FINITE _127196 s) : @FINITE _127196 s.
Proof. exact (h1). Qed.
Lemma lem6975537 {_127196 : Type'} (c : nat) (s : _127196 -> Prop) (h1 : @FINITE _127196 s) : (term141 _127196 s c) = (term41 _127196 s c).
Proof. exact (@lem6975535 _127196 s c (@lem6975536 _127196 s h1)). Qed.
Lemma lem6975543 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem6975564 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : term140 _127196 s c.
Proof. exact (fun h0 : @FINITE _127196 s => @lem6975537 _127196 c s h0). Qed.
Lemma lem6975565 {A : Type'} (s : A -> Prop) (c : nat) : term140 A s c.
Proof. exact (@lem6975564 A s c). Qed.
Lemma lem6975566 {A : Type'} (s : A -> Prop) (b : nat) : term140 A s b.
Proof. exact (@lem6975565 A s b). Qed.
Lemma lem6975568 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem6975543 A s) (@lem6974671 A s h1)). Qed.
Lemma lem6975569 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : True = (@FINITE A s).
Proof. exact (SYM (@lem6975568 A s h1)). Qed.
Lemma lem6975570 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (EQ_MP (@lem6975569 A s h1) (@lem0)). Qed.
Lemma lem6975571 {A : Type'} (b : nat) (s : A -> Prop) (h1 : @FINITE A s) : (term141 A s b) = (term41 A s b).
Proof. exact (@lem6975566 A s b (@lem6975570 A s h1)). Qed.
Lemma lem6975572 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem6975573 {A : Type'} (b : nat) (s : A -> Prop) (h1 : @FINITE A s) : (term142 A s b) = (term143 A s b).
Proof. exact (MK_COMB (@lem6975572) (@lem6975571 A b s h1)). Qed.
Lemma lem6975574 {A : Type'} (s : A -> Prop) (b : nat) : (term41 A s b) = (term41 A s b).
Proof. exact (eq_refl (term41 A s b)). Qed.
Lemma lem6975575 {A : Type'} (b : nat) (s : A -> Prop) (h1 : @FINITE A s) : (term144 A s b) = (term145 A s b).
Proof. exact (MK_COMB (@lem6975573 A b s h1) (@lem6975574 A s b)). Qed.
Lemma lem6975577 (n : nat) : (Peano.le n n) = True.
Proof. exact (EQ_MP (@lem6975528 n) (@lem6975527 n)). Qed.
Lemma lem6975578 {A : Type'} (s : A -> Prop) (b : nat) : (term145 A s b) = True.
Proof. exact (@lem6975577 (term41 A s b)). Qed.
Lemma lem6975579 {A : Type'} (b : nat) (s : A -> Prop) (h1 : @FINITE A s) : (term144 A s b) = True.
Proof. exact (TRANS (@lem6975575 A b s h1) (@lem6975578 A s b)). Qed.
Lemma lem6975580 {A : Type'} (b : nat) (s : A -> Prop) (h1 : @FINITE A s) : True = (term144 A s b).
Proof. exact (SYM (@lem6975579 A b s h1)). Qed.
Lemma lem6975581 {A : Type'} (b : nat) (s : A -> Prop) (h1 : @FINITE A s) : term144 A s b.
Proof. exact (EQ_MP (@lem6975580 A b s h1) (@lem0)). Qed.
Lemma lem6975582 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term37 A s f b) (h2 : @FINITE A s) (h3 : term39 A f x b) (h4 : @IN A x s) : term146 A f s b.
Proof. exact (conj (@lem6975524 A f b x s h1 h2 h3 h4) (@lem6975581 A b s h2)). Qed.
Lemma lem6975583 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term37 A s f b) (h2 : @FINITE A s) (h3 : term39 A f x b) (h4 : @IN A x s) : term147 A f s b.
Proof. exact (ex_intro (term148 A f s b) (term141 A s b) (@lem6975582 A f b x s h1 h2 h3 h4)). Qed.
Lemma lem6975584 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term37 A s f b) (h2 : @FINITE A s) (h3 : term39 A f x b) (h4 : @IN A x s) : term149 A f s b.
Proof. exact (@lem6974679 A f s b (@lem6975583 A f b x s h1 h2 h3 h4)). Qed.
Lemma lem6975585 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term34 A s f b) : term35 A s f b.
Proof. exact (proj2 (@lem6974669 A s f b h1)). Qed.
Lemma lem6975586 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term34 A s f b) : @FINITE A s.
Proof. exact (proj1 (@lem6974669 A s f b h1)). Qed.
Lemma lem6975587 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term35 A s f b) : term36 A s f b.
Proof. exact (proj2 (@lem6974670 A s f b h1)). Qed.
Lemma lem6975588 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term35 A s f b) : term37 A s f b.
Proof. exact (proj1 (@lem6974670 A s f b h1)). Qed.
Lemma lem6975589 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (b : nat) (h1 : term38 A s f x b) : term39 A f x b.
Proof. exact (proj2 (@lem6974674 A s f x b h1)). Qed.
Lemma lem6975590 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (b : nat) (h1 : term38 A s f x b) : @IN A x s.
Proof. exact (proj1 (@lem6974674 A s f x b h1)). Qed.
Lemma lem6975591 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term37 A s f b) (h2 : @FINITE A s) (h3 : term39 A f x b) (h4 : @IN A x s) : (term39 A f x b) = (term149 A f s b).
Proof. exact (prop_ext (fun h5 : term39 A f x b => @lem6975584 A f b x s h1 h2 h3 h4) (fun h5 : term149 A f s b => @lem6974675 A f x b h3)). Qed.
Lemma lem6975592 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term37 A s f b) (h2 : @FINITE A s) (h3 : term39 A f x b) (h4 : @IN A x s) : term149 A f s b.
Proof. exact (EQ_MP (@lem6975591 A f b x s h1 h2 h3 h4) (@lem6974675 A f x b h3)). Qed.
Lemma lem6975593 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term37 A s f b) (h2 : @FINITE A s) (h3 : term39 A f x b) (h4 : @IN A x s) : (@IN A x s) = (term149 A f s b).
Proof. exact (prop_ext (fun h5 : @IN A x s => @lem6975592 A f b x s h1 h2 h3 h4) (fun h5 : term149 A f s b => @lem6974676 A x s h4)). Qed.
Lemma lem6975594 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term37 A s f b) (h2 : @FINITE A s) (h3 : term39 A f x b) (h4 : @IN A x s) : term149 A f s b.
Proof. exact (EQ_MP (@lem6975593 A f b x s h1 h2 h3 h4) (@lem6974676 A x s h4)). Qed.
Lemma lem6975595 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term37 A s f b) (h2 : @FINITE A s) (h3 : term38 A s f x b) (h4 : @IN A x s) : (term39 A f x b) = (term149 A f s b).
Proof. exact (prop_ext (fun h5 : term39 A f x b => @lem6975594 A f b x s h1 h2 h5 h4) (fun h5 : term149 A f s b => @lem6975589 A s f x b h3)). Qed.
Lemma lem6975596 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term37 A s f b) (h2 : @FINITE A s) (h3 : term38 A s f x b) (h4 : @IN A x s) : term149 A f s b.
Proof. exact (EQ_MP (@lem6975595 A f b x s h1 h2 h3 h4) (@lem6975589 A s f x b h3)). Qed.
Lemma lem6975597 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (b : nat) (h1 : term37 A s f b) (h2 : @FINITE A s) (h3 : term38 A s f x b) : (@IN A x s) = (term149 A f s b).
Proof. exact (prop_ext (fun h4 : @IN A x s => @lem6975596 A f b x s h1 h2 h3 h4) (fun h4 : term149 A f s b => @lem6975590 A s f x b h3)). Qed.
Lemma lem6975598 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (b : nat) (h1 : term37 A s f b) (h2 : @FINITE A s) (h3 : term38 A s f x b) : term149 A f s b.
Proof. exact (EQ_MP (@lem6975597 A s f x b h1 h2 h3) (@lem6975590 A s f x b h3)). Qed.
Lemma lem6975599 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term37 A s f b) (h2 : term36 A s f b) (h3 : @FINITE A s) : term149 A f s b.
Proof. exact (ex_elim (@lem6974672 A s f b h2) (fun x : A => fun h0 : term70 A s f b x => @lem6975598 A s f x b h1 h3 h0)). Qed.
Lemma lem6975600 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term37 A s f b) (h2 : term36 A s f b) (h3 : @FINITE A s) : (term37 A s f b) = (term149 A f s b).
Proof. exact (prop_ext (fun h4 : term37 A s f b => @lem6975599 A f b s h1 h2 h3) (fun h4 : term149 A f s b => @lem6974673 A s f b h1)). Qed.
Lemma lem6975601 {A : Type'} (f : A -> nat) (b : nat) (s : A -> Prop) (h1 : term37 A s f b) (h2 : term36 A s f b) (h3 : @FINITE A s) : term149 A f s b.
Proof. exact (EQ_MP (@lem6975600 A f b s h1 h2 h3) (@lem6974673 A s f b h1)). Qed.
Lemma lem6975602 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term37 A s f b) (h2 : @FINITE A s) (h3 : term35 A s f b) : (term36 A s f b) = (term149 A f s b).
Proof. exact (prop_ext (fun h4 : term36 A s f b => @lem6975601 A f b s h1 h4 h2) (fun h4 : term149 A f s b => @lem6975587 A s f b h3)). Qed.
Lemma lem6975603 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term37 A s f b) (h2 : @FINITE A s) (h3 : term35 A s f b) : term149 A f s b.
Proof. exact (EQ_MP (@lem6975602 A s f b h1 h2 h3) (@lem6975587 A s f b h3)). Qed.
Lemma lem6975604 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : @FINITE A s) (h2 : term35 A s f b) : (term37 A s f b) = (term149 A f s b).
Proof. exact (prop_ext (fun h3 : term37 A s f b => @lem6975603 A s f b h3 h1 h2) (fun h3 : term149 A f s b => @lem6975588 A s f b h2)). Qed.
Lemma lem6975605 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : @FINITE A s) (h2 : term35 A s f b) : term149 A f s b.
Proof. exact (EQ_MP (@lem6975604 A s f b h1 h2) (@lem6975588 A s f b h2)). Qed.
Lemma lem6975606 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : @FINITE A s) (h2 : term35 A s f b) : (@FINITE A s) = (term149 A f s b).
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem6975605 A s f b h1 h2) (fun h3 : term149 A f s b => @lem6974671 A s h1)). Qed.
Lemma lem6975607 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : @FINITE A s) (h2 : term35 A s f b) : term149 A f s b.
Proof. exact (EQ_MP (@lem6975606 A s f b h1 h2) (@lem6974671 A s h1)). Qed.
Lemma lem6975608 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : @FINITE A s) (h2 : term34 A s f b) : (term35 A s f b) = (term149 A f s b).
Proof. exact (prop_ext (fun h3 : term35 A s f b => @lem6975607 A s f b h1 h3) (fun h3 : term149 A f s b => @lem6975585 A s f b h2)). Qed.
Lemma lem6975609 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : @FINITE A s) (h2 : term34 A s f b) : term149 A f s b.
Proof. exact (EQ_MP (@lem6975608 A s f b h1 h2) (@lem6975585 A s f b h2)). Qed.
Lemma lem6975610 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term34 A s f b) : (@FINITE A s) = (term149 A f s b).
Proof. exact (prop_ext (fun h2 : @FINITE A s => @lem6975609 A s f b h2 h1) (fun h2 : term149 A f s b => @lem6975586 A s f b h1)). Qed.
Lemma lem6975611 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term34 A s f b) : term149 A f s b.
Proof. exact (EQ_MP (@lem6975610 A s f b h1) (@lem6975586 A s f b h1)). Qed.
Lemma lem6975612 {A : Type'} (f : A -> nat) (s : A -> Prop) (b : nat) : term150 A f s b.
Proof. exact (fun h0 : term34 A s f b => @lem6975611 A s f b h0). Qed.
Lemma lem6975617 {A : Type'} (f : A -> nat) (s : A -> Prop) : term151 A f s.
Proof. exact (fun b : nat => @lem6975612 A f s b). Qed.
Lemma lem6975622 {A : Type'} (s : A -> Prop) : term152 A s.
Proof. exact (fun f : A -> nat => @lem6975617 A f s). Qed.
Lemma lem6975627 {A : Type'} : term153 A.
Proof. exact (fun s : A -> Prop => @lem6975622 A s). Qed.
