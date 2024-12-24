Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUP_INSERT_FINITE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_INSERT_spec.
Require Import FORALL_IN_INSERT_spec.
Require Import IN_INSERT_spec.
Require Import IN_SING_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_INSERT_EMPTY_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import SUP_FINITE_spec.
Require Import SUP_UNIQUE_FINITE_spec.
Require Import real_max_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1339240_spec.
Require Import thm1339577_spec.
Require Import thm1339697_spec.
Require Import thm13473_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1831_spec.
Require Import thm1832_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19018_spec.
Require Import thm19019_spec.
Require Import thm19490_spec.
Require Import thm196_spec.
Require Import thm197_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem5175619 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5175620 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5175621 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5175620 t1) (@lem5175619 t1)). Qed.
Lemma lem5175622 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5175621 t1 t2). Qed.
Lemma lem5175623 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5175624 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5175623 t1 t2) (@lem5175622 t1 t2)). Qed.
Lemma lem5175625 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5175624 t1 t2 t3). Qed.
Lemma lem5175626 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5175627 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5175626 t1 t2 t3) (@lem5175625 t1 t2 t3)). Qed.
Lemma lem5175628 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5175627 t1 t2 t3)). Qed.
Lemma lem5175629 (n : real) : term7 n.
Proof. exact (@lem1345564 n). Qed.
Lemma lem5175630 (n : real) : (term7 n) = (term8 n).
Proof. exact (eq_refl (term7 n)). Qed.
Lemma lem5175631 (n : real) : term8 n.
Proof. exact (EQ_MP (@lem5175630 n) (@lem5175629 n)). Qed.
Lemma lem5175632 (n : real) (m : real) : term9 n m.
Proof. exact (@lem5175631 n m). Qed.
Lemma lem5175633 (n : real) (m : real) : (term9 n m) = ((real_max m n) = (term10 n m)).
Proof. exact (eq_refl (term9 n m)). Qed.
Lemma lem5175635 (x : real) : term11 x.
Proof. exact (@lem1339240 x). Qed.
Lemma lem5175636 (x : real) : (term11 x) = (real_le x x).
Proof. exact (eq_refl (term11 x)). Qed.
Lemma lem5175637 (x : real) : real_le x x.
Proof. exact (EQ_MP (@lem5175636 x) (@lem5175635 x)). Qed.
Lemma lem5175638 (x : real) : (real_le x x) = ((real_le x x) = True).
Proof. exact (@lem7 (real_le x x)). Qed.
Lemma lem5175640 {A : Type'} (x : A) : term12 A x.
Proof. exact (@lem3205876 A x). Qed.
Lemma lem5175641 {A : Type'} (x : A) : (term12 A x) = (term13 A x).
Proof. exact (eq_refl (term12 A x)). Qed.
Lemma lem5175642 {A : Type'} (x : A) : term13 A x.
Proof. exact (EQ_MP (@lem5175641 A x) (@lem5175640 A x)). Qed.
Lemma lem5175643 {A : Type'} (x : A) (y : A) : term14 A x y.
Proof. exact (@lem5175642 A x y). Qed.
Lemma lem5175644 {A : Type'} (x : A) (y : A) : (term14 A x y) = ((term15 A x y) = (x = y)).
Proof. exact (eq_refl (term14 A x y)). Qed.
Lemma lem5175646 (s : real -> Prop) (h1 : @FINITE real s) : @FINITE real s.
Proof. exact (h1). Qed.
Lemma lem5175647 (_474 : real) (_475 : Prop) (_476 : real -> Prop) (_477 : real) : (term16 _476 _475 _474 _477) = (term17 _474 _475 _476 _477).
Proof. exact (@lem13473 real _474 _475 _476 _477). Qed.
Lemma lem5175648 (_474 : real) (_475 : Prop) (x : real) (s : real -> Prop) (_477 : real) : (term18 x s _475 _474 _477) = (term19 _474 _475 x s _477).
Proof. exact (@lem5175647 _474 _475 (term20 x s) _477). Qed.
Lemma lem5175649 (x : real) (s : real -> Prop) : (term21 x s) = (term22 x s).
Proof. exact (@lem5175648 x (s = (@EMPTY real)) x s (term23 x s)). Qed.
Lemma lem5175650 (x : real) (s : real -> Prop) : (term24 x s) = ((term25 x s) = (term23 x s)).
Proof. exact (eq_refl (term24 x s)). Qed.
Lemma lem5175651 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5175652 (x : real) (s : real -> Prop) : (term27 x s) = (term28 x s).
Proof. exact (MK_COMB (@lem5175651 s) (@lem5175650 x s)). Qed.
Lemma lem5175653 (s : real -> Prop) (x : real) : (term29 s x) = ((term25 x s) = x).
Proof. exact (eq_refl (term29 s x)). Qed.
Lemma lem5175654 (s : real -> Prop) : (term30 s) = (term30 s).
Proof. exact (eq_refl (term30 s)). Qed.
Lemma lem5175655 (s : real -> Prop) (x : real) : (term31 s x) = (term32 s x).
Proof. exact (MK_COMB (@lem5175654 s) (@lem5175653 s x)). Qed.
Lemma lem5175656 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5175657 (s : real -> Prop) (x : real) : (term33 s x) = (term34 s x).
Proof. exact (MK_COMB (@lem5175656) (@lem5175655 s x)). Qed.
Lemma lem5175658 (x : real) (s : real -> Prop) : (term22 x s) = (term35 x s).
Proof. exact (MK_COMB (@lem5175657 s x) (@lem5175652 x s)). Qed.
Lemma lem5175659 (x : real) (s : real -> Prop) : (term21 x s) = ((term25 x s) = (term36 x s)).
Proof. exact (eq_refl (term21 x s)). Qed.
Lemma lem5175660 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5175661 (x : real) (s : real -> Prop) : (term37 x s) = (term38 x s).
Proof. exact (MK_COMB (@lem5175660) (@lem5175659 x s)). Qed.
Lemma lem5175662 (x : real) (s : real -> Prop) : ((term21 x s) = (term22 x s)) = (((term25 x s) = (term36 x s)) = (term35 x s)).
Proof. exact (MK_COMB (@lem5175661 x s) (@lem5175658 x s)). Qed.
Lemma lem5175663 (x : real) (s : real -> Prop) : ((term25 x s) = (term36 x s)) = (term35 x s).
Proof. exact (EQ_MP (@lem5175662 x s) (@lem5175649 x s)). Qed.
Lemma lem5175664 (x : real) (s : real -> Prop) : (term35 x s) = ((term25 x s) = (term36 x s)).
Proof. exact (SYM (@lem5175663 x s)). Qed.
Lemma lem5175665 (s : real -> Prop) (h1 : s = (@EMPTY real)) : s = (@EMPTY real).
Proof. exact (h1). Qed.
Lemma lem5175682 (s : real -> Prop) (h1 : term39 s) : term39 s.
Proof. exact (h1). Qed.
Lemma lem5175699 {A : Type'} (x : A) : term40 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem5175700 {A : Type'} (x : A) : (term40 A x) = (term41 A x).
Proof. exact (eq_refl (term40 A x)). Qed.
Lemma lem5175701 {A : Type'} (x : A) : term41 A x.
Proof. exact (EQ_MP (@lem5175700 A x) (@lem5175699 A x)). Qed.
Lemma lem5175702 {A : Type'} (x : A) : term42 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem5175704 {_83983 : Type'} (P : _83983 -> Prop) : term43 _83983 P.
Proof. exact (@lem3207453 _83983 P). Qed.
Lemma lem5175705 {_83983 : Type'} (P : _83983 -> Prop) : (term43 _83983 P) = (term44 _83983 P).
Proof. exact (eq_refl (term43 _83983 P)). Qed.
Lemma lem5175706 {_83983 : Type'} (P : _83983 -> Prop) : term44 _83983 P.
Proof. exact (EQ_MP (@lem5175705 _83983 P) (@lem5175704 _83983 P)). Qed.
Lemma lem5175707 {_83983 : Type'} (P : _83983 -> Prop) (a : _83983) : term45 _83983 P a.
Proof. exact (@lem5175706 _83983 P a). Qed.
Lemma lem5175708 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) : (term45 _83983 P a) = (term46 _83983 a P).
Proof. exact (eq_refl (term45 _83983 P a)). Qed.
Lemma lem5175709 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) : term46 _83983 a P.
Proof. exact (EQ_MP (@lem5175708 _83983 a P) (@lem5175707 _83983 P a)). Qed.
Lemma lem5175710 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) (s : _83983 -> Prop) : term47 _83983 a P s.
Proof. exact (@lem5175709 _83983 a P s). Qed.
Lemma lem5175711 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term47 _83983 a P s) = ((term48 _83983 a s P) = (term49 _83983 a s P)).
Proof. exact (eq_refl (term47 _83983 a P s)). Qed.
Lemma lem5175713 {A : Type'} (x : A) : term50 A x.
Proof. exact (@lem3278799 A x). Qed.
Lemma lem5175714 {A : Type'} (x : A) : (term50 A x) = (term51 A x).
Proof. exact (eq_refl (term50 A x)). Qed.
Lemma lem5175715 {A : Type'} (x : A) : term51 A x.
Proof. exact (EQ_MP (@lem5175714 A x) (@lem5175713 A x)). Qed.
Lemma lem5175716 {A : Type'} (x : A) (s : A -> Prop) : term52 A x s.
Proof. exact (@lem5175715 A x s). Qed.
Lemma lem5175717 {A : Type'} (x : A) (s : A -> Prop) : (term52 A x s) = (term53 A x s).
Proof. exact (eq_refl (term52 A x s)). Qed.
Lemma lem5175718 {A : Type'} (x : A) (s : A -> Prop) : term53 A x s.
Proof. exact (EQ_MP (@lem5175717 A x s) (@lem5175716 A x s)). Qed.
Lemma lem5175719 {A : Type'} (x : A) (s : A -> Prop) : term54 A x s.
Proof. exact (@lem82 ((@INSERT A x s) = (@EMPTY A))). Qed.
Lemma lem5175734 {A : Type'} (s : A -> Prop) : term55 A s.
Proof. exact (@lem3608316 A s). Qed.
Lemma lem5175735 {A : Type'} (s : A -> Prop) : (term55 A s) = (term56 A s).
Proof. exact (eq_refl (term55 A s)). Qed.
Lemma lem5175736 {A : Type'} (s : A -> Prop) : term56 A s.
Proof. exact (EQ_MP (@lem5175735 A s) (@lem5175734 A s)). Qed.
Lemma lem5175737 {A : Type'} (s : A -> Prop) (x : A) : term57 A s x.
Proof. exact (@lem5175736 A s x). Qed.
Lemma lem5175738 {A : Type'} (x : A) (s : A -> Prop) : (term57 A s x) = ((term58 A x s) = (@FINITE A s)).
Proof. exact (eq_refl (term57 A s x)). Qed.
Lemma lem5175740 (a : real) (s : real -> Prop) : term59 a s.
Proof. exact (@lem5175618 a s). Qed.
Lemma lem5175741 (s : real -> Prop) (a : real) : (term59 a s) = (term60 s a).
Proof. exact (eq_refl (term59 a s)). Qed.
Lemma lem5175742 (s : real -> Prop) (a : real) : term60 s a.
Proof. exact (EQ_MP (@lem5175741 s a) (@lem5175740 a s)). Qed.
Lemma lem5175743 (s : real -> Prop) (h1 : term61 s) : term61 s.
Proof. exact (h1). Qed.
Lemma lem5175744 (a : real) (s : real -> Prop) (h1 : term61 s) : ((sup s) = a) = (term62 s a).
Proof. exact (@lem5175742 s a (@lem5175743 s h1)). Qed.
Lemma lem5175750 (s : real -> Prop) : (@FINITE real s) = ((@FINITE real s) = True).
Proof. exact (@lem7 (@FINITE real s)). Qed.
Lemma lem5175753 (s : real -> Prop) (a : real) : term60 s a.
Proof. exact (fun h0 : term61 s => @lem5175744 a s h0). Qed.
Lemma lem5175754 (s : real -> Prop) (x : real) : term63 s x.
Proof. exact (@lem5175753 (@INSERT real x s) x). Qed.
Lemma lem5175758 {A : Type'} (x : A) (s : A -> Prop) : (term58 A x s) = (@FINITE A s).
Proof. exact (EQ_MP (@lem5175738 A x s) (@lem5175737 A s x)). Qed.
Lemma lem5175759 (x : real) (s : real -> Prop) : (term64 x s) = (@FINITE real s).
Proof. exact (@lem5175758 real x s). Qed.
Lemma lem5175761 (s : real -> Prop) (h1 : @FINITE real s) : (@FINITE real s) = True.
Proof. exact (EQ_MP (@lem5175750 s) (@lem5175646 s h1)). Qed.
Lemma lem5175762 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : (term64 x s) = True.
Proof. exact (TRANS (@lem5175759 x s) (@lem5175761 s h1)). Qed.
Lemma lem5175763 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5175764 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : (term65 x s) = (and True).
Proof. exact (MK_COMB (@lem5175763) (@lem5175762 x s h1)). Qed.
Lemma lem5175766 {A : Type'} (x : A) (s : A -> Prop) : ((@INSERT A x s) = (@EMPTY A)) = False.
Proof. exact (@lem5175719 A x s (@lem5175718 A x s)). Qed.
Lemma lem5175767 (x : real) (s : real -> Prop) : ((@INSERT real x s) = (@EMPTY real)) = False.
Proof. exact (@lem5175766 real x s). Qed.
Lemma lem5175768 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5175769 (x : real) (s : real -> Prop) : (term66 x s) = (~ False).
Proof. exact (MK_COMB (@lem5175768) (@lem5175767 x s)). Qed.
Lemma lem5175771 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem5175772 (x : real) (s : real -> Prop) : (term66 x s) = True.
Proof. exact (TRANS (@lem5175769 x s) (@lem5175771)). Qed.
Lemma lem5175773 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : (term67 x s) = (True /\ True).
Proof. exact (MK_COMB (@lem5175764 x s h1) (@lem5175772 x s)). Qed.
Lemma lem5175775 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5175776 : (True /\ True) = True.
Proof. exact (@lem5175775 True). Qed.
Lemma lem5175777 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : (term67 x s) = True.
Proof. exact (TRANS (@lem5175773 x s h1) (@lem5175776)). Qed.
Lemma lem5175778 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : True = (term67 x s).
Proof. exact (SYM (@lem5175777 x s h1)). Qed.
Lemma lem5175779 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : term67 x s.
Proof. exact (EQ_MP (@lem5175778 x s h1) (@lem0)). Qed.
Lemma lem5175780 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : ((term25 x s) = x) = (term68 s x).
Proof. exact (@lem5175754 s x (@lem5175779 x s h1)). Qed.
Lemma lem5175784 (s : real -> Prop) (h1 : s = (@EMPTY real)) : s = (@EMPTY real).
Proof. exact (h1). Qed.
Lemma lem5175785 (x : real) : (@INSERT real x) = (@INSERT real x).
Proof. exact (eq_refl (@INSERT real x)). Qed.
Lemma lem5175786 (x : real) (s : real -> Prop) (h1 : s = (@EMPTY real)) : (@INSERT real x s) = (@INSERT real x (@EMPTY real)).
Proof. exact (MK_COMB (@lem5175785 x) (@lem5175784 s h1)). Qed.
Lemma lem5175787 (x : real) : (@IN real x) = (@IN real x).
Proof. exact (eq_refl (@IN real x)). Qed.
Lemma lem5175788 (x : real) (s : real -> Prop) (h1 : s = (@EMPTY real)) : (term69 x s) = (term70 x).
Proof. exact (MK_COMB (@lem5175787 x) (@lem5175786 x s h1)). Qed.
Lemma lem5175789 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5175790 (x : real) (s : real -> Prop) (h1 : s = (@EMPTY real)) : (term71 x s) = (term72 x).
Proof. exact (MK_COMB (@lem5175789) (@lem5175788 x s h1)). Qed.
Lemma lem5175792 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term48 _83983 a s P) = (term49 _83983 a s P).
Proof. exact (EQ_MP (@lem5175711 _83983 a s P) (@lem5175710 _83983 a P s)). Qed.
Lemma lem5175793 (a : real) (s : real -> Prop) (P : real -> Prop) : (term73 a s P) = (term74 a s P).
Proof. exact (@lem5175792 real a s P). Qed.
Lemma lem5175794 (s : real -> Prop) (x : real) : (term75 s x) = (term76 s x).
Proof. exact (@lem5175793 x s (term77 x)). Qed.
Lemma lem5175795 (y : real) (x : real) : (term78 x y) = (real_le y x).
Proof. exact (eq_refl (term78 x y)). Qed.
Lemma lem5175796 (y : real) (x : real) (s : real -> Prop) : (term79 y x s) = (term79 y x s).
Proof. exact (eq_refl (term79 y x s)). Qed.
Lemma lem5175797 (s : real -> Prop) (y : real) (x : real) : (term80 s x y) = (term81 s y x).
Proof. exact (MK_COMB (@lem5175796 y x s) (@lem5175795 y x)). Qed.
Lemma lem5175798 (s : real -> Prop) (x : real) : (term82 s x) = (term83 s x).
Proof. exact (fun_ext (fun y : real => @lem5175797 s y x)). Qed.
Lemma lem5175799 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5175800 (s : real -> Prop) (x : real) : (term75 s x) = (term84 s x).
Proof. exact (MK_COMB (@lem5175799) (@lem5175798 s x)). Qed.
Lemma lem5175801 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5175802 (s : real -> Prop) (x : real) : (term85 s x) = (term86 s x).
Proof. exact (MK_COMB (@lem5175801) (@lem5175800 s x)). Qed.
Lemma lem5175803 (x : real) : (term87 x) = (real_le x x).
Proof. exact (eq_refl (term87 x)). Qed.
Lemma lem5175804 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5175805 (x : real) : (term88 x) = (term89 x).
Proof. exact (MK_COMB (@lem5175804) (@lem5175803 x)). Qed.
Lemma lem5175806 (y : real) (x : real) : (term78 x y) = (real_le y x).
Proof. exact (eq_refl (term78 x y)). Qed.
Lemma lem5175807 (y : real) (s : real -> Prop) : (term90 y s) = (term90 y s).
Proof. exact (eq_refl (term90 y s)). Qed.
Lemma lem5175808 (s : real -> Prop) (y : real) (x : real) : (term91 s x y) = (term92 s y x).
Proof. exact (MK_COMB (@lem5175807 y s) (@lem5175806 y x)). Qed.
Lemma lem5175809 (s : real -> Prop) (x : real) : (term93 s x) = (term94 s x).
Proof. exact (fun_ext (fun y : real => @lem5175808 s y x)). Qed.
Lemma lem5175810 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5175811 (s : real -> Prop) (x : real) : (term95 s x) = (term96 s x).
Proof. exact (MK_COMB (@lem5175810) (@lem5175809 s x)). Qed.
Lemma lem5175812 (s : real -> Prop) (x : real) : (term76 s x) = (term97 s x).
Proof. exact (MK_COMB (@lem5175805 x) (@lem5175811 s x)). Qed.
Lemma lem5175813 (s : real -> Prop) (x : real) : ((term75 s x) = (term76 s x)) = ((term84 s x) = (term97 s x)).
Proof. exact (MK_COMB (@lem5175802 s x) (@lem5175812 s x)). Qed.
Lemma lem5175814 (s : real -> Prop) (x : real) : (term84 s x) = (term97 s x).
Proof. exact (EQ_MP (@lem5175813 s x) (@lem5175794 s x)). Qed.
Lemma lem5175824 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term98 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5175825 (p : Prop) (q : Prop) (p' : Prop) : term99 p q p'.
Proof. exact (fun q' : Prop => @lem5175824 p q p' q'). Qed.
Lemma lem5175826 (p : Prop) (q : Prop) : term100 p q.
Proof. exact (fun p' : Prop => @lem5175825 p q p'). Qed.
Lemma lem5175827 (s : real -> Prop) (y : real) (x : real) : term101 s y x.
Proof. exact (@lem5175826 (@IN real y s) (real_le y x)). Qed.
Lemma lem5175828 (s : real -> Prop) (y : real) (x : real) (p' : Prop) : term102 s y x p'.
Proof. exact (@lem5175827 s y x p'). Qed.
Lemma lem5175829 (s : real -> Prop) (y : real) (x : real) (p' : Prop) : (term102 s y x p') = (term103 s y x p').
Proof. exact (eq_refl (term102 s y x p')). Qed.
Lemma lem5175830 (s : real -> Prop) (y : real) (x : real) (p' : Prop) : term103 s y x p'.
Proof. exact (EQ_MP (@lem5175829 s y x p') (@lem5175828 s y x p')). Qed.
Lemma lem5175831 (s : real -> Prop) (y : real) (x : real) (p' : Prop) (q' : Prop) : term104 s y x p' q'.
Proof. exact (@lem5175830 s y x p' q'). Qed.
Lemma lem5175832 (s : real -> Prop) (y : real) (x : real) (p' : Prop) (q' : Prop) : (term104 s y x p' q') = (term105 s y x p' q').
Proof. exact (eq_refl (term104 s y x p' q')). Qed.
Lemma lem5175833 (s : real -> Prop) (y : real) (x : real) (p' : Prop) (q' : Prop) : term105 s y x p' q'.
Proof. exact (EQ_MP (@lem5175832 s y x p' q') (@lem5175831 s y x p' q')). Qed.
Lemma lem5175835 (s : real -> Prop) (h1 : s = (@EMPTY real)) : s = (@EMPTY real).
Proof. exact (h1). Qed.
Lemma lem5175836 (y : real) : (@IN real y) = (@IN real y).
Proof. exact (eq_refl (@IN real y)). Qed.
Lemma lem5175837 (y : real) (s : real -> Prop) (h1 : s = (@EMPTY real)) : (@IN real y s) = (@IN real y (@EMPTY real)).
Proof. exact (MK_COMB (@lem5175836 y) (@lem5175835 s h1)). Qed.
Lemma lem5175839 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem5175702 A x (@lem5175701 A x)). Qed.
Lemma lem5175840 (x : real) : (@IN real x (@EMPTY real)) = False.
Proof. exact (@lem5175839 real x). Qed.
Lemma lem5175841 (y : real) : (@IN real y (@EMPTY real)) = False.
Proof. exact (@lem5175840 y). Qed.
Lemma lem5175842 (y : real) (s : real -> Prop) (h1 : s = (@EMPTY real)) : (@IN real y s) = False.
Proof. exact (TRANS (@lem5175837 y s h1) (@lem5175841 y)). Qed.
Lemma lem5175843 (s : real -> Prop) (y : real) (x : real) (q' : Prop) : term106 s y x q'.
Proof. exact (@lem5175833 s y x False q'). Qed.
Lemma lem5175844 (y : real) (x : real) (q' : Prop) (s : real -> Prop) (h1 : s = (@EMPTY real)) : term107 s y x q'.
Proof. exact (@lem5175843 s y x q' (@lem5175842 y s h1)). Qed.
Lemma lem5175848 (y : real) (x : real) : (real_le y x) = (real_le y x).
Proof. exact (eq_refl (real_le y x)). Qed.
Lemma lem5175849 (y : real) (x : real) : term108 y x.
Proof. exact (fun h0 : False => @lem5175848 y x). Qed.
Lemma lem5175850 (y : real) (x : real) (s : real -> Prop) (h1 : s = (@EMPTY real)) : term109 s y x.
Proof. exact (@lem5175844 y x (real_le y x) s h1). Qed.
Lemma lem5175851 (y : real) (x : real) (s : real -> Prop) (h1 : s = (@EMPTY real)) : (term92 s y x) = (term110 y x).
Proof. exact (@lem5175850 y x s h1 (@lem5175849 y x)). Qed.
Lemma lem5175853 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem5175854 (y : real) (x : real) : (term110 y x) = True.
Proof. exact (@lem5175853 (real_le y x)). Qed.
Lemma lem5175855 (y : real) (x : real) (s : real -> Prop) (h1 : s = (@EMPTY real)) : (term92 s y x) = True.
Proof. exact (TRANS (@lem5175851 y x s h1) (@lem5175854 y x)). Qed.
Lemma lem5175856 (x : real) (s : real -> Prop) (h1 : s = (@EMPTY real)) : (term94 s x) = term111.
Proof. exact (fun_ext (fun y : real => @lem5175855 y x s h1)). Qed.
Lemma lem5175857 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5175858 (x : real) (s : real -> Prop) (h1 : s = (@EMPTY real)) : (term96 s x) = term112.
Proof. exact (MK_COMB (@lem5175857) (@lem5175856 x s h1)). Qed.
Lemma lem5175860 {A : Type'} (t : Prop) : (term113 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5175861 (t : Prop) : (term114 t) = t.
Proof. exact (@lem5175860 real t). Qed.
Lemma lem5175862 : term112 = True.
Proof. exact (@lem5175861 True). Qed.
Lemma lem5175863 (x : real) (s : real -> Prop) (h1 : s = (@EMPTY real)) : (term96 s x) = True.
Proof. exact (TRANS (@lem5175858 x s h1) (@lem5175862)). Qed.
Lemma lem5175864 (x : real) : (term89 x) = (term89 x).
Proof. exact (eq_refl (term89 x)). Qed.
Lemma lem5175865 (x : real) (s : real -> Prop) (h1 : s = (@EMPTY real)) : (term97 s x) = (term115 x).
Proof. exact (MK_COMB (@lem5175864 x) (@lem5175863 x s h1)). Qed.
Lemma lem5175867 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem5175868 (x : real) : (term115 x) = (real_le x x).
Proof. exact (@lem5175867 (real_le x x)). Qed.
Lemma lem5175869 (x : real) (s : real -> Prop) (h1 : s = (@EMPTY real)) : (term97 s x) = (real_le x x).
Proof. exact (TRANS (@lem5175865 x s h1) (@lem5175868 x)). Qed.
Lemma lem5175870 (x : real) (s : real -> Prop) (h1 : s = (@EMPTY real)) : (term84 s x) = (real_le x x).
Proof. exact (TRANS (@lem5175814 s x) (@lem5175869 x s h1)). Qed.
Lemma lem5175871 (x : real) (s : real -> Prop) (h1 : s = (@EMPTY real)) : (term68 s x) = (term116 x).
Proof. exact (MK_COMB (@lem5175790 x s h1) (@lem5175870 x s h1)). Qed.
Lemma lem5175874 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : s = (@EMPTY real)) : ((term25 x s) = x) = (term116 x).
Proof. exact (TRANS (@lem5175780 x s h1) (@lem5175871 x s h2)). Qed.
Lemma lem5175875 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : s = (@EMPTY real)) : (term116 x) = ((term25 x s) = x).
Proof. exact (SYM (@lem5175874 x s h1 h2)). Qed.
Lemma lem5175881 {_83983 : Type'} (P : _83983 -> Prop) : term43 _83983 P.
Proof. exact (@lem3207453 _83983 P). Qed.
Lemma lem5175882 {_83983 : Type'} (P : _83983 -> Prop) : (term43 _83983 P) = (term44 _83983 P).
Proof. exact (eq_refl (term43 _83983 P)). Qed.
Lemma lem5175883 {_83983 : Type'} (P : _83983 -> Prop) : term44 _83983 P.
Proof. exact (EQ_MP (@lem5175882 _83983 P) (@lem5175881 _83983 P)). Qed.
Lemma lem5175884 {_83983 : Type'} (P : _83983 -> Prop) (a : _83983) : term45 _83983 P a.
Proof. exact (@lem5175883 _83983 P a). Qed.
Lemma lem5175885 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) : (term45 _83983 P a) = (term46 _83983 a P).
Proof. exact (eq_refl (term45 _83983 P a)). Qed.
Lemma lem5175886 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) : term46 _83983 a P.
Proof. exact (EQ_MP (@lem5175885 _83983 a P) (@lem5175884 _83983 P a)). Qed.
Lemma lem5175887 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) (s : _83983 -> Prop) : term47 _83983 a P s.
Proof. exact (@lem5175886 _83983 a P s). Qed.
Lemma lem5175888 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term47 _83983 a P s) = ((term48 _83983 a s P) = (term49 _83983 a s P)).
Proof. exact (eq_refl (term47 _83983 a P s)). Qed.
Lemma lem5175890 {A : Type'} (x : A) : term50 A x.
Proof. exact (@lem3278799 A x). Qed.
Lemma lem5175891 {A : Type'} (x : A) : (term50 A x) = (term51 A x).
Proof. exact (eq_refl (term50 A x)). Qed.
Lemma lem5175892 {A : Type'} (x : A) : term51 A x.
Proof. exact (EQ_MP (@lem5175891 A x) (@lem5175890 A x)). Qed.
Lemma lem5175893 {A : Type'} (x : A) (s : A -> Prop) : term52 A x s.
Proof. exact (@lem5175892 A x s). Qed.
Lemma lem5175894 {A : Type'} (x : A) (s : A -> Prop) : (term52 A x s) = (term53 A x s).
Proof. exact (eq_refl (term52 A x s)). Qed.
Lemma lem5175895 {A : Type'} (x : A) (s : A -> Prop) : term53 A x s.
Proof. exact (EQ_MP (@lem5175894 A x s) (@lem5175893 A x s)). Qed.
Lemma lem5175896 {A : Type'} (x : A) (s : A -> Prop) : term54 A x s.
Proof. exact (@lem82 ((@INSERT A x s) = (@EMPTY A))). Qed.
Lemma lem5175911 {A : Type'} (s : A -> Prop) : term55 A s.
Proof. exact (@lem3608316 A s). Qed.
Lemma lem5175912 {A : Type'} (s : A -> Prop) : (term55 A s) = (term56 A s).
Proof. exact (eq_refl (term55 A s)). Qed.
Lemma lem5175913 {A : Type'} (s : A -> Prop) : term56 A s.
Proof. exact (EQ_MP (@lem5175912 A s) (@lem5175911 A s)). Qed.
Lemma lem5175914 {A : Type'} (s : A -> Prop) (x : A) : term57 A s x.
Proof. exact (@lem5175913 A s x). Qed.
Lemma lem5175915 {A : Type'} (x : A) (s : A -> Prop) : (term57 A s x) = ((term58 A x s) = (@FINITE A s)).
Proof. exact (eq_refl (term57 A s x)). Qed.
Lemma lem5175917 (a : real) (s : real -> Prop) : term59 a s.
Proof. exact (@lem5175618 a s). Qed.
Lemma lem5175918 (s : real -> Prop) (a : real) : (term59 a s) = (term60 s a).
Proof. exact (eq_refl (term59 a s)). Qed.
Lemma lem5175919 (s : real -> Prop) (a : real) : term60 s a.
Proof. exact (EQ_MP (@lem5175918 s a) (@lem5175917 a s)). Qed.
Lemma lem5175920 (s : real -> Prop) (h1 : term61 s) : term61 s.
Proof. exact (h1). Qed.
Lemma lem5175921 (a : real) (s : real -> Prop) (h1 : term61 s) : ((sup s) = a) = (term62 s a).
Proof. exact (@lem5175919 s a (@lem5175920 s h1)). Qed.
Lemma lem5175927 (s : real -> Prop) : (@FINITE real s) = ((@FINITE real s) = True).
Proof. exact (@lem7 (@FINITE real s)). Qed.
Lemma lem5175943 (s : real -> Prop) (a : real) : term60 s a.
Proof. exact (fun h0 : term61 s => @lem5175921 a s h0). Qed.
Lemma lem5175944 (x : real) (s : real -> Prop) : term117 x s.
Proof. exact (@lem5175943 (@INSERT real x s) (term23 x s)). Qed.
Lemma lem5175948 {A : Type'} (x : A) (s : A -> Prop) : (term58 A x s) = (@FINITE A s).
Proof. exact (EQ_MP (@lem5175915 A x s) (@lem5175914 A s x)). Qed.
Lemma lem5175949 (x : real) (s : real -> Prop) : (term64 x s) = (@FINITE real s).
Proof. exact (@lem5175948 real x s). Qed.
Lemma lem5175951 (s : real -> Prop) (h1 : @FINITE real s) : (@FINITE real s) = True.
Proof. exact (EQ_MP (@lem5175927 s) (@lem5175646 s h1)). Qed.
Lemma lem5175952 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : (term64 x s) = True.
Proof. exact (TRANS (@lem5175949 x s) (@lem5175951 s h1)). Qed.
Lemma lem5175953 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5175954 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : (term65 x s) = (and True).
Proof. exact (MK_COMB (@lem5175953) (@lem5175952 x s h1)). Qed.
Lemma lem5175956 {A : Type'} (x : A) (s : A -> Prop) : ((@INSERT A x s) = (@EMPTY A)) = False.
Proof. exact (@lem5175896 A x s (@lem5175895 A x s)). Qed.
Lemma lem5175957 (x : real) (s : real -> Prop) : ((@INSERT real x s) = (@EMPTY real)) = False.
Proof. exact (@lem5175956 real x s). Qed.
Lemma lem5175958 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5175959 (x : real) (s : real -> Prop) : (term66 x s) = (~ False).
Proof. exact (MK_COMB (@lem5175958) (@lem5175957 x s)). Qed.
Lemma lem5175961 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem5175962 (x : real) (s : real -> Prop) : (term66 x s) = True.
Proof. exact (TRANS (@lem5175959 x s) (@lem5175961)). Qed.
Lemma lem5175963 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : (term67 x s) = (True /\ True).
Proof. exact (MK_COMB (@lem5175954 x s h1) (@lem5175962 x s)). Qed.
Lemma lem5175965 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5175966 : (True /\ True) = True.
Proof. exact (@lem5175965 True). Qed.
Lemma lem5175967 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : (term67 x s) = True.
Proof. exact (TRANS (@lem5175963 x s h1) (@lem5175966)). Qed.
Lemma lem5175968 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : True = (term67 x s).
Proof. exact (SYM (@lem5175967 x s h1)). Qed.
Lemma lem5175969 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : term67 x s.
Proof. exact (EQ_MP (@lem5175968 x s h1) (@lem0)). Qed.
Lemma lem5175970 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : ((term25 x s) = (term23 x s)) = (term118 x s).
Proof. exact (@lem5175944 x s (@lem5175969 x s h1)). Qed.
Lemma lem5175974 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term48 _83983 a s P) = (term49 _83983 a s P).
Proof. exact (EQ_MP (@lem5175888 _83983 a s P) (@lem5175887 _83983 a P s)). Qed.
Lemma lem5175975 (a : real) (s : real -> Prop) (P : real -> Prop) : (term73 a s P) = (term74 a s P).
Proof. exact (@lem5175974 real a s P). Qed.
Lemma lem5175976 (x : real) (s : real -> Prop) : (term119 x s) = (term120 x s).
Proof. exact (@lem5175975 x s (term121 x s)). Qed.
Lemma lem5175977 (y : real) (x : real) (s : real -> Prop) : (term122 x s y) = (term123 y x s).
Proof. exact (eq_refl (term122 x s y)). Qed.
Lemma lem5175978 (y : real) (x : real) (s : real -> Prop) : (term79 y x s) = (term79 y x s).
Proof. exact (eq_refl (term79 y x s)). Qed.
Lemma lem5175979 (y : real) (x : real) (s : real -> Prop) : (term124 x s y) = (term125 y x s).
Proof. exact (MK_COMB (@lem5175978 y x s) (@lem5175977 y x s)). Qed.
Lemma lem5175980 (x : real) (s : real -> Prop) : (term126 x s) = (term127 x s).
Proof. exact (fun_ext (fun y : real => @lem5175979 y x s)). Qed.
Lemma lem5175981 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5175982 (x : real) (s : real -> Prop) : (term119 x s) = (term128 x s).
Proof. exact (MK_COMB (@lem5175981) (@lem5175980 x s)). Qed.
Lemma lem5175983 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5175984 (x : real) (s : real -> Prop) : (term129 x s) = (term130 x s).
Proof. exact (MK_COMB (@lem5175983) (@lem5175982 x s)). Qed.
Lemma lem5175985 (x : real) (s : real -> Prop) : (term131 s x) = (term132 x s).
Proof. exact (eq_refl (term131 s x)). Qed.
Lemma lem5175986 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5175987 (x : real) (s : real -> Prop) : (term133 s x) = (term134 x s).
Proof. exact (MK_COMB (@lem5175986) (@lem5175985 x s)). Qed.
Lemma lem5175988 (y : real) (x : real) (s : real -> Prop) : (term122 x s y) = (term123 y x s).
Proof. exact (eq_refl (term122 x s y)). Qed.
Lemma lem5175989 (y : real) (s : real -> Prop) : (term90 y s) = (term90 y s).
Proof. exact (eq_refl (term90 y s)). Qed.
Lemma lem5175990 (y : real) (x : real) (s : real -> Prop) : (term135 x s y) = (term136 y x s).
Proof. exact (MK_COMB (@lem5175989 y s) (@lem5175988 y x s)). Qed.
Lemma lem5175991 (x : real) (s : real -> Prop) : (term137 x s) = (term138 x s).
Proof. exact (fun_ext (fun y : real => @lem5175990 y x s)). Qed.
Lemma lem5175992 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5175993 (x : real) (s : real -> Prop) : (term139 x s) = (term140 x s).
Proof. exact (MK_COMB (@lem5175992) (@lem5175991 x s)). Qed.
Lemma lem5175994 (x : real) (s : real -> Prop) : (term120 x s) = (term141 x s).
Proof. exact (MK_COMB (@lem5175987 x s) (@lem5175993 x s)). Qed.
Lemma lem5175995 (x : real) (s : real -> Prop) : ((term119 x s) = (term120 x s)) = ((term128 x s) = (term141 x s)).
Proof. exact (MK_COMB (@lem5175984 x s) (@lem5175994 x s)). Qed.
Lemma lem5175996 (x : real) (s : real -> Prop) : (term128 x s) = (term141 x s).
Proof. exact (EQ_MP (@lem5175995 x s) (@lem5175976 x s)). Qed.
Lemma lem5176026 (x : real) (s : real -> Prop) : (term142 x s) = (term142 x s).
Proof. exact (eq_refl (term142 x s)). Qed.
Lemma lem5176027 (x : real) (s : real -> Prop) : (term118 x s) = (term143 x s).
Proof. exact (MK_COMB (@lem5176026 x s) (@lem5175996 x s)). Qed.
Lemma lem5176059 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : ((term25 x s) = (term23 x s)) = (term143 x s).
Proof. exact (TRANS (@lem5175970 x s h1) (@lem5176027 x s)). Qed.
Lemma lem5176060 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : (term143 x s) = ((term25 x s) = (term23 x s)).
Proof. exact (SYM (@lem5176059 x s h1)). Qed.
Lemma lem5176064 {A : Type'} (x : A) (y : A) : (term15 A x y) = (x = y).
Proof. exact (EQ_MP (@lem5175644 A x y) (@lem5175643 A x y)). Qed.
Lemma lem5176065 (x : real) (y : real) : (term144 x y) = (x = y).
Proof. exact (@lem5176064 real x y). Qed.
Lemma lem5176066 (x : real) : (term70 x) = (x = x).
Proof. exact (@lem5176065 x x). Qed.
Lemma lem5176068 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5176069 (x : real) : (x = x) = True.
Proof. exact (@lem5176068 real x). Qed.
Lemma lem5176070 (x : real) : (term70 x) = True.
Proof. exact (TRANS (@lem5176066 x) (@lem5176069 x)). Qed.
Lemma lem5176071 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5176072 (x : real) : (term72 x) = (and True).
Proof. exact (MK_COMB (@lem5176071) (@lem5176070 x)). Qed.
Lemma lem5176074 (x : real) : (real_le x x) = True.
Proof. exact (EQ_MP (@lem5175638 x) (@lem5175637 x)). Qed.
Lemma lem5176075 (x : real) : (term116 x) = (True /\ True).
Proof. exact (MK_COMB (@lem5176072 x) (@lem5176074 x)). Qed.
Lemma lem5176077 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5176078 : (True /\ True) = True.
Proof. exact (@lem5176077 True). Qed.
Lemma lem5176079 (x : real) : (term116 x) = True.
Proof. exact (TRANS (@lem5176075 x) (@lem5176078)). Qed.
Lemma lem5176080 (x : real) : True = (term116 x).
Proof. exact (SYM (@lem5176079 x)). Qed.
Lemma lem5176081 (x : real) : term116 x.
Proof. exact (EQ_MP (@lem5176080 x) (@lem0)). Qed.
Lemma lem5176101 (n : real) (m : real) : (real_max m n) = (term10 n m).
Proof. exact (EQ_MP (@lem5175633 n m) (@lem5175632 n m)). Qed.
Lemma lem5176102 (s : real -> Prop) (x : real) : (term23 x s) = (term145 s x).
Proof. exact (@lem5176101 (sup s) x). Qed.
Lemma lem5176103 : (@IN real) = (@IN real).
Proof. exact (eq_refl (@IN real)). Qed.
Lemma lem5176104 (s : real -> Prop) (x : real) : (term146 x s) = (term147 s x).
Proof. exact (MK_COMB (@lem5176103) (@lem5176102 s x)). Qed.
Lemma lem5176105 (x : real) (s : real -> Prop) : (@INSERT real x s) = (@INSERT real x s).
Proof. exact (eq_refl (@INSERT real x s)). Qed.
Lemma lem5176106 (x : real) (s : real -> Prop) : (term148 x s) = (term149 x s).
Proof. exact (MK_COMB (@lem5176104 s x) (@lem5176105 x s)). Qed.
Lemma lem5176107 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5176108 (x : real) (s : real -> Prop) : (term142 x s) = (term150 x s).
Proof. exact (MK_COMB (@lem5176107) (@lem5176106 x s)). Qed.
Lemma lem5176112 (n : real) (m : real) : (real_max m n) = (term10 n m).
Proof. exact (EQ_MP (@lem5175633 n m) (@lem5175632 n m)). Qed.
Lemma lem5176113 (s : real -> Prop) (x : real) : (term23 x s) = (term145 s x).
Proof. exact (@lem5176112 (sup s) x). Qed.
Lemma lem5176114 (x : real) : (real_le x) = (real_le x).
Proof. exact (eq_refl (real_le x)). Qed.
Lemma lem5176115 (s : real -> Prop) (x : real) : (term132 x s) = (term151 s x).
Proof. exact (MK_COMB (@lem5176114 x) (@lem5176113 s x)). Qed.
Lemma lem5176116 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5176117 (s : real -> Prop) (x : real) : (term134 x s) = (term152 s x).
Proof. exact (MK_COMB (@lem5176116) (@lem5176115 s x)). Qed.
Lemma lem5176125 (n : real) (m : real) : (real_max m n) = (term10 n m).
Proof. exact (EQ_MP (@lem5175633 n m) (@lem5175632 n m)). Qed.
Lemma lem5176126 (s : real -> Prop) (x : real) : (term23 x s) = (term145 s x).
Proof. exact (@lem5176125 (sup s) x). Qed.
Lemma lem5176127 (y : real) : (real_le y) = (real_le y).
Proof. exact (eq_refl (real_le y)). Qed.
Lemma lem5176128 (y : real) (s : real -> Prop) (x : real) : (term123 y x s) = (term153 y s x).
Proof. exact (MK_COMB (@lem5176127 y) (@lem5176126 s x)). Qed.
Lemma lem5176129 (y : real) (s : real -> Prop) : (term90 y s) = (term90 y s).
Proof. exact (eq_refl (term90 y s)). Qed.
Lemma lem5176130 (y : real) (s : real -> Prop) (x : real) : (term136 y x s) = (term154 y s x).
Proof. exact (MK_COMB (@lem5176129 y s) (@lem5176128 y s x)). Qed.
Lemma lem5176133 (s : real -> Prop) (x : real) : (term138 x s) = (term155 s x).
Proof. exact (fun_ext (fun y : real => @lem5176130 y s x)). Qed.
Lemma lem5176134 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5176135 (s : real -> Prop) (x : real) : (term140 x s) = (term156 s x).
Proof. exact (MK_COMB (@lem5176134) (@lem5176133 s x)). Qed.
Lemma lem5176140 (s : real -> Prop) (x : real) : (term141 x s) = (term157 s x).
Proof. exact (MK_COMB (@lem5176117 s x) (@lem5176135 s x)). Qed.
Lemma lem5176143 (s : real -> Prop) (x : real) : (term143 x s) = (term158 s x).
Proof. exact (MK_COMB (@lem5176108 x s) (@lem5176140 s x)). Qed.
Lemma lem5176146 (x : real) (s : real -> Prop) : (term158 s x) = (term143 x s).
Proof. exact (SYM (@lem5176143 s x)). Qed.
Lemma lem5176147 (_474 : real) (_475 : Prop) (_476 : real -> Prop) (_477 : real) : (term16 _476 _475 _474 _477) = (term17 _474 _475 _476 _477).
Proof. exact (@lem13473 real _474 _475 _476 _477). Qed.
Lemma lem5176148 (_474 : real) (_475 : Prop) (x : real) (s : real -> Prop) (_477 : real) : (term159 x s _475 _474 _477) = (term160 _474 _475 x s _477).
Proof. exact (@lem5176147 _474 _475 (term161 x s) _477). Qed.
Lemma lem5176149 (s : real -> Prop) (x : real) : (term162 s x) = (term163 s x).
Proof. exact (@lem5176148 (sup s) (term164 x s) x s x). Qed.
Lemma lem5176150 (s : real -> Prop) (x : real) : (term165 s x) = (term166 s x).
Proof. exact (eq_refl (term165 s x)). Qed.
Lemma lem5176151 (x : real) (s : real -> Prop) : (term167 x s) = (term167 x s).
Proof. exact (eq_refl (term167 x s)). Qed.
Lemma lem5176152 (s : real -> Prop) (x : real) : (term168 s x) = (term169 s x).
Proof. exact (MK_COMB (@lem5176151 x s) (@lem5176150 s x)). Qed.
Lemma lem5176153 (x : real) (s : real -> Prop) : (term170 x s) = (term171 x s).
Proof. exact (eq_refl (term170 x s)). Qed.
Lemma lem5176154 (x : real) (s : real -> Prop) : (term172 x s) = (term172 x s).
Proof. exact (eq_refl (term172 x s)). Qed.
Lemma lem5176155 (x : real) (s : real -> Prop) : (term173 x s) = (term174 x s).
Proof. exact (MK_COMB (@lem5176154 x s) (@lem5176153 x s)). Qed.
Lemma lem5176156 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5176157 (x : real) (s : real -> Prop) : (term175 x s) = (term176 x s).
Proof. exact (MK_COMB (@lem5176156) (@lem5176155 x s)). Qed.
Lemma lem5176158 (s : real -> Prop) (x : real) : (term163 s x) = (term177 s x).
Proof. exact (MK_COMB (@lem5176157 x s) (@lem5176152 s x)). Qed.
Lemma lem5176159 (s : real -> Prop) (x : real) : (term162 s x) = (term158 s x).
Proof. exact (eq_refl (term162 s x)). Qed.
Lemma lem5176160 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5176161 (s : real -> Prop) (x : real) : (term178 s x) = (term179 s x).
Proof. exact (MK_COMB (@lem5176160) (@lem5176159 s x)). Qed.
Lemma lem5176162 (s : real -> Prop) (x : real) : ((term162 s x) = (term163 s x)) = ((term158 s x) = (term177 s x)).
Proof. exact (MK_COMB (@lem5176161 s x) (@lem5176158 s x)). Qed.
Lemma lem5176163 (s : real -> Prop) (x : real) : (term158 s x) = (term177 s x).
Proof. exact (EQ_MP (@lem5176162 s x) (@lem5176149 s x)). Qed.
Lemma lem5176164 (s : real -> Prop) (x : real) : (term177 s x) = (term158 s x).
Proof. exact (SYM (@lem5176163 s x)). Qed.
Lemma lem5176165 (x : real) (s : real -> Prop) (h1 : term164 x s) : term164 x s.
Proof. exact (h1). Qed.
Lemma lem5176166 (x : real) (s : real -> Prop) : (term164 x s) = ((term164 x s) = True).
Proof. exact (@lem7 (term164 x s)). Qed.
Lemma lem5176167 (x : real) (s : real -> Prop) (h1 : term164 x s) : (term164 x s) = True.
Proof. exact (EQ_MP (@lem5176166 x s) (@lem5176165 x s h1)). Qed.
Lemma lem5176168 (x : real) (s : real -> Prop) : (term180 x s) = (term180 x s).
Proof. exact (eq_refl (term180 x s)). Qed.
Lemma lem5176169 (x : real) (s : real -> Prop) (h1 : term164 x s) : (term181 x s) = (term182 x s).
Proof. exact (MK_COMB (@lem5176168 x s) (@lem5176167 x s h1)). Qed.
Lemma lem5176170 (x : real) (s : real -> Prop) : (term182 x s) = (term183 x s).
Proof. exact (eq_refl (term182 x s)). Qed.
Lemma lem5176171 (x : real) (s : real -> Prop) : (term184 x s) = (term184 x s).
Proof. exact (eq_refl (term184 x s)). Qed.
Lemma lem5176172 (x : real) (s : real -> Prop) : ((term181 x s) = (term182 x s)) = ((term181 x s) = (term183 x s)).
Proof. exact (MK_COMB (@lem5176171 x s) (@lem5176170 x s)). Qed.
Lemma lem5176173 (x : real) (s : real -> Prop) : (term181 x s) = (term171 x s).
Proof. exact (eq_refl (term181 x s)). Qed.
Lemma lem5176174 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5176175 (x : real) (s : real -> Prop) : (term184 x s) = (term185 x s).
Proof. exact (MK_COMB (@lem5176174) (@lem5176173 x s)). Qed.
Lemma lem5176176 (x : real) (s : real -> Prop) : (term183 x s) = (term183 x s).
Proof. exact (eq_refl (term183 x s)). Qed.
Lemma lem5176177 (x : real) (s : real -> Prop) : ((term181 x s) = (term183 x s)) = ((term171 x s) = (term183 x s)).
Proof. exact (MK_COMB (@lem5176175 x s) (@lem5176176 x s)). Qed.
Lemma lem5176178 (x : real) (s : real -> Prop) : ((term181 x s) = (term182 x s)) = ((term171 x s) = (term183 x s)).
Proof. exact (TRANS (@lem5176172 x s) (@lem5176177 x s)). Qed.
Lemma lem5176179 (x : real) (s : real -> Prop) (h1 : term164 x s) : (term171 x s) = (term183 x s).
Proof. exact (EQ_MP (@lem5176178 x s) (@lem5176169 x s h1)). Qed.
Lemma lem5176180 (x : real) (s : real -> Prop) (h1 : term164 x s) : (term183 x s) = (term171 x s).
Proof. exact (SYM (@lem5176179 x s h1)). Qed.
Lemma lem5176181 (x : real) (s : real -> Prop) (h1 : term186 x s) : term186 x s.
Proof. exact (h1). Qed.
Lemma lem5176203 {A : Type'} (x : A) : term187 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem5176204 {A : Type'} (x : A) : (term187 A x) = (term188 A x).
Proof. exact (eq_refl (term187 A x)). Qed.
Lemma lem5176205 {A : Type'} (x : A) : term188 A x.
Proof. exact (EQ_MP (@lem5176204 A x) (@lem5176203 A x)). Qed.
Lemma lem5176206 {A : Type'} (x : A) (y : A) : term189 A x y.
Proof. exact (@lem5176205 A x y). Qed.
Lemma lem5176207 {A : Type'} (y : A) (x : A) : (term189 A x y) = (term190 A y x).
Proof. exact (eq_refl (term189 A x y)). Qed.
Lemma lem5176208 {A : Type'} (y : A) (x : A) : term190 A y x.
Proof. exact (EQ_MP (@lem5176207 A y x) (@lem5176206 A x y)). Qed.
Lemma lem5176209 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term191 A y x s.
Proof. exact (@lem5176208 A y x s). Qed.
Lemma lem5176210 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term191 A y x s) = ((term192 A x y s) = (term193 A y x s)).
Proof. exact (eq_refl (term191 A y x s)). Qed.
Lemma lem5176212 (s : real -> Prop) : term194 s.
Proof. exact (@lem5145274 s). Qed.
Lemma lem5176213 (s : real -> Prop) : (term194 s) = (term195 s).
Proof. exact (eq_refl (term194 s)). Qed.
Lemma lem5176214 (s : real -> Prop) : term195 s.
Proof. exact (EQ_MP (@lem5176213 s) (@lem5176212 s)). Qed.
Lemma lem5176215 (s : real -> Prop) (h1 : term61 s) : term61 s.
Proof. exact (h1). Qed.
Lemma lem5176216 (s : real -> Prop) (h1 : term61 s) : term196 s.
Proof. exact (@lem5176214 s (@lem5176215 s h1)). Qed.
Lemma lem5176217 (s : real -> Prop) (h1 : term61 s) : term197 s.
Proof. exact (proj2 (@lem5176216 s h1)). Qed.
Lemma lem5176218 (x : real) (s : real -> Prop) (h1 : term61 s) : term198 s x.
Proof. exact (@lem5176217 s h1 x). Qed.
Lemma lem5176219 (x : real) (s : real -> Prop) : (term198 s x) = (term199 x s).
Proof. exact (eq_refl (term198 s x)). Qed.
Lemma lem5176220 (x : real) (s : real -> Prop) (h1 : term61 s) : term199 x s.
Proof. exact (EQ_MP (@lem5176219 x s) (@lem5176218 x s h1)). Qed.
Lemma lem5176221 (x : real) (s : real -> Prop) (h1 : @IN real x s) : @IN real x s.
Proof. exact (h1). Qed.
Lemma lem5176222 (x : real) (s : real -> Prop) (h1 : term61 s) (h2 : @IN real x s) : term164 x s.
Proof. exact (@lem5176220 x s h1 (@lem5176221 x s h2)). Qed.
Lemma lem5176223 (x : real) (s : real -> Prop) : (term164 x s) = ((term164 x s) = True).
Proof. exact (@lem7 (term164 x s)). Qed.
Lemma lem5176224 (x : real) (s : real -> Prop) (h1 : term61 s) (h2 : @IN real x s) : (term164 x s) = True.
Proof. exact (EQ_MP (@lem5176223 x s) (@lem5176222 x s h1 h2)). Qed.
Lemma lem5176225 (x : real) (s : real -> Prop) (h1 : term61 s) : term200 x s.
Proof. exact (fun h0 : @IN real x s => @lem5176224 x s h1 h0). Qed.
Lemma lem5176226 (x : real) (s : real -> Prop) : term201 x s.
Proof. exact (fun h0 : term61 s => @lem5176225 x s h0). Qed.
Lemma lem5176228 (p : Prop) (q : Prop) (r : Prop) : (term202 p q r) = (term203 p q r).
Proof. exact (EQ_MP (@lem197 p q r) (@lem196 p q r)). Qed.
Lemma lem5176233 (x : real) (s : real -> Prop) : (term201 x s) = (term204 x s).
Proof. exact (@lem5176228 (term61 s) (@IN real x s) ((term164 x s) = True)). Qed.
Lemma lem5176235 (s : real -> Prop) (h1 : term61 s) : term205 s.
Proof. exact (proj1 (@lem5176216 s h1)). Qed.
Lemma lem5176236 (s : real -> Prop) : (term205 s) = ((term205 s) = True).
Proof. exact (@lem7 (term205 s)). Qed.
Lemma lem5176237 (s : real -> Prop) (h1 : term61 s) : (term205 s) = True.
Proof. exact (EQ_MP (@lem5176236 s) (@lem5176235 s h1)). Qed.
Lemma lem5176243 (s : real -> Prop) : (@FINITE real s) = ((@FINITE real s) = True).
Proof. exact (@lem7 (@FINITE real s)). Qed.
Lemma lem5176245 (s : real -> Prop) : term206 s.
Proof. exact (@lem82 (s = (@EMPTY real))). Qed.
Lemma lem5176265 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term192 A x y s) = (term193 A y x s).
Proof. exact (EQ_MP (@lem5176210 A y x s) (@lem5176209 A y x s)). Qed.
Lemma lem5176266 (y : real) (x : real) (s : real -> Prop) : (term207 x y s) = (term208 y x s).
Proof. exact (@lem5176265 real y x s). Qed.
Lemma lem5176267 (x : real) (s : real -> Prop) : (term209 x s) = (term210 x s).
Proof. exact (@lem5176266 x (sup s) s). Qed.
Lemma lem5176273 (s : real -> Prop) : term211 s.
Proof. exact (fun h0 : term61 s => @lem5176237 s h0). Qed.
Lemma lem5176277 (s : real -> Prop) (h1 : @FINITE real s) : (@FINITE real s) = True.
Proof. exact (EQ_MP (@lem5176243 s) (@lem5175646 s h1)). Qed.
Lemma lem5176278 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5176279 (s : real -> Prop) (h1 : @FINITE real s) : (term212 s) = (and True).
Proof. exact (MK_COMB (@lem5176278) (@lem5176277 s h1)). Qed.
Lemma lem5176281 (s : real -> Prop) (h1 : term39 s) : (s = (@EMPTY real)) = False.
Proof. exact (@lem5176245 s (@lem5175682 s h1)). Qed.
Lemma lem5176282 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5176283 (s : real -> Prop) (h1 : term39 s) : (term39 s) = (~ False).
Proof. exact (MK_COMB (@lem5176282) (@lem5176281 s h1)). Qed.
Lemma lem5176285 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem5176286 (s : real -> Prop) (h1 : term39 s) : (term39 s) = True.
Proof. exact (TRANS (@lem5176283 s h1) (@lem5176285)). Qed.
Lemma lem5176287 (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : (term61 s) = (True /\ True).
Proof. exact (MK_COMB (@lem5176279 s h1) (@lem5176286 s h2)). Qed.
Lemma lem5176289 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5176290 : (True /\ True) = True.
Proof. exact (@lem5176289 True). Qed.
Lemma lem5176291 (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : (term61 s) = True.
Proof. exact (TRANS (@lem5176287 s h1 h2) (@lem5176290)). Qed.
Lemma lem5176292 (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : True = (term61 s).
Proof. exact (SYM (@lem5176291 s h1 h2)). Qed.
Lemma lem5176293 (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : term61 s.
Proof. exact (EQ_MP (@lem5176292 s h1 h2) (@lem0)). Qed.
Lemma lem5176294 (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : (term205 s) = True.
Proof. exact (@lem5176273 s (@lem5176293 s h1 h2)). Qed.
Lemma lem5176295 (s : real -> Prop) (x : real) : (term213 s x) = (term213 s x).
Proof. exact (eq_refl (term213 s x)). Qed.
Lemma lem5176296 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : (term210 x s) = (term214 s x).
Proof. exact (MK_COMB (@lem5176295 s x) (@lem5176294 s h1 h2)). Qed.
Lemma lem5176298 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem5176299 (s : real -> Prop) (x : real) : (term214 s x) = True.
Proof. exact (@lem5176298 ((sup s) = x)). Qed.
Lemma lem5176300 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : (term210 x s) = True.
Proof. exact (TRANS (@lem5176296 x s h1 h2) (@lem5176299 s x)). Qed.
Lemma lem5176301 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : (term209 x s) = True.
Proof. exact (TRANS (@lem5176267 x s) (@lem5176300 x s h1 h2)). Qed.
Lemma lem5176302 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5176303 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : (term215 x s) = (and True).
Proof. exact (MK_COMB (@lem5176302) (@lem5176301 x s h1 h2)). Qed.
Lemma lem5176305 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5176306 (s : real -> Prop) : (term216 s) = (term197 s).
Proof. exact (@lem5176305 (term197 s)). Qed.
Lemma lem5176314 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term98 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5176315 (p : Prop) (q : Prop) (p' : Prop) : term99 p q p'.
Proof. exact (fun q' : Prop => @lem5176314 p q p' q'). Qed.
Lemma lem5176316 (p : Prop) (q : Prop) : term100 p q.
Proof. exact (fun p' : Prop => @lem5176315 p q p'). Qed.
Lemma lem5176317 (y : real) (s : real -> Prop) : term217 y s.
Proof. exact (@lem5176316 (@IN real y s) (term164 y s)). Qed.
Lemma lem5176318 (y : real) (s : real -> Prop) (p' : Prop) : term218 y s p'.
Proof. exact (@lem5176317 y s p'). Qed.
Lemma lem5176319 (y : real) (s : real -> Prop) (p' : Prop) : (term218 y s p') = (term219 y s p').
Proof. exact (eq_refl (term218 y s p')). Qed.
Lemma lem5176320 (y : real) (s : real -> Prop) (p' : Prop) : term219 y s p'.
Proof. exact (EQ_MP (@lem5176319 y s p') (@lem5176318 y s p')). Qed.
Lemma lem5176321 (y : real) (s : real -> Prop) (p' : Prop) (q' : Prop) : term220 y s p' q'.
Proof. exact (@lem5176320 y s p' q'). Qed.
Lemma lem5176322 (y : real) (s : real -> Prop) (p' : Prop) (q' : Prop) : (term220 y s p' q') = (term221 y s p' q').
Proof. exact (eq_refl (term220 y s p' q')). Qed.
Lemma lem5176323 (y : real) (s : real -> Prop) (p' : Prop) (q' : Prop) : term221 y s p' q'.
Proof. exact (EQ_MP (@lem5176322 y s p' q') (@lem5176321 y s p' q')). Qed.
Lemma lem5176324 (y : real) (s : real -> Prop) : (@IN real y s) = (@IN real y s).
Proof. exact (eq_refl (@IN real y s)). Qed.
Lemma lem5176325 (y : real) (s : real -> Prop) (q' : Prop) : term222 y s q'.
Proof. exact (@lem5176323 y s (@IN real y s) q'). Qed.
Lemma lem5176326 (y : real) (s : real -> Prop) (q' : Prop) : term223 y s q'.
Proof. exact (@lem5176325 y s q' (@lem5176324 y s)). Qed.
Lemma lem5176327 (y : real) (s : real -> Prop) (h1 : @IN real y s) : @IN real y s.
Proof. exact (h1). Qed.
Lemma lem5176328 (y : real) (s : real -> Prop) : (@IN real y s) = ((@IN real y s) = True).
Proof. exact (@lem7 (@IN real y s)). Qed.
Lemma lem5176331 (x : real) (s : real -> Prop) : term204 x s.
Proof. exact (EQ_MP (@lem5176233 x s) (@lem5176226 x s)). Qed.
Lemma lem5176332 (y : real) (s : real -> Prop) : term204 y s.
Proof. exact (@lem5176331 y s). Qed.
Lemma lem5176338 (s : real -> Prop) (h1 : @FINITE real s) : (@FINITE real s) = True.
Proof. exact (EQ_MP (@lem5176243 s) (@lem5175646 s h1)). Qed.
Lemma lem5176339 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5176340 (s : real -> Prop) (h1 : @FINITE real s) : (term212 s) = (and True).
Proof. exact (MK_COMB (@lem5176339) (@lem5176338 s h1)). Qed.
Lemma lem5176342 (s : real -> Prop) (h1 : term39 s) : (s = (@EMPTY real)) = False.
Proof. exact (@lem5176245 s (@lem5175682 s h1)). Qed.
Lemma lem5176343 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5176344 (s : real -> Prop) (h1 : term39 s) : (term39 s) = (~ False).
Proof. exact (MK_COMB (@lem5176343) (@lem5176342 s h1)). Qed.
Lemma lem5176346 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem5176347 (s : real -> Prop) (h1 : term39 s) : (term39 s) = True.
Proof. exact (TRANS (@lem5176344 s h1) (@lem5176346)). Qed.
Lemma lem5176348 (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : (term61 s) = (True /\ True).
Proof. exact (MK_COMB (@lem5176340 s h1) (@lem5176347 s h2)). Qed.
Lemma lem5176350 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5176351 : (True /\ True) = True.
Proof. exact (@lem5176350 True). Qed.
Lemma lem5176352 (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : (term61 s) = True.
Proof. exact (TRANS (@lem5176348 s h1 h2) (@lem5176351)). Qed.
Lemma lem5176353 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5176354 (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : (term224 s) = (and True).
Proof. exact (MK_COMB (@lem5176353) (@lem5176352 s h1 h2)). Qed.
Lemma lem5176356 (y : real) (s : real -> Prop) (h1 : @IN real y s) : (@IN real y s) = True.
Proof. exact (EQ_MP (@lem5176328 y s) (@lem5176327 y s h1)). Qed.
Lemma lem5176357 (y : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) (h3 : @IN real y s) : (term225 y s) = (True /\ True).
Proof. exact (MK_COMB (@lem5176354 s h1 h2) (@lem5176356 y s h3)). Qed.
Lemma lem5176359 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5176360 : (True /\ True) = True.
Proof. exact (@lem5176359 True). Qed.
Lemma lem5176361 (y : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) (h3 : @IN real y s) : (term225 y s) = True.
Proof. exact (TRANS (@lem5176357 y s h1 h2 h3) (@lem5176360)). Qed.
Lemma lem5176362 (y : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) (h3 : @IN real y s) : True = (term225 y s).
Proof. exact (SYM (@lem5176361 y s h1 h2 h3)). Qed.
Lemma lem5176363 (y : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) (h3 : @IN real y s) : term225 y s.
Proof. exact (EQ_MP (@lem5176362 y s h1 h2 h3) (@lem0)). Qed.
Lemma lem5176364 (y : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) (h3 : @IN real y s) : (term164 y s) = True.
Proof. exact (@lem5176332 y s (@lem5176363 y s h1 h2 h3)). Qed.
Lemma lem5176365 (y : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : term200 y s.
Proof. exact (fun h0 : @IN real y s => @lem5176364 y s h1 h2 h0). Qed.
Lemma lem5176366 (y : real) (s : real -> Prop) : term226 y s.
Proof. exact (@lem5176326 y s True). Qed.
Lemma lem5176367 (y : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : (term199 y s) = (term227 y s).
Proof. exact (@lem5176366 y s (@lem5176365 y s h1 h2)). Qed.
Lemma lem5176369 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem5176370 (y : real) (s : real -> Prop) : (term227 y s) = True.
Proof. exact (@lem5176369 (@IN real y s)). Qed.
Lemma lem5176371 (y : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : (term199 y s) = True.
Proof. exact (TRANS (@lem5176367 y s h1 h2) (@lem5176370 y s)). Qed.
Lemma lem5176372 (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : (term228 s) = term111.
Proof. exact (fun_ext (fun y : real => @lem5176371 y s h1 h2)). Qed.
Lemma lem5176373 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5176374 (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : (term197 s) = term112.
Proof. exact (MK_COMB (@lem5176373) (@lem5176372 s h1 h2)). Qed.
Lemma lem5176376 {A : Type'} (t : Prop) : (term113 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5176377 (t : Prop) : (term114 t) = t.
Proof. exact (@lem5176376 real t). Qed.
Lemma lem5176378 : term112 = True.
Proof. exact (@lem5176377 True). Qed.
Lemma lem5176379 (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : (term197 s) = True.
Proof. exact (TRANS (@lem5176374 s h1 h2) (@lem5176378)). Qed.
Lemma lem5176380 (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : (term216 s) = True.
Proof. exact (TRANS (@lem5176306 s) (@lem5176379 s h1 h2)). Qed.
Lemma lem5176381 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : (term183 x s) = (True /\ True).
Proof. exact (MK_COMB (@lem5176303 x s h1 h2) (@lem5176380 s h1 h2)). Qed.
Lemma lem5176383 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5176384 : (True /\ True) = True.
Proof. exact (@lem5176383 True). Qed.
Lemma lem5176385 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : (term183 x s) = True.
Proof. exact (TRANS (@lem5176381 x s h1 h2) (@lem5176384)). Qed.
Lemma lem5176386 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : True = (term183 x s).
Proof. exact (SYM (@lem5176385 x s h1 h2)). Qed.
Lemma lem5176387 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : term183 x s.
Proof. exact (EQ_MP (@lem5176386 x s h1 h2) (@lem0)). Qed.
Lemma lem5176388 (x : real) : term11 x.
Proof. exact (@lem1339240 x). Qed.
Lemma lem5176389 (x : real) : (term11 x) = (real_le x x).
Proof. exact (eq_refl (term11 x)). Qed.
Lemma lem5176390 (x : real) : real_le x x.
Proof. exact (EQ_MP (@lem5176389 x) (@lem5176388 x)). Qed.
Lemma lem5176391 (x : real) : (real_le x x) = ((real_le x x) = True).
Proof. exact (@lem7 (real_le x x)). Qed.
Lemma lem5176393 {A : Type'} (x : A) : term187 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem5176394 {A : Type'} (x : A) : (term187 A x) = (term188 A x).
Proof. exact (eq_refl (term187 A x)). Qed.
Lemma lem5176395 {A : Type'} (x : A) : term188 A x.
Proof. exact (EQ_MP (@lem5176394 A x) (@lem5176393 A x)). Qed.
Lemma lem5176396 {A : Type'} (x : A) (y : A) : term189 A x y.
Proof. exact (@lem5176395 A x y). Qed.
Lemma lem5176397 {A : Type'} (y : A) (x : A) : (term189 A x y) = (term190 A y x).
Proof. exact (eq_refl (term189 A x y)). Qed.
Lemma lem5176398 {A : Type'} (y : A) (x : A) : term190 A y x.
Proof. exact (EQ_MP (@lem5176397 A y x) (@lem5176396 A x y)). Qed.
Lemma lem5176399 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term191 A y x s.
Proof. exact (@lem5176398 A y x s). Qed.
Lemma lem5176400 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term191 A y x s) = ((term192 A x y s) = (term193 A y x s)).
Proof. exact (eq_refl (term191 A y x s)). Qed.
Lemma lem5176453 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term192 A x y s) = (term193 A y x s).
Proof. exact (EQ_MP (@lem5176400 A y x s) (@lem5176399 A y x s)). Qed.
Lemma lem5176454 (y : real) (x : real) (s : real -> Prop) : (term207 x y s) = (term208 y x s).
Proof. exact (@lem5176453 real y x s). Qed.
Lemma lem5176455 (x : real) (s : real -> Prop) : (term69 x s) = (term229 x s).
Proof. exact (@lem5176454 x x s). Qed.
Lemma lem5176459 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5176460 (x : real) : (x = x) = True.
Proof. exact (@lem5176459 real x). Qed.
Lemma lem5176461 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5176462 (x : real) : (term230 x) = (or True).
Proof. exact (MK_COMB (@lem5176461) (@lem5176460 x)). Qed.
Lemma lem5176463 (x : real) (s : real -> Prop) : (@IN real x s) = (@IN real x s).
Proof. exact (eq_refl (@IN real x s)). Qed.
Lemma lem5176464 (x : real) (s : real -> Prop) : (term229 x s) = (term231 x s).
Proof. exact (MK_COMB (@lem5176462 x) (@lem5176463 x s)). Qed.
Lemma lem5176466 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem5176467 (x : real) (s : real -> Prop) : (term231 x s) = True.
Proof. exact (@lem5176466 (@IN real x s)). Qed.
Lemma lem5176468 (x : real) (s : real -> Prop) : (term229 x s) = True.
Proof. exact (TRANS (@lem5176464 x s) (@lem5176467 x s)). Qed.
Lemma lem5176469 (x : real) (s : real -> Prop) : (term69 x s) = True.
Proof. exact (TRANS (@lem5176455 x s) (@lem5176468 x s)). Qed.
Lemma lem5176470 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5176471 (x : real) (s : real -> Prop) : (term71 x s) = (and True).
Proof. exact (MK_COMB (@lem5176470) (@lem5176469 x s)). Qed.
Lemma lem5176475 (x : real) : (real_le x x) = True.
Proof. exact (EQ_MP (@lem5176391 x) (@lem5176390 x)). Qed.
Lemma lem5176476 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5176477 (x : real) : (term89 x) = (and True).
Proof. exact (MK_COMB (@lem5176476) (@lem5176475 x)). Qed.
Lemma lem5176509 (s : real -> Prop) (x : real) : (term96 s x) = (term96 s x).
Proof. exact (eq_refl (term96 s x)). Qed.
Lemma lem5176510 (s : real -> Prop) (x : real) : (term97 s x) = (term232 s x).
Proof. exact (MK_COMB (@lem5176477 x) (@lem5176509 s x)). Qed.
Lemma lem5176512 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5176513 (s : real -> Prop) (x : real) : (term232 s x) = (term96 s x).
Proof. exact (@lem5176512 (term96 s x)). Qed.
Lemma lem5176545 (s : real -> Prop) (x : real) : (term97 s x) = (term96 s x).
Proof. exact (TRANS (@lem5176510 s x) (@lem5176513 s x)). Qed.
Lemma lem5176546 (s : real -> Prop) (x : real) : (term166 s x) = (term232 s x).
Proof. exact (MK_COMB (@lem5176471 x s) (@lem5176545 s x)). Qed.
Lemma lem5176548 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5176549 (s : real -> Prop) (x : real) : (term232 s x) = (term96 s x).
Proof. exact (@lem5176548 (term96 s x)). Qed.
Lemma lem5176581 (s : real -> Prop) (x : real) : (term166 s x) = (term96 s x).
Proof. exact (TRANS (@lem5176546 s x) (@lem5176549 s x)). Qed.
Lemma lem5176582 (s : real -> Prop) (x : real) : (term96 s x) = (term166 s x).
Proof. exact (SYM (@lem5176581 s x)). Qed.
Lemma lem5176584 (p : Prop) : p = (term233 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5176585 (s : real -> Prop) (x : real) : (term96 s x) = (term234 s x).
Proof. exact (@lem5176584 (term96 s x)). Qed.
Lemma lem5176586 (s : real -> Prop) (x : real) : (term234 s x) = (term96 s x).
Proof. exact (SYM (@lem5176585 s x)). Qed.
Lemma lem5176587 (s : real -> Prop) (x : real) (h1 : term235 s x) : term235 s x.
Proof. exact (h1). Qed.
Lemma lem5176590 (s : real -> Prop) (x : real) (h1 : term236 s x) : term236 s x.
Proof. exact (h1). Qed.
Lemma lem5176591 (s : real -> Prop) (x : real) : term237 s x.
Proof. exact (fun h0 : term236 s x => @lem5176590 s x h0). Qed.
Lemma lem5176592 (s : real -> Prop) (x : real) (h1 : term237 s x) : term237 s x.
Proof. exact (h1). Qed.
Lemma lem5176593 (s : real -> Prop) (x : real) (h1 : term236 s x) : term236 s x.
Proof. exact (h1). Qed.
Lemma lem5176594 (s : real -> Prop) (x : real) (h1 : term236 s x) (h2 : term237 s x) : term236 s x.
Proof. exact (@lem5176592 s x h2 (@lem5176593 s x h1)). Qed.
Lemma lem5176595 (s : real -> Prop) (x : real) (h1 : term236 s x) : term238 s x.
Proof. exact (fun h0 : term237 s x => @lem5176594 s x h1 h0). Qed.
Lemma lem5176596 (s : real -> Prop) (x : real) (h1 : term237 s x) : term237 s x.
Proof. exact (h1). Qed.
Lemma lem5176597 (s : real -> Prop) (x : real) (h1 : term236 s x) (h2 : term237 s x) : term236 s x.
Proof. exact (@lem5176595 s x h1 (@lem5176596 s x h2)). Qed.
Lemma lem5176598 (s : real -> Prop) (x : real) (h1 : term237 s x) : term237 s x.
Proof. exact (fun h0 : term236 s x => @lem5176597 s x h0 h1). Qed.
Lemma lem5176599 (s : real -> Prop) (x : real) : term239 s x.
Proof. exact (fun h0 : term237 s x => @lem5176598 s x h0). Qed.
Lemma lem5176602 (s : real -> Prop) (x : real) : term237 s x.
Proof. exact (@lem5176599 s x (@lem5176591 s x)). Qed.
Lemma lem5176700 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5176701 : term240 = term241.
Proof. exact (@lem5176700 term242). Qed.
Lemma lem5176718 : term243 = term243.
Proof. exact (eq_refl term243). Qed.
Lemma lem5176719 : term244 = term245.
Proof. exact (MK_COMB (@lem5176718) (@lem5176701)). Qed.
Lemma lem5176722 : term246 = term246.
Proof. exact (eq_refl term246). Qed.
Lemma lem5176723 : term247 = term248.
Proof. exact (MK_COMB (@lem5176722) (@lem5176719)). Qed.
Lemma lem5176726 (s : real -> Prop) (x : real) : (term249 s x) = (term249 s x).
Proof. exact (eq_refl (term249 s x)). Qed.
Lemma lem5176727 (s : real -> Prop) (x : real) : (term250 s x) = (term251 s x).
Proof. exact (MK_COMB (@lem5176726 s x) (@lem5176723)). Qed.
Lemma lem5176730 (x : real) (s : real -> Prop) : (term167 x s) = (term167 x s).
Proof. exact (eq_refl (term167 x s)). Qed.
Lemma lem5176731 (s : real -> Prop) (x : real) : (term252 s x) = (term253 s x).
Proof. exact (MK_COMB (@lem5176730 x s) (@lem5176727 s x)). Qed.
Lemma lem5176734 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5176735 (s : real -> Prop) (x : real) : (term254 s x) = (term255 s x).
Proof. exact (MK_COMB (@lem5176734 s) (@lem5176731 s x)). Qed.
Lemma lem5176738 (s : real -> Prop) : (term256 s) = (term256 s).
Proof. exact (eq_refl (term256 s)). Qed.
Lemma lem5176739 (s : real -> Prop) (x : real) : (term236 s x) = (term257 s x).
Proof. exact (MK_COMB (@lem5176738 s) (@lem5176735 s x)). Qed.
Lemma lem5176742 (x : real) : (term258 x) = (term259 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5176739 s x)). Qed.
Lemma lem5176743 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5176744 (x : real) : (term260 x) = (term261 x).
Proof. exact (MK_COMB (@lem5176743) (@lem5176742 x)). Qed.
Lemma lem5176749 : term262 = term263.
Proof. exact (fun_ext (fun x : real => @lem5176744 x)). Qed.
Lemma lem5176750 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5176759 : term264 = term265.
Proof. exact (MK_COMB (@lem5176750) (@lem5176749)). Qed.
Lemma lem5176764 (x : real) (s : real -> Prop) : (term199 x s) = (term199 x s).
Proof. exact (eq_refl (term199 x s)). Qed.
Lemma lem5176765 (s : real -> Prop) : (term228 s) = (term228 s).
Proof. exact (fun_ext (fun x : real => @lem5176764 x s)). Qed.
Lemma lem5176766 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5176767 (s : real -> Prop) : (term197 s) = (term197 s).
Proof. exact (MK_COMB (@lem5176766) (@lem5176765 s)). Qed.
Lemma lem5176770 (s : real -> Prop) : (term266 s) = (term266 s).
Proof. exact (eq_refl (term266 s)). Qed.
Lemma lem5176771 (s : real -> Prop) : (term196 s) = (term196 s).
Proof. exact (MK_COMB (@lem5176770 s) (@lem5176767 s)). Qed.
Lemma lem5176780 (s : real -> Prop) : (term267 s) = (term267 s).
Proof. exact (eq_refl (term267 s)). Qed.
Lemma lem5176781 (s : real -> Prop) : (term195 s) = (term195 s).
Proof. exact (MK_COMB (@lem5176780 s) (@lem5176771 s)). Qed.
Lemma lem5176782 : term268 = term268.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5176781 s)). Qed.
Lemma lem5176783 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5176784 : term242 = term242.
Proof. exact (MK_COMB (@lem5176783) (@lem5176782)). Qed.
Lemma lem5176785 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5176786 : term241 = term241.
Proof. exact (MK_COMB (@lem5176785) (@lem5176784)). Qed.
Lemma lem5176791 (y : real) (x : real) : (term269 y x) = (term269 y x).
Proof. exact (eq_refl (term269 y x)). Qed.
Lemma lem5176792 (x : real) : (term270 x) = (term270 x).
Proof. exact (fun_ext (fun y : real => @lem5176791 y x)). Qed.
Lemma lem5176793 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5176794 (x : real) : (term271 x) = (term271 x).
Proof. exact (MK_COMB (@lem5176793) (@lem5176792 x)). Qed.
Lemma lem5176795 : term272 = term272.
Proof. exact (fun_ext (fun x : real => @lem5176794 x)). Qed.
Lemma lem5176796 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5176797 : term273 = term273.
Proof. exact (MK_COMB (@lem5176796) (@lem5176795)). Qed.
Lemma lem5176798 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5176799 : term243 = term243.
Proof. exact (MK_COMB (@lem5176798) (@lem5176797)). Qed.
Lemma lem5176800 : term245 = term245.
Proof. exact (MK_COMB (@lem5176799) (@lem5176786)). Qed.
Lemma lem5176809 (y : real) (x : real) (z : real) : (term274 y x z) = (term274 y x z).
Proof. exact (eq_refl (term274 y x z)). Qed.
Lemma lem5176810 (y : real) (x : real) : (term275 y x) = (term275 y x).
Proof. exact (fun_ext (fun z : real => @lem5176809 y x z)). Qed.
Lemma lem5176811 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5176812 (y : real) (x : real) : (term276 y x) = (term276 y x).
Proof. exact (MK_COMB (@lem5176811) (@lem5176810 y x)). Qed.
Lemma lem5176813 (x : real) : (term277 x) = (term277 x).
Proof. exact (fun_ext (fun y : real => @lem5176812 y x)). Qed.
Lemma lem5176814 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5176815 (x : real) : (term278 x) = (term278 x).
Proof. exact (MK_COMB (@lem5176814) (@lem5176813 x)). Qed.
Lemma lem5176816 : term279 = term279.
Proof. exact (fun_ext (fun x : real => @lem5176815 x)). Qed.
Lemma lem5176817 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5176818 : term280 = term280.
Proof. exact (MK_COMB (@lem5176817) (@lem5176816)). Qed.
Lemma lem5176819 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5176820 : term246 = term246.
Proof. exact (MK_COMB (@lem5176819) (@lem5176818)). Qed.
Lemma lem5176821 : term248 = term248.
Proof. exact (MK_COMB (@lem5176820) (@lem5176800)). Qed.
Lemma lem5176826 (s : real -> Prop) (y : real) (x : real) : (term92 s y x) = (term92 s y x).
Proof. exact (eq_refl (term92 s y x)). Qed.
Lemma lem5176827 (s : real -> Prop) (x : real) : (term94 s x) = (term94 s x).
Proof. exact (fun_ext (fun y : real => @lem5176826 s y x)). Qed.
Lemma lem5176828 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5176829 (s : real -> Prop) (x : real) : (term96 s x) = (term96 s x).
Proof. exact (MK_COMB (@lem5176828) (@lem5176827 s x)). Qed.
Lemma lem5176830 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5176831 (s : real -> Prop) (x : real) : (term235 s x) = (term235 s x).
Proof. exact (MK_COMB (@lem5176830) (@lem5176829 s x)). Qed.
Lemma lem5176832 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5176833 (s : real -> Prop) (x : real) : (term249 s x) = (term249 s x).
Proof. exact (MK_COMB (@lem5176832) (@lem5176831 s x)). Qed.
Lemma lem5176834 (s : real -> Prop) (x : real) : (term251 s x) = (term251 s x).
Proof. exact (MK_COMB (@lem5176833 s x) (@lem5176821)). Qed.
Lemma lem5176839 (x : real) (s : real -> Prop) : (term167 x s) = (term167 x s).
Proof. exact (eq_refl (term167 x s)). Qed.
Lemma lem5176840 (s : real -> Prop) (x : real) : (term253 s x) = (term253 s x).
Proof. exact (MK_COMB (@lem5176839 x s) (@lem5176834 s x)). Qed.
Lemma lem5176845 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5176846 (s : real -> Prop) (x : real) : (term255 s x) = (term255 s x).
Proof. exact (MK_COMB (@lem5176845 s) (@lem5176840 s x)). Qed.
Lemma lem5176849 (s : real -> Prop) : (term256 s) = (term256 s).
Proof. exact (eq_refl (term256 s)). Qed.
Lemma lem5176850 (s : real -> Prop) (x : real) : (term257 s x) = (term257 s x).
Proof. exact (MK_COMB (@lem5176849 s) (@lem5176846 s x)). Qed.
Lemma lem5176851 (x : real) : (term259 x) = (term259 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5176850 s x)). Qed.
Lemma lem5176852 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5176853 (x : real) : (term261 x) = (term261 x).
Proof. exact (MK_COMB (@lem5176852) (@lem5176851 x)). Qed.
Lemma lem5176854 : term263 = term263.
Proof. exact (fun_ext (fun x : real => @lem5176853 x)). Qed.
Lemma lem5176855 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5176856 : term265 = term265.
Proof. exact (MK_COMB (@lem5176855) (@lem5176854)). Qed.
Lemma lem5176947 : term264 = term265.
Proof. exact (TRANS (@lem5176759) (@lem5176856)). Qed.
Lemma lem5176948 : term265 = term264.
Proof. exact (SYM (@lem5176947)). Qed.
Lemma lem5176952 (s : real -> Prop) (x : real) (h1 : term235 s x) : term235 s x.
Proof. exact (h1). Qed.
Lemma lem5176953 (h1 : term280) : term280.
Proof. exact (h1). Qed.
Lemma lem5176954 (h1 : term273) : term273.
Proof. exact (h1). Qed.
Lemma lem5176955 (h1 : term242) : term242.
Proof. exact (h1). Qed.
Lemma lem5176961 (s : real -> Prop) (h1 : @FINITE real s) : @FINITE real s.
Proof. exact (h1). Qed.
Lemma lem5176967 (s : real -> Prop) (h1 : term39 s) : term39 s.
Proof. exact (h1). Qed.
Lemma lem5176973 (x : real) (s : real -> Prop) (h1 : term186 x s) : term186 x s.
Proof. exact (h1). Qed.
Lemma lem5176980 (s : real -> Prop) (y : real) (x : real) : (term281 s y x) = (term282 s y x).
Proof. exact (@lem17362 (@IN real y s) (real_le y x)). Qed.
Lemma lem5176981 (P : real -> Prop) : (term283 P) = (term284 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5176982 (s : real -> Prop) (x : real) : (term235 s x) = (term285 s x).
Proof. exact (@lem5176981 (term94 s x)). Qed.
Lemma lem5176983 (s : real -> Prop) (y : real) (x : real) : (term286 s x y) = (term92 s y x).
Proof. exact (eq_refl (term286 s x y)). Qed.
Lemma lem5176984 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5176985 (s : real -> Prop) (y : real) (x : real) : (term287 s x y) = (term281 s y x).
Proof. exact (MK_COMB (@lem5176984) (@lem5176983 s y x)). Qed.
Lemma lem5176986 (s : real -> Prop) (y : real) (x : real) : (term287 s x y) = (term282 s y x).
Proof. exact (TRANS (@lem5176985 s y x) (@lem5176980 s y x)). Qed.
Lemma lem5176987 (s : real -> Prop) (x : real) : (term288 s x) = (term289 s x).
Proof. exact (fun_ext (fun y : real => @lem5176986 s y x)). Qed.
Lemma lem5176988 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5176989 (s : real -> Prop) (x : real) : (term285 s x) = (term290 s x).
Proof. exact (MK_COMB (@lem5176988) (@lem5176987 s x)). Qed.
Lemma lem5177042 (s : real -> Prop) (x : real) : (term235 s x) = (term290 s x).
Proof. exact (TRANS (@lem5176982 s x) (@lem5176989 s x)). Qed.
Lemma lem5177043 (s : real -> Prop) (x : real) (h1 : term235 s x) : term290 s x.
Proof. exact (EQ_MP (@lem5177042 s x) (@lem5176952 s x h1)). Qed.
Lemma lem5177050 (x : real) (y : real) (z : real) : (term291 x y z) = (term292 x y z).
Proof. exact (@lem17045 (real_le x y) (real_le y z)). Qed.
Lemma lem5177051 (x : real) (z : real) : (real_le x z) = (real_le x z).
Proof. exact (eq_refl (real_le x z)). Qed.
Lemma lem5177052 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5177053 (x : real) (y : real) (z : real) : (term293 x y z) = (term294 x y z).
Proof. exact (MK_COMB (@lem5177052) (@lem5177050 x y z)). Qed.
Lemma lem5177054 (y : real) (x : real) (z : real) : (term295 y x z) = (term296 y x z).
Proof. exact (MK_COMB (@lem5177053 x y z) (@lem5177051 x z)). Qed.
Lemma lem5177055 (y : real) (x : real) (z : real) : (term274 y x z) = (term295 y x z).
Proof. exact (@lem17265 (term297 x y z) (real_le x z)). Qed.
Lemma lem5177056 (y : real) (x : real) (z : real) : (term274 y x z) = (term296 y x z).
Proof. exact (TRANS (@lem5177055 y x z) (@lem5177054 y x z)). Qed.
Lemma lem5177057 (y : real) (x : real) : (term275 y x) = (term298 y x).
Proof. exact (fun_ext (fun z : real => @lem5177056 y x z)). Qed.
Lemma lem5177058 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5177059 (y : real) (x : real) : (term276 y x) = (term299 y x).
Proof. exact (MK_COMB (@lem5177058) (@lem5177057 y x)). Qed.
Lemma lem5177060 (x : real) : (term277 x) = (term300 x).
Proof. exact (fun_ext (fun y : real => @lem5177059 y x)). Qed.
Lemma lem5177061 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5177062 (x : real) : (term278 x) = (term301 x).
Proof. exact (MK_COMB (@lem5177061) (@lem5177060 x)). Qed.
Lemma lem5177063 : term279 = term302.
Proof. exact (fun_ext (fun x : real => @lem5177062 x)). Qed.
Lemma lem5177064 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5177125 : term280 = term303.
Proof. exact (MK_COMB (@lem5177064) (@lem5177063)). Qed.
Lemma lem5177126 (h1 : term280) : term303.
Proof. exact (EQ_MP (@lem5177125) (@lem5176953 h1)). Qed.
Lemma lem5177131 (y : real) (x : real) : (term269 y x) = (term269 y x).
Proof. exact (eq_refl (term269 y x)). Qed.
Lemma lem5177132 (x : real) : (term270 x) = (term270 x).
Proof. exact (fun_ext (fun y : real => @lem5177131 y x)). Qed.
Lemma lem5177133 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5177134 (x : real) : (term271 x) = (term271 x).
Proof. exact (MK_COMB (@lem5177133) (@lem5177132 x)). Qed.
Lemma lem5177135 : term272 = term272.
Proof. exact (fun_ext (fun x : real => @lem5177134 x)). Qed.
Lemma lem5177136 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5177193 : term273 = term273.
Proof. exact (MK_COMB (@lem5177136) (@lem5177135)). Qed.
Lemma lem5177194 (h1 : term273) : term273.
Proof. exact (EQ_MP (@lem5177193) (@lem5176954 h1)). Qed.
Lemma lem5177198 (s : real -> Prop) : (term304 s) = (s = (@EMPTY real)).
Proof. exact (@lem16933 (s = (@EMPTY real))). Qed.
Lemma lem5177200 (s : real -> Prop) : (term305 s) = (term305 s).
Proof. exact (eq_refl (term305 s)). Qed.
Lemma lem5177201 (s : real -> Prop) : (term306 s) = (term307 s).
Proof. exact (MK_COMB (@lem5177200 s) (@lem5177198 s)). Qed.
Lemma lem5177202 (s : real -> Prop) : (term308 s) = (term306 s).
Proof. exact (@lem17045 (@FINITE real s) (term39 s)). Qed.
Lemma lem5177203 (s : real -> Prop) : (term308 s) = (term307 s).
Proof. exact (TRANS (@lem5177202 s) (@lem5177201 s)). Qed.
Lemma lem5177211 (x : real) (s : real -> Prop) : (term199 x s) = (term309 x s).
Proof. exact (@lem17265 (@IN real x s) (term164 x s)). Qed.
Lemma lem5177212 (s : real -> Prop) : (term228 s) = (term310 s).
Proof. exact (fun_ext (fun x : real => @lem5177211 x s)). Qed.
Lemma lem5177213 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5177214 (s : real -> Prop) : (term197 s) = (term311 s).
Proof. exact (MK_COMB (@lem5177213) (@lem5177212 s)). Qed.
Lemma lem5177216 (s : real -> Prop) : (term266 s) = (term266 s).
Proof. exact (eq_refl (term266 s)). Qed.
Lemma lem5177217 (s : real -> Prop) : (term196 s) = (term312 s).
Proof. exact (MK_COMB (@lem5177216 s) (@lem5177214 s)). Qed.
Lemma lem5177218 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5177219 (s : real -> Prop) : (term313 s) = (term314 s).
Proof. exact (MK_COMB (@lem5177218) (@lem5177203 s)). Qed.
Lemma lem5177220 (s : real -> Prop) : (term315 s) = (term316 s).
Proof. exact (MK_COMB (@lem5177219 s) (@lem5177217 s)). Qed.
Lemma lem5177221 (s : real -> Prop) : (term195 s) = (term315 s).
Proof. exact (@lem17265 (term61 s) (term196 s)). Qed.
Lemma lem5177222 (s : real -> Prop) : (term195 s) = (term316 s).
Proof. exact (TRANS (@lem5177221 s) (@lem5177220 s)). Qed.
Lemma lem5177223 : term268 = term317.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5177222 s)). Qed.
Lemma lem5177224 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5177325 : term242 = term318.
Proof. exact (MK_COMB (@lem5177224) (@lem5177223)). Qed.
Lemma lem5177326 (h1 : term242) : term318.
Proof. exact (EQ_MP (@lem5177325) (@lem5176955 h1)). Qed.
Lemma lem5177331 (s : real -> Prop) (h1 : @FINITE real s) : @FINITE real s.
Proof. exact (h1). Qed.
Lemma lem5177339 (s : real -> Prop) (h1 : term39 s) : term39 s.
Proof. exact (h1). Qed.
Lemma lem5177349 (x : real) (s : real -> Prop) (h1 : term186 x s) : term186 x s.
Proof. exact (h1). Qed.
Lemma lem5177374 (y : real) (x : real) (z : real) : (term296 y x z) = (term296 y x z).
Proof. exact (eq_refl (term296 y x z)). Qed.
Lemma lem5177375 (y : real) (x : real) : (term298 y x) = (term298 y x).
Proof. exact (fun_ext (fun z : real => @lem5177374 y x z)). Qed.
Lemma lem5177376 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5177377 (y : real) (x : real) : (term299 y x) = (term299 y x).
Proof. exact (MK_COMB (@lem5177376) (@lem5177375 y x)). Qed.
Lemma lem5177378 (x : real) : (term300 x) = (term300 x).
Proof. exact (fun_ext (fun y : real => @lem5177377 y x)). Qed.
Lemma lem5177379 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5177380 (x : real) : (term301 x) = (term301 x).
Proof. exact (MK_COMB (@lem5177379) (@lem5177378 x)). Qed.
Lemma lem5177381 : term302 = term302.
Proof. exact (fun_ext (fun x : real => @lem5177380 x)). Qed.
Lemma lem5177382 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5177383 : term303 = term303.
Proof. exact (MK_COMB (@lem5177382) (@lem5177381)). Qed.
Lemma lem5177384 (h1 : term280) : term303.
Proof. exact (EQ_MP (@lem5177383) (@lem5177126 h1)). Qed.
Lemma lem5177397 (y : real) (x : real) : (term269 y x) = (term269 y x).
Proof. exact (eq_refl (term269 y x)). Qed.
Lemma lem5177398 (x : real) : (term270 x) = (term270 x).
Proof. exact (fun_ext (fun y : real => @lem5177397 y x)). Qed.
Lemma lem5177399 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5177400 (x : real) : (term271 x) = (term271 x).
Proof. exact (MK_COMB (@lem5177399) (@lem5177398 x)). Qed.
Lemma lem5177401 : term272 = term272.
Proof. exact (fun_ext (fun x : real => @lem5177400 x)). Qed.
Lemma lem5177402 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5177403 : term273 = term273.
Proof. exact (MK_COMB (@lem5177402) (@lem5177401)). Qed.
Lemma lem5177404 (h1 : term273) : term273.
Proof. exact (EQ_MP (@lem5177403) (@lem5177194 h1)). Qed.
Lemma lem5177421 (x : real) (s : real -> Prop) : (term309 x s) = (term309 x s).
Proof. exact (eq_refl (term309 x s)). Qed.
Lemma lem5177422 (s : real -> Prop) : (term310 s) = (term310 s).
Proof. exact (fun_ext (fun x : real => @lem5177421 x s)). Qed.
Lemma lem5177423 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5177424 (s : real -> Prop) : (term311 s) = (term311 s).
Proof. exact (MK_COMB (@lem5177423) (@lem5177422 s)). Qed.
Lemma lem5177433 (s : real -> Prop) : (term266 s) = (term266 s).
Proof. exact (eq_refl (term266 s)). Qed.
Lemma lem5177434 (s : real -> Prop) : (term312 s) = (term312 s).
Proof. exact (MK_COMB (@lem5177433 s) (@lem5177424 s)). Qed.
Lemma lem5177449 (s : real -> Prop) : (term314 s) = (term314 s).
Proof. exact (eq_refl (term314 s)). Qed.
Lemma lem5177450 (s : real -> Prop) : (term316 s) = (term316 s).
Proof. exact (MK_COMB (@lem5177449 s) (@lem5177434 s)). Qed.
Lemma lem5177451 : term317 = term317.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5177450 s)). Qed.
Lemma lem5177452 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5177453 : term318 = term318.
Proof. exact (MK_COMB (@lem5177452) (@lem5177451)). Qed.
Lemma lem5177454 (h1 : term242) : term318.
Proof. exact (EQ_MP (@lem5177453) (@lem5177326 h1)). Qed.
Lemma lem5177470 (s : real -> Prop) (y : real) (x : real) (h1 : term282 s y x) : term282 s y x.
Proof. exact (h1). Qed.
Lemma lem5177476 (s : real -> Prop) (h1 : @FINITE real s) : @FINITE real s.
Proof. exact (h1). Qed.
Lemma lem5177480 (s : real -> Prop) (h1 : term39 s) : term39 s.
Proof. exact (h1). Qed.
Lemma lem5177484 (x : real) (s : real -> Prop) (h1 : term186 x s) : term186 x s.
Proof. exact (h1). Qed.
Lemma lem5177498 (y : real) (x : real) (z : real) : (term296 y x z) = (term296 y x z).
Proof. exact (eq_refl (term296 y x z)). Qed.
Lemma lem5177499 (y : real) (x : real) : (term298 y x) = (term298 y x).
Proof. exact (fun_ext (fun z : real => @lem5177498 y x z)). Qed.
Lemma lem5177500 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5177501 (y : real) (x : real) : (term299 y x) = (term299 y x).
Proof. exact (MK_COMB (@lem5177500) (@lem5177499 y x)). Qed.
Lemma lem5177502 (x : real) : (term300 x) = (term300 x).
Proof. exact (fun_ext (fun y : real => @lem5177501 y x)). Qed.
Lemma lem5177503 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5177504 (x : real) : (term301 x) = (term301 x).
Proof. exact (MK_COMB (@lem5177503) (@lem5177502 x)). Qed.
Lemma lem5177505 : term302 = term302.
Proof. exact (fun_ext (fun x : real => @lem5177504 x)). Qed.
Lemma lem5177506 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5177508 : term303 = term303.
Proof. exact (MK_COMB (@lem5177506) (@lem5177505)). Qed.
Lemma lem5177509 (h1 : term280) : term303.
Proof. exact (EQ_MP (@lem5177508) (@lem5177384 h1)). Qed.
Lemma lem5177517 (y : real) (x : real) : (term269 y x) = (term269 y x).
Proof. exact (eq_refl (term269 y x)). Qed.
Lemma lem5177518 (x : real) : (term270 x) = (term270 x).
Proof. exact (fun_ext (fun y : real => @lem5177517 y x)). Qed.
Lemma lem5177519 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5177520 (x : real) : (term271 x) = (term271 x).
Proof. exact (MK_COMB (@lem5177519) (@lem5177518 x)). Qed.
Lemma lem5177521 : term272 = term272.
Proof. exact (fun_ext (fun x : real => @lem5177520 x)). Qed.
Lemma lem5177522 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5177524 : term273 = term273.
Proof. exact (MK_COMB (@lem5177522) (@lem5177521)). Qed.
Lemma lem5177525 (h1 : term273) : term273.
Proof. exact (EQ_MP (@lem5177524) (@lem5177404 h1)). Qed.
Lemma lem5177527 {A : Type'} (P : Prop) (Q : A -> Prop) : (term319 A P Q) = (term320 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem5177528 (P : Prop) (Q : real -> Prop) : (term321 P Q) = (term322 P Q).
Proof. exact (@lem5177527 real P Q). Qed.
Lemma lem5177529 (s : real -> Prop) : (term323 s) = (term324 s).
Proof. exact (@lem5177528 (term205 s) (term310 s)). Qed.
Lemma lem5177530 (x : real) (s : real -> Prop) : (term325 s x) = (term309 x s).
Proof. exact (eq_refl (term325 s x)). Qed.
Lemma lem5177531 (s : real -> Prop) : (term326 s) = (term310 s).
Proof. exact (fun_ext (fun x : real => @lem5177530 x s)). Qed.
Lemma lem5177532 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5177533 (s : real -> Prop) : (term327 s) = (term311 s).
Proof. exact (MK_COMB (@lem5177532) (@lem5177531 s)). Qed.
Lemma lem5177534 (s : real -> Prop) : (term266 s) = (term266 s).
Proof. exact (eq_refl (term266 s)). Qed.
Lemma lem5177535 (s : real -> Prop) : (term323 s) = (term312 s).
Proof. exact (MK_COMB (@lem5177534 s) (@lem5177533 s)). Qed.
Lemma lem5177536 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5177537 (s : real -> Prop) : (term328 s) = (term329 s).
Proof. exact (MK_COMB (@lem5177536) (@lem5177535 s)). Qed.
Lemma lem5177538 (x : real) (s : real -> Prop) : (term325 s x) = (term309 x s).
Proof. exact (eq_refl (term325 s x)). Qed.
Lemma lem5177539 (s : real -> Prop) : (term266 s) = (term266 s).
Proof. exact (eq_refl (term266 s)). Qed.
Lemma lem5177540 (x : real) (s : real -> Prop) : (term330 s x) = (term331 x s).
Proof. exact (MK_COMB (@lem5177539 s) (@lem5177538 x s)). Qed.
Lemma lem5177541 (s : real -> Prop) : (term332 s) = (term333 s).
Proof. exact (fun_ext (fun x : real => @lem5177540 x s)). Qed.
Lemma lem5177542 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5177543 (s : real -> Prop) : (term324 s) = (term334 s).
Proof. exact (MK_COMB (@lem5177542) (@lem5177541 s)). Qed.
Lemma lem5177544 (s : real -> Prop) : ((term323 s) = (term324 s)) = ((term312 s) = (term334 s)).
Proof. exact (MK_COMB (@lem5177537 s) (@lem5177543 s)). Qed.
Lemma lem5177545 (s : real -> Prop) : (term312 s) = (term334 s).
Proof. exact (EQ_MP (@lem5177544 s) (@lem5177529 s)). Qed.
Lemma lem5177546 (s : real -> Prop) : (term314 s) = (term314 s).
Proof. exact (eq_refl (term314 s)). Qed.
Lemma lem5177547 (s : real -> Prop) : (term316 s) = (term335 s).
Proof. exact (MK_COMB (@lem5177546 s) (@lem5177545 s)). Qed.
Lemma lem5177549 {A : Type'} (P : Prop) (Q : A -> Prop) : (term336 A P Q) = (term337 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5177550 (P : Prop) (Q : real -> Prop) : (term338 P Q) = (term339 P Q).
Proof. exact (@lem5177549 real P Q). Qed.
Lemma lem5177551 (s : real -> Prop) : (term340 s) = (term341 s).
Proof. exact (@lem5177550 (term307 s) (term333 s)). Qed.
Lemma lem5177552 (x : real) (s : real -> Prop) : (term342 s x) = (term331 x s).
Proof. exact (eq_refl (term342 s x)). Qed.
Lemma lem5177553 (s : real -> Prop) : (term343 s) = (term333 s).
Proof. exact (fun_ext (fun x : real => @lem5177552 x s)). Qed.
Lemma lem5177554 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5177555 (s : real -> Prop) : (term344 s) = (term334 s).
Proof. exact (MK_COMB (@lem5177554) (@lem5177553 s)). Qed.
Lemma lem5177556 (s : real -> Prop) : (term314 s) = (term314 s).
Proof. exact (eq_refl (term314 s)). Qed.
Lemma lem5177557 (s : real -> Prop) : (term340 s) = (term335 s).
Proof. exact (MK_COMB (@lem5177556 s) (@lem5177555 s)). Qed.
Lemma lem5177558 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5177559 (s : real -> Prop) : (term345 s) = (term346 s).
Proof. exact (MK_COMB (@lem5177558) (@lem5177557 s)). Qed.
Lemma lem5177560 (x : real) (s : real -> Prop) : (term342 s x) = (term331 x s).
Proof. exact (eq_refl (term342 s x)). Qed.
Lemma lem5177561 (s : real -> Prop) : (term314 s) = (term314 s).
Proof. exact (eq_refl (term314 s)). Qed.
Lemma lem5177562 (x : real) (s : real -> Prop) : (term347 s x) = (term348 x s).
Proof. exact (MK_COMB (@lem5177561 s) (@lem5177560 x s)). Qed.
Lemma lem5177563 (s : real -> Prop) : (term349 s) = (term350 s).
Proof. exact (fun_ext (fun x : real => @lem5177562 x s)). Qed.
Lemma lem5177564 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5177565 (s : real -> Prop) : (term341 s) = (term351 s).
Proof. exact (MK_COMB (@lem5177564) (@lem5177563 s)). Qed.
Lemma lem5177566 (s : real -> Prop) : ((term340 s) = (term341 s)) = ((term335 s) = (term351 s)).
Proof. exact (MK_COMB (@lem5177559 s) (@lem5177565 s)). Qed.
Lemma lem5177567 (s : real -> Prop) : (term335 s) = (term351 s).
Proof. exact (EQ_MP (@lem5177566 s) (@lem5177551 s)). Qed.
Lemma lem5177568 (s : real -> Prop) : (term316 s) = (term351 s).
Proof. exact (TRANS (@lem5177547 s) (@lem5177567 s)). Qed.
Lemma lem5177569 : term317 = term352.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5177568 s)). Qed.
Lemma lem5177570 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5177571 : term318 = term353.
Proof. exact (MK_COMB (@lem5177570) (@lem5177569)). Qed.
Lemma lem5177600 (x : real) (s : real -> Prop) : (term348 x s) = (term354 x s).
Proof. exact (@lem19490 (term205 s) (term307 s) (term309 x s)). Qed.
Lemma lem5177601 (s : real -> Prop) : (term350 s) = (term355 s).
Proof. exact (fun_ext (fun x : real => @lem5177600 x s)). Qed.
Lemma lem5177602 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5177603 (s : real -> Prop) : (term351 s) = (term356 s).
Proof. exact (MK_COMB (@lem5177602) (@lem5177601 s)). Qed.
Lemma lem5177604 : term352 = term357.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5177603 s)). Qed.
Lemma lem5177605 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5177606 : term353 = term358.
Proof. exact (MK_COMB (@lem5177605) (@lem5177604)). Qed.
Lemma lem5177607 : term318 = term358.
Proof. exact (TRANS (@lem5177571) (@lem5177606)). Qed.
Lemma lem5177608 (h1 : term242) : term358.
Proof. exact (EQ_MP (@lem5177607) (@lem5177454 h1)). Qed.
Lemma lem5177617 (_67630 : real) (h1 : term280) : term359 _67630.
Proof. exact (@lem5177509 h1 _67630). Qed.
Lemma lem5177618 (_67630 : real) : (term359 _67630) = (term301 _67630).
Proof. exact (eq_refl (term359 _67630)). Qed.
Lemma lem5177619 (_67630 : real) (h1 : term280) : term301 _67630.
Proof. exact (EQ_MP (@lem5177618 _67630) (@lem5177617 _67630 h1)). Qed.
Lemma lem5177620 (_67630 : real) (_67631 : real) (h1 : term280) : term360 _67630 _67631.
Proof. exact (@lem5177619 _67630 h1 _67631). Qed.
Lemma lem5177621 (_67631 : real) (_67630 : real) : (term360 _67630 _67631) = (term299 _67631 _67630).
Proof. exact (eq_refl (term360 _67630 _67631)). Qed.
Lemma lem5177622 (_67631 : real) (_67630 : real) (h1 : term280) : term299 _67631 _67630.
Proof. exact (EQ_MP (@lem5177621 _67631 _67630) (@lem5177620 _67630 _67631 h1)). Qed.
Lemma lem5177623 (_67631 : real) (_67630 : real) (_67632 : real) (h1 : term280) : term361 _67631 _67630 _67632.
Proof. exact (@lem5177622 _67631 _67630 h1 _67632). Qed.
Lemma lem5177624 (_67631 : real) (_67630 : real) (_67632 : real) : (term361 _67631 _67630 _67632) = (term296 _67631 _67630 _67632).
Proof. exact (eq_refl (term361 _67631 _67630 _67632)). Qed.
Lemma lem5177625 (_67631 : real) (_67630 : real) (_67632 : real) (h1 : term280) : term296 _67631 _67630 _67632.
Proof. exact (EQ_MP (@lem5177624 _67631 _67630 _67632) (@lem5177623 _67631 _67630 _67632 h1)). Qed.
Lemma lem5177626 (_67633 : real) (h1 : term273) : term362 _67633.
Proof. exact (@lem5177525 h1 _67633). Qed.
Lemma lem5177627 (_67633 : real) : (term362 _67633) = (term271 _67633).
Proof. exact (eq_refl (term362 _67633)). Qed.
Lemma lem5177628 (_67633 : real) (h1 : term273) : term271 _67633.
Proof. exact (EQ_MP (@lem5177627 _67633) (@lem5177626 _67633 h1)). Qed.
Lemma lem5177629 (_67633 : real) (_67634 : real) (h1 : term273) : term363 _67633 _67634.
Proof. exact (@lem5177628 _67633 h1 _67634). Qed.
Lemma lem5177630 (_67634 : real) (_67633 : real) : (term363 _67633 _67634) = (term269 _67634 _67633).
Proof. exact (eq_refl (term363 _67633 _67634)). Qed.
Lemma lem5177632 (_67635 : real -> Prop) (h1 : term242) : term364 _67635.
Proof. exact (@lem5177608 h1 _67635). Qed.
Lemma lem5177633 (_67635 : real -> Prop) : (term364 _67635) = (term356 _67635).
Proof. exact (eq_refl (term364 _67635)). Qed.
Lemma lem5177634 (_67635 : real -> Prop) (h1 : term242) : term356 _67635.
Proof. exact (EQ_MP (@lem5177633 _67635) (@lem5177632 _67635 h1)). Qed.
Lemma lem5177635 (_67635 : real -> Prop) (_67636 : real) (h1 : term242) : term365 _67635 _67636.
Proof. exact (@lem5177634 _67635 h1 _67636). Qed.
Lemma lem5177636 (_67636 : real) (_67635 : real -> Prop) : (term365 _67635 _67636) = (term354 _67636 _67635).
Proof. exact (eq_refl (term365 _67635 _67636)). Qed.
Lemma lem5177637 (_67636 : real) (_67635 : real -> Prop) (h1 : term242) : term354 _67636 _67635.
Proof. exact (EQ_MP (@lem5177636 _67636 _67635) (@lem5177635 _67635 _67636 h1)). Qed.
Lemma lem5177638 (_67636 : real) (_67635 : real -> Prop) (h1 : term242) : term366 _67636 _67635.
Proof. exact (proj2 (@lem5177637 _67636 _67635 h1)). Qed.
Lemma lem5177641 (s : real -> Prop) (h1 : @FINITE real s) : @FINITE real s.
Proof. exact (h1). Qed.
Lemma lem5177643 (s : real -> Prop) (h1 : term39 s) : term39 s.
Proof. exact (h1). Qed.
Lemma lem5177645 (x : real) (s : real -> Prop) (h1 : term186 x s) : term186 x s.
Proof. exact (h1). Qed.
Lemma lem5177656 (_67631 : real) (_67630 : real) (_67632 : real) : (term296 _67631 _67630 _67632) = (term367 _67631 _67630 _67632).
Proof. exact (@lem5175628 (term368 _67630 _67631) (term368 _67631 _67632) (real_le _67630 _67632)). Qed.
Lemma lem5177657 (_67631 : real) (_67630 : real) (_67632 : real) (h1 : term280) : term367 _67631 _67630 _67632.
Proof. exact (EQ_MP (@lem5177656 _67631 _67630 _67632) (@lem5177625 _67631 _67630 _67632 h1)). Qed.
Lemma lem5177663 (_67634 : real) (_67633 : real) (h1 : term273) : term269 _67634 _67633.
Proof. exact (EQ_MP (@lem5177630 _67634 _67633) (@lem5177629 _67633 _67634 h1)). Qed.
Lemma lem5177667 (s : real -> Prop) (y : real) (x : real) (h1 : term282 s y x) : term368 y x.
Proof. exact (proj2 (@lem5177470 s y x h1)). Qed.
Lemma lem5177694 (_67636 : real) (_67635 : real -> Prop) : (term366 _67636 _67635) = (term369 _67636 _67635).
Proof. exact (@lem5175628 (term370 _67635) (_67635 = (@EMPTY real)) (term309 _67636 _67635)). Qed.
Lemma lem5177695 (_67636 : real) (_67635 : real -> Prop) (h1 : term242) : term369 _67636 _67635.
Proof. exact (EQ_MP (@lem5177694 _67636 _67635) (@lem5177638 _67636 _67635 h1)). Qed.
Lemma lem5177759 (s : real -> Prop) (h1 : @FINITE real s) : @FINITE real s.
Proof. exact (h1). Qed.
Lemma lem5177760 (s : real -> Prop) (h1 : @FINITE real s) : term371 s.
Proof. exact (fun h0 : term370 s => @lem5177759 s h1). Qed.
Lemma lem5177762 (p : Prop) : (term372 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5177763 (s : real -> Prop) : (term371 s) = (@FINITE real s).
Proof. exact (@lem5177762 (@FINITE real s)). Qed.
Lemma lem5177764 (s : real -> Prop) (h1 : @FINITE real s) : @FINITE real s.
Proof. exact (EQ_MP (@lem5177763 s) (@lem5177760 s h1)). Qed.
Lemma lem5177766 (s : real -> Prop) (h1 : term39 s) : term39 s.
Proof. exact (h1). Qed.
Lemma lem5177767 (s : real -> Prop) (h1 : term39 s) : term373 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5177766 s h1). Qed.
Lemma lem5177769 (p : Prop) : (term374 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5177770 (s : real -> Prop) : (term373 s) = (term39 s).
Proof. exact (@lem5177769 (s = (@EMPTY real))). Qed.
Lemma lem5177771 (s : real -> Prop) (h1 : term39 s) : term39 s.
Proof. exact (EQ_MP (@lem5177770 s) (@lem5177767 s h1)). Qed.
Lemma lem5177773 (s : real -> Prop) (y : real) (x : real) (h1 : term282 s y x) : @IN real y s.
Proof. exact (proj1 (@lem5177470 s y x h1)). Qed.
Lemma lem5177774 (s : real -> Prop) (y : real) (x : real) (h1 : term282 s y x) : term375 y s.
Proof. exact (fun h0 : term376 y s => @lem5177773 s y x h1). Qed.
Lemma lem5177776 (p : Prop) : (term372 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5177777 (y : real) (s : real -> Prop) : (term375 y s) = (@IN real y s).
Proof. exact (@lem5177776 (@IN real y s)). Qed.
Lemma lem5177778 (s : real -> Prop) (y : real) (x : real) (h1 : term282 s y x) : @IN real y s.
Proof. exact (EQ_MP (@lem5177777 y s) (@lem5177774 s y x h1)). Qed.
Lemma lem5177784 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5177785 (_67636 : real) (_67635 : real -> Prop) : (term369 _67636 _67635) = (term377 _67636 _67635).
Proof. exact (@lem5177784 (_67635 = (@EMPTY real)) (term370 _67635) (term309 _67636 _67635)). Qed.
Lemma lem5177811 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5177812 (_67636 : real) (_67635 : real -> Prop) : (term309 _67636 _67635) = (term378 _67636 _67635).
Proof. exact (@lem5177811 (term164 _67636 _67635) (term376 _67636 _67635)). Qed.
Lemma lem5177818 (_67635 : real -> Prop) : (term305 _67635) = (term305 _67635).
Proof. exact (eq_refl (term305 _67635)). Qed.
Lemma lem5177819 (_67636 : real) (_67635 : real -> Prop) : (term379 _67636 _67635) = (term380 _67636 _67635).
Proof. exact (MK_COMB (@lem5177818 _67635) (@lem5177812 _67636 _67635)). Qed.
Lemma lem5177823 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5177824 (_67636 : real) (_67635 : real -> Prop) : (term380 _67636 _67635) = (term381 _67636 _67635).
Proof. exact (@lem5177823 (term164 _67636 _67635) (term370 _67635) (term376 _67636 _67635)). Qed.
Lemma lem5177840 (_67636 : real) (_67635 : real -> Prop) : (term379 _67636 _67635) = (term381 _67636 _67635).
Proof. exact (TRANS (@lem5177819 _67636 _67635) (@lem5177824 _67636 _67635)). Qed.
Lemma lem5177841 (_67635 : real -> Prop) : (term382 _67635) = (term382 _67635).
Proof. exact (eq_refl (term382 _67635)). Qed.
Lemma lem5177842 (_67636 : real) (_67635 : real -> Prop) : (term377 _67636 _67635) = (term383 _67636 _67635).
Proof. exact (MK_COMB (@lem5177841 _67635) (@lem5177840 _67636 _67635)). Qed.
Lemma lem5177853 (_67636 : real) (_67635 : real -> Prop) : (term369 _67636 _67635) = (term383 _67636 _67635).
Proof. exact (TRANS (@lem5177785 _67636 _67635) (@lem5177842 _67636 _67635)). Qed.
Lemma lem5177854 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5177855 (_67636 : real) (_67635 : real -> Prop) : (term384 _67636 _67635) = (term385 _67636 _67635).
Proof. exact (MK_COMB (@lem5177854) (@lem5177853 _67636 _67635)). Qed.
Lemma lem5177869 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5177870 (_67636 : real) (_67635 : real -> Prop) : (term386 _67636 _67635) = (term387 _67636 _67635).
Proof. exact (@lem5177869 (_67635 = (@EMPTY real)) (term370 _67635) (term376 _67636 _67635)). Qed.
Lemma lem5177888 (_67636 : real) (_67635 : real -> Prop) : (term388 _67636 _67635) = (term388 _67636 _67635).
Proof. exact (eq_refl (term388 _67636 _67635)). Qed.
Lemma lem5177889 (_67636 : real) (_67635 : real -> Prop) : (term389 _67636 _67635) = (term390 _67636 _67635).
Proof. exact (MK_COMB (@lem5177888 _67636 _67635) (@lem5177870 _67636 _67635)). Qed.
Lemma lem5177893 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5177894 (_67636 : real) (_67635 : real -> Prop) : (term390 _67636 _67635) = (term383 _67636 _67635).
Proof. exact (@lem5177893 (_67635 = (@EMPTY real)) (term164 _67636 _67635) (term391 _67636 _67635)). Qed.
Lemma lem5177922 (_67636 : real) (_67635 : real -> Prop) : (term389 _67636 _67635) = (term383 _67636 _67635).
Proof. exact (TRANS (@lem5177889 _67636 _67635) (@lem5177894 _67636 _67635)). Qed.
Lemma lem5177923 (_67636 : real) (_67635 : real -> Prop) : ((term369 _67636 _67635) = (term389 _67636 _67635)) = ((term383 _67636 _67635) = (term383 _67636 _67635)).
Proof. exact (MK_COMB (@lem5177855 _67636 _67635) (@lem5177922 _67636 _67635)). Qed.
Lemma lem5177925 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5177926 (x : Prop) : (x = x) = True.
Proof. exact (@lem5177925 Prop x). Qed.
Lemma lem5177927 (_67636 : real) (_67635 : real -> Prop) : ((term383 _67636 _67635) = (term383 _67636 _67635)) = True.
Proof. exact (@lem5177926 (term383 _67636 _67635)). Qed.
Lemma lem5177928 (_67636 : real) (_67635 : real -> Prop) : ((term369 _67636 _67635) = (term389 _67636 _67635)) = True.
Proof. exact (TRANS (@lem5177923 _67636 _67635) (@lem5177927 _67636 _67635)). Qed.
Lemma lem5177929 (_67636 : real) (_67635 : real -> Prop) : True = ((term369 _67636 _67635) = (term389 _67636 _67635)).
Proof. exact (SYM (@lem5177928 _67636 _67635)). Qed.
Lemma lem5177930 (_67636 : real) (_67635 : real -> Prop) : (term369 _67636 _67635) = (term389 _67636 _67635).
Proof. exact (EQ_MP (@lem5177929 _67636 _67635) (@lem0)). Qed.
Lemma lem5177931 (_67636 : real) (_67635 : real -> Prop) (h1 : term242) : term389 _67636 _67635.
Proof. exact (EQ_MP (@lem5177930 _67636 _67635) (@lem5177695 _67636 _67635 h1)). Qed.
Lemma lem5177933 (b : Prop) (a : Prop) : (a \/ b) = (term392 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5177934 (_67636 : real) (_67635 : real -> Prop) : (term389 _67636 _67635) = (term393 _67636 _67635).
Proof. exact (@lem5177933 (term386 _67636 _67635) (term164 _67636 _67635)). Qed.
Lemma lem5177936 (a : Prop) (b : Prop) : (term394 a b) = (term395 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5177937 (_67636 : real) (_67635 : real -> Prop) : (term396 _67636 _67635) = (term397 _67636 _67635).
Proof. exact (@lem5177936 (term370 _67635) (term398 _67636 _67635)). Qed.
Lemma lem5177939 (a : Prop) : (term399 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5177940 (_67635 : real -> Prop) : (term400 _67635) = (@FINITE real _67635).
Proof. exact (@lem5177939 (@FINITE real _67635)). Qed.
Lemma lem5177941 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5177942 (_67635 : real -> Prop) : (term401 _67635) = (term212 _67635).
Proof. exact (MK_COMB (@lem5177941) (@lem5177940 _67635)). Qed.
Lemma lem5177944 (a : Prop) (b : Prop) : (term394 a b) = (term395 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5177945 (_67636 : real) (_67635 : real -> Prop) : (term402 _67636 _67635) = (term403 _67636 _67635).
Proof. exact (@lem5177944 (_67635 = (@EMPTY real)) (term376 _67636 _67635)). Qed.
Lemma lem5177947 (a : Prop) : (term399 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5177948 (_67636 : real) (_67635 : real -> Prop) : (term404 _67636 _67635) = (@IN real _67636 _67635).
Proof. exact (@lem5177947 (@IN real _67636 _67635)). Qed.
Lemma lem5177949 (_67635 : real -> Prop) : (term405 _67635) = (term405 _67635).
Proof. exact (eq_refl (term405 _67635)). Qed.
Lemma lem5177950 (_67636 : real) (_67635 : real -> Prop) : (term403 _67636 _67635) = (term406 _67636 _67635).
Proof. exact (MK_COMB (@lem5177949 _67635) (@lem5177948 _67636 _67635)). Qed.
Lemma lem5177951 (_67636 : real) (_67635 : real -> Prop) : (term402 _67636 _67635) = (term406 _67636 _67635).
Proof. exact (TRANS (@lem5177945 _67636 _67635) (@lem5177950 _67636 _67635)). Qed.
Lemma lem5177952 (_67636 : real) (_67635 : real -> Prop) : (term397 _67636 _67635) = (term407 _67636 _67635).
Proof. exact (MK_COMB (@lem5177942 _67635) (@lem5177951 _67636 _67635)). Qed.
Lemma lem5177953 (_67636 : real) (_67635 : real -> Prop) : (term396 _67636 _67635) = (term407 _67636 _67635).
Proof. exact (TRANS (@lem5177937 _67636 _67635) (@lem5177952 _67636 _67635)). Qed.
Lemma lem5177954 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5177955 (_67636 : real) (_67635 : real -> Prop) : (term408 _67636 _67635) = (term409 _67636 _67635).
Proof. exact (MK_COMB (@lem5177954) (@lem5177953 _67636 _67635)). Qed.
Lemma lem5177956 (_67636 : real) (_67635 : real -> Prop) : (term164 _67636 _67635) = (term164 _67636 _67635).
Proof. exact (eq_refl (term164 _67636 _67635)). Qed.
Lemma lem5177957 (_67636 : real) (_67635 : real -> Prop) : (term393 _67636 _67635) = (term410 _67636 _67635).
Proof. exact (MK_COMB (@lem5177955 _67636 _67635) (@lem5177956 _67636 _67635)). Qed.
Lemma lem5177958 (_67636 : real) (_67635 : real -> Prop) : (term389 _67636 _67635) = (term410 _67636 _67635).
Proof. exact (TRANS (@lem5177934 _67636 _67635) (@lem5177957 _67636 _67635)). Qed.
Lemma lem5177960 (s : real -> Prop) (y : real) (x : real) (h1 : term39 s) (h2 : term282 s y x) : term406 y s.
Proof. exact (conj (@lem5177771 s h1) (@lem5177778 s y x h2)). Qed.
Lemma lem5177961 (s : real -> Prop) (y : real) (x : real) (h1 : @FINITE real s) (h2 : term39 s) (h3 : term282 s y x) : term407 y s.
Proof. exact (conj (@lem5177764 s h1) (@lem5177960 s y x h2 h3)). Qed.
Lemma lem5177963 (_67636 : real) (_67635 : real -> Prop) (h1 : term242) : term410 _67636 _67635.
Proof. exact (EQ_MP (@lem5177958 _67636 _67635) (@lem5177931 _67636 _67635 h1)). Qed.
Lemma lem5177964 (y : real) (s : real -> Prop) (h1 : term242) : term410 y s.
Proof. exact (@lem5177963 y s h1). Qed.
Lemma lem5177967 (s : real -> Prop) (y : real) (x : real) (h1 : term242) (h2 : @FINITE real s) (h3 : term39 s) (h4 : term282 s y x) : term164 y s.
Proof. exact (@lem5177964 y s h1 (@lem5177961 s y x h2 h3 h4)). Qed.
Lemma lem5177968 (s : real -> Prop) (y : real) (x : real) (h1 : term242) (h2 : @FINITE real s) (h3 : term39 s) (h4 : term282 s y x) : term411 y s.
Proof. exact (fun h0 : term186 y s => @lem5177967 s y x h1 h2 h3 h4). Qed.
Lemma lem5177970 (p : Prop) : (term372 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5177971 (y : real) (s : real -> Prop) : (term411 y s) = (term164 y s).
Proof. exact (@lem5177970 (term164 y s)). Qed.
Lemma lem5177972 (s : real -> Prop) (y : real) (x : real) (h1 : term242) (h2 : @FINITE real s) (h3 : term39 s) (h4 : term282 s y x) : term164 y s.
Proof. exact (EQ_MP (@lem5177971 y s) (@lem5177968 s y x h1 h2 h3 h4)). Qed.
Lemma lem5177974 (x : real) (s : real -> Prop) (h1 : term186 x s) : term186 x s.
Proof. exact (h1). Qed.
Lemma lem5177975 (x : real) (s : real -> Prop) (h1 : term186 x s) : term412 x s.
Proof. exact (fun h0 : term164 x s => @lem5177974 x s h1). Qed.
Lemma lem5177977 (p : Prop) : (term374 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5177978 (x : real) (s : real -> Prop) : (term412 x s) = (term186 x s).
Proof. exact (@lem5177977 (term164 x s)). Qed.
Lemma lem5177979 (x : real) (s : real -> Prop) (h1 : term186 x s) : term186 x s.
Proof. exact (EQ_MP (@lem5177978 x s) (@lem5177975 x s h1)). Qed.
Lemma lem5177981 (b : Prop) (a : Prop) : (a \/ b) = (term392 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5177982 (_67632 : real) (_67630 : real) (_67631 : real) : (term367 _67631 _67630 _67632) = (term413 _67632 _67630 _67631).
Proof. exact (@lem5177981 (term414 _67631 _67630 _67632) (term368 _67630 _67631)). Qed.
Lemma lem5177984 (a : Prop) (b : Prop) : (term394 a b) = (term395 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5177985 (_67631 : real) (_67630 : real) (_67632 : real) : (term415 _67631 _67630 _67632) = (term416 _67631 _67630 _67632).
Proof. exact (@lem5177984 (term368 _67631 _67632) (real_le _67630 _67632)). Qed.
Lemma lem5177987 (a : Prop) : (term399 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5177988 (_67631 : real) (_67632 : real) : (term417 _67631 _67632) = (real_le _67631 _67632).
Proof. exact (@lem5177987 (real_le _67631 _67632)). Qed.
Lemma lem5177989 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5177990 (_67631 : real) (_67632 : real) : (term418 _67631 _67632) = (term419 _67631 _67632).
Proof. exact (MK_COMB (@lem5177989) (@lem5177988 _67631 _67632)). Qed.
Lemma lem5177991 (_67630 : real) (_67632 : real) : (term368 _67630 _67632) = (term368 _67630 _67632).
Proof. exact (eq_refl (term368 _67630 _67632)). Qed.
Lemma lem5177992 (_67631 : real) (_67630 : real) (_67632 : real) : (term416 _67631 _67630 _67632) = (term420 _67631 _67630 _67632).
Proof. exact (MK_COMB (@lem5177990 _67631 _67632) (@lem5177991 _67630 _67632)). Qed.
Lemma lem5177993 (_67631 : real) (_67630 : real) (_67632 : real) : (term415 _67631 _67630 _67632) = (term420 _67631 _67630 _67632).
Proof. exact (TRANS (@lem5177985 _67631 _67630 _67632) (@lem5177992 _67631 _67630 _67632)). Qed.
Lemma lem5177994 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5177995 (_67631 : real) (_67630 : real) (_67632 : real) : (term421 _67631 _67630 _67632) = (term422 _67631 _67630 _67632).
Proof. exact (MK_COMB (@lem5177994) (@lem5177993 _67631 _67630 _67632)). Qed.
Lemma lem5177996 (_67630 : real) (_67631 : real) : (term368 _67630 _67631) = (term368 _67630 _67631).
Proof. exact (eq_refl (term368 _67630 _67631)). Qed.
Lemma lem5177997 (_67632 : real) (_67630 : real) (_67631 : real) : (term413 _67632 _67630 _67631) = (term423 _67632 _67630 _67631).
Proof. exact (MK_COMB (@lem5177995 _67631 _67630 _67632) (@lem5177996 _67630 _67631)). Qed.
Lemma lem5177998 (_67632 : real) (_67630 : real) (_67631 : real) : (term367 _67631 _67630 _67632) = (term423 _67632 _67630 _67631).
Proof. exact (TRANS (@lem5177982 _67632 _67630 _67631) (@lem5177997 _67632 _67630 _67631)). Qed.
Lemma lem5178000 (s : real -> Prop) (y : real) (x : real) (h1 : term242) (h2 : @FINITE real s) (h3 : term39 s) (h4 : term186 x s) (h5 : term282 s y x) : term424 y x s.
Proof. exact (conj (@lem5177972 s y x h1 h2 h3 h5) (@lem5177979 x s h4)). Qed.
Lemma lem5178002 (_67632 : real) (_67630 : real) (_67631 : real) (h1 : term280) : term423 _67632 _67630 _67631.
Proof. exact (EQ_MP (@lem5177998 _67632 _67630 _67631) (@lem5177657 _67631 _67630 _67632 h1)). Qed.
Lemma lem5178003 (s : real -> Prop) (x : real) (y : real) (h1 : term280) : term425 s x y.
Proof. exact (@lem5178002 (sup s) x y h1). Qed.
Lemma lem5178006 (s : real -> Prop) (y : real) (x : real) (h1 : term242) (h2 : term280) (h3 : @FINITE real s) (h4 : term39 s) (h5 : term186 x s) (h6 : term282 s y x) : term368 x y.
Proof. exact (@lem5178003 s x y h2 (@lem5178000 s y x h1 h3 h4 h5 h6)). Qed.
Lemma lem5178007 (s : real -> Prop) (y : real) (x : real) (h1 : term242) (h2 : term280) (h3 : @FINITE real s) (h4 : term39 s) (h5 : term186 x s) (h6 : term282 s y x) : term426 x y.
Proof. exact (fun h0 : real_le x y => @lem5178006 s y x h1 h2 h3 h4 h5 h6). Qed.
Lemma lem5178009 (p : Prop) : (term374 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5178010 (x : real) (y : real) : (term426 x y) = (term368 x y).
Proof. exact (@lem5178009 (real_le x y)). Qed.
Lemma lem5178011 (s : real -> Prop) (y : real) (x : real) (h1 : term242) (h2 : term280) (h3 : @FINITE real s) (h4 : term39 s) (h5 : term186 x s) (h6 : term282 s y x) : term368 x y.
Proof. exact (EQ_MP (@lem5178010 x y) (@lem5178007 s y x h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem5178022 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5178023 (_67634 : real) (_67633 : real) : (term269 _67633 _67634) = (term269 _67634 _67633).
Proof. exact (@lem5178022 (real_le _67633 _67634) (real_le _67634 _67633)). Qed.
Lemma lem5178029 (_67634 : real) (_67633 : real) : (term427 _67634 _67633) = (term427 _67634 _67633).
Proof. exact (eq_refl (term427 _67634 _67633)). Qed.
Lemma lem5178030 (_67634 : real) (_67633 : real) : ((term269 _67634 _67633) = (term269 _67633 _67634)) = ((term269 _67634 _67633) = (term269 _67634 _67633)).
Proof. exact (MK_COMB (@lem5178029 _67634 _67633) (@lem5178023 _67634 _67633)). Qed.
Lemma lem5178032 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5178033 (x : Prop) : (x = x) = True.
Proof. exact (@lem5178032 Prop x). Qed.
Lemma lem5178034 (_67634 : real) (_67633 : real) : ((term269 _67634 _67633) = (term269 _67634 _67633)) = True.
Proof. exact (@lem5178033 (term269 _67634 _67633)). Qed.
Lemma lem5178035 (_67633 : real) (_67634 : real) : ((term269 _67634 _67633) = (term269 _67633 _67634)) = True.
Proof. exact (TRANS (@lem5178030 _67634 _67633) (@lem5178034 _67634 _67633)). Qed.
Lemma lem5178036 (_67633 : real) (_67634 : real) : True = ((term269 _67634 _67633) = (term269 _67633 _67634)).
Proof. exact (SYM (@lem5178035 _67633 _67634)). Qed.
Lemma lem5178037 (_67633 : real) (_67634 : real) : (term269 _67634 _67633) = (term269 _67633 _67634).
Proof. exact (EQ_MP (@lem5178036 _67633 _67634) (@lem0)). Qed.
Lemma lem5178038 (_67633 : real) (_67634 : real) (h1 : term273) : term269 _67633 _67634.
Proof. exact (EQ_MP (@lem5178037 _67633 _67634) (@lem5177663 _67634 _67633 h1)). Qed.
Lemma lem5178040 (b : Prop) (a : Prop) : (a \/ b) = (term392 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5178043 (_67634 : real) (_67633 : real) : (term269 _67633 _67634) = (term428 _67634 _67633).
Proof. exact (@lem5178040 (real_le _67633 _67634) (real_le _67634 _67633)). Qed.
Lemma lem5178046 (_67634 : real) (_67633 : real) (h1 : term273) : term428 _67634 _67633.
Proof. exact (EQ_MP (@lem5178043 _67634 _67633) (@lem5178038 _67633 _67634 h1)). Qed.
Lemma lem5178047 (y : real) (x : real) (h1 : term273) : term428 y x.
Proof. exact (@lem5178046 y x h1). Qed.
Lemma lem5178050 (s : real -> Prop) (y : real) (x : real) (h1 : term242) (h2 : term280) (h3 : term273) (h4 : @FINITE real s) (h5 : term39 s) (h6 : term186 x s) (h7 : term282 s y x) : real_le y x.
Proof. exact (@lem5178047 y x h3 (@lem5178011 s y x h1 h2 h4 h5 h6 h7)). Qed.
Lemma lem5178051 (s : real -> Prop) (y : real) (x : real) (h1 : term242) (h2 : term280) (h3 : term273) (h4 : @FINITE real s) (h5 : term39 s) (h6 : term186 x s) (h7 : term282 s y x) : term429 y x.
Proof. exact (fun h0 : term368 y x => @lem5178050 s y x h1 h2 h3 h4 h5 h6 h7). Qed.
Lemma lem5178053 (p : Prop) : (term372 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5178054 (y : real) (x : real) : (term429 y x) = (real_le y x).
Proof. exact (@lem5178053 (real_le y x)). Qed.
Lemma lem5178055 (s : real -> Prop) (y : real) (x : real) (h1 : term242) (h2 : term280) (h3 : term273) (h4 : @FINITE real s) (h5 : term39 s) (h6 : term186 x s) (h7 : term282 s y x) : real_le y x.
Proof. exact (EQ_MP (@lem5178054 y x) (@lem5178051 s y x h1 h2 h3 h4 h5 h6 h7)). Qed.
Lemma lem5178058 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5178060 (y : real) (x : real) : (term368 y x) = (term430 y x).
Proof. exact (@lem5178058 (real_le y x)). Qed.
Lemma lem5178063 (s : real -> Prop) (y : real) (x : real) (h1 : term282 s y x) : term430 y x.
Proof. exact (EQ_MP (@lem5178060 y x) (@lem5177667 s y x h1)). Qed.
Lemma lem5178066 (s : real -> Prop) (y : real) (x : real) (h1 : term242) (h2 : term280) (h3 : term273) (h4 : @FINITE real s) (h5 : term39 s) (h6 : term186 x s) (h7 : term282 s y x) : False.
Proof. exact (@lem5178063 s y x h7 (@lem5178055 s y x h1 h2 h3 h4 h5 h6 h7)). Qed.
Lemma lem5178067 (s : real -> Prop) (y : real) (x : real) (h1 : term242) (h2 : term280) (h3 : term273) (h4 : @FINITE real s) (h5 : term39 s) (h6 : term186 x s) (h7 : term282 s y x) : term431.
Proof. exact (fun h0 : ~ False => @lem5178066 s y x h1 h2 h3 h4 h5 h6 h7). Qed.
Lemma lem5178069 (p : Prop) : (term372 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5178070 : term431 = False.
Proof. exact (@lem5178069 False). Qed.
Lemma lem5178071 (s : real -> Prop) (y : real) (x : real) (h1 : term242) (h2 : term280) (h3 : term273) (h4 : @FINITE real s) (h5 : term39 s) (h6 : term186 x s) (h7 : term282 s y x) : False.
Proof. exact (EQ_MP (@lem5178070) (@lem5178067 s y x h1 h2 h3 h4 h5 h6 h7)). Qed.
Lemma lem5178072 (s : real -> Prop) (y : real) (x : real) (h1 : term242) (h2 : term280) (h3 : term273) (h4 : @FINITE real s) (h5 : term39 s) (h6 : term186 x s) (h7 : term282 s y x) : (term186 x s) = False.
Proof. exact (prop_ext (fun h8 : term186 x s => @lem5178071 s y x h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5177645 x s h6)). Qed.
Lemma lem5178073 (s : real -> Prop) (y : real) (x : real) (h1 : term242) (h2 : term280) (h3 : term273) (h4 : @FINITE real s) (h5 : term39 s) (h6 : term186 x s) (h7 : term282 s y x) : False.
Proof. exact (EQ_MP (@lem5178072 s y x h1 h2 h3 h4 h5 h6 h7) (@lem5177645 x s h6)). Qed.
Lemma lem5178074 (s : real -> Prop) (y : real) (x : real) (h1 : term242) (h2 : term280) (h3 : term273) (h4 : @FINITE real s) (h5 : term39 s) (h6 : term186 x s) (h7 : term282 s y x) : (term39 s) = False.
Proof. exact (prop_ext (fun h8 : term39 s => @lem5178073 s y x h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5177643 s h5)). Qed.
Lemma lem5178075 (s : real -> Prop) (y : real) (x : real) (h1 : term242) (h2 : term280) (h3 : term273) (h4 : @FINITE real s) (h5 : term39 s) (h6 : term186 x s) (h7 : term282 s y x) : False.
Proof. exact (EQ_MP (@lem5178074 s y x h1 h2 h3 h4 h5 h6 h7) (@lem5177643 s h5)). Qed.
Lemma lem5178076 (s : real -> Prop) (y : real) (x : real) (h1 : term242) (h2 : term280) (h3 : term273) (h4 : @FINITE real s) (h5 : term39 s) (h6 : term186 x s) (h7 : term282 s y x) : (@FINITE real s) = False.
Proof. exact (prop_ext (fun h8 : @FINITE real s => @lem5178075 s y x h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5177641 s h4)). Qed.
Lemma lem5178077 (s : real -> Prop) (y : real) (x : real) (h1 : term242) (h2 : term280) (h3 : term273) (h4 : @FINITE real s) (h5 : term39 s) (h6 : term186 x s) (h7 : term282 s y x) : False.
Proof. exact (EQ_MP (@lem5178076 s y x h1 h2 h3 h4 h5 h6 h7) (@lem5177641 s h4)). Qed.
Lemma lem5178078 (s : real -> Prop) (y : real) (x : real) (h1 : term242) (h2 : term280) (h3 : term273) (h4 : @FINITE real s) (h5 : term39 s) (h6 : term186 x s) (h7 : term282 s y x) : (term186 x s) = False.
Proof. exact (prop_ext (fun h8 : term186 x s => @lem5178077 s y x h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5177484 x s h6)). Qed.
Lemma lem5178079 (s : real -> Prop) (y : real) (x : real) (h1 : term242) (h2 : term280) (h3 : term273) (h4 : @FINITE real s) (h5 : term39 s) (h6 : term186 x s) (h7 : term282 s y x) : False.
Proof. exact (EQ_MP (@lem5178078 s y x h1 h2 h3 h4 h5 h6 h7) (@lem5177484 x s h6)). Qed.
Lemma lem5178080 (s : real -> Prop) (y : real) (x : real) (h1 : term242) (h2 : term280) (h3 : term273) (h4 : @FINITE real s) (h5 : term39 s) (h6 : term186 x s) (h7 : term282 s y x) : (term39 s) = False.
Proof. exact (prop_ext (fun h8 : term39 s => @lem5178079 s y x h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5177480 s h5)). Qed.
Lemma lem5178081 (s : real -> Prop) (y : real) (x : real) (h1 : term242) (h2 : term280) (h3 : term273) (h4 : @FINITE real s) (h5 : term39 s) (h6 : term186 x s) (h7 : term282 s y x) : False.
Proof. exact (EQ_MP (@lem5178080 s y x h1 h2 h3 h4 h5 h6 h7) (@lem5177480 s h5)). Qed.
Lemma lem5178082 (s : real -> Prop) (y : real) (x : real) (h1 : term242) (h2 : term280) (h3 : term273) (h4 : @FINITE real s) (h5 : term39 s) (h6 : term186 x s) (h7 : term282 s y x) : (@FINITE real s) = False.
Proof. exact (prop_ext (fun h8 : @FINITE real s => @lem5178081 s y x h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5177476 s h4)). Qed.
Lemma lem5178083 (s : real -> Prop) (y : real) (x : real) (h1 : term242) (h2 : term280) (h3 : term273) (h4 : @FINITE real s) (h5 : term39 s) (h6 : term186 x s) (h7 : term282 s y x) : False.
Proof. exact (EQ_MP (@lem5178082 s y x h1 h2 h3 h4 h5 h6 h7) (@lem5177476 s h4)). Qed.
Lemma lem5178084 (s : real -> Prop) (y : real) (x : real) (h1 : term242) (h2 : term280) (h3 : term273) (h4 : @FINITE real s) (h5 : term39 s) (h6 : term186 x s) (h7 : term282 s y x) : term273 = False.
Proof. exact (prop_ext (fun h8 : term273 => @lem5178083 s y x h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5177525 h3)). Qed.
Lemma lem5178085 (s : real -> Prop) (y : real) (x : real) (h1 : term242) (h2 : term280) (h3 : term273) (h4 : @FINITE real s) (h5 : term39 s) (h6 : term186 x s) (h7 : term282 s y x) : False.
Proof. exact (EQ_MP (@lem5178084 s y x h1 h2 h3 h4 h5 h6 h7) (@lem5177525 h3)). Qed.
Lemma lem5178086 (s : real -> Prop) (y : real) (x : real) (h1 : term242) (h2 : term280) (h3 : term273) (h4 : @FINITE real s) (h5 : term39 s) (h6 : term186 x s) (h7 : term282 s y x) : (term186 x s) = False.
Proof. exact (prop_ext (fun h8 : term186 x s => @lem5178085 s y x h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5177484 x s h6)). Qed.
Lemma lem5178087 (s : real -> Prop) (y : real) (x : real) (h1 : term242) (h2 : term280) (h3 : term273) (h4 : @FINITE real s) (h5 : term39 s) (h6 : term186 x s) (h7 : term282 s y x) : False.
Proof. exact (EQ_MP (@lem5178086 s y x h1 h2 h3 h4 h5 h6 h7) (@lem5177484 x s h6)). Qed.
Lemma lem5178088 (s : real -> Prop) (y : real) (x : real) (h1 : term242) (h2 : term280) (h3 : term273) (h4 : @FINITE real s) (h5 : term39 s) (h6 : term186 x s) (h7 : term282 s y x) : (term39 s) = False.
Proof. exact (prop_ext (fun h8 : term39 s => @lem5178087 s y x h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5177480 s h5)). Qed.
Lemma lem5178089 (s : real -> Prop) (y : real) (x : real) (h1 : term242) (h2 : term280) (h3 : term273) (h4 : @FINITE real s) (h5 : term39 s) (h6 : term186 x s) (h7 : term282 s y x) : False.
Proof. exact (EQ_MP (@lem5178088 s y x h1 h2 h3 h4 h5 h6 h7) (@lem5177480 s h5)). Qed.
Lemma lem5178090 (s : real -> Prop) (y : real) (x : real) (h1 : term242) (h2 : term280) (h3 : term273) (h4 : @FINITE real s) (h5 : term39 s) (h6 : term186 x s) (h7 : term282 s y x) : (@FINITE real s) = False.
Proof. exact (prop_ext (fun h8 : @FINITE real s => @lem5178089 s y x h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5177476 s h4)). Qed.
Lemma lem5178091 (s : real -> Prop) (y : real) (x : real) (h1 : term242) (h2 : term280) (h3 : term273) (h4 : @FINITE real s) (h5 : term39 s) (h6 : term186 x s) (h7 : term282 s y x) : False.
Proof. exact (EQ_MP (@lem5178090 s y x h1 h2 h3 h4 h5 h6 h7) (@lem5177476 s h4)). Qed.
Lemma lem5178092 (s : real -> Prop) (y : real) (x : real) (h1 : term242) (h2 : term280) (h3 : term273) (h4 : @FINITE real s) (h5 : term39 s) (h6 : term186 x s) (h7 : term282 s y x) : (term282 s y x) = False.
Proof. exact (prop_ext (fun h8 : term282 s y x => @lem5178091 s y x h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5177470 s y x h7)). Qed.
Lemma lem5178093 (s : real -> Prop) (y : real) (x : real) (h1 : term242) (h2 : term280) (h3 : term273) (h4 : @FINITE real s) (h5 : term39 s) (h6 : term186 x s) (h7 : term282 s y x) : False.
Proof. exact (EQ_MP (@lem5178092 s y x h1 h2 h3 h4 h5 h6 h7) (@lem5177470 s y x h7)). Qed.
Lemma lem5178094 (s : real -> Prop) (y : real) (x : real) (h1 : term242) (h2 : term280) (h3 : term273) (h4 : @FINITE real s) (h5 : term39 s) (h6 : term186 x s) (h7 : term282 s y x) : term273 = False.
Proof. exact (prop_ext (fun h8 : term273 => @lem5178093 s y x h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5177404 h3)). Qed.
Lemma lem5178095 (s : real -> Prop) (y : real) (x : real) (h1 : term242) (h2 : term280) (h3 : term273) (h4 : @FINITE real s) (h5 : term39 s) (h6 : term186 x s) (h7 : term282 s y x) : False.
Proof. exact (EQ_MP (@lem5178094 s y x h1 h2 h3 h4 h5 h6 h7) (@lem5177404 h3)). Qed.
Lemma lem5178096 (s : real -> Prop) (y : real) (x : real) (h1 : term242) (h2 : term280) (h3 : term273) (h4 : @FINITE real s) (h5 : term39 s) (h6 : term186 x s) (h7 : term282 s y x) : (term186 x s) = False.
Proof. exact (prop_ext (fun h8 : term186 x s => @lem5178095 s y x h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5177349 x s h6)). Qed.
Lemma lem5178097 (s : real -> Prop) (y : real) (x : real) (h1 : term242) (h2 : term280) (h3 : term273) (h4 : @FINITE real s) (h5 : term39 s) (h6 : term186 x s) (h7 : term282 s y x) : False.
Proof. exact (EQ_MP (@lem5178096 s y x h1 h2 h3 h4 h5 h6 h7) (@lem5177349 x s h6)). Qed.
Lemma lem5178098 (s : real -> Prop) (y : real) (x : real) (h1 : term242) (h2 : term280) (h3 : term273) (h4 : @FINITE real s) (h5 : term39 s) (h6 : term186 x s) (h7 : term282 s y x) : (term39 s) = False.
Proof. exact (prop_ext (fun h8 : term39 s => @lem5178097 s y x h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5177339 s h5)). Qed.
Lemma lem5178099 (s : real -> Prop) (y : real) (x : real) (h1 : term242) (h2 : term280) (h3 : term273) (h4 : @FINITE real s) (h5 : term39 s) (h6 : term186 x s) (h7 : term282 s y x) : False.
Proof. exact (EQ_MP (@lem5178098 s y x h1 h2 h3 h4 h5 h6 h7) (@lem5177339 s h5)). Qed.
Lemma lem5178100 (s : real -> Prop) (y : real) (x : real) (h1 : term242) (h2 : term280) (h3 : term273) (h4 : @FINITE real s) (h5 : term39 s) (h6 : term186 x s) (h7 : term282 s y x) : (@FINITE real s) = False.
Proof. exact (prop_ext (fun h8 : @FINITE real s => @lem5178099 s y x h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5177331 s h4)). Qed.
Lemma lem5178101 (s : real -> Prop) (y : real) (x : real) (h1 : term242) (h2 : term280) (h3 : term273) (h4 : @FINITE real s) (h5 : term39 s) (h6 : term186 x s) (h7 : term282 s y x) : False.
Proof. exact (EQ_MP (@lem5178100 s y x h1 h2 h3 h4 h5 h6 h7) (@lem5177331 s h4)). Qed.
Lemma lem5178102 (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : term273) (h4 : @FINITE real s) (h5 : term235 s x) (h6 : term39 s) (h7 : term186 x s) : False.
Proof. exact (ex_elim (@lem5177043 s x h5) (fun y : real => fun h0 : term289 s x y => @lem5178101 s y x h1 h2 h3 h4 h6 h7 h0)). Qed.
Lemma lem5178103 (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : term273) (h4 : @FINITE real s) (h5 : term235 s x) (h6 : term39 s) (h7 : term186 x s) : term273 = False.
Proof. exact (prop_ext (fun h8 : term273 => @lem5178102 x s h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5177194 h3)). Qed.
Lemma lem5178104 (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : term273) (h4 : @FINITE real s) (h5 : term235 s x) (h6 : term39 s) (h7 : term186 x s) : False.
Proof. exact (EQ_MP (@lem5178103 x s h1 h2 h3 h4 h5 h6 h7) (@lem5177194 h3)). Qed.
Lemma lem5178105 (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : term273) (h4 : @FINITE real s) (h5 : term235 s x) (h6 : term39 s) (h7 : term186 x s) : (term186 x s) = False.
Proof. exact (prop_ext (fun h8 : term186 x s => @lem5178104 x s h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5176973 x s h7)). Qed.
Lemma lem5178106 (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : term273) (h4 : @FINITE real s) (h5 : term235 s x) (h6 : term39 s) (h7 : term186 x s) : False.
Proof. exact (EQ_MP (@lem5178105 x s h1 h2 h3 h4 h5 h6 h7) (@lem5176973 x s h7)). Qed.
Lemma lem5178107 (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : term273) (h4 : @FINITE real s) (h5 : term235 s x) (h6 : term39 s) (h7 : term186 x s) : (term39 s) = False.
Proof. exact (prop_ext (fun h8 : term39 s => @lem5178106 x s h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5176967 s h6)). Qed.
Lemma lem5178108 (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : term273) (h4 : @FINITE real s) (h5 : term235 s x) (h6 : term39 s) (h7 : term186 x s) : False.
Proof. exact (EQ_MP (@lem5178107 x s h1 h2 h3 h4 h5 h6 h7) (@lem5176967 s h6)). Qed.
Lemma lem5178109 (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : term273) (h4 : @FINITE real s) (h5 : term235 s x) (h6 : term39 s) (h7 : term186 x s) : (@FINITE real s) = False.
Proof. exact (prop_ext (fun h8 : @FINITE real s => @lem5178108 x s h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5176961 s h4)). Qed.
Lemma lem5178110 (x : real) (s : real -> Prop) (h1 : term242) (h2 : term280) (h3 : term273) (h4 : @FINITE real s) (h5 : term235 s x) (h6 : term39 s) (h7 : term186 x s) : False.
Proof. exact (EQ_MP (@lem5178109 x s h1 h2 h3 h4 h5 h6 h7) (@lem5176961 s h4)). Qed.
Lemma lem5178111 (x : real) (s : real -> Prop) (h1 : term280) (h2 : term273) (h3 : @FINITE real s) (h4 : term235 s x) (h5 : term39 s) (h6 : term186 x s) : term240.
Proof. exact (fun h0 : term242 => @lem5178110 x s h0 h1 h2 h3 h4 h5 h6). Qed.
Lemma lem5178112 : term240 = term241.
Proof. exact (@lem69 term242). Qed.
Lemma lem5178113 (x : real) (s : real -> Prop) (h1 : term280) (h2 : term273) (h3 : @FINITE real s) (h4 : term235 s x) (h5 : term39 s) (h6 : term186 x s) : term241.
Proof. exact (EQ_MP (@lem5178112) (@lem5178111 x s h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem5178114 (x : real) (s : real -> Prop) (h1 : term280) (h2 : @FINITE real s) (h3 : term235 s x) (h4 : term39 s) (h5 : term186 x s) : term245.
Proof. exact (fun h0 : term273 => @lem5178113 x s h1 h0 h2 h3 h4 h5). Qed.
Lemma lem5178115 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term235 s x) (h3 : term39 s) (h4 : term186 x s) : term248.
Proof. exact (fun h0 : term280 => @lem5178114 x s h0 h1 h2 h3 h4). Qed.
Lemma lem5178116 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) (h3 : term186 x s) : term251 s x.
Proof. exact (fun h0 : term235 s x => @lem5178115 x s h1 h0 h2 h3). Qed.
Lemma lem5178117 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : term253 s x.
Proof. exact (fun h0 : term186 x s => @lem5178116 x s h1 h2 h0). Qed.
Lemma lem5178118 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : term255 s x.
Proof. exact (fun h0 : term39 s => @lem5178117 x s h1 h0). Qed.
Lemma lem5178119 (s : real -> Prop) (x : real) : term257 s x.
Proof. exact (fun h0 : @FINITE real s => @lem5178118 x s h0). Qed.
Lemma lem5178124 (x : real) : term261 x.
Proof. exact (fun s : real -> Prop => @lem5178119 s x). Qed.
Lemma lem5178129 : term265.
Proof. exact (fun x : real => @lem5178124 x). Qed.
Lemma lem5178130 : term264.
Proof. exact (EQ_MP (@lem5176948) (@lem5178129)). Qed.
Lemma lem5178131 (x : real) : term432 x.
Proof. exact (@lem5178130 x). Qed.
Lemma lem5178132 (x : real) : (term432 x) = (term260 x).
Proof. exact (eq_refl (term432 x)). Qed.
Lemma lem5178133 (x : real) : term260 x.
Proof. exact (EQ_MP (@lem5178132 x) (@lem5178131 x)). Qed.
Lemma lem5178134 (x : real) (s : real -> Prop) : term433 x s.
Proof. exact (@lem5178133 x s). Qed.
Lemma lem5178135 (s : real -> Prop) (x : real) : (term433 x s) = (term236 s x).
Proof. exact (eq_refl (term433 x s)). Qed.
Lemma lem5178136 (s : real -> Prop) (x : real) : term236 s x.
Proof. exact (EQ_MP (@lem5178135 s x) (@lem5178134 x s)). Qed.
Lemma lem5178138 (s : real -> Prop) (x : real) : term236 s x.
Proof. exact (@lem5176602 s x (@lem5178136 s x)). Qed.
Lemma lem5178139 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : term254 s x.
Proof. exact (@lem5178138 s x (@lem5175646 s h1)). Qed.
Lemma lem5178140 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : term252 s x.
Proof. exact (@lem5178139 x s h1 (@lem5175682 s h2)). Qed.
Lemma lem5178141 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) (h3 : term186 x s) : term250 s x.
Proof. exact (@lem5178140 x s h1 h2 (@lem5176181 x s h3)). Qed.
Lemma lem5178142 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term235 s x) (h3 : term39 s) (h4 : term186 x s) : term247.
Proof. exact (@lem5178141 x s h1 h3 h4 (@lem5176587 s x h2)). Qed.
Lemma lem5178143 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term235 s x) (h3 : term39 s) (h4 : term186 x s) : term244.
Proof. exact (@lem5178142 x s h1 h2 h3 h4 (@lem1339577)). Qed.
Lemma lem5178144 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term235 s x) (h3 : term39 s) (h4 : term186 x s) : term240.
Proof. exact (@lem5178143 x s h1 h2 h3 h4 (@lem1339697)). Qed.
Lemma lem5178145 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term235 s x) (h3 : term39 s) (h4 : term186 x s) : False.
Proof. exact (@lem5178144 x s h1 h2 h3 h4 (@lem5145274)). Qed.
Lemma lem5178146 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term235 s x) (h3 : term39 s) (h4 : term186 x s) : (term235 s x) = False.
Proof. exact (prop_ext (fun h5 : term235 s x => @lem5178145 x s h1 h2 h3 h4) (fun h5 : False => @lem5176587 s x h2)). Qed.
Lemma lem5178147 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term235 s x) (h3 : term39 s) (h4 : term186 x s) : False.
Proof. exact (EQ_MP (@lem5178146 x s h1 h2 h3 h4) (@lem5176587 s x h2)). Qed.
Lemma lem5178148 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) (h3 : term186 x s) : term234 s x.
Proof. exact (fun h0 : term235 s x => @lem5178147 x s h1 h0 h2 h3). Qed.
Lemma lem5178149 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) (h3 : term186 x s) : term96 s x.
Proof. exact (EQ_MP (@lem5176586 s x) (@lem5178148 x s h1 h2 h3)). Qed.
Lemma lem5178151 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) (h3 : term186 x s) : term166 s x.
Proof. exact (EQ_MP (@lem5176582 s x) (@lem5178149 x s h1 h2 h3)). Qed.
Lemma lem5178152 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) (h3 : term186 x s) : (term186 x s) = (term166 s x).
Proof. exact (prop_ext (fun h4 : term186 x s => @lem5178151 x s h1 h2 h3) (fun h4 : term166 s x => @lem5176181 x s h3)). Qed.
Lemma lem5178153 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) (h3 : term186 x s) : term166 s x.
Proof. exact (EQ_MP (@lem5178152 x s h1 h2 h3) (@lem5176181 x s h3)). Qed.
Lemma lem5178154 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : term169 s x.
Proof. exact (fun h0 : term186 x s => @lem5178153 x s h1 h2 h0). Qed.
Lemma lem5178155 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) (h3 : term164 x s) : term171 x s.
Proof. exact (EQ_MP (@lem5176180 x s h3) (@lem5176387 x s h1 h2)). Qed.
Lemma lem5178156 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) (h3 : term164 x s) : (term164 x s) = (term171 x s).
Proof. exact (prop_ext (fun h4 : term164 x s => @lem5178155 x s h1 h2 h3) (fun h4 : term171 x s => @lem5176165 x s h3)). Qed.
Lemma lem5178157 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) (h3 : term164 x s) : term171 x s.
Proof. exact (EQ_MP (@lem5178156 x s h1 h2 h3) (@lem5176165 x s h3)). Qed.
Lemma lem5178158 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : term174 x s.
Proof. exact (fun h0 : term164 x s => @lem5178157 x s h1 h2 h0). Qed.
Lemma lem5178159 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : term177 s x.
Proof. exact (conj (@lem5178158 x s h1 h2) (@lem5178154 x s h1 h2)). Qed.
Lemma lem5178160 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : term158 s x.
Proof. exact (EQ_MP (@lem5176164 s x) (@lem5178159 x s h1 h2)). Qed.
Lemma lem5178162 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : term143 x s.
Proof. exact (EQ_MP (@lem5176146 x s) (@lem5178160 x s h1 h2)). Qed.
Lemma lem5178165 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : (term25 x s) = (term23 x s).
Proof. exact (EQ_MP (@lem5176060 x s h1) (@lem5178162 x s h1 h2)). Qed.
Lemma lem5178166 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : (term39 s) = ((term25 x s) = (term23 x s)).
Proof. exact (prop_ext (fun h3 : term39 s => @lem5178165 x s h1 h2) (fun h3 : (term25 x s) = (term23 x s) => @lem5175682 s h2)). Qed.
Lemma lem5178167 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : term39 s) : (term25 x s) = (term23 x s).
Proof. exact (EQ_MP (@lem5178166 x s h1 h2) (@lem5175682 s h2)). Qed.
Lemma lem5178168 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : term28 x s.
Proof. exact (fun h0 : term39 s => @lem5178167 x s h1 h0). Qed.
Lemma lem5178169 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : s = (@EMPTY real)) : (term25 x s) = x.
Proof. exact (EQ_MP (@lem5175875 x s h1 h2) (@lem5176081 x)). Qed.
Lemma lem5178170 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : s = (@EMPTY real)) : (s = (@EMPTY real)) = ((term25 x s) = x).
Proof. exact (prop_ext (fun h3 : s = (@EMPTY real) => @lem5178169 x s h1 h2) (fun h3 : (term25 x s) = x => @lem5175665 s h2)). Qed.
Lemma lem5178171 (x : real) (s : real -> Prop) (h1 : @FINITE real s) (h2 : s = (@EMPTY real)) : (term25 x s) = x.
Proof. exact (EQ_MP (@lem5178170 x s h1 h2) (@lem5175665 s h2)). Qed.
Lemma lem5178172 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : term32 s x.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5178171 x s h1 h0). Qed.
Lemma lem5178173 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : term35 x s.
Proof. exact (conj (@lem5178172 x s h1) (@lem5178168 x s h1)). Qed.
Lemma lem5178174 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : (term25 x s) = (term36 x s).
Proof. exact (EQ_MP (@lem5175664 x s) (@lem5178173 x s h1)). Qed.
Lemma lem5178175 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : (@FINITE real s) = ((term25 x s) = (term36 x s)).
Proof. exact (prop_ext (fun h2 : @FINITE real s => @lem5178174 x s h1) (fun h2 : (term25 x s) = (term36 x s) => @lem5175646 s h1)). Qed.
Lemma lem5178176 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : (term25 x s) = (term36 x s).
Proof. exact (EQ_MP (@lem5178175 x s h1) (@lem5175646 s h1)). Qed.
Lemma lem5178177 (x : real) (s : real -> Prop) : term434 x s.
Proof. exact (fun h0 : @FINITE real s => @lem5178176 x s h0). Qed.
Lemma lem5178182 (x : real) : term435 x.
Proof. exact (fun s : real -> Prop => @lem5178177 x s). Qed.
Lemma lem5178187 : term436.
Proof. exact (fun x : real => @lem5178182 x). Qed.
