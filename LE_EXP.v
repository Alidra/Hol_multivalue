Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LE_EXP_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import DE_MORGAN_THM_spec.
Require Import LT_EXP_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_LT_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm13473_spec.
Require Import thm1821_spec.
Require Import thm1823_spec.
Require Import thm1831_spec.
Require Import thm1832_spec.
Require Import thm1833_spec.
Require Import thm1834_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1855_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm80360_spec.
Require Import thm80550_spec.
Require Import thm82_spec.
Require Import thm89994_spec.
Lemma lem148578 (n : nat) (m : nat) (h1 : (term0 m n) = (Peano.le n m)) : (term0 m n) = (Peano.le n m).
Proof. exact (h1). Qed.
Lemma lem148579 (n : nat) (m : nat) (h1 : (term0 m n) = (Peano.le n m)) : (Peano.le n m) = (term0 m n).
Proof. exact (SYM (@lem148578 n m h1)). Qed.
Lemma lem148580 (m : nat) (n : nat) (h1 : (Peano.le n m) = (term0 m n)) : (Peano.le n m) = (term0 m n).
Proof. exact (h1). Qed.
Lemma lem148581 (m : nat) (n : nat) (h1 : (Peano.le n m) = (term0 m n)) : (term0 m n) = (Peano.le n m).
Proof. exact (SYM (@lem148580 m n h1)). Qed.
Lemma lem148582 (m : nat) (n : nat) : ((term0 m n) = (Peano.le n m)) = ((Peano.le n m) = (term0 m n)).
Proof. exact (prop_ext (fun h1 : (term0 m n) = (Peano.le n m) => @lem148579 n m h1) (fun h1 : (Peano.le n m) = (term0 m n) => @lem148581 m n h1)). Qed.
Lemma lem148583 (m : nat) : (term1 m) = (term2 m).
Proof. exact (fun_ext (fun n : nat => @lem148582 m n)). Qed.
Lemma lem148584 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem148585 (m : nat) : (term3 m) = (term4 m).
Proof. exact (MK_COMB (@lem148584) (@lem148583 m)). Qed.
Lemma lem148586 : term5 = term6.
Proof. exact (fun_ext (fun m : nat => @lem148585 m)). Qed.
Lemma lem148587 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem148588 : term7 = term8.
Proof. exact (MK_COMB (@lem148587) (@lem148586)). Qed.
Lemma lem148589 : term8.
Proof. exact (EQ_MP (@lem148588) (@lem98377)). Qed.
Lemma lem148590 (t1 : Prop) : term9 t1.
Proof. exact (@lem10089 t1). Qed.
Lemma lem148591 (t1 : Prop) : (term9 t1) = (term10 t1).
Proof. exact (eq_refl (term9 t1)). Qed.
Lemma lem148592 (t1 : Prop) : term10 t1.
Proof. exact (EQ_MP (@lem148591 t1) (@lem148590 t1)). Qed.
Lemma lem148593 (t1 : Prop) (t2 : Prop) : term11 t1 t2.
Proof. exact (@lem148592 t1 t2). Qed.
Lemma lem148594 (t1 : Prop) (t2 : Prop) : (term11 t1 t2) = (term12 t1 t2).
Proof. exact (eq_refl (term11 t1 t2)). Qed.
Lemma lem148595 (t1 : Prop) (t2 : Prop) : term12 t1 t2.
Proof. exact (EQ_MP (@lem148594 t1 t2) (@lem148593 t1 t2)). Qed.
Lemma lem148598 (x : nat) : term13 x.
Proof. exact (@lem148575 x). Qed.
Lemma lem148599 (x : nat) : (term13 x) = (term14 x).
Proof. exact (eq_refl (term13 x)). Qed.
Lemma lem148600 (x : nat) : term14 x.
Proof. exact (EQ_MP (@lem148599 x) (@lem148598 x)). Qed.
Lemma lem148601 (x : nat) (m : nat) : term15 x m.
Proof. exact (@lem148600 x m). Qed.
Lemma lem148602 (x : nat) (m : nat) : (term15 x m) = (term16 x m).
Proof. exact (eq_refl (term15 x m)). Qed.
Lemma lem148603 (x : nat) (m : nat) : term16 x m.
Proof. exact (EQ_MP (@lem148602 x m) (@lem148601 x m)). Qed.
Lemma lem148604 (x : nat) (m : nat) (n : nat) : term17 x m n.
Proof. exact (@lem148603 x m n). Qed.
Lemma lem148605 (x : nat) (m : nat) (n : nat) : (term17 x m n) = ((term18 m x n) = (term19 x m n)).
Proof. exact (eq_refl (term17 x m n)). Qed.
Lemma lem148607 (m : nat) : term20 m.
Proof. exact (@lem148589 m). Qed.
Lemma lem148608 (m : nat) : (term20 m) = (term4 m).
Proof. exact (eq_refl (term20 m)). Qed.
Lemma lem148609 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem148608 m) (@lem148607 m)). Qed.
Lemma lem148610 (m : nat) (n : nat) : term21 m n.
Proof. exact (@lem148609 m n). Qed.
Lemma lem148611 (m : nat) (n : nat) : (term21 m n) = ((Peano.le n m) = (term0 m n)).
Proof. exact (eq_refl (term21 m n)). Qed.
Lemma lem148616 (m : nat) (n : nat) : (Peano.le n m) = (term0 m n).
Proof. exact (EQ_MP (@lem148611 m n) (@lem148610 m n)). Qed.
Lemma lem148617 (n : nat) (x : nat) (m : nat) : (term22 m x n) = (term23 n x m).
Proof. exact (@lem148616 (Nat.pow x n) (Nat.pow x m)). Qed.
Lemma lem148619 (x : nat) (m : nat) (n : nat) : (term18 m x n) = (term19 x m n).
Proof. exact (EQ_MP (@lem148605 x m n) (@lem148604 x m n)). Qed.
Lemma lem148620 (x : nat) (n : nat) (m : nat) : (term18 n x m) = (term19 x n m).
Proof. exact (@lem148619 x n m). Qed.
Lemma lem148626 (m : nat) (n : nat) : (Peano.le n m) = (term0 m n).
Proof. exact (EQ_MP (@lem148611 m n) (@lem148610 m n)). Qed.
Lemma lem148627 (x : nat) : (term24 x) = (term25 x).
Proof. exact (@lem148626 x term26). Qed.
Lemma lem148628 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem148629 (x : nat) : (term27 x) = (term28 x).
Proof. exact (MK_COMB (@lem148628) (@lem148627 x)). Qed.
Lemma lem148630 (n : nat) (m : nat) : (Peano.lt n m) = (Peano.lt n m).
Proof. exact (eq_refl (Peano.lt n m)). Qed.
Lemma lem148631 (x : nat) (n : nat) (m : nat) : (term29 x n m) = (term30 x n m).
Proof. exact (MK_COMB (@lem148629 x) (@lem148630 n m)). Qed.
Lemma lem148634 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem148635 (x : nat) (n : nat) (m : nat) : (term31 x n m) = (term32 x n m).
Proof. exact (MK_COMB (@lem148634) (@lem148631 x n m)). Qed.
Lemma lem148646 (x : nat) (n : nat) (m : nat) : (term33 x n m) = (term33 x n m).
Proof. exact (eq_refl (term33 x n m)). Qed.
Lemma lem148647 (x : nat) (n : nat) (m : nat) : (term19 x n m) = (term34 x n m).
Proof. exact (MK_COMB (@lem148635 x n m) (@lem148646 x n m)). Qed.
Lemma lem148650 (x : nat) (n : nat) (m : nat) : (term18 n x m) = (term34 x n m).
Proof. exact (TRANS (@lem148620 x n m) (@lem148647 x n m)). Qed.
Lemma lem148651 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem148652 (x : nat) (n : nat) (m : nat) : (term23 n x m) = (term35 x n m).
Proof. exact (MK_COMB (@lem148651) (@lem148650 x n m)). Qed.
Lemma lem148654 (t1 : Prop) (t2 : Prop) : (term36 t1 t2) = (term37 t1 t2).
Proof. exact (proj2 (@lem148595 t1 t2)). Qed.
Lemma lem148655 (x : nat) (n : nat) (m : nat) : (term35 x n m) = (term38 x n m).
Proof. exact (@lem148654 (term30 x n m) (term33 x n m)). Qed.
Lemma lem148659 (t1 : Prop) (t2 : Prop) : (term39 t1 t2) = (term40 t1 t2).
Proof. exact (proj1 (@lem148595 t1 t2)). Qed.
Lemma lem148660 (x : nat) (n : nat) (m : nat) : (term41 x n m) = (term42 x n m).
Proof. exact (@lem148659 (term25 x) (Peano.lt n m)). Qed.
Lemma lem148664 (t : Prop) : (term43 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem148665 (x : nat) : (term44 x) = (term45 x).
Proof. exact (@lem148664 (term45 x)). Qed.
Lemma lem148666 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem148667 (x : nat) : (term46 x) = (term47 x).
Proof. exact (MK_COMB (@lem148666) (@lem148665 x)). Qed.
Lemma lem148668 (n : nat) (m : nat) : (term0 n m) = (term0 n m).
Proof. exact (eq_refl (term0 n m)). Qed.
Lemma lem148669 (x : nat) (n : nat) (m : nat) : (term42 x n m) = (term48 x n m).
Proof. exact (MK_COMB (@lem148667 x) (@lem148668 n m)). Qed.
Lemma lem148672 (x : nat) (n : nat) (m : nat) : (term41 x n m) = (term48 x n m).
Proof. exact (TRANS (@lem148660 x n m) (@lem148669 x n m)). Qed.
Lemma lem148673 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem148674 (x : nat) (n : nat) (m : nat) : (term49 x n m) = (term50 x n m).
Proof. exact (MK_COMB (@lem148673) (@lem148672 x n m)). Qed.
Lemma lem148676 (t1 : Prop) (t2 : Prop) : (term39 t1 t2) = (term40 t1 t2).
Proof. exact (proj1 (@lem148595 t1 t2)). Qed.
Lemma lem148677 (x : nat) (n : nat) (m : nat) : (term51 x n m) = (term52 x n m).
Proof. exact (@lem148676 (x = (NUMERAL 0)) (term53 n m)). Qed.
Lemma lem148683 (t1 : Prop) (t2 : Prop) : (term39 t1 t2) = (term40 t1 t2).
Proof. exact (proj1 (@lem148595 t1 t2)). Qed.
Lemma lem148684 (n : nat) (m : nat) : (term54 n m) = (term55 n m).
Proof. exact (@lem148683 (term56 n) (m = (NUMERAL 0))). Qed.
Lemma lem148688 (t : Prop) : (term43 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem148689 (n : nat) : (term57 n) = (n = (NUMERAL 0)).
Proof. exact (@lem148688 (n = (NUMERAL 0))). Qed.
Lemma lem148692 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem148693 (n : nat) : (term58 n) = (term59 n).
Proof. exact (MK_COMB (@lem148692) (@lem148689 n)). Qed.
Lemma lem148696 (m : nat) : (term56 m) = (term56 m).
Proof. exact (eq_refl (term56 m)). Qed.
Lemma lem148697 (n : nat) (m : nat) : (term55 n m) = (term60 n m).
Proof. exact (MK_COMB (@lem148693 n) (@lem148696 m)). Qed.
Lemma lem148700 (n : nat) (m : nat) : (term54 n m) = (term60 n m).
Proof. exact (TRANS (@lem148684 n m) (@lem148697 n m)). Qed.
Lemma lem148701 (x : nat) : (term61 x) = (term61 x).
Proof. exact (eq_refl (term61 x)). Qed.
Lemma lem148702 (x : nat) (n : nat) (m : nat) : (term52 x n m) = (term62 x n m).
Proof. exact (MK_COMB (@lem148701 x) (@lem148700 n m)). Qed.
Lemma lem148705 (x : nat) (n : nat) (m : nat) : (term51 x n m) = (term62 x n m).
Proof. exact (TRANS (@lem148677 x n m) (@lem148702 x n m)). Qed.
Lemma lem148706 (x : nat) (n : nat) (m : nat) : (term38 x n m) = (term63 x n m).
Proof. exact (MK_COMB (@lem148674 x n m) (@lem148705 x n m)). Qed.
Lemma lem148709 (x : nat) (n : nat) (m : nat) : (term35 x n m) = (term63 x n m).
Proof. exact (TRANS (@lem148655 x n m) (@lem148706 x n m)). Qed.
Lemma lem148710 (x : nat) (n : nat) (m : nat) : (term23 n x m) = (term63 x n m).
Proof. exact (TRANS (@lem148652 x n m) (@lem148709 x n m)). Qed.
Lemma lem148711 (x : nat) (n : nat) (m : nat) : (term22 m x n) = (term63 x n m).
Proof. exact (TRANS (@lem148617 n x m) (@lem148710 x n m)). Qed.
Lemma lem148712 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem148713 (x : nat) (n : nat) (m : nat) : (term64 m x n) = (term65 x n m).
Proof. exact (MK_COMB (@lem148712) (@lem148711 x n m)). Qed.
Lemma lem148731 (m : nat) (n : nat) : (Peano.le n m) = (term0 m n).
Proof. exact (EQ_MP (@lem148611 m n) (@lem148610 m n)). Qed.
Lemma lem148732 (n : nat) (m : nat) : (Peano.le m n) = (term0 n m).
Proof. exact (@lem148731 n m). Qed.
Lemma lem148733 (x : nat) : (term66 x) = (term66 x).
Proof. exact (eq_refl (term66 x)). Qed.
Lemma lem148734 (x : nat) (n : nat) (m : nat) : (term67 x m n) = (term68 x n m).
Proof. exact (MK_COMB (@lem148733 x) (@lem148732 n m)). Qed.
Lemma lem148737 (x : nat) (m : nat) (n : nat) : (term69 x m n) = (term69 x m n).
Proof. exact (eq_refl (term69 x m n)). Qed.
Lemma lem148738 (x : nat) (n : nat) (m : nat) : (term70 x m n) = (term71 x n m).
Proof. exact (MK_COMB (@lem148737 x m n) (@lem148734 x n m)). Qed.
Lemma lem148741 (x : nat) (n : nat) (m : nat) : ((term22 m x n) = (term70 x m n)) = ((term63 x n m) = (term71 x n m)).
Proof. exact (MK_COMB (@lem148713 x n m) (@lem148738 x n m)). Qed.
Lemma lem148744 (x : nat) (m : nat) (n : nat) : ((term63 x n m) = (term71 x n m)) = ((term22 m x n) = (term70 x m n)).
Proof. exact (SYM (@lem148741 x n m)). Qed.
Lemma lem148745 (_474 : Prop) (_475 : Prop) (_476 : Prop -> Prop) (_477 : Prop) : (term72 _476 _475 _474 _477) = (term73 _474 _475 _476 _477).
Proof. exact (@lem13473 Prop _474 _475 _476 _477). Qed.
Lemma lem148746 (_474 : Prop) (_475 : Prop) (x : nat) (n : nat) (m : nat) (_477 : Prop) : (term74 x n m _475 _474 _477) = (term75 _474 _475 x n m _477).
Proof. exact (@lem148745 _474 _475 (term76 x n m) _477). Qed.
Lemma lem148747 (x : nat) (n : nat) (m : nat) : (term77 x n m) = (term78 x n m).
Proof. exact (@lem148746 (term79 m n) (x = (NUMERAL 0)) x n m (term68 x n m)). Qed.
Lemma lem148748 (x : nat) (n : nat) (m : nat) : (term80 x n m) = ((term63 x n m) = (term68 x n m)).
Proof. exact (eq_refl (term80 x n m)). Qed.
Lemma lem148749 (x : nat) : (term81 x) = (term81 x).
Proof. exact (eq_refl (term81 x)). Qed.
Lemma lem148750 (x : nat) (n : nat) (m : nat) : (term82 x n m) = (term83 x n m).
Proof. exact (MK_COMB (@lem148749 x) (@lem148748 x n m)). Qed.
Lemma lem148751 (x : nat) (m : nat) (n : nat) : (term84 x m n) = ((term63 x n m) = (term79 m n)).
Proof. exact (eq_refl (term84 x m n)). Qed.
Lemma lem148752 (x : nat) : (term85 x) = (term85 x).
Proof. exact (eq_refl (term85 x)). Qed.
Lemma lem148753 (x : nat) (m : nat) (n : nat) : (term86 x m n) = (term87 x m n).
Proof. exact (MK_COMB (@lem148752 x) (@lem148751 x m n)). Qed.
Lemma lem148754 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem148755 (x : nat) (m : nat) (n : nat) : (term88 x m n) = (term89 x m n).
Proof. exact (MK_COMB (@lem148754) (@lem148753 x m n)). Qed.
Lemma lem148756 (x : nat) (n : nat) (m : nat) : (term78 x n m) = (term90 x n m).
Proof. exact (MK_COMB (@lem148755 x m n) (@lem148750 x n m)). Qed.
Lemma lem148757 (x : nat) (n : nat) (m : nat) : (term77 x n m) = ((term63 x n m) = (term71 x n m)).
Proof. exact (eq_refl (term77 x n m)). Qed.
Lemma lem148758 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem148759 (x : nat) (n : nat) (m : nat) : (term91 x n m) = (term92 x n m).
Proof. exact (MK_COMB (@lem148758) (@lem148757 x n m)). Qed.
Lemma lem148760 (x : nat) (n : nat) (m : nat) : ((term77 x n m) = (term78 x n m)) = (((term63 x n m) = (term71 x n m)) = (term90 x n m)).
Proof. exact (MK_COMB (@lem148759 x n m) (@lem148756 x n m)). Qed.
Lemma lem148761 (x : nat) (n : nat) (m : nat) : ((term63 x n m) = (term71 x n m)) = (term90 x n m).
Proof. exact (EQ_MP (@lem148760 x n m) (@lem148747 x n m)). Qed.
Lemma lem148762 (x : nat) (n : nat) (m : nat) : (term90 x n m) = ((term63 x n m) = (term71 x n m)).
Proof. exact (SYM (@lem148761 x n m)). Qed.
Lemma lem148763 (x : nat) (h1 : x = (NUMERAL 0)) : x = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem148764 (x : nat) : (x = (NUMERAL 0)) = ((x = (NUMERAL 0)) = True).
Proof. exact (@lem7 (x = (NUMERAL 0))). Qed.
Lemma lem148765 (x : nat) (h1 : x = (NUMERAL 0)) : (x = (NUMERAL 0)) = True.
Proof. exact (EQ_MP (@lem148764 x) (@lem148763 x h1)). Qed.
Lemma lem148766 (x : nat) (m : nat) (n : nat) : (term93 x m n) = (term93 x m n).
Proof. exact (eq_refl (term93 x m n)). Qed.
Lemma lem148767 (m : nat) (n : nat) (x : nat) (h1 : x = (NUMERAL 0)) : (term94 m n x) = (term95 x m n).
Proof. exact (MK_COMB (@lem148766 x m n) (@lem148765 x h1)). Qed.
Lemma lem148768 (x : nat) (m : nat) (n : nat) : (term95 x m n) = ((term96 x n m) = (term79 m n)).
Proof. exact (eq_refl (term95 x m n)). Qed.
Lemma lem148769 (m : nat) (n : nat) (x : nat) : (term97 m n x) = (term97 m n x).
Proof. exact (eq_refl (term97 m n x)). Qed.
Lemma lem148770 (x : nat) (m : nat) (n : nat) : ((term94 m n x) = (term95 x m n)) = ((term94 m n x) = ((term96 x n m) = (term79 m n))).
Proof. exact (MK_COMB (@lem148769 m n x) (@lem148768 x m n)). Qed.
Lemma lem148771 (x : nat) (m : nat) (n : nat) : (term94 m n x) = ((term63 x n m) = (term79 m n)).
Proof. exact (eq_refl (term94 m n x)). Qed.
Lemma lem148772 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem148773 (x : nat) (m : nat) (n : nat) : (term97 m n x) = (term98 x m n).
Proof. exact (MK_COMB (@lem148772) (@lem148771 x m n)). Qed.
Lemma lem148774 (x : nat) (m : nat) (n : nat) : ((term96 x n m) = (term79 m n)) = ((term96 x n m) = (term79 m n)).
Proof. exact (eq_refl ((term96 x n m) = (term79 m n))). Qed.
Lemma lem148775 (x : nat) (m : nat) (n : nat) : ((term94 m n x) = ((term96 x n m) = (term79 m n))) = (((term63 x n m) = (term79 m n)) = ((term96 x n m) = (term79 m n))).
Proof. exact (MK_COMB (@lem148773 x m n) (@lem148774 x m n)). Qed.
Lemma lem148776 (x : nat) (m : nat) (n : nat) : ((term94 m n x) = (term95 x m n)) = (((term63 x n m) = (term79 m n)) = ((term96 x n m) = (term79 m n))).
Proof. exact (TRANS (@lem148770 x m n) (@lem148775 x m n)). Qed.
Lemma lem148777 (m : nat) (n : nat) (x : nat) (h1 : x = (NUMERAL 0)) : ((term63 x n m) = (term79 m n)) = ((term96 x n m) = (term79 m n)).
Proof. exact (EQ_MP (@lem148776 x m n) (@lem148767 m n x h1)). Qed.
Lemma lem148778 (m : nat) (n : nat) (x : nat) (h1 : x = (NUMERAL 0)) : ((term96 x n m) = (term79 m n)) = ((term63 x n m) = (term79 m n)).
Proof. exact (SYM (@lem148777 m n x h1)). Qed.
Lemma lem148779 (x : nat) (h1 : term56 x) : term56 x.
Proof. exact (h1). Qed.
Lemma lem148780 (x : nat) : term99 x.
Proof. exact (@lem82 (x = (NUMERAL 0))). Qed.
Lemma lem148781 (x : nat) (h1 : term56 x) : (x = (NUMERAL 0)) = False.
Proof. exact (@lem148780 x (@lem148779 x h1)). Qed.
Lemma lem148782 (x : nat) (n : nat) (m : nat) : (term100 x n m) = (term100 x n m).
Proof. exact (eq_refl (term100 x n m)). Qed.
Lemma lem148783 (n : nat) (m : nat) (x : nat) (h1 : term56 x) : (term101 n m x) = (term102 x n m).
Proof. exact (MK_COMB (@lem148782 x n m) (@lem148781 x h1)). Qed.
Lemma lem148784 (x : nat) (n : nat) (m : nat) : (term102 x n m) = ((term103 x n m) = (term68 x n m)).
Proof. exact (eq_refl (term102 x n m)). Qed.
Lemma lem148785 (n : nat) (m : nat) (x : nat) : (term104 n m x) = (term104 n m x).
Proof. exact (eq_refl (term104 n m x)). Qed.
Lemma lem148786 (x : nat) (n : nat) (m : nat) : ((term101 n m x) = (term102 x n m)) = ((term101 n m x) = ((term103 x n m) = (term68 x n m))).
Proof. exact (MK_COMB (@lem148785 n m x) (@lem148784 x n m)). Qed.
Lemma lem148787 (x : nat) (n : nat) (m : nat) : (term101 n m x) = ((term63 x n m) = (term68 x n m)).
Proof. exact (eq_refl (term101 n m x)). Qed.
Lemma lem148788 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem148789 (x : nat) (n : nat) (m : nat) : (term104 n m x) = (term105 x n m).
Proof. exact (MK_COMB (@lem148788) (@lem148787 x n m)). Qed.
Lemma lem148790 (x : nat) (n : nat) (m : nat) : ((term103 x n m) = (term68 x n m)) = ((term103 x n m) = (term68 x n m)).
Proof. exact (eq_refl ((term103 x n m) = (term68 x n m))). Qed.
Lemma lem148791 (x : nat) (n : nat) (m : nat) : ((term101 n m x) = ((term103 x n m) = (term68 x n m))) = (((term63 x n m) = (term68 x n m)) = ((term103 x n m) = (term68 x n m))).
Proof. exact (MK_COMB (@lem148789 x n m) (@lem148790 x n m)). Qed.
Lemma lem148792 (x : nat) (n : nat) (m : nat) : ((term101 n m x) = (term102 x n m)) = (((term63 x n m) = (term68 x n m)) = ((term103 x n m) = (term68 x n m))).
Proof. exact (TRANS (@lem148786 x n m) (@lem148791 x n m)). Qed.
Lemma lem148793 (n : nat) (m : nat) (x : nat) (h1 : term56 x) : ((term63 x n m) = (term68 x n m)) = ((term103 x n m) = (term68 x n m)).
Proof. exact (EQ_MP (@lem148792 x n m) (@lem148783 n m x h1)). Qed.
Lemma lem148794 (n : nat) (m : nat) (x : nat) (h1 : term56 x) : ((term103 x n m) = (term68 x n m)) = ((term63 x n m) = (term68 x n m)).
Proof. exact (SYM (@lem148793 n m x h1)). Qed.
Lemma lem148795 : term106.
Proof. exact (proj2 (@lem89994)). Qed.
Lemma lem148796 (m : nat) : term107 m.
Proof. exact (@lem148795 m). Qed.
Lemma lem148797 (m : nat) : (term107 m) = (term108 m).
Proof. exact (eq_refl (term107 m)). Qed.
Lemma lem148798 (m : nat) : term108 m.
Proof. exact (EQ_MP (@lem148797 m) (@lem148796 m)). Qed.
Lemma lem148799 (m : nat) (n : nat) : term109 m n.
Proof. exact (@lem148798 m n). Qed.
Lemma lem148800 (m : nat) (n : nat) : (term109 m n) = ((term110 m n) = (term111 m n)).
Proof. exact (eq_refl (term109 m n)). Qed.
Lemma lem148802 : term112.
Proof. exact (proj1 (@lem89994)). Qed.
Lemma lem148803 (m : nat) : term113 m.
Proof. exact (@lem148802 m). Qed.
Lemma lem148804 (m : nat) : (term113 m) = ((term114 m) = False).
Proof. exact (eq_refl (term113 m)). Qed.
Lemma lem148813 (x : nat) (h1 : x = (NUMERAL 0)) : x = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem148814 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem148815 (x : nat) (h1 : x = (NUMERAL 0)) : (Peano.lt x) = term115.
Proof. exact (MK_COMB (@lem148814) (@lem148813 x h1)). Qed.
Lemma lem148817 : term26 = term116.
Proof. exact (EQ_MP (@lem80550) (@lem0)). Qed.
Lemma lem148819 : term117 = term118.
Proof. exact (EQ_MP (@lem80360) (@lem0)). Qed.
Lemma lem148820 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem148821 : term116 = term119.
Proof. exact (MK_COMB (@lem148820) (@lem148819)). Qed.
Lemma lem148822 : term26 = term119.
Proof. exact (TRANS (@lem148817) (@lem148821)). Qed.
Lemma lem148823 (x : nat) (h1 : x = (NUMERAL 0)) : (term45 x) = term120.
Proof. exact (MK_COMB (@lem148815 x h1) (@lem148822)). Qed.
Lemma lem148825 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (EQ_MP (@lem148800 m n) (@lem148799 m n)). Qed.
Lemma lem148826 : term120 = term121.
Proof. exact (@lem148825 (NUMERAL 0) term118). Qed.
Lemma lem148832 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (EQ_MP (@lem148800 m n) (@lem148799 m n)). Qed.
Lemma lem148833 : term122 = term123.
Proof. exact (@lem148832 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem148837 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem148838 (x : nat) : (x = x) = True.
Proof. exact (@lem148837 nat x). Qed.
Lemma lem148839 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem148838 (NUMERAL 0)). Qed.
Lemma lem148840 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem148841 : term124 = (or True).
Proof. exact (MK_COMB (@lem148840) (@lem148839)). Qed.
Lemma lem148843 (m : nat) : (term114 m) = False.
Proof. exact (EQ_MP (@lem148804 m) (@lem148803 m)). Qed.
Lemma lem148844 : term125 = False.
Proof. exact (@lem148843 (NUMERAL 0)). Qed.
Lemma lem148845 : term123 = (True \/ False).
Proof. exact (MK_COMB (@lem148841) (@lem148844)). Qed.
Lemma lem148847 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem148848 : (True \/ False) = True.
Proof. exact (@lem148847 False). Qed.
Lemma lem148849 : term123 = True.
Proof. exact (TRANS (@lem148845) (@lem148848)). Qed.
Lemma lem148850 : term122 = True.
Proof. exact (TRANS (@lem148833) (@lem148849)). Qed.
Lemma lem148851 : term126 = term126.
Proof. exact (eq_refl term126). Qed.
Lemma lem148852 : term121 = term127.
Proof. exact (MK_COMB (@lem148851) (@lem148850)). Qed.
Lemma lem148854 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem148855 : term127 = True.
Proof. exact (@lem148854 ((NUMERAL 0) = term118)). Qed.
Lemma lem148856 : term121 = True.
Proof. exact (TRANS (@lem148852) (@lem148855)). Qed.
Lemma lem148857 : term120 = True.
Proof. exact (TRANS (@lem148826) (@lem148856)). Qed.
Lemma lem148858 (x : nat) (h1 : x = (NUMERAL 0)) : (term45 x) = True.
Proof. exact (TRANS (@lem148823 x h1) (@lem148857)). Qed.
Lemma lem148859 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem148860 (x : nat) (h1 : x = (NUMERAL 0)) : (term47 x) = (or True).
Proof. exact (MK_COMB (@lem148859) (@lem148858 x h1)). Qed.
Lemma lem148861 (n : nat) (m : nat) : (term0 n m) = (term0 n m).
Proof. exact (eq_refl (term0 n m)). Qed.
Lemma lem148862 (n : nat) (m : nat) (x : nat) (h1 : x = (NUMERAL 0)) : (term48 x n m) = (term128 n m).
Proof. exact (MK_COMB (@lem148860 x h1) (@lem148861 n m)). Qed.
Lemma lem148864 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem148865 (n : nat) (m : nat) : (term128 n m) = True.
Proof. exact (@lem148864 (term0 n m)). Qed.
Lemma lem148866 (n : nat) (m : nat) (x : nat) (h1 : x = (NUMERAL 0)) : (term48 x n m) = True.
Proof. exact (TRANS (@lem148862 n m x h1) (@lem148865 n m)). Qed.
Lemma lem148867 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem148868 (n : nat) (m : nat) (x : nat) (h1 : x = (NUMERAL 0)) : (term50 x n m) = (and True).
Proof. exact (MK_COMB (@lem148867) (@lem148866 n m x h1)). Qed.
Lemma lem148872 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem148873 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem148874 : term129 = (or False).
Proof. exact (MK_COMB (@lem148873) (@lem148872)). Qed.
Lemma lem148881 (n : nat) (m : nat) : (term60 n m) = (term60 n m).
Proof. exact (eq_refl (term60 n m)). Qed.
Lemma lem148882 (n : nat) (m : nat) : (term130 n m) = (term131 n m).
Proof. exact (MK_COMB (@lem148874) (@lem148881 n m)). Qed.
Lemma lem148884 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem148885 (n : nat) (m : nat) : (term131 n m) = (term60 n m).
Proof. exact (@lem148884 (term60 n m)). Qed.
Lemma lem148892 (n : nat) (m : nat) : (term130 n m) = (term60 n m).
Proof. exact (TRANS (@lem148882 n m) (@lem148885 n m)). Qed.
Lemma lem148893 (n : nat) (m : nat) (x : nat) (h1 : x = (NUMERAL 0)) : (term96 x n m) = (term132 n m).
Proof. exact (MK_COMB (@lem148868 n m x h1) (@lem148892 n m)). Qed.
Lemma lem148895 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem148896 (n : nat) (m : nat) : (term132 n m) = (term60 n m).
Proof. exact (@lem148895 (term60 n m)). Qed.
Lemma lem148903 (n : nat) (m : nat) (x : nat) (h1 : x = (NUMERAL 0)) : (term96 x n m) = (term60 n m).
Proof. exact (TRANS (@lem148893 n m x h1) (@lem148896 n m)). Qed.
Lemma lem148904 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem148905 (n : nat) (m : nat) (x : nat) (h1 : x = (NUMERAL 0)) : (term133 x n m) = (term134 n m).
Proof. exact (MK_COMB (@lem148904) (@lem148903 n m x h1)). Qed.
Lemma lem148914 (m : nat) (n : nat) : (term79 m n) = (term79 m n).
Proof. exact (eq_refl (term79 m n)). Qed.
Lemma lem148915 (m : nat) (n : nat) (x : nat) (h1 : x = (NUMERAL 0)) : ((term96 x n m) = (term79 m n)) = ((term60 n m) = (term79 m n)).
Proof. exact (MK_COMB (@lem148905 n m x h1) (@lem148914 m n)). Qed.
Lemma lem148918 (m : nat) (n : nat) (x : nat) (h1 : x = (NUMERAL 0)) : ((term60 n m) = (term79 m n)) = ((term96 x n m) = (term79 m n)).
Proof. exact (SYM (@lem148915 m n x h1)). Qed.
Lemma lem148919 : term106.
Proof. exact (proj2 (@lem89994)). Qed.
Lemma lem148920 (m : nat) : term107 m.
Proof. exact (@lem148919 m). Qed.
Lemma lem148921 (m : nat) : (term107 m) = (term108 m).
Proof. exact (eq_refl (term107 m)). Qed.
Lemma lem148922 (m : nat) : term108 m.
Proof. exact (EQ_MP (@lem148921 m) (@lem148920 m)). Qed.
Lemma lem148923 (m : nat) (n : nat) : term109 m n.
Proof. exact (@lem148922 m n). Qed.
Lemma lem148924 (m : nat) (n : nat) : (term109 m n) = ((term110 m n) = (term111 m n)).
Proof. exact (eq_refl (term109 m n)). Qed.
Lemma lem148926 : term112.
Proof. exact (proj1 (@lem89994)). Qed.
Lemma lem148927 (m : nat) : term113 m.
Proof. exact (@lem148926 m). Qed.
Lemma lem148928 (m : nat) : (term113 m) = ((term114 m) = False).
Proof. exact (eq_refl (term113 m)). Qed.
Lemma lem148930 (x : nat) : term99 x.
Proof. exact (@lem82 (x = (NUMERAL 0))). Qed.
Lemma lem148950 : term26 = term116.
Proof. exact (EQ_MP (@lem80550) (@lem0)). Qed.
Lemma lem148952 : term117 = term118.
Proof. exact (EQ_MP (@lem80360) (@lem0)). Qed.
Lemma lem148953 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem148954 : term116 = term119.
Proof. exact (MK_COMB (@lem148953) (@lem148952)). Qed.
Lemma lem148955 : term26 = term119.
Proof. exact (TRANS (@lem148950) (@lem148954)). Qed.
Lemma lem148956 (x : nat) : (Peano.lt x) = (Peano.lt x).
Proof. exact (eq_refl (Peano.lt x)). Qed.
Lemma lem148957 (x : nat) : (term45 x) = (term135 x).
Proof. exact (MK_COMB (@lem148956 x) (@lem148955)). Qed.
Lemma lem148959 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (EQ_MP (@lem148924 m n) (@lem148923 m n)). Qed.
Lemma lem148960 (x : nat) : (term135 x) = (term136 x).
Proof. exact (@lem148959 x term118). Qed.
Lemma lem148966 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (EQ_MP (@lem148924 m n) (@lem148923 m n)). Qed.
Lemma lem148967 (x : nat) : (term137 x) = (term138 x).
Proof. exact (@lem148966 x (NUMERAL 0)). Qed.
Lemma lem148971 (x : nat) (h1 : term56 x) : (x = (NUMERAL 0)) = False.
Proof. exact (@lem148930 x (@lem148779 x h1)). Qed.
Lemma lem148972 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem148973 (x : nat) (h1 : term56 x) : (term59 x) = (or False).
Proof. exact (MK_COMB (@lem148972) (@lem148971 x h1)). Qed.
Lemma lem148975 (m : nat) : (term114 m) = False.
Proof. exact (EQ_MP (@lem148928 m) (@lem148927 m)). Qed.
Lemma lem148976 (x : nat) : (term114 x) = False.
Proof. exact (@lem148975 x). Qed.
Lemma lem148977 (x : nat) (h1 : term56 x) : (term138 x) = (False \/ False).
Proof. exact (MK_COMB (@lem148973 x h1) (@lem148976 x)). Qed.
Lemma lem148979 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem148980 : (False \/ False) = False.
Proof. exact (@lem148979 False). Qed.
Lemma lem148981 (x : nat) (h1 : term56 x) : (term138 x) = False.
Proof. exact (TRANS (@lem148977 x h1) (@lem148980)). Qed.
Lemma lem148982 (x : nat) (h1 : term56 x) : (term137 x) = False.
Proof. exact (TRANS (@lem148967 x) (@lem148981 x h1)). Qed.
Lemma lem148983 (x : nat) : (term139 x) = (term139 x).
Proof. exact (eq_refl (term139 x)). Qed.
Lemma lem148984 (x : nat) (h1 : term56 x) : (term136 x) = (term140 x).
Proof. exact (MK_COMB (@lem148983 x) (@lem148982 x h1)). Qed.
Lemma lem148986 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem148987 (x : nat) : (term140 x) = (x = term118).
Proof. exact (@lem148986 (x = term118)). Qed.
Lemma lem148990 (x : nat) (h1 : term56 x) : (term136 x) = (x = term118).
Proof. exact (TRANS (@lem148984 x h1) (@lem148987 x)). Qed.
Lemma lem148991 (x : nat) (h1 : term56 x) : (term135 x) = (x = term118).
Proof. exact (TRANS (@lem148960 x) (@lem148990 x h1)). Qed.
Lemma lem148992 (x : nat) (h1 : term56 x) : (term45 x) = (x = term118).
Proof. exact (TRANS (@lem148957 x) (@lem148991 x h1)). Qed.
Lemma lem148993 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem148994 (x : nat) (h1 : term56 x) : (term47 x) = (term139 x).
Proof. exact (MK_COMB (@lem148993) (@lem148992 x h1)). Qed.
Lemma lem148995 (n : nat) (m : nat) : (term0 n m) = (term0 n m).
Proof. exact (eq_refl (term0 n m)). Qed.
Lemma lem148996 (n : nat) (m : nat) (x : nat) (h1 : term56 x) : (term48 x n m) = (term141 x n m).
Proof. exact (MK_COMB (@lem148994 x h1) (@lem148995 n m)). Qed.
Lemma lem148999 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem149000 (n : nat) (m : nat) (x : nat) (h1 : term56 x) : (term50 x n m) = (term142 x n m).
Proof. exact (MK_COMB (@lem148999) (@lem148996 n m x h1)). Qed.
Lemma lem149004 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem149005 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem149006 : term143 = (or True).
Proof. exact (MK_COMB (@lem149005) (@lem149004)). Qed.
Lemma lem149013 (n : nat) (m : nat) : (term60 n m) = (term60 n m).
Proof. exact (eq_refl (term60 n m)). Qed.
Lemma lem149014 (n : nat) (m : nat) : (term144 n m) = (term145 n m).
Proof. exact (MK_COMB (@lem149006) (@lem149013 n m)). Qed.
Lemma lem149016 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem149017 (n : nat) (m : nat) : (term145 n m) = True.
Proof. exact (@lem149016 (term60 n m)). Qed.
Lemma lem149018 (n : nat) (m : nat) : (term144 n m) = True.
Proof. exact (TRANS (@lem149014 n m) (@lem149017 n m)). Qed.
Lemma lem149019 (n : nat) (m : nat) (x : nat) (h1 : term56 x) : (term103 x n m) = (term146 x n m).
Proof. exact (MK_COMB (@lem149000 n m x h1) (@lem149018 n m)). Qed.
Lemma lem149021 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem149022 (x : nat) (n : nat) (m : nat) : (term146 x n m) = (term141 x n m).
Proof. exact (@lem149021 (term141 x n m)). Qed.
Lemma lem149027 (n : nat) (m : nat) (x : nat) (h1 : term56 x) : (term103 x n m) = (term141 x n m).
Proof. exact (TRANS (@lem149019 n m x h1) (@lem149022 x n m)). Qed.
Lemma lem149028 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem149029 (n : nat) (m : nat) (x : nat) (h1 : term56 x) : (term147 x n m) = (term148 x n m).
Proof. exact (MK_COMB (@lem149028) (@lem149027 n m x h1)). Qed.
Lemma lem149035 : term117 = term118.
Proof. exact (EQ_MP (@lem80360) (@lem0)). Qed.
Lemma lem149036 (x : nat) : (@eq nat x) = (@eq nat x).
Proof. exact (eq_refl (@eq nat x)). Qed.
Lemma lem149037 (x : nat) : (x = term117) = (x = term118).
Proof. exact (MK_COMB (@lem149036 x) (@lem149035)). Qed.
Lemma lem149040 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem149041 (x : nat) : (term66 x) = (term139 x).
Proof. exact (MK_COMB (@lem149040) (@lem149037 x)). Qed.
Lemma lem149042 (n : nat) (m : nat) : (term0 n m) = (term0 n m).
Proof. exact (eq_refl (term0 n m)). Qed.
Lemma lem149043 (x : nat) (n : nat) (m : nat) : (term68 x n m) = (term141 x n m).
Proof. exact (MK_COMB (@lem149041 x) (@lem149042 n m)). Qed.
Lemma lem149046 (n : nat) (m : nat) (x : nat) (h1 : term56 x) : ((term103 x n m) = (term68 x n m)) = ((term141 x n m) = (term141 x n m)).
Proof. exact (MK_COMB (@lem149029 n m x h1) (@lem149043 x n m)). Qed.
Lemma lem149048 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem149049 (x : Prop) : (x = x) = True.
Proof. exact (@lem149048 Prop x). Qed.
Lemma lem149050 (x : nat) (n : nat) (m : nat) : ((term141 x n m) = (term141 x n m)) = True.
Proof. exact (@lem149049 (term141 x n m)). Qed.
Lemma lem149051 (n : nat) (m : nat) (x : nat) (h1 : term56 x) : ((term103 x n m) = (term68 x n m)) = True.
Proof. exact (TRANS (@lem149046 n m x h1) (@lem149050 x n m)). Qed.
Lemma lem149052 (n : nat) (m : nat) (x : nat) (h1 : term56 x) : True = ((term103 x n m) = (term68 x n m)).
Proof. exact (SYM (@lem149051 n m x h1)). Qed.
Lemma lem149053 (n : nat) (m : nat) (x : nat) (h1 : term56 x) : (term103 x n m) = (term68 x n m).
Proof. exact (EQ_MP (@lem149052 n m x h1) (@lem0)). Qed.
Lemma lem149072 (n : nat) : term149 n.
Proof. exact (@lem9851 (n = (NUMERAL 0))). Qed.
Lemma lem149073 (n : nat) : (term149 n) = (term150 n).
Proof. exact (eq_refl (term149 n)). Qed.
Lemma lem149074 (n : nat) : term150 n.
Proof. exact (EQ_MP (@lem149073 n) (@lem149072 n)). Qed.
Lemma lem149075 (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (n = (NUMERAL 0)) = True.
Proof. exact (h1). Qed.
Lemma lem149076 (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (n = (NUMERAL 0)) = False.
Proof. exact (h1). Qed.
Lemma lem149095 (m : nat) : (term151 m) = (term151 m).
Proof. exact (eq_refl (term151 m)). Qed.
Lemma lem149096 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (term152 m n) = (term153 m).
Proof. exact (MK_COMB (@lem149095 m) (@lem149075 n h1)). Qed.
Lemma lem149097 (m : nat) : (term153 m) = ((term154 m) = (term155 m)).
Proof. exact (eq_refl (term153 m)). Qed.
Lemma lem149098 (m : nat) (n : nat) : (term156 m n) = (term156 m n).
Proof. exact (eq_refl (term156 m n)). Qed.
Lemma lem149099 (n : nat) (m : nat) : ((term152 m n) = (term153 m)) = ((term152 m n) = ((term154 m) = (term155 m))).
Proof. exact (MK_COMB (@lem149098 m n) (@lem149097 m)). Qed.
Lemma lem149100 (m : nat) (n : nat) : (term152 m n) = ((term60 n m) = (term79 m n)).
Proof. exact (eq_refl (term152 m n)). Qed.
Lemma lem149101 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem149102 (m : nat) (n : nat) : (term156 m n) = (term157 m n).
Proof. exact (MK_COMB (@lem149101) (@lem149100 m n)). Qed.
Lemma lem149103 (m : nat) : ((term154 m) = (term155 m)) = ((term154 m) = (term155 m)).
Proof. exact (eq_refl ((term154 m) = (term155 m))). Qed.
Lemma lem149104 (n : nat) (m : nat) : ((term152 m n) = ((term154 m) = (term155 m))) = (((term60 n m) = (term79 m n)) = ((term154 m) = (term155 m))).
Proof. exact (MK_COMB (@lem149102 m n) (@lem149103 m)). Qed.
Lemma lem149105 (n : nat) (m : nat) : ((term152 m n) = (term153 m)) = (((term60 n m) = (term79 m n)) = ((term154 m) = (term155 m))).
Proof. exact (TRANS (@lem149099 n m) (@lem149104 n m)). Qed.
Lemma lem149106 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = True) : ((term60 n m) = (term79 m n)) = ((term154 m) = (term155 m)).
Proof. exact (EQ_MP (@lem149105 n m) (@lem149096 m n h1)). Qed.
Lemma lem149107 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = True) : ((term154 m) = (term155 m)) = ((term60 n m) = (term79 m n)).
Proof. exact (SYM (@lem149106 m n h1)). Qed.
Lemma lem149108 (m : nat) : (term151 m) = (term151 m).
Proof. exact (eq_refl (term151 m)). Qed.
Lemma lem149109 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (term152 m n) = (term158 m).
Proof. exact (MK_COMB (@lem149108 m) (@lem149076 n h1)). Qed.
Lemma lem149110 (m : nat) : (term158 m) = ((term159 m) = (term160 m)).
Proof. exact (eq_refl (term158 m)). Qed.
Lemma lem149111 (m : nat) (n : nat) : (term156 m n) = (term156 m n).
Proof. exact (eq_refl (term156 m n)). Qed.
Lemma lem149112 (n : nat) (m : nat) : ((term152 m n) = (term158 m)) = ((term152 m n) = ((term159 m) = (term160 m))).
Proof. exact (MK_COMB (@lem149111 m n) (@lem149110 m)). Qed.
Lemma lem149113 (m : nat) (n : nat) : (term152 m n) = ((term60 n m) = (term79 m n)).
Proof. exact (eq_refl (term152 m n)). Qed.
Lemma lem149114 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem149115 (m : nat) (n : nat) : (term156 m n) = (term157 m n).
Proof. exact (MK_COMB (@lem149114) (@lem149113 m n)). Qed.
Lemma lem149116 (m : nat) : ((term159 m) = (term160 m)) = ((term159 m) = (term160 m)).
Proof. exact (eq_refl ((term159 m) = (term160 m))). Qed.
Lemma lem149117 (n : nat) (m : nat) : ((term152 m n) = ((term159 m) = (term160 m))) = (((term60 n m) = (term79 m n)) = ((term159 m) = (term160 m))).
Proof. exact (MK_COMB (@lem149115 m n) (@lem149116 m)). Qed.
Lemma lem149118 (n : nat) (m : nat) : ((term152 m n) = (term158 m)) = (((term60 n m) = (term79 m n)) = ((term159 m) = (term160 m))).
Proof. exact (TRANS (@lem149112 n m) (@lem149117 n m)). Qed.
Lemma lem149119 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = False) : ((term60 n m) = (term79 m n)) = ((term159 m) = (term160 m)).
Proof. exact (EQ_MP (@lem149118 n m) (@lem149109 m n h1)). Qed.
Lemma lem149120 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = False) : ((term159 m) = (term160 m)) = ((term60 n m) = (term79 m n)).
Proof. exact (SYM (@lem149119 m n h1)). Qed.
Lemma lem149124 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem149125 (m : nat) : (term154 m) = True.
Proof. exact (@lem149124 (term56 m)). Qed.
Lemma lem149126 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem149127 (m : nat) : (term161 m) = (@eq Prop True).
Proof. exact (MK_COMB (@lem149126) (@lem149125 m)). Qed.
Lemma lem149131 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem149132 (m : nat) : (term155 m) = True.
Proof. exact (@lem149131 (m = (NUMERAL 0))). Qed.
Lemma lem149133 (m : nat) : ((term154 m) = (term155 m)) = (True = True).
Proof. exact (MK_COMB (@lem149127 m) (@lem149132 m)). Qed.
Lemma lem149135 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem149136 : (True = True) = True.
Proof. exact (@lem149135 True). Qed.
Lemma lem149137 (m : nat) : ((term154 m) = (term155 m)) = True.
Proof. exact (TRANS (@lem149133 m) (@lem149136)). Qed.
Lemma lem149138 (m : nat) : True = ((term154 m) = (term155 m)).
Proof. exact (SYM (@lem149137 m)). Qed.
Lemma lem149139 (m : nat) : (term154 m) = (term155 m).
Proof. exact (EQ_MP (@lem149138 m) (@lem0)). Qed.
Lemma lem149143 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem149144 (m : nat) : (term159 m) = (term56 m).
Proof. exact (@lem149143 (term56 m)). Qed.
Lemma lem149147 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem149148 (m : nat) : (term162 m) = (term163 m).
Proof. exact (MK_COMB (@lem149147) (@lem149144 m)). Qed.
Lemma lem149152 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem149153 (m : nat) : (term160 m) = (term56 m).
Proof. exact (@lem149152 (m = (NUMERAL 0))). Qed.
Lemma lem149156 (m : nat) : ((term159 m) = (term160 m)) = ((term56 m) = (term56 m)).
Proof. exact (MK_COMB (@lem149148 m) (@lem149153 m)). Qed.
Lemma lem149158 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem149159 (x : Prop) : (x = x) = True.
Proof. exact (@lem149158 Prop x). Qed.
Lemma lem149160 (m : nat) : ((term56 m) = (term56 m)) = True.
Proof. exact (@lem149159 (term56 m)). Qed.
Lemma lem149161 (m : nat) : ((term159 m) = (term160 m)) = True.
Proof. exact (TRANS (@lem149156 m) (@lem149160 m)). Qed.
Lemma lem149162 (m : nat) : True = ((term159 m) = (term160 m)).
Proof. exact (SYM (@lem149161 m)). Qed.
Lemma lem149163 (m : nat) : (term159 m) = (term160 m).
Proof. exact (EQ_MP (@lem149162 m) (@lem0)). Qed.
Lemma lem149164 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (term60 n m) = (term79 m n).
Proof. exact (EQ_MP (@lem149120 m n h1) (@lem149163 m)). Qed.
Lemma lem149165 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (term60 n m) = (term79 m n).
Proof. exact (EQ_MP (@lem149107 m n h1) (@lem149139 m)). Qed.
Lemma lem149168 (m : nat) (n : nat) : (term60 n m) = (term79 m n).
Proof. exact (or_elim (@lem149074 n) (fun h0 : (n = (NUMERAL 0)) = True => @lem149165 m n h0) (fun h0 : (n = (NUMERAL 0)) = False => @lem149164 m n h0)). Qed.
Lemma lem149169 (m : nat) (n : nat) : ((term60 n m) = (term79 m n)) = (((term60 n m) = (term79 m n)) = True).
Proof. exact (@lem7 ((term60 n m) = (term79 m n))). Qed.
Lemma lem149170 (m : nat) (n : nat) : ((term60 n m) = (term79 m n)) = True.
Proof. exact (EQ_MP (@lem149169 m n) (@lem149168 m n)). Qed.
Lemma lem149171 (m : nat) (n : nat) : True = ((term60 n m) = (term79 m n)).
Proof. exact (SYM (@lem149170 m n)). Qed.
Lemma lem149172 (m : nat) (n : nat) : (term60 n m) = (term79 m n).
Proof. exact (EQ_MP (@lem149171 m n) (@lem0)). Qed.
Lemma lem149173 (m : nat) (n : nat) (x : nat) (h1 : x = (NUMERAL 0)) : (term96 x n m) = (term79 m n).
Proof. exact (EQ_MP (@lem148918 m n x h1) (@lem149172 m n)). Qed.
Lemma lem149174 (n : nat) (m : nat) (x : nat) (h1 : term56 x) : (term63 x n m) = (term68 x n m).
Proof. exact (EQ_MP (@lem148794 n m x h1) (@lem149053 n m x h1)). Qed.
Lemma lem149175 (n : nat) (m : nat) (x : nat) (h1 : term56 x) : (term56 x) = ((term63 x n m) = (term68 x n m)).
Proof. exact (prop_ext (fun h2 : term56 x => @lem149174 n m x h1) (fun h2 : (term63 x n m) = (term68 x n m) => @lem148779 x h1)). Qed.
Lemma lem149176 (n : nat) (m : nat) (x : nat) (h1 : term56 x) : (term63 x n m) = (term68 x n m).
Proof. exact (EQ_MP (@lem149175 n m x h1) (@lem148779 x h1)). Qed.
Lemma lem149177 (x : nat) (n : nat) (m : nat) : term83 x n m.
Proof. exact (fun h0 : term56 x => @lem149176 n m x h0). Qed.
Lemma lem149178 (m : nat) (n : nat) (x : nat) (h1 : x = (NUMERAL 0)) : (term63 x n m) = (term79 m n).
Proof. exact (EQ_MP (@lem148778 m n x h1) (@lem149173 m n x h1)). Qed.
Lemma lem149179 (m : nat) (n : nat) (x : nat) (h1 : x = (NUMERAL 0)) : (x = (NUMERAL 0)) = ((term63 x n m) = (term79 m n)).
Proof. exact (prop_ext (fun h2 : x = (NUMERAL 0) => @lem149178 m n x h1) (fun h2 : (term63 x n m) = (term79 m n) => @lem148763 x h1)). Qed.
Lemma lem149180 (m : nat) (n : nat) (x : nat) (h1 : x = (NUMERAL 0)) : (term63 x n m) = (term79 m n).
Proof. exact (EQ_MP (@lem149179 m n x h1) (@lem148763 x h1)). Qed.
Lemma lem149181 (x : nat) (m : nat) (n : nat) : term87 x m n.
Proof. exact (fun h0 : x = (NUMERAL 0) => @lem149180 m n x h0). Qed.
Lemma lem149182 (x : nat) (n : nat) (m : nat) : term90 x n m.
Proof. exact (conj (@lem149181 x m n) (@lem149177 x n m)). Qed.
Lemma lem149183 (x : nat) (n : nat) (m : nat) : (term63 x n m) = (term71 x n m).
Proof. exact (EQ_MP (@lem148762 x n m) (@lem149182 x n m)). Qed.
Lemma lem149184 (x : nat) (m : nat) (n : nat) : (term22 m x n) = (term70 x m n).
Proof. exact (EQ_MP (@lem148744 x m n) (@lem149183 x n m)). Qed.
Lemma lem149189 (x : nat) (m : nat) : term164 x m.
Proof. exact (fun n : nat => @lem149184 x m n). Qed.
Lemma lem149194 (x : nat) : term165 x.
Proof. exact (fun m : nat => @lem149189 x m). Qed.
Lemma lem149199 : term166.
Proof. exact (fun x : nat => @lem149194 x). Qed.
