Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_POLY_CLAUSES_term_abbrevs.
Require Import REAL_ADD_AC_spec.
Require Import REAL_MUL_LZERO_spec.
Require Import thm0_spec.
Require Import thm1338512_spec.
Require Import thm1338712_spec.
Require Import thm1338912_spec.
Require Import thm1338986_spec.
Require Import thm1339188_spec.
Require Import thm1344310_spec.
Require Import thm1344311_spec.
Require Import thm1344313_spec.
Require Import thm1344314_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1383498 (x : real) : term0 x.
Proof. exact (@lem1338712 x). Qed.
Lemma lem1383499 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1383500 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1383499 x) (@lem1383498 x)). Qed.
Lemma lem1383501 (x : real) (y : real) : term2 x y.
Proof. exact (@lem1383500 x y). Qed.
Lemma lem1383502 (y : real) (x : real) : (term2 x y) = ((real_mul x y) = (real_mul y x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1383504 (n : real) (m : real) (p : real) : term3 n m p.
Proof. exact (proj2 (@lem1352530 n m p)). Qed.
Lemma lem1383508 (x : real) : term4 x.
Proof. exact (@lem1338986 x). Qed.
Lemma lem1383509 (x : real) : (term4 x) = ((term5 x) = x).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem1383511 (x : real) : term6 x.
Proof. exact (@lem1338512 x). Qed.
Lemma lem1383512 (x : real) : (term6 x) = ((term7 x) = x).
Proof. exact (eq_refl (term6 x)). Qed.
Lemma lem1383514 (x : real) : term8 x.
Proof. exact (@lem1338912 x). Qed.
Lemma lem1383515 (x : real) : (term8 x) = (term9 x).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem1383516 (x : real) : term9 x.
Proof. exact (EQ_MP (@lem1383515 x) (@lem1383514 x)). Qed.
Lemma lem1383517 (x : real) (y : real) : term10 x y.
Proof. exact (@lem1383516 x y). Qed.
Lemma lem1383518 (x : real) (y : real) : (term10 x y) = (term11 x y).
Proof. exact (eq_refl (term10 x y)). Qed.
Lemma lem1383519 (x : real) (y : real) : term11 x y.
Proof. exact (EQ_MP (@lem1383518 x y) (@lem1383517 x y)). Qed.
Lemma lem1383520 (x : real) (y : real) (z : real) : term12 x y z.
Proof. exact (@lem1383519 x y z). Qed.
Lemma lem1383521 (x : real) (y : real) (z : real) : (term12 x y z) = ((term13 x y z) = (term14 x y z)).
Proof. exact (eq_refl (term12 x y z)). Qed.
Lemma lem1383523 (x : real) : term15 x.
Proof. exact (@lem1357243 x). Qed.
Lemma lem1383524 (x : real) : (term15 x) = ((term16 x) = term17).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1383526 (x : real) : term18 x.
Proof. exact (@lem1339188 x). Qed.
Lemma lem1383527 (x : real) : (term18 x) = (term19 x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem1383528 (x : real) : term19 x.
Proof. exact (EQ_MP (@lem1383527 x) (@lem1383526 x)). Qed.
Lemma lem1383529 (x : real) (y : real) : term20 x y.
Proof. exact (@lem1383528 x y). Qed.
Lemma lem1383530 (y : real) (x : real) : (term20 x y) = (term21 y x).
Proof. exact (eq_refl (term20 x y)). Qed.
Lemma lem1383531 (y : real) (x : real) : term21 y x.
Proof. exact (EQ_MP (@lem1383530 y x) (@lem1383529 x y)). Qed.
Lemma lem1383532 (y : real) (x : real) (z : real) : term22 y x z.
Proof. exact (@lem1383531 y x z). Qed.
Lemma lem1383533 (y : real) (x : real) (z : real) : (term22 y x z) = ((term23 x y z) = (term24 y x z)).
Proof. exact (eq_refl (term22 y x z)). Qed.
Lemma lem1383535 (x : real) : term25 x.
Proof. exact (EQ_MP (@lem1344314 x) (@lem1344313 x)). Qed.
Lemma lem1383536 (x : real) (n : nat) : term26 x n.
Proof. exact (@lem1383535 x n). Qed.
Lemma lem1383537 (x : real) (n : nat) : (term26 x n) = ((term27 x n) = (term28 x n)).
Proof. exact (eq_refl (term26 x n)). Qed.
Lemma lem1383621 (x : real) : (term16 x) = term17.
Proof. exact (EQ_MP (@lem1383524 x) (@lem1383523 x)). Qed.
Lemma lem1383622 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1383623 (x : real) : (term29 x) = term30.
Proof. exact (MK_COMB (@lem1383622) (@lem1383621 x)). Qed.
Lemma lem1383624 : term17 = term17.
Proof. exact (eq_refl term17). Qed.
Lemma lem1383625 (x : real) : ((term16 x) = term17) = (term17 = term17).
Proof. exact (MK_COMB (@lem1383623 x) (@lem1383624)). Qed.
Lemma lem1383627 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1383628 (x : real) : (x = x) = True.
Proof. exact (@lem1383627 real x). Qed.
Lemma lem1383629 : (term17 = term17) = True.
Proof. exact (@lem1383628 term17). Qed.
Lemma lem1383630 (x : real) : ((term16 x) = term17) = True.
Proof. exact (TRANS (@lem1383625 x) (@lem1383629)). Qed.
Lemma lem1383631 : term31 = term32.
Proof. exact (fun_ext (fun x : real => @lem1383630 x)). Qed.
Lemma lem1383632 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1383633 : term33 = term34.
Proof. exact (MK_COMB (@lem1383632) (@lem1383631)). Qed.
Lemma lem1383635 {A : Type'} (t : Prop) : (term35 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1383636 (t : Prop) : (term36 t) = t.
Proof. exact (@lem1383635 real t). Qed.
Lemma lem1383637 : term34 = True.
Proof. exact (@lem1383636 True). Qed.
Lemma lem1383638 : term33 = True.
Proof. exact (TRANS (@lem1383633) (@lem1383637)). Qed.
Lemma lem1383639 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1383640 : term37 = (and True).
Proof. exact (MK_COMB (@lem1383639) (@lem1383638)). Qed.
Lemma lem1383658 (y : real) (x : real) (z : real) : (term23 x y z) = (term24 y x z).
Proof. exact (EQ_MP (@lem1383533 y x z) (@lem1383532 y x z)). Qed.
Lemma lem1383659 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1383660 (y : real) (x : real) (z : real) : (term38 x y z) = (term39 y x z).
Proof. exact (MK_COMB (@lem1383659) (@lem1383658 y x z)). Qed.
Lemma lem1383661 (y : real) (x : real) (z : real) : (term24 y x z) = (term24 y x z).
Proof. exact (eq_refl (term24 y x z)). Qed.
Lemma lem1383662 (y : real) (x : real) (z : real) : ((term23 x y z) = (term24 y x z)) = ((term24 y x z) = (term24 y x z)).
Proof. exact (MK_COMB (@lem1383660 y x z) (@lem1383661 y x z)). Qed.
Lemma lem1383664 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1383665 (x : real) : (x = x) = True.
Proof. exact (@lem1383664 real x). Qed.
Lemma lem1383666 (y : real) (x : real) (z : real) : ((term24 y x z) = (term24 y x z)) = True.
Proof. exact (@lem1383665 (term24 y x z)). Qed.
Lemma lem1383667 (y : real) (x : real) (z : real) : ((term23 x y z) = (term24 y x z)) = True.
Proof. exact (TRANS (@lem1383662 y x z) (@lem1383666 y x z)). Qed.
Lemma lem1383668 (y : real) (x : real) : (term40 y x) = term32.
Proof. exact (fun_ext (fun z : real => @lem1383667 y x z)). Qed.
Lemma lem1383669 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1383670 (y : real) (x : real) : (term21 y x) = term34.
Proof. exact (MK_COMB (@lem1383669) (@lem1383668 y x)). Qed.
Lemma lem1383672 {A : Type'} (t : Prop) : (term35 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1383673 (t : Prop) : (term36 t) = t.
Proof. exact (@lem1383672 real t). Qed.
Lemma lem1383674 : term34 = True.
Proof. exact (@lem1383673 True). Qed.
Lemma lem1383675 (y : real) (x : real) : (term21 y x) = True.
Proof. exact (TRANS (@lem1383670 y x) (@lem1383674)). Qed.
Lemma lem1383676 (x : real) : (term41 x) = term32.
Proof. exact (fun_ext (fun y : real => @lem1383675 y x)). Qed.
Lemma lem1383677 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1383678 (x : real) : (term19 x) = term34.
Proof. exact (MK_COMB (@lem1383677) (@lem1383676 x)). Qed.
Lemma lem1383680 {A : Type'} (t : Prop) : (term35 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1383681 (t : Prop) : (term36 t) = t.
Proof. exact (@lem1383680 real t). Qed.
Lemma lem1383682 : term34 = True.
Proof. exact (@lem1383681 True). Qed.
Lemma lem1383683 (x : real) : (term19 x) = True.
Proof. exact (TRANS (@lem1383678 x) (@lem1383682)). Qed.
Lemma lem1383684 : term42 = term32.
Proof. exact (fun_ext (fun x : real => @lem1383683 x)). Qed.
Lemma lem1383685 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1383686 : term43 = term34.
Proof. exact (MK_COMB (@lem1383685) (@lem1383684)). Qed.
Lemma lem1383688 {A : Type'} (t : Prop) : (term35 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1383689 (t : Prop) : (term36 t) = t.
Proof. exact (@lem1383688 real t). Qed.
Lemma lem1383690 : term34 = True.
Proof. exact (@lem1383689 True). Qed.
Lemma lem1383691 : term43 = True.
Proof. exact (TRANS (@lem1383686) (@lem1383690)). Qed.
Lemma lem1383692 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1383693 : term44 = (and True).
Proof. exact (MK_COMB (@lem1383692) (@lem1383691)). Qed.
Lemma lem1383703 (x : real) : (term45 x) = term46.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem1383704 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1383705 (x : real) : (term47 x) = term48.
Proof. exact (MK_COMB (@lem1383704) (@lem1383703 x)). Qed.
Lemma lem1383706 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1383707 (x : real) : ((term45 x) = term46) = (term46 = term46).
Proof. exact (MK_COMB (@lem1383705 x) (@lem1383706)). Qed.
Lemma lem1383709 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1383710 (x : real) : (x = x) = True.
Proof. exact (@lem1383709 real x). Qed.
Lemma lem1383711 : (term46 = term46) = True.
Proof. exact (@lem1383710 term46). Qed.
Lemma lem1383712 (x : real) : ((term45 x) = term46) = True.
Proof. exact (TRANS (@lem1383707 x) (@lem1383711)). Qed.
Lemma lem1383713 : term49 = term32.
Proof. exact (fun_ext (fun x : real => @lem1383712 x)). Qed.
Lemma lem1383714 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1383715 : term50 = term34.
Proof. exact (MK_COMB (@lem1383714) (@lem1383713)). Qed.
Lemma lem1383717 {A : Type'} (t : Prop) : (term35 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1383718 (t : Prop) : (term36 t) = t.
Proof. exact (@lem1383717 real t). Qed.
Lemma lem1383719 : term34 = True.
Proof. exact (@lem1383718 True). Qed.
Lemma lem1383720 : term50 = True.
Proof. exact (TRANS (@lem1383715) (@lem1383719)). Qed.
Lemma lem1383721 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1383722 : term51 = (and True).
Proof. exact (MK_COMB (@lem1383721) (@lem1383720)). Qed.
Lemma lem1383734 (x : real) (n : nat) : (term27 x n) = (term28 x n).
Proof. exact (EQ_MP (@lem1383537 x n) (@lem1383536 x n)). Qed.
Lemma lem1383735 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1383736 (x : real) (n : nat) : (term52 x n) = (term53 x n).
Proof. exact (MK_COMB (@lem1383735) (@lem1383734 x n)). Qed.
Lemma lem1383737 (x : real) (n : nat) : (term28 x n) = (term28 x n).
Proof. exact (eq_refl (term28 x n)). Qed.
Lemma lem1383738 (x : real) (n : nat) : ((term27 x n) = (term28 x n)) = ((term28 x n) = (term28 x n)).
Proof. exact (MK_COMB (@lem1383736 x n) (@lem1383737 x n)). Qed.
Lemma lem1383740 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1383741 (x : real) : (x = x) = True.
Proof. exact (@lem1383740 real x). Qed.
Lemma lem1383742 (x : real) (n : nat) : ((term28 x n) = (term28 x n)) = True.
Proof. exact (@lem1383741 (term28 x n)). Qed.
Lemma lem1383743 (x : real) (n : nat) : ((term27 x n) = (term28 x n)) = True.
Proof. exact (TRANS (@lem1383738 x n) (@lem1383742 x n)). Qed.
Lemma lem1383744 (x : real) : (term54 x) = term55.
Proof. exact (fun_ext (fun n : nat => @lem1383743 x n)). Qed.
Lemma lem1383745 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1383746 (x : real) : (term25 x) = term56.
Proof. exact (MK_COMB (@lem1383745) (@lem1383744 x)). Qed.
Lemma lem1383748 {A : Type'} (t : Prop) : (term35 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1383749 (t : Prop) : (term57 t) = t.
Proof. exact (@lem1383748 nat t). Qed.
Lemma lem1383750 : term56 = True.
Proof. exact (@lem1383749 True). Qed.
Lemma lem1383751 (x : real) : (term25 x) = True.
Proof. exact (TRANS (@lem1383746 x) (@lem1383750)). Qed.
Lemma lem1383752 : term58 = term32.
Proof. exact (fun_ext (fun x : real => @lem1383751 x)). Qed.
Lemma lem1383753 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1383754 : term59 = term34.
Proof. exact (MK_COMB (@lem1383753) (@lem1383752)). Qed.
Lemma lem1383756 {A : Type'} (t : Prop) : (term35 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1383757 (t : Prop) : (term36 t) = t.
Proof. exact (@lem1383756 real t). Qed.
Lemma lem1383758 : term34 = True.
Proof. exact (@lem1383757 True). Qed.
Lemma lem1383759 : term59 = True.
Proof. exact (TRANS (@lem1383754) (@lem1383758)). Qed.
Lemma lem1383760 : term60 = (True /\ True).
Proof. exact (MK_COMB (@lem1383722) (@lem1383759)). Qed.
Lemma lem1383762 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1383763 : (True /\ True) = True.
Proof. exact (@lem1383762 True). Qed.
Lemma lem1383764 : term60 = True.
Proof. exact (TRANS (@lem1383760) (@lem1383763)). Qed.
Lemma lem1383765 : term61 = (True /\ True).
Proof. exact (MK_COMB (@lem1383693) (@lem1383764)). Qed.
Lemma lem1383767 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1383768 : (True /\ True) = True.
Proof. exact (@lem1383767 True). Qed.
Lemma lem1383769 : term61 = True.
Proof. exact (TRANS (@lem1383765) (@lem1383768)). Qed.
Lemma lem1383770 : term62 = (True /\ True).
Proof. exact (MK_COMB (@lem1383640) (@lem1383769)). Qed.
Lemma lem1383772 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1383773 : (True /\ True) = True.
Proof. exact (@lem1383772 True). Qed.
Lemma lem1383774 : term62 = True.
Proof. exact (TRANS (@lem1383770) (@lem1383773)). Qed.
Lemma lem1383775 : term63 = term63.
Proof. exact (eq_refl term63). Qed.
Lemma lem1383776 : term64 = term65.
Proof. exact (MK_COMB (@lem1383775) (@lem1383774)). Qed.
Lemma lem1383778 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1383779 : term65 = term66.
Proof. exact (@lem1383778 term66). Qed.
Lemma lem1383786 : term64 = term66.
Proof. exact (TRANS (@lem1383776) (@lem1383779)). Qed.
Lemma lem1383787 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem1383788 : term68 = term69.
Proof. exact (MK_COMB (@lem1383787) (@lem1383786)). Qed.
Lemma lem1383791 : term70 = term70.
Proof. exact (eq_refl term70). Qed.
Lemma lem1383792 : term71 = term72.
Proof. exact (MK_COMB (@lem1383791) (@lem1383788)). Qed.
Lemma lem1383795 : term73 = term73.
Proof. exact (eq_refl term73). Qed.
Lemma lem1383796 : term74 = term75.
Proof. exact (MK_COMB (@lem1383795) (@lem1383792)). Qed.
Lemma lem1383799 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1383800 : term77 = term78.
Proof. exact (MK_COMB (@lem1383799) (@lem1383796)). Qed.
Lemma lem1383803 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem1383804 : term80 = term81.
Proof. exact (MK_COMB (@lem1383803) (@lem1383800)). Qed.
Lemma lem1383807 : term81 = term80.
Proof. exact (SYM (@lem1383804)). Qed.
Lemma lem1383845 (x : real) : (term7 x) = x.
Proof. exact (EQ_MP (@lem1383512 x) (@lem1383511 x)). Qed.
Lemma lem1383846 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1383847 (x : real) : (term82 x) = (@eq real x).
Proof. exact (MK_COMB (@lem1383846) (@lem1383845 x)). Qed.
Lemma lem1383848 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1383849 (x : real) : ((term7 x) = x) = (x = x).
Proof. exact (MK_COMB (@lem1383847 x) (@lem1383848 x)). Qed.
Lemma lem1383851 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1383852 (x : real) : (x = x) = True.
Proof. exact (@lem1383851 real x). Qed.
Lemma lem1383853 (x : real) : ((term7 x) = x) = True.
Proof. exact (TRANS (@lem1383849 x) (@lem1383852 x)). Qed.
Lemma lem1383854 : term83 = term32.
Proof. exact (fun_ext (fun x : real => @lem1383853 x)). Qed.
Lemma lem1383855 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1383856 : term84 = term34.
Proof. exact (MK_COMB (@lem1383855) (@lem1383854)). Qed.
Lemma lem1383858 {A : Type'} (t : Prop) : (term35 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1383859 (t : Prop) : (term36 t) = t.
Proof. exact (@lem1383858 real t). Qed.
Lemma lem1383860 : term34 = True.
Proof. exact (@lem1383859 True). Qed.
Lemma lem1383861 : term84 = True.
Proof. exact (TRANS (@lem1383856) (@lem1383860)). Qed.
Lemma lem1383862 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1383863 : term73 = (and True).
Proof. exact (MK_COMB (@lem1383862) (@lem1383861)). Qed.
Lemma lem1383881 (x : real) (y : real) (z : real) : (term13 x y z) = (term14 x y z).
Proof. exact (EQ_MP (@lem1383521 x y z) (@lem1383520 x y z)). Qed.
Lemma lem1383882 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1383883 (x : real) (y : real) (z : real) : (term85 x y z) = (term86 x y z).
Proof. exact (MK_COMB (@lem1383882) (@lem1383881 x y z)). Qed.
Lemma lem1383884 (x : real) (y : real) (z : real) : (term14 x y z) = (term14 x y z).
Proof. exact (eq_refl (term14 x y z)). Qed.
Lemma lem1383885 (x : real) (y : real) (z : real) : ((term13 x y z) = (term14 x y z)) = ((term14 x y z) = (term14 x y z)).
Proof. exact (MK_COMB (@lem1383883 x y z) (@lem1383884 x y z)). Qed.
Lemma lem1383887 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1383888 (x : real) : (x = x) = True.
Proof. exact (@lem1383887 real x). Qed.
Lemma lem1383889 (x : real) (y : real) (z : real) : ((term14 x y z) = (term14 x y z)) = True.
Proof. exact (@lem1383888 (term14 x y z)). Qed.
Lemma lem1383890 (x : real) (y : real) (z : real) : ((term13 x y z) = (term14 x y z)) = True.
Proof. exact (TRANS (@lem1383885 x y z) (@lem1383889 x y z)). Qed.
Lemma lem1383891 (x : real) (y : real) : (term87 x y) = term32.
Proof. exact (fun_ext (fun z : real => @lem1383890 x y z)). Qed.
Lemma lem1383892 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1383893 (x : real) (y : real) : (term11 x y) = term34.
Proof. exact (MK_COMB (@lem1383892) (@lem1383891 x y)). Qed.
Lemma lem1383895 {A : Type'} (t : Prop) : (term35 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1383896 (t : Prop) : (term36 t) = t.
Proof. exact (@lem1383895 real t). Qed.
Lemma lem1383897 : term34 = True.
Proof. exact (@lem1383896 True). Qed.
Lemma lem1383898 (x : real) (y : real) : (term11 x y) = True.
Proof. exact (TRANS (@lem1383893 x y) (@lem1383897)). Qed.
Lemma lem1383899 (x : real) : (term88 x) = term32.
Proof. exact (fun_ext (fun y : real => @lem1383898 x y)). Qed.
Lemma lem1383900 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1383901 (x : real) : (term9 x) = term34.
Proof. exact (MK_COMB (@lem1383900) (@lem1383899 x)). Qed.
Lemma lem1383903 {A : Type'} (t : Prop) : (term35 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1383904 (t : Prop) : (term36 t) = t.
Proof. exact (@lem1383903 real t). Qed.
Lemma lem1383905 : term34 = True.
Proof. exact (@lem1383904 True). Qed.
Lemma lem1383906 (x : real) : (term9 x) = True.
Proof. exact (TRANS (@lem1383901 x) (@lem1383905)). Qed.
Lemma lem1383907 : term89 = term32.
Proof. exact (fun_ext (fun x : real => @lem1383906 x)). Qed.
Lemma lem1383908 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1383909 : term90 = term34.
Proof. exact (MK_COMB (@lem1383908) (@lem1383907)). Qed.
Lemma lem1383911 {A : Type'} (t : Prop) : (term35 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1383912 (t : Prop) : (term36 t) = t.
Proof. exact (@lem1383911 real t). Qed.
Lemma lem1383913 : term34 = True.
Proof. exact (@lem1383912 True). Qed.
Lemma lem1383914 : term90 = True.
Proof. exact (TRANS (@lem1383909) (@lem1383913)). Qed.
Lemma lem1383915 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1383916 : term70 = (and True).
Proof. exact (MK_COMB (@lem1383915) (@lem1383914)). Qed.
Lemma lem1383936 (x : real) : (term5 x) = x.
Proof. exact (EQ_MP (@lem1383509 x) (@lem1383508 x)). Qed.
Lemma lem1383937 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1383938 (x : real) : (term91 x) = (@eq real x).
Proof. exact (MK_COMB (@lem1383937) (@lem1383936 x)). Qed.
Lemma lem1383939 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1383940 (x : real) : ((term5 x) = x) = (x = x).
Proof. exact (MK_COMB (@lem1383938 x) (@lem1383939 x)). Qed.
Lemma lem1383942 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1383943 (x : real) : (x = x) = True.
Proof. exact (@lem1383942 real x). Qed.
Lemma lem1383944 (x : real) : ((term5 x) = x) = True.
Proof. exact (TRANS (@lem1383940 x) (@lem1383943 x)). Qed.
Lemma lem1383945 : term92 = term32.
Proof. exact (fun_ext (fun x : real => @lem1383944 x)). Qed.
Lemma lem1383946 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1383947 : term66 = term34.
Proof. exact (MK_COMB (@lem1383946) (@lem1383945)). Qed.
Lemma lem1383949 {A : Type'} (t : Prop) : (term35 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1383950 (t : Prop) : (term36 t) = t.
Proof. exact (@lem1383949 real t). Qed.
Lemma lem1383951 : term34 = True.
Proof. exact (@lem1383950 True). Qed.
Lemma lem1383952 : term66 = True.
Proof. exact (TRANS (@lem1383947) (@lem1383951)). Qed.
Lemma lem1383953 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem1383954 : term69 = term93.
Proof. exact (MK_COMB (@lem1383953) (@lem1383952)). Qed.
Lemma lem1383956 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1383957 : term93 = term94.
Proof. exact (@lem1383956 term94). Qed.
Lemma lem1383968 : term69 = term94.
Proof. exact (TRANS (@lem1383954) (@lem1383957)). Qed.
Lemma lem1383969 : term72 = term95.
Proof. exact (MK_COMB (@lem1383916) (@lem1383968)). Qed.
Lemma lem1383971 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1383972 : term95 = term94.
Proof. exact (@lem1383971 term94). Qed.
Lemma lem1383983 : term72 = term94.
Proof. exact (TRANS (@lem1383969) (@lem1383972)). Qed.
Lemma lem1383984 : term75 = term95.
Proof. exact (MK_COMB (@lem1383863) (@lem1383983)). Qed.
Lemma lem1383986 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1383987 : term95 = term94.
Proof. exact (@lem1383986 term94). Qed.
Lemma lem1383998 : term75 = term94.
Proof. exact (TRANS (@lem1383984) (@lem1383987)). Qed.
Lemma lem1383999 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1384000 : term78 = term96.
Proof. exact (MK_COMB (@lem1383999) (@lem1383998)). Qed.
Lemma lem1384003 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem1384004 : term81 = term97.
Proof. exact (MK_COMB (@lem1384003) (@lem1384000)). Qed.
Lemma lem1384007 : term97 = term81.
Proof. exact (SYM (@lem1384004)). Qed.
Lemma lem1384034 (m : real) (n : real) (p : real) : (term98 m n p) = (term99 m n p).
Proof. exact (proj1 (@lem1383504 n m p)). Qed.
Lemma lem1384035 (x : real) (y : real) (z : real) : (term98 x y z) = (term99 x y z).
Proof. exact (@lem1384034 x y z). Qed.
Lemma lem1384045 (x : real) (y : real) (z : real) : (term100 x y z) = (term100 x y z).
Proof. exact (eq_refl (term100 x y z)). Qed.
Lemma lem1384046 (x : real) (y : real) (z : real) : ((term99 x y z) = (term98 x y z)) = ((term99 x y z) = (term99 x y z)).
Proof. exact (MK_COMB (@lem1384045 x y z) (@lem1384035 x y z)). Qed.
Lemma lem1384048 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1384049 (x : real) : (x = x) = True.
Proof. exact (@lem1384048 real x). Qed.
Lemma lem1384050 (x : real) (y : real) (z : real) : ((term99 x y z) = (term99 x y z)) = True.
Proof. exact (@lem1384049 (term99 x y z)). Qed.
Lemma lem1384051 (x : real) (y : real) (z : real) : ((term99 x y z) = (term98 x y z)) = True.
Proof. exact (TRANS (@lem1384046 x y z) (@lem1384050 x y z)). Qed.
Lemma lem1384052 (x : real) (y : real) : (term101 x y) = term32.
Proof. exact (fun_ext (fun z : real => @lem1384051 x y z)). Qed.
Lemma lem1384053 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1384054 (x : real) (y : real) : (term102 x y) = term34.
Proof. exact (MK_COMB (@lem1384053) (@lem1384052 x y)). Qed.
Lemma lem1384056 {A : Type'} (t : Prop) : (term35 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1384057 (t : Prop) : (term36 t) = t.
Proof. exact (@lem1384056 real t). Qed.
Lemma lem1384058 : term34 = True.
Proof. exact (@lem1384057 True). Qed.
Lemma lem1384059 (x : real) (y : real) : (term102 x y) = True.
Proof. exact (TRANS (@lem1384054 x y) (@lem1384058)). Qed.
Lemma lem1384060 (x : real) : (term103 x) = term32.
Proof. exact (fun_ext (fun y : real => @lem1384059 x y)). Qed.
Lemma lem1384061 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1384062 (x : real) : (term104 x) = term34.
Proof. exact (MK_COMB (@lem1384061) (@lem1384060 x)). Qed.
Lemma lem1384064 {A : Type'} (t : Prop) : (term35 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1384065 (t : Prop) : (term36 t) = t.
Proof. exact (@lem1384064 real t). Qed.
Lemma lem1384066 : term34 = True.
Proof. exact (@lem1384065 True). Qed.
Lemma lem1384067 (x : real) : (term104 x) = True.
Proof. exact (TRANS (@lem1384062 x) (@lem1384066)). Qed.
Lemma lem1384068 : term105 = term32.
Proof. exact (fun_ext (fun x : real => @lem1384067 x)). Qed.
Lemma lem1384069 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1384070 : term106 = term34.
Proof. exact (MK_COMB (@lem1384069) (@lem1384068)). Qed.
Lemma lem1384072 {A : Type'} (t : Prop) : (term35 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1384073 (t : Prop) : (term36 t) = t.
Proof. exact (@lem1384072 real t). Qed.
Lemma lem1384074 : term34 = True.
Proof. exact (@lem1384073 True). Qed.
Lemma lem1384075 : term106 = True.
Proof. exact (TRANS (@lem1384070) (@lem1384074)). Qed.
Lemma lem1384076 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1384077 : term79 = (and True).
Proof. exact (MK_COMB (@lem1384076) (@lem1384075)). Qed.
Lemma lem1384094 (n : real) (m : real) : (real_add m n) = (real_add n m).
Proof. exact (proj1 (@lem1352530 n m (@el real))). Qed.
Lemma lem1384095 (x : real) (y : real) : (real_add y x) = (real_add x y).
Proof. exact (@lem1384094 x y). Qed.
Lemma lem1384099 (x : real) (y : real) : (term107 x y) = (term107 x y).
Proof. exact (eq_refl (term107 x y)). Qed.
Lemma lem1384100 (x : real) (y : real) : ((real_add x y) = (real_add y x)) = ((real_add x y) = (real_add x y)).
Proof. exact (MK_COMB (@lem1384099 x y) (@lem1384095 x y)). Qed.
Lemma lem1384102 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1384103 (x : real) : (x = x) = True.
Proof. exact (@lem1384102 real x). Qed.
Lemma lem1384104 (x : real) (y : real) : ((real_add x y) = (real_add x y)) = True.
Proof. exact (@lem1384103 (real_add x y)). Qed.
Lemma lem1384105 (y : real) (x : real) : ((real_add x y) = (real_add y x)) = True.
Proof. exact (TRANS (@lem1384100 x y) (@lem1384104 x y)). Qed.
Lemma lem1384106 (x : real) : (term108 x) = term32.
Proof. exact (fun_ext (fun y : real => @lem1384105 y x)). Qed.
Lemma lem1384107 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1384108 (x : real) : (term109 x) = term34.
Proof. exact (MK_COMB (@lem1384107) (@lem1384106 x)). Qed.
Lemma lem1384110 {A : Type'} (t : Prop) : (term35 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1384111 (t : Prop) : (term36 t) = t.
Proof. exact (@lem1384110 real t). Qed.
Lemma lem1384112 : term34 = True.
Proof. exact (@lem1384111 True). Qed.
Lemma lem1384113 (x : real) : (term109 x) = True.
Proof. exact (TRANS (@lem1384108 x) (@lem1384112)). Qed.
Lemma lem1384114 : term110 = term32.
Proof. exact (fun_ext (fun x : real => @lem1384113 x)). Qed.
Lemma lem1384115 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1384116 : term111 = term34.
Proof. exact (MK_COMB (@lem1384115) (@lem1384114)). Qed.
Lemma lem1384118 {A : Type'} (t : Prop) : (term35 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1384119 (t : Prop) : (term36 t) = t.
Proof. exact (@lem1384118 real t). Qed.
Lemma lem1384120 : term34 = True.
Proof. exact (@lem1384119 True). Qed.
Lemma lem1384121 : term111 = True.
Proof. exact (TRANS (@lem1384116) (@lem1384120)). Qed.
Lemma lem1384122 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1384123 : term76 = (and True).
Proof. exact (MK_COMB (@lem1384122) (@lem1384121)). Qed.
Lemma lem1384134 : term94 = term94.
Proof. exact (eq_refl term94). Qed.
Lemma lem1384135 : term96 = term95.
Proof. exact (MK_COMB (@lem1384123) (@lem1384134)). Qed.
Lemma lem1384137 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1384138 : term95 = term94.
Proof. exact (@lem1384137 term94). Qed.
Lemma lem1384149 : term96 = term94.
Proof. exact (TRANS (@lem1384135) (@lem1384138)). Qed.
Lemma lem1384150 : term97 = term95.
Proof. exact (MK_COMB (@lem1384077) (@lem1384149)). Qed.
Lemma lem1384152 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1384153 : term95 = term94.
Proof. exact (@lem1384152 term94). Qed.
Lemma lem1384164 : term97 = term94.
Proof. exact (TRANS (@lem1384150) (@lem1384153)). Qed.
Lemma lem1384165 : term94 = term97.
Proof. exact (SYM (@lem1384164)). Qed.
Lemma lem1384179 (y : real) (x : real) : (real_mul x y) = (real_mul y x).
Proof. exact (EQ_MP (@lem1383502 y x) (@lem1383501 x y)). Qed.
Lemma lem1384180 (x : real) (y : real) : (real_mul y x) = (real_mul x y).
Proof. exact (@lem1384179 x y). Qed.
Lemma lem1384183 (x : real) (y : real) : (term112 x y) = (term112 x y).
Proof. exact (eq_refl (term112 x y)). Qed.
Lemma lem1384184 (x : real) (y : real) : ((real_mul x y) = (real_mul y x)) = ((real_mul x y) = (real_mul x y)).
Proof. exact (MK_COMB (@lem1384183 x y) (@lem1384180 x y)). Qed.
Lemma lem1384186 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1384187 (x : real) : (x = x) = True.
Proof. exact (@lem1384186 real x). Qed.
Lemma lem1384188 (x : real) (y : real) : ((real_mul x y) = (real_mul x y)) = True.
Proof. exact (@lem1384187 (real_mul x y)). Qed.
Lemma lem1384189 (y : real) (x : real) : ((real_mul x y) = (real_mul y x)) = True.
Proof. exact (TRANS (@lem1384184 x y) (@lem1384188 x y)). Qed.
Lemma lem1384190 (x : real) : (term113 x) = term32.
Proof. exact (fun_ext (fun y : real => @lem1384189 y x)). Qed.
Lemma lem1384191 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1384192 (x : real) : (term1 x) = term34.
Proof. exact (MK_COMB (@lem1384191) (@lem1384190 x)). Qed.
Lemma lem1384194 {A : Type'} (t : Prop) : (term35 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1384195 (t : Prop) : (term36 t) = t.
Proof. exact (@lem1384194 real t). Qed.
Lemma lem1384196 : term34 = True.
Proof. exact (@lem1384195 True). Qed.
Lemma lem1384197 (x : real) : (term1 x) = True.
Proof. exact (TRANS (@lem1384192 x) (@lem1384196)). Qed.
Lemma lem1384198 : term114 = term32.
Proof. exact (fun_ext (fun x : real => @lem1384197 x)). Qed.
Lemma lem1384199 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1384200 : term94 = term34.
Proof. exact (MK_COMB (@lem1384199) (@lem1384198)). Qed.
Lemma lem1384202 {A : Type'} (t : Prop) : (term35 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1384203 (t : Prop) : (term36 t) = t.
Proof. exact (@lem1384202 real t). Qed.
Lemma lem1384204 : term34 = True.
Proof. exact (@lem1384203 True). Qed.
Lemma lem1384205 : term94 = True.
Proof. exact (TRANS (@lem1384200) (@lem1384204)). Qed.
Lemma lem1384206 : True = term94.
Proof. exact (SYM (@lem1384205)). Qed.
Lemma lem1384207 : term94.
Proof. exact (EQ_MP (@lem1384206) (@lem0)). Qed.
Lemma lem1384208 : term97.
Proof. exact (EQ_MP (@lem1384165) (@lem1384207)). Qed.
Lemma lem1384209 : term81.
Proof. exact (EQ_MP (@lem1384007) (@lem1384208)). Qed.
Lemma lem1384210 : term80.
Proof. exact (EQ_MP (@lem1383807) (@lem1384209)). Qed.
