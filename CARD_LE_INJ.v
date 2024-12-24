Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARD_LE_INJ_term_abbrevs.
Require Import CARD_CLAUSES_spec.
Require Import DISJ_ACI_spec.
Require Import EMPTY_SUBSET_spec.
Require Import FINITE_INDUCT_STRONG_spec.
Require Import IMAGE_CLAUSES_spec.
Require Import IN_IMAGE_spec.
Require Import IN_INSERT_spec.
Require Import LE_SUC_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import NOT_SUC_spec.
Require Import RIGHT_FORALL_IMP_THM_spec.
Require Import SUBSET_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm15249_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1812_spec.
Require Import thm1813_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm20234_spec.
Require Import thm20420_spec.
Require Import thm20421_spec.
Require Import thm20425_spec.
Require Import thm20611_spec.
Require Import thm20612_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
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
Require Import thm21386_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm885_spec.
Require Import thm886_spec.
Require Import thm89498_spec.
Lemma lem4979620 {A B : Type'} (y : B) : term0 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem4979621 {A B : Type'} (y : B) : (term0 A B y) = (term1 A B y).
Proof. exact (eq_refl (term0 A B y)). Qed.
Lemma lem4979622 {A B : Type'} (y : B) : term1 A B y.
Proof. exact (EQ_MP (@lem4979621 A B y) (@lem4979620 A B y)). Qed.
Lemma lem4979623 {A B : Type'} (y : B) (s : A -> Prop) : term2 A B y s.
Proof. exact (@lem4979622 A B y s). Qed.
Lemma lem4979624 {A B : Type'} (y : B) (s : A -> Prop) : (term2 A B y s) = (term3 A B y s).
Proof. exact (eq_refl (term2 A B y s)). Qed.
Lemma lem4979625 {A B : Type'} (y : B) (s : A -> Prop) : term3 A B y s.
Proof. exact (EQ_MP (@lem4979624 A B y s) (@lem4979623 A B y s)). Qed.
Lemma lem4979626 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term4 A B y s f.
Proof. exact (@lem4979625 A B y s f). Qed.
Lemma lem4979627 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term4 A B y s f) = ((term5 A B y f s) = (term6 A B y f s)).
Proof. exact (eq_refl (term4 A B y s f)). Qed.
Lemma lem4979629 {A : Type'} (s : A -> Prop) : term7 A s.
Proof. exact (@lem3194148 A s). Qed.
Lemma lem4979630 {A : Type'} (s : A -> Prop) : (term7 A s) = (term8 A s).
Proof. exact (eq_refl (term7 A s)). Qed.
Lemma lem4979631 {A : Type'} (s : A -> Prop) : term8 A s.
Proof. exact (EQ_MP (@lem4979630 A s) (@lem4979629 A s)). Qed.
Lemma lem4979632 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term9 A s t.
Proof. exact (@lem4979631 A s t). Qed.
Lemma lem4979633 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term9 A s t) = ((@SUBSET A s t) = (term10 A s t)).
Proof. exact (eq_refl (term9 A s t)). Qed.
Lemma lem4979635 {A : Type'} (x : A) : term11 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem4979636 {A : Type'} (x : A) : (term11 A x) = (term12 A x).
Proof. exact (eq_refl (term11 A x)). Qed.
Lemma lem4979637 {A : Type'} (x : A) : term12 A x.
Proof. exact (EQ_MP (@lem4979636 A x) (@lem4979635 A x)). Qed.
Lemma lem4979638 {A : Type'} (x : A) (y : A) : term13 A x y.
Proof. exact (@lem4979637 A x y). Qed.
Lemma lem4979639 {A : Type'} (y : A) (x : A) : (term13 A x y) = (term14 A y x).
Proof. exact (eq_refl (term13 A x y)). Qed.
Lemma lem4979640 {A : Type'} (y : A) (x : A) : term14 A y x.
Proof. exact (EQ_MP (@lem4979639 A y x) (@lem4979638 A x y)). Qed.
Lemma lem4979641 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term15 A y x s.
Proof. exact (@lem4979640 A y x s). Qed.
Lemma lem4979642 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term15 A y x s) = ((term16 A x y s) = (term17 A y x s)).
Proof. exact (eq_refl (term15 A y x s)). Qed.
Lemma lem4979644 (m : nat) : term18 m.
Proof. exact (@lem91360 m). Qed.
Lemma lem4979645 (m : nat) : (term18 m) = (term19 m).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem4979646 (m : nat) : term19 m.
Proof. exact (EQ_MP (@lem4979645 m) (@lem4979644 m)). Qed.
Lemma lem4979647 (m : nat) (n : nat) : term20 m n.
Proof. exact (@lem4979646 m n). Qed.
Lemma lem4979648 (m : nat) (n : nat) : (term20 m n) = ((term21 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term20 m n)). Qed.
Lemma lem4979650 {A : Type'} : term22 A.
Proof. exact (proj2 (@lem3840691 A)). Qed.
Lemma lem4979651 {A : Type'} (x : A) : term23 A x.
Proof. exact (@lem4979650 A x). Qed.
Lemma lem4979652 {A : Type'} (x : A) : (term23 A x) = (term24 A x).
Proof. exact (eq_refl (term23 A x)). Qed.
Lemma lem4979653 {A : Type'} (x : A) : term24 A x.
Proof. exact (EQ_MP (@lem4979652 A x) (@lem4979651 A x)). Qed.
Lemma lem4979654 {A : Type'} (x : A) (s : A -> Prop) : term25 A x s.
Proof. exact (@lem4979653 A x s). Qed.
Lemma lem4979655 {A : Type'} (x : A) (s : A -> Prop) : (term25 A x s) = (term26 A x s).
Proof. exact (eq_refl (term25 A x s)). Qed.
Lemma lem4979656 {A : Type'} (x : A) (s : A -> Prop) : term26 A x s.
Proof. exact (EQ_MP (@lem4979655 A x s) (@lem4979654 A x s)). Qed.
Lemma lem4979657 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4979658 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term27 A x s) = (term28 A x s).
Proof. exact (@lem4979656 A x s (@lem4979657 A s h1)). Qed.
Lemma lem4979665 (n : nat) : term29 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem4979666 (n : nat) : (term29 n) = (term30 n).
Proof. exact (eq_refl (term29 n)). Qed.
Lemma lem4979667 (n : nat) : term30 n.
Proof. exact (EQ_MP (@lem4979666 n) (@lem4979665 n)). Qed.
Lemma lem4979668 (n : nat) : term31 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem4979688 : term32.
Proof. exact (proj1 (@lem89498)). Qed.
Lemma lem4979689 (m : nat) : term33 m.
Proof. exact (@lem4979688 m). Qed.
Lemma lem4979690 (m : nat) : (term33 m) = ((term34 m) = (m = (NUMERAL 0))).
Proof. exact (eq_refl (term33 m)). Qed.
Lemma lem4979702 {A : Type'} (h1 : term35 A) : term35 A.
Proof. exact (h1). Qed.
Lemma lem4979703 {A : Type'} (P : type686 A) (h1 : term35 A) : term36 A P.
Proof. exact (@lem4979702 A h1 P). Qed.
Lemma lem4979704 {A : Type'} (P : type686 A) : (term36 A P) = (term37 A P).
Proof. exact (eq_refl (term36 A P)). Qed.
Lemma lem4979705 {A : Type'} (P : type686 A) (h1 : term35 A) : term37 A P.
Proof. exact (EQ_MP (@lem4979704 A P) (@lem4979703 A P h1)). Qed.
Lemma lem4979706 {A : Type'} (P : type686 A) (h1 : term38 A P) : term38 A P.
Proof. exact (h1). Qed.
Lemma lem4979707 {A : Type'} (P : type686 A) (h1 : term35 A) (h2 : term38 A P) : term39 A P.
Proof. exact (@lem4979705 A P h1 (@lem4979706 A P h2)). Qed.
Lemma lem4979708 {A : Type'} (P : type686 A) (h1 : term38 A P) : term40 A P.
Proof. exact (fun h0 : term35 A => @lem4979707 A P h0 h1). Qed.
Lemma lem4979709 {A : Type'} (h1 : term35 A) : term35 A.
Proof. exact (h1). Qed.
Lemma lem4979710 {A : Type'} (P : type686 A) (h1 : term35 A) (h2 : term38 A P) : term39 A P.
Proof. exact (@lem4979708 A P h2 (@lem4979709 A h1)). Qed.
Lemma lem4979711 {A : Type'} (P : type686 A) (h1 : term35 A) : term37 A P.
Proof. exact (fun h0 : term38 A P => @lem4979710 A P h1 h0). Qed.
Lemma lem4979712 {A : Type'} (h1 : term35 A) : term35 A.
Proof. exact (fun P : type686 A => @lem4979711 A P h1). Qed.
Lemma lem4979713 {A : Type'} : term41 A.
Proof. exact (fun h0 : term35 A => @lem4979712 A h0). Qed.
Lemma lem4979714 {A : Type'} : term35 A.
Proof. exact (@lem4979713 A (@lem3558722 A)). Qed.
Lemma lem4979715 {A : Type'} (P : type686 A) : term36 A P.
Proof. exact (@lem4979714 A P). Qed.
Lemma lem4979716 {A : Type'} (P : type686 A) : (term36 A P) = (term37 A P).
Proof. exact (eq_refl (term36 A P)). Qed.
Lemma lem4979718 {A : Type'} : term22 A.
Proof. exact (proj2 (@lem3840691 A)). Qed.
Lemma lem4979719 {A : Type'} (x : A) : term23 A x.
Proof. exact (@lem4979718 A x). Qed.
Lemma lem4979720 {A : Type'} (x : A) : (term23 A x) = (term24 A x).
Proof. exact (eq_refl (term23 A x)). Qed.
Lemma lem4979721 {A : Type'} (x : A) : term24 A x.
Proof. exact (EQ_MP (@lem4979720 A x) (@lem4979719 A x)). Qed.
Lemma lem4979722 {A : Type'} (x : A) (s : A -> Prop) : term25 A x s.
Proof. exact (@lem4979721 A x s). Qed.
Lemma lem4979723 {A : Type'} (x : A) (s : A -> Prop) : (term25 A x s) = (term26 A x s).
Proof. exact (eq_refl (term25 A x s)). Qed.
Lemma lem4979724 {A : Type'} (x : A) (s : A -> Prop) : term26 A x s.
Proof. exact (EQ_MP (@lem4979723 A x s) (@lem4979722 A x s)). Qed.
Lemma lem4979725 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4979726 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term27 A x s) = (term28 A x s).
Proof. exact (@lem4979724 A x s (@lem4979725 A s h1)). Qed.
Lemma lem4979733 {A : Type'} (x : A) : term42 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem4979734 {A : Type'} (x : A) : (term42 A x) = (term43 A x).
Proof. exact (eq_refl (term42 A x)). Qed.
Lemma lem4979735 {A : Type'} (x : A) : term43 A x.
Proof. exact (EQ_MP (@lem4979734 A x) (@lem4979733 A x)). Qed.
Lemma lem4979736 {A : Type'} (x : A) : term44 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem4979738 {A : Type'} (s : A -> Prop) : term45 A s.
Proof. exact (@lem3219985 A s). Qed.
Lemma lem4979739 {A : Type'} (s : A -> Prop) : (term45 A s) = (@SUBSET A (@EMPTY A) s).
Proof. exact (eq_refl (term45 A s)). Qed.
Lemma lem4979740 {A : Type'} (s : A -> Prop) : @SUBSET A (@EMPTY A) s.
Proof. exact (EQ_MP (@lem4979739 A s) (@lem4979738 A s)). Qed.
Lemma lem4979741 {A : Type'} (s : A -> Prop) : (@SUBSET A (@EMPTY A) s) = ((@SUBSET A (@EMPTY A) s) = True).
Proof. exact (@lem7 (@SUBSET A (@EMPTY A) s)). Qed.
Lemma lem4979745 {A : Type'} (h1 : term35 A) : term35 A.
Proof. exact (h1). Qed.
Lemma lem4979746 {A : Type'} (P : type686 A) (h1 : term35 A) : term36 A P.
Proof. exact (@lem4979745 A h1 P). Qed.
Lemma lem4979747 {A : Type'} (P : type686 A) : (term36 A P) = (term37 A P).
Proof. exact (eq_refl (term36 A P)). Qed.
Lemma lem4979748 {A : Type'} (P : type686 A) (h1 : term35 A) : term37 A P.
Proof. exact (EQ_MP (@lem4979747 A P) (@lem4979746 A P h1)). Qed.
Lemma lem4979749 {A : Type'} (P : type686 A) (h1 : term38 A P) : term38 A P.
Proof. exact (h1). Qed.
Lemma lem4979750 {A : Type'} (P : type686 A) (h1 : term35 A) (h2 : term38 A P) : term39 A P.
Proof. exact (@lem4979748 A P h1 (@lem4979749 A P h2)). Qed.
Lemma lem4979751 {A : Type'} (P : type686 A) (h1 : term38 A P) : term40 A P.
Proof. exact (fun h0 : term35 A => @lem4979750 A P h0 h1). Qed.
Lemma lem4979752 {A : Type'} (h1 : term35 A) : term35 A.
Proof. exact (h1). Qed.
Lemma lem4979753 {A : Type'} (P : type686 A) (h1 : term35 A) (h2 : term38 A P) : term39 A P.
Proof. exact (@lem4979751 A P h2 (@lem4979752 A h1)). Qed.
Lemma lem4979754 {A : Type'} (P : type686 A) (h1 : term35 A) : term37 A P.
Proof. exact (fun h0 : term38 A P => @lem4979753 A P h1 h0). Qed.
Lemma lem4979755 {A : Type'} (h1 : term35 A) : term35 A.
Proof. exact (fun P : type686 A => @lem4979754 A P h1). Qed.
Lemma lem4979756 {A : Type'} : term41 A.
Proof. exact (fun h0 : term35 A => @lem4979755 A h0). Qed.
Lemma lem4979757 {A : Type'} : term35 A.
Proof. exact (@lem4979756 A (@lem3558722 A)). Qed.
Lemma lem4979758 {A : Type'} (P : type686 A) : term36 A P.
Proof. exact (@lem4979757 A P). Qed.
Lemma lem4979759 {A : Type'} (P : type686 A) : (term36 A P) = (term37 A P).
Proof. exact (eq_refl (term36 A P)). Qed.
Lemma lem4979761 {A : Type'} (P : Prop) : term46 A P.
Proof. exact (@lem6534 A P). Qed.
Lemma lem4979762 {A : Type'} (P : Prop) : (term46 A P) = (term47 A P).
Proof. exact (eq_refl (term46 A P)). Qed.
Lemma lem4979763 {A : Type'} (P : Prop) : term47 A P.
Proof. exact (EQ_MP (@lem4979762 A P) (@lem4979761 A P)). Qed.
Lemma lem4979764 {A : Type'} (P : Prop) (Q : A -> Prop) : term48 A P Q.
Proof. exact (@lem4979763 A P Q). Qed.
Lemma lem4979765 {A : Type'} (P : Prop) (Q : A -> Prop) : (term48 A P Q) = ((term49 A P Q) = (term50 A P Q)).
Proof. exact (eq_refl (term48 A P Q)). Qed.
Lemma lem4979776 (p : Prop) (q : Prop) (r : Prop) : (term51 p q r) = (term52 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem4979777 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term53 A B t s) = (term54 A B t s).
Proof. exact (@lem4979776 (@FINITE A s) (term55 A B s t) (term56 A B t s)). Qed.
Lemma lem4979781 (p : Prop) (q : Prop) (r : Prop) : (term51 p q r) = (term52 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem4979782 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term57 A B t s) = (term58 A B t s).
Proof. exact (@lem4979781 (@FINITE B t) (term59 A B s t) (term56 A B t s)). Qed.
Lemma lem4979802 (p : Prop) (q : Prop) (r : Prop) : (term51 p q r) = (term52 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem4979803 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term60 A B s f x y) = (term61 A B s f x y).
Proof. exact (@lem4979802 (@IN A x s) (term62 A B s x f y) (x = y)). Qed.
Lemma lem4979807 (p : Prop) (q : Prop) (r : Prop) : (term51 p q r) = (term52 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem4979808 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term63 A B s f x y) = (term64 A B s f x y).
Proof. exact (@lem4979807 (@IN A y s) ((f x) = (f y)) (x = y)). Qed.
Lemma lem4979819 {A : Type'} (x : A) (s : A -> Prop) : (term65 A x s) = (term65 A x s).
Proof. exact (eq_refl (term65 A x s)). Qed.
Lemma lem4979820 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term61 A B s f x y) = (term66 A B s f x y).
Proof. exact (MK_COMB (@lem4979819 A x s) (@lem4979808 A B s f x y)). Qed.
Lemma lem4979823 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term60 A B s f x y) = (term66 A B s f x y).
Proof. exact (TRANS (@lem4979803 A B s f x y) (@lem4979820 A B s f x y)). Qed.
Lemma lem4979824 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term67 A B s f x) = (term68 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem4979823 A B s f x y)). Qed.
Lemma lem4979825 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4979826 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term69 A B s f x) = (term70 A B s f x).
Proof. exact (MK_COMB (@lem4979825 A) (@lem4979824 A B s f x)). Qed.
Lemma lem4979831 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term71 A B s f) = (term72 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4979826 A B s f x)). Qed.
Lemma lem4979832 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4979833 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term73 A B s f) = (term74 A B s f).
Proof. exact (MK_COMB (@lem4979832 A) (@lem4979831 A B s f)). Qed.
Lemma lem4979838 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term75 A B f s t) = (term75 A B f s t).
Proof. exact (eq_refl (term75 A B f s t)). Qed.
Lemma lem4979839 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term76 A B t s f) = (term77 A B t s f).
Proof. exact (MK_COMB (@lem4979838 A B f s t) (@lem4979833 A B s f)). Qed.
Lemma lem4979842 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term78 A B t s) = (term79 A B t s).
Proof. exact (fun_ext (fun f : A -> B => @lem4979839 A B t s f)). Qed.
Lemma lem4979843 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem4979844 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term56 A B t s) = (term80 A B t s).
Proof. exact (MK_COMB (@lem4979843 A B) (@lem4979842 A B t s)). Qed.
Lemma lem4979849 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term81 A B s t) = (term81 A B s t).
Proof. exact (eq_refl (term81 A B s t)). Qed.
Lemma lem4979850 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term82 A B t s) = (term83 A B t s).
Proof. exact (MK_COMB (@lem4979849 A B s t) (@lem4979844 A B t s)). Qed.
Lemma lem4979853 {B : Type'} (t : B -> Prop) : (term84 B t) = (term84 B t).
Proof. exact (eq_refl (term84 B t)). Qed.
Lemma lem4979854 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term58 A B t s) = (term85 A B t s).
Proof. exact (MK_COMB (@lem4979853 B t) (@lem4979850 A B t s)). Qed.
Lemma lem4979857 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term57 A B t s) = (term85 A B t s).
Proof. exact (TRANS (@lem4979782 A B t s) (@lem4979854 A B t s)). Qed.
Lemma lem4979858 {A : Type'} (s : A -> Prop) : (term84 A s) = (term84 A s).
Proof. exact (eq_refl (term84 A s)). Qed.
Lemma lem4979859 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term54 A B t s) = (term86 A B t s).
Proof. exact (MK_COMB (@lem4979858 A s) (@lem4979857 A B t s)). Qed.
Lemma lem4979862 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term53 A B t s) = (term86 A B t s).
Proof. exact (TRANS (@lem4979777 A B t s) (@lem4979859 A B t s)). Qed.
Lemma lem4979863 {A B : Type'} (s : A -> Prop) : (term87 A B s) = (term88 A B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4979862 A B t s)). Qed.
Lemma lem4979864 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4979865 {A B : Type'} (s : A -> Prop) : (term89 A B s) = (term90 A B s).
Proof. exact (MK_COMB (@lem4979864 B) (@lem4979863 A B s)). Qed.
Lemma lem4979870 {A B : Type'} : (term91 A B) = (term92 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4979865 A B s)). Qed.
Lemma lem4979871 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4979872 {A B : Type'} : (term93 A B) = (term94 A B).
Proof. exact (MK_COMB (@lem4979871 A) (@lem4979870 A B)). Qed.
Lemma lem4979877 {A B : Type'} : (term94 A B) = (term93 A B).
Proof. exact (SYM (@lem4979872 A B)). Qed.
Lemma lem4979883 {A : Type'} (P : Prop) (Q : A -> Prop) : (term49 A P Q) = (term50 A P Q).
Proof. exact (EQ_MP (@lem4979765 A P Q) (@lem4979764 A P Q)). Qed.
Lemma lem4979884 {B : Type'} (P : Prop) (Q : type686 B) : (term95 B P Q) = (term96 B P Q).
Proof. exact (@lem4979883 (B -> Prop) P Q). Qed.
Lemma lem4979885 {A B : Type'} (s : A -> Prop) : (term97 A B s) = (term98 A B s).
Proof. exact (@lem4979884 B (@FINITE A s) (term99 A B s)). Qed.
Lemma lem4979886 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term100 A B s t) = (term85 A B t s).
Proof. exact (eq_refl (term100 A B s t)). Qed.
Lemma lem4979887 {A : Type'} (s : A -> Prop) : (term84 A s) = (term84 A s).
Proof. exact (eq_refl (term84 A s)). Qed.
Lemma lem4979888 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term101 A B s t) = (term86 A B t s).
Proof. exact (MK_COMB (@lem4979887 A s) (@lem4979886 A B t s)). Qed.
Lemma lem4979889 {A B : Type'} (s : A -> Prop) : (term102 A B s) = (term88 A B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4979888 A B t s)). Qed.
Lemma lem4979890 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4979891 {A B : Type'} (s : A -> Prop) : (term97 A B s) = (term90 A B s).
Proof. exact (MK_COMB (@lem4979890 B) (@lem4979889 A B s)). Qed.
Lemma lem4979892 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4979893 {A B : Type'} (s : A -> Prop) : (term103 A B s) = (term104 A B s).
Proof. exact (MK_COMB (@lem4979892) (@lem4979891 A B s)). Qed.
Lemma lem4979894 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term100 A B s t) = (term85 A B t s).
Proof. exact (eq_refl (term100 A B s t)). Qed.
Lemma lem4979895 {A B : Type'} (s : A -> Prop) : (term105 A B s) = (term99 A B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4979894 A B t s)). Qed.
Lemma lem4979896 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4979897 {A B : Type'} (s : A -> Prop) : (term106 A B s) = (term107 A B s).
Proof. exact (MK_COMB (@lem4979896 B) (@lem4979895 A B s)). Qed.
Lemma lem4979898 {A : Type'} (s : A -> Prop) : (term84 A s) = (term84 A s).
Proof. exact (eq_refl (term84 A s)). Qed.
Lemma lem4979899 {A B : Type'} (s : A -> Prop) : (term98 A B s) = (term108 A B s).
Proof. exact (MK_COMB (@lem4979898 A s) (@lem4979897 A B s)). Qed.
Lemma lem4979900 {A B : Type'} (s : A -> Prop) : ((term97 A B s) = (term98 A B s)) = ((term90 A B s) = (term108 A B s)).
Proof. exact (MK_COMB (@lem4979893 A B s) (@lem4979899 A B s)). Qed.
Lemma lem4979901 {A B : Type'} (s : A -> Prop) : (term90 A B s) = (term108 A B s).
Proof. exact (EQ_MP (@lem4979900 A B s) (@lem4979885 A B s)). Qed.
Lemma lem4979943 {A : Type'} (P : Prop) (Q : A -> Prop) : (term49 A P Q) = (term50 A P Q).
Proof. exact (EQ_MP (@lem4979765 A P Q) (@lem4979764 A P Q)). Qed.
Lemma lem4979944 {A : Type'} (P : Prop) (Q : A -> Prop) : (term49 A P Q) = (term50 A P Q).
Proof. exact (@lem4979943 A P Q). Qed.
Lemma lem4979945 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term109 A B s f x) = (term110 A B s f x).
Proof. exact (@lem4979944 A (@IN A x s) (term111 A B s f x)). Qed.
Lemma lem4979946 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term112 A B s f x y) = (term64 A B s f x y).
Proof. exact (eq_refl (term112 A B s f x y)). Qed.
Lemma lem4979947 {A : Type'} (x : A) (s : A -> Prop) : (term65 A x s) = (term65 A x s).
Proof. exact (eq_refl (term65 A x s)). Qed.
Lemma lem4979948 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term113 A B s f x y) = (term66 A B s f x y).
Proof. exact (MK_COMB (@lem4979947 A x s) (@lem4979946 A B s f x y)). Qed.
Lemma lem4979949 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term114 A B s f x) = (term68 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem4979948 A B s f x y)). Qed.
Lemma lem4979950 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4979951 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term109 A B s f x) = (term70 A B s f x).
Proof. exact (MK_COMB (@lem4979950 A) (@lem4979949 A B s f x)). Qed.
Lemma lem4979952 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4979953 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term115 A B s f x) = (term116 A B s f x).
Proof. exact (MK_COMB (@lem4979952) (@lem4979951 A B s f x)). Qed.
Lemma lem4979954 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term112 A B s f x y) = (term64 A B s f x y).
Proof. exact (eq_refl (term112 A B s f x y)). Qed.
Lemma lem4979955 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term117 A B s f x) = (term111 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem4979954 A B s f x y)). Qed.
Lemma lem4979956 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4979957 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term118 A B s f x) = (term119 A B s f x).
Proof. exact (MK_COMB (@lem4979956 A) (@lem4979955 A B s f x)). Qed.
Lemma lem4979958 {A : Type'} (x : A) (s : A -> Prop) : (term65 A x s) = (term65 A x s).
Proof. exact (eq_refl (term65 A x s)). Qed.
Lemma lem4979959 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term110 A B s f x) = (term120 A B s f x).
Proof. exact (MK_COMB (@lem4979958 A x s) (@lem4979957 A B s f x)). Qed.
Lemma lem4979960 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : ((term109 A B s f x) = (term110 A B s f x)) = ((term70 A B s f x) = (term120 A B s f x)).
Proof. exact (MK_COMB (@lem4979953 A B s f x) (@lem4979959 A B s f x)). Qed.
Lemma lem4979961 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term70 A B s f x) = (term120 A B s f x).
Proof. exact (EQ_MP (@lem4979960 A B s f x) (@lem4979945 A B s f x)). Qed.
Lemma lem4979998 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term72 A B s f) = (term121 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4979961 A B s f x)). Qed.
Lemma lem4979999 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4980000 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term74 A B s f) = (term122 A B s f).
Proof. exact (MK_COMB (@lem4979999 A) (@lem4979998 A B s f)). Qed.
Lemma lem4980025 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term75 A B f s t) = (term75 A B f s t).
Proof. exact (eq_refl (term75 A B f s t)). Qed.
Lemma lem4980026 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term77 A B t s f) = (term123 A B t s f).
Proof. exact (MK_COMB (@lem4980025 A B f s t) (@lem4980000 A B s f)). Qed.
Lemma lem4980029 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term79 A B t s) = (term124 A B t s).
Proof. exact (fun_ext (fun f : A -> B => @lem4980026 A B t s f)). Qed.
Lemma lem4980030 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem4980031 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term80 A B t s) = (term125 A B t s).
Proof. exact (MK_COMB (@lem4980030 A B) (@lem4980029 A B t s)). Qed.
Lemma lem4980036 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term81 A B s t) = (term81 A B s t).
Proof. exact (eq_refl (term81 A B s t)). Qed.
Lemma lem4980037 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term83 A B t s) = (term126 A B t s).
Proof. exact (MK_COMB (@lem4980036 A B s t) (@lem4980031 A B t s)). Qed.
Lemma lem4980040 {B : Type'} (t : B -> Prop) : (term84 B t) = (term84 B t).
Proof. exact (eq_refl (term84 B t)). Qed.
Lemma lem4980041 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term85 A B t s) = (term127 A B t s).
Proof. exact (MK_COMB (@lem4980040 B t) (@lem4980037 A B t s)). Qed.
Lemma lem4980044 {A B : Type'} (s : A -> Prop) : (term99 A B s) = (term128 A B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4980041 A B t s)). Qed.
Lemma lem4980045 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4980046 {A B : Type'} (s : A -> Prop) : (term107 A B s) = (term129 A B s).
Proof. exact (MK_COMB (@lem4980045 B) (@lem4980044 A B s)). Qed.
Lemma lem4980071 {A : Type'} (s : A -> Prop) : (term84 A s) = (term84 A s).
Proof. exact (eq_refl (term84 A s)). Qed.
Lemma lem4980072 {A B : Type'} (s : A -> Prop) : (term108 A B s) = (term130 A B s).
Proof. exact (MK_COMB (@lem4980071 A s) (@lem4980046 A B s)). Qed.
Lemma lem4980075 {A B : Type'} (s : A -> Prop) : (term90 A B s) = (term130 A B s).
Proof. exact (TRANS (@lem4979901 A B s) (@lem4980072 A B s)). Qed.
Lemma lem4980076 {A B : Type'} : (term92 A B) = (term131 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4980075 A B s)). Qed.
Lemma lem4980077 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4980078 {A B : Type'} : (term94 A B) = (term132 A B).
Proof. exact (MK_COMB (@lem4980077 A) (@lem4980076 A B)). Qed.
Lemma lem4980103 {A B : Type'} : (term132 A B) = (term94 A B).
Proof. exact (SYM (@lem4980078 A B)). Qed.
Lemma lem4980105 {A : Type'} (P : type686 A) : term37 A P.
Proof. exact (EQ_MP (@lem4979759 A P) (@lem4979758 A P)). Qed.
Lemma lem4980106 {A : Type'} (P : type686 A) : term37 A P.
Proof. exact (@lem4980105 A P). Qed.
Lemma lem4980107 {A B : Type'} : term133 A B.
Proof. exact (@lem4980106 A (term134 A B)). Qed.
Lemma lem4980108 {A B : Type'} : (term135 A B) = (term136 A B).
Proof. exact (eq_refl (term135 A B)). Qed.
Lemma lem4980109 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4980110 {A B : Type'} : (term137 A B) = (term138 A B).
Proof. exact (MK_COMB (@lem4980109) (@lem4980108 A B)). Qed.
Lemma lem4980111 {A B : Type'} (s : A -> Prop) : (term139 A B s) = (term129 A B s).
Proof. exact (eq_refl (term139 A B s)). Qed.
Lemma lem4980112 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4980113 {A B : Type'} (s : A -> Prop) : (term140 A B s) = (term141 A B s).
Proof. exact (MK_COMB (@lem4980112) (@lem4980111 A B s)). Qed.
Lemma lem4980114 {A : Type'} (x : A) (s : A -> Prop) : (term142 A x s) = (term142 A x s).
Proof. exact (eq_refl (term142 A x s)). Qed.
Lemma lem4980115 {A B : Type'} (x : A) (s : A -> Prop) : (term143 A B x s) = (term144 A B x s).
Proof. exact (MK_COMB (@lem4980113 A B s) (@lem4980114 A x s)). Qed.
Lemma lem4980116 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4980117 {A B : Type'} (x : A) (s : A -> Prop) : (term145 A B x s) = (term146 A B x s).
Proof. exact (MK_COMB (@lem4980116) (@lem4980115 A B x s)). Qed.
Lemma lem4980118 {A B : Type'} (x : A) (s : A -> Prop) : (term147 A B x s) = (term148 A B x s).
Proof. exact (eq_refl (term147 A B x s)). Qed.
Lemma lem4980119 {A B : Type'} (x : A) (s : A -> Prop) : (term149 A B x s) = (term150 A B x s).
Proof. exact (MK_COMB (@lem4980117 A B x s) (@lem4980118 A B x s)). Qed.
Lemma lem4980120 {A B : Type'} (x : A) : (term151 A B x) = (term152 A B x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4980119 A B x s)). Qed.
Lemma lem4980121 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4980122 {A B : Type'} (x : A) : (term153 A B x) = (term154 A B x).
Proof. exact (MK_COMB (@lem4980121 A) (@lem4980120 A B x)). Qed.
Lemma lem4980123 {A B : Type'} : (term155 A B) = (term156 A B).
Proof. exact (fun_ext (fun x : A => @lem4980122 A B x)). Qed.
Lemma lem4980124 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4980125 {A B : Type'} : (term157 A B) = (term158 A B).
Proof. exact (MK_COMB (@lem4980124 A) (@lem4980123 A B)). Qed.
Lemma lem4980126 {A B : Type'} : (term159 A B) = (term160 A B).
Proof. exact (MK_COMB (@lem4980110 A B) (@lem4980125 A B)). Qed.
Lemma lem4980127 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4980128 {A B : Type'} : (term161 A B) = (term162 A B).
Proof. exact (MK_COMB (@lem4980127) (@lem4980126 A B)). Qed.
Lemma lem4980129 {A B : Type'} (s : A -> Prop) : (term139 A B s) = (term129 A B s).
Proof. exact (eq_refl (term139 A B s)). Qed.
Lemma lem4980130 {A : Type'} (s : A -> Prop) : (term84 A s) = (term84 A s).
Proof. exact (eq_refl (term84 A s)). Qed.
Lemma lem4980131 {A B : Type'} (s : A -> Prop) : (term163 A B s) = (term130 A B s).
Proof. exact (MK_COMB (@lem4980130 A s) (@lem4980129 A B s)). Qed.
Lemma lem4980132 {A B : Type'} : (term164 A B) = (term131 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4980131 A B s)). Qed.
Lemma lem4980133 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4980134 {A B : Type'} : (term165 A B) = (term132 A B).
Proof. exact (MK_COMB (@lem4980133 A) (@lem4980132 A B)). Qed.
Lemma lem4980135 {A B : Type'} : (term133 A B) = (term166 A B).
Proof. exact (MK_COMB (@lem4980128 A B) (@lem4980134 A B)). Qed.
Lemma lem4980136 {A B : Type'} : term166 A B.
Proof. exact (EQ_MP (@lem4980135 A B) (@lem4980107 A B)). Qed.
Lemma lem4980154 {_87477 _87481 : Type'} (f : _87477 -> _87481) : (@IMAGE _87477 _87481 f (@EMPTY _87477)) = (@EMPTY _87481).
Proof. exact (proj1 (@lem3366870 _87477 _87481 (@el _87477) f (@el (_87477 -> Prop)))). Qed.
Lemma lem4980155 {A B : Type'} (f : A -> B) : (@IMAGE A B f (@EMPTY A)) = (@EMPTY B).
Proof. exact (@lem4980154 A B f). Qed.
Lemma lem4980156 {B : Type'} : (@SUBSET B) = (@SUBSET B).
Proof. exact (eq_refl (@SUBSET B)). Qed.
Lemma lem4980157 {A B : Type'} (f : A -> B) : (term167 A B f) = (@SUBSET B (@EMPTY B)).
Proof. exact (MK_COMB (@lem4980156 B) (@lem4980155 A B f)). Qed.
Lemma lem4980158 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4980159 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term168 A B f t) = (@SUBSET B (@EMPTY B) t).
Proof. exact (MK_COMB (@lem4980157 A B f) (@lem4980158 B t)). Qed.
Lemma lem4980161 {A : Type'} (s : A -> Prop) : (@SUBSET A (@EMPTY A) s) = True.
Proof. exact (EQ_MP (@lem4979741 A s) (@lem4979740 A s)). Qed.
Lemma lem4980162 {B : Type'} (s : B -> Prop) : (@SUBSET B (@EMPTY B) s) = True.
Proof. exact (@lem4980161 B s). Qed.
Lemma lem4980163 {B : Type'} (t : B -> Prop) : (@SUBSET B (@EMPTY B) t) = True.
Proof. exact (@lem4980162 B t). Qed.
Lemma lem4980164 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term168 A B f t) = True.
Proof. exact (TRANS (@lem4980159 A B f t) (@lem4980163 B t)). Qed.
Lemma lem4980165 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4980166 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term169 A B f t) = (and True).
Proof. exact (MK_COMB (@lem4980165) (@lem4980164 A B f t)). Qed.
Lemma lem4980174 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4979736 A x (@lem4979735 A x)). Qed.
Lemma lem4980175 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4980174 A x). Qed.
Lemma lem4980176 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4980177 {A : Type'} (x : A) : (term170 A x) = (imp False).
Proof. exact (MK_COMB (@lem4980176) (@lem4980175 A x)). Qed.
Lemma lem4980185 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4979736 A x (@lem4979735 A x)). Qed.
Lemma lem4980186 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4980185 A x). Qed.
Lemma lem4980187 {A : Type'} (y : A) : (@IN A y (@EMPTY A)) = False.
Proof. exact (@lem4980186 A y). Qed.
Lemma lem4980188 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4980189 {A : Type'} (y : A) : (term170 A y) = (imp False).
Proof. exact (MK_COMB (@lem4980188) (@lem4980187 A y)). Qed.
Lemma lem4980198 {A B : Type'} (f : A -> B) (x : A) (y : A) : (term171 A B f x y) = (term171 A B f x y).
Proof. exact (eq_refl (term171 A B f x y)). Qed.
Lemma lem4980199 {A B : Type'} (f : A -> B) (x : A) (y : A) : (term172 A B f x y) = (term173 A B f x y).
Proof. exact (MK_COMB (@lem4980189 A y) (@lem4980198 A B f x y)). Qed.
Lemma lem4980201 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem4980202 {A B : Type'} (f : A -> B) (x : A) (y : A) : (term173 A B f x y) = True.
Proof. exact (@lem4980201 (term171 A B f x y)). Qed.
Lemma lem4980203 {A B : Type'} (f : A -> B) (x : A) (y : A) : (term172 A B f x y) = True.
Proof. exact (TRANS (@lem4980199 A B f x y) (@lem4980202 A B f x y)). Qed.
Lemma lem4980204 {A B : Type'} (f : A -> B) (x : A) : (term174 A B f x) = (term175 A).
Proof. exact (fun_ext (fun y : A => @lem4980203 A B f x y)). Qed.
Lemma lem4980205 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4980206 {A B : Type'} (f : A -> B) (x : A) : (term176 A B f x) = (term177 A).
Proof. exact (MK_COMB (@lem4980205 A) (@lem4980204 A B f x)). Qed.
Lemma lem4980208 {A : Type'} (t : Prop) : (term178 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4980209 {A : Type'} (t : Prop) : (term178 A t) = t.
Proof. exact (@lem4980208 A t). Qed.
Lemma lem4980210 {A : Type'} : (term177 A) = True.
Proof. exact (@lem4980209 A True). Qed.
Lemma lem4980211 {A B : Type'} (f : A -> B) (x : A) : (term176 A B f x) = True.
Proof. exact (TRANS (@lem4980206 A B f x) (@lem4980210 A)). Qed.
Lemma lem4980212 {A B : Type'} (f : A -> B) (x : A) : (term179 A B f x) = (False -> True).
Proof. exact (MK_COMB (@lem4980177 A x) (@lem4980211 A B f x)). Qed.
Lemma lem4980214 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem4980215 : (False -> True) = True.
Proof. exact (@lem4980214 True). Qed.
Lemma lem4980216 {A B : Type'} (f : A -> B) (x : A) : (term179 A B f x) = True.
Proof. exact (TRANS (@lem4980212 A B f x) (@lem4980215)). Qed.
Lemma lem4980217 {A B : Type'} (f : A -> B) : (term180 A B f) = (term175 A).
Proof. exact (fun_ext (fun x : A => @lem4980216 A B f x)). Qed.
Lemma lem4980218 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4980219 {A B : Type'} (f : A -> B) : (term181 A B f) = (term177 A).
Proof. exact (MK_COMB (@lem4980218 A) (@lem4980217 A B f)). Qed.
Lemma lem4980221 {A : Type'} (t : Prop) : (term178 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4980222 {A : Type'} (t : Prop) : (term178 A t) = t.
Proof. exact (@lem4980221 A t). Qed.
Lemma lem4980223 {A : Type'} : (term177 A) = True.
Proof. exact (@lem4980222 A True). Qed.
Lemma lem4980224 {A B : Type'} (f : A -> B) : (term181 A B f) = True.
Proof. exact (TRANS (@lem4980219 A B f) (@lem4980223 A)). Qed.
Lemma lem4980225 {A B : Type'} (t : B -> Prop) (f : A -> B) : (term182 A B t f) = (True /\ True).
Proof. exact (MK_COMB (@lem4980166 A B f t) (@lem4980224 A B f)). Qed.
Lemma lem4980227 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4980228 : (True /\ True) = True.
Proof. exact (@lem4980227 True). Qed.
Lemma lem4980229 {A B : Type'} (t : B -> Prop) (f : A -> B) : (term182 A B t f) = True.
Proof. exact (TRANS (@lem4980225 A B t f) (@lem4980228)). Qed.
Lemma lem4980230 {A B : Type'} (t : B -> Prop) : (term183 A B t) = (term184 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem4980229 A B t f)). Qed.
Lemma lem4980231 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem4980232 {A B : Type'} (t : B -> Prop) : (term185 A B t) = (term186 A B).
Proof. exact (MK_COMB (@lem4980231 A B) (@lem4980230 A B t)). Qed.
Lemma lem4980234 {A : Type'} (t : Prop) : (term187 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem4980235 {A B : Type'} (t : Prop) : (term188 A B t) = t.
Proof. exact (@lem4980234 (A -> B) t). Qed.
Lemma lem4980236 {A B : Type'} : (term186 A B) = True.
Proof. exact (@lem4980235 A B True). Qed.
Lemma lem4980237 {A B : Type'} (t : B -> Prop) : (term185 A B t) = True.
Proof. exact (TRANS (@lem4980232 A B t) (@lem4980236 A B)). Qed.
Lemma lem4980238 {A B : Type'} (t : B -> Prop) : (term189 A B t) = (term189 A B t).
Proof. exact (eq_refl (term189 A B t)). Qed.
Lemma lem4980239 {A B : Type'} (t : B -> Prop) : (term190 A B t) = (term191 A B t).
Proof. exact (MK_COMB (@lem4980238 A B t) (@lem4980237 A B t)). Qed.
Lemma lem4980241 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4980242 {A B : Type'} (t : B -> Prop) : (term191 A B t) = True.
Proof. exact (@lem4980241 (term192 A B t)). Qed.
Lemma lem4980243 {A B : Type'} (t : B -> Prop) : (term190 A B t) = True.
Proof. exact (TRANS (@lem4980239 A B t) (@lem4980242 A B t)). Qed.
Lemma lem4980244 {B : Type'} (t : B -> Prop) : (term84 B t) = (term84 B t).
Proof. exact (eq_refl (term84 B t)). Qed.
Lemma lem4980245 {A B : Type'} (t : B -> Prop) : (term193 A B t) = (term194 B t).
Proof. exact (MK_COMB (@lem4980244 B t) (@lem4980243 A B t)). Qed.
Lemma lem4980247 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4980248 {B : Type'} (t : B -> Prop) : (term194 B t) = True.
Proof. exact (@lem4980247 (@FINITE B t)). Qed.
Lemma lem4980249 {A B : Type'} (t : B -> Prop) : (term193 A B t) = True.
Proof. exact (TRANS (@lem4980245 A B t) (@lem4980248 B t)). Qed.
Lemma lem4980250 {A B : Type'} : (term195 A B) = (term196 B).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4980249 A B t)). Qed.
Lemma lem4980251 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4980252 {A B : Type'} : (term136 A B) = (term197 B).
Proof. exact (MK_COMB (@lem4980251 B) (@lem4980250 A B)). Qed.
Lemma lem4980254 {A : Type'} (t : Prop) : (term178 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4980255 {B : Type'} (t : Prop) : (term198 B t) = t.
Proof. exact (@lem4980254 (B -> Prop) t). Qed.
Lemma lem4980256 {B : Type'} : (term197 B) = True.
Proof. exact (@lem4980255 B True). Qed.
Lemma lem4980257 {A B : Type'} : (term136 A B) = True.
Proof. exact (TRANS (@lem4980252 A B) (@lem4980256 B)). Qed.
Lemma lem4980258 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4980259 {A B : Type'} : (term138 A B) = (and True).
Proof. exact (MK_COMB (@lem4980258) (@lem4980257 A B)). Qed.
Lemma lem4980323 {_87477 _87481 : Type'} (x : _87477) (f : _87477 -> _87481) (s : _87477 -> Prop) : (term199 _87477 _87481 f x s) = (term200 _87477 _87481 x f s).
Proof. exact (proj2 (@lem3366870 _87477 _87481 x f s)). Qed.
Lemma lem4980324 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term199 A B f x s) = (term200 A B x f s).
Proof. exact (@lem4980323 A B x f s). Qed.
Lemma lem4980325 {B : Type'} : (@SUBSET B) = (@SUBSET B).
Proof. exact (eq_refl (@SUBSET B)). Qed.
Lemma lem4980326 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term201 A B f x s) = (term202 A B x f s).
Proof. exact (MK_COMB (@lem4980325 B) (@lem4980324 A B x f s)). Qed.
Lemma lem4980327 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4980328 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term203 A B f x s t) = (term204 A B x f s t).
Proof. exact (MK_COMB (@lem4980326 A B x f s) (@lem4980327 B t)). Qed.
Lemma lem4980329 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4980330 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term205 A B f x s t) = (term206 A B x f s t).
Proof. exact (MK_COMB (@lem4980329) (@lem4980328 A B x f s t)). Qed.
Lemma lem4980351 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) : (term207 A B x s f) = (term207 A B x s f).
Proof. exact (eq_refl (term207 A B x s f)). Qed.
Lemma lem4980352 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (f : A -> B) : (term208 A B t x s f) = (term209 A B t x s f).
Proof. exact (MK_COMB (@lem4980330 A B x f s t) (@lem4980351 A B x s f)). Qed.
Lemma lem4980355 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) : (term210 A B t x s) = (term211 A B t x s).
Proof. exact (fun_ext (fun f : A -> B => @lem4980352 A B t x s f)). Qed.
Lemma lem4980356 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem4980357 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) : (term212 A B t x s) = (term213 A B t x s).
Proof. exact (MK_COMB (@lem4980356 A B) (@lem4980355 A B t x s)). Qed.
Lemma lem4980362 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) : (term214 A B x s t) = (term214 A B x s t).
Proof. exact (eq_refl (term214 A B x s t)). Qed.
Lemma lem4980363 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) : (term215 A B t x s) = (term216 A B t x s).
Proof. exact (MK_COMB (@lem4980362 A B x s t) (@lem4980357 A B t x s)). Qed.
Lemma lem4980366 {B : Type'} (t : B -> Prop) : (term84 B t) = (term84 B t).
Proof. exact (eq_refl (term84 B t)). Qed.
Lemma lem4980367 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) : (term217 A B t x s) = (term218 A B t x s).
Proof. exact (MK_COMB (@lem4980366 B t) (@lem4980363 A B t x s)). Qed.
Lemma lem4980370 {A B : Type'} (x : A) (s : A -> Prop) : (term219 A B x s) = (term220 A B x s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4980367 A B t x s)). Qed.
Lemma lem4980371 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4980372 {A B : Type'} (x : A) (s : A -> Prop) : (term148 A B x s) = (term221 A B x s).
Proof. exact (MK_COMB (@lem4980371 B) (@lem4980370 A B x s)). Qed.
Lemma lem4980377 {A B : Type'} (x : A) (s : A -> Prop) : (term146 A B x s) = (term146 A B x s).
Proof. exact (eq_refl (term146 A B x s)). Qed.
Lemma lem4980378 {A B : Type'} (x : A) (s : A -> Prop) : (term150 A B x s) = (term222 A B x s).
Proof. exact (MK_COMB (@lem4980377 A B x s) (@lem4980372 A B x s)). Qed.
Lemma lem4980381 {A B : Type'} (x : A) : (term152 A B x) = (term223 A B x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4980378 A B x s)). Qed.
Lemma lem4980382 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4980383 {A B : Type'} (x : A) : (term154 A B x) = (term224 A B x).
Proof. exact (MK_COMB (@lem4980382 A) (@lem4980381 A B x)). Qed.
Lemma lem4980388 {A B : Type'} : (term156 A B) = (term225 A B).
Proof. exact (fun_ext (fun x : A => @lem4980383 A B x)). Qed.
Lemma lem4980389 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4980390 {A B : Type'} : (term158 A B) = (term226 A B).
Proof. exact (MK_COMB (@lem4980389 A) (@lem4980388 A B)). Qed.
Lemma lem4980395 {A B : Type'} : (term160 A B) = (term227 A B).
Proof. exact (MK_COMB (@lem4980259 A B) (@lem4980390 A B)). Qed.
Lemma lem4980397 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4980398 {A B : Type'} : (term227 A B) = (term226 A B).
Proof. exact (@lem4980397 (term226 A B)). Qed.
Lemma lem4980481 {A B : Type'} : (term160 A B) = (term226 A B).
Proof. exact (TRANS (@lem4980395 A B) (@lem4980398 A B)). Qed.
Lemma lem4980482 {A B : Type'} : (term226 A B) = (term160 A B).
Proof. exact (SYM (@lem4980481 A B)). Qed.
Lemma lem4980494 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term228 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4980495 (p : Prop) (q : Prop) (p' : Prop) : term229 p q p'.
Proof. exact (fun q' : Prop => @lem4980494 p q p' q'). Qed.
Lemma lem4980496 (p : Prop) (q : Prop) : term230 p q.
Proof. exact (fun p' : Prop => @lem4980495 p q p'). Qed.
Lemma lem4980497 {A B : Type'} (x : A) (s : A -> Prop) : term231 A B x s.
Proof. exact (@lem4980496 (term144 A B x s) (term221 A B x s)). Qed.
Lemma lem4980498 {A B : Type'} (x : A) (s : A -> Prop) (p' : Prop) : term232 A B x s p'.
Proof. exact (@lem4980497 A B x s p'). Qed.
Lemma lem4980499 {A B : Type'} (x : A) (s : A -> Prop) (p' : Prop) : (term232 A B x s p') = (term233 A B x s p').
Proof. exact (eq_refl (term232 A B x s p')). Qed.
Lemma lem4980500 {A B : Type'} (x : A) (s : A -> Prop) (p' : Prop) : term233 A B x s p'.
Proof. exact (EQ_MP (@lem4980499 A B x s p') (@lem4980498 A B x s p')). Qed.
Lemma lem4980501 {A B : Type'} (x : A) (s : A -> Prop) (p' : Prop) (q' : Prop) : term234 A B x s p' q'.
Proof. exact (@lem4980500 A B x s p' q'). Qed.
Lemma lem4980502 {A B : Type'} (x : A) (s : A -> Prop) (p' : Prop) (q' : Prop) : (term234 A B x s p' q') = (term235 A B x s p' q').
Proof. exact (eq_refl (term234 A B x s p' q')). Qed.
Lemma lem4980503 {A B : Type'} (x : A) (s : A -> Prop) (p' : Prop) (q' : Prop) : term235 A B x s p' q'.
Proof. exact (EQ_MP (@lem4980502 A B x s p' q') (@lem4980501 A B x s p' q')). Qed.
Lemma lem4981425 {A B : Type'} (x : A) (s : A -> Prop) : (term144 A B x s) = (term144 A B x s).
Proof. exact (eq_refl (term144 A B x s)). Qed.
Lemma lem4981426 {A B : Type'} (x : A) (s : A -> Prop) (q' : Prop) : term236 A B x s q'.
Proof. exact (@lem4980503 A B x s (term144 A B x s) q'). Qed.
Lemma lem4981427 {A B : Type'} (x : A) (s : A -> Prop) (q' : Prop) : term237 A B x s q'.
Proof. exact (@lem4981426 A B x s q' (@lem4981425 A B x s)). Qed.
Lemma lem4981428 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term144 A B x s) : term144 A B x s.
Proof. exact (h1). Qed.
Lemma lem4981429 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term144 A B x s) : term142 A x s.
Proof. exact (proj2 (@lem4981428 A B x s h1)). Qed.
Lemma lem4981430 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term144 A B x s) : @FINITE A s.
Proof. exact (proj2 (@lem4981429 A B x s h1)). Qed.
Lemma lem4981431 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem4981433 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term144 A B x s) : term238 A x s.
Proof. exact (proj1 (@lem4981429 A B x s h1)). Qed.
Lemma lem4981434 {A : Type'} (x : A) (s : A -> Prop) : term239 A x s.
Proof. exact (@lem82 (@IN A x s)). Qed.
Lemma lem4981463 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term228 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4981464 (p : Prop) (q : Prop) (p' : Prop) : term229 p q p'.
Proof. exact (fun q' : Prop => @lem4981463 p q p' q'). Qed.
Lemma lem4981465 (p : Prop) (q : Prop) : term230 p q.
Proof. exact (fun p' : Prop => @lem4981464 p q p'). Qed.
Lemma lem4981466 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) : term240 A B t x s.
Proof. exact (@lem4981465 (@FINITE B t) (term216 A B t x s)). Qed.
Lemma lem4981467 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (p' : Prop) : term241 A B t x s p'.
Proof. exact (@lem4981466 A B t x s p'). Qed.
Lemma lem4981468 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (p' : Prop) : (term241 A B t x s p') = (term242 A B t x s p').
Proof. exact (eq_refl (term241 A B t x s p')). Qed.
Lemma lem4981469 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (p' : Prop) : term242 A B t x s p'.
Proof. exact (EQ_MP (@lem4981468 A B t x s p') (@lem4981467 A B t x s p')). Qed.
Lemma lem4981470 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (p' : Prop) (q' : Prop) : term243 A B t x s p' q'.
Proof. exact (@lem4981469 A B t x s p' q'). Qed.
Lemma lem4981471 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (p' : Prop) (q' : Prop) : (term243 A B t x s p' q') = (term244 A B t x s p' q').
Proof. exact (eq_refl (term243 A B t x s p' q')). Qed.
Lemma lem4981472 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (p' : Prop) (q' : Prop) : term244 A B t x s p' q'.
Proof. exact (EQ_MP (@lem4981471 A B t x s p' q') (@lem4981470 A B t x s p' q')). Qed.
Lemma lem4981473 {B : Type'} (t : B -> Prop) : (@FINITE B t) = (@FINITE B t).
Proof. exact (eq_refl (@FINITE B t)). Qed.
Lemma lem4981474 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (q' : Prop) : term245 A B x s t q'.
Proof. exact (@lem4981472 A B t x s (@FINITE B t) q'). Qed.
Lemma lem4981475 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (q' : Prop) : term246 A B x s t q'.
Proof. exact (@lem4981474 A B x s t q' (@lem4981473 B t)). Qed.
Lemma lem4981482 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term228 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4981483 (p : Prop) (q : Prop) (p' : Prop) : term229 p q p'.
Proof. exact (fun q' : Prop => @lem4981482 p q p' q'). Qed.
Lemma lem4981484 (p : Prop) (q : Prop) : term230 p q.
Proof. exact (fun p' : Prop => @lem4981483 p q p'). Qed.
Lemma lem4981485 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) : term247 A B t x s.
Proof. exact (@lem4981484 (term248 A B x s t) (term213 A B t x s)). Qed.
Lemma lem4981486 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (p' : Prop) : term249 A B t x s p'.
Proof. exact (@lem4981485 A B t x s p'). Qed.
Lemma lem4981487 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (p' : Prop) : (term249 A B t x s p') = (term250 A B t x s p').
Proof. exact (eq_refl (term249 A B t x s p')). Qed.
Lemma lem4981488 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (p' : Prop) : term250 A B t x s p'.
Proof. exact (EQ_MP (@lem4981487 A B t x s p') (@lem4981486 A B t x s p')). Qed.
Lemma lem4981489 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (p' : Prop) (q' : Prop) : term251 A B t x s p' q'.
Proof. exact (@lem4981488 A B t x s p' q'). Qed.
Lemma lem4981490 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (p' : Prop) (q' : Prop) : (term251 A B t x s p' q') = (term252 A B t x s p' q').
Proof. exact (eq_refl (term251 A B t x s p' q')). Qed.
Lemma lem4981491 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (p' : Prop) (q' : Prop) : term252 A B t x s p' q'.
Proof. exact (EQ_MP (@lem4981490 A B t x s p' q') (@lem4981489 A B t x s p' q')). Qed.
Lemma lem4981493 {A : Type'} (x : A) (s : A -> Prop) : term26 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem4979726 A x s h0). Qed.
Lemma lem4981494 {A : Type'} (x : A) (s : A -> Prop) : term26 A x s.
Proof. exact (@lem4981493 A x s). Qed.
Lemma lem4981496 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term144 A B x s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem4981431 A s) (@lem4981430 A B x s h1)). Qed.
Lemma lem4981497 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term144 A B x s) : True = (@FINITE A s).
Proof. exact (SYM (@lem4981496 A B x s h1)). Qed.
Lemma lem4981498 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term144 A B x s) : @FINITE A s.
Proof. exact (EQ_MP (@lem4981497 A B x s h1) (@lem0)). Qed.
Lemma lem4981499 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term144 A B x s) : (term27 A x s) = (term28 A x s).
Proof. exact (@lem4981494 A x s (@lem4981498 A B x s h1)). Qed.
Lemma lem4981501 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term253 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem4981502 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term254 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem4981501 _2963 g t e g' t' e'). Qed.
Lemma lem4981503 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term255 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem4981502 _2963 g t e g' t'). Qed.
Lemma lem4981504 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term256 _2963 g t e.
Proof. exact (fun g' : Prop => @lem4981503 _2963 g t e g'). Qed.
Lemma lem4981505 (g : Prop) (t : nat) (e : nat) : term257 g t e.
Proof. exact (@lem4981504 nat g t e). Qed.
Lemma lem4981506 {A : Type'} (x : A) (s : A -> Prop) : term258 A x s.
Proof. exact (@lem4981505 (@IN A x s) (@CARD A s) (term259 A s)). Qed.
Lemma lem4981507 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) : term260 A x s g'.
Proof. exact (@lem4981506 A x s g'). Qed.
Lemma lem4981508 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) : (term260 A x s g') = (term261 A x s g').
Proof. exact (eq_refl (term260 A x s g')). Qed.
Lemma lem4981509 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) : term261 A x s g'.
Proof. exact (EQ_MP (@lem4981508 A x s g') (@lem4981507 A x s g')). Qed.
Lemma lem4981510 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) (t' : nat) : term262 A x s g' t'.
Proof. exact (@lem4981509 A x s g' t'). Qed.
Lemma lem4981511 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) (t' : nat) : (term262 A x s g' t') = (term263 A x s g' t').
Proof. exact (eq_refl (term262 A x s g' t')). Qed.
Lemma lem4981512 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) (t' : nat) : term263 A x s g' t'.
Proof. exact (EQ_MP (@lem4981511 A x s g' t') (@lem4981510 A x s g' t')). Qed.
Lemma lem4981513 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) (t' : nat) (e' : nat) : term264 A x s g' t' e'.
Proof. exact (@lem4981512 A x s g' t' e'). Qed.
Lemma lem4981514 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) (t' : nat) (e' : nat) : (term264 A x s g' t' e') = (term265 A x s g' t' e').
Proof. exact (eq_refl (term264 A x s g' t' e')). Qed.
Lemma lem4981515 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) (t' : nat) (e' : nat) : term265 A x s g' t' e'.
Proof. exact (EQ_MP (@lem4981514 A x s g' t' e') (@lem4981513 A x s g' t' e')). Qed.
Lemma lem4981517 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term144 A B x s) : (@IN A x s) = False.
Proof. exact (@lem4981434 A x s (@lem4981433 A B x s h1)). Qed.
Lemma lem4981518 {A : Type'} (x : A) (s : A -> Prop) (t' : nat) (e' : nat) : term266 A x s t' e'.
Proof. exact (@lem4981515 A x s False t' e'). Qed.
Lemma lem4981519 {A B : Type'} (t' : nat) (e' : nat) (x : A) (s : A -> Prop) (h1 : term144 A B x s) : term267 A x s t' e'.
Proof. exact (@lem4981518 A x s t' e' (@lem4981517 A B x s h1)). Qed.
Lemma lem4981523 {A : Type'} (s : A -> Prop) : (@CARD A s) = (@CARD A s).
Proof. exact (eq_refl (@CARD A s)). Qed.
Lemma lem4981524 {A : Type'} (s : A -> Prop) : term268 A s.
Proof. exact (fun h0 : False => @lem4981523 A s). Qed.
Lemma lem4981525 {A B : Type'} (e' : nat) (x : A) (s : A -> Prop) (h1 : term144 A B x s) : term269 A x s e'.
Proof. exact (@lem4981519 A B (@CARD A s) e' x s h1). Qed.
Lemma lem4981526 {A B : Type'} (e' : nat) (x : A) (s : A -> Prop) (h1 : term144 A B x s) : term270 A x s e'.
Proof. exact (@lem4981525 A B e' x s h1 (@lem4981524 A s)). Qed.
Lemma lem4981532 {A : Type'} (s : A -> Prop) : (term259 A s) = (term259 A s).
Proof. exact (eq_refl (term259 A s)). Qed.
Lemma lem4981533 {A : Type'} (s : A -> Prop) : term271 A s.
Proof. exact (fun h0 : ~ False => @lem4981532 A s). Qed.
Lemma lem4981534 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term144 A B x s) : term272 A x s.
Proof. exact (@lem4981526 A B (term259 A s) x s h1). Qed.
Lemma lem4981535 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term144 A B x s) : (term28 A x s) = (term273 A s).
Proof. exact (@lem4981534 A B x s h1 (@lem4981533 A s)). Qed.
Lemma lem4981537 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4981538 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem4981537 nat t1 t2). Qed.
Lemma lem4981539 {A : Type'} (s : A -> Prop) : (term273 A s) = (term259 A s).
Proof. exact (@lem4981538 (@CARD A s) (term259 A s)). Qed.
Lemma lem4981540 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term144 A B x s) : (term28 A x s) = (term259 A s).
Proof. exact (TRANS (@lem4981535 A B x s h1) (@lem4981539 A s)). Qed.
Lemma lem4981541 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term144 A B x s) : (term27 A x s) = (term259 A s).
Proof. exact (TRANS (@lem4981499 A B x s h1) (@lem4981540 A B x s h1)). Qed.
Lemma lem4981542 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem4981543 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term144 A B x s) : (term274 A x s) = (term275 A s).
Proof. exact (MK_COMB (@lem4981542) (@lem4981541 A B x s h1)). Qed.
Lemma lem4981544 {B : Type'} (t : B -> Prop) : (@CARD B t) = (@CARD B t).
Proof. exact (eq_refl (@CARD B t)). Qed.
Lemma lem4981545 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (h1 : term144 A B x s) : (term248 A B x s t) = (term276 A B s t).
Proof. exact (MK_COMB (@lem4981543 A B x s h1) (@lem4981544 B t)). Qed.
Lemma lem4981546 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (q' : Prop) : term277 A B x s t q'.
Proof. exact (@lem4981491 A B t x s (term276 A B s t) q'). Qed.
Lemma lem4981547 {A B : Type'} (t : B -> Prop) (q' : Prop) (x : A) (s : A -> Prop) (h1 : term144 A B x s) : term278 A B x s t q'.
Proof. exact (@lem4981546 A B x s t q' (@lem4981545 A B t x s h1)). Qed.
Lemma lem4981762 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) : (term213 A B t x s) = (term213 A B t x s).
Proof. exact (eq_refl (term213 A B t x s)). Qed.
Lemma lem4981763 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) : term279 A B t x s.
Proof. exact (fun h0 : term276 A B s t => @lem4981762 A B t x s). Qed.
Lemma lem4981764 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (h1 : term144 A B x s) : term280 A B t x s.
Proof. exact (@lem4981547 A B t (term213 A B t x s) x s h1). Qed.
Lemma lem4981765 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (h1 : term144 A B x s) : (term216 A B t x s) = (term281 A B t x s).
Proof. exact (@lem4981764 A B t x s h1 (@lem4981763 A B t x s)). Qed.
Lemma lem4982211 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (h1 : term144 A B x s) : term282 A B t x s.
Proof. exact (fun h0 : @FINITE B t => @lem4981765 A B t x s h1). Qed.
Lemma lem4982212 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) : term283 A B t x s.
Proof. exact (@lem4981475 A B x s t (term281 A B t x s)). Qed.
Lemma lem4982213 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (h1 : term144 A B x s) : (term218 A B t x s) = (term284 A B t x s).
Proof. exact (@lem4982212 A B t x s (@lem4982211 A B t x s h1)). Qed.
Lemma lem4983127 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term144 A B x s) : (term220 A B x s) = (term285 A B x s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4982213 A B t x s h1)). Qed.
Lemma lem4984041 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4984042 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term144 A B x s) : (term221 A B x s) = (term286 A B x s).
Proof. exact (MK_COMB (@lem4984041 B) (@lem4983127 A B x s h1)). Qed.
Lemma lem4984960 {A B : Type'} (x : A) (s : A -> Prop) : term287 A B x s.
Proof. exact (fun h0 : term144 A B x s => @lem4984042 A B x s h0). Qed.
Lemma lem4984961 {A B : Type'} (x : A) (s : A -> Prop) : term288 A B x s.
Proof. exact (@lem4981427 A B x s (term286 A B x s)). Qed.
Lemma lem4984962 {A B : Type'} (x : A) (s : A -> Prop) : (term222 A B x s) = (term289 A B x s).
Proof. exact (@lem4984961 A B x s (@lem4984960 A B x s)). Qed.
Lemma lem4988687 {A B : Type'} (x : A) : (term223 A B x) = (term290 A B x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4984962 A B x s)). Qed.
Lemma lem4992412 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4992413 {A B : Type'} (x : A) : (term224 A B x) = (term291 A B x).
Proof. exact (MK_COMB (@lem4992412 A) (@lem4988687 A B x)). Qed.
Lemma lem4996142 {A B : Type'} : (term225 A B) = (term292 A B).
Proof. exact (fun_ext (fun x : A => @lem4992413 A B x)). Qed.
Lemma lem4999871 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4999872 {A B : Type'} : (term226 A B) = (term293 A B).
Proof. exact (MK_COMB (@lem4999871 A) (@lem4996142 A B)). Qed.
Lemma lem5003605 {A B : Type'} : (term293 A B) = (term226 A B).
Proof. exact (SYM (@lem4999872 A B)). Qed.
Lemma lem5003606 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term144 A B x s) : term144 A B x s.
Proof. exact (h1). Qed.
Lemma lem5003607 {A : Type'} (x : A) (s : A -> Prop) (h1 : term142 A x s) : term142 A x s.
Proof. exact (h1). Qed.
Lemma lem5003608 {A B : Type'} (s : A -> Prop) (h1 : term129 A B s) : term129 A B s.
Proof. exact (h1). Qed.
Lemma lem5003609 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem5003610 {A : Type'} (x : A) (s : A -> Prop) (h1 : term238 A x s) : term238 A x s.
Proof. exact (h1). Qed.
Lemma lem5003612 {A : Type'} (P : type686 A) : term37 A P.
Proof. exact (EQ_MP (@lem4979716 A P) (@lem4979715 A P)). Qed.
Lemma lem5003613 {B : Type'} (P : type686 B) : term37 B P.
Proof. exact (@lem5003612 B P). Qed.
Lemma lem5003614 {A B : Type'} (x : A) (s : A -> Prop) : term294 A B x s.
Proof. exact (@lem5003613 B (term295 A B x s)). Qed.
Lemma lem5003615 {A B : Type'} (x : A) (s : A -> Prop) : (term296 A B x s) = (term297 A B x s).
Proof. exact (eq_refl (term296 A B x s)). Qed.
Lemma lem5003616 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5003617 {A B : Type'} (x : A) (s : A -> Prop) : (term298 A B x s) = (term299 A B x s).
Proof. exact (MK_COMB (@lem5003616) (@lem5003615 A B x s)). Qed.
Lemma lem5003618 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) : (term300 A B x s t) = (term281 A B t x s).
Proof. exact (eq_refl (term300 A B x s t)). Qed.
Lemma lem5003619 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5003620 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) : (term301 A B x s t) = (term302 A B t x s).
Proof. exact (MK_COMB (@lem5003619) (@lem5003618 A B t x s)). Qed.
Lemma lem5003621 {B : Type'} (x : B) (t : B -> Prop) : (term142 B x t) = (term142 B x t).
Proof. exact (eq_refl (term142 B x t)). Qed.
Lemma lem5003622 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (t : B -> Prop) : (term303 A B x s x' t) = (term304 A B x s x' t).
Proof. exact (MK_COMB (@lem5003620 A B t x s) (@lem5003621 B x' t)). Qed.
Lemma lem5003623 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5003624 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (t : B -> Prop) : (term305 A B x s x' t) = (term306 A B x s x' t).
Proof. exact (MK_COMB (@lem5003623) (@lem5003622 A B x s x' t)). Qed.
Lemma lem5003625 {A B : Type'} (x : B) (t : B -> Prop) (x' : A) (s : A -> Prop) : (term307 A B x' s x t) = (term308 A B x t x' s).
Proof. exact (eq_refl (term307 A B x' s x t)). Qed.
Lemma lem5003626 {A B : Type'} (x : B) (t : B -> Prop) (x' : A) (s : A -> Prop) : (term309 A B x' s x t) = (term310 A B x t x' s).
Proof. exact (MK_COMB (@lem5003624 A B x' s x t) (@lem5003625 A B x t x' s)). Qed.
Lemma lem5003627 {A B : Type'} (x : B) (x' : A) (s : A -> Prop) : (term311 A B x' s x) = (term312 A B x x' s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5003626 A B x t x' s)). Qed.
Lemma lem5003628 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5003629 {A B : Type'} (x : B) (x' : A) (s : A -> Prop) : (term313 A B x' s x) = (term314 A B x x' s).
Proof. exact (MK_COMB (@lem5003628 B) (@lem5003627 A B x x' s)). Qed.
Lemma lem5003630 {A B : Type'} (x : A) (s : A -> Prop) : (term315 A B x s) = (term316 A B x s).
Proof. exact (fun_ext (fun x' : B => @lem5003629 A B x' x s)). Qed.
Lemma lem5003631 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5003632 {A B : Type'} (x : A) (s : A -> Prop) : (term317 A B x s) = (term318 A B x s).
Proof. exact (MK_COMB (@lem5003631 B) (@lem5003630 A B x s)). Qed.
Lemma lem5003633 {A B : Type'} (x : A) (s : A -> Prop) : (term319 A B x s) = (term320 A B x s).
Proof. exact (MK_COMB (@lem5003617 A B x s) (@lem5003632 A B x s)). Qed.
Lemma lem5003634 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5003635 {A B : Type'} (x : A) (s : A -> Prop) : (term321 A B x s) = (term322 A B x s).
Proof. exact (MK_COMB (@lem5003634) (@lem5003633 A B x s)). Qed.
Lemma lem5003636 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) : (term300 A B x s t) = (term281 A B t x s).
Proof. exact (eq_refl (term300 A B x s t)). Qed.
Lemma lem5003637 {B : Type'} (t : B -> Prop) : (term84 B t) = (term84 B t).
Proof. exact (eq_refl (term84 B t)). Qed.
Lemma lem5003638 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) : (term323 A B x s t) = (term284 A B t x s).
Proof. exact (MK_COMB (@lem5003637 B t) (@lem5003636 A B t x s)). Qed.
Lemma lem5003639 {A B : Type'} (x : A) (s : A -> Prop) : (term324 A B x s) = (term285 A B x s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5003638 A B t x s)). Qed.
Lemma lem5003640 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5003641 {A B : Type'} (x : A) (s : A -> Prop) : (term325 A B x s) = (term286 A B x s).
Proof. exact (MK_COMB (@lem5003640 B) (@lem5003639 A B x s)). Qed.
Lemma lem5003642 {A B : Type'} (x : A) (s : A -> Prop) : (term294 A B x s) = (term326 A B x s).
Proof. exact (MK_COMB (@lem5003635 A B x s) (@lem5003641 A B x s)). Qed.
Lemma lem5003643 {A B : Type'} (x : A) (s : A -> Prop) : term326 A B x s.
Proof. exact (EQ_MP (@lem5003642 A B x s) (@lem5003614 A B x s)). Qed.
Lemma lem5003649 {A : Type'} : (@CARD A (@EMPTY A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem3840691 A)). Qed.
Lemma lem5003650 {B : Type'} : (@CARD B (@EMPTY B)) = (NUMERAL 0).
Proof. exact (@lem5003649 B). Qed.
Lemma lem5003651 {A : Type'} (s : A -> Prop) : (term275 A s) = (term275 A s).
Proof. exact (eq_refl (term275 A s)). Qed.
Lemma lem5003652 {A B : Type'} (s : A -> Prop) : (term327 A B s) = (term328 A s).
Proof. exact (MK_COMB (@lem5003651 A s) (@lem5003650 B)). Qed.
Lemma lem5003654 (m : nat) : (term34 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem4979690 m) (@lem4979689 m)). Qed.
Lemma lem5003655 {A : Type'} (s : A -> Prop) : (term328 A s) = ((term259 A s) = (NUMERAL 0)).
Proof. exact (@lem5003654 (term259 A s)). Qed.
Lemma lem5003657 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem4979668 n (@lem4979667 n)). Qed.
Lemma lem5003658 {A : Type'} (s : A -> Prop) : ((term259 A s) = (NUMERAL 0)) = False.
Proof. exact (@lem5003657 (@CARD A s)). Qed.
Lemma lem5003659 {A : Type'} (s : A -> Prop) : (term328 A s) = False.
Proof. exact (TRANS (@lem5003655 A s) (@lem5003658 A s)). Qed.
Lemma lem5003660 {A B : Type'} (s : A -> Prop) : (term327 A B s) = False.
Proof. exact (TRANS (@lem5003652 A B s) (@lem5003659 A s)). Qed.
Lemma lem5003661 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5003662 {A B : Type'} (s : A -> Prop) : (term329 A B s) = (imp False).
Proof. exact (MK_COMB (@lem5003661) (@lem5003660 A B s)). Qed.
Lemma lem5003689 {A B : Type'} (x : A) (s : A -> Prop) : (term330 A B x s) = (term330 A B x s).
Proof. exact (eq_refl (term330 A B x s)). Qed.
Lemma lem5003690 {A B : Type'} (x : A) (s : A -> Prop) : (term297 A B x s) = (term331 A B x s).
Proof. exact (MK_COMB (@lem5003662 A B s) (@lem5003689 A B x s)). Qed.
Lemma lem5003692 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem5003693 {A B : Type'} (x : A) (s : A -> Prop) : (term331 A B x s) = True.
Proof. exact (@lem5003692 (term330 A B x s)). Qed.
Lemma lem5003694 {A B : Type'} (x : A) (s : A -> Prop) : (term297 A B x s) = True.
Proof. exact (TRANS (@lem5003690 A B x s) (@lem5003693 A B x s)). Qed.
Lemma lem5003695 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5003696 {A B : Type'} (x : A) (s : A -> Prop) : (term299 A B x s) = (and True).
Proof. exact (MK_COMB (@lem5003695) (@lem5003694 A B x s)). Qed.
Lemma lem5003767 {A B : Type'} (x : A) (s : A -> Prop) : (term318 A B x s) = (term318 A B x s).
Proof. exact (eq_refl (term318 A B x s)). Qed.
Lemma lem5003768 {A B : Type'} (x : A) (s : A -> Prop) : (term320 A B x s) = (term332 A B x s).
Proof. exact (MK_COMB (@lem5003696 A B x s) (@lem5003767 A B x s)). Qed.
Lemma lem5003770 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5003771 {A B : Type'} (x : A) (s : A -> Prop) : (term332 A B x s) = (term318 A B x s).
Proof. exact (@lem5003770 (term318 A B x s)). Qed.
Lemma lem5003842 {A B : Type'} (x : A) (s : A -> Prop) : (term320 A B x s) = (term318 A B x s).
Proof. exact (TRANS (@lem5003768 A B x s) (@lem5003771 A B x s)). Qed.
Lemma lem5003843 {A B : Type'} (x : A) (s : A -> Prop) : (term318 A B x s) = (term320 A B x s).
Proof. exact (SYM (@lem5003842 A B x s)). Qed.
Lemma lem5003847 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term228 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5003848 (p : Prop) (q : Prop) (p' : Prop) : term229 p q p'.
Proof. exact (fun q' : Prop => @lem5003847 p q p' q'). Qed.
Lemma lem5003849 (p : Prop) (q : Prop) : term230 p q.
Proof. exact (fun p' : Prop => @lem5003848 p q p'). Qed.
Lemma lem5003850 {A B : Type'} (y : B) (t : B -> Prop) (x : A) (s : A -> Prop) : term333 A B y t x s.
Proof. exact (@lem5003849 (term304 A B x s y t) (term308 A B y t x s)). Qed.
Lemma lem5003851 {A B : Type'} (y : B) (t : B -> Prop) (x : A) (s : A -> Prop) (p' : Prop) : term334 A B y t x s p'.
Proof. exact (@lem5003850 A B y t x s p'). Qed.
Lemma lem5003852 {A B : Type'} (y : B) (t : B -> Prop) (x : A) (s : A -> Prop) (p' : Prop) : (term334 A B y t x s p') = (term335 A B y t x s p').
Proof. exact (eq_refl (term334 A B y t x s p')). Qed.
Lemma lem5003853 {A B : Type'} (y : B) (t : B -> Prop) (x : A) (s : A -> Prop) (p' : Prop) : term335 A B y t x s p'.
Proof. exact (EQ_MP (@lem5003852 A B y t x s p') (@lem5003851 A B y t x s p')). Qed.
Lemma lem5003854 {A B : Type'} (y : B) (t : B -> Prop) (x : A) (s : A -> Prop) (p' : Prop) (q' : Prop) : term336 A B y t x s p' q'.
Proof. exact (@lem5003853 A B y t x s p' q'). Qed.
Lemma lem5003855 {A B : Type'} (y : B) (t : B -> Prop) (x : A) (s : A -> Prop) (p' : Prop) (q' : Prop) : (term336 A B y t x s p' q') = (term337 A B y t x s p' q').
Proof. exact (eq_refl (term336 A B y t x s p' q')). Qed.
Lemma lem5003856 {A B : Type'} (y : B) (t : B -> Prop) (x : A) (s : A -> Prop) (p' : Prop) (q' : Prop) : term337 A B y t x s p' q'.
Proof. exact (EQ_MP (@lem5003855 A B y t x s p' q') (@lem5003854 A B y t x s p' q')). Qed.
Lemma lem5004306 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) : (term304 A B x s y t) = (term304 A B x s y t).
Proof. exact (eq_refl (term304 A B x s y t)). Qed.
Lemma lem5004307 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (q' : Prop) : term338 A B x s y t q'.
Proof. exact (@lem5003856 A B y t x s (term304 A B x s y t) q'). Qed.
Lemma lem5004308 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (q' : Prop) : term339 A B x s y t q'.
Proof. exact (@lem5004307 A B x s y t q' (@lem5004306 A B x s y t)). Qed.
Lemma lem5004309 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (h1 : term304 A B x s y t) : term304 A B x s y t.
Proof. exact (h1). Qed.
Lemma lem5004310 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (h1 : term304 A B x s y t) : term142 B y t.
Proof. exact (proj2 (@lem5004309 A B x s y t h1)). Qed.
Lemma lem5004311 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (h1 : term304 A B x s y t) : @FINITE B t.
Proof. exact (proj2 (@lem5004310 A B x s y t h1)). Qed.
Lemma lem5004312 {B : Type'} (t : B -> Prop) : (@FINITE B t) = ((@FINITE B t) = True).
Proof. exact (@lem7 (@FINITE B t)). Qed.
Lemma lem5004314 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (h1 : term304 A B x s y t) : term238 B y t.
Proof. exact (proj1 (@lem5004310 A B x s y t h1)). Qed.
Lemma lem5004315 {B : Type'} (y : B) (t : B -> Prop) : term239 B y t.
Proof. exact (@lem82 (@IN B y t)). Qed.
Lemma lem5004330 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term228 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5004331 (p : Prop) (q : Prop) (p' : Prop) : term229 p q p'.
Proof. exact (fun q' : Prop => @lem5004330 p q p' q'). Qed.
Lemma lem5004332 (p : Prop) (q : Prop) : term230 p q.
Proof. exact (fun p' : Prop => @lem5004331 p q p'). Qed.
Lemma lem5004333 {A B : Type'} (y : B) (t : B -> Prop) (x : A) (s : A -> Prop) : term340 A B y t x s.
Proof. exact (@lem5004332 (term341 A B s y t) (term342 A B y t x s)). Qed.
Lemma lem5004334 {A B : Type'} (y : B) (t : B -> Prop) (x : A) (s : A -> Prop) (p' : Prop) : term343 A B y t x s p'.
Proof. exact (@lem5004333 A B y t x s p'). Qed.
Lemma lem5004335 {A B : Type'} (y : B) (t : B -> Prop) (x : A) (s : A -> Prop) (p' : Prop) : (term343 A B y t x s p') = (term344 A B y t x s p').
Proof. exact (eq_refl (term343 A B y t x s p')). Qed.
Lemma lem5004336 {A B : Type'} (y : B) (t : B -> Prop) (x : A) (s : A -> Prop) (p' : Prop) : term344 A B y t x s p'.
Proof. exact (EQ_MP (@lem5004335 A B y t x s p') (@lem5004334 A B y t x s p')). Qed.
Lemma lem5004337 {A B : Type'} (y : B) (t : B -> Prop) (x : A) (s : A -> Prop) (p' : Prop) (q' : Prop) : term345 A B y t x s p' q'.
Proof. exact (@lem5004336 A B y t x s p' q'). Qed.
Lemma lem5004338 {A B : Type'} (y : B) (t : B -> Prop) (x : A) (s : A -> Prop) (p' : Prop) (q' : Prop) : (term345 A B y t x s p' q') = (term346 A B y t x s p' q').
Proof. exact (eq_refl (term345 A B y t x s p' q')). Qed.
Lemma lem5004339 {A B : Type'} (y : B) (t : B -> Prop) (x : A) (s : A -> Prop) (p' : Prop) (q' : Prop) : term346 A B y t x s p' q'.
Proof. exact (EQ_MP (@lem5004338 A B y t x s p' q') (@lem5004337 A B y t x s p' q')). Qed.
Lemma lem5004341 {A : Type'} (x : A) (s : A -> Prop) : term26 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem4979658 A x s h0). Qed.
Lemma lem5004342 {B : Type'} (x : B) (s : B -> Prop) : term26 B x s.
Proof. exact (@lem5004341 B x s). Qed.
Lemma lem5004343 {B : Type'} (y : B) (t : B -> Prop) : term26 B y t.
Proof. exact (@lem5004342 B y t). Qed.
Lemma lem5004345 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (h1 : term304 A B x s y t) : (@FINITE B t) = True.
Proof. exact (EQ_MP (@lem5004312 B t) (@lem5004311 A B x s y t h1)). Qed.
Lemma lem5004346 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (h1 : term304 A B x s y t) : True = (@FINITE B t).
Proof. exact (SYM (@lem5004345 A B x s y t h1)). Qed.
Lemma lem5004347 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (h1 : term304 A B x s y t) : @FINITE B t.
Proof. exact (EQ_MP (@lem5004346 A B x s y t h1) (@lem0)). Qed.
Lemma lem5004348 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (h1 : term304 A B x s y t) : (term27 B y t) = (term28 B y t).
Proof. exact (@lem5004343 B y t (@lem5004347 A B x s y t h1)). Qed.
Lemma lem5004350 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term253 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem5004351 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term254 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem5004350 _2963 g t e g' t' e'). Qed.
Lemma lem5004352 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term255 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem5004351 _2963 g t e g' t'). Qed.
Lemma lem5004353 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term256 _2963 g t e.
Proof. exact (fun g' : Prop => @lem5004352 _2963 g t e g'). Qed.
Lemma lem5004354 (g : Prop) (t : nat) (e : nat) : term257 g t e.
Proof. exact (@lem5004353 nat g t e). Qed.
Lemma lem5004355 {B : Type'} (y : B) (t : B -> Prop) : term258 B y t.
Proof. exact (@lem5004354 (@IN B y t) (@CARD B t) (term259 B t)). Qed.
Lemma lem5004356 {B : Type'} (y : B) (t : B -> Prop) (g' : Prop) : term260 B y t g'.
Proof. exact (@lem5004355 B y t g'). Qed.
Lemma lem5004357 {B : Type'} (y : B) (t : B -> Prop) (g' : Prop) : (term260 B y t g') = (term261 B y t g').
Proof. exact (eq_refl (term260 B y t g')). Qed.
Lemma lem5004358 {B : Type'} (y : B) (t : B -> Prop) (g' : Prop) : term261 B y t g'.
Proof. exact (EQ_MP (@lem5004357 B y t g') (@lem5004356 B y t g')). Qed.
Lemma lem5004359 {B : Type'} (y : B) (t : B -> Prop) (g' : Prop) (t' : nat) : term262 B y t g' t'.
Proof. exact (@lem5004358 B y t g' t'). Qed.
Lemma lem5004360 {B : Type'} (y : B) (t : B -> Prop) (g' : Prop) (t' : nat) : (term262 B y t g' t') = (term263 B y t g' t').
Proof. exact (eq_refl (term262 B y t g' t')). Qed.
Lemma lem5004361 {B : Type'} (y : B) (t : B -> Prop) (g' : Prop) (t' : nat) : term263 B y t g' t'.
Proof. exact (EQ_MP (@lem5004360 B y t g' t') (@lem5004359 B y t g' t')). Qed.
Lemma lem5004362 {B : Type'} (y : B) (t : B -> Prop) (g' : Prop) (t' : nat) (e' : nat) : term264 B y t g' t' e'.
Proof. exact (@lem5004361 B y t g' t' e'). Qed.
Lemma lem5004363 {B : Type'} (y : B) (t : B -> Prop) (g' : Prop) (t' : nat) (e' : nat) : (term264 B y t g' t' e') = (term265 B y t g' t' e').
Proof. exact (eq_refl (term264 B y t g' t' e')). Qed.
Lemma lem5004364 {B : Type'} (y : B) (t : B -> Prop) (g' : Prop) (t' : nat) (e' : nat) : term265 B y t g' t' e'.
Proof. exact (EQ_MP (@lem5004363 B y t g' t' e') (@lem5004362 B y t g' t' e')). Qed.
Lemma lem5004366 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (h1 : term304 A B x s y t) : (@IN B y t) = False.
Proof. exact (@lem5004315 B y t (@lem5004314 A B x s y t h1)). Qed.
Lemma lem5004367 {B : Type'} (y : B) (t : B -> Prop) (t' : nat) (e' : nat) : term266 B y t t' e'.
Proof. exact (@lem5004364 B y t False t' e'). Qed.
Lemma lem5004368 {A B : Type'} (t' : nat) (e' : nat) (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (h1 : term304 A B x s y t) : term267 B y t t' e'.
Proof. exact (@lem5004367 B y t t' e' (@lem5004366 A B x s y t h1)). Qed.
Lemma lem5004372 {B : Type'} (t : B -> Prop) : (@CARD B t) = (@CARD B t).
Proof. exact (eq_refl (@CARD B t)). Qed.
Lemma lem5004373 {B : Type'} (t : B -> Prop) : term268 B t.
Proof. exact (fun h0 : False => @lem5004372 B t). Qed.
Lemma lem5004374 {A B : Type'} (e' : nat) (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (h1 : term304 A B x s y t) : term269 B y t e'.
Proof. exact (@lem5004368 A B (@CARD B t) e' x s y t h1). Qed.
Lemma lem5004375 {A B : Type'} (e' : nat) (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (h1 : term304 A B x s y t) : term270 B y t e'.
Proof. exact (@lem5004374 A B e' x s y t h1 (@lem5004373 B t)). Qed.
Lemma lem5004381 {B : Type'} (t : B -> Prop) : (term259 B t) = (term259 B t).
Proof. exact (eq_refl (term259 B t)). Qed.
Lemma lem5004382 {B : Type'} (t : B -> Prop) : term271 B t.
Proof. exact (fun h0 : ~ False => @lem5004381 B t). Qed.
Lemma lem5004383 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (h1 : term304 A B x s y t) : term272 B y t.
Proof. exact (@lem5004375 A B (term259 B t) x s y t h1). Qed.
Lemma lem5004384 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (h1 : term304 A B x s y t) : (term28 B y t) = (term273 B t).
Proof. exact (@lem5004383 A B x s y t h1 (@lem5004382 B t)). Qed.
Lemma lem5004386 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem5004387 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem5004386 nat t1 t2). Qed.
Lemma lem5004388 {B : Type'} (t : B -> Prop) : (term273 B t) = (term259 B t).
Proof. exact (@lem5004387 (@CARD B t) (term259 B t)). Qed.
Lemma lem5004389 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (h1 : term304 A B x s y t) : (term28 B y t) = (term259 B t).
Proof. exact (TRANS (@lem5004384 A B x s y t h1) (@lem5004388 B t)). Qed.
Lemma lem5004390 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (h1 : term304 A B x s y t) : (term27 B y t) = (term259 B t).
Proof. exact (TRANS (@lem5004348 A B x s y t h1) (@lem5004389 A B x s y t h1)). Qed.
Lemma lem5004391 {A : Type'} (s : A -> Prop) : (term275 A s) = (term275 A s).
Proof. exact (eq_refl (term275 A s)). Qed.
Lemma lem5004392 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (h1 : term304 A B x s y t) : (term341 A B s y t) = (term347 A B s t).
Proof. exact (MK_COMB (@lem5004391 A s) (@lem5004390 A B x s y t h1)). Qed.
Lemma lem5004393 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (t : B -> Prop) (q' : Prop) : term348 A B y x s t q'.
Proof. exact (@lem5004339 A B y t x s (term347 A B s t) q'). Qed.
Lemma lem5004394 {A B : Type'} (q' : Prop) (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (h1 : term304 A B x s y t) : term349 A B y x s t q'.
Proof. exact (@lem5004393 A B y x s t q' (@lem5004392 A B x s y t h1)). Qed.
Lemma lem5004609 {A B : Type'} (y : B) (t : B -> Prop) (x : A) (s : A -> Prop) : (term342 A B y t x s) = (term342 A B y t x s).
Proof. exact (eq_refl (term342 A B y t x s)). Qed.
Lemma lem5004610 {A B : Type'} (y : B) (t : B -> Prop) (x : A) (s : A -> Prop) : term350 A B y t x s.
Proof. exact (fun h0 : term347 A B s t => @lem5004609 A B y t x s). Qed.
Lemma lem5004611 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (h1 : term304 A B x s y t) : term351 A B y t x s.
Proof. exact (@lem5004394 A B (term342 A B y t x s) x s y t h1). Qed.
Lemma lem5004612 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (h1 : term304 A B x s y t) : (term308 A B y t x s) = (term352 A B y t x s).
Proof. exact (@lem5004611 A B x s y t h1 (@lem5004610 A B y t x s)). Qed.
Lemma lem5005058 {A B : Type'} (y : B) (t : B -> Prop) (x : A) (s : A -> Prop) : term353 A B y t x s.
Proof. exact (fun h0 : term304 A B x s y t => @lem5004612 A B x s y t h0). Qed.
Lemma lem5005059 {A B : Type'} (y : B) (t : B -> Prop) (x : A) (s : A -> Prop) : term354 A B y t x s.
Proof. exact (@lem5004308 A B x s y t (term352 A B y t x s)). Qed.
Lemma lem5005060 {A B : Type'} (y : B) (t : B -> Prop) (x : A) (s : A -> Prop) : (term310 A B y t x s) = (term355 A B y t x s).
Proof. exact (@lem5005059 A B y t x s (@lem5005058 A B y t x s)). Qed.
Lemma lem5006887 {A B : Type'} (y : B) (t : B -> Prop) (x : A) (s : A -> Prop) : (term355 A B y t x s) = (term310 A B y t x s).
Proof. exact (SYM (@lem5005060 A B y t x s)). Qed.
Lemma lem5006888 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (h1 : term304 A B x s y t) : term304 A B x s y t.
Proof. exact (h1). Qed.
Lemma lem5006889 {B : Type'} (y : B) (t : B -> Prop) (h1 : term142 B y t) : term142 B y t.
Proof. exact (h1). Qed.
Lemma lem5006891 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (h1). Qed.
Lemma lem5006892 {B : Type'} (y : B) (t : B -> Prop) (h1 : term238 B y t) : term238 B y t.
Proof. exact (h1). Qed.
Lemma lem5006896 (m : nat) (n : nat) : (term21 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem4979648 m n) (@lem4979647 m n)). Qed.
Lemma lem5006897 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term347 A B s t) = (term59 A B s t).
Proof. exact (@lem5006896 (@CARD A s) (@CARD B t)). Qed.
Lemma lem5006898 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5006899 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term356 A B s t) = (term81 A B s t).
Proof. exact (MK_COMB (@lem5006898) (@lem5006897 A B s t)). Qed.
Lemma lem5006926 {A B : Type'} (y : B) (t : B -> Prop) (x : A) (s : A -> Prop) : (term342 A B y t x s) = (term342 A B y t x s).
Proof. exact (eq_refl (term342 A B y t x s)). Qed.
Lemma lem5006927 {A B : Type'} (y : B) (t : B -> Prop) (x : A) (s : A -> Prop) : (term352 A B y t x s) = (term357 A B y t x s).
Proof. exact (MK_COMB (@lem5006899 A B s t) (@lem5006926 A B y t x s)). Qed.
Lemma lem5006930 {A B : Type'} (y : B) (t : B -> Prop) (x : A) (s : A -> Prop) : (term357 A B y t x s) = (term352 A B y t x s).
Proof. exact (SYM (@lem5006927 A B y t x s)). Qed.
Lemma lem5006931 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term59 A B s t) : term59 A B s t.
Proof. exact (h1). Qed.
Lemma lem5006932 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term129 A B s) : term358 A B s t.
Proof. exact (@lem5003608 A B s h1 t). Qed.
Lemma lem5006933 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term358 A B s t) = (term127 A B t s).
Proof. exact (eq_refl (term358 A B s t)). Qed.
Lemma lem5006934 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term129 A B s) : term127 A B t s.
Proof. exact (EQ_MP (@lem5006933 A B t s) (@lem5006932 A B t s h1)). Qed.
Lemma lem5006941 {B : Type'} (t : B -> Prop) : (@FINITE B t) = ((@FINITE B t) = True).
Proof. exact (@lem7 (@FINITE B t)). Qed.
Lemma lem5006943 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term59 A B s t) = ((term59 A B s t) = True).
Proof. exact (@lem7 (term59 A B s t)). Qed.
Lemma lem5006950 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : (@FINITE B t) = True.
Proof. exact (EQ_MP (@lem5006941 B t) (@lem5006891 B t h1)). Qed.
Lemma lem5006951 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5006952 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : (term84 B t) = (imp True).
Proof. exact (MK_COMB (@lem5006951) (@lem5006950 B t h1)). Qed.
Lemma lem5006956 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term59 A B s t) : (term59 A B s t) = True.
Proof. exact (EQ_MP (@lem5006943 A B s t) (@lem5006931 A B s t h1)). Qed.
Lemma lem5006957 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5006958 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term59 A B s t) : (term81 A B s t) = (imp True).
Proof. exact (MK_COMB (@lem5006957) (@lem5006956 A B s t h1)). Qed.
Lemma lem5007011 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term125 A B t s) = (term125 A B t s).
Proof. exact (eq_refl (term125 A B t s)). Qed.
Lemma lem5007012 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term59 A B s t) : (term126 A B t s) = (term359 A B t s).
Proof. exact (MK_COMB (@lem5006958 A B s t h1) (@lem5007011 A B t s)). Qed.
Lemma lem5007014 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem5007015 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term359 A B t s) = (term125 A B t s).
Proof. exact (@lem5007014 (term125 A B t s)). Qed.
Lemma lem5007068 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term59 A B s t) : (term126 A B t s) = (term125 A B t s).
Proof. exact (TRANS (@lem5007012 A B s t h1) (@lem5007015 A B t s)). Qed.
Lemma lem5007069 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE B t) (h2 : term59 A B s t) : (term127 A B t s) = (term359 A B t s).
Proof. exact (MK_COMB (@lem5006952 B t h1) (@lem5007068 A B s t h2)). Qed.
Lemma lem5007071 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem5007072 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term359 A B t s) = (term125 A B t s).
Proof. exact (@lem5007071 (term125 A B t s)). Qed.
Lemma lem5007125 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE B t) (h2 : term59 A B s t) : (term127 A B t s) = (term125 A B t s).
Proof. exact (TRANS (@lem5007069 A B s t h1 h2) (@lem5007072 A B t s)). Qed.
Lemma lem5007126 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5007127 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE B t) (h2 : term59 A B s t) : (term360 A B t s) = (term361 A B t s).
Proof. exact (MK_COMB (@lem5007126) (@lem5007125 A B s t h1 h2)). Qed.
Lemma lem5007154 {A B : Type'} (y : B) (t : B -> Prop) (x : A) (s : A -> Prop) : (term342 A B y t x s) = (term342 A B y t x s).
Proof. exact (eq_refl (term342 A B y t x s)). Qed.
Lemma lem5007155 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE B t) (h2 : term59 A B s t) : (term362 A B y t x s) = (term363 A B y t x s).
Proof. exact (MK_COMB (@lem5007127 A B s t h1 h2) (@lem5007154 A B y t x s)). Qed.
Lemma lem5007158 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE B t) (h2 : term59 A B s t) : (term363 A B y t x s) = (term362 A B y t x s).
Proof. exact (SYM (@lem5007155 A B y x s t h1 h2)). Qed.
Lemma lem5007159 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term125 A B t s) : term125 A B t s.
Proof. exact (h1). Qed.
Lemma lem5007160 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term123 A B t s f) : term123 A B t s f.
Proof. exact (h1). Qed.
Lemma lem5007161 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term122 A B s f) : term122 A B s f.
Proof. exact (h1). Qed.
Lemma lem5007162 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term364 A B f s t) : term364 A B f s t.
Proof. exact (h1). Qed.
Lemma lem5007166 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term10 A s t).
Proof. exact (EQ_MP (@lem4979633 A s t) (@lem4979632 A s t)). Qed.
Lemma lem5007167 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (term10 B s t).
Proof. exact (@lem5007166 B s t). Qed.
Lemma lem5007168 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (y : B) (t : B -> Prop) : (term365 A B x f s y t) = (term366 A B x f s y t).
Proof. exact (@lem5007167 B (term367 A B x y f s) (@INSERT B y t)). Qed.
Lemma lem5007176 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term16 A x y s) = (term17 A y x s).
Proof. exact (EQ_MP (@lem4979642 A y x s) (@lem4979641 A y x s)). Qed.
Lemma lem5007177 {B : Type'} (y : B) (x : B) (s : B -> Prop) : (term16 B x y s) = (term17 B y x s).
Proof. exact (@lem5007176 B y x s). Qed.
Lemma lem5007178 {A B : Type'} (x : B) (x' : A) (y : B) (f : A -> B) (s : A -> Prop) : (term368 A B x x' y f s) = (term369 A B x x' y f s).
Proof. exact (@lem5007177 B (term370 A B y f x') x (term371 A B x' y f s)). Qed.
Lemma lem5007184 {A B : Type'} (f : A -> B) (y : A) : (term372 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem5007185 {A B : Type'} (f : A -> B) (y : A) : (term372 A B f y) = (f y).
Proof. exact (@lem5007184 A B f y). Qed.
Lemma lem5007186 {A B : Type'} (y : B) (f : A -> B) (x : A) : (term373 A B y f x) = (term370 A B y f x).
Proof. exact (@lem5007185 A B (term374 A B x y f) x). Qed.
Lemma lem5007187 {A B : Type'} (x : A) (y : B) (f : A -> B) (z : A) : (term375 A B x y f z) = (term376 A B x y f z).
Proof. exact (eq_refl (term375 A B x y f z)). Qed.
Lemma lem5007188 {A B : Type'} (x : A) (y : B) (f : A -> B) : (term377 A B x y f) = (term374 A B x y f).
Proof. exact (fun_ext (fun z : A => @lem5007187 A B x y f z)). Qed.
Lemma lem5007189 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5007190 {A B : Type'} (y : B) (f : A -> B) (x : A) : (term373 A B y f x) = (term370 A B y f x).
Proof. exact (MK_COMB (@lem5007188 A B x y f) (@lem5007189 A x)). Qed.
Lemma lem5007191 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5007192 {A B : Type'} (y : B) (f : A -> B) (x : A) : (term378 A B y f x) = (term379 A B y f x).
Proof. exact (MK_COMB (@lem5007191 B) (@lem5007190 A B y f x)). Qed.
Lemma lem5007193 {A B : Type'} (y : B) (f : A -> B) (x : A) : (term370 A B y f x) = (term380 A B y f x).
Proof. exact (eq_refl (term370 A B y f x)). Qed.
Lemma lem5007194 {A B : Type'} (y : B) (f : A -> B) (x : A) : ((term373 A B y f x) = (term370 A B y f x)) = ((term370 A B y f x) = (term380 A B y f x)).
Proof. exact (MK_COMB (@lem5007192 A B y f x) (@lem5007193 A B y f x)). Qed.
Lemma lem5007195 {A B : Type'} (y : B) (f : A -> B) (x : A) : (term370 A B y f x) = (term380 A B y f x).
Proof. exact (EQ_MP (@lem5007194 A B y f x) (@lem5007186 A B y f x)). Qed.
Lemma lem5007197 {_2975 _2982 : Type'} (x : _2982) (z : _2975) (y : _2975) : (term381 _2975 _2982 x y z) = y.
Proof. exact (EQ_MP (@lem15249 _2975 _2982 x z y) (@lem0)). Qed.
Lemma lem5007198 {A B : Type'} (x : A) (z : B) (y : B) : (term382 A B x y z) = y.
Proof. exact (@lem5007197 B A x z y). Qed.
Lemma lem5007199 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term380 A B y f x) = y.
Proof. exact (@lem5007198 A B x (f x) y). Qed.
Lemma lem5007200 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term370 A B y f x) = y.
Proof. exact (TRANS (@lem5007195 A B y f x) (@lem5007199 A B f x y)). Qed.
Lemma lem5007201 {B : Type'} (x : B) : (@eq B x) = (@eq B x).
Proof. exact (eq_refl (@eq B x)). Qed.
Lemma lem5007202 {A B : Type'} (f : A -> B) (x : A) (x' : B) (y : B) : (x' = (term370 A B y f x)) = (x' = y).
Proof. exact (MK_COMB (@lem5007201 B x') (@lem5007200 A B f x y)). Qed.
Lemma lem5007205 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5007206 {A B : Type'} (f : A -> B) (x : A) (x' : B) (y : B) : (term383 A B x' y f x) = (term384 B x' y).
Proof. exact (MK_COMB (@lem5007205) (@lem5007202 A B f x x' y)). Qed.
Lemma lem5007208 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term5 A B y f s) = (term6 A B y f s).
Proof. exact (EQ_MP (@lem4979627 A B y f s) (@lem4979626 A B y s f)). Qed.
Lemma lem5007209 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term5 A B y f s) = (term6 A B y f s).
Proof. exact (@lem5007208 A B y f s). Qed.
Lemma lem5007210 {A B : Type'} (x : B) (x' : A) (y : B) (f : A -> B) (s : A -> Prop) : (term385 A B x x' y f s) = (term386 A B x x' y f s).
Proof. exact (@lem5007209 A B x (term374 A B x' y f) s). Qed.
Lemma lem5007220 {A B : Type'} (f : A -> B) (y : A) : (term372 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem5007221 {A B : Type'} (f : A -> B) (y : A) : (term372 A B f y) = (f y).
Proof. exact (@lem5007220 A B f y). Qed.
Lemma lem5007222 {A B : Type'} (x : A) (y : B) (f : A -> B) (x' : A) : (term387 A B x y f x') = (term375 A B x y f x').
Proof. exact (@lem5007221 A B (term374 A B x y f) x'). Qed.
Lemma lem5007223 {A B : Type'} (x : A) (y : B) (f : A -> B) (z : A) : (term375 A B x y f z) = (term376 A B x y f z).
Proof. exact (eq_refl (term375 A B x y f z)). Qed.
Lemma lem5007224 {A B : Type'} (x : A) (y : B) (f : A -> B) : (term377 A B x y f) = (term374 A B x y f).
Proof. exact (fun_ext (fun z : A => @lem5007223 A B x y f z)). Qed.
Lemma lem5007225 {A : Type'} (x' : A) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem5007226 {A B : Type'} (x : A) (y : B) (f : A -> B) (x' : A) : (term387 A B x y f x') = (term375 A B x y f x').
Proof. exact (MK_COMB (@lem5007224 A B x y f) (@lem5007225 A x')). Qed.
Lemma lem5007227 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5007228 {A B : Type'} (x : A) (y : B) (f : A -> B) (x' : A) : (term388 A B x y f x') = (term389 A B x y f x').
Proof. exact (MK_COMB (@lem5007227 B) (@lem5007226 A B x y f x')). Qed.
Lemma lem5007229 {A B : Type'} (x : A) (y : B) (f : A -> B) (x' : A) : (term375 A B x y f x') = (term376 A B x y f x').
Proof. exact (eq_refl (term375 A B x y f x')). Qed.
Lemma lem5007230 {A B : Type'} (x : A) (y : B) (f : A -> B) (x' : A) : ((term387 A B x y f x') = (term375 A B x y f x')) = ((term375 A B x y f x') = (term376 A B x y f x')).
Proof. exact (MK_COMB (@lem5007228 A B x y f x') (@lem5007229 A B x y f x')). Qed.
Lemma lem5007231 {A B : Type'} (x : A) (y : B) (f : A -> B) (x' : A) : (term375 A B x y f x') = (term376 A B x y f x').
Proof. exact (EQ_MP (@lem5007230 A B x y f x') (@lem5007222 A B x y f x')). Qed.
Lemma lem5007236 {B : Type'} (x : B) : (@eq B x) = (@eq B x).
Proof. exact (eq_refl (@eq B x)). Qed.
Lemma lem5007237 {A B : Type'} (x : B) (x' : A) (y : B) (f : A -> B) (x'' : A) : (x = (term375 A B x' y f x'')) = (x = (term376 A B x' y f x'')).
Proof. exact (MK_COMB (@lem5007236 B x) (@lem5007231 A B x' y f x'')). Qed.
Lemma lem5007240 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5007241 {A B : Type'} (x : B) (x' : A) (y : B) (f : A -> B) (x'' : A) : (term390 A B x x' y f x'') = (term391 A B x x' y f x'').
Proof. exact (MK_COMB (@lem5007240) (@lem5007237 A B x x' y f x'')). Qed.
Lemma lem5007242 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (@IN A x' s).
Proof. exact (eq_refl (@IN A x' s)). Qed.
Lemma lem5007243 {A B : Type'} (x : B) (x' : A) (y : B) (f : A -> B) (x'' : A) (s : A -> Prop) : (term392 A B x x' y f x'' s) = (term393 A B x x' y f x'' s).
Proof. exact (MK_COMB (@lem5007241 A B x x' y f x'') (@lem5007242 A x'' s)). Qed.
Lemma lem5007246 {A B : Type'} (x : B) (x' : A) (y : B) (f : A -> B) (s : A -> Prop) : (term394 A B x x' y f s) = (term395 A B x x' y f s).
Proof. exact (fun_ext (fun x'' : A => @lem5007243 A B x x' y f x'' s)). Qed.
Lemma lem5007247 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5007248 {A B : Type'} (x : B) (x' : A) (y : B) (f : A -> B) (s : A -> Prop) : (term386 A B x x' y f s) = (term396 A B x x' y f s).
Proof. exact (MK_COMB (@lem5007247 A) (@lem5007246 A B x x' y f s)). Qed.
Lemma lem5007253 {A B : Type'} (x : B) (x' : A) (y : B) (f : A -> B) (s : A -> Prop) : (term385 A B x x' y f s) = (term396 A B x x' y f s).
Proof. exact (TRANS (@lem5007210 A B x x' y f s) (@lem5007248 A B x x' y f s)). Qed.
Lemma lem5007254 {A B : Type'} (x : B) (x' : A) (y : B) (f : A -> B) (s : A -> Prop) : (term369 A B x x' y f s) = (term397 A B x x' y f s).
Proof. exact (MK_COMB (@lem5007206 A B f x' x y) (@lem5007253 A B x x' y f s)). Qed.
Lemma lem5007257 {A B : Type'} (x : B) (x' : A) (y : B) (f : A -> B) (s : A -> Prop) : (term368 A B x x' y f s) = (term397 A B x x' y f s).
Proof. exact (TRANS (@lem5007178 A B x x' y f s) (@lem5007254 A B x x' y f s)). Qed.
Lemma lem5007258 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5007259 {A B : Type'} (x : B) (x' : A) (y : B) (f : A -> B) (s : A -> Prop) : (term398 A B x x' y f s) = (term399 A B x x' y f s).
Proof. exact (MK_COMB (@lem5007258) (@lem5007257 A B x x' y f s)). Qed.
Lemma lem5007261 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term16 A x y s) = (term17 A y x s).
Proof. exact (EQ_MP (@lem4979642 A y x s) (@lem4979641 A y x s)). Qed.
Lemma lem5007262 {B : Type'} (y : B) (x : B) (s : B -> Prop) : (term16 B x y s) = (term17 B y x s).
Proof. exact (@lem5007261 B y x s). Qed.
Lemma lem5007263 {B : Type'} (y : B) (x : B) (t : B -> Prop) : (term16 B x y t) = (term17 B y x t).
Proof. exact (@lem5007262 B y x t). Qed.
Lemma lem5007268 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (y : B) (x' : B) (t : B -> Prop) : (term400 A B x f s x' y t) = (term401 A B x f s y x' t).
Proof. exact (MK_COMB (@lem5007259 A B x' x y f s) (@lem5007263 B y x' t)). Qed.
Lemma lem5007271 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (y : B) (t : B -> Prop) : (term402 A B x f s y t) = (term403 A B x f s y t).
Proof. exact (fun_ext (fun x' : B => @lem5007268 A B x f s y x' t)). Qed.
Lemma lem5007272 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5007273 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (y : B) (t : B -> Prop) : (term366 A B x f s y t) = (term404 A B x f s y t).
Proof. exact (MK_COMB (@lem5007272 B) (@lem5007271 A B x f s y t)). Qed.
Lemma lem5007278 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (y : B) (t : B -> Prop) : (term365 A B x f s y t) = (term404 A B x f s y t).
Proof. exact (TRANS (@lem5007168 A B x f s y t) (@lem5007273 A B x f s y t)). Qed.
Lemma lem5007279 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5007280 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (y : B) (t : B -> Prop) : (term405 A B x f s y t) = (term406 A B x f s y t).
Proof. exact (MK_COMB (@lem5007279) (@lem5007278 A B x f s y t)). Qed.
Lemma lem5007288 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term16 A x y s) = (term17 A y x s).
Proof. exact (EQ_MP (@lem4979642 A y x s) (@lem4979641 A y x s)). Qed.
Lemma lem5007289 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term16 A x y s) = (term17 A y x s).
Proof. exact (@lem5007288 A y x s). Qed.
Lemma lem5007290 {A : Type'} (x : A) (x' : A) (s : A -> Prop) : (term16 A x' x s) = (term17 A x x' s).
Proof. exact (@lem5007289 A x x' s). Qed.
Lemma lem5007295 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5007296 {A : Type'} (x : A) (x' : A) (s : A -> Prop) : (term407 A x' x s) = (term408 A x x' s).
Proof. exact (MK_COMB (@lem5007295) (@lem5007290 A x x' s)). Qed.
Lemma lem5007304 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term16 A x y s) = (term17 A y x s).
Proof. exact (EQ_MP (@lem4979642 A y x s) (@lem4979641 A y x s)). Qed.
Lemma lem5007305 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term16 A x y s) = (term17 A y x s).
Proof. exact (@lem5007304 A y x s). Qed.
Lemma lem5007306 {A : Type'} (x : A) (y : A) (s : A -> Prop) : (term16 A y x s) = (term17 A x y s).
Proof. exact (@lem5007305 A x y s). Qed.
Lemma lem5007311 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5007312 {A : Type'} (x : A) (y : A) (s : A -> Prop) : (term407 A y x s) = (term408 A x y s).
Proof. exact (MK_COMB (@lem5007311) (@lem5007306 A x y s)). Qed.
Lemma lem5007320 {A B : Type'} (f : A -> B) (y : A) : (term372 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem5007321 {A B : Type'} (f : A -> B) (y : A) : (term372 A B f y) = (f y).
Proof. exact (@lem5007320 A B f y). Qed.
Lemma lem5007322 {A B : Type'} (x : A) (y : B) (f : A -> B) (x' : A) : (term387 A B x y f x') = (term375 A B x y f x').
Proof. exact (@lem5007321 A B (term374 A B x y f) x'). Qed.
Lemma lem5007323 {A B : Type'} (x : A) (y : B) (f : A -> B) (z : A) : (term375 A B x y f z) = (term376 A B x y f z).
Proof. exact (eq_refl (term375 A B x y f z)). Qed.
Lemma lem5007324 {A B : Type'} (x : A) (y : B) (f : A -> B) : (term377 A B x y f) = (term374 A B x y f).
Proof. exact (fun_ext (fun z : A => @lem5007323 A B x y f z)). Qed.
Lemma lem5007325 {A : Type'} (x' : A) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem5007326 {A B : Type'} (x : A) (y : B) (f : A -> B) (x' : A) : (term387 A B x y f x') = (term375 A B x y f x').
Proof. exact (MK_COMB (@lem5007324 A B x y f) (@lem5007325 A x')). Qed.
Lemma lem5007327 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5007328 {A B : Type'} (x : A) (y : B) (f : A -> B) (x' : A) : (term388 A B x y f x') = (term389 A B x y f x').
Proof. exact (MK_COMB (@lem5007327 B) (@lem5007326 A B x y f x')). Qed.
Lemma lem5007329 {A B : Type'} (x : A) (y : B) (f : A -> B) (x' : A) : (term375 A B x y f x') = (term376 A B x y f x').
Proof. exact (eq_refl (term375 A B x y f x')). Qed.
Lemma lem5007330 {A B : Type'} (x : A) (y : B) (f : A -> B) (x' : A) : ((term387 A B x y f x') = (term375 A B x y f x')) = ((term375 A B x y f x') = (term376 A B x y f x')).
Proof. exact (MK_COMB (@lem5007328 A B x y f x') (@lem5007329 A B x y f x')). Qed.
Lemma lem5007331 {A B : Type'} (x : A) (y : B) (f : A -> B) (x' : A) : (term375 A B x y f x') = (term376 A B x y f x').
Proof. exact (EQ_MP (@lem5007330 A B x y f x') (@lem5007322 A B x y f x')). Qed.
Lemma lem5007336 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5007337 {A B : Type'} (x : A) (y : B) (f : A -> B) (x' : A) : (term389 A B x y f x') = (term409 A B x y f x').
Proof. exact (MK_COMB (@lem5007336 B) (@lem5007331 A B x y f x')). Qed.
Lemma lem5007339 {A B : Type'} (f : A -> B) (y : A) : (term372 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem5007340 {A B : Type'} (f : A -> B) (y : A) : (term372 A B f y) = (f y).
Proof. exact (@lem5007339 A B f y). Qed.
Lemma lem5007341 {A B : Type'} (x : A) (y : B) (f : A -> B) (y' : A) : (term387 A B x y f y') = (term375 A B x y f y').
Proof. exact (@lem5007340 A B (term374 A B x y f) y'). Qed.
Lemma lem5007342 {A B : Type'} (x : A) (y : B) (f : A -> B) (z : A) : (term375 A B x y f z) = (term376 A B x y f z).
Proof. exact (eq_refl (term375 A B x y f z)). Qed.
Lemma lem5007343 {A B : Type'} (x : A) (y : B) (f : A -> B) : (term377 A B x y f) = (term374 A B x y f).
Proof. exact (fun_ext (fun z : A => @lem5007342 A B x y f z)). Qed.
Lemma lem5007344 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5007345 {A B : Type'} (x : A) (y : B) (f : A -> B) (y' : A) : (term387 A B x y f y') = (term375 A B x y f y').
Proof. exact (MK_COMB (@lem5007343 A B x y f) (@lem5007344 A y')). Qed.
Lemma lem5007346 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5007347 {A B : Type'} (x : A) (y : B) (f : A -> B) (y' : A) : (term388 A B x y f y') = (term389 A B x y f y').
Proof. exact (MK_COMB (@lem5007346 B) (@lem5007345 A B x y f y')). Qed.
Lemma lem5007348 {A B : Type'} (x : A) (y : B) (f : A -> B) (y' : A) : (term375 A B x y f y') = (term376 A B x y f y').
Proof. exact (eq_refl (term375 A B x y f y')). Qed.
Lemma lem5007349 {A B : Type'} (x : A) (y : B) (f : A -> B) (y' : A) : ((term387 A B x y f y') = (term375 A B x y f y')) = ((term375 A B x y f y') = (term376 A B x y f y')).
Proof. exact (MK_COMB (@lem5007347 A B x y f y') (@lem5007348 A B x y f y')). Qed.
Lemma lem5007350 {A B : Type'} (x : A) (y : B) (f : A -> B) (y' : A) : (term375 A B x y f y') = (term376 A B x y f y').
Proof. exact (EQ_MP (@lem5007349 A B x y f y') (@lem5007341 A B x y f y')). Qed.
Lemma lem5007355 {A B : Type'} (x' : A) (x : A) (y : B) (f : A -> B) (y' : A) : ((term375 A B x y f x') = (term375 A B x y f y')) = ((term376 A B x y f x') = (term376 A B x y f y')).
Proof. exact (MK_COMB (@lem5007337 A B x y f x') (@lem5007350 A B x y f y')). Qed.
Lemma lem5007358 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5007359 {A B : Type'} (x' : A) (x : A) (y : B) (f : A -> B) (y' : A) : (term410 A B x' x y f y') = (term411 A B x' x y f y').
Proof. exact (MK_COMB (@lem5007358) (@lem5007355 A B x' x y f y')). Qed.
Lemma lem5007362 {A : Type'} (x' : A) (y : A) : (x' = y) = (x' = y).
Proof. exact (eq_refl (x' = y)). Qed.
Lemma lem5007363 {A B : Type'} (x : A) (y : B) (f : A -> B) (x' : A) (y' : A) : (term412 A B x y f x' y') = (term413 A B x y f x' y').
Proof. exact (MK_COMB (@lem5007359 A B x' x y f y') (@lem5007362 A x' y')). Qed.
Lemma lem5007368 {A B : Type'} (s : A -> Prop) (x : A) (y : B) (f : A -> B) (x' : A) (y' : A) : (term414 A B s x y f x' y') = (term415 A B s x y f x' y').
Proof. exact (MK_COMB (@lem5007312 A x y' s) (@lem5007363 A B x y f x' y')). Qed.
Lemma lem5007371 {A B : Type'} (s : A -> Prop) (x : A) (y : B) (f : A -> B) (x' : A) : (term416 A B s x y f x') = (term417 A B s x y f x').
Proof. exact (fun_ext (fun y' : A => @lem5007368 A B s x y f x' y')). Qed.
Lemma lem5007372 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5007373 {A B : Type'} (s : A -> Prop) (x : A) (y : B) (f : A -> B) (x' : A) : (term418 A B s x y f x') = (term419 A B s x y f x').
Proof. exact (MK_COMB (@lem5007372 A) (@lem5007371 A B s x y f x')). Qed.
Lemma lem5007378 {A B : Type'} (s : A -> Prop) (x : A) (y : B) (f : A -> B) (x' : A) : (term420 A B s x y f x') = (term421 A B s x y f x').
Proof. exact (MK_COMB (@lem5007296 A x x' s) (@lem5007373 A B s x y f x')). Qed.
Lemma lem5007381 {A B : Type'} (s : A -> Prop) (x : A) (y : B) (f : A -> B) : (term422 A B s x y f) = (term423 A B s x y f).
Proof. exact (fun_ext (fun x' : A => @lem5007378 A B s x y f x')). Qed.
Lemma lem5007382 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5007383 {A B : Type'} (s : A -> Prop) (x : A) (y : B) (f : A -> B) : (term424 A B s x y f) = (term425 A B s x y f).
Proof. exact (MK_COMB (@lem5007382 A) (@lem5007381 A B s x y f)). Qed.
Lemma lem5007388 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) (y : B) (f : A -> B) : (term426 A B t s x y f) = (term427 A B t s x y f).
Proof. exact (MK_COMB (@lem5007280 A B x f s y t) (@lem5007383 A B s x y f)). Qed.
Lemma lem5007391 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) (y : B) (f : A -> B) : (term427 A B t s x y f) = (term426 A B t s x y f).
Proof. exact (SYM (@lem5007388 A B t s x y f)). Qed.
Lemma lem5007393 (p : Prop) : p = (term428 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5007394 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) (y : B) (f : A -> B) : (term427 A B t s x y f) = (term429 A B t s x y f).
Proof. exact (@lem5007393 (term427 A B t s x y f)). Qed.
Lemma lem5007395 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) (y : B) (f : A -> B) : (term429 A B t s x y f) = (term427 A B t s x y f).
Proof. exact (SYM (@lem5007394 A B t s x y f)). Qed.
Lemma lem5007396 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) (y : B) (f : A -> B) (h1 : term430 A B t s x y f) : term430 A B t s x y f.
Proof. exact (h1). Qed.
Lemma lem5007397 {B : Type'} : term431 B.
Proof. exact (@lem3194148 B). Qed.
Lemma lem5007398 {A : Type'} : term431 A.
Proof. exact (@lem3194148 A). Qed.
Lemma lem5007400 {A : Type'} : term432 A.
Proof. exact (@lem3206070 A A). Qed.
Lemma lem5007401 {A B : Type'} : term433 A B.
Proof. exact (@lem3206070 A B). Qed.
Lemma lem5007406 {B : Type'} : term432 B.
Proof. exact (@lem3206070 B B). Qed.
Lemma lem5007409 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) (y : B) (f : A -> B) (h1 : term434 A B t s x y f) : term434 A B t s x y f.
Proof. exact (h1). Qed.
Lemma lem5007410 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) (y : B) (f : A -> B) : term435 A B t s x y f.
Proof. exact (fun h0 : term434 A B t s x y f => @lem5007409 A B t s x y f h0). Qed.
Lemma lem5007411 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) (y : B) (f : A -> B) (h1 : term435 A B t s x y f) : term435 A B t s x y f.
Proof. exact (h1). Qed.
Lemma lem5007412 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) (y : B) (f : A -> B) (h1 : term434 A B t s x y f) : term434 A B t s x y f.
Proof. exact (h1). Qed.
Lemma lem5007413 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) (y : B) (f : A -> B) (h1 : term434 A B t s x y f) (h2 : term435 A B t s x y f) : term434 A B t s x y f.
Proof. exact (@lem5007411 A B t s x y f h2 (@lem5007412 A B t s x y f h1)). Qed.
Lemma lem5007414 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) (y : B) (f : A -> B) (h1 : term434 A B t s x y f) : term436 A B t s x y f.
Proof. exact (fun h0 : term435 A B t s x y f => @lem5007413 A B t s x y f h1 h0). Qed.
Lemma lem5007415 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) (y : B) (f : A -> B) (h1 : term435 A B t s x y f) : term435 A B t s x y f.
Proof. exact (h1). Qed.
Lemma lem5007416 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) (y : B) (f : A -> B) (h1 : term434 A B t s x y f) (h2 : term435 A B t s x y f) : term434 A B t s x y f.
Proof. exact (@lem5007414 A B t s x y f h1 (@lem5007415 A B t s x y f h2)). Qed.
Lemma lem5007417 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) (y : B) (f : A -> B) (h1 : term435 A B t s x y f) : term435 A B t s x y f.
Proof. exact (fun h0 : term434 A B t s x y f => @lem5007416 A B t s x y f h0 h1). Qed.
Lemma lem5007418 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) (y : B) (f : A -> B) : term437 A B t s x y f.
Proof. exact (fun h0 : term435 A B t s x y f => @lem5007417 A B t s x y f h0). Qed.
Lemma lem5007421 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) (y : B) (f : A -> B) : term435 A B t s x y f.
Proof. exact (@lem5007418 A B t s x y f (@lem5007410 A B t s x y f)). Qed.
Lemma lem5007422 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) (y : B) (f : A -> B) : term435 A B t s x y f.
Proof. exact (@lem5007421 A B t s x y f). Qed.
Lemma lem5007762 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5007763 {B : Type'} : (term438 B) = (term439 B).
Proof. exact (@lem5007762 (term431 B)). Qed.
Lemma lem5007778 {A : Type'} : (term440 A) = (term440 A).
Proof. exact (eq_refl (term440 A)). Qed.
Lemma lem5007779 {A B : Type'} : (term441 A B) = (term442 A B).
Proof. exact (MK_COMB (@lem5007778 A) (@lem5007763 B)). Qed.
Lemma lem5007782 {B : Type'} : (term443 B) = (term443 B).
Proof. exact (eq_refl (term443 B)). Qed.
Lemma lem5007783 {A B : Type'} : (term444 A B) = (term445 A B).
Proof. exact (MK_COMB (@lem5007782 B) (@lem5007779 A B)). Qed.
Lemma lem5007786 {A B : Type'} : (term446 A B) = (term446 A B).
Proof. exact (eq_refl (term446 A B)). Qed.
Lemma lem5007787 {A B : Type'} : (term447 A B) = (term448 A B).
Proof. exact (MK_COMB (@lem5007786 A B) (@lem5007783 A B)). Qed.
Lemma lem5007790 {A : Type'} : (term443 A) = (term443 A).
Proof. exact (eq_refl (term443 A)). Qed.
Lemma lem5007791 {A B : Type'} : (term449 A B) = (term450 A B).
Proof. exact (MK_COMB (@lem5007790 A) (@lem5007787 A B)). Qed.
Lemma lem5007794 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) (y : B) (f : A -> B) : (term451 A B t s x y f) = (term451 A B t s x y f).
Proof. exact (eq_refl (term451 A B t s x y f)). Qed.
Lemma lem5007795 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) (y : B) (f : A -> B) : (term452 A B t s x y f) = (term453 A B t s x y f).
Proof. exact (MK_COMB (@lem5007794 A B t s x y f) (@lem5007791 A B)). Qed.
Lemma lem5007798 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term454 A B s f) = (term454 A B s f).
Proof. exact (eq_refl (term454 A B s f)). Qed.
Lemma lem5007799 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) (y : B) (f : A -> B) : (term455 A B t s x y f) = (term456 A B t s x y f).
Proof. exact (MK_COMB (@lem5007798 A B s f) (@lem5007795 A B t s x y f)). Qed.
Lemma lem5007802 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term457 A B f s t) = (term457 A B f s t).
Proof. exact (eq_refl (term457 A B f s t)). Qed.
Lemma lem5007803 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) (y : B) (f : A -> B) : (term458 A B t s x y f) = (term459 A B t s x y f).
Proof. exact (MK_COMB (@lem5007802 A B f s t) (@lem5007799 A B t s x y f)). Qed.
Lemma lem5007806 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term81 A B s t) = (term81 A B s t).
Proof. exact (eq_refl (term81 A B s t)). Qed.
Lemma lem5007807 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) (y : B) (f : A -> B) : (term460 A B t s x y f) = (term461 A B t s x y f).
Proof. exact (MK_COMB (@lem5007806 A B s t) (@lem5007803 A B t s x y f)). Qed.
Lemma lem5007810 {B : Type'} (t : B -> Prop) : (term84 B t) = (term84 B t).
Proof. exact (eq_refl (term84 B t)). Qed.
Lemma lem5007811 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) (y : B) (f : A -> B) : (term462 A B t s x y f) = (term463 A B t s x y f).
Proof. exact (MK_COMB (@lem5007810 B t) (@lem5007807 A B t s x y f)). Qed.
Lemma lem5007814 {B : Type'} (y : B) (t : B -> Prop) : (term464 B y t) = (term464 B y t).
Proof. exact (eq_refl (term464 B y t)). Qed.
Lemma lem5007815 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) (y : B) (f : A -> B) : (term465 A B t s x y f) = (term466 A B t s x y f).
Proof. exact (MK_COMB (@lem5007814 B y t) (@lem5007811 A B t s x y f)). Qed.
Lemma lem5007818 {A : Type'} (s : A -> Prop) : (term84 A s) = (term84 A s).
Proof. exact (eq_refl (term84 A s)). Qed.
Lemma lem5007819 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) (y : B) (f : A -> B) : (term467 A B t s x y f) = (term468 A B t s x y f).
Proof. exact (MK_COMB (@lem5007818 A s) (@lem5007815 A B t s x y f)). Qed.
Lemma lem5007822 {A : Type'} (x : A) (s : A -> Prop) : (term464 A x s) = (term464 A x s).
Proof. exact (eq_refl (term464 A x s)). Qed.
Lemma lem5007823 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) (y : B) (f : A -> B) : (term434 A B t s x y f) = (term469 A B t s x y f).
Proof. exact (MK_COMB (@lem5007822 A x s) (@lem5007819 A B t s x y f)). Qed.
Lemma lem5007826 {A B : Type'} (s : A -> Prop) (x : A) (y : B) (f : A -> B) : (term470 A B s x y f) = (term471 A B s x y f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5007823 A B t s x y f)). Qed.
Lemma lem5007827 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5007828 {A B : Type'} (s : A -> Prop) (x : A) (y : B) (f : A -> B) : (term472 A B s x y f) = (term473 A B s x y f).
Proof. exact (MK_COMB (@lem5007827 B) (@lem5007826 A B s x y f)). Qed.
Lemma lem5007833 {A B : Type'} (x : A) (y : B) (f : A -> B) : (term474 A B x y f) = (term475 A B x y f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5007828 A B s x y f)). Qed.
Lemma lem5007834 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5007835 {A B : Type'} (x : A) (y : B) (f : A -> B) : (term476 A B x y f) = (term477 A B x y f).
Proof. exact (MK_COMB (@lem5007834 A) (@lem5007833 A B x y f)). Qed.
Lemma lem5007840 {A B : Type'} (y : B) (f : A -> B) : (term478 A B y f) = (term479 A B y f).
Proof. exact (fun_ext (fun x : A => @lem5007835 A B x y f)). Qed.
Lemma lem5007841 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5007842 {A B : Type'} (y : B) (f : A -> B) : (term480 A B y f) = (term481 A B y f).
Proof. exact (MK_COMB (@lem5007841 A) (@lem5007840 A B y f)). Qed.
Lemma lem5007847 {A B : Type'} (f : A -> B) : (term482 A B f) = (term483 A B f).
Proof. exact (fun_ext (fun y : B => @lem5007842 A B y f)). Qed.
Lemma lem5007848 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5007849 {A B : Type'} (f : A -> B) : (term484 A B f) = (term485 A B f).
Proof. exact (MK_COMB (@lem5007848 B) (@lem5007847 A B f)). Qed.
Lemma lem5007854 {A B : Type'} : (term486 A B) = (term487 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem5007849 A B f)). Qed.
Lemma lem5007855 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5007864 {A B : Type'} : (term488 A B) = (term489 A B).
Proof. exact (MK_COMB (@lem5007855 A B) (@lem5007854 A B)). Qed.
Lemma lem5007869 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term490 B s x t) = (term490 B s x t).
Proof. exact (eq_refl (term490 B s x t)). Qed.
Lemma lem5007870 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term491 B s t) = (term491 B s t).
Proof. exact (fun_ext (fun x : B => @lem5007869 B s x t)). Qed.
Lemma lem5007871 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5007872 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term10 B s t) = (term10 B s t).
Proof. exact (MK_COMB (@lem5007871 B) (@lem5007870 B s t)). Qed.
Lemma lem5007875 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term492 B s t) = (term492 B s t).
Proof. exact (eq_refl (term492 B s t)). Qed.
Lemma lem5007876 {B : Type'} (s : B -> Prop) (t : B -> Prop) : ((@SUBSET B s t) = (term10 B s t)) = ((@SUBSET B s t) = (term10 B s t)).
Proof. exact (MK_COMB (@lem5007875 B s t) (@lem5007872 B s t)). Qed.
Lemma lem5007877 {B : Type'} (s : B -> Prop) : (term493 B s) = (term493 B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5007876 B s t)). Qed.
Lemma lem5007878 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5007879 {B : Type'} (s : B -> Prop) : (term8 B s) = (term8 B s).
Proof. exact (MK_COMB (@lem5007878 B) (@lem5007877 B s)). Qed.
Lemma lem5007880 {B : Type'} : (term494 B) = (term494 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5007879 B s)). Qed.
Lemma lem5007881 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5007882 {B : Type'} : (term431 B) = (term431 B).
Proof. exact (MK_COMB (@lem5007881 B) (@lem5007880 B)). Qed.
Lemma lem5007883 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5007884 {B : Type'} : (term439 B) = (term439 B).
Proof. exact (MK_COMB (@lem5007883) (@lem5007882 B)). Qed.
Lemma lem5007889 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term490 A s x t) = (term490 A s x t).
Proof. exact (eq_refl (term490 A s x t)). Qed.
Lemma lem5007890 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term491 A s t) = (term491 A s t).
Proof. exact (fun_ext (fun x : A => @lem5007889 A s x t)). Qed.
Lemma lem5007891 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5007892 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term10 A s t) = (term10 A s t).
Proof. exact (MK_COMB (@lem5007891 A) (@lem5007890 A s t)). Qed.
Lemma lem5007895 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term492 A s t) = (term492 A s t).
Proof. exact (eq_refl (term492 A s t)). Qed.
Lemma lem5007896 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((@SUBSET A s t) = (term10 A s t)) = ((@SUBSET A s t) = (term10 A s t)).
Proof. exact (MK_COMB (@lem5007895 A s t) (@lem5007892 A s t)). Qed.
Lemma lem5007897 {A : Type'} (s : A -> Prop) : (term493 A s) = (term493 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5007896 A s t)). Qed.
Lemma lem5007898 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5007899 {A : Type'} (s : A -> Prop) : (term8 A s) = (term8 A s).
Proof. exact (MK_COMB (@lem5007898 A) (@lem5007897 A s)). Qed.
Lemma lem5007900 {A : Type'} : (term494 A) = (term494 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5007899 A s)). Qed.
Lemma lem5007901 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5007902 {A : Type'} : (term431 A) = (term431 A).
Proof. exact (MK_COMB (@lem5007901 A) (@lem5007900 A)). Qed.
Lemma lem5007903 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5007904 {A : Type'} : (term440 A) = (term440 A).
Proof. exact (MK_COMB (@lem5007903) (@lem5007902 A)). Qed.
Lemma lem5007905 {A B : Type'} : (term442 A B) = (term442 A B).
Proof. exact (MK_COMB (@lem5007904 A) (@lem5007884 B)). Qed.
Lemma lem5007910 {B : Type'} (y : B) (f : B -> B) (x : B) (s : B -> Prop) : (term495 B y f x s) = (term495 B y f x s).
Proof. exact (eq_refl (term495 B y f x s)). Qed.
Lemma lem5007911 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term496 B y f s) = (term496 B y f s).
Proof. exact (fun_ext (fun x : B => @lem5007910 B y f x s)). Qed.
Lemma lem5007912 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5007913 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term497 B y f s) = (term497 B y f s).
Proof. exact (MK_COMB (@lem5007912 B) (@lem5007911 B y f s)). Qed.
Lemma lem5007916 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term498 B y f s) = (term498 B y f s).
Proof. exact (eq_refl (term498 B y f s)). Qed.
Lemma lem5007917 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : ((term499 B y f s) = (term497 B y f s)) = ((term499 B y f s) = (term497 B y f s)).
Proof. exact (MK_COMB (@lem5007916 B y f s) (@lem5007913 B y f s)). Qed.
Lemma lem5007918 {B : Type'} (y : B) (s : B -> Prop) : (term500 B y s) = (term500 B y s).
Proof. exact (fun_ext (fun f : B -> B => @lem5007917 B y f s)). Qed.
Lemma lem5007919 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem5007920 {B : Type'} (y : B) (s : B -> Prop) : (term501 B y s) = (term501 B y s).
Proof. exact (MK_COMB (@lem5007919 B) (@lem5007918 B y s)). Qed.
Lemma lem5007921 {B : Type'} (y : B) : (term502 B y) = (term502 B y).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5007920 B y s)). Qed.
Lemma lem5007922 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5007923 {B : Type'} (y : B) : (term503 B y) = (term503 B y).
Proof. exact (MK_COMB (@lem5007922 B) (@lem5007921 B y)). Qed.
Lemma lem5007924 {B : Type'} : (term504 B) = (term504 B).
Proof. exact (fun_ext (fun y : B => @lem5007923 B y)). Qed.
Lemma lem5007925 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5007926 {B : Type'} : (term432 B) = (term432 B).
Proof. exact (MK_COMB (@lem5007925 B) (@lem5007924 B)). Qed.
Lemma lem5007927 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5007928 {B : Type'} : (term443 B) = (term443 B).
Proof. exact (MK_COMB (@lem5007927) (@lem5007926 B)). Qed.
Lemma lem5007929 {A B : Type'} : (term445 A B) = (term445 A B).
Proof. exact (MK_COMB (@lem5007928 B) (@lem5007905 A B)). Qed.
Lemma lem5007934 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term505 A B y f x s) = (term505 A B y f x s).
Proof. exact (eq_refl (term505 A B y f x s)). Qed.
Lemma lem5007935 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term506 A B y f s) = (term506 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem5007934 A B y f x s)). Qed.
Lemma lem5007936 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5007937 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term6 A B y f s) = (term6 A B y f s).
Proof. exact (MK_COMB (@lem5007936 A) (@lem5007935 A B y f s)). Qed.
Lemma lem5007940 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term507 A B y f s) = (term507 A B y f s).
Proof. exact (eq_refl (term507 A B y f s)). Qed.
Lemma lem5007941 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : ((term5 A B y f s) = (term6 A B y f s)) = ((term5 A B y f s) = (term6 A B y f s)).
Proof. exact (MK_COMB (@lem5007940 A B y f s) (@lem5007937 A B y f s)). Qed.
Lemma lem5007942 {A B : Type'} (y : B) (s : A -> Prop) : (term508 A B y s) = (term508 A B y s).
Proof. exact (fun_ext (fun f : A -> B => @lem5007941 A B y f s)). Qed.
Lemma lem5007943 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5007944 {A B : Type'} (y : B) (s : A -> Prop) : (term3 A B y s) = (term3 A B y s).
Proof. exact (MK_COMB (@lem5007943 A B) (@lem5007942 A B y s)). Qed.
Lemma lem5007945 {A B : Type'} (y : B) : (term509 A B y) = (term509 A B y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5007944 A B y s)). Qed.
Lemma lem5007946 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5007947 {A B : Type'} (y : B) : (term1 A B y) = (term1 A B y).
Proof. exact (MK_COMB (@lem5007946 A) (@lem5007945 A B y)). Qed.
Lemma lem5007948 {A B : Type'} : (term510 A B) = (term510 A B).
Proof. exact (fun_ext (fun y : B => @lem5007947 A B y)). Qed.
Lemma lem5007949 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5007950 {A B : Type'} : (term433 A B) = (term433 A B).
Proof. exact (MK_COMB (@lem5007949 B) (@lem5007948 A B)). Qed.
Lemma lem5007951 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5007952 {A B : Type'} : (term446 A B) = (term446 A B).
Proof. exact (MK_COMB (@lem5007951) (@lem5007950 A B)). Qed.
Lemma lem5007953 {A B : Type'} : (term448 A B) = (term448 A B).
Proof. exact (MK_COMB (@lem5007952 A B) (@lem5007929 A B)). Qed.
Lemma lem5007958 {A : Type'} (y : A) (f : A -> A) (x : A) (s : A -> Prop) : (term495 A y f x s) = (term495 A y f x s).
Proof. exact (eq_refl (term495 A y f x s)). Qed.
Lemma lem5007959 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term496 A y f s) = (term496 A y f s).
Proof. exact (fun_ext (fun x : A => @lem5007958 A y f x s)). Qed.
Lemma lem5007960 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5007961 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term497 A y f s) = (term497 A y f s).
Proof. exact (MK_COMB (@lem5007960 A) (@lem5007959 A y f s)). Qed.
Lemma lem5007964 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term498 A y f s) = (term498 A y f s).
Proof. exact (eq_refl (term498 A y f s)). Qed.
Lemma lem5007965 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : ((term499 A y f s) = (term497 A y f s)) = ((term499 A y f s) = (term497 A y f s)).
Proof. exact (MK_COMB (@lem5007964 A y f s) (@lem5007961 A y f s)). Qed.
Lemma lem5007966 {A : Type'} (y : A) (s : A -> Prop) : (term500 A y s) = (term500 A y s).
Proof. exact (fun_ext (fun f : A -> A => @lem5007965 A y f s)). Qed.
Lemma lem5007967 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem5007968 {A : Type'} (y : A) (s : A -> Prop) : (term501 A y s) = (term501 A y s).
Proof. exact (MK_COMB (@lem5007967 A) (@lem5007966 A y s)). Qed.
Lemma lem5007969 {A : Type'} (y : A) : (term502 A y) = (term502 A y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5007968 A y s)). Qed.
Lemma lem5007970 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5007971 {A : Type'} (y : A) : (term503 A y) = (term503 A y).
Proof. exact (MK_COMB (@lem5007970 A) (@lem5007969 A y)). Qed.
Lemma lem5007972 {A : Type'} : (term504 A) = (term504 A).
Proof. exact (fun_ext (fun y : A => @lem5007971 A y)). Qed.
Lemma lem5007973 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5007974 {A : Type'} : (term432 A) = (term432 A).
Proof. exact (MK_COMB (@lem5007973 A) (@lem5007972 A)). Qed.
Lemma lem5007975 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5007976 {A : Type'} : (term443 A) = (term443 A).
Proof. exact (MK_COMB (@lem5007975) (@lem5007974 A)). Qed.
Lemma lem5007977 {A B : Type'} : (term450 A B) = (term450 A B).
Proof. exact (MK_COMB (@lem5007976 A) (@lem5007953 A B)). Qed.
Lemma lem5007981 {A : Type'} (x' : A) (x : A) (h1 : (x' = x) = False) : (x' = x) = False.
Proof. exact (h1). Qed.
Lemma lem5007982 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5007983 {A : Type'} (x' : A) (x : A) (h1 : (x' = x) = False) : (term384 A x' x) = (or False).
Proof. exact (MK_COMB (@lem5007982) (@lem5007981 A x' x h1)). Qed.
Lemma lem5007984 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (@IN A x' s).
Proof. exact (eq_refl (@IN A x' s)). Qed.
Lemma lem5007985 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : (x' = x) = False) : (term17 A x x' s) = (term511 A x' s).
Proof. exact (MK_COMB (@lem5007983 A x' x h1) (@lem5007984 A x' s)). Qed.
Lemma lem5007987 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem5007988 {A : Type'} (x' : A) (s : A -> Prop) : (term511 A x' s) = (@IN A x' s).
Proof. exact (@lem5007987 (@IN A x' s)). Qed.
Lemma lem5007989 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : (x' = x) = False) : (term17 A x x' s) = (@IN A x' s).
Proof. exact (TRANS (@lem5007985 A s x' x h1) (@lem5007988 A x' s)). Qed.
Lemma lem5007990 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5007991 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : (x' = x) = False) : (term408 A x x' s) = (term65 A x' s).
Proof. exact (MK_COMB (@lem5007990) (@lem5007989 A s x' x h1)). Qed.
Lemma lem5007997 {A : Type'} (x' : A) (x : A) (h1 : (x' = x) = False) : (x' = x) = False.
Proof. exact (h1). Qed.
Lemma lem5007998 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem5007999 {A B : Type'} (x' : A) (x : A) (h1 : (x' = x) = False) : (term512 A B x' x) = (@COND B False).
Proof. exact (MK_COMB (@lem5007998 B) (@lem5007997 A x' x h1)). Qed.
Lemma lem5008000 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5008001 {A B : Type'} (y : B) (x' : A) (x : A) (h1 : (x' = x) = False) : (term513 A B x' x y) = (@COND B False y).
Proof. exact (MK_COMB (@lem5007999 A B x' x h1) (@lem5008000 B y)). Qed.
Lemma lem5008002 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (eq_refl (f x')). Qed.
Lemma lem5008003 {A B : Type'} (y : B) (f : A -> B) (x' : A) (x : A) (h1 : (x' = x) = False) : (term376 A B x y f x') = (term514 A B y f x').
Proof. exact (MK_COMB (@lem5008001 A B y x' x h1) (@lem5008002 A B f x')). Qed.
Lemma lem5008005 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem5008006 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem5008005 B t1 t2). Qed.
Lemma lem5008007 {A B : Type'} (y : B) (f : A -> B) (x' : A) : (term514 A B y f x') = (f x').
Proof. exact (@lem5008006 B y (f x')). Qed.
Lemma lem5008008 {A B : Type'} (y : B) (f : A -> B) (x' : A) (x : A) (h1 : (x' = x) = False) : (term376 A B x y f x') = (f x').
Proof. exact (TRANS (@lem5008003 A B y f x' x h1) (@lem5008007 A B y f x')). Qed.
Lemma lem5008009 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5008010 {A B : Type'} (y : B) (f : A -> B) (x' : A) (x : A) (h1 : (x' = x) = False) : (term409 A B x y f x') = (term515 A B f x').
Proof. exact (MK_COMB (@lem5008009 B) (@lem5008008 A B y f x' x h1)). Qed.
Lemma lem5008015 {A B : Type'} (x : A) (y : B) (f : A -> B) (y' : A) : (term376 A B x y f y') = (term376 A B x y f y').
Proof. exact (eq_refl (term376 A B x y f y')). Qed.
Lemma lem5008016 {A B : Type'} (y : B) (f : A -> B) (y' : A) (x' : A) (x : A) (h1 : (x' = x) = False) : ((term376 A B x y f x') = (term376 A B x y f y')) = ((f x') = (term376 A B x y f y')).
Proof. exact (MK_COMB (@lem5008010 A B y f x' x h1) (@lem5008015 A B x y f y')). Qed.
Lemma lem5008019 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5008020 {A B : Type'} (y : B) (f : A -> B) (y' : A) (x' : A) (x : A) (h1 : (x' = x) = False) : (term411 A B x' x y f y') = (term516 A B x' x y f y').
Proof. exact (MK_COMB (@lem5008019) (@lem5008016 A B y f y' x' x h1)). Qed.
Lemma lem5008023 {A : Type'} (x' : A) (y : A) : (x' = y) = (x' = y).
Proof. exact (eq_refl (x' = y)). Qed.
Lemma lem5008024 {A B : Type'} (y : B) (f : A -> B) (y' : A) (x' : A) (x : A) (h1 : (x' = x) = False) : (term413 A B x y f x' y') = (term517 A B x y f x' y').
Proof. exact (MK_COMB (@lem5008020 A B y f y' x' x h1) (@lem5008023 A x' y')). Qed.
Lemma lem5008029 {A : Type'} (x : A) (y : A) (s : A -> Prop) : (term408 A x y s) = (term408 A x y s).
Proof. exact (eq_refl (term408 A x y s)). Qed.
Lemma lem5008030 {A B : Type'} (s : A -> Prop) (y : B) (f : A -> B) (y' : A) (x' : A) (x : A) (h1 : (x' = x) = False) : (term415 A B s x y f x' y') = (term518 A B s x y f x' y').
Proof. exact (MK_COMB (@lem5008029 A x y' s) (@lem5008024 A B y f y' x' x h1)). Qed.
Lemma lem5008033 {A B : Type'} (s : A -> Prop) (y : B) (f : A -> B) (x' : A) (x : A) (h1 : (x' = x) = False) : (term417 A B s x y f x') = (term519 A B s x y f x').
Proof. exact (fun_ext (fun y' : A => @lem5008030 A B s y f y' x' x h1)). Qed.
Lemma lem5008034 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5008035 {A B : Type'} (s : A -> Prop) (y : B) (f : A -> B) (x' : A) (x : A) (h1 : (x' = x) = False) : (term419 A B s x y f x') = (term520 A B s x y f x').
Proof. exact (MK_COMB (@lem5008034 A) (@lem5008033 A B s y f x' x h1)). Qed.
Lemma lem5008040 {A B : Type'} (s : A -> Prop) (y : B) (f : A -> B) (x' : A) (x : A) (h1 : (x' = x) = False) : (term421 A B s x y f x') = (term521 A B s x y f x').
Proof. exact (MK_COMB (@lem5007991 A s x' x h1) (@lem5008035 A B s y f x' x h1)). Qed.
Lemma lem5008043 {A B : Type'} (s : A -> Prop) (x : A) (y : B) (f : A -> B) (x' : A) : term522 A B s x y f x'.
Proof. exact (fun h0 : (x' = x) = False => @lem5008040 A B s y f x' x h0). Qed.
Lemma lem5008045 {A : Type'} (x' : A) (x : A) (h1 : (x' = x) = True) : (x' = x) = True.
Proof. exact (h1). Qed.
Lemma lem5008046 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5008047 {A : Type'} (x' : A) (x : A) (h1 : (x' = x) = True) : (term384 A x' x) = (or True).
Proof. exact (MK_COMB (@lem5008046) (@lem5008045 A x' x h1)). Qed.
Lemma lem5008048 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (@IN A x' s).
Proof. exact (eq_refl (@IN A x' s)). Qed.
Lemma lem5008049 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : (x' = x) = True) : (term17 A x x' s) = (term523 A x' s).
Proof. exact (MK_COMB (@lem5008047 A x' x h1) (@lem5008048 A x' s)). Qed.
Lemma lem5008051 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem5008052 {A : Type'} (x' : A) (s : A -> Prop) : (term523 A x' s) = True.
Proof. exact (@lem5008051 (@IN A x' s)). Qed.
Lemma lem5008053 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : (x' = x) = True) : (term17 A x x' s) = True.
Proof. exact (TRANS (@lem5008049 A s x' x h1) (@lem5008052 A x' s)). Qed.
Lemma lem5008054 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5008055 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : (x' = x) = True) : (term408 A x x' s) = (imp True).
Proof. exact (MK_COMB (@lem5008054) (@lem5008053 A s x' x h1)). Qed.
Lemma lem5008061 {A : Type'} (x' : A) (x : A) (h1 : (x' = x) = True) : (x' = x) = True.
Proof. exact (h1). Qed.
Lemma lem5008062 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem5008063 {A B : Type'} (x' : A) (x : A) (h1 : (x' = x) = True) : (term512 A B x' x) = (@COND B True).
Proof. exact (MK_COMB (@lem5008062 B) (@lem5008061 A x' x h1)). Qed.
Lemma lem5008064 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5008065 {A B : Type'} (y : B) (x' : A) (x : A) (h1 : (x' = x) = True) : (term513 A B x' x y) = (@COND B True y).
Proof. exact (MK_COMB (@lem5008063 A B x' x h1) (@lem5008064 B y)). Qed.
Lemma lem5008066 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (eq_refl (f x')). Qed.
Lemma lem5008067 {A B : Type'} (y : B) (f : A -> B) (x' : A) (x : A) (h1 : (x' = x) = True) : (term376 A B x y f x') = (term524 A B y f x').
Proof. exact (MK_COMB (@lem5008065 A B y x' x h1) (@lem5008066 A B f x')). Qed.
Lemma lem5008069 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem5008070 {B : Type'} (t2 : B) (t1 : B) : (@COND B True t1 t2) = t1.
Proof. exact (@lem5008069 B t2 t1). Qed.
Lemma lem5008071 {A B : Type'} (f : A -> B) (x' : A) (y : B) : (term524 A B y f x') = y.
Proof. exact (@lem5008070 B (f x') y). Qed.
Lemma lem5008072 {A B : Type'} (f : A -> B) (y : B) (x' : A) (x : A) (h1 : (x' = x) = True) : (term376 A B x y f x') = y.
Proof. exact (TRANS (@lem5008067 A B y f x' x h1) (@lem5008071 A B f x' y)). Qed.
Lemma lem5008073 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5008074 {A B : Type'} (f : A -> B) (y : B) (x' : A) (x : A) (h1 : (x' = x) = True) : (term409 A B x y f x') = (@eq B y).
Proof. exact (MK_COMB (@lem5008073 B) (@lem5008072 A B f y x' x h1)). Qed.
Lemma lem5008079 {A B : Type'} (x : A) (y : B) (f : A -> B) (y' : A) : (term376 A B x y f y') = (term376 A B x y f y').
Proof. exact (eq_refl (term376 A B x y f y')). Qed.
Lemma lem5008080 {A B : Type'} (y : B) (f : A -> B) (y' : A) (x' : A) (x : A) (h1 : (x' = x) = True) : ((term376 A B x y f x') = (term376 A B x y f y')) = (y = (term376 A B x y f y')).
Proof. exact (MK_COMB (@lem5008074 A B f y x' x h1) (@lem5008079 A B x y f y')). Qed.
Lemma lem5008083 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5008084 {A B : Type'} (y : B) (f : A -> B) (y' : A) (x' : A) (x : A) (h1 : (x' = x) = True) : (term411 A B x' x y f y') = (term525 A B x y f y').
Proof. exact (MK_COMB (@lem5008083) (@lem5008080 A B y f y' x' x h1)). Qed.
Lemma lem5008087 {A : Type'} (x' : A) (y : A) : (x' = y) = (x' = y).
Proof. exact (eq_refl (x' = y)). Qed.
Lemma lem5008088 {A B : Type'} (y : B) (f : A -> B) (y' : A) (x' : A) (x : A) (h1 : (x' = x) = True) : (term413 A B x y f x' y') = (term526 A B x y f x' y').
Proof. exact (MK_COMB (@lem5008084 A B y f y' x' x h1) (@lem5008087 A x' y')). Qed.
Lemma lem5008093 {A : Type'} (x : A) (y : A) (s : A -> Prop) : (term408 A x y s) = (term408 A x y s).
Proof. exact (eq_refl (term408 A x y s)). Qed.
Lemma lem5008094 {A B : Type'} (s : A -> Prop) (y : B) (f : A -> B) (y' : A) (x' : A) (x : A) (h1 : (x' = x) = True) : (term415 A B s x y f x' y') = (term527 A B s x y f x' y').
Proof. exact (MK_COMB (@lem5008093 A x y' s) (@lem5008088 A B y f y' x' x h1)). Qed.
Lemma lem5008097 {A B : Type'} (s : A -> Prop) (y : B) (f : A -> B) (x' : A) (x : A) (h1 : (x' = x) = True) : (term417 A B s x y f x') = (term528 A B s x y f x').
Proof. exact (fun_ext (fun y' : A => @lem5008094 A B s y f y' x' x h1)). Qed.
Lemma lem5008098 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5008099 {A B : Type'} (s : A -> Prop) (y : B) (f : A -> B) (x' : A) (x : A) (h1 : (x' = x) = True) : (term419 A B s x y f x') = (term529 A B s x y f x').
Proof. exact (MK_COMB (@lem5008098 A) (@lem5008097 A B s y f x' x h1)). Qed.
Lemma lem5008104 {A B : Type'} (s : A -> Prop) (y : B) (f : A -> B) (x' : A) (x : A) (h1 : (x' = x) = True) : (term421 A B s x y f x') = (term530 A B s x y f x').
Proof. exact (MK_COMB (@lem5008055 A s x' x h1) (@lem5008099 A B s y f x' x h1)). Qed.
Lemma lem5008106 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem5008107 {A B : Type'} (s : A -> Prop) (x : A) (y : B) (f : A -> B) (x' : A) : (term530 A B s x y f x') = (term529 A B s x y f x').
Proof. exact (@lem5008106 (term529 A B s x y f x')). Qed.
Lemma lem5008112 {A B : Type'} (s : A -> Prop) (y : B) (f : A -> B) (x' : A) (x : A) (h1 : (x' = x) = True) : (term421 A B s x y f x') = (term529 A B s x y f x').
Proof. exact (TRANS (@lem5008104 A B s y f x' x h1) (@lem5008107 A B s x y f x')). Qed.
Lemma lem5008113 {A B : Type'} (s : A -> Prop) (x : A) (y : B) (f : A -> B) (x' : A) : term531 A B s x y f x'.
Proof. exact (fun h0 : (x' = x) = True => @lem5008112 A B s y f x' x h0). Qed.
Lemma lem5008114 {A B : Type'} (s : A -> Prop) (x : A) (y : B) (f : A -> B) (x' : A) : term532 A B s x y f x'.
Proof. exact (conj (@lem5008043 A B s x y f x') (@lem5008113 A B s x y f x')). Qed.
Lemma lem5008116 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term533 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem5008117 {A B : Type'} (s : A -> Prop) (x : A) (y : B) (f : A -> B) (x' : A) : term534 A B s x y f x'.
Proof. exact (@lem5008116 (term421 A B s x y f x') (term529 A B s x y f x') (x' = x) (term521 A B s x y f x')). Qed.
Lemma lem5008132 {A B : Type'} (s : A -> Prop) (x : A) (y : B) (f : A -> B) (x' : A) : (term421 A B s x y f x') = (term535 A B s x y f x').
Proof. exact (@lem5008117 A B s x y f x' (@lem5008114 A B s x y f x')). Qed.
Lemma lem5008136 {A : Type'} (y : A) (x : A) (h1 : (y = x) = False) : (y = x) = False.
Proof. exact (h1). Qed.
Lemma lem5008137 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5008138 {A : Type'} (y : A) (x : A) (h1 : (y = x) = False) : (term384 A y x) = (or False).
Proof. exact (MK_COMB (@lem5008137) (@lem5008136 A y x h1)). Qed.
Lemma lem5008139 {A : Type'} (y : A) (s : A -> Prop) : (@IN A y s) = (@IN A y s).
Proof. exact (eq_refl (@IN A y s)). Qed.
Lemma lem5008140 {A : Type'} (s : A -> Prop) (y : A) (x : A) (h1 : (y = x) = False) : (term17 A x y s) = (term511 A y s).
Proof. exact (MK_COMB (@lem5008138 A y x h1) (@lem5008139 A y s)). Qed.
Lemma lem5008142 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem5008143 {A : Type'} (y : A) (s : A -> Prop) : (term511 A y s) = (@IN A y s).
Proof. exact (@lem5008142 (@IN A y s)). Qed.
Lemma lem5008144 {A : Type'} (s : A -> Prop) (y : A) (x : A) (h1 : (y = x) = False) : (term17 A x y s) = (@IN A y s).
Proof. exact (TRANS (@lem5008140 A s y x h1) (@lem5008143 A y s)). Qed.
Lemma lem5008145 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5008146 {A : Type'} (s : A -> Prop) (y : A) (x : A) (h1 : (y = x) = False) : (term408 A x y s) = (term65 A y s).
Proof. exact (MK_COMB (@lem5008145) (@lem5008144 A s y x h1)). Qed.
Lemma lem5008148 {A : Type'} (y : A) (x : A) (h1 : (y = x) = False) : (y = x) = False.
Proof. exact (h1). Qed.
Lemma lem5008149 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem5008150 {A B : Type'} (y : A) (x : A) (h1 : (y = x) = False) : (term512 A B y x) = (@COND B False).
Proof. exact (MK_COMB (@lem5008149 B) (@lem5008148 A y x h1)). Qed.
Lemma lem5008151 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5008152 {A B : Type'} (y : B) (y' : A) (x : A) (h1 : (y' = x) = False) : (term513 A B y' x y) = (@COND B False y).
Proof. exact (MK_COMB (@lem5008150 A B y' x h1) (@lem5008151 B y)). Qed.
Lemma lem5008153 {A B : Type'} (f : A -> B) (y : A) : (f y) = (f y).
Proof. exact (eq_refl (f y)). Qed.
Lemma lem5008154 {A B : Type'} (y : B) (f : A -> B) (y' : A) (x : A) (h1 : (y' = x) = False) : (term376 A B x y f y') = (term514 A B y f y').
Proof. exact (MK_COMB (@lem5008152 A B y y' x h1) (@lem5008153 A B f y')). Qed.
Lemma lem5008156 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem5008157 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem5008156 B t1 t2). Qed.
Lemma lem5008158 {A B : Type'} (y : B) (f : A -> B) (y' : A) : (term514 A B y f y') = (f y').
Proof. exact (@lem5008157 B y (f y')). Qed.
Lemma lem5008159 {A B : Type'} (y : B) (f : A -> B) (y' : A) (x : A) (h1 : (y' = x) = False) : (term376 A B x y f y') = (f y').
Proof. exact (TRANS (@lem5008154 A B y f y' x h1) (@lem5008158 A B y f y')). Qed.
Lemma lem5008160 {A B : Type'} (f : A -> B) (x' : A) : (term515 A B f x') = (term515 A B f x').
Proof. exact (eq_refl (term515 A B f x')). Qed.
Lemma lem5008161 {A B : Type'} (y : B) (x' : A) (f : A -> B) (y' : A) (x : A) (h1 : (y' = x) = False) : ((f x') = (term376 A B x y f y')) = ((f x') = (f y')).
Proof. exact (MK_COMB (@lem5008160 A B f x') (@lem5008159 A B y f y' x h1)). Qed.
Lemma lem5008164 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5008165 {A B : Type'} (y : B) (x' : A) (f : A -> B) (y' : A) (x : A) (h1 : (y' = x) = False) : (term516 A B x' x y f y') = (term536 A B x' f y').
Proof. exact (MK_COMB (@lem5008164) (@lem5008161 A B y x' f y' x h1)). Qed.
Lemma lem5008168 {A : Type'} (x' : A) (y : A) : (x' = y) = (x' = y).
Proof. exact (eq_refl (x' = y)). Qed.
Lemma lem5008169 {A B : Type'} (y : B) (f : A -> B) (x' : A) (y' : A) (x : A) (h1 : (y' = x) = False) : (term517 A B x y f x' y') = (term171 A B f x' y').
Proof. exact (MK_COMB (@lem5008165 A B y x' f y' x h1) (@lem5008168 A x' y')). Qed.
Lemma lem5008174 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) (x' : A) (y' : A) (x : A) (h1 : (y' = x) = False) : (term518 A B s x y f x' y') = (term64 A B s f x' y').
Proof. exact (MK_COMB (@lem5008146 A s y' x h1) (@lem5008169 A B y f x' y' x h1)). Qed.
Lemma lem5008177 {A B : Type'} (x : A) (y : B) (s : A -> Prop) (f : A -> B) (x' : A) (y' : A) : term537 A B x y s f x' y'.
Proof. exact (fun h0 : (y' = x) = False => @lem5008174 A B y s f x' y' x h0). Qed.
Lemma lem5008179 {A : Type'} (y : A) (x : A) (h1 : (y = x) = True) : (y = x) = True.
Proof. exact (h1). Qed.
Lemma lem5008180 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5008181 {A : Type'} (y : A) (x : A) (h1 : (y = x) = True) : (term384 A y x) = (or True).
Proof. exact (MK_COMB (@lem5008180) (@lem5008179 A y x h1)). Qed.
Lemma lem5008182 {A : Type'} (y : A) (s : A -> Prop) : (@IN A y s) = (@IN A y s).
Proof. exact (eq_refl (@IN A y s)). Qed.
Lemma lem5008183 {A : Type'} (s : A -> Prop) (y : A) (x : A) (h1 : (y = x) = True) : (term17 A x y s) = (term523 A y s).
Proof. exact (MK_COMB (@lem5008181 A y x h1) (@lem5008182 A y s)). Qed.
Lemma lem5008185 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem5008186 {A : Type'} (y : A) (s : A -> Prop) : (term523 A y s) = True.
Proof. exact (@lem5008185 (@IN A y s)). Qed.
Lemma lem5008187 {A : Type'} (s : A -> Prop) (y : A) (x : A) (h1 : (y = x) = True) : (term17 A x y s) = True.
Proof. exact (TRANS (@lem5008183 A s y x h1) (@lem5008186 A y s)). Qed.
Lemma lem5008188 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5008189 {A : Type'} (s : A -> Prop) (y : A) (x : A) (h1 : (y = x) = True) : (term408 A x y s) = (imp True).
Proof. exact (MK_COMB (@lem5008188) (@lem5008187 A s y x h1)). Qed.
Lemma lem5008191 {A : Type'} (y : A) (x : A) (h1 : (y = x) = True) : (y = x) = True.
Proof. exact (h1). Qed.
Lemma lem5008192 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem5008193 {A B : Type'} (y : A) (x : A) (h1 : (y = x) = True) : (term512 A B y x) = (@COND B True).
Proof. exact (MK_COMB (@lem5008192 B) (@lem5008191 A y x h1)). Qed.
Lemma lem5008194 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5008195 {A B : Type'} (y : B) (y' : A) (x : A) (h1 : (y' = x) = True) : (term513 A B y' x y) = (@COND B True y).
Proof. exact (MK_COMB (@lem5008193 A B y' x h1) (@lem5008194 B y)). Qed.
Lemma lem5008196 {A B : Type'} (f : A -> B) (y : A) : (f y) = (f y).
Proof. exact (eq_refl (f y)). Qed.
Lemma lem5008197 {A B : Type'} (y : B) (f : A -> B) (y' : A) (x : A) (h1 : (y' = x) = True) : (term376 A B x y f y') = (term524 A B y f y').
Proof. exact (MK_COMB (@lem5008195 A B y y' x h1) (@lem5008196 A B f y')). Qed.
Lemma lem5008199 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem5008200 {B : Type'} (t2 : B) (t1 : B) : (@COND B True t1 t2) = t1.
Proof. exact (@lem5008199 B t2 t1). Qed.
Lemma lem5008201 {A B : Type'} (f : A -> B) (y : A) (y' : B) : (term524 A B y' f y) = y'.
Proof. exact (@lem5008200 B (f y) y'). Qed.
Lemma lem5008202 {A B : Type'} (f : A -> B) (y : B) (y' : A) (x : A) (h1 : (y' = x) = True) : (term376 A B x y f y') = y.
Proof. exact (TRANS (@lem5008197 A B y f y' x h1) (@lem5008201 A B f y' y)). Qed.
Lemma lem5008203 {A B : Type'} (f : A -> B) (x' : A) : (term515 A B f x') = (term515 A B f x').
Proof. exact (eq_refl (term515 A B f x')). Qed.
Lemma lem5008204 {A B : Type'} (f : A -> B) (x' : A) (y : B) (y' : A) (x : A) (h1 : (y' = x) = True) : ((f x') = (term376 A B x y f y')) = ((f x') = y).
Proof. exact (MK_COMB (@lem5008203 A B f x') (@lem5008202 A B f y y' x h1)). Qed.
Lemma lem5008207 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5008208 {A B : Type'} (f : A -> B) (x' : A) (y : B) (y' : A) (x : A) (h1 : (y' = x) = True) : (term516 A B x' x y f y') = (term538 A B f x' y).
Proof. exact (MK_COMB (@lem5008207) (@lem5008204 A B f x' y y' x h1)). Qed.
Lemma lem5008211 {A : Type'} (x' : A) (y : A) : (x' = y) = (x' = y).
Proof. exact (eq_refl (x' = y)). Qed.
Lemma lem5008212 {A B : Type'} (f : A -> B) (y : B) (x' : A) (y' : A) (x : A) (h1 : (y' = x) = True) : (term517 A B x y f x' y') = (term539 A B f y x' y').
Proof. exact (MK_COMB (@lem5008208 A B f x' y y' x h1) (@lem5008211 A x' y')). Qed.
Lemma lem5008217 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x' : A) (y' : A) (x : A) (h1 : (y' = x) = True) : (term518 A B s x y f x' y') = (term540 A B f y x' y').
Proof. exact (MK_COMB (@lem5008189 A s y' x h1) (@lem5008212 A B f y x' y' x h1)). Qed.
Lemma lem5008219 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem5008220 {A B : Type'} (f : A -> B) (y : B) (x' : A) (y' : A) : (term540 A B f y x' y') = (term539 A B f y x' y').
Proof. exact (@lem5008219 (term539 A B f y x' y')). Qed.
Lemma lem5008225 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x' : A) (y' : A) (x : A) (h1 : (y' = x) = True) : (term518 A B s x y f x' y') = (term539 A B f y x' y').
Proof. exact (TRANS (@lem5008217 A B s f y x' y' x h1) (@lem5008220 A B f y x' y')). Qed.
Lemma lem5008226 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : B) (x' : A) (y' : A) : term541 A B s x f y x' y'.
Proof. exact (fun h0 : (y' = x) = True => @lem5008225 A B s f y x' y' x h0). Qed.
Lemma lem5008227 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : B) (x' : A) (y' : A) : term542 A B s x f y x' y'.
Proof. exact (conj (@lem5008177 A B x y s f x' y') (@lem5008226 A B s x f y x' y')). Qed.
Lemma lem5008229 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term533 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem5008230 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) (y' : A) : term543 A B y x s f x' y'.
Proof. exact (@lem5008229 (term518 A B s x y f x' y') (term539 A B f y x' y') (y' = x) (term64 A B s f x' y')). Qed.
Lemma lem5008275 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) (y' : A) : (term518 A B s x y f x' y') = (term544 A B y x s f x' y').
Proof. exact (@lem5008230 A B y x s f x' y' (@lem5008227 A B s x f y x' y')). Qed.
Lemma lem5008276 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term519 A B s x y f x') = (term545 A B y x s f x').
Proof. exact (fun_ext (fun y' : A => @lem5008275 A B y x s f x' y')). Qed.
Lemma lem5008277 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5008278 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term520 A B s x y f x') = (term546 A B y x s f x').
Proof. exact (MK_COMB (@lem5008277 A) (@lem5008276 A B y x s f x')). Qed.
Lemma lem5008281 {A : Type'} (x' : A) (s : A -> Prop) : (term65 A x' s) = (term65 A x' s).
Proof. exact (eq_refl (term65 A x' s)). Qed.
Lemma lem5008282 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term521 A B s x y f x') = (term547 A B y x s f x').
Proof. exact (MK_COMB (@lem5008281 A x' s) (@lem5008278 A B y x s f x')). Qed.
Lemma lem5008285 {A : Type'} (x' : A) (x : A) : (term384 A x' x) = (term384 A x' x).
Proof. exact (eq_refl (term384 A x' x)). Qed.
Lemma lem5008286 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term548 A B s x y f x') = (term549 A B y x s f x').
Proof. exact (MK_COMB (@lem5008285 A x' x) (@lem5008282 A B y x s f x')). Qed.
Lemma lem5008290 {A : Type'} (y : A) (x : A) (h1 : (y = x) = False) : (y = x) = False.
Proof. exact (h1). Qed.
Lemma lem5008291 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5008292 {A : Type'} (y : A) (x : A) (h1 : (y = x) = False) : (term384 A y x) = (or False).
Proof. exact (MK_COMB (@lem5008291) (@lem5008290 A y x h1)). Qed.
Lemma lem5008293 {A : Type'} (y : A) (s : A -> Prop) : (@IN A y s) = (@IN A y s).
Proof. exact (eq_refl (@IN A y s)). Qed.
Lemma lem5008294 {A : Type'} (s : A -> Prop) (y : A) (x : A) (h1 : (y = x) = False) : (term17 A x y s) = (term511 A y s).
Proof. exact (MK_COMB (@lem5008292 A y x h1) (@lem5008293 A y s)). Qed.
Lemma lem5008296 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem5008297 {A : Type'} (y : A) (s : A -> Prop) : (term511 A y s) = (@IN A y s).
Proof. exact (@lem5008296 (@IN A y s)). Qed.
Lemma lem5008298 {A : Type'} (s : A -> Prop) (y : A) (x : A) (h1 : (y = x) = False) : (term17 A x y s) = (@IN A y s).
Proof. exact (TRANS (@lem5008294 A s y x h1) (@lem5008297 A y s)). Qed.
Lemma lem5008299 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5008300 {A : Type'} (s : A -> Prop) (y : A) (x : A) (h1 : (y = x) = False) : (term408 A x y s) = (term65 A y s).
Proof. exact (MK_COMB (@lem5008299) (@lem5008298 A s y x h1)). Qed.
Lemma lem5008302 {A : Type'} (y : A) (x : A) (h1 : (y = x) = False) : (y = x) = False.
Proof. exact (h1). Qed.
Lemma lem5008303 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem5008304 {A B : Type'} (y : A) (x : A) (h1 : (y = x) = False) : (term512 A B y x) = (@COND B False).
Proof. exact (MK_COMB (@lem5008303 B) (@lem5008302 A y x h1)). Qed.
Lemma lem5008305 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5008306 {A B : Type'} (y : B) (y' : A) (x : A) (h1 : (y' = x) = False) : (term513 A B y' x y) = (@COND B False y).
Proof. exact (MK_COMB (@lem5008304 A B y' x h1) (@lem5008305 B y)). Qed.
Lemma lem5008307 {A B : Type'} (f : A -> B) (y : A) : (f y) = (f y).
Proof. exact (eq_refl (f y)). Qed.
Lemma lem5008308 {A B : Type'} (y : B) (f : A -> B) (y' : A) (x : A) (h1 : (y' = x) = False) : (term376 A B x y f y') = (term514 A B y f y').
Proof. exact (MK_COMB (@lem5008306 A B y y' x h1) (@lem5008307 A B f y')). Qed.
Lemma lem5008310 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem5008311 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem5008310 B t1 t2). Qed.
Lemma lem5008312 {A B : Type'} (y : B) (f : A -> B) (y' : A) : (term514 A B y f y') = (f y').
Proof. exact (@lem5008311 B y (f y')). Qed.
Lemma lem5008313 {A B : Type'} (y : B) (f : A -> B) (y' : A) (x : A) (h1 : (y' = x) = False) : (term376 A B x y f y') = (f y').
Proof. exact (TRANS (@lem5008308 A B y f y' x h1) (@lem5008312 A B y f y')). Qed.
Lemma lem5008314 {B : Type'} (y : B) : (@eq B y) = (@eq B y).
Proof. exact (eq_refl (@eq B y)). Qed.
Lemma lem5008315 {A B : Type'} (y : B) (f : A -> B) (y' : A) (x : A) (h1 : (y' = x) = False) : (y = (term376 A B x y f y')) = (y = (f y')).
Proof. exact (MK_COMB (@lem5008314 B y) (@lem5008313 A B y f y' x h1)). Qed.
Lemma lem5008318 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5008319 {A B : Type'} (y : B) (f : A -> B) (y' : A) (x : A) (h1 : (y' = x) = False) : (term525 A B x y f y') = (term550 A B y f y').
Proof. exact (MK_COMB (@lem5008318) (@lem5008315 A B y f y' x h1)). Qed.
Lemma lem5008322 {A : Type'} (x' : A) (y : A) : (x' = y) = (x' = y).
Proof. exact (eq_refl (x' = y)). Qed.
Lemma lem5008323 {A B : Type'} (y : B) (f : A -> B) (x' : A) (y' : A) (x : A) (h1 : (y' = x) = False) : (term526 A B x y f x' y') = (term551 A B y f x' y').
Proof. exact (MK_COMB (@lem5008319 A B y f y' x h1) (@lem5008322 A x' y')). Qed.
Lemma lem5008328 {A B : Type'} (s : A -> Prop) (y : B) (f : A -> B) (x' : A) (y' : A) (x : A) (h1 : (y' = x) = False) : (term527 A B s x y f x' y') = (term552 A B s y f x' y').
Proof. exact (MK_COMB (@lem5008300 A s y' x h1) (@lem5008323 A B y f x' y' x h1)). Qed.
Lemma lem5008331 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) (y' : A) : term553 A B x s y f x' y'.
Proof. exact (fun h0 : (y' = x) = False => @lem5008328 A B s y f x' y' x h0). Qed.
Lemma lem5008333 {A : Type'} (y : A) (x : A) (h1 : (y = x) = True) : (y = x) = True.
Proof. exact (h1). Qed.
Lemma lem5008334 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5008335 {A : Type'} (y : A) (x : A) (h1 : (y = x) = True) : (term384 A y x) = (or True).
Proof. exact (MK_COMB (@lem5008334) (@lem5008333 A y x h1)). Qed.
Lemma lem5008336 {A : Type'} (y : A) (s : A -> Prop) : (@IN A y s) = (@IN A y s).
Proof. exact (eq_refl (@IN A y s)). Qed.
Lemma lem5008337 {A : Type'} (s : A -> Prop) (y : A) (x : A) (h1 : (y = x) = True) : (term17 A x y s) = (term523 A y s).
Proof. exact (MK_COMB (@lem5008335 A y x h1) (@lem5008336 A y s)). Qed.
Lemma lem5008339 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem5008340 {A : Type'} (y : A) (s : A -> Prop) : (term523 A y s) = True.
Proof. exact (@lem5008339 (@IN A y s)). Qed.
Lemma lem5008341 {A : Type'} (s : A -> Prop) (y : A) (x : A) (h1 : (y = x) = True) : (term17 A x y s) = True.
Proof. exact (TRANS (@lem5008337 A s y x h1) (@lem5008340 A y s)). Qed.
Lemma lem5008342 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5008343 {A : Type'} (s : A -> Prop) (y : A) (x : A) (h1 : (y = x) = True) : (term408 A x y s) = (imp True).
Proof. exact (MK_COMB (@lem5008342) (@lem5008341 A s y x h1)). Qed.
Lemma lem5008345 {A : Type'} (y : A) (x : A) (h1 : (y = x) = True) : (y = x) = True.
Proof. exact (h1). Qed.
Lemma lem5008346 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem5008347 {A B : Type'} (y : A) (x : A) (h1 : (y = x) = True) : (term512 A B y x) = (@COND B True).
Proof. exact (MK_COMB (@lem5008346 B) (@lem5008345 A y x h1)). Qed.
Lemma lem5008348 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5008349 {A B : Type'} (y : B) (y' : A) (x : A) (h1 : (y' = x) = True) : (term513 A B y' x y) = (@COND B True y).
Proof. exact (MK_COMB (@lem5008347 A B y' x h1) (@lem5008348 B y)). Qed.
Lemma lem5008350 {A B : Type'} (f : A -> B) (y : A) : (f y) = (f y).
Proof. exact (eq_refl (f y)). Qed.
Lemma lem5008351 {A B : Type'} (y : B) (f : A -> B) (y' : A) (x : A) (h1 : (y' = x) = True) : (term376 A B x y f y') = (term524 A B y f y').
Proof. exact (MK_COMB (@lem5008349 A B y y' x h1) (@lem5008350 A B f y')). Qed.
Lemma lem5008353 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem5008354 {B : Type'} (t2 : B) (t1 : B) : (@COND B True t1 t2) = t1.
Proof. exact (@lem5008353 B t2 t1). Qed.
Lemma lem5008355 {A B : Type'} (f : A -> B) (y : A) (y' : B) : (term524 A B y' f y) = y'.
Proof. exact (@lem5008354 B (f y) y'). Qed.
Lemma lem5008356 {A B : Type'} (f : A -> B) (y : B) (y' : A) (x : A) (h1 : (y' = x) = True) : (term376 A B x y f y') = y.
Proof. exact (TRANS (@lem5008351 A B y f y' x h1) (@lem5008355 A B f y' y)). Qed.
Lemma lem5008357 {B : Type'} (y : B) : (@eq B y) = (@eq B y).
Proof. exact (eq_refl (@eq B y)). Qed.
Lemma lem5008358 {A B : Type'} (f : A -> B) (y : B) (y' : A) (x : A) (h1 : (y' = x) = True) : (y = (term376 A B x y f y')) = (y = y).
Proof. exact (MK_COMB (@lem5008357 B y) (@lem5008356 A B f y y' x h1)). Qed.
Lemma lem5008360 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5008361 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem5008360 B x). Qed.
Lemma lem5008362 {B : Type'} (y : B) : (y = y) = True.
Proof. exact (@lem5008361 B y). Qed.
Lemma lem5008363 {A B : Type'} (y : B) (f : A -> B) (y' : A) (x : A) (h1 : (y' = x) = True) : (y = (term376 A B x y f y')) = True.
Proof. exact (TRANS (@lem5008358 A B f y y' x h1) (@lem5008362 B y)). Qed.
Lemma lem5008364 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5008365 {A B : Type'} (y : B) (f : A -> B) (y' : A) (x : A) (h1 : (y' = x) = True) : (term525 A B x y f y') = (imp True).
Proof. exact (MK_COMB (@lem5008364) (@lem5008363 A B y f y' x h1)). Qed.
Lemma lem5008368 {A : Type'} (x' : A) (y : A) : (x' = y) = (x' = y).
Proof. exact (eq_refl (x' = y)). Qed.
Lemma lem5008369 {A B : Type'} (y : B) (f : A -> B) (x' : A) (y' : A) (x : A) (h1 : (y' = x) = True) : (term526 A B x y f x' y') = (term554 A x' y').
Proof. exact (MK_COMB (@lem5008365 A B y f y' x h1) (@lem5008368 A x' y')). Qed.
Lemma lem5008371 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem5008372 {A : Type'} (x' : A) (y : A) : (term554 A x' y) = (x' = y).
Proof. exact (@lem5008371 (x' = y)). Qed.
Lemma lem5008375 {A B : Type'} (y : B) (f : A -> B) (x' : A) (y' : A) (x : A) (h1 : (y' = x) = True) : (term526 A B x y f x' y') = (x' = y').
Proof. exact (TRANS (@lem5008369 A B y f x' y' x h1) (@lem5008372 A x' y')). Qed.
Lemma lem5008376 {A B : Type'} (s : A -> Prop) (y : B) (f : A -> B) (x' : A) (y' : A) (x : A) (h1 : (y' = x) = True) : (term527 A B s x y f x' y') = (term554 A x' y').
Proof. exact (MK_COMB (@lem5008343 A s y' x h1) (@lem5008375 A B y f x' y' x h1)). Qed.
Lemma lem5008378 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem5008379 {A : Type'} (x' : A) (y : A) : (term554 A x' y) = (x' = y).
Proof. exact (@lem5008378 (x' = y)). Qed.
Lemma lem5008382 {A B : Type'} (s : A -> Prop) (y : B) (f : A -> B) (x' : A) (y' : A) (x : A) (h1 : (y' = x) = True) : (term527 A B s x y f x' y') = (x' = y').
Proof. exact (TRANS (@lem5008376 A B s y f x' y' x h1) (@lem5008379 A x' y')). Qed.
Lemma lem5008383 {A B : Type'} (s : A -> Prop) (x : A) (y : B) (f : A -> B) (x' : A) (y' : A) : term555 A B s x y f x' y'.
Proof. exact (fun h0 : (y' = x) = True => @lem5008382 A B s y f x' y' x h0). Qed.
Lemma lem5008384 {A B : Type'} (s : A -> Prop) (x : A) (y : B) (f : A -> B) (x' : A) (y' : A) : term556 A B s x y f x' y'.
Proof. exact (conj (@lem5008331 A B x s y f x' y') (@lem5008383 A B s x y f x' y')). Qed.
Lemma lem5008386 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term533 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem5008387 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) (y' : A) : term557 A B x s y f x' y'.
Proof. exact (@lem5008386 (term527 A B s x y f x' y') (x' = y') (y' = x) (term552 A B s y f x' y')). Qed.
Lemma lem5008428 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) (y' : A) : (term527 A B s x y f x' y') = (term558 A B x s y f x' y').
Proof. exact (@lem5008387 A B x s y f x' y' (@lem5008384 A B s x y f x' y')). Qed.
Lemma lem5008429 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term528 A B s x y f x') = (term559 A B x s y f x').
Proof. exact (fun_ext (fun y' : A => @lem5008428 A B x s y f x' y')). Qed.
Lemma lem5008430 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5008431 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term529 A B s x y f x') = (term560 A B x s y f x').
Proof. exact (MK_COMB (@lem5008430 A) (@lem5008429 A B x s y f x')). Qed.
Lemma lem5008436 {A : Type'} (x' : A) (x : A) : (term561 A x' x) = (term561 A x' x).
Proof. exact (eq_refl (term561 A x' x)). Qed.
Lemma lem5008437 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term562 A B s x y f x') = (term563 A B x s y f x').
Proof. exact (MK_COMB (@lem5008436 A x' x) (@lem5008431 A B x s y f x')). Qed.
Lemma lem5008438 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5008439 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term564 A B s x y f x') = (term565 A B x s y f x').
Proof. exact (MK_COMB (@lem5008438) (@lem5008437 A B x s y f x')). Qed.
Lemma lem5008440 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term535 A B s x y f x') = (term566 A B y x s f x').
Proof. exact (MK_COMB (@lem5008439 A B x s y f x') (@lem5008286 A B y x s f x')). Qed.
Lemma lem5008441 {A B : Type'} (s : A -> Prop) (x : A) (y : B) (f : A -> B) (x' : A) : (term567 A B s x y f x') = (term567 A B s x y f x').
Proof. exact (eq_refl (term567 A B s x y f x')). Qed.
Lemma lem5008442 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : ((term421 A B s x y f x') = (term535 A B s x y f x')) = ((term421 A B s x y f x') = (term566 A B y x s f x')).
Proof. exact (MK_COMB (@lem5008441 A B s x y f x') (@lem5008440 A B y x s f x')). Qed.
Lemma lem5008443 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term421 A B s x y f x') = (term566 A B y x s f x').
Proof. exact (EQ_MP (@lem5008442 A B y x s f x') (@lem5008132 A B s x y f x')). Qed.
Lemma lem5008444 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term423 A B s x y f) = (term568 A B y x s f).
Proof. exact (fun_ext (fun x' : A => @lem5008443 A B y x s f x')). Qed.
Lemma lem5008445 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5008446 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term425 A B s x y f) = (term569 A B y x s f).
Proof. exact (MK_COMB (@lem5008445 A) (@lem5008444 A B y x s f)). Qed.
Lemma lem5008451 {B : Type'} (y : B) (x : B) (t : B -> Prop) : (term17 B y x t) = (term17 B y x t).
Proof. exact (eq_refl (term17 B y x t)). Qed.
Lemma lem5008455 {A : Type'} (x' : A) (x : A) (h1 : (x' = x) = False) : (x' = x) = False.
Proof. exact (h1). Qed.
Lemma lem5008456 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem5008457 {A B : Type'} (x' : A) (x : A) (h1 : (x' = x) = False) : (term512 A B x' x) = (@COND B False).
Proof. exact (MK_COMB (@lem5008456 B) (@lem5008455 A x' x h1)). Qed.
Lemma lem5008458 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5008459 {A B : Type'} (y : B) (x' : A) (x : A) (h1 : (x' = x) = False) : (term513 A B x' x y) = (@COND B False y).
Proof. exact (MK_COMB (@lem5008457 A B x' x h1) (@lem5008458 B y)). Qed.
Lemma lem5008460 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (eq_refl (f x')). Qed.
Lemma lem5008461 {A B : Type'} (y : B) (f : A -> B) (x' : A) (x : A) (h1 : (x' = x) = False) : (term376 A B x y f x') = (term514 A B y f x').
Proof. exact (MK_COMB (@lem5008459 A B y x' x h1) (@lem5008460 A B f x')). Qed.
Lemma lem5008463 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem5008464 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem5008463 B t1 t2). Qed.
Lemma lem5008465 {A B : Type'} (y : B) (f : A -> B) (x' : A) : (term514 A B y f x') = (f x').
Proof. exact (@lem5008464 B y (f x')). Qed.
Lemma lem5008466 {A B : Type'} (y : B) (f : A -> B) (x' : A) (x : A) (h1 : (x' = x) = False) : (term376 A B x y f x') = (f x').
Proof. exact (TRANS (@lem5008461 A B y f x' x h1) (@lem5008465 A B y f x')). Qed.
Lemma lem5008467 {B : Type'} (x : B) : (@eq B x) = (@eq B x).
Proof. exact (eq_refl (@eq B x)). Qed.
Lemma lem5008468 {A B : Type'} (y : B) (x : B) (f : A -> B) (x' : A) (x'' : A) (h1 : (x' = x'') = False) : (x = (term376 A B x'' y f x')) = (x = (f x')).
Proof. exact (MK_COMB (@lem5008467 B x) (@lem5008466 A B y f x' x'' h1)). Qed.
Lemma lem5008471 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5008472 {A B : Type'} (y : B) (x : B) (f : A -> B) (x' : A) (x'' : A) (h1 : (x' = x'') = False) : (term391 A B x x'' y f x') = (term570 A B x f x').
Proof. exact (MK_COMB (@lem5008471) (@lem5008468 A B y x f x' x'' h1)). Qed.
Lemma lem5008473 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (@IN A x' s).
Proof. exact (eq_refl (@IN A x' s)). Qed.
Lemma lem5008474 {A B : Type'} (y : B) (x : B) (f : A -> B) (s : A -> Prop) (x' : A) (x'' : A) (h1 : (x' = x'') = False) : (term393 A B x x'' y f x' s) = (term505 A B x f x' s).
Proof. exact (MK_COMB (@lem5008472 A B y x f x' x'' h1) (@lem5008473 A x' s)). Qed.
Lemma lem5008477 {A B : Type'} (x : A) (y : B) (x' : B) (f : A -> B) (x'' : A) (s : A -> Prop) : term571 A B x y x' f x'' s.
Proof. exact (fun h0 : (x'' = x) = False => @lem5008474 A B y x' f s x'' x h0). Qed.
Lemma lem5008479 {A : Type'} (x' : A) (x : A) (h1 : (x' = x) = True) : (x' = x) = True.
Proof. exact (h1). Qed.
Lemma lem5008480 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem5008481 {A B : Type'} (x' : A) (x : A) (h1 : (x' = x) = True) : (term512 A B x' x) = (@COND B True).
Proof. exact (MK_COMB (@lem5008480 B) (@lem5008479 A x' x h1)). Qed.
Lemma lem5008482 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5008483 {A B : Type'} (y : B) (x' : A) (x : A) (h1 : (x' = x) = True) : (term513 A B x' x y) = (@COND B True y).
Proof. exact (MK_COMB (@lem5008481 A B x' x h1) (@lem5008482 B y)). Qed.
Lemma lem5008484 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (eq_refl (f x')). Qed.
Lemma lem5008485 {A B : Type'} (y : B) (f : A -> B) (x' : A) (x : A) (h1 : (x' = x) = True) : (term376 A B x y f x') = (term524 A B y f x').
Proof. exact (MK_COMB (@lem5008483 A B y x' x h1) (@lem5008484 A B f x')). Qed.
Lemma lem5008487 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem5008488 {B : Type'} (t2 : B) (t1 : B) : (@COND B True t1 t2) = t1.
Proof. exact (@lem5008487 B t2 t1). Qed.
Lemma lem5008489 {A B : Type'} (f : A -> B) (x' : A) (y : B) : (term524 A B y f x') = y.
Proof. exact (@lem5008488 B (f x') y). Qed.
Lemma lem5008490 {A B : Type'} (f : A -> B) (y : B) (x' : A) (x : A) (h1 : (x' = x) = True) : (term376 A B x y f x') = y.
Proof. exact (TRANS (@lem5008485 A B y f x' x h1) (@lem5008489 A B f x' y)). Qed.
Lemma lem5008491 {B : Type'} (x : B) : (@eq B x) = (@eq B x).
Proof. exact (eq_refl (@eq B x)). Qed.
Lemma lem5008492 {A B : Type'} (f : A -> B) (x : B) (y : B) (x' : A) (x'' : A) (h1 : (x' = x'') = True) : (x = (term376 A B x'' y f x')) = (x = y).
Proof. exact (MK_COMB (@lem5008491 B x) (@lem5008490 A B f y x' x'' h1)). Qed.
Lemma lem5008495 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5008496 {A B : Type'} (f : A -> B) (x : B) (y : B) (x' : A) (x'' : A) (h1 : (x' = x'') = True) : (term391 A B x x'' y f x') = (term572 B x y).
Proof. exact (MK_COMB (@lem5008495) (@lem5008492 A B f x y x' x'' h1)). Qed.
Lemma lem5008497 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (@IN A x' s).
Proof. exact (eq_refl (@IN A x' s)). Qed.
Lemma lem5008498 {A B : Type'} (f : A -> B) (x : B) (y : B) (s : A -> Prop) (x' : A) (x'' : A) (h1 : (x' = x'') = True) : (term393 A B x x'' y f x' s) = (term573 A B x y x' s).
Proof. exact (MK_COMB (@lem5008496 A B f x y x' x'' h1) (@lem5008497 A x' s)). Qed.
Lemma lem5008501 {A B : Type'} (x : A) (f : A -> B) (x' : B) (y : B) (x'' : A) (s : A -> Prop) : term574 A B x f x' y x'' s.
Proof. exact (fun h0 : (x'' = x) = True => @lem5008498 A B f x' y s x'' x h0). Qed.
Lemma lem5008502 {A B : Type'} (x : A) (f : A -> B) (x' : B) (y : B) (x'' : A) (s : A -> Prop) : term575 A B x f x' y x'' s.
Proof. exact (conj (@lem5008477 A B x y x' f x'' s) (@lem5008501 A B x f x' y x'' s)). Qed.
Lemma lem5008504 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term576 x x1 b x0.
Proof. exact (or_elim (@lem20234 b) (fun h0 : b = True => @lem20421 x x1 x0 b h0) (fun h0 : b = False => @lem20420 x x1 x0 b h0)). Qed.
Lemma lem5008505 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (x'' : A) (s : A -> Prop) : term577 A B y x x' f x'' s.
Proof. exact (@lem5008504 (term393 A B x' x y f x'' s) (term573 A B x' y x'' s) (x'' = x) (term505 A B x' f x'' s)). Qed.
Lemma lem5008546 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (x'' : A) (s : A -> Prop) : (term393 A B x' x y f x'' s) = (term578 A B y x x' f x'' s).
Proof. exact (@lem5008505 A B y x x' f x'' s (@lem5008502 A B x f x' y x'' s)). Qed.
Lemma lem5008547 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (s : A -> Prop) : (term395 A B x' x y f s) = (term579 A B y x x' f s).
Proof. exact (fun_ext (fun x'' : A => @lem5008546 A B y x x' f x'' s)). Qed.
Lemma lem5008548 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5008549 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (s : A -> Prop) : (term396 A B x' x y f s) = (term580 A B y x x' f s).
Proof. exact (MK_COMB (@lem5008548 A) (@lem5008547 A B y x x' f s)). Qed.
Lemma lem5008552 {B : Type'} (x : B) (y : B) : (term384 B x y) = (term384 B x y).
Proof. exact (eq_refl (term384 B x y)). Qed.
Lemma lem5008553 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (s : A -> Prop) : (term397 A B x' x y f s) = (term581 A B y x x' f s).
Proof. exact (MK_COMB (@lem5008552 B x' y) (@lem5008549 A B y x x' f s)). Qed.
Lemma lem5008554 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5008555 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (s : A -> Prop) : (term399 A B x' x y f s) = (term582 A B y x x' f s).
Proof. exact (MK_COMB (@lem5008554) (@lem5008553 A B y x x' f s)). Qed.
Lemma lem5008556 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (y : B) (x' : B) (t : B -> Prop) : (term401 A B x f s y x' t) = (term583 A B x f s y x' t).
Proof. exact (MK_COMB (@lem5008555 A B y x x' f s) (@lem5008451 B y x' t)). Qed.
Lemma lem5008557 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (y : B) (t : B -> Prop) : (term403 A B x f s y t) = (term584 A B x f s y t).
Proof. exact (fun_ext (fun x' : B => @lem5008556 A B x f s y x' t)). Qed.
Lemma lem5008558 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5008559 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (y : B) (t : B -> Prop) : (term404 A B x f s y t) = (term585 A B x f s y t).
Proof. exact (MK_COMB (@lem5008558 B) (@lem5008557 A B x f s y t)). Qed.
Lemma lem5008560 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5008561 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (y : B) (t : B -> Prop) : (term406 A B x f s y t) = (term586 A B x f s y t).
Proof. exact (MK_COMB (@lem5008560) (@lem5008559 A B x f s y t)). Qed.
Lemma lem5008562 {A B : Type'} (t : B -> Prop) (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term427 A B t s x y f) = (term587 A B t y x s f).
Proof. exact (MK_COMB (@lem5008561 A B x f s y t) (@lem5008446 A B y x s f)). Qed.
Lemma lem5008563 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5008564 {A B : Type'} (t : B -> Prop) (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term430 A B t s x y f) = (term588 A B t y x s f).
Proof. exact (MK_COMB (@lem5008563) (@lem5008562 A B t y x s f)). Qed.
Lemma lem5008565 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5008566 {A B : Type'} (t : B -> Prop) (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term451 A B t s x y f) = (term589 A B t y x s f).
Proof. exact (MK_COMB (@lem5008565) (@lem5008564 A B t y x s f)). Qed.
Lemma lem5008567 {A B : Type'} (t : B -> Prop) (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term453 A B t s x y f) = (term590 A B t y x s f).
Proof. exact (MK_COMB (@lem5008566 A B t y x s f) (@lem5007977 A B)). Qed.
Lemma lem5008576 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term64 A B s f x y) = (term64 A B s f x y).
Proof. exact (eq_refl (term64 A B s f x y)). Qed.
Lemma lem5008577 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term111 A B s f x) = (term111 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem5008576 A B s f x y)). Qed.
Lemma lem5008578 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5008579 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term119 A B s f x) = (term119 A B s f x).
Proof. exact (MK_COMB (@lem5008578 A) (@lem5008577 A B s f x)). Qed.
Lemma lem5008582 {A : Type'} (x : A) (s : A -> Prop) : (term65 A x s) = (term65 A x s).
Proof. exact (eq_refl (term65 A x s)). Qed.
Lemma lem5008583 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term120 A B s f x) = (term120 A B s f x).
Proof. exact (MK_COMB (@lem5008582 A x s) (@lem5008579 A B s f x)). Qed.
Lemma lem5008584 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term121 A B s f) = (term121 A B s f).
Proof. exact (fun_ext (fun x : A => @lem5008583 A B s f x)). Qed.
Lemma lem5008585 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5008586 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term122 A B s f) = (term122 A B s f).
Proof. exact (MK_COMB (@lem5008585 A) (@lem5008584 A B s f)). Qed.
Lemma lem5008587 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5008588 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term454 A B s f) = (term454 A B s f).
Proof. exact (MK_COMB (@lem5008587) (@lem5008586 A B s f)). Qed.
Lemma lem5008589 {A B : Type'} (t : B -> Prop) (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term456 A B t s x y f) = (term591 A B t y x s f).
Proof. exact (MK_COMB (@lem5008588 A B s f) (@lem5008567 A B t y x s f)). Qed.
Lemma lem5008592 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term457 A B f s t) = (term457 A B f s t).
Proof. exact (eq_refl (term457 A B f s t)). Qed.
Lemma lem5008593 {A B : Type'} (t : B -> Prop) (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term459 A B t s x y f) = (term592 A B t y x s f).
Proof. exact (MK_COMB (@lem5008592 A B f s t) (@lem5008589 A B t y x s f)). Qed.
Lemma lem5008596 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term81 A B s t) = (term81 A B s t).
Proof. exact (eq_refl (term81 A B s t)). Qed.
Lemma lem5008597 {A B : Type'} (t : B -> Prop) (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term461 A B t s x y f) = (term593 A B t y x s f).
Proof. exact (MK_COMB (@lem5008596 A B s t) (@lem5008593 A B t y x s f)). Qed.
Lemma lem5008600 {B : Type'} (t : B -> Prop) : (term84 B t) = (term84 B t).
Proof. exact (eq_refl (term84 B t)). Qed.
Lemma lem5008601 {A B : Type'} (t : B -> Prop) (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term463 A B t s x y f) = (term594 A B t y x s f).
Proof. exact (MK_COMB (@lem5008600 B t) (@lem5008597 A B t y x s f)). Qed.
Lemma lem5008606 {B : Type'} (y : B) (t : B -> Prop) : (term464 B y t) = (term464 B y t).
Proof. exact (eq_refl (term464 B y t)). Qed.
Lemma lem5008607 {A B : Type'} (t : B -> Prop) (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term466 A B t s x y f) = (term595 A B t y x s f).
Proof. exact (MK_COMB (@lem5008606 B y t) (@lem5008601 A B t y x s f)). Qed.
Lemma lem5008610 {A : Type'} (s : A -> Prop) : (term84 A s) = (term84 A s).
Proof. exact (eq_refl (term84 A s)). Qed.
Lemma lem5008611 {A B : Type'} (t : B -> Prop) (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term468 A B t s x y f) = (term596 A B t y x s f).
Proof. exact (MK_COMB (@lem5008610 A s) (@lem5008607 A B t y x s f)). Qed.
Lemma lem5008616 {A : Type'} (x : A) (s : A -> Prop) : (term464 A x s) = (term464 A x s).
Proof. exact (eq_refl (term464 A x s)). Qed.
Lemma lem5008617 {A B : Type'} (t : B -> Prop) (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term469 A B t s x y f) = (term597 A B t y x s f).
Proof. exact (MK_COMB (@lem5008616 A x s) (@lem5008611 A B t y x s f)). Qed.
Lemma lem5008618 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term471 A B s x y f) = (term598 A B y x s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5008617 A B t y x s f)). Qed.
Lemma lem5008619 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5008620 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term473 A B s x y f) = (term599 A B y x s f).
Proof. exact (MK_COMB (@lem5008619 B) (@lem5008618 A B y x s f)). Qed.
Lemma lem5008621 {A B : Type'} (y : B) (x : A) (f : A -> B) : (term475 A B x y f) = (term600 A B y x f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5008620 A B y x s f)). Qed.
Lemma lem5008622 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5008623 {A B : Type'} (y : B) (x : A) (f : A -> B) : (term477 A B x y f) = (term601 A B y x f).
Proof. exact (MK_COMB (@lem5008622 A) (@lem5008621 A B y x f)). Qed.
Lemma lem5008624 {A B : Type'} (y : B) (f : A -> B) : (term479 A B y f) = (term602 A B y f).
Proof. exact (fun_ext (fun x : A => @lem5008623 A B y x f)). Qed.
Lemma lem5008625 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5008626 {A B : Type'} (y : B) (f : A -> B) : (term481 A B y f) = (term603 A B y f).
Proof. exact (MK_COMB (@lem5008625 A) (@lem5008624 A B y f)). Qed.
Lemma lem5008627 {A B : Type'} (f : A -> B) : (term483 A B f) = (term604 A B f).
Proof. exact (fun_ext (fun y : B => @lem5008626 A B y f)). Qed.
Lemma lem5008628 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5008629 {A B : Type'} (f : A -> B) : (term485 A B f) = (term605 A B f).
Proof. exact (MK_COMB (@lem5008628 B) (@lem5008627 A B f)). Qed.
Lemma lem5008630 {A B : Type'} : (term487 A B) = (term606 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem5008629 A B f)). Qed.
Lemma lem5008631 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5008632 {A B : Type'} : (term489 A B) = (term607 A B).
Proof. exact (MK_COMB (@lem5008631 A B) (@lem5008630 A B)). Qed.
Lemma lem5008903 {A B : Type'} : (term488 A B) = (term607 A B).
Proof. exact (TRANS (@lem5007864 A B) (@lem5008632 A B)). Qed.
Lemma lem5008904 {A B : Type'} : (term607 A B) = (term488 A B).
Proof. exact (SYM (@lem5008903 A B)). Qed.
Lemma lem5008911 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term122 A B s f) : term122 A B s f.
Proof. exact (h1). Qed.
Lemma lem5008912 {A B : Type'} (t : B -> Prop) (y : B) (x : A) (s : A -> Prop) (f : A -> B) (h1 : term588 A B t y x s f) : term588 A B t y x s f.
Proof. exact (h1). Qed.
Lemma lem5008913 {A : Type'} (h1 : term432 A) : term432 A.
Proof. exact (h1). Qed.
Lemma lem5008914 {A B : Type'} (h1 : term433 A B) : term433 A B.
Proof. exact (h1). Qed.
Lemma lem5008915 {B : Type'} (h1 : term432 B) : term432 B.
Proof. exact (h1). Qed.
Lemma lem5008916 {A : Type'} (h1 : term431 A) : term431 A.
Proof. exact (h1). Qed.
Lemma lem5008917 {B : Type'} (h1 : term431 B) : term431 B.
Proof. exact (h1). Qed.
Lemma lem5008935 {B : Type'} (y : B) (t : B -> Prop) (h1 : term238 B y t) : term238 B y t.
Proof. exact (h1). Qed.
Lemma lem5008953 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term364 A B f s t) : term364 A B f s t.
Proof. exact (h1). Qed.
Lemma lem5008962 {A B : Type'} (f : A -> B) (x : A) (y : A) : (term171 A B f x y) = (term608 A B f x y).
Proof. exact (@lem17265 ((f x) = (f y)) (x = y)). Qed.
Lemma lem5008964 {A : Type'} (y : A) (s : A -> Prop) : (term609 A y s) = (term609 A y s).
Proof. exact (eq_refl (term609 A y s)). Qed.
Lemma lem5008965 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term610 A B s f x y) = (term611 A B s f x y).
Proof. exact (MK_COMB (@lem5008964 A y s) (@lem5008962 A B f x y)). Qed.
Lemma lem5008966 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term64 A B s f x y) = (term610 A B s f x y).
Proof. exact (@lem17265 (@IN A y s) (term171 A B f x y)). Qed.
Lemma lem5008967 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term64 A B s f x y) = (term611 A B s f x y).
Proof. exact (TRANS (@lem5008966 A B s f x y) (@lem5008965 A B s f x y)). Qed.
Lemma lem5008968 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term111 A B s f x) = (term612 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem5008967 A B s f x y)). Qed.
Lemma lem5008969 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5008970 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term119 A B s f x) = (term613 A B s f x).
Proof. exact (MK_COMB (@lem5008969 A) (@lem5008968 A B s f x)). Qed.
Lemma lem5008972 {A : Type'} (x : A) (s : A -> Prop) : (term609 A x s) = (term609 A x s).
Proof. exact (eq_refl (term609 A x s)). Qed.
Lemma lem5008973 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term614 A B s f x) = (term615 A B s f x).
Proof. exact (MK_COMB (@lem5008972 A x s) (@lem5008970 A B s f x)). Qed.
Lemma lem5008974 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term120 A B s f x) = (term614 A B s f x).
Proof. exact (@lem17265 (@IN A x s) (term119 A B s f x)). Qed.
Lemma lem5008975 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term120 A B s f x) = (term615 A B s f x).
Proof. exact (TRANS (@lem5008974 A B s f x) (@lem5008973 A B s f x)). Qed.
Lemma lem5008976 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term121 A B s f) = (term616 A B s f).
Proof. exact (fun_ext (fun x : A => @lem5008975 A B s f x)). Qed.
Lemma lem5008977 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5009078 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term122 A B s f) = (term617 A B s f).
Proof. exact (MK_COMB (@lem5008977 A) (@lem5008976 A B s f)). Qed.
Lemma lem5009079 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term122 A B s f) : term617 A B s f.
Proof. exact (EQ_MP (@lem5009078 A B s f) (@lem5008911 A B s f h1)). Qed.
Lemma lem5009101 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (x'' : A) (s : A -> Prop) : (term578 A B y x x' f x'' s) = (term578 A B y x x' f x'' s).
Proof. exact (eq_refl (term578 A B y x x' f x'' s)). Qed.
Lemma lem5009102 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (s : A -> Prop) : (term579 A B y x x' f s) = (term579 A B y x x' f s).
Proof. exact (fun_ext (fun x'' : A => @lem5009101 A B y x x' f x'' s)). Qed.
Lemma lem5009103 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5009104 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (s : A -> Prop) : (term580 A B y x x' f s) = (term580 A B y x x' f s).
Proof. exact (MK_COMB (@lem5009103 A) (@lem5009102 A B y x x' f s)). Qed.
Lemma lem5009106 {B : Type'} (x : B) (y : B) : (term384 B x y) = (term384 B x y).
Proof. exact (eq_refl (term384 B x y)). Qed.
Lemma lem5009107 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (s : A -> Prop) : (term581 A B y x x' f s) = (term581 A B y x x' f s).
Proof. exact (MK_COMB (@lem5009106 B x' y) (@lem5009104 A B y x x' f s)). Qed.
Lemma lem5009114 {B : Type'} (y : B) (x : B) (t : B -> Prop) : (term618 B y x t) = (term619 B y x t).
Proof. exact (@lem17160 (x = y) (@IN B x t)). Qed.
Lemma lem5009115 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5009116 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (s : A -> Prop) : (term620 A B y x x' f s) = (term620 A B y x x' f s).
Proof. exact (MK_COMB (@lem5009115) (@lem5009107 A B y x x' f s)). Qed.
Lemma lem5009117 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (y : B) (x' : B) (t : B -> Prop) : (term621 A B x f s y x' t) = (term622 A B x f s y x' t).
Proof. exact (MK_COMB (@lem5009116 A B y x x' f s) (@lem5009114 B y x' t)). Qed.
Lemma lem5009118 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (y : B) (x' : B) (t : B -> Prop) : (term623 A B x f s y x' t) = (term621 A B x f s y x' t).
Proof. exact (@lem17362 (term581 A B y x x' f s) (term17 B y x' t)). Qed.
Lemma lem5009119 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (y : B) (x' : B) (t : B -> Prop) : (term623 A B x f s y x' t) = (term622 A B x f s y x' t).
Proof. exact (TRANS (@lem5009118 A B x f s y x' t) (@lem5009117 A B x f s y x' t)). Qed.
Lemma lem5009120 {B : Type'} (P : B -> Prop) : (term624 B P) = (term625 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem5009121 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (y : B) (t : B -> Prop) : (term626 A B x f s y t) = (term627 A B x f s y t).
Proof. exact (@lem5009120 B (term584 A B x f s y t)). Qed.
Lemma lem5009122 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (y : B) (x' : B) (t : B -> Prop) : (term628 A B x f s y t x') = (term583 A B x f s y x' t).
Proof. exact (eq_refl (term628 A B x f s y t x')). Qed.
Lemma lem5009123 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5009124 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (y : B) (x' : B) (t : B -> Prop) : (term629 A B x f s y t x') = (term623 A B x f s y x' t).
Proof. exact (MK_COMB (@lem5009123) (@lem5009122 A B x f s y x' t)). Qed.
Lemma lem5009125 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (y : B) (x' : B) (t : B -> Prop) : (term629 A B x f s y t x') = (term622 A B x f s y x' t).
Proof. exact (TRANS (@lem5009124 A B x f s y x' t) (@lem5009119 A B x f s y x' t)). Qed.
Lemma lem5009126 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (y : B) (t : B -> Prop) : (term630 A B x f s y t) = (term631 A B x f s y t).
Proof. exact (fun_ext (fun x' : B => @lem5009125 A B x f s y x' t)). Qed.
Lemma lem5009127 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5009128 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (y : B) (t : B -> Prop) : (term627 A B x f s y t) = (term632 A B x f s y t).
Proof. exact (MK_COMB (@lem5009127 B) (@lem5009126 A B x f s y t)). Qed.
Lemma lem5009129 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (y : B) (t : B -> Prop) : (term626 A B x f s y t) = (term632 A B x f s y t).
Proof. exact (TRANS (@lem5009121 A B x f s y t) (@lem5009128 A B x f s y t)). Qed.
Lemma lem5009132 {A : Type'} (x' : A) (x : A) : (term633 A x' x) = (x' = x).
Proof. exact (@lem16933 (x' = x)). Qed.
Lemma lem5009135 {A : Type'} (y : A) (x : A) : (term633 A y x) = (y = x).
Proof. exact (@lem16933 (y = x)). Qed.
Lemma lem5009136 {A : Type'} (x' : A) (y : A) : (term634 A x' y) = (term634 A x' y).
Proof. exact (eq_refl (term634 A x' y)). Qed.
Lemma lem5009137 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5009138 {A : Type'} (y : A) (x : A) : (term635 A y x) = (term572 A y x).
Proof. exact (MK_COMB (@lem5009137) (@lem5009135 A y x)). Qed.
Lemma lem5009139 {A : Type'} (x : A) (x' : A) (y : A) : (term636 A x x' y) = (term637 A x x' y).
Proof. exact (MK_COMB (@lem5009138 A y x) (@lem5009136 A x' y)). Qed.
Lemma lem5009140 {A : Type'} (x : A) (x' : A) (y : A) : (term638 A x x' y) = (term636 A x x' y).
Proof. exact (@lem17160 (term634 A y x) (x' = y)). Qed.
Lemma lem5009141 {A : Type'} (x : A) (x' : A) (y : A) : (term638 A x x' y) = (term637 A x x' y).
Proof. exact (TRANS (@lem5009140 A x x' y) (@lem5009139 A x x' y)). Qed.
Lemma lem5009150 {A B : Type'} (y : B) (f : A -> B) (x' : A) (y' : A) : (term639 A B y f x' y') = (term640 A B y f x' y').
Proof. exact (@lem17362 (y = (f y')) (x' = y')). Qed.
Lemma lem5009152 {A : Type'} (y : A) (s : A -> Prop) : (term641 A y s) = (term641 A y s).
Proof. exact (eq_refl (term641 A y s)). Qed.
Lemma lem5009153 {A B : Type'} (s : A -> Prop) (y : B) (f : A -> B) (x' : A) (y' : A) : (term642 A B s y f x' y') = (term643 A B s y f x' y').
Proof. exact (MK_COMB (@lem5009152 A y' s) (@lem5009150 A B y f x' y')). Qed.
Lemma lem5009154 {A B : Type'} (s : A -> Prop) (y : B) (f : A -> B) (x' : A) (y' : A) : (term644 A B s y f x' y') = (term642 A B s y f x' y').
Proof. exact (@lem17362 (@IN A y' s) (term551 A B y f x' y')). Qed.
Lemma lem5009155 {A B : Type'} (s : A -> Prop) (y : B) (f : A -> B) (x' : A) (y' : A) : (term644 A B s y f x' y') = (term643 A B s y f x' y').
Proof. exact (TRANS (@lem5009154 A B s y f x' y') (@lem5009153 A B s y f x' y')). Qed.
Lemma lem5009157 {A : Type'} (y : A) (x : A) : (term645 A y x) = (term645 A y x).
Proof. exact (eq_refl (term645 A y x)). Qed.
Lemma lem5009158 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) (y' : A) : (term646 A B x s y f x' y') = (term647 A B x s y f x' y').
Proof. exact (MK_COMB (@lem5009157 A y' x) (@lem5009155 A B s y f x' y')). Qed.
Lemma lem5009159 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) (y' : A) : (term648 A B x s y f x' y') = (term646 A B x s y f x' y').
Proof. exact (@lem17160 (y' = x) (term552 A B s y f x' y')). Qed.
Lemma lem5009160 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) (y' : A) : (term648 A B x s y f x' y') = (term647 A B x s y f x' y').
Proof. exact (TRANS (@lem5009159 A B x s y f x' y') (@lem5009158 A B x s y f x' y')). Qed.
Lemma lem5009161 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5009162 {A : Type'} (x : A) (x' : A) (y : A) : (term649 A x x' y) = (term650 A x x' y).
Proof. exact (MK_COMB (@lem5009161) (@lem5009141 A x x' y)). Qed.
Lemma lem5009163 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) (y' : A) : (term651 A B x s y f x' y') = (term652 A B x s y f x' y').
Proof. exact (MK_COMB (@lem5009162 A x x' y') (@lem5009160 A B x s y f x' y')). Qed.
Lemma lem5009164 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) (y' : A) : (term653 A B x s y f x' y') = (term651 A B x s y f x' y').
Proof. exact (@lem17045 (term654 A x x' y') (term655 A B x s y f x' y')). Qed.
Lemma lem5009165 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) (y' : A) : (term653 A B x s y f x' y') = (term652 A B x s y f x' y').
Proof. exact (TRANS (@lem5009164 A B x s y f x' y') (@lem5009163 A B x s y f x' y')). Qed.
Lemma lem5009166 {A : Type'} (P : A -> Prop) : (term624 A P) = (term625 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem5009167 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term656 A B x s y f x') = (term657 A B x s y f x').
Proof. exact (@lem5009166 A (term559 A B x s y f x')). Qed.
Lemma lem5009168 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) (y' : A) : (term658 A B x s y f x' y') = (term558 A B x s y f x' y').
Proof. exact (eq_refl (term658 A B x s y f x' y')). Qed.
Lemma lem5009169 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5009170 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) (y' : A) : (term659 A B x s y f x' y') = (term653 A B x s y f x' y').
Proof. exact (MK_COMB (@lem5009169) (@lem5009168 A B x s y f x' y')). Qed.
Lemma lem5009171 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) (y' : A) : (term659 A B x s y f x' y') = (term652 A B x s y f x' y').
Proof. exact (TRANS (@lem5009170 A B x s y f x' y') (@lem5009165 A B x s y f x' y')). Qed.
Lemma lem5009172 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term660 A B x s y f x') = (term661 A B x s y f x').
Proof. exact (fun_ext (fun y' : A => @lem5009171 A B x s y f x' y')). Qed.
Lemma lem5009173 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5009174 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term657 A B x s y f x') = (term662 A B x s y f x').
Proof. exact (MK_COMB (@lem5009173 A) (@lem5009172 A B x s y f x')). Qed.
Lemma lem5009175 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term656 A B x s y f x') = (term662 A B x s y f x').
Proof. exact (TRANS (@lem5009167 A B x s y f x') (@lem5009174 A B x s y f x')). Qed.
Lemma lem5009176 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5009177 {A : Type'} (x' : A) (x : A) : (term635 A x' x) = (term572 A x' x).
Proof. exact (MK_COMB (@lem5009176) (@lem5009132 A x' x)). Qed.
Lemma lem5009178 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term663 A B x s y f x') = (term664 A B x s y f x').
Proof. exact (MK_COMB (@lem5009177 A x' x) (@lem5009175 A B x s y f x')). Qed.
Lemma lem5009179 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term665 A B x s y f x') = (term663 A B x s y f x').
Proof. exact (@lem17160 (term634 A x' x) (term560 A B x s y f x')). Qed.
Lemma lem5009180 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term665 A B x s y f x') = (term664 A B x s y f x').
Proof. exact (TRANS (@lem5009179 A B x s y f x') (@lem5009178 A B x s y f x')). Qed.
Lemma lem5009185 {A : Type'} (y : A) (x : A) : (term633 A y x) = (y = x).
Proof. exact (@lem16933 (y = x)). Qed.
Lemma lem5009192 {A B : Type'} (f : A -> B) (y : B) (x' : A) (y' : A) : (term666 A B f y x' y') = (term667 A B f y x' y').
Proof. exact (@lem17362 ((f x') = y) (x' = y')). Qed.
Lemma lem5009193 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5009194 {A : Type'} (y : A) (x : A) : (term635 A y x) = (term572 A y x).
Proof. exact (MK_COMB (@lem5009193) (@lem5009185 A y x)). Qed.
Lemma lem5009195 {A B : Type'} (x : A) (f : A -> B) (y : B) (x' : A) (y' : A) : (term668 A B x f y x' y') = (term669 A B x f y x' y').
Proof. exact (MK_COMB (@lem5009194 A y' x) (@lem5009192 A B f y x' y')). Qed.
Lemma lem5009196 {A B : Type'} (x : A) (f : A -> B) (y : B) (x' : A) (y' : A) : (term670 A B x f y x' y') = (term668 A B x f y x' y').
Proof. exact (@lem17160 (term634 A y' x) (term539 A B f y x' y')). Qed.
Lemma lem5009197 {A B : Type'} (x : A) (f : A -> B) (y : B) (x' : A) (y' : A) : (term670 A B x f y x' y') = (term669 A B x f y x' y').
Proof. exact (TRANS (@lem5009196 A B x f y x' y') (@lem5009195 A B x f y x' y')). Qed.
Lemma lem5009206 {A B : Type'} (f : A -> B) (x' : A) (y : A) : (term671 A B f x' y) = (term672 A B f x' y).
Proof. exact (@lem17362 ((f x') = (f y)) (x' = y)). Qed.
Lemma lem5009208 {A : Type'} (y : A) (s : A -> Prop) : (term641 A y s) = (term641 A y s).
Proof. exact (eq_refl (term641 A y s)). Qed.
Lemma lem5009209 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (y : A) : (term673 A B s f x' y) = (term674 A B s f x' y).
Proof. exact (MK_COMB (@lem5009208 A y s) (@lem5009206 A B f x' y)). Qed.
Lemma lem5009210 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (y : A) : (term675 A B s f x' y) = (term673 A B s f x' y).
Proof. exact (@lem17362 (@IN A y s) (term171 A B f x' y)). Qed.
Lemma lem5009211 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (y : A) : (term675 A B s f x' y) = (term674 A B s f x' y).
Proof. exact (TRANS (@lem5009210 A B s f x' y) (@lem5009209 A B s f x' y)). Qed.
Lemma lem5009213 {A : Type'} (y : A) (x : A) : (term645 A y x) = (term645 A y x).
Proof. exact (eq_refl (term645 A y x)). Qed.
Lemma lem5009214 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (x' : A) (y : A) : (term676 A B x s f x' y) = (term677 A B x s f x' y).
Proof. exact (MK_COMB (@lem5009213 A y x) (@lem5009211 A B s f x' y)). Qed.
Lemma lem5009215 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (x' : A) (y : A) : (term678 A B x s f x' y) = (term676 A B x s f x' y).
Proof. exact (@lem17160 (y = x) (term64 A B s f x' y)). Qed.
Lemma lem5009216 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (x' : A) (y : A) : (term678 A B x s f x' y) = (term677 A B x s f x' y).
Proof. exact (TRANS (@lem5009215 A B x s f x' y) (@lem5009214 A B x s f x' y)). Qed.
Lemma lem5009217 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5009218 {A B : Type'} (x : A) (f : A -> B) (y : B) (x' : A) (y' : A) : (term679 A B x f y x' y') = (term680 A B x f y x' y').
Proof. exact (MK_COMB (@lem5009217) (@lem5009197 A B x f y x' y')). Qed.
Lemma lem5009219 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) (y' : A) : (term681 A B y x s f x' y') = (term682 A B y x s f x' y').
Proof. exact (MK_COMB (@lem5009218 A B x f y x' y') (@lem5009216 A B x s f x' y')). Qed.
Lemma lem5009220 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) (y' : A) : (term683 A B y x s f x' y') = (term681 A B y x s f x' y').
Proof. exact (@lem17045 (term684 A B x f y x' y') (term685 A B x s f x' y')). Qed.
Lemma lem5009221 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) (y' : A) : (term683 A B y x s f x' y') = (term682 A B y x s f x' y').
Proof. exact (TRANS (@lem5009220 A B y x s f x' y') (@lem5009219 A B y x s f x' y')). Qed.
Lemma lem5009222 {A : Type'} (P : A -> Prop) : (term624 A P) = (term625 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem5009223 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term686 A B y x s f x') = (term687 A B y x s f x').
Proof. exact (@lem5009222 A (term545 A B y x s f x')). Qed.
Lemma lem5009224 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) (y' : A) : (term688 A B y x s f x' y') = (term544 A B y x s f x' y').
Proof. exact (eq_refl (term688 A B y x s f x' y')). Qed.
Lemma lem5009225 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5009226 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) (y' : A) : (term689 A B y x s f x' y') = (term683 A B y x s f x' y').
Proof. exact (MK_COMB (@lem5009225) (@lem5009224 A B y x s f x' y')). Qed.
Lemma lem5009227 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) (y' : A) : (term689 A B y x s f x' y') = (term682 A B y x s f x' y').
Proof. exact (TRANS (@lem5009226 A B y x s f x' y') (@lem5009221 A B y x s f x' y')). Qed.
Lemma lem5009228 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term690 A B y x s f x') = (term691 A B y x s f x').
Proof. exact (fun_ext (fun y' : A => @lem5009227 A B y x s f x' y')). Qed.
Lemma lem5009229 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5009230 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term687 A B y x s f x') = (term692 A B y x s f x').
Proof. exact (MK_COMB (@lem5009229 A) (@lem5009228 A B y x s f x')). Qed.
Lemma lem5009231 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term686 A B y x s f x') = (term692 A B y x s f x').
Proof. exact (TRANS (@lem5009223 A B y x s f x') (@lem5009230 A B y x s f x')). Qed.
Lemma lem5009233 {A : Type'} (x' : A) (s : A -> Prop) : (term641 A x' s) = (term641 A x' s).
Proof. exact (eq_refl (term641 A x' s)). Qed.
Lemma lem5009234 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term693 A B y x s f x') = (term694 A B y x s f x').
Proof. exact (MK_COMB (@lem5009233 A x' s) (@lem5009231 A B y x s f x')). Qed.
Lemma lem5009235 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term695 A B y x s f x') = (term693 A B y x s f x').
Proof. exact (@lem17362 (@IN A x' s) (term546 A B y x s f x')). Qed.
Lemma lem5009236 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term695 A B y x s f x') = (term694 A B y x s f x').
Proof. exact (TRANS (@lem5009235 A B y x s f x') (@lem5009234 A B y x s f x')). Qed.
Lemma lem5009238 {A : Type'} (x' : A) (x : A) : (term645 A x' x) = (term645 A x' x).
Proof. exact (eq_refl (term645 A x' x)). Qed.
Lemma lem5009239 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term696 A B y x s f x') = (term697 A B y x s f x').
Proof. exact (MK_COMB (@lem5009238 A x' x) (@lem5009236 A B y x s f x')). Qed.
Lemma lem5009240 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term698 A B y x s f x') = (term696 A B y x s f x').
Proof. exact (@lem17160 (x' = x) (term547 A B y x s f x')). Qed.
Lemma lem5009241 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term698 A B y x s f x') = (term697 A B y x s f x').
Proof. exact (TRANS (@lem5009240 A B y x s f x') (@lem5009239 A B y x s f x')). Qed.
Lemma lem5009242 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5009243 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term699 A B x s y f x') = (term700 A B x s y f x').
Proof. exact (MK_COMB (@lem5009242) (@lem5009180 A B x s y f x')). Qed.
Lemma lem5009244 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term701 A B y x s f x') = (term702 A B y x s f x').
Proof. exact (MK_COMB (@lem5009243 A B x s y f x') (@lem5009241 A B y x s f x')). Qed.
Lemma lem5009245 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term703 A B y x s f x') = (term701 A B y x s f x').
Proof. exact (@lem17045 (term563 A B x s y f x') (term549 A B y x s f x')). Qed.
Lemma lem5009246 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term703 A B y x s f x') = (term702 A B y x s f x').
Proof. exact (TRANS (@lem5009245 A B y x s f x') (@lem5009244 A B y x s f x')). Qed.
Lemma lem5009247 {A : Type'} (P : A -> Prop) : (term624 A P) = (term625 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem5009248 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term704 A B y x s f) = (term705 A B y x s f).
Proof. exact (@lem5009247 A (term568 A B y x s f)). Qed.
Lemma lem5009249 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term706 A B y x s f x') = (term566 A B y x s f x').
Proof. exact (eq_refl (term706 A B y x s f x')). Qed.
Lemma lem5009250 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5009251 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term707 A B y x s f x') = (term703 A B y x s f x').
Proof. exact (MK_COMB (@lem5009250) (@lem5009249 A B y x s f x')). Qed.
Lemma lem5009252 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term707 A B y x s f x') = (term702 A B y x s f x').
Proof. exact (TRANS (@lem5009251 A B y x s f x') (@lem5009246 A B y x s f x')). Qed.
Lemma lem5009253 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term708 A B y x s f) = (term709 A B y x s f).
Proof. exact (fun_ext (fun x' : A => @lem5009252 A B y x s f x')). Qed.
Lemma lem5009254 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5009255 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term705 A B y x s f) = (term710 A B y x s f).
Proof. exact (MK_COMB (@lem5009254 A) (@lem5009253 A B y x s f)). Qed.
Lemma lem5009256 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term704 A B y x s f) = (term710 A B y x s f).
Proof. exact (TRANS (@lem5009248 A B y x s f) (@lem5009255 A B y x s f)). Qed.
Lemma lem5009257 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5009258 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (y : B) (t : B -> Prop) : (term711 A B x f s y t) = (term712 A B x f s y t).
Proof. exact (MK_COMB (@lem5009257) (@lem5009129 A B x f s y t)). Qed.
Lemma lem5009259 {A B : Type'} (t : B -> Prop) (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term713 A B t y x s f) = (term714 A B t y x s f).
Proof. exact (MK_COMB (@lem5009258 A B x f s y t) (@lem5009256 A B y x s f)). Qed.
Lemma lem5009260 {A B : Type'} (t : B -> Prop) (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term588 A B t y x s f) = (term713 A B t y x s f).
Proof. exact (@lem17045 (term585 A B x f s y t) (term569 A B y x s f)). Qed.
Lemma lem5009261 {A B : Type'} (t : B -> Prop) (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term588 A B t y x s f) = (term714 A B t y x s f).
Proof. exact (TRANS (@lem5009260 A B t y x s f) (@lem5009259 A B t y x s f)). Qed.
Lemma lem5009311 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term715 A P Q) = (term716 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem5009312 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term715 A P Q) = (term716 A P Q).
Proof. exact (@lem5009311 A P Q). Qed.
Lemma lem5009313 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (s : A -> Prop) : (term717 A B y x x' f s) = (term718 A B y x x' f s).
Proof. exact (@lem5009312 A (term719 A B x x' y s) (term720 A B x x' f s)). Qed.
Lemma lem5009314 {A B : Type'} (x : A) (x' : B) (y : B) (x'' : A) (s : A -> Prop) : (term721 A B x x' y s x'') = (term722 A B x x' y x'' s).
Proof. exact (eq_refl (term721 A B x x' y s x'')). Qed.
Lemma lem5009315 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5009316 {A B : Type'} (x : A) (x' : B) (y : B) (x'' : A) (s : A -> Prop) : (term723 A B x x' y s x'') = (term724 A B x x' y x'' s).
Proof. exact (MK_COMB (@lem5009315) (@lem5009314 A B x x' y x'' s)). Qed.
Lemma lem5009317 {A B : Type'} (x : A) (x' : B) (f : A -> B) (x'' : A) (s : A -> Prop) : (term725 A B x x' f s x'') = (term726 A B x x' f x'' s).
Proof. exact (eq_refl (term725 A B x x' f s x'')). Qed.
Lemma lem5009318 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (x'' : A) (s : A -> Prop) : (term727 A B y x x' f s x'') = (term578 A B y x x' f x'' s).
Proof. exact (MK_COMB (@lem5009316 A B x x' y x'' s) (@lem5009317 A B x x' f x'' s)). Qed.
Lemma lem5009319 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (s : A -> Prop) : (term728 A B y x x' f s) = (term579 A B y x x' f s).
Proof. exact (fun_ext (fun x'' : A => @lem5009318 A B y x x' f x'' s)). Qed.
Lemma lem5009320 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5009321 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (s : A -> Prop) : (term717 A B y x x' f s) = (term580 A B y x x' f s).
Proof. exact (MK_COMB (@lem5009320 A) (@lem5009319 A B y x x' f s)). Qed.
Lemma lem5009322 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5009323 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (s : A -> Prop) : (term729 A B y x x' f s) = (term730 A B y x x' f s).
Proof. exact (MK_COMB (@lem5009322) (@lem5009321 A B y x x' f s)). Qed.
Lemma lem5009324 {A B : Type'} (x : A) (x' : B) (y : B) (x'' : A) (s : A -> Prop) : (term721 A B x x' y s x'') = (term722 A B x x' y x'' s).
Proof. exact (eq_refl (term721 A B x x' y s x'')). Qed.
Lemma lem5009325 {A B : Type'} (x : A) (x' : B) (y : B) (s : A -> Prop) : (term731 A B x x' y s) = (term719 A B x x' y s).
Proof. exact (fun_ext (fun x'' : A => @lem5009324 A B x x' y x'' s)). Qed.
Lemma lem5009326 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5009327 {A B : Type'} (x : A) (x' : B) (y : B) (s : A -> Prop) : (term732 A B x x' y s) = (term733 A B x x' y s).
Proof. exact (MK_COMB (@lem5009326 A) (@lem5009325 A B x x' y s)). Qed.
Lemma lem5009328 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5009329 {A B : Type'} (x : A) (x' : B) (y : B) (s : A -> Prop) : (term734 A B x x' y s) = (term735 A B x x' y s).
Proof. exact (MK_COMB (@lem5009328) (@lem5009327 A B x x' y s)). Qed.
Lemma lem5009330 {A B : Type'} (x : A) (x' : B) (f : A -> B) (x'' : A) (s : A -> Prop) : (term725 A B x x' f s x'') = (term726 A B x x' f x'' s).
Proof. exact (eq_refl (term725 A B x x' f s x'')). Qed.
Lemma lem5009331 {A B : Type'} (x : A) (x' : B) (f : A -> B) (s : A -> Prop) : (term736 A B x x' f s) = (term720 A B x x' f s).
Proof. exact (fun_ext (fun x'' : A => @lem5009330 A B x x' f x'' s)). Qed.
Lemma lem5009332 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5009333 {A B : Type'} (x : A) (x' : B) (f : A -> B) (s : A -> Prop) : (term737 A B x x' f s) = (term738 A B x x' f s).
Proof. exact (MK_COMB (@lem5009332 A) (@lem5009331 A B x x' f s)). Qed.
Lemma lem5009334 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (s : A -> Prop) : (term718 A B y x x' f s) = (term739 A B y x x' f s).
Proof. exact (MK_COMB (@lem5009329 A B x x' y s) (@lem5009333 A B x x' f s)). Qed.
Lemma lem5009335 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (s : A -> Prop) : ((term717 A B y x x' f s) = (term718 A B y x x' f s)) = ((term580 A B y x x' f s) = (term739 A B y x x' f s)).
Proof. exact (MK_COMB (@lem5009323 A B y x x' f s) (@lem5009334 A B y x x' f s)). Qed.
Lemma lem5009336 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (s : A -> Prop) : (term580 A B y x x' f s) = (term739 A B y x x' f s).
Proof. exact (EQ_MP (@lem5009335 A B y x x' f s) (@lem5009313 A B y x x' f s)). Qed.
Lemma lem5009433 {B : Type'} (x : B) (y : B) : (term384 B x y) = (term384 B x y).
Proof. exact (eq_refl (term384 B x y)). Qed.
Lemma lem5009434 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (s : A -> Prop) : (term581 A B y x x' f s) = (term740 A B y x x' f s).
Proof. exact (MK_COMB (@lem5009433 B x' y) (@lem5009336 A B y x x' f s)). Qed.
Lemma lem5009435 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5009436 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (s : A -> Prop) : (term620 A B y x x' f s) = (term741 A B y x x' f s).
Proof. exact (MK_COMB (@lem5009435) (@lem5009434 A B y x x' f s)). Qed.
Lemma lem5009437 {B : Type'} (y : B) (x : B) (t : B -> Prop) : (term619 B y x t) = (term619 B y x t).
Proof. exact (eq_refl (term619 B y x t)). Qed.
Lemma lem5009438 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (y : B) (x' : B) (t : B -> Prop) : (term622 A B x f s y x' t) = (term742 A B x f s y x' t).
Proof. exact (MK_COMB (@lem5009436 A B y x x' f s) (@lem5009437 B y x' t)). Qed.
Lemma lem5009439 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (y : B) (t : B -> Prop) : (term631 A B x f s y t) = (term743 A B x f s y t).
Proof. exact (fun_ext (fun x' : B => @lem5009438 A B x f s y x' t)). Qed.
Lemma lem5009440 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5009441 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (y : B) (t : B -> Prop) : (term632 A B x f s y t) = (term744 A B x f s y t).
Proof. exact (MK_COMB (@lem5009440 B) (@lem5009439 A B x f s y t)). Qed.
Lemma lem5009490 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5009491 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (y : B) (t : B -> Prop) : (term712 A B x f s y t) = (term745 A B x f s y t).
Proof. exact (MK_COMB (@lem5009490) (@lem5009441 A B x f s y t)). Qed.
Lemma lem5009493 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term715 A P Q) = (term716 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem5009494 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term715 A P Q) = (term716 A P Q).
Proof. exact (@lem5009493 A P Q). Qed.
Lemma lem5009495 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term746 A B y x s f) = (term747 A B y x s f).
Proof. exact (@lem5009494 A (term748 A B x s y f) (term749 A B y x s f)). Qed.
Lemma lem5009496 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term750 A B x s y f x') = (term664 A B x s y f x').
Proof. exact (eq_refl (term750 A B x s y f x')). Qed.
Lemma lem5009497 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5009498 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term751 A B x s y f x') = (term700 A B x s y f x').
Proof. exact (MK_COMB (@lem5009497) (@lem5009496 A B x s y f x')). Qed.
Lemma lem5009499 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term752 A B y x s f x') = (term697 A B y x s f x').
Proof. exact (eq_refl (term752 A B y x s f x')). Qed.
Lemma lem5009500 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term753 A B y x s f x') = (term702 A B y x s f x').
Proof. exact (MK_COMB (@lem5009498 A B x s y f x') (@lem5009499 A B y x s f x')). Qed.
Lemma lem5009501 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term754 A B y x s f) = (term709 A B y x s f).
Proof. exact (fun_ext (fun x' : A => @lem5009500 A B y x s f x')). Qed.
Lemma lem5009502 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5009503 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term746 A B y x s f) = (term710 A B y x s f).
Proof. exact (MK_COMB (@lem5009502 A) (@lem5009501 A B y x s f)). Qed.
Lemma lem5009504 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5009505 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term755 A B y x s f) = (term756 A B y x s f).
Proof. exact (MK_COMB (@lem5009504) (@lem5009503 A B y x s f)). Qed.
Lemma lem5009506 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term750 A B x s y f x') = (term664 A B x s y f x').
Proof. exact (eq_refl (term750 A B x s y f x')). Qed.
Lemma lem5009507 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) : (term757 A B x s y f) = (term748 A B x s y f).
Proof. exact (fun_ext (fun x' : A => @lem5009506 A B x s y f x')). Qed.
Lemma lem5009508 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5009509 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) : (term758 A B x s y f) = (term759 A B x s y f).
Proof. exact (MK_COMB (@lem5009508 A) (@lem5009507 A B x s y f)). Qed.
Lemma lem5009510 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5009511 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) : (term760 A B x s y f) = (term761 A B x s y f).
Proof. exact (MK_COMB (@lem5009510) (@lem5009509 A B x s y f)). Qed.
Lemma lem5009512 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term752 A B y x s f x') = (term697 A B y x s f x').
Proof. exact (eq_refl (term752 A B y x s f x')). Qed.
Lemma lem5009513 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term762 A B y x s f) = (term749 A B y x s f).
Proof. exact (fun_ext (fun x' : A => @lem5009512 A B y x s f x')). Qed.
Lemma lem5009514 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5009515 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term763 A B y x s f) = (term764 A B y x s f).
Proof. exact (MK_COMB (@lem5009514 A) (@lem5009513 A B y x s f)). Qed.
Lemma lem5009516 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term747 A B y x s f) = (term765 A B y x s f).
Proof. exact (MK_COMB (@lem5009511 A B x s y f) (@lem5009515 A B y x s f)). Qed.
Lemma lem5009517 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) : ((term746 A B y x s f) = (term747 A B y x s f)) = ((term710 A B y x s f) = (term765 A B y x s f)).
Proof. exact (MK_COMB (@lem5009505 A B y x s f) (@lem5009516 A B y x s f)). Qed.
Lemma lem5009518 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term710 A B y x s f) = (term765 A B y x s f).
Proof. exact (EQ_MP (@lem5009517 A B y x s f) (@lem5009495 A B y x s f)). Qed.
Lemma lem5009568 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term715 A P Q) = (term716 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem5009569 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term715 A P Q) = (term716 A P Q).
Proof. exact (@lem5009568 A P Q). Qed.
Lemma lem5009570 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term766 A B x s y f x') = (term767 A B x s y f x').
Proof. exact (@lem5009569 A (term768 A x x') (term769 A B x s y f x')). Qed.
Lemma lem5009571 {A : Type'} (x : A) (x' : A) (y : A) : (term770 A x x' y) = (term637 A x x' y).
Proof. exact (eq_refl (term770 A x x' y)). Qed.
Lemma lem5009572 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5009573 {A : Type'} (x : A) (x' : A) (y : A) : (term771 A x x' y) = (term650 A x x' y).
Proof. exact (MK_COMB (@lem5009572) (@lem5009571 A x x' y)). Qed.
Lemma lem5009574 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) (y' : A) : (term772 A B x s y f x' y') = (term647 A B x s y f x' y').
Proof. exact (eq_refl (term772 A B x s y f x' y')). Qed.
Lemma lem5009575 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) (y' : A) : (term773 A B x s y f x' y') = (term652 A B x s y f x' y').
Proof. exact (MK_COMB (@lem5009573 A x x' y') (@lem5009574 A B x s y f x' y')). Qed.
Lemma lem5009576 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term774 A B x s y f x') = (term661 A B x s y f x').
Proof. exact (fun_ext (fun y' : A => @lem5009575 A B x s y f x' y')). Qed.
Lemma lem5009577 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5009578 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term766 A B x s y f x') = (term662 A B x s y f x').
Proof. exact (MK_COMB (@lem5009577 A) (@lem5009576 A B x s y f x')). Qed.
Lemma lem5009579 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5009580 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term775 A B x s y f x') = (term776 A B x s y f x').
Proof. exact (MK_COMB (@lem5009579) (@lem5009578 A B x s y f x')). Qed.
Lemma lem5009581 {A : Type'} (x : A) (x' : A) (y : A) : (term770 A x x' y) = (term637 A x x' y).
Proof. exact (eq_refl (term770 A x x' y)). Qed.
Lemma lem5009582 {A : Type'} (x : A) (x' : A) : (term777 A x x') = (term768 A x x').
Proof. exact (fun_ext (fun y : A => @lem5009581 A x x' y)). Qed.
Lemma lem5009583 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5009584 {A : Type'} (x : A) (x' : A) : (term778 A x x') = (term779 A x x').
Proof. exact (MK_COMB (@lem5009583 A) (@lem5009582 A x x')). Qed.
Lemma lem5009585 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5009586 {A : Type'} (x : A) (x' : A) : (term780 A x x') = (term781 A x x').
Proof. exact (MK_COMB (@lem5009585) (@lem5009584 A x x')). Qed.
Lemma lem5009587 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) (y' : A) : (term772 A B x s y f x' y') = (term647 A B x s y f x' y').
Proof. exact (eq_refl (term772 A B x s y f x' y')). Qed.
Lemma lem5009588 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term782 A B x s y f x') = (term769 A B x s y f x').
Proof. exact (fun_ext (fun y' : A => @lem5009587 A B x s y f x' y')). Qed.
Lemma lem5009589 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5009590 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term783 A B x s y f x') = (term784 A B x s y f x').
Proof. exact (MK_COMB (@lem5009589 A) (@lem5009588 A B x s y f x')). Qed.
Lemma lem5009591 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term767 A B x s y f x') = (term785 A B x s y f x').
Proof. exact (MK_COMB (@lem5009586 A x x') (@lem5009590 A B x s y f x')). Qed.
Lemma lem5009592 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : ((term766 A B x s y f x') = (term767 A B x s y f x')) = ((term662 A B x s y f x') = (term785 A B x s y f x')).
Proof. exact (MK_COMB (@lem5009580 A B x s y f x') (@lem5009591 A B x s y f x')). Qed.
Lemma lem5009593 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term662 A B x s y f x') = (term785 A B x s y f x').
Proof. exact (EQ_MP (@lem5009592 A B x s y f x') (@lem5009570 A B x s y f x')). Qed.
Lemma lem5009690 {A : Type'} (x' : A) (x : A) : (term572 A x' x) = (term572 A x' x).
Proof. exact (eq_refl (term572 A x' x)). Qed.
Lemma lem5009691 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term664 A B x s y f x') = (term786 A B x s y f x').
Proof. exact (MK_COMB (@lem5009690 A x' x) (@lem5009593 A B x s y f x')). Qed.
Lemma lem5009692 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) : (term748 A B x s y f) = (term787 A B x s y f).
Proof. exact (fun_ext (fun x' : A => @lem5009691 A B x s y f x')). Qed.
Lemma lem5009693 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5009694 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) : (term759 A B x s y f) = (term788 A B x s y f).
Proof. exact (MK_COMB (@lem5009693 A) (@lem5009692 A B x s y f)). Qed.
Lemma lem5009743 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5009744 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) : (term761 A B x s y f) = (term789 A B x s y f).
Proof. exact (MK_COMB (@lem5009743) (@lem5009694 A B x s y f)). Qed.
Lemma lem5009794 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term715 A P Q) = (term716 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem5009795 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term715 A P Q) = (term716 A P Q).
Proof. exact (@lem5009794 A P Q). Qed.
Lemma lem5009796 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term790 A B y x s f x') = (term791 A B y x s f x').
Proof. exact (@lem5009795 A (term792 A B x f y x') (term793 A B x s f x')). Qed.
Lemma lem5009797 {A B : Type'} (x : A) (f : A -> B) (y : B) (x' : A) (y' : A) : (term794 A B x f y x' y') = (term669 A B x f y x' y').
Proof. exact (eq_refl (term794 A B x f y x' y')). Qed.
Lemma lem5009798 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5009799 {A B : Type'} (x : A) (f : A -> B) (y : B) (x' : A) (y' : A) : (term795 A B x f y x' y') = (term680 A B x f y x' y').
Proof. exact (MK_COMB (@lem5009798) (@lem5009797 A B x f y x' y')). Qed.
Lemma lem5009800 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (x' : A) (y : A) : (term796 A B x s f x' y) = (term677 A B x s f x' y).
Proof. exact (eq_refl (term796 A B x s f x' y)). Qed.
Lemma lem5009801 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) (y' : A) : (term797 A B y x s f x' y') = (term682 A B y x s f x' y').
Proof. exact (MK_COMB (@lem5009799 A B x f y x' y') (@lem5009800 A B x s f x' y')). Qed.
Lemma lem5009802 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term798 A B y x s f x') = (term691 A B y x s f x').
Proof. exact (fun_ext (fun y' : A => @lem5009801 A B y x s f x' y')). Qed.
Lemma lem5009803 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5009804 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term790 A B y x s f x') = (term692 A B y x s f x').
Proof. exact (MK_COMB (@lem5009803 A) (@lem5009802 A B y x s f x')). Qed.
Lemma lem5009805 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5009806 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term799 A B y x s f x') = (term800 A B y x s f x').
Proof. exact (MK_COMB (@lem5009805) (@lem5009804 A B y x s f x')). Qed.
Lemma lem5009807 {A B : Type'} (x : A) (f : A -> B) (y : B) (x' : A) (y' : A) : (term794 A B x f y x' y') = (term669 A B x f y x' y').
Proof. exact (eq_refl (term794 A B x f y x' y')). Qed.
Lemma lem5009808 {A B : Type'} (x : A) (f : A -> B) (y : B) (x' : A) : (term801 A B x f y x') = (term792 A B x f y x').
Proof. exact (fun_ext (fun y' : A => @lem5009807 A B x f y x' y')). Qed.
Lemma lem5009809 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5009810 {A B : Type'} (x : A) (f : A -> B) (y : B) (x' : A) : (term802 A B x f y x') = (term803 A B x f y x').
Proof. exact (MK_COMB (@lem5009809 A) (@lem5009808 A B x f y x')). Qed.
Lemma lem5009811 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5009812 {A B : Type'} (x : A) (f : A -> B) (y : B) (x' : A) : (term804 A B x f y x') = (term805 A B x f y x').
Proof. exact (MK_COMB (@lem5009811) (@lem5009810 A B x f y x')). Qed.
Lemma lem5009813 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (x' : A) (y : A) : (term796 A B x s f x' y) = (term677 A B x s f x' y).
Proof. exact (eq_refl (term796 A B x s f x' y)). Qed.
Lemma lem5009814 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term806 A B x s f x') = (term793 A B x s f x').
Proof. exact (fun_ext (fun y : A => @lem5009813 A B x s f x' y)). Qed.
Lemma lem5009815 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5009816 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term807 A B x s f x') = (term808 A B x s f x').
Proof. exact (MK_COMB (@lem5009815 A) (@lem5009814 A B x s f x')). Qed.
Lemma lem5009817 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term791 A B y x s f x') = (term809 A B y x s f x').
Proof. exact (MK_COMB (@lem5009812 A B x f y x') (@lem5009816 A B x s f x')). Qed.
Lemma lem5009818 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : ((term790 A B y x s f x') = (term791 A B y x s f x')) = ((term692 A B y x s f x') = (term809 A B y x s f x')).
Proof. exact (MK_COMB (@lem5009806 A B y x s f x') (@lem5009817 A B y x s f x')). Qed.
Lemma lem5009819 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term692 A B y x s f x') = (term809 A B y x s f x').
Proof. exact (EQ_MP (@lem5009818 A B y x s f x') (@lem5009796 A B y x s f x')). Qed.
Lemma lem5009916 {A : Type'} (x' : A) (s : A -> Prop) : (term641 A x' s) = (term641 A x' s).
Proof. exact (eq_refl (term641 A x' s)). Qed.
Lemma lem5009917 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term694 A B y x s f x') = (term810 A B y x s f x').
Proof. exact (MK_COMB (@lem5009916 A x' s) (@lem5009819 A B y x s f x')). Qed.
Lemma lem5009918 {A : Type'} (x' : A) (x : A) : (term645 A x' x) = (term645 A x' x).
Proof. exact (eq_refl (term645 A x' x)). Qed.
Lemma lem5009919 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term697 A B y x s f x') = (term811 A B y x s f x').
Proof. exact (MK_COMB (@lem5009918 A x' x) (@lem5009917 A B y x s f x')). Qed.
Lemma lem5009920 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term749 A B y x s f) = (term812 A B y x s f).
Proof. exact (fun_ext (fun x' : A => @lem5009919 A B y x s f x')). Qed.
Lemma lem5009921 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5009922 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term764 A B y x s f) = (term813 A B y x s f).
Proof. exact (MK_COMB (@lem5009921 A) (@lem5009920 A B y x s f)). Qed.
Lemma lem5009971 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term765 A B y x s f) = (term814 A B y x s f).
Proof. exact (MK_COMB (@lem5009744 A B x s y f) (@lem5009922 A B y x s f)). Qed.
Lemma lem5009972 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term710 A B y x s f) = (term814 A B y x s f).
Proof. exact (TRANS (@lem5009518 A B y x s f) (@lem5009971 A B y x s f)). Qed.
Lemma lem5009973 {A B : Type'} (t : B -> Prop) (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term714 A B t y x s f) = (term815 A B t y x s f).
Proof. exact (MK_COMB (@lem5009491 A B x f s y t) (@lem5009972 A B y x s f)). Qed.
Lemma lem5009975 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term716 A P Q) = (term715 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5009976 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term716 A P Q) = (term715 A P Q).
Proof. exact (@lem5009975 A P Q). Qed.
Lemma lem5009977 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (s : A -> Prop) : (term718 A B y x x' f s) = (term717 A B y x x' f s).
Proof. exact (@lem5009976 A (term719 A B x x' y s) (term720 A B x x' f s)). Qed.
Lemma lem5009978 {A B : Type'} (x : A) (x' : B) (y : B) (x'' : A) (s : A -> Prop) : (term721 A B x x' y s x'') = (term722 A B x x' y x'' s).
Proof. exact (eq_refl (term721 A B x x' y s x'')). Qed.
Lemma lem5009979 {A B : Type'} (x : A) (x' : B) (y : B) (s : A -> Prop) : (term731 A B x x' y s) = (term719 A B x x' y s).
Proof. exact (fun_ext (fun x'' : A => @lem5009978 A B x x' y x'' s)). Qed.
Lemma lem5009980 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5009981 {A B : Type'} (x : A) (x' : B) (y : B) (s : A -> Prop) : (term732 A B x x' y s) = (term733 A B x x' y s).
Proof. exact (MK_COMB (@lem5009980 A) (@lem5009979 A B x x' y s)). Qed.
Lemma lem5009982 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5009983 {A B : Type'} (x : A) (x' : B) (y : B) (s : A -> Prop) : (term734 A B x x' y s) = (term735 A B x x' y s).
Proof. exact (MK_COMB (@lem5009982) (@lem5009981 A B x x' y s)). Qed.
Lemma lem5009984 {A B : Type'} (x : A) (x' : B) (f : A -> B) (x'' : A) (s : A -> Prop) : (term725 A B x x' f s x'') = (term726 A B x x' f x'' s).
Proof. exact (eq_refl (term725 A B x x' f s x'')). Qed.
Lemma lem5009985 {A B : Type'} (x : A) (x' : B) (f : A -> B) (s : A -> Prop) : (term736 A B x x' f s) = (term720 A B x x' f s).
Proof. exact (fun_ext (fun x'' : A => @lem5009984 A B x x' f x'' s)). Qed.
Lemma lem5009986 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5009987 {A B : Type'} (x : A) (x' : B) (f : A -> B) (s : A -> Prop) : (term737 A B x x' f s) = (term738 A B x x' f s).
Proof. exact (MK_COMB (@lem5009986 A) (@lem5009985 A B x x' f s)). Qed.
Lemma lem5009988 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (s : A -> Prop) : (term718 A B y x x' f s) = (term739 A B y x x' f s).
Proof. exact (MK_COMB (@lem5009983 A B x x' y s) (@lem5009987 A B x x' f s)). Qed.
Lemma lem5009989 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5009990 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (s : A -> Prop) : (term816 A B y x x' f s) = (term817 A B y x x' f s).
Proof. exact (MK_COMB (@lem5009989) (@lem5009988 A B y x x' f s)). Qed.
Lemma lem5009991 {A B : Type'} (x : A) (x' : B) (y : B) (x'' : A) (s : A -> Prop) : (term721 A B x x' y s x'') = (term722 A B x x' y x'' s).
Proof. exact (eq_refl (term721 A B x x' y s x'')). Qed.
Lemma lem5009992 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5009993 {A B : Type'} (x : A) (x' : B) (y : B) (x'' : A) (s : A -> Prop) : (term723 A B x x' y s x'') = (term724 A B x x' y x'' s).
Proof. exact (MK_COMB (@lem5009992) (@lem5009991 A B x x' y x'' s)). Qed.
Lemma lem5009994 {A B : Type'} (x : A) (x' : B) (f : A -> B) (x'' : A) (s : A -> Prop) : (term725 A B x x' f s x'') = (term726 A B x x' f x'' s).
Proof. exact (eq_refl (term725 A B x x' f s x'')). Qed.
Lemma lem5009995 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (x'' : A) (s : A -> Prop) : (term727 A B y x x' f s x'') = (term578 A B y x x' f x'' s).
Proof. exact (MK_COMB (@lem5009993 A B x x' y x'' s) (@lem5009994 A B x x' f x'' s)). Qed.
Lemma lem5009996 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (s : A -> Prop) : (term728 A B y x x' f s) = (term579 A B y x x' f s).
Proof. exact (fun_ext (fun x'' : A => @lem5009995 A B y x x' f x'' s)). Qed.
Lemma lem5009997 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5009998 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (s : A -> Prop) : (term717 A B y x x' f s) = (term580 A B y x x' f s).
Proof. exact (MK_COMB (@lem5009997 A) (@lem5009996 A B y x x' f s)). Qed.
Lemma lem5009999 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (s : A -> Prop) : ((term718 A B y x x' f s) = (term717 A B y x x' f s)) = ((term739 A B y x x' f s) = (term580 A B y x x' f s)).
Proof. exact (MK_COMB (@lem5009990 A B y x x' f s) (@lem5009998 A B y x x' f s)). Qed.
Lemma lem5010000 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (s : A -> Prop) : (term739 A B y x x' f s) = (term580 A B y x x' f s).
Proof. exact (EQ_MP (@lem5009999 A B y x x' f s) (@lem5009977 A B y x x' f s)). Qed.
Lemma lem5010001 {B : Type'} (x : B) (y : B) : (term384 B x y) = (term384 B x y).
Proof. exact (eq_refl (term384 B x y)). Qed.
Lemma lem5010002 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (s : A -> Prop) : (term740 A B y x x' f s) = (term581 A B y x x' f s).
Proof. exact (MK_COMB (@lem5010001 B x' y) (@lem5010000 A B y x x' f s)). Qed.
Lemma lem5010004 {A : Type'} (P : Prop) (Q : A -> Prop) : (term818 A P Q) = (term819 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5010005 {A : Type'} (P : Prop) (Q : A -> Prop) : (term818 A P Q) = (term819 A P Q).
Proof. exact (@lem5010004 A P Q). Qed.
Lemma lem5010006 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (s : A -> Prop) : (term820 A B y x x' f s) = (term821 A B y x x' f s).
Proof. exact (@lem5010005 A (x' = y) (term579 A B y x x' f s)). Qed.
Lemma lem5010007 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (x'' : A) (s : A -> Prop) : (term822 A B y x x' f s x'') = (term578 A B y x x' f x'' s).
Proof. exact (eq_refl (term822 A B y x x' f s x'')). Qed.
Lemma lem5010008 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (s : A -> Prop) : (term823 A B y x x' f s) = (term579 A B y x x' f s).
Proof. exact (fun_ext (fun x'' : A => @lem5010007 A B y x x' f x'' s)). Qed.
Lemma lem5010009 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5010010 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (s : A -> Prop) : (term824 A B y x x' f s) = (term580 A B y x x' f s).
Proof. exact (MK_COMB (@lem5010009 A) (@lem5010008 A B y x x' f s)). Qed.
Lemma lem5010011 {B : Type'} (x : B) (y : B) : (term384 B x y) = (term384 B x y).
Proof. exact (eq_refl (term384 B x y)). Qed.
Lemma lem5010012 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (s : A -> Prop) : (term820 A B y x x' f s) = (term581 A B y x x' f s).
Proof. exact (MK_COMB (@lem5010011 B x' y) (@lem5010010 A B y x x' f s)). Qed.
Lemma lem5010013 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5010014 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (s : A -> Prop) : (term825 A B y x x' f s) = (term826 A B y x x' f s).
Proof. exact (MK_COMB (@lem5010013) (@lem5010012 A B y x x' f s)). Qed.
Lemma lem5010015 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (x'' : A) (s : A -> Prop) : (term822 A B y x x' f s x'') = (term578 A B y x x' f x'' s).
Proof. exact (eq_refl (term822 A B y x x' f s x'')). Qed.
Lemma lem5010016 {B : Type'} (x : B) (y : B) : (term384 B x y) = (term384 B x y).
Proof. exact (eq_refl (term384 B x y)). Qed.
Lemma lem5010017 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (x'' : A) (s : A -> Prop) : (term827 A B y x x' f s x'') = (term828 A B y x x' f x'' s).
Proof. exact (MK_COMB (@lem5010016 B x' y) (@lem5010015 A B y x x' f x'' s)). Qed.
Lemma lem5010018 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (s : A -> Prop) : (term829 A B y x x' f s) = (term830 A B y x x' f s).
Proof. exact (fun_ext (fun x'' : A => @lem5010017 A B y x x' f x'' s)). Qed.
Lemma lem5010019 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5010020 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (s : A -> Prop) : (term821 A B y x x' f s) = (term831 A B y x x' f s).
Proof. exact (MK_COMB (@lem5010019 A) (@lem5010018 A B y x x' f s)). Qed.
Lemma lem5010021 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (s : A -> Prop) : ((term820 A B y x x' f s) = (term821 A B y x x' f s)) = ((term581 A B y x x' f s) = (term831 A B y x x' f s)).
Proof. exact (MK_COMB (@lem5010014 A B y x x' f s) (@lem5010020 A B y x x' f s)). Qed.
Lemma lem5010022 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (s : A -> Prop) : (term581 A B y x x' f s) = (term831 A B y x x' f s).
Proof. exact (EQ_MP (@lem5010021 A B y x x' f s) (@lem5010006 A B y x x' f s)). Qed.
Lemma lem5010023 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (s : A -> Prop) : (term740 A B y x x' f s) = (term831 A B y x x' f s).
Proof. exact (TRANS (@lem5010002 A B y x x' f s) (@lem5010022 A B y x x' f s)). Qed.
Lemma lem5010024 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5010025 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (s : A -> Prop) : (term741 A B y x x' f s) = (term832 A B y x x' f s).
Proof. exact (MK_COMB (@lem5010024) (@lem5010023 A B y x x' f s)). Qed.
Lemma lem5010026 {B : Type'} (y : B) (x : B) (t : B -> Prop) : (term619 B y x t) = (term619 B y x t).
Proof. exact (eq_refl (term619 B y x t)). Qed.
Lemma lem5010027 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (y : B) (x' : B) (t : B -> Prop) : (term742 A B x f s y x' t) = (term833 A B x f s y x' t).
Proof. exact (MK_COMB (@lem5010025 A B y x x' f s) (@lem5010026 B y x' t)). Qed.
Lemma lem5010029 {A : Type'} (P : A -> Prop) (Q : Prop) : (term834 A P Q) = (term835 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5010030 {A : Type'} (P : A -> Prop) (Q : Prop) : (term834 A P Q) = (term835 A P Q).
Proof. exact (@lem5010029 A P Q). Qed.
Lemma lem5010031 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (y : B) (x' : B) (t : B -> Prop) : (term836 A B x f s y x' t) = (term837 A B x f s y x' t).
Proof. exact (@lem5010030 A (term830 A B y x x' f s) (term619 B y x' t)). Qed.
Lemma lem5010032 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (x'' : A) (s : A -> Prop) : (term838 A B y x x' f s x'') = (term828 A B y x x' f x'' s).
Proof. exact (eq_refl (term838 A B y x x' f s x'')). Qed.
Lemma lem5010033 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (s : A -> Prop) : (term839 A B y x x' f s) = (term830 A B y x x' f s).
Proof. exact (fun_ext (fun x'' : A => @lem5010032 A B y x x' f x'' s)). Qed.
Lemma lem5010034 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5010035 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (s : A -> Prop) : (term840 A B y x x' f s) = (term831 A B y x x' f s).
Proof. exact (MK_COMB (@lem5010034 A) (@lem5010033 A B y x x' f s)). Qed.
Lemma lem5010036 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5010037 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (s : A -> Prop) : (term841 A B y x x' f s) = (term832 A B y x x' f s).
Proof. exact (MK_COMB (@lem5010036) (@lem5010035 A B y x x' f s)). Qed.
Lemma lem5010038 {B : Type'} (y : B) (x : B) (t : B -> Prop) : (term619 B y x t) = (term619 B y x t).
Proof. exact (eq_refl (term619 B y x t)). Qed.
Lemma lem5010039 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (y : B) (x' : B) (t : B -> Prop) : (term836 A B x f s y x' t) = (term833 A B x f s y x' t).
Proof. exact (MK_COMB (@lem5010037 A B y x x' f s) (@lem5010038 B y x' t)). Qed.
Lemma lem5010040 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5010041 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (y : B) (x' : B) (t : B -> Prop) : (term842 A B x f s y x' t) = (term843 A B x f s y x' t).
Proof. exact (MK_COMB (@lem5010040) (@lem5010039 A B x f s y x' t)). Qed.
Lemma lem5010042 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (x'' : A) (s : A -> Prop) : (term838 A B y x x' f s x'') = (term828 A B y x x' f x'' s).
Proof. exact (eq_refl (term838 A B y x x' f s x'')). Qed.
Lemma lem5010043 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5010044 {A B : Type'} (y : B) (x : A) (x' : B) (f : A -> B) (x'' : A) (s : A -> Prop) : (term844 A B y x x' f s x'') = (term845 A B y x x' f x'' s).
Proof. exact (MK_COMB (@lem5010043) (@lem5010042 A B y x x' f x'' s)). Qed.
Lemma lem5010045 {B : Type'} (y : B) (x : B) (t : B -> Prop) : (term619 B y x t) = (term619 B y x t).
Proof. exact (eq_refl (term619 B y x t)). Qed.
Lemma lem5010046 {A B : Type'} (x : A) (f : A -> B) (x' : A) (s : A -> Prop) (y : B) (x'' : B) (t : B -> Prop) : (term846 A B x f s x' y x'' t) = (term847 A B x f x' s y x'' t).
Proof. exact (MK_COMB (@lem5010044 A B y x x'' f x' s) (@lem5010045 B y x'' t)). Qed.
Lemma lem5010047 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (y : B) (x' : B) (t : B -> Prop) : (term848 A B x f s y x' t) = (term849 A B x f s y x' t).
Proof. exact (fun_ext (fun x'' : A => @lem5010046 A B x f x'' s y x' t)). Qed.
Lemma lem5010048 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5010049 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (y : B) (x' : B) (t : B -> Prop) : (term837 A B x f s y x' t) = (term850 A B x f s y x' t).
Proof. exact (MK_COMB (@lem5010048 A) (@lem5010047 A B x f s y x' t)). Qed.
Lemma lem5010050 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (y : B) (x' : B) (t : B -> Prop) : ((term836 A B x f s y x' t) = (term837 A B x f s y x' t)) = ((term833 A B x f s y x' t) = (term850 A B x f s y x' t)).
Proof. exact (MK_COMB (@lem5010041 A B x f s y x' t) (@lem5010049 A B x f s y x' t)). Qed.
Lemma lem5010051 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (y : B) (x' : B) (t : B -> Prop) : (term833 A B x f s y x' t) = (term850 A B x f s y x' t).
Proof. exact (EQ_MP (@lem5010050 A B x f s y x' t) (@lem5010031 A B x f s y x' t)). Qed.
Lemma lem5010052 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (y : B) (x' : B) (t : B -> Prop) : (term742 A B x f s y x' t) = (term850 A B x f s y x' t).
Proof. exact (TRANS (@lem5010027 A B x f s y x' t) (@lem5010051 A B x f s y x' t)). Qed.
Lemma lem5010053 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (y : B) (t : B -> Prop) : (term743 A B x f s y t) = (term851 A B x f s y t).
Proof. exact (fun_ext (fun x' : B => @lem5010052 A B x f s y x' t)). Qed.
Lemma lem5010054 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5010055 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (y : B) (t : B -> Prop) : (term744 A B x f s y t) = (term852 A B x f s y t).
Proof. exact (MK_COMB (@lem5010054 B) (@lem5010053 A B x f s y t)). Qed.
Lemma lem5010056 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5010057 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (y : B) (t : B -> Prop) : (term745 A B x f s y t) = (term853 A B x f s y t).
Proof. exact (MK_COMB (@lem5010056) (@lem5010055 A B x f s y t)). Qed.
Lemma lem5010059 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term716 A P Q) = (term715 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5010060 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term716 A P Q) = (term715 A P Q).
Proof. exact (@lem5010059 A P Q). Qed.
Lemma lem5010061 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term767 A B x s y f x') = (term766 A B x s y f x').
Proof. exact (@lem5010060 A (term768 A x x') (term769 A B x s y f x')). Qed.
Lemma lem5010062 {A : Type'} (x : A) (x' : A) (y : A) : (term770 A x x' y) = (term637 A x x' y).
Proof. exact (eq_refl (term770 A x x' y)). Qed.
Lemma lem5010063 {A : Type'} (x : A) (x' : A) : (term777 A x x') = (term768 A x x').
Proof. exact (fun_ext (fun y : A => @lem5010062 A x x' y)). Qed.
Lemma lem5010064 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5010065 {A : Type'} (x : A) (x' : A) : (term778 A x x') = (term779 A x x').
Proof. exact (MK_COMB (@lem5010064 A) (@lem5010063 A x x')). Qed.
Lemma lem5010066 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5010067 {A : Type'} (x : A) (x' : A) : (term780 A x x') = (term781 A x x').
Proof. exact (MK_COMB (@lem5010066) (@lem5010065 A x x')). Qed.
Lemma lem5010068 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) (y' : A) : (term772 A B x s y f x' y') = (term647 A B x s y f x' y').
Proof. exact (eq_refl (term772 A B x s y f x' y')). Qed.
Lemma lem5010069 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term782 A B x s y f x') = (term769 A B x s y f x').
Proof. exact (fun_ext (fun y' : A => @lem5010068 A B x s y f x' y')). Qed.
Lemma lem5010070 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5010071 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term783 A B x s y f x') = (term784 A B x s y f x').
Proof. exact (MK_COMB (@lem5010070 A) (@lem5010069 A B x s y f x')). Qed.
Lemma lem5010072 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term767 A B x s y f x') = (term785 A B x s y f x').
Proof. exact (MK_COMB (@lem5010067 A x x') (@lem5010071 A B x s y f x')). Qed.
Lemma lem5010073 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5010074 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term854 A B x s y f x') = (term855 A B x s y f x').
Proof. exact (MK_COMB (@lem5010073) (@lem5010072 A B x s y f x')). Qed.
Lemma lem5010075 {A : Type'} (x : A) (x' : A) (y : A) : (term770 A x x' y) = (term637 A x x' y).
Proof. exact (eq_refl (term770 A x x' y)). Qed.
Lemma lem5010076 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5010077 {A : Type'} (x : A) (x' : A) (y : A) : (term771 A x x' y) = (term650 A x x' y).
Proof. exact (MK_COMB (@lem5010076) (@lem5010075 A x x' y)). Qed.
Lemma lem5010078 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) (y' : A) : (term772 A B x s y f x' y') = (term647 A B x s y f x' y').
Proof. exact (eq_refl (term772 A B x s y f x' y')). Qed.
Lemma lem5010079 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) (y' : A) : (term773 A B x s y f x' y') = (term652 A B x s y f x' y').
Proof. exact (MK_COMB (@lem5010077 A x x' y') (@lem5010078 A B x s y f x' y')). Qed.
Lemma lem5010080 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term774 A B x s y f x') = (term661 A B x s y f x').
Proof. exact (fun_ext (fun y' : A => @lem5010079 A B x s y f x' y')). Qed.
Lemma lem5010081 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5010082 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term766 A B x s y f x') = (term662 A B x s y f x').
Proof. exact (MK_COMB (@lem5010081 A) (@lem5010080 A B x s y f x')). Qed.
Lemma lem5010083 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : ((term767 A B x s y f x') = (term766 A B x s y f x')) = ((term785 A B x s y f x') = (term662 A B x s y f x')).
Proof. exact (MK_COMB (@lem5010074 A B x s y f x') (@lem5010082 A B x s y f x')). Qed.
Lemma lem5010084 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term785 A B x s y f x') = (term662 A B x s y f x').
Proof. exact (EQ_MP (@lem5010083 A B x s y f x') (@lem5010061 A B x s y f x')). Qed.
Lemma lem5010085 {A : Type'} (x' : A) (x : A) : (term572 A x' x) = (term572 A x' x).
Proof. exact (eq_refl (term572 A x' x)). Qed.
Lemma lem5010086 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term786 A B x s y f x') = (term664 A B x s y f x').
Proof. exact (MK_COMB (@lem5010085 A x' x) (@lem5010084 A B x s y f x')). Qed.
Lemma lem5010088 {A : Type'} (P : Prop) (Q : A -> Prop) : (term856 A P Q) = (term857 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5010089 {A : Type'} (P : Prop) (Q : A -> Prop) : (term856 A P Q) = (term857 A P Q).
Proof. exact (@lem5010088 A P Q). Qed.
Lemma lem5010090 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term858 A B x s y f x') = (term859 A B x s y f x').
Proof. exact (@lem5010089 A (x' = x) (term661 A B x s y f x')). Qed.
Lemma lem5010091 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) (y' : A) : (term860 A B x s y f x' y') = (term652 A B x s y f x' y').
Proof. exact (eq_refl (term860 A B x s y f x' y')). Qed.
Lemma lem5010092 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term861 A B x s y f x') = (term661 A B x s y f x').
Proof. exact (fun_ext (fun y' : A => @lem5010091 A B x s y f x' y')). Qed.
Lemma lem5010093 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5010094 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term862 A B x s y f x') = (term662 A B x s y f x').
Proof. exact (MK_COMB (@lem5010093 A) (@lem5010092 A B x s y f x')). Qed.
Lemma lem5010095 {A : Type'} (x' : A) (x : A) : (term572 A x' x) = (term572 A x' x).
Proof. exact (eq_refl (term572 A x' x)). Qed.
Lemma lem5010096 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term858 A B x s y f x') = (term664 A B x s y f x').
Proof. exact (MK_COMB (@lem5010095 A x' x) (@lem5010094 A B x s y f x')). Qed.
Lemma lem5010097 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5010098 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term863 A B x s y f x') = (term864 A B x s y f x').
Proof. exact (MK_COMB (@lem5010097) (@lem5010096 A B x s y f x')). Qed.
Lemma lem5010099 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) (y' : A) : (term860 A B x s y f x' y') = (term652 A B x s y f x' y').
Proof. exact (eq_refl (term860 A B x s y f x' y')). Qed.
Lemma lem5010100 {A : Type'} (x' : A) (x : A) : (term572 A x' x) = (term572 A x' x).
Proof. exact (eq_refl (term572 A x' x)). Qed.
Lemma lem5010101 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) (y' : A) : (term865 A B x s y f x' y') = (term866 A B x s y f x' y').
Proof. exact (MK_COMB (@lem5010100 A x' x) (@lem5010099 A B x s y f x' y')). Qed.
Lemma lem5010102 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term867 A B x s y f x') = (term868 A B x s y f x').
Proof. exact (fun_ext (fun y' : A => @lem5010101 A B x s y f x' y')). Qed.
Lemma lem5010103 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5010104 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term859 A B x s y f x') = (term869 A B x s y f x').
Proof. exact (MK_COMB (@lem5010103 A) (@lem5010102 A B x s y f x')). Qed.
Lemma lem5010105 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : ((term858 A B x s y f x') = (term859 A B x s y f x')) = ((term664 A B x s y f x') = (term869 A B x s y f x')).
Proof. exact (MK_COMB (@lem5010098 A B x s y f x') (@lem5010104 A B x s y f x')). Qed.
Lemma lem5010106 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term664 A B x s y f x') = (term869 A B x s y f x').
Proof. exact (EQ_MP (@lem5010105 A B x s y f x') (@lem5010090 A B x s y f x')). Qed.
Lemma lem5010107 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term786 A B x s y f x') = (term869 A B x s y f x').
Proof. exact (TRANS (@lem5010086 A B x s y f x') (@lem5010106 A B x s y f x')). Qed.
Lemma lem5010108 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) : (term787 A B x s y f) = (term870 A B x s y f).
Proof. exact (fun_ext (fun x' : A => @lem5010107 A B x s y f x')). Qed.
Lemma lem5010109 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5010110 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) : (term788 A B x s y f) = (term871 A B x s y f).
Proof. exact (MK_COMB (@lem5010109 A) (@lem5010108 A B x s y f)). Qed.
Lemma lem5010111 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5010112 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) : (term789 A B x s y f) = (term872 A B x s y f).
Proof. exact (MK_COMB (@lem5010111) (@lem5010110 A B x s y f)). Qed.
Lemma lem5010114 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term716 A P Q) = (term715 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5010115 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term716 A P Q) = (term715 A P Q).
Proof. exact (@lem5010114 A P Q). Qed.
Lemma lem5010116 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term791 A B y x s f x') = (term790 A B y x s f x').
Proof. exact (@lem5010115 A (term792 A B x f y x') (term793 A B x s f x')). Qed.
Lemma lem5010117 {A B : Type'} (x : A) (f : A -> B) (y : B) (x' : A) (y' : A) : (term794 A B x f y x' y') = (term669 A B x f y x' y').
Proof. exact (eq_refl (term794 A B x f y x' y')). Qed.
Lemma lem5010118 {A B : Type'} (x : A) (f : A -> B) (y : B) (x' : A) : (term801 A B x f y x') = (term792 A B x f y x').
Proof. exact (fun_ext (fun y' : A => @lem5010117 A B x f y x' y')). Qed.
Lemma lem5010119 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5010120 {A B : Type'} (x : A) (f : A -> B) (y : B) (x' : A) : (term802 A B x f y x') = (term803 A B x f y x').
Proof. exact (MK_COMB (@lem5010119 A) (@lem5010118 A B x f y x')). Qed.
Lemma lem5010121 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5010122 {A B : Type'} (x : A) (f : A -> B) (y : B) (x' : A) : (term804 A B x f y x') = (term805 A B x f y x').
Proof. exact (MK_COMB (@lem5010121) (@lem5010120 A B x f y x')). Qed.
Lemma lem5010123 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (x' : A) (y : A) : (term796 A B x s f x' y) = (term677 A B x s f x' y).
Proof. exact (eq_refl (term796 A B x s f x' y)). Qed.
Lemma lem5010124 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term806 A B x s f x') = (term793 A B x s f x').
Proof. exact (fun_ext (fun y : A => @lem5010123 A B x s f x' y)). Qed.
Lemma lem5010125 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5010126 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term807 A B x s f x') = (term808 A B x s f x').
Proof. exact (MK_COMB (@lem5010125 A) (@lem5010124 A B x s f x')). Qed.
Lemma lem5010127 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term791 A B y x s f x') = (term809 A B y x s f x').
Proof. exact (MK_COMB (@lem5010122 A B x f y x') (@lem5010126 A B x s f x')). Qed.
Lemma lem5010128 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5010129 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term873 A B y x s f x') = (term874 A B y x s f x').
Proof. exact (MK_COMB (@lem5010128) (@lem5010127 A B y x s f x')). Qed.
Lemma lem5010130 {A B : Type'} (x : A) (f : A -> B) (y : B) (x' : A) (y' : A) : (term794 A B x f y x' y') = (term669 A B x f y x' y').
Proof. exact (eq_refl (term794 A B x f y x' y')). Qed.
Lemma lem5010131 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5010132 {A B : Type'} (x : A) (f : A -> B) (y : B) (x' : A) (y' : A) : (term795 A B x f y x' y') = (term680 A B x f y x' y').
Proof. exact (MK_COMB (@lem5010131) (@lem5010130 A B x f y x' y')). Qed.
Lemma lem5010133 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (x' : A) (y : A) : (term796 A B x s f x' y) = (term677 A B x s f x' y).
Proof. exact (eq_refl (term796 A B x s f x' y)). Qed.
Lemma lem5010134 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) (y' : A) : (term797 A B y x s f x' y') = (term682 A B y x s f x' y').
Proof. exact (MK_COMB (@lem5010132 A B x f y x' y') (@lem5010133 A B x s f x' y')). Qed.
Lemma lem5010135 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term798 A B y x s f x') = (term691 A B y x s f x').
Proof. exact (fun_ext (fun y' : A => @lem5010134 A B y x s f x' y')). Qed.
Lemma lem5010136 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5010137 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term790 A B y x s f x') = (term692 A B y x s f x').
Proof. exact (MK_COMB (@lem5010136 A) (@lem5010135 A B y x s f x')). Qed.
Lemma lem5010138 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : ((term791 A B y x s f x') = (term790 A B y x s f x')) = ((term809 A B y x s f x') = (term692 A B y x s f x')).
Proof. exact (MK_COMB (@lem5010129 A B y x s f x') (@lem5010137 A B y x s f x')). Qed.
Lemma lem5010139 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term809 A B y x s f x') = (term692 A B y x s f x').
Proof. exact (EQ_MP (@lem5010138 A B y x s f x') (@lem5010116 A B y x s f x')). Qed.
Lemma lem5010140 {A : Type'} (x' : A) (s : A -> Prop) : (term641 A x' s) = (term641 A x' s).
Proof. exact (eq_refl (term641 A x' s)). Qed.
Lemma lem5010141 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term810 A B y x s f x') = (term694 A B y x s f x').
Proof. exact (MK_COMB (@lem5010140 A x' s) (@lem5010139 A B y x s f x')). Qed.
Lemma lem5010143 {A : Type'} (P : Prop) (Q : A -> Prop) : (term856 A P Q) = (term857 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5010144 {A : Type'} (P : Prop) (Q : A -> Prop) : (term856 A P Q) = (term857 A P Q).
Proof. exact (@lem5010143 A P Q). Qed.
Lemma lem5010145 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term875 A B y x s f x') = (term876 A B y x s f x').
Proof. exact (@lem5010144 A (@IN A x' s) (term691 A B y x s f x')). Qed.
Lemma lem5010146 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) (y' : A) : (term877 A B y x s f x' y') = (term682 A B y x s f x' y').
Proof. exact (eq_refl (term877 A B y x s f x' y')). Qed.
Lemma lem5010147 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term878 A B y x s f x') = (term691 A B y x s f x').
Proof. exact (fun_ext (fun y' : A => @lem5010146 A B y x s f x' y')). Qed.
Lemma lem5010148 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5010149 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term879 A B y x s f x') = (term692 A B y x s f x').
Proof. exact (MK_COMB (@lem5010148 A) (@lem5010147 A B y x s f x')). Qed.
Lemma lem5010150 {A : Type'} (x' : A) (s : A -> Prop) : (term641 A x' s) = (term641 A x' s).
Proof. exact (eq_refl (term641 A x' s)). Qed.
Lemma lem5010151 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term875 A B y x s f x') = (term694 A B y x s f x').
Proof. exact (MK_COMB (@lem5010150 A x' s) (@lem5010149 A B y x s f x')). Qed.
Lemma lem5010152 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5010153 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term880 A B y x s f x') = (term881 A B y x s f x').
Proof. exact (MK_COMB (@lem5010152) (@lem5010151 A B y x s f x')). Qed.
Lemma lem5010154 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) (y' : A) : (term877 A B y x s f x' y') = (term682 A B y x s f x' y').
Proof. exact (eq_refl (term877 A B y x s f x' y')). Qed.
Lemma lem5010155 {A : Type'} (x' : A) (s : A -> Prop) : (term641 A x' s) = (term641 A x' s).
Proof. exact (eq_refl (term641 A x' s)). Qed.
Lemma lem5010156 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) (y' : A) : (term882 A B y x s f x' y') = (term883 A B y x s f x' y').
Proof. exact (MK_COMB (@lem5010155 A x' s) (@lem5010154 A B y x s f x' y')). Qed.
Lemma lem5010157 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term884 A B y x s f x') = (term885 A B y x s f x').
Proof. exact (fun_ext (fun y' : A => @lem5010156 A B y x s f x' y')). Qed.
Lemma lem5010158 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5010159 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term876 A B y x s f x') = (term886 A B y x s f x').
Proof. exact (MK_COMB (@lem5010158 A) (@lem5010157 A B y x s f x')). Qed.
Lemma lem5010160 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : ((term875 A B y x s f x') = (term876 A B y x s f x')) = ((term694 A B y x s f x') = (term886 A B y x s f x')).
Proof. exact (MK_COMB (@lem5010153 A B y x s f x') (@lem5010159 A B y x s f x')). Qed.
Lemma lem5010161 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term694 A B y x s f x') = (term886 A B y x s f x').
Proof. exact (EQ_MP (@lem5010160 A B y x s f x') (@lem5010145 A B y x s f x')). Qed.
Lemma lem5010162 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term810 A B y x s f x') = (term886 A B y x s f x').
Proof. exact (TRANS (@lem5010141 A B y x s f x') (@lem5010161 A B y x s f x')). Qed.
Lemma lem5010163 {A : Type'} (x' : A) (x : A) : (term645 A x' x) = (term645 A x' x).
Proof. exact (eq_refl (term645 A x' x)). Qed.
Lemma lem5010164 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term811 A B y x s f x') = (term887 A B y x s f x').
Proof. exact (MK_COMB (@lem5010163 A x' x) (@lem5010162 A B y x s f x')). Qed.
Lemma lem5010166 {A : Type'} (P : Prop) (Q : A -> Prop) : (term856 A P Q) = (term857 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5010167 {A : Type'} (P : Prop) (Q : A -> Prop) : (term856 A P Q) = (term857 A P Q).
Proof. exact (@lem5010166 A P Q). Qed.
Lemma lem5010168 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term888 A B y x s f x') = (term889 A B y x s f x').
Proof. exact (@lem5010167 A (term634 A x' x) (term885 A B y x s f x')). Qed.
Lemma lem5010169 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) (y' : A) : (term890 A B y x s f x' y') = (term883 A B y x s f x' y').
Proof. exact (eq_refl (term890 A B y x s f x' y')). Qed.
Lemma lem5010170 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term891 A B y x s f x') = (term885 A B y x s f x').
Proof. exact (fun_ext (fun y' : A => @lem5010169 A B y x s f x' y')). Qed.
Lemma lem5010171 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5010172 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term892 A B y x s f x') = (term886 A B y x s f x').
Proof. exact (MK_COMB (@lem5010171 A) (@lem5010170 A B y x s f x')). Qed.
Lemma lem5010173 {A : Type'} (x' : A) (x : A) : (term645 A x' x) = (term645 A x' x).
Proof. exact (eq_refl (term645 A x' x)). Qed.
Lemma lem5010174 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term888 A B y x s f x') = (term887 A B y x s f x').
Proof. exact (MK_COMB (@lem5010173 A x' x) (@lem5010172 A B y x s f x')). Qed.
Lemma lem5010175 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5010176 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term893 A B y x s f x') = (term894 A B y x s f x').
Proof. exact (MK_COMB (@lem5010175) (@lem5010174 A B y x s f x')). Qed.
Lemma lem5010177 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) (y' : A) : (term890 A B y x s f x' y') = (term883 A B y x s f x' y').
Proof. exact (eq_refl (term890 A B y x s f x' y')). Qed.
Lemma lem5010178 {A : Type'} (x' : A) (x : A) : (term645 A x' x) = (term645 A x' x).
Proof. exact (eq_refl (term645 A x' x)). Qed.
Lemma lem5010179 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) (y' : A) : (term895 A B y x s f x' y') = (term896 A B y x s f x' y').
Proof. exact (MK_COMB (@lem5010178 A x' x) (@lem5010177 A B y x s f x' y')). Qed.
Lemma lem5010180 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term897 A B y x s f x') = (term898 A B y x s f x').
Proof. exact (fun_ext (fun y' : A => @lem5010179 A B y x s f x' y')). Qed.
Lemma lem5010181 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5010182 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term889 A B y x s f x') = (term899 A B y x s f x').
Proof. exact (MK_COMB (@lem5010181 A) (@lem5010180 A B y x s f x')). Qed.
Lemma lem5010183 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : ((term888 A B y x s f x') = (term889 A B y x s f x')) = ((term887 A B y x s f x') = (term899 A B y x s f x')).
Proof. exact (MK_COMB (@lem5010176 A B y x s f x') (@lem5010182 A B y x s f x')). Qed.
Lemma lem5010184 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term887 A B y x s f x') = (term899 A B y x s f x').
Proof. exact (EQ_MP (@lem5010183 A B y x s f x') (@lem5010168 A B y x s f x')). Qed.
Lemma lem5010185 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term811 A B y x s f x') = (term899 A B y x s f x').
Proof. exact (TRANS (@lem5010164 A B y x s f x') (@lem5010184 A B y x s f x')). Qed.
Lemma lem5010186 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term812 A B y x s f) = (term900 A B y x s f).
Proof. exact (fun_ext (fun x' : A => @lem5010185 A B y x s f x')). Qed.
Lemma lem5010187 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5010188 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term813 A B y x s f) = (term901 A B y x s f).
Proof. exact (MK_COMB (@lem5010187 A) (@lem5010186 A B y x s f)). Qed.
Lemma lem5010189 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term814 A B y x s f) = (term902 A B y x s f).
Proof. exact (MK_COMB (@lem5010112 A B x s y f) (@lem5010188 A B y x s f)). Qed.
Lemma lem5010191 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term716 A P Q) = (term715 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5010192 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term716 A P Q) = (term715 A P Q).
Proof. exact (@lem5010191 A P Q). Qed.
Lemma lem5010193 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term903 A B y x s f) = (term904 A B y x s f).
Proof. exact (@lem5010192 A (term870 A B x s y f) (term900 A B y x s f)). Qed.
Lemma lem5010194 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term905 A B x s y f x') = (term869 A B x s y f x').
Proof. exact (eq_refl (term905 A B x s y f x')). Qed.
Lemma lem5010195 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) : (term906 A B x s y f) = (term870 A B x s y f).
Proof. exact (fun_ext (fun x' : A => @lem5010194 A B x s y f x')). Qed.
Lemma lem5010196 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5010197 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) : (term907 A B x s y f) = (term871 A B x s y f).
Proof. exact (MK_COMB (@lem5010196 A) (@lem5010195 A B x s y f)). Qed.
Lemma lem5010198 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5010199 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) : (term908 A B x s y f) = (term872 A B x s y f).
Proof. exact (MK_COMB (@lem5010198) (@lem5010197 A B x s y f)). Qed.
Lemma lem5010200 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term909 A B y x s f x') = (term899 A B y x s f x').
Proof. exact (eq_refl (term909 A B y x s f x')). Qed.
Lemma lem5010201 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term910 A B y x s f) = (term900 A B y x s f).
Proof. exact (fun_ext (fun x' : A => @lem5010200 A B y x s f x')). Qed.
Lemma lem5010202 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5010203 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term911 A B y x s f) = (term901 A B y x s f).
Proof. exact (MK_COMB (@lem5010202 A) (@lem5010201 A B y x s f)). Qed.
Lemma lem5010204 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term903 A B y x s f) = (term902 A B y x s f).
Proof. exact (MK_COMB (@lem5010199 A B x s y f) (@lem5010203 A B y x s f)). Qed.
Lemma lem5010205 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5010206 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term912 A B y x s f) = (term913 A B y x s f).
Proof. exact (MK_COMB (@lem5010205) (@lem5010204 A B y x s f)). Qed.
Lemma lem5010207 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term905 A B x s y f x') = (term869 A B x s y f x').
Proof. exact (eq_refl (term905 A B x s y f x')). Qed.
Lemma lem5010208 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5010209 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term914 A B x s y f x') = (term915 A B x s y f x').
Proof. exact (MK_COMB (@lem5010208) (@lem5010207 A B x s y f x')). Qed.
Lemma lem5010210 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term909 A B y x s f x') = (term899 A B y x s f x').
Proof. exact (eq_refl (term909 A B y x s f x')). Qed.
Lemma lem5010211 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term916 A B y x s f x') = (term917 A B y x s f x').
Proof. exact (MK_COMB (@lem5010209 A B x s y f x') (@lem5010210 A B y x s f x')). Qed.
Lemma lem5010212 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term918 A B y x s f) = (term919 A B y x s f).
Proof. exact (fun_ext (fun x' : A => @lem5010211 A B y x s f x')). Qed.
Lemma lem5010213 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5010214 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term904 A B y x s f) = (term920 A B y x s f).
Proof. exact (MK_COMB (@lem5010213 A) (@lem5010212 A B y x s f)). Qed.
Lemma lem5010215 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) : ((term903 A B y x s f) = (term904 A B y x s f)) = ((term902 A B y x s f) = (term920 A B y x s f)).
Proof. exact (MK_COMB (@lem5010206 A B y x s f) (@lem5010214 A B y x s f)). Qed.
Lemma lem5010216 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term902 A B y x s f) = (term920 A B y x s f).
Proof. exact (EQ_MP (@lem5010215 A B y x s f) (@lem5010193 A B y x s f)). Qed.
Lemma lem5010218 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term716 A P Q) = (term715 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5010219 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term716 A P Q) = (term715 A P Q).
Proof. exact (@lem5010218 A P Q). Qed.
Lemma lem5010220 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term921 A B y x s f x') = (term922 A B y x s f x').
Proof. exact (@lem5010219 A (term868 A B x s y f x') (term898 A B y x s f x')). Qed.
Lemma lem5010221 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) (y' : A) : (term923 A B x s y f x' y') = (term866 A B x s y f x' y').
Proof. exact (eq_refl (term923 A B x s y f x' y')). Qed.
Lemma lem5010222 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term924 A B x s y f x') = (term868 A B x s y f x').
Proof. exact (fun_ext (fun y' : A => @lem5010221 A B x s y f x' y')). Qed.
Lemma lem5010223 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5010224 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term925 A B x s y f x') = (term869 A B x s y f x').
Proof. exact (MK_COMB (@lem5010223 A) (@lem5010222 A B x s y f x')). Qed.
Lemma lem5010225 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5010226 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) : (term926 A B x s y f x') = (term915 A B x s y f x').
Proof. exact (MK_COMB (@lem5010225) (@lem5010224 A B x s y f x')). Qed.
Lemma lem5010227 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) (y' : A) : (term927 A B y x s f x' y') = (term896 A B y x s f x' y').
Proof. exact (eq_refl (term927 A B y x s f x' y')). Qed.
Lemma lem5010228 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term928 A B y x s f x') = (term898 A B y x s f x').
Proof. exact (fun_ext (fun y' : A => @lem5010227 A B y x s f x' y')). Qed.
Lemma lem5010229 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5010230 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term929 A B y x s f x') = (term899 A B y x s f x').
Proof. exact (MK_COMB (@lem5010229 A) (@lem5010228 A B y x s f x')). Qed.
Lemma lem5010231 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term921 A B y x s f x') = (term917 A B y x s f x').
Proof. exact (MK_COMB (@lem5010226 A B x s y f x') (@lem5010230 A B y x s f x')). Qed.
Lemma lem5010232 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5010233 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term930 A B y x s f x') = (term931 A B y x s f x').
Proof. exact (MK_COMB (@lem5010232) (@lem5010231 A B y x s f x')). Qed.
Lemma lem5010234 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) (y' : A) : (term923 A B x s y f x' y') = (term866 A B x s y f x' y').
Proof. exact (eq_refl (term923 A B x s y f x' y')). Qed.
Lemma lem5010235 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5010236 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x' : A) (y' : A) : (term932 A B x s y f x' y') = (term933 A B x s y f x' y').
Proof. exact (MK_COMB (@lem5010235) (@lem5010234 A B x s y f x' y')). Qed.
Lemma lem5010237 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) (y' : A) : (term927 A B y x s f x' y') = (term896 A B y x s f x' y').
Proof. exact (eq_refl (term927 A B y x s f x' y')). Qed.
Lemma lem5010238 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) (y' : A) : (term934 A B y x s f x' y') = (term935 A B y x s f x' y').
Proof. exact (MK_COMB (@lem5010236 A B x s y f x' y') (@lem5010237 A B y x s f x' y')). Qed.
Lemma lem5010239 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term936 A B y x s f x') = (term937 A B y x s f x').
Proof. exact (fun_ext (fun y' : A => @lem5010238 A B y x s f x' y')). Qed.
Lemma lem5010240 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5010241 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term922 A B y x s f x') = (term938 A B y x s f x').
Proof. exact (MK_COMB (@lem5010240 A) (@lem5010239 A B y x s f x')). Qed.
Lemma lem5010242 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : ((term921 A B y x s f x') = (term922 A B y x s f x')) = ((term917 A B y x s f x') = (term938 A B y x s f x')).
Proof. exact (MK_COMB (@lem5010233 A B y x s f x') (@lem5010241 A B y x s f x')). Qed.
Lemma lem5010243 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term917 A B y x s f x') = (term938 A B y x s f x').
Proof. exact (EQ_MP (@lem5010242 A B y x s f x') (@lem5010220 A B y x s f x')). Qed.
Lemma lem5010244 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term919 A B y x s f) = (term939 A B y x s f).
Proof. exact (fun_ext (fun x' : A => @lem5010243 A B y x s f x')). Qed.
Lemma lem5010245 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5010246 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term920 A B y x s f) = (term940 A B y x s f).
Proof. exact (MK_COMB (@lem5010245 A) (@lem5010244 A B y x s f)). Qed.
Lemma lem5010247 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term902 A B y x s f) = (term940 A B y x s f).
Proof. exact (TRANS (@lem5010216 A B y x s f) (@lem5010246 A B y x s f)). Qed.
Lemma lem5010248 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term814 A B y x s f) = (term940 A B y x s f).
Proof. exact (TRANS (@lem5010189 A B y x s f) (@lem5010247 A B y x s f)). Qed.
Lemma lem5010249 {A B : Type'} (t : B -> Prop) (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term815 A B t y x s f) = (term941 A B t y x s f).
Proof. exact (MK_COMB (@lem5010057 A B x f s y t) (@lem5010248 A B y x s f)). Qed.
Lemma lem5010253 {A : Type'} (P : A -> Prop) (Q : Prop) : (term942 A P Q) = (term943 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5010254 {B : Type'} (P : B -> Prop) (Q : Prop) : (term942 B P Q) = (term943 B P Q).
Proof. exact (@lem5010253 B P Q). Qed.
Lemma lem5010255 {A B : Type'} (t : B -> Prop) (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term944 A B t y x s f) = (term945 A B t y x s f).
Proof. exact (@lem5010254 B (term851 A B x f s y t) (term940 A B y x s f)). Qed.
Lemma lem5010256 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (y : B) (x' : B) (t : B -> Prop) : (term946 A B x f s y t x') = (term850 A B x f s y x' t).
Proof. exact (eq_refl (term946 A B x f s y t x')). Qed.
Lemma lem5010257 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (y : B) (t : B -> Prop) : (term947 A B x f s y t) = (term851 A B x f s y t).
Proof. exact (fun_ext (fun x' : B => @lem5010256 A B x f s y x' t)). Qed.
Lemma lem5010258 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5010259 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (y : B) (t : B -> Prop) : (term948 A B x f s y t) = (term852 A B x f s y t).
Proof. exact (MK_COMB (@lem5010258 B) (@lem5010257 A B x f s y t)). Qed.
Lemma lem5010260 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5010261 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (y : B) (t : B -> Prop) : (term949 A B x f s y t) = (term853 A B x f s y t).
Proof. exact (MK_COMB (@lem5010260) (@lem5010259 A B x f s y t)). Qed.
Lemma lem5010262 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term940 A B y x s f) = (term940 A B y x s f).
Proof. exact (eq_refl (term940 A B y x s f)). Qed.
Lemma lem5010263 {A B : Type'} (t : B -> Prop) (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term944 A B t y x s f) = (term941 A B t y x s f).
Proof. exact (MK_COMB (@lem5010261 A B x f s y t) (@lem5010262 A B y x s f)). Qed.
Lemma lem5010264 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5010265 {A B : Type'} (t : B -> Prop) (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term950 A B t y x s f) = (term951 A B t y x s f).
Proof. exact (MK_COMB (@lem5010264) (@lem5010263 A B t y x s f)). Qed.
Lemma lem5010266 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (y : B) (x' : B) (t : B -> Prop) : (term946 A B x f s y t x') = (term850 A B x f s y x' t).
Proof. exact (eq_refl (term946 A B x f s y t x')). Qed.
Lemma lem5010267 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5010268 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (y : B) (x' : B) (t : B -> Prop) : (term952 A B x f s y t x') = (term953 A B x f s y x' t).
Proof. exact (MK_COMB (@lem5010267) (@lem5010266 A B x f s y x' t)). Qed.
Lemma lem5010269 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term940 A B y x s f) = (term940 A B y x s f).
Proof. exact (eq_refl (term940 A B y x s f)). Qed.
Lemma lem5010270 {A B : Type'} (x : B) (t : B -> Prop) (y : B) (x' : A) (s : A -> Prop) (f : A -> B) : (term954 A B t x y x' s f) = (term955 A B x t y x' s f).
Proof. exact (MK_COMB (@lem5010268 A B x' f s y x t) (@lem5010269 A B y x' s f)). Qed.
Lemma lem5010271 {A B : Type'} (t : B -> Prop) (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term956 A B t y x s f) = (term957 A B t y x s f).
Proof. exact (fun_ext (fun x' : B => @lem5010270 A B x' t y x s f)). Qed.
Lemma lem5010272 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5010273 {A B : Type'} (t : B -> Prop) (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term945 A B t y x s f) = (term958 A B t y x s f).
Proof. exact (MK_COMB (@lem5010272 B) (@lem5010271 A B t y x s f)). Qed.
Lemma lem5010274 {A B : Type'} (t : B -> Prop) (y : B) (x : A) (s : A -> Prop) (f : A -> B) : ((term944 A B t y x s f) = (term945 A B t y x s f)) = ((term941 A B t y x s f) = (term958 A B t y x s f)).
Proof. exact (MK_COMB (@lem5010265 A B t y x s f) (@lem5010273 A B t y x s f)). Qed.
Lemma lem5010275 {A B : Type'} (t : B -> Prop) (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term941 A B t y x s f) = (term958 A B t y x s f).
Proof. exact (EQ_MP (@lem5010274 A B t y x s f) (@lem5010255 A B t y x s f)). Qed.
Lemma lem5010277 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term716 A P Q) = (term715 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5010278 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term716 A P Q) = (term715 A P Q).
Proof. exact (@lem5010277 A P Q). Qed.
Lemma lem5010279 {A B : Type'} (x : B) (t : B -> Prop) (y : B) (x' : A) (s : A -> Prop) (f : A -> B) : (term959 A B x t y x' s f) = (term960 A B x t y x' s f).
Proof. exact (@lem5010278 A (term849 A B x' f s y x t) (term939 A B y x' s f)). Qed.
Lemma lem5010280 {A B : Type'} (x : A) (f : A -> B) (x' : A) (s : A -> Prop) (y : B) (x'' : B) (t : B -> Prop) : (term961 A B x f s y x'' t x') = (term847 A B x f x' s y x'' t).
Proof. exact (eq_refl (term961 A B x f s y x'' t x')). Qed.
Lemma lem5010281 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (y : B) (x' : B) (t : B -> Prop) : (term962 A B x f s y x' t) = (term849 A B x f s y x' t).
Proof. exact (fun_ext (fun x'' : A => @lem5010280 A B x f x'' s y x' t)). Qed.
Lemma lem5010282 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5010283 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (y : B) (x' : B) (t : B -> Prop) : (term963 A B x f s y x' t) = (term850 A B x f s y x' t).
Proof. exact (MK_COMB (@lem5010282 A) (@lem5010281 A B x f s y x' t)). Qed.
Lemma lem5010284 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5010285 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (y : B) (x' : B) (t : B -> Prop) : (term964 A B x f s y x' t) = (term953 A B x f s y x' t).
Proof. exact (MK_COMB (@lem5010284) (@lem5010283 A B x f s y x' t)). Qed.
Lemma lem5010286 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term965 A B y x s f x') = (term938 A B y x s f x').
Proof. exact (eq_refl (term965 A B y x s f x')). Qed.
Lemma lem5010287 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term966 A B y x s f) = (term939 A B y x s f).
Proof. exact (fun_ext (fun x' : A => @lem5010286 A B y x s f x')). Qed.
Lemma lem5010288 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5010289 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term967 A B y x s f) = (term940 A B y x s f).
Proof. exact (MK_COMB (@lem5010288 A) (@lem5010287 A B y x s f)). Qed.
Lemma lem5010290 {A B : Type'} (x : B) (t : B -> Prop) (y : B) (x' : A) (s : A -> Prop) (f : A -> B) : (term959 A B x t y x' s f) = (term955 A B x t y x' s f).
Proof. exact (MK_COMB (@lem5010285 A B x' f s y x t) (@lem5010289 A B y x' s f)). Qed.
Lemma lem5010291 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5010292 {A B : Type'} (x : B) (t : B -> Prop) (y : B) (x' : A) (s : A -> Prop) (f : A -> B) : (term968 A B x t y x' s f) = (term969 A B x t y x' s f).
Proof. exact (MK_COMB (@lem5010291) (@lem5010290 A B x t y x' s f)). Qed.
Lemma lem5010293 {A B : Type'} (x : A) (f : A -> B) (x' : A) (s : A -> Prop) (y : B) (x'' : B) (t : B -> Prop) : (term961 A B x f s y x'' t x') = (term847 A B x f x' s y x'' t).
Proof. exact (eq_refl (term961 A B x f s y x'' t x')). Qed.
Lemma lem5010294 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5010295 {A B : Type'} (x : A) (f : A -> B) (x' : A) (s : A -> Prop) (y : B) (x'' : B) (t : B -> Prop) : (term970 A B x f s y x'' t x') = (term971 A B x f x' s y x'' t).
Proof. exact (MK_COMB (@lem5010294) (@lem5010293 A B x f x' s y x'' t)). Qed.
Lemma lem5010296 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term965 A B y x s f x') = (term938 A B y x s f x').
Proof. exact (eq_refl (term965 A B y x s f x')). Qed.
Lemma lem5010297 {A B : Type'} (x : B) (t : B -> Prop) (y : B) (x' : A) (s : A -> Prop) (f : A -> B) (x'' : A) : (term972 A B x t y x' s f x'') = (term973 A B x t y x' s f x'').
Proof. exact (MK_COMB (@lem5010295 A B x' f x'' s y x t) (@lem5010296 A B y x' s f x'')). Qed.
Lemma lem5010298 {A B : Type'} (x : B) (t : B -> Prop) (y : B) (x' : A) (s : A -> Prop) (f : A -> B) : (term974 A B x t y x' s f) = (term975 A B x t y x' s f).
Proof. exact (fun_ext (fun x'' : A => @lem5010297 A B x t y x' s f x'')). Qed.
Lemma lem5010299 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5010300 {A B : Type'} (x : B) (t : B -> Prop) (y : B) (x' : A) (s : A -> Prop) (f : A -> B) : (term960 A B x t y x' s f) = (term976 A B x t y x' s f).
Proof. exact (MK_COMB (@lem5010299 A) (@lem5010298 A B x t y x' s f)). Qed.
Lemma lem5010301 {A B : Type'} (x : B) (t : B -> Prop) (y : B) (x' : A) (s : A -> Prop) (f : A -> B) : ((term959 A B x t y x' s f) = (term960 A B x t y x' s f)) = ((term955 A B x t y x' s f) = (term976 A B x t y x' s f)).
Proof. exact (MK_COMB (@lem5010292 A B x t y x' s f) (@lem5010300 A B x t y x' s f)). Qed.
Lemma lem5010302 {A B : Type'} (x : B) (t : B -> Prop) (y : B) (x' : A) (s : A -> Prop) (f : A -> B) : (term955 A B x t y x' s f) = (term976 A B x t y x' s f).
Proof. exact (EQ_MP (@lem5010301 A B x t y x' s f) (@lem5010279 A B x t y x' s f)). Qed.
Lemma lem5010304 {A : Type'} (P : Prop) (Q : A -> Prop) : (term818 A P Q) = (term819 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5010305 {A : Type'} (P : Prop) (Q : A -> Prop) : (term818 A P Q) = (term819 A P Q).
Proof. exact (@lem5010304 A P Q). Qed.
Lemma lem5010306 {A B : Type'} (x : B) (t : B -> Prop) (y : B) (x' : A) (s : A -> Prop) (f : A -> B) (x'' : A) : (term977 A B x t y x' s f x'') = (term978 A B x t y x' s f x'').
Proof. exact (@lem5010305 A (term847 A B x' f x'' s y x t) (term937 A B y x' s f x'')). Qed.
Lemma lem5010307 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) (y' : A) : (term979 A B y x s f x' y') = (term935 A B y x s f x' y').
Proof. exact (eq_refl (term979 A B y x s f x' y')). Qed.
Lemma lem5010308 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term980 A B y x s f x') = (term937 A B y x s f x').
Proof. exact (fun_ext (fun y' : A => @lem5010307 A B y x s f x' y')). Qed.
Lemma lem5010309 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5010310 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) : (term981 A B y x s f x') = (term938 A B y x s f x').
Proof. exact (MK_COMB (@lem5010309 A) (@lem5010308 A B y x s f x')). Qed.
Lemma lem5010311 {A B : Type'} (x : A) (f : A -> B) (x' : A) (s : A -> Prop) (y : B) (x'' : B) (t : B -> Prop) : (term971 A B x f x' s y x'' t) = (term971 A B x f x' s y x'' t).
Proof. exact (eq_refl (term971 A B x f x' s y x'' t)). Qed.
Lemma lem5010312 {A B : Type'} (x : B) (t : B -> Prop) (y : B) (x' : A) (s : A -> Prop) (f : A -> B) (x'' : A) : (term977 A B x t y x' s f x'') = (term973 A B x t y x' s f x'').
Proof. exact (MK_COMB (@lem5010311 A B x' f x'' s y x t) (@lem5010310 A B y x' s f x'')). Qed.
Lemma lem5010313 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5010314 {A B : Type'} (x : B) (t : B -> Prop) (y : B) (x' : A) (s : A -> Prop) (f : A -> B) (x'' : A) : (term982 A B x t y x' s f x'') = (term983 A B x t y x' s f x'').
Proof. exact (MK_COMB (@lem5010313) (@lem5010312 A B x t y x' s f x'')). Qed.
Lemma lem5010315 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x' : A) (y' : A) : (term979 A B y x s f x' y') = (term935 A B y x s f x' y').
Proof. exact (eq_refl (term979 A B y x s f x' y')). Qed.
Lemma lem5010316 {A B : Type'} (x : A) (f : A -> B) (x' : A) (s : A -> Prop) (y : B) (x'' : B) (t : B -> Prop) : (term971 A B x f x' s y x'' t) = (term971 A B x f x' s y x'' t).
Proof. exact (eq_refl (term971 A B x f x' s y x'' t)). Qed.
Lemma lem5010317 {A B : Type'} (x : B) (t : B -> Prop) (y : B) (x' : A) (s : A -> Prop) (f : A -> B) (x'' : A) (y' : A) : (term984 A B x t y x' s f x'' y') = (term985 A B x t y x' s f x'' y').
Proof. exact (MK_COMB (@lem5010316 A B x' f x'' s y x t) (@lem5010315 A B y x' s f x'' y')). Qed.
Lemma lem5010318 {A B : Type'} (x : B) (t : B -> Prop) (y : B) (x' : A) (s : A -> Prop) (f : A -> B) (x'' : A) : (term986 A B x t y x' s f x'') = (term987 A B x t y x' s f x'').
Proof. exact (fun_ext (fun y' : A => @lem5010317 A B x t y x' s f x'' y')). Qed.
Lemma lem5010319 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5010320 {A B : Type'} (x : B) (t : B -> Prop) (y : B) (x' : A) (s : A -> Prop) (f : A -> B) (x'' : A) : (term978 A B x t y x' s f x'') = (term988 A B x t y x' s f x'').
Proof. exact (MK_COMB (@lem5010319 A) (@lem5010318 A B x t y x' s f x'')). Qed.
Lemma lem5010321 {A B : Type'} (x : B) (t : B -> Prop) (y : B) (x' : A) (s : A -> Prop) (f : A -> B) (x'' : A) : ((term977 A B x t y x' s f x'') = (term978 A B x t y x' s f x'')) = ((term973 A B x t y x' s f x'') = (term988 A B x t y x' s f x'')).
Proof. exact (MK_COMB (@lem5010314 A B x t y x' s f x'') (@lem5010320 A B x t y x' s f x'')). Qed.
Lemma lem5010322 {A B : Type'} (x : B) (t : B -> Prop) (y : B) (x' : A) (s : A -> Prop) (f : A -> B) (x'' : A) : (term973 A B x t y x' s f x'') = (term988 A B x t y x' s f x'').
Proof. exact (EQ_MP (@lem5010321 A B x t y x' s f x'') (@lem5010306 A B x t y x' s f x'')). Qed.
Lemma lem5010323 {A B : Type'} (x : B) (t : B -> Prop) (y : B) (x' : A) (s : A -> Prop) (f : A -> B) : (term975 A B x t y x' s f) = (term989 A B x t y x' s f).
Proof. exact (fun_ext (fun x'' : A => @lem5010322 A B x t y x' s f x'')). Qed.
Lemma lem5010324 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5010325 {A B : Type'} (x : B) (t : B -> Prop) (y : B) (x' : A) (s : A -> Prop) (f : A -> B) : (term976 A B x t y x' s f) = (term990 A B x t y x' s f).
Proof. exact (MK_COMB (@lem5010324 A) (@lem5010323 A B x t y x' s f)). Qed.
Lemma lem5010326 {A B : Type'} (x : B) (t : B -> Prop) (y : B) (x' : A) (s : A -> Prop) (f : A -> B) : (term955 A B x t y x' s f) = (term990 A B x t y x' s f).
Proof. exact (TRANS (@lem5010302 A B x t y x' s f) (@lem5010325 A B x t y x' s f)). Qed.
Lemma lem5010327 {A B : Type'} (t : B -> Prop) (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term957 A B t y x s f) = (term991 A B t y x s f).
Proof. exact (fun_ext (fun x' : B => @lem5010326 A B x' t y x s f)). Qed.
Lemma lem5010328 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5010329 {A B : Type'} (t : B -> Prop) (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term958 A B t y x s f) = (term992 A B t y x s f).
Proof. exact (MK_COMB (@lem5010328 B) (@lem5010327 A B t y x s f)). Qed.
Lemma lem5010330 {A B : Type'} (t : B -> Prop) (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term941 A B t y x s f) = (term992 A B t y x s f).
Proof. exact (TRANS (@lem5010275 A B t y x s f) (@lem5010329 A B t y x s f)). Qed.
Lemma lem5010331 {A B : Type'} (t : B -> Prop) (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term815 A B t y x s f) = (term992 A B t y x s f).
Proof. exact (TRANS (@lem5010249 A B t y x s f) (@lem5010330 A B t y x s f)). Qed.
Lemma lem5010332 {A B : Type'} (t : B -> Prop) (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term714 A B t y x s f) = (term992 A B t y x s f).
Proof. exact (TRANS (@lem5009973 A B t y x s f) (@lem5010331 A B t y x s f)). Qed.
Lemma lem5010333 {A B : Type'} (t : B -> Prop) (y : B) (x : A) (s : A -> Prop) (f : A -> B) : (term588 A B t y x s f) = (term992 A B t y x s f).
Proof. exact (TRANS (@lem5009261 A B t y x s f) (@lem5010332 A B t y x s f)). Qed.
Lemma lem5010334 {A B : Type'} (t : B -> Prop) (y : B) (x : A) (s : A -> Prop) (f : A -> B) (h1 : term588 A B t y x s f) : term992 A B t y x s f.
Proof. exact (EQ_MP (@lem5010333 A B t y x s f) (@lem5008912 A B t y x s f h1)). Qed.
Lemma lem5010345 {A : Type'} (y : A) (f : A -> A) (x : A) (s : A -> Prop) : (term993 A y f x s) = (term994 A y f x s).
Proof. exact (@lem17045 (y = (f x)) (@IN A x s)). Qed.
Lemma lem5010348 {A : Type'} (y : A) (f : A -> A) (x : A) (s : A -> Prop) : (term495 A y f x s) = (term495 A y f x s).
Proof. exact (eq_refl (term495 A y f x s)). Qed.
Lemma lem5010349 {A : Type'} (P : A -> Prop) : (term995 A P) = (term996 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem5010350 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term997 A y f s) = (term998 A y f s).
Proof. exact (@lem5010349 A (term496 A y f s)). Qed.
Lemma lem5010351 {A : Type'} (y : A) (f : A -> A) (x : A) (s : A -> Prop) : (term999 A y f s x) = (term495 A y f x s).
Proof. exact (eq_refl (term999 A y f s x)). Qed.
Lemma lem5010352 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5010353 {A : Type'} (y : A) (f : A -> A) (x : A) (s : A -> Prop) : (term1000 A y f s x) = (term993 A y f x s).
Proof. exact (MK_COMB (@lem5010352) (@lem5010351 A y f x s)). Qed.
Lemma lem5010354 {A : Type'} (y : A) (f : A -> A) (x : A) (s : A -> Prop) : (term1000 A y f s x) = (term994 A y f x s).
Proof. exact (TRANS (@lem5010353 A y f x s) (@lem5010345 A y f x s)). Qed.
Lemma lem5010355 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term1001 A y f s) = (term1002 A y f s).
Proof. exact (fun_ext (fun x : A => @lem5010354 A y f x s)). Qed.
Lemma lem5010356 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5010357 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term998 A y f s) = (term1003 A y f s).
Proof. exact (MK_COMB (@lem5010356 A) (@lem5010355 A y f s)). Qed.
Lemma lem5010358 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term997 A y f s) = (term1003 A y f s).
Proof. exact (TRANS (@lem5010350 A y f s) (@lem5010357 A y f s)). Qed.
Lemma lem5010359 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term496 A y f s) = (term496 A y f s).
Proof. exact (fun_ext (fun x : A => @lem5010348 A y f x s)). Qed.
Lemma lem5010360 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5010361 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term497 A y f s) = (term497 A y f s).
Proof. exact (MK_COMB (@lem5010360 A) (@lem5010359 A y f s)). Qed.
Lemma lem5010363 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term1004 A y f s) = (term1004 A y f s).
Proof. exact (eq_refl (term1004 A y f s)). Qed.
Lemma lem5010364 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term1005 A y f s) = (term1005 A y f s).
Proof. exact (MK_COMB (@lem5010363 A y f s) (@lem5010361 A y f s)). Qed.
Lemma lem5010366 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term1006 A y f s) = (term1006 A y f s).
Proof. exact (eq_refl (term1006 A y f s)). Qed.
Lemma lem5010367 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term1007 A y f s) = (term1008 A y f s).
Proof. exact (MK_COMB (@lem5010366 A y f s) (@lem5010358 A y f s)). Qed.
Lemma lem5010368 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5010369 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term1009 A y f s) = (term1010 A y f s).
Proof. exact (MK_COMB (@lem5010368) (@lem5010367 A y f s)). Qed.
Lemma lem5010370 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term1011 A y f s) = (term1012 A y f s).
Proof. exact (MK_COMB (@lem5010369 A y f s) (@lem5010364 A y f s)). Qed.
Lemma lem5010371 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : ((term499 A y f s) = (term497 A y f s)) = (term1011 A y f s).
Proof. exact (@lem17784 (term499 A y f s) (term497 A y f s)). Qed.
Lemma lem5010372 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : ((term499 A y f s) = (term497 A y f s)) = (term1012 A y f s).
Proof. exact (TRANS (@lem5010371 A y f s) (@lem5010370 A y f s)). Qed.
Lemma lem5010373 {A : Type'} (y : A) (s : A -> Prop) : (term500 A y s) = (term1013 A y s).
Proof. exact (fun_ext (fun f : A -> A => @lem5010372 A y f s)). Qed.
Lemma lem5010374 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem5010375 {A : Type'} (y : A) (s : A -> Prop) : (term501 A y s) = (term1014 A y s).
Proof. exact (MK_COMB (@lem5010374 A) (@lem5010373 A y s)). Qed.
Lemma lem5010376 {A : Type'} (y : A) : (term502 A y) = (term1015 A y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5010375 A y s)). Qed.
Lemma lem5010377 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5010378 {A : Type'} (y : A) : (term503 A y) = (term1016 A y).
Proof. exact (MK_COMB (@lem5010377 A) (@lem5010376 A y)). Qed.
Lemma lem5010379 {A : Type'} : (term504 A) = (term1017 A).
Proof. exact (fun_ext (fun y : A => @lem5010378 A y)). Qed.
Lemma lem5010380 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5010381 {A : Type'} : (term432 A) = (term1018 A).
Proof. exact (MK_COMB (@lem5010380 A) (@lem5010379 A)). Qed.
Lemma lem5010391 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term1019 A P Q) = (term1020 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5010392 {A : Type'} (P : type488 A) (Q : type488 A) : (term1021 A P Q) = (term1022 A P Q).
Proof. exact (@lem5010391 (A -> A) P Q). Qed.
Lemma lem5010393 {A : Type'} (y : A) (s : A -> Prop) : (term1023 A y s) = (term1024 A y s).
Proof. exact (@lem5010392 A (term1025 A y s) (term1026 A y s)). Qed.
Lemma lem5010394 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term1027 A y s f) = (term1008 A y f s).
Proof. exact (eq_refl (term1027 A y s f)). Qed.
Lemma lem5010395 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5010396 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term1028 A y s f) = (term1010 A y f s).
Proof. exact (MK_COMB (@lem5010395) (@lem5010394 A y f s)). Qed.
Lemma lem5010397 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term1029 A y s f) = (term1005 A y f s).
Proof. exact (eq_refl (term1029 A y s f)). Qed.
Lemma lem5010398 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term1030 A y s f) = (term1012 A y f s).
Proof. exact (MK_COMB (@lem5010396 A y f s) (@lem5010397 A y f s)). Qed.
Lemma lem5010399 {A : Type'} (y : A) (s : A -> Prop) : (term1031 A y s) = (term1013 A y s).
Proof. exact (fun_ext (fun f : A -> A => @lem5010398 A y f s)). Qed.
Lemma lem5010400 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem5010401 {A : Type'} (y : A) (s : A -> Prop) : (term1023 A y s) = (term1014 A y s).
Proof. exact (MK_COMB (@lem5010400 A) (@lem5010399 A y s)). Qed.
Lemma lem5010402 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5010403 {A : Type'} (y : A) (s : A -> Prop) : (term1032 A y s) = (term1033 A y s).
Proof. exact (MK_COMB (@lem5010402) (@lem5010401 A y s)). Qed.
Lemma lem5010404 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term1027 A y s f) = (term1008 A y f s).
Proof. exact (eq_refl (term1027 A y s f)). Qed.
Lemma lem5010405 {A : Type'} (y : A) (s : A -> Prop) : (term1034 A y s) = (term1025 A y s).
Proof. exact (fun_ext (fun f : A -> A => @lem5010404 A y f s)). Qed.
Lemma lem5010406 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem5010407 {A : Type'} (y : A) (s : A -> Prop) : (term1035 A y s) = (term1036 A y s).
Proof. exact (MK_COMB (@lem5010406 A) (@lem5010405 A y s)). Qed.
Lemma lem5010408 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5010409 {A : Type'} (y : A) (s : A -> Prop) : (term1037 A y s) = (term1038 A y s).
Proof. exact (MK_COMB (@lem5010408) (@lem5010407 A y s)). Qed.
Lemma lem5010410 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term1029 A y s f) = (term1005 A y f s).
Proof. exact (eq_refl (term1029 A y s f)). Qed.
Lemma lem5010411 {A : Type'} (y : A) (s : A -> Prop) : (term1039 A y s) = (term1026 A y s).
Proof. exact (fun_ext (fun f : A -> A => @lem5010410 A y f s)). Qed.
Lemma lem5010412 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem5010413 {A : Type'} (y : A) (s : A -> Prop) : (term1040 A y s) = (term1041 A y s).
Proof. exact (MK_COMB (@lem5010412 A) (@lem5010411 A y s)). Qed.
Lemma lem5010414 {A : Type'} (y : A) (s : A -> Prop) : (term1024 A y s) = (term1042 A y s).
Proof. exact (MK_COMB (@lem5010409 A y s) (@lem5010413 A y s)). Qed.
Lemma lem5010415 {A : Type'} (y : A) (s : A -> Prop) : ((term1023 A y s) = (term1024 A y s)) = ((term1014 A y s) = (term1042 A y s)).
Proof. exact (MK_COMB (@lem5010403 A y s) (@lem5010414 A y s)). Qed.
Lemma lem5010416 {A : Type'} (y : A) (s : A -> Prop) : (term1014 A y s) = (term1042 A y s).
Proof. exact (EQ_MP (@lem5010415 A y s) (@lem5010393 A y s)). Qed.
Lemma lem5010609 {A : Type'} (y : A) : (term1015 A y) = (term1043 A y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5010416 A y s)). Qed.
Lemma lem5010610 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5010611 {A : Type'} (y : A) : (term1016 A y) = (term1044 A y).
Proof. exact (MK_COMB (@lem5010610 A) (@lem5010609 A y)). Qed.
Lemma lem5010613 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term1019 A P Q) = (term1020 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5010614 {A : Type'} (P : type686 A) (Q : type686 A) : (term1045 A P Q) = (term1046 A P Q).
Proof. exact (@lem5010613 (A -> Prop) P Q). Qed.
Lemma lem5010615 {A : Type'} (y : A) : (term1047 A y) = (term1048 A y).
Proof. exact (@lem5010614 A (term1049 A y) (term1050 A y)). Qed.
Lemma lem5010616 {A : Type'} (y : A) (s : A -> Prop) : (term1051 A y s) = (term1036 A y s).
Proof. exact (eq_refl (term1051 A y s)). Qed.
Lemma lem5010617 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5010618 {A : Type'} (y : A) (s : A -> Prop) : (term1052 A y s) = (term1038 A y s).
Proof. exact (MK_COMB (@lem5010617) (@lem5010616 A y s)). Qed.
Lemma lem5010619 {A : Type'} (y : A) (s : A -> Prop) : (term1053 A y s) = (term1041 A y s).
Proof. exact (eq_refl (term1053 A y s)). Qed.
Lemma lem5010620 {A : Type'} (y : A) (s : A -> Prop) : (term1054 A y s) = (term1042 A y s).
Proof. exact (MK_COMB (@lem5010618 A y s) (@lem5010619 A y s)). Qed.
Lemma lem5010621 {A : Type'} (y : A) : (term1055 A y) = (term1043 A y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5010620 A y s)). Qed.
Lemma lem5010622 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5010623 {A : Type'} (y : A) : (term1047 A y) = (term1044 A y).
Proof. exact (MK_COMB (@lem5010622 A) (@lem5010621 A y)). Qed.
Lemma lem5010624 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5010625 {A : Type'} (y : A) : (term1056 A y) = (term1057 A y).
Proof. exact (MK_COMB (@lem5010624) (@lem5010623 A y)). Qed.
Lemma lem5010626 {A : Type'} (y : A) (s : A -> Prop) : (term1051 A y s) = (term1036 A y s).
Proof. exact (eq_refl (term1051 A y s)). Qed.
Lemma lem5010627 {A : Type'} (y : A) : (term1058 A y) = (term1049 A y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5010626 A y s)). Qed.
Lemma lem5010628 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5010629 {A : Type'} (y : A) : (term1059 A y) = (term1060 A y).
Proof. exact (MK_COMB (@lem5010628 A) (@lem5010627 A y)). Qed.
Lemma lem5010630 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5010631 {A : Type'} (y : A) : (term1061 A y) = (term1062 A y).
Proof. exact (MK_COMB (@lem5010630) (@lem5010629 A y)). Qed.
Lemma lem5010632 {A : Type'} (y : A) (s : A -> Prop) : (term1053 A y s) = (term1041 A y s).
Proof. exact (eq_refl (term1053 A y s)). Qed.
Lemma lem5010633 {A : Type'} (y : A) : (term1063 A y) = (term1050 A y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5010632 A y s)). Qed.
Lemma lem5010634 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5010635 {A : Type'} (y : A) : (term1064 A y) = (term1065 A y).
Proof. exact (MK_COMB (@lem5010634 A) (@lem5010633 A y)). Qed.
Lemma lem5010636 {A : Type'} (y : A) : (term1048 A y) = (term1066 A y).
Proof. exact (MK_COMB (@lem5010631 A y) (@lem5010635 A y)). Qed.
Lemma lem5010637 {A : Type'} (y : A) : ((term1047 A y) = (term1048 A y)) = ((term1044 A y) = (term1066 A y)).
Proof. exact (MK_COMB (@lem5010625 A y) (@lem5010636 A y)). Qed.
Lemma lem5010638 {A : Type'} (y : A) : (term1044 A y) = (term1066 A y).
Proof. exact (EQ_MP (@lem5010637 A y) (@lem5010615 A y)). Qed.
Lemma lem5010839 {A : Type'} (y : A) : (term1016 A y) = (term1066 A y).
Proof. exact (TRANS (@lem5010611 A y) (@lem5010638 A y)). Qed.
Lemma lem5010840 {A : Type'} : (term1017 A) = (term1067 A).
Proof. exact (fun_ext (fun y : A => @lem5010839 A y)). Qed.
Lemma lem5010841 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5010842 {A : Type'} : (term1018 A) = (term1068 A).
Proof. exact (MK_COMB (@lem5010841 A) (@lem5010840 A)). Qed.
Lemma lem5010844 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term1019 A P Q) = (term1020 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5010845 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term1019 A P Q) = (term1020 A P Q).
Proof. exact (@lem5010844 A P Q). Qed.
Lemma lem5010846 {A : Type'} : (term1069 A) = (term1070 A).
Proof. exact (@lem5010845 A (term1071 A) (term1072 A)). Qed.
Lemma lem5010847 {A : Type'} (y : A) : (term1073 A y) = (term1060 A y).
Proof. exact (eq_refl (term1073 A y)). Qed.
Lemma lem5010848 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5010849 {A : Type'} (y : A) : (term1074 A y) = (term1062 A y).
Proof. exact (MK_COMB (@lem5010848) (@lem5010847 A y)). Qed.
Lemma lem5010850 {A : Type'} (y : A) : (term1075 A y) = (term1065 A y).
Proof. exact (eq_refl (term1075 A y)). Qed.
Lemma lem5010851 {A : Type'} (y : A) : (term1076 A y) = (term1066 A y).
Proof. exact (MK_COMB (@lem5010849 A y) (@lem5010850 A y)). Qed.
Lemma lem5010852 {A : Type'} : (term1077 A) = (term1067 A).
Proof. exact (fun_ext (fun y : A => @lem5010851 A y)). Qed.
Lemma lem5010853 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5010854 {A : Type'} : (term1069 A) = (term1068 A).
Proof. exact (MK_COMB (@lem5010853 A) (@lem5010852 A)). Qed.
Lemma lem5010855 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5010856 {A : Type'} : (term1078 A) = (term1079 A).
Proof. exact (MK_COMB (@lem5010855) (@lem5010854 A)). Qed.
Lemma lem5010857 {A : Type'} (y : A) : (term1073 A y) = (term1060 A y).
Proof. exact (eq_refl (term1073 A y)). Qed.
Lemma lem5010858 {A : Type'} : (term1080 A) = (term1071 A).
Proof. exact (fun_ext (fun y : A => @lem5010857 A y)). Qed.
Lemma lem5010859 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5010860 {A : Type'} : (term1081 A) = (term1082 A).
Proof. exact (MK_COMB (@lem5010859 A) (@lem5010858 A)). Qed.
Lemma lem5010861 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5010862 {A : Type'} : (term1083 A) = (term1084 A).
Proof. exact (MK_COMB (@lem5010861) (@lem5010860 A)). Qed.
Lemma lem5010863 {A : Type'} (y : A) : (term1075 A y) = (term1065 A y).
Proof. exact (eq_refl (term1075 A y)). Qed.
Lemma lem5010864 {A : Type'} : (term1085 A) = (term1072 A).
Proof. exact (fun_ext (fun y : A => @lem5010863 A y)). Qed.
Lemma lem5010865 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5010866 {A : Type'} : (term1086 A) = (term1087 A).
Proof. exact (MK_COMB (@lem5010865 A) (@lem5010864 A)). Qed.
Lemma lem5010867 {A : Type'} : (term1070 A) = (term1088 A).
Proof. exact (MK_COMB (@lem5010862 A) (@lem5010866 A)). Qed.
Lemma lem5010868 {A : Type'} : ((term1069 A) = (term1070 A)) = ((term1068 A) = (term1088 A)).
Proof. exact (MK_COMB (@lem5010856 A) (@lem5010867 A)). Qed.
Lemma lem5010869 {A : Type'} : (term1068 A) = (term1088 A).
Proof. exact (EQ_MP (@lem5010868 A) (@lem5010846 A)). Qed.
Lemma lem5011078 {A : Type'} : (term1018 A) = (term1088 A).
Proof. exact (TRANS (@lem5010842 A) (@lem5010869 A)). Qed.
Lemma lem5011080 {A : Type'} (P : Prop) (Q : A -> Prop) : (term818 A P Q) = (term819 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5011081 {A : Type'} (P : Prop) (Q : A -> Prop) : (term818 A P Q) = (term819 A P Q).
Proof. exact (@lem5011080 A P Q). Qed.
Lemma lem5011082 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term1089 A y f s) = (term1090 A y f s).
Proof. exact (@lem5011081 A (term1091 A y f s) (term496 A y f s)). Qed.
Lemma lem5011083 {A : Type'} (y : A) (f : A -> A) (x : A) (s : A -> Prop) : (term999 A y f s x) = (term495 A y f x s).
Proof. exact (eq_refl (term999 A y f s x)). Qed.
Lemma lem5011084 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term1092 A y f s) = (term496 A y f s).
Proof. exact (fun_ext (fun x : A => @lem5011083 A y f x s)). Qed.
Lemma lem5011085 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5011086 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term1093 A y f s) = (term497 A y f s).
Proof. exact (MK_COMB (@lem5011085 A) (@lem5011084 A y f s)). Qed.
Lemma lem5011087 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term1004 A y f s) = (term1004 A y f s).
Proof. exact (eq_refl (term1004 A y f s)). Qed.
Lemma lem5011088 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term1089 A y f s) = (term1005 A y f s).
Proof. exact (MK_COMB (@lem5011087 A y f s) (@lem5011086 A y f s)). Qed.
Lemma lem5011089 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5011090 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term1094 A y f s) = (term1095 A y f s).
Proof. exact (MK_COMB (@lem5011089) (@lem5011088 A y f s)). Qed.
Lemma lem5011091 {A : Type'} (y : A) (f : A -> A) (x : A) (s : A -> Prop) : (term999 A y f s x) = (term495 A y f x s).
Proof. exact (eq_refl (term999 A y f s x)). Qed.
Lemma lem5011092 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term1004 A y f s) = (term1004 A y f s).
Proof. exact (eq_refl (term1004 A y f s)). Qed.
Lemma lem5011093 {A : Type'} (y : A) (f : A -> A) (x : A) (s : A -> Prop) : (term1096 A y f s x) = (term1097 A y f x s).
Proof. exact (MK_COMB (@lem5011092 A y f s) (@lem5011091 A y f x s)). Qed.
Lemma lem5011094 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term1098 A y f s) = (term1099 A y f s).
Proof. exact (fun_ext (fun x : A => @lem5011093 A y f x s)). Qed.
Lemma lem5011095 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5011096 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term1090 A y f s) = (term1100 A y f s).
Proof. exact (MK_COMB (@lem5011095 A) (@lem5011094 A y f s)). Qed.
Lemma lem5011097 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : ((term1089 A y f s) = (term1090 A y f s)) = ((term1005 A y f s) = (term1100 A y f s)).
Proof. exact (MK_COMB (@lem5011090 A y f s) (@lem5011096 A y f s)). Qed.
Lemma lem5011098 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term1005 A y f s) = (term1100 A y f s).
Proof. exact (EQ_MP (@lem5011097 A y f s) (@lem5011082 A y f s)). Qed.
Lemma lem5011099 {A : Type'} (y : A) (s : A -> Prop) : (term1026 A y s) = (term1101 A y s).
Proof. exact (fun_ext (fun f : A -> A => @lem5011098 A y f s)). Qed.
Lemma lem5011100 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem5011101 {A : Type'} (y : A) (s : A -> Prop) : (term1041 A y s) = (term1102 A y s).
Proof. exact (MK_COMB (@lem5011100 A) (@lem5011099 A y s)). Qed.
Lemma lem5011103 {A B : Type'} (P : type1413 A B) : (term1103 A B P) = (term1104 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5011104 {A : Type'} (P : type486 A) : (term1105 A P) = (term1106 A P).
Proof. exact (@lem5011103 (A -> A) A P). Qed.
Lemma lem5011105 {A : Type'} (y : A) (s : A -> Prop) : (term1107 A y s) = (term1108 A y s).
Proof. exact (@lem5011104 A (term1109 A y s)). Qed.
Lemma lem5011106 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term1110 A y s f) = (term1099 A y f s).
Proof. exact (eq_refl (term1110 A y s f)). Qed.
Lemma lem5011107 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5011108 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) (x : A) : (term1111 A y s f x) = (term1112 A y f s x).
Proof. exact (MK_COMB (@lem5011106 A y f s) (@lem5011107 A x)). Qed.
Lemma lem5011109 {A : Type'} (y : A) (f : A -> A) (x : A) (s : A -> Prop) : (term1112 A y f s x) = (term1097 A y f x s).
Proof. exact (eq_refl (term1112 A y f s x)). Qed.
Lemma lem5011110 {A : Type'} (y : A) (f : A -> A) (x : A) (s : A -> Prop) : (term1111 A y s f x) = (term1097 A y f x s).
Proof. exact (TRANS (@lem5011108 A y f s x) (@lem5011109 A y f x s)). Qed.
Lemma lem5011111 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term1113 A y s f) = (term1099 A y f s).
Proof. exact (fun_ext (fun x : A => @lem5011110 A y f x s)). Qed.
Lemma lem5011112 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5011113 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term1114 A y s f) = (term1100 A y f s).
Proof. exact (MK_COMB (@lem5011112 A) (@lem5011111 A y f s)). Qed.
Lemma lem5011114 {A : Type'} (y : A) (s : A -> Prop) : (term1115 A y s) = (term1101 A y s).
Proof. exact (fun_ext (fun f : A -> A => @lem5011113 A y f s)). Qed.
Lemma lem5011115 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem5011116 {A : Type'} (y : A) (s : A -> Prop) : (term1107 A y s) = (term1102 A y s).
Proof. exact (MK_COMB (@lem5011115 A) (@lem5011114 A y s)). Qed.
Lemma lem5011117 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5011118 {A : Type'} (y : A) (s : A -> Prop) : (term1116 A y s) = (term1117 A y s).
Proof. exact (MK_COMB (@lem5011117) (@lem5011116 A y s)). Qed.
Lemma lem5011119 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term1110 A y s f) = (term1099 A y f s).
Proof. exact (eq_refl (term1110 A y s f)). Qed.
Lemma lem5011120 {A : Type'} (x : type487 A) (f : A -> A) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem5011121 {A : Type'} (y : A) (s : A -> Prop) (x : type487 A) (f : A -> A) : (term1118 A y s x f) = (term1119 A y s x f).
Proof. exact (MK_COMB (@lem5011119 A y f s) (@lem5011120 A x f)). Qed.
Lemma lem5011122 {A : Type'} (y : A) (x : type487 A) (f : A -> A) (s : A -> Prop) : (term1119 A y s x f) = (term1120 A y x f s).
Proof. exact (eq_refl (term1119 A y s x f)). Qed.
Lemma lem5011123 {A : Type'} (y : A) (x : type487 A) (f : A -> A) (s : A -> Prop) : (term1118 A y s x f) = (term1120 A y x f s).
Proof. exact (TRANS (@lem5011121 A y s x f) (@lem5011122 A y x f s)). Qed.
Lemma lem5011124 {A : Type'} (y : A) (x : type487 A) (s : A -> Prop) : (term1121 A y s x) = (term1122 A y x s).
Proof. exact (fun_ext (fun f : A -> A => @lem5011123 A y x f s)). Qed.
Lemma lem5011125 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem5011126 {A : Type'} (y : A) (x : type487 A) (s : A -> Prop) : (term1123 A y s x) = (term1124 A y x s).
Proof. exact (MK_COMB (@lem5011125 A) (@lem5011124 A y x s)). Qed.
Lemma lem5011127 {A : Type'} (y : A) (s : A -> Prop) : (term1125 A y s) = (term1126 A y s).
Proof. exact (fun_ext (fun x : type487 A => @lem5011126 A y x s)). Qed.
Lemma lem5011128 {A : Type'} : (@ex ((A -> A) -> A)) = (@ex ((A -> A) -> A)).
Proof. exact (eq_refl (@ex ((A -> A) -> A))). Qed.
Lemma lem5011129 {A : Type'} (y : A) (s : A -> Prop) : (term1108 A y s) = (term1127 A y s).
Proof. exact (MK_COMB (@lem5011128 A) (@lem5011127 A y s)). Qed.
Lemma lem5011130 {A : Type'} (y : A) (s : A -> Prop) : ((term1107 A y s) = (term1108 A y s)) = ((term1102 A y s) = (term1127 A y s)).
Proof. exact (MK_COMB (@lem5011118 A y s) (@lem5011129 A y s)). Qed.
Lemma lem5011131 {A : Type'} (y : A) (s : A -> Prop) : (term1102 A y s) = (term1127 A y s).
Proof. exact (EQ_MP (@lem5011130 A y s) (@lem5011105 A y s)). Qed.
Lemma lem5011132 {A : Type'} (y : A) (s : A -> Prop) : (term1041 A y s) = (term1127 A y s).
Proof. exact (TRANS (@lem5011101 A y s) (@lem5011131 A y s)). Qed.
Lemma lem5011133 {A : Type'} (y : A) : (term1050 A y) = (term1128 A y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5011132 A y s)). Qed.
Lemma lem5011134 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5011135 {A : Type'} (y : A) : (term1065 A y) = (term1129 A y).
Proof. exact (MK_COMB (@lem5011134 A) (@lem5011133 A y)). Qed.
Lemma lem5011137 {A B : Type'} (P : type1413 A B) : (term1103 A B P) = (term1104 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5011138 {A : Type'} (P : type587 A) : (term1130 A P) = (term1131 A P).
Proof. exact (@lem5011137 (A -> Prop) (type487 A) P). Qed.
Lemma lem5011139 {A : Type'} (y : A) : (term1132 A y) = (term1133 A y).
Proof. exact (@lem5011138 A (term1134 A y)). Qed.
Lemma lem5011140 {A : Type'} (y : A) (s : A -> Prop) : (term1135 A y s) = (term1126 A y s).
Proof. exact (eq_refl (term1135 A y s)). Qed.
Lemma lem5011141 {A : Type'} (x : type487 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5011142 {A : Type'} (y : A) (s : A -> Prop) (x : type487 A) : (term1136 A y s x) = (term1137 A y s x).
Proof. exact (MK_COMB (@lem5011140 A y s) (@lem5011141 A x)). Qed.
Lemma lem5011143 {A : Type'} (y : A) (x : type487 A) (s : A -> Prop) : (term1137 A y s x) = (term1124 A y x s).
Proof. exact (eq_refl (term1137 A y s x)). Qed.
Lemma lem5011144 {A : Type'} (y : A) (x : type487 A) (s : A -> Prop) : (term1136 A y s x) = (term1124 A y x s).
Proof. exact (TRANS (@lem5011142 A y s x) (@lem5011143 A y x s)). Qed.
Lemma lem5011145 {A : Type'} (y : A) (s : A -> Prop) : (term1138 A y s) = (term1126 A y s).
Proof. exact (fun_ext (fun x : type487 A => @lem5011144 A y x s)). Qed.
Lemma lem5011146 {A : Type'} : (@ex ((A -> A) -> A)) = (@ex ((A -> A) -> A)).
Proof. exact (eq_refl (@ex ((A -> A) -> A))). Qed.
Lemma lem5011147 {A : Type'} (y : A) (s : A -> Prop) : (term1139 A y s) = (term1127 A y s).
Proof. exact (MK_COMB (@lem5011146 A) (@lem5011145 A y s)). Qed.
Lemma lem5011148 {A : Type'} (y : A) : (term1140 A y) = (term1128 A y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5011147 A y s)). Qed.
Lemma lem5011149 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5011150 {A : Type'} (y : A) : (term1132 A y) = (term1129 A y).
Proof. exact (MK_COMB (@lem5011149 A) (@lem5011148 A y)). Qed.
Lemma lem5011151 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5011152 {A : Type'} (y : A) : (term1141 A y) = (term1142 A y).
Proof. exact (MK_COMB (@lem5011151) (@lem5011150 A y)). Qed.
Lemma lem5011153 {A : Type'} (y : A) (s : A -> Prop) : (term1135 A y s) = (term1126 A y s).
Proof. exact (eq_refl (term1135 A y s)). Qed.
Lemma lem5011154 {A : Type'} (x : type623 A) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem5011155 {A : Type'} (y : A) (x : type623 A) (s : A -> Prop) : (term1143 A y x s) = (term1144 A y x s).
Proof. exact (MK_COMB (@lem5011153 A y s) (@lem5011154 A x s)). Qed.
Lemma lem5011156 {A : Type'} (y : A) (x : type623 A) (s : A -> Prop) : (term1144 A y x s) = (term1145 A y x s).
Proof. exact (eq_refl (term1144 A y x s)). Qed.
Lemma lem5011157 {A : Type'} (y : A) (x : type623 A) (s : A -> Prop) : (term1143 A y x s) = (term1145 A y x s).
Proof. exact (TRANS (@lem5011155 A y x s) (@lem5011156 A y x s)). Qed.
Lemma lem5011158 {A : Type'} (y : A) (x : type623 A) : (term1146 A y x) = (term1147 A y x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5011157 A y x s)). Qed.
Lemma lem5011159 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5011160 {A : Type'} (y : A) (x : type623 A) : (term1148 A y x) = (term1149 A y x).
Proof. exact (MK_COMB (@lem5011159 A) (@lem5011158 A y x)). Qed.
Lemma lem5011161 {A : Type'} (y : A) : (term1150 A y) = (term1151 A y).
Proof. exact (fun_ext (fun x : type623 A => @lem5011160 A y x)). Qed.
Lemma lem5011162 {A : Type'} : (@ex ((A -> Prop) -> (A -> A) -> A)) = (@ex ((A -> Prop) -> (A -> A) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> A) -> A))). Qed.
Lemma lem5011163 {A : Type'} (y : A) : (term1133 A y) = (term1152 A y).
Proof. exact (MK_COMB (@lem5011162 A) (@lem5011161 A y)). Qed.
Lemma lem5011164 {A : Type'} (y : A) : ((term1132 A y) = (term1133 A y)) = ((term1129 A y) = (term1152 A y)).
Proof. exact (MK_COMB (@lem5011152 A y) (@lem5011163 A y)). Qed.
Lemma lem5011165 {A : Type'} (y : A) : (term1129 A y) = (term1152 A y).
Proof. exact (EQ_MP (@lem5011164 A y) (@lem5011139 A y)). Qed.
Lemma lem5011166 {A : Type'} (y : A) : (term1065 A y) = (term1152 A y).
Proof. exact (TRANS (@lem5011135 A y) (@lem5011165 A y)). Qed.
Lemma lem5011167 {A : Type'} : (term1072 A) = (term1153 A).
Proof. exact (fun_ext (fun y : A => @lem5011166 A y)). Qed.
Lemma lem5011168 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5011169 {A : Type'} : (term1087 A) = (term1154 A).
Proof. exact (MK_COMB (@lem5011168 A) (@lem5011167 A)). Qed.
Lemma lem5011171 {A B : Type'} (P : type1413 A B) : (term1103 A B P) = (term1104 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5011172 {A : Type'} (P : type1356 A) : (term1155 A P) = (term1156 A P).
Proof. exact (@lem5011171 A (type623 A) P). Qed.
Lemma lem5011173 {A : Type'} : (term1157 A) = (term1158 A).
Proof. exact (@lem5011172 A (term1159 A)). Qed.
Lemma lem5011174 {A : Type'} (y : A) : (term1160 A y) = (term1151 A y).
Proof. exact (eq_refl (term1160 A y)). Qed.
Lemma lem5011175 {A : Type'} (x : type623 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5011176 {A : Type'} (y : A) (x : type623 A) : (term1161 A y x) = (term1162 A y x).
Proof. exact (MK_COMB (@lem5011174 A y) (@lem5011175 A x)). Qed.
Lemma lem5011177 {A : Type'} (y : A) (x : type623 A) : (term1162 A y x) = (term1149 A y x).
Proof. exact (eq_refl (term1162 A y x)). Qed.
Lemma lem5011178 {A : Type'} (y : A) (x : type623 A) : (term1161 A y x) = (term1149 A y x).
Proof. exact (TRANS (@lem5011176 A y x) (@lem5011177 A y x)). Qed.
Lemma lem5011179 {A : Type'} (y : A) : (term1163 A y) = (term1151 A y).
Proof. exact (fun_ext (fun x : type623 A => @lem5011178 A y x)). Qed.
Lemma lem5011180 {A : Type'} : (@ex ((A -> Prop) -> (A -> A) -> A)) = (@ex ((A -> Prop) -> (A -> A) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> A) -> A))). Qed.
Lemma lem5011181 {A : Type'} (y : A) : (term1164 A y) = (term1152 A y).
Proof. exact (MK_COMB (@lem5011180 A) (@lem5011179 A y)). Qed.
Lemma lem5011182 {A : Type'} : (term1165 A) = (term1153 A).
Proof. exact (fun_ext (fun y : A => @lem5011181 A y)). Qed.
Lemma lem5011183 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5011184 {A : Type'} : (term1157 A) = (term1154 A).
Proof. exact (MK_COMB (@lem5011183 A) (@lem5011182 A)). Qed.
Lemma lem5011185 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5011186 {A : Type'} : (term1166 A) = (term1167 A).
Proof. exact (MK_COMB (@lem5011185) (@lem5011184 A)). Qed.
Lemma lem5011187 {A : Type'} (y : A) : (term1160 A y) = (term1151 A y).
Proof. exact (eq_refl (term1160 A y)). Qed.
Lemma lem5011188 {A : Type'} (x : type1361 A) (y : A) : (x y) = (x y).
Proof. exact (eq_refl (x y)). Qed.
Lemma lem5011189 {A : Type'} (x : type1361 A) (y : A) : (term1168 A x y) = (term1169 A x y).
Proof. exact (MK_COMB (@lem5011187 A y) (@lem5011188 A x y)). Qed.
Lemma lem5011190 {A : Type'} (x : type1361 A) (y : A) : (term1169 A x y) = (term1170 A x y).
Proof. exact (eq_refl (term1169 A x y)). Qed.
Lemma lem5011191 {A : Type'} (x : type1361 A) (y : A) : (term1168 A x y) = (term1170 A x y).
Proof. exact (TRANS (@lem5011189 A x y) (@lem5011190 A x y)). Qed.
Lemma lem5011192 {A : Type'} (x : type1361 A) : (term1171 A x) = (term1172 A x).
Proof. exact (fun_ext (fun y : A => @lem5011191 A x y)). Qed.
Lemma lem5011193 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5011194 {A : Type'} (x : type1361 A) : (term1173 A x) = (term1174 A x).
Proof. exact (MK_COMB (@lem5011193 A) (@lem5011192 A x)). Qed.
Lemma lem5011195 {A : Type'} : (term1175 A) = (term1176 A).
Proof. exact (fun_ext (fun x : type1361 A => @lem5011194 A x)). Qed.
Lemma lem5011196 {A : Type'} : (@ex (A -> (A -> Prop) -> (A -> A) -> A)) = (@ex (A -> (A -> Prop) -> (A -> A) -> A)).
Proof. exact (eq_refl (@ex (A -> (A -> Prop) -> (A -> A) -> A))). Qed.
Lemma lem5011197 {A : Type'} : (term1158 A) = (term1177 A).
Proof. exact (MK_COMB (@lem5011196 A) (@lem5011195 A)). Qed.
Lemma lem5011198 {A : Type'} : ((term1157 A) = (term1158 A)) = ((term1154 A) = (term1177 A)).
Proof. exact (MK_COMB (@lem5011186 A) (@lem5011197 A)). Qed.
Lemma lem5011199 {A : Type'} : (term1154 A) = (term1177 A).
Proof. exact (EQ_MP (@lem5011198 A) (@lem5011173 A)). Qed.
Lemma lem5011200 {A : Type'} : (term1087 A) = (term1177 A).
Proof. exact (TRANS (@lem5011169 A) (@lem5011199 A)). Qed.
Lemma lem5011201 {A : Type'} : (term1084 A) = (term1084 A).
Proof. exact (eq_refl (term1084 A)). Qed.
Lemma lem5011202 {A : Type'} : (term1088 A) = (term1178 A).
Proof. exact (MK_COMB (@lem5011201 A) (@lem5011200 A)). Qed.
Lemma lem5011204 {A : Type'} (P : Prop) (Q : A -> Prop) : (term856 A P Q) = (term857 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5011205 {A : Type'} (P : Prop) (Q : type391 A) : (term1179 A P Q) = (term1180 A P Q).
Proof. exact (@lem5011204 (type1361 A) P Q). Qed.
Lemma lem5011206 {A : Type'} : (term1181 A) = (term1182 A).
Proof. exact (@lem5011205 A (term1082 A) (term1176 A)). Qed.
Lemma lem5011207 {A : Type'} (x : type1361 A) : (term1183 A x) = (term1174 A x).
Proof. exact (eq_refl (term1183 A x)). Qed.
Lemma lem5011208 {A : Type'} : (term1184 A) = (term1176 A).
Proof. exact (fun_ext (fun x : type1361 A => @lem5011207 A x)). Qed.
Lemma lem5011209 {A : Type'} : (@ex (A -> (A -> Prop) -> (A -> A) -> A)) = (@ex (A -> (A -> Prop) -> (A -> A) -> A)).
Proof. exact (eq_refl (@ex (A -> (A -> Prop) -> (A -> A) -> A))). Qed.
Lemma lem5011210 {A : Type'} : (term1185 A) = (term1177 A).
Proof. exact (MK_COMB (@lem5011209 A) (@lem5011208 A)). Qed.
Lemma lem5011211 {A : Type'} : (term1084 A) = (term1084 A).
Proof. exact (eq_refl (term1084 A)). Qed.
Lemma lem5011212 {A : Type'} : (term1181 A) = (term1178 A).
Proof. exact (MK_COMB (@lem5011211 A) (@lem5011210 A)). Qed.
Lemma lem5011213 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5011214 {A : Type'} : (term1186 A) = (term1187 A).
Proof. exact (MK_COMB (@lem5011213) (@lem5011212 A)). Qed.
Lemma lem5011215 {A : Type'} (x : type1361 A) : (term1183 A x) = (term1174 A x).
Proof. exact (eq_refl (term1183 A x)). Qed.
Lemma lem5011216 {A : Type'} : (term1084 A) = (term1084 A).
Proof. exact (eq_refl (term1084 A)). Qed.
Lemma lem5011217 {A : Type'} (x : type1361 A) : (term1188 A x) = (term1189 A x).
Proof. exact (MK_COMB (@lem5011216 A) (@lem5011215 A x)). Qed.
Lemma lem5011218 {A : Type'} : (term1190 A) = (term1191 A).
Proof. exact (fun_ext (fun x : type1361 A => @lem5011217 A x)). Qed.
Lemma lem5011219 {A : Type'} : (@ex (A -> (A -> Prop) -> (A -> A) -> A)) = (@ex (A -> (A -> Prop) -> (A -> A) -> A)).
Proof. exact (eq_refl (@ex (A -> (A -> Prop) -> (A -> A) -> A))). Qed.
Lemma lem5011220 {A : Type'} : (term1182 A) = (term1192 A).
Proof. exact (MK_COMB (@lem5011219 A) (@lem5011218 A)). Qed.
Lemma lem5011221 {A : Type'} : ((term1181 A) = (term1182 A)) = ((term1178 A) = (term1192 A)).
Proof. exact (MK_COMB (@lem5011214 A) (@lem5011220 A)). Qed.
Lemma lem5011222 {A : Type'} : (term1178 A) = (term1192 A).
Proof. exact (EQ_MP (@lem5011221 A) (@lem5011206 A)). Qed.
Lemma lem5011223 {A : Type'} : (term1088 A) = (term1192 A).
Proof. exact (TRANS (@lem5011202 A) (@lem5011222 A)). Qed.
Lemma lem5011224 {A : Type'} : (term1018 A) = (term1192 A).
Proof. exact (TRANS (@lem5011078 A) (@lem5011223 A)). Qed.
Lemma lem5011225 {A : Type'} : (term432 A) = (term1192 A).
Proof. exact (TRANS (@lem5010381 A) (@lem5011224 A)). Qed.
Lemma lem5011226 {A : Type'} (h1 : term432 A) : term1192 A.
Proof. exact (EQ_MP (@lem5011225 A) (@lem5008913 A h1)). Qed.
Lemma lem5011237 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term1193 A B y f x s) = (term1194 A B y f x s).
Proof. exact (@lem17045 (y = (f x)) (@IN A x s)). Qed.
Lemma lem5011240 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term505 A B y f x s) = (term505 A B y f x s).
Proof. exact (eq_refl (term505 A B y f x s)). Qed.
Lemma lem5011241 {A : Type'} (P : A -> Prop) : (term995 A P) = (term996 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem5011242 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1195 A B y f s) = (term1196 A B y f s).
Proof. exact (@lem5011241 A (term506 A B y f s)). Qed.
Lemma lem5011243 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term1197 A B y f s x) = (term505 A B y f x s).
Proof. exact (eq_refl (term1197 A B y f s x)). Qed.
Lemma lem5011244 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5011245 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term1198 A B y f s x) = (term1193 A B y f x s).
Proof. exact (MK_COMB (@lem5011244) (@lem5011243 A B y f x s)). Qed.
Lemma lem5011246 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term1198 A B y f s x) = (term1194 A B y f x s).
Proof. exact (TRANS (@lem5011245 A B y f x s) (@lem5011237 A B y f x s)). Qed.
Lemma lem5011247 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1199 A B y f s) = (term1200 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem5011246 A B y f x s)). Qed.
Lemma lem5011248 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5011249 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1196 A B y f s) = (term1201 A B y f s).
Proof. exact (MK_COMB (@lem5011248 A) (@lem5011247 A B y f s)). Qed.
Lemma lem5011250 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1195 A B y f s) = (term1201 A B y f s).
Proof. exact (TRANS (@lem5011242 A B y f s) (@lem5011249 A B y f s)). Qed.
Lemma lem5011251 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term506 A B y f s) = (term506 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem5011240 A B y f x s)). Qed.
Lemma lem5011252 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5011253 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term6 A B y f s) = (term6 A B y f s).
Proof. exact (MK_COMB (@lem5011252 A) (@lem5011251 A B y f s)). Qed.
Lemma lem5011255 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1202 A B y f s) = (term1202 A B y f s).
Proof. exact (eq_refl (term1202 A B y f s)). Qed.
Lemma lem5011256 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1203 A B y f s) = (term1203 A B y f s).
Proof. exact (MK_COMB (@lem5011255 A B y f s) (@lem5011253 A B y f s)). Qed.
Lemma lem5011258 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1204 A B y f s) = (term1204 A B y f s).
Proof. exact (eq_refl (term1204 A B y f s)). Qed.
Lemma lem5011259 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1205 A B y f s) = (term1206 A B y f s).
Proof. exact (MK_COMB (@lem5011258 A B y f s) (@lem5011250 A B y f s)). Qed.
Lemma lem5011260 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5011261 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1207 A B y f s) = (term1208 A B y f s).
Proof. exact (MK_COMB (@lem5011260) (@lem5011259 A B y f s)). Qed.
Lemma lem5011262 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1209 A B y f s) = (term1210 A B y f s).
Proof. exact (MK_COMB (@lem5011261 A B y f s) (@lem5011256 A B y f s)). Qed.
Lemma lem5011263 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : ((term5 A B y f s) = (term6 A B y f s)) = (term1209 A B y f s).
Proof. exact (@lem17784 (term5 A B y f s) (term6 A B y f s)). Qed.
Lemma lem5011264 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : ((term5 A B y f s) = (term6 A B y f s)) = (term1210 A B y f s).
Proof. exact (TRANS (@lem5011263 A B y f s) (@lem5011262 A B y f s)). Qed.
Lemma lem5011265 {A B : Type'} (y : B) (s : A -> Prop) : (term508 A B y s) = (term1211 A B y s).
Proof. exact (fun_ext (fun f : A -> B => @lem5011264 A B y f s)). Qed.
Lemma lem5011266 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5011267 {A B : Type'} (y : B) (s : A -> Prop) : (term3 A B y s) = (term1212 A B y s).
Proof. exact (MK_COMB (@lem5011266 A B) (@lem5011265 A B y s)). Qed.
Lemma lem5011268 {A B : Type'} (y : B) : (term509 A B y) = (term1213 A B y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5011267 A B y s)). Qed.
Lemma lem5011269 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5011270 {A B : Type'} (y : B) : (term1 A B y) = (term1214 A B y).
Proof. exact (MK_COMB (@lem5011269 A) (@lem5011268 A B y)). Qed.
Lemma lem5011271 {A B : Type'} : (term510 A B) = (term1215 A B).
Proof. exact (fun_ext (fun y : B => @lem5011270 A B y)). Qed.
Lemma lem5011272 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5011273 {A B : Type'} : (term433 A B) = (term1216 A B).
Proof. exact (MK_COMB (@lem5011272 B) (@lem5011271 A B)). Qed.
Lemma lem5011283 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term1019 A P Q) = (term1020 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5011284 {A B : Type'} (P : type572 A B) (Q : type572 A B) : (term1217 A B P Q) = (term1218 A B P Q).
Proof. exact (@lem5011283 (A -> B) P Q). Qed.
Lemma lem5011285 {A B : Type'} (y : B) (s : A -> Prop) : (term1219 A B y s) = (term1220 A B y s).
Proof. exact (@lem5011284 A B (term1221 A B y s) (term1222 A B y s)). Qed.
Lemma lem5011286 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1223 A B y s f) = (term1206 A B y f s).
Proof. exact (eq_refl (term1223 A B y s f)). Qed.
Lemma lem5011287 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5011288 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1224 A B y s f) = (term1208 A B y f s).
Proof. exact (MK_COMB (@lem5011287) (@lem5011286 A B y f s)). Qed.
Lemma lem5011289 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1225 A B y s f) = (term1203 A B y f s).
Proof. exact (eq_refl (term1225 A B y s f)). Qed.
Lemma lem5011290 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1226 A B y s f) = (term1210 A B y f s).
Proof. exact (MK_COMB (@lem5011288 A B y f s) (@lem5011289 A B y f s)). Qed.
Lemma lem5011291 {A B : Type'} (y : B) (s : A -> Prop) : (term1227 A B y s) = (term1211 A B y s).
Proof. exact (fun_ext (fun f : A -> B => @lem5011290 A B y f s)). Qed.
Lemma lem5011292 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5011293 {A B : Type'} (y : B) (s : A -> Prop) : (term1219 A B y s) = (term1212 A B y s).
Proof. exact (MK_COMB (@lem5011292 A B) (@lem5011291 A B y s)). Qed.
Lemma lem5011294 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5011295 {A B : Type'} (y : B) (s : A -> Prop) : (term1228 A B y s) = (term1229 A B y s).
Proof. exact (MK_COMB (@lem5011294) (@lem5011293 A B y s)). Qed.
Lemma lem5011296 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1223 A B y s f) = (term1206 A B y f s).
Proof. exact (eq_refl (term1223 A B y s f)). Qed.
Lemma lem5011297 {A B : Type'} (y : B) (s : A -> Prop) : (term1230 A B y s) = (term1221 A B y s).
Proof. exact (fun_ext (fun f : A -> B => @lem5011296 A B y f s)). Qed.
Lemma lem5011298 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5011299 {A B : Type'} (y : B) (s : A -> Prop) : (term1231 A B y s) = (term1232 A B y s).
Proof. exact (MK_COMB (@lem5011298 A B) (@lem5011297 A B y s)). Qed.
Lemma lem5011300 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5011301 {A B : Type'} (y : B) (s : A -> Prop) : (term1233 A B y s) = (term1234 A B y s).
Proof. exact (MK_COMB (@lem5011300) (@lem5011299 A B y s)). Qed.
Lemma lem5011302 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1225 A B y s f) = (term1203 A B y f s).
Proof. exact (eq_refl (term1225 A B y s f)). Qed.
Lemma lem5011303 {A B : Type'} (y : B) (s : A -> Prop) : (term1235 A B y s) = (term1222 A B y s).
Proof. exact (fun_ext (fun f : A -> B => @lem5011302 A B y f s)). Qed.
Lemma lem5011304 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5011305 {A B : Type'} (y : B) (s : A -> Prop) : (term1236 A B y s) = (term1237 A B y s).
Proof. exact (MK_COMB (@lem5011304 A B) (@lem5011303 A B y s)). Qed.
Lemma lem5011306 {A B : Type'} (y : B) (s : A -> Prop) : (term1220 A B y s) = (term1238 A B y s).
Proof. exact (MK_COMB (@lem5011301 A B y s) (@lem5011305 A B y s)). Qed.
Lemma lem5011307 {A B : Type'} (y : B) (s : A -> Prop) : ((term1219 A B y s) = (term1220 A B y s)) = ((term1212 A B y s) = (term1238 A B y s)).
Proof. exact (MK_COMB (@lem5011295 A B y s) (@lem5011306 A B y s)). Qed.
Lemma lem5011308 {A B : Type'} (y : B) (s : A -> Prop) : (term1212 A B y s) = (term1238 A B y s).
Proof. exact (EQ_MP (@lem5011307 A B y s) (@lem5011285 A B y s)). Qed.
Lemma lem5011501 {A B : Type'} (y : B) : (term1213 A B y) = (term1239 A B y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5011308 A B y s)). Qed.
Lemma lem5011502 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5011503 {A B : Type'} (y : B) : (term1214 A B y) = (term1240 A B y).
Proof. exact (MK_COMB (@lem5011502 A) (@lem5011501 A B y)). Qed.
Lemma lem5011505 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term1019 A P Q) = (term1020 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5011506 {A : Type'} (P : type686 A) (Q : type686 A) : (term1045 A P Q) = (term1046 A P Q).
Proof. exact (@lem5011505 (A -> Prop) P Q). Qed.
Lemma lem5011507 {A B : Type'} (y : B) : (term1241 A B y) = (term1242 A B y).
Proof. exact (@lem5011506 A (term1243 A B y) (term1244 A B y)). Qed.
Lemma lem5011508 {A B : Type'} (y : B) (s : A -> Prop) : (term1245 A B y s) = (term1232 A B y s).
Proof. exact (eq_refl (term1245 A B y s)). Qed.
Lemma lem5011509 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5011510 {A B : Type'} (y : B) (s : A -> Prop) : (term1246 A B y s) = (term1234 A B y s).
Proof. exact (MK_COMB (@lem5011509) (@lem5011508 A B y s)). Qed.
Lemma lem5011511 {A B : Type'} (y : B) (s : A -> Prop) : (term1247 A B y s) = (term1237 A B y s).
Proof. exact (eq_refl (term1247 A B y s)). Qed.
Lemma lem5011512 {A B : Type'} (y : B) (s : A -> Prop) : (term1248 A B y s) = (term1238 A B y s).
Proof. exact (MK_COMB (@lem5011510 A B y s) (@lem5011511 A B y s)). Qed.
Lemma lem5011513 {A B : Type'} (y : B) : (term1249 A B y) = (term1239 A B y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5011512 A B y s)). Qed.
Lemma lem5011514 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5011515 {A B : Type'} (y : B) : (term1241 A B y) = (term1240 A B y).
Proof. exact (MK_COMB (@lem5011514 A) (@lem5011513 A B y)). Qed.
Lemma lem5011516 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5011517 {A B : Type'} (y : B) : (term1250 A B y) = (term1251 A B y).
Proof. exact (MK_COMB (@lem5011516) (@lem5011515 A B y)). Qed.
Lemma lem5011518 {A B : Type'} (y : B) (s : A -> Prop) : (term1245 A B y s) = (term1232 A B y s).
Proof. exact (eq_refl (term1245 A B y s)). Qed.
Lemma lem5011519 {A B : Type'} (y : B) : (term1252 A B y) = (term1243 A B y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5011518 A B y s)). Qed.
Lemma lem5011520 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5011521 {A B : Type'} (y : B) : (term1253 A B y) = (term1254 A B y).
Proof. exact (MK_COMB (@lem5011520 A) (@lem5011519 A B y)). Qed.
Lemma lem5011522 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5011523 {A B : Type'} (y : B) : (term1255 A B y) = (term1256 A B y).
Proof. exact (MK_COMB (@lem5011522) (@lem5011521 A B y)). Qed.
Lemma lem5011524 {A B : Type'} (y : B) (s : A -> Prop) : (term1247 A B y s) = (term1237 A B y s).
Proof. exact (eq_refl (term1247 A B y s)). Qed.
Lemma lem5011525 {A B : Type'} (y : B) : (term1257 A B y) = (term1244 A B y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5011524 A B y s)). Qed.
Lemma lem5011526 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5011527 {A B : Type'} (y : B) : (term1258 A B y) = (term1259 A B y).
Proof. exact (MK_COMB (@lem5011526 A) (@lem5011525 A B y)). Qed.
Lemma lem5011528 {A B : Type'} (y : B) : (term1242 A B y) = (term1260 A B y).
Proof. exact (MK_COMB (@lem5011523 A B y) (@lem5011527 A B y)). Qed.
Lemma lem5011529 {A B : Type'} (y : B) : ((term1241 A B y) = (term1242 A B y)) = ((term1240 A B y) = (term1260 A B y)).
Proof. exact (MK_COMB (@lem5011517 A B y) (@lem5011528 A B y)). Qed.
Lemma lem5011530 {A B : Type'} (y : B) : (term1240 A B y) = (term1260 A B y).
Proof. exact (EQ_MP (@lem5011529 A B y) (@lem5011507 A B y)). Qed.
Lemma lem5011731 {A B : Type'} (y : B) : (term1214 A B y) = (term1260 A B y).
Proof. exact (TRANS (@lem5011503 A B y) (@lem5011530 A B y)). Qed.
Lemma lem5011732 {A B : Type'} : (term1215 A B) = (term1261 A B).
Proof. exact (fun_ext (fun y : B => @lem5011731 A B y)). Qed.
Lemma lem5011733 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5011734 {A B : Type'} : (term1216 A B) = (term1262 A B).
Proof. exact (MK_COMB (@lem5011733 B) (@lem5011732 A B)). Qed.
Lemma lem5011736 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term1019 A P Q) = (term1020 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5011737 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term1019 B P Q) = (term1020 B P Q).
Proof. exact (@lem5011736 B P Q). Qed.
Lemma lem5011738 {A B : Type'} : (term1263 A B) = (term1264 A B).
Proof. exact (@lem5011737 B (term1265 A B) (term1266 A B)). Qed.
Lemma lem5011739 {A B : Type'} (y : B) : (term1267 A B y) = (term1254 A B y).
Proof. exact (eq_refl (term1267 A B y)). Qed.
Lemma lem5011740 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5011741 {A B : Type'} (y : B) : (term1268 A B y) = (term1256 A B y).
Proof. exact (MK_COMB (@lem5011740) (@lem5011739 A B y)). Qed.
Lemma lem5011742 {A B : Type'} (y : B) : (term1269 A B y) = (term1259 A B y).
Proof. exact (eq_refl (term1269 A B y)). Qed.
Lemma lem5011743 {A B : Type'} (y : B) : (term1270 A B y) = (term1260 A B y).
Proof. exact (MK_COMB (@lem5011741 A B y) (@lem5011742 A B y)). Qed.
Lemma lem5011744 {A B : Type'} : (term1271 A B) = (term1261 A B).
Proof. exact (fun_ext (fun y : B => @lem5011743 A B y)). Qed.
Lemma lem5011745 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5011746 {A B : Type'} : (term1263 A B) = (term1262 A B).
Proof. exact (MK_COMB (@lem5011745 B) (@lem5011744 A B)). Qed.
Lemma lem5011747 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5011748 {A B : Type'} : (term1272 A B) = (term1273 A B).
Proof. exact (MK_COMB (@lem5011747) (@lem5011746 A B)). Qed.
Lemma lem5011749 {A B : Type'} (y : B) : (term1267 A B y) = (term1254 A B y).
Proof. exact (eq_refl (term1267 A B y)). Qed.
Lemma lem5011750 {A B : Type'} : (term1274 A B) = (term1265 A B).
Proof. exact (fun_ext (fun y : B => @lem5011749 A B y)). Qed.
Lemma lem5011751 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5011752 {A B : Type'} : (term1275 A B) = (term1276 A B).
Proof. exact (MK_COMB (@lem5011751 B) (@lem5011750 A B)). Qed.
Lemma lem5011753 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5011754 {A B : Type'} : (term1277 A B) = (term1278 A B).
Proof. exact (MK_COMB (@lem5011753) (@lem5011752 A B)). Qed.
Lemma lem5011755 {A B : Type'} (y : B) : (term1269 A B y) = (term1259 A B y).
Proof. exact (eq_refl (term1269 A B y)). Qed.
Lemma lem5011756 {A B : Type'} : (term1279 A B) = (term1266 A B).
Proof. exact (fun_ext (fun y : B => @lem5011755 A B y)). Qed.
Lemma lem5011757 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5011758 {A B : Type'} : (term1280 A B) = (term1281 A B).
Proof. exact (MK_COMB (@lem5011757 B) (@lem5011756 A B)). Qed.
Lemma lem5011759 {A B : Type'} : (term1264 A B) = (term1282 A B).
Proof. exact (MK_COMB (@lem5011754 A B) (@lem5011758 A B)). Qed.
Lemma lem5011760 {A B : Type'} : ((term1263 A B) = (term1264 A B)) = ((term1262 A B) = (term1282 A B)).
Proof. exact (MK_COMB (@lem5011748 A B) (@lem5011759 A B)). Qed.
Lemma lem5011761 {A B : Type'} : (term1262 A B) = (term1282 A B).
Proof. exact (EQ_MP (@lem5011760 A B) (@lem5011738 A B)). Qed.
Lemma lem5011970 {A B : Type'} : (term1216 A B) = (term1282 A B).
Proof. exact (TRANS (@lem5011734 A B) (@lem5011761 A B)). Qed.
Lemma lem5011972 {A : Type'} (P : Prop) (Q : A -> Prop) : (term818 A P Q) = (term819 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5011973 {A : Type'} (P : Prop) (Q : A -> Prop) : (term818 A P Q) = (term819 A P Q).
Proof. exact (@lem5011972 A P Q). Qed.
Lemma lem5011974 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1283 A B y f s) = (term1284 A B y f s).
Proof. exact (@lem5011973 A (term1285 A B y f s) (term506 A B y f s)). Qed.
Lemma lem5011975 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term1197 A B y f s x) = (term505 A B y f x s).
Proof. exact (eq_refl (term1197 A B y f s x)). Qed.
Lemma lem5011976 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1286 A B y f s) = (term506 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem5011975 A B y f x s)). Qed.
Lemma lem5011977 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5011978 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1287 A B y f s) = (term6 A B y f s).
Proof. exact (MK_COMB (@lem5011977 A) (@lem5011976 A B y f s)). Qed.
Lemma lem5011979 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1202 A B y f s) = (term1202 A B y f s).
Proof. exact (eq_refl (term1202 A B y f s)). Qed.
Lemma lem5011980 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1283 A B y f s) = (term1203 A B y f s).
Proof. exact (MK_COMB (@lem5011979 A B y f s) (@lem5011978 A B y f s)). Qed.
Lemma lem5011981 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5011982 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1288 A B y f s) = (term1289 A B y f s).
Proof. exact (MK_COMB (@lem5011981) (@lem5011980 A B y f s)). Qed.
Lemma lem5011983 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term1197 A B y f s x) = (term505 A B y f x s).
Proof. exact (eq_refl (term1197 A B y f s x)). Qed.
Lemma lem5011984 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1202 A B y f s) = (term1202 A B y f s).
Proof. exact (eq_refl (term1202 A B y f s)). Qed.
Lemma lem5011985 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term1290 A B y f s x) = (term1291 A B y f x s).
Proof. exact (MK_COMB (@lem5011984 A B y f s) (@lem5011983 A B y f x s)). Qed.
Lemma lem5011986 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1292 A B y f s) = (term1293 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem5011985 A B y f x s)). Qed.
Lemma lem5011987 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5011988 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1284 A B y f s) = (term1294 A B y f s).
Proof. exact (MK_COMB (@lem5011987 A) (@lem5011986 A B y f s)). Qed.
Lemma lem5011989 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : ((term1283 A B y f s) = (term1284 A B y f s)) = ((term1203 A B y f s) = (term1294 A B y f s)).
Proof. exact (MK_COMB (@lem5011982 A B y f s) (@lem5011988 A B y f s)). Qed.
Lemma lem5011990 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1203 A B y f s) = (term1294 A B y f s).
Proof. exact (EQ_MP (@lem5011989 A B y f s) (@lem5011974 A B y f s)). Qed.
Lemma lem5011991 {A B : Type'} (y : B) (s : A -> Prop) : (term1222 A B y s) = (term1295 A B y s).
Proof. exact (fun_ext (fun f : A -> B => @lem5011990 A B y f s)). Qed.
Lemma lem5011992 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5011993 {A B : Type'} (y : B) (s : A -> Prop) : (term1237 A B y s) = (term1296 A B y s).
Proof. exact (MK_COMB (@lem5011992 A B) (@lem5011991 A B y s)). Qed.
Lemma lem5011995 {A B : Type'} (P : type1413 A B) : (term1103 A B P) = (term1104 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5011996 {A B : Type'} (P : type551 A B) : (term1297 A B P) = (term1298 A B P).
Proof. exact (@lem5011995 (A -> B) A P). Qed.
Lemma lem5011997 {A B : Type'} (y : B) (s : A -> Prop) : (term1299 A B y s) = (term1300 A B y s).
Proof. exact (@lem5011996 A B (term1301 A B y s)). Qed.
Lemma lem5011998 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1302 A B y s f) = (term1293 A B y f s).
Proof. exact (eq_refl (term1302 A B y s f)). Qed.
Lemma lem5011999 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5012000 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) : (term1303 A B y s f x) = (term1304 A B y f s x).
Proof. exact (MK_COMB (@lem5011998 A B y f s) (@lem5011999 A x)). Qed.
Lemma lem5012001 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term1304 A B y f s x) = (term1291 A B y f x s).
Proof. exact (eq_refl (term1304 A B y f s x)). Qed.
Lemma lem5012002 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term1303 A B y s f x) = (term1291 A B y f x s).
Proof. exact (TRANS (@lem5012000 A B y f s x) (@lem5012001 A B y f x s)). Qed.
Lemma lem5012003 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1305 A B y s f) = (term1293 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem5012002 A B y f x s)). Qed.
Lemma lem5012004 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5012005 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1306 A B y s f) = (term1294 A B y f s).
Proof. exact (MK_COMB (@lem5012004 A) (@lem5012003 A B y f s)). Qed.
Lemma lem5012006 {A B : Type'} (y : B) (s : A -> Prop) : (term1307 A B y s) = (term1295 A B y s).
Proof. exact (fun_ext (fun f : A -> B => @lem5012005 A B y f s)). Qed.
Lemma lem5012007 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5012008 {A B : Type'} (y : B) (s : A -> Prop) : (term1299 A B y s) = (term1296 A B y s).
Proof. exact (MK_COMB (@lem5012007 A B) (@lem5012006 A B y s)). Qed.
Lemma lem5012009 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5012010 {A B : Type'} (y : B) (s : A -> Prop) : (term1308 A B y s) = (term1309 A B y s).
Proof. exact (MK_COMB (@lem5012009) (@lem5012008 A B y s)). Qed.
Lemma lem5012011 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1302 A B y s f) = (term1293 A B y f s).
Proof. exact (eq_refl (term1302 A B y s f)). Qed.
Lemma lem5012012 {A B : Type'} (x : type569 A B) (f : A -> B) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem5012013 {A B : Type'} (y : B) (s : A -> Prop) (x : type569 A B) (f : A -> B) : (term1310 A B y s x f) = (term1311 A B y s x f).
Proof. exact (MK_COMB (@lem5012011 A B y f s) (@lem5012012 A B x f)). Qed.
Lemma lem5012014 {A B : Type'} (y : B) (x : type569 A B) (f : A -> B) (s : A -> Prop) : (term1311 A B y s x f) = (term1312 A B y x f s).
Proof. exact (eq_refl (term1311 A B y s x f)). Qed.
Lemma lem5012015 {A B : Type'} (y : B) (x : type569 A B) (f : A -> B) (s : A -> Prop) : (term1310 A B y s x f) = (term1312 A B y x f s).
Proof. exact (TRANS (@lem5012013 A B y s x f) (@lem5012014 A B y x f s)). Qed.
Lemma lem5012016 {A B : Type'} (y : B) (x : type569 A B) (s : A -> Prop) : (term1313 A B y s x) = (term1314 A B y x s).
Proof. exact (fun_ext (fun f : A -> B => @lem5012015 A B y x f s)). Qed.
Lemma lem5012017 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5012018 {A B : Type'} (y : B) (x : type569 A B) (s : A -> Prop) : (term1315 A B y s x) = (term1316 A B y x s).
Proof. exact (MK_COMB (@lem5012017 A B) (@lem5012016 A B y x s)). Qed.
Lemma lem5012019 {A B : Type'} (y : B) (s : A -> Prop) : (term1317 A B y s) = (term1318 A B y s).
Proof. exact (fun_ext (fun x : type569 A B => @lem5012018 A B y x s)). Qed.
Lemma lem5012020 {A B : Type'} : (@ex ((A -> B) -> A)) = (@ex ((A -> B) -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> A))). Qed.
Lemma lem5012021 {A B : Type'} (y : B) (s : A -> Prop) : (term1300 A B y s) = (term1319 A B y s).
Proof. exact (MK_COMB (@lem5012020 A B) (@lem5012019 A B y s)). Qed.
Lemma lem5012022 {A B : Type'} (y : B) (s : A -> Prop) : ((term1299 A B y s) = (term1300 A B y s)) = ((term1296 A B y s) = (term1319 A B y s)).
Proof. exact (MK_COMB (@lem5012010 A B y s) (@lem5012021 A B y s)). Qed.
Lemma lem5012023 {A B : Type'} (y : B) (s : A -> Prop) : (term1296 A B y s) = (term1319 A B y s).
Proof. exact (EQ_MP (@lem5012022 A B y s) (@lem5011997 A B y s)). Qed.
Lemma lem5012024 {A B : Type'} (y : B) (s : A -> Prop) : (term1237 A B y s) = (term1319 A B y s).
Proof. exact (TRANS (@lem5011993 A B y s) (@lem5012023 A B y s)). Qed.
Lemma lem5012025 {A B : Type'} (y : B) : (term1244 A B y) = (term1320 A B y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5012024 A B y s)). Qed.
Lemma lem5012026 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5012027 {A B : Type'} (y : B) : (term1259 A B y) = (term1321 A B y).
Proof. exact (MK_COMB (@lem5012026 A) (@lem5012025 A B y)). Qed.
Lemma lem5012029 {A B : Type'} (P : type1413 A B) : (term1103 A B P) = (term1104 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5012030 {A B : Type'} (P : type593 A B) : (term1322 A B P) = (term1323 A B P).
Proof. exact (@lem5012029 (A -> Prop) (type569 A B) P). Qed.
Lemma lem5012031 {A B : Type'} (y : B) : (term1324 A B y) = (term1325 A B y).
Proof. exact (@lem5012030 A B (term1326 A B y)). Qed.
Lemma lem5012032 {A B : Type'} (y : B) (s : A -> Prop) : (term1327 A B y s) = (term1318 A B y s).
Proof. exact (eq_refl (term1327 A B y s)). Qed.
Lemma lem5012033 {A B : Type'} (x : type569 A B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5012034 {A B : Type'} (y : B) (s : A -> Prop) (x : type569 A B) : (term1328 A B y s x) = (term1329 A B y s x).
Proof. exact (MK_COMB (@lem5012032 A B y s) (@lem5012033 A B x)). Qed.
Lemma lem5012035 {A B : Type'} (y : B) (x : type569 A B) (s : A -> Prop) : (term1329 A B y s x) = (term1316 A B y x s).
Proof. exact (eq_refl (term1329 A B y s x)). Qed.
Lemma lem5012036 {A B : Type'} (y : B) (x : type569 A B) (s : A -> Prop) : (term1328 A B y s x) = (term1316 A B y x s).
Proof. exact (TRANS (@lem5012034 A B y s x) (@lem5012035 A B y x s)). Qed.
Lemma lem5012037 {A B : Type'} (y : B) (s : A -> Prop) : (term1330 A B y s) = (term1318 A B y s).
Proof. exact (fun_ext (fun x : type569 A B => @lem5012036 A B y x s)). Qed.
Lemma lem5012038 {A B : Type'} : (@ex ((A -> B) -> A)) = (@ex ((A -> B) -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> A))). Qed.
Lemma lem5012039 {A B : Type'} (y : B) (s : A -> Prop) : (term1331 A B y s) = (term1319 A B y s).
Proof. exact (MK_COMB (@lem5012038 A B) (@lem5012037 A B y s)). Qed.
Lemma lem5012040 {A B : Type'} (y : B) : (term1332 A B y) = (term1320 A B y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5012039 A B y s)). Qed.
Lemma lem5012041 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5012042 {A B : Type'} (y : B) : (term1324 A B y) = (term1321 A B y).
Proof. exact (MK_COMB (@lem5012041 A) (@lem5012040 A B y)). Qed.
Lemma lem5012043 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5012044 {A B : Type'} (y : B) : (term1333 A B y) = (term1334 A B y).
Proof. exact (MK_COMB (@lem5012043) (@lem5012042 A B y)). Qed.
Lemma lem5012045 {A B : Type'} (y : B) (s : A -> Prop) : (term1327 A B y s) = (term1318 A B y s).
Proof. exact (eq_refl (term1327 A B y s)). Qed.
Lemma lem5012046 {A B : Type'} (x : type631 A B) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem5012047 {A B : Type'} (y : B) (x : type631 A B) (s : A -> Prop) : (term1335 A B y x s) = (term1336 A B y x s).
Proof. exact (MK_COMB (@lem5012045 A B y s) (@lem5012046 A B x s)). Qed.
Lemma lem5012048 {A B : Type'} (y : B) (x : type631 A B) (s : A -> Prop) : (term1336 A B y x s) = (term1337 A B y x s).
Proof. exact (eq_refl (term1336 A B y x s)). Qed.
Lemma lem5012049 {A B : Type'} (y : B) (x : type631 A B) (s : A -> Prop) : (term1335 A B y x s) = (term1337 A B y x s).
Proof. exact (TRANS (@lem5012047 A B y x s) (@lem5012048 A B y x s)). Qed.
Lemma lem5012050 {A B : Type'} (y : B) (x : type631 A B) : (term1338 A B y x) = (term1339 A B y x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5012049 A B y x s)). Qed.
Lemma lem5012051 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5012052 {A B : Type'} (y : B) (x : type631 A B) : (term1340 A B y x) = (term1341 A B y x).
Proof. exact (MK_COMB (@lem5012051 A) (@lem5012050 A B y x)). Qed.
Lemma lem5012053 {A B : Type'} (y : B) : (term1342 A B y) = (term1343 A B y).
Proof. exact (fun_ext (fun x : type631 A B => @lem5012052 A B y x)). Qed.
Lemma lem5012054 {A B : Type'} : (@ex ((A -> Prop) -> (A -> B) -> A)) = (@ex ((A -> Prop) -> (A -> B) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> B) -> A))). Qed.
Lemma lem5012055 {A B : Type'} (y : B) : (term1325 A B y) = (term1344 A B y).
Proof. exact (MK_COMB (@lem5012054 A B) (@lem5012053 A B y)). Qed.
Lemma lem5012056 {A B : Type'} (y : B) : ((term1324 A B y) = (term1325 A B y)) = ((term1321 A B y) = (term1344 A B y)).
Proof. exact (MK_COMB (@lem5012044 A B y) (@lem5012055 A B y)). Qed.
Lemma lem5012057 {A B : Type'} (y : B) : (term1321 A B y) = (term1344 A B y).
Proof. exact (EQ_MP (@lem5012056 A B y) (@lem5012031 A B y)). Qed.
Lemma lem5012058 {A B : Type'} (y : B) : (term1259 A B y) = (term1344 A B y).
Proof. exact (TRANS (@lem5012027 A B y) (@lem5012057 A B y)). Qed.
Lemma lem5012059 {A B : Type'} : (term1266 A B) = (term1345 A B).
Proof. exact (fun_ext (fun y : B => @lem5012058 A B y)). Qed.
Lemma lem5012060 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5012061 {A B : Type'} : (term1281 A B) = (term1346 A B).
Proof. exact (MK_COMB (@lem5012060 B) (@lem5012059 A B)). Qed.
Lemma lem5012063 {A B : Type'} (P : type1413 A B) : (term1103 A B P) = (term1104 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5012064 {A B : Type'} (P : type1437 A B) : (term1347 A B P) = (term1348 A B P).
Proof. exact (@lem5012063 B (type631 A B) P). Qed.
Lemma lem5012065 {A B : Type'} : (term1349 A B) = (term1350 A B).
Proof. exact (@lem5012064 A B (term1351 A B)). Qed.
Lemma lem5012066 {A B : Type'} (y : B) : (term1352 A B y) = (term1343 A B y).
Proof. exact (eq_refl (term1352 A B y)). Qed.
Lemma lem5012067 {A B : Type'} (x : type631 A B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5012068 {A B : Type'} (y : B) (x : type631 A B) : (term1353 A B y x) = (term1354 A B y x).
Proof. exact (MK_COMB (@lem5012066 A B y) (@lem5012067 A B x)). Qed.
Lemma lem5012069 {A B : Type'} (y : B) (x : type631 A B) : (term1354 A B y x) = (term1341 A B y x).
Proof. exact (eq_refl (term1354 A B y x)). Qed.
Lemma lem5012070 {A B : Type'} (y : B) (x : type631 A B) : (term1353 A B y x) = (term1341 A B y x).
Proof. exact (TRANS (@lem5012068 A B y x) (@lem5012069 A B y x)). Qed.
Lemma lem5012071 {A B : Type'} (y : B) : (term1355 A B y) = (term1343 A B y).
Proof. exact (fun_ext (fun x : type631 A B => @lem5012070 A B y x)). Qed.
Lemma lem5012072 {A B : Type'} : (@ex ((A -> Prop) -> (A -> B) -> A)) = (@ex ((A -> Prop) -> (A -> B) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> B) -> A))). Qed.
Lemma lem5012073 {A B : Type'} (y : B) : (term1356 A B y) = (term1344 A B y).
Proof. exact (MK_COMB (@lem5012072 A B) (@lem5012071 A B y)). Qed.
Lemma lem5012074 {A B : Type'} : (term1357 A B) = (term1345 A B).
Proof. exact (fun_ext (fun y : B => @lem5012073 A B y)). Qed.
Lemma lem5012075 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5012076 {A B : Type'} : (term1349 A B) = (term1346 A B).
Proof. exact (MK_COMB (@lem5012075 B) (@lem5012074 A B)). Qed.
Lemma lem5012077 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5012078 {A B : Type'} : (term1358 A B) = (term1359 A B).
Proof. exact (MK_COMB (@lem5012077) (@lem5012076 A B)). Qed.
Lemma lem5012079 {A B : Type'} (y : B) : (term1352 A B y) = (term1343 A B y).
Proof. exact (eq_refl (term1352 A B y)). Qed.
Lemma lem5012080 {A B : Type'} (x : type1448 A B) (y : B) : (x y) = (x y).
Proof. exact (eq_refl (x y)). Qed.
Lemma lem5012081 {A B : Type'} (x : type1448 A B) (y : B) : (term1360 A B x y) = (term1361 A B x y).
Proof. exact (MK_COMB (@lem5012079 A B y) (@lem5012080 A B x y)). Qed.
Lemma lem5012082 {A B : Type'} (x : type1448 A B) (y : B) : (term1361 A B x y) = (term1362 A B x y).
Proof. exact (eq_refl (term1361 A B x y)). Qed.
Lemma lem5012083 {A B : Type'} (x : type1448 A B) (y : B) : (term1360 A B x y) = (term1362 A B x y).
Proof. exact (TRANS (@lem5012081 A B x y) (@lem5012082 A B x y)). Qed.
Lemma lem5012084 {A B : Type'} (x : type1448 A B) : (term1363 A B x) = (term1364 A B x).
Proof. exact (fun_ext (fun y : B => @lem5012083 A B x y)). Qed.
Lemma lem5012085 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5012086 {A B : Type'} (x : type1448 A B) : (term1365 A B x) = (term1366 A B x).
Proof. exact (MK_COMB (@lem5012085 B) (@lem5012084 A B x)). Qed.
Lemma lem5012087 {A B : Type'} : (term1367 A B) = (term1368 A B).
Proof. exact (fun_ext (fun x : type1448 A B => @lem5012086 A B x)). Qed.
Lemma lem5012088 {A B : Type'} : (@ex (B -> (A -> Prop) -> (A -> B) -> A)) = (@ex (B -> (A -> Prop) -> (A -> B) -> A)).
Proof. exact (eq_refl (@ex (B -> (A -> Prop) -> (A -> B) -> A))). Qed.
Lemma lem5012089 {A B : Type'} : (term1350 A B) = (term1369 A B).
Proof. exact (MK_COMB (@lem5012088 A B) (@lem5012087 A B)). Qed.
Lemma lem5012090 {A B : Type'} : ((term1349 A B) = (term1350 A B)) = ((term1346 A B) = (term1369 A B)).
Proof. exact (MK_COMB (@lem5012078 A B) (@lem5012089 A B)). Qed.
Lemma lem5012091 {A B : Type'} : (term1346 A B) = (term1369 A B).
Proof. exact (EQ_MP (@lem5012090 A B) (@lem5012065 A B)). Qed.
Lemma lem5012092 {A B : Type'} : (term1281 A B) = (term1369 A B).
Proof. exact (TRANS (@lem5012061 A B) (@lem5012091 A B)). Qed.
Lemma lem5012093 {A B : Type'} : (term1278 A B) = (term1278 A B).
Proof. exact (eq_refl (term1278 A B)). Qed.
Lemma lem5012094 {A B : Type'} : (term1282 A B) = (term1370 A B).
Proof. exact (MK_COMB (@lem5012093 A B) (@lem5012092 A B)). Qed.
Lemma lem5012096 {A : Type'} (P : Prop) (Q : A -> Prop) : (term856 A P Q) = (term857 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5012097 {A B : Type'} (P : Prop) (Q : type719 A B) : (term1371 A B P Q) = (term1372 A B P Q).
Proof. exact (@lem5012096 (type1448 A B) P Q). Qed.
Lemma lem5012098 {A B : Type'} : (term1373 A B) = (term1374 A B).
Proof. exact (@lem5012097 A B (term1276 A B) (term1368 A B)). Qed.
Lemma lem5012099 {A B : Type'} (x : type1448 A B) : (term1375 A B x) = (term1366 A B x).
Proof. exact (eq_refl (term1375 A B x)). Qed.
Lemma lem5012100 {A B : Type'} : (term1376 A B) = (term1368 A B).
Proof. exact (fun_ext (fun x : type1448 A B => @lem5012099 A B x)). Qed.
Lemma lem5012101 {A B : Type'} : (@ex (B -> (A -> Prop) -> (A -> B) -> A)) = (@ex (B -> (A -> Prop) -> (A -> B) -> A)).
Proof. exact (eq_refl (@ex (B -> (A -> Prop) -> (A -> B) -> A))). Qed.
Lemma lem5012102 {A B : Type'} : (term1377 A B) = (term1369 A B).
Proof. exact (MK_COMB (@lem5012101 A B) (@lem5012100 A B)). Qed.
Lemma lem5012103 {A B : Type'} : (term1278 A B) = (term1278 A B).
Proof. exact (eq_refl (term1278 A B)). Qed.
Lemma lem5012104 {A B : Type'} : (term1373 A B) = (term1370 A B).
Proof. exact (MK_COMB (@lem5012103 A B) (@lem5012102 A B)). Qed.
Lemma lem5012105 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5012106 {A B : Type'} : (term1378 A B) = (term1379 A B).
Proof. exact (MK_COMB (@lem5012105) (@lem5012104 A B)). Qed.
Lemma lem5012107 {A B : Type'} (x : type1448 A B) : (term1375 A B x) = (term1366 A B x).
Proof. exact (eq_refl (term1375 A B x)). Qed.
Lemma lem5012108 {A B : Type'} : (term1278 A B) = (term1278 A B).
Proof. exact (eq_refl (term1278 A B)). Qed.
Lemma lem5012109 {A B : Type'} (x : type1448 A B) : (term1380 A B x) = (term1381 A B x).
Proof. exact (MK_COMB (@lem5012108 A B) (@lem5012107 A B x)). Qed.
Lemma lem5012110 {A B : Type'} : (term1382 A B) = (term1383 A B).
Proof. exact (fun_ext (fun x : type1448 A B => @lem5012109 A B x)). Qed.
Lemma lem5012111 {A B : Type'} : (@ex (B -> (A -> Prop) -> (A -> B) -> A)) = (@ex (B -> (A -> Prop) -> (A -> B) -> A)).
Proof. exact (eq_refl (@ex (B -> (A -> Prop) -> (A -> B) -> A))). Qed.
Lemma lem5012112 {A B : Type'} : (term1374 A B) = (term1384 A B).
Proof. exact (MK_COMB (@lem5012111 A B) (@lem5012110 A B)). Qed.
Lemma lem5012113 {A B : Type'} : ((term1373 A B) = (term1374 A B)) = ((term1370 A B) = (term1384 A B)).
Proof. exact (MK_COMB (@lem5012106 A B) (@lem5012112 A B)). Qed.
Lemma lem5012114 {A B : Type'} : (term1370 A B) = (term1384 A B).
Proof. exact (EQ_MP (@lem5012113 A B) (@lem5012098 A B)). Qed.
Lemma lem5012115 {A B : Type'} : (term1282 A B) = (term1384 A B).
Proof. exact (TRANS (@lem5012094 A B) (@lem5012114 A B)). Qed.
Lemma lem5012116 {A B : Type'} : (term1216 A B) = (term1384 A B).
Proof. exact (TRANS (@lem5011970 A B) (@lem5012115 A B)). Qed.
Lemma lem5012117 {A B : Type'} : (term433 A B) = (term1384 A B).
Proof. exact (TRANS (@lem5011273 A B) (@lem5012116 A B)). Qed.
Lemma lem5012118 {A B : Type'} (h1 : term433 A B) : term1384 A B.
Proof. exact (EQ_MP (@lem5012117 A B) (@lem5008914 A B h1)). Qed.
Lemma lem5012129 {B : Type'} (y : B) (f : B -> B) (x : B) (s : B -> Prop) : (term993 B y f x s) = (term994 B y f x s).
Proof. exact (@lem17045 (y = (f x)) (@IN B x s)). Qed.
Lemma lem5012132 {B : Type'} (y : B) (f : B -> B) (x : B) (s : B -> Prop) : (term495 B y f x s) = (term495 B y f x s).
Proof. exact (eq_refl (term495 B y f x s)). Qed.
Lemma lem5012133 {B : Type'} (P : B -> Prop) : (term995 B P) = (term996 B P).
Proof. exact (@lem18394 B P). Qed.
Lemma lem5012134 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term997 B y f s) = (term998 B y f s).
Proof. exact (@lem5012133 B (term496 B y f s)). Qed.
Lemma lem5012135 {B : Type'} (y : B) (f : B -> B) (x : B) (s : B -> Prop) : (term999 B y f s x) = (term495 B y f x s).
Proof. exact (eq_refl (term999 B y f s x)). Qed.
Lemma lem5012136 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5012137 {B : Type'} (y : B) (f : B -> B) (x : B) (s : B -> Prop) : (term1000 B y f s x) = (term993 B y f x s).
Proof. exact (MK_COMB (@lem5012136) (@lem5012135 B y f x s)). Qed.
Lemma lem5012138 {B : Type'} (y : B) (f : B -> B) (x : B) (s : B -> Prop) : (term1000 B y f s x) = (term994 B y f x s).
Proof. exact (TRANS (@lem5012137 B y f x s) (@lem5012129 B y f x s)). Qed.
Lemma lem5012139 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term1001 B y f s) = (term1002 B y f s).
Proof. exact (fun_ext (fun x : B => @lem5012138 B y f x s)). Qed.
Lemma lem5012140 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5012141 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term998 B y f s) = (term1003 B y f s).
Proof. exact (MK_COMB (@lem5012140 B) (@lem5012139 B y f s)). Qed.
Lemma lem5012142 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term997 B y f s) = (term1003 B y f s).
Proof. exact (TRANS (@lem5012134 B y f s) (@lem5012141 B y f s)). Qed.
Lemma lem5012143 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term496 B y f s) = (term496 B y f s).
Proof. exact (fun_ext (fun x : B => @lem5012132 B y f x s)). Qed.
Lemma lem5012144 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5012145 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term497 B y f s) = (term497 B y f s).
Proof. exact (MK_COMB (@lem5012144 B) (@lem5012143 B y f s)). Qed.
Lemma lem5012147 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term1004 B y f s) = (term1004 B y f s).
Proof. exact (eq_refl (term1004 B y f s)). Qed.
Lemma lem5012148 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term1005 B y f s) = (term1005 B y f s).
Proof. exact (MK_COMB (@lem5012147 B y f s) (@lem5012145 B y f s)). Qed.
Lemma lem5012150 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term1006 B y f s) = (term1006 B y f s).
Proof. exact (eq_refl (term1006 B y f s)). Qed.
Lemma lem5012151 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term1007 B y f s) = (term1008 B y f s).
Proof. exact (MK_COMB (@lem5012150 B y f s) (@lem5012142 B y f s)). Qed.
Lemma lem5012152 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5012153 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term1009 B y f s) = (term1010 B y f s).
Proof. exact (MK_COMB (@lem5012152) (@lem5012151 B y f s)). Qed.
Lemma lem5012154 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term1011 B y f s) = (term1012 B y f s).
Proof. exact (MK_COMB (@lem5012153 B y f s) (@lem5012148 B y f s)). Qed.
Lemma lem5012155 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : ((term499 B y f s) = (term497 B y f s)) = (term1011 B y f s).
Proof. exact (@lem17784 (term499 B y f s) (term497 B y f s)). Qed.
Lemma lem5012156 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : ((term499 B y f s) = (term497 B y f s)) = (term1012 B y f s).
Proof. exact (TRANS (@lem5012155 B y f s) (@lem5012154 B y f s)). Qed.
Lemma lem5012157 {B : Type'} (y : B) (s : B -> Prop) : (term500 B y s) = (term1013 B y s).
Proof. exact (fun_ext (fun f : B -> B => @lem5012156 B y f s)). Qed.
Lemma lem5012158 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem5012159 {B : Type'} (y : B) (s : B -> Prop) : (term501 B y s) = (term1014 B y s).
Proof. exact (MK_COMB (@lem5012158 B) (@lem5012157 B y s)). Qed.
Lemma lem5012160 {B : Type'} (y : B) : (term502 B y) = (term1015 B y).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5012159 B y s)). Qed.
Lemma lem5012161 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5012162 {B : Type'} (y : B) : (term503 B y) = (term1016 B y).
Proof. exact (MK_COMB (@lem5012161 B) (@lem5012160 B y)). Qed.
Lemma lem5012163 {B : Type'} : (term504 B) = (term1017 B).
Proof. exact (fun_ext (fun y : B => @lem5012162 B y)). Qed.
Lemma lem5012164 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5012165 {B : Type'} : (term432 B) = (term1018 B).
Proof. exact (MK_COMB (@lem5012164 B) (@lem5012163 B)). Qed.
Lemma lem5012175 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term1019 A P Q) = (term1020 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5012176 {B : Type'} (P : type488 B) (Q : type488 B) : (term1021 B P Q) = (term1022 B P Q).
Proof. exact (@lem5012175 (B -> B) P Q). Qed.
Lemma lem5012177 {B : Type'} (y : B) (s : B -> Prop) : (term1023 B y s) = (term1024 B y s).
Proof. exact (@lem5012176 B (term1025 B y s) (term1026 B y s)). Qed.
Lemma lem5012178 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term1027 B y s f) = (term1008 B y f s).
Proof. exact (eq_refl (term1027 B y s f)). Qed.
Lemma lem5012179 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5012180 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term1028 B y s f) = (term1010 B y f s).
Proof. exact (MK_COMB (@lem5012179) (@lem5012178 B y f s)). Qed.
Lemma lem5012181 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term1029 B y s f) = (term1005 B y f s).
Proof. exact (eq_refl (term1029 B y s f)). Qed.
Lemma lem5012182 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term1030 B y s f) = (term1012 B y f s).
Proof. exact (MK_COMB (@lem5012180 B y f s) (@lem5012181 B y f s)). Qed.
Lemma lem5012183 {B : Type'} (y : B) (s : B -> Prop) : (term1031 B y s) = (term1013 B y s).
Proof. exact (fun_ext (fun f : B -> B => @lem5012182 B y f s)). Qed.
Lemma lem5012184 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem5012185 {B : Type'} (y : B) (s : B -> Prop) : (term1023 B y s) = (term1014 B y s).
Proof. exact (MK_COMB (@lem5012184 B) (@lem5012183 B y s)). Qed.
Lemma lem5012186 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5012187 {B : Type'} (y : B) (s : B -> Prop) : (term1032 B y s) = (term1033 B y s).
Proof. exact (MK_COMB (@lem5012186) (@lem5012185 B y s)). Qed.
Lemma lem5012188 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term1027 B y s f) = (term1008 B y f s).
Proof. exact (eq_refl (term1027 B y s f)). Qed.
Lemma lem5012189 {B : Type'} (y : B) (s : B -> Prop) : (term1034 B y s) = (term1025 B y s).
Proof. exact (fun_ext (fun f : B -> B => @lem5012188 B y f s)). Qed.
Lemma lem5012190 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem5012191 {B : Type'} (y : B) (s : B -> Prop) : (term1035 B y s) = (term1036 B y s).
Proof. exact (MK_COMB (@lem5012190 B) (@lem5012189 B y s)). Qed.
Lemma lem5012192 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5012193 {B : Type'} (y : B) (s : B -> Prop) : (term1037 B y s) = (term1038 B y s).
Proof. exact (MK_COMB (@lem5012192) (@lem5012191 B y s)). Qed.
Lemma lem5012194 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term1029 B y s f) = (term1005 B y f s).
Proof. exact (eq_refl (term1029 B y s f)). Qed.
Lemma lem5012195 {B : Type'} (y : B) (s : B -> Prop) : (term1039 B y s) = (term1026 B y s).
Proof. exact (fun_ext (fun f : B -> B => @lem5012194 B y f s)). Qed.
Lemma lem5012196 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem5012197 {B : Type'} (y : B) (s : B -> Prop) : (term1040 B y s) = (term1041 B y s).
Proof. exact (MK_COMB (@lem5012196 B) (@lem5012195 B y s)). Qed.
Lemma lem5012198 {B : Type'} (y : B) (s : B -> Prop) : (term1024 B y s) = (term1042 B y s).
Proof. exact (MK_COMB (@lem5012193 B y s) (@lem5012197 B y s)). Qed.
Lemma lem5012199 {B : Type'} (y : B) (s : B -> Prop) : ((term1023 B y s) = (term1024 B y s)) = ((term1014 B y s) = (term1042 B y s)).
Proof. exact (MK_COMB (@lem5012187 B y s) (@lem5012198 B y s)). Qed.
Lemma lem5012200 {B : Type'} (y : B) (s : B -> Prop) : (term1014 B y s) = (term1042 B y s).
Proof. exact (EQ_MP (@lem5012199 B y s) (@lem5012177 B y s)). Qed.
Lemma lem5012393 {B : Type'} (y : B) : (term1015 B y) = (term1043 B y).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5012200 B y s)). Qed.
Lemma lem5012394 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5012395 {B : Type'} (y : B) : (term1016 B y) = (term1044 B y).
Proof. exact (MK_COMB (@lem5012394 B) (@lem5012393 B y)). Qed.
Lemma lem5012397 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term1019 A P Q) = (term1020 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5012398 {B : Type'} (P : type686 B) (Q : type686 B) : (term1045 B P Q) = (term1046 B P Q).
Proof. exact (@lem5012397 (B -> Prop) P Q). Qed.
Lemma lem5012399 {B : Type'} (y : B) : (term1047 B y) = (term1048 B y).
Proof. exact (@lem5012398 B (term1049 B y) (term1050 B y)). Qed.
Lemma lem5012400 {B : Type'} (y : B) (s : B -> Prop) : (term1051 B y s) = (term1036 B y s).
Proof. exact (eq_refl (term1051 B y s)). Qed.
Lemma lem5012401 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5012402 {B : Type'} (y : B) (s : B -> Prop) : (term1052 B y s) = (term1038 B y s).
Proof. exact (MK_COMB (@lem5012401) (@lem5012400 B y s)). Qed.
Lemma lem5012403 {B : Type'} (y : B) (s : B -> Prop) : (term1053 B y s) = (term1041 B y s).
Proof. exact (eq_refl (term1053 B y s)). Qed.
Lemma lem5012404 {B : Type'} (y : B) (s : B -> Prop) : (term1054 B y s) = (term1042 B y s).
Proof. exact (MK_COMB (@lem5012402 B y s) (@lem5012403 B y s)). Qed.
Lemma lem5012405 {B : Type'} (y : B) : (term1055 B y) = (term1043 B y).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5012404 B y s)). Qed.
Lemma lem5012406 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5012407 {B : Type'} (y : B) : (term1047 B y) = (term1044 B y).
Proof. exact (MK_COMB (@lem5012406 B) (@lem5012405 B y)). Qed.
Lemma lem5012408 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5012409 {B : Type'} (y : B) : (term1056 B y) = (term1057 B y).
Proof. exact (MK_COMB (@lem5012408) (@lem5012407 B y)). Qed.
Lemma lem5012410 {B : Type'} (y : B) (s : B -> Prop) : (term1051 B y s) = (term1036 B y s).
Proof. exact (eq_refl (term1051 B y s)). Qed.
Lemma lem5012411 {B : Type'} (y : B) : (term1058 B y) = (term1049 B y).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5012410 B y s)). Qed.
Lemma lem5012412 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5012413 {B : Type'} (y : B) : (term1059 B y) = (term1060 B y).
Proof. exact (MK_COMB (@lem5012412 B) (@lem5012411 B y)). Qed.
Lemma lem5012414 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5012415 {B : Type'} (y : B) : (term1061 B y) = (term1062 B y).
Proof. exact (MK_COMB (@lem5012414) (@lem5012413 B y)). Qed.
Lemma lem5012416 {B : Type'} (y : B) (s : B -> Prop) : (term1053 B y s) = (term1041 B y s).
Proof. exact (eq_refl (term1053 B y s)). Qed.
Lemma lem5012417 {B : Type'} (y : B) : (term1063 B y) = (term1050 B y).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5012416 B y s)). Qed.
Lemma lem5012418 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5012419 {B : Type'} (y : B) : (term1064 B y) = (term1065 B y).
Proof. exact (MK_COMB (@lem5012418 B) (@lem5012417 B y)). Qed.
Lemma lem5012420 {B : Type'} (y : B) : (term1048 B y) = (term1066 B y).
Proof. exact (MK_COMB (@lem5012415 B y) (@lem5012419 B y)). Qed.
Lemma lem5012421 {B : Type'} (y : B) : ((term1047 B y) = (term1048 B y)) = ((term1044 B y) = (term1066 B y)).
Proof. exact (MK_COMB (@lem5012409 B y) (@lem5012420 B y)). Qed.
Lemma lem5012422 {B : Type'} (y : B) : (term1044 B y) = (term1066 B y).
Proof. exact (EQ_MP (@lem5012421 B y) (@lem5012399 B y)). Qed.
Lemma lem5012623 {B : Type'} (y : B) : (term1016 B y) = (term1066 B y).
Proof. exact (TRANS (@lem5012395 B y) (@lem5012422 B y)). Qed.
Lemma lem5012624 {B : Type'} : (term1017 B) = (term1067 B).
Proof. exact (fun_ext (fun y : B => @lem5012623 B y)). Qed.
Lemma lem5012625 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5012626 {B : Type'} : (term1018 B) = (term1068 B).
Proof. exact (MK_COMB (@lem5012625 B) (@lem5012624 B)). Qed.
Lemma lem5012628 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term1019 A P Q) = (term1020 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5012629 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term1019 B P Q) = (term1020 B P Q).
Proof. exact (@lem5012628 B P Q). Qed.
Lemma lem5012630 {B : Type'} : (term1069 B) = (term1070 B).
Proof. exact (@lem5012629 B (term1071 B) (term1072 B)). Qed.
Lemma lem5012631 {B : Type'} (y : B) : (term1073 B y) = (term1060 B y).
Proof. exact (eq_refl (term1073 B y)). Qed.
Lemma lem5012632 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5012633 {B : Type'} (y : B) : (term1074 B y) = (term1062 B y).
Proof. exact (MK_COMB (@lem5012632) (@lem5012631 B y)). Qed.
Lemma lem5012634 {B : Type'} (y : B) : (term1075 B y) = (term1065 B y).
Proof. exact (eq_refl (term1075 B y)). Qed.
Lemma lem5012635 {B : Type'} (y : B) : (term1076 B y) = (term1066 B y).
Proof. exact (MK_COMB (@lem5012633 B y) (@lem5012634 B y)). Qed.
Lemma lem5012636 {B : Type'} : (term1077 B) = (term1067 B).
Proof. exact (fun_ext (fun y : B => @lem5012635 B y)). Qed.
Lemma lem5012637 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5012638 {B : Type'} : (term1069 B) = (term1068 B).
Proof. exact (MK_COMB (@lem5012637 B) (@lem5012636 B)). Qed.
Lemma lem5012639 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5012640 {B : Type'} : (term1078 B) = (term1079 B).
Proof. exact (MK_COMB (@lem5012639) (@lem5012638 B)). Qed.
Lemma lem5012641 {B : Type'} (y : B) : (term1073 B y) = (term1060 B y).
Proof. exact (eq_refl (term1073 B y)). Qed.
Lemma lem5012642 {B : Type'} : (term1080 B) = (term1071 B).
Proof. exact (fun_ext (fun y : B => @lem5012641 B y)). Qed.
Lemma lem5012643 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5012644 {B : Type'} : (term1081 B) = (term1082 B).
Proof. exact (MK_COMB (@lem5012643 B) (@lem5012642 B)). Qed.
Lemma lem5012645 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5012646 {B : Type'} : (term1083 B) = (term1084 B).
Proof. exact (MK_COMB (@lem5012645) (@lem5012644 B)). Qed.
Lemma lem5012647 {B : Type'} (y : B) : (term1075 B y) = (term1065 B y).
Proof. exact (eq_refl (term1075 B y)). Qed.
Lemma lem5012648 {B : Type'} : (term1085 B) = (term1072 B).
Proof. exact (fun_ext (fun y : B => @lem5012647 B y)). Qed.
Lemma lem5012649 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5012650 {B : Type'} : (term1086 B) = (term1087 B).
Proof. exact (MK_COMB (@lem5012649 B) (@lem5012648 B)). Qed.
Lemma lem5012651 {B : Type'} : (term1070 B) = (term1088 B).
Proof. exact (MK_COMB (@lem5012646 B) (@lem5012650 B)). Qed.
Lemma lem5012652 {B : Type'} : ((term1069 B) = (term1070 B)) = ((term1068 B) = (term1088 B)).
Proof. exact (MK_COMB (@lem5012640 B) (@lem5012651 B)). Qed.
Lemma lem5012653 {B : Type'} : (term1068 B) = (term1088 B).
Proof. exact (EQ_MP (@lem5012652 B) (@lem5012630 B)). Qed.
Lemma lem5012862 {B : Type'} : (term1018 B) = (term1088 B).
Proof. exact (TRANS (@lem5012626 B) (@lem5012653 B)). Qed.
Lemma lem5012864 {A : Type'} (P : Prop) (Q : A -> Prop) : (term818 A P Q) = (term819 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5012865 {B : Type'} (P : Prop) (Q : B -> Prop) : (term818 B P Q) = (term819 B P Q).
Proof. exact (@lem5012864 B P Q). Qed.
Lemma lem5012866 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term1089 B y f s) = (term1090 B y f s).
Proof. exact (@lem5012865 B (term1091 B y f s) (term496 B y f s)). Qed.
Lemma lem5012867 {B : Type'} (y : B) (f : B -> B) (x : B) (s : B -> Prop) : (term999 B y f s x) = (term495 B y f x s).
Proof. exact (eq_refl (term999 B y f s x)). Qed.
Lemma lem5012868 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term1092 B y f s) = (term496 B y f s).
Proof. exact (fun_ext (fun x : B => @lem5012867 B y f x s)). Qed.
Lemma lem5012869 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5012870 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term1093 B y f s) = (term497 B y f s).
Proof. exact (MK_COMB (@lem5012869 B) (@lem5012868 B y f s)). Qed.
Lemma lem5012871 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term1004 B y f s) = (term1004 B y f s).
Proof. exact (eq_refl (term1004 B y f s)). Qed.
Lemma lem5012872 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term1089 B y f s) = (term1005 B y f s).
Proof. exact (MK_COMB (@lem5012871 B y f s) (@lem5012870 B y f s)). Qed.
Lemma lem5012873 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5012874 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term1094 B y f s) = (term1095 B y f s).
Proof. exact (MK_COMB (@lem5012873) (@lem5012872 B y f s)). Qed.
Lemma lem5012875 {B : Type'} (y : B) (f : B -> B) (x : B) (s : B -> Prop) : (term999 B y f s x) = (term495 B y f x s).
Proof. exact (eq_refl (term999 B y f s x)). Qed.
Lemma lem5012876 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term1004 B y f s) = (term1004 B y f s).
Proof. exact (eq_refl (term1004 B y f s)). Qed.
Lemma lem5012877 {B : Type'} (y : B) (f : B -> B) (x : B) (s : B -> Prop) : (term1096 B y f s x) = (term1097 B y f x s).
Proof. exact (MK_COMB (@lem5012876 B y f s) (@lem5012875 B y f x s)). Qed.
Lemma lem5012878 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term1098 B y f s) = (term1099 B y f s).
Proof. exact (fun_ext (fun x : B => @lem5012877 B y f x s)). Qed.
Lemma lem5012879 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5012880 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term1090 B y f s) = (term1100 B y f s).
Proof. exact (MK_COMB (@lem5012879 B) (@lem5012878 B y f s)). Qed.
Lemma lem5012881 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : ((term1089 B y f s) = (term1090 B y f s)) = ((term1005 B y f s) = (term1100 B y f s)).
Proof. exact (MK_COMB (@lem5012874 B y f s) (@lem5012880 B y f s)). Qed.
Lemma lem5012882 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term1005 B y f s) = (term1100 B y f s).
Proof. exact (EQ_MP (@lem5012881 B y f s) (@lem5012866 B y f s)). Qed.
Lemma lem5012883 {B : Type'} (y : B) (s : B -> Prop) : (term1026 B y s) = (term1101 B y s).
Proof. exact (fun_ext (fun f : B -> B => @lem5012882 B y f s)). Qed.
Lemma lem5012884 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem5012885 {B : Type'} (y : B) (s : B -> Prop) : (term1041 B y s) = (term1102 B y s).
Proof. exact (MK_COMB (@lem5012884 B) (@lem5012883 B y s)). Qed.
Lemma lem5012887 {A B : Type'} (P : type1413 A B) : (term1103 A B P) = (term1104 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5012888 {B : Type'} (P : type486 B) : (term1105 B P) = (term1106 B P).
Proof. exact (@lem5012887 (B -> B) B P). Qed.
Lemma lem5012889 {B : Type'} (y : B) (s : B -> Prop) : (term1107 B y s) = (term1108 B y s).
Proof. exact (@lem5012888 B (term1109 B y s)). Qed.
Lemma lem5012890 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term1110 B y s f) = (term1099 B y f s).
Proof. exact (eq_refl (term1110 B y s f)). Qed.
Lemma lem5012891 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5012892 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) (x : B) : (term1111 B y s f x) = (term1112 B y f s x).
Proof. exact (MK_COMB (@lem5012890 B y f s) (@lem5012891 B x)). Qed.
Lemma lem5012893 {B : Type'} (y : B) (f : B -> B) (x : B) (s : B -> Prop) : (term1112 B y f s x) = (term1097 B y f x s).
Proof. exact (eq_refl (term1112 B y f s x)). Qed.
Lemma lem5012894 {B : Type'} (y : B) (f : B -> B) (x : B) (s : B -> Prop) : (term1111 B y s f x) = (term1097 B y f x s).
Proof. exact (TRANS (@lem5012892 B y f s x) (@lem5012893 B y f x s)). Qed.
Lemma lem5012895 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term1113 B y s f) = (term1099 B y f s).
Proof. exact (fun_ext (fun x : B => @lem5012894 B y f x s)). Qed.
Lemma lem5012896 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5012897 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term1114 B y s f) = (term1100 B y f s).
Proof. exact (MK_COMB (@lem5012896 B) (@lem5012895 B y f s)). Qed.
Lemma lem5012898 {B : Type'} (y : B) (s : B -> Prop) : (term1115 B y s) = (term1101 B y s).
Proof. exact (fun_ext (fun f : B -> B => @lem5012897 B y f s)). Qed.
Lemma lem5012899 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem5012900 {B : Type'} (y : B) (s : B -> Prop) : (term1107 B y s) = (term1102 B y s).
Proof. exact (MK_COMB (@lem5012899 B) (@lem5012898 B y s)). Qed.
Lemma lem5012901 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5012902 {B : Type'} (y : B) (s : B -> Prop) : (term1116 B y s) = (term1117 B y s).
Proof. exact (MK_COMB (@lem5012901) (@lem5012900 B y s)). Qed.
Lemma lem5012903 {B : Type'} (y : B) (f : B -> B) (s : B -> Prop) : (term1110 B y s f) = (term1099 B y f s).
Proof. exact (eq_refl (term1110 B y s f)). Qed.
Lemma lem5012904 {B : Type'} (x : type487 B) (f : B -> B) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem5012905 {B : Type'} (y : B) (s : B -> Prop) (x : type487 B) (f : B -> B) : (term1118 B y s x f) = (term1119 B y s x f).
Proof. exact (MK_COMB (@lem5012903 B y f s) (@lem5012904 B x f)). Qed.
Lemma lem5012906 {B : Type'} (y : B) (x : type487 B) (f : B -> B) (s : B -> Prop) : (term1119 B y s x f) = (term1120 B y x f s).
Proof. exact (eq_refl (term1119 B y s x f)). Qed.
Lemma lem5012907 {B : Type'} (y : B) (x : type487 B) (f : B -> B) (s : B -> Prop) : (term1118 B y s x f) = (term1120 B y x f s).
Proof. exact (TRANS (@lem5012905 B y s x f) (@lem5012906 B y x f s)). Qed.
Lemma lem5012908 {B : Type'} (y : B) (x : type487 B) (s : B -> Prop) : (term1121 B y s x) = (term1122 B y x s).
Proof. exact (fun_ext (fun f : B -> B => @lem5012907 B y x f s)). Qed.
Lemma lem5012909 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem5012910 {B : Type'} (y : B) (x : type487 B) (s : B -> Prop) : (term1123 B y s x) = (term1124 B y x s).
Proof. exact (MK_COMB (@lem5012909 B) (@lem5012908 B y x s)). Qed.
Lemma lem5012911 {B : Type'} (y : B) (s : B -> Prop) : (term1125 B y s) = (term1126 B y s).
Proof. exact (fun_ext (fun x : type487 B => @lem5012910 B y x s)). Qed.
Lemma lem5012912 {B : Type'} : (@ex ((B -> B) -> B)) = (@ex ((B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B) -> B))). Qed.
Lemma lem5012913 {B : Type'} (y : B) (s : B -> Prop) : (term1108 B y s) = (term1127 B y s).
Proof. exact (MK_COMB (@lem5012912 B) (@lem5012911 B y s)). Qed.
Lemma lem5012914 {B : Type'} (y : B) (s : B -> Prop) : ((term1107 B y s) = (term1108 B y s)) = ((term1102 B y s) = (term1127 B y s)).
Proof. exact (MK_COMB (@lem5012902 B y s) (@lem5012913 B y s)). Qed.
Lemma lem5012915 {B : Type'} (y : B) (s : B -> Prop) : (term1102 B y s) = (term1127 B y s).
Proof. exact (EQ_MP (@lem5012914 B y s) (@lem5012889 B y s)). Qed.
Lemma lem5012916 {B : Type'} (y : B) (s : B -> Prop) : (term1041 B y s) = (term1127 B y s).
Proof. exact (TRANS (@lem5012885 B y s) (@lem5012915 B y s)). Qed.
Lemma lem5012917 {B : Type'} (y : B) : (term1050 B y) = (term1128 B y).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5012916 B y s)). Qed.
Lemma lem5012918 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5012919 {B : Type'} (y : B) : (term1065 B y) = (term1129 B y).
Proof. exact (MK_COMB (@lem5012918 B) (@lem5012917 B y)). Qed.
Lemma lem5012921 {A B : Type'} (P : type1413 A B) : (term1103 A B P) = (term1104 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5012922 {B : Type'} (P : type587 B) : (term1130 B P) = (term1131 B P).
Proof. exact (@lem5012921 (B -> Prop) (type487 B) P). Qed.
Lemma lem5012923 {B : Type'} (y : B) : (term1132 B y) = (term1133 B y).
Proof. exact (@lem5012922 B (term1134 B y)). Qed.
Lemma lem5012924 {B : Type'} (y : B) (s : B -> Prop) : (term1135 B y s) = (term1126 B y s).
Proof. exact (eq_refl (term1135 B y s)). Qed.
Lemma lem5012925 {B : Type'} (x : type487 B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5012926 {B : Type'} (y : B) (s : B -> Prop) (x : type487 B) : (term1136 B y s x) = (term1137 B y s x).
Proof. exact (MK_COMB (@lem5012924 B y s) (@lem5012925 B x)). Qed.
Lemma lem5012927 {B : Type'} (y : B) (x : type487 B) (s : B -> Prop) : (term1137 B y s x) = (term1124 B y x s).
Proof. exact (eq_refl (term1137 B y s x)). Qed.
Lemma lem5012928 {B : Type'} (y : B) (x : type487 B) (s : B -> Prop) : (term1136 B y s x) = (term1124 B y x s).
Proof. exact (TRANS (@lem5012926 B y s x) (@lem5012927 B y x s)). Qed.
Lemma lem5012929 {B : Type'} (y : B) (s : B -> Prop) : (term1138 B y s) = (term1126 B y s).
Proof. exact (fun_ext (fun x : type487 B => @lem5012928 B y x s)). Qed.
Lemma lem5012930 {B : Type'} : (@ex ((B -> B) -> B)) = (@ex ((B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> B) -> B))). Qed.
Lemma lem5012931 {B : Type'} (y : B) (s : B -> Prop) : (term1139 B y s) = (term1127 B y s).
Proof. exact (MK_COMB (@lem5012930 B) (@lem5012929 B y s)). Qed.
Lemma lem5012932 {B : Type'} (y : B) : (term1140 B y) = (term1128 B y).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5012931 B y s)). Qed.
Lemma lem5012933 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5012934 {B : Type'} (y : B) : (term1132 B y) = (term1129 B y).
Proof. exact (MK_COMB (@lem5012933 B) (@lem5012932 B y)). Qed.
Lemma lem5012935 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5012936 {B : Type'} (y : B) : (term1141 B y) = (term1142 B y).
Proof. exact (MK_COMB (@lem5012935) (@lem5012934 B y)). Qed.
Lemma lem5012937 {B : Type'} (y : B) (s : B -> Prop) : (term1135 B y s) = (term1126 B y s).
Proof. exact (eq_refl (term1135 B y s)). Qed.
Lemma lem5012938 {B : Type'} (x : type623 B) (s : B -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem5012939 {B : Type'} (y : B) (x : type623 B) (s : B -> Prop) : (term1143 B y x s) = (term1144 B y x s).
Proof. exact (MK_COMB (@lem5012937 B y s) (@lem5012938 B x s)). Qed.
Lemma lem5012940 {B : Type'} (y : B) (x : type623 B) (s : B -> Prop) : (term1144 B y x s) = (term1145 B y x s).
Proof. exact (eq_refl (term1144 B y x s)). Qed.
Lemma lem5012941 {B : Type'} (y : B) (x : type623 B) (s : B -> Prop) : (term1143 B y x s) = (term1145 B y x s).
Proof. exact (TRANS (@lem5012939 B y x s) (@lem5012940 B y x s)). Qed.
Lemma lem5012942 {B : Type'} (y : B) (x : type623 B) : (term1146 B y x) = (term1147 B y x).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5012941 B y x s)). Qed.
Lemma lem5012943 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5012944 {B : Type'} (y : B) (x : type623 B) : (term1148 B y x) = (term1149 B y x).
Proof. exact (MK_COMB (@lem5012943 B) (@lem5012942 B y x)). Qed.
Lemma lem5012945 {B : Type'} (y : B) : (term1150 B y) = (term1151 B y).
Proof. exact (fun_ext (fun x : type623 B => @lem5012944 B y x)). Qed.
Lemma lem5012946 {B : Type'} : (@ex ((B -> Prop) -> (B -> B) -> B)) = (@ex ((B -> Prop) -> (B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> (B -> B) -> B))). Qed.
Lemma lem5012947 {B : Type'} (y : B) : (term1133 B y) = (term1152 B y).
Proof. exact (MK_COMB (@lem5012946 B) (@lem5012945 B y)). Qed.
Lemma lem5012948 {B : Type'} (y : B) : ((term1132 B y) = (term1133 B y)) = ((term1129 B y) = (term1152 B y)).
Proof. exact (MK_COMB (@lem5012936 B y) (@lem5012947 B y)). Qed.
Lemma lem5012949 {B : Type'} (y : B) : (term1129 B y) = (term1152 B y).
Proof. exact (EQ_MP (@lem5012948 B y) (@lem5012923 B y)). Qed.
Lemma lem5012950 {B : Type'} (y : B) : (term1065 B y) = (term1152 B y).
Proof. exact (TRANS (@lem5012919 B y) (@lem5012949 B y)). Qed.
Lemma lem5012951 {B : Type'} : (term1072 B) = (term1153 B).
Proof. exact (fun_ext (fun y : B => @lem5012950 B y)). Qed.
Lemma lem5012952 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5012953 {B : Type'} : (term1087 B) = (term1154 B).
Proof. exact (MK_COMB (@lem5012952 B) (@lem5012951 B)). Qed.
Lemma lem5012955 {A B : Type'} (P : type1413 A B) : (term1103 A B P) = (term1104 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5012956 {B : Type'} (P : type1356 B) : (term1155 B P) = (term1156 B P).
Proof. exact (@lem5012955 B (type623 B) P). Qed.
Lemma lem5012957 {B : Type'} : (term1157 B) = (term1158 B).
Proof. exact (@lem5012956 B (term1159 B)). Qed.
Lemma lem5012958 {B : Type'} (y : B) : (term1160 B y) = (term1151 B y).
Proof. exact (eq_refl (term1160 B y)). Qed.
Lemma lem5012959 {B : Type'} (x : type623 B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5012960 {B : Type'} (y : B) (x : type623 B) : (term1161 B y x) = (term1162 B y x).
Proof. exact (MK_COMB (@lem5012958 B y) (@lem5012959 B x)). Qed.
Lemma lem5012961 {B : Type'} (y : B) (x : type623 B) : (term1162 B y x) = (term1149 B y x).
Proof. exact (eq_refl (term1162 B y x)). Qed.
Lemma lem5012962 {B : Type'} (y : B) (x : type623 B) : (term1161 B y x) = (term1149 B y x).
Proof. exact (TRANS (@lem5012960 B y x) (@lem5012961 B y x)). Qed.
Lemma lem5012963 {B : Type'} (y : B) : (term1163 B y) = (term1151 B y).
Proof. exact (fun_ext (fun x : type623 B => @lem5012962 B y x)). Qed.
Lemma lem5012964 {B : Type'} : (@ex ((B -> Prop) -> (B -> B) -> B)) = (@ex ((B -> Prop) -> (B -> B) -> B)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> (B -> B) -> B))). Qed.
Lemma lem5012965 {B : Type'} (y : B) : (term1164 B y) = (term1152 B y).
Proof. exact (MK_COMB (@lem5012964 B) (@lem5012963 B y)). Qed.
Lemma lem5012966 {B : Type'} : (term1165 B) = (term1153 B).
Proof. exact (fun_ext (fun y : B => @lem5012965 B y)). Qed.
Lemma lem5012967 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5012968 {B : Type'} : (term1157 B) = (term1154 B).
Proof. exact (MK_COMB (@lem5012967 B) (@lem5012966 B)). Qed.
Lemma lem5012969 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5012970 {B : Type'} : (term1166 B) = (term1167 B).
Proof. exact (MK_COMB (@lem5012969) (@lem5012968 B)). Qed.
Lemma lem5012971 {B : Type'} (y : B) : (term1160 B y) = (term1151 B y).
Proof. exact (eq_refl (term1160 B y)). Qed.
Lemma lem5012972 {B : Type'} (x : type1361 B) (y : B) : (x y) = (x y).
Proof. exact (eq_refl (x y)). Qed.
Lemma lem5012973 {B : Type'} (x : type1361 B) (y : B) : (term1168 B x y) = (term1169 B x y).
Proof. exact (MK_COMB (@lem5012971 B y) (@lem5012972 B x y)). Qed.
Lemma lem5012974 {B : Type'} (x : type1361 B) (y : B) : (term1169 B x y) = (term1170 B x y).
Proof. exact (eq_refl (term1169 B x y)). Qed.
Lemma lem5012975 {B : Type'} (x : type1361 B) (y : B) : (term1168 B x y) = (term1170 B x y).
Proof. exact (TRANS (@lem5012973 B x y) (@lem5012974 B x y)). Qed.
Lemma lem5012976 {B : Type'} (x : type1361 B) : (term1171 B x) = (term1172 B x).
Proof. exact (fun_ext (fun y : B => @lem5012975 B x y)). Qed.
Lemma lem5012977 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5012978 {B : Type'} (x : type1361 B) : (term1173 B x) = (term1174 B x).
Proof. exact (MK_COMB (@lem5012977 B) (@lem5012976 B x)). Qed.
Lemma lem5012979 {B : Type'} : (term1175 B) = (term1176 B).
Proof. exact (fun_ext (fun x : type1361 B => @lem5012978 B x)). Qed.
Lemma lem5012980 {B : Type'} : (@ex (B -> (B -> Prop) -> (B -> B) -> B)) = (@ex (B -> (B -> Prop) -> (B -> B) -> B)).
Proof. exact (eq_refl (@ex (B -> (B -> Prop) -> (B -> B) -> B))). Qed.
Lemma lem5012981 {B : Type'} : (term1158 B) = (term1177 B).
Proof. exact (MK_COMB (@lem5012980 B) (@lem5012979 B)). Qed.
Lemma lem5012982 {B : Type'} : ((term1157 B) = (term1158 B)) = ((term1154 B) = (term1177 B)).
Proof. exact (MK_COMB (@lem5012970 B) (@lem5012981 B)). Qed.
Lemma lem5012983 {B : Type'} : (term1154 B) = (term1177 B).
Proof. exact (EQ_MP (@lem5012982 B) (@lem5012957 B)). Qed.
Lemma lem5012984 {B : Type'} : (term1087 B) = (term1177 B).
Proof. exact (TRANS (@lem5012953 B) (@lem5012983 B)). Qed.
Lemma lem5012985 {B : Type'} : (term1084 B) = (term1084 B).
Proof. exact (eq_refl (term1084 B)). Qed.
Lemma lem5012986 {B : Type'} : (term1088 B) = (term1178 B).
Proof. exact (MK_COMB (@lem5012985 B) (@lem5012984 B)). Qed.
Lemma lem5012988 {A : Type'} (P : Prop) (Q : A -> Prop) : (term856 A P Q) = (term857 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5012989 {B : Type'} (P : Prop) (Q : type391 B) : (term1179 B P Q) = (term1180 B P Q).
Proof. exact (@lem5012988 (type1361 B) P Q). Qed.
Lemma lem5012990 {B : Type'} : (term1181 B) = (term1182 B).
Proof. exact (@lem5012989 B (term1082 B) (term1176 B)). Qed.
Lemma lem5012991 {B : Type'} (x : type1361 B) : (term1183 B x) = (term1174 B x).
Proof. exact (eq_refl (term1183 B x)). Qed.
Lemma lem5012992 {B : Type'} : (term1184 B) = (term1176 B).
Proof. exact (fun_ext (fun x : type1361 B => @lem5012991 B x)). Qed.
Lemma lem5012993 {B : Type'} : (@ex (B -> (B -> Prop) -> (B -> B) -> B)) = (@ex (B -> (B -> Prop) -> (B -> B) -> B)).
Proof. exact (eq_refl (@ex (B -> (B -> Prop) -> (B -> B) -> B))). Qed.
Lemma lem5012994 {B : Type'} : (term1185 B) = (term1177 B).
Proof. exact (MK_COMB (@lem5012993 B) (@lem5012992 B)). Qed.
Lemma lem5012995 {B : Type'} : (term1084 B) = (term1084 B).
Proof. exact (eq_refl (term1084 B)). Qed.
Lemma lem5012996 {B : Type'} : (term1181 B) = (term1178 B).
Proof. exact (MK_COMB (@lem5012995 B) (@lem5012994 B)). Qed.
Lemma lem5012997 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5012998 {B : Type'} : (term1186 B) = (term1187 B).
Proof. exact (MK_COMB (@lem5012997) (@lem5012996 B)). Qed.
Lemma lem5012999 {B : Type'} (x : type1361 B) : (term1183 B x) = (term1174 B x).
Proof. exact (eq_refl (term1183 B x)). Qed.
Lemma lem5013000 {B : Type'} : (term1084 B) = (term1084 B).
Proof. exact (eq_refl (term1084 B)). Qed.
Lemma lem5013001 {B : Type'} (x : type1361 B) : (term1188 B x) = (term1189 B x).
Proof. exact (MK_COMB (@lem5013000 B) (@lem5012999 B x)). Qed.
Lemma lem5013002 {B : Type'} : (term1190 B) = (term1191 B).
Proof. exact (fun_ext (fun x : type1361 B => @lem5013001 B x)). Qed.
Lemma lem5013003 {B : Type'} : (@ex (B -> (B -> Prop) -> (B -> B) -> B)) = (@ex (B -> (B -> Prop) -> (B -> B) -> B)).
Proof. exact (eq_refl (@ex (B -> (B -> Prop) -> (B -> B) -> B))). Qed.
Lemma lem5013004 {B : Type'} : (term1182 B) = (term1192 B).
Proof. exact (MK_COMB (@lem5013003 B) (@lem5013002 B)). Qed.
Lemma lem5013005 {B : Type'} : ((term1181 B) = (term1182 B)) = ((term1178 B) = (term1192 B)).
Proof. exact (MK_COMB (@lem5012998 B) (@lem5013004 B)). Qed.
Lemma lem5013006 {B : Type'} : (term1178 B) = (term1192 B).
Proof. exact (EQ_MP (@lem5013005 B) (@lem5012990 B)). Qed.
Lemma lem5013007 {B : Type'} : (term1088 B) = (term1192 B).
Proof. exact (TRANS (@lem5012986 B) (@lem5013006 B)). Qed.
Lemma lem5013008 {B : Type'} : (term1018 B) = (term1192 B).
Proof. exact (TRANS (@lem5012862 B) (@lem5013007 B)). Qed.
Lemma lem5013009 {B : Type'} : (term432 B) = (term1192 B).
Proof. exact (TRANS (@lem5012165 B) (@lem5013008 B)). Qed.
Lemma lem5013010 {B : Type'} (h1 : term432 B) : term1192 B.
Proof. exact (EQ_MP (@lem5013009 B) (@lem5008915 B h1)). Qed.
Lemma lem5013021 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term1385 A s x t) = (term1386 A s x t).
Proof. exact (@lem17362 (@IN A x s) (@IN A x t)). Qed.
Lemma lem5013026 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term490 A s x t) = (term1387 A s x t).
Proof. exact (@lem17265 (@IN A x s) (@IN A x t)). Qed.
Lemma lem5013027 {A : Type'} (P : A -> Prop) : (term624 A P) = (term625 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem5013028 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1388 A s t) = (term1389 A s t).
Proof. exact (@lem5013027 A (term491 A s t)). Qed.
Lemma lem5013029 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term1390 A s t x) = (term490 A s x t).
Proof. exact (eq_refl (term1390 A s t x)). Qed.
Lemma lem5013030 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5013031 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term1391 A s t x) = (term1385 A s x t).
Proof. exact (MK_COMB (@lem5013030) (@lem5013029 A s x t)). Qed.
Lemma lem5013032 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term1391 A s t x) = (term1386 A s x t).
Proof. exact (TRANS (@lem5013031 A s x t) (@lem5013021 A s x t)). Qed.
Lemma lem5013033 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1392 A s t) = (term1393 A s t).
Proof. exact (fun_ext (fun x : A => @lem5013032 A s x t)). Qed.
Lemma lem5013034 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5013035 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1389 A s t) = (term1394 A s t).
Proof. exact (MK_COMB (@lem5013034 A) (@lem5013033 A s t)). Qed.
Lemma lem5013036 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1388 A s t) = (term1394 A s t).
Proof. exact (TRANS (@lem5013028 A s t) (@lem5013035 A s t)). Qed.
Lemma lem5013037 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term491 A s t) = (term1395 A s t).
Proof. exact (fun_ext (fun x : A => @lem5013026 A s x t)). Qed.
Lemma lem5013038 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5013039 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term10 A s t) = (term1396 A s t).
Proof. exact (MK_COMB (@lem5013038 A) (@lem5013037 A s t)). Qed.
Lemma lem5013041 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1397 A s t) = (term1397 A s t).
Proof. exact (eq_refl (term1397 A s t)). Qed.
Lemma lem5013042 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1398 A s t) = (term1399 A s t).
Proof. exact (MK_COMB (@lem5013041 A s t) (@lem5013039 A s t)). Qed.
Lemma lem5013044 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1400 A s t) = (term1400 A s t).
Proof. exact (eq_refl (term1400 A s t)). Qed.
Lemma lem5013045 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1401 A s t) = (term1402 A s t).
Proof. exact (MK_COMB (@lem5013044 A s t) (@lem5013036 A s t)). Qed.
Lemma lem5013046 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5013047 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1403 A s t) = (term1404 A s t).
Proof. exact (MK_COMB (@lem5013046) (@lem5013045 A s t)). Qed.
Lemma lem5013048 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1405 A s t) = (term1406 A s t).
Proof. exact (MK_COMB (@lem5013047 A s t) (@lem5013042 A s t)). Qed.
Lemma lem5013049 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((@SUBSET A s t) = (term10 A s t)) = (term1405 A s t).
Proof. exact (@lem17784 (@SUBSET A s t) (term10 A s t)). Qed.
Lemma lem5013050 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((@SUBSET A s t) = (term10 A s t)) = (term1406 A s t).
Proof. exact (TRANS (@lem5013049 A s t) (@lem5013048 A s t)). Qed.
Lemma lem5013051 {A : Type'} (s : A -> Prop) : (term493 A s) = (term1407 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5013050 A s t)). Qed.
Lemma lem5013052 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5013053 {A : Type'} (s : A -> Prop) : (term8 A s) = (term1408 A s).
Proof. exact (MK_COMB (@lem5013052 A) (@lem5013051 A s)). Qed.
Lemma lem5013054 {A : Type'} : (term494 A) = (term1409 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5013053 A s)). Qed.
Lemma lem5013055 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5013056 {A : Type'} : (term431 A) = (term1410 A).
Proof. exact (MK_COMB (@lem5013055 A) (@lem5013054 A)). Qed.
Lemma lem5013062 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term1019 A P Q) = (term1020 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5013063 {A : Type'} (P : type686 A) (Q : type686 A) : (term1045 A P Q) = (term1046 A P Q).
Proof. exact (@lem5013062 (A -> Prop) P Q). Qed.
Lemma lem5013064 {A : Type'} (s : A -> Prop) : (term1411 A s) = (term1412 A s).
Proof. exact (@lem5013063 A (term1413 A s) (term1414 A s)). Qed.
Lemma lem5013065 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1415 A s t) = (term1402 A s t).
Proof. exact (eq_refl (term1415 A s t)). Qed.
Lemma lem5013066 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5013067 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1416 A s t) = (term1404 A s t).
Proof. exact (MK_COMB (@lem5013066) (@lem5013065 A s t)). Qed.
Lemma lem5013068 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1417 A s t) = (term1399 A s t).
Proof. exact (eq_refl (term1417 A s t)). Qed.
Lemma lem5013069 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1418 A s t) = (term1406 A s t).
Proof. exact (MK_COMB (@lem5013067 A s t) (@lem5013068 A s t)). Qed.
Lemma lem5013070 {A : Type'} (s : A -> Prop) : (term1419 A s) = (term1407 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5013069 A s t)). Qed.
Lemma lem5013071 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5013072 {A : Type'} (s : A -> Prop) : (term1411 A s) = (term1408 A s).
Proof. exact (MK_COMB (@lem5013071 A) (@lem5013070 A s)). Qed.
Lemma lem5013073 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5013074 {A : Type'} (s : A -> Prop) : (term1420 A s) = (term1421 A s).
Proof. exact (MK_COMB (@lem5013073) (@lem5013072 A s)). Qed.
Lemma lem5013075 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1415 A s t) = (term1402 A s t).
Proof. exact (eq_refl (term1415 A s t)). Qed.
Lemma lem5013076 {A : Type'} (s : A -> Prop) : (term1422 A s) = (term1413 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5013075 A s t)). Qed.
Lemma lem5013077 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5013078 {A : Type'} (s : A -> Prop) : (term1423 A s) = (term1424 A s).
Proof. exact (MK_COMB (@lem5013077 A) (@lem5013076 A s)). Qed.
Lemma lem5013079 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5013080 {A : Type'} (s : A -> Prop) : (term1425 A s) = (term1426 A s).
Proof. exact (MK_COMB (@lem5013079) (@lem5013078 A s)). Qed.
Lemma lem5013081 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1417 A s t) = (term1399 A s t).
Proof. exact (eq_refl (term1417 A s t)). Qed.
Lemma lem5013082 {A : Type'} (s : A -> Prop) : (term1427 A s) = (term1414 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5013081 A s t)). Qed.
Lemma lem5013083 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5013084 {A : Type'} (s : A -> Prop) : (term1428 A s) = (term1429 A s).
Proof. exact (MK_COMB (@lem5013083 A) (@lem5013082 A s)). Qed.
Lemma lem5013085 {A : Type'} (s : A -> Prop) : (term1412 A s) = (term1430 A s).
Proof. exact (MK_COMB (@lem5013080 A s) (@lem5013084 A s)). Qed.
Lemma lem5013086 {A : Type'} (s : A -> Prop) : ((term1411 A s) = (term1412 A s)) = ((term1408 A s) = (term1430 A s)).
Proof. exact (MK_COMB (@lem5013074 A s) (@lem5013085 A s)). Qed.
Lemma lem5013087 {A : Type'} (s : A -> Prop) : (term1408 A s) = (term1430 A s).
Proof. exact (EQ_MP (@lem5013086 A s) (@lem5013064 A s)). Qed.
Lemma lem5013280 {A : Type'} : (term1409 A) = (term1431 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5013087 A s)). Qed.
Lemma lem5013281 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5013282 {A : Type'} : (term1410 A) = (term1432 A).
Proof. exact (MK_COMB (@lem5013281 A) (@lem5013280 A)). Qed.
Lemma lem5013284 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term1019 A P Q) = (term1020 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5013285 {A : Type'} (P : type686 A) (Q : type686 A) : (term1045 A P Q) = (term1046 A P Q).
Proof. exact (@lem5013284 (A -> Prop) P Q). Qed.
Lemma lem5013286 {A : Type'} : (term1433 A) = (term1434 A).
Proof. exact (@lem5013285 A (term1435 A) (term1436 A)). Qed.
Lemma lem5013287 {A : Type'} (s : A -> Prop) : (term1437 A s) = (term1424 A s).
Proof. exact (eq_refl (term1437 A s)). Qed.
Lemma lem5013288 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5013289 {A : Type'} (s : A -> Prop) : (term1438 A s) = (term1426 A s).
Proof. exact (MK_COMB (@lem5013288) (@lem5013287 A s)). Qed.
Lemma lem5013290 {A : Type'} (s : A -> Prop) : (term1439 A s) = (term1429 A s).
Proof. exact (eq_refl (term1439 A s)). Qed.
Lemma lem5013291 {A : Type'} (s : A -> Prop) : (term1440 A s) = (term1430 A s).
Proof. exact (MK_COMB (@lem5013289 A s) (@lem5013290 A s)). Qed.
Lemma lem5013292 {A : Type'} : (term1441 A) = (term1431 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5013291 A s)). Qed.
Lemma lem5013293 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5013294 {A : Type'} : (term1433 A) = (term1432 A).
Proof. exact (MK_COMB (@lem5013293 A) (@lem5013292 A)). Qed.
Lemma lem5013295 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5013296 {A : Type'} : (term1442 A) = (term1443 A).
Proof. exact (MK_COMB (@lem5013295) (@lem5013294 A)). Qed.
Lemma lem5013297 {A : Type'} (s : A -> Prop) : (term1437 A s) = (term1424 A s).
Proof. exact (eq_refl (term1437 A s)). Qed.
Lemma lem5013298 {A : Type'} : (term1444 A) = (term1435 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5013297 A s)). Qed.
Lemma lem5013299 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5013300 {A : Type'} : (term1445 A) = (term1446 A).
Proof. exact (MK_COMB (@lem5013299 A) (@lem5013298 A)). Qed.
Lemma lem5013301 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5013302 {A : Type'} : (term1447 A) = (term1448 A).
Proof. exact (MK_COMB (@lem5013301) (@lem5013300 A)). Qed.
Lemma lem5013303 {A : Type'} (s : A -> Prop) : (term1439 A s) = (term1429 A s).
Proof. exact (eq_refl (term1439 A s)). Qed.
Lemma lem5013304 {A : Type'} : (term1449 A) = (term1436 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5013303 A s)). Qed.
Lemma lem5013305 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5013306 {A : Type'} : (term1450 A) = (term1451 A).
Proof. exact (MK_COMB (@lem5013305 A) (@lem5013304 A)). Qed.
Lemma lem5013307 {A : Type'} : (term1434 A) = (term1452 A).
Proof. exact (MK_COMB (@lem5013302 A) (@lem5013306 A)). Qed.
Lemma lem5013308 {A : Type'} : ((term1433 A) = (term1434 A)) = ((term1432 A) = (term1452 A)).
Proof. exact (MK_COMB (@lem5013296 A) (@lem5013307 A)). Qed.
Lemma lem5013309 {A : Type'} : (term1432 A) = (term1452 A).
Proof. exact (EQ_MP (@lem5013308 A) (@lem5013286 A)). Qed.
Lemma lem5013510 {A : Type'} : (term1410 A) = (term1452 A).
Proof. exact (TRANS (@lem5013282 A) (@lem5013309 A)). Qed.
Lemma lem5013512 {A : Type'} (P : Prop) (Q : A -> Prop) : (term818 A P Q) = (term819 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5013513 {A : Type'} (P : Prop) (Q : A -> Prop) : (term818 A P Q) = (term819 A P Q).
Proof. exact (@lem5013512 A P Q). Qed.
Lemma lem5013514 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1453 A s t) = (term1454 A s t).
Proof. exact (@lem5013513 A (@SUBSET A s t) (term1393 A s t)). Qed.
Lemma lem5013515 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term1455 A s t x) = (term1386 A s x t).
Proof. exact (eq_refl (term1455 A s t x)). Qed.
Lemma lem5013516 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1456 A s t) = (term1393 A s t).
Proof. exact (fun_ext (fun x : A => @lem5013515 A s x t)). Qed.
Lemma lem5013517 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5013518 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1457 A s t) = (term1394 A s t).
Proof. exact (MK_COMB (@lem5013517 A) (@lem5013516 A s t)). Qed.
Lemma lem5013519 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1400 A s t) = (term1400 A s t).
Proof. exact (eq_refl (term1400 A s t)). Qed.
Lemma lem5013520 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1453 A s t) = (term1402 A s t).
Proof. exact (MK_COMB (@lem5013519 A s t) (@lem5013518 A s t)). Qed.
Lemma lem5013521 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5013522 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1458 A s t) = (term1459 A s t).
Proof. exact (MK_COMB (@lem5013521) (@lem5013520 A s t)). Qed.
Lemma lem5013523 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term1455 A s t x) = (term1386 A s x t).
Proof. exact (eq_refl (term1455 A s t x)). Qed.
Lemma lem5013524 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1400 A s t) = (term1400 A s t).
Proof. exact (eq_refl (term1400 A s t)). Qed.
Lemma lem5013525 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term1460 A s t x) = (term1461 A s x t).
Proof. exact (MK_COMB (@lem5013524 A s t) (@lem5013523 A s x t)). Qed.
Lemma lem5013526 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1462 A s t) = (term1463 A s t).
Proof. exact (fun_ext (fun x : A => @lem5013525 A s x t)). Qed.
Lemma lem5013527 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5013528 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1454 A s t) = (term1464 A s t).
Proof. exact (MK_COMB (@lem5013527 A) (@lem5013526 A s t)). Qed.
Lemma lem5013529 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term1453 A s t) = (term1454 A s t)) = ((term1402 A s t) = (term1464 A s t)).
Proof. exact (MK_COMB (@lem5013522 A s t) (@lem5013528 A s t)). Qed.
Lemma lem5013530 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1402 A s t) = (term1464 A s t).
Proof. exact (EQ_MP (@lem5013529 A s t) (@lem5013514 A s t)). Qed.
Lemma lem5013531 {A : Type'} (s : A -> Prop) : (term1413 A s) = (term1465 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5013530 A s t)). Qed.
Lemma lem5013532 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5013533 {A : Type'} (s : A -> Prop) : (term1424 A s) = (term1466 A s).
Proof. exact (MK_COMB (@lem5013532 A) (@lem5013531 A s)). Qed.
Lemma lem5013535 {A B : Type'} (P : type1413 A B) : (term1103 A B P) = (term1104 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5013536 {A : Type'} (P : type672 A) : (term1467 A P) = (term1468 A P).
Proof. exact (@lem5013535 (A -> Prop) A P). Qed.
Lemma lem5013537 {A : Type'} (s : A -> Prop) : (term1469 A s) = (term1470 A s).
Proof. exact (@lem5013536 A (term1471 A s)). Qed.
Lemma lem5013538 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1472 A s t) = (term1463 A s t).
Proof. exact (eq_refl (term1472 A s t)). Qed.
Lemma lem5013539 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5013540 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term1473 A s t x) = (term1474 A s t x).
Proof. exact (MK_COMB (@lem5013538 A s t) (@lem5013539 A x)). Qed.
Lemma lem5013541 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term1474 A s t x) = (term1461 A s x t).
Proof. exact (eq_refl (term1474 A s t x)). Qed.
Lemma lem5013542 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term1473 A s t x) = (term1461 A s x t).
Proof. exact (TRANS (@lem5013540 A s t x) (@lem5013541 A s x t)). Qed.
Lemma lem5013543 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1475 A s t) = (term1463 A s t).
Proof. exact (fun_ext (fun x : A => @lem5013542 A s x t)). Qed.
Lemma lem5013544 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5013545 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1476 A s t) = (term1464 A s t).
Proof. exact (MK_COMB (@lem5013544 A) (@lem5013543 A s t)). Qed.
Lemma lem5013546 {A : Type'} (s : A -> Prop) : (term1477 A s) = (term1465 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5013545 A s t)). Qed.
Lemma lem5013547 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5013548 {A : Type'} (s : A -> Prop) : (term1469 A s) = (term1466 A s).
Proof. exact (MK_COMB (@lem5013547 A) (@lem5013546 A s)). Qed.
Lemma lem5013549 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5013550 {A : Type'} (s : A -> Prop) : (term1478 A s) = (term1479 A s).
Proof. exact (MK_COMB (@lem5013549) (@lem5013548 A s)). Qed.
Lemma lem5013551 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1472 A s t) = (term1463 A s t).
Proof. exact (eq_refl (term1472 A s t)). Qed.
Lemma lem5013552 {A : Type'} (x : type684 A) (t : A -> Prop) : (x t) = (x t).
Proof. exact (eq_refl (x t)). Qed.
Lemma lem5013553 {A : Type'} (s : A -> Prop) (x : type684 A) (t : A -> Prop) : (term1480 A s x t) = (term1481 A s x t).
Proof. exact (MK_COMB (@lem5013551 A s t) (@lem5013552 A x t)). Qed.
Lemma lem5013554 {A : Type'} (s : A -> Prop) (x : type684 A) (t : A -> Prop) : (term1481 A s x t) = (term1482 A s x t).
Proof. exact (eq_refl (term1481 A s x t)). Qed.
Lemma lem5013555 {A : Type'} (s : A -> Prop) (x : type684 A) (t : A -> Prop) : (term1480 A s x t) = (term1482 A s x t).
Proof. exact (TRANS (@lem5013553 A s x t) (@lem5013554 A s x t)). Qed.
Lemma lem5013556 {A : Type'} (s : A -> Prop) (x : type684 A) : (term1483 A s x) = (term1484 A s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5013555 A s x t)). Qed.
Lemma lem5013557 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5013558 {A : Type'} (s : A -> Prop) (x : type684 A) : (term1485 A s x) = (term1486 A s x).
Proof. exact (MK_COMB (@lem5013557 A) (@lem5013556 A s x)). Qed.
Lemma lem5013559 {A : Type'} (s : A -> Prop) : (term1487 A s) = (term1488 A s).
Proof. exact (fun_ext (fun x : type684 A => @lem5013558 A s x)). Qed.
Lemma lem5013560 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem5013561 {A : Type'} (s : A -> Prop) : (term1470 A s) = (term1489 A s).
Proof. exact (MK_COMB (@lem5013560 A) (@lem5013559 A s)). Qed.
Lemma lem5013562 {A : Type'} (s : A -> Prop) : ((term1469 A s) = (term1470 A s)) = ((term1466 A s) = (term1489 A s)).
Proof. exact (MK_COMB (@lem5013550 A s) (@lem5013561 A s)). Qed.
Lemma lem5013563 {A : Type'} (s : A -> Prop) : (term1466 A s) = (term1489 A s).
Proof. exact (EQ_MP (@lem5013562 A s) (@lem5013537 A s)). Qed.
Lemma lem5013564 {A : Type'} (s : A -> Prop) : (term1424 A s) = (term1489 A s).
Proof. exact (TRANS (@lem5013533 A s) (@lem5013563 A s)). Qed.
Lemma lem5013565 {A : Type'} : (term1435 A) = (term1490 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5013564 A s)). Qed.
Lemma lem5013566 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5013567 {A : Type'} : (term1446 A) = (term1491 A).
Proof. exact (MK_COMB (@lem5013566 A) (@lem5013565 A)). Qed.
Lemma lem5013569 {A B : Type'} (P : type1413 A B) : (term1103 A B P) = (term1104 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5013570 {A : Type'} (P : type597 A) : (term1492 A P) = (term1493 A P).
Proof. exact (@lem5013569 (A -> Prop) (type684 A) P). Qed.
Lemma lem5013571 {A : Type'} : (term1494 A) = (term1495 A).
Proof. exact (@lem5013570 A (term1496 A)). Qed.
Lemma lem5013572 {A : Type'} (s : A -> Prop) : (term1497 A s) = (term1488 A s).
Proof. exact (eq_refl (term1497 A s)). Qed.
Lemma lem5013573 {A : Type'} (x : type684 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5013574 {A : Type'} (s : A -> Prop) (x : type684 A) : (term1498 A s x) = (term1499 A s x).
Proof. exact (MK_COMB (@lem5013572 A s) (@lem5013573 A x)). Qed.
Lemma lem5013575 {A : Type'} (s : A -> Prop) (x : type684 A) : (term1499 A s x) = (term1486 A s x).
Proof. exact (eq_refl (term1499 A s x)). Qed.
Lemma lem5013576 {A : Type'} (s : A -> Prop) (x : type684 A) : (term1498 A s x) = (term1486 A s x).
Proof. exact (TRANS (@lem5013574 A s x) (@lem5013575 A s x)). Qed.
Lemma lem5013577 {A : Type'} (s : A -> Prop) : (term1500 A s) = (term1488 A s).
Proof. exact (fun_ext (fun x : type684 A => @lem5013576 A s x)). Qed.
Lemma lem5013578 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem5013579 {A : Type'} (s : A -> Prop) : (term1501 A s) = (term1489 A s).
Proof. exact (MK_COMB (@lem5013578 A) (@lem5013577 A s)). Qed.
Lemma lem5013580 {A : Type'} : (term1502 A) = (term1490 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5013579 A s)). Qed.
Lemma lem5013581 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5013582 {A : Type'} : (term1494 A) = (term1491 A).
Proof. exact (MK_COMB (@lem5013581 A) (@lem5013580 A)). Qed.
Lemma lem5013583 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5013584 {A : Type'} : (term1503 A) = (term1504 A).
Proof. exact (MK_COMB (@lem5013583) (@lem5013582 A)). Qed.
Lemma lem5013585 {A : Type'} (s : A -> Prop) : (term1497 A s) = (term1488 A s).
Proof. exact (eq_refl (term1497 A s)). Qed.
Lemma lem5013586 {A : Type'} (x : type638 A) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem5013587 {A : Type'} (x : type638 A) (s : A -> Prop) : (term1505 A x s) = (term1506 A x s).
Proof. exact (MK_COMB (@lem5013585 A s) (@lem5013586 A x s)). Qed.
Lemma lem5013588 {A : Type'} (x : type638 A) (s : A -> Prop) : (term1506 A x s) = (term1507 A x s).
Proof. exact (eq_refl (term1506 A x s)). Qed.
Lemma lem5013589 {A : Type'} (x : type638 A) (s : A -> Prop) : (term1505 A x s) = (term1507 A x s).
Proof. exact (TRANS (@lem5013587 A x s) (@lem5013588 A x s)). Qed.
Lemma lem5013590 {A : Type'} (x : type638 A) : (term1508 A x) = (term1509 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5013589 A x s)). Qed.
Lemma lem5013591 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5013592 {A : Type'} (x : type638 A) : (term1510 A x) = (term1511 A x).
Proof. exact (MK_COMB (@lem5013591 A) (@lem5013590 A x)). Qed.
Lemma lem5013593 {A : Type'} : (term1512 A) = (term1513 A).
Proof. exact (fun_ext (fun x : type638 A => @lem5013592 A x)). Qed.
Lemma lem5013594 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A)) = (@ex ((A -> Prop) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A))). Qed.
Lemma lem5013595 {A : Type'} : (term1495 A) = (term1514 A).
Proof. exact (MK_COMB (@lem5013594 A) (@lem5013593 A)). Qed.
Lemma lem5013596 {A : Type'} : ((term1494 A) = (term1495 A)) = ((term1491 A) = (term1514 A)).
Proof. exact (MK_COMB (@lem5013584 A) (@lem5013595 A)). Qed.
Lemma lem5013597 {A : Type'} : (term1491 A) = (term1514 A).
Proof. exact (EQ_MP (@lem5013596 A) (@lem5013571 A)). Qed.
Lemma lem5013598 {A : Type'} : (term1446 A) = (term1514 A).
Proof. exact (TRANS (@lem5013567 A) (@lem5013597 A)). Qed.
Lemma lem5013599 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5013600 {A : Type'} : (term1448 A) = (term1515 A).
Proof. exact (MK_COMB (@lem5013599) (@lem5013598 A)). Qed.
Lemma lem5013601 {A : Type'} : (term1451 A) = (term1451 A).
Proof. exact (eq_refl (term1451 A)). Qed.
Lemma lem5013602 {A : Type'} : (term1452 A) = (term1516 A).
Proof. exact (MK_COMB (@lem5013600 A) (@lem5013601 A)). Qed.
Lemma lem5013604 {A : Type'} (P : A -> Prop) (Q : Prop) : (term834 A P Q) = (term835 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5013605 {A : Type'} (P : type139 A) (Q : Prop) : (term1517 A P Q) = (term1518 A P Q).
Proof. exact (@lem5013604 (type638 A) P Q). Qed.
Lemma lem5013606 {A : Type'} : (term1519 A) = (term1520 A).
Proof. exact (@lem5013605 A (term1513 A) (term1451 A)). Qed.
Lemma lem5013607 {A : Type'} (x : type638 A) : (term1521 A x) = (term1511 A x).
Proof. exact (eq_refl (term1521 A x)). Qed.
Lemma lem5013608 {A : Type'} : (term1522 A) = (term1513 A).
Proof. exact (fun_ext (fun x : type638 A => @lem5013607 A x)). Qed.
Lemma lem5013609 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A)) = (@ex ((A -> Prop) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A))). Qed.
Lemma lem5013610 {A : Type'} : (term1523 A) = (term1514 A).
Proof. exact (MK_COMB (@lem5013609 A) (@lem5013608 A)). Qed.
Lemma lem5013611 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5013612 {A : Type'} : (term1524 A) = (term1515 A).
Proof. exact (MK_COMB (@lem5013611) (@lem5013610 A)). Qed.
Lemma lem5013613 {A : Type'} : (term1451 A) = (term1451 A).
Proof. exact (eq_refl (term1451 A)). Qed.
Lemma lem5013614 {A : Type'} : (term1519 A) = (term1516 A).
Proof. exact (MK_COMB (@lem5013612 A) (@lem5013613 A)). Qed.
Lemma lem5013615 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5013616 {A : Type'} : (term1525 A) = (term1526 A).
Proof. exact (MK_COMB (@lem5013615) (@lem5013614 A)). Qed.
Lemma lem5013617 {A : Type'} (x : type638 A) : (term1521 A x) = (term1511 A x).
Proof. exact (eq_refl (term1521 A x)). Qed.
Lemma lem5013618 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5013619 {A : Type'} (x : type638 A) : (term1527 A x) = (term1528 A x).
Proof. exact (MK_COMB (@lem5013618) (@lem5013617 A x)). Qed.
Lemma lem5013620 {A : Type'} : (term1451 A) = (term1451 A).
Proof. exact (eq_refl (term1451 A)). Qed.
Lemma lem5013621 {A : Type'} (x : type638 A) : (term1529 A x) = (term1530 A x).
Proof. exact (MK_COMB (@lem5013619 A x) (@lem5013620 A)). Qed.
Lemma lem5013622 {A : Type'} : (term1531 A) = (term1532 A).
Proof. exact (fun_ext (fun x : type638 A => @lem5013621 A x)). Qed.
Lemma lem5013623 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A)) = (@ex ((A -> Prop) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A))). Qed.
Lemma lem5013624 {A : Type'} : (term1520 A) = (term1533 A).
Proof. exact (MK_COMB (@lem5013623 A) (@lem5013622 A)). Qed.
Lemma lem5013625 {A : Type'} : ((term1519 A) = (term1520 A)) = ((term1516 A) = (term1533 A)).
Proof. exact (MK_COMB (@lem5013616 A) (@lem5013624 A)). Qed.
Lemma lem5013626 {A : Type'} : (term1516 A) = (term1533 A).
Proof. exact (EQ_MP (@lem5013625 A) (@lem5013606 A)). Qed.
Lemma lem5013627 {A : Type'} : (term1452 A) = (term1533 A).
Proof. exact (TRANS (@lem5013602 A) (@lem5013626 A)). Qed.
Lemma lem5013628 {A : Type'} : (term1410 A) = (term1533 A).
Proof. exact (TRANS (@lem5013510 A) (@lem5013627 A)). Qed.
Lemma lem5013629 {A : Type'} : (term431 A) = (term1533 A).
Proof. exact (TRANS (@lem5013056 A) (@lem5013628 A)). Qed.
Lemma lem5013630 {A : Type'} (h1 : term431 A) : term1533 A.
Proof. exact (EQ_MP (@lem5013629 A) (@lem5008916 A h1)). Qed.
Lemma lem5013641 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term1385 B s x t) = (term1386 B s x t).
Proof. exact (@lem17362 (@IN B x s) (@IN B x t)). Qed.
Lemma lem5013646 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term490 B s x t) = (term1387 B s x t).
Proof. exact (@lem17265 (@IN B x s) (@IN B x t)). Qed.
Lemma lem5013647 {B : Type'} (P : B -> Prop) : (term624 B P) = (term625 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem5013648 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1388 B s t) = (term1389 B s t).
Proof. exact (@lem5013647 B (term491 B s t)). Qed.
Lemma lem5013649 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term1390 B s t x) = (term490 B s x t).
Proof. exact (eq_refl (term1390 B s t x)). Qed.
Lemma lem5013650 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5013651 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term1391 B s t x) = (term1385 B s x t).
Proof. exact (MK_COMB (@lem5013650) (@lem5013649 B s x t)). Qed.
Lemma lem5013652 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term1391 B s t x) = (term1386 B s x t).
Proof. exact (TRANS (@lem5013651 B s x t) (@lem5013641 B s x t)). Qed.
Lemma lem5013653 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1392 B s t) = (term1393 B s t).
Proof. exact (fun_ext (fun x : B => @lem5013652 B s x t)). Qed.
Lemma lem5013654 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5013655 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1389 B s t) = (term1394 B s t).
Proof. exact (MK_COMB (@lem5013654 B) (@lem5013653 B s t)). Qed.
Lemma lem5013656 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1388 B s t) = (term1394 B s t).
Proof. exact (TRANS (@lem5013648 B s t) (@lem5013655 B s t)). Qed.
Lemma lem5013657 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term491 B s t) = (term1395 B s t).
Proof. exact (fun_ext (fun x : B => @lem5013646 B s x t)). Qed.
Lemma lem5013658 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5013659 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term10 B s t) = (term1396 B s t).
Proof. exact (MK_COMB (@lem5013658 B) (@lem5013657 B s t)). Qed.
Lemma lem5013661 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1397 B s t) = (term1397 B s t).
Proof. exact (eq_refl (term1397 B s t)). Qed.
Lemma lem5013662 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1398 B s t) = (term1399 B s t).
Proof. exact (MK_COMB (@lem5013661 B s t) (@lem5013659 B s t)). Qed.
Lemma lem5013664 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1400 B s t) = (term1400 B s t).
Proof. exact (eq_refl (term1400 B s t)). Qed.
Lemma lem5013665 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1401 B s t) = (term1402 B s t).
Proof. exact (MK_COMB (@lem5013664 B s t) (@lem5013656 B s t)). Qed.
Lemma lem5013666 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5013667 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1403 B s t) = (term1404 B s t).
Proof. exact (MK_COMB (@lem5013666) (@lem5013665 B s t)). Qed.
Lemma lem5013668 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1405 B s t) = (term1406 B s t).
Proof. exact (MK_COMB (@lem5013667 B s t) (@lem5013662 B s t)). Qed.
Lemma lem5013669 {B : Type'} (s : B -> Prop) (t : B -> Prop) : ((@SUBSET B s t) = (term10 B s t)) = (term1405 B s t).
Proof. exact (@lem17784 (@SUBSET B s t) (term10 B s t)). Qed.
Lemma lem5013670 {B : Type'} (s : B -> Prop) (t : B -> Prop) : ((@SUBSET B s t) = (term10 B s t)) = (term1406 B s t).
Proof. exact (TRANS (@lem5013669 B s t) (@lem5013668 B s t)). Qed.
Lemma lem5013671 {B : Type'} (s : B -> Prop) : (term493 B s) = (term1407 B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5013670 B s t)). Qed.
Lemma lem5013672 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5013673 {B : Type'} (s : B -> Prop) : (term8 B s) = (term1408 B s).
Proof. exact (MK_COMB (@lem5013672 B) (@lem5013671 B s)). Qed.
Lemma lem5013674 {B : Type'} : (term494 B) = (term1409 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5013673 B s)). Qed.
Lemma lem5013675 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5013676 {B : Type'} : (term431 B) = (term1410 B).
Proof. exact (MK_COMB (@lem5013675 B) (@lem5013674 B)). Qed.
Lemma lem5013682 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term1019 A P Q) = (term1020 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5013683 {B : Type'} (P : type686 B) (Q : type686 B) : (term1045 B P Q) = (term1046 B P Q).
Proof. exact (@lem5013682 (B -> Prop) P Q). Qed.
Lemma lem5013684 {B : Type'} (s : B -> Prop) : (term1411 B s) = (term1412 B s).
Proof. exact (@lem5013683 B (term1413 B s) (term1414 B s)). Qed.
Lemma lem5013685 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1415 B s t) = (term1402 B s t).
Proof. exact (eq_refl (term1415 B s t)). Qed.
Lemma lem5013686 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5013687 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1416 B s t) = (term1404 B s t).
Proof. exact (MK_COMB (@lem5013686) (@lem5013685 B s t)). Qed.
Lemma lem5013688 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1417 B s t) = (term1399 B s t).
Proof. exact (eq_refl (term1417 B s t)). Qed.
Lemma lem5013689 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1418 B s t) = (term1406 B s t).
Proof. exact (MK_COMB (@lem5013687 B s t) (@lem5013688 B s t)). Qed.
Lemma lem5013690 {B : Type'} (s : B -> Prop) : (term1419 B s) = (term1407 B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5013689 B s t)). Qed.
Lemma lem5013691 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5013692 {B : Type'} (s : B -> Prop) : (term1411 B s) = (term1408 B s).
Proof. exact (MK_COMB (@lem5013691 B) (@lem5013690 B s)). Qed.
Lemma lem5013693 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5013694 {B : Type'} (s : B -> Prop) : (term1420 B s) = (term1421 B s).
Proof. exact (MK_COMB (@lem5013693) (@lem5013692 B s)). Qed.
Lemma lem5013695 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1415 B s t) = (term1402 B s t).
Proof. exact (eq_refl (term1415 B s t)). Qed.
Lemma lem5013696 {B : Type'} (s : B -> Prop) : (term1422 B s) = (term1413 B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5013695 B s t)). Qed.
Lemma lem5013697 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5013698 {B : Type'} (s : B -> Prop) : (term1423 B s) = (term1424 B s).
Proof. exact (MK_COMB (@lem5013697 B) (@lem5013696 B s)). Qed.
Lemma lem5013699 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5013700 {B : Type'} (s : B -> Prop) : (term1425 B s) = (term1426 B s).
Proof. exact (MK_COMB (@lem5013699) (@lem5013698 B s)). Qed.
Lemma lem5013701 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1417 B s t) = (term1399 B s t).
Proof. exact (eq_refl (term1417 B s t)). Qed.
Lemma lem5013702 {B : Type'} (s : B -> Prop) : (term1427 B s) = (term1414 B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5013701 B s t)). Qed.
Lemma lem5013703 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5013704 {B : Type'} (s : B -> Prop) : (term1428 B s) = (term1429 B s).
Proof. exact (MK_COMB (@lem5013703 B) (@lem5013702 B s)). Qed.
Lemma lem5013705 {B : Type'} (s : B -> Prop) : (term1412 B s) = (term1430 B s).
Proof. exact (MK_COMB (@lem5013700 B s) (@lem5013704 B s)). Qed.
Lemma lem5013706 {B : Type'} (s : B -> Prop) : ((term1411 B s) = (term1412 B s)) = ((term1408 B s) = (term1430 B s)).
Proof. exact (MK_COMB (@lem5013694 B s) (@lem5013705 B s)). Qed.
Lemma lem5013707 {B : Type'} (s : B -> Prop) : (term1408 B s) = (term1430 B s).
Proof. exact (EQ_MP (@lem5013706 B s) (@lem5013684 B s)). Qed.
Lemma lem5013900 {B : Type'} : (term1409 B) = (term1431 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5013707 B s)). Qed.
Lemma lem5013901 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5013902 {B : Type'} : (term1410 B) = (term1432 B).
Proof. exact (MK_COMB (@lem5013901 B) (@lem5013900 B)). Qed.
Lemma lem5013904 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term1019 A P Q) = (term1020 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5013905 {B : Type'} (P : type686 B) (Q : type686 B) : (term1045 B P Q) = (term1046 B P Q).
Proof. exact (@lem5013904 (B -> Prop) P Q). Qed.
Lemma lem5013906 {B : Type'} : (term1433 B) = (term1434 B).
Proof. exact (@lem5013905 B (term1435 B) (term1436 B)). Qed.
Lemma lem5013907 {B : Type'} (s : B -> Prop) : (term1437 B s) = (term1424 B s).
Proof. exact (eq_refl (term1437 B s)). Qed.
Lemma lem5013908 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5013909 {B : Type'} (s : B -> Prop) : (term1438 B s) = (term1426 B s).
Proof. exact (MK_COMB (@lem5013908) (@lem5013907 B s)). Qed.
Lemma lem5013910 {B : Type'} (s : B -> Prop) : (term1439 B s) = (term1429 B s).
Proof. exact (eq_refl (term1439 B s)). Qed.
Lemma lem5013911 {B : Type'} (s : B -> Prop) : (term1440 B s) = (term1430 B s).
Proof. exact (MK_COMB (@lem5013909 B s) (@lem5013910 B s)). Qed.
Lemma lem5013912 {B : Type'} : (term1441 B) = (term1431 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5013911 B s)). Qed.
Lemma lem5013913 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5013914 {B : Type'} : (term1433 B) = (term1432 B).
Proof. exact (MK_COMB (@lem5013913 B) (@lem5013912 B)). Qed.
Lemma lem5013915 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5013916 {B : Type'} : (term1442 B) = (term1443 B).
Proof. exact (MK_COMB (@lem5013915) (@lem5013914 B)). Qed.
Lemma lem5013917 {B : Type'} (s : B -> Prop) : (term1437 B s) = (term1424 B s).
Proof. exact (eq_refl (term1437 B s)). Qed.
Lemma lem5013918 {B : Type'} : (term1444 B) = (term1435 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5013917 B s)). Qed.
Lemma lem5013919 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5013920 {B : Type'} : (term1445 B) = (term1446 B).
Proof. exact (MK_COMB (@lem5013919 B) (@lem5013918 B)). Qed.
Lemma lem5013921 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5013922 {B : Type'} : (term1447 B) = (term1448 B).
Proof. exact (MK_COMB (@lem5013921) (@lem5013920 B)). Qed.
Lemma lem5013923 {B : Type'} (s : B -> Prop) : (term1439 B s) = (term1429 B s).
Proof. exact (eq_refl (term1439 B s)). Qed.
Lemma lem5013924 {B : Type'} : (term1449 B) = (term1436 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5013923 B s)). Qed.
Lemma lem5013925 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5013926 {B : Type'} : (term1450 B) = (term1451 B).
Proof. exact (MK_COMB (@lem5013925 B) (@lem5013924 B)). Qed.
Lemma lem5013927 {B : Type'} : (term1434 B) = (term1452 B).
Proof. exact (MK_COMB (@lem5013922 B) (@lem5013926 B)). Qed.
Lemma lem5013928 {B : Type'} : ((term1433 B) = (term1434 B)) = ((term1432 B) = (term1452 B)).
Proof. exact (MK_COMB (@lem5013916 B) (@lem5013927 B)). Qed.
Lemma lem5013929 {B : Type'} : (term1432 B) = (term1452 B).
Proof. exact (EQ_MP (@lem5013928 B) (@lem5013906 B)). Qed.
Lemma lem5014130 {B : Type'} : (term1410 B) = (term1452 B).
Proof. exact (TRANS (@lem5013902 B) (@lem5013929 B)). Qed.
Lemma lem5014132 {A : Type'} (P : Prop) (Q : A -> Prop) : (term818 A P Q) = (term819 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5014133 {B : Type'} (P : Prop) (Q : B -> Prop) : (term818 B P Q) = (term819 B P Q).
Proof. exact (@lem5014132 B P Q). Qed.
Lemma lem5014134 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1453 B s t) = (term1454 B s t).
Proof. exact (@lem5014133 B (@SUBSET B s t) (term1393 B s t)). Qed.
Lemma lem5014135 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term1455 B s t x) = (term1386 B s x t).
Proof. exact (eq_refl (term1455 B s t x)). Qed.
Lemma lem5014136 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1456 B s t) = (term1393 B s t).
Proof. exact (fun_ext (fun x : B => @lem5014135 B s x t)). Qed.
Lemma lem5014137 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5014138 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1457 B s t) = (term1394 B s t).
Proof. exact (MK_COMB (@lem5014137 B) (@lem5014136 B s t)). Qed.
Lemma lem5014139 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1400 B s t) = (term1400 B s t).
Proof. exact (eq_refl (term1400 B s t)). Qed.
Lemma lem5014140 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1453 B s t) = (term1402 B s t).
Proof. exact (MK_COMB (@lem5014139 B s t) (@lem5014138 B s t)). Qed.
Lemma lem5014141 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5014142 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1458 B s t) = (term1459 B s t).
Proof. exact (MK_COMB (@lem5014141) (@lem5014140 B s t)). Qed.
Lemma lem5014143 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term1455 B s t x) = (term1386 B s x t).
Proof. exact (eq_refl (term1455 B s t x)). Qed.
Lemma lem5014144 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1400 B s t) = (term1400 B s t).
Proof. exact (eq_refl (term1400 B s t)). Qed.
Lemma lem5014145 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term1460 B s t x) = (term1461 B s x t).
Proof. exact (MK_COMB (@lem5014144 B s t) (@lem5014143 B s x t)). Qed.
Lemma lem5014146 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1462 B s t) = (term1463 B s t).
Proof. exact (fun_ext (fun x : B => @lem5014145 B s x t)). Qed.
Lemma lem5014147 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5014148 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1454 B s t) = (term1464 B s t).
Proof. exact (MK_COMB (@lem5014147 B) (@lem5014146 B s t)). Qed.
Lemma lem5014149 {B : Type'} (s : B -> Prop) (t : B -> Prop) : ((term1453 B s t) = (term1454 B s t)) = ((term1402 B s t) = (term1464 B s t)).
Proof. exact (MK_COMB (@lem5014142 B s t) (@lem5014148 B s t)). Qed.
Lemma lem5014150 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1402 B s t) = (term1464 B s t).
Proof. exact (EQ_MP (@lem5014149 B s t) (@lem5014134 B s t)). Qed.
Lemma lem5014151 {B : Type'} (s : B -> Prop) : (term1413 B s) = (term1465 B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5014150 B s t)). Qed.
Lemma lem5014152 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5014153 {B : Type'} (s : B -> Prop) : (term1424 B s) = (term1466 B s).
Proof. exact (MK_COMB (@lem5014152 B) (@lem5014151 B s)). Qed.
Lemma lem5014155 {A B : Type'} (P : type1413 A B) : (term1103 A B P) = (term1104 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5014156 {B : Type'} (P : type672 B) : (term1467 B P) = (term1468 B P).
Proof. exact (@lem5014155 (B -> Prop) B P). Qed.
Lemma lem5014157 {B : Type'} (s : B -> Prop) : (term1469 B s) = (term1470 B s).
Proof. exact (@lem5014156 B (term1471 B s)). Qed.
Lemma lem5014158 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1472 B s t) = (term1463 B s t).
Proof. exact (eq_refl (term1472 B s t)). Qed.
Lemma lem5014159 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5014160 {B : Type'} (s : B -> Prop) (t : B -> Prop) (x : B) : (term1473 B s t x) = (term1474 B s t x).
Proof. exact (MK_COMB (@lem5014158 B s t) (@lem5014159 B x)). Qed.
Lemma lem5014161 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term1474 B s t x) = (term1461 B s x t).
Proof. exact (eq_refl (term1474 B s t x)). Qed.
Lemma lem5014162 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term1473 B s t x) = (term1461 B s x t).
Proof. exact (TRANS (@lem5014160 B s t x) (@lem5014161 B s x t)). Qed.
Lemma lem5014163 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1475 B s t) = (term1463 B s t).
Proof. exact (fun_ext (fun x : B => @lem5014162 B s x t)). Qed.
Lemma lem5014164 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5014165 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1476 B s t) = (term1464 B s t).
Proof. exact (MK_COMB (@lem5014164 B) (@lem5014163 B s t)). Qed.
Lemma lem5014166 {B : Type'} (s : B -> Prop) : (term1477 B s) = (term1465 B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5014165 B s t)). Qed.
Lemma lem5014167 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5014168 {B : Type'} (s : B -> Prop) : (term1469 B s) = (term1466 B s).
Proof. exact (MK_COMB (@lem5014167 B) (@lem5014166 B s)). Qed.
Lemma lem5014169 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5014170 {B : Type'} (s : B -> Prop) : (term1478 B s) = (term1479 B s).
Proof. exact (MK_COMB (@lem5014169) (@lem5014168 B s)). Qed.
Lemma lem5014171 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1472 B s t) = (term1463 B s t).
Proof. exact (eq_refl (term1472 B s t)). Qed.
Lemma lem5014172 {B : Type'} (x : type684 B) (t : B -> Prop) : (x t) = (x t).
Proof. exact (eq_refl (x t)). Qed.
Lemma lem5014173 {B : Type'} (s : B -> Prop) (x : type684 B) (t : B -> Prop) : (term1480 B s x t) = (term1481 B s x t).
Proof. exact (MK_COMB (@lem5014171 B s t) (@lem5014172 B x t)). Qed.
Lemma lem5014174 {B : Type'} (s : B -> Prop) (x : type684 B) (t : B -> Prop) : (term1481 B s x t) = (term1482 B s x t).
Proof. exact (eq_refl (term1481 B s x t)). Qed.
Lemma lem5014175 {B : Type'} (s : B -> Prop) (x : type684 B) (t : B -> Prop) : (term1480 B s x t) = (term1482 B s x t).
Proof. exact (TRANS (@lem5014173 B s x t) (@lem5014174 B s x t)). Qed.
Lemma lem5014176 {B : Type'} (s : B -> Prop) (x : type684 B) : (term1483 B s x) = (term1484 B s x).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5014175 B s x t)). Qed.
Lemma lem5014177 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5014178 {B : Type'} (s : B -> Prop) (x : type684 B) : (term1485 B s x) = (term1486 B s x).
Proof. exact (MK_COMB (@lem5014177 B) (@lem5014176 B s x)). Qed.
Lemma lem5014179 {B : Type'} (s : B -> Prop) : (term1487 B s) = (term1488 B s).
Proof. exact (fun_ext (fun x : type684 B => @lem5014178 B s x)). Qed.
Lemma lem5014180 {B : Type'} : (@ex ((B -> Prop) -> B)) = (@ex ((B -> Prop) -> B)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> B))). Qed.
Lemma lem5014181 {B : Type'} (s : B -> Prop) : (term1470 B s) = (term1489 B s).
Proof. exact (MK_COMB (@lem5014180 B) (@lem5014179 B s)). Qed.
Lemma lem5014182 {B : Type'} (s : B -> Prop) : ((term1469 B s) = (term1470 B s)) = ((term1466 B s) = (term1489 B s)).
Proof. exact (MK_COMB (@lem5014170 B s) (@lem5014181 B s)). Qed.
Lemma lem5014183 {B : Type'} (s : B -> Prop) : (term1466 B s) = (term1489 B s).
Proof. exact (EQ_MP (@lem5014182 B s) (@lem5014157 B s)). Qed.
Lemma lem5014184 {B : Type'} (s : B -> Prop) : (term1424 B s) = (term1489 B s).
Proof. exact (TRANS (@lem5014153 B s) (@lem5014183 B s)). Qed.
Lemma lem5014185 {B : Type'} : (term1435 B) = (term1490 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5014184 B s)). Qed.
Lemma lem5014186 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5014187 {B : Type'} : (term1446 B) = (term1491 B).
Proof. exact (MK_COMB (@lem5014186 B) (@lem5014185 B)). Qed.
Lemma lem5014189 {A B : Type'} (P : type1413 A B) : (term1103 A B P) = (term1104 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5014190 {B : Type'} (P : type597 B) : (term1492 B P) = (term1493 B P).
Proof. exact (@lem5014189 (B -> Prop) (type684 B) P). Qed.
Lemma lem5014191 {B : Type'} : (term1494 B) = (term1495 B).
Proof. exact (@lem5014190 B (term1496 B)). Qed.
Lemma lem5014192 {B : Type'} (s : B -> Prop) : (term1497 B s) = (term1488 B s).
Proof. exact (eq_refl (term1497 B s)). Qed.
Lemma lem5014193 {B : Type'} (x : type684 B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5014194 {B : Type'} (s : B -> Prop) (x : type684 B) : (term1498 B s x) = (term1499 B s x).
Proof. exact (MK_COMB (@lem5014192 B s) (@lem5014193 B x)). Qed.
Lemma lem5014195 {B : Type'} (s : B -> Prop) (x : type684 B) : (term1499 B s x) = (term1486 B s x).
Proof. exact (eq_refl (term1499 B s x)). Qed.
Lemma lem5014196 {B : Type'} (s : B -> Prop) (x : type684 B) : (term1498 B s x) = (term1486 B s x).
Proof. exact (TRANS (@lem5014194 B s x) (@lem5014195 B s x)). Qed.
Lemma lem5014197 {B : Type'} (s : B -> Prop) : (term1500 B s) = (term1488 B s).
Proof. exact (fun_ext (fun x : type684 B => @lem5014196 B s x)). Qed.
Lemma lem5014198 {B : Type'} : (@ex ((B -> Prop) -> B)) = (@ex ((B -> Prop) -> B)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> B))). Qed.
Lemma lem5014199 {B : Type'} (s : B -> Prop) : (term1501 B s) = (term1489 B s).
Proof. exact (MK_COMB (@lem5014198 B) (@lem5014197 B s)). Qed.
Lemma lem5014200 {B : Type'} : (term1502 B) = (term1490 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5014199 B s)). Qed.
Lemma lem5014201 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5014202 {B : Type'} : (term1494 B) = (term1491 B).
Proof. exact (MK_COMB (@lem5014201 B) (@lem5014200 B)). Qed.
Lemma lem5014203 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5014204 {B : Type'} : (term1503 B) = (term1504 B).
Proof. exact (MK_COMB (@lem5014203) (@lem5014202 B)). Qed.
Lemma lem5014205 {B : Type'} (s : B -> Prop) : (term1497 B s) = (term1488 B s).
Proof. exact (eq_refl (term1497 B s)). Qed.
Lemma lem5014206 {B : Type'} (x : type638 B) (s : B -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem5014207 {B : Type'} (x : type638 B) (s : B -> Prop) : (term1505 B x s) = (term1506 B x s).
Proof. exact (MK_COMB (@lem5014205 B s) (@lem5014206 B x s)). Qed.
Lemma lem5014208 {B : Type'} (x : type638 B) (s : B -> Prop) : (term1506 B x s) = (term1507 B x s).
Proof. exact (eq_refl (term1506 B x s)). Qed.
Lemma lem5014209 {B : Type'} (x : type638 B) (s : B -> Prop) : (term1505 B x s) = (term1507 B x s).
Proof. exact (TRANS (@lem5014207 B x s) (@lem5014208 B x s)). Qed.
Lemma lem5014210 {B : Type'} (x : type638 B) : (term1508 B x) = (term1509 B x).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5014209 B x s)). Qed.
Lemma lem5014211 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5014212 {B : Type'} (x : type638 B) : (term1510 B x) = (term1511 B x).
Proof. exact (MK_COMB (@lem5014211 B) (@lem5014210 B x)). Qed.
Lemma lem5014213 {B : Type'} : (term1512 B) = (term1513 B).
Proof. exact (fun_ext (fun x : type638 B => @lem5014212 B x)). Qed.
Lemma lem5014214 {B : Type'} : (@ex ((B -> Prop) -> (B -> Prop) -> B)) = (@ex ((B -> Prop) -> (B -> Prop) -> B)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> (B -> Prop) -> B))). Qed.
Lemma lem5014215 {B : Type'} : (term1495 B) = (term1514 B).
Proof. exact (MK_COMB (@lem5014214 B) (@lem5014213 B)). Qed.
Lemma lem5014216 {B : Type'} : ((term1494 B) = (term1495 B)) = ((term1491 B) = (term1514 B)).
Proof. exact (MK_COMB (@lem5014204 B) (@lem5014215 B)). Qed.
Lemma lem5014217 {B : Type'} : (term1491 B) = (term1514 B).
Proof. exact (EQ_MP (@lem5014216 B) (@lem5014191 B)). Qed.
Lemma lem5014218 {B : Type'} : (term1446 B) = (term1514 B).
Proof. exact (TRANS (@lem5014187 B) (@lem5014217 B)). Qed.
Lemma lem5014219 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5014220 {B : Type'} : (term1448 B) = (term1515 B).
Proof. exact (MK_COMB (@lem5014219) (@lem5014218 B)). Qed.
Lemma lem5014221 {B : Type'} : (term1451 B) = (term1451 B).
Proof. exact (eq_refl (term1451 B)). Qed.
Lemma lem5014222 {B : Type'} : (term1452 B) = (term1516 B).
Proof. exact (MK_COMB (@lem5014220 B) (@lem5014221 B)). Qed.
Lemma lem5014224 {A : Type'} (P : A -> Prop) (Q : Prop) : (term834 A P Q) = (term835 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5014225 {B : Type'} (P : type139 B) (Q : Prop) : (term1517 B P Q) = (term1518 B P Q).
Proof. exact (@lem5014224 (type638 B) P Q). Qed.
Lemma lem5014226 {B : Type'} : (term1519 B) = (term1520 B).
Proof. exact (@lem5014225 B (term1513 B) (term1451 B)). Qed.
Lemma lem5014227 {B : Type'} (x : type638 B) : (term1521 B x) = (term1511 B x).
Proof. exact (eq_refl (term1521 B x)). Qed.
Lemma lem5014228 {B : Type'} : (term1522 B) = (term1513 B).
Proof. exact (fun_ext (fun x : type638 B => @lem5014227 B x)). Qed.
Lemma lem5014229 {B : Type'} : (@ex ((B -> Prop) -> (B -> Prop) -> B)) = (@ex ((B -> Prop) -> (B -> Prop) -> B)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> (B -> Prop) -> B))). Qed.
Lemma lem5014230 {B : Type'} : (term1523 B) = (term1514 B).
Proof. exact (MK_COMB (@lem5014229 B) (@lem5014228 B)). Qed.
Lemma lem5014231 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5014232 {B : Type'} : (term1524 B) = (term1515 B).
Proof. exact (MK_COMB (@lem5014231) (@lem5014230 B)). Qed.
Lemma lem5014233 {B : Type'} : (term1451 B) = (term1451 B).
Proof. exact (eq_refl (term1451 B)). Qed.
Lemma lem5014234 {B : Type'} : (term1519 B) = (term1516 B).
Proof. exact (MK_COMB (@lem5014232 B) (@lem5014233 B)). Qed.
Lemma lem5014235 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5014236 {B : Type'} : (term1525 B) = (term1526 B).
Proof. exact (MK_COMB (@lem5014235) (@lem5014234 B)). Qed.
Lemma lem5014237 {B : Type'} (x : type638 B) : (term1521 B x) = (term1511 B x).
Proof. exact (eq_refl (term1521 B x)). Qed.
Lemma lem5014238 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5014239 {B : Type'} (x : type638 B) : (term1527 B x) = (term1528 B x).
Proof. exact (MK_COMB (@lem5014238) (@lem5014237 B x)). Qed.
Lemma lem5014240 {B : Type'} : (term1451 B) = (term1451 B).
Proof. exact (eq_refl (term1451 B)). Qed.
Lemma lem5014241 {B : Type'} (x : type638 B) : (term1529 B x) = (term1530 B x).
Proof. exact (MK_COMB (@lem5014239 B x) (@lem5014240 B)). Qed.
Lemma lem5014242 {B : Type'} : (term1531 B) = (term1532 B).
Proof. exact (fun_ext (fun x : type638 B => @lem5014241 B x)). Qed.
Lemma lem5014243 {B : Type'} : (@ex ((B -> Prop) -> (B -> Prop) -> B)) = (@ex ((B -> Prop) -> (B -> Prop) -> B)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> (B -> Prop) -> B))). Qed.
Lemma lem5014244 {B : Type'} : (term1520 B) = (term1533 B).
Proof. exact (MK_COMB (@lem5014243 B) (@lem5014242 B)). Qed.
Lemma lem5014245 {B : Type'} : ((term1519 B) = (term1520 B)) = ((term1516 B) = (term1533 B)).
Proof. exact (MK_COMB (@lem5014236 B) (@lem5014244 B)). Qed.
Lemma lem5014246 {B : Type'} : (term1516 B) = (term1533 B).
Proof. exact (EQ_MP (@lem5014245 B) (@lem5014226 B)). Qed.
Lemma lem5014247 {B : Type'} : (term1452 B) = (term1533 B).
Proof. exact (TRANS (@lem5014222 B) (@lem5014246 B)). Qed.
Lemma lem5014248 {B : Type'} : (term1410 B) = (term1533 B).
Proof. exact (TRANS (@lem5014130 B) (@lem5014247 B)). Qed.
Lemma lem5014249 {B : Type'} : (term431 B) = (term1533 B).
Proof. exact (TRANS (@lem5013676 B) (@lem5014248 B)). Qed.
Lemma lem5014250 {B : Type'} (h1 : term431 B) : term1533 B.
Proof. exact (EQ_MP (@lem5014249 B) (@lem5008917 B h1)). Qed.
Lemma lem5014251 {B : Type'} (x' : type638 B) (h1 : term1530 B x') : term1530 B x'.
Proof. exact (h1). Qed.
Lemma lem5014254 {A B : Type'} (x'''' : type1448 A B) (h1 : term1381 A B x'''') : term1381 A B x''''.
Proof. exact (h1). Qed.
Lemma lem5014256 {A B : Type'} (x'''''' : B) (t : B -> Prop) (y : B) (x : A) (s : A -> Prop) (f : A -> B) (h1 : term990 A B x'''''' t y x s f) : term990 A B x'''''' t y x s f.
Proof. exact (h1). Qed.
Lemma lem5014257 {A B : Type'} (x'''''' : B) (t : B -> Prop) (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x''''''' : A) (h1 : term988 A B x'''''' t y x s f x''''''') : term988 A B x'''''' t y x s f x'''''''.
Proof. exact (h1). Qed.
Lemma lem5014258 {A B : Type'} (x'''''' : B) (t : B -> Prop) (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term985 A B x'''''' t y x s f x''''''' y') : term985 A B x'''''' t y x s f x''''''' y'.
Proof. exact (h1). Qed.
Lemma lem5014288 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5014295 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5014296 {B : Type'} (f : type1364 B) (x : B) : (f x) = (@I (B -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem5014295 B (type686 B) f x). Qed.
Lemma lem5014297 {B : Type'} (y : B) : (@IN B y) = (@I (B -> (B -> Prop) -> Prop) (@IN B) y).
Proof. exact (@lem5014296 B (@IN B) y). Qed.
Lemma lem5014298 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5014299 {B : Type'} (y : B) (t : B -> Prop) : (@IN B y t) = (@I (B -> (B -> Prop) -> Prop) (@IN B) y t).
Proof. exact (MK_COMB (@lem5014297 B y) (@lem5014298 B t)). Qed.
Lemma lem5014301 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5014302 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem5014301 (B -> Prop) Prop f x). Qed.
Lemma lem5014303 {B : Type'} (y : B) (t : B -> Prop) : (@I (B -> (B -> Prop) -> Prop) (@IN B) y t) = (term1534 B y t).
Proof. exact (@lem5014302 B (@I (B -> (B -> Prop) -> Prop) (@IN B) y) t). Qed.
Lemma lem5014305 {B : Type'} (y : B) (t : B -> Prop) : (@IN B y t) = (term1534 B y t).
Proof. exact (TRANS (@lem5014299 B y t) (@lem5014303 B y t)). Qed.
Lemma lem5014306 {B : Type'} (y : B) (t : B -> Prop) : (term238 B y t) = (term1535 B y t).
Proof. exact (MK_COMB (@lem5014288) (@lem5014305 B y t)). Qed.
Lemma lem5014349 {B : Type'} : (@SUBSET B) = (@SUBSET B).
Proof. exact (eq_refl (@SUBSET B)). Qed.
Lemma lem5014356 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5014357 {A B : Type'} (f : type528 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) f x).
Proof. exact (@lem5014356 (A -> B) (type678 A B) f x). Qed.
Lemma lem5014358 {A B : Type'} (f : A -> B) : (@IMAGE A B f) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f).
Proof. exact (@lem5014357 A B (@IMAGE A B) f). Qed.
Lemma lem5014359 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5014360 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@IMAGE A B f s) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f s).
Proof. exact (MK_COMB (@lem5014358 A B f) (@lem5014359 A s)). Qed.
Lemma lem5014362 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5014363 {A B : Type'} (f : type678 A B) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> B -> Prop) f x).
Proof. exact (@lem5014362 (A -> Prop) (B -> Prop) f x). Qed.
Lemma lem5014364 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f s) = (term1536 A B f s).
Proof. exact (@lem5014363 A B (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f) s). Qed.
Lemma lem5014366 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@IMAGE A B f s) = (term1536 A B f s).
Proof. exact (TRANS (@lem5014360 A B f s) (@lem5014364 A B f s)). Qed.
Lemma lem5014367 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5014368 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term1537 A B f s) = (term1538 A B f s).
Proof. exact (MK_COMB (@lem5014349 B) (@lem5014366 A B f s)). Qed.
Lemma lem5014369 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term364 A B f s t) = (term1539 A B f s t).
Proof. exact (MK_COMB (@lem5014368 A B f s) (@lem5014367 B t)). Qed.
Lemma lem5014371 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5014372 {B : Type'} (f : type639 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem5014371 (B -> Prop) (type686 B) f x). Qed.
Lemma lem5014373 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term1538 A B f s) = (term1540 A B f s).
Proof. exact (@lem5014372 B (@SUBSET B) (term1536 A B f s)). Qed.
Lemma lem5014374 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5014375 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term1539 A B f s t) = (term1541 A B f s t).
Proof. exact (MK_COMB (@lem5014373 A B f s) (@lem5014374 B t)). Qed.
Lemma lem5014377 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5014378 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem5014377 (B -> Prop) Prop f x). Qed.
Lemma lem5014379 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term1541 A B f s t) = (term1542 A B f s t).
Proof. exact (@lem5014378 B (term1540 A B f s) t). Qed.
Lemma lem5014380 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term1539 A B f s t) = (term1542 A B f s t).
Proof. exact (TRANS (@lem5014375 A B f s t) (@lem5014379 A B f s t)). Qed.
Lemma lem5014381 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term364 A B f s t) = (term1542 A B f s t).
Proof. exact (TRANS (@lem5014369 A B f s t) (@lem5014380 A B f s t)). Qed.
Lemma lem5014387 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem5014388 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5014389 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5014394 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5014396 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem5014394 A B f x). Qed.
Lemma lem5014401 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5014402 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem5014401 A B f x). Qed.
Lemma lem5014404 {A B : Type'} (f : A -> B) (y : A) : (f y) = (@I (A -> B) f y).
Proof. exact (@lem5014402 A B f y). Qed.
Lemma lem5014405 {A B : Type'} (f : A -> B) (x : A) : (term515 A B f x) = (term1543 A B f x).
Proof. exact (MK_COMB (@lem5014389 B) (@lem5014396 A B f x)). Qed.
Lemma lem5014406 {A B : Type'} (x : A) (f : A -> B) (y : A) : ((f x) = (f y)) = ((@I (A -> B) f x) = (@I (A -> B) f y)).
Proof. exact (MK_COMB (@lem5014405 A B f x) (@lem5014404 A B f y)). Qed.
Lemma lem5014407 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term1544 A B x f y) = (term1545 A B x f y).
Proof. exact (MK_COMB (@lem5014388) (@lem5014406 A B x f y)). Qed.
Lemma lem5014408 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5014409 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term1546 A B x f y) = (term1547 A B x f y).
Proof. exact (MK_COMB (@lem5014408) (@lem5014407 A B x f y)). Qed.
Lemma lem5014410 {A B : Type'} (f : A -> B) (x : A) (y : A) : (term608 A B f x y) = (term1548 A B f x y).
Proof. exact (MK_COMB (@lem5014409 A B x f y) (@lem5014387 A x y)). Qed.
Lemma lem5014411 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5014418 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5014419 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5014418 A (type686 A) f x). Qed.
Lemma lem5014420 {A : Type'} (y : A) : (@IN A y) = (@I (A -> (A -> Prop) -> Prop) (@IN A) y).
Proof. exact (@lem5014419 A (@IN A) y). Qed.
Lemma lem5014421 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5014422 {A : Type'} (y : A) (s : A -> Prop) : (@IN A y s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) y s).
Proof. exact (MK_COMB (@lem5014420 A y) (@lem5014421 A s)). Qed.
Lemma lem5014424 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5014425 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5014424 (A -> Prop) Prop f x). Qed.
Lemma lem5014426 {A : Type'} (y : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) y s) = (term1534 A y s).
Proof. exact (@lem5014425 A (@I (A -> (A -> Prop) -> Prop) (@IN A) y) s). Qed.
Lemma lem5014428 {A : Type'} (y : A) (s : A -> Prop) : (@IN A y s) = (term1534 A y s).
Proof. exact (TRANS (@lem5014422 A y s) (@lem5014426 A y s)). Qed.
Lemma lem5014429 {A : Type'} (y : A) (s : A -> Prop) : (term238 A y s) = (term1535 A y s).
Proof. exact (MK_COMB (@lem5014411) (@lem5014428 A y s)). Qed.
Lemma lem5014430 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5014431 {A : Type'} (y : A) (s : A -> Prop) : (term609 A y s) = (term1549 A y s).
Proof. exact (MK_COMB (@lem5014430) (@lem5014429 A y s)). Qed.
Lemma lem5014432 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term611 A B s f x y) = (term1550 A B s f x y).
Proof. exact (MK_COMB (@lem5014431 A y s) (@lem5014410 A B f x y)). Qed.
Lemma lem5014433 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term612 A B s f x) = (term1551 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem5014432 A B s f x y)). Qed.
Lemma lem5014434 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5014435 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term613 A B s f x) = (term1552 A B s f x).
Proof. exact (MK_COMB (@lem5014434 A) (@lem5014433 A B s f x)). Qed.
Lemma lem5014436 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5014443 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5014444 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5014443 A (type686 A) f x). Qed.
Lemma lem5014445 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem5014444 A (@IN A) x). Qed.
Lemma lem5014446 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5014447 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x s).
Proof. exact (MK_COMB (@lem5014445 A x) (@lem5014446 A s)). Qed.
Lemma lem5014449 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5014450 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5014449 (A -> Prop) Prop f x). Qed.
Lemma lem5014451 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x s) = (term1534 A x s).
Proof. exact (@lem5014450 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) s). Qed.
Lemma lem5014453 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (term1534 A x s).
Proof. exact (TRANS (@lem5014447 A x s) (@lem5014451 A x s)). Qed.
Lemma lem5014454 {A : Type'} (x : A) (s : A -> Prop) : (term238 A x s) = (term1535 A x s).
Proof. exact (MK_COMB (@lem5014436) (@lem5014453 A x s)). Qed.
Lemma lem5014455 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5014456 {A : Type'} (x : A) (s : A -> Prop) : (term609 A x s) = (term1549 A x s).
Proof. exact (MK_COMB (@lem5014455) (@lem5014454 A x s)). Qed.
Lemma lem5014457 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term615 A B s f x) = (term1553 A B s f x).
Proof. exact (MK_COMB (@lem5014456 A x s) (@lem5014435 A B s f x)). Qed.
Lemma lem5014458 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term616 A B s f) = (term1554 A B s f).
Proof. exact (fun_ext (fun x : A => @lem5014457 A B s f x)). Qed.
Lemma lem5014459 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5014460 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term617 A B s f) = (term1555 A B s f).
Proof. exact (MK_COMB (@lem5014459 A) (@lem5014458 A B s f)). Qed.
Lemma lem5014461 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term122 A B s f) : term1555 A B s f.
Proof. exact (EQ_MP (@lem5014460 A B s f) (@lem5009079 A B s f h1)). Qed.
Lemma lem5014468 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5014469 {B : Type'} (f : type1364 B) (x : B) : (f x) = (@I (B -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem5014468 B (type686 B) f x). Qed.
Lemma lem5014470 {B : Type'} (x : B) : (@IN B x) = (@I (B -> (B -> Prop) -> Prop) (@IN B) x).
Proof. exact (@lem5014469 B (@IN B) x). Qed.
Lemma lem5014471 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5014472 {B : Type'} (x : B) (t : B -> Prop) : (@IN B x t) = (@I (B -> (B -> Prop) -> Prop) (@IN B) x t).
Proof. exact (MK_COMB (@lem5014470 B x) (@lem5014471 B t)). Qed.
Lemma lem5014474 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5014475 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem5014474 (B -> Prop) Prop f x). Qed.
Lemma lem5014476 {B : Type'} (x : B) (t : B -> Prop) : (@I (B -> (B -> Prop) -> Prop) (@IN B) x t) = (term1534 B x t).
Proof. exact (@lem5014475 B (@I (B -> (B -> Prop) -> Prop) (@IN B) x) t). Qed.
Lemma lem5014478 {B : Type'} (x : B) (t : B -> Prop) : (@IN B x t) = (term1534 B x t).
Proof. exact (TRANS (@lem5014472 B x t) (@lem5014476 B x t)). Qed.
Lemma lem5014479 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5014486 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5014487 {B : Type'} (f : type1364 B) (x : B) : (f x) = (@I (B -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem5014486 B (type686 B) f x). Qed.
Lemma lem5014488 {B : Type'} (x : B) : (@IN B x) = (@I (B -> (B -> Prop) -> Prop) (@IN B) x).
Proof. exact (@lem5014487 B (@IN B) x). Qed.
Lemma lem5014489 {B : Type'} (s : B -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5014490 {B : Type'} (x : B) (s : B -> Prop) : (@IN B x s) = (@I (B -> (B -> Prop) -> Prop) (@IN B) x s).
Proof. exact (MK_COMB (@lem5014488 B x) (@lem5014489 B s)). Qed.
Lemma lem5014492 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5014493 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem5014492 (B -> Prop) Prop f x). Qed.
Lemma lem5014494 {B : Type'} (x : B) (s : B -> Prop) : (@I (B -> (B -> Prop) -> Prop) (@IN B) x s) = (term1534 B x s).
Proof. exact (@lem5014493 B (@I (B -> (B -> Prop) -> Prop) (@IN B) x) s). Qed.
Lemma lem5014496 {B : Type'} (x : B) (s : B -> Prop) : (@IN B x s) = (term1534 B x s).
Proof. exact (TRANS (@lem5014490 B x s) (@lem5014494 B x s)). Qed.
Lemma lem5014497 {B : Type'} (x : B) (s : B -> Prop) : (term238 B x s) = (term1535 B x s).
Proof. exact (MK_COMB (@lem5014479) (@lem5014496 B x s)). Qed.
Lemma lem5014498 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5014499 {B : Type'} (x : B) (s : B -> Prop) : (term609 B x s) = (term1549 B x s).
Proof. exact (MK_COMB (@lem5014498) (@lem5014497 B x s)). Qed.
Lemma lem5014500 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term1387 B s x t) = (term1556 B s x t).
Proof. exact (MK_COMB (@lem5014499 B x s) (@lem5014478 B x t)). Qed.
Lemma lem5014501 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1395 B s t) = (term1557 B s t).
Proof. exact (fun_ext (fun x : B => @lem5014500 B s x t)). Qed.
Lemma lem5014502 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5014503 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1396 B s t) = (term1558 B s t).
Proof. exact (MK_COMB (@lem5014502 B) (@lem5014501 B s t)). Qed.
Lemma lem5014504 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5014511 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5014512 {B : Type'} (f : type639 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem5014511 (B -> Prop) (type686 B) f x). Qed.
Lemma lem5014513 {B : Type'} (s : B -> Prop) : (@SUBSET B s) = (@I ((B -> Prop) -> (B -> Prop) -> Prop) (@SUBSET B) s).
Proof. exact (@lem5014512 B (@SUBSET B) s). Qed.
Lemma lem5014514 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5014515 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (@I ((B -> Prop) -> (B -> Prop) -> Prop) (@SUBSET B) s t).
Proof. exact (MK_COMB (@lem5014513 B s) (@lem5014514 B t)). Qed.
Lemma lem5014517 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5014518 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem5014517 (B -> Prop) Prop f x). Qed.
Lemma lem5014519 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@I ((B -> Prop) -> (B -> Prop) -> Prop) (@SUBSET B) s t) = (term1559 B s t).
Proof. exact (@lem5014518 B (@I ((B -> Prop) -> (B -> Prop) -> Prop) (@SUBSET B) s) t). Qed.
Lemma lem5014521 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (term1559 B s t).
Proof. exact (TRANS (@lem5014515 B s t) (@lem5014519 B s t)). Qed.
Lemma lem5014522 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1560 B s t) = (term1561 B s t).
Proof. exact (MK_COMB (@lem5014504) (@lem5014521 B s t)). Qed.
Lemma lem5014523 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5014524 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1397 B s t) = (term1562 B s t).
Proof. exact (MK_COMB (@lem5014523) (@lem5014522 B s t)). Qed.
Lemma lem5014525 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1399 B s t) = (term1563 B s t).
Proof. exact (MK_COMB (@lem5014524 B s t) (@lem5014503 B s t)). Qed.
Lemma lem5014526 {B : Type'} (s : B -> Prop) : (term1414 B s) = (term1564 B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5014525 B s t)). Qed.
Lemma lem5014527 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5014528 {B : Type'} (s : B -> Prop) : (term1429 B s) = (term1565 B s).
Proof. exact (MK_COMB (@lem5014527 B) (@lem5014526 B s)). Qed.
Lemma lem5014529 {B : Type'} : (term1436 B) = (term1566 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5014528 B s)). Qed.
Lemma lem5014530 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5014531 {B : Type'} : (term1451 B) = (term1567 B).
Proof. exact (MK_COMB (@lem5014530 B) (@lem5014529 B)). Qed.
Lemma lem5014532 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5014533 {B : Type'} : (@IN B) = (@IN B).
Proof. exact (eq_refl (@IN B)). Qed.
Lemma lem5014540 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5014541 {B : Type'} (f : type638 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> (B -> Prop) -> B) f x).
Proof. exact (@lem5014540 (B -> Prop) (type684 B) f x). Qed.
Lemma lem5014542 {B : Type'} (x' : type638 B) (s : B -> Prop) : (x' s) = (@I ((B -> Prop) -> (B -> Prop) -> B) x' s).
Proof. exact (@lem5014541 B x' s). Qed.
Lemma lem5014543 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5014544 {B : Type'} (x' : type638 B) (s : B -> Prop) (t : B -> Prop) : (x' s t) = (@I ((B -> Prop) -> (B -> Prop) -> B) x' s t).
Proof. exact (MK_COMB (@lem5014542 B x' s) (@lem5014543 B t)). Qed.
Lemma lem5014546 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5014547 {B : Type'} (f : type684 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> B) f x).
Proof. exact (@lem5014546 (B -> Prop) B f x). Qed.
Lemma lem5014548 {B : Type'} (x' : type638 B) (s : B -> Prop) (t : B -> Prop) : (@I ((B -> Prop) -> (B -> Prop) -> B) x' s t) = (term1568 B x' s t).
Proof. exact (@lem5014547 B (@I ((B -> Prop) -> (B -> Prop) -> B) x' s) t). Qed.
Lemma lem5014550 {B : Type'} (x' : type638 B) (s : B -> Prop) (t : B -> Prop) : (x' s t) = (term1568 B x' s t).
Proof. exact (TRANS (@lem5014544 B x' s t) (@lem5014548 B x' s t)). Qed.
Lemma lem5014551 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5014552 {B : Type'} (x' : type638 B) (s : B -> Prop) (t : B -> Prop) : (term1569 B x' s t) = (term1570 B x' s t).
Proof. exact (MK_COMB (@lem5014533 B) (@lem5014550 B x' s t)). Qed.
Lemma lem5014553 {B : Type'} (x' : type638 B) (s : B -> Prop) (t : B -> Prop) : (term1571 B x' s t) = (term1572 B x' s t).
Proof. exact (MK_COMB (@lem5014552 B x' s t) (@lem5014551 B t)). Qed.
Lemma lem5014555 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5014556 {B : Type'} (f : type1364 B) (x : B) : (f x) = (@I (B -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem5014555 B (type686 B) f x). Qed.
Lemma lem5014557 {B : Type'} (x' : type638 B) (s : B -> Prop) (t : B -> Prop) : (term1570 B x' s t) = (term1573 B x' s t).
Proof. exact (@lem5014556 B (@IN B) (term1568 B x' s t)). Qed.
Lemma lem5014558 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5014559 {B : Type'} (x' : type638 B) (s : B -> Prop) (t : B -> Prop) : (term1572 B x' s t) = (term1574 B x' s t).
Proof. exact (MK_COMB (@lem5014557 B x' s t) (@lem5014558 B t)). Qed.
Lemma lem5014561 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5014562 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem5014561 (B -> Prop) Prop f x). Qed.
Lemma lem5014563 {B : Type'} (x' : type638 B) (s : B -> Prop) (t : B -> Prop) : (term1574 B x' s t) = (term1575 B x' s t).
Proof. exact (@lem5014562 B (term1573 B x' s t) t). Qed.
Lemma lem5014564 {B : Type'} (x' : type638 B) (s : B -> Prop) (t : B -> Prop) : (term1572 B x' s t) = (term1575 B x' s t).
Proof. exact (TRANS (@lem5014559 B x' s t) (@lem5014563 B x' s t)). Qed.
Lemma lem5014565 {B : Type'} (x' : type638 B) (s : B -> Prop) (t : B -> Prop) : (term1571 B x' s t) = (term1575 B x' s t).
Proof. exact (TRANS (@lem5014553 B x' s t) (@lem5014564 B x' s t)). Qed.
Lemma lem5014566 {B : Type'} (x' : type638 B) (s : B -> Prop) (t : B -> Prop) : (term1576 B x' s t) = (term1577 B x' s t).
Proof. exact (MK_COMB (@lem5014532) (@lem5014565 B x' s t)). Qed.
Lemma lem5014567 {B : Type'} : (@IN B) = (@IN B).
Proof. exact (eq_refl (@IN B)). Qed.
Lemma lem5014574 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5014575 {B : Type'} (f : type638 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> (B -> Prop) -> B) f x).
Proof. exact (@lem5014574 (B -> Prop) (type684 B) f x). Qed.
Lemma lem5014576 {B : Type'} (x' : type638 B) (s : B -> Prop) : (x' s) = (@I ((B -> Prop) -> (B -> Prop) -> B) x' s).
Proof. exact (@lem5014575 B x' s). Qed.
Lemma lem5014577 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5014578 {B : Type'} (x' : type638 B) (s : B -> Prop) (t : B -> Prop) : (x' s t) = (@I ((B -> Prop) -> (B -> Prop) -> B) x' s t).
Proof. exact (MK_COMB (@lem5014576 B x' s) (@lem5014577 B t)). Qed.
Lemma lem5014580 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5014581 {B : Type'} (f : type684 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> B) f x).
Proof. exact (@lem5014580 (B -> Prop) B f x). Qed.
Lemma lem5014582 {B : Type'} (x' : type638 B) (s : B -> Prop) (t : B -> Prop) : (@I ((B -> Prop) -> (B -> Prop) -> B) x' s t) = (term1568 B x' s t).
Proof. exact (@lem5014581 B (@I ((B -> Prop) -> (B -> Prop) -> B) x' s) t). Qed.
Lemma lem5014584 {B : Type'} (x' : type638 B) (s : B -> Prop) (t : B -> Prop) : (x' s t) = (term1568 B x' s t).
Proof. exact (TRANS (@lem5014578 B x' s t) (@lem5014582 B x' s t)). Qed.
Lemma lem5014585 {B : Type'} (s : B -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5014586 {B : Type'} (x' : type638 B) (s : B -> Prop) (t : B -> Prop) : (term1569 B x' s t) = (term1570 B x' s t).
Proof. exact (MK_COMB (@lem5014567 B) (@lem5014584 B x' s t)). Qed.
Lemma lem5014587 {B : Type'} (x' : type638 B) (t : B -> Prop) (s : B -> Prop) : (term1578 B x' t s) = (term1579 B x' t s).
Proof. exact (MK_COMB (@lem5014586 B x' s t) (@lem5014585 B s)). Qed.
Lemma lem5014589 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5014590 {B : Type'} (f : type1364 B) (x : B) : (f x) = (@I (B -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem5014589 B (type686 B) f x). Qed.
Lemma lem5014591 {B : Type'} (x' : type638 B) (s : B -> Prop) (t : B -> Prop) : (term1570 B x' s t) = (term1573 B x' s t).
Proof. exact (@lem5014590 B (@IN B) (term1568 B x' s t)). Qed.
Lemma lem5014592 {B : Type'} (s : B -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5014593 {B : Type'} (x' : type638 B) (t : B -> Prop) (s : B -> Prop) : (term1579 B x' t s) = (term1580 B x' t s).
Proof. exact (MK_COMB (@lem5014591 B x' s t) (@lem5014592 B s)). Qed.
Lemma lem5014595 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5014596 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem5014595 (B -> Prop) Prop f x). Qed.
Lemma lem5014597 {B : Type'} (x' : type638 B) (t : B -> Prop) (s : B -> Prop) : (term1580 B x' t s) = (term1581 B x' t s).
Proof. exact (@lem5014596 B (term1573 B x' s t) s). Qed.
Lemma lem5014598 {B : Type'} (x' : type638 B) (t : B -> Prop) (s : B -> Prop) : (term1579 B x' t s) = (term1581 B x' t s).
Proof. exact (TRANS (@lem5014593 B x' t s) (@lem5014597 B x' t s)). Qed.
Lemma lem5014599 {B : Type'} (x' : type638 B) (t : B -> Prop) (s : B -> Prop) : (term1578 B x' t s) = (term1581 B x' t s).
Proof. exact (TRANS (@lem5014587 B x' t s) (@lem5014598 B x' t s)). Qed.
Lemma lem5014600 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5014601 {B : Type'} (x' : type638 B) (t : B -> Prop) (s : B -> Prop) : (term1582 B x' t s) = (term1583 B x' t s).
Proof. exact (MK_COMB (@lem5014600) (@lem5014599 B x' t s)). Qed.
Lemma lem5014602 {B : Type'} (x' : type638 B) (s : B -> Prop) (t : B -> Prop) : (term1584 B x' s t) = (term1585 B x' s t).
Proof. exact (MK_COMB (@lem5014601 B x' t s) (@lem5014566 B x' s t)). Qed.
Lemma lem5014609 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5014610 {B : Type'} (f : type639 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem5014609 (B -> Prop) (type686 B) f x). Qed.
Lemma lem5014611 {B : Type'} (s : B -> Prop) : (@SUBSET B s) = (@I ((B -> Prop) -> (B -> Prop) -> Prop) (@SUBSET B) s).
Proof. exact (@lem5014610 B (@SUBSET B) s). Qed.
Lemma lem5014612 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5014613 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (@I ((B -> Prop) -> (B -> Prop) -> Prop) (@SUBSET B) s t).
Proof. exact (MK_COMB (@lem5014611 B s) (@lem5014612 B t)). Qed.
Lemma lem5014615 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5014616 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem5014615 (B -> Prop) Prop f x). Qed.
Lemma lem5014617 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@I ((B -> Prop) -> (B -> Prop) -> Prop) (@SUBSET B) s t) = (term1559 B s t).
Proof. exact (@lem5014616 B (@I ((B -> Prop) -> (B -> Prop) -> Prop) (@SUBSET B) s) t). Qed.
Lemma lem5014619 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (term1559 B s t).
Proof. exact (TRANS (@lem5014613 B s t) (@lem5014617 B s t)). Qed.
Lemma lem5014620 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5014621 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1400 B s t) = (term1586 B s t).
Proof. exact (MK_COMB (@lem5014620) (@lem5014619 B s t)). Qed.
Lemma lem5014622 {B : Type'} (x' : type638 B) (s : B -> Prop) (t : B -> Prop) : (term1587 B x' s t) = (term1588 B x' s t).
Proof. exact (MK_COMB (@lem5014621 B s t) (@lem5014602 B x' s t)). Qed.
Lemma lem5014623 {B : Type'} (x' : type638 B) (s : B -> Prop) : (term1589 B x' s) = (term1590 B x' s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5014622 B x' s t)). Qed.
Lemma lem5014624 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5014625 {B : Type'} (x' : type638 B) (s : B -> Prop) : (term1507 B x' s) = (term1591 B x' s).
Proof. exact (MK_COMB (@lem5014624 B) (@lem5014623 B x' s)). Qed.
Lemma lem5014626 {B : Type'} (x' : type638 B) : (term1509 B x') = (term1592 B x').
Proof. exact (fun_ext (fun s : B -> Prop => @lem5014625 B x' s)). Qed.
Lemma lem5014627 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5014628 {B : Type'} (x' : type638 B) : (term1511 B x') = (term1593 B x').
Proof. exact (MK_COMB (@lem5014627 B) (@lem5014626 B x')). Qed.
Lemma lem5014629 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5014630 {B : Type'} (x' : type638 B) : (term1528 B x') = (term1594 B x').
Proof. exact (MK_COMB (@lem5014629) (@lem5014628 B x')). Qed.
Lemma lem5014631 {B : Type'} (x' : type638 B) : (term1530 B x') = (term1595 B x').
Proof. exact (MK_COMB (@lem5014630 B x') (@lem5014531 B)). Qed.
Lemma lem5014632 {B : Type'} (x' : type638 B) (h1 : term1530 B x') : term1595 B x'.
Proof. exact (EQ_MP (@lem5014631 B x') (@lem5014251 B x' h1)). Qed.
Lemma lem5015020 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem5015029 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5015030 {A B : Type'} (f : type1448 A B) (x : B) : (f x) = (@I (B -> (A -> Prop) -> (A -> B) -> A) f x).
Proof. exact (@lem5015029 B (type631 A B) f x). Qed.
Lemma lem5015031 {A B : Type'} (x'''' : type1448 A B) (y : B) : (x'''' y) = (@I (B -> (A -> Prop) -> (A -> B) -> A) x'''' y).
Proof. exact (@lem5015030 A B x'''' y). Qed.
Lemma lem5015032 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5015033 {A B : Type'} (x'''' : type1448 A B) (y : B) (s : A -> Prop) : (x'''' y s) = (@I (B -> (A -> Prop) -> (A -> B) -> A) x'''' y s).
Proof. exact (MK_COMB (@lem5015031 A B x'''' y) (@lem5015032 A s)). Qed.
Lemma lem5015035 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5015036 {A B : Type'} (f : type631 A B) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> B) -> A) f x).
Proof. exact (@lem5015035 (A -> Prop) (type569 A B) f x). Qed.
Lemma lem5015037 {A B : Type'} (x'''' : type1448 A B) (y : B) (s : A -> Prop) : (@I (B -> (A -> Prop) -> (A -> B) -> A) x'''' y s) = (term1596 A B x'''' y s).
Proof. exact (@lem5015036 A B (@I (B -> (A -> Prop) -> (A -> B) -> A) x'''' y) s). Qed.
Lemma lem5015038 {A B : Type'} (x'''' : type1448 A B) (y : B) (s : A -> Prop) : (x'''' y s) = (term1596 A B x'''' y s).
Proof. exact (TRANS (@lem5015033 A B x'''' y s) (@lem5015037 A B x'''' y s)). Qed.
Lemma lem5015039 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5015040 {A B : Type'} (x'''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) : (x'''' y s f) = (term1597 A B x'''' y s f).
Proof. exact (MK_COMB (@lem5015038 A B x'''' y s) (@lem5015039 A B f)). Qed.
Lemma lem5015042 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5015043 {A B : Type'} (f : type569 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> A) f x).
Proof. exact (@lem5015042 (A -> B) A f x). Qed.
Lemma lem5015044 {A B : Type'} (x'''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) : (term1597 A B x'''' y s f) = (term1598 A B x'''' y s f).
Proof. exact (@lem5015043 A B (term1596 A B x'''' y s) f). Qed.
Lemma lem5015046 {A B : Type'} (x'''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) : (x'''' y s f) = (term1598 A B x'''' y s f).
Proof. exact (TRANS (@lem5015040 A B x'''' y s f) (@lem5015044 A B x'''' y s f)). Qed.
Lemma lem5015047 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5015048 {A B : Type'} (x'''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) : (term1599 A B x'''' y s f) = (term1600 A B x'''' y s f).
Proof. exact (MK_COMB (@lem5015020 A) (@lem5015046 A B x'''' y s f)). Qed.
Lemma lem5015049 {A B : Type'} (x'''' : type1448 A B) (y : B) (f : A -> B) (s : A -> Prop) : (term1601 A B x'''' y f s) = (term1602 A B x'''' y f s).
Proof. exact (MK_COMB (@lem5015048 A B x'''' y s f) (@lem5015047 A s)). Qed.
Lemma lem5015051 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5015052 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5015051 A (type686 A) f x). Qed.
Lemma lem5015053 {A B : Type'} (x'''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) : (term1600 A B x'''' y s f) = (term1603 A B x'''' y s f).
Proof. exact (@lem5015052 A (@IN A) (term1598 A B x'''' y s f)). Qed.
Lemma lem5015054 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5015055 {A B : Type'} (x'''' : type1448 A B) (y : B) (f : A -> B) (s : A -> Prop) : (term1602 A B x'''' y f s) = (term1604 A B x'''' y f s).
Proof. exact (MK_COMB (@lem5015053 A B x'''' y s f) (@lem5015054 A s)). Qed.
Lemma lem5015057 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5015058 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5015057 (A -> Prop) Prop f x). Qed.
Lemma lem5015059 {A B : Type'} (x'''' : type1448 A B) (y : B) (f : A -> B) (s : A -> Prop) : (term1604 A B x'''' y f s) = (term1605 A B x'''' y f s).
Proof. exact (@lem5015058 A (term1603 A B x'''' y s f) s). Qed.
Lemma lem5015060 {A B : Type'} (x'''' : type1448 A B) (y : B) (f : A -> B) (s : A -> Prop) : (term1602 A B x'''' y f s) = (term1605 A B x'''' y f s).
Proof. exact (TRANS (@lem5015055 A B x'''' y f s) (@lem5015059 A B x'''' y f s)). Qed.
Lemma lem5015061 {A B : Type'} (x'''' : type1448 A B) (y : B) (f : A -> B) (s : A -> Prop) : (term1601 A B x'''' y f s) = (term1605 A B x'''' y f s).
Proof. exact (TRANS (@lem5015049 A B x'''' y f s) (@lem5015060 A B x'''' y f s)). Qed.
Lemma lem5015064 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5015073 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5015074 {A B : Type'} (f : type1448 A B) (x : B) : (f x) = (@I (B -> (A -> Prop) -> (A -> B) -> A) f x).
Proof. exact (@lem5015073 B (type631 A B) f x). Qed.
Lemma lem5015075 {A B : Type'} (x'''' : type1448 A B) (y : B) : (x'''' y) = (@I (B -> (A -> Prop) -> (A -> B) -> A) x'''' y).
Proof. exact (@lem5015074 A B x'''' y). Qed.
Lemma lem5015076 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5015077 {A B : Type'} (x'''' : type1448 A B) (y : B) (s : A -> Prop) : (x'''' y s) = (@I (B -> (A -> Prop) -> (A -> B) -> A) x'''' y s).
Proof. exact (MK_COMB (@lem5015075 A B x'''' y) (@lem5015076 A s)). Qed.
Lemma lem5015079 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5015080 {A B : Type'} (f : type631 A B) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> B) -> A) f x).
Proof. exact (@lem5015079 (A -> Prop) (type569 A B) f x). Qed.
Lemma lem5015081 {A B : Type'} (x'''' : type1448 A B) (y : B) (s : A -> Prop) : (@I (B -> (A -> Prop) -> (A -> B) -> A) x'''' y s) = (term1596 A B x'''' y s).
Proof. exact (@lem5015080 A B (@I (B -> (A -> Prop) -> (A -> B) -> A) x'''' y) s). Qed.
Lemma lem5015082 {A B : Type'} (x'''' : type1448 A B) (y : B) (s : A -> Prop) : (x'''' y s) = (term1596 A B x'''' y s).
Proof. exact (TRANS (@lem5015077 A B x'''' y s) (@lem5015081 A B x'''' y s)). Qed.
Lemma lem5015083 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5015084 {A B : Type'} (x'''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) : (x'''' y s f) = (term1597 A B x'''' y s f).
Proof. exact (MK_COMB (@lem5015082 A B x'''' y s) (@lem5015083 A B f)). Qed.
Lemma lem5015086 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5015087 {A B : Type'} (f : type569 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> A) f x).
Proof. exact (@lem5015086 (A -> B) A f x). Qed.
Lemma lem5015088 {A B : Type'} (x'''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) : (term1597 A B x'''' y s f) = (term1598 A B x'''' y s f).
Proof. exact (@lem5015087 A B (term1596 A B x'''' y s) f). Qed.
Lemma lem5015090 {A B : Type'} (x'''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) : (x'''' y s f) = (term1598 A B x'''' y s f).
Proof. exact (TRANS (@lem5015084 A B x'''' y s f) (@lem5015088 A B x'''' y s f)). Qed.
Lemma lem5015091 {A B : Type'} (x'''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) : (term1606 A B x'''' y s f) = (term1607 A B x'''' y s f).
Proof. exact (MK_COMB (@lem5015064 A B f) (@lem5015090 A B x'''' y s f)). Qed.
Lemma lem5015093 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5015094 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem5015093 A B f x). Qed.
Lemma lem5015095 {A B : Type'} (x'''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) : (term1607 A B x'''' y s f) = (term1608 A B x'''' y s f).
Proof. exact (@lem5015094 A B f (term1598 A B x'''' y s f)). Qed.
Lemma lem5015096 {A B : Type'} (x'''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) : (term1606 A B x'''' y s f) = (term1608 A B x'''' y s f).
Proof. exact (TRANS (@lem5015091 A B x'''' y s f) (@lem5015095 A B x'''' y s f)). Qed.
Lemma lem5015097 {B : Type'} (y : B) : (@eq B y) = (@eq B y).
Proof. exact (eq_refl (@eq B y)). Qed.
Lemma lem5015098 {A B : Type'} (x'''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) : (y = (term1606 A B x'''' y s f)) = (y = (term1608 A B x'''' y s f)).
Proof. exact (MK_COMB (@lem5015097 B y) (@lem5015096 A B x'''' y s f)). Qed.
Lemma lem5015099 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5015100 {A B : Type'} (x'''' : type1448 A B) (y : B) (s : A -> Prop) (f : A -> B) : (term1609 A B x'''' y s f) = (term1610 A B x'''' y s f).
Proof. exact (MK_COMB (@lem5015099) (@lem5015098 A B x'''' y s f)). Qed.
Lemma lem5015101 {A B : Type'} (x'''' : type1448 A B) (y : B) (f : A -> B) (s : A -> Prop) : (term1611 A B x'''' y f s) = (term1612 A B x'''' y f s).
Proof. exact (MK_COMB (@lem5015100 A B x'''' y s f) (@lem5015061 A B x'''' y f s)). Qed.
Lemma lem5015102 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5015111 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5015112 {A B : Type'} (f : type528 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) f x).
Proof. exact (@lem5015111 (A -> B) (type678 A B) f x). Qed.
Lemma lem5015113 {A B : Type'} (f : A -> B) : (@IMAGE A B f) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f).
Proof. exact (@lem5015112 A B (@IMAGE A B) f). Qed.
Lemma lem5015114 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5015115 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@IMAGE A B f s) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f s).
Proof. exact (MK_COMB (@lem5015113 A B f) (@lem5015114 A s)). Qed.
Lemma lem5015117 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5015118 {A B : Type'} (f : type678 A B) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> B -> Prop) f x).
Proof. exact (@lem5015117 (A -> Prop) (B -> Prop) f x). Qed.
Lemma lem5015119 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f s) = (term1536 A B f s).
Proof. exact (@lem5015118 A B (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f) s). Qed.
Lemma lem5015121 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@IMAGE A B f s) = (term1536 A B f s).
Proof. exact (TRANS (@lem5015115 A B f s) (@lem5015119 A B f s)). Qed.
Lemma lem5015122 {B : Type'} (y : B) : (@IN B y) = (@IN B y).
Proof. exact (eq_refl (@IN B y)). Qed.
Lemma lem5015123 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term5 A B y f s) = (term1613 A B y f s).
Proof. exact (MK_COMB (@lem5015122 B y) (@lem5015121 A B f s)). Qed.
Lemma lem5015125 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5015126 {B : Type'} (f : type1364 B) (x : B) : (f x) = (@I (B -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem5015125 B (type686 B) f x). Qed.
Lemma lem5015127 {B : Type'} (y : B) : (@IN B y) = (@I (B -> (B -> Prop) -> Prop) (@IN B) y).
Proof. exact (@lem5015126 B (@IN B) y). Qed.
Lemma lem5015128 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term1536 A B f s) = (term1536 A B f s).
Proof. exact (eq_refl (term1536 A B f s)). Qed.
Lemma lem5015129 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1613 A B y f s) = (term1614 A B y f s).
Proof. exact (MK_COMB (@lem5015127 B y) (@lem5015128 A B f s)). Qed.
Lemma lem5015131 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5015132 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem5015131 (B -> Prop) Prop f x). Qed.
Lemma lem5015133 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1614 A B y f s) = (term1615 A B y f s).
Proof. exact (@lem5015132 B (@I (B -> (B -> Prop) -> Prop) (@IN B) y) (term1536 A B f s)). Qed.
Lemma lem5015134 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1613 A B y f s) = (term1615 A B y f s).
Proof. exact (TRANS (@lem5015129 A B y f s) (@lem5015133 A B y f s)). Qed.
Lemma lem5015135 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term5 A B y f s) = (term1615 A B y f s).
Proof. exact (TRANS (@lem5015123 A B y f s) (@lem5015134 A B y f s)). Qed.
Lemma lem5015136 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1285 A B y f s) = (term1616 A B y f s).
Proof. exact (MK_COMB (@lem5015102) (@lem5015135 A B y f s)). Qed.
Lemma lem5015137 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5015138 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1202 A B y f s) = (term1617 A B y f s).
Proof. exact (MK_COMB (@lem5015137) (@lem5015136 A B y f s)). Qed.
Lemma lem5015139 {A B : Type'} (x'''' : type1448 A B) (y : B) (f : A -> B) (s : A -> Prop) : (term1618 A B x'''' y f s) = (term1619 A B x'''' y f s).
Proof. exact (MK_COMB (@lem5015138 A B y f s) (@lem5015101 A B x'''' y f s)). Qed.
Lemma lem5015140 {A B : Type'} (x'''' : type1448 A B) (y : B) (s : A -> Prop) : (term1620 A B x'''' y s) = (term1621 A B x'''' y s).
Proof. exact (fun_ext (fun f : A -> B => @lem5015139 A B x'''' y f s)). Qed.
Lemma lem5015141 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5015142 {A B : Type'} (x'''' : type1448 A B) (y : B) (s : A -> Prop) : (term1622 A B x'''' y s) = (term1623 A B x'''' y s).
Proof. exact (MK_COMB (@lem5015141 A B) (@lem5015140 A B x'''' y s)). Qed.
Lemma lem5015143 {A B : Type'} (x'''' : type1448 A B) (y : B) : (term1624 A B x'''' y) = (term1625 A B x'''' y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5015142 A B x'''' y s)). Qed.
Lemma lem5015144 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5015145 {A B : Type'} (x'''' : type1448 A B) (y : B) : (term1362 A B x'''' y) = (term1626 A B x'''' y).
Proof. exact (MK_COMB (@lem5015144 A) (@lem5015143 A B x'''' y)). Qed.
Lemma lem5015146 {A B : Type'} (x'''' : type1448 A B) : (term1364 A B x'''') = (term1627 A B x'''').
Proof. exact (fun_ext (fun y : B => @lem5015145 A B x'''' y)). Qed.
Lemma lem5015147 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5015148 {A B : Type'} (x'''' : type1448 A B) : (term1366 A B x'''') = (term1628 A B x'''').
Proof. exact (MK_COMB (@lem5015147 B) (@lem5015146 A B x'''')). Qed.
Lemma lem5015149 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5015156 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5015157 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5015156 A (type686 A) f x). Qed.
Lemma lem5015158 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem5015157 A (@IN A) x). Qed.
Lemma lem5015159 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5015160 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x s).
Proof. exact (MK_COMB (@lem5015158 A x) (@lem5015159 A s)). Qed.
Lemma lem5015162 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5015163 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5015162 (A -> Prop) Prop f x). Qed.
Lemma lem5015164 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x s) = (term1534 A x s).
Proof. exact (@lem5015163 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) s). Qed.
Lemma lem5015166 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (term1534 A x s).
Proof. exact (TRANS (@lem5015160 A x s) (@lem5015164 A x s)). Qed.
Lemma lem5015167 {A : Type'} (x : A) (s : A -> Prop) : (term238 A x s) = (term1535 A x s).
Proof. exact (MK_COMB (@lem5015149) (@lem5015166 A x s)). Qed.
Lemma lem5015168 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5015175 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5015177 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem5015175 A B f x). Qed.
Lemma lem5015178 {B : Type'} (y : B) : (@eq B y) = (@eq B y).
Proof. exact (eq_refl (@eq B y)). Qed.
Lemma lem5015179 {A B : Type'} (y : B) (f : A -> B) (x : A) : (y = (f x)) = (y = (@I (A -> B) f x)).
Proof. exact (MK_COMB (@lem5015178 B y) (@lem5015177 A B f x)). Qed.
Lemma lem5015180 {A B : Type'} (y : B) (f : A -> B) (x : A) : (term1629 A B y f x) = (term1630 A B y f x).
Proof. exact (MK_COMB (@lem5015168) (@lem5015179 A B y f x)). Qed.
Lemma lem5015181 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5015182 {A B : Type'} (y : B) (f : A -> B) (x : A) : (term1631 A B y f x) = (term1632 A B y f x).
Proof. exact (MK_COMB (@lem5015181) (@lem5015180 A B y f x)). Qed.
Lemma lem5015183 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term1194 A B y f x s) = (term1633 A B y f x s).
Proof. exact (MK_COMB (@lem5015182 A B y f x) (@lem5015167 A x s)). Qed.
Lemma lem5015184 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1200 A B y f s) = (term1634 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem5015183 A B y f x s)). Qed.
Lemma lem5015185 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5015186 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1201 A B y f s) = (term1635 A B y f s).
Proof. exact (MK_COMB (@lem5015185 A) (@lem5015184 A B y f s)). Qed.
Lemma lem5015195 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5015196 {A B : Type'} (f : type528 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) f x).
Proof. exact (@lem5015195 (A -> B) (type678 A B) f x). Qed.
Lemma lem5015197 {A B : Type'} (f : A -> B) : (@IMAGE A B f) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f).
Proof. exact (@lem5015196 A B (@IMAGE A B) f). Qed.
Lemma lem5015198 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5015199 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@IMAGE A B f s) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f s).
Proof. exact (MK_COMB (@lem5015197 A B f) (@lem5015198 A s)). Qed.
Lemma lem5015201 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5015202 {A B : Type'} (f : type678 A B) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> B -> Prop) f x).
Proof. exact (@lem5015201 (A -> Prop) (B -> Prop) f x). Qed.
Lemma lem5015203 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f s) = (term1536 A B f s).
Proof. exact (@lem5015202 A B (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f) s). Qed.
Lemma lem5015205 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@IMAGE A B f s) = (term1536 A B f s).
Proof. exact (TRANS (@lem5015199 A B f s) (@lem5015203 A B f s)). Qed.
Lemma lem5015206 {B : Type'} (y : B) : (@IN B y) = (@IN B y).
Proof. exact (eq_refl (@IN B y)). Qed.
Lemma lem5015207 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term5 A B y f s) = (term1613 A B y f s).
Proof. exact (MK_COMB (@lem5015206 B y) (@lem5015205 A B f s)). Qed.
Lemma lem5015209 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5015210 {B : Type'} (f : type1364 B) (x : B) : (f x) = (@I (B -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem5015209 B (type686 B) f x). Qed.
Lemma lem5015211 {B : Type'} (y : B) : (@IN B y) = (@I (B -> (B -> Prop) -> Prop) (@IN B) y).
Proof. exact (@lem5015210 B (@IN B) y). Qed.
Lemma lem5015212 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term1536 A B f s) = (term1536 A B f s).
Proof. exact (eq_refl (term1536 A B f s)). Qed.
Lemma lem5015213 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1613 A B y f s) = (term1614 A B y f s).
Proof. exact (MK_COMB (@lem5015211 B y) (@lem5015212 A B f s)). Qed.
Lemma lem5015215 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5015216 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem5015215 (B -> Prop) Prop f x). Qed.
Lemma lem5015217 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1614 A B y f s) = (term1615 A B y f s).
Proof. exact (@lem5015216 B (@I (B -> (B -> Prop) -> Prop) (@IN B) y) (term1536 A B f s)). Qed.
Lemma lem5015218 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1613 A B y f s) = (term1615 A B y f s).
Proof. exact (TRANS (@lem5015213 A B y f s) (@lem5015217 A B y f s)). Qed.
Lemma lem5015219 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term5 A B y f s) = (term1615 A B y f s).
Proof. exact (TRANS (@lem5015207 A B y f s) (@lem5015218 A B y f s)). Qed.
Lemma lem5015220 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5015221 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1204 A B y f s) = (term1636 A B y f s).
Proof. exact (MK_COMB (@lem5015220) (@lem5015219 A B y f s)). Qed.
Lemma lem5015222 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1206 A B y f s) = (term1637 A B y f s).
Proof. exact (MK_COMB (@lem5015221 A B y f s) (@lem5015186 A B y f s)). Qed.
Lemma lem5015223 {A B : Type'} (y : B) (s : A -> Prop) : (term1221 A B y s) = (term1638 A B y s).
Proof. exact (fun_ext (fun f : A -> B => @lem5015222 A B y f s)). Qed.
Lemma lem5015224 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5015225 {A B : Type'} (y : B) (s : A -> Prop) : (term1232 A B y s) = (term1639 A B y s).
Proof. exact (MK_COMB (@lem5015224 A B) (@lem5015223 A B y s)). Qed.
Lemma lem5015226 {A B : Type'} (y : B) : (term1243 A B y) = (term1640 A B y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5015225 A B y s)). Qed.
Lemma lem5015227 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5015228 {A B : Type'} (y : B) : (term1254 A B y) = (term1641 A B y).
Proof. exact (MK_COMB (@lem5015227 A) (@lem5015226 A B y)). Qed.
Lemma lem5015229 {A B : Type'} : (term1265 A B) = (term1642 A B).
Proof. exact (fun_ext (fun y : B => @lem5015228 A B y)). Qed.
Lemma lem5015230 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5015231 {A B : Type'} : (term1276 A B) = (term1643 A B).
Proof. exact (MK_COMB (@lem5015230 B) (@lem5015229 A B)). Qed.
Lemma lem5015232 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5015233 {A B : Type'} : (term1278 A B) = (term1644 A B).
Proof. exact (MK_COMB (@lem5015232) (@lem5015231 A B)). Qed.
Lemma lem5015234 {A B : Type'} (x'''' : type1448 A B) : (term1381 A B x'''') = (term1645 A B x'''').
Proof. exact (MK_COMB (@lem5015233 A B) (@lem5015148 A B x'''')). Qed.
Lemma lem5015235 {A B : Type'} (x'''' : type1448 A B) (h1 : term1381 A B x'''') : term1645 A B x''''.
Proof. exact (EQ_MP (@lem5015234 A B x'''') (@lem5014254 A B x'''' h1)). Qed.
Lemma lem5015458 {A : Type'} (x''''''' : A) (y' : A) : (term634 A x''''''' y') = (term634 A x''''''' y').
Proof. exact (eq_refl (term634 A x''''''' y')). Qed.
Lemma lem5015459 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5015464 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5015465 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem5015464 A B f x). Qed.
Lemma lem5015467 {A B : Type'} (f : A -> B) (x''''''' : A) : (f x''''''') = (@I (A -> B) f x''''''').
Proof. exact (@lem5015465 A B f x'''''''). Qed.
Lemma lem5015472 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5015473 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem5015472 A B f x). Qed.
Lemma lem5015475 {A B : Type'} (f : A -> B) (y' : A) : (f y') = (@I (A -> B) f y').
Proof. exact (@lem5015473 A B f y'). Qed.
Lemma lem5015476 {A B : Type'} (f : A -> B) (x''''''' : A) : (term515 A B f x''''''') = (term1543 A B f x''''''').
Proof. exact (MK_COMB (@lem5015459 B) (@lem5015467 A B f x''''''')). Qed.
Lemma lem5015477 {A B : Type'} (x''''''' : A) (f : A -> B) (y' : A) : ((f x''''''') = (f y')) = ((@I (A -> B) f x''''''') = (@I (A -> B) f y')).
Proof. exact (MK_COMB (@lem5015476 A B f x''''''') (@lem5015475 A B f y')). Qed.
Lemma lem5015478 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5015479 {A B : Type'} (x''''''' : A) (f : A -> B) (y' : A) : (term1646 A B x''''''' f y') = (term1647 A B x''''''' f y').
Proof. exact (MK_COMB (@lem5015478) (@lem5015477 A B x''''''' f y')). Qed.
Lemma lem5015480 {A B : Type'} (f : A -> B) (x''''''' : A) (y' : A) : (term672 A B f x''''''' y') = (term1648 A B f x''''''' y').
Proof. exact (MK_COMB (@lem5015479 A B x''''''' f y') (@lem5015458 A x''''''' y')). Qed.
Lemma lem5015487 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5015488 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5015487 A (type686 A) f x). Qed.
Lemma lem5015489 {A : Type'} (y' : A) : (@IN A y') = (@I (A -> (A -> Prop) -> Prop) (@IN A) y').
Proof. exact (@lem5015488 A (@IN A) y'). Qed.
Lemma lem5015490 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5015491 {A : Type'} (y' : A) (s : A -> Prop) : (@IN A y' s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) y' s).
Proof. exact (MK_COMB (@lem5015489 A y') (@lem5015490 A s)). Qed.
Lemma lem5015493 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5015494 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5015493 (A -> Prop) Prop f x). Qed.
Lemma lem5015495 {A : Type'} (y' : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) y' s) = (term1534 A y' s).
Proof. exact (@lem5015494 A (@I (A -> (A -> Prop) -> Prop) (@IN A) y') s). Qed.
Lemma lem5015497 {A : Type'} (y' : A) (s : A -> Prop) : (@IN A y' s) = (term1534 A y' s).
Proof. exact (TRANS (@lem5015491 A y' s) (@lem5015495 A y' s)). Qed.
Lemma lem5015498 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5015499 {A : Type'} (y' : A) (s : A -> Prop) : (term641 A y' s) = (term1649 A y' s).
Proof. exact (MK_COMB (@lem5015498) (@lem5015497 A y' s)). Qed.
Lemma lem5015500 {A B : Type'} (s : A -> Prop) (f : A -> B) (x''''''' : A) (y' : A) : (term674 A B s f x''''''' y') = (term1650 A B s f x''''''' y').
Proof. exact (MK_COMB (@lem5015499 A y' s) (@lem5015480 A B f x''''''' y')). Qed.
Lemma lem5015509 {A : Type'} (y' : A) (x : A) : (term645 A y' x) = (term645 A y' x).
Proof. exact (eq_refl (term645 A y' x)). Qed.
Lemma lem5015510 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (x''''''' : A) (y' : A) : (term677 A B x s f x''''''' y') = (term1651 A B x s f x''''''' y').
Proof. exact (MK_COMB (@lem5015509 A y' x) (@lem5015500 A B s f x''''''' y')). Qed.
Lemma lem5015517 {A : Type'} (x''''''' : A) (y' : A) : (term634 A x''''''' y') = (term634 A x''''''' y').
Proof. exact (eq_refl (term634 A x''''''' y')). Qed.
Lemma lem5015518 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5015523 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5015524 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem5015523 A B f x). Qed.
Lemma lem5015526 {A B : Type'} (f : A -> B) (x''''''' : A) : (f x''''''') = (@I (A -> B) f x''''''').
Proof. exact (@lem5015524 A B f x'''''''). Qed.
Lemma lem5015527 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5015528 {A B : Type'} (f : A -> B) (x''''''' : A) : (term515 A B f x''''''') = (term1543 A B f x''''''').
Proof. exact (MK_COMB (@lem5015518 B) (@lem5015526 A B f x''''''')). Qed.
Lemma lem5015529 {A B : Type'} (f : A -> B) (x''''''' : A) (y : B) : ((f x''''''') = y) = ((@I (A -> B) f x''''''') = y).
Proof. exact (MK_COMB (@lem5015528 A B f x''''''') (@lem5015527 B y)). Qed.
Lemma lem5015530 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5015531 {A B : Type'} (f : A -> B) (x''''''' : A) (y : B) : (term1652 A B f x''''''' y) = (term1653 A B f x''''''' y).
Proof. exact (MK_COMB (@lem5015530) (@lem5015529 A B f x''''''' y)). Qed.
Lemma lem5015532 {A B : Type'} (f : A -> B) (y : B) (x''''''' : A) (y' : A) : (term667 A B f y x''''''' y') = (term1654 A B f y x''''''' y').
Proof. exact (MK_COMB (@lem5015531 A B f x''''''' y) (@lem5015517 A x''''''' y')). Qed.
Lemma lem5015539 {A : Type'} (y' : A) (x : A) : (term572 A y' x) = (term572 A y' x).
Proof. exact (eq_refl (term572 A y' x)). Qed.
Lemma lem5015540 {A B : Type'} (x : A) (f : A -> B) (y : B) (x''''''' : A) (y' : A) : (term669 A B x f y x''''''' y') = (term1655 A B x f y x''''''' y').
Proof. exact (MK_COMB (@lem5015539 A y' x) (@lem5015532 A B f y x''''''' y')). Qed.
Lemma lem5015541 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5015542 {A B : Type'} (x : A) (f : A -> B) (y : B) (x''''''' : A) (y' : A) : (term680 A B x f y x''''''' y') = (term1656 A B x f y x''''''' y').
Proof. exact (MK_COMB (@lem5015541) (@lem5015540 A B x f y x''''''' y')). Qed.
Lemma lem5015543 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x''''''' : A) (y' : A) : (term682 A B y x s f x''''''' y') = (term1657 A B y x s f x''''''' y').
Proof. exact (MK_COMB (@lem5015542 A B x f y x''''''' y') (@lem5015510 A B x s f x''''''' y')). Qed.
Lemma lem5015550 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5015551 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5015550 A (type686 A) f x). Qed.
Lemma lem5015552 {A : Type'} (x''''''' : A) : (@IN A x''''''') = (@I (A -> (A -> Prop) -> Prop) (@IN A) x''''''').
Proof. exact (@lem5015551 A (@IN A) x'''''''). Qed.
Lemma lem5015553 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5015554 {A : Type'} (x''''''' : A) (s : A -> Prop) : (@IN A x''''''' s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x''''''' s).
Proof. exact (MK_COMB (@lem5015552 A x''''''') (@lem5015553 A s)). Qed.
Lemma lem5015556 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5015557 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5015556 (A -> Prop) Prop f x). Qed.
Lemma lem5015558 {A : Type'} (x''''''' : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x''''''' s) = (term1534 A x''''''' s).
Proof. exact (@lem5015557 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x''''''') s). Qed.
Lemma lem5015560 {A : Type'} (x''''''' : A) (s : A -> Prop) : (@IN A x''''''' s) = (term1534 A x''''''' s).
Proof. exact (TRANS (@lem5015554 A x''''''' s) (@lem5015558 A x''''''' s)). Qed.
Lemma lem5015561 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5015562 {A : Type'} (x''''''' : A) (s : A -> Prop) : (term641 A x''''''' s) = (term1649 A x''''''' s).
Proof. exact (MK_COMB (@lem5015561) (@lem5015560 A x''''''' s)). Qed.
Lemma lem5015563 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x''''''' : A) (y' : A) : (term883 A B y x s f x''''''' y') = (term1658 A B y x s f x''''''' y').
Proof. exact (MK_COMB (@lem5015562 A x''''''' s) (@lem5015543 A B y x s f x''''''' y')). Qed.
Lemma lem5015572 {A : Type'} (x''''''' : A) (x : A) : (term645 A x''''''' x) = (term645 A x''''''' x).
Proof. exact (eq_refl (term645 A x''''''' x)). Qed.
Lemma lem5015573 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x''''''' : A) (y' : A) : (term896 A B y x s f x''''''' y') = (term1659 A B y x s f x''''''' y').
Proof. exact (MK_COMB (@lem5015572 A x''''''' x) (@lem5015563 A B y x s f x''''''' y')). Qed.
Lemma lem5015580 {A : Type'} (x''''''' : A) (y' : A) : (term634 A x''''''' y') = (term634 A x''''''' y').
Proof. exact (eq_refl (term634 A x''''''' y')). Qed.
Lemma lem5015587 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5015588 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem5015587 A B f x). Qed.
Lemma lem5015590 {A B : Type'} (f : A -> B) (y' : A) : (f y') = (@I (A -> B) f y').
Proof. exact (@lem5015588 A B f y'). Qed.
Lemma lem5015591 {B : Type'} (y : B) : (@eq B y) = (@eq B y).
Proof. exact (eq_refl (@eq B y)). Qed.
Lemma lem5015592 {A B : Type'} (y : B) (f : A -> B) (y' : A) : (y = (f y')) = (y = (@I (A -> B) f y')).
Proof. exact (MK_COMB (@lem5015591 B y) (@lem5015590 A B f y')). Qed.
Lemma lem5015593 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5015594 {A B : Type'} (y : B) (f : A -> B) (y' : A) : (term570 A B y f y') = (term1660 A B y f y').
Proof. exact (MK_COMB (@lem5015593) (@lem5015592 A B y f y')). Qed.
Lemma lem5015595 {A B : Type'} (y : B) (f : A -> B) (x''''''' : A) (y' : A) : (term640 A B y f x''''''' y') = (term1661 A B y f x''''''' y').
Proof. exact (MK_COMB (@lem5015594 A B y f y') (@lem5015580 A x''''''' y')). Qed.
Lemma lem5015602 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5015603 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5015602 A (type686 A) f x). Qed.
Lemma lem5015604 {A : Type'} (y' : A) : (@IN A y') = (@I (A -> (A -> Prop) -> Prop) (@IN A) y').
Proof. exact (@lem5015603 A (@IN A) y'). Qed.
Lemma lem5015605 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5015606 {A : Type'} (y' : A) (s : A -> Prop) : (@IN A y' s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) y' s).
Proof. exact (MK_COMB (@lem5015604 A y') (@lem5015605 A s)). Qed.
Lemma lem5015608 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5015609 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5015608 (A -> Prop) Prop f x). Qed.
Lemma lem5015610 {A : Type'} (y' : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) y' s) = (term1534 A y' s).
Proof. exact (@lem5015609 A (@I (A -> (A -> Prop) -> Prop) (@IN A) y') s). Qed.
Lemma lem5015612 {A : Type'} (y' : A) (s : A -> Prop) : (@IN A y' s) = (term1534 A y' s).
Proof. exact (TRANS (@lem5015606 A y' s) (@lem5015610 A y' s)). Qed.
Lemma lem5015613 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5015614 {A : Type'} (y' : A) (s : A -> Prop) : (term641 A y' s) = (term1649 A y' s).
Proof. exact (MK_COMB (@lem5015613) (@lem5015612 A y' s)). Qed.
Lemma lem5015615 {A B : Type'} (s : A -> Prop) (y : B) (f : A -> B) (x''''''' : A) (y' : A) : (term643 A B s y f x''''''' y') = (term1662 A B s y f x''''''' y').
Proof. exact (MK_COMB (@lem5015614 A y' s) (@lem5015595 A B y f x''''''' y')). Qed.
Lemma lem5015624 {A : Type'} (y' : A) (x : A) : (term645 A y' x) = (term645 A y' x).
Proof. exact (eq_refl (term645 A y' x)). Qed.
Lemma lem5015625 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x''''''' : A) (y' : A) : (term647 A B x s y f x''''''' y') = (term1663 A B x s y f x''''''' y').
Proof. exact (MK_COMB (@lem5015624 A y' x) (@lem5015615 A B s y f x''''''' y')). Qed.
Lemma lem5015642 {A : Type'} (x : A) (x''''''' : A) (y' : A) : (term650 A x x''''''' y') = (term650 A x x''''''' y').
Proof. exact (eq_refl (term650 A x x''''''' y')). Qed.
Lemma lem5015643 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x''''''' : A) (y' : A) : (term652 A B x s y f x''''''' y') = (term1664 A B x s y f x''''''' y').
Proof. exact (MK_COMB (@lem5015642 A x x''''''' y') (@lem5015625 A B x s y f x''''''' y')). Qed.
Lemma lem5015650 {A : Type'} (x''''''' : A) (x : A) : (term572 A x''''''' x) = (term572 A x''''''' x).
Proof. exact (eq_refl (term572 A x''''''' x)). Qed.
Lemma lem5015651 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x''''''' : A) (y' : A) : (term866 A B x s y f x''''''' y') = (term1665 A B x s y f x''''''' y').
Proof. exact (MK_COMB (@lem5015650 A x''''''' x) (@lem5015643 A B x s y f x''''''' y')). Qed.
Lemma lem5015652 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5015653 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x''''''' : A) (y' : A) : (term933 A B x s y f x''''''' y') = (term1666 A B x s y f x''''''' y').
Proof. exact (MK_COMB (@lem5015652) (@lem5015651 A B x s y f x''''''' y')). Qed.
Lemma lem5015654 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x''''''' : A) (y' : A) : (term935 A B y x s f x''''''' y') = (term1667 A B y x s f x''''''' y').
Proof. exact (MK_COMB (@lem5015653 A B x s y f x''''''' y') (@lem5015573 A B y x s f x''''''' y')). Qed.
Lemma lem5015655 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5015662 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5015663 {B : Type'} (f : type1364 B) (x : B) : (f x) = (@I (B -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem5015662 B (type686 B) f x). Qed.
Lemma lem5015664 {B : Type'} (x'''''' : B) : (@IN B x'''''') = (@I (B -> (B -> Prop) -> Prop) (@IN B) x'''''').
Proof. exact (@lem5015663 B (@IN B) x''''''). Qed.
Lemma lem5015665 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5015666 {B : Type'} (x'''''' : B) (t : B -> Prop) : (@IN B x'''''' t) = (@I (B -> (B -> Prop) -> Prop) (@IN B) x'''''' t).
Proof. exact (MK_COMB (@lem5015664 B x'''''') (@lem5015665 B t)). Qed.
Lemma lem5015668 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5015669 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem5015668 (B -> Prop) Prop f x). Qed.
Lemma lem5015670 {B : Type'} (x'''''' : B) (t : B -> Prop) : (@I (B -> (B -> Prop) -> Prop) (@IN B) x'''''' t) = (term1534 B x'''''' t).
Proof. exact (@lem5015669 B (@I (B -> (B -> Prop) -> Prop) (@IN B) x'''''') t). Qed.
Lemma lem5015672 {B : Type'} (x'''''' : B) (t : B -> Prop) : (@IN B x'''''' t) = (term1534 B x'''''' t).
Proof. exact (TRANS (@lem5015666 B x'''''' t) (@lem5015670 B x'''''' t)). Qed.
Lemma lem5015673 {B : Type'} (x'''''' : B) (t : B -> Prop) : (term238 B x'''''' t) = (term1535 B x'''''' t).
Proof. exact (MK_COMB (@lem5015655) (@lem5015672 B x'''''' t)). Qed.
Lemma lem5015682 {B : Type'} (x'''''' : B) (y : B) : (term645 B x'''''' y) = (term645 B x'''''' y).
Proof. exact (eq_refl (term645 B x'''''' y)). Qed.
Lemma lem5015683 {B : Type'} (y : B) (x'''''' : B) (t : B -> Prop) : (term619 B y x'''''' t) = (term1668 B y x'''''' t).
Proof. exact (MK_COMB (@lem5015682 B x'''''' y) (@lem5015673 B x'''''' t)). Qed.
Lemma lem5015690 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5015691 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5015690 A (type686 A) f x). Qed.
Lemma lem5015692 {A : Type'} (x''''''' : A) : (@IN A x''''''') = (@I (A -> (A -> Prop) -> Prop) (@IN A) x''''''').
Proof. exact (@lem5015691 A (@IN A) x'''''''). Qed.
Lemma lem5015693 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5015694 {A : Type'} (x''''''' : A) (s : A -> Prop) : (@IN A x''''''' s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x''''''' s).
Proof. exact (MK_COMB (@lem5015692 A x''''''') (@lem5015693 A s)). Qed.
Lemma lem5015696 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5015697 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5015696 (A -> Prop) Prop f x). Qed.
Lemma lem5015698 {A : Type'} (x''''''' : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x''''''' s) = (term1534 A x''''''' s).
Proof. exact (@lem5015697 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x''''''') s). Qed.
Lemma lem5015700 {A : Type'} (x''''''' : A) (s : A -> Prop) : (@IN A x''''''' s) = (term1534 A x''''''' s).
Proof. exact (TRANS (@lem5015694 A x''''''' s) (@lem5015698 A x''''''' s)). Qed.
Lemma lem5015707 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5015708 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem5015707 A B f x). Qed.
Lemma lem5015710 {A B : Type'} (f : A -> B) (x''''''' : A) : (f x''''''') = (@I (A -> B) f x''''''').
Proof. exact (@lem5015708 A B f x'''''''). Qed.
Lemma lem5015711 {B : Type'} (x'''''' : B) : (@eq B x'''''') = (@eq B x'''''').
Proof. exact (eq_refl (@eq B x'''''')). Qed.
Lemma lem5015712 {A B : Type'} (x'''''' : B) (f : A -> B) (x''''''' : A) : (x'''''' = (f x''''''')) = (x'''''' = (@I (A -> B) f x''''''')).
Proof. exact (MK_COMB (@lem5015711 B x'''''') (@lem5015710 A B f x''''''')). Qed.
Lemma lem5015713 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5015714 {A B : Type'} (x'''''' : B) (f : A -> B) (x''''''' : A) : (term570 A B x'''''' f x''''''') = (term1660 A B x'''''' f x''''''').
Proof. exact (MK_COMB (@lem5015713) (@lem5015712 A B x'''''' f x''''''')). Qed.
Lemma lem5015715 {A B : Type'} (x'''''' : B) (f : A -> B) (x''''''' : A) (s : A -> Prop) : (term505 A B x'''''' f x''''''' s) = (term1669 A B x'''''' f x''''''' s).
Proof. exact (MK_COMB (@lem5015714 A B x'''''' f x''''''') (@lem5015700 A x''''''' s)). Qed.
Lemma lem5015724 {A : Type'} (x''''''' : A) (x : A) : (term645 A x''''''' x) = (term645 A x''''''' x).
Proof. exact (eq_refl (term645 A x''''''' x)). Qed.
Lemma lem5015725 {A B : Type'} (x : A) (x'''''' : B) (f : A -> B) (x''''''' : A) (s : A -> Prop) : (term726 A B x x'''''' f x''''''' s) = (term1670 A B x x'''''' f x''''''' s).
Proof. exact (MK_COMB (@lem5015724 A x''''''' x) (@lem5015715 A B x'''''' f x''''''' s)). Qed.
Lemma lem5015732 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5015733 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5015732 A (type686 A) f x). Qed.
Lemma lem5015734 {A : Type'} (x''''''' : A) : (@IN A x''''''') = (@I (A -> (A -> Prop) -> Prop) (@IN A) x''''''').
Proof. exact (@lem5015733 A (@IN A) x'''''''). Qed.
Lemma lem5015735 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5015736 {A : Type'} (x''''''' : A) (s : A -> Prop) : (@IN A x''''''' s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x''''''' s).
Proof. exact (MK_COMB (@lem5015734 A x''''''') (@lem5015735 A s)). Qed.
Lemma lem5015738 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5015739 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5015738 (A -> Prop) Prop f x). Qed.
Lemma lem5015740 {A : Type'} (x''''''' : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x''''''' s) = (term1534 A x''''''' s).
Proof. exact (@lem5015739 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x''''''') s). Qed.
Lemma lem5015742 {A : Type'} (x''''''' : A) (s : A -> Prop) : (@IN A x''''''' s) = (term1534 A x''''''' s).
Proof. exact (TRANS (@lem5015736 A x''''''' s) (@lem5015740 A x''''''' s)). Qed.
Lemma lem5015749 {B : Type'} (x'''''' : B) (y : B) : (term572 B x'''''' y) = (term572 B x'''''' y).
Proof. exact (eq_refl (term572 B x'''''' y)). Qed.
Lemma lem5015750 {A B : Type'} (x'''''' : B) (y : B) (x''''''' : A) (s : A -> Prop) : (term573 A B x'''''' y x''''''' s) = (term1671 A B x'''''' y x''''''' s).
Proof. exact (MK_COMB (@lem5015749 B x'''''' y) (@lem5015742 A x''''''' s)). Qed.
Lemma lem5015757 {A : Type'} (x''''''' : A) (x : A) : (term572 A x''''''' x) = (term572 A x''''''' x).
Proof. exact (eq_refl (term572 A x''''''' x)). Qed.
Lemma lem5015758 {A B : Type'} (x : A) (x'''''' : B) (y : B) (x''''''' : A) (s : A -> Prop) : (term722 A B x x'''''' y x''''''' s) = (term1672 A B x x'''''' y x''''''' s).
Proof. exact (MK_COMB (@lem5015757 A x''''''' x) (@lem5015750 A B x'''''' y x''''''' s)). Qed.
Lemma lem5015759 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5015760 {A B : Type'} (x : A) (x'''''' : B) (y : B) (x''''''' : A) (s : A -> Prop) : (term724 A B x x'''''' y x''''''' s) = (term1673 A B x x'''''' y x''''''' s).
Proof. exact (MK_COMB (@lem5015759) (@lem5015758 A B x x'''''' y x''''''' s)). Qed.
Lemma lem5015761 {A B : Type'} (y : B) (x : A) (x'''''' : B) (f : A -> B) (x''''''' : A) (s : A -> Prop) : (term578 A B y x x'''''' f x''''''' s) = (term1674 A B y x x'''''' f x''''''' s).
Proof. exact (MK_COMB (@lem5015760 A B x x'''''' y x''''''' s) (@lem5015725 A B x x'''''' f x''''''' s)). Qed.
Lemma lem5015768 {B : Type'} (x'''''' : B) (y : B) : (term384 B x'''''' y) = (term384 B x'''''' y).
Proof. exact (eq_refl (term384 B x'''''' y)). Qed.
Lemma lem5015769 {A B : Type'} (y : B) (x : A) (x'''''' : B) (f : A -> B) (x''''''' : A) (s : A -> Prop) : (term828 A B y x x'''''' f x''''''' s) = (term1675 A B y x x'''''' f x''''''' s).
Proof. exact (MK_COMB (@lem5015768 B x'''''' y) (@lem5015761 A B y x x'''''' f x''''''' s)). Qed.
Lemma lem5015770 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5015771 {A B : Type'} (y : B) (x : A) (x'''''' : B) (f : A -> B) (x''''''' : A) (s : A -> Prop) : (term845 A B y x x'''''' f x''''''' s) = (term1676 A B y x x'''''' f x''''''' s).
Proof. exact (MK_COMB (@lem5015770) (@lem5015769 A B y x x'''''' f x''''''' s)). Qed.
Lemma lem5015772 {A B : Type'} (x : A) (f : A -> B) (x''''''' : A) (s : A -> Prop) (y : B) (x'''''' : B) (t : B -> Prop) : (term847 A B x f x''''''' s y x'''''' t) = (term1677 A B x f x''''''' s y x'''''' t).
Proof. exact (MK_COMB (@lem5015771 A B y x x'''''' f x''''''' s) (@lem5015683 B y x'''''' t)). Qed.
Lemma lem5015773 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5015774 {A B : Type'} (x : A) (f : A -> B) (x''''''' : A) (s : A -> Prop) (y : B) (x'''''' : B) (t : B -> Prop) : (term971 A B x f x''''''' s y x'''''' t) = (term1678 A B x f x''''''' s y x'''''' t).
Proof. exact (MK_COMB (@lem5015773) (@lem5015772 A B x f x''''''' s y x'''''' t)). Qed.
Lemma lem5015775 {A B : Type'} (x'''''' : B) (t : B -> Prop) (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x''''''' : A) (y' : A) : (term985 A B x'''''' t y x s f x''''''' y') = (term1679 A B x'''''' t y x s f x''''''' y').
Proof. exact (MK_COMB (@lem5015774 A B x f x''''''' s y x'''''' t) (@lem5015654 A B y x s f x''''''' y')). Qed.
Lemma lem5015776 {A B : Type'} (x'''''' : B) (t : B -> Prop) (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term985 A B x'''''' t y x s f x''''''' y') : term1679 A B x'''''' t y x s f x''''''' y'.
Proof. exact (EQ_MP (@lem5015775 A B x'''''' t y x s f x''''''' y') (@lem5014258 A B x'''''' t y x s f x''''''' y' h1)). Qed.
Lemma lem5015780 {A B : Type'} (x'''' : type1448 A B) (h1 : term1381 A B x'''') : term1643 A B.
Proof. exact (proj1 (@lem5015235 A B x'''' h1)). Qed.
Lemma lem5015785 {B : Type'} (x' : type638 B) (h1 : term1530 B x') : term1567 B.
Proof. exact (proj2 (@lem5014632 B x' h1)). Qed.
Lemma lem5015787 {A B : Type'} (x : A) (f : A -> B) (x''''''' : A) (s : A -> Prop) (y : B) (x'''''' : B) (t : B -> Prop) (h1 : term1677 A B x f x''''''' s y x'''''' t) : term1677 A B x f x''''''' s y x'''''' t.
Proof. exact (h1). Qed.
Lemma lem5015788 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term1667 A B y x s f x''''''' y') : term1667 A B y x s f x''''''' y'.
Proof. exact (h1). Qed.
Lemma lem5015789 {A B : Type'} (x : A) (f : A -> B) (x''''''' : A) (s : A -> Prop) (y : B) (x'''''' : B) (t : B -> Prop) (h1 : term1677 A B x f x''''''' s y x'''''' t) : term1668 B y x'''''' t.
Proof. exact (proj2 (@lem5015787 A B x f x''''''' s y x'''''' t h1)). Qed.
Lemma lem5015790 {A B : Type'} (x : A) (f : A -> B) (x''''''' : A) (s : A -> Prop) (y : B) (x'''''' : B) (t : B -> Prop) (h1 : term1677 A B x f x''''''' s y x'''''' t) : term1675 A B y x x'''''' f x''''''' s.
Proof. exact (proj1 (@lem5015787 A B x f x''''''' s y x'''''' t h1)). Qed.
Lemma lem5015794 {A B : Type'} (y : B) (x : A) (x'''''' : B) (f : A -> B) (x''''''' : A) (s : A -> Prop) (h1 : term1674 A B y x x'''''' f x''''''' s) : term1674 A B y x x'''''' f x''''''' s.
Proof. exact (h1). Qed.
Lemma lem5015795 {A B : Type'} (x : A) (x'''''' : B) (y : B) (x''''''' : A) (s : A -> Prop) (h1 : term1672 A B x x'''''' y x''''''' s) : term1672 A B x x'''''' y x''''''' s.
Proof. exact (h1). Qed.
Lemma lem5015796 {A B : Type'} (x : A) (x'''''' : B) (f : A -> B) (x''''''' : A) (s : A -> Prop) (h1 : term1670 A B x x'''''' f x''''''' s) : term1670 A B x x'''''' f x''''''' s.
Proof. exact (h1). Qed.
Lemma lem5015797 {A B : Type'} (x : A) (x'''''' : B) (y : B) (x''''''' : A) (s : A -> Prop) (h1 : term1672 A B x x'''''' y x''''''' s) : term1671 A B x'''''' y x''''''' s.
Proof. exact (proj2 (@lem5015795 A B x x'''''' y x''''''' s h1)). Qed.
Lemma lem5015801 {A B : Type'} (x : A) (x'''''' : B) (f : A -> B) (x''''''' : A) (s : A -> Prop) (h1 : term1670 A B x x'''''' f x''''''' s) : term1669 A B x'''''' f x''''''' s.
Proof. exact (proj2 (@lem5015796 A B x x'''''' f x''''''' s h1)). Qed.
Lemma lem5015805 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term1665 A B x s y f x''''''' y') : term1665 A B x s y f x''''''' y'.
Proof. exact (h1). Qed.
Lemma lem5015806 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term1659 A B y x s f x''''''' y') : term1659 A B y x s f x''''''' y'.
Proof. exact (h1). Qed.
Lemma lem5015807 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term1665 A B x s y f x''''''' y') : term1664 A B x s y f x''''''' y'.
Proof. exact (proj2 (@lem5015805 A B x s y f x''''''' y' h1)). Qed.
Lemma lem5015809 {A : Type'} (x : A) (x''''''' : A) (y' : A) (h1 : term637 A x x''''''' y') : term637 A x x''''''' y'.
Proof. exact (h1). Qed.
Lemma lem5015810 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term1663 A B x s y f x''''''' y') : term1663 A B x s y f x''''''' y'.
Proof. exact (h1). Qed.
Lemma lem5015813 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term1663 A B x s y f x''''''' y') : term1662 A B s y f x''''''' y'.
Proof. exact (proj2 (@lem5015810 A B x s y f x''''''' y' h1)). Qed.
Lemma lem5015815 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term1663 A B x s y f x''''''' y') : term1661 A B y f x''''''' y'.
Proof. exact (proj2 (@lem5015813 A B x s y f x''''''' y' h1)). Qed.
Lemma lem5015819 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term1659 A B y x s f x''''''' y') : term1658 A B y x s f x''''''' y'.
Proof. exact (proj2 (@lem5015806 A B y x s f x''''''' y' h1)). Qed.
Lemma lem5015821 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term1659 A B y x s f x''''''' y') : term1657 A B y x s f x''''''' y'.
Proof. exact (proj2 (@lem5015819 A B y x s f x''''''' y' h1)). Qed.
Lemma lem5015823 {A B : Type'} (x : A) (f : A -> B) (y : B) (x''''''' : A) (y' : A) (h1 : term1655 A B x f y x''''''' y') : term1655 A B x f y x''''''' y'.
Proof. exact (h1). Qed.
Lemma lem5015824 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term1651 A B x s f x''''''' y') : term1651 A B x s f x''''''' y'.
Proof. exact (h1). Qed.
Lemma lem5015825 {A B : Type'} (x : A) (f : A -> B) (y : B) (x''''''' : A) (y' : A) (h1 : term1655 A B x f y x''''''' y') : term1654 A B f y x''''''' y'.
Proof. exact (proj2 (@lem5015823 A B x f y x''''''' y' h1)). Qed.
Lemma lem5015829 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term1651 A B x s f x''''''' y') : term1650 A B s f x''''''' y'.
Proof. exact (proj2 (@lem5015824 A B x s f x''''''' y' h1)). Qed.
Lemma lem5015831 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term1651 A B x s f x''''''' y') : term1648 A B f x''''''' y'.
Proof. exact (proj2 (@lem5015829 A B x s f x''''''' y' h1)). Qed.
Lemma lem5016327 {B : Type'} (x'''''' : B) (y : B) (h1 : x'''''' = y) : x'''''' = y.
Proof. exact (h1). Qed.
Lemma lem5016989 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1680 A P Q) = (term1681 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5016990 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1680 A P Q) = (term1681 A P Q).
Proof. exact (@lem5016989 A P Q). Qed.
Lemma lem5016991 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1682 A B y f s) = (term1683 A B y f s).
Proof. exact (@lem5016990 A (term1615 A B y f s) (term1634 A B y f s)). Qed.
Lemma lem5016992 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term1684 A B y f s x) = (term1633 A B y f x s).
Proof. exact (eq_refl (term1684 A B y f s x)). Qed.
Lemma lem5016993 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1685 A B y f s) = (term1634 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem5016992 A B y f x s)). Qed.
Lemma lem5016994 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5016995 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1686 A B y f s) = (term1635 A B y f s).
Proof. exact (MK_COMB (@lem5016994 A) (@lem5016993 A B y f s)). Qed.
Lemma lem5016996 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1636 A B y f s) = (term1636 A B y f s).
Proof. exact (eq_refl (term1636 A B y f s)). Qed.
Lemma lem5016997 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1682 A B y f s) = (term1637 A B y f s).
Proof. exact (MK_COMB (@lem5016996 A B y f s) (@lem5016995 A B y f s)). Qed.
Lemma lem5016998 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5016999 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1687 A B y f s) = (term1688 A B y f s).
Proof. exact (MK_COMB (@lem5016998) (@lem5016997 A B y f s)). Qed.
Lemma lem5017000 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term1684 A B y f s x) = (term1633 A B y f x s).
Proof. exact (eq_refl (term1684 A B y f s x)). Qed.
Lemma lem5017001 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1636 A B y f s) = (term1636 A B y f s).
Proof. exact (eq_refl (term1636 A B y f s)). Qed.
Lemma lem5017002 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term1689 A B y f s x) = (term1690 A B y f x s).
Proof. exact (MK_COMB (@lem5017001 A B y f s) (@lem5017000 A B y f x s)). Qed.
Lemma lem5017003 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1691 A B y f s) = (term1692 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem5017002 A B y f x s)). Qed.
Lemma lem5017004 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5017005 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1683 A B y f s) = (term1693 A B y f s).
Proof. exact (MK_COMB (@lem5017004 A) (@lem5017003 A B y f s)). Qed.
Lemma lem5017006 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : ((term1682 A B y f s) = (term1683 A B y f s)) = ((term1637 A B y f s) = (term1693 A B y f s)).
Proof. exact (MK_COMB (@lem5016999 A B y f s) (@lem5017005 A B y f s)). Qed.
Lemma lem5017007 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1637 A B y f s) = (term1693 A B y f s).
Proof. exact (EQ_MP (@lem5017006 A B y f s) (@lem5016991 A B y f s)). Qed.
Lemma lem5017008 {A B : Type'} (y : B) (s : A -> Prop) : (term1638 A B y s) = (term1694 A B y s).
Proof. exact (fun_ext (fun f : A -> B => @lem5017007 A B y f s)). Qed.
Lemma lem5017009 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5017010 {A B : Type'} (y : B) (s : A -> Prop) : (term1639 A B y s) = (term1695 A B y s).
Proof. exact (MK_COMB (@lem5017009 A B) (@lem5017008 A B y s)). Qed.
Lemma lem5017011 {A B : Type'} (y : B) : (term1640 A B y) = (term1696 A B y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5017010 A B y s)). Qed.
Lemma lem5017012 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5017013 {A B : Type'} (y : B) : (term1641 A B y) = (term1697 A B y).
Proof. exact (MK_COMB (@lem5017012 A) (@lem5017011 A B y)). Qed.
Lemma lem5017014 {A B : Type'} : (term1642 A B) = (term1698 A B).
Proof. exact (fun_ext (fun y : B => @lem5017013 A B y)). Qed.
Lemma lem5017015 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5017016 {A B : Type'} : (term1643 A B) = (term1699 A B).
Proof. exact (MK_COMB (@lem5017015 B) (@lem5017014 A B)). Qed.
Lemma lem5017029 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term1690 A B y f x s) = (term1690 A B y f x s).
Proof. exact (eq_refl (term1690 A B y f x s)). Qed.
Lemma lem5017030 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1692 A B y f s) = (term1692 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem5017029 A B y f x s)). Qed.
Lemma lem5017031 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5017032 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1693 A B y f s) = (term1693 A B y f s).
Proof. exact (MK_COMB (@lem5017031 A) (@lem5017030 A B y f s)). Qed.
Lemma lem5017033 {A B : Type'} (y : B) (s : A -> Prop) : (term1694 A B y s) = (term1694 A B y s).
Proof. exact (fun_ext (fun f : A -> B => @lem5017032 A B y f s)). Qed.
Lemma lem5017034 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5017035 {A B : Type'} (y : B) (s : A -> Prop) : (term1695 A B y s) = (term1695 A B y s).
Proof. exact (MK_COMB (@lem5017034 A B) (@lem5017033 A B y s)). Qed.
Lemma lem5017036 {A B : Type'} (y : B) : (term1696 A B y) = (term1696 A B y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5017035 A B y s)). Qed.
Lemma lem5017037 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5017038 {A B : Type'} (y : B) : (term1697 A B y) = (term1697 A B y).
Proof. exact (MK_COMB (@lem5017037 A) (@lem5017036 A B y)). Qed.
Lemma lem5017039 {A B : Type'} : (term1698 A B) = (term1698 A B).
Proof. exact (fun_ext (fun y : B => @lem5017038 A B y)). Qed.
Lemma lem5017040 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5017041 {A B : Type'} : (term1699 A B) = (term1699 A B).
Proof. exact (MK_COMB (@lem5017040 B) (@lem5017039 A B)). Qed.
Lemma lem5017042 {A B : Type'} : (term1643 A B) = (term1699 A B).
Proof. exact (TRANS (@lem5017016 A B) (@lem5017041 A B)). Qed.
Lemma lem5017043 {A B : Type'} (x'''' : type1448 A B) (h1 : term1381 A B x'''') : term1699 A B.
Proof. exact (EQ_MP (@lem5017042 A B) (@lem5015780 A B x'''' h1)). Qed.
Lemma lem5017261 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1680 A P Q) = (term1681 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5017262 {B : Type'} (P : Prop) (Q : B -> Prop) : (term1680 B P Q) = (term1681 B P Q).
Proof. exact (@lem5017261 B P Q). Qed.
Lemma lem5017263 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1700 B s t) = (term1701 B s t).
Proof. exact (@lem5017262 B (term1561 B s t) (term1557 B s t)). Qed.
Lemma lem5017264 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term1702 B s t x) = (term1556 B s x t).
Proof. exact (eq_refl (term1702 B s t x)). Qed.
Lemma lem5017265 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1703 B s t) = (term1557 B s t).
Proof. exact (fun_ext (fun x : B => @lem5017264 B s x t)). Qed.
Lemma lem5017266 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5017267 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1704 B s t) = (term1558 B s t).
Proof. exact (MK_COMB (@lem5017266 B) (@lem5017265 B s t)). Qed.
Lemma lem5017268 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1562 B s t) = (term1562 B s t).
Proof. exact (eq_refl (term1562 B s t)). Qed.
Lemma lem5017269 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1700 B s t) = (term1563 B s t).
Proof. exact (MK_COMB (@lem5017268 B s t) (@lem5017267 B s t)). Qed.
Lemma lem5017270 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5017271 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1705 B s t) = (term1706 B s t).
Proof. exact (MK_COMB (@lem5017270) (@lem5017269 B s t)). Qed.
Lemma lem5017272 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term1702 B s t x) = (term1556 B s x t).
Proof. exact (eq_refl (term1702 B s t x)). Qed.
Lemma lem5017273 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1562 B s t) = (term1562 B s t).
Proof. exact (eq_refl (term1562 B s t)). Qed.
Lemma lem5017274 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term1707 B s t x) = (term1708 B s x t).
Proof. exact (MK_COMB (@lem5017273 B s t) (@lem5017272 B s x t)). Qed.
Lemma lem5017275 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1709 B s t) = (term1710 B s t).
Proof. exact (fun_ext (fun x : B => @lem5017274 B s x t)). Qed.
Lemma lem5017276 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5017277 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1701 B s t) = (term1711 B s t).
Proof. exact (MK_COMB (@lem5017276 B) (@lem5017275 B s t)). Qed.
Lemma lem5017278 {B : Type'} (s : B -> Prop) (t : B -> Prop) : ((term1700 B s t) = (term1701 B s t)) = ((term1563 B s t) = (term1711 B s t)).
Proof. exact (MK_COMB (@lem5017271 B s t) (@lem5017277 B s t)). Qed.
Lemma lem5017279 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1563 B s t) = (term1711 B s t).
Proof. exact (EQ_MP (@lem5017278 B s t) (@lem5017263 B s t)). Qed.
Lemma lem5017280 {B : Type'} (s : B -> Prop) : (term1564 B s) = (term1712 B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5017279 B s t)). Qed.
Lemma lem5017281 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5017282 {B : Type'} (s : B -> Prop) : (term1565 B s) = (term1713 B s).
Proof. exact (MK_COMB (@lem5017281 B) (@lem5017280 B s)). Qed.
Lemma lem5017283 {B : Type'} : (term1566 B) = (term1714 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5017282 B s)). Qed.
Lemma lem5017284 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5017285 {B : Type'} : (term1567 B) = (term1715 B).
Proof. exact (MK_COMB (@lem5017284 B) (@lem5017283 B)). Qed.
Lemma lem5017298 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term1708 B s x t) = (term1708 B s x t).
Proof. exact (eq_refl (term1708 B s x t)). Qed.
Lemma lem5017299 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1710 B s t) = (term1710 B s t).
Proof. exact (fun_ext (fun x : B => @lem5017298 B s x t)). Qed.
Lemma lem5017300 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5017301 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1711 B s t) = (term1711 B s t).
Proof. exact (MK_COMB (@lem5017300 B) (@lem5017299 B s t)). Qed.
Lemma lem5017302 {B : Type'} (s : B -> Prop) : (term1712 B s) = (term1712 B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5017301 B s t)). Qed.
Lemma lem5017303 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5017304 {B : Type'} (s : B -> Prop) : (term1713 B s) = (term1713 B s).
Proof. exact (MK_COMB (@lem5017303 B) (@lem5017302 B s)). Qed.
Lemma lem5017305 {B : Type'} : (term1714 B) = (term1714 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5017304 B s)). Qed.
Lemma lem5017306 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5017307 {B : Type'} : (term1715 B) = (term1715 B).
Proof. exact (MK_COMB (@lem5017306 B) (@lem5017305 B)). Qed.
Lemma lem5017308 {B : Type'} : (term1567 B) = (term1715 B).
Proof. exact (TRANS (@lem5017285 B) (@lem5017307 B)). Qed.
Lemma lem5017309 {B : Type'} (x' : type638 B) (h1 : term1530 B x') : term1715 B.
Proof. exact (EQ_MP (@lem5017308 B) (@lem5015785 B x' h1)). Qed.
Lemma lem5017983 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1680 A P Q) = (term1681 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5017984 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1680 A P Q) = (term1681 A P Q).
Proof. exact (@lem5017983 A P Q). Qed.
Lemma lem5017985 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1682 A B y f s) = (term1683 A B y f s).
Proof. exact (@lem5017984 A (term1615 A B y f s) (term1634 A B y f s)). Qed.
Lemma lem5017986 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term1684 A B y f s x) = (term1633 A B y f x s).
Proof. exact (eq_refl (term1684 A B y f s x)). Qed.
Lemma lem5017987 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1685 A B y f s) = (term1634 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem5017986 A B y f x s)). Qed.
Lemma lem5017988 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5017989 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1686 A B y f s) = (term1635 A B y f s).
Proof. exact (MK_COMB (@lem5017988 A) (@lem5017987 A B y f s)). Qed.
Lemma lem5017990 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1636 A B y f s) = (term1636 A B y f s).
Proof. exact (eq_refl (term1636 A B y f s)). Qed.
Lemma lem5017991 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1682 A B y f s) = (term1637 A B y f s).
Proof. exact (MK_COMB (@lem5017990 A B y f s) (@lem5017989 A B y f s)). Qed.
Lemma lem5017992 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5017993 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1687 A B y f s) = (term1688 A B y f s).
Proof. exact (MK_COMB (@lem5017992) (@lem5017991 A B y f s)). Qed.
Lemma lem5017994 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term1684 A B y f s x) = (term1633 A B y f x s).
Proof. exact (eq_refl (term1684 A B y f s x)). Qed.
Lemma lem5017995 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1636 A B y f s) = (term1636 A B y f s).
Proof. exact (eq_refl (term1636 A B y f s)). Qed.
Lemma lem5017996 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term1689 A B y f s x) = (term1690 A B y f x s).
Proof. exact (MK_COMB (@lem5017995 A B y f s) (@lem5017994 A B y f x s)). Qed.
Lemma lem5017997 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1691 A B y f s) = (term1692 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem5017996 A B y f x s)). Qed.
Lemma lem5017998 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5017999 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1683 A B y f s) = (term1693 A B y f s).
Proof. exact (MK_COMB (@lem5017998 A) (@lem5017997 A B y f s)). Qed.
Lemma lem5018000 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : ((term1682 A B y f s) = (term1683 A B y f s)) = ((term1637 A B y f s) = (term1693 A B y f s)).
Proof. exact (MK_COMB (@lem5017993 A B y f s) (@lem5017999 A B y f s)). Qed.
Lemma lem5018001 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1637 A B y f s) = (term1693 A B y f s).
Proof. exact (EQ_MP (@lem5018000 A B y f s) (@lem5017985 A B y f s)). Qed.
Lemma lem5018002 {A B : Type'} (y : B) (s : A -> Prop) : (term1638 A B y s) = (term1694 A B y s).
Proof. exact (fun_ext (fun f : A -> B => @lem5018001 A B y f s)). Qed.
Lemma lem5018003 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5018004 {A B : Type'} (y : B) (s : A -> Prop) : (term1639 A B y s) = (term1695 A B y s).
Proof. exact (MK_COMB (@lem5018003 A B) (@lem5018002 A B y s)). Qed.
Lemma lem5018005 {A B : Type'} (y : B) : (term1640 A B y) = (term1696 A B y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5018004 A B y s)). Qed.
Lemma lem5018006 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5018007 {A B : Type'} (y : B) : (term1641 A B y) = (term1697 A B y).
Proof. exact (MK_COMB (@lem5018006 A) (@lem5018005 A B y)). Qed.
Lemma lem5018008 {A B : Type'} : (term1642 A B) = (term1698 A B).
Proof. exact (fun_ext (fun y : B => @lem5018007 A B y)). Qed.
Lemma lem5018009 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5018010 {A B : Type'} : (term1643 A B) = (term1699 A B).
Proof. exact (MK_COMB (@lem5018009 B) (@lem5018008 A B)). Qed.
Lemma lem5018023 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term1690 A B y f x s) = (term1690 A B y f x s).
Proof. exact (eq_refl (term1690 A B y f x s)). Qed.
Lemma lem5018024 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1692 A B y f s) = (term1692 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem5018023 A B y f x s)). Qed.
Lemma lem5018025 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5018026 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1693 A B y f s) = (term1693 A B y f s).
Proof. exact (MK_COMB (@lem5018025 A) (@lem5018024 A B y f s)). Qed.
Lemma lem5018027 {A B : Type'} (y : B) (s : A -> Prop) : (term1694 A B y s) = (term1694 A B y s).
Proof. exact (fun_ext (fun f : A -> B => @lem5018026 A B y f s)). Qed.
Lemma lem5018028 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5018029 {A B : Type'} (y : B) (s : A -> Prop) : (term1695 A B y s) = (term1695 A B y s).
Proof. exact (MK_COMB (@lem5018028 A B) (@lem5018027 A B y s)). Qed.
Lemma lem5018030 {A B : Type'} (y : B) : (term1696 A B y) = (term1696 A B y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5018029 A B y s)). Qed.
Lemma lem5018031 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5018032 {A B : Type'} (y : B) : (term1697 A B y) = (term1697 A B y).
Proof. exact (MK_COMB (@lem5018031 A) (@lem5018030 A B y)). Qed.
Lemma lem5018033 {A B : Type'} : (term1698 A B) = (term1698 A B).
Proof. exact (fun_ext (fun y : B => @lem5018032 A B y)). Qed.
Lemma lem5018034 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5018035 {A B : Type'} : (term1699 A B) = (term1699 A B).
Proof. exact (MK_COMB (@lem5018034 B) (@lem5018033 A B)). Qed.
Lemma lem5018036 {A B : Type'} : (term1643 A B) = (term1699 A B).
Proof. exact (TRANS (@lem5018010 A B) (@lem5018035 A B)). Qed.
Lemma lem5018037 {A B : Type'} (x'''' : type1448 A B) (h1 : term1381 A B x'''') : term1699 A B.
Proof. exact (EQ_MP (@lem5018036 A B) (@lem5015780 A B x'''' h1)). Qed.
Lemma lem5018255 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1680 A P Q) = (term1681 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5018256 {B : Type'} (P : Prop) (Q : B -> Prop) : (term1680 B P Q) = (term1681 B P Q).
Proof. exact (@lem5018255 B P Q). Qed.
Lemma lem5018257 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1700 B s t) = (term1701 B s t).
Proof. exact (@lem5018256 B (term1561 B s t) (term1557 B s t)). Qed.
Lemma lem5018258 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term1702 B s t x) = (term1556 B s x t).
Proof. exact (eq_refl (term1702 B s t x)). Qed.
Lemma lem5018259 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1703 B s t) = (term1557 B s t).
Proof. exact (fun_ext (fun x : B => @lem5018258 B s x t)). Qed.
Lemma lem5018260 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5018261 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1704 B s t) = (term1558 B s t).
Proof. exact (MK_COMB (@lem5018260 B) (@lem5018259 B s t)). Qed.
Lemma lem5018262 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1562 B s t) = (term1562 B s t).
Proof. exact (eq_refl (term1562 B s t)). Qed.
Lemma lem5018263 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1700 B s t) = (term1563 B s t).
Proof. exact (MK_COMB (@lem5018262 B s t) (@lem5018261 B s t)). Qed.
Lemma lem5018264 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5018265 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1705 B s t) = (term1706 B s t).
Proof. exact (MK_COMB (@lem5018264) (@lem5018263 B s t)). Qed.
Lemma lem5018266 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term1702 B s t x) = (term1556 B s x t).
Proof. exact (eq_refl (term1702 B s t x)). Qed.
Lemma lem5018267 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1562 B s t) = (term1562 B s t).
Proof. exact (eq_refl (term1562 B s t)). Qed.
Lemma lem5018268 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term1707 B s t x) = (term1708 B s x t).
Proof. exact (MK_COMB (@lem5018267 B s t) (@lem5018266 B s x t)). Qed.
Lemma lem5018269 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1709 B s t) = (term1710 B s t).
Proof. exact (fun_ext (fun x : B => @lem5018268 B s x t)). Qed.
Lemma lem5018270 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5018271 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1701 B s t) = (term1711 B s t).
Proof. exact (MK_COMB (@lem5018270 B) (@lem5018269 B s t)). Qed.
Lemma lem5018272 {B : Type'} (s : B -> Prop) (t : B -> Prop) : ((term1700 B s t) = (term1701 B s t)) = ((term1563 B s t) = (term1711 B s t)).
Proof. exact (MK_COMB (@lem5018265 B s t) (@lem5018271 B s t)). Qed.
Lemma lem5018273 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1563 B s t) = (term1711 B s t).
Proof. exact (EQ_MP (@lem5018272 B s t) (@lem5018257 B s t)). Qed.
Lemma lem5018274 {B : Type'} (s : B -> Prop) : (term1564 B s) = (term1712 B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5018273 B s t)). Qed.
Lemma lem5018275 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5018276 {B : Type'} (s : B -> Prop) : (term1565 B s) = (term1713 B s).
Proof. exact (MK_COMB (@lem5018275 B) (@lem5018274 B s)). Qed.
Lemma lem5018277 {B : Type'} : (term1566 B) = (term1714 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5018276 B s)). Qed.
Lemma lem5018278 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5018279 {B : Type'} : (term1567 B) = (term1715 B).
Proof. exact (MK_COMB (@lem5018278 B) (@lem5018277 B)). Qed.
Lemma lem5018292 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term1708 B s x t) = (term1708 B s x t).
Proof. exact (eq_refl (term1708 B s x t)). Qed.
Lemma lem5018293 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1710 B s t) = (term1710 B s t).
Proof. exact (fun_ext (fun x : B => @lem5018292 B s x t)). Qed.
Lemma lem5018294 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5018295 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1711 B s t) = (term1711 B s t).
Proof. exact (MK_COMB (@lem5018294 B) (@lem5018293 B s t)). Qed.
Lemma lem5018296 {B : Type'} (s : B -> Prop) : (term1712 B s) = (term1712 B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5018295 B s t)). Qed.
Lemma lem5018297 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5018298 {B : Type'} (s : B -> Prop) : (term1713 B s) = (term1713 B s).
Proof. exact (MK_COMB (@lem5018297 B) (@lem5018296 B s)). Qed.
Lemma lem5018299 {B : Type'} : (term1714 B) = (term1714 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5018298 B s)). Qed.
Lemma lem5018300 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5018301 {B : Type'} : (term1715 B) = (term1715 B).
Proof. exact (MK_COMB (@lem5018300 B) (@lem5018299 B)). Qed.
Lemma lem5018302 {B : Type'} : (term1567 B) = (term1715 B).
Proof. exact (TRANS (@lem5018279 B) (@lem5018301 B)). Qed.
Lemma lem5018303 {B : Type'} (x' : type638 B) (h1 : term1530 B x') : term1715 B.
Proof. exact (EQ_MP (@lem5018302 B) (@lem5015785 B x' h1)). Qed.
Lemma lem5018484 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1680 A P Q) = (term1681 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5018485 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1680 A P Q) = (term1681 A P Q).
Proof. exact (@lem5018484 A P Q). Qed.
Lemma lem5018486 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1682 A B y f s) = (term1683 A B y f s).
Proof. exact (@lem5018485 A (term1615 A B y f s) (term1634 A B y f s)). Qed.
Lemma lem5018487 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term1684 A B y f s x) = (term1633 A B y f x s).
Proof. exact (eq_refl (term1684 A B y f s x)). Qed.
Lemma lem5018488 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1685 A B y f s) = (term1634 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem5018487 A B y f x s)). Qed.
Lemma lem5018489 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5018490 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1686 A B y f s) = (term1635 A B y f s).
Proof. exact (MK_COMB (@lem5018489 A) (@lem5018488 A B y f s)). Qed.
Lemma lem5018491 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1636 A B y f s) = (term1636 A B y f s).
Proof. exact (eq_refl (term1636 A B y f s)). Qed.
Lemma lem5018492 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1682 A B y f s) = (term1637 A B y f s).
Proof. exact (MK_COMB (@lem5018491 A B y f s) (@lem5018490 A B y f s)). Qed.
Lemma lem5018493 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5018494 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1687 A B y f s) = (term1688 A B y f s).
Proof. exact (MK_COMB (@lem5018493) (@lem5018492 A B y f s)). Qed.
Lemma lem5018495 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term1684 A B y f s x) = (term1633 A B y f x s).
Proof. exact (eq_refl (term1684 A B y f s x)). Qed.
Lemma lem5018496 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1636 A B y f s) = (term1636 A B y f s).
Proof. exact (eq_refl (term1636 A B y f s)). Qed.
Lemma lem5018497 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term1689 A B y f s x) = (term1690 A B y f x s).
Proof. exact (MK_COMB (@lem5018496 A B y f s) (@lem5018495 A B y f x s)). Qed.
Lemma lem5018498 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1691 A B y f s) = (term1692 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem5018497 A B y f x s)). Qed.
Lemma lem5018499 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5018500 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1683 A B y f s) = (term1693 A B y f s).
Proof. exact (MK_COMB (@lem5018499 A) (@lem5018498 A B y f s)). Qed.
Lemma lem5018501 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : ((term1682 A B y f s) = (term1683 A B y f s)) = ((term1637 A B y f s) = (term1693 A B y f s)).
Proof. exact (MK_COMB (@lem5018494 A B y f s) (@lem5018500 A B y f s)). Qed.
Lemma lem5018502 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1637 A B y f s) = (term1693 A B y f s).
Proof. exact (EQ_MP (@lem5018501 A B y f s) (@lem5018486 A B y f s)). Qed.
Lemma lem5018503 {A B : Type'} (y : B) (s : A -> Prop) : (term1638 A B y s) = (term1694 A B y s).
Proof. exact (fun_ext (fun f : A -> B => @lem5018502 A B y f s)). Qed.
Lemma lem5018504 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5018505 {A B : Type'} (y : B) (s : A -> Prop) : (term1639 A B y s) = (term1695 A B y s).
Proof. exact (MK_COMB (@lem5018504 A B) (@lem5018503 A B y s)). Qed.
Lemma lem5018506 {A B : Type'} (y : B) : (term1640 A B y) = (term1696 A B y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5018505 A B y s)). Qed.
Lemma lem5018507 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5018508 {A B : Type'} (y : B) : (term1641 A B y) = (term1697 A B y).
Proof. exact (MK_COMB (@lem5018507 A) (@lem5018506 A B y)). Qed.
Lemma lem5018509 {A B : Type'} : (term1642 A B) = (term1698 A B).
Proof. exact (fun_ext (fun y : B => @lem5018508 A B y)). Qed.
Lemma lem5018510 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5018511 {A B : Type'} : (term1643 A B) = (term1699 A B).
Proof. exact (MK_COMB (@lem5018510 B) (@lem5018509 A B)). Qed.
Lemma lem5018524 {A B : Type'} (y : B) (f : A -> B) (x : A) (s : A -> Prop) : (term1690 A B y f x s) = (term1690 A B y f x s).
Proof. exact (eq_refl (term1690 A B y f x s)). Qed.
Lemma lem5018525 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1692 A B y f s) = (term1692 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem5018524 A B y f x s)). Qed.
Lemma lem5018526 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5018527 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term1693 A B y f s) = (term1693 A B y f s).
Proof. exact (MK_COMB (@lem5018526 A) (@lem5018525 A B y f s)). Qed.
Lemma lem5018528 {A B : Type'} (y : B) (s : A -> Prop) : (term1694 A B y s) = (term1694 A B y s).
Proof. exact (fun_ext (fun f : A -> B => @lem5018527 A B y f s)). Qed.
Lemma lem5018529 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5018530 {A B : Type'} (y : B) (s : A -> Prop) : (term1695 A B y s) = (term1695 A B y s).
Proof. exact (MK_COMB (@lem5018529 A B) (@lem5018528 A B y s)). Qed.
Lemma lem5018531 {A B : Type'} (y : B) : (term1696 A B y) = (term1696 A B y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5018530 A B y s)). Qed.
Lemma lem5018532 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5018533 {A B : Type'} (y : B) : (term1697 A B y) = (term1697 A B y).
Proof. exact (MK_COMB (@lem5018532 A) (@lem5018531 A B y)). Qed.
Lemma lem5018534 {A B : Type'} : (term1698 A B) = (term1698 A B).
Proof. exact (fun_ext (fun y : B => @lem5018533 A B y)). Qed.
Lemma lem5018535 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5018536 {A B : Type'} : (term1699 A B) = (term1699 A B).
Proof. exact (MK_COMB (@lem5018535 B) (@lem5018534 A B)). Qed.
Lemma lem5018537 {A B : Type'} : (term1643 A B) = (term1699 A B).
Proof. exact (TRANS (@lem5018511 A B) (@lem5018536 A B)). Qed.
Lemma lem5018538 {A B : Type'} (x'''' : type1448 A B) (h1 : term1381 A B x'''') : term1699 A B.
Proof. exact (EQ_MP (@lem5018537 A B) (@lem5015780 A B x'''' h1)). Qed.
Lemma lem5018756 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1680 A P Q) = (term1681 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5018757 {B : Type'} (P : Prop) (Q : B -> Prop) : (term1680 B P Q) = (term1681 B P Q).
Proof. exact (@lem5018756 B P Q). Qed.
Lemma lem5018758 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1700 B s t) = (term1701 B s t).
Proof. exact (@lem5018757 B (term1561 B s t) (term1557 B s t)). Qed.
Lemma lem5018759 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term1702 B s t x) = (term1556 B s x t).
Proof. exact (eq_refl (term1702 B s t x)). Qed.
Lemma lem5018760 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1703 B s t) = (term1557 B s t).
Proof. exact (fun_ext (fun x : B => @lem5018759 B s x t)). Qed.
Lemma lem5018761 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5018762 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1704 B s t) = (term1558 B s t).
Proof. exact (MK_COMB (@lem5018761 B) (@lem5018760 B s t)). Qed.
Lemma lem5018763 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1562 B s t) = (term1562 B s t).
Proof. exact (eq_refl (term1562 B s t)). Qed.
Lemma lem5018764 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1700 B s t) = (term1563 B s t).
Proof. exact (MK_COMB (@lem5018763 B s t) (@lem5018762 B s t)). Qed.
Lemma lem5018765 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5018766 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1705 B s t) = (term1706 B s t).
Proof. exact (MK_COMB (@lem5018765) (@lem5018764 B s t)). Qed.
Lemma lem5018767 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term1702 B s t x) = (term1556 B s x t).
Proof. exact (eq_refl (term1702 B s t x)). Qed.
Lemma lem5018768 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1562 B s t) = (term1562 B s t).
Proof. exact (eq_refl (term1562 B s t)). Qed.
Lemma lem5018769 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term1707 B s t x) = (term1708 B s x t).
Proof. exact (MK_COMB (@lem5018768 B s t) (@lem5018767 B s x t)). Qed.
Lemma lem5018770 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1709 B s t) = (term1710 B s t).
Proof. exact (fun_ext (fun x : B => @lem5018769 B s x t)). Qed.
Lemma lem5018771 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5018772 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1701 B s t) = (term1711 B s t).
Proof. exact (MK_COMB (@lem5018771 B) (@lem5018770 B s t)). Qed.
Lemma lem5018773 {B : Type'} (s : B -> Prop) (t : B -> Prop) : ((term1700 B s t) = (term1701 B s t)) = ((term1563 B s t) = (term1711 B s t)).
Proof. exact (MK_COMB (@lem5018766 B s t) (@lem5018772 B s t)). Qed.
Lemma lem5018774 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1563 B s t) = (term1711 B s t).
Proof. exact (EQ_MP (@lem5018773 B s t) (@lem5018758 B s t)). Qed.
Lemma lem5018775 {B : Type'} (s : B -> Prop) : (term1564 B s) = (term1712 B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5018774 B s t)). Qed.
Lemma lem5018776 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5018777 {B : Type'} (s : B -> Prop) : (term1565 B s) = (term1713 B s).
Proof. exact (MK_COMB (@lem5018776 B) (@lem5018775 B s)). Qed.
Lemma lem5018778 {B : Type'} : (term1566 B) = (term1714 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5018777 B s)). Qed.
Lemma lem5018779 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5018780 {B : Type'} : (term1567 B) = (term1715 B).
Proof. exact (MK_COMB (@lem5018779 B) (@lem5018778 B)). Qed.
Lemma lem5018793 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term1708 B s x t) = (term1708 B s x t).
Proof. exact (eq_refl (term1708 B s x t)). Qed.
Lemma lem5018794 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1710 B s t) = (term1710 B s t).
Proof. exact (fun_ext (fun x : B => @lem5018793 B s x t)). Qed.
Lemma lem5018795 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5018796 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term1711 B s t) = (term1711 B s t).
Proof. exact (MK_COMB (@lem5018795 B) (@lem5018794 B s t)). Qed.
Lemma lem5018797 {B : Type'} (s : B -> Prop) : (term1712 B s) = (term1712 B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5018796 B s t)). Qed.
Lemma lem5018798 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5018799 {B : Type'} (s : B -> Prop) : (term1713 B s) = (term1713 B s).
Proof. exact (MK_COMB (@lem5018798 B) (@lem5018797 B s)). Qed.
Lemma lem5018800 {B : Type'} : (term1714 B) = (term1714 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5018799 B s)). Qed.
Lemma lem5018801 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5018802 {B : Type'} : (term1715 B) = (term1715 B).
Proof. exact (MK_COMB (@lem5018801 B) (@lem5018800 B)). Qed.
Lemma lem5018803 {B : Type'} : (term1567 B) = (term1715 B).
Proof. exact (TRANS (@lem5018780 B) (@lem5018802 B)). Qed.
Lemma lem5018804 {B : Type'} (x' : type638 B) (h1 : term1530 B x') : term1715 B.
Proof. exact (EQ_MP (@lem5018803 B) (@lem5015785 B x' h1)). Qed.
Lemma lem5018850 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1680 A P Q) = (term1681 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5018851 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1680 A P Q) = (term1681 A P Q).
Proof. exact (@lem5018850 A P Q). Qed.
Lemma lem5018852 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term1716 A B s f x) = (term1717 A B s f x).
Proof. exact (@lem5018851 A (term1535 A x s) (term1551 A B s f x)). Qed.
Lemma lem5018853 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term1718 A B s f x y) = (term1550 A B s f x y).
Proof. exact (eq_refl (term1718 A B s f x y)). Qed.
Lemma lem5018854 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term1719 A B s f x) = (term1551 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem5018853 A B s f x y)). Qed.
Lemma lem5018855 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5018856 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term1720 A B s f x) = (term1552 A B s f x).
Proof. exact (MK_COMB (@lem5018855 A) (@lem5018854 A B s f x)). Qed.
Lemma lem5018857 {A : Type'} (x : A) (s : A -> Prop) : (term1549 A x s) = (term1549 A x s).
Proof. exact (eq_refl (term1549 A x s)). Qed.
Lemma lem5018858 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term1716 A B s f x) = (term1553 A B s f x).
Proof. exact (MK_COMB (@lem5018857 A x s) (@lem5018856 A B s f x)). Qed.
Lemma lem5018859 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5018860 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term1721 A B s f x) = (term1722 A B s f x).
Proof. exact (MK_COMB (@lem5018859) (@lem5018858 A B s f x)). Qed.
Lemma lem5018861 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term1718 A B s f x y) = (term1550 A B s f x y).
Proof. exact (eq_refl (term1718 A B s f x y)). Qed.
Lemma lem5018862 {A : Type'} (x : A) (s : A -> Prop) : (term1549 A x s) = (term1549 A x s).
Proof. exact (eq_refl (term1549 A x s)). Qed.
Lemma lem5018863 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term1723 A B s f x y) = (term1724 A B s f x y).
Proof. exact (MK_COMB (@lem5018862 A x s) (@lem5018861 A B s f x y)). Qed.
Lemma lem5018864 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term1725 A B s f x) = (term1726 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem5018863 A B s f x y)). Qed.
Lemma lem5018865 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5018866 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term1717 A B s f x) = (term1727 A B s f x).
Proof. exact (MK_COMB (@lem5018865 A) (@lem5018864 A B s f x)). Qed.
Lemma lem5018867 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : ((term1716 A B s f x) = (term1717 A B s f x)) = ((term1553 A B s f x) = (term1727 A B s f x)).
Proof. exact (MK_COMB (@lem5018860 A B s f x) (@lem5018866 A B s f x)). Qed.
Lemma lem5018868 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term1553 A B s f x) = (term1727 A B s f x).
Proof. exact (EQ_MP (@lem5018867 A B s f x) (@lem5018852 A B s f x)). Qed.
Lemma lem5018869 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term1554 A B s f) = (term1728 A B s f).
Proof. exact (fun_ext (fun x : A => @lem5018868 A B s f x)). Qed.
Lemma lem5018870 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5018871 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term1555 A B s f) = (term1729 A B s f).
Proof. exact (MK_COMB (@lem5018870 A) (@lem5018869 A B s f)). Qed.
Lemma lem5018890 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term1724 A B s f x y) = (term1724 A B s f x y).
Proof. exact (eq_refl (term1724 A B s f x y)). Qed.
Lemma lem5018891 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term1726 A B s f x) = (term1726 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem5018890 A B s f x y)). Qed.
Lemma lem5018892 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5018893 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term1727 A B s f x) = (term1727 A B s f x).
Proof. exact (MK_COMB (@lem5018892 A) (@lem5018891 A B s f x)). Qed.
Lemma lem5018894 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term1728 A B s f) = (term1728 A B s f).
Proof. exact (fun_ext (fun x : A => @lem5018893 A B s f x)). Qed.
Lemma lem5018895 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5018896 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term1729 A B s f) = (term1729 A B s f).
Proof. exact (MK_COMB (@lem5018895 A) (@lem5018894 A B s f)). Qed.
Lemma lem5018897 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term1555 A B s f) = (term1729 A B s f).
Proof. exact (TRANS (@lem5018871 A B s f) (@lem5018896 A B s f)). Qed.
Lemma lem5018898 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term122 A B s f) : term1729 A B s f.
Proof. exact (EQ_MP (@lem5018897 A B s f) (@lem5014461 A B s f h1)). Qed.
Lemma lem5019555 {A B : Type'} (_63072 : B) (x'''' : type1448 A B) (h1 : term1381 A B x'''') : term1730 A B _63072.
Proof. exact (@lem5017043 A B x'''' h1 _63072). Qed.
Lemma lem5019556 {A B : Type'} (_63072 : B) : (term1730 A B _63072) = (term1697 A B _63072).
Proof. exact (eq_refl (term1730 A B _63072)). Qed.
Lemma lem5019557 {A B : Type'} (_63072 : B) (x'''' : type1448 A B) (h1 : term1381 A B x'''') : term1697 A B _63072.
Proof. exact (EQ_MP (@lem5019556 A B _63072) (@lem5019555 A B _63072 x'''' h1)). Qed.
Lemma lem5019558 {A B : Type'} (_63072 : B) (_63073 : A -> Prop) (x'''' : type1448 A B) (h1 : term1381 A B x'''') : term1731 A B _63072 _63073.
Proof. exact (@lem5019557 A B _63072 x'''' h1 _63073). Qed.
Lemma lem5019559 {A B : Type'} (_63072 : B) (_63073 : A -> Prop) : (term1731 A B _63072 _63073) = (term1695 A B _63072 _63073).
Proof. exact (eq_refl (term1731 A B _63072 _63073)). Qed.
Lemma lem5019560 {A B : Type'} (_63072 : B) (_63073 : A -> Prop) (x'''' : type1448 A B) (h1 : term1381 A B x'''') : term1695 A B _63072 _63073.
Proof. exact (EQ_MP (@lem5019559 A B _63072 _63073) (@lem5019558 A B _63072 _63073 x'''' h1)). Qed.
Lemma lem5019561 {A B : Type'} (_63072 : B) (_63073 : A -> Prop) (_63074 : A -> B) (x'''' : type1448 A B) (h1 : term1381 A B x'''') : term1732 A B _63072 _63073 _63074.
Proof. exact (@lem5019560 A B _63072 _63073 x'''' h1 _63074). Qed.
Lemma lem5019562 {A B : Type'} (_63072 : B) (_63074 : A -> B) (_63073 : A -> Prop) : (term1732 A B _63072 _63073 _63074) = (term1693 A B _63072 _63074 _63073).
Proof. exact (eq_refl (term1732 A B _63072 _63073 _63074)). Qed.
Lemma lem5019563 {A B : Type'} (_63072 : B) (_63074 : A -> B) (_63073 : A -> Prop) (x'''' : type1448 A B) (h1 : term1381 A B x'''') : term1693 A B _63072 _63074 _63073.
Proof. exact (EQ_MP (@lem5019562 A B _63072 _63074 _63073) (@lem5019561 A B _63072 _63073 _63074 x'''' h1)). Qed.
Lemma lem5019564 {A B : Type'} (_63072 : B) (_63074 : A -> B) (_63073 : A -> Prop) (_63075 : A) (x'''' : type1448 A B) (h1 : term1381 A B x'''') : term1733 A B _63072 _63074 _63073 _63075.
Proof. exact (@lem5019563 A B _63072 _63074 _63073 x'''' h1 _63075). Qed.
Lemma lem5019565 {A B : Type'} (_63072 : B) (_63074 : A -> B) (_63075 : A) (_63073 : A -> Prop) : (term1733 A B _63072 _63074 _63073 _63075) = (term1690 A B _63072 _63074 _63075 _63073).
Proof. exact (eq_refl (term1733 A B _63072 _63074 _63073 _63075)). Qed.
Lemma lem5019618 {B : Type'} (_63093 : B -> Prop) (x' : type638 B) (h1 : term1530 B x') : term1734 B _63093.
Proof. exact (@lem5017309 B x' h1 _63093). Qed.
Lemma lem5019619 {B : Type'} (_63093 : B -> Prop) : (term1734 B _63093) = (term1713 B _63093).
Proof. exact (eq_refl (term1734 B _63093)). Qed.
Lemma lem5019620 {B : Type'} (_63093 : B -> Prop) (x' : type638 B) (h1 : term1530 B x') : term1713 B _63093.
Proof. exact (EQ_MP (@lem5019619 B _63093) (@lem5019618 B _63093 x' h1)). Qed.
Lemma lem5019621 {B : Type'} (_63093 : B -> Prop) (_63094 : B -> Prop) (x' : type638 B) (h1 : term1530 B x') : term1735 B _63093 _63094.
Proof. exact (@lem5019620 B _63093 x' h1 _63094). Qed.
Lemma lem5019622 {B : Type'} (_63093 : B -> Prop) (_63094 : B -> Prop) : (term1735 B _63093 _63094) = (term1711 B _63093 _63094).
Proof. exact (eq_refl (term1735 B _63093 _63094)). Qed.
Lemma lem5019623 {B : Type'} (_63093 : B -> Prop) (_63094 : B -> Prop) (x' : type638 B) (h1 : term1530 B x') : term1711 B _63093 _63094.
Proof. exact (EQ_MP (@lem5019622 B _63093 _63094) (@lem5019621 B _63093 _63094 x' h1)). Qed.
Lemma lem5019624 {B : Type'} (_63093 : B -> Prop) (_63094 : B -> Prop) (_63095 : B) (x' : type638 B) (h1 : term1530 B x') : term1736 B _63093 _63094 _63095.
Proof. exact (@lem5019623 B _63093 _63094 x' h1 _63095). Qed.
Lemma lem5019625 {B : Type'} (_63093 : B -> Prop) (_63095 : B) (_63094 : B -> Prop) : (term1736 B _63093 _63094 _63095) = (term1708 B _63093 _63095 _63094).
Proof. exact (eq_refl (term1736 B _63093 _63094 _63095)). Qed.
Lemma lem5019753 {A B : Type'} (_63138 : B) (x'''' : type1448 A B) (h1 : term1381 A B x'''') : term1730 A B _63138.
Proof. exact (@lem5018037 A B x'''' h1 _63138). Qed.
Lemma lem5019754 {A B : Type'} (_63138 : B) : (term1730 A B _63138) = (term1697 A B _63138).
Proof. exact (eq_refl (term1730 A B _63138)). Qed.
Lemma lem5019755 {A B : Type'} (_63138 : B) (x'''' : type1448 A B) (h1 : term1381 A B x'''') : term1697 A B _63138.
Proof. exact (EQ_MP (@lem5019754 A B _63138) (@lem5019753 A B _63138 x'''' h1)). Qed.
Lemma lem5019756 {A B : Type'} (_63138 : B) (_63139 : A -> Prop) (x'''' : type1448 A B) (h1 : term1381 A B x'''') : term1731 A B _63138 _63139.
Proof. exact (@lem5019755 A B _63138 x'''' h1 _63139). Qed.
Lemma lem5019757 {A B : Type'} (_63138 : B) (_63139 : A -> Prop) : (term1731 A B _63138 _63139) = (term1695 A B _63138 _63139).
Proof. exact (eq_refl (term1731 A B _63138 _63139)). Qed.
Lemma lem5019758 {A B : Type'} (_63138 : B) (_63139 : A -> Prop) (x'''' : type1448 A B) (h1 : term1381 A B x'''') : term1695 A B _63138 _63139.
Proof. exact (EQ_MP (@lem5019757 A B _63138 _63139) (@lem5019756 A B _63138 _63139 x'''' h1)). Qed.
Lemma lem5019759 {A B : Type'} (_63138 : B) (_63139 : A -> Prop) (_63140 : A -> B) (x'''' : type1448 A B) (h1 : term1381 A B x'''') : term1732 A B _63138 _63139 _63140.
Proof. exact (@lem5019758 A B _63138 _63139 x'''' h1 _63140). Qed.
Lemma lem5019760 {A B : Type'} (_63138 : B) (_63140 : A -> B) (_63139 : A -> Prop) : (term1732 A B _63138 _63139 _63140) = (term1693 A B _63138 _63140 _63139).
Proof. exact (eq_refl (term1732 A B _63138 _63139 _63140)). Qed.
Lemma lem5019761 {A B : Type'} (_63138 : B) (_63140 : A -> B) (_63139 : A -> Prop) (x'''' : type1448 A B) (h1 : term1381 A B x'''') : term1693 A B _63138 _63140 _63139.
Proof. exact (EQ_MP (@lem5019760 A B _63138 _63140 _63139) (@lem5019759 A B _63138 _63139 _63140 x'''' h1)). Qed.
Lemma lem5019762 {A B : Type'} (_63138 : B) (_63140 : A -> B) (_63139 : A -> Prop) (_63141 : A) (x'''' : type1448 A B) (h1 : term1381 A B x'''') : term1733 A B _63138 _63140 _63139 _63141.
Proof. exact (@lem5019761 A B _63138 _63140 _63139 x'''' h1 _63141). Qed.
Lemma lem5019763 {A B : Type'} (_63138 : B) (_63140 : A -> B) (_63141 : A) (_63139 : A -> Prop) : (term1733 A B _63138 _63140 _63139 _63141) = (term1690 A B _63138 _63140 _63141 _63139).
Proof. exact (eq_refl (term1733 A B _63138 _63140 _63139 _63141)). Qed.
Lemma lem5019816 {B : Type'} (_63159 : B -> Prop) (x' : type638 B) (h1 : term1530 B x') : term1734 B _63159.
Proof. exact (@lem5018303 B x' h1 _63159). Qed.
Lemma lem5019817 {B : Type'} (_63159 : B -> Prop) : (term1734 B _63159) = (term1713 B _63159).
Proof. exact (eq_refl (term1734 B _63159)). Qed.
Lemma lem5019818 {B : Type'} (_63159 : B -> Prop) (x' : type638 B) (h1 : term1530 B x') : term1713 B _63159.
Proof. exact (EQ_MP (@lem5019817 B _63159) (@lem5019816 B _63159 x' h1)). Qed.
Lemma lem5019819 {B : Type'} (_63159 : B -> Prop) (_63160 : B -> Prop) (x' : type638 B) (h1 : term1530 B x') : term1735 B _63159 _63160.
Proof. exact (@lem5019818 B _63159 x' h1 _63160). Qed.
Lemma lem5019820 {B : Type'} (_63159 : B -> Prop) (_63160 : B -> Prop) : (term1735 B _63159 _63160) = (term1711 B _63159 _63160).
Proof. exact (eq_refl (term1735 B _63159 _63160)). Qed.
Lemma lem5019821 {B : Type'} (_63159 : B -> Prop) (_63160 : B -> Prop) (x' : type638 B) (h1 : term1530 B x') : term1711 B _63159 _63160.
Proof. exact (EQ_MP (@lem5019820 B _63159 _63160) (@lem5019819 B _63159 _63160 x' h1)). Qed.
Lemma lem5019822 {B : Type'} (_63159 : B -> Prop) (_63160 : B -> Prop) (_63161 : B) (x' : type638 B) (h1 : term1530 B x') : term1736 B _63159 _63160 _63161.
Proof. exact (@lem5019821 B _63159 _63160 x' h1 _63161). Qed.
Lemma lem5019823 {B : Type'} (_63159 : B -> Prop) (_63161 : B) (_63160 : B -> Prop) : (term1736 B _63159 _63160 _63161) = (term1708 B _63159 _63161 _63160).
Proof. exact (eq_refl (term1736 B _63159 _63160 _63161)). Qed.
Lemma lem5019852 {A B : Type'} (_63171 : B) (x'''' : type1448 A B) (h1 : term1381 A B x'''') : term1730 A B _63171.
Proof. exact (@lem5018538 A B x'''' h1 _63171). Qed.
Lemma lem5019853 {A B : Type'} (_63171 : B) : (term1730 A B _63171) = (term1697 A B _63171).
Proof. exact (eq_refl (term1730 A B _63171)). Qed.
Lemma lem5019854 {A B : Type'} (_63171 : B) (x'''' : type1448 A B) (h1 : term1381 A B x'''') : term1697 A B _63171.
Proof. exact (EQ_MP (@lem5019853 A B _63171) (@lem5019852 A B _63171 x'''' h1)). Qed.
Lemma lem5019855 {A B : Type'} (_63171 : B) (_63172 : A -> Prop) (x'''' : type1448 A B) (h1 : term1381 A B x'''') : term1731 A B _63171 _63172.
Proof. exact (@lem5019854 A B _63171 x'''' h1 _63172). Qed.
Lemma lem5019856 {A B : Type'} (_63171 : B) (_63172 : A -> Prop) : (term1731 A B _63171 _63172) = (term1695 A B _63171 _63172).
Proof. exact (eq_refl (term1731 A B _63171 _63172)). Qed.
Lemma lem5019857 {A B : Type'} (_63171 : B) (_63172 : A -> Prop) (x'''' : type1448 A B) (h1 : term1381 A B x'''') : term1695 A B _63171 _63172.
Proof. exact (EQ_MP (@lem5019856 A B _63171 _63172) (@lem5019855 A B _63171 _63172 x'''' h1)). Qed.
Lemma lem5019858 {A B : Type'} (_63171 : B) (_63172 : A -> Prop) (_63173 : A -> B) (x'''' : type1448 A B) (h1 : term1381 A B x'''') : term1732 A B _63171 _63172 _63173.
Proof. exact (@lem5019857 A B _63171 _63172 x'''' h1 _63173). Qed.
Lemma lem5019859 {A B : Type'} (_63171 : B) (_63173 : A -> B) (_63172 : A -> Prop) : (term1732 A B _63171 _63172 _63173) = (term1693 A B _63171 _63173 _63172).
Proof. exact (eq_refl (term1732 A B _63171 _63172 _63173)). Qed.
Lemma lem5019860 {A B : Type'} (_63171 : B) (_63173 : A -> B) (_63172 : A -> Prop) (x'''' : type1448 A B) (h1 : term1381 A B x'''') : term1693 A B _63171 _63173 _63172.
Proof. exact (EQ_MP (@lem5019859 A B _63171 _63173 _63172) (@lem5019858 A B _63171 _63172 _63173 x'''' h1)). Qed.
Lemma lem5019861 {A B : Type'} (_63171 : B) (_63173 : A -> B) (_63172 : A -> Prop) (_63174 : A) (x'''' : type1448 A B) (h1 : term1381 A B x'''') : term1733 A B _63171 _63173 _63172 _63174.
Proof. exact (@lem5019860 A B _63171 _63173 _63172 x'''' h1 _63174). Qed.
Lemma lem5019862 {A B : Type'} (_63171 : B) (_63173 : A -> B) (_63174 : A) (_63172 : A -> Prop) : (term1733 A B _63171 _63173 _63172 _63174) = (term1690 A B _63171 _63173 _63174 _63172).
Proof. exact (eq_refl (term1733 A B _63171 _63173 _63172 _63174)). Qed.
Lemma lem5019915 {B : Type'} (_63192 : B -> Prop) (x' : type638 B) (h1 : term1530 B x') : term1734 B _63192.
Proof. exact (@lem5018804 B x' h1 _63192). Qed.
Lemma lem5019916 {B : Type'} (_63192 : B -> Prop) : (term1734 B _63192) = (term1713 B _63192).
Proof. exact (eq_refl (term1734 B _63192)). Qed.
Lemma lem5019917 {B : Type'} (_63192 : B -> Prop) (x' : type638 B) (h1 : term1530 B x') : term1713 B _63192.
Proof. exact (EQ_MP (@lem5019916 B _63192) (@lem5019915 B _63192 x' h1)). Qed.
Lemma lem5019918 {B : Type'} (_63192 : B -> Prop) (_63193 : B -> Prop) (x' : type638 B) (h1 : term1530 B x') : term1735 B _63192 _63193.
Proof. exact (@lem5019917 B _63192 x' h1 _63193). Qed.
Lemma lem5019919 {B : Type'} (_63192 : B -> Prop) (_63193 : B -> Prop) : (term1735 B _63192 _63193) = (term1711 B _63192 _63193).
Proof. exact (eq_refl (term1735 B _63192 _63193)). Qed.
Lemma lem5019920 {B : Type'} (_63192 : B -> Prop) (_63193 : B -> Prop) (x' : type638 B) (h1 : term1530 B x') : term1711 B _63192 _63193.
Proof. exact (EQ_MP (@lem5019919 B _63192 _63193) (@lem5019918 B _63192 _63193 x' h1)). Qed.
Lemma lem5019921 {B : Type'} (_63192 : B -> Prop) (_63193 : B -> Prop) (_63194 : B) (x' : type638 B) (h1 : term1530 B x') : term1736 B _63192 _63193 _63194.
Proof. exact (@lem5019920 B _63192 _63193 x' h1 _63194). Qed.
Lemma lem5019922 {B : Type'} (_63192 : B -> Prop) (_63194 : B) (_63193 : B -> Prop) : (term1736 B _63192 _63193 _63194) = (term1708 B _63192 _63194 _63193).
Proof. exact (eq_refl (term1736 B _63192 _63193 _63194)). Qed.
Lemma lem5019924 {A B : Type'} (_63195 : A) (s : A -> Prop) (f : A -> B) (h1 : term122 A B s f) : term1737 A B s f _63195.
Proof. exact (@lem5018898 A B s f h1 _63195). Qed.
Lemma lem5019925 {A B : Type'} (s : A -> Prop) (f : A -> B) (_63195 : A) : (term1737 A B s f _63195) = (term1727 A B s f _63195).
Proof. exact (eq_refl (term1737 A B s f _63195)). Qed.
Lemma lem5019926 {A B : Type'} (_63195 : A) (s : A -> Prop) (f : A -> B) (h1 : term122 A B s f) : term1727 A B s f _63195.
Proof. exact (EQ_MP (@lem5019925 A B s f _63195) (@lem5019924 A B _63195 s f h1)). Qed.
Lemma lem5019927 {A B : Type'} (_63195 : A) (_63196 : A) (s : A -> Prop) (f : A -> B) (h1 : term122 A B s f) : term1738 A B s f _63195 _63196.
Proof. exact (@lem5019926 A B _63195 s f h1 _63196). Qed.
Lemma lem5019928 {A B : Type'} (s : A -> Prop) (f : A -> B) (_63195 : A) (_63196 : A) : (term1738 A B s f _63195 _63196) = (term1724 A B s f _63195 _63196).
Proof. exact (eq_refl (term1738 A B s f _63195 _63196)). Qed.
Lemma lem5020170 {A B : Type'} (x : A) (f : A -> B) (x''''''' : A) (s : A -> Prop) (y : B) (x'''''' : B) (t : B -> Prop) (h1 : term1677 A B x f x''''''' s y x'''''' t) : term634 B x'''''' y.
Proof. exact (proj1 (@lem5015789 A B x f x''''''' s y x'''''' t h1)). Qed.
Lemma lem5020174 {B : Type'} (x'''''' : B) (y : B) (h1 : x'''''' = y) : x'''''' = y.
Proof. exact (h1). Qed.
Lemma lem5020312 {A B : Type'} (x : A) (f : A -> B) (x''''''' : A) (s : A -> Prop) (y : B) (x'''''' : B) (t : B -> Prop) (h1 : term1677 A B x f x''''''' s y x'''''' t) : term634 B x'''''' y.
Proof. exact (proj1 (@lem5015789 A B x f x''''''' s y x'''''' t h1)). Qed.
Lemma lem5020318 {A B : Type'} (x : A) (x'''''' : B) (y : B) (x''''''' : A) (s : A -> Prop) (h1 : term1672 A B x x'''''' y x''''''' s) : x'''''' = y.
Proof. exact (proj1 (@lem5015797 A B x x'''''' y x''''''' s h1)). Qed.
Lemma lem5020460 {A B : Type'} (x : A) (f : A -> B) (x''''''' : A) (s : A -> Prop) (y : B) (x'''''' : B) (t : B -> Prop) (h1 : term1677 A B x f x''''''' s y x'''''' t) : term1535 B x'''''' t.
Proof. exact (proj2 (@lem5015789 A B x f x''''''' s y x'''''' t h1)). Qed.
Lemma lem5020464 {A B : Type'} (x : A) (x'''''' : B) (f : A -> B) (x''''''' : A) (s : A -> Prop) (h1 : term1670 A B x x'''''' f x''''''' s) : x'''''' = (@I (A -> B) f x''''''').
Proof. exact (proj1 (@lem5015801 A B x x'''''' f x''''''' s h1)). Qed.
Lemma lem5020606 {A : Type'} (x : A) (x''''''' : A) (y' : A) (h1 : term637 A x x''''''' y') : y' = x.
Proof. exact (proj1 (@lem5015809 A x x''''''' y' h1)). Qed.
Lemma lem5020608 {A : Type'} (x : A) (x''''''' : A) (y' : A) (h1 : term637 A x x''''''' y') : term634 A x''''''' y'.
Proof. exact (proj2 (@lem5015809 A x x''''''' y' h1)). Qed.
Lemma lem5020674 {B : Type'} (y : B) (t : B -> Prop) (h1 : term238 B y t) : term1535 B y t.
Proof. exact (EQ_MP (@lem5014306 B y t) (@lem5008935 B y t h1)). Qed.
Lemma lem5020752 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term1663 A B x s y f x''''''' y') : y = (@I (A -> B) f y').
Proof. exact (proj1 (@lem5015815 A B x s y f x''''''' y' h1)). Qed.
Lemma lem5020820 {B : Type'} (y : B) (t : B -> Prop) (h1 : term238 B y t) : term1535 B y t.
Proof. exact (EQ_MP (@lem5014306 B y t) (@lem5008935 B y t h1)). Qed.
Lemma lem5020898 {A B : Type'} (x : A) (f : A -> B) (y : B) (x''''''' : A) (y' : A) (h1 : term1655 A B x f y x''''''' y') : (@I (A -> B) f x''''''') = y.
Proof. exact (proj1 (@lem5015825 A B x f y x''''''' y' h1)). Qed.
Lemma lem5020986 {A B : Type'} (_63195 : A) (_63196 : A) (s : A -> Prop) (f : A -> B) (h1 : term122 A B s f) : term1724 A B s f _63195 _63196.
Proof. exact (EQ_MP (@lem5019928 A B s f _63195 _63196) (@lem5019927 A B _63195 _63196 s f h1)). Qed.
Lemma lem5021048 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term1651 A B x s f x''''''' y') : term634 A x''''''' y'.
Proof. exact (proj2 (@lem5015831 A B x s f x''''''' y' h1)). Qed.
Lemma lem5021291 {B : Type'} (y : B) : (term1739 B y) = (term1739 B y).
Proof. exact (eq_refl (term1739 B y)). Qed.
Lemma lem5021292 {B : Type'} (x'''''' : B) (y : B) (h1 : x'''''' = y) : (term1740 B y x'''''') = (term1741 B y).
Proof. exact (MK_COMB (@lem5021291 B y) (@lem5020174 B x'''''' y h1)). Qed.
Lemma lem5021293 {B : Type'} (y : B) : (term1741 B y) = (term1742 B y).
Proof. exact (eq_refl (term1741 B y)). Qed.
Lemma lem5021294 {B : Type'} (y : B) (x'''''' : B) : (term1743 B y x'''''') = (term1743 B y x'''''').
Proof. exact (eq_refl (term1743 B y x'''''')). Qed.
Lemma lem5021295 {B : Type'} (x'''''' : B) (y : B) : ((term1740 B y x'''''') = (term1741 B y)) = ((term1740 B y x'''''') = (term1742 B y)).
Proof. exact (MK_COMB (@lem5021294 B y x'''''') (@lem5021293 B y)). Qed.
Lemma lem5021296 {B : Type'} (x'''''' : B) (y : B) : (term1740 B y x'''''') = (term634 B x'''''' y).
Proof. exact (eq_refl (term1740 B y x'''''')). Qed.
Lemma lem5021297 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5021298 {B : Type'} (x'''''' : B) (y : B) : (term1743 B y x'''''') = (term1744 B x'''''' y).
Proof. exact (MK_COMB (@lem5021297) (@lem5021296 B x'''''' y)). Qed.
Lemma lem5021299 {B : Type'} (y : B) : (term1742 B y) = (term1742 B y).
Proof. exact (eq_refl (term1742 B y)). Qed.
Lemma lem5021300 {B : Type'} (x'''''' : B) (y : B) : ((term1740 B y x'''''') = (term1742 B y)) = ((term634 B x'''''' y) = (term1742 B y)).
Proof. exact (MK_COMB (@lem5021298 B x'''''' y) (@lem5021299 B y)). Qed.
Lemma lem5021301 {B : Type'} (x'''''' : B) (y : B) : ((term1740 B y x'''''') = (term1741 B y)) = ((term634 B x'''''' y) = (term1742 B y)).
Proof. exact (TRANS (@lem5021295 B x'''''' y) (@lem5021300 B x'''''' y)). Qed.
Lemma lem5021302 {B : Type'} (x'''''' : B) (y : B) (h1 : x'''''' = y) : (term634 B x'''''' y) = (term1742 B y).
Proof. exact (EQ_MP (@lem5021301 B x'''''' y) (@lem5021292 B x'''''' y h1)). Qed.
Lemma lem5021303 {A B : Type'} (x : A) (f : A -> B) (x''''''' : A) (s : A -> Prop) (t : B -> Prop) (x'''''' : B) (y : B) (h1 : term1677 A B x f x''''''' s y x'''''' t) (h2 : x'''''' = y) : term1742 B y.
Proof. exact (EQ_MP (@lem5021302 B x'''''' y h2) (@lem5020170 A B x f x''''''' s y x'''''' t h1)). Qed.
Lemma lem5021639 {B : Type'} (y : B) : (term1739 B y) = (term1739 B y).
Proof. exact (eq_refl (term1739 B y)). Qed.
Lemma lem5021640 {A B : Type'} (x : A) (x'''''' : B) (y : B) (x''''''' : A) (s : A -> Prop) (h1 : term1672 A B x x'''''' y x''''''' s) : (term1740 B y x'''''') = (term1741 B y).
Proof. exact (MK_COMB (@lem5021639 B y) (@lem5020318 A B x x'''''' y x''''''' s h1)). Qed.
Lemma lem5021641 {B : Type'} (y : B) : (term1741 B y) = (term1742 B y).
Proof. exact (eq_refl (term1741 B y)). Qed.
Lemma lem5021642 {B : Type'} (y : B) (x'''''' : B) : (term1743 B y x'''''') = (term1743 B y x'''''').
Proof. exact (eq_refl (term1743 B y x'''''')). Qed.
Lemma lem5021643 {B : Type'} (x'''''' : B) (y : B) : ((term1740 B y x'''''') = (term1741 B y)) = ((term1740 B y x'''''') = (term1742 B y)).
Proof. exact (MK_COMB (@lem5021642 B y x'''''') (@lem5021641 B y)). Qed.
Lemma lem5021644 {B : Type'} (x'''''' : B) (y : B) : (term1740 B y x'''''') = (term634 B x'''''' y).
Proof. exact (eq_refl (term1740 B y x'''''')). Qed.
Lemma lem5021645 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5021646 {B : Type'} (x'''''' : B) (y : B) : (term1743 B y x'''''') = (term1744 B x'''''' y).
Proof. exact (MK_COMB (@lem5021645) (@lem5021644 B x'''''' y)). Qed.
Lemma lem5021647 {B : Type'} (y : B) : (term1742 B y) = (term1742 B y).
Proof. exact (eq_refl (term1742 B y)). Qed.
Lemma lem5021648 {B : Type'} (x'''''' : B) (y : B) : ((term1740 B y x'''''') = (term1742 B y)) = ((term634 B x'''''' y) = (term1742 B y)).
Proof. exact (MK_COMB (@lem5021646 B x'''''' y) (@lem5021647 B y)). Qed.
Lemma lem5021649 {B : Type'} (x'''''' : B) (y : B) : ((term1740 B y x'''''') = (term1741 B y)) = ((term634 B x'''''' y) = (term1742 B y)).
Proof. exact (TRANS (@lem5021643 B x'''''' y) (@lem5021648 B x'''''' y)). Qed.
Lemma lem5021650 {A B : Type'} (x : A) (x'''''' : B) (y : B) (x''''''' : A) (s : A -> Prop) (h1 : term1672 A B x x'''''' y x''''''' s) : (term634 B x'''''' y) = (term1742 B y).
Proof. exact (EQ_MP (@lem5021649 B x'''''' y) (@lem5021640 A B x x'''''' y x''''''' s h1)). Qed.
Lemma lem5022028 {A B : Type'} (x : A) (f : A -> B) (x''''''' : A) (s : A -> Prop) (y : B) (x'''''' : B) (t : B -> Prop) (h1 : term1672 A B x x'''''' y x''''''' s) (h2 : term1677 A B x f x''''''' s y x'''''' t) : term1742 B y.
Proof. exact (EQ_MP (@lem5021650 A B x x'''''' y x''''''' s h1) (@lem5020312 A B x f x''''''' s y x'''''' t h2)). Qed.
Lemma lem5022335 {A B : Type'} (_63072 : B) (_63074 : A -> B) (_63075 : A) (_63073 : A -> Prop) (x'''' : type1448 A B) (h1 : term1381 A B x'''') : term1690 A B _63072 _63074 _63075 _63073.
Proof. exact (EQ_MP (@lem5019565 A B _63072 _63074 _63075 _63073) (@lem5019564 A B _63072 _63074 _63073 _63075 x'''' h1)). Qed.
Lemma lem5022377 {B : Type'} (_63093 : B -> Prop) (_63095 : B) (_63094 : B -> Prop) (x' : type638 B) (h1 : term1530 B x') : term1708 B _63093 _63095 _63094.
Proof. exact (EQ_MP (@lem5019625 B _63093 _63095 _63094) (@lem5019624 B _63093 _63094 _63095 x' h1)). Qed.
Lemma lem5022391 {B : Type'} (t : B -> Prop) : (term1745 B t) = (term1745 B t).
Proof. exact (eq_refl (term1745 B t)). Qed.
Lemma lem5022392 {A B : Type'} (t : B -> Prop) (x : A) (x'''''' : B) (f : A -> B) (x''''''' : A) (s : A -> Prop) (h1 : term1670 A B x x'''''' f x''''''' s) : (term1746 B t x'''''') = (term1747 A B t f x''''''').
Proof. exact (MK_COMB (@lem5022391 B t) (@lem5020464 A B x x'''''' f x''''''' s h1)). Qed.
Lemma lem5022393 {A B : Type'} (f : A -> B) (x''''''' : A) (t : B -> Prop) : (term1747 A B t f x''''''') = (term1748 A B f x''''''' t).
Proof. exact (eq_refl (term1747 A B t f x''''''')). Qed.
Lemma lem5022394 {B : Type'} (t : B -> Prop) (x'''''' : B) : (term1749 B t x'''''') = (term1749 B t x'''''').
Proof. exact (eq_refl (term1749 B t x'''''')). Qed.
Lemma lem5022395 {A B : Type'} (x'''''' : B) (f : A -> B) (x''''''' : A) (t : B -> Prop) : ((term1746 B t x'''''') = (term1747 A B t f x''''''')) = ((term1746 B t x'''''') = (term1748 A B f x''''''' t)).
Proof. exact (MK_COMB (@lem5022394 B t x'''''') (@lem5022393 A B f x''''''' t)). Qed.
Lemma lem5022396 {B : Type'} (x'''''' : B) (t : B -> Prop) : (term1746 B t x'''''') = (term1535 B x'''''' t).
Proof. exact (eq_refl (term1746 B t x'''''')). Qed.
Lemma lem5022397 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5022398 {B : Type'} (x'''''' : B) (t : B -> Prop) : (term1749 B t x'''''') = (term1750 B x'''''' t).
Proof. exact (MK_COMB (@lem5022397) (@lem5022396 B x'''''' t)). Qed.
Lemma lem5022399 {A B : Type'} (f : A -> B) (x''''''' : A) (t : B -> Prop) : (term1748 A B f x''''''' t) = (term1748 A B f x''''''' t).
Proof. exact (eq_refl (term1748 A B f x''''''' t)). Qed.
Lemma lem5022400 {A B : Type'} (x'''''' : B) (f : A -> B) (x''''''' : A) (t : B -> Prop) : ((term1746 B t x'''''') = (term1748 A B f x''''''' t)) = ((term1535 B x'''''' t) = (term1748 A B f x''''''' t)).
Proof. exact (MK_COMB (@lem5022398 B x'''''' t) (@lem5022399 A B f x''''''' t)). Qed.
Lemma lem5022401 {A B : Type'} (x'''''' : B) (f : A -> B) (x''''''' : A) (t : B -> Prop) : ((term1746 B t x'''''') = (term1747 A B t f x''''''')) = ((term1535 B x'''''' t) = (term1748 A B f x''''''' t)).
Proof. exact (TRANS (@lem5022395 A B x'''''' f x''''''' t) (@lem5022400 A B x'''''' f x''''''' t)). Qed.
Lemma lem5022402 {A B : Type'} (t : B -> Prop) (x : A) (x'''''' : B) (f : A -> B) (x''''''' : A) (s : A -> Prop) (h1 : term1670 A B x x'''''' f x''''''' s) : (term1535 B x'''''' t) = (term1748 A B f x''''''' t).
Proof. exact (EQ_MP (@lem5022401 A B x'''''' f x''''''' t) (@lem5022392 A B t x x'''''' f x''''''' s h1)). Qed.
Lemma lem5022403 {A B : Type'} (x : A) (f : A -> B) (x''''''' : A) (s : A -> Prop) (y : B) (x'''''' : B) (t : B -> Prop) (h1 : term1670 A B x x'''''' f x''''''' s) (h2 : term1677 A B x f x''''''' s y x'''''' t) : term1748 A B f x''''''' t.
Proof. exact (EQ_MP (@lem5022402 A B t x x'''''' f x''''''' s h1) (@lem5020460 A B x f x''''''' s y x'''''' t h2)). Qed.
Lemma lem5022767 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term1665 A B x s y f x''''''' y') : x''''''' = x.
Proof. exact (proj1 (@lem5015805 A B x s y f x''''''' y' h1)). Qed.
Lemma lem5022768 {A : Type'} (x''''''' : A) : (term1751 A x''''''') = (term1751 A x''''''').
Proof. exact (eq_refl (term1751 A x''''''')). Qed.
Lemma lem5022769 {A : Type'} (x : A) (x''''''' : A) (y' : A) (h1 : term637 A x x''''''' y') : (term1752 A x''''''' y') = (term1752 A x''''''' x).
Proof. exact (MK_COMB (@lem5022768 A x''''''') (@lem5020606 A x x''''''' y' h1)). Qed.
Lemma lem5022770 {A : Type'} (x''''''' : A) (x : A) : (term1752 A x''''''' x) = (term634 A x''''''' x).
Proof. exact (eq_refl (term1752 A x''''''' x)). Qed.
Lemma lem5022771 {A : Type'} (x''''''' : A) (y' : A) : (term1753 A x''''''' y') = (term1753 A x''''''' y').
Proof. exact (eq_refl (term1753 A x''''''' y')). Qed.
Lemma lem5022772 {A : Type'} (y' : A) (x''''''' : A) (x : A) : ((term1752 A x''''''' y') = (term1752 A x''''''' x)) = ((term1752 A x''''''' y') = (term634 A x''''''' x)).
Proof. exact (MK_COMB (@lem5022771 A x''''''' y') (@lem5022770 A x''''''' x)). Qed.
Lemma lem5022773 {A : Type'} (x''''''' : A) (y' : A) : (term1752 A x''''''' y') = (term634 A x''''''' y').
Proof. exact (eq_refl (term1752 A x''''''' y')). Qed.
Lemma lem5022774 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5022775 {A : Type'} (x''''''' : A) (y' : A) : (term1753 A x''''''' y') = (term1744 A x''''''' y').
Proof. exact (MK_COMB (@lem5022774) (@lem5022773 A x''''''' y')). Qed.
Lemma lem5022776 {A : Type'} (x''''''' : A) (x : A) : (term634 A x''''''' x) = (term634 A x''''''' x).
Proof. exact (eq_refl (term634 A x''''''' x)). Qed.
Lemma lem5022777 {A : Type'} (y' : A) (x''''''' : A) (x : A) : ((term1752 A x''''''' y') = (term634 A x''''''' x)) = ((term634 A x''''''' y') = (term634 A x''''''' x)).
Proof. exact (MK_COMB (@lem5022775 A x''''''' y') (@lem5022776 A x''''''' x)). Qed.
Lemma lem5022778 {A : Type'} (y' : A) (x''''''' : A) (x : A) : ((term1752 A x''''''' y') = (term1752 A x''''''' x)) = ((term634 A x''''''' y') = (term634 A x''''''' x)).
Proof. exact (TRANS (@lem5022772 A y' x''''''' x) (@lem5022777 A y' x''''''' x)). Qed.
Lemma lem5022779 {A : Type'} (x : A) (x''''''' : A) (y' : A) (h1 : term637 A x x''''''' y') : (term634 A x''''''' y') = (term634 A x''''''' x).
Proof. exact (EQ_MP (@lem5022778 A y' x''''''' x) (@lem5022769 A x x''''''' y' h1)). Qed.
Lemma lem5022780 {A : Type'} (x : A) (x''''''' : A) (y' : A) (h1 : term637 A x x''''''' y') : term634 A x''''''' x.
Proof. exact (EQ_MP (@lem5022779 A x x''''''' y' h1) (@lem5020608 A x x''''''' y' h1)). Qed.
Lemma lem5023103 {A : Type'} (x : A) : (term1739 A x) = (term1739 A x).
Proof. exact (eq_refl (term1739 A x)). Qed.
Lemma lem5023104 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term1665 A B x s y f x''''''' y') : (term1740 A x x''''''') = (term1741 A x).
Proof. exact (MK_COMB (@lem5023103 A x) (@lem5022767 A B x s y f x''''''' y' h1)). Qed.
Lemma lem5023105 {A : Type'} (x : A) : (term1741 A x) = (term1742 A x).
Proof. exact (eq_refl (term1741 A x)). Qed.
Lemma lem5023106 {A : Type'} (x : A) (x''''''' : A) : (term1743 A x x''''''') = (term1743 A x x''''''').
Proof. exact (eq_refl (term1743 A x x''''''')). Qed.
Lemma lem5023107 {A : Type'} (x''''''' : A) (x : A) : ((term1740 A x x''''''') = (term1741 A x)) = ((term1740 A x x''''''') = (term1742 A x)).
Proof. exact (MK_COMB (@lem5023106 A x x''''''') (@lem5023105 A x)). Qed.
Lemma lem5023108 {A : Type'} (x''''''' : A) (x : A) : (term1740 A x x''''''') = (term634 A x''''''' x).
Proof. exact (eq_refl (term1740 A x x''''''')). Qed.
Lemma lem5023109 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5023110 {A : Type'} (x''''''' : A) (x : A) : (term1743 A x x''''''') = (term1744 A x''''''' x).
Proof. exact (MK_COMB (@lem5023109) (@lem5023108 A x''''''' x)). Qed.
Lemma lem5023111 {A : Type'} (x : A) : (term1742 A x) = (term1742 A x).
Proof. exact (eq_refl (term1742 A x)). Qed.
Lemma lem5023112 {A : Type'} (x''''''' : A) (x : A) : ((term1740 A x x''''''') = (term1742 A x)) = ((term634 A x''''''' x) = (term1742 A x)).
Proof. exact (MK_COMB (@lem5023110 A x''''''' x) (@lem5023111 A x)). Qed.
Lemma lem5023113 {A : Type'} (x''''''' : A) (x : A) : ((term1740 A x x''''''') = (term1741 A x)) = ((term634 A x''''''' x) = (term1742 A x)).
Proof. exact (TRANS (@lem5023107 A x''''''' x) (@lem5023112 A x''''''' x)). Qed.
Lemma lem5023114 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term1665 A B x s y f x''''''' y') : (term634 A x''''''' x) = (term1742 A x).
Proof. exact (EQ_MP (@lem5023113 A x''''''' x) (@lem5023104 A B x s y f x''''''' y' h1)). Qed.
Lemma lem5023115 {A B : Type'} (s : A -> Prop) (y : B) (f : A -> B) (x : A) (x''''''' : A) (y' : A) (h1 : term1665 A B x s y f x''''''' y') (h2 : term637 A x x''''''' y') : term1742 A x.
Proof. exact (EQ_MP (@lem5023114 A B x s y f x''''''' y' h1) (@lem5022780 A x x''''''' y' h2)). Qed.
Lemma lem5023298 {B : Type'} (t : B -> Prop) : (term1745 B t) = (term1745 B t).
Proof. exact (eq_refl (term1745 B t)). Qed.
Lemma lem5023299 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term1663 A B x s y f x''''''' y') : (term1746 B t y) = (term1747 A B t f y').
Proof. exact (MK_COMB (@lem5023298 B t) (@lem5020752 A B x s y f x''''''' y' h1)). Qed.
Lemma lem5023300 {A B : Type'} (f : A -> B) (y' : A) (t : B -> Prop) : (term1747 A B t f y') = (term1748 A B f y' t).
Proof. exact (eq_refl (term1747 A B t f y')). Qed.
Lemma lem5023301 {B : Type'} (t : B -> Prop) (y : B) : (term1749 B t y) = (term1749 B t y).
Proof. exact (eq_refl (term1749 B t y)). Qed.
Lemma lem5023302 {A B : Type'} (y : B) (f : A -> B) (y' : A) (t : B -> Prop) : ((term1746 B t y) = (term1747 A B t f y')) = ((term1746 B t y) = (term1748 A B f y' t)).
Proof. exact (MK_COMB (@lem5023301 B t y) (@lem5023300 A B f y' t)). Qed.
Lemma lem5023303 {B : Type'} (y : B) (t : B -> Prop) : (term1746 B t y) = (term1535 B y t).
Proof. exact (eq_refl (term1746 B t y)). Qed.
Lemma lem5023304 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5023305 {B : Type'} (y : B) (t : B -> Prop) : (term1749 B t y) = (term1750 B y t).
Proof. exact (MK_COMB (@lem5023304) (@lem5023303 B y t)). Qed.
Lemma lem5023306 {A B : Type'} (f : A -> B) (y' : A) (t : B -> Prop) : (term1748 A B f y' t) = (term1748 A B f y' t).
Proof. exact (eq_refl (term1748 A B f y' t)). Qed.
Lemma lem5023307 {A B : Type'} (y : B) (f : A -> B) (y' : A) (t : B -> Prop) : ((term1746 B t y) = (term1748 A B f y' t)) = ((term1535 B y t) = (term1748 A B f y' t)).
Proof. exact (MK_COMB (@lem5023305 B y t) (@lem5023306 A B f y' t)). Qed.
Lemma lem5023308 {A B : Type'} (y : B) (f : A -> B) (y' : A) (t : B -> Prop) : ((term1746 B t y) = (term1747 A B t f y')) = ((term1535 B y t) = (term1748 A B f y' t)).
Proof. exact (TRANS (@lem5023302 A B y f y' t) (@lem5023307 A B y f y' t)). Qed.
Lemma lem5023309 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term1663 A B x s y f x''''''' y') : (term1535 B y t) = (term1748 A B f y' t).
Proof. exact (EQ_MP (@lem5023308 A B y f y' t) (@lem5023299 A B t x s y f x''''''' y' h1)). Qed.
Lemma lem5023688 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term238 B y t) (h2 : term1663 A B x s y f x''''''' y') : term1748 A B f y' t.
Proof. exact (EQ_MP (@lem5023309 A B t x s y f x''''''' y' h2) (@lem5020674 B y t h1)). Qed.
Lemma lem5023772 {A B : Type'} (_63138 : B) (_63140 : A -> B) (_63141 : A) (_63139 : A -> Prop) (x'''' : type1448 A B) (h1 : term1381 A B x'''') : term1690 A B _63138 _63140 _63141 _63139.
Proof. exact (EQ_MP (@lem5019763 A B _63138 _63140 _63141 _63139) (@lem5019762 A B _63138 _63140 _63139 _63141 x'''' h1)). Qed.
Lemma lem5023814 {B : Type'} (_63159 : B -> Prop) (_63161 : B) (_63160 : B -> Prop) (x' : type638 B) (h1 : term1530 B x') : term1708 B _63159 _63161 _63160.
Proof. exact (EQ_MP (@lem5019823 B _63159 _63161 _63160) (@lem5019822 B _63159 _63160 _63161 x' h1)). Qed.
Lemma lem5023996 {A B : Type'} (x : A) (f : A -> B) (y : B) (x''''''' : A) (y' : A) (h1 : term1655 A B x f y x''''''' y') : y = (@I (A -> B) f x''''''').
Proof. exact (SYM (@lem5020898 A B x f y x''''''' y' h1)). Qed.
Lemma lem5024039 {B : Type'} (t : B -> Prop) : (term1745 B t) = (term1745 B t).
Proof. exact (eq_refl (term1745 B t)). Qed.
Lemma lem5024040 {A B : Type'} (t : B -> Prop) (x : A) (f : A -> B) (y : B) (x''''''' : A) (y' : A) (h1 : term1655 A B x f y x''''''' y') : (term1746 B t y) = (term1747 A B t f x''''''').
Proof. exact (MK_COMB (@lem5024039 B t) (@lem5023996 A B x f y x''''''' y' h1)). Qed.
Lemma lem5024041 {A B : Type'} (f : A -> B) (x''''''' : A) (t : B -> Prop) : (term1747 A B t f x''''''') = (term1748 A B f x''''''' t).
Proof. exact (eq_refl (term1747 A B t f x''''''')). Qed.
Lemma lem5024042 {B : Type'} (t : B -> Prop) (y : B) : (term1749 B t y) = (term1749 B t y).
Proof. exact (eq_refl (term1749 B t y)). Qed.
Lemma lem5024043 {A B : Type'} (y : B) (f : A -> B) (x''''''' : A) (t : B -> Prop) : ((term1746 B t y) = (term1747 A B t f x''''''')) = ((term1746 B t y) = (term1748 A B f x''''''' t)).
Proof. exact (MK_COMB (@lem5024042 B t y) (@lem5024041 A B f x''''''' t)). Qed.
Lemma lem5024044 {B : Type'} (y : B) (t : B -> Prop) : (term1746 B t y) = (term1535 B y t).
Proof. exact (eq_refl (term1746 B t y)). Qed.
Lemma lem5024045 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5024046 {B : Type'} (y : B) (t : B -> Prop) : (term1749 B t y) = (term1750 B y t).
Proof. exact (MK_COMB (@lem5024045) (@lem5024044 B y t)). Qed.
Lemma lem5024047 {A B : Type'} (f : A -> B) (x''''''' : A) (t : B -> Prop) : (term1748 A B f x''''''' t) = (term1748 A B f x''''''' t).
Proof. exact (eq_refl (term1748 A B f x''''''' t)). Qed.
Lemma lem5024048 {A B : Type'} (y : B) (f : A -> B) (x''''''' : A) (t : B -> Prop) : ((term1746 B t y) = (term1748 A B f x''''''' t)) = ((term1535 B y t) = (term1748 A B f x''''''' t)).
Proof. exact (MK_COMB (@lem5024046 B y t) (@lem5024047 A B f x''''''' t)). Qed.
Lemma lem5024049 {A B : Type'} (y : B) (f : A -> B) (x''''''' : A) (t : B -> Prop) : ((term1746 B t y) = (term1747 A B t f x''''''')) = ((term1535 B y t) = (term1748 A B f x''''''' t)).
Proof. exact (TRANS (@lem5024043 A B y f x''''''' t) (@lem5024048 A B y f x''''''' t)). Qed.
Lemma lem5024050 {A B : Type'} (t : B -> Prop) (x : A) (f : A -> B) (y : B) (x''''''' : A) (y' : A) (h1 : term1655 A B x f y x''''''' y') : (term1535 B y t) = (term1748 A B f x''''''' t).
Proof. exact (EQ_MP (@lem5024049 A B y f x''''''' t) (@lem5024040 A B t x f y x''''''' y' h1)). Qed.
Lemma lem5024429 {A B : Type'} (t : B -> Prop) (x : A) (f : A -> B) (y : B) (x''''''' : A) (y' : A) (h1 : term238 B y t) (h2 : term1655 A B x f y x''''''' y') : term1748 A B f x''''''' t.
Proof. exact (EQ_MP (@lem5024050 A B t x f y x''''''' y' h2) (@lem5020820 B y t h1)). Qed.
Lemma lem5024513 {A B : Type'} (_63171 : B) (_63173 : A -> B) (_63174 : A) (_63172 : A -> Prop) (x'''' : type1448 A B) (h1 : term1381 A B x'''') : term1690 A B _63171 _63173 _63174 _63172.
Proof. exact (EQ_MP (@lem5019862 A B _63171 _63173 _63174 _63172) (@lem5019861 A B _63171 _63173 _63172 _63174 x'''' h1)). Qed.
Lemma lem5024555 {B : Type'} (_63192 : B -> Prop) (_63194 : B) (_63193 : B -> Prop) (x' : type638 B) (h1 : term1530 B x') : term1708 B _63192 _63194 _63193.
Proof. exact (EQ_MP (@lem5019922 B _63192 _63194 _63193) (@lem5019921 B _63192 _63193 _63194 x' h1)). Qed.
Lemma lem5025304 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem5025305 {B : Type'} (x : B) : x = x.
Proof. exact (@lem5025304 B x). Qed.
Lemma lem5025306 {B : Type'} (y : B) : y = y.
Proof. exact (@lem5025305 B y). Qed.
Lemma lem5025307 {B : Type'} (y : B) : term1754 B y.
Proof. exact (fun h0 : term1742 B y => @lem5025306 B y). Qed.
Lemma lem5025309 (p : Prop) : (term1755 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5025310 {B : Type'} (y : B) : (term1754 B y) = (y = y).
Proof. exact (@lem5025309 (y = y)). Qed.
Lemma lem5025311 {B : Type'} (y : B) : y = y.
Proof. exact (EQ_MP (@lem5025310 B y) (@lem5025307 B y)). Qed.
Lemma lem5025314 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5025316 {B : Type'} (y : B) : (term1742 B y) = (term1756 B y).
Proof. exact (@lem5025314 (y = y)). Qed.
Lemma lem5025319 {A B : Type'} (x : A) (f : A -> B) (x''''''' : A) (s : A -> Prop) (t : B -> Prop) (x'''''' : B) (y : B) (h1 : term1677 A B x f x''''''' s y x'''''' t) (h2 : x'''''' = y) : term1756 B y.
Proof. exact (EQ_MP (@lem5025316 B y) (@lem5021303 A B x f x''''''' s t x'''''' y h1 h2)). Qed.
Lemma lem5025322 {A B : Type'} (x : A) (f : A -> B) (x''''''' : A) (s : A -> Prop) (t : B -> Prop) (x'''''' : B) (y : B) (h1 : term1677 A B x f x''''''' s y x'''''' t) (h2 : x'''''' = y) : False.
Proof. exact (@lem5025319 A B x f x''''''' s t x'''''' y h1 h2 (@lem5025311 B y)). Qed.
Lemma lem5025323 {A B : Type'} (x : A) (f : A -> B) (x''''''' : A) (s : A -> Prop) (t : B -> Prop) (x'''''' : B) (y : B) (h1 : term1677 A B x f x''''''' s y x'''''' t) (h2 : x'''''' = y) : term1757.
Proof. exact (fun h0 : ~ False => @lem5025322 A B x f x''''''' s t x'''''' y h1 h2). Qed.
Lemma lem5025325 (p : Prop) : (term1755 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5025326 : term1757 = False.
Proof. exact (@lem5025325 False). Qed.
Lemma lem5025895 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem5025896 {B : Type'} (x : B) : x = x.
Proof. exact (@lem5025895 B x). Qed.
Lemma lem5025897 {B : Type'} (y : B) : y = y.
Proof. exact (@lem5025896 B y). Qed.
Lemma lem5025898 {B : Type'} (y : B) : term1754 B y.
Proof. exact (fun h0 : term1742 B y => @lem5025897 B y). Qed.
Lemma lem5025900 (p : Prop) : (term1755 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5025901 {B : Type'} (y : B) : (term1754 B y) = (y = y).
Proof. exact (@lem5025900 (y = y)). Qed.
Lemma lem5025902 {B : Type'} (y : B) : y = y.
Proof. exact (EQ_MP (@lem5025901 B y) (@lem5025898 B y)). Qed.
Lemma lem5025905 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5025907 {B : Type'} (y : B) : (term1742 B y) = (term1756 B y).
Proof. exact (@lem5025905 (y = y)). Qed.
Lemma lem5025910 {A B : Type'} (x : A) (f : A -> B) (x''''''' : A) (s : A -> Prop) (y : B) (x'''''' : B) (t : B -> Prop) (h1 : term1672 A B x x'''''' y x''''''' s) (h2 : term1677 A B x f x''''''' s y x'''''' t) : term1756 B y.
Proof. exact (EQ_MP (@lem5025907 B y) (@lem5022028 A B x f x''''''' s y x'''''' t h1 h2)). Qed.
Lemma lem5025913 {A B : Type'} (x : A) (f : A -> B) (x''''''' : A) (s : A -> Prop) (y : B) (x'''''' : B) (t : B -> Prop) (h1 : term1672 A B x x'''''' y x''''''' s) (h2 : term1677 A B x f x''''''' s y x'''''' t) : False.
Proof. exact (@lem5025910 A B x f x''''''' s y x'''''' t h1 h2 (@lem5025902 B y)). Qed.
Lemma lem5025914 {A B : Type'} (x : A) (f : A -> B) (x''''''' : A) (s : A -> Prop) (y : B) (x'''''' : B) (t : B -> Prop) (h1 : term1672 A B x x'''''' y x''''''' s) (h2 : term1677 A B x f x''''''' s y x'''''' t) : term1757.
Proof. exact (fun h0 : ~ False => @lem5025913 A B x f x''''''' s y x'''''' t h1 h2). Qed.
Lemma lem5025916 (p : Prop) : (term1755 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5025917 : term1757 = False.
Proof. exact (@lem5025916 False). Qed.
Lemma lem5026486 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term364 A B f s t) : term1542 A B f s t.
Proof. exact (EQ_MP (@lem5014381 A B f s t) (@lem5008953 A B f s t h1)). Qed.
Lemma lem5026487 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term364 A B f s t) : term1758 A B f s t.
Proof. exact (fun h0 : term1759 A B f s t => @lem5026486 A B f s t h1). Qed.
Lemma lem5026489 (p : Prop) : (term1755 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5026490 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term1758 A B f s t) = (term1542 A B f s t).
Proof. exact (@lem5026489 (term1542 A B f s t)). Qed.
Lemma lem5026491 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term364 A B f s t) : term1542 A B f s t.
Proof. exact (EQ_MP (@lem5026490 A B f s t) (@lem5026487 A B f s t h1)). Qed.
Lemma lem5026493 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem5026494 {B : Type'} (x : B) : x = x.
Proof. exact (@lem5026493 B x). Qed.
Lemma lem5026495 {A B : Type'} (f : A -> B) (x''''''' : A) : (@I (A -> B) f x''''''') = (@I (A -> B) f x''''''').
Proof. exact (@lem5026494 B (@I (A -> B) f x''''''')). Qed.
Lemma lem5026496 {A B : Type'} (f : A -> B) (x''''''' : A) : term1760 A B f x'''''''.
Proof. exact (fun h0 : term1761 A B f x''''''' => @lem5026495 A B f x'''''''). Qed.
Lemma lem5026498 (p : Prop) : (term1755 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5026499 {A B : Type'} (f : A -> B) (x''''''' : A) : (term1760 A B f x''''''') = ((@I (A -> B) f x''''''') = (@I (A -> B) f x''''''')).
Proof. exact (@lem5026498 ((@I (A -> B) f x''''''') = (@I (A -> B) f x'''''''))). Qed.
Lemma lem5026500 {A B : Type'} (f : A -> B) (x''''''' : A) : (@I (A -> B) f x''''''') = (@I (A -> B) f x''''''').
Proof. exact (EQ_MP (@lem5026499 A B f x''''''') (@lem5026496 A B f x''''''')). Qed.
Lemma lem5026502 {A B : Type'} (x : A) (x'''''' : B) (f : A -> B) (x''''''' : A) (s : A -> Prop) (h1 : term1670 A B x x'''''' f x''''''' s) : term1534 A x''''''' s.
Proof. exact (proj2 (@lem5015801 A B x x'''''' f x''''''' s h1)). Qed.
Lemma lem5026503 {A B : Type'} (x : A) (x'''''' : B) (f : A -> B) (x''''''' : A) (s : A -> Prop) (h1 : term1670 A B x x'''''' f x''''''' s) : term1762 A x''''''' s.
Proof. exact (fun h0 : term1535 A x''''''' s => @lem5026502 A B x x'''''' f x''''''' s h1). Qed.
Lemma lem5026505 (p : Prop) : (term1755 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5026506 {A : Type'} (x''''''' : A) (s : A -> Prop) : (term1762 A x''''''' s) = (term1534 A x''''''' s).
Proof. exact (@lem5026505 (term1534 A x''''''' s)). Qed.
Lemma lem5026507 {A B : Type'} (x : A) (x'''''' : B) (f : A -> B) (x''''''' : A) (s : A -> Prop) (h1 : term1670 A B x x'''''' f x''''''' s) : term1534 A x''''''' s.
Proof. exact (EQ_MP (@lem5026506 A x''''''' s) (@lem5026503 A B x x'''''' f x''''''' s h1)). Qed.
Lemma lem5026509 (b : Prop) (a : Prop) : (a \/ b) = (term1763 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5026510 {A B : Type'} (_63075 : A) (_63072 : B) (_63074 : A -> B) (_63073 : A -> Prop) : (term1690 A B _63072 _63074 _63075 _63073) = (term1764 A B _63075 _63072 _63074 _63073).
Proof. exact (@lem5026509 (term1633 A B _63072 _63074 _63075 _63073) (term1615 A B _63072 _63074 _63073)). Qed.
Lemma lem5026512 (a : Prop) (b : Prop) : (term1765 a b) = (term1766 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5026513 {A B : Type'} (_63072 : B) (_63074 : A -> B) (_63075 : A) (_63073 : A -> Prop) : (term1767 A B _63072 _63074 _63075 _63073) = (term1768 A B _63072 _63074 _63075 _63073).
Proof. exact (@lem5026512 (term1630 A B _63072 _63074 _63075) (term1535 A _63075 _63073)). Qed.
Lemma lem5026515 (a : Prop) : (term1769 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5026516 {A B : Type'} (_63072 : B) (_63074 : A -> B) (_63075 : A) : (term1770 A B _63072 _63074 _63075) = (_63072 = (@I (A -> B) _63074 _63075)).
Proof. exact (@lem5026515 (_63072 = (@I (A -> B) _63074 _63075))). Qed.
Lemma lem5026517 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5026518 {A B : Type'} (_63072 : B) (_63074 : A -> B) (_63075 : A) : (term1771 A B _63072 _63074 _63075) = (term1660 A B _63072 _63074 _63075).
Proof. exact (MK_COMB (@lem5026517) (@lem5026516 A B _63072 _63074 _63075)). Qed.
Lemma lem5026520 (a : Prop) : (term1769 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5026521 {A : Type'} (_63075 : A) (_63073 : A -> Prop) : (term1772 A _63075 _63073) = (term1534 A _63075 _63073).
Proof. exact (@lem5026520 (term1534 A _63075 _63073)). Qed.
Lemma lem5026522 {A B : Type'} (_63072 : B) (_63074 : A -> B) (_63075 : A) (_63073 : A -> Prop) : (term1768 A B _63072 _63074 _63075 _63073) = (term1669 A B _63072 _63074 _63075 _63073).
Proof. exact (MK_COMB (@lem5026518 A B _63072 _63074 _63075) (@lem5026521 A _63075 _63073)). Qed.
Lemma lem5026523 {A B : Type'} (_63072 : B) (_63074 : A -> B) (_63075 : A) (_63073 : A -> Prop) : (term1767 A B _63072 _63074 _63075 _63073) = (term1669 A B _63072 _63074 _63075 _63073).
Proof. exact (TRANS (@lem5026513 A B _63072 _63074 _63075 _63073) (@lem5026522 A B _63072 _63074 _63075 _63073)). Qed.
Lemma lem5026524 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5026525 {A B : Type'} (_63072 : B) (_63074 : A -> B) (_63075 : A) (_63073 : A -> Prop) : (term1773 A B _63072 _63074 _63075 _63073) = (term1774 A B _63072 _63074 _63075 _63073).
Proof. exact (MK_COMB (@lem5026524) (@lem5026523 A B _63072 _63074 _63075 _63073)). Qed.
Lemma lem5026526 {A B : Type'} (_63072 : B) (_63074 : A -> B) (_63073 : A -> Prop) : (term1615 A B _63072 _63074 _63073) = (term1615 A B _63072 _63074 _63073).
Proof. exact (eq_refl (term1615 A B _63072 _63074 _63073)). Qed.
Lemma lem5026527 {A B : Type'} (_63075 : A) (_63072 : B) (_63074 : A -> B) (_63073 : A -> Prop) : (term1764 A B _63075 _63072 _63074 _63073) = (term1775 A B _63075 _63072 _63074 _63073).
Proof. exact (MK_COMB (@lem5026525 A B _63072 _63074 _63075 _63073) (@lem5026526 A B _63072 _63074 _63073)). Qed.
Lemma lem5026528 {A B : Type'} (_63075 : A) (_63072 : B) (_63074 : A -> B) (_63073 : A -> Prop) : (term1690 A B _63072 _63074 _63075 _63073) = (term1775 A B _63075 _63072 _63074 _63073).
Proof. exact (TRANS (@lem5026510 A B _63075 _63072 _63074 _63073) (@lem5026527 A B _63075 _63072 _63074 _63073)). Qed.
Lemma lem5026530 {A B : Type'} (x : A) (x'''''' : B) (f : A -> B) (x''''''' : A) (s : A -> Prop) (h1 : term1670 A B x x'''''' f x''''''' s) : term1776 A B f x''''''' s.
Proof. exact (conj (@lem5026500 A B f x''''''') (@lem5026507 A B x x'''''' f x''''''' s h1)). Qed.
Lemma lem5026532 {A B : Type'} (_63075 : A) (_63072 : B) (_63074 : A -> B) (_63073 : A -> Prop) (x'''' : type1448 A B) (h1 : term1381 A B x'''') : term1775 A B _63075 _63072 _63074 _63073.
Proof. exact (EQ_MP (@lem5026528 A B _63075 _63072 _63074 _63073) (@lem5022335 A B _63072 _63074 _63075 _63073 x'''' h1)). Qed.
Lemma lem5026533 {A B : Type'} (_63075 : A) (_63072 : B) (_63074 : A -> B) (_63073 : A -> Prop) (x'''' : type1448 A B) (h1 : term1381 A B x'''') : term1775 A B _63075 _63072 _63074 _63073.
Proof. exact (@lem5026532 A B _63075 _63072 _63074 _63073 x'''' h1). Qed.
Lemma lem5026534 {A B : Type'} (x''''''' : A) (f : A -> B) (s : A -> Prop) (x'''' : type1448 A B) (h1 : term1381 A B x'''') : term1777 A B x''''''' f s.
Proof. exact (@lem5026533 A B x''''''' (@I (A -> B) f x''''''') f s x'''' h1). Qed.
Lemma lem5026537 {A B : Type'} (x'''' : type1448 A B) (x : A) (x'''''' : B) (f : A -> B) (x''''''' : A) (s : A -> Prop) (h1 : term1381 A B x'''') (h2 : term1670 A B x x'''''' f x''''''' s) : term1778 A B x''''''' f s.
Proof. exact (@lem5026534 A B x''''''' f s x'''' h1 (@lem5026530 A B x x'''''' f x''''''' s h2)). Qed.
Lemma lem5026538 {A B : Type'} (x'''' : type1448 A B) (x : A) (x'''''' : B) (f : A -> B) (x''''''' : A) (s : A -> Prop) (h1 : term1381 A B x'''') (h2 : term1670 A B x x'''''' f x''''''' s) : term1779 A B x''''''' f s.
Proof. exact (fun h0 : term1780 A B x''''''' f s => @lem5026537 A B x'''' x x'''''' f x''''''' s h1 h2). Qed.
Lemma lem5026540 (p : Prop) : (term1755 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5026541 {A B : Type'} (x''''''' : A) (f : A -> B) (s : A -> Prop) : (term1779 A B x''''''' f s) = (term1778 A B x''''''' f s).
Proof. exact (@lem5026540 (term1778 A B x''''''' f s)). Qed.
Lemma lem5026542 {A B : Type'} (x'''' : type1448 A B) (x : A) (x'''''' : B) (f : A -> B) (x''''''' : A) (s : A -> Prop) (h1 : term1381 A B x'''') (h2 : term1670 A B x x'''''' f x''''''' s) : term1778 A B x''''''' f s.
Proof. exact (EQ_MP (@lem5026541 A B x''''''' f s) (@lem5026538 A B x'''' x x'''''' f x''''''' s h1 h2)). Qed.
Lemma lem5026548 (q : Prop) (p : Prop) (r : Prop) : (term1781 p q r) = (term1781 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5026549 {B : Type'} (_63093 : B -> Prop) (_63095 : B) (_63094 : B -> Prop) : (term1708 B _63093 _63095 _63094) = (term1782 B _63093 _63095 _63094).
Proof. exact (@lem5026548 (term1535 B _63095 _63093) (term1561 B _63093 _63094) (term1534 B _63095 _63094)). Qed.
Lemma lem5026563 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5026564 {B : Type'} (_63095 : B) (_63093 : B -> Prop) (_63094 : B -> Prop) : (term1783 B _63093 _63095 _63094) = (term1784 B _63095 _63093 _63094).
Proof. exact (@lem5026563 (term1534 B _63095 _63094) (term1561 B _63093 _63094)). Qed.
Lemma lem5026570 {B : Type'} (_63095 : B) (_63093 : B -> Prop) : (term1549 B _63095 _63093) = (term1549 B _63095 _63093).
Proof. exact (eq_refl (term1549 B _63095 _63093)). Qed.
Lemma lem5026571 {B : Type'} (_63095 : B) (_63093 : B -> Prop) (_63094 : B -> Prop) : (term1782 B _63093 _63095 _63094) = (term1785 B _63095 _63093 _63094).
Proof. exact (MK_COMB (@lem5026570 B _63095 _63093) (@lem5026564 B _63095 _63093 _63094)). Qed.
Lemma lem5026575 (q : Prop) (p : Prop) (r : Prop) : (term1781 p q r) = (term1781 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5026576 {B : Type'} (_63095 : B) (_63093 : B -> Prop) (_63094 : B -> Prop) : (term1785 B _63095 _63093 _63094) = (term1786 B _63095 _63093 _63094).
Proof. exact (@lem5026575 (term1534 B _63095 _63094) (term1535 B _63095 _63093) (term1561 B _63093 _63094)). Qed.
Lemma lem5026592 {B : Type'} (_63095 : B) (_63093 : B -> Prop) (_63094 : B -> Prop) : (term1782 B _63093 _63095 _63094) = (term1786 B _63095 _63093 _63094).
Proof. exact (TRANS (@lem5026571 B _63095 _63093 _63094) (@lem5026576 B _63095 _63093 _63094)). Qed.
Lemma lem5026593 {B : Type'} (_63095 : B) (_63093 : B -> Prop) (_63094 : B -> Prop) : (term1708 B _63093 _63095 _63094) = (term1786 B _63095 _63093 _63094).
Proof. exact (TRANS (@lem5026549 B _63093 _63095 _63094) (@lem5026592 B _63095 _63093 _63094)). Qed.
Lemma lem5026594 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5026595 {B : Type'} (_63095 : B) (_63093 : B -> Prop) (_63094 : B -> Prop) : (term1787 B _63093 _63095 _63094) = (term1788 B _63095 _63093 _63094).
Proof. exact (MK_COMB (@lem5026594) (@lem5026593 B _63095 _63093 _63094)). Qed.
Lemma lem5026609 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5026610 {B : Type'} (_63095 : B) (_63093 : B -> Prop) (_63094 : B -> Prop) : (term1789 B _63094 _63095 _63093) = (term1790 B _63095 _63093 _63094).
Proof. exact (@lem5026609 (term1535 B _63095 _63093) (term1561 B _63093 _63094)). Qed.
Lemma lem5026616 {B : Type'} (_63095 : B) (_63094 : B -> Prop) : (term1791 B _63095 _63094) = (term1791 B _63095 _63094).
Proof. exact (eq_refl (term1791 B _63095 _63094)). Qed.
Lemma lem5026617 {B : Type'} (_63095 : B) (_63093 : B -> Prop) (_63094 : B -> Prop) : (term1792 B _63094 _63095 _63093) = (term1786 B _63095 _63093 _63094).
Proof. exact (MK_COMB (@lem5026616 B _63095 _63094) (@lem5026610 B _63095 _63093 _63094)). Qed.
Lemma lem5026628 {B : Type'} (_63095 : B) (_63093 : B -> Prop) (_63094 : B -> Prop) : ((term1708 B _63093 _63095 _63094) = (term1792 B _63094 _63095 _63093)) = ((term1786 B _63095 _63093 _63094) = (term1786 B _63095 _63093 _63094)).
Proof. exact (MK_COMB (@lem5026595 B _63095 _63093 _63094) (@lem5026617 B _63095 _63093 _63094)). Qed.
Lemma lem5026630 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5026631 (x : Prop) : (x = x) = True.
Proof. exact (@lem5026630 Prop x). Qed.
Lemma lem5026632 {B : Type'} (_63095 : B) (_63093 : B -> Prop) (_63094 : B -> Prop) : ((term1786 B _63095 _63093 _63094) = (term1786 B _63095 _63093 _63094)) = True.
Proof. exact (@lem5026631 (term1786 B _63095 _63093 _63094)). Qed.
Lemma lem5026633 {B : Type'} (_63094 : B -> Prop) (_63095 : B) (_63093 : B -> Prop) : ((term1708 B _63093 _63095 _63094) = (term1792 B _63094 _63095 _63093)) = True.
Proof. exact (TRANS (@lem5026628 B _63095 _63093 _63094) (@lem5026632 B _63095 _63093 _63094)). Qed.
Lemma lem5026634 {B : Type'} (_63094 : B -> Prop) (_63095 : B) (_63093 : B -> Prop) : True = ((term1708 B _63093 _63095 _63094) = (term1792 B _63094 _63095 _63093)).
Proof. exact (SYM (@lem5026633 B _63094 _63095 _63093)). Qed.
Lemma lem5026635 {B : Type'} (_63094 : B -> Prop) (_63095 : B) (_63093 : B -> Prop) : (term1708 B _63093 _63095 _63094) = (term1792 B _63094 _63095 _63093).
Proof. exact (EQ_MP (@lem5026634 B _63094 _63095 _63093) (@lem0)). Qed.
Lemma lem5026636 {B : Type'} (_63094 : B -> Prop) (_63095 : B) (_63093 : B -> Prop) (x' : type638 B) (h1 : term1530 B x') : term1792 B _63094 _63095 _63093.
Proof. exact (EQ_MP (@lem5026635 B _63094 _63095 _63093) (@lem5022377 B _63093 _63095 _63094 x' h1)). Qed.
Lemma lem5026638 (b : Prop) (a : Prop) : (a \/ b) = (term1763 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5026639 {B : Type'} (_63093 : B -> Prop) (_63095 : B) (_63094 : B -> Prop) : (term1792 B _63094 _63095 _63093) = (term1793 B _63093 _63095 _63094).
Proof. exact (@lem5026638 (term1789 B _63094 _63095 _63093) (term1534 B _63095 _63094)). Qed.
Lemma lem5026641 (a : Prop) (b : Prop) : (term1765 a b) = (term1766 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5026642 {B : Type'} (_63094 : B -> Prop) (_63095 : B) (_63093 : B -> Prop) : (term1794 B _63094 _63095 _63093) = (term1795 B _63094 _63095 _63093).
Proof. exact (@lem5026641 (term1561 B _63093 _63094) (term1535 B _63095 _63093)). Qed.
Lemma lem5026644 (a : Prop) : (term1769 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5026645 {B : Type'} (_63093 : B -> Prop) (_63094 : B -> Prop) : (term1796 B _63093 _63094) = (term1559 B _63093 _63094).
Proof. exact (@lem5026644 (term1559 B _63093 _63094)). Qed.
Lemma lem5026646 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5026647 {B : Type'} (_63093 : B -> Prop) (_63094 : B -> Prop) : (term1797 B _63093 _63094) = (term1798 B _63093 _63094).
Proof. exact (MK_COMB (@lem5026646) (@lem5026645 B _63093 _63094)). Qed.
Lemma lem5026649 (a : Prop) : (term1769 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5026650 {B : Type'} (_63095 : B) (_63093 : B -> Prop) : (term1772 B _63095 _63093) = (term1534 B _63095 _63093).
Proof. exact (@lem5026649 (term1534 B _63095 _63093)). Qed.
Lemma lem5026651 {B : Type'} (_63094 : B -> Prop) (_63095 : B) (_63093 : B -> Prop) : (term1795 B _63094 _63095 _63093) = (term1799 B _63094 _63095 _63093).
Proof. exact (MK_COMB (@lem5026647 B _63093 _63094) (@lem5026650 B _63095 _63093)). Qed.
Lemma lem5026652 {B : Type'} (_63094 : B -> Prop) (_63095 : B) (_63093 : B -> Prop) : (term1794 B _63094 _63095 _63093) = (term1799 B _63094 _63095 _63093).
Proof. exact (TRANS (@lem5026642 B _63094 _63095 _63093) (@lem5026651 B _63094 _63095 _63093)). Qed.
Lemma lem5026653 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5026654 {B : Type'} (_63094 : B -> Prop) (_63095 : B) (_63093 : B -> Prop) : (term1800 B _63094 _63095 _63093) = (term1801 B _63094 _63095 _63093).
Proof. exact (MK_COMB (@lem5026653) (@lem5026652 B _63094 _63095 _63093)). Qed.
Lemma lem5026655 {B : Type'} (_63095 : B) (_63094 : B -> Prop) : (term1534 B _63095 _63094) = (term1534 B _63095 _63094).
Proof. exact (eq_refl (term1534 B _63095 _63094)). Qed.
Lemma lem5026656 {B : Type'} (_63093 : B -> Prop) (_63095 : B) (_63094 : B -> Prop) : (term1793 B _63093 _63095 _63094) = (term1802 B _63093 _63095 _63094).
Proof. exact (MK_COMB (@lem5026654 B _63094 _63095 _63093) (@lem5026655 B _63095 _63094)). Qed.
Lemma lem5026657 {B : Type'} (_63093 : B -> Prop) (_63095 : B) (_63094 : B -> Prop) : (term1792 B _63094 _63095 _63093) = (term1802 B _63093 _63095 _63094).
Proof. exact (TRANS (@lem5026639 B _63093 _63095 _63094) (@lem5026656 B _63093 _63095 _63094)). Qed.
Lemma lem5026659 {A B : Type'} (x'''' : type1448 A B) (x : A) (x'''''' : B) (x''''''' : A) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term1381 A B x'''') (h2 : term1670 A B x x'''''' f x''''''' s) (h3 : term364 A B f s t) : term1803 A B t x''''''' f s.
Proof. exact (conj (@lem5026491 A B f s t h3) (@lem5026542 A B x'''' x x'''''' f x''''''' s h1 h2)). Qed.
Lemma lem5026661 {B : Type'} (_63093 : B -> Prop) (_63095 : B) (_63094 : B -> Prop) (x' : type638 B) (h1 : term1530 B x') : term1802 B _63093 _63095 _63094.
Proof. exact (EQ_MP (@lem5026657 B _63093 _63095 _63094) (@lem5026636 B _63094 _63095 _63093 x' h1)). Qed.
Lemma lem5026662 {B : Type'} (_63093 : B -> Prop) (_63095 : B) (_63094 : B -> Prop) (x' : type638 B) (h1 : term1530 B x') : term1802 B _63093 _63095 _63094.
Proof. exact (@lem5026661 B _63093 _63095 _63094 x' h1). Qed.
Lemma lem5026663 {A B : Type'} (s : A -> Prop) (f : A -> B) (x''''''' : A) (t : B -> Prop) (x' : type638 B) (h1 : term1530 B x') : term1804 A B s f x''''''' t.
Proof. exact (@lem5026662 B (term1536 A B f s) (@I (A -> B) f x''''''') t x' h1). Qed.
Lemma lem5026666 {A B : Type'} (x'''' : type1448 A B) (x' : type638 B) (x : A) (x'''''' : B) (x''''''' : A) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term1381 A B x'''') (h2 : term1530 B x') (h3 : term1670 A B x x'''''' f x''''''' s) (h4 : term364 A B f s t) : term1805 A B f x''''''' t.
Proof. exact (@lem5026663 A B s f x''''''' t x' h2 (@lem5026659 A B x'''' x x'''''' x''''''' f s t h1 h3 h4)). Qed.
Lemma lem5026667 {A B : Type'} (x'''' : type1448 A B) (x' : type638 B) (x : A) (x'''''' : B) (x''''''' : A) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term1381 A B x'''') (h2 : term1530 B x') (h3 : term1670 A B x x'''''' f x''''''' s) (h4 : term364 A B f s t) : term1806 A B f x''''''' t.
Proof. exact (fun h0 : term1748 A B f x''''''' t => @lem5026666 A B x'''' x' x x'''''' x''''''' f s t h1 h2 h3 h4). Qed.
Lemma lem5026669 (p : Prop) : (term1755 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5026670 {A B : Type'} (f : A -> B) (x''''''' : A) (t : B -> Prop) : (term1806 A B f x''''''' t) = (term1805 A B f x''''''' t).
Proof. exact (@lem5026669 (term1805 A B f x''''''' t)). Qed.
Lemma lem5026671 {A B : Type'} (x'''' : type1448 A B) (x' : type638 B) (x : A) (x'''''' : B) (x''''''' : A) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term1381 A B x'''') (h2 : term1530 B x') (h3 : term1670 A B x x'''''' f x''''''' s) (h4 : term364 A B f s t) : term1805 A B f x''''''' t.
Proof. exact (EQ_MP (@lem5026670 A B f x''''''' t) (@lem5026667 A B x'''' x' x x'''''' x''''''' f s t h1 h2 h3 h4)). Qed.
Lemma lem5026674 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5026676 {A B : Type'} (f : A -> B) (x''''''' : A) (t : B -> Prop) : (term1748 A B f x''''''' t) = (term1807 A B f x''''''' t).
Proof. exact (@lem5026674 (term1805 A B f x''''''' t)). Qed.
Lemma lem5026679 {A B : Type'} (x : A) (f : A -> B) (x''''''' : A) (s : A -> Prop) (y : B) (x'''''' : B) (t : B -> Prop) (h1 : term1670 A B x x'''''' f x''''''' s) (h2 : term1677 A B x f x''''''' s y x'''''' t) : term1807 A B f x''''''' t.
Proof. exact (EQ_MP (@lem5026676 A B f x''''''' t) (@lem5022403 A B x f x''''''' s y x'''''' t h1 h2)). Qed.
Lemma lem5026682 {A B : Type'} (x'''' : type1448 A B) (x' : type638 B) (x : A) (x''''''' : A) (y : B) (x'''''' : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term1381 A B x'''') (h2 : term1530 B x') (h3 : term1670 A B x x'''''' f x''''''' s) (h4 : term1677 A B x f x''''''' s y x'''''' t) (h5 : term364 A B f s t) : False.
Proof. exact (@lem5026679 A B x f x''''''' s y x'''''' t h3 h4 (@lem5026671 A B x'''' x' x x'''''' x''''''' f s t h1 h2 h3 h5)). Qed.
Lemma lem5026683 {A B : Type'} (x'''' : type1448 A B) (x' : type638 B) (x : A) (x''''''' : A) (y : B) (x'''''' : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term1381 A B x'''') (h2 : term1530 B x') (h3 : term1670 A B x x'''''' f x''''''' s) (h4 : term1677 A B x f x''''''' s y x'''''' t) (h5 : term364 A B f s t) : term1757.
Proof. exact (fun h0 : ~ False => @lem5026682 A B x'''' x' x x''''''' y x'''''' f s t h1 h2 h3 h4 h5). Qed.
Lemma lem5026685 (p : Prop) : (term1755 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5026686 : term1757 = False.
Proof. exact (@lem5026685 False). Qed.
Lemma lem5027255 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem5027256 {A : Type'} (x : A) : x = x.
Proof. exact (@lem5027255 A x). Qed.
Lemma lem5027257 {A : Type'} (x : A) : term1754 A x.
Proof. exact (fun h0 : term1742 A x => @lem5027256 A x). Qed.
Lemma lem5027259 (p : Prop) : (term1755 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5027260 {A : Type'} (x : A) : (term1754 A x) = (x = x).
Proof. exact (@lem5027259 (x = x)). Qed.
Lemma lem5027261 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem5027260 A x) (@lem5027257 A x)). Qed.
Lemma lem5027264 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5027266 {A : Type'} (x : A) : (term1742 A x) = (term1756 A x).
Proof. exact (@lem5027264 (x = x)). Qed.
Lemma lem5027269 {A B : Type'} (s : A -> Prop) (y : B) (f : A -> B) (x : A) (x''''''' : A) (y' : A) (h1 : term1665 A B x s y f x''''''' y') (h2 : term637 A x x''''''' y') : term1756 A x.
Proof. exact (EQ_MP (@lem5027266 A x) (@lem5023115 A B s y f x x''''''' y' h1 h2)). Qed.
Lemma lem5027272 {A B : Type'} (s : A -> Prop) (y : B) (f : A -> B) (x : A) (x''''''' : A) (y' : A) (h1 : term1665 A B x s y f x''''''' y') (h2 : term637 A x x''''''' y') : False.
Proof. exact (@lem5027269 A B s y f x x''''''' y' h1 h2 (@lem5027261 A x)). Qed.
Lemma lem5027273 {A B : Type'} (s : A -> Prop) (y : B) (f : A -> B) (x : A) (x''''''' : A) (y' : A) (h1 : term1665 A B x s y f x''''''' y') (h2 : term637 A x x''''''' y') : term1757.
Proof. exact (fun h0 : ~ False => @lem5027272 A B s y f x x''''''' y' h1 h2). Qed.
Lemma lem5027275 (p : Prop) : (term1755 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5027276 : term1757 = False.
Proof. exact (@lem5027275 False). Qed.
Lemma lem5027845 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term364 A B f s t) : term1542 A B f s t.
Proof. exact (EQ_MP (@lem5014381 A B f s t) (@lem5008953 A B f s t h1)). Qed.
Lemma lem5027846 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term364 A B f s t) : term1758 A B f s t.
Proof. exact (fun h0 : term1759 A B f s t => @lem5027845 A B f s t h1). Qed.
Lemma lem5027848 (p : Prop) : (term1755 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5027849 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term1758 A B f s t) = (term1542 A B f s t).
Proof. exact (@lem5027848 (term1542 A B f s t)). Qed.
Lemma lem5027850 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term364 A B f s t) : term1542 A B f s t.
Proof. exact (EQ_MP (@lem5027849 A B f s t) (@lem5027846 A B f s t h1)). Qed.
Lemma lem5027852 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem5027853 {B : Type'} (x : B) : x = x.
Proof. exact (@lem5027852 B x). Qed.
Lemma lem5027854 {A B : Type'} (f : A -> B) (y' : A) : (@I (A -> B) f y') = (@I (A -> B) f y').
Proof. exact (@lem5027853 B (@I (A -> B) f y')). Qed.
Lemma lem5027855 {A B : Type'} (f : A -> B) (y' : A) : term1760 A B f y'.
Proof. exact (fun h0 : term1761 A B f y' => @lem5027854 A B f y'). Qed.
Lemma lem5027857 (p : Prop) : (term1755 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5027858 {A B : Type'} (f : A -> B) (y' : A) : (term1760 A B f y') = ((@I (A -> B) f y') = (@I (A -> B) f y')).
Proof. exact (@lem5027857 ((@I (A -> B) f y') = (@I (A -> B) f y'))). Qed.
Lemma lem5027859 {A B : Type'} (f : A -> B) (y' : A) : (@I (A -> B) f y') = (@I (A -> B) f y').
Proof. exact (EQ_MP (@lem5027858 A B f y') (@lem5027855 A B f y')). Qed.
Lemma lem5027861 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term1663 A B x s y f x''''''' y') : term1534 A y' s.
Proof. exact (proj1 (@lem5015813 A B x s y f x''''''' y' h1)). Qed.
Lemma lem5027862 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term1663 A B x s y f x''''''' y') : term1762 A y' s.
Proof. exact (fun h0 : term1535 A y' s => @lem5027861 A B x s y f x''''''' y' h1). Qed.
Lemma lem5027864 (p : Prop) : (term1755 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5027865 {A : Type'} (y' : A) (s : A -> Prop) : (term1762 A y' s) = (term1534 A y' s).
Proof. exact (@lem5027864 (term1534 A y' s)). Qed.
Lemma lem5027866 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term1663 A B x s y f x''''''' y') : term1534 A y' s.
Proof. exact (EQ_MP (@lem5027865 A y' s) (@lem5027862 A B x s y f x''''''' y' h1)). Qed.
Lemma lem5027868 (b : Prop) (a : Prop) : (a \/ b) = (term1763 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5027869 {A B : Type'} (_63141 : A) (_63138 : B) (_63140 : A -> B) (_63139 : A -> Prop) : (term1690 A B _63138 _63140 _63141 _63139) = (term1764 A B _63141 _63138 _63140 _63139).
Proof. exact (@lem5027868 (term1633 A B _63138 _63140 _63141 _63139) (term1615 A B _63138 _63140 _63139)). Qed.
Lemma lem5027871 (a : Prop) (b : Prop) : (term1765 a b) = (term1766 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5027872 {A B : Type'} (_63138 : B) (_63140 : A -> B) (_63141 : A) (_63139 : A -> Prop) : (term1767 A B _63138 _63140 _63141 _63139) = (term1768 A B _63138 _63140 _63141 _63139).
Proof. exact (@lem5027871 (term1630 A B _63138 _63140 _63141) (term1535 A _63141 _63139)). Qed.
Lemma lem5027874 (a : Prop) : (term1769 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5027875 {A B : Type'} (_63138 : B) (_63140 : A -> B) (_63141 : A) : (term1770 A B _63138 _63140 _63141) = (_63138 = (@I (A -> B) _63140 _63141)).
Proof. exact (@lem5027874 (_63138 = (@I (A -> B) _63140 _63141))). Qed.
Lemma lem5027876 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5027877 {A B : Type'} (_63138 : B) (_63140 : A -> B) (_63141 : A) : (term1771 A B _63138 _63140 _63141) = (term1660 A B _63138 _63140 _63141).
Proof. exact (MK_COMB (@lem5027876) (@lem5027875 A B _63138 _63140 _63141)). Qed.
Lemma lem5027879 (a : Prop) : (term1769 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5027880 {A : Type'} (_63141 : A) (_63139 : A -> Prop) : (term1772 A _63141 _63139) = (term1534 A _63141 _63139).
Proof. exact (@lem5027879 (term1534 A _63141 _63139)). Qed.
Lemma lem5027881 {A B : Type'} (_63138 : B) (_63140 : A -> B) (_63141 : A) (_63139 : A -> Prop) : (term1768 A B _63138 _63140 _63141 _63139) = (term1669 A B _63138 _63140 _63141 _63139).
Proof. exact (MK_COMB (@lem5027877 A B _63138 _63140 _63141) (@lem5027880 A _63141 _63139)). Qed.
Lemma lem5027882 {A B : Type'} (_63138 : B) (_63140 : A -> B) (_63141 : A) (_63139 : A -> Prop) : (term1767 A B _63138 _63140 _63141 _63139) = (term1669 A B _63138 _63140 _63141 _63139).
Proof. exact (TRANS (@lem5027872 A B _63138 _63140 _63141 _63139) (@lem5027881 A B _63138 _63140 _63141 _63139)). Qed.
Lemma lem5027883 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5027884 {A B : Type'} (_63138 : B) (_63140 : A -> B) (_63141 : A) (_63139 : A -> Prop) : (term1773 A B _63138 _63140 _63141 _63139) = (term1774 A B _63138 _63140 _63141 _63139).
Proof. exact (MK_COMB (@lem5027883) (@lem5027882 A B _63138 _63140 _63141 _63139)). Qed.
Lemma lem5027885 {A B : Type'} (_63138 : B) (_63140 : A -> B) (_63139 : A -> Prop) : (term1615 A B _63138 _63140 _63139) = (term1615 A B _63138 _63140 _63139).
Proof. exact (eq_refl (term1615 A B _63138 _63140 _63139)). Qed.
Lemma lem5027886 {A B : Type'} (_63141 : A) (_63138 : B) (_63140 : A -> B) (_63139 : A -> Prop) : (term1764 A B _63141 _63138 _63140 _63139) = (term1775 A B _63141 _63138 _63140 _63139).
Proof. exact (MK_COMB (@lem5027884 A B _63138 _63140 _63141 _63139) (@lem5027885 A B _63138 _63140 _63139)). Qed.
Lemma lem5027887 {A B : Type'} (_63141 : A) (_63138 : B) (_63140 : A -> B) (_63139 : A -> Prop) : (term1690 A B _63138 _63140 _63141 _63139) = (term1775 A B _63141 _63138 _63140 _63139).
Proof. exact (TRANS (@lem5027869 A B _63141 _63138 _63140 _63139) (@lem5027886 A B _63141 _63138 _63140 _63139)). Qed.
Lemma lem5027889 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term1663 A B x s y f x''''''' y') : term1776 A B f y' s.
Proof. exact (conj (@lem5027859 A B f y') (@lem5027866 A B x s y f x''''''' y' h1)). Qed.
Lemma lem5027891 {A B : Type'} (_63141 : A) (_63138 : B) (_63140 : A -> B) (_63139 : A -> Prop) (x'''' : type1448 A B) (h1 : term1381 A B x'''') : term1775 A B _63141 _63138 _63140 _63139.
Proof. exact (EQ_MP (@lem5027887 A B _63141 _63138 _63140 _63139) (@lem5023772 A B _63138 _63140 _63141 _63139 x'''' h1)). Qed.
Lemma lem5027892 {A B : Type'} (_63141 : A) (_63138 : B) (_63140 : A -> B) (_63139 : A -> Prop) (x'''' : type1448 A B) (h1 : term1381 A B x'''') : term1775 A B _63141 _63138 _63140 _63139.
Proof. exact (@lem5027891 A B _63141 _63138 _63140 _63139 x'''' h1). Qed.
Lemma lem5027893 {A B : Type'} (y' : A) (f : A -> B) (s : A -> Prop) (x'''' : type1448 A B) (h1 : term1381 A B x'''') : term1777 A B y' f s.
Proof. exact (@lem5027892 A B y' (@I (A -> B) f y') f s x'''' h1). Qed.
Lemma lem5027896 {A B : Type'} (x'''' : type1448 A B) (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term1381 A B x'''') (h2 : term1663 A B x s y f x''''''' y') : term1778 A B y' f s.
Proof. exact (@lem5027893 A B y' f s x'''' h1 (@lem5027889 A B x s y f x''''''' y' h2)). Qed.
Lemma lem5027897 {A B : Type'} (x'''' : type1448 A B) (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term1381 A B x'''') (h2 : term1663 A B x s y f x''''''' y') : term1779 A B y' f s.
Proof. exact (fun h0 : term1780 A B y' f s => @lem5027896 A B x'''' x s y f x''''''' y' h1 h2). Qed.
Lemma lem5027899 (p : Prop) : (term1755 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5027900 {A B : Type'} (y' : A) (f : A -> B) (s : A -> Prop) : (term1779 A B y' f s) = (term1778 A B y' f s).
Proof. exact (@lem5027899 (term1778 A B y' f s)). Qed.
Lemma lem5027901 {A B : Type'} (x'''' : type1448 A B) (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term1381 A B x'''') (h2 : term1663 A B x s y f x''''''' y') : term1778 A B y' f s.
Proof. exact (EQ_MP (@lem5027900 A B y' f s) (@lem5027897 A B x'''' x s y f x''''''' y' h1 h2)). Qed.
Lemma lem5027907 (q : Prop) (p : Prop) (r : Prop) : (term1781 p q r) = (term1781 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5027908 {B : Type'} (_63159 : B -> Prop) (_63161 : B) (_63160 : B -> Prop) : (term1708 B _63159 _63161 _63160) = (term1782 B _63159 _63161 _63160).
Proof. exact (@lem5027907 (term1535 B _63161 _63159) (term1561 B _63159 _63160) (term1534 B _63161 _63160)). Qed.
Lemma lem5027922 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5027923 {B : Type'} (_63161 : B) (_63159 : B -> Prop) (_63160 : B -> Prop) : (term1783 B _63159 _63161 _63160) = (term1784 B _63161 _63159 _63160).
Proof. exact (@lem5027922 (term1534 B _63161 _63160) (term1561 B _63159 _63160)). Qed.
Lemma lem5027929 {B : Type'} (_63161 : B) (_63159 : B -> Prop) : (term1549 B _63161 _63159) = (term1549 B _63161 _63159).
Proof. exact (eq_refl (term1549 B _63161 _63159)). Qed.
Lemma lem5027930 {B : Type'} (_63161 : B) (_63159 : B -> Prop) (_63160 : B -> Prop) : (term1782 B _63159 _63161 _63160) = (term1785 B _63161 _63159 _63160).
Proof. exact (MK_COMB (@lem5027929 B _63161 _63159) (@lem5027923 B _63161 _63159 _63160)). Qed.
Lemma lem5027934 (q : Prop) (p : Prop) (r : Prop) : (term1781 p q r) = (term1781 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5027935 {B : Type'} (_63161 : B) (_63159 : B -> Prop) (_63160 : B -> Prop) : (term1785 B _63161 _63159 _63160) = (term1786 B _63161 _63159 _63160).
Proof. exact (@lem5027934 (term1534 B _63161 _63160) (term1535 B _63161 _63159) (term1561 B _63159 _63160)). Qed.
Lemma lem5027951 {B : Type'} (_63161 : B) (_63159 : B -> Prop) (_63160 : B -> Prop) : (term1782 B _63159 _63161 _63160) = (term1786 B _63161 _63159 _63160).
Proof. exact (TRANS (@lem5027930 B _63161 _63159 _63160) (@lem5027935 B _63161 _63159 _63160)). Qed.
Lemma lem5027952 {B : Type'} (_63161 : B) (_63159 : B -> Prop) (_63160 : B -> Prop) : (term1708 B _63159 _63161 _63160) = (term1786 B _63161 _63159 _63160).
Proof. exact (TRANS (@lem5027908 B _63159 _63161 _63160) (@lem5027951 B _63161 _63159 _63160)). Qed.
Lemma lem5027953 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5027954 {B : Type'} (_63161 : B) (_63159 : B -> Prop) (_63160 : B -> Prop) : (term1787 B _63159 _63161 _63160) = (term1788 B _63161 _63159 _63160).
Proof. exact (MK_COMB (@lem5027953) (@lem5027952 B _63161 _63159 _63160)). Qed.
Lemma lem5027968 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5027969 {B : Type'} (_63161 : B) (_63159 : B -> Prop) (_63160 : B -> Prop) : (term1789 B _63160 _63161 _63159) = (term1790 B _63161 _63159 _63160).
Proof. exact (@lem5027968 (term1535 B _63161 _63159) (term1561 B _63159 _63160)). Qed.
Lemma lem5027975 {B : Type'} (_63161 : B) (_63160 : B -> Prop) : (term1791 B _63161 _63160) = (term1791 B _63161 _63160).
Proof. exact (eq_refl (term1791 B _63161 _63160)). Qed.
Lemma lem5027976 {B : Type'} (_63161 : B) (_63159 : B -> Prop) (_63160 : B -> Prop) : (term1792 B _63160 _63161 _63159) = (term1786 B _63161 _63159 _63160).
Proof. exact (MK_COMB (@lem5027975 B _63161 _63160) (@lem5027969 B _63161 _63159 _63160)). Qed.
Lemma lem5027987 {B : Type'} (_63161 : B) (_63159 : B -> Prop) (_63160 : B -> Prop) : ((term1708 B _63159 _63161 _63160) = (term1792 B _63160 _63161 _63159)) = ((term1786 B _63161 _63159 _63160) = (term1786 B _63161 _63159 _63160)).
Proof. exact (MK_COMB (@lem5027954 B _63161 _63159 _63160) (@lem5027976 B _63161 _63159 _63160)). Qed.
Lemma lem5027989 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5027990 (x : Prop) : (x = x) = True.
Proof. exact (@lem5027989 Prop x). Qed.
Lemma lem5027991 {B : Type'} (_63161 : B) (_63159 : B -> Prop) (_63160 : B -> Prop) : ((term1786 B _63161 _63159 _63160) = (term1786 B _63161 _63159 _63160)) = True.
Proof. exact (@lem5027990 (term1786 B _63161 _63159 _63160)). Qed.
Lemma lem5027992 {B : Type'} (_63160 : B -> Prop) (_63161 : B) (_63159 : B -> Prop) : ((term1708 B _63159 _63161 _63160) = (term1792 B _63160 _63161 _63159)) = True.
Proof. exact (TRANS (@lem5027987 B _63161 _63159 _63160) (@lem5027991 B _63161 _63159 _63160)). Qed.
Lemma lem5027993 {B : Type'} (_63160 : B -> Prop) (_63161 : B) (_63159 : B -> Prop) : True = ((term1708 B _63159 _63161 _63160) = (term1792 B _63160 _63161 _63159)).
Proof. exact (SYM (@lem5027992 B _63160 _63161 _63159)). Qed.
Lemma lem5027994 {B : Type'} (_63160 : B -> Prop) (_63161 : B) (_63159 : B -> Prop) : (term1708 B _63159 _63161 _63160) = (term1792 B _63160 _63161 _63159).
Proof. exact (EQ_MP (@lem5027993 B _63160 _63161 _63159) (@lem0)). Qed.
Lemma lem5027995 {B : Type'} (_63160 : B -> Prop) (_63161 : B) (_63159 : B -> Prop) (x' : type638 B) (h1 : term1530 B x') : term1792 B _63160 _63161 _63159.
Proof. exact (EQ_MP (@lem5027994 B _63160 _63161 _63159) (@lem5023814 B _63159 _63161 _63160 x' h1)). Qed.
Lemma lem5027997 (b : Prop) (a : Prop) : (a \/ b) = (term1763 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5027998 {B : Type'} (_63159 : B -> Prop) (_63161 : B) (_63160 : B -> Prop) : (term1792 B _63160 _63161 _63159) = (term1793 B _63159 _63161 _63160).
Proof. exact (@lem5027997 (term1789 B _63160 _63161 _63159) (term1534 B _63161 _63160)). Qed.
Lemma lem5028000 (a : Prop) (b : Prop) : (term1765 a b) = (term1766 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5028001 {B : Type'} (_63160 : B -> Prop) (_63161 : B) (_63159 : B -> Prop) : (term1794 B _63160 _63161 _63159) = (term1795 B _63160 _63161 _63159).
Proof. exact (@lem5028000 (term1561 B _63159 _63160) (term1535 B _63161 _63159)). Qed.
Lemma lem5028003 (a : Prop) : (term1769 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5028004 {B : Type'} (_63159 : B -> Prop) (_63160 : B -> Prop) : (term1796 B _63159 _63160) = (term1559 B _63159 _63160).
Proof. exact (@lem5028003 (term1559 B _63159 _63160)). Qed.
Lemma lem5028005 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5028006 {B : Type'} (_63159 : B -> Prop) (_63160 : B -> Prop) : (term1797 B _63159 _63160) = (term1798 B _63159 _63160).
Proof. exact (MK_COMB (@lem5028005) (@lem5028004 B _63159 _63160)). Qed.
Lemma lem5028008 (a : Prop) : (term1769 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5028009 {B : Type'} (_63161 : B) (_63159 : B -> Prop) : (term1772 B _63161 _63159) = (term1534 B _63161 _63159).
Proof. exact (@lem5028008 (term1534 B _63161 _63159)). Qed.
Lemma lem5028010 {B : Type'} (_63160 : B -> Prop) (_63161 : B) (_63159 : B -> Prop) : (term1795 B _63160 _63161 _63159) = (term1799 B _63160 _63161 _63159).
Proof. exact (MK_COMB (@lem5028006 B _63159 _63160) (@lem5028009 B _63161 _63159)). Qed.
Lemma lem5028011 {B : Type'} (_63160 : B -> Prop) (_63161 : B) (_63159 : B -> Prop) : (term1794 B _63160 _63161 _63159) = (term1799 B _63160 _63161 _63159).
Proof. exact (TRANS (@lem5028001 B _63160 _63161 _63159) (@lem5028010 B _63160 _63161 _63159)). Qed.
Lemma lem5028012 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5028013 {B : Type'} (_63160 : B -> Prop) (_63161 : B) (_63159 : B -> Prop) : (term1800 B _63160 _63161 _63159) = (term1801 B _63160 _63161 _63159).
Proof. exact (MK_COMB (@lem5028012) (@lem5028011 B _63160 _63161 _63159)). Qed.
Lemma lem5028014 {B : Type'} (_63161 : B) (_63160 : B -> Prop) : (term1534 B _63161 _63160) = (term1534 B _63161 _63160).
Proof. exact (eq_refl (term1534 B _63161 _63160)). Qed.
Lemma lem5028015 {B : Type'} (_63159 : B -> Prop) (_63161 : B) (_63160 : B -> Prop) : (term1793 B _63159 _63161 _63160) = (term1802 B _63159 _63161 _63160).
Proof. exact (MK_COMB (@lem5028013 B _63160 _63161 _63159) (@lem5028014 B _63161 _63160)). Qed.
Lemma lem5028016 {B : Type'} (_63159 : B -> Prop) (_63161 : B) (_63160 : B -> Prop) : (term1792 B _63160 _63161 _63159) = (term1802 B _63159 _63161 _63160).
Proof. exact (TRANS (@lem5027998 B _63159 _63161 _63160) (@lem5028015 B _63159 _63161 _63160)). Qed.
Lemma lem5028018 {A B : Type'} (x'''' : type1448 A B) (x : A) (y : B) (x''''''' : A) (y' : A) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term1381 A B x'''') (h2 : term1663 A B x s y f x''''''' y') (h3 : term364 A B f s t) : term1803 A B t y' f s.
Proof. exact (conj (@lem5027850 A B f s t h3) (@lem5027901 A B x'''' x s y f x''''''' y' h1 h2)). Qed.
Lemma lem5028020 {B : Type'} (_63159 : B -> Prop) (_63161 : B) (_63160 : B -> Prop) (x' : type638 B) (h1 : term1530 B x') : term1802 B _63159 _63161 _63160.
Proof. exact (EQ_MP (@lem5028016 B _63159 _63161 _63160) (@lem5027995 B _63160 _63161 _63159 x' h1)). Qed.
Lemma lem5028021 {B : Type'} (_63159 : B -> Prop) (_63161 : B) (_63160 : B -> Prop) (x' : type638 B) (h1 : term1530 B x') : term1802 B _63159 _63161 _63160.
Proof. exact (@lem5028020 B _63159 _63161 _63160 x' h1). Qed.
Lemma lem5028022 {A B : Type'} (s : A -> Prop) (f : A -> B) (y' : A) (t : B -> Prop) (x' : type638 B) (h1 : term1530 B x') : term1804 A B s f y' t.
Proof. exact (@lem5028021 B (term1536 A B f s) (@I (A -> B) f y') t x' h1). Qed.
Lemma lem5028025 {A B : Type'} (x'''' : type1448 A B) (x' : type638 B) (x : A) (y : B) (x''''''' : A) (y' : A) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term1381 A B x'''') (h2 : term1530 B x') (h3 : term1663 A B x s y f x''''''' y') (h4 : term364 A B f s t) : term1805 A B f y' t.
Proof. exact (@lem5028022 A B s f y' t x' h2 (@lem5028018 A B x'''' x y x''''''' y' f s t h1 h3 h4)). Qed.
Lemma lem5028026 {A B : Type'} (x'''' : type1448 A B) (x' : type638 B) (x : A) (y : B) (x''''''' : A) (y' : A) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term1381 A B x'''') (h2 : term1530 B x') (h3 : term1663 A B x s y f x''''''' y') (h4 : term364 A B f s t) : term1806 A B f y' t.
Proof. exact (fun h0 : term1748 A B f y' t => @lem5028025 A B x'''' x' x y x''''''' y' f s t h1 h2 h3 h4). Qed.
Lemma lem5028028 (p : Prop) : (term1755 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5028029 {A B : Type'} (f : A -> B) (y' : A) (t : B -> Prop) : (term1806 A B f y' t) = (term1805 A B f y' t).
Proof. exact (@lem5028028 (term1805 A B f y' t)). Qed.
Lemma lem5028030 {A B : Type'} (x'''' : type1448 A B) (x' : type638 B) (x : A) (y : B) (x''''''' : A) (y' : A) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term1381 A B x'''') (h2 : term1530 B x') (h3 : term1663 A B x s y f x''''''' y') (h4 : term364 A B f s t) : term1805 A B f y' t.
Proof. exact (EQ_MP (@lem5028029 A B f y' t) (@lem5028026 A B x'''' x' x y x''''''' y' f s t h1 h2 h3 h4)). Qed.
Lemma lem5028033 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5028035 {A B : Type'} (f : A -> B) (y' : A) (t : B -> Prop) : (term1748 A B f y' t) = (term1807 A B f y' t).
Proof. exact (@lem5028033 (term1805 A B f y' t)). Qed.
Lemma lem5028038 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (y : B) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term238 B y t) (h2 : term1663 A B x s y f x''''''' y') : term1807 A B f y' t.
Proof. exact (EQ_MP (@lem5028035 A B f y' t) (@lem5023688 A B t x s y f x''''''' y' h1 h2)). Qed.
Lemma lem5028041 {A B : Type'} (x'''' : type1448 A B) (x' : type638 B) (x : A) (y : B) (x''''''' : A) (y' : A) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term238 B y t) (h2 : term1381 A B x'''') (h3 : term1530 B x') (h4 : term1663 A B x s y f x''''''' y') (h5 : term364 A B f s t) : False.
Proof. exact (@lem5028038 A B t x s y f x''''''' y' h1 h4 (@lem5028030 A B x'''' x' x y x''''''' y' f s t h2 h3 h4 h5)). Qed.
Lemma lem5028042 {A B : Type'} (x'''' : type1448 A B) (x' : type638 B) (x : A) (y : B) (x''''''' : A) (y' : A) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term238 B y t) (h2 : term1381 A B x'''') (h3 : term1530 B x') (h4 : term1663 A B x s y f x''''''' y') (h5 : term364 A B f s t) : term1757.
Proof. exact (fun h0 : ~ False => @lem5028041 A B x'''' x' x y x''''''' y' f s t h1 h2 h3 h4 h5). Qed.
Lemma lem5028044 (p : Prop) : (term1755 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5028045 : term1757 = False.
Proof. exact (@lem5028044 False). Qed.
Lemma lem5028614 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term364 A B f s t) : term1542 A B f s t.
Proof. exact (EQ_MP (@lem5014381 A B f s t) (@lem5008953 A B f s t h1)). Qed.
Lemma lem5028615 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term364 A B f s t) : term1758 A B f s t.
Proof. exact (fun h0 : term1759 A B f s t => @lem5028614 A B f s t h1). Qed.
Lemma lem5028617 (p : Prop) : (term1755 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5028618 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term1758 A B f s t) = (term1542 A B f s t).
Proof. exact (@lem5028617 (term1542 A B f s t)). Qed.
Lemma lem5028619 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term364 A B f s t) : term1542 A B f s t.
Proof. exact (EQ_MP (@lem5028618 A B f s t) (@lem5028615 A B f s t h1)). Qed.
Lemma lem5028621 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem5028622 {B : Type'} (x : B) : x = x.
Proof. exact (@lem5028621 B x). Qed.
Lemma lem5028623 {A B : Type'} (f : A -> B) (x''''''' : A) : (@I (A -> B) f x''''''') = (@I (A -> B) f x''''''').
Proof. exact (@lem5028622 B (@I (A -> B) f x''''''')). Qed.
Lemma lem5028624 {A B : Type'} (f : A -> B) (x''''''' : A) : term1760 A B f x'''''''.
Proof. exact (fun h0 : term1761 A B f x''''''' => @lem5028623 A B f x'''''''). Qed.
Lemma lem5028626 (p : Prop) : (term1755 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5028627 {A B : Type'} (f : A -> B) (x''''''' : A) : (term1760 A B f x''''''') = ((@I (A -> B) f x''''''') = (@I (A -> B) f x''''''')).
Proof. exact (@lem5028626 ((@I (A -> B) f x''''''') = (@I (A -> B) f x'''''''))). Qed.
Lemma lem5028628 {A B : Type'} (f : A -> B) (x''''''' : A) : (@I (A -> B) f x''''''') = (@I (A -> B) f x''''''').
Proof. exact (EQ_MP (@lem5028627 A B f x''''''') (@lem5028624 A B f x''''''')). Qed.
Lemma lem5028630 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term1659 A B y x s f x''''''' y') : term1534 A x''''''' s.
Proof. exact (proj1 (@lem5015819 A B y x s f x''''''' y' h1)). Qed.
Lemma lem5028631 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term1659 A B y x s f x''''''' y') : term1762 A x''''''' s.
Proof. exact (fun h0 : term1535 A x''''''' s => @lem5028630 A B y x s f x''''''' y' h1). Qed.
Lemma lem5028633 (p : Prop) : (term1755 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5028634 {A : Type'} (x''''''' : A) (s : A -> Prop) : (term1762 A x''''''' s) = (term1534 A x''''''' s).
Proof. exact (@lem5028633 (term1534 A x''''''' s)). Qed.
Lemma lem5028635 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term1659 A B y x s f x''''''' y') : term1534 A x''''''' s.
Proof. exact (EQ_MP (@lem5028634 A x''''''' s) (@lem5028631 A B y x s f x''''''' y' h1)). Qed.
Lemma lem5028637 (b : Prop) (a : Prop) : (a \/ b) = (term1763 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5028638 {A B : Type'} (_63174 : A) (_63171 : B) (_63173 : A -> B) (_63172 : A -> Prop) : (term1690 A B _63171 _63173 _63174 _63172) = (term1764 A B _63174 _63171 _63173 _63172).
Proof. exact (@lem5028637 (term1633 A B _63171 _63173 _63174 _63172) (term1615 A B _63171 _63173 _63172)). Qed.
Lemma lem5028640 (a : Prop) (b : Prop) : (term1765 a b) = (term1766 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5028641 {A B : Type'} (_63171 : B) (_63173 : A -> B) (_63174 : A) (_63172 : A -> Prop) : (term1767 A B _63171 _63173 _63174 _63172) = (term1768 A B _63171 _63173 _63174 _63172).
Proof. exact (@lem5028640 (term1630 A B _63171 _63173 _63174) (term1535 A _63174 _63172)). Qed.
Lemma lem5028643 (a : Prop) : (term1769 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5028644 {A B : Type'} (_63171 : B) (_63173 : A -> B) (_63174 : A) : (term1770 A B _63171 _63173 _63174) = (_63171 = (@I (A -> B) _63173 _63174)).
Proof. exact (@lem5028643 (_63171 = (@I (A -> B) _63173 _63174))). Qed.
Lemma lem5028645 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5028646 {A B : Type'} (_63171 : B) (_63173 : A -> B) (_63174 : A) : (term1771 A B _63171 _63173 _63174) = (term1660 A B _63171 _63173 _63174).
Proof. exact (MK_COMB (@lem5028645) (@lem5028644 A B _63171 _63173 _63174)). Qed.
Lemma lem5028648 (a : Prop) : (term1769 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5028649 {A : Type'} (_63174 : A) (_63172 : A -> Prop) : (term1772 A _63174 _63172) = (term1534 A _63174 _63172).
Proof. exact (@lem5028648 (term1534 A _63174 _63172)). Qed.
Lemma lem5028650 {A B : Type'} (_63171 : B) (_63173 : A -> B) (_63174 : A) (_63172 : A -> Prop) : (term1768 A B _63171 _63173 _63174 _63172) = (term1669 A B _63171 _63173 _63174 _63172).
Proof. exact (MK_COMB (@lem5028646 A B _63171 _63173 _63174) (@lem5028649 A _63174 _63172)). Qed.
Lemma lem5028651 {A B : Type'} (_63171 : B) (_63173 : A -> B) (_63174 : A) (_63172 : A -> Prop) : (term1767 A B _63171 _63173 _63174 _63172) = (term1669 A B _63171 _63173 _63174 _63172).
Proof. exact (TRANS (@lem5028641 A B _63171 _63173 _63174 _63172) (@lem5028650 A B _63171 _63173 _63174 _63172)). Qed.
Lemma lem5028652 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5028653 {A B : Type'} (_63171 : B) (_63173 : A -> B) (_63174 : A) (_63172 : A -> Prop) : (term1773 A B _63171 _63173 _63174 _63172) = (term1774 A B _63171 _63173 _63174 _63172).
Proof. exact (MK_COMB (@lem5028652) (@lem5028651 A B _63171 _63173 _63174 _63172)). Qed.
Lemma lem5028654 {A B : Type'} (_63171 : B) (_63173 : A -> B) (_63172 : A -> Prop) : (term1615 A B _63171 _63173 _63172) = (term1615 A B _63171 _63173 _63172).
Proof. exact (eq_refl (term1615 A B _63171 _63173 _63172)). Qed.
Lemma lem5028655 {A B : Type'} (_63174 : A) (_63171 : B) (_63173 : A -> B) (_63172 : A -> Prop) : (term1764 A B _63174 _63171 _63173 _63172) = (term1775 A B _63174 _63171 _63173 _63172).
Proof. exact (MK_COMB (@lem5028653 A B _63171 _63173 _63174 _63172) (@lem5028654 A B _63171 _63173 _63172)). Qed.
Lemma lem5028656 {A B : Type'} (_63174 : A) (_63171 : B) (_63173 : A -> B) (_63172 : A -> Prop) : (term1690 A B _63171 _63173 _63174 _63172) = (term1775 A B _63174 _63171 _63173 _63172).
Proof. exact (TRANS (@lem5028638 A B _63174 _63171 _63173 _63172) (@lem5028655 A B _63174 _63171 _63173 _63172)). Qed.
Lemma lem5028658 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term1659 A B y x s f x''''''' y') : term1776 A B f x''''''' s.
Proof. exact (conj (@lem5028628 A B f x''''''') (@lem5028635 A B y x s f x''''''' y' h1)). Qed.
Lemma lem5028660 {A B : Type'} (_63174 : A) (_63171 : B) (_63173 : A -> B) (_63172 : A -> Prop) (x'''' : type1448 A B) (h1 : term1381 A B x'''') : term1775 A B _63174 _63171 _63173 _63172.
Proof. exact (EQ_MP (@lem5028656 A B _63174 _63171 _63173 _63172) (@lem5024513 A B _63171 _63173 _63174 _63172 x'''' h1)). Qed.
Lemma lem5028661 {A B : Type'} (_63174 : A) (_63171 : B) (_63173 : A -> B) (_63172 : A -> Prop) (x'''' : type1448 A B) (h1 : term1381 A B x'''') : term1775 A B _63174 _63171 _63173 _63172.
Proof. exact (@lem5028660 A B _63174 _63171 _63173 _63172 x'''' h1). Qed.
Lemma lem5028662 {A B : Type'} (x''''''' : A) (f : A -> B) (s : A -> Prop) (x'''' : type1448 A B) (h1 : term1381 A B x'''') : term1777 A B x''''''' f s.
Proof. exact (@lem5028661 A B x''''''' (@I (A -> B) f x''''''') f s x'''' h1). Qed.
Lemma lem5028665 {A B : Type'} (x'''' : type1448 A B) (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term1381 A B x'''') (h2 : term1659 A B y x s f x''''''' y') : term1778 A B x''''''' f s.
Proof. exact (@lem5028662 A B x''''''' f s x'''' h1 (@lem5028658 A B y x s f x''''''' y' h2)). Qed.
Lemma lem5028666 {A B : Type'} (x'''' : type1448 A B) (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term1381 A B x'''') (h2 : term1659 A B y x s f x''''''' y') : term1779 A B x''''''' f s.
Proof. exact (fun h0 : term1780 A B x''''''' f s => @lem5028665 A B x'''' y x s f x''''''' y' h1 h2). Qed.
Lemma lem5028668 (p : Prop) : (term1755 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5028669 {A B : Type'} (x''''''' : A) (f : A -> B) (s : A -> Prop) : (term1779 A B x''''''' f s) = (term1778 A B x''''''' f s).
Proof. exact (@lem5028668 (term1778 A B x''''''' f s)). Qed.
Lemma lem5028670 {A B : Type'} (x'''' : type1448 A B) (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term1381 A B x'''') (h2 : term1659 A B y x s f x''''''' y') : term1778 A B x''''''' f s.
Proof. exact (EQ_MP (@lem5028669 A B x''''''' f s) (@lem5028666 A B x'''' y x s f x''''''' y' h1 h2)). Qed.
Lemma lem5028676 (q : Prop) (p : Prop) (r : Prop) : (term1781 p q r) = (term1781 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5028677 {B : Type'} (_63192 : B -> Prop) (_63194 : B) (_63193 : B -> Prop) : (term1708 B _63192 _63194 _63193) = (term1782 B _63192 _63194 _63193).
Proof. exact (@lem5028676 (term1535 B _63194 _63192) (term1561 B _63192 _63193) (term1534 B _63194 _63193)). Qed.
Lemma lem5028691 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5028692 {B : Type'} (_63194 : B) (_63192 : B -> Prop) (_63193 : B -> Prop) : (term1783 B _63192 _63194 _63193) = (term1784 B _63194 _63192 _63193).
Proof. exact (@lem5028691 (term1534 B _63194 _63193) (term1561 B _63192 _63193)). Qed.
Lemma lem5028698 {B : Type'} (_63194 : B) (_63192 : B -> Prop) : (term1549 B _63194 _63192) = (term1549 B _63194 _63192).
Proof. exact (eq_refl (term1549 B _63194 _63192)). Qed.
Lemma lem5028699 {B : Type'} (_63194 : B) (_63192 : B -> Prop) (_63193 : B -> Prop) : (term1782 B _63192 _63194 _63193) = (term1785 B _63194 _63192 _63193).
Proof. exact (MK_COMB (@lem5028698 B _63194 _63192) (@lem5028692 B _63194 _63192 _63193)). Qed.
Lemma lem5028703 (q : Prop) (p : Prop) (r : Prop) : (term1781 p q r) = (term1781 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5028704 {B : Type'} (_63194 : B) (_63192 : B -> Prop) (_63193 : B -> Prop) : (term1785 B _63194 _63192 _63193) = (term1786 B _63194 _63192 _63193).
Proof. exact (@lem5028703 (term1534 B _63194 _63193) (term1535 B _63194 _63192) (term1561 B _63192 _63193)). Qed.
Lemma lem5028720 {B : Type'} (_63194 : B) (_63192 : B -> Prop) (_63193 : B -> Prop) : (term1782 B _63192 _63194 _63193) = (term1786 B _63194 _63192 _63193).
Proof. exact (TRANS (@lem5028699 B _63194 _63192 _63193) (@lem5028704 B _63194 _63192 _63193)). Qed.
Lemma lem5028721 {B : Type'} (_63194 : B) (_63192 : B -> Prop) (_63193 : B -> Prop) : (term1708 B _63192 _63194 _63193) = (term1786 B _63194 _63192 _63193).
Proof. exact (TRANS (@lem5028677 B _63192 _63194 _63193) (@lem5028720 B _63194 _63192 _63193)). Qed.
Lemma lem5028722 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5028723 {B : Type'} (_63194 : B) (_63192 : B -> Prop) (_63193 : B -> Prop) : (term1787 B _63192 _63194 _63193) = (term1788 B _63194 _63192 _63193).
Proof. exact (MK_COMB (@lem5028722) (@lem5028721 B _63194 _63192 _63193)). Qed.
Lemma lem5028737 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5028738 {B : Type'} (_63194 : B) (_63192 : B -> Prop) (_63193 : B -> Prop) : (term1789 B _63193 _63194 _63192) = (term1790 B _63194 _63192 _63193).
Proof. exact (@lem5028737 (term1535 B _63194 _63192) (term1561 B _63192 _63193)). Qed.
Lemma lem5028744 {B : Type'} (_63194 : B) (_63193 : B -> Prop) : (term1791 B _63194 _63193) = (term1791 B _63194 _63193).
Proof. exact (eq_refl (term1791 B _63194 _63193)). Qed.
Lemma lem5028745 {B : Type'} (_63194 : B) (_63192 : B -> Prop) (_63193 : B -> Prop) : (term1792 B _63193 _63194 _63192) = (term1786 B _63194 _63192 _63193).
Proof. exact (MK_COMB (@lem5028744 B _63194 _63193) (@lem5028738 B _63194 _63192 _63193)). Qed.
Lemma lem5028756 {B : Type'} (_63194 : B) (_63192 : B -> Prop) (_63193 : B -> Prop) : ((term1708 B _63192 _63194 _63193) = (term1792 B _63193 _63194 _63192)) = ((term1786 B _63194 _63192 _63193) = (term1786 B _63194 _63192 _63193)).
Proof. exact (MK_COMB (@lem5028723 B _63194 _63192 _63193) (@lem5028745 B _63194 _63192 _63193)). Qed.
Lemma lem5028758 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5028759 (x : Prop) : (x = x) = True.
Proof. exact (@lem5028758 Prop x). Qed.
Lemma lem5028760 {B : Type'} (_63194 : B) (_63192 : B -> Prop) (_63193 : B -> Prop) : ((term1786 B _63194 _63192 _63193) = (term1786 B _63194 _63192 _63193)) = True.
Proof. exact (@lem5028759 (term1786 B _63194 _63192 _63193)). Qed.
Lemma lem5028761 {B : Type'} (_63193 : B -> Prop) (_63194 : B) (_63192 : B -> Prop) : ((term1708 B _63192 _63194 _63193) = (term1792 B _63193 _63194 _63192)) = True.
Proof. exact (TRANS (@lem5028756 B _63194 _63192 _63193) (@lem5028760 B _63194 _63192 _63193)). Qed.
Lemma lem5028762 {B : Type'} (_63193 : B -> Prop) (_63194 : B) (_63192 : B -> Prop) : True = ((term1708 B _63192 _63194 _63193) = (term1792 B _63193 _63194 _63192)).
Proof. exact (SYM (@lem5028761 B _63193 _63194 _63192)). Qed.
Lemma lem5028763 {B : Type'} (_63193 : B -> Prop) (_63194 : B) (_63192 : B -> Prop) : (term1708 B _63192 _63194 _63193) = (term1792 B _63193 _63194 _63192).
Proof. exact (EQ_MP (@lem5028762 B _63193 _63194 _63192) (@lem0)). Qed.
Lemma lem5028764 {B : Type'} (_63193 : B -> Prop) (_63194 : B) (_63192 : B -> Prop) (x' : type638 B) (h1 : term1530 B x') : term1792 B _63193 _63194 _63192.
Proof. exact (EQ_MP (@lem5028763 B _63193 _63194 _63192) (@lem5024555 B _63192 _63194 _63193 x' h1)). Qed.
Lemma lem5028766 (b : Prop) (a : Prop) : (a \/ b) = (term1763 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5028767 {B : Type'} (_63192 : B -> Prop) (_63194 : B) (_63193 : B -> Prop) : (term1792 B _63193 _63194 _63192) = (term1793 B _63192 _63194 _63193).
Proof. exact (@lem5028766 (term1789 B _63193 _63194 _63192) (term1534 B _63194 _63193)). Qed.
Lemma lem5028769 (a : Prop) (b : Prop) : (term1765 a b) = (term1766 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5028770 {B : Type'} (_63193 : B -> Prop) (_63194 : B) (_63192 : B -> Prop) : (term1794 B _63193 _63194 _63192) = (term1795 B _63193 _63194 _63192).
Proof. exact (@lem5028769 (term1561 B _63192 _63193) (term1535 B _63194 _63192)). Qed.
Lemma lem5028772 (a : Prop) : (term1769 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5028773 {B : Type'} (_63192 : B -> Prop) (_63193 : B -> Prop) : (term1796 B _63192 _63193) = (term1559 B _63192 _63193).
Proof. exact (@lem5028772 (term1559 B _63192 _63193)). Qed.
Lemma lem5028774 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5028775 {B : Type'} (_63192 : B -> Prop) (_63193 : B -> Prop) : (term1797 B _63192 _63193) = (term1798 B _63192 _63193).
Proof. exact (MK_COMB (@lem5028774) (@lem5028773 B _63192 _63193)). Qed.
Lemma lem5028777 (a : Prop) : (term1769 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5028778 {B : Type'} (_63194 : B) (_63192 : B -> Prop) : (term1772 B _63194 _63192) = (term1534 B _63194 _63192).
Proof. exact (@lem5028777 (term1534 B _63194 _63192)). Qed.
Lemma lem5028779 {B : Type'} (_63193 : B -> Prop) (_63194 : B) (_63192 : B -> Prop) : (term1795 B _63193 _63194 _63192) = (term1799 B _63193 _63194 _63192).
Proof. exact (MK_COMB (@lem5028775 B _63192 _63193) (@lem5028778 B _63194 _63192)). Qed.
Lemma lem5028780 {B : Type'} (_63193 : B -> Prop) (_63194 : B) (_63192 : B -> Prop) : (term1794 B _63193 _63194 _63192) = (term1799 B _63193 _63194 _63192).
Proof. exact (TRANS (@lem5028770 B _63193 _63194 _63192) (@lem5028779 B _63193 _63194 _63192)). Qed.
Lemma lem5028781 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5028782 {B : Type'} (_63193 : B -> Prop) (_63194 : B) (_63192 : B -> Prop) : (term1800 B _63193 _63194 _63192) = (term1801 B _63193 _63194 _63192).
Proof. exact (MK_COMB (@lem5028781) (@lem5028780 B _63193 _63194 _63192)). Qed.
Lemma lem5028783 {B : Type'} (_63194 : B) (_63193 : B -> Prop) : (term1534 B _63194 _63193) = (term1534 B _63194 _63193).
Proof. exact (eq_refl (term1534 B _63194 _63193)). Qed.
Lemma lem5028784 {B : Type'} (_63192 : B -> Prop) (_63194 : B) (_63193 : B -> Prop) : (term1793 B _63192 _63194 _63193) = (term1802 B _63192 _63194 _63193).
Proof. exact (MK_COMB (@lem5028782 B _63193 _63194 _63192) (@lem5028783 B _63194 _63193)). Qed.
Lemma lem5028785 {B : Type'} (_63192 : B -> Prop) (_63194 : B) (_63193 : B -> Prop) : (term1792 B _63193 _63194 _63192) = (term1802 B _63192 _63194 _63193).
Proof. exact (TRANS (@lem5028767 B _63192 _63194 _63193) (@lem5028784 B _63192 _63194 _63193)). Qed.
Lemma lem5028787 {A B : Type'} (x'''' : type1448 A B) (y : B) (x : A) (x''''''' : A) (y' : A) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term1381 A B x'''') (h2 : term1659 A B y x s f x''''''' y') (h3 : term364 A B f s t) : term1803 A B t x''''''' f s.
Proof. exact (conj (@lem5028619 A B f s t h3) (@lem5028670 A B x'''' y x s f x''''''' y' h1 h2)). Qed.
Lemma lem5028789 {B : Type'} (_63192 : B -> Prop) (_63194 : B) (_63193 : B -> Prop) (x' : type638 B) (h1 : term1530 B x') : term1802 B _63192 _63194 _63193.
Proof. exact (EQ_MP (@lem5028785 B _63192 _63194 _63193) (@lem5028764 B _63193 _63194 _63192 x' h1)). Qed.
Lemma lem5028790 {B : Type'} (_63192 : B -> Prop) (_63194 : B) (_63193 : B -> Prop) (x' : type638 B) (h1 : term1530 B x') : term1802 B _63192 _63194 _63193.
Proof. exact (@lem5028789 B _63192 _63194 _63193 x' h1). Qed.
Lemma lem5028791 {A B : Type'} (s : A -> Prop) (f : A -> B) (x''''''' : A) (t : B -> Prop) (x' : type638 B) (h1 : term1530 B x') : term1804 A B s f x''''''' t.
Proof. exact (@lem5028790 B (term1536 A B f s) (@I (A -> B) f x''''''') t x' h1). Qed.
Lemma lem5028794 {A B : Type'} (x'''' : type1448 A B) (x' : type638 B) (y : B) (x : A) (x''''''' : A) (y' : A) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term1381 A B x'''') (h2 : term1530 B x') (h3 : term1659 A B y x s f x''''''' y') (h4 : term364 A B f s t) : term1805 A B f x''''''' t.
Proof. exact (@lem5028791 A B s f x''''''' t x' h2 (@lem5028787 A B x'''' y x x''''''' y' f s t h1 h3 h4)). Qed.
Lemma lem5028795 {A B : Type'} (x'''' : type1448 A B) (x' : type638 B) (y : B) (x : A) (x''''''' : A) (y' : A) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term1381 A B x'''') (h2 : term1530 B x') (h3 : term1659 A B y x s f x''''''' y') (h4 : term364 A B f s t) : term1806 A B f x''''''' t.
Proof. exact (fun h0 : term1748 A B f x''''''' t => @lem5028794 A B x'''' x' y x x''''''' y' f s t h1 h2 h3 h4). Qed.
Lemma lem5028797 (p : Prop) : (term1755 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5028798 {A B : Type'} (f : A -> B) (x''''''' : A) (t : B -> Prop) : (term1806 A B f x''''''' t) = (term1805 A B f x''''''' t).
Proof. exact (@lem5028797 (term1805 A B f x''''''' t)). Qed.
Lemma lem5028799 {A B : Type'} (x'''' : type1448 A B) (x' : type638 B) (y : B) (x : A) (x''''''' : A) (y' : A) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term1381 A B x'''') (h2 : term1530 B x') (h3 : term1659 A B y x s f x''''''' y') (h4 : term364 A B f s t) : term1805 A B f x''''''' t.
Proof. exact (EQ_MP (@lem5028798 A B f x''''''' t) (@lem5028795 A B x'''' x' y x x''''''' y' f s t h1 h2 h3 h4)). Qed.
Lemma lem5028802 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5028804 {A B : Type'} (f : A -> B) (x''''''' : A) (t : B -> Prop) : (term1748 A B f x''''''' t) = (term1807 A B f x''''''' t).
Proof. exact (@lem5028802 (term1805 A B f x''''''' t)). Qed.
Lemma lem5028807 {A B : Type'} (t : B -> Prop) (x : A) (f : A -> B) (y : B) (x''''''' : A) (y' : A) (h1 : term238 B y t) (h2 : term1655 A B x f y x''''''' y') : term1807 A B f x''''''' t.
Proof. exact (EQ_MP (@lem5028804 A B f x''''''' t) (@lem5024429 A B t x f y x''''''' y' h1 h2)). Qed.
Lemma lem5028810 {A B : Type'} (x'''' : type1448 A B) (x' : type638 B) (x : A) (y : B) (x''''''' : A) (y' : A) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term238 B y t) (h2 : term1381 A B x'''') (h3 : term1530 B x') (h4 : term1659 A B y x s f x''''''' y') (h5 : term1655 A B x f y x''''''' y') (h6 : term364 A B f s t) : False.
Proof. exact (@lem5028807 A B t x f y x''''''' y' h1 h5 (@lem5028799 A B x'''' x' y x x''''''' y' f s t h2 h3 h4 h6)). Qed.
Lemma lem5028811 {A B : Type'} (x'''' : type1448 A B) (x' : type638 B) (x : A) (y : B) (x''''''' : A) (y' : A) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term238 B y t) (h2 : term1381 A B x'''') (h3 : term1530 B x') (h4 : term1659 A B y x s f x''''''' y') (h5 : term1655 A B x f y x''''''' y') (h6 : term364 A B f s t) : term1757.
Proof. exact (fun h0 : ~ False => @lem5028810 A B x'''' x' x y x''''''' y' f s t h1 h2 h3 h4 h5 h6). Qed.
Lemma lem5028813 (p : Prop) : (term1755 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5028814 : term1757 = False.
Proof. exact (@lem5028813 False). Qed.
Lemma lem5029383 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term1659 A B y x s f x''''''' y') : term1534 A x''''''' s.
Proof. exact (proj1 (@lem5015819 A B y x s f x''''''' y' h1)). Qed.
Lemma lem5029384 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term1659 A B y x s f x''''''' y') : term1762 A x''''''' s.
Proof. exact (fun h0 : term1535 A x''''''' s => @lem5029383 A B y x s f x''''''' y' h1). Qed.
Lemma lem5029386 (p : Prop) : (term1755 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5029387 {A : Type'} (x''''''' : A) (s : A -> Prop) : (term1762 A x''''''' s) = (term1534 A x''''''' s).
Proof. exact (@lem5029386 (term1534 A x''''''' s)). Qed.
Lemma lem5029388 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term1659 A B y x s f x''''''' y') : term1534 A x''''''' s.
Proof. exact (EQ_MP (@lem5029387 A x''''''' s) (@lem5029384 A B y x s f x''''''' y' h1)). Qed.
Lemma lem5029390 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term1651 A B x s f x''''''' y') : term1534 A y' s.
Proof. exact (proj1 (@lem5015829 A B x s f x''''''' y' h1)). Qed.
Lemma lem5029391 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term1651 A B x s f x''''''' y') : term1762 A y' s.
Proof. exact (fun h0 : term1535 A y' s => @lem5029390 A B x s f x''''''' y' h1). Qed.
Lemma lem5029393 (p : Prop) : (term1755 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5029394 {A : Type'} (y' : A) (s : A -> Prop) : (term1762 A y' s) = (term1534 A y' s).
Proof. exact (@lem5029393 (term1534 A y' s)). Qed.
Lemma lem5029395 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term1651 A B x s f x''''''' y') : term1534 A y' s.
Proof. exact (EQ_MP (@lem5029394 A y' s) (@lem5029391 A B x s f x''''''' y' h1)). Qed.
Lemma lem5029397 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term1651 A B x s f x''''''' y') : (@I (A -> B) f x''''''') = (@I (A -> B) f y').
Proof. exact (proj1 (@lem5015831 A B x s f x''''''' y' h1)). Qed.
Lemma lem5029398 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term1651 A B x s f x''''''' y') : term1808 A B x''''''' f y'.
Proof. exact (fun h0 : term1545 A B x''''''' f y' => @lem5029397 A B x s f x''''''' y' h1). Qed.
Lemma lem5029400 (p : Prop) : (term1755 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5029401 {A B : Type'} (x''''''' : A) (f : A -> B) (y' : A) : (term1808 A B x''''''' f y') = ((@I (A -> B) f x''''''') = (@I (A -> B) f y')).
Proof. exact (@lem5029400 ((@I (A -> B) f x''''''') = (@I (A -> B) f y'))). Qed.
Lemma lem5029402 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term1651 A B x s f x''''''' y') : (@I (A -> B) f x''''''') = (@I (A -> B) f y').
Proof. exact (EQ_MP (@lem5029401 A B x''''''' f y') (@lem5029398 A B x s f x''''''' y' h1)). Qed.
Lemma lem5029418 (q : Prop) (p : Prop) (r : Prop) : (term1781 p q r) = (term1781 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5029419 {A B : Type'} (f : A -> B) (s : A -> Prop) (_63195 : A) (_63196 : A) : (term1550 A B s f _63195 _63196) = (term1809 A B f s _63195 _63196).
Proof. exact (@lem5029418 (term1545 A B _63195 f _63196) (term1535 A _63196 s) (_63195 = _63196)). Qed.
Lemma lem5029435 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5029436 {A : Type'} (_63195 : A) (_63196 : A) (s : A -> Prop) : (term1810 A s _63195 _63196) = (term1811 A _63195 _63196 s).
Proof. exact (@lem5029435 (_63195 = _63196) (term1535 A _63196 s)). Qed.
Lemma lem5029444 {A B : Type'} (_63195 : A) (f : A -> B) (_63196 : A) : (term1547 A B _63195 f _63196) = (term1547 A B _63195 f _63196).
Proof. exact (eq_refl (term1547 A B _63195 f _63196)). Qed.
Lemma lem5029445 {A B : Type'} (f : A -> B) (_63195 : A) (_63196 : A) (s : A -> Prop) : (term1809 A B f s _63195 _63196) = (term1812 A B f _63195 _63196 s).
Proof. exact (MK_COMB (@lem5029444 A B _63195 f _63196) (@lem5029436 A _63195 _63196 s)). Qed.
Lemma lem5029449 (q : Prop) (p : Prop) (r : Prop) : (term1781 p q r) = (term1781 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5029450 {A B : Type'} (_63195 : A) (f : A -> B) (_63196 : A) (s : A -> Prop) : (term1812 A B f _63195 _63196 s) = (term1813 A B _63195 f _63196 s).
Proof. exact (@lem5029449 (_63195 = _63196) (term1545 A B _63195 f _63196) (term1535 A _63196 s)). Qed.
Lemma lem5029470 {A B : Type'} (_63195 : A) (f : A -> B) (_63196 : A) (s : A -> Prop) : (term1809 A B f s _63195 _63196) = (term1813 A B _63195 f _63196 s).
Proof. exact (TRANS (@lem5029445 A B f _63195 _63196 s) (@lem5029450 A B _63195 f _63196 s)). Qed.
Lemma lem5029471 {A B : Type'} (_63195 : A) (f : A -> B) (_63196 : A) (s : A -> Prop) : (term1550 A B s f _63195 _63196) = (term1813 A B _63195 f _63196 s).
Proof. exact (TRANS (@lem5029419 A B f s _63195 _63196) (@lem5029470 A B _63195 f _63196 s)). Qed.
Lemma lem5029472 {A : Type'} (_63195 : A) (s : A -> Prop) : (term1549 A _63195 s) = (term1549 A _63195 s).
Proof. exact (eq_refl (term1549 A _63195 s)). Qed.
Lemma lem5029473 {A B : Type'} (_63195 : A) (f : A -> B) (_63196 : A) (s : A -> Prop) : (term1724 A B s f _63195 _63196) = (term1814 A B _63195 f _63196 s).
Proof. exact (MK_COMB (@lem5029472 A _63195 s) (@lem5029471 A B _63195 f _63196 s)). Qed.
Lemma lem5029477 (q : Prop) (p : Prop) (r : Prop) : (term1781 p q r) = (term1781 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5029478 {A B : Type'} (_63195 : A) (f : A -> B) (_63196 : A) (s : A -> Prop) : (term1814 A B _63195 f _63196 s) = (term1815 A B _63195 f _63196 s).
Proof. exact (@lem5029477 (_63195 = _63196) (term1535 A _63195 s) (term1816 A B _63195 f _63196 s)). Qed.
Lemma lem5029494 (q : Prop) (p : Prop) (r : Prop) : (term1781 p q r) = (term1781 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5029495 {A B : Type'} (f : A -> B) (_63195 : A) (_63196 : A) (s : A -> Prop) : (term1817 A B _63195 f _63196 s) = (term1818 A B f _63195 _63196 s).
Proof. exact (@lem5029494 (term1545 A B _63195 f _63196) (term1535 A _63195 s) (term1535 A _63196 s)). Qed.
Lemma lem5029513 {A : Type'} (_63195 : A) (_63196 : A) : (term384 A _63195 _63196) = (term384 A _63195 _63196).
Proof. exact (eq_refl (term384 A _63195 _63196)). Qed.
Lemma lem5029514 {A B : Type'} (f : A -> B) (_63195 : A) (_63196 : A) (s : A -> Prop) : (term1815 A B _63195 f _63196 s) = (term1819 A B f _63195 _63196 s).
Proof. exact (MK_COMB (@lem5029513 A _63195 _63196) (@lem5029495 A B f _63195 _63196 s)). Qed.
Lemma lem5029525 {A B : Type'} (f : A -> B) (_63195 : A) (_63196 : A) (s : A -> Prop) : (term1814 A B _63195 f _63196 s) = (term1819 A B f _63195 _63196 s).
Proof. exact (TRANS (@lem5029478 A B _63195 f _63196 s) (@lem5029514 A B f _63195 _63196 s)). Qed.
Lemma lem5029526 {A B : Type'} (f : A -> B) (_63195 : A) (_63196 : A) (s : A -> Prop) : (term1724 A B s f _63195 _63196) = (term1819 A B f _63195 _63196 s).
Proof. exact (TRANS (@lem5029473 A B _63195 f _63196 s) (@lem5029525 A B f _63195 _63196 s)). Qed.
Lemma lem5029527 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5029528 {A B : Type'} (f : A -> B) (_63195 : A) (_63196 : A) (s : A -> Prop) : (term1820 A B s f _63195 _63196) = (term1821 A B f _63195 _63196 s).
Proof. exact (MK_COMB (@lem5029527) (@lem5029526 A B f _63195 _63196 s)). Qed.
Lemma lem5029554 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5029555 {A B : Type'} (_63195 : A) (f : A -> B) (_63196 : A) (s : A -> Prop) : (term1822 A B s _63195 f _63196) = (term1816 A B _63195 f _63196 s).
Proof. exact (@lem5029554 (term1545 A B _63195 f _63196) (term1535 A _63196 s)). Qed.
Lemma lem5029563 {A : Type'} (_63195 : A) (s : A -> Prop) : (term1549 A _63195 s) = (term1549 A _63195 s).
Proof. exact (eq_refl (term1549 A _63195 s)). Qed.
Lemma lem5029564 {A B : Type'} (_63195 : A) (f : A -> B) (_63196 : A) (s : A -> Prop) : (term1823 A B s _63195 f _63196) = (term1817 A B _63195 f _63196 s).
Proof. exact (MK_COMB (@lem5029563 A _63195 s) (@lem5029555 A B _63195 f _63196 s)). Qed.
Lemma lem5029568 (q : Prop) (p : Prop) (r : Prop) : (term1781 p q r) = (term1781 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5029569 {A B : Type'} (f : A -> B) (_63195 : A) (_63196 : A) (s : A -> Prop) : (term1817 A B _63195 f _63196 s) = (term1818 A B f _63195 _63196 s).
Proof. exact (@lem5029568 (term1545 A B _63195 f _63196) (term1535 A _63195 s) (term1535 A _63196 s)). Qed.
Lemma lem5029587 {A B : Type'} (f : A -> B) (_63195 : A) (_63196 : A) (s : A -> Prop) : (term1823 A B s _63195 f _63196) = (term1818 A B f _63195 _63196 s).
Proof. exact (TRANS (@lem5029564 A B _63195 f _63196 s) (@lem5029569 A B f _63195 _63196 s)). Qed.
Lemma lem5029588 {A : Type'} (_63195 : A) (_63196 : A) : (term384 A _63195 _63196) = (term384 A _63195 _63196).
Proof. exact (eq_refl (term384 A _63195 _63196)). Qed.
Lemma lem5029589 {A B : Type'} (f : A -> B) (_63195 : A) (_63196 : A) (s : A -> Prop) : (term1824 A B s _63195 f _63196) = (term1819 A B f _63195 _63196 s).
Proof. exact (MK_COMB (@lem5029588 A _63195 _63196) (@lem5029587 A B f _63195 _63196 s)). Qed.
Lemma lem5029600 {A B : Type'} (f : A -> B) (_63195 : A) (_63196 : A) (s : A -> Prop) : ((term1724 A B s f _63195 _63196) = (term1824 A B s _63195 f _63196)) = ((term1819 A B f _63195 _63196 s) = (term1819 A B f _63195 _63196 s)).
Proof. exact (MK_COMB (@lem5029528 A B f _63195 _63196 s) (@lem5029589 A B f _63195 _63196 s)). Qed.
Lemma lem5029602 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5029603 (x : Prop) : (x = x) = True.
Proof. exact (@lem5029602 Prop x). Qed.
Lemma lem5029604 {A B : Type'} (f : A -> B) (_63195 : A) (_63196 : A) (s : A -> Prop) : ((term1819 A B f _63195 _63196 s) = (term1819 A B f _63195 _63196 s)) = True.
Proof. exact (@lem5029603 (term1819 A B f _63195 _63196 s)). Qed.
Lemma lem5029605 {A B : Type'} (s : A -> Prop) (_63195 : A) (f : A -> B) (_63196 : A) : ((term1724 A B s f _63195 _63196) = (term1824 A B s _63195 f _63196)) = True.
Proof. exact (TRANS (@lem5029600 A B f _63195 _63196 s) (@lem5029604 A B f _63195 _63196 s)). Qed.
Lemma lem5029606 {A B : Type'} (s : A -> Prop) (_63195 : A) (f : A -> B) (_63196 : A) : True = ((term1724 A B s f _63195 _63196) = (term1824 A B s _63195 f _63196)).
Proof. exact (SYM (@lem5029605 A B s _63195 f _63196)). Qed.
Lemma lem5029607 {A B : Type'} (s : A -> Prop) (_63195 : A) (f : A -> B) (_63196 : A) : (term1724 A B s f _63195 _63196) = (term1824 A B s _63195 f _63196).
Proof. exact (EQ_MP (@lem5029606 A B s _63195 f _63196) (@lem0)). Qed.
Lemma lem5029608 {A B : Type'} (_63195 : A) (_63196 : A) (s : A -> Prop) (f : A -> B) (h1 : term122 A B s f) : term1824 A B s _63195 f _63196.
Proof. exact (EQ_MP (@lem5029607 A B s _63195 f _63196) (@lem5020986 A B _63195 _63196 s f h1)). Qed.
Lemma lem5029610 (b : Prop) (a : Prop) : (a \/ b) = (term1763 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5029611 {A B : Type'} (s : A -> Prop) (f : A -> B) (_63195 : A) (_63196 : A) : (term1824 A B s _63195 f _63196) = (term1825 A B s f _63195 _63196).
Proof. exact (@lem5029610 (term1823 A B s _63195 f _63196) (_63195 = _63196)). Qed.
Lemma lem5029613 (a : Prop) (b : Prop) : (term1765 a b) = (term1766 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5029614 {A B : Type'} (s : A -> Prop) (_63195 : A) (f : A -> B) (_63196 : A) : (term1826 A B s _63195 f _63196) = (term1827 A B s _63195 f _63196).
Proof. exact (@lem5029613 (term1535 A _63195 s) (term1822 A B s _63195 f _63196)). Qed.
Lemma lem5029616 (a : Prop) : (term1769 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5029617 {A : Type'} (_63195 : A) (s : A -> Prop) : (term1772 A _63195 s) = (term1534 A _63195 s).
Proof. exact (@lem5029616 (term1534 A _63195 s)). Qed.
Lemma lem5029618 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5029619 {A : Type'} (_63195 : A) (s : A -> Prop) : (term1828 A _63195 s) = (term1649 A _63195 s).
Proof. exact (MK_COMB (@lem5029618) (@lem5029617 A _63195 s)). Qed.
Lemma lem5029621 (a : Prop) (b : Prop) : (term1765 a b) = (term1766 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5029622 {A B : Type'} (s : A -> Prop) (_63195 : A) (f : A -> B) (_63196 : A) : (term1829 A B s _63195 f _63196) = (term1830 A B s _63195 f _63196).
Proof. exact (@lem5029621 (term1535 A _63196 s) (term1545 A B _63195 f _63196)). Qed.
Lemma lem5029624 (a : Prop) : (term1769 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5029625 {A : Type'} (_63196 : A) (s : A -> Prop) : (term1772 A _63196 s) = (term1534 A _63196 s).
Proof. exact (@lem5029624 (term1534 A _63196 s)). Qed.
Lemma lem5029626 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5029627 {A : Type'} (_63196 : A) (s : A -> Prop) : (term1828 A _63196 s) = (term1649 A _63196 s).
Proof. exact (MK_COMB (@lem5029626) (@lem5029625 A _63196 s)). Qed.
Lemma lem5029629 (a : Prop) : (term1769 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5029630 {A B : Type'} (_63195 : A) (f : A -> B) (_63196 : A) : (term1831 A B _63195 f _63196) = ((@I (A -> B) f _63195) = (@I (A -> B) f _63196)).
Proof. exact (@lem5029629 ((@I (A -> B) f _63195) = (@I (A -> B) f _63196))). Qed.
Lemma lem5029631 {A B : Type'} (s : A -> Prop) (_63195 : A) (f : A -> B) (_63196 : A) : (term1830 A B s _63195 f _63196) = (term1832 A B s _63195 f _63196).
Proof. exact (MK_COMB (@lem5029627 A _63196 s) (@lem5029630 A B _63195 f _63196)). Qed.
Lemma lem5029632 {A B : Type'} (s : A -> Prop) (_63195 : A) (f : A -> B) (_63196 : A) : (term1829 A B s _63195 f _63196) = (term1832 A B s _63195 f _63196).
Proof. exact (TRANS (@lem5029622 A B s _63195 f _63196) (@lem5029631 A B s _63195 f _63196)). Qed.
Lemma lem5029633 {A B : Type'} (s : A -> Prop) (_63195 : A) (f : A -> B) (_63196 : A) : (term1827 A B s _63195 f _63196) = (term1833 A B s _63195 f _63196).
Proof. exact (MK_COMB (@lem5029619 A _63195 s) (@lem5029632 A B s _63195 f _63196)). Qed.
Lemma lem5029634 {A B : Type'} (s : A -> Prop) (_63195 : A) (f : A -> B) (_63196 : A) : (term1826 A B s _63195 f _63196) = (term1833 A B s _63195 f _63196).
Proof. exact (TRANS (@lem5029614 A B s _63195 f _63196) (@lem5029633 A B s _63195 f _63196)). Qed.
Lemma lem5029635 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5029636 {A B : Type'} (s : A -> Prop) (_63195 : A) (f : A -> B) (_63196 : A) : (term1834 A B s _63195 f _63196) = (term1835 A B s _63195 f _63196).
Proof. exact (MK_COMB (@lem5029635) (@lem5029634 A B s _63195 f _63196)). Qed.
Lemma lem5029637 {A : Type'} (_63195 : A) (_63196 : A) : (_63195 = _63196) = (_63195 = _63196).
Proof. exact (eq_refl (_63195 = _63196)). Qed.
Lemma lem5029638 {A B : Type'} (s : A -> Prop) (f : A -> B) (_63195 : A) (_63196 : A) : (term1825 A B s f _63195 _63196) = (term1836 A B s f _63195 _63196).
Proof. exact (MK_COMB (@lem5029636 A B s _63195 f _63196) (@lem5029637 A _63195 _63196)). Qed.
Lemma lem5029639 {A B : Type'} (s : A -> Prop) (f : A -> B) (_63195 : A) (_63196 : A) : (term1824 A B s _63195 f _63196) = (term1836 A B s f _63195 _63196).
Proof. exact (TRANS (@lem5029611 A B s f _63195 _63196) (@lem5029638 A B s f _63195 _63196)). Qed.
Lemma lem5029641 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term1651 A B x s f x''''''' y') : term1832 A B s x''''''' f y'.
Proof. exact (conj (@lem5029395 A B x s f x''''''' y' h1) (@lem5029402 A B x s f x''''''' y' h1)). Qed.
Lemma lem5029642 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term1659 A B y x s f x''''''' y') (h2 : term1651 A B x s f x''''''' y') : term1833 A B s x''''''' f y'.
Proof. exact (conj (@lem5029388 A B y x s f x''''''' y' h1) (@lem5029641 A B x s f x''''''' y' h2)). Qed.
Lemma lem5029644 {A B : Type'} (_63195 : A) (_63196 : A) (s : A -> Prop) (f : A -> B) (h1 : term122 A B s f) : term1836 A B s f _63195 _63196.
Proof. exact (EQ_MP (@lem5029639 A B s f _63195 _63196) (@lem5029608 A B _63195 _63196 s f h1)). Qed.
Lemma lem5029645 {A B : Type'} (_63195 : A) (_63196 : A) (s : A -> Prop) (f : A -> B) (h1 : term122 A B s f) : term1836 A B s f _63195 _63196.
Proof. exact (@lem5029644 A B _63195 _63196 s f h1). Qed.
Lemma lem5029646 {A B : Type'} (x''''''' : A) (y' : A) (s : A -> Prop) (f : A -> B) (h1 : term122 A B s f) : term1836 A B s f x''''''' y'.
Proof. exact (@lem5029645 A B x''''''' y' s f h1). Qed.
Lemma lem5029649 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term122 A B s f) (h2 : term1659 A B y x s f x''''''' y') (h3 : term1651 A B x s f x''''''' y') : x''''''' = y'.
Proof. exact (@lem5029646 A B x''''''' y' s f h1 (@lem5029642 A B y x s f x''''''' y' h2 h3)). Qed.
Lemma lem5029650 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term122 A B s f) (h2 : term1659 A B y x s f x''''''' y') (h3 : term1651 A B x s f x''''''' y') : term1837 A x''''''' y'.
Proof. exact (fun h0 : term634 A x''''''' y' => @lem5029649 A B y x s f x''''''' y' h1 h2 h3). Qed.
Lemma lem5029652 (p : Prop) : (term1755 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5029653 {A : Type'} (x''''''' : A) (y' : A) : (term1837 A x''''''' y') = (x''''''' = y').
Proof. exact (@lem5029652 (x''''''' = y')). Qed.
Lemma lem5029654 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term122 A B s f) (h2 : term1659 A B y x s f x''''''' y') (h3 : term1651 A B x s f x''''''' y') : x''''''' = y'.
Proof. exact (EQ_MP (@lem5029653 A x''''''' y') (@lem5029650 A B y x s f x''''''' y' h1 h2 h3)). Qed.
Lemma lem5029657 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5029659 {A : Type'} (x''''''' : A) (y' : A) : (term634 A x''''''' y') = (term1838 A x''''''' y').
Proof. exact (@lem5029657 (x''''''' = y')). Qed.
Lemma lem5029662 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term1651 A B x s f x''''''' y') : term1838 A x''''''' y'.
Proof. exact (EQ_MP (@lem5029659 A x''''''' y') (@lem5021048 A B x s f x''''''' y' h1)). Qed.
Lemma lem5029665 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term122 A B s f) (h2 : term1659 A B y x s f x''''''' y') (h3 : term1651 A B x s f x''''''' y') : False.
Proof. exact (@lem5029662 A B x s f x''''''' y' h3 (@lem5029654 A B y x s f x''''''' y' h1 h2 h3)). Qed.
Lemma lem5029666 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term122 A B s f) (h2 : term1659 A B y x s f x''''''' y') (h3 : term1651 A B x s f x''''''' y') : term1757.
Proof. exact (fun h0 : ~ False => @lem5029665 A B y x s f x''''''' y' h1 h2 h3). Qed.
Lemma lem5029668 (p : Prop) : (term1755 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5029669 : term1757 = False.
Proof. exact (@lem5029668 False). Qed.
Lemma lem5029670 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term122 A B s f) (h2 : term1659 A B y x s f x''''''' y') (h3 : term1651 A B x s f x''''''' y') : False.
Proof. exact (EQ_MP (@lem5029669) (@lem5029666 A B y x s f x''''''' y' h1 h2 h3)). Qed.
Lemma lem5029672 {A B : Type'} (x'''' : type1448 A B) (x' : type638 B) (x : A) (y : B) (x''''''' : A) (y' : A) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term238 B y t) (h2 : term1381 A B x'''') (h3 : term1530 B x') (h4 : term1659 A B y x s f x''''''' y') (h5 : term1655 A B x f y x''''''' y') (h6 : term364 A B f s t) : False.
Proof. exact (EQ_MP (@lem5028814) (@lem5028811 A B x'''' x' x y x''''''' y' f s t h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem5029674 {A B : Type'} (x'''' : type1448 A B) (x' : type638 B) (x : A) (y : B) (x''''''' : A) (y' : A) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term238 B y t) (h2 : term1381 A B x'''') (h3 : term1530 B x') (h4 : term1663 A B x s y f x''''''' y') (h5 : term364 A B f s t) : False.
Proof. exact (EQ_MP (@lem5028045) (@lem5028042 A B x'''' x' x y x''''''' y' f s t h1 h2 h3 h4 h5)). Qed.
Lemma lem5029676 {A B : Type'} (s : A -> Prop) (y : B) (f : A -> B) (x : A) (x''''''' : A) (y' : A) (h1 : term1665 A B x s y f x''''''' y') (h2 : term637 A x x''''''' y') : False.
Proof. exact (EQ_MP (@lem5027276) (@lem5027273 A B s y f x x''''''' y' h1 h2)). Qed.
Lemma lem5029677 {A B : Type'} (x'''' : type1448 A B) (x' : type638 B) (x : A) (x''''''' : A) (y : B) (x'''''' : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term1381 A B x'''') (h2 : term1530 B x') (h3 : term1670 A B x x'''''' f x''''''' s) (h4 : term1677 A B x f x''''''' s y x'''''' t) (h5 : term364 A B f s t) : False.
Proof. exact (EQ_MP (@lem5026686) (@lem5026683 A B x'''' x' x x''''''' y x'''''' f s t h1 h2 h3 h4 h5)). Qed.
Lemma lem5029679 {A B : Type'} (x : A) (f : A -> B) (x''''''' : A) (s : A -> Prop) (y : B) (x'''''' : B) (t : B -> Prop) (h1 : term1672 A B x x'''''' y x''''''' s) (h2 : term1677 A B x f x''''''' s y x'''''' t) : False.
Proof. exact (EQ_MP (@lem5025917) (@lem5025914 A B x f x''''''' s y x'''''' t h1 h2)). Qed.
Lemma lem5029680 {A B : Type'} (x : A) (f : A -> B) (x''''''' : A) (s : A -> Prop) (t : B -> Prop) (x'''''' : B) (y : B) (h1 : term1677 A B x f x''''''' s y x'''''' t) (h2 : x'''''' = y) : False.
Proof. exact (EQ_MP (@lem5025326) (@lem5025323 A B x f x''''''' s t x'''''' y h1 h2)). Qed.
Lemma lem5029681 {A B : Type'} (x : A) (f : A -> B) (x''''''' : A) (s : A -> Prop) (t : B -> Prop) (x'''''' : B) (y : B) (h1 : term1677 A B x f x''''''' s y x'''''' t) (h2 : x'''''' = y) : (x'''''' = y) = False.
Proof. exact (prop_ext (fun h3 : x'''''' = y => @lem5029680 A B x f x''''''' s t x'''''' y h1 h2) (fun h3 : False => @lem5020174 B x'''''' y h2)). Qed.
Lemma lem5029682 {A B : Type'} (x : A) (f : A -> B) (x''''''' : A) (s : A -> Prop) (t : B -> Prop) (x'''''' : B) (y : B) (h1 : term1677 A B x f x''''''' s y x'''''' t) (h2 : x'''''' = y) : False.
Proof. exact (EQ_MP (@lem5029681 A B x f x''''''' s t x'''''' y h1 h2) (@lem5020174 B x'''''' y h2)). Qed.
Lemma lem5029683 {A B : Type'} (x : A) (f : A -> B) (x''''''' : A) (s : A -> Prop) (t : B -> Prop) (x'''''' : B) (y : B) (h1 : term1677 A B x f x''''''' s y x'''''' t) (h2 : x'''''' = y) : (x'''''' = y) = False.
Proof. exact (prop_ext (fun h3 : x'''''' = y => @lem5029682 A B x f x''''''' s t x'''''' y h1 h2) (fun h3 : False => @lem5016327 B x'''''' y h2)). Qed.
Lemma lem5029684 {A B : Type'} (x : A) (f : A -> B) (x''''''' : A) (s : A -> Prop) (t : B -> Prop) (x'''''' : B) (y : B) (h1 : term1677 A B x f x''''''' s y x'''''' t) (h2 : x'''''' = y) : False.
Proof. exact (EQ_MP (@lem5029683 A B x f x''''''' s t x'''''' y h1 h2) (@lem5016327 B x'''''' y h2)). Qed.
Lemma lem5029685 {A B : Type'} (x : A) (f : A -> B) (x''''''' : A) (s : A -> Prop) (t : B -> Prop) (x'''''' : B) (y : B) (h1 : term1677 A B x f x''''''' s y x'''''' t) (h2 : x'''''' = y) : (x'''''' = y) = False.
Proof. exact (prop_ext (fun h3 : x'''''' = y => @lem5029684 A B x f x''''''' s t x'''''' y h1 h2) (fun h3 : False => @lem5016327 B x'''''' y h2)). Qed.
Lemma lem5029686 {A B : Type'} (x : A) (f : A -> B) (x''''''' : A) (s : A -> Prop) (t : B -> Prop) (x'''''' : B) (y : B) (h1 : term1677 A B x f x''''''' s y x'''''' t) (h2 : x'''''' = y) : False.
Proof. exact (EQ_MP (@lem5029685 A B x f x''''''' s t x'''''' y h1 h2) (@lem5016327 B x'''''' y h2)). Qed.
Lemma lem5029687 {A B : Type'} (x'''' : type1448 A B) (x' : type638 B) (y : B) (x : A) (x''''''' : A) (y' : A) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term122 A B s f) (h2 : term238 B y t) (h3 : term1381 A B x'''') (h4 : term1530 B x') (h5 : term1659 A B y x s f x''''''' y') (h6 : term364 A B f s t) : False.
Proof. exact (or_elim (@lem5015821 A B y x s f x''''''' y' h5) (fun h0 : term1655 A B x f y x''''''' y' => @lem5029672 A B x'''' x' x y x''''''' y' f s t h2 h3 h4 h5 h0 h6) (fun h0 : term1651 A B x s f x''''''' y' => @lem5029670 A B y x s f x''''''' y' h1 h5 h0)). Qed.
Lemma lem5029688 {A B : Type'} (x'''' : type1448 A B) (x' : type638 B) (x : A) (y : B) (x''''''' : A) (y' : A) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term238 B y t) (h2 : term1381 A B x'''') (h3 : term1530 B x') (h4 : term1665 A B x s y f x''''''' y') (h5 : term364 A B f s t) : False.
Proof. exact (or_elim (@lem5015807 A B x s y f x''''''' y' h4) (fun h0 : term637 A x x''''''' y' => @lem5029676 A B s y f x x''''''' y' h4 h0) (fun h0 : term1663 A B x s y f x''''''' y' => @lem5029674 A B x'''' x' x y x''''''' y' f s t h1 h2 h3 h0 h5)). Qed.
Lemma lem5029689 {A B : Type'} (x'''' : type1448 A B) (x' : type638 B) (t : B -> Prop) (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term122 A B s f) (h2 : term238 B y t) (h3 : term1381 A B x'''') (h4 : term1530 B x') (h5 : term364 A B f s t) (h6 : term1667 A B y x s f x''''''' y') : False.
Proof. exact (or_elim (@lem5015788 A B y x s f x''''''' y' h6) (fun h0 : term1665 A B x s y f x''''''' y' => @lem5029688 A B x'''' x' x y x''''''' y' f s t h2 h3 h4 h0 h5) (fun h0 : term1659 A B y x s f x''''''' y' => @lem5029687 A B x'''' x' y x x''''''' y' f s t h1 h2 h3 h4 h0 h5)). Qed.
Lemma lem5029690 {A B : Type'} (x'''' : type1448 A B) (x' : type638 B) (t : B -> Prop) (y : B) (x : A) (x'''''' : B) (f : A -> B) (x''''''' : A) (s : A -> Prop) (h1 : term1381 A B x'''') (h2 : term1530 B x') (h3 : term1677 A B x f x''''''' s y x'''''' t) (h4 : term364 A B f s t) (h5 : term1674 A B y x x'''''' f x''''''' s) : False.
Proof. exact (or_elim (@lem5015794 A B y x x'''''' f x''''''' s h5) (fun h0 : term1672 A B x x'''''' y x''''''' s => @lem5029679 A B x f x''''''' s y x'''''' t h0 h3) (fun h0 : term1670 A B x x'''''' f x''''''' s => @lem5029677 A B x'''' x' x x''''''' y x'''''' f s t h1 h2 h0 h3 h4)). Qed.
Lemma lem5029691 {A B : Type'} (x'''' : type1448 A B) (x' : type638 B) (x : A) (x''''''' : A) (y : B) (x'''''' : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term1381 A B x'''') (h2 : term1530 B x') (h3 : term1677 A B x f x''''''' s y x'''''' t) (h4 : term364 A B f s t) : False.
Proof. exact (or_elim (@lem5015790 A B x f x''''''' s y x'''''' t h3) (fun h0 : x'''''' = y => @lem5029686 A B x f x''''''' s t x'''''' y h3 h0) (fun h0 : term1674 A B y x x'''''' f x''''''' s => @lem5029690 A B x'''' x' t y x x'''''' f x''''''' s h1 h2 h3 h4 h0)). Qed.
Lemma lem5029692 {A B : Type'} (x'''' : type1448 A B) (x' : type638 B) (x'''''' : B) (t : B -> Prop) (y : B) (x : A) (s : A -> Prop) (f : A -> B) (x''''''' : A) (y' : A) (h1 : term122 A B s f) (h2 : term238 B y t) (h3 : term1381 A B x'''') (h4 : term1530 B x') (h5 : term364 A B f s t) (h6 : term985 A B x'''''' t y x s f x''''''' y') : False.
Proof. exact (or_elim (@lem5015776 A B x'''''' t y x s f x''''''' y' h6) (fun h0 : term1677 A B x f x''''''' s y x'''''' t => @lem5029691 A B x'''' x' x x''''''' y x'''''' f s t h3 h4 h0 h5) (fun h0 : term1667 A B y x s f x''''''' y' => @lem5029689 A B x'''' x' t y x s f x''''''' y' h1 h2 h3 h4 h5 h0)). Qed.
Lemma lem5029693 {A B : Type'} (x'''''' : B) (x : A) (x''''''' : A) (y : B) (x'''' : type1448 A B) (x' : type638 B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term122 A B s f) (h2 : term988 A B x'''''' t y x s f x''''''') (h3 : term238 B y t) (h4 : term1381 A B x'''') (h5 : term1530 B x') (h6 : term364 A B f s t) : False.
Proof. exact (ex_elim (@lem5014257 A B x'''''' t y x s f x''''''' h2) (fun y' : A => fun h0 : term987 A B x'''''' t y x s f x''''''' y' => @lem5029692 A B x'''' x' x'''''' t y x s f x''''''' y' h1 h3 h4 h5 h6 h0)). Qed.
Lemma lem5029694 {A B : Type'} (x'''''' : B) (x : A) (y : B) (x'''' : type1448 A B) (x' : type638 B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term122 A B s f) (h2 : term990 A B x'''''' t y x s f) (h3 : term238 B y t) (h4 : term1381 A B x'''') (h5 : term1530 B x') (h6 : term364 A B f s t) : False.
Proof. exact (ex_elim (@lem5014256 A B x'''''' t y x s f h2) (fun x''''''' : A => fun h0 : term989 A B x'''''' t y x s f x''''''' => @lem5029693 A B x'''''' x x''''''' y x'''' x' f s t h1 h0 h3 h4 h5 h6)). Qed.
Lemma lem5029695 {A B : Type'} (x : A) (y : B) (x'''' : type1448 A B) (x' : type638 B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term122 A B s f) (h2 : term588 A B t y x s f) (h3 : term238 B y t) (h4 : term1381 A B x'''') (h5 : term1530 B x') (h6 : term364 A B f s t) : False.
Proof. exact (ex_elim (@lem5010334 A B t y x s f h2) (fun x'''''' : B => fun h0 : term991 A B t y x s f x'''''' => @lem5029694 A B x'''''' x y x'''' x' f s t h1 h0 h3 h4 h5 h6)). Qed.
Lemma lem5029696 {A B : Type'} (x : A) (y : B) (x'''' : type1448 A B) (x' : type638 B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term432 A) (h2 : term122 A B s f) (h3 : term588 A B t y x s f) (h4 : term238 B y t) (h5 : term1381 A B x'''') (h6 : term1530 B x') (h7 : term364 A B f s t) : False.
Proof. exact (ex_elim (@lem5011226 A h1) (fun x''''' : type1361 A => fun h0 : term1191 A x''''' => @lem5029695 A B x y x'''' x' f s t h2 h3 h4 h5 h6 h7)). Qed.
Lemma lem5029697 {A B : Type'} (x : A) (y : B) (x' : type638 B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term432 A) (h2 : term122 A B s f) (h3 : term433 A B) (h4 : term588 A B t y x s f) (h5 : term238 B y t) (h6 : term1530 B x') (h7 : term364 A B f s t) : False.
Proof. exact (ex_elim (@lem5012118 A B h3) (fun x'''' : type1448 A B => fun h0 : term1383 A B x'''' => @lem5029696 A B x y x'''' x' f s t h1 h2 h4 h5 h0 h6 h7)). Qed.
Lemma lem5029698 {A B : Type'} (x : A) (y : B) (x' : type638 B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term432 A) (h2 : term122 A B s f) (h3 : term433 A B) (h4 : term432 B) (h5 : term588 A B t y x s f) (h6 : term238 B y t) (h7 : term1530 B x') (h8 : term364 A B f s t) : False.
Proof. exact (ex_elim (@lem5013010 B h4) (fun x''' : type1361 B => fun h0 : term1191 B x''' => @lem5029697 A B x y x' f s t h1 h2 h3 h5 h6 h7 h8)). Qed.
Lemma lem5029699 {A B : Type'} (x : A) (y : B) (x' : type638 B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term432 A) (h2 : term122 A B s f) (h3 : term433 A B) (h4 : term432 B) (h5 : term431 A) (h6 : term588 A B t y x s f) (h7 : term238 B y t) (h8 : term1530 B x') (h9 : term364 A B f s t) : False.
Proof. exact (ex_elim (@lem5013630 A h5) (fun x'' : type638 A => fun h0 : term1532 A x'' => @lem5029698 A B x y x' f s t h1 h2 h3 h4 h6 h7 h8 h9)). Qed.
Lemma lem5029700 {A B : Type'} (x : A) (y : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term432 A) (h2 : term122 A B s f) (h3 : term433 A B) (h4 : term432 B) (h5 : term431 A) (h6 : term431 B) (h7 : term588 A B t y x s f) (h8 : term238 B y t) (h9 : term364 A B f s t) : False.
Proof. exact (ex_elim (@lem5014250 B h6) (fun x' : type638 B => fun h0 : term1532 B x' => @lem5029699 A B x y x' f s t h1 h2 h3 h4 h5 h7 h8 h0 h9)). Qed.
Lemma lem5029701 {A B : Type'} (x : A) (y : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term432 A) (h2 : term122 A B s f) (h3 : term433 A B) (h4 : term432 B) (h5 : term431 A) (h6 : term431 B) (h7 : term588 A B t y x s f) (h8 : term238 B y t) (h9 : term364 A B f s t) : (term364 A B f s t) = False.
Proof. exact (prop_ext (fun h10 : term364 A B f s t => @lem5029700 A B x y f s t h1 h2 h3 h4 h5 h6 h7 h8 h9) (fun h10 : False => @lem5008953 A B f s t h9)). Qed.
Lemma lem5029702 {A B : Type'} (x : A) (y : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term432 A) (h2 : term122 A B s f) (h3 : term433 A B) (h4 : term432 B) (h5 : term431 A) (h6 : term431 B) (h7 : term588 A B t y x s f) (h8 : term238 B y t) (h9 : term364 A B f s t) : False.
Proof. exact (EQ_MP (@lem5029701 A B x y f s t h1 h2 h3 h4 h5 h6 h7 h8 h9) (@lem5008953 A B f s t h9)). Qed.
Lemma lem5029703 {A B : Type'} (x : A) (y : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term432 A) (h2 : term122 A B s f) (h3 : term433 A B) (h4 : term432 B) (h5 : term431 A) (h6 : term431 B) (h7 : term588 A B t y x s f) (h8 : term238 B y t) (h9 : term364 A B f s t) : (term238 B y t) = False.
Proof. exact (prop_ext (fun h10 : term238 B y t => @lem5029702 A B x y f s t h1 h2 h3 h4 h5 h6 h7 h8 h9) (fun h10 : False => @lem5008935 B y t h8)). Qed.
Lemma lem5029704 {A B : Type'} (x : A) (y : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term432 A) (h2 : term122 A B s f) (h3 : term433 A B) (h4 : term432 B) (h5 : term431 A) (h6 : term431 B) (h7 : term588 A B t y x s f) (h8 : term238 B y t) (h9 : term364 A B f s t) : False.
Proof. exact (EQ_MP (@lem5029703 A B x y f s t h1 h2 h3 h4 h5 h6 h7 h8 h9) (@lem5008935 B y t h8)). Qed.
Lemma lem5029705 {A B : Type'} (x : A) (y : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term432 A) (h2 : term122 A B s f) (h3 : term433 A B) (h4 : term432 B) (h5 : term431 A) (h6 : term588 A B t y x s f) (h7 : term238 B y t) (h8 : term364 A B f s t) : term438 B.
Proof. exact (fun h0 : term431 B => @lem5029704 A B x y f s t h1 h2 h3 h4 h5 h0 h6 h7 h8). Qed.
Lemma lem5029706 {B : Type'} : (term438 B) = (term439 B).
Proof. exact (@lem69 (term431 B)). Qed.
Lemma lem5029707 {A B : Type'} (x : A) (y : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term432 A) (h2 : term122 A B s f) (h3 : term433 A B) (h4 : term432 B) (h5 : term431 A) (h6 : term588 A B t y x s f) (h7 : term238 B y t) (h8 : term364 A B f s t) : term439 B.
Proof. exact (EQ_MP (@lem5029706 B) (@lem5029705 A B x y f s t h1 h2 h3 h4 h5 h6 h7 h8)). Qed.
Lemma lem5029708 {A B : Type'} (x : A) (y : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term432 A) (h2 : term122 A B s f) (h3 : term433 A B) (h4 : term432 B) (h5 : term588 A B t y x s f) (h6 : term238 B y t) (h7 : term364 A B f s t) : term442 A B.
Proof. exact (fun h0 : term431 A => @lem5029707 A B x y f s t h1 h2 h3 h4 h0 h5 h6 h7). Qed.
Lemma lem5029709 {A B : Type'} (x : A) (y : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term432 A) (h2 : term122 A B s f) (h3 : term433 A B) (h4 : term588 A B t y x s f) (h5 : term238 B y t) (h6 : term364 A B f s t) : term445 A B.
Proof. exact (fun h0 : term432 B => @lem5029708 A B x y f s t h1 h2 h3 h0 h4 h5 h6). Qed.
Lemma lem5029710 {A B : Type'} (x : A) (y : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term432 A) (h2 : term122 A B s f) (h3 : term588 A B t y x s f) (h4 : term238 B y t) (h5 : term364 A B f s t) : term448 A B.
Proof. exact (fun h0 : term433 A B => @lem5029709 A B x y f s t h1 h2 h0 h3 h4 h5). Qed.
Lemma lem5029711 {A B : Type'} (x : A) (y : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term122 A B s f) (h2 : term588 A B t y x s f) (h3 : term238 B y t) (h4 : term364 A B f s t) : term450 A B.
Proof. exact (fun h0 : term432 A => @lem5029710 A B x y f s t h0 h1 h2 h3 h4). Qed.
Lemma lem5029712 {A B : Type'} (x : A) (y : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term122 A B s f) (h2 : term238 B y t) (h3 : term364 A B f s t) : term590 A B t y x s f.
Proof. exact (fun h0 : term588 A B t y x s f => @lem5029711 A B x y f s t h1 h0 h2 h3). Qed.
Lemma lem5029713 {A B : Type'} (x : A) (y : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term238 B y t) (h2 : term364 A B f s t) : term591 A B t y x s f.
Proof. exact (fun h0 : term122 A B s f => @lem5029712 A B x y f s t h0 h1 h2). Qed.
Lemma lem5029714 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (y : B) (t : B -> Prop) (h1 : term238 B y t) : term592 A B t y x s f.
Proof. exact (fun h0 : term364 A B f s t => @lem5029713 A B x y f s t h1 h0). Qed.
Lemma lem5029715 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (y : B) (t : B -> Prop) (h1 : term238 B y t) : term593 A B t y x s f.
Proof. exact (fun h0 : term59 A B s t => @lem5029714 A B x s f y t h1). Qed.
Lemma lem5029716 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (y : B) (t : B -> Prop) (h1 : term238 B y t) : term594 A B t y x s f.
Proof. exact (fun h0 : @FINITE B t => @lem5029715 A B x s f y t h1). Qed.
Lemma lem5029717 {A B : Type'} (t : B -> Prop) (y : B) (x : A) (s : A -> Prop) (f : A -> B) : term595 A B t y x s f.
Proof. exact (fun h0 : term238 B y t => @lem5029716 A B x s f y t h0). Qed.
Lemma lem5029718 {A B : Type'} (t : B -> Prop) (y : B) (x : A) (s : A -> Prop) (f : A -> B) : term596 A B t y x s f.
Proof. exact (fun h0 : @FINITE A s => @lem5029717 A B t y x s f). Qed.
Lemma lem5029719 {A B : Type'} (t : B -> Prop) (y : B) (x : A) (s : A -> Prop) (f : A -> B) : term597 A B t y x s f.
Proof. exact (fun h0 : term238 A x s => @lem5029718 A B t y x s f). Qed.
Lemma lem5029724 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (f : A -> B) : term599 A B y x s f.
Proof. exact (fun t : B -> Prop => @lem5029719 A B t y x s f). Qed.
Lemma lem5029729 {A B : Type'} (y : B) (x : A) (f : A -> B) : term601 A B y x f.
Proof. exact (fun s : A -> Prop => @lem5029724 A B y x s f). Qed.
Lemma lem5029734 {A B : Type'} (y : B) (f : A -> B) : term603 A B y f.
Proof. exact (fun x : A => @lem5029729 A B y x f). Qed.
Lemma lem5029739 {A B : Type'} (f : A -> B) : term605 A B f.
Proof. exact (fun y : B => @lem5029734 A B y f). Qed.
Lemma lem5029744 {A B : Type'} : term607 A B.
Proof. exact (fun f : A -> B => @lem5029739 A B f). Qed.
Lemma lem5029745 {A B : Type'} : term488 A B.
Proof. exact (EQ_MP (@lem5008904 A B) (@lem5029744 A B)). Qed.
Lemma lem5029746 {A B : Type'} (f : A -> B) : term1839 A B f.
Proof. exact (@lem5029745 A B f). Qed.
Lemma lem5029747 {A B : Type'} (f : A -> B) : (term1839 A B f) = (term484 A B f).
Proof. exact (eq_refl (term1839 A B f)). Qed.
Lemma lem5029748 {A B : Type'} (f : A -> B) : term484 A B f.
Proof. exact (EQ_MP (@lem5029747 A B f) (@lem5029746 A B f)). Qed.
Lemma lem5029749 {A B : Type'} (f : A -> B) (y : B) : term1840 A B f y.
Proof. exact (@lem5029748 A B f y). Qed.
Lemma lem5029750 {A B : Type'} (y : B) (f : A -> B) : (term1840 A B f y) = (term480 A B y f).
Proof. exact (eq_refl (term1840 A B f y)). Qed.
Lemma lem5029751 {A B : Type'} (y : B) (f : A -> B) : term480 A B y f.
Proof. exact (EQ_MP (@lem5029750 A B y f) (@lem5029749 A B f y)). Qed.
Lemma lem5029752 {A B : Type'} (y : B) (f : A -> B) (x : A) : term1841 A B y f x.
Proof. exact (@lem5029751 A B y f x). Qed.
Lemma lem5029753 {A B : Type'} (x : A) (y : B) (f : A -> B) : (term1841 A B y f x) = (term476 A B x y f).
Proof. exact (eq_refl (term1841 A B y f x)). Qed.
Lemma lem5029754 {A B : Type'} (x : A) (y : B) (f : A -> B) : term476 A B x y f.
Proof. exact (EQ_MP (@lem5029753 A B x y f) (@lem5029752 A B y f x)). Qed.
Lemma lem5029755 {A B : Type'} (x : A) (y : B) (f : A -> B) (s : A -> Prop) : term1842 A B x y f s.
Proof. exact (@lem5029754 A B x y f s). Qed.
Lemma lem5029756 {A B : Type'} (s : A -> Prop) (x : A) (y : B) (f : A -> B) : (term1842 A B x y f s) = (term472 A B s x y f).
Proof. exact (eq_refl (term1842 A B x y f s)). Qed.
Lemma lem5029757 {A B : Type'} (s : A -> Prop) (x : A) (y : B) (f : A -> B) : term472 A B s x y f.
Proof. exact (EQ_MP (@lem5029756 A B s x y f) (@lem5029755 A B x y f s)). Qed.
Lemma lem5029758 {A B : Type'} (s : A -> Prop) (x : A) (y : B) (f : A -> B) (t : B -> Prop) : term1843 A B s x y f t.
Proof. exact (@lem5029757 A B s x y f t). Qed.
Lemma lem5029759 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) (y : B) (f : A -> B) : (term1843 A B s x y f t) = (term434 A B t s x y f).
Proof. exact (eq_refl (term1843 A B s x y f t)). Qed.
Lemma lem5029760 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) (y : B) (f : A -> B) : term434 A B t s x y f.
Proof. exact (EQ_MP (@lem5029759 A B t s x y f) (@lem5029758 A B s x y f t)). Qed.
Lemma lem5029762 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (x : A) (y : B) (f : A -> B) : term434 A B t s x y f.
Proof. exact (@lem5007422 A B t s x y f (@lem5029760 A B t s x y f)). Qed.
Lemma lem5029763 {A B : Type'} (t : B -> Prop) (y : B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term238 A x s) : term467 A B t s x y f.
Proof. exact (@lem5029762 A B t s x y f (@lem5003610 A x s h1)). Qed.
Lemma lem5029764 {A B : Type'} (t : B -> Prop) (y : B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term238 A x s) : term465 A B t s x y f.
Proof. exact (@lem5029763 A B t y f x s h2 (@lem5003609 A s h1)). Qed.
Lemma lem5029765 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term238 A x s) (h3 : term238 B y t) : term462 A B t s x y f.
Proof. exact (@lem5029764 A B t y f x s h1 h2 (@lem5006892 B y t h3)). Qed.
Lemma lem5029766 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term238 A x s) (h4 : term238 B y t) : term460 A B t s x y f.
Proof. exact (@lem5029765 A B f x s y t h1 h3 h4 (@lem5006891 B t h2)). Qed.
Lemma lem5029767 {A B : Type'} (f : A -> B) (x : A) (y : B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term238 A x s) (h4 : term238 B y t) (h5 : term59 A B s t) : term458 A B t s x y f.
Proof. exact (@lem5029766 A B f x s y t h1 h2 h3 h4 (@lem5006931 A B s t h5)). Qed.
Lemma lem5029768 {A B : Type'} (x : A) (y : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term238 A x s) (h4 : term238 B y t) (h5 : term59 A B s t) (h6 : term364 A B f s t) : term455 A B t s x y f.
Proof. exact (@lem5029767 A B f x y s t h1 h2 h3 h4 h5 (@lem5007162 A B f s t h6)). Qed.
Lemma lem5029769 {A B : Type'} (x : A) (y : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term122 A B s f) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : term238 A x s) (h5 : term238 B y t) (h6 : term59 A B s t) (h7 : term364 A B f s t) : term452 A B t s x y f.
Proof. exact (@lem5029768 A B x y f s t h2 h3 h4 h5 h6 h7 (@lem5007161 A B s f h1)). Qed.
Lemma lem5029770 {A B : Type'} (x : A) (y : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term122 A B s f) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : term430 A B t s x y f) (h5 : term238 A x s) (h6 : term238 B y t) (h7 : term59 A B s t) (h8 : term364 A B f s t) : term449 A B.
Proof. exact (@lem5029769 A B x y f s t h1 h2 h3 h5 h6 h7 h8 (@lem5007396 A B t s x y f h4)). Qed.
Lemma lem5029771 {A B : Type'} (x : A) (y : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term122 A B s f) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : term430 A B t s x y f) (h5 : term238 A x s) (h6 : term238 B y t) (h7 : term59 A B s t) (h8 : term364 A B f s t) : term447 A B.
Proof. exact (@lem5029770 A B x y f s t h1 h2 h3 h4 h5 h6 h7 h8 (@lem5007400 A)). Qed.
Lemma lem5029772 {A B : Type'} (x : A) (y : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term122 A B s f) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : term430 A B t s x y f) (h5 : term238 A x s) (h6 : term238 B y t) (h7 : term59 A B s t) (h8 : term364 A B f s t) : term444 A B.
Proof. exact (@lem5029771 A B x y f s t h1 h2 h3 h4 h5 h6 h7 h8 (@lem5007401 A B)). Qed.
Lemma lem5029773 {A B : Type'} (x : A) (y : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term122 A B s f) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : term430 A B t s x y f) (h5 : term238 A x s) (h6 : term238 B y t) (h7 : term59 A B s t) (h8 : term364 A B f s t) : term441 A B.
Proof. exact (@lem5029772 A B x y f s t h1 h2 h3 h4 h5 h6 h7 h8 (@lem5007406 B)). Qed.
Lemma lem5029774 {A B : Type'} (x : A) (y : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term122 A B s f) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : term430 A B t s x y f) (h5 : term238 A x s) (h6 : term238 B y t) (h7 : term59 A B s t) (h8 : term364 A B f s t) : term438 B.
Proof. exact (@lem5029773 A B x y f s t h1 h2 h3 h4 h5 h6 h7 h8 (@lem5007398 A)). Qed.
Lemma lem5029775 {A B : Type'} (x : A) (y : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term122 A B s f) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : term430 A B t s x y f) (h5 : term238 A x s) (h6 : term238 B y t) (h7 : term59 A B s t) (h8 : term364 A B f s t) : False.
Proof. exact (@lem5029774 A B x y f s t h1 h2 h3 h4 h5 h6 h7 h8 (@lem5007397 B)). Qed.
Lemma lem5029776 {A B : Type'} (x : A) (y : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term122 A B s f) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : term430 A B t s x y f) (h5 : term238 A x s) (h6 : term238 B y t) (h7 : term59 A B s t) (h8 : term364 A B f s t) : (term430 A B t s x y f) = False.
Proof. exact (prop_ext (fun h9 : term430 A B t s x y f => @lem5029775 A B x y f s t h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem5007396 A B t s x y f h4)). Qed.
Lemma lem5029777 {A B : Type'} (x : A) (y : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term122 A B s f) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : term430 A B t s x y f) (h5 : term238 A x s) (h6 : term238 B y t) (h7 : term59 A B s t) (h8 : term364 A B f s t) : False.
Proof. exact (EQ_MP (@lem5029776 A B x y f s t h1 h2 h3 h4 h5 h6 h7 h8) (@lem5007396 A B t s x y f h4)). Qed.
Lemma lem5029778 {A B : Type'} (x : A) (y : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term122 A B s f) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : term238 A x s) (h5 : term238 B y t) (h6 : term59 A B s t) (h7 : term364 A B f s t) : term429 A B t s x y f.
Proof. exact (fun h0 : term430 A B t s x y f => @lem5029777 A B x y f s t h1 h2 h3 h0 h4 h5 h6 h7). Qed.
Lemma lem5029779 {A B : Type'} (x : A) (y : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term122 A B s f) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : term238 A x s) (h5 : term238 B y t) (h6 : term59 A B s t) (h7 : term364 A B f s t) : term427 A B t s x y f.
Proof. exact (EQ_MP (@lem5007395 A B t s x y f) (@lem5029778 A B x y f s t h1 h2 h3 h4 h5 h6 h7)). Qed.
Lemma lem5029780 {A B : Type'} (x : A) (y : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term122 A B s f) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : term238 A x s) (h5 : term238 B y t) (h6 : term59 A B s t) (h7 : term364 A B f s t) : term426 A B t s x y f.
Proof. exact (EQ_MP (@lem5007391 A B t s x y f) (@lem5029779 A B x y f s t h1 h2 h3 h4 h5 h6 h7)). Qed.
Lemma lem5029781 {A B : Type'} (x : A) (y : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term122 A B s f) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : term238 A x s) (h5 : term238 B y t) (h6 : term59 A B s t) (h7 : term364 A B f s t) : term342 A B y t x s.
Proof. exact (ex_intro (term1844 A B y t x s) (term374 A B x y f) (@lem5029780 A B x y f s t h1 h2 h3 h4 h5 h6 h7)). Qed.
Lemma lem5029782 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term123 A B t s f) : term122 A B s f.
Proof. exact (proj2 (@lem5007160 A B t s f h1)). Qed.
Lemma lem5029783 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term123 A B t s f) : term364 A B f s t.
Proof. exact (proj1 (@lem5007160 A B t s f h1)). Qed.
Lemma lem5029784 {A B : Type'} (x : A) (y : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term122 A B s f) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : term238 A x s) (h5 : term238 B y t) (h6 : term59 A B s t) (h7 : term364 A B f s t) : (term122 A B s f) = (term342 A B y t x s).
Proof. exact (prop_ext (fun h8 : term122 A B s f => @lem5029781 A B x y f s t h1 h2 h3 h4 h5 h6 h7) (fun h8 : term342 A B y t x s => @lem5007161 A B s f h1)). Qed.
Lemma lem5029785 {A B : Type'} (x : A) (y : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term122 A B s f) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : term238 A x s) (h5 : term238 B y t) (h6 : term59 A B s t) (h7 : term364 A B f s t) : term342 A B y t x s.
Proof. exact (EQ_MP (@lem5029784 A B x y f s t h1 h2 h3 h4 h5 h6 h7) (@lem5007161 A B s f h1)). Qed.
Lemma lem5029786 {A B : Type'} (x : A) (y : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term122 A B s f) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : term238 A x s) (h5 : term238 B y t) (h6 : term59 A B s t) (h7 : term364 A B f s t) : (term364 A B f s t) = (term342 A B y t x s).
Proof. exact (prop_ext (fun h8 : term364 A B f s t => @lem5029785 A B x y f s t h1 h2 h3 h4 h5 h6 h7) (fun h8 : term342 A B y t x s => @lem5007162 A B f s t h7)). Qed.
Lemma lem5029787 {A B : Type'} (x : A) (y : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term122 A B s f) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : term238 A x s) (h5 : term238 B y t) (h6 : term59 A B s t) (h7 : term364 A B f s t) : term342 A B y t x s.
Proof. exact (EQ_MP (@lem5029786 A B x y f s t h1 h2 h3 h4 h5 h6 h7) (@lem5007162 A B f s t h7)). Qed.
Lemma lem5029788 {A B : Type'} (x : A) (y : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term238 A x s) (h4 : term238 B y t) (h5 : term123 A B t s f) (h6 : term59 A B s t) (h7 : term364 A B f s t) : (term122 A B s f) = (term342 A B y t x s).
Proof. exact (prop_ext (fun h8 : term122 A B s f => @lem5029787 A B x y f s t h8 h1 h2 h3 h4 h6 h7) (fun h8 : term342 A B y t x s => @lem5029782 A B t s f h5)). Qed.
Lemma lem5029789 {A B : Type'} (x : A) (y : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term238 A x s) (h4 : term238 B y t) (h5 : term123 A B t s f) (h6 : term59 A B s t) (h7 : term364 A B f s t) : term342 A B y t x s.
Proof. exact (EQ_MP (@lem5029788 A B x y f s t h1 h2 h3 h4 h5 h6 h7) (@lem5029782 A B t s f h5)). Qed.
Lemma lem5029790 {A B : Type'} (x : A) (y : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term238 A x s) (h4 : term238 B y t) (h5 : term123 A B t s f) (h6 : term59 A B s t) : (term364 A B f s t) = (term342 A B y t x s).
Proof. exact (prop_ext (fun h7 : term364 A B f s t => @lem5029789 A B x y f s t h1 h2 h3 h4 h5 h6 h7) (fun h7 : term342 A B y t x s => @lem5029783 A B t s f h5)). Qed.
Lemma lem5029791 {A B : Type'} (x : A) (y : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term238 A x s) (h4 : term238 B y t) (h5 : term123 A B t s f) (h6 : term59 A B s t) : term342 A B y t x s.
Proof. exact (EQ_MP (@lem5029790 A B x y f s t h1 h2 h3 h4 h5 h6) (@lem5029783 A B t s f h5)). Qed.
Lemma lem5029792 {A B : Type'} (x : A) (y : B) (s : A -> Prop) (t : B -> Prop) (h1 : term125 A B t s) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : term238 A x s) (h5 : term238 B y t) (h6 : term59 A B s t) : term342 A B y t x s.
Proof. exact (ex_elim (@lem5007159 A B t s h1) (fun f : A -> B => fun h0 : term124 A B t s f => @lem5029791 A B x y f s t h2 h3 h4 h5 h0 h6)). Qed.
Lemma lem5029793 {A B : Type'} (x : A) (y : B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term238 A x s) (h4 : term238 B y t) (h5 : term59 A B s t) : term363 A B y t x s.
Proof. exact (fun h0 : term125 A B t s => @lem5029792 A B x y s t h0 h1 h2 h3 h4 h5). Qed.
Lemma lem5029794 {A B : Type'} (x : A) (y : B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term238 A x s) (h4 : term238 B y t) (h5 : term59 A B s t) : term362 A B y t x s.
Proof. exact (EQ_MP (@lem5007158 A B y x s t h2 h5) (@lem5029793 A B x y s t h1 h2 h3 h4 h5)). Qed.
Lemma lem5029795 {A B : Type'} (x : A) (y : B) (s : A -> Prop) (t : B -> Prop) (h1 : term129 A B s) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : term238 A x s) (h5 : term238 B y t) (h6 : term59 A B s t) : term342 A B y t x s.
Proof. exact (@lem5029794 A B x y s t h2 h3 h4 h5 h6 (@lem5006934 A B t s h1)). Qed.
Lemma lem5029796 {A B : Type'} (x : A) (y : B) (s : A -> Prop) (t : B -> Prop) (h1 : term129 A B s) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : term238 A x s) (h5 : term238 B y t) (h6 : term59 A B s t) : (term59 A B s t) = (term342 A B y t x s).
Proof. exact (prop_ext (fun h7 : term59 A B s t => @lem5029795 A B x y s t h1 h2 h3 h4 h5 h6) (fun h7 : term342 A B y t x s => @lem5006931 A B s t h6)). Qed.
Lemma lem5029797 {A B : Type'} (x : A) (y : B) (s : A -> Prop) (t : B -> Prop) (h1 : term129 A B s) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : term238 A x s) (h5 : term238 B y t) (h6 : term59 A B s t) : term342 A B y t x s.
Proof. exact (EQ_MP (@lem5029796 A B x y s t h1 h2 h3 h4 h5 h6) (@lem5006931 A B s t h6)). Qed.
Lemma lem5029798 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (h1 : term129 A B s) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : term238 A x s) (h5 : term238 B y t) : term357 A B y t x s.
Proof. exact (fun h0 : term59 A B s t => @lem5029797 A B x y s t h1 h2 h3 h4 h5 h0). Qed.
Lemma lem5029799 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (h1 : term129 A B s) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : term238 A x s) (h5 : term238 B y t) : term352 A B y t x s.
Proof. exact (EQ_MP (@lem5006930 A B y t x s) (@lem5029798 A B x s y t h1 h2 h3 h4 h5)). Qed.
Lemma lem5029800 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (h1 : term304 A B x s y t) : term142 B y t.
Proof. exact (proj2 (@lem5006888 A B x s y t h1)). Qed.
Lemma lem5029802 {B : Type'} (y : B) (t : B -> Prop) (h1 : term142 B y t) : @FINITE B t.
Proof. exact (proj2 (@lem5006889 B y t h1)). Qed.
Lemma lem5029803 {B : Type'} (y : B) (t : B -> Prop) (h1 : term142 B y t) : term238 B y t.
Proof. exact (proj1 (@lem5006889 B y t h1)). Qed.
Lemma lem5029804 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (h1 : term129 A B s) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : term238 A x s) (h5 : term238 B y t) : (@FINITE B t) = (term352 A B y t x s).
Proof. exact (prop_ext (fun h6 : @FINITE B t => @lem5029799 A B x s y t h1 h2 h3 h4 h5) (fun h6 : term352 A B y t x s => @lem5006891 B t h3)). Qed.
Lemma lem5029805 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (h1 : term129 A B s) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : term238 A x s) (h5 : term238 B y t) : term352 A B y t x s.
Proof. exact (EQ_MP (@lem5029804 A B x s y t h1 h2 h3 h4 h5) (@lem5006891 B t h3)). Qed.
Lemma lem5029806 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (h1 : term129 A B s) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : term238 A x s) (h5 : term238 B y t) : (term238 B y t) = (term352 A B y t x s).
Proof. exact (prop_ext (fun h6 : term238 B y t => @lem5029805 A B x s y t h1 h2 h3 h4 h5) (fun h6 : term352 A B y t x s => @lem5006892 B y t h5)). Qed.
Lemma lem5029807 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (h1 : term129 A B s) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : term238 A x s) (h5 : term238 B y t) : term352 A B y t x s.
Proof. exact (EQ_MP (@lem5029806 A B x s y t h1 h2 h3 h4 h5) (@lem5006892 B y t h5)). Qed.
Lemma lem5029808 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (h1 : term129 A B s) (h2 : @FINITE A s) (h3 : term238 A x s) (h4 : term238 B y t) (h5 : term142 B y t) : (@FINITE B t) = (term352 A B y t x s).
Proof. exact (prop_ext (fun h6 : @FINITE B t => @lem5029807 A B x s y t h1 h2 h6 h3 h4) (fun h6 : term352 A B y t x s => @lem5029802 B y t h5)). Qed.
Lemma lem5029809 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (h1 : term129 A B s) (h2 : @FINITE A s) (h3 : term238 A x s) (h4 : term238 B y t) (h5 : term142 B y t) : term352 A B y t x s.
Proof. exact (EQ_MP (@lem5029808 A B x s y t h1 h2 h3 h4 h5) (@lem5029802 B y t h5)). Qed.
Lemma lem5029810 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (h1 : term129 A B s) (h2 : @FINITE A s) (h3 : term238 A x s) (h4 : term142 B y t) : (term238 B y t) = (term352 A B y t x s).
Proof. exact (prop_ext (fun h5 : term238 B y t => @lem5029809 A B x s y t h1 h2 h3 h5 h4) (fun h5 : term352 A B y t x s => @lem5029803 B y t h4)). Qed.
Lemma lem5029811 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (h1 : term129 A B s) (h2 : @FINITE A s) (h3 : term238 A x s) (h4 : term142 B y t) : term352 A B y t x s.
Proof. exact (EQ_MP (@lem5029810 A B x s y t h1 h2 h3 h4) (@lem5029803 B y t h4)). Qed.
Lemma lem5029812 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (h1 : term129 A B s) (h2 : @FINITE A s) (h3 : term238 A x s) (h4 : term304 A B x s y t) : (term142 B y t) = (term352 A B y t x s).
Proof. exact (prop_ext (fun h5 : term142 B y t => @lem5029811 A B x s y t h1 h2 h3 h5) (fun h5 : term352 A B y t x s => @lem5029800 A B x s y t h4)). Qed.
Lemma lem5029813 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (h1 : term129 A B s) (h2 : @FINITE A s) (h3 : term238 A x s) (h4 : term304 A B x s y t) : term352 A B y t x s.
Proof. exact (EQ_MP (@lem5029812 A B x s y t h1 h2 h3 h4) (@lem5029800 A B x s y t h4)). Qed.
Lemma lem5029814 {A B : Type'} (y : B) (t : B -> Prop) (x : A) (s : A -> Prop) (h1 : term129 A B s) (h2 : @FINITE A s) (h3 : term238 A x s) : term355 A B y t x s.
Proof. exact (fun h0 : term304 A B x s y t => @lem5029813 A B x s y t h1 h2 h3 h0). Qed.
Lemma lem5029815 {A B : Type'} (y : B) (t : B -> Prop) (x : A) (s : A -> Prop) (h1 : term129 A B s) (h2 : @FINITE A s) (h3 : term238 A x s) : term310 A B y t x s.
Proof. exact (EQ_MP (@lem5006887 A B y t x s) (@lem5029814 A B y t x s h1 h2 h3)). Qed.
Lemma lem5029820 {A B : Type'} (y : B) (x : A) (s : A -> Prop) (h1 : term129 A B s) (h2 : @FINITE A s) (h3 : term238 A x s) : term314 A B y x s.
Proof. exact (fun t : B -> Prop => @lem5029815 A B y t x s h1 h2 h3). Qed.
Lemma lem5029825 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term129 A B s) (h2 : @FINITE A s) (h3 : term238 A x s) : term318 A B x s.
Proof. exact (fun y : B => @lem5029820 A B y x s h1 h2 h3). Qed.
Lemma lem5029826 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term129 A B s) (h2 : @FINITE A s) (h3 : term238 A x s) : term320 A B x s.
Proof. exact (EQ_MP (@lem5003843 A B x s) (@lem5029825 A B x s h1 h2 h3)). Qed.
Lemma lem5029827 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term129 A B s) (h2 : @FINITE A s) (h3 : term238 A x s) : term286 A B x s.
Proof. exact (@lem5003643 A B x s (@lem5029826 A B x s h1 h2 h3)). Qed.
Lemma lem5029828 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term144 A B x s) : term142 A x s.
Proof. exact (proj2 (@lem5003606 A B x s h1)). Qed.
Lemma lem5029829 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term144 A B x s) : term129 A B s.
Proof. exact (proj1 (@lem5003606 A B x s h1)). Qed.
Lemma lem5029830 {A : Type'} (x : A) (s : A -> Prop) (h1 : term142 A x s) : @FINITE A s.
Proof. exact (proj2 (@lem5003607 A x s h1)). Qed.
Lemma lem5029831 {A : Type'} (x : A) (s : A -> Prop) (h1 : term142 A x s) : term238 A x s.
Proof. exact (proj1 (@lem5003607 A x s h1)). Qed.
Lemma lem5029832 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term129 A B s) (h2 : @FINITE A s) (h3 : term238 A x s) : (@FINITE A s) = (term286 A B x s).
Proof. exact (prop_ext (fun h4 : @FINITE A s => @lem5029827 A B x s h1 h2 h3) (fun h4 : term286 A B x s => @lem5003609 A s h2)). Qed.
Lemma lem5029833 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term129 A B s) (h2 : @FINITE A s) (h3 : term238 A x s) : term286 A B x s.
Proof. exact (EQ_MP (@lem5029832 A B x s h1 h2 h3) (@lem5003609 A s h2)). Qed.
Lemma lem5029834 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term129 A B s) (h2 : @FINITE A s) (h3 : term238 A x s) : (term238 A x s) = (term286 A B x s).
Proof. exact (prop_ext (fun h4 : term238 A x s => @lem5029833 A B x s h1 h2 h3) (fun h4 : term286 A B x s => @lem5003610 A x s h3)). Qed.
Lemma lem5029835 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term129 A B s) (h2 : @FINITE A s) (h3 : term238 A x s) : term286 A B x s.
Proof. exact (EQ_MP (@lem5029834 A B x s h1 h2 h3) (@lem5003610 A x s h3)). Qed.
Lemma lem5029836 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term129 A B s) (h2 : term238 A x s) (h3 : term142 A x s) : (@FINITE A s) = (term286 A B x s).
Proof. exact (prop_ext (fun h4 : @FINITE A s => @lem5029835 A B x s h1 h4 h2) (fun h4 : term286 A B x s => @lem5029830 A x s h3)). Qed.
Lemma lem5029837 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term129 A B s) (h2 : term238 A x s) (h3 : term142 A x s) : term286 A B x s.
Proof. exact (EQ_MP (@lem5029836 A B x s h1 h2 h3) (@lem5029830 A x s h3)). Qed.
Lemma lem5029838 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term129 A B s) (h2 : term142 A x s) : (term238 A x s) = (term286 A B x s).
Proof. exact (prop_ext (fun h3 : term238 A x s => @lem5029837 A B x s h1 h3 h2) (fun h3 : term286 A B x s => @lem5029831 A x s h2)). Qed.
Lemma lem5029839 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term129 A B s) (h2 : term142 A x s) : term286 A B x s.
Proof. exact (EQ_MP (@lem5029838 A B x s h1 h2) (@lem5029831 A x s h2)). Qed.
Lemma lem5029840 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term129 A B s) (h2 : term142 A x s) : (term129 A B s) = (term286 A B x s).
Proof. exact (prop_ext (fun h3 : term129 A B s => @lem5029839 A B x s h1 h2) (fun h3 : term286 A B x s => @lem5003608 A B s h1)). Qed.
Lemma lem5029841 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term129 A B s) (h2 : term142 A x s) : term286 A B x s.
Proof. exact (EQ_MP (@lem5029840 A B x s h1 h2) (@lem5003608 A B s h1)). Qed.
Lemma lem5029842 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term129 A B s) (h2 : term144 A B x s) : (term142 A x s) = (term286 A B x s).
Proof. exact (prop_ext (fun h3 : term142 A x s => @lem5029841 A B x s h1 h3) (fun h3 : term286 A B x s => @lem5029828 A B x s h2)). Qed.
Lemma lem5029843 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term129 A B s) (h2 : term144 A B x s) : term286 A B x s.
Proof. exact (EQ_MP (@lem5029842 A B x s h1 h2) (@lem5029828 A B x s h2)). Qed.
Lemma lem5029844 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term144 A B x s) : (term129 A B s) = (term286 A B x s).
Proof. exact (prop_ext (fun h2 : term129 A B s => @lem5029843 A B x s h2 h1) (fun h2 : term286 A B x s => @lem5029829 A B x s h1)). Qed.
Lemma lem5029845 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term144 A B x s) : term286 A B x s.
Proof. exact (EQ_MP (@lem5029844 A B x s h1) (@lem5029829 A B x s h1)). Qed.
Lemma lem5029846 {A B : Type'} (x : A) (s : A -> Prop) : term289 A B x s.
Proof. exact (fun h0 : term144 A B x s => @lem5029845 A B x s h0). Qed.
Lemma lem5029851 {A B : Type'} (x : A) : term291 A B x.
Proof. exact (fun s : A -> Prop => @lem5029846 A B x s). Qed.
Lemma lem5029856 {A B : Type'} : term293 A B.
Proof. exact (fun x : A => @lem5029851 A B x). Qed.
Lemma lem5029857 {A B : Type'} : term226 A B.
Proof. exact (EQ_MP (@lem5003605 A B) (@lem5029856 A B)). Qed.
Lemma lem5029858 {A B : Type'} : term160 A B.
Proof. exact (EQ_MP (@lem4980482 A B) (@lem5029857 A B)). Qed.
Lemma lem5029859 {A B : Type'} : term132 A B.
Proof. exact (@lem4980136 A B (@lem5029858 A B)). Qed.
Lemma lem5029860 {A B : Type'} : term94 A B.
Proof. exact (EQ_MP (@lem4980103 A B) (@lem5029859 A B)). Qed.
Lemma lem5029861 {A B : Type'} : term93 A B.
Proof. exact (EQ_MP (@lem4979877 A B) (@lem5029860 A B)). Qed.
