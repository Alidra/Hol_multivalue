Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NUMSUM_INJ_term_abbrevs.
Require Import EQ_MULT_LCANCEL_spec.
Require Import EVEN_DOUBLE_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NUMSUM_spec.
Require Import SUC_INJ_spec.
Require Import thm0_spec.
Require Import thm124233_spec.
Require Import thm13473_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm1833_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm32_spec.
Require Import thm521920_spec.
Require Import thm522075_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem1053437 : term0.
Proof. exact (EQ_MP (@lem521920) (@lem522075)). Qed.
Lemma lem1053438 : term1.
Proof. exact (proj2 (@lem1053437)). Qed.
Lemma lem1053439 : term2.
Proof. exact (proj2 (@lem1053438)). Qed.
Lemma lem1053440 : term3.
Proof. exact (proj2 (@lem1053439)). Qed.
Lemma lem1053482 : term4.
Proof. exact (proj1 (@lem1053440)). Qed.
Lemma lem1053483 (n : nat) : term5 n.
Proof. exact (@lem1053482 n). Qed.
Lemma lem1053484 (n : nat) : (term5 n) = (((BIT1 n) = 0) = False).
Proof. exact (eq_refl (term5 n)). Qed.
Lemma lem1053486 : term6.
Proof. exact (proj1 (@lem1053439)). Qed.
Lemma lem1053487 (n : nat) : term7 n.
Proof. exact (@lem1053486 n). Qed.
Lemma lem1053488 (n : nat) : (term7 n) = (((BIT0 n) = 0) = (n = 0)).
Proof. exact (eq_refl (term7 n)). Qed.
Lemma lem1053491 : term8.
Proof. exact (proj1 (@lem1053437)). Qed.
Lemma lem1053492 (m : nat) : term9 m.
Proof. exact (@lem1053491 m). Qed.
Lemma lem1053493 (m : nat) : (term9 m) = (term10 m).
Proof. exact (eq_refl (term9 m)). Qed.
Lemma lem1053494 (m : nat) : term10 m.
Proof. exact (EQ_MP (@lem1053493 m) (@lem1053492 m)). Qed.
Lemma lem1053495 (m : nat) (n : nat) : term11 m n.
Proof. exact (@lem1053494 m n). Qed.
Lemma lem1053496 (m : nat) (n : nat) : (term11 m n) = (((NUMERAL m) = (NUMERAL n)) = (m = n)).
Proof. exact (eq_refl (term11 m n)). Qed.
Lemma lem1053748 (m : nat) : term12 m.
Proof. exact (@lem84830 m). Qed.
Lemma lem1053749 (m : nat) : (term12 m) = (term13 m).
Proof. exact (eq_refl (term12 m)). Qed.
Lemma lem1053750 (m : nat) : term13 m.
Proof. exact (EQ_MP (@lem1053749 m) (@lem1053748 m)). Qed.
Lemma lem1053751 (m : nat) (n : nat) : term14 m n.
Proof. exact (@lem1053750 m n). Qed.
Lemma lem1053752 (m : nat) (n : nat) : (term14 m n) = (term15 m n).
Proof. exact (eq_refl (term14 m n)). Qed.
Lemma lem1053753 (m : nat) (n : nat) : term15 m n.
Proof. exact (EQ_MP (@lem1053752 m n) (@lem1053751 m n)). Qed.
Lemma lem1053754 (m : nat) (n : nat) (p : nat) : term16 m n p.
Proof. exact (@lem1053753 m n p). Qed.
Lemma lem1053755 (m : nat) (n : nat) (p : nat) : (term16 m n p) = (((Nat.mul m n) = (Nat.mul m p)) = (term17 m n p)).
Proof. exact (eq_refl (term16 m n p)). Qed.
Lemma lem1053757 (m : nat) : term18 m.
Proof. exact (@lem72973 m). Qed.
Lemma lem1053758 (m : nat) : (term18 m) = (term19 m).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem1053759 (m : nat) : term19 m.
Proof. exact (EQ_MP (@lem1053758 m) (@lem1053757 m)). Qed.
Lemma lem1053760 (m : nat) (n : nat) : term20 m n.
Proof. exact (@lem1053759 m n). Qed.
Lemma lem1053761 (m : nat) (n : nat) : (term20 m n) = (((S m) = (S n)) = (m = n)).
Proof. exact (eq_refl (term20 m n)). Qed.
Lemma lem1053763 (n : nat) : term21 n.
Proof. exact (@lem128384 n). Qed.
Lemma lem1053764 (n : nat) : (term21 n) = (term22 n).
Proof. exact (eq_refl (term21 n)). Qed.
Lemma lem1053765 (n : nat) : term22 n.
Proof. exact (EQ_MP (@lem1053764 n) (@lem1053763 n)). Qed.
Lemma lem1053766 (n : nat) : (term22 n) = ((term22 n) = True).
Proof. exact (@lem7 (term22 n)). Qed.
Lemma lem1053768 : term23.
Proof. exact (proj2 (@lem124233)). Qed.
Lemma lem1053769 (n : nat) : term24 n.
Proof. exact (@lem1053768 n). Qed.
Lemma lem1053770 (n : nat) : (term24 n) = ((term25 n) = (term26 n)).
Proof. exact (eq_refl (term24 n)). Qed.
Lemma lem1053773 (b : Prop) : term27 b.
Proof. exact (@lem1053103 b). Qed.
Lemma lem1053774 (b : Prop) : (term27 b) = (term28 b).
Proof. exact (eq_refl (term27 b)). Qed.
Lemma lem1053775 (b : Prop) : term28 b.
Proof. exact (EQ_MP (@lem1053774 b) (@lem1053773 b)). Qed.
Lemma lem1053776 (b : Prop) (x : nat) : term29 b x.
Proof. exact (@lem1053775 b x). Qed.
Lemma lem1053777 (b : Prop) (x : nat) : (term29 b x) = ((NUMSUM b x) = (term30 b x)).
Proof. exact (eq_refl (term29 b x)). Qed.
Lemma lem1053779 (b1 : Prop) (x1 : nat) (b2 : Prop) (x2 : nat) (h1 : (NUMSUM b1 x1) = (NUMSUM b2 x2)) : (NUMSUM b1 x1) = (NUMSUM b2 x2).
Proof. exact (h1). Qed.
Lemma lem1053780 (b1 : Prop) (b2 : Prop) (x1 : nat) (x2 : nat) (h1 : term31 b1 b2 x1 x2) : term31 b1 b2 x1 x2.
Proof. exact (h1). Qed.
Lemma lem1053794 (b1 : Prop) (b2 : Prop) (x1 : nat) (x2 : nat) (h1 : term31 b1 b2 x1 x2) : b1 = b2.
Proof. exact (proj1 (@lem1053780 b1 b2 x1 x2 h1)). Qed.
Lemma lem1053795 : NUMSUM = NUMSUM.
Proof. exact (eq_refl NUMSUM). Qed.
Lemma lem1053796 (b1 : Prop) (b2 : Prop) (x1 : nat) (x2 : nat) (h1 : term31 b1 b2 x1 x2) : (NUMSUM b1) = (NUMSUM b2).
Proof. exact (MK_COMB (@lem1053795) (@lem1053794 b1 b2 x1 x2 h1)). Qed.
Lemma lem1053798 (b1 : Prop) (b2 : Prop) (x1 : nat) (x2 : nat) (h1 : term31 b1 b2 x1 x2) : x1 = x2.
Proof. exact (proj2 (@lem1053780 b1 b2 x1 x2 h1)). Qed.
Lemma lem1053799 (b1 : Prop) (b2 : Prop) (x1 : nat) (x2 : nat) (h1 : term31 b1 b2 x1 x2) : (NUMSUM b1 x1) = (NUMSUM b2 x2).
Proof. exact (MK_COMB (@lem1053796 b1 b2 x1 x2 h1) (@lem1053798 b1 b2 x1 x2 h1)). Qed.
Lemma lem1053800 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1053801 (b1 : Prop) (b2 : Prop) (x1 : nat) (x2 : nat) (h1 : term31 b1 b2 x1 x2) : (term32 b1 x1) = (term32 b2 x2).
Proof. exact (MK_COMB (@lem1053800) (@lem1053799 b1 b2 x1 x2 h1)). Qed.
Lemma lem1053802 (b2 : Prop) (x2 : nat) : (NUMSUM b2 x2) = (NUMSUM b2 x2).
Proof. exact (eq_refl (NUMSUM b2 x2)). Qed.
Lemma lem1053803 (b1 : Prop) (b2 : Prop) (x1 : nat) (x2 : nat) (h1 : term31 b1 b2 x1 x2) : ((NUMSUM b1 x1) = (NUMSUM b2 x2)) = ((NUMSUM b2 x2) = (NUMSUM b2 x2)).
Proof. exact (MK_COMB (@lem1053801 b1 b2 x1 x2 h1) (@lem1053802 b2 x2)). Qed.
Lemma lem1053805 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1053806 (x : nat) : (x = x) = True.
Proof. exact (@lem1053805 nat x). Qed.
Lemma lem1053807 (b2 : Prop) (x2 : nat) : ((NUMSUM b2 x2) = (NUMSUM b2 x2)) = True.
Proof. exact (@lem1053806 (NUMSUM b2 x2)). Qed.
Lemma lem1053808 (b1 : Prop) (b2 : Prop) (x1 : nat) (x2 : nat) (h1 : term31 b1 b2 x1 x2) : ((NUMSUM b1 x1) = (NUMSUM b2 x2)) = True.
Proof. exact (TRANS (@lem1053803 b1 b2 x1 x2 h1) (@lem1053807 b2 x2)). Qed.
Lemma lem1053809 (b1 : Prop) (b2 : Prop) (x1 : nat) (x2 : nat) (h1 : term31 b1 b2 x1 x2) : True = ((NUMSUM b1 x1) = (NUMSUM b2 x2)).
Proof. exact (SYM (@lem1053808 b1 b2 x1 x2 h1)). Qed.
Lemma lem1053810 (b1 : Prop) (b2 : Prop) (x1 : nat) (x2 : nat) (h1 : term31 b1 b2 x1 x2) : (NUMSUM b1 x1) = (NUMSUM b2 x2).
Proof. exact (EQ_MP (@lem1053809 b1 b2 x1 x2 h1) (@lem0)). Qed.
Lemma lem1053814 (b : Prop) (x : nat) : (NUMSUM b x) = (term30 b x).
Proof. exact (EQ_MP (@lem1053777 b x) (@lem1053776 b x)). Qed.
Lemma lem1053815 (b1 : Prop) (x1 : nat) : (NUMSUM b1 x1) = (term30 b1 x1).
Proof. exact (@lem1053814 b1 x1). Qed.
Lemma lem1053816 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1053817 (b1 : Prop) (x1 : nat) : (term32 b1 x1) = (term33 b1 x1).
Proof. exact (MK_COMB (@lem1053816) (@lem1053815 b1 x1)). Qed.
Lemma lem1053819 (b : Prop) (x : nat) : (NUMSUM b x) = (term30 b x).
Proof. exact (EQ_MP (@lem1053777 b x) (@lem1053776 b x)). Qed.
Lemma lem1053820 (b2 : Prop) (x2 : nat) : (NUMSUM b2 x2) = (term30 b2 x2).
Proof. exact (@lem1053819 b2 x2). Qed.
Lemma lem1053821 (b1 : Prop) (x1 : nat) (b2 : Prop) (x2 : nat) : ((NUMSUM b1 x1) = (NUMSUM b2 x2)) = ((term30 b1 x1) = (term30 b2 x2)).
Proof. exact (MK_COMB (@lem1053817 b1 x1) (@lem1053820 b2 x2)). Qed.
Lemma lem1053824 (b1 : Prop) (x1 : nat) (b2 : Prop) (x2 : nat) (h1 : (NUMSUM b1 x1) = (NUMSUM b2 x2)) : (term30 b1 x1) = (term30 b2 x2).
Proof. exact (EQ_MP (@lem1053821 b1 x1 b2 x2) (@lem1053779 b1 x1 b2 x2 h1)). Qed.
Lemma lem1053825 (b1 : Prop) (x1 : nat) (b2 : Prop) (x2 : nat) (h1 : (term30 b1 x1) = (term30 b2 x2)) : (term30 b1 x1) = (term30 b2 x2).
Proof. exact (h1). Qed.
Lemma lem1053826 : Coq.Arith.PeanoNat.Nat.Even = Coq.Arith.PeanoNat.Nat.Even.
Proof. exact (eq_refl Coq.Arith.PeanoNat.Nat.Even). Qed.
Lemma lem1053827 (b1 : Prop) (x1 : nat) (b2 : Prop) (x2 : nat) (h1 : (term30 b1 x1) = (term30 b2 x2)) : (term34 b1 x1) = (term34 b2 x2).
Proof. exact (MK_COMB (@lem1053826) (@lem1053825 b1 x1 b2 x2 h1)). Qed.
Lemma lem1053828 (_474 : nat) (_475 : Prop) (_476 : nat -> Prop) (_477 : nat) : (term35 _476 _475 _474 _477) = (term36 _474 _475 _476 _477).
Proof. exact (@lem13473 nat _474 _475 _476 _477). Qed.
Lemma lem1053829 (_474 : nat) (_475 : Prop) (b1 : Prop) (b2 : Prop) (x1 : nat) (x2 : nat) (_477 : nat) : (term37 b1 b2 x1 x2 _475 _474 _477) = (term38 _474 _475 b1 b2 x1 x2 _477).
Proof. exact (@lem1053828 _474 _475 (term39 b1 b2 x1 x2) _477). Qed.
Lemma lem1053830 (b1 : Prop) (b2 : Prop) (x2 : nat) (x1 : nat) : (term40 b2 x2 b1 x1) = (term41 b1 b2 x2 x1).
Proof. exact (@lem1053829 (term42 x1) b1 b1 b2 x1 x2 (term43 x1)). Qed.
Lemma lem1053831 (b1 : Prop) (b2 : Prop) (x1 : nat) (x2 : nat) : (term44 b1 b2 x2 x1) = (term45 b1 b2 x1 x2).
Proof. exact (eq_refl (term44 b1 b2 x2 x1)). Qed.
Lemma lem1053832 (b1 : Prop) : (term46 b1) = (term46 b1).
Proof. exact (eq_refl (term46 b1)). Qed.
Lemma lem1053833 (b1 : Prop) (b2 : Prop) (x1 : nat) (x2 : nat) : (term47 b1 b2 x2 x1) = (term48 b1 b2 x1 x2).
Proof. exact (MK_COMB (@lem1053832 b1) (@lem1053831 b1 b2 x1 x2)). Qed.
Lemma lem1053834 (b1 : Prop) (b2 : Prop) (x1 : nat) (x2 : nat) : (term49 b1 b2 x2 x1) = (term50 b1 b2 x1 x2).
Proof. exact (eq_refl (term49 b1 b2 x2 x1)). Qed.
Lemma lem1053835 (b1 : Prop) : (imp b1) = (imp b1).
Proof. exact (eq_refl (imp b1)). Qed.
Lemma lem1053836 (b1 : Prop) (b2 : Prop) (x1 : nat) (x2 : nat) : (term51 b1 b2 x2 x1) = (term52 b1 b2 x1 x2).
Proof. exact (MK_COMB (@lem1053835 b1) (@lem1053834 b1 b2 x1 x2)). Qed.
Lemma lem1053837 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1053838 (b1 : Prop) (b2 : Prop) (x1 : nat) (x2 : nat) : (term53 b1 b2 x2 x1) = (term54 b1 b2 x1 x2).
Proof. exact (MK_COMB (@lem1053837) (@lem1053836 b1 b2 x1 x2)). Qed.
Lemma lem1053839 (b1 : Prop) (b2 : Prop) (x1 : nat) (x2 : nat) : (term41 b1 b2 x2 x1) = (term55 b1 b2 x1 x2).
Proof. exact (MK_COMB (@lem1053838 b1 b2 x1 x2) (@lem1053833 b1 b2 x1 x2)). Qed.
Lemma lem1053840 (b1 : Prop) (b2 : Prop) (x1 : nat) (x2 : nat) : (term40 b2 x2 b1 x1) = (term56 b1 b2 x1 x2).
Proof. exact (eq_refl (term40 b2 x2 b1 x1)). Qed.
Lemma lem1053841 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1053842 (b1 : Prop) (b2 : Prop) (x1 : nat) (x2 : nat) : (term57 b2 x2 b1 x1) = (term58 b1 b2 x1 x2).
Proof. exact (MK_COMB (@lem1053841) (@lem1053840 b1 b2 x1 x2)). Qed.
Lemma lem1053843 (b1 : Prop) (b2 : Prop) (x1 : nat) (x2 : nat) : ((term40 b2 x2 b1 x1) = (term41 b1 b2 x2 x1)) = ((term56 b1 b2 x1 x2) = (term55 b1 b2 x1 x2)).
Proof. exact (MK_COMB (@lem1053842 b1 b2 x1 x2) (@lem1053839 b1 b2 x1 x2)). Qed.
Lemma lem1053844 (b1 : Prop) (b2 : Prop) (x1 : nat) (x2 : nat) : (term56 b1 b2 x1 x2) = (term55 b1 b2 x1 x2).
Proof. exact (EQ_MP (@lem1053843 b1 b2 x1 x2) (@lem1053830 b1 b2 x2 x1)). Qed.
Lemma lem1053845 (b1 : Prop) (b2 : Prop) (x1 : nat) (x2 : nat) : (term55 b1 b2 x1 x2) = (term56 b1 b2 x1 x2).
Proof. exact (SYM (@lem1053844 b1 b2 x1 x2)). Qed.
Lemma lem1053846 (b1 : Prop) (h1 : b1) : b1.
Proof. exact (h1). Qed.
Lemma lem1053847 (b1 : Prop) : b1 = (b1 = True).
Proof. exact (@lem7 b1). Qed.
Lemma lem1053848 (b1 : Prop) (h1 : b1) : b1 = True.
Proof. exact (EQ_MP (@lem1053847 b1) (@lem1053846 b1 h1)). Qed.
Lemma lem1053849 (b2 : Prop) (x1 : nat) (x2 : nat) : (term59 b2 x1 x2) = (term59 b2 x1 x2).
Proof. exact (eq_refl (term59 b2 x1 x2)). Qed.
Lemma lem1053850 (b2 : Prop) (x1 : nat) (x2 : nat) (b1 : Prop) (h1 : b1) : (term60 b2 x1 x2 b1) = (term61 b2 x1 x2).
Proof. exact (MK_COMB (@lem1053849 b2 x1 x2) (@lem1053848 b1 h1)). Qed.
Lemma lem1053851 (b2 : Prop) (x1 : nat) (x2 : nat) : (term61 b2 x1 x2) = (term62 b2 x1 x2).
Proof. exact (eq_refl (term61 b2 x1 x2)). Qed.
Lemma lem1053852 (b2 : Prop) (x1 : nat) (x2 : nat) (b1 : Prop) : (term63 b2 x1 x2 b1) = (term63 b2 x1 x2 b1).
Proof. exact (eq_refl (term63 b2 x1 x2 b1)). Qed.
Lemma lem1053853 (b1 : Prop) (b2 : Prop) (x1 : nat) (x2 : nat) : ((term60 b2 x1 x2 b1) = (term61 b2 x1 x2)) = ((term60 b2 x1 x2 b1) = (term62 b2 x1 x2)).
Proof. exact (MK_COMB (@lem1053852 b2 x1 x2 b1) (@lem1053851 b2 x1 x2)). Qed.
Lemma lem1053854 (b1 : Prop) (b2 : Prop) (x1 : nat) (x2 : nat) : (term60 b2 x1 x2 b1) = (term50 b1 b2 x1 x2).
Proof. exact (eq_refl (term60 b2 x1 x2 b1)). Qed.
Lemma lem1053855 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1053856 (b1 : Prop) (b2 : Prop) (x1 : nat) (x2 : nat) : (term63 b2 x1 x2 b1) = (term64 b1 b2 x1 x2).
Proof. exact (MK_COMB (@lem1053855) (@lem1053854 b1 b2 x1 x2)). Qed.
Lemma lem1053857 (b2 : Prop) (x1 : nat) (x2 : nat) : (term62 b2 x1 x2) = (term62 b2 x1 x2).
Proof. exact (eq_refl (term62 b2 x1 x2)). Qed.
Lemma lem1053858 (b1 : Prop) (b2 : Prop) (x1 : nat) (x2 : nat) : ((term60 b2 x1 x2 b1) = (term62 b2 x1 x2)) = ((term50 b1 b2 x1 x2) = (term62 b2 x1 x2)).
Proof. exact (MK_COMB (@lem1053856 b1 b2 x1 x2) (@lem1053857 b2 x1 x2)). Qed.
Lemma lem1053859 (b1 : Prop) (b2 : Prop) (x1 : nat) (x2 : nat) : ((term60 b2 x1 x2 b1) = (term61 b2 x1 x2)) = ((term50 b1 b2 x1 x2) = (term62 b2 x1 x2)).
Proof. exact (TRANS (@lem1053853 b1 b2 x1 x2) (@lem1053858 b1 b2 x1 x2)). Qed.
Lemma lem1053860 (b2 : Prop) (x1 : nat) (x2 : nat) (b1 : Prop) (h1 : b1) : (term50 b1 b2 x1 x2) = (term62 b2 x1 x2).
Proof. exact (EQ_MP (@lem1053859 b1 b2 x1 x2) (@lem1053850 b2 x1 x2 b1 h1)). Qed.
Lemma lem1053861 (b2 : Prop) (x1 : nat) (x2 : nat) (b1 : Prop) (h1 : b1) : (term62 b2 x1 x2) = (term50 b1 b2 x1 x2).
Proof. exact (SYM (@lem1053860 b2 x1 x2 b1 h1)). Qed.
Lemma lem1053862 (b1 : Prop) (h1 : ~ b1) : ~ b1.
Proof. exact (h1). Qed.
Lemma lem1053863 (b1 : Prop) : term65 b1.
Proof. exact (@lem82 b1). Qed.
Lemma lem1053864 (b1 : Prop) (h1 : ~ b1) : b1 = False.
Proof. exact (@lem1053863 b1 (@lem1053862 b1 h1)). Qed.
Lemma lem1053865 (b2 : Prop) (x1 : nat) (x2 : nat) : (term66 b2 x1 x2) = (term66 b2 x1 x2).
Proof. exact (eq_refl (term66 b2 x1 x2)). Qed.
Lemma lem1053866 (b2 : Prop) (x1 : nat) (x2 : nat) (b1 : Prop) (h1 : ~ b1) : (term67 b2 x1 x2 b1) = (term68 b2 x1 x2).
Proof. exact (MK_COMB (@lem1053865 b2 x1 x2) (@lem1053864 b1 h1)). Qed.
Lemma lem1053867 (b2 : Prop) (x1 : nat) (x2 : nat) : (term68 b2 x1 x2) = (term69 b2 x1 x2).
Proof. exact (eq_refl (term68 b2 x1 x2)). Qed.
Lemma lem1053868 (b2 : Prop) (x1 : nat) (x2 : nat) (b1 : Prop) : (term70 b2 x1 x2 b1) = (term70 b2 x1 x2 b1).
Proof. exact (eq_refl (term70 b2 x1 x2 b1)). Qed.
Lemma lem1053869 (b1 : Prop) (b2 : Prop) (x1 : nat) (x2 : nat) : ((term67 b2 x1 x2 b1) = (term68 b2 x1 x2)) = ((term67 b2 x1 x2 b1) = (term69 b2 x1 x2)).
Proof. exact (MK_COMB (@lem1053868 b2 x1 x2 b1) (@lem1053867 b2 x1 x2)). Qed.
Lemma lem1053870 (b1 : Prop) (b2 : Prop) (x1 : nat) (x2 : nat) : (term67 b2 x1 x2 b1) = (term45 b1 b2 x1 x2).
Proof. exact (eq_refl (term67 b2 x1 x2 b1)). Qed.
Lemma lem1053871 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1053872 (b1 : Prop) (b2 : Prop) (x1 : nat) (x2 : nat) : (term70 b2 x1 x2 b1) = (term71 b1 b2 x1 x2).
Proof. exact (MK_COMB (@lem1053871) (@lem1053870 b1 b2 x1 x2)). Qed.
Lemma lem1053873 (b2 : Prop) (x1 : nat) (x2 : nat) : (term69 b2 x1 x2) = (term69 b2 x1 x2).
Proof. exact (eq_refl (term69 b2 x1 x2)). Qed.
Lemma lem1053874 (b1 : Prop) (b2 : Prop) (x1 : nat) (x2 : nat) : ((term67 b2 x1 x2 b1) = (term69 b2 x1 x2)) = ((term45 b1 b2 x1 x2) = (term69 b2 x1 x2)).
Proof. exact (MK_COMB (@lem1053872 b1 b2 x1 x2) (@lem1053873 b2 x1 x2)). Qed.
Lemma lem1053875 (b1 : Prop) (b2 : Prop) (x1 : nat) (x2 : nat) : ((term67 b2 x1 x2 b1) = (term68 b2 x1 x2)) = ((term45 b1 b2 x1 x2) = (term69 b2 x1 x2)).
Proof. exact (TRANS (@lem1053869 b1 b2 x1 x2) (@lem1053874 b1 b2 x1 x2)). Qed.
Lemma lem1053876 (b2 : Prop) (x1 : nat) (x2 : nat) (b1 : Prop) (h1 : ~ b1) : (term45 b1 b2 x1 x2) = (term69 b2 x1 x2).
Proof. exact (EQ_MP (@lem1053875 b1 b2 x1 x2) (@lem1053866 b2 x1 x2 b1 h1)). Qed.
Lemma lem1053877 (b2 : Prop) (x1 : nat) (x2 : nat) (b1 : Prop) (h1 : ~ b1) : (term69 b2 x1 x2) = (term45 b1 b2 x1 x2).
Proof. exact (SYM (@lem1053876 b2 x1 x2 b1 h1)). Qed.
Lemma lem1053878 (_474 : nat) (_475 : Prop) (_476 : nat -> Prop) (_477 : nat) : (term35 _476 _475 _474 _477) = (term36 _474 _475 _476 _477).
Proof. exact (@lem13473 nat _474 _475 _476 _477). Qed.
Lemma lem1053879 (_474 : nat) (_475 : Prop) (b2 : Prop) (x1 : nat) (x2 : nat) (_477 : nat) : (term72 b2 x1 x2 _475 _474 _477) = (term73 _474 _475 b2 x1 x2 _477).
Proof. exact (@lem1053878 _474 _475 (term74 b2 x1 x2) _477). Qed.
Lemma lem1053880 (b2 : Prop) (x1 : nat) (x2 : nat) : (term75 x1 b2 x2) = (term76 b2 x1 x2).
Proof. exact (@lem1053879 (term42 x2) b2 b2 x1 x2 (term43 x2)). Qed.
Lemma lem1053881 (b2 : Prop) (x1 : nat) (x2 : nat) : (term77 b2 x1 x2) = (term78 b2 x1 x2).
Proof. exact (eq_refl (term77 b2 x1 x2)). Qed.
Lemma lem1053882 (b2 : Prop) : (term46 b2) = (term46 b2).
Proof. exact (eq_refl (term46 b2)). Qed.
Lemma lem1053883 (b2 : Prop) (x1 : nat) (x2 : nat) : (term79 b2 x1 x2) = (term80 b2 x1 x2).
Proof. exact (MK_COMB (@lem1053882 b2) (@lem1053881 b2 x1 x2)). Qed.
Lemma lem1053884 (b2 : Prop) (x1 : nat) (x2 : nat) : (term81 b2 x1 x2) = (term82 b2 x1 x2).
Proof. exact (eq_refl (term81 b2 x1 x2)). Qed.
Lemma lem1053885 (b2 : Prop) : (imp b2) = (imp b2).
Proof. exact (eq_refl (imp b2)). Qed.
Lemma lem1053886 (b2 : Prop) (x1 : nat) (x2 : nat) : (term83 b2 x1 x2) = (term84 b2 x1 x2).
Proof. exact (MK_COMB (@lem1053885 b2) (@lem1053884 b2 x1 x2)). Qed.
Lemma lem1053887 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1053888 (b2 : Prop) (x1 : nat) (x2 : nat) : (term85 b2 x1 x2) = (term86 b2 x1 x2).
Proof. exact (MK_COMB (@lem1053887) (@lem1053886 b2 x1 x2)). Qed.
Lemma lem1053889 (b2 : Prop) (x1 : nat) (x2 : nat) : (term76 b2 x1 x2) = (term87 b2 x1 x2).
Proof. exact (MK_COMB (@lem1053888 b2 x1 x2) (@lem1053883 b2 x1 x2)). Qed.
Lemma lem1053890 (b2 : Prop) (x1 : nat) (x2 : nat) : (term75 x1 b2 x2) = (term62 b2 x1 x2).
Proof. exact (eq_refl (term75 x1 b2 x2)). Qed.
Lemma lem1053891 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1053892 (b2 : Prop) (x1 : nat) (x2 : nat) : (term88 x1 b2 x2) = (term89 b2 x1 x2).
Proof. exact (MK_COMB (@lem1053891) (@lem1053890 b2 x1 x2)). Qed.
Lemma lem1053893 (b2 : Prop) (x1 : nat) (x2 : nat) : ((term75 x1 b2 x2) = (term76 b2 x1 x2)) = ((term62 b2 x1 x2) = (term87 b2 x1 x2)).
Proof. exact (MK_COMB (@lem1053892 b2 x1 x2) (@lem1053889 b2 x1 x2)). Qed.
Lemma lem1053894 (b2 : Prop) (x1 : nat) (x2 : nat) : (term62 b2 x1 x2) = (term87 b2 x1 x2).
Proof. exact (EQ_MP (@lem1053893 b2 x1 x2) (@lem1053880 b2 x1 x2)). Qed.
Lemma lem1053895 (b2 : Prop) (x1 : nat) (x2 : nat) : (term87 b2 x1 x2) = (term62 b2 x1 x2).
Proof. exact (SYM (@lem1053894 b2 x1 x2)). Qed.
Lemma lem1053896 (b2 : Prop) (h1 : b2) : b2.
Proof. exact (h1). Qed.
Lemma lem1053897 (b2 : Prop) : b2 = (b2 = True).
Proof. exact (@lem7 b2). Qed.
Lemma lem1053898 (b2 : Prop) (h1 : b2) : b2 = True.
Proof. exact (EQ_MP (@lem1053897 b2) (@lem1053896 b2 h1)). Qed.
Lemma lem1053899 (x1 : nat) (x2 : nat) : (term90 x1 x2) = (term90 x1 x2).
Proof. exact (eq_refl (term90 x1 x2)). Qed.
Lemma lem1053900 (x1 : nat) (x2 : nat) (b2 : Prop) (h1 : b2) : (term91 x1 x2 b2) = (term92 x1 x2).
Proof. exact (MK_COMB (@lem1053899 x1 x2) (@lem1053898 b2 h1)). Qed.
Lemma lem1053901 (x1 : nat) (x2 : nat) : (term92 x1 x2) = (term93 x1 x2).
Proof. exact (eq_refl (term92 x1 x2)). Qed.
Lemma lem1053902 (x1 : nat) (x2 : nat) (b2 : Prop) : (term94 x1 x2 b2) = (term94 x1 x2 b2).
Proof. exact (eq_refl (term94 x1 x2 b2)). Qed.
Lemma lem1053903 (b2 : Prop) (x1 : nat) (x2 : nat) : ((term91 x1 x2 b2) = (term92 x1 x2)) = ((term91 x1 x2 b2) = (term93 x1 x2)).
Proof. exact (MK_COMB (@lem1053902 x1 x2 b2) (@lem1053901 x1 x2)). Qed.
Lemma lem1053904 (b2 : Prop) (x1 : nat) (x2 : nat) : (term91 x1 x2 b2) = (term82 b2 x1 x2).
Proof. exact (eq_refl (term91 x1 x2 b2)). Qed.
Lemma lem1053905 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1053906 (b2 : Prop) (x1 : nat) (x2 : nat) : (term94 x1 x2 b2) = (term95 b2 x1 x2).
Proof. exact (MK_COMB (@lem1053905) (@lem1053904 b2 x1 x2)). Qed.
Lemma lem1053907 (x1 : nat) (x2 : nat) : (term93 x1 x2) = (term93 x1 x2).
Proof. exact (eq_refl (term93 x1 x2)). Qed.
Lemma lem1053908 (b2 : Prop) (x1 : nat) (x2 : nat) : ((term91 x1 x2 b2) = (term93 x1 x2)) = ((term82 b2 x1 x2) = (term93 x1 x2)).
Proof. exact (MK_COMB (@lem1053906 b2 x1 x2) (@lem1053907 x1 x2)). Qed.
Lemma lem1053909 (b2 : Prop) (x1 : nat) (x2 : nat) : ((term91 x1 x2 b2) = (term92 x1 x2)) = ((term82 b2 x1 x2) = (term93 x1 x2)).
Proof. exact (TRANS (@lem1053903 b2 x1 x2) (@lem1053908 b2 x1 x2)). Qed.
Lemma lem1053910 (x1 : nat) (x2 : nat) (b2 : Prop) (h1 : b2) : (term82 b2 x1 x2) = (term93 x1 x2).
Proof. exact (EQ_MP (@lem1053909 b2 x1 x2) (@lem1053900 x1 x2 b2 h1)). Qed.
Lemma lem1053911 (x1 : nat) (x2 : nat) (b2 : Prop) (h1 : b2) : (term93 x1 x2) = (term82 b2 x1 x2).
Proof. exact (SYM (@lem1053910 x1 x2 b2 h1)). Qed.
Lemma lem1053912 (b2 : Prop) (h1 : ~ b2) : ~ b2.
Proof. exact (h1). Qed.
Lemma lem1053913 (b2 : Prop) : term65 b2.
Proof. exact (@lem82 b2). Qed.
Lemma lem1053914 (b2 : Prop) (h1 : ~ b2) : b2 = False.
Proof. exact (@lem1053913 b2 (@lem1053912 b2 h1)). Qed.
Lemma lem1053915 (x1 : nat) (x2 : nat) : (term96 x1 x2) = (term96 x1 x2).
Proof. exact (eq_refl (term96 x1 x2)). Qed.
Lemma lem1053916 (x1 : nat) (x2 : nat) (b2 : Prop) (h1 : ~ b2) : (term97 x1 x2 b2) = (term98 x1 x2).
Proof. exact (MK_COMB (@lem1053915 x1 x2) (@lem1053914 b2 h1)). Qed.
Lemma lem1053917 (x1 : nat) (x2 : nat) : (term98 x1 x2) = (term99 x1 x2).
Proof. exact (eq_refl (term98 x1 x2)). Qed.
Lemma lem1053918 (x1 : nat) (x2 : nat) (b2 : Prop) : (term100 x1 x2 b2) = (term100 x1 x2 b2).
Proof. exact (eq_refl (term100 x1 x2 b2)). Qed.
Lemma lem1053919 (b2 : Prop) (x1 : nat) (x2 : nat) : ((term97 x1 x2 b2) = (term98 x1 x2)) = ((term97 x1 x2 b2) = (term99 x1 x2)).
Proof. exact (MK_COMB (@lem1053918 x1 x2 b2) (@lem1053917 x1 x2)). Qed.
Lemma lem1053920 (b2 : Prop) (x1 : nat) (x2 : nat) : (term97 x1 x2 b2) = (term78 b2 x1 x2).
Proof. exact (eq_refl (term97 x1 x2 b2)). Qed.
Lemma lem1053921 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1053922 (b2 : Prop) (x1 : nat) (x2 : nat) : (term100 x1 x2 b2) = (term101 b2 x1 x2).
Proof. exact (MK_COMB (@lem1053921) (@lem1053920 b2 x1 x2)). Qed.
Lemma lem1053923 (x1 : nat) (x2 : nat) : (term99 x1 x2) = (term99 x1 x2).
Proof. exact (eq_refl (term99 x1 x2)). Qed.
Lemma lem1053924 (b2 : Prop) (x1 : nat) (x2 : nat) : ((term97 x1 x2 b2) = (term99 x1 x2)) = ((term78 b2 x1 x2) = (term99 x1 x2)).
Proof. exact (MK_COMB (@lem1053922 b2 x1 x2) (@lem1053923 x1 x2)). Qed.
Lemma lem1053925 (b2 : Prop) (x1 : nat) (x2 : nat) : ((term97 x1 x2 b2) = (term98 x1 x2)) = ((term78 b2 x1 x2) = (term99 x1 x2)).
Proof. exact (TRANS (@lem1053919 b2 x1 x2) (@lem1053924 b2 x1 x2)). Qed.
Lemma lem1053926 (x1 : nat) (x2 : nat) (b2 : Prop) (h1 : ~ b2) : (term78 b2 x1 x2) = (term99 x1 x2).
Proof. exact (EQ_MP (@lem1053925 b2 x1 x2) (@lem1053916 x1 x2 b2 h1)). Qed.
Lemma lem1053927 (x1 : nat) (x2 : nat) (b2 : Prop) (h1 : ~ b2) : (term99 x1 x2) = (term78 b2 x1 x2).
Proof. exact (SYM (@lem1053926 x1 x2 b2 h1)). Qed.
Lemma lem1053928 (_474 : nat) (_475 : Prop) (_476 : nat -> Prop) (_477 : nat) : (term35 _476 _475 _474 _477) = (term36 _474 _475 _476 _477).
Proof. exact (@lem13473 nat _474 _475 _476 _477). Qed.
Lemma lem1053929 (_474 : nat) (_475 : Prop) (b2 : Prop) (x1 : nat) (x2 : nat) (_477 : nat) : (term102 b2 x1 x2 _475 _474 _477) = (term103 _474 _475 b2 x1 x2 _477).
Proof. exact (@lem1053928 _474 _475 (term104 b2 x1 x2) _477). Qed.
Lemma lem1053930 (b2 : Prop) (x1 : nat) (x2 : nat) : (term105 x1 b2 x2) = (term106 b2 x1 x2).
Proof. exact (@lem1053929 (term42 x2) b2 b2 x1 x2 (term43 x2)). Qed.
Lemma lem1053931 (b2 : Prop) (x1 : nat) (x2 : nat) : (term107 b2 x1 x2) = (term108 b2 x1 x2).
Proof. exact (eq_refl (term107 b2 x1 x2)). Qed.
Lemma lem1053932 (b2 : Prop) : (term46 b2) = (term46 b2).
Proof. exact (eq_refl (term46 b2)). Qed.
Lemma lem1053933 (b2 : Prop) (x1 : nat) (x2 : nat) : (term109 b2 x1 x2) = (term110 b2 x1 x2).
Proof. exact (MK_COMB (@lem1053932 b2) (@lem1053931 b2 x1 x2)). Qed.
Lemma lem1053934 (b2 : Prop) (x1 : nat) (x2 : nat) : (term111 b2 x1 x2) = (term112 b2 x1 x2).
Proof. exact (eq_refl (term111 b2 x1 x2)). Qed.
Lemma lem1053935 (b2 : Prop) : (imp b2) = (imp b2).
Proof. exact (eq_refl (imp b2)). Qed.
Lemma lem1053936 (b2 : Prop) (x1 : nat) (x2 : nat) : (term113 b2 x1 x2) = (term114 b2 x1 x2).
Proof. exact (MK_COMB (@lem1053935 b2) (@lem1053934 b2 x1 x2)). Qed.
Lemma lem1053937 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1053938 (b2 : Prop) (x1 : nat) (x2 : nat) : (term115 b2 x1 x2) = (term116 b2 x1 x2).
Proof. exact (MK_COMB (@lem1053937) (@lem1053936 b2 x1 x2)). Qed.
Lemma lem1053939 (b2 : Prop) (x1 : nat) (x2 : nat) : (term106 b2 x1 x2) = (term117 b2 x1 x2).
Proof. exact (MK_COMB (@lem1053938 b2 x1 x2) (@lem1053933 b2 x1 x2)). Qed.
Lemma lem1053940 (b2 : Prop) (x1 : nat) (x2 : nat) : (term105 x1 b2 x2) = (term69 b2 x1 x2).
Proof. exact (eq_refl (term105 x1 b2 x2)). Qed.
Lemma lem1053941 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1053942 (b2 : Prop) (x1 : nat) (x2 : nat) : (term118 x1 b2 x2) = (term119 b2 x1 x2).
Proof. exact (MK_COMB (@lem1053941) (@lem1053940 b2 x1 x2)). Qed.
Lemma lem1053943 (b2 : Prop) (x1 : nat) (x2 : nat) : ((term105 x1 b2 x2) = (term106 b2 x1 x2)) = ((term69 b2 x1 x2) = (term117 b2 x1 x2)).
Proof. exact (MK_COMB (@lem1053942 b2 x1 x2) (@lem1053939 b2 x1 x2)). Qed.
Lemma lem1053944 (b2 : Prop) (x1 : nat) (x2 : nat) : (term69 b2 x1 x2) = (term117 b2 x1 x2).
Proof. exact (EQ_MP (@lem1053943 b2 x1 x2) (@lem1053930 b2 x1 x2)). Qed.
Lemma lem1053945 (b2 : Prop) (x1 : nat) (x2 : nat) : (term117 b2 x1 x2) = (term69 b2 x1 x2).
Proof. exact (SYM (@lem1053944 b2 x1 x2)). Qed.
Lemma lem1053946 (b2 : Prop) (h1 : b2) : b2.
Proof. exact (h1). Qed.
Lemma lem1053947 (b2 : Prop) : b2 = (b2 = True).
Proof. exact (@lem7 b2). Qed.
Lemma lem1053948 (b2 : Prop) (h1 : b2) : b2 = True.
Proof. exact (EQ_MP (@lem1053947 b2) (@lem1053946 b2 h1)). Qed.
Lemma lem1053949 (x1 : nat) (x2 : nat) : (term120 x1 x2) = (term120 x1 x2).
Proof. exact (eq_refl (term120 x1 x2)). Qed.
Lemma lem1053950 (x1 : nat) (x2 : nat) (b2 : Prop) (h1 : b2) : (term121 x1 x2 b2) = (term122 x1 x2).
Proof. exact (MK_COMB (@lem1053949 x1 x2) (@lem1053948 b2 h1)). Qed.
Lemma lem1053951 (x1 : nat) (x2 : nat) : (term122 x1 x2) = (term123 x1 x2).
Proof. exact (eq_refl (term122 x1 x2)). Qed.
Lemma lem1053952 (x1 : nat) (x2 : nat) (b2 : Prop) : (term124 x1 x2 b2) = (term124 x1 x2 b2).
Proof. exact (eq_refl (term124 x1 x2 b2)). Qed.
Lemma lem1053953 (b2 : Prop) (x1 : nat) (x2 : nat) : ((term121 x1 x2 b2) = (term122 x1 x2)) = ((term121 x1 x2 b2) = (term123 x1 x2)).
Proof. exact (MK_COMB (@lem1053952 x1 x2 b2) (@lem1053951 x1 x2)). Qed.
Lemma lem1053954 (b2 : Prop) (x1 : nat) (x2 : nat) : (term121 x1 x2 b2) = (term112 b2 x1 x2).
Proof. exact (eq_refl (term121 x1 x2 b2)). Qed.
Lemma lem1053955 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1053956 (b2 : Prop) (x1 : nat) (x2 : nat) : (term124 x1 x2 b2) = (term125 b2 x1 x2).
Proof. exact (MK_COMB (@lem1053955) (@lem1053954 b2 x1 x2)). Qed.
Lemma lem1053957 (x1 : nat) (x2 : nat) : (term123 x1 x2) = (term123 x1 x2).
Proof. exact (eq_refl (term123 x1 x2)). Qed.
Lemma lem1053958 (b2 : Prop) (x1 : nat) (x2 : nat) : ((term121 x1 x2 b2) = (term123 x1 x2)) = ((term112 b2 x1 x2) = (term123 x1 x2)).
Proof. exact (MK_COMB (@lem1053956 b2 x1 x2) (@lem1053957 x1 x2)). Qed.
Lemma lem1053959 (b2 : Prop) (x1 : nat) (x2 : nat) : ((term121 x1 x2 b2) = (term122 x1 x2)) = ((term112 b2 x1 x2) = (term123 x1 x2)).
Proof. exact (TRANS (@lem1053953 b2 x1 x2) (@lem1053958 b2 x1 x2)). Qed.
Lemma lem1053960 (x1 : nat) (x2 : nat) (b2 : Prop) (h1 : b2) : (term112 b2 x1 x2) = (term123 x1 x2).
Proof. exact (EQ_MP (@lem1053959 b2 x1 x2) (@lem1053950 x1 x2 b2 h1)). Qed.
Lemma lem1053961 (x1 : nat) (x2 : nat) (b2 : Prop) (h1 : b2) : (term123 x1 x2) = (term112 b2 x1 x2).
Proof. exact (SYM (@lem1053960 x1 x2 b2 h1)). Qed.
Lemma lem1053962 (b2 : Prop) (h1 : ~ b2) : ~ b2.
Proof. exact (h1). Qed.
Lemma lem1053963 (b2 : Prop) : term65 b2.
Proof. exact (@lem82 b2). Qed.
Lemma lem1053964 (b2 : Prop) (h1 : ~ b2) : b2 = False.
Proof. exact (@lem1053963 b2 (@lem1053962 b2 h1)). Qed.
Lemma lem1053965 (x1 : nat) (x2 : nat) : (term126 x1 x2) = (term126 x1 x2).
Proof. exact (eq_refl (term126 x1 x2)). Qed.
Lemma lem1053966 (x1 : nat) (x2 : nat) (b2 : Prop) (h1 : ~ b2) : (term127 x1 x2 b2) = (term128 x1 x2).
Proof. exact (MK_COMB (@lem1053965 x1 x2) (@lem1053964 b2 h1)). Qed.
Lemma lem1053967 (x1 : nat) (x2 : nat) : (term128 x1 x2) = (term129 x1 x2).
Proof. exact (eq_refl (term128 x1 x2)). Qed.
Lemma lem1053968 (x1 : nat) (x2 : nat) (b2 : Prop) : (term130 x1 x2 b2) = (term130 x1 x2 b2).
Proof. exact (eq_refl (term130 x1 x2 b2)). Qed.
Lemma lem1053969 (b2 : Prop) (x1 : nat) (x2 : nat) : ((term127 x1 x2 b2) = (term128 x1 x2)) = ((term127 x1 x2 b2) = (term129 x1 x2)).
Proof. exact (MK_COMB (@lem1053968 x1 x2 b2) (@lem1053967 x1 x2)). Qed.
Lemma lem1053970 (b2 : Prop) (x1 : nat) (x2 : nat) : (term127 x1 x2 b2) = (term108 b2 x1 x2).
Proof. exact (eq_refl (term127 x1 x2 b2)). Qed.
Lemma lem1053971 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1053972 (b2 : Prop) (x1 : nat) (x2 : nat) : (term130 x1 x2 b2) = (term131 b2 x1 x2).
Proof. exact (MK_COMB (@lem1053971) (@lem1053970 b2 x1 x2)). Qed.
Lemma lem1053973 (x1 : nat) (x2 : nat) : (term129 x1 x2) = (term129 x1 x2).
Proof. exact (eq_refl (term129 x1 x2)). Qed.
Lemma lem1053974 (b2 : Prop) (x1 : nat) (x2 : nat) : ((term127 x1 x2 b2) = (term129 x1 x2)) = ((term108 b2 x1 x2) = (term129 x1 x2)).
Proof. exact (MK_COMB (@lem1053972 b2 x1 x2) (@lem1053973 x1 x2)). Qed.
Lemma lem1053975 (b2 : Prop) (x1 : nat) (x2 : nat) : ((term127 x1 x2 b2) = (term128 x1 x2)) = ((term108 b2 x1 x2) = (term129 x1 x2)).
Proof. exact (TRANS (@lem1053969 b2 x1 x2) (@lem1053974 b2 x1 x2)). Qed.
Lemma lem1053976 (x1 : nat) (x2 : nat) (b2 : Prop) (h1 : ~ b2) : (term108 b2 x1 x2) = (term129 x1 x2).
Proof. exact (EQ_MP (@lem1053975 b2 x1 x2) (@lem1053966 x1 x2 b2 h1)). Qed.
Lemma lem1053977 (x1 : nat) (x2 : nat) (b2 : Prop) (h1 : ~ b2) : (term129 x1 x2) = (term108 b2 x1 x2).
Proof. exact (SYM (@lem1053976 x1 x2 b2 h1)). Qed.
Lemma lem1053985 (n : nat) : (term25 n) = (term26 n).
Proof. exact (EQ_MP (@lem1053770 n) (@lem1053769 n)). Qed.
Lemma lem1053986 (x1 : nat) : (term132 x1) = (term133 x1).
Proof. exact (@lem1053985 (term43 x1)). Qed.
Lemma lem1053988 (n : nat) : (term22 n) = True.
Proof. exact (EQ_MP (@lem1053766 n) (@lem1053765 n)). Qed.
Lemma lem1053989 (x1 : nat) : (term22 x1) = True.
Proof. exact (@lem1053988 x1). Qed.
Lemma lem1053990 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1053991 (x1 : nat) : (term133 x1) = (~ True).
Proof. exact (MK_COMB (@lem1053990) (@lem1053989 x1)). Qed.
Lemma lem1053993 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1053994 (x1 : nat) : (term133 x1) = False.
Proof. exact (TRANS (@lem1053991 x1) (@lem1053993)). Qed.
Lemma lem1053995 (x1 : nat) : (term132 x1) = False.
Proof. exact (TRANS (@lem1053986 x1) (@lem1053994 x1)). Qed.
Lemma lem1053996 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1053997 (x1 : nat) : (term134 x1) = (@eq Prop False).
Proof. exact (MK_COMB (@lem1053996) (@lem1053995 x1)). Qed.
Lemma lem1053999 (n : nat) : (term25 n) = (term26 n).
Proof. exact (EQ_MP (@lem1053770 n) (@lem1053769 n)). Qed.
Lemma lem1054000 (x2 : nat) : (term132 x2) = (term133 x2).
Proof. exact (@lem1053999 (term43 x2)). Qed.
Lemma lem1054002 (n : nat) : (term22 n) = True.
Proof. exact (EQ_MP (@lem1053766 n) (@lem1053765 n)). Qed.
Lemma lem1054003 (x2 : nat) : (term22 x2) = True.
Proof. exact (@lem1054002 x2). Qed.
Lemma lem1054004 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1054005 (x2 : nat) : (term133 x2) = (~ True).
Proof. exact (MK_COMB (@lem1054004) (@lem1054003 x2)). Qed.
Lemma lem1054007 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1054008 (x2 : nat) : (term133 x2) = False.
Proof. exact (TRANS (@lem1054005 x2) (@lem1054007)). Qed.
Lemma lem1054009 (x2 : nat) : (term132 x2) = False.
Proof. exact (TRANS (@lem1054000 x2) (@lem1054008 x2)). Qed.
Lemma lem1054010 (x1 : nat) (x2 : nat) : ((term132 x1) = (term132 x2)) = (False = False).
Proof. exact (MK_COMB (@lem1053997 x1) (@lem1054009 x2)). Qed.
Lemma lem1054012 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem1054013 : (False = False) = (~ False).
Proof. exact (@lem1054012 False). Qed.
Lemma lem1054015 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1054016 : (False = False) = True.
Proof. exact (TRANS (@lem1054013) (@lem1054015)). Qed.
Lemma lem1054017 (x1 : nat) (x2 : nat) : ((term132 x1) = (term132 x2)) = True.
Proof. exact (TRANS (@lem1054010 x1 x2) (@lem1054016)). Qed.
Lemma lem1054018 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1054019 (x1 : nat) (x2 : nat) : (term135 x1 x2) = (imp True).
Proof. exact (MK_COMB (@lem1054018) (@lem1054017 x1 x2)). Qed.
Lemma lem1054029 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1054030 : (True = True) = True.
Proof. exact (@lem1054029 True). Qed.
Lemma lem1054031 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1054032 : term136 = (and True).
Proof. exact (MK_COMB (@lem1054031) (@lem1054030)). Qed.
Lemma lem1054035 (x1 : nat) (x2 : nat) : (x1 = x2) = (x1 = x2).
Proof. exact (eq_refl (x1 = x2)). Qed.
Lemma lem1054036 (x1 : nat) (x2 : nat) : (term137 x1 x2) = (term138 x1 x2).
Proof. exact (MK_COMB (@lem1054032) (@lem1054035 x1 x2)). Qed.
Lemma lem1054038 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1054039 (x1 : nat) (x2 : nat) : (term138 x1 x2) = (x1 = x2).
Proof. exact (@lem1054038 (x1 = x2)). Qed.
Lemma lem1054042 (x1 : nat) (x2 : nat) : (term137 x1 x2) = (x1 = x2).
Proof. exact (TRANS (@lem1054036 x1 x2) (@lem1054039 x1 x2)). Qed.
Lemma lem1054043 (x1 : nat) (x2 : nat) : (term139 x1 x2) = (term139 x1 x2).
Proof. exact (eq_refl (term139 x1 x2)). Qed.
Lemma lem1054044 (x1 : nat) (x2 : nat) : (term140 x1 x2) = (term141 x1 x2).
Proof. exact (MK_COMB (@lem1054043 x1 x2) (@lem1054042 x1 x2)). Qed.
Lemma lem1054049 (x1 : nat) (x2 : nat) : (term93 x1 x2) = (term142 x1 x2).
Proof. exact (MK_COMB (@lem1054019 x1 x2) (@lem1054044 x1 x2)). Qed.
Lemma lem1054051 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1054052 (x1 : nat) (x2 : nat) : (term142 x1 x2) = (term141 x1 x2).
Proof. exact (@lem1054051 (term141 x1 x2)). Qed.
Lemma lem1054061 (x1 : nat) (x2 : nat) : (term93 x1 x2) = (term141 x1 x2).
Proof. exact (TRANS (@lem1054049 x1 x2) (@lem1054052 x1 x2)). Qed.
Lemma lem1054062 (x1 : nat) (x2 : nat) : (term141 x1 x2) = (term93 x1 x2).
Proof. exact (SYM (@lem1054061 x1 x2)). Qed.
Lemma lem1054070 (n : nat) : (term25 n) = (term26 n).
Proof. exact (EQ_MP (@lem1053770 n) (@lem1053769 n)). Qed.
Lemma lem1054071 (x1 : nat) : (term132 x1) = (term133 x1).
Proof. exact (@lem1054070 (term43 x1)). Qed.
Lemma lem1054073 (n : nat) : (term22 n) = True.
Proof. exact (EQ_MP (@lem1053766 n) (@lem1053765 n)). Qed.
Lemma lem1054074 (x1 : nat) : (term22 x1) = True.
Proof. exact (@lem1054073 x1). Qed.
Lemma lem1054075 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1054076 (x1 : nat) : (term133 x1) = (~ True).
Proof. exact (MK_COMB (@lem1054075) (@lem1054074 x1)). Qed.
Lemma lem1054078 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1054079 (x1 : nat) : (term133 x1) = False.
Proof. exact (TRANS (@lem1054076 x1) (@lem1054078)). Qed.
Lemma lem1054080 (x1 : nat) : (term132 x1) = False.
Proof. exact (TRANS (@lem1054071 x1) (@lem1054079 x1)). Qed.
Lemma lem1054081 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1054082 (x1 : nat) : (term134 x1) = (@eq Prop False).
Proof. exact (MK_COMB (@lem1054081) (@lem1054080 x1)). Qed.
Lemma lem1054084 (n : nat) : (term22 n) = True.
Proof. exact (EQ_MP (@lem1053766 n) (@lem1053765 n)). Qed.
Lemma lem1054085 (x2 : nat) : (term22 x2) = True.
Proof. exact (@lem1054084 x2). Qed.
Lemma lem1054086 (x1 : nat) (x2 : nat) : ((term132 x1) = (term22 x2)) = (False = True).
Proof. exact (MK_COMB (@lem1054082 x1) (@lem1054085 x2)). Qed.
Lemma lem1054088 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem1054089 : (False = True) = (~ True).
Proof. exact (@lem1054088 True). Qed.
Lemma lem1054091 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1054092 : (False = True) = False.
Proof. exact (TRANS (@lem1054089) (@lem1054091)). Qed.
Lemma lem1054093 (x1 : nat) (x2 : nat) : ((term132 x1) = (term22 x2)) = False.
Proof. exact (TRANS (@lem1054086 x1 x2) (@lem1054092)). Qed.
Lemma lem1054094 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1054095 (x1 : nat) (x2 : nat) : (term143 x1 x2) = (imp False).
Proof. exact (MK_COMB (@lem1054094) (@lem1054093 x1 x2)). Qed.
Lemma lem1054105 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1054106 : (True = False) = False.
Proof. exact (@lem1054105 False). Qed.
Lemma lem1054107 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1054108 : term144 = (and False).
Proof. exact (MK_COMB (@lem1054107) (@lem1054106)). Qed.
Lemma lem1054111 (x1 : nat) (x2 : nat) : (x1 = x2) = (x1 = x2).
Proof. exact (eq_refl (x1 = x2)). Qed.
Lemma lem1054112 (x1 : nat) (x2 : nat) : (term145 x1 x2) = (term146 x1 x2).
Proof. exact (MK_COMB (@lem1054108) (@lem1054111 x1 x2)). Qed.
Lemma lem1054114 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1054115 (x1 : nat) (x2 : nat) : (term146 x1 x2) = False.
Proof. exact (@lem1054114 (x1 = x2)). Qed.
Lemma lem1054116 (x1 : nat) (x2 : nat) : (term145 x1 x2) = False.
Proof. exact (TRANS (@lem1054112 x1 x2) (@lem1054115 x1 x2)). Qed.
Lemma lem1054117 (x1 : nat) (x2 : nat) : (term147 x1 x2) = (term147 x1 x2).
Proof. exact (eq_refl (term147 x1 x2)). Qed.
Lemma lem1054118 (x1 : nat) (x2 : nat) : (term148 x1 x2) = (term149 x1 x2).
Proof. exact (MK_COMB (@lem1054117 x1 x2) (@lem1054116 x1 x2)). Qed.
Lemma lem1054122 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1054123 (x1 : nat) (x2 : nat) : (term149 x1 x2) = (term150 x1 x2).
Proof. exact (@lem1054122 ((term42 x1) = (term43 x2))). Qed.
Lemma lem1054126 (x1 : nat) (x2 : nat) : (term148 x1 x2) = (term150 x1 x2).
Proof. exact (TRANS (@lem1054118 x1 x2) (@lem1054123 x1 x2)). Qed.
Lemma lem1054127 (x1 : nat) (x2 : nat) : (term99 x1 x2) = (term151 x1 x2).
Proof. exact (MK_COMB (@lem1054095 x1 x2) (@lem1054126 x1 x2)). Qed.
Lemma lem1054129 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1054130 (x1 : nat) (x2 : nat) : (term151 x1 x2) = True.
Proof. exact (@lem1054129 (term150 x1 x2)). Qed.
Lemma lem1054131 (x1 : nat) (x2 : nat) : (term99 x1 x2) = True.
Proof. exact (TRANS (@lem1054127 x1 x2) (@lem1054130 x1 x2)). Qed.
Lemma lem1054132 (x1 : nat) (x2 : nat) : True = (term99 x1 x2).
Proof. exact (SYM (@lem1054131 x1 x2)). Qed.
Lemma lem1054133 (x1 : nat) (x2 : nat) : term99 x1 x2.
Proof. exact (EQ_MP (@lem1054132 x1 x2) (@lem0)). Qed.
Lemma lem1054141 (n : nat) : (term22 n) = True.
Proof. exact (EQ_MP (@lem1053766 n) (@lem1053765 n)). Qed.
Lemma lem1054142 (x1 : nat) : (term22 x1) = True.
Proof. exact (@lem1054141 x1). Qed.
Lemma lem1054143 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1054144 (x1 : nat) : (term152 x1) = (@eq Prop True).
Proof. exact (MK_COMB (@lem1054143) (@lem1054142 x1)). Qed.
Lemma lem1054146 (n : nat) : (term25 n) = (term26 n).
Proof. exact (EQ_MP (@lem1053770 n) (@lem1053769 n)). Qed.
Lemma lem1054147 (x2 : nat) : (term132 x2) = (term133 x2).
Proof. exact (@lem1054146 (term43 x2)). Qed.
Lemma lem1054149 (n : nat) : (term22 n) = True.
Proof. exact (EQ_MP (@lem1053766 n) (@lem1053765 n)). Qed.
Lemma lem1054150 (x2 : nat) : (term22 x2) = True.
Proof. exact (@lem1054149 x2). Qed.
Lemma lem1054151 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1054152 (x2 : nat) : (term133 x2) = (~ True).
Proof. exact (MK_COMB (@lem1054151) (@lem1054150 x2)). Qed.
Lemma lem1054154 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1054155 (x2 : nat) : (term133 x2) = False.
Proof. exact (TRANS (@lem1054152 x2) (@lem1054154)). Qed.
Lemma lem1054156 (x2 : nat) : (term132 x2) = False.
Proof. exact (TRANS (@lem1054147 x2) (@lem1054155 x2)). Qed.
Lemma lem1054157 (x1 : nat) (x2 : nat) : ((term22 x1) = (term132 x2)) = (True = False).
Proof. exact (MK_COMB (@lem1054144 x1) (@lem1054156 x2)). Qed.
Lemma lem1054159 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1054160 : (True = False) = False.
Proof. exact (@lem1054159 False). Qed.
Lemma lem1054161 (x1 : nat) (x2 : nat) : ((term22 x1) = (term132 x2)) = False.
Proof. exact (TRANS (@lem1054157 x1 x2) (@lem1054160)). Qed.
Lemma lem1054162 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1054163 (x1 : nat) (x2 : nat) : (term153 x1 x2) = (imp False).
Proof. exact (MK_COMB (@lem1054162) (@lem1054161 x1 x2)). Qed.
Lemma lem1054173 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem1054174 : (False = True) = (~ True).
Proof. exact (@lem1054173 True). Qed.
Lemma lem1054176 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1054177 : (False = True) = False.
Proof. exact (TRANS (@lem1054174) (@lem1054176)). Qed.
Lemma lem1054178 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1054179 : term154 = (and False).
Proof. exact (MK_COMB (@lem1054178) (@lem1054177)). Qed.
Lemma lem1054182 (x1 : nat) (x2 : nat) : (x1 = x2) = (x1 = x2).
Proof. exact (eq_refl (x1 = x2)). Qed.
Lemma lem1054183 (x1 : nat) (x2 : nat) : (term155 x1 x2) = (term146 x1 x2).
Proof. exact (MK_COMB (@lem1054179) (@lem1054182 x1 x2)). Qed.
Lemma lem1054185 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1054186 (x1 : nat) (x2 : nat) : (term146 x1 x2) = False.
Proof. exact (@lem1054185 (x1 = x2)). Qed.
Lemma lem1054187 (x1 : nat) (x2 : nat) : (term155 x1 x2) = False.
Proof. exact (TRANS (@lem1054183 x1 x2) (@lem1054186 x1 x2)). Qed.
Lemma lem1054188 (x1 : nat) (x2 : nat) : (term156 x1 x2) = (term156 x1 x2).
Proof. exact (eq_refl (term156 x1 x2)). Qed.
Lemma lem1054189 (x1 : nat) (x2 : nat) : (term157 x1 x2) = (term158 x1 x2).
Proof. exact (MK_COMB (@lem1054188 x1 x2) (@lem1054187 x1 x2)). Qed.
Lemma lem1054193 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1054194 (x1 : nat) (x2 : nat) : (term158 x1 x2) = (term159 x1 x2).
Proof. exact (@lem1054193 ((term43 x1) = (term42 x2))). Qed.
Lemma lem1054197 (x1 : nat) (x2 : nat) : (term157 x1 x2) = (term159 x1 x2).
Proof. exact (TRANS (@lem1054189 x1 x2) (@lem1054194 x1 x2)). Qed.
Lemma lem1054198 (x1 : nat) (x2 : nat) : (term123 x1 x2) = (term160 x1 x2).
Proof. exact (MK_COMB (@lem1054163 x1 x2) (@lem1054197 x1 x2)). Qed.
Lemma lem1054200 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1054201 (x1 : nat) (x2 : nat) : (term160 x1 x2) = True.
Proof. exact (@lem1054200 (term159 x1 x2)). Qed.
Lemma lem1054202 (x1 : nat) (x2 : nat) : (term123 x1 x2) = True.
Proof. exact (TRANS (@lem1054198 x1 x2) (@lem1054201 x1 x2)). Qed.
Lemma lem1054203 (x1 : nat) (x2 : nat) : True = (term123 x1 x2).
Proof. exact (SYM (@lem1054202 x1 x2)). Qed.
Lemma lem1054204 (x1 : nat) (x2 : nat) : term123 x1 x2.
Proof. exact (EQ_MP (@lem1054203 x1 x2) (@lem0)). Qed.
Lemma lem1054212 (n : nat) : (term22 n) = True.
Proof. exact (EQ_MP (@lem1053766 n) (@lem1053765 n)). Qed.
Lemma lem1054213 (x1 : nat) : (term22 x1) = True.
Proof. exact (@lem1054212 x1). Qed.
Lemma lem1054214 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1054215 (x1 : nat) : (term152 x1) = (@eq Prop True).
Proof. exact (MK_COMB (@lem1054214) (@lem1054213 x1)). Qed.
Lemma lem1054217 (n : nat) : (term22 n) = True.
Proof. exact (EQ_MP (@lem1053766 n) (@lem1053765 n)). Qed.
Lemma lem1054218 (x2 : nat) : (term22 x2) = True.
Proof. exact (@lem1054217 x2). Qed.
Lemma lem1054219 (x1 : nat) (x2 : nat) : ((term22 x1) = (term22 x2)) = (True = True).
Proof. exact (MK_COMB (@lem1054215 x1) (@lem1054218 x2)). Qed.
Lemma lem1054221 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1054222 : (True = True) = True.
Proof. exact (@lem1054221 True). Qed.
Lemma lem1054223 (x1 : nat) (x2 : nat) : ((term22 x1) = (term22 x2)) = True.
Proof. exact (TRANS (@lem1054219 x1 x2) (@lem1054222)). Qed.
Lemma lem1054224 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1054225 (x1 : nat) (x2 : nat) : (term161 x1 x2) = (imp True).
Proof. exact (MK_COMB (@lem1054224) (@lem1054223 x1 x2)). Qed.
Lemma lem1054235 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem1054236 : (False = False) = (~ False).
Proof. exact (@lem1054235 False). Qed.
Lemma lem1054238 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1054239 : (False = False) = True.
Proof. exact (TRANS (@lem1054236) (@lem1054238)). Qed.
Lemma lem1054240 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1054241 : term162 = (and True).
Proof. exact (MK_COMB (@lem1054240) (@lem1054239)). Qed.
Lemma lem1054244 (x1 : nat) (x2 : nat) : (x1 = x2) = (x1 = x2).
Proof. exact (eq_refl (x1 = x2)). Qed.
Lemma lem1054245 (x1 : nat) (x2 : nat) : (term163 x1 x2) = (term138 x1 x2).
Proof. exact (MK_COMB (@lem1054241) (@lem1054244 x1 x2)). Qed.
Lemma lem1054247 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1054248 (x1 : nat) (x2 : nat) : (term138 x1 x2) = (x1 = x2).
Proof. exact (@lem1054247 (x1 = x2)). Qed.
Lemma lem1054251 (x1 : nat) (x2 : nat) : (term163 x1 x2) = (x1 = x2).
Proof. exact (TRANS (@lem1054245 x1 x2) (@lem1054248 x1 x2)). Qed.
Lemma lem1054252 (x1 : nat) (x2 : nat) : (term164 x1 x2) = (term164 x1 x2).
Proof. exact (eq_refl (term164 x1 x2)). Qed.
Lemma lem1054253 (x1 : nat) (x2 : nat) : (term165 x1 x2) = (term166 x1 x2).
Proof. exact (MK_COMB (@lem1054252 x1 x2) (@lem1054251 x1 x2)). Qed.
Lemma lem1054258 (x1 : nat) (x2 : nat) : (term129 x1 x2) = (term167 x1 x2).
Proof. exact (MK_COMB (@lem1054225 x1 x2) (@lem1054253 x1 x2)). Qed.
Lemma lem1054260 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1054261 (x1 : nat) (x2 : nat) : (term167 x1 x2) = (term166 x1 x2).
Proof. exact (@lem1054260 (term166 x1 x2)). Qed.
Lemma lem1054270 (x1 : nat) (x2 : nat) : (term129 x1 x2) = (term166 x1 x2).
Proof. exact (TRANS (@lem1054258 x1 x2) (@lem1054261 x1 x2)). Qed.
Lemma lem1054271 (x1 : nat) (x2 : nat) : (term166 x1 x2) = (term129 x1 x2).
Proof. exact (SYM (@lem1054270 x1 x2)). Qed.
Lemma lem1054277 (m : nat) (n : nat) : ((S m) = (S n)) = (m = n).
Proof. exact (EQ_MP (@lem1053761 m n) (@lem1053760 m n)). Qed.
Lemma lem1054278 (x1 : nat) (x2 : nat) : ((term42 x1) = (term42 x2)) = ((term43 x1) = (term43 x2)).
Proof. exact (@lem1054277 (term43 x1) (term43 x2)). Qed.
Lemma lem1054280 (m : nat) (n : nat) (p : nat) : ((Nat.mul m n) = (Nat.mul m p)) = (term17 m n p).
Proof. exact (EQ_MP (@lem1053755 m n p) (@lem1053754 m n p)). Qed.
Lemma lem1054281 (x1 : nat) (x2 : nat) : ((term43 x1) = (term43 x2)) = (term168 x1 x2).
Proof. exact (@lem1054280 term169 x1 x2). Qed.
Lemma lem1054284 (x1 : nat) (x2 : nat) : ((term42 x1) = (term42 x2)) = (term168 x1 x2).
Proof. exact (TRANS (@lem1054278 x1 x2) (@lem1054281 x1 x2)). Qed.
Lemma lem1054286 (m : nat) (n : nat) : ((NUMERAL m) = (NUMERAL n)) = (m = n).
Proof. exact (EQ_MP (@lem1053496 m n) (@lem1053495 m n)). Qed.
Lemma lem1054287 : (term169 = (NUMERAL 0)) = (term170 = 0).
Proof. exact (@lem1054286 term170 0). Qed.
Lemma lem1054289 (n : nat) : ((BIT0 n) = 0) = (n = 0).
Proof. exact (EQ_MP (@lem1053488 n) (@lem1053487 n)). Qed.
Lemma lem1054290 : (term170 = 0) = ((BIT1 0) = 0).
Proof. exact (@lem1054289 (BIT1 0)). Qed.
Lemma lem1054292 (n : nat) : ((BIT1 n) = 0) = False.
Proof. exact (EQ_MP (@lem1053484 n) (@lem1053483 n)). Qed.
Lemma lem1054293 : ((BIT1 0) = 0) = False.
Proof. exact (@lem1054292 0). Qed.
Lemma lem1054294 : (term170 = 0) = False.
Proof. exact (TRANS (@lem1054290) (@lem1054293)). Qed.
Lemma lem1054295 : (term169 = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem1054287) (@lem1054294)). Qed.
Lemma lem1054296 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1054297 : term171 = (or False).
Proof. exact (MK_COMB (@lem1054296) (@lem1054295)). Qed.
Lemma lem1054300 (x1 : nat) (x2 : nat) : (x1 = x2) = (x1 = x2).
Proof. exact (eq_refl (x1 = x2)). Qed.
Lemma lem1054301 (x1 : nat) (x2 : nat) : (term168 x1 x2) = (term172 x1 x2).
Proof. exact (MK_COMB (@lem1054297) (@lem1054300 x1 x2)). Qed.
Lemma lem1054303 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem1054304 (x1 : nat) (x2 : nat) : (term172 x1 x2) = (x1 = x2).
Proof. exact (@lem1054303 (x1 = x2)). Qed.
Lemma lem1054307 (x1 : nat) (x2 : nat) : (term168 x1 x2) = (x1 = x2).
Proof. exact (TRANS (@lem1054301 x1 x2) (@lem1054304 x1 x2)). Qed.
Lemma lem1054308 (x1 : nat) (x2 : nat) : ((term42 x1) = (term42 x2)) = (x1 = x2).
Proof. exact (TRANS (@lem1054284 x1 x2) (@lem1054307 x1 x2)). Qed.
Lemma lem1054309 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1054310 (x1 : nat) (x2 : nat) : (term139 x1 x2) = (term173 x1 x2).
Proof. exact (MK_COMB (@lem1054309) (@lem1054308 x1 x2)). Qed.
Lemma lem1054313 (x1 : nat) (x2 : nat) : (x1 = x2) = (x1 = x2).
Proof. exact (eq_refl (x1 = x2)). Qed.
Lemma lem1054314 (x1 : nat) (x2 : nat) : (term141 x1 x2) = (term174 x1 x2).
Proof. exact (MK_COMB (@lem1054310 x1 x2) (@lem1054313 x1 x2)). Qed.
Lemma lem1054318 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem1054319 (x1 : nat) (x2 : nat) : (term174 x1 x2) = True.
Proof. exact (@lem1054318 (x1 = x2)). Qed.
Lemma lem1054320 (x1 : nat) (x2 : nat) : (term141 x1 x2) = True.
Proof. exact (TRANS (@lem1054314 x1 x2) (@lem1054319 x1 x2)). Qed.
Lemma lem1054321 (x1 : nat) (x2 : nat) : True = (term141 x1 x2).
Proof. exact (SYM (@lem1054320 x1 x2)). Qed.
Lemma lem1054322 (x1 : nat) (x2 : nat) : term141 x1 x2.
Proof. exact (EQ_MP (@lem1054321 x1 x2) (@lem0)). Qed.
Lemma lem1054328 (m : nat) (n : nat) (p : nat) : ((Nat.mul m n) = (Nat.mul m p)) = (term17 m n p).
Proof. exact (EQ_MP (@lem1053755 m n p) (@lem1053754 m n p)). Qed.
Lemma lem1054329 (x1 : nat) (x2 : nat) : ((term43 x1) = (term43 x2)) = (term168 x1 x2).
Proof. exact (@lem1054328 term169 x1 x2). Qed.
Lemma lem1054333 (m : nat) (n : nat) : ((NUMERAL m) = (NUMERAL n)) = (m = n).
Proof. exact (EQ_MP (@lem1053496 m n) (@lem1053495 m n)). Qed.
Lemma lem1054334 : (term169 = (NUMERAL 0)) = (term170 = 0).
Proof. exact (@lem1054333 term170 0). Qed.
Lemma lem1054336 (n : nat) : ((BIT0 n) = 0) = (n = 0).
Proof. exact (EQ_MP (@lem1053488 n) (@lem1053487 n)). Qed.
Lemma lem1054337 : (term170 = 0) = ((BIT1 0) = 0).
Proof. exact (@lem1054336 (BIT1 0)). Qed.
Lemma lem1054339 (n : nat) : ((BIT1 n) = 0) = False.
Proof. exact (EQ_MP (@lem1053484 n) (@lem1053483 n)). Qed.
Lemma lem1054340 : ((BIT1 0) = 0) = False.
Proof. exact (@lem1054339 0). Qed.
Lemma lem1054341 : (term170 = 0) = False.
Proof. exact (TRANS (@lem1054337) (@lem1054340)). Qed.
Lemma lem1054342 : (term169 = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem1054334) (@lem1054341)). Qed.
Lemma lem1054343 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1054344 : term171 = (or False).
Proof. exact (MK_COMB (@lem1054343) (@lem1054342)). Qed.
Lemma lem1054347 (x1 : nat) (x2 : nat) : (x1 = x2) = (x1 = x2).
Proof. exact (eq_refl (x1 = x2)). Qed.
Lemma lem1054348 (x1 : nat) (x2 : nat) : (term168 x1 x2) = (term172 x1 x2).
Proof. exact (MK_COMB (@lem1054344) (@lem1054347 x1 x2)). Qed.
Lemma lem1054350 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem1054351 (x1 : nat) (x2 : nat) : (term172 x1 x2) = (x1 = x2).
Proof. exact (@lem1054350 (x1 = x2)). Qed.
Lemma lem1054354 (x1 : nat) (x2 : nat) : (term168 x1 x2) = (x1 = x2).
Proof. exact (TRANS (@lem1054348 x1 x2) (@lem1054351 x1 x2)). Qed.
Lemma lem1054355 (x1 : nat) (x2 : nat) : ((term43 x1) = (term43 x2)) = (x1 = x2).
Proof. exact (TRANS (@lem1054329 x1 x2) (@lem1054354 x1 x2)). Qed.
Lemma lem1054356 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1054357 (x1 : nat) (x2 : nat) : (term164 x1 x2) = (term173 x1 x2).
Proof. exact (MK_COMB (@lem1054356) (@lem1054355 x1 x2)). Qed.
Lemma lem1054360 (x1 : nat) (x2 : nat) : (x1 = x2) = (x1 = x2).
Proof. exact (eq_refl (x1 = x2)). Qed.
Lemma lem1054361 (x1 : nat) (x2 : nat) : (term166 x1 x2) = (term174 x1 x2).
Proof. exact (MK_COMB (@lem1054357 x1 x2) (@lem1054360 x1 x2)). Qed.
Lemma lem1054365 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem1054366 (x1 : nat) (x2 : nat) : (term174 x1 x2) = True.
Proof. exact (@lem1054365 (x1 = x2)). Qed.
Lemma lem1054367 (x1 : nat) (x2 : nat) : (term166 x1 x2) = True.
Proof. exact (TRANS (@lem1054361 x1 x2) (@lem1054366 x1 x2)). Qed.
Lemma lem1054368 (x1 : nat) (x2 : nat) : True = (term166 x1 x2).
Proof. exact (SYM (@lem1054367 x1 x2)). Qed.
Lemma lem1054369 (x1 : nat) (x2 : nat) : term166 x1 x2.
Proof. exact (EQ_MP (@lem1054368 x1 x2) (@lem0)). Qed.
Lemma lem1054370 (x1 : nat) (x2 : nat) : term129 x1 x2.
Proof. exact (EQ_MP (@lem1054271 x1 x2) (@lem1054369 x1 x2)). Qed.
Lemma lem1054371 (x1 : nat) (x2 : nat) : term93 x1 x2.
Proof. exact (EQ_MP (@lem1054062 x1 x2) (@lem1054322 x1 x2)). Qed.
Lemma lem1054372 (x1 : nat) (x2 : nat) (b2 : Prop) (h1 : ~ b2) : term108 b2 x1 x2.
Proof. exact (EQ_MP (@lem1053977 x1 x2 b2 h1) (@lem1054370 x1 x2)). Qed.
Lemma lem1054373 (x1 : nat) (x2 : nat) (b2 : Prop) (h1 : ~ b2) : (~ b2) = (term108 b2 x1 x2).
Proof. exact (prop_ext (fun h2 : ~ b2 => @lem1054372 x1 x2 b2 h1) (fun h2 : term108 b2 x1 x2 => @lem1053962 b2 h1)). Qed.
Lemma lem1054374 (x1 : nat) (x2 : nat) (b2 : Prop) (h1 : ~ b2) : term108 b2 x1 x2.
Proof. exact (EQ_MP (@lem1054373 x1 x2 b2 h1) (@lem1053962 b2 h1)). Qed.
Lemma lem1054375 (b2 : Prop) (x1 : nat) (x2 : nat) : term110 b2 x1 x2.
Proof. exact (fun h0 : ~ b2 => @lem1054374 x1 x2 b2 h0). Qed.
Lemma lem1054376 (x1 : nat) (x2 : nat) (b2 : Prop) (h1 : b2) : term112 b2 x1 x2.
Proof. exact (EQ_MP (@lem1053961 x1 x2 b2 h1) (@lem1054204 x1 x2)). Qed.
Lemma lem1054377 (x1 : nat) (x2 : nat) (b2 : Prop) (h1 : b2) : b2 = (term112 b2 x1 x2).
Proof. exact (prop_ext (fun h2 : b2 => @lem1054376 x1 x2 b2 h1) (fun h2 : term112 b2 x1 x2 => @lem1053946 b2 h1)). Qed.
Lemma lem1054378 (x1 : nat) (x2 : nat) (b2 : Prop) (h1 : b2) : term112 b2 x1 x2.
Proof. exact (EQ_MP (@lem1054377 x1 x2 b2 h1) (@lem1053946 b2 h1)). Qed.
Lemma lem1054379 (b2 : Prop) (x1 : nat) (x2 : nat) : term114 b2 x1 x2.
Proof. exact (fun h0 : b2 => @lem1054378 x1 x2 b2 h0). Qed.
Lemma lem1054380 (b2 : Prop) (x1 : nat) (x2 : nat) : term117 b2 x1 x2.
Proof. exact (conj (@lem1054379 b2 x1 x2) (@lem1054375 b2 x1 x2)). Qed.
Lemma lem1054381 (b2 : Prop) (x1 : nat) (x2 : nat) : term69 b2 x1 x2.
Proof. exact (EQ_MP (@lem1053945 b2 x1 x2) (@lem1054380 b2 x1 x2)). Qed.
Lemma lem1054382 (x1 : nat) (x2 : nat) (b2 : Prop) (h1 : ~ b2) : term78 b2 x1 x2.
Proof. exact (EQ_MP (@lem1053927 x1 x2 b2 h1) (@lem1054133 x1 x2)). Qed.
Lemma lem1054383 (x1 : nat) (x2 : nat) (b2 : Prop) (h1 : ~ b2) : (~ b2) = (term78 b2 x1 x2).
Proof. exact (prop_ext (fun h2 : ~ b2 => @lem1054382 x1 x2 b2 h1) (fun h2 : term78 b2 x1 x2 => @lem1053912 b2 h1)). Qed.
Lemma lem1054384 (x1 : nat) (x2 : nat) (b2 : Prop) (h1 : ~ b2) : term78 b2 x1 x2.
Proof. exact (EQ_MP (@lem1054383 x1 x2 b2 h1) (@lem1053912 b2 h1)). Qed.
Lemma lem1054385 (b2 : Prop) (x1 : nat) (x2 : nat) : term80 b2 x1 x2.
Proof. exact (fun h0 : ~ b2 => @lem1054384 x1 x2 b2 h0). Qed.
Lemma lem1054386 (x1 : nat) (x2 : nat) (b2 : Prop) (h1 : b2) : term82 b2 x1 x2.
Proof. exact (EQ_MP (@lem1053911 x1 x2 b2 h1) (@lem1054371 x1 x2)). Qed.
Lemma lem1054387 (x1 : nat) (x2 : nat) (b2 : Prop) (h1 : b2) : b2 = (term82 b2 x1 x2).
Proof. exact (prop_ext (fun h2 : b2 => @lem1054386 x1 x2 b2 h1) (fun h2 : term82 b2 x1 x2 => @lem1053896 b2 h1)). Qed.
Lemma lem1054388 (x1 : nat) (x2 : nat) (b2 : Prop) (h1 : b2) : term82 b2 x1 x2.
Proof. exact (EQ_MP (@lem1054387 x1 x2 b2 h1) (@lem1053896 b2 h1)). Qed.
Lemma lem1054389 (b2 : Prop) (x1 : nat) (x2 : nat) : term84 b2 x1 x2.
Proof. exact (fun h0 : b2 => @lem1054388 x1 x2 b2 h0). Qed.
Lemma lem1054390 (b2 : Prop) (x1 : nat) (x2 : nat) : term87 b2 x1 x2.
Proof. exact (conj (@lem1054389 b2 x1 x2) (@lem1054385 b2 x1 x2)). Qed.
Lemma lem1054391 (b2 : Prop) (x1 : nat) (x2 : nat) : term62 b2 x1 x2.
Proof. exact (EQ_MP (@lem1053895 b2 x1 x2) (@lem1054390 b2 x1 x2)). Qed.
Lemma lem1054392 (b2 : Prop) (x1 : nat) (x2 : nat) (b1 : Prop) (h1 : ~ b1) : term45 b1 b2 x1 x2.
Proof. exact (EQ_MP (@lem1053877 b2 x1 x2 b1 h1) (@lem1054381 b2 x1 x2)). Qed.
Lemma lem1054393 (b2 : Prop) (x1 : nat) (x2 : nat) (b1 : Prop) (h1 : ~ b1) : (~ b1) = (term45 b1 b2 x1 x2).
Proof. exact (prop_ext (fun h2 : ~ b1 => @lem1054392 b2 x1 x2 b1 h1) (fun h2 : term45 b1 b2 x1 x2 => @lem1053862 b1 h1)). Qed.
Lemma lem1054394 (b2 : Prop) (x1 : nat) (x2 : nat) (b1 : Prop) (h1 : ~ b1) : term45 b1 b2 x1 x2.
Proof. exact (EQ_MP (@lem1054393 b2 x1 x2 b1 h1) (@lem1053862 b1 h1)). Qed.
Lemma lem1054395 (b1 : Prop) (b2 : Prop) (x1 : nat) (x2 : nat) : term48 b1 b2 x1 x2.
Proof. exact (fun h0 : ~ b1 => @lem1054394 b2 x1 x2 b1 h0). Qed.
Lemma lem1054396 (b2 : Prop) (x1 : nat) (x2 : nat) (b1 : Prop) (h1 : b1) : term50 b1 b2 x1 x2.
Proof. exact (EQ_MP (@lem1053861 b2 x1 x2 b1 h1) (@lem1054391 b2 x1 x2)). Qed.
Lemma lem1054397 (b2 : Prop) (x1 : nat) (x2 : nat) (b1 : Prop) (h1 : b1) : b1 = (term50 b1 b2 x1 x2).
Proof. exact (prop_ext (fun h2 : b1 => @lem1054396 b2 x1 x2 b1 h1) (fun h2 : term50 b1 b2 x1 x2 => @lem1053846 b1 h1)). Qed.
Lemma lem1054398 (b2 : Prop) (x1 : nat) (x2 : nat) (b1 : Prop) (h1 : b1) : term50 b1 b2 x1 x2.
Proof. exact (EQ_MP (@lem1054397 b2 x1 x2 b1 h1) (@lem1053846 b1 h1)). Qed.
Lemma lem1054399 (b1 : Prop) (b2 : Prop) (x1 : nat) (x2 : nat) : term52 b1 b2 x1 x2.
Proof. exact (fun h0 : b1 => @lem1054398 b2 x1 x2 b1 h0). Qed.
Lemma lem1054400 (b1 : Prop) (b2 : Prop) (x1 : nat) (x2 : nat) : term55 b1 b2 x1 x2.
Proof. exact (conj (@lem1054399 b1 b2 x1 x2) (@lem1054395 b1 b2 x1 x2)). Qed.
Lemma lem1054401 (b1 : Prop) (b2 : Prop) (x1 : nat) (x2 : nat) : term56 b1 b2 x1 x2.
Proof. exact (EQ_MP (@lem1053845 b1 b2 x1 x2) (@lem1054400 b1 b2 x1 x2)). Qed.
Lemma lem1054402 (b1 : Prop) (x1 : nat) (b2 : Prop) (x2 : nat) (h1 : (term30 b1 x1) = (term30 b2 x2)) : term175 b1 b2 x1 x2.
Proof. exact (@lem1054401 b1 b2 x1 x2 (@lem1053827 b1 x1 b2 x2 h1)). Qed.
Lemma lem1054403 (b1 : Prop) (x1 : nat) (b2 : Prop) (x2 : nat) (h1 : (term30 b1 x1) = (term30 b2 x2)) : term31 b1 b2 x1 x2.
Proof. exact (@lem1054402 b1 x1 b2 x2 h1 (@lem1053825 b1 x1 b2 x2 h1)). Qed.
Lemma lem1054404 (b1 : Prop) (b2 : Prop) (x1 : nat) (x2 : nat) : term175 b1 b2 x1 x2.
Proof. exact (fun h0 : (term30 b1 x1) = (term30 b2 x2) => @lem1054403 b1 x1 b2 x2 h0). Qed.
Lemma lem1054406 (b1 : Prop) (x1 : nat) (b2 : Prop) (x2 : nat) (h1 : (NUMSUM b1 x1) = (NUMSUM b2 x2)) : term31 b1 b2 x1 x2.
Proof. exact (@lem1054404 b1 b2 x1 x2 (@lem1053824 b1 x1 b2 x2 h1)). Qed.
Lemma lem1054407 (b1 : Prop) (x1 : nat) (b2 : Prop) (x2 : nat) : term176 b1 x1 b2 x2.
Proof. exact (fun h0 : term31 b1 b2 x1 x2 => @lem1053810 b1 b2 x1 x2 h0). Qed.
Lemma lem1054408 (b1 : Prop) (b2 : Prop) (x1 : nat) (x2 : nat) : term177 b1 b2 x1 x2.
Proof. exact (fun h0 : (NUMSUM b1 x1) = (NUMSUM b2 x2) => @lem1054406 b1 x1 b2 x2 h0). Qed.
Lemma lem1054409 (b1 : Prop) (x1 : nat) (b2 : Prop) (x2 : nat) : term178 b1 x1 b2 x2.
Proof. exact (conj (@lem1054408 b1 b2 x1 x2) (@lem1054407 b1 x1 b2 x2)). Qed.
Lemma lem1054410 (b1 : Prop) (b2 : Prop) (x1 : nat) (x2 : nat) : (term178 b1 x1 b2 x2) = (((NUMSUM b1 x1) = (NUMSUM b2 x2)) = (term31 b1 b2 x1 x2)).
Proof. exact (@lem32 ((NUMSUM b1 x1) = (NUMSUM b2 x2)) (term31 b1 b2 x1 x2)). Qed.
Lemma lem1054411 (b1 : Prop) (b2 : Prop) (x1 : nat) (x2 : nat) : ((NUMSUM b1 x1) = (NUMSUM b2 x2)) = (term31 b1 b2 x1 x2).
Proof. exact (EQ_MP (@lem1054410 b1 b2 x1 x2) (@lem1054409 b1 x1 b2 x2)). Qed.
Lemma lem1054416 (b1 : Prop) (b2 : Prop) (x1 : nat) : term179 b1 b2 x1.
Proof. exact (fun x2 : nat => @lem1054411 b1 b2 x1 x2). Qed.
Lemma lem1054421 (b1 : Prop) (x1 : nat) : term180 b1 x1.
Proof. exact (fun b2 : Prop => @lem1054416 b1 b2 x1). Qed.
Lemma lem1054426 (b1 : Prop) : term181 b1.
Proof. exact (fun x1 : nat => @lem1054421 b1 x1). Qed.
Lemma lem1054431 : term182.
Proof. exact (fun b1 : Prop => @lem1054426 b1). Qed.
