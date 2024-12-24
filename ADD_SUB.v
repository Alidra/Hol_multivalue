Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ADD_SUB_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import SUB_0_spec.
Require Import SUB_SUC_spec.
Require Import thm0_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Lemma lem135736 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem135737 (m : nat) : term1 m.
Proof. exact (@lem135736 (term2 m)). Qed.
Lemma lem135738 (m : nat) : (term3 m) = ((term4 m) = m).
Proof. exact (eq_refl (term3 m)). Qed.
Lemma lem135739 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem135740 (m : nat) : (term5 m) = (term6 m).
Proof. exact (MK_COMB (@lem135739) (@lem135738 m)). Qed.
Lemma lem135741 (n : nat) (m : nat) : (term7 m n) = ((term8 m n) = m).
Proof. exact (eq_refl (term7 m n)). Qed.
Lemma lem135742 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem135743 (n : nat) (m : nat) : (term9 m n) = (term10 n m).
Proof. exact (MK_COMB (@lem135742) (@lem135741 n m)). Qed.
Lemma lem135744 (n : nat) (m : nat) : (term11 m n) = ((term12 m n) = m).
Proof. exact (eq_refl (term11 m n)). Qed.
Lemma lem135745 (n : nat) (m : nat) : (term13 m n) = (term14 n m).
Proof. exact (MK_COMB (@lem135743 n m) (@lem135744 n m)). Qed.
Lemma lem135746 (m : nat) : (term15 m) = (term16 m).
Proof. exact (fun_ext (fun n : nat => @lem135745 n m)). Qed.
Lemma lem135747 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem135748 (m : nat) : (term17 m) = (term18 m).
Proof. exact (MK_COMB (@lem135747) (@lem135746 m)). Qed.
Lemma lem135749 (m : nat) : (term19 m) = (term20 m).
Proof. exact (MK_COMB (@lem135740 m) (@lem135748 m)). Qed.
Lemma lem135750 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem135751 (m : nat) : (term21 m) = (term22 m).
Proof. exact (MK_COMB (@lem135750) (@lem135749 m)). Qed.
Lemma lem135752 (n : nat) (m : nat) : (term7 m n) = ((term8 m n) = m).
Proof. exact (eq_refl (term7 m n)). Qed.
Lemma lem135753 (m : nat) : (term23 m) = (term2 m).
Proof. exact (fun_ext (fun n : nat => @lem135752 n m)). Qed.
Lemma lem135754 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem135755 (m : nat) : (term24 m) = (term25 m).
Proof. exact (MK_COMB (@lem135754) (@lem135753 m)). Qed.
Lemma lem135756 (m : nat) : (term1 m) = (term26 m).
Proof. exact (MK_COMB (@lem135751 m) (@lem135755 m)). Qed.
Lemma lem135757 (m : nat) : term26 m.
Proof. exact (EQ_MP (@lem135756 m) (@lem135737 m)). Qed.
Lemma lem135759 (m : nat) : term27 m.
Proof. exact (@lem135231 m). Qed.
Lemma lem135760 (m : nat) : (term27 m) = (term28 m).
Proof. exact (eq_refl (term27 m)). Qed.
Lemma lem135761 (m : nat) : term28 m.
Proof. exact (EQ_MP (@lem135760 m) (@lem135759 m)). Qed.
Lemma lem135770 : term29.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem135786 : term30.
Proof. exact (proj1 (@lem135770)). Qed.
Lemma lem135787 (m : nat) : term31 m.
Proof. exact (@lem135786 m). Qed.
Lemma lem135788 (m : nat) : (term31 m) = ((term32 m) = m).
Proof. exact (eq_refl (term31 m)). Qed.
Lemma lem135797 (m : nat) : (term33 m) = m.
Proof. exact (proj2 (@lem135761 m)). Qed.
Lemma lem135798 (m : nat) : (term4 m) = (term32 m).
Proof. exact (@lem135797 (term32 m)). Qed.
Lemma lem135800 (m : nat) : (term32 m) = m.
Proof. exact (EQ_MP (@lem135788 m) (@lem135787 m)). Qed.
Lemma lem135801 (m : nat) : (term4 m) = m.
Proof. exact (TRANS (@lem135798 m) (@lem135800 m)). Qed.
Lemma lem135802 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem135803 (m : nat) : (term34 m) = (@eq nat m).
Proof. exact (MK_COMB (@lem135802) (@lem135801 m)). Qed.
Lemma lem135804 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem135805 (m : nat) : ((term4 m) = m) = (m = m).
Proof. exact (MK_COMB (@lem135803 m) (@lem135804 m)). Qed.
Lemma lem135807 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem135808 (x : nat) : (x = x) = True.
Proof. exact (@lem135807 nat x). Qed.
Lemma lem135809 (m : nat) : (m = m) = True.
Proof. exact (@lem135808 m). Qed.
Lemma lem135810 (m : nat) : ((term4 m) = m) = True.
Proof. exact (TRANS (@lem135805 m) (@lem135809 m)). Qed.
Lemma lem135811 (m : nat) : True = ((term4 m) = m).
Proof. exact (SYM (@lem135810 m)). Qed.
Lemma lem135812 (m : nat) : (term4 m) = m.
Proof. exact (EQ_MP (@lem135811 m) (@lem0)). Qed.
Lemma lem135818 (m : nat) : term35 m.
Proof. exact (@lem135645 m). Qed.
Lemma lem135819 (m : nat) : (term35 m) = (term36 m).
Proof. exact (eq_refl (term35 m)). Qed.
Lemma lem135820 (m : nat) : term36 m.
Proof. exact (EQ_MP (@lem135819 m) (@lem135818 m)). Qed.
Lemma lem135821 (m : nat) (n : nat) : term37 m n.
Proof. exact (@lem135820 m n). Qed.
Lemma lem135822 (m : nat) (n : nat) : (term37 m n) = ((term38 m n) = (Nat.sub m n)).
Proof. exact (eq_refl (term37 m n)). Qed.
Lemma lem135824 : term29.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem135825 : term39.
Proof. exact (proj2 (@lem135824)). Qed.
Lemma lem135826 : term40.
Proof. exact (proj2 (@lem135825)). Qed.
Lemma lem135827 (m : nat) : term41 m.
Proof. exact (@lem135826 m). Qed.
Lemma lem135828 (m : nat) : (term41 m) = (term42 m).
Proof. exact (eq_refl (term41 m)). Qed.
Lemma lem135829 (m : nat) : term42 m.
Proof. exact (EQ_MP (@lem135828 m) (@lem135827 m)). Qed.
Lemma lem135830 (m : nat) (n : nat) : term43 m n.
Proof. exact (@lem135829 m n). Qed.
Lemma lem135831 (m : nat) (n : nat) : (term43 m n) = ((term44 m n) = (term45 m n)).
Proof. exact (eq_refl (term43 m n)). Qed.
Lemma lem135851 (m : nat) (n : nat) : (term44 m n) = (term45 m n).
Proof. exact (EQ_MP (@lem135831 m n) (@lem135830 m n)). Qed.
Lemma lem135852 : Nat.sub = Nat.sub.
Proof. exact (eq_refl Nat.sub). Qed.
Lemma lem135853 (m : nat) (n : nat) : (term46 m n) = (term47 m n).
Proof. exact (MK_COMB (@lem135852) (@lem135851 m n)). Qed.
Lemma lem135854 (n : nat) : (S n) = (S n).
Proof. exact (eq_refl (S n)). Qed.
Lemma lem135855 (m : nat) (n : nat) : (term12 m n) = (term48 m n).
Proof. exact (MK_COMB (@lem135853 m n) (@lem135854 n)). Qed.
Lemma lem135857 (m : nat) (n : nat) : (term38 m n) = (Nat.sub m n).
Proof. exact (EQ_MP (@lem135822 m n) (@lem135821 m n)). Qed.
Lemma lem135858 (m : nat) (n : nat) : (term48 m n) = (term8 m n).
Proof. exact (@lem135857 (Nat.add m n) n). Qed.
Lemma lem135860 (n : nat) (m : nat) (h1 : (term8 m n) = m) : (term8 m n) = m.
Proof. exact (h1). Qed.
Lemma lem135861 (n : nat) (m : nat) (h1 : (term8 m n) = m) : (term48 m n) = m.
Proof. exact (TRANS (@lem135858 m n) (@lem135860 n m h1)). Qed.
Lemma lem135862 (n : nat) (m : nat) (h1 : (term8 m n) = m) : (term12 m n) = m.
Proof. exact (TRANS (@lem135855 m n) (@lem135861 n m h1)). Qed.
Lemma lem135863 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem135864 (n : nat) (m : nat) (h1 : (term8 m n) = m) : (term49 m n) = (@eq nat m).
Proof. exact (MK_COMB (@lem135863) (@lem135862 n m h1)). Qed.
Lemma lem135865 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem135866 (n : nat) (m : nat) (h1 : (term8 m n) = m) : ((term12 m n) = m) = (m = m).
Proof. exact (MK_COMB (@lem135864 n m h1) (@lem135865 m)). Qed.
Lemma lem135868 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem135869 (x : nat) : (x = x) = True.
Proof. exact (@lem135868 nat x). Qed.
Lemma lem135870 (m : nat) : (m = m) = True.
Proof. exact (@lem135869 m). Qed.
Lemma lem135871 (n : nat) (m : nat) (h1 : (term8 m n) = m) : ((term12 m n) = m) = True.
Proof. exact (TRANS (@lem135866 n m h1) (@lem135870 m)). Qed.
Lemma lem135872 (n : nat) (m : nat) (h1 : (term8 m n) = m) : True = ((term12 m n) = m).
Proof. exact (SYM (@lem135871 n m h1)). Qed.
Lemma lem135873 (n : nat) (m : nat) (h1 : (term8 m n) = m) : (term12 m n) = m.
Proof. exact (EQ_MP (@lem135872 n m h1) (@lem0)). Qed.
Lemma lem135874 (n : nat) (m : nat) : term14 n m.
Proof. exact (fun h0 : (term8 m n) = m => @lem135873 n m h0). Qed.
Lemma lem135879 (m : nat) : term18 m.
Proof. exact (fun n : nat => @lem135874 n m). Qed.
Lemma lem135880 (m : nat) : term20 m.
Proof. exact (conj (@lem135812 m) (@lem135879 m)). Qed.
Lemma lem135881 (m : nat) : term25 m.
Proof. exact (@lem135757 m (@lem135880 m)). Qed.
Lemma lem135886 : term50.
Proof. exact (fun m : nat => @lem135881 m). Qed.
