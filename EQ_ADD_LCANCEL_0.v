Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EQ_ADD_LCANCEL_0_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import SUC_INJ_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Lemma lem79716 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem79717 : term1.
Proof. exact (@lem79716 term2). Qed.
Lemma lem79718 : term3 = term4.
Proof. exact (eq_refl term3). Qed.
Lemma lem79719 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem79720 : term5 = term6.
Proof. exact (MK_COMB (@lem79719) (@lem79718)). Qed.
Lemma lem79721 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem79722 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem79723 (m : nat) : (term9 m) = (term10 m).
Proof. exact (MK_COMB (@lem79722) (@lem79721 m)). Qed.
Lemma lem79724 (m : nat) : (term11 m) = (term12 m).
Proof. exact (eq_refl (term11 m)). Qed.
Lemma lem79725 (m : nat) : (term13 m) = (term14 m).
Proof. exact (MK_COMB (@lem79723 m) (@lem79724 m)). Qed.
Lemma lem79726 : term15 = term16.
Proof. exact (fun_ext (fun m : nat => @lem79725 m)). Qed.
Lemma lem79727 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem79728 : term17 = term18.
Proof. exact (MK_COMB (@lem79727) (@lem79726)). Qed.
Lemma lem79729 : term19 = term20.
Proof. exact (MK_COMB (@lem79720) (@lem79728)). Qed.
Lemma lem79730 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem79731 : term21 = term22.
Proof. exact (MK_COMB (@lem79730) (@lem79729)). Qed.
Lemma lem79732 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem79733 : term23 = term2.
Proof. exact (fun_ext (fun m : nat => @lem79732 m)). Qed.
Lemma lem79734 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem79735 : term24 = term25.
Proof. exact (MK_COMB (@lem79734) (@lem79733)). Qed.
Lemma lem79736 : term1 = term26.
Proof. exact (MK_COMB (@lem79731) (@lem79735)). Qed.
Lemma lem79737 : term26.
Proof. exact (EQ_MP (@lem79736) (@lem79717)). Qed.
Lemma lem79738 (m : nat) (h1 : term8 m) : term8 m.
Proof. exact (h1). Qed.
Lemma lem79765 : term27.
Proof. exact (proj1 (@lem77629)). Qed.
Lemma lem79766 (n : nat) : term28 n.
Proof. exact (@lem79765 n). Qed.
Lemma lem79767 (n : nat) : (term28 n) = ((term29 n) = n).
Proof. exact (eq_refl (term28 n)). Qed.
Lemma lem79778 (n : nat) : (term29 n) = n.
Proof. exact (EQ_MP (@lem79767 n) (@lem79766 n)). Qed.
Lemma lem79779 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem79780 (n : nat) : (term30 n) = (@eq nat n).
Proof. exact (MK_COMB (@lem79779) (@lem79778 n)). Qed.
Lemma lem79781 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem79782 (n : nat) : ((term29 n) = (NUMERAL 0)) = (n = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem79780 n) (@lem79781)). Qed.
Lemma lem79785 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem79786 (n : nat) : (term31 n) = (term32 n).
Proof. exact (MK_COMB (@lem79785) (@lem79782 n)). Qed.
Lemma lem79789 (n : nat) : (n = (NUMERAL 0)) = (n = (NUMERAL 0)).
Proof. exact (eq_refl (n = (NUMERAL 0))). Qed.
Lemma lem79790 (n : nat) : (((term29 n) = (NUMERAL 0)) = (n = (NUMERAL 0))) = ((n = (NUMERAL 0)) = (n = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem79786 n) (@lem79789 n)). Qed.
Lemma lem79792 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem79793 (x : Prop) : (x = x) = True.
Proof. exact (@lem79792 Prop x). Qed.
Lemma lem79794 (n : nat) : ((n = (NUMERAL 0)) = (n = (NUMERAL 0))) = True.
Proof. exact (@lem79793 (n = (NUMERAL 0))). Qed.
Lemma lem79795 (n : nat) : (((term29 n) = (NUMERAL 0)) = (n = (NUMERAL 0))) = True.
Proof. exact (TRANS (@lem79790 n) (@lem79794 n)). Qed.
Lemma lem79796 : term33 = term34.
Proof. exact (fun_ext (fun n : nat => @lem79795 n)). Qed.
Lemma lem79797 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem79798 : term4 = term35.
Proof. exact (MK_COMB (@lem79797) (@lem79796)). Qed.
Lemma lem79800 {A : Type'} (t : Prop) : (term36 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem79801 (t : Prop) : (term37 t) = t.
Proof. exact (@lem79800 nat t). Qed.
Lemma lem79802 : term35 = True.
Proof. exact (@lem79801 True). Qed.
Lemma lem79803 : term4 = True.
Proof. exact (TRANS (@lem79798) (@lem79802)). Qed.
Lemma lem79804 : True = term4.
Proof. exact (SYM (@lem79803)). Qed.
Lemma lem79805 : term4.
Proof. exact (EQ_MP (@lem79804) (@lem0)). Qed.
Lemma lem79806 (m : nat) : term38 m.
Proof. exact (@lem72973 m). Qed.
Lemma lem79807 (m : nat) : (term38 m) = (term39 m).
Proof. exact (eq_refl (term38 m)). Qed.
Lemma lem79808 (m : nat) : term39 m.
Proof. exact (EQ_MP (@lem79807 m) (@lem79806 m)). Qed.
Lemma lem79809 (m : nat) (n : nat) : term40 m n.
Proof. exact (@lem79808 m n). Qed.
Lemma lem79810 (m : nat) (n : nat) : (term40 m n) = (((S m) = (S n)) = (m = n)).
Proof. exact (eq_refl (term40 m n)). Qed.
Lemma lem79812 : term41.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem79813 : term42.
Proof. exact (proj2 (@lem79812)). Qed.
Lemma lem79821 : term43.
Proof. exact (proj1 (@lem79813)). Qed.
Lemma lem79822 (m : nat) : term44 m.
Proof. exact (@lem79821 m). Qed.
Lemma lem79823 (m : nat) : (term44 m) = (term45 m).
Proof. exact (eq_refl (term44 m)). Qed.
Lemma lem79824 (m : nat) : term45 m.
Proof. exact (EQ_MP (@lem79823 m) (@lem79822 m)). Qed.
Lemma lem79825 (m : nat) (n : nat) : term46 m n.
Proof. exact (@lem79824 m n). Qed.
Lemma lem79826 (m : nat) (n : nat) : (term46 m n) = ((term47 m n) = (term48 m n)).
Proof. exact (eq_refl (term46 m n)). Qed.
Lemma lem79836 (n : nat) (m : nat) (h1 : term8 m) : term49 m n.
Proof. exact (@lem79738 m h1 n). Qed.
Lemma lem79837 (m : nat) (n : nat) : (term49 m n) = (((Nat.add m n) = m) = (n = (NUMERAL 0))).
Proof. exact (eq_refl (term49 m n)). Qed.
Lemma lem79848 (m : nat) (n : nat) : (term47 m n) = (term48 m n).
Proof. exact (EQ_MP (@lem79826 m n) (@lem79825 m n)). Qed.
Lemma lem79849 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem79850 (m : nat) (n : nat) : (term50 m n) = (term51 m n).
Proof. exact (MK_COMB (@lem79849) (@lem79848 m n)). Qed.
Lemma lem79851 (m : nat) : (S m) = (S m).
Proof. exact (eq_refl (S m)). Qed.
Lemma lem79852 (n : nat) (m : nat) : ((term47 m n) = (S m)) = ((term48 m n) = (S m)).
Proof. exact (MK_COMB (@lem79850 m n) (@lem79851 m)). Qed.
Lemma lem79854 (m : nat) (n : nat) : ((S m) = (S n)) = (m = n).
Proof. exact (EQ_MP (@lem79810 m n) (@lem79809 m n)). Qed.
Lemma lem79855 (n : nat) (m : nat) : ((term48 m n) = (S m)) = ((Nat.add m n) = m).
Proof. exact (@lem79854 (Nat.add m n) m). Qed.
Lemma lem79857 (n : nat) (m : nat) (h1 : term8 m) : ((Nat.add m n) = m) = (n = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem79837 m n) (@lem79836 n m h1)). Qed.
Lemma lem79860 (n : nat) (m : nat) (h1 : term8 m) : ((term48 m n) = (S m)) = (n = (NUMERAL 0)).
Proof. exact (TRANS (@lem79855 n m) (@lem79857 n m h1)). Qed.
Lemma lem79861 (n : nat) (m : nat) (h1 : term8 m) : ((term47 m n) = (S m)) = (n = (NUMERAL 0)).
Proof. exact (TRANS (@lem79852 n m) (@lem79860 n m h1)). Qed.
Lemma lem79862 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem79863 (n : nat) (m : nat) (h1 : term8 m) : (term52 n m) = (term32 n).
Proof. exact (MK_COMB (@lem79862) (@lem79861 n m h1)). Qed.
Lemma lem79866 (n : nat) : (n = (NUMERAL 0)) = (n = (NUMERAL 0)).
Proof. exact (eq_refl (n = (NUMERAL 0))). Qed.
Lemma lem79867 (n : nat) (m : nat) (h1 : term8 m) : (((term47 m n) = (S m)) = (n = (NUMERAL 0))) = ((n = (NUMERAL 0)) = (n = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem79863 n m h1) (@lem79866 n)). Qed.
Lemma lem79869 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem79870 (x : Prop) : (x = x) = True.
Proof. exact (@lem79869 Prop x). Qed.
Lemma lem79871 (n : nat) : ((n = (NUMERAL 0)) = (n = (NUMERAL 0))) = True.
Proof. exact (@lem79870 (n = (NUMERAL 0))). Qed.
Lemma lem79872 (n : nat) (m : nat) (h1 : term8 m) : (((term47 m n) = (S m)) = (n = (NUMERAL 0))) = True.
Proof. exact (TRANS (@lem79867 n m h1) (@lem79871 n)). Qed.
Lemma lem79873 (m : nat) (h1 : term8 m) : (term53 m) = term34.
Proof. exact (fun_ext (fun n : nat => @lem79872 n m h1)). Qed.
Lemma lem79874 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem79875 (m : nat) (h1 : term8 m) : (term12 m) = term35.
Proof. exact (MK_COMB (@lem79874) (@lem79873 m h1)). Qed.
Lemma lem79877 {A : Type'} (t : Prop) : (term36 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem79878 (t : Prop) : (term37 t) = t.
Proof. exact (@lem79877 nat t). Qed.
Lemma lem79879 : term35 = True.
Proof. exact (@lem79878 True). Qed.
Lemma lem79880 (m : nat) (h1 : term8 m) : (term12 m) = True.
Proof. exact (TRANS (@lem79875 m h1) (@lem79879)). Qed.
Lemma lem79881 (m : nat) (h1 : term8 m) : True = (term12 m).
Proof. exact (SYM (@lem79880 m h1)). Qed.
Lemma lem79882 (m : nat) (h1 : term8 m) : term12 m.
Proof. exact (EQ_MP (@lem79881 m h1) (@lem0)). Qed.
Lemma lem79883 (m : nat) : term14 m.
Proof. exact (fun h0 : term8 m => @lem79882 m h0). Qed.
Lemma lem79888 : term18.
Proof. exact (fun m : nat => @lem79883 m). Qed.
Lemma lem79889 : term20.
Proof. exact (conj (@lem79805) (@lem79888)). Qed.
Lemma lem79890 : term25.
Proof. exact (@lem79737 (@lem79889)). Qed.
