Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MOD_MOD_REFL_term_abbrevs.
Require Import EXCLUDED_MIDDLE_spec.
Require Import MOD_MOD_spec.
Require Import MOD_ZERO_spec.
Require Import MULT_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm1823_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem182836 (m : nat) : term0 m.
Proof. exact (@lem182819 m). Qed.
Lemma lem182837 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem182838 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem182837 m) (@lem182836 m)). Qed.
Lemma lem182839 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem182838 m n). Qed.
Lemma lem182840 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem182841 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem182840 m n) (@lem182839 m n)). Qed.
Lemma lem182842 (m : nat) (n : nat) : term4 m n.
Proof. exact (@lem182841 m n term5). Qed.
Lemma lem182843 (m : nat) (n : nat) : (term4 m n) = ((term6 m n) = (Nat.modulo m n)).
Proof. exact (eq_refl (term4 m n)). Qed.
Lemma lem182844 (m : nat) (n : nat) : (term6 m n) = (Nat.modulo m n).
Proof. exact (EQ_MP (@lem182843 m n) (@lem182842 m n)). Qed.
Lemma lem182845 (n : nat) : term7 n.
Proof. exact (@lem9784 (n = (NUMERAL 0))). Qed.
Lemma lem182846 (n : nat) : (term7 n) = (term8 n).
Proof. exact (eq_refl (term7 n)). Qed.
Lemma lem182847 (n : nat) : term8 n.
Proof. exact (EQ_MP (@lem182846 n) (@lem182845 n)). Qed.
Lemma lem182850 (n : nat) : term9 n.
Proof. exact (@lem159121 n). Qed.
Lemma lem182851 (n : nat) : (term9 n) = ((term10 n) = n).
Proof. exact (eq_refl (term9 n)). Qed.
Lemma lem182856 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem182857 (m : nat) : (Nat.modulo m) = (Nat.modulo m).
Proof. exact (eq_refl (Nat.modulo m)). Qed.
Lemma lem182858 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.modulo m n) = (term10 m).
Proof. exact (MK_COMB (@lem182857 m) (@lem182856 n h1)). Qed.
Lemma lem182860 (n : nat) : (term10 n) = n.
Proof. exact (EQ_MP (@lem182851 n) (@lem182850 n)). Qed.
Lemma lem182861 (m : nat) : (term10 m) = m.
Proof. exact (@lem182860 m). Qed.
Lemma lem182862 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.modulo m n) = m.
Proof. exact (TRANS (@lem182858 m n h1) (@lem182861 m)). Qed.
Lemma lem182863 : Nat.modulo = Nat.modulo.
Proof. exact (eq_refl Nat.modulo). Qed.
Lemma lem182864 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term11 m n) = (Nat.modulo m).
Proof. exact (MK_COMB (@lem182863) (@lem182862 m n h1)). Qed.
Lemma lem182866 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem182867 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term12 m n) = (term10 m).
Proof. exact (MK_COMB (@lem182864 m n h1) (@lem182866 n h1)). Qed.
Lemma lem182869 (n : nat) : (term10 n) = n.
Proof. exact (EQ_MP (@lem182851 n) (@lem182850 n)). Qed.
Lemma lem182870 (m : nat) : (term10 m) = m.
Proof. exact (@lem182869 m). Qed.
Lemma lem182871 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term12 m n) = m.
Proof. exact (TRANS (@lem182867 m n h1) (@lem182870 m)). Qed.
Lemma lem182872 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem182873 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term13 m n) = (@eq nat m).
Proof. exact (MK_COMB (@lem182872) (@lem182871 m n h1)). Qed.
Lemma lem182875 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem182876 (m : nat) : (Nat.modulo m) = (Nat.modulo m).
Proof. exact (eq_refl (Nat.modulo m)). Qed.
Lemma lem182877 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.modulo m n) = (term10 m).
Proof. exact (MK_COMB (@lem182876 m) (@lem182875 n h1)). Qed.
Lemma lem182879 (n : nat) : (term10 n) = n.
Proof. exact (EQ_MP (@lem182851 n) (@lem182850 n)). Qed.
Lemma lem182880 (m : nat) : (term10 m) = m.
Proof. exact (@lem182879 m). Qed.
Lemma lem182881 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.modulo m n) = m.
Proof. exact (TRANS (@lem182877 m n h1) (@lem182880 m)). Qed.
Lemma lem182882 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : ((term12 m n) = (Nat.modulo m n)) = (m = m).
Proof. exact (MK_COMB (@lem182873 m n h1) (@lem182881 m n h1)). Qed.
Lemma lem182884 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem182885 (x : nat) : (x = x) = True.
Proof. exact (@lem182884 nat x). Qed.
Lemma lem182886 (m : nat) : (m = m) = True.
Proof. exact (@lem182885 m). Qed.
Lemma lem182887 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : ((term12 m n) = (Nat.modulo m n)) = True.
Proof. exact (TRANS (@lem182882 m n h1) (@lem182886 m)). Qed.
Lemma lem182888 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : True = ((term12 m n) = (Nat.modulo m n)).
Proof. exact (SYM (@lem182887 m n h1)). Qed.
Lemma lem182889 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term12 m n) = (Nat.modulo m n).
Proof. exact (EQ_MP (@lem182888 m n h1) (@lem0)). Qed.
Lemma lem182916 : term14.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem182917 : term15.
Proof. exact (proj2 (@lem182916)). Qed.
Lemma lem182918 : term16.
Proof. exact (proj2 (@lem182917)). Qed.
Lemma lem182934 : term17.
Proof. exact (proj1 (@lem182918)). Qed.
Lemma lem182935 (m : nat) : term18 m.
Proof. exact (@lem182934 m). Qed.
Lemma lem182936 (m : nat) : (term18 m) = ((term19 m) = m).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem182970 (m : nat) : (term19 m) = m.
Proof. exact (EQ_MP (@lem182936 m) (@lem182935 m)). Qed.
Lemma lem182971 (n : nat) : (term19 n) = n.
Proof. exact (@lem182970 n). Qed.
Lemma lem182972 (m : nat) : (Nat.modulo m) = (Nat.modulo m).
Proof. exact (eq_refl (Nat.modulo m)). Qed.
Lemma lem182973 (m : nat) (n : nat) : (term20 m n) = (Nat.modulo m n).
Proof. exact (MK_COMB (@lem182972 m) (@lem182971 n)). Qed.
Lemma lem182974 : Nat.modulo = Nat.modulo.
Proof. exact (eq_refl Nat.modulo). Qed.
Lemma lem182975 (m : nat) (n : nat) : (term21 m n) = (term11 m n).
Proof. exact (MK_COMB (@lem182974) (@lem182973 m n)). Qed.
Lemma lem182976 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem182977 (m : nat) (n : nat) : (term6 m n) = (term12 m n).
Proof. exact (MK_COMB (@lem182975 m n) (@lem182976 n)). Qed.
Lemma lem182978 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem182979 (m : nat) (n : nat) : (term22 m n) = (term13 m n).
Proof. exact (MK_COMB (@lem182978) (@lem182977 m n)). Qed.
Lemma lem182980 (m : nat) (n : nat) : (Nat.modulo m n) = (Nat.modulo m n).
Proof. exact (eq_refl (Nat.modulo m n)). Qed.
Lemma lem182981 (m : nat) (n : nat) : ((term6 m n) = (Nat.modulo m n)) = ((term12 m n) = (Nat.modulo m n)).
Proof. exact (MK_COMB (@lem182979 m n) (@lem182980 m n)). Qed.
Lemma lem182984 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem182985 (m : nat) (n : nat) : (term23 m n) = (term24 m n).
Proof. exact (MK_COMB (@lem182984) (@lem182981 m n)). Qed.
Lemma lem182988 (m : nat) (n : nat) : ((term12 m n) = (Nat.modulo m n)) = ((term12 m n) = (Nat.modulo m n)).
Proof. exact (eq_refl ((term12 m n) = (Nat.modulo m n))). Qed.
Lemma lem182989 (m : nat) (n : nat) : (term25 m n) = (term26 m n).
Proof. exact (MK_COMB (@lem182985 m n) (@lem182988 m n)). Qed.
Lemma lem182993 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem182994 (m : nat) (n : nat) : (term26 m n) = True.
Proof. exact (@lem182993 ((term12 m n) = (Nat.modulo m n))). Qed.
Lemma lem182995 (m : nat) (n : nat) : (term25 m n) = True.
Proof. exact (TRANS (@lem182989 m n) (@lem182994 m n)). Qed.
Lemma lem182996 (m : nat) (n : nat) : True = (term25 m n).
Proof. exact (SYM (@lem182995 m n)). Qed.
Lemma lem182997 (m : nat) (n : nat) : term25 m n.
Proof. exact (EQ_MP (@lem182996 m n) (@lem0)). Qed.
Lemma lem182999 (m : nat) (n : nat) : (term12 m n) = (Nat.modulo m n).
Proof. exact (@lem182997 m n (@lem182844 m n)). Qed.
Lemma lem183000 (m : nat) (n : nat) : (term12 m n) = (Nat.modulo m n).
Proof. exact (or_elim (@lem182847 n) (fun h0 : n = (NUMERAL 0) => @lem182889 m n h0) (fun h0 : term27 n => @lem182999 m n)). Qed.
Lemma lem183005 (m : nat) : term28 m.
Proof. exact (fun n : nat => @lem183000 m n). Qed.
Lemma lem183010 : term29.
Proof. exact (fun m : nat => @lem183005 m). Qed.
