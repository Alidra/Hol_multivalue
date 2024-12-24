Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm155916_term_abbrevs.
Require Import thm155635_spec.
Require Import thm155860_spec.
Lemma lem155861 : term0 = term1.
Proof. exact (eq_refl term0). Qed.
Lemma lem155862 : term1.
Proof. exact (EQ_MP (@lem155861) (@lem155635)). Qed.
Lemma lem155863 : term2.
Proof. exact (@lem155862 term3). Qed.
Lemma lem155864 : term2 = term4.
Proof. exact (eq_refl term2). Qed.
Lemma lem155865 : term4.
Proof. exact (EQ_MP (@lem155864) (@lem155863)). Qed.
Lemma lem155866 (h1 : Nat.modulo = term5) : Nat.modulo = term5.
Proof. exact (h1). Qed.
Lemma lem155867 (h1 : Nat.modulo = term5) : term5 = Nat.modulo.
Proof. exact (SYM (@lem155866 h1)). Qed.
Lemma lem155868 (h1 : term5 = Nat.modulo) : term5 = Nat.modulo.
Proof. exact (h1). Qed.
Lemma lem155869 (h1 : term5 = Nat.modulo) : Nat.modulo = term5.
Proof. exact (SYM (@lem155868 h1)). Qed.
Lemma lem155870 : (Nat.modulo = term5) = (term5 = Nat.modulo).
Proof. exact (prop_ext (fun h1 : Nat.modulo = term5 => @lem155867 h1) (fun h1 : term5 = Nat.modulo => @lem155869 h1)). Qed.
Lemma lem155873 : term5 = Nat.modulo.
Proof. exact (EQ_MP (@lem155870) (@lem155860)). Qed.
Lemma lem155874 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem155875 (m : nat) : (term6 m) = (Nat.modulo m).
Proof. exact (MK_COMB (@lem155873) (@lem155874 m)). Qed.
Lemma lem155876 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem155877 (m : nat) (n : nat) : (term7 m n) = (Nat.modulo m n).
Proof. exact (MK_COMB (@lem155875 m) (@lem155876 n)). Qed.
Lemma lem155878 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem155879 (m : nat) (n : nat) : (term8 m n) = (term9 m n).
Proof. exact (MK_COMB (@lem155878) (@lem155877 m n)). Qed.
Lemma lem155880 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem155881 (n : nat) (m : nat) : ((term7 m n) = m) = ((Nat.modulo m n) = m).
Proof. exact (MK_COMB (@lem155879 m n) (@lem155880 m)). Qed.
Lemma lem155882 (m : nat) (n : nat) : (term10 m n) = (term10 m n).
Proof. exact (eq_refl (term10 m n)). Qed.
Lemma lem155883 (n : nat) (m : nat) : (term11 n m) = (term12 n m).
Proof. exact (MK_COMB (@lem155882 m n) (@lem155881 n m)). Qed.
Lemma lem155884 (n : nat) : (term13 n) = (term13 n).
Proof. exact (eq_refl (term13 n)). Qed.
Lemma lem155885 (n : nat) (m : nat) : (term14 n m) = (term15 n m).
Proof. exact (MK_COMB (@lem155884 n) (@lem155883 n m)). Qed.
Lemma lem155887 : term5 = Nat.modulo.
Proof. exact (EQ_MP (@lem155870) (@lem155860)). Qed.
Lemma lem155888 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem155889 (m : nat) : (term6 m) = (Nat.modulo m).
Proof. exact (MK_COMB (@lem155887) (@lem155888 m)). Qed.
Lemma lem155890 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem155891 (m : nat) (n : nat) : (term7 m n) = (Nat.modulo m n).
Proof. exact (MK_COMB (@lem155889 m) (@lem155890 n)). Qed.
Lemma lem155892 (m : nat) (n : nat) : (term16 m n) = (term16 m n).
Proof. exact (eq_refl (term16 m n)). Qed.
Lemma lem155893 (m : nat) (n : nat) : (term17 m n) = (term18 m n).
Proof. exact (MK_COMB (@lem155892 m n) (@lem155891 m n)). Qed.
Lemma lem155894 (m : nat) : (@eq nat m) = (@eq nat m).
Proof. exact (eq_refl (@eq nat m)). Qed.
Lemma lem155895 (m : nat) (n : nat) : (m = (term17 m n)) = (m = (term18 m n)).
Proof. exact (MK_COMB (@lem155894 m) (@lem155893 m n)). Qed.
Lemma lem155896 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem155897 (m : nat) (n : nat) : (term19 m n) = (term20 m n).
Proof. exact (MK_COMB (@lem155896) (@lem155895 m n)). Qed.
Lemma lem155899 : term5 = Nat.modulo.
Proof. exact (EQ_MP (@lem155870) (@lem155860)). Qed.
Lemma lem155900 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem155901 (m : nat) : (term6 m) = (Nat.modulo m).
Proof. exact (MK_COMB (@lem155899) (@lem155900 m)). Qed.
Lemma lem155902 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem155903 (m : nat) (n : nat) : (term7 m n) = (Nat.modulo m n).
Proof. exact (MK_COMB (@lem155901 m) (@lem155902 n)). Qed.
Lemma lem155904 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem155905 (m : nat) (n : nat) : (term21 m n) = (term22 m n).
Proof. exact (MK_COMB (@lem155904) (@lem155903 m n)). Qed.
Lemma lem155906 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem155907 (m : nat) (n : nat) : (term23 m n) = (term24 m n).
Proof. exact (MK_COMB (@lem155905 m n) (@lem155906 n)). Qed.
Lemma lem155908 (m : nat) (n : nat) : (term25 m n) = (term26 m n).
Proof. exact (MK_COMB (@lem155897 m n) (@lem155907 m n)). Qed.
Lemma lem155909 (m : nat) (n : nat) : (term27 m n) = (term28 m n).
Proof. exact (MK_COMB (@lem155885 n m) (@lem155908 m n)). Qed.
Lemma lem155910 (m : nat) : (term29 m) = (term30 m).
Proof. exact (fun_ext (fun n : nat => @lem155909 m n)). Qed.
Lemma lem155911 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem155912 (m : nat) : (term31 m) = (term32 m).
Proof. exact (MK_COMB (@lem155911) (@lem155910 m)). Qed.
Lemma lem155913 : term33 = term34.
Proof. exact (fun_ext (fun m : nat => @lem155912 m)). Qed.
Lemma lem155914 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem155915 : term4 = term35.
Proof. exact (MK_COMB (@lem155914) (@lem155913)). Qed.
Lemma lem155916 : term35.
Proof. exact (EQ_MP (@lem155915) (@lem155865)). Qed.
