Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ADD_SUB2_term_abbrevs.
Require Import ADD_SUB_spec.
Require Import ADD_SYM_spec.
Lemma lem135887 (m : nat) : term0 m.
Proof. exact (@lem77775 m). Qed.
Lemma lem135888 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem135889 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem135888 m) (@lem135887 m)). Qed.
Lemma lem135890 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem135889 m n). Qed.
Lemma lem135891 (n : nat) (m : nat) : (term2 m n) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem135904 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem135891 n m) (@lem135890 m n)). Qed.
Lemma lem135905 : Nat.sub = Nat.sub.
Proof. exact (eq_refl Nat.sub). Qed.
Lemma lem135906 (n : nat) (m : nat) : (term3 m n) = (term3 n m).
Proof. exact (MK_COMB (@lem135905) (@lem135904 n m)). Qed.
Lemma lem135907 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem135908 (n : nat) (m : nat) : (term4 n m) = (term5 n m).
Proof. exact (MK_COMB (@lem135906 n m) (@lem135907 m)). Qed.
Lemma lem135909 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem135910 (n : nat) (m : nat) : (term6 n m) = (term7 n m).
Proof. exact (MK_COMB (@lem135909) (@lem135908 n m)). Qed.
Lemma lem135911 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem135912 (m : nat) (n : nat) : ((term4 n m) = n) = ((term5 n m) = n).
Proof. exact (MK_COMB (@lem135910 n m) (@lem135911 n)). Qed.
Lemma lem135913 (m : nat) : (term8 m) = (term9 m).
Proof. exact (fun_ext (fun n : nat => @lem135912 m n)). Qed.
Lemma lem135914 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem135915 (m : nat) : (term10 m) = (term11 m).
Proof. exact (MK_COMB (@lem135914) (@lem135913 m)). Qed.
Lemma lem135916 : term12 = term13.
Proof. exact (fun_ext (fun m : nat => @lem135915 m)). Qed.
Lemma lem135917 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem135918 : term14 = term15.
Proof. exact (MK_COMB (@lem135917) (@lem135916)). Qed.
Lemma lem135919 : term15 = term14.
Proof. exact (SYM (@lem135918)). Qed.
Lemma lem135920 (m : nat) : term16 m.
Proof. exact (@lem135886 m). Qed.
Lemma lem135921 (m : nat) : (term16 m) = (term17 m).
Proof. exact (eq_refl (term16 m)). Qed.
Lemma lem135922 (m : nat) : term17 m.
Proof. exact (EQ_MP (@lem135921 m) (@lem135920 m)). Qed.
Lemma lem135923 (m : nat) (n : nat) : term18 m n.
Proof. exact (@lem135922 m n). Qed.
Lemma lem135924 (n : nat) (m : nat) : (term18 m n) = ((term5 m n) = m).
Proof. exact (eq_refl (term18 m n)). Qed.
Lemma lem135927 (n : nat) (m : nat) : (term5 m n) = m.
Proof. exact (EQ_MP (@lem135924 n m) (@lem135923 m n)). Qed.
Lemma lem135928 (m : nat) (n : nat) : (term5 n m) = n.
Proof. exact (@lem135927 m n). Qed.
Lemma lem135933 (m : nat) : term11 m.
Proof. exact (fun n : nat => @lem135928 m n). Qed.
Lemma lem135938 : term15.
Proof. exact (fun m : nat => @lem135933 m). Qed.
Lemma lem135939 : term14.
Proof. exact (EQ_MP (@lem135919) (@lem135938)). Qed.
