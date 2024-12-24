Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIST_RZERO_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import SUB_0_spec.
Require Import dist_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1244860 : term0.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem1244876 : term1.
Proof. exact (proj1 (@lem1244860)). Qed.
Lemma lem1244877 (m : nat) : term2 m.
Proof. exact (@lem1244876 m). Qed.
Lemma lem1244878 (m : nat) : (term2 m) = ((term3 m) = m).
Proof. exact (eq_refl (term2 m)). Qed.
Lemma lem1244884 (m : nat) : term4 m.
Proof. exact (@lem135231 m). Qed.
Lemma lem1244885 (m : nat) : (term4 m) = (term5 m).
Proof. exact (eq_refl (term4 m)). Qed.
Lemma lem1244886 (m : nat) : term5 m.
Proof. exact (EQ_MP (@lem1244885 m) (@lem1244884 m)). Qed.
Lemma lem1244889 (n : nat) : term6 n.
Proof. exact (@lem1244710 n). Qed.
Lemma lem1244890 (n : nat) : (term6 n) = (term7 n).
Proof. exact (eq_refl (term6 n)). Qed.
Lemma lem1244891 (n : nat) : term7 n.
Proof. exact (EQ_MP (@lem1244890 n) (@lem1244889 n)). Qed.
Lemma lem1244892 (n : nat) (m : nat) : term8 n m.
Proof. exact (@lem1244891 n m). Qed.
Lemma lem1244893 (n : nat) (m : nat) : (term8 n m) = ((term9 m n) = (term10 n m)).
Proof. exact (eq_refl (term8 n m)). Qed.
Lemma lem1244902 (n : nat) (m : nat) : (term9 m n) = (term10 n m).
Proof. exact (EQ_MP (@lem1244893 n m) (@lem1244892 n m)). Qed.
Lemma lem1244903 (n : nat) : (term11 n) = (term12 n).
Proof. exact (@lem1244902 (NUMERAL 0) n). Qed.
Lemma lem1244905 (m : nat) : (term13 m) = m.
Proof. exact (proj2 (@lem1244886 m)). Qed.
Lemma lem1244906 (n : nat) : (term13 n) = n.
Proof. exact (@lem1244905 n). Qed.
Lemma lem1244907 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1244908 (n : nat) : (term14 n) = (Nat.add n).
Proof. exact (MK_COMB (@lem1244907) (@lem1244906 n)). Qed.
Lemma lem1244910 (m : nat) : (term15 m) = (NUMERAL 0).
Proof. exact (proj1 (@lem1244886 m)). Qed.
Lemma lem1244911 (n : nat) : (term15 n) = (NUMERAL 0).
Proof. exact (@lem1244910 n). Qed.
Lemma lem1244912 (n : nat) : (term12 n) = (term3 n).
Proof. exact (MK_COMB (@lem1244908 n) (@lem1244911 n)). Qed.
Lemma lem1244914 (m : nat) : (term3 m) = m.
Proof. exact (EQ_MP (@lem1244878 m) (@lem1244877 m)). Qed.
Lemma lem1244915 (n : nat) : (term3 n) = n.
Proof. exact (@lem1244914 n). Qed.
Lemma lem1244916 (n : nat) : (term12 n) = n.
Proof. exact (TRANS (@lem1244912 n) (@lem1244915 n)). Qed.
Lemma lem1244917 (n : nat) : (term11 n) = n.
Proof. exact (TRANS (@lem1244903 n) (@lem1244916 n)). Qed.
Lemma lem1244918 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1244919 (n : nat) : (term16 n) = (@eq nat n).
Proof. exact (MK_COMB (@lem1244918) (@lem1244917 n)). Qed.
Lemma lem1244920 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1244921 (n : nat) : ((term11 n) = n) = (n = n).
Proof. exact (MK_COMB (@lem1244919 n) (@lem1244920 n)). Qed.
Lemma lem1244923 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1244924 (x : nat) : (x = x) = True.
Proof. exact (@lem1244923 nat x). Qed.
Lemma lem1244925 (n : nat) : (n = n) = True.
Proof. exact (@lem1244924 n). Qed.
Lemma lem1244926 (n : nat) : ((term11 n) = n) = True.
Proof. exact (TRANS (@lem1244921 n) (@lem1244925 n)). Qed.
Lemma lem1244927 : term17 = term18.
Proof. exact (fun_ext (fun n : nat => @lem1244926 n)). Qed.
Lemma lem1244928 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1244929 : term19 = term20.
Proof. exact (MK_COMB (@lem1244928) (@lem1244927)). Qed.
Lemma lem1244931 {A : Type'} (t : Prop) : (term21 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1244932 (t : Prop) : (term22 t) = t.
Proof. exact (@lem1244931 nat t). Qed.
Lemma lem1244933 : term20 = True.
Proof. exact (@lem1244932 True). Qed.
Lemma lem1244934 : term19 = True.
Proof. exact (TRANS (@lem1244929) (@lem1244933)). Qed.
Lemma lem1244935 : True = term19.
Proof. exact (SYM (@lem1244934)). Qed.
Lemma lem1244936 : term19.
Proof. exact (EQ_MP (@lem1244935) (@lem0)). Qed.
