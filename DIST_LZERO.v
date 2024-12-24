Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIST_LZERO_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import SUB_0_spec.
Require Import dist_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1244804 : term0.
Proof. exact (proj1 (@lem77629)). Qed.
Lemma lem1244805 (n : nat) : term1 n.
Proof. exact (@lem1244804 n). Qed.
Lemma lem1244806 (n : nat) : (term1 n) = ((term2 n) = n).
Proof. exact (eq_refl (term1 n)). Qed.
Lemma lem1244808 (m : nat) : term3 m.
Proof. exact (@lem135231 m). Qed.
Lemma lem1244809 (m : nat) : (term3 m) = (term4 m).
Proof. exact (eq_refl (term3 m)). Qed.
Lemma lem1244810 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem1244809 m) (@lem1244808 m)). Qed.
Lemma lem1244813 (n : nat) : term5 n.
Proof. exact (@lem1244710 n). Qed.
Lemma lem1244814 (n : nat) : (term5 n) = (term6 n).
Proof. exact (eq_refl (term5 n)). Qed.
Lemma lem1244815 (n : nat) : term6 n.
Proof. exact (EQ_MP (@lem1244814 n) (@lem1244813 n)). Qed.
Lemma lem1244816 (n : nat) (m : nat) : term7 n m.
Proof. exact (@lem1244815 n m). Qed.
Lemma lem1244817 (n : nat) (m : nat) : (term7 n m) = ((term8 m n) = (term9 n m)).
Proof. exact (eq_refl (term7 n m)). Qed.
Lemma lem1244826 (n : nat) (m : nat) : (term8 m n) = (term9 n m).
Proof. exact (EQ_MP (@lem1244817 n m) (@lem1244816 n m)). Qed.
Lemma lem1244827 (n : nat) : (term10 n) = (term11 n).
Proof. exact (@lem1244826 n (NUMERAL 0)). Qed.
Lemma lem1244829 (m : nat) : (term12 m) = (NUMERAL 0).
Proof. exact (proj1 (@lem1244810 m)). Qed.
Lemma lem1244830 (n : nat) : (term12 n) = (NUMERAL 0).
Proof. exact (@lem1244829 n). Qed.
Lemma lem1244831 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1244832 (n : nat) : (term13 n) = term14.
Proof. exact (MK_COMB (@lem1244831) (@lem1244830 n)). Qed.
Lemma lem1244834 (m : nat) : (term15 m) = m.
Proof. exact (proj2 (@lem1244810 m)). Qed.
Lemma lem1244835 (n : nat) : (term15 n) = n.
Proof. exact (@lem1244834 n). Qed.
Lemma lem1244836 (n : nat) : (term11 n) = (term2 n).
Proof. exact (MK_COMB (@lem1244832 n) (@lem1244835 n)). Qed.
Lemma lem1244838 (n : nat) : (term2 n) = n.
Proof. exact (EQ_MP (@lem1244806 n) (@lem1244805 n)). Qed.
Lemma lem1244839 (n : nat) : (term11 n) = n.
Proof. exact (TRANS (@lem1244836 n) (@lem1244838 n)). Qed.
Lemma lem1244840 (n : nat) : (term10 n) = n.
Proof. exact (TRANS (@lem1244827 n) (@lem1244839 n)). Qed.
Lemma lem1244841 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1244842 (n : nat) : (term16 n) = (@eq nat n).
Proof. exact (MK_COMB (@lem1244841) (@lem1244840 n)). Qed.
Lemma lem1244843 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1244844 (n : nat) : ((term10 n) = n) = (n = n).
Proof. exact (MK_COMB (@lem1244842 n) (@lem1244843 n)). Qed.
Lemma lem1244846 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1244847 (x : nat) : (x = x) = True.
Proof. exact (@lem1244846 nat x). Qed.
Lemma lem1244848 (n : nat) : (n = n) = True.
Proof. exact (@lem1244847 n). Qed.
Lemma lem1244849 (n : nat) : ((term10 n) = n) = True.
Proof. exact (TRANS (@lem1244844 n) (@lem1244848 n)). Qed.
Lemma lem1244850 : term17 = term18.
Proof. exact (fun_ext (fun n : nat => @lem1244849 n)). Qed.
Lemma lem1244851 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1244852 : term19 = term20.
Proof. exact (MK_COMB (@lem1244851) (@lem1244850)). Qed.
Lemma lem1244854 {A : Type'} (t : Prop) : (term21 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1244855 (t : Prop) : (term22 t) = t.
Proof. exact (@lem1244854 nat t). Qed.
Lemma lem1244856 : term20 = True.
Proof. exact (@lem1244855 True). Qed.
Lemma lem1244857 : term19 = True.
Proof. exact (TRANS (@lem1244852) (@lem1244856)). Qed.
Lemma lem1244858 : True = term19.
Proof. exact (SYM (@lem1244857)). Qed.
Lemma lem1244859 : term19.
Proof. exact (EQ_MP (@lem1244858) (@lem0)). Qed.
