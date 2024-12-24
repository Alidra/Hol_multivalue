Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import BIT1_term_abbrevs.
Require Import BIT0_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm76570_spec.
Lemma lem80085 (n : nat) : term0 n.
Proof. exact (@lem80084 n). Qed.
Lemma lem80086 (n : nat) : (term0 n) = ((BIT0 n) = (Nat.add n n)).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem80088 (n : nat) : term1 n.
Proof. exact (@lem76570 n). Qed.
Lemma lem80089 (n : nat) : (term1 n) = ((BIT1 n) = (term2 n)).
Proof. exact (eq_refl (term1 n)). Qed.
Lemma lem80098 (n : nat) : (BIT1 n) = (term2 n).
Proof. exact (EQ_MP (@lem80089 n) (@lem80088 n)). Qed.
Lemma lem80100 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem80086 n) (@lem80085 n)). Qed.
Lemma lem80101 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem80102 (n : nat) : (term2 n) = (term3 n).
Proof. exact (MK_COMB (@lem80101) (@lem80100 n)). Qed.
Lemma lem80103 (n : nat) : (BIT1 n) = (term3 n).
Proof. exact (TRANS (@lem80098 n) (@lem80102 n)). Qed.
Lemma lem80104 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem80105 (n : nat) : (term4 n) = (term5 n).
Proof. exact (MK_COMB (@lem80104) (@lem80103 n)). Qed.
Lemma lem80106 (n : nat) : (term3 n) = (term3 n).
Proof. exact (eq_refl (term3 n)). Qed.
Lemma lem80107 (n : nat) : ((BIT1 n) = (term3 n)) = ((term3 n) = (term3 n)).
Proof. exact (MK_COMB (@lem80105 n) (@lem80106 n)). Qed.
Lemma lem80109 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem80110 (x : nat) : (x = x) = True.
Proof. exact (@lem80109 nat x). Qed.
Lemma lem80111 (n : nat) : ((term3 n) = (term3 n)) = True.
Proof. exact (@lem80110 (term3 n)). Qed.
Lemma lem80112 (n : nat) : ((BIT1 n) = (term3 n)) = True.
Proof. exact (TRANS (@lem80107 n) (@lem80111 n)). Qed.
Lemma lem80113 : term6 = term7.
Proof. exact (fun_ext (fun n : nat => @lem80112 n)). Qed.
Lemma lem80114 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem80115 : term8 = term9.
Proof. exact (MK_COMB (@lem80114) (@lem80113)). Qed.
Lemma lem80117 {A : Type'} (t : Prop) : (term10 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem80118 (t : Prop) : (term11 t) = t.
Proof. exact (@lem80117 nat t). Qed.
Lemma lem80119 : term9 = True.
Proof. exact (@lem80118 True). Qed.
Lemma lem80120 : term8 = True.
Proof. exact (TRANS (@lem80115) (@lem80119)). Qed.
Lemma lem80121 : True = term8.
Proof. exact (SYM (@lem80120)). Qed.
Lemma lem80122 : term8.
Proof. exact (EQ_MP (@lem80121) (@lem0)). Qed.
