Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUC_SUB1_term_abbrevs.
Require Import SUB_0_spec.
Require Import SUB_SUC_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm80360_spec.
Lemma lem137109 (m : nat) : term0 m.
Proof. exact (@lem135231 m). Qed.
Lemma lem137110 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem137111 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem137110 m) (@lem137109 m)). Qed.
Lemma lem137114 (m : nat) : term2 m.
Proof. exact (@lem135645 m). Qed.
Lemma lem137115 (m : nat) : (term2 m) = (term3 m).
Proof. exact (eq_refl (term2 m)). Qed.
Lemma lem137116 (m : nat) : term3 m.
Proof. exact (EQ_MP (@lem137115 m) (@lem137114 m)). Qed.
Lemma lem137117 (m : nat) (n : nat) : term4 m n.
Proof. exact (@lem137116 m n). Qed.
Lemma lem137118 (m : nat) (n : nat) : (term4 m n) = ((term5 m n) = (Nat.sub m n)).
Proof. exact (eq_refl (term4 m n)). Qed.
Lemma lem137127 : term6 = term7.
Proof. exact (EQ_MP (@lem80360) (@lem0)). Qed.
Lemma lem137128 (n : nat) : (term8 n) = (term8 n).
Proof. exact (eq_refl (term8 n)). Qed.
Lemma lem137129 (n : nat) : (term9 n) = (term10 n).
Proof. exact (MK_COMB (@lem137128 n) (@lem137127)). Qed.
Lemma lem137131 (m : nat) (n : nat) : (term5 m n) = (Nat.sub m n).
Proof. exact (EQ_MP (@lem137118 m n) (@lem137117 m n)). Qed.
Lemma lem137132 (n : nat) : (term10 n) = (term11 n).
Proof. exact (@lem137131 n (NUMERAL 0)). Qed.
Lemma lem137134 (m : nat) : (term11 m) = m.
Proof. exact (proj2 (@lem137111 m)). Qed.
Lemma lem137135 (n : nat) : (term11 n) = n.
Proof. exact (@lem137134 n). Qed.
Lemma lem137136 (n : nat) : (term10 n) = n.
Proof. exact (TRANS (@lem137132 n) (@lem137135 n)). Qed.
Lemma lem137137 (n : nat) : (term9 n) = n.
Proof. exact (TRANS (@lem137129 n) (@lem137136 n)). Qed.
Lemma lem137138 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem137139 (n : nat) : (term12 n) = (@eq nat n).
Proof. exact (MK_COMB (@lem137138) (@lem137137 n)). Qed.
Lemma lem137140 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem137141 (n : nat) : ((term9 n) = n) = (n = n).
Proof. exact (MK_COMB (@lem137139 n) (@lem137140 n)). Qed.
Lemma lem137143 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem137144 (x : nat) : (x = x) = True.
Proof. exact (@lem137143 nat x). Qed.
Lemma lem137145 (n : nat) : (n = n) = True.
Proof. exact (@lem137144 n). Qed.
Lemma lem137146 (n : nat) : ((term9 n) = n) = True.
Proof. exact (TRANS (@lem137141 n) (@lem137145 n)). Qed.
Lemma lem137147 : term13 = term14.
Proof. exact (fun_ext (fun n : nat => @lem137146 n)). Qed.
Lemma lem137148 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem137149 : term15 = term16.
Proof. exact (MK_COMB (@lem137148) (@lem137147)). Qed.
Lemma lem137151 {A : Type'} (t : Prop) : (term17 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem137152 (t : Prop) : (term18 t) = t.
Proof. exact (@lem137151 nat t). Qed.
Lemma lem137153 : term16 = True.
Proof. exact (@lem137152 True). Qed.
Lemma lem137154 : term15 = True.
Proof. exact (TRANS (@lem137149) (@lem137153)). Qed.
Lemma lem137155 : True = term15.
Proof. exact (SYM (@lem137154)). Qed.
Lemma lem137156 : term15.
Proof. exact (EQ_MP (@lem137155) (@lem0)). Qed.
