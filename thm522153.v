Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm522153_term_abbrevs.
Require Import SUB_EQ_0_spec.
Require Import thm512704_spec.
Require Import thm512705_spec.
Lemma lem522135 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512705 n) (@lem512704 n)). Qed.
Lemma lem522136 : (NUMERAL 0) = 0.
Proof. exact (@lem522135 0). Qed.
Lemma lem522137 (m : nat) (n : nat) : (term0 m n) = (term0 m n).
Proof. exact (eq_refl (term0 m n)). Qed.
Lemma lem522138 (m : nat) (n : nat) : ((Nat.sub m n) = (NUMERAL 0)) = ((Nat.sub m n) = 0).
Proof. exact (MK_COMB (@lem522137 m n) (@lem522136)). Qed.
Lemma lem522139 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem522140 (m : nat) (n : nat) : (term1 m n) = (term2 m n).
Proof. exact (MK_COMB (@lem522139) (@lem522138 m n)). Qed.
Lemma lem522141 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem522142 (m : nat) (n : nat) : (((Nat.sub m n) = (NUMERAL 0)) = (Peano.le m n)) = (((Nat.sub m n) = 0) = (Peano.le m n)).
Proof. exact (MK_COMB (@lem522140 m n) (@lem522141 m n)). Qed.
Lemma lem522143 (m : nat) : (term3 m) = (term4 m).
Proof. exact (fun_ext (fun n : nat => @lem522142 m n)). Qed.
Lemma lem522144 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem522145 (m : nat) : (term5 m) = (term6 m).
Proof. exact (MK_COMB (@lem522144) (@lem522143 m)). Qed.
Lemma lem522146 : term7 = term8.
Proof. exact (fun_ext (fun m : nat => @lem522145 m)). Qed.
Lemma lem522147 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem522148 : term9 = term10.
Proof. exact (MK_COMB (@lem522147) (@lem522146)). Qed.
Lemma lem522149 : term10.
Proof. exact (EQ_MP (@lem522148) (@lem136259)). Qed.
Lemma lem522150 (m : nat) : term11 m.
Proof. exact (@lem522149 m). Qed.
Lemma lem522151 (m : nat) : (term11 m) = (term6 m).
Proof. exact (eq_refl (term11 m)). Qed.
Lemma lem522152 (m : nat) : term6 m.
Proof. exact (EQ_MP (@lem522151 m) (@lem522150 m)). Qed.
Lemma lem522153 (m : nat) (n : nat) : term12 m n.
Proof. exact (@lem522152 m n). Qed.
