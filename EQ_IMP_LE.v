Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EQ_IMP_LE_term_abbrevs.
Require Import LE_REFL_spec.
Require Import thm0_spec.
Require Import thm7_spec.
Lemma lem98440 (m : nat) (n : nat) (h1 : m = n) : m = n.
Proof. exact (h1). Qed.
Lemma lem98441 (n : nat) : term0 n.
Proof. exact (@lem91603 n). Qed.
Lemma lem98442 (n : nat) : (term0 n) = (Peano.le n n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem98443 (n : nat) : Peano.le n n.
Proof. exact (EQ_MP (@lem98442 n) (@lem98441 n)). Qed.
Lemma lem98444 (n : nat) : (Peano.le n n) = ((Peano.le n n) = True).
Proof. exact (@lem7 (Peano.le n n)). Qed.
Lemma lem98449 (m : nat) (n : nat) (h1 : m = n) : m = n.
Proof. exact (h1). Qed.
Lemma lem98450 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem98451 (m : nat) (n : nat) (h1 : m = n) : (Peano.le m) = (Peano.le n).
Proof. exact (MK_COMB (@lem98450) (@lem98449 m n h1)). Qed.
Lemma lem98452 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem98453 (m : nat) (n : nat) (h1 : m = n) : (Peano.le m n) = (Peano.le n n).
Proof. exact (MK_COMB (@lem98451 m n h1) (@lem98452 n)). Qed.
Lemma lem98455 (n : nat) : (Peano.le n n) = True.
Proof. exact (EQ_MP (@lem98444 n) (@lem98443 n)). Qed.
Lemma lem98456 (m : nat) (n : nat) (h1 : m = n) : (Peano.le m n) = True.
Proof. exact (TRANS (@lem98453 m n h1) (@lem98455 n)). Qed.
Lemma lem98457 (m : nat) (n : nat) (h1 : m = n) : True = (Peano.le m n).
Proof. exact (SYM (@lem98456 m n h1)). Qed.
Lemma lem98458 (m : nat) (n : nat) (h1 : m = n) : Peano.le m n.
Proof. exact (EQ_MP (@lem98457 m n h1) (@lem0)). Qed.
Lemma lem98459 (m : nat) (n : nat) (h1 : m = n) : (m = n) = (Peano.le m n).
Proof. exact (prop_ext (fun h2 : m = n => @lem98458 m n h1) (fun h2 : Peano.le m n => @lem98440 m n h1)). Qed.
Lemma lem98460 (m : nat) (n : nat) (h1 : m = n) : Peano.le m n.
Proof. exact (EQ_MP (@lem98459 m n h1) (@lem98440 m n h1)). Qed.
Lemma lem98461 (m : nat) (n : nat) : term1 m n.
Proof. exact (fun h0 : m = n => @lem98460 m n h0). Qed.
Lemma lem98466 (m : nat) : term2 m.
Proof. exact (fun n : nat => @lem98461 m n). Qed.
Lemma lem98471 : term3.
Proof. exact (fun m : nat => @lem98466 m). Qed.
