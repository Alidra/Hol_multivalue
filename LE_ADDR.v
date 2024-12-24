Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LE_ADDR_term_abbrevs.
Require Import ADD_SYM_spec.
Require Import LE_ADD_spec.
Lemma lem100518 (m : nat) : term0 m.
Proof. exact (@lem77775 m). Qed.
Lemma lem100519 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem100520 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem100519 m) (@lem100518 m)). Qed.
Lemma lem100521 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem100520 m n). Qed.
Lemma lem100522 (n : nat) (m : nat) : (term2 m n) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem100533 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem100522 n m) (@lem100521 m n)). Qed.
Lemma lem100534 (n : nat) : (Peano.le n) = (Peano.le n).
Proof. exact (eq_refl (Peano.le n)). Qed.
Lemma lem100535 (n : nat) (m : nat) : (term3 m n) = (term4 n m).
Proof. exact (MK_COMB (@lem100534 n) (@lem100533 n m)). Qed.
Lemma lem100536 (m : nat) : (term5 m) = (term6 m).
Proof. exact (fun_ext (fun n : nat => @lem100535 n m)). Qed.
Lemma lem100537 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem100538 (m : nat) : (term7 m) = (term8 m).
Proof. exact (MK_COMB (@lem100537) (@lem100536 m)). Qed.
Lemma lem100539 : term9 = term10.
Proof. exact (fun_ext (fun m : nat => @lem100538 m)). Qed.
Lemma lem100540 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem100541 : term11 = term12.
Proof. exact (MK_COMB (@lem100540) (@lem100539)). Qed.
Lemma lem100542 : term12 = term11.
Proof. exact (SYM (@lem100541)). Qed.
Lemma lem100543 (m : nat) : term13 m.
Proof. exact (@lem100517 m). Qed.
Lemma lem100544 (m : nat) : (term13 m) = (term14 m).
Proof. exact (eq_refl (term13 m)). Qed.
Lemma lem100545 (m : nat) : term14 m.
Proof. exact (EQ_MP (@lem100544 m) (@lem100543 m)). Qed.
Lemma lem100546 (m : nat) (n : nat) : term15 m n.
Proof. exact (@lem100545 m n). Qed.
Lemma lem100547 (m : nat) (n : nat) : (term15 m n) = (term4 m n).
Proof. exact (eq_refl (term15 m n)). Qed.
Lemma lem100550 (m : nat) (n : nat) : term4 m n.
Proof. exact (EQ_MP (@lem100547 m n) (@lem100546 m n)). Qed.
Lemma lem100551 (n : nat) (m : nat) : term4 n m.
Proof. exact (@lem100550 n m). Qed.
Lemma lem100556 (m : nat) : term8 m.
Proof. exact (fun n : nat => @lem100551 n m). Qed.
Lemma lem100561 : term12.
Proof. exact (fun m : nat => @lem100556 m). Qed.
Lemma lem100562 : term11.
Proof. exact (EQ_MP (@lem100542) (@lem100561)). Qed.
