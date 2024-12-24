Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LT_0_term_abbrevs.
Require Import LE_0_spec.
Require Import LT_SUC_LE_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Lemma lem91500 (n : nat) : term0 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem91501 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem91502 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem91501 n) (@lem91500 n)). Qed.
Lemma lem91503 (n : nat) : (term1 n) = ((term1 n) = True).
Proof. exact (@lem7 (term1 n)). Qed.
Lemma lem91505 (m : nat) : term2 m.
Proof. exact (@lem91305 m). Qed.
Lemma lem91506 (m : nat) : (term2 m) = (term3 m).
Proof. exact (eq_refl (term2 m)). Qed.
Lemma lem91507 (m : nat) : term3 m.
Proof. exact (EQ_MP (@lem91506 m) (@lem91505 m)). Qed.
Lemma lem91508 (m : nat) (n : nat) : term4 m n.
Proof. exact (@lem91507 m n). Qed.
Lemma lem91509 (m : nat) (n : nat) : (term4 m n) = ((term5 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term4 m n)). Qed.
Lemma lem91516 (m : nat) (n : nat) : (term5 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem91509 m n) (@lem91508 m n)). Qed.
Lemma lem91517 (n : nat) : (term6 n) = (term1 n).
Proof. exact (@lem91516 (NUMERAL 0) n). Qed.
Lemma lem91519 (n : nat) : (term1 n) = True.
Proof. exact (EQ_MP (@lem91503 n) (@lem91502 n)). Qed.
Lemma lem91520 (n : nat) : (term6 n) = True.
Proof. exact (TRANS (@lem91517 n) (@lem91519 n)). Qed.
Lemma lem91521 : term7 = term8.
Proof. exact (fun_ext (fun n : nat => @lem91520 n)). Qed.
Lemma lem91522 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem91523 : term9 = term10.
Proof. exact (MK_COMB (@lem91522) (@lem91521)). Qed.
Lemma lem91525 {A : Type'} (t : Prop) : (term11 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem91526 (t : Prop) : (term12 t) = t.
Proof. exact (@lem91525 nat t). Qed.
Lemma lem91527 : term10 = True.
Proof. exact (@lem91526 True). Qed.
Lemma lem91528 : term9 = True.
Proof. exact (TRANS (@lem91523) (@lem91527)). Qed.
Lemma lem91529 : True = term9.
Proof. exact (SYM (@lem91528)). Qed.
Lemma lem91530 : term9.
Proof. exact (EQ_MP (@lem91529) (@lem0)). Qed.
