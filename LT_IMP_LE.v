Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LT_IMP_LE_term_abbrevs.
Require Import LT_LE_spec.
Lemma lem98378 (m : nat) : term0 m.
Proof. exact (@lem97539 m). Qed.
Lemma lem98379 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem98380 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem98379 m) (@lem98378 m)). Qed.
Lemma lem98381 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem98380 m n). Qed.
Lemma lem98382 (m : nat) (n : nat) : (term2 m n) = ((Peano.lt m n) = (term3 m n)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem98395 (m : nat) (n : nat) : (Peano.lt m n) = (term3 m n).
Proof. exact (EQ_MP (@lem98382 m n) (@lem98381 m n)). Qed.
Lemma lem98400 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem98401 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (MK_COMB (@lem98400) (@lem98395 m n)). Qed.
Lemma lem98402 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem98403 (m : nat) (n : nat) : (term6 m n) = (term7 m n).
Proof. exact (MK_COMB (@lem98401 m n) (@lem98402 m n)). Qed.
Lemma lem98406 (m : nat) : (term8 m) = (term9 m).
Proof. exact (fun_ext (fun n : nat => @lem98403 m n)). Qed.
Lemma lem98407 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem98408 (m : nat) : (term10 m) = (term11 m).
Proof. exact (MK_COMB (@lem98407) (@lem98406 m)). Qed.
Lemma lem98413 : term12 = term13.
Proof. exact (fun_ext (fun m : nat => @lem98408 m)). Qed.
Lemma lem98414 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem98415 : term14 = term15.
Proof. exact (MK_COMB (@lem98414) (@lem98413)). Qed.
Lemma lem98420 : term15 = term14.
Proof. exact (SYM (@lem98415)). Qed.
Lemma lem98421 (m : nat) (n : nat) (h1 : term3 m n) : term3 m n.
Proof. exact (h1). Qed.
Lemma lem98423 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem98425 (m : nat) (n : nat) (h1 : term3 m n) : Peano.le m n.
Proof. exact (proj1 (@lem98421 m n h1)). Qed.
Lemma lem98426 (m : nat) (n : nat) (h1 : term3 m n) : (Peano.le m n) = (Peano.le m n).
Proof. exact (prop_ext (fun h2 : Peano.le m n => @lem98423 m n h2) (fun h2 : Peano.le m n => @lem98425 m n h1)). Qed.
Lemma lem98427 (m : nat) (n : nat) (h1 : term3 m n) : Peano.le m n.
Proof. exact (EQ_MP (@lem98426 m n h1) (@lem98425 m n h1)). Qed.
Lemma lem98428 (m : nat) (n : nat) : term7 m n.
Proof. exact (fun h0 : term3 m n => @lem98427 m n h0). Qed.
Lemma lem98433 (m : nat) : term11 m.
Proof. exact (fun n : nat => @lem98428 m n). Qed.
Lemma lem98438 : term15.
Proof. exact (fun m : nat => @lem98433 m). Qed.
Lemma lem98439 : term14.
Proof. exact (EQ_MP (@lem98420) (@lem98438)). Qed.
