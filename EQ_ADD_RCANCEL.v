Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EQ_ADD_RCANCEL_term_abbrevs.
Require Import ADD_SYM_spec.
Require Import EQ_ADD_LCANCEL_spec.
Lemma lem79640 (m : nat) : term0 m.
Proof. exact (@lem77775 m). Qed.
Lemma lem79641 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem79642 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem79641 m) (@lem79640 m)). Qed.
Lemma lem79643 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem79642 m n). Qed.
Lemma lem79644 (n : nat) (m : nat) : (term2 m n) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem79663 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem79644 n m) (@lem79643 m n)). Qed.
Lemma lem79664 (p : nat) (m : nat) : (Nat.add m p) = (Nat.add p m).
Proof. exact (@lem79663 p m). Qed.
Lemma lem79665 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem79666 (p : nat) (m : nat) : (term3 m p) = (term3 p m).
Proof. exact (MK_COMB (@lem79665) (@lem79664 p m)). Qed.
Lemma lem79668 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem79644 n m) (@lem79643 m n)). Qed.
Lemma lem79669 (p : nat) (n : nat) : (Nat.add n p) = (Nat.add p n).
Proof. exact (@lem79668 p n). Qed.
Lemma lem79670 (m : nat) (p : nat) (n : nat) : ((Nat.add m p) = (Nat.add n p)) = ((Nat.add p m) = (Nat.add p n)).
Proof. exact (MK_COMB (@lem79666 p m) (@lem79669 p n)). Qed.
Lemma lem79671 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem79672 (m : nat) (p : nat) (n : nat) : (term4 m n p) = (term5 m p n).
Proof. exact (MK_COMB (@lem79671) (@lem79670 m p n)). Qed.
Lemma lem79675 (m : nat) (n : nat) : (m = n) = (m = n).
Proof. exact (eq_refl (m = n)). Qed.
Lemma lem79676 (p : nat) (m : nat) (n : nat) : (((Nat.add m p) = (Nat.add n p)) = (m = n)) = (((Nat.add p m) = (Nat.add p n)) = (m = n)).
Proof. exact (MK_COMB (@lem79672 m p n) (@lem79675 m n)). Qed.
Lemma lem79677 (m : nat) (n : nat) : (term6 m n) = (term7 m n).
Proof. exact (fun_ext (fun p : nat => @lem79676 p m n)). Qed.
Lemma lem79678 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem79679 (m : nat) (n : nat) : (term8 m n) = (term9 m n).
Proof. exact (MK_COMB (@lem79678) (@lem79677 m n)). Qed.
Lemma lem79680 (m : nat) : (term10 m) = (term11 m).
Proof. exact (fun_ext (fun n : nat => @lem79679 m n)). Qed.
Lemma lem79681 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem79682 (m : nat) : (term12 m) = (term13 m).
Proof. exact (MK_COMB (@lem79681) (@lem79680 m)). Qed.
Lemma lem79683 : term14 = term15.
Proof. exact (fun_ext (fun m : nat => @lem79682 m)). Qed.
Lemma lem79684 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem79685 : term16 = term17.
Proof. exact (MK_COMB (@lem79684) (@lem79683)). Qed.
Lemma lem79686 : term17 = term16.
Proof. exact (SYM (@lem79685)). Qed.
Lemma lem79687 (m : nat) : term18 m.
Proof. exact (@lem79639 m). Qed.
Lemma lem79688 (m : nat) : (term18 m) = (term19 m).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem79689 (m : nat) : term19 m.
Proof. exact (EQ_MP (@lem79688 m) (@lem79687 m)). Qed.
Lemma lem79690 (m : nat) (n : nat) : term20 m n.
Proof. exact (@lem79689 m n). Qed.
Lemma lem79691 (m : nat) (n : nat) : (term20 m n) = (term21 m n).
Proof. exact (eq_refl (term20 m n)). Qed.
Lemma lem79692 (m : nat) (n : nat) : term21 m n.
Proof. exact (EQ_MP (@lem79691 m n) (@lem79690 m n)). Qed.
Lemma lem79693 (m : nat) (n : nat) (p : nat) : term22 m n p.
Proof. exact (@lem79692 m n p). Qed.
Lemma lem79694 (m : nat) (n : nat) (p : nat) : (term22 m n p) = (((Nat.add m n) = (Nat.add m p)) = (n = p)).
Proof. exact (eq_refl (term22 m n p)). Qed.
Lemma lem79697 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem79694 m n p) (@lem79693 m n p)). Qed.
Lemma lem79698 (p : nat) (m : nat) (n : nat) : ((Nat.add p m) = (Nat.add p n)) = (m = n).
Proof. exact (@lem79697 p m n). Qed.
Lemma lem79703 (m : nat) (n : nat) : term9 m n.
Proof. exact (fun p : nat => @lem79698 p m n). Qed.
Lemma lem79708 (m : nat) : term13 m.
Proof. exact (fun n : nat => @lem79703 m n). Qed.
Lemma lem79713 : term17.
Proof. exact (fun m : nat => @lem79708 m). Qed.
Lemma lem79714 : term16.
Proof. exact (EQ_MP (@lem79686) (@lem79713)). Qed.
