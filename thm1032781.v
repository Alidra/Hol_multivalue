Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1032781_term_abbrevs.
Require Import SUB_ELIM_THM_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Lemma lem1032764 (a : nat) (b : nat) (d : nat) : (term0 a b d) = (term1 a b d).
Proof. exact (@lem17045 (Peano.lt a b) (d = (NUMERAL 0))). Qed.
Lemma lem1032766 (a : nat) (b : nat) (d : nat) : (term2 a b d) = (term2 a b d).
Proof. exact (eq_refl (term2 a b d)). Qed.
Lemma lem1032767 (a : nat) (b : nat) (d : nat) : (term3 a b d) = (term4 a b d).
Proof. exact (MK_COMB (@lem1032766 a b d) (@lem1032764 a b d)). Qed.
Lemma lem1032768 (a : nat) (b : nat) (d : nat) : (term5 a b d) = (term3 a b d).
Proof. exact (@lem17160 (a = (Nat.add b d)) (term6 a b d)). Qed.
Lemma lem1032769 (a : nat) (b : nat) (d : nat) : (term5 a b d) = (term4 a b d).
Proof. exact (TRANS (@lem1032768 a b d) (@lem1032767 a b d)). Qed.
Lemma lem1032770 (P : nat -> Prop) (d : nat) : (P d) = (P d).
Proof. exact (eq_refl (P d)). Qed.
Lemma lem1032771 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1032772 (a : nat) (b : nat) (d : nat) : (term7 a b d) = (term8 a b d).
Proof. exact (MK_COMB (@lem1032771) (@lem1032769 a b d)). Qed.
Lemma lem1032773 (a : nat) (b : nat) (P : nat -> Prop) (d : nat) : (term9 a b P d) = (term10 a b P d).
Proof. exact (MK_COMB (@lem1032772 a b d) (@lem1032770 P d)). Qed.
Lemma lem1032774 (a : nat) (b : nat) (P : nat -> Prop) (d : nat) : (term11 a b P d) = (term9 a b P d).
Proof. exact (@lem17265 (term12 a b d) (P d)). Qed.
Lemma lem1032775 (a : nat) (b : nat) (P : nat -> Prop) (d : nat) : (term11 a b P d) = (term10 a b P d).
Proof. exact (TRANS (@lem1032774 a b P d) (@lem1032773 a b P d)). Qed.
Lemma lem1032776 (a : nat) (b : nat) (P : nat -> Prop) : (term13 a b P) = (term14 a b P).
Proof. exact (fun_ext (fun d : nat => @lem1032775 a b P d)). Qed.
Lemma lem1032777 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1032778 (a : nat) (b : nat) (P : nat -> Prop) : (term15 a b P) = (term16 a b P).
Proof. exact (MK_COMB (@lem1032777) (@lem1032776 a b P)). Qed.
Lemma lem1032779 (P : nat -> Prop) (a : nat) (b : nat) : (term17 P a b) = (term17 P a b).
Proof. exact (eq_refl (term17 P a b)). Qed.
Lemma lem1032780 (a : nat) (b : nat) (P : nat -> Prop) : ((term18 P a b) = (term15 a b P)) = ((term18 P a b) = (term16 a b P)).
Proof. exact (MK_COMB (@lem1032779 P a b) (@lem1032778 a b P)). Qed.
Lemma lem1032781 (a : nat) (b : nat) (P : nat -> Prop) : (term18 P a b) = (term16 a b P).
Proof. exact (EQ_MP (@lem1032780 a b P) (@lem254652 a b P)). Qed.
