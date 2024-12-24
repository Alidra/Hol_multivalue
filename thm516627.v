Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm516627_term_abbrevs.
Require Import NOT_SUC_spec.
Require Import thm512704_spec.
Require Import thm512705_spec.
Lemma lem516618 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512705 n) (@lem512704 n)). Qed.
Lemma lem516619 : (NUMERAL 0) = 0.
Proof. exact (@lem516618 0). Qed.
Lemma lem516620 (n : nat) : (term0 n) = (term0 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem516621 (n : nat) : ((S n) = (NUMERAL 0)) = ((S n) = 0).
Proof. exact (MK_COMB (@lem516620 n) (@lem516619)). Qed.
Lemma lem516622 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem516623 (n : nat) : (term1 n) = (term2 n).
Proof. exact (MK_COMB (@lem516622) (@lem516621 n)). Qed.
Lemma lem516624 : term3 = term4.
Proof. exact (fun_ext (fun n : nat => @lem516623 n)). Qed.
Lemma lem516625 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem516626 : term5 = term6.
Proof. exact (MK_COMB (@lem516625) (@lem516624)). Qed.
Lemma lem516627 : term6.
Proof. exact (EQ_MP (@lem516626) (@lem75570)). Qed.
