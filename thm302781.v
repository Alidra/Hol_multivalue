Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm302781_term_abbrevs.
Require Import thm0_spec.
Require Import thm1833_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm302535_spec.
Require Import thm302536_spec.
Require Import thm302702_spec.
Require Import thm80550_spec.
Lemma lem302751 : term0 = term1.
Proof. exact (EQ_MP (@lem80550) (@lem0)). Qed.
Lemma lem302752 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem302753 : term2 = term3.
Proof. exact (MK_COMB (@lem302752) (@lem302751)). Qed.
Lemma lem302754 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem302755 : (term0 = (NUMERAL 0)) = (term1 = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem302753) (@lem302754)). Qed.
Lemma lem302757 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem302536 n (@lem302535 n)). Qed.
Lemma lem302758 : (term1 = (NUMERAL 0)) = False.
Proof. exact (@lem302757 term4). Qed.
Lemma lem302759 : (term0 = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem302755) (@lem302758)). Qed.
Lemma lem302760 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem302761 : term5 = (or False).
Proof. exact (MK_COMB (@lem302760) (@lem302759)). Qed.
Lemma lem302764 (m : nat) (n : nat) : (m = n) = (m = n).
Proof. exact (eq_refl (m = n)). Qed.
Lemma lem302765 (m : nat) (n : nat) : (term6 m n) = (term7 m n).
Proof. exact (MK_COMB (@lem302761) (@lem302764 m n)). Qed.
Lemma lem302767 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem302768 (m : nat) (n : nat) : (term7 m n) = (m = n).
Proof. exact (@lem302767 (m = n)). Qed.
Lemma lem302771 (m : nat) (n : nat) : (term6 m n) = (m = n).
Proof. exact (TRANS (@lem302765 m n) (@lem302768 m n)). Qed.
Lemma lem302772 (m : nat) (n : nat) : (term8 m n) = (term8 m n).
Proof. exact (eq_refl (term8 m n)). Qed.
Lemma lem302773 (m : nat) (n : nat) : ((m = n) = (term6 m n)) = ((m = n) = (m = n)).
Proof. exact (MK_COMB (@lem302772 m n) (@lem302771 m n)). Qed.
Lemma lem302775 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem302776 (x : Prop) : (x = x) = True.
Proof. exact (@lem302775 Prop x). Qed.
Lemma lem302777 (m : nat) (n : nat) : ((m = n) = (m = n)) = True.
Proof. exact (@lem302776 (m = n)). Qed.
Lemma lem302778 (m : nat) (n : nat) : ((m = n) = (term6 m n)) = True.
Proof. exact (TRANS (@lem302773 m n) (@lem302777 m n)). Qed.
Lemma lem302779 (m : nat) (n : nat) : True = ((m = n) = (term6 m n)).
Proof. exact (SYM (@lem302778 m n)). Qed.
Lemma lem302780 (m : nat) (n : nat) : (m = n) = (term6 m n).
Proof. exact (EQ_MP (@lem302779 m n) (@lem0)). Qed.
Lemma lem302781 (m : nat) (n : nat) : (m = n) = ((term9 m) = (term9 n)).
Proof. exact (EQ_MP (@lem302702 m n) (@lem302780 m n)). Qed.
