Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LT_REFL_term_abbrevs.
Require Import LT_SUC_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm82_spec.
Require Import thm89994_spec.
Lemma lem91611 : term0.
Proof. exact (proj1 (@lem89994)). Qed.
Lemma lem91612 (m : nat) : term1 m.
Proof. exact (@lem91611 m). Qed.
Lemma lem91613 (m : nat) : (term1 m) = ((term2 m) = False).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem91616 (P : nat -> Prop) : term3 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem91617 : term4.
Proof. exact (@lem91616 term5). Qed.
Lemma lem91618 : term6 = term7.
Proof. exact (eq_refl term6). Qed.
Lemma lem91619 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem91620 : term8 = term9.
Proof. exact (MK_COMB (@lem91619) (@lem91618)). Qed.
Lemma lem91621 (n : nat) : (term10 n) = (term11 n).
Proof. exact (eq_refl (term10 n)). Qed.
Lemma lem91622 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem91623 (n : nat) : (term12 n) = (term13 n).
Proof. exact (MK_COMB (@lem91622) (@lem91621 n)). Qed.
Lemma lem91624 (n : nat) : (term14 n) = (term15 n).
Proof. exact (eq_refl (term14 n)). Qed.
Lemma lem91625 (n : nat) : (term16 n) = (term17 n).
Proof. exact (MK_COMB (@lem91623 n) (@lem91624 n)). Qed.
Lemma lem91626 : term18 = term19.
Proof. exact (fun_ext (fun n : nat => @lem91625 n)). Qed.
Lemma lem91627 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem91628 : term20 = term21.
Proof. exact (MK_COMB (@lem91627) (@lem91626)). Qed.
Lemma lem91629 : term22 = term23.
Proof. exact (MK_COMB (@lem91620) (@lem91628)). Qed.
Lemma lem91630 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem91631 : term24 = term25.
Proof. exact (MK_COMB (@lem91630) (@lem91629)). Qed.
Lemma lem91632 (n : nat) : (term10 n) = (term11 n).
Proof. exact (eq_refl (term10 n)). Qed.
Lemma lem91633 : term26 = term5.
Proof. exact (fun_ext (fun n : nat => @lem91632 n)). Qed.
Lemma lem91634 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem91635 : term27 = term28.
Proof. exact (MK_COMB (@lem91634) (@lem91633)). Qed.
Lemma lem91636 : term4 = term29.
Proof. exact (MK_COMB (@lem91631) (@lem91635)). Qed.
Lemma lem91637 : term29.
Proof. exact (EQ_MP (@lem91636) (@lem91617)). Qed.
Lemma lem91638 (n : nat) (h1 : term11 n) : term11 n.
Proof. exact (h1). Qed.
Lemma lem91647 (m : nat) : term30 m.
Proof. exact (@lem91415 m). Qed.
Lemma lem91648 (m : nat) : (term30 m) = (term31 m).
Proof. exact (eq_refl (term30 m)). Qed.
Lemma lem91649 (m : nat) : term31 m.
Proof. exact (EQ_MP (@lem91648 m) (@lem91647 m)). Qed.
Lemma lem91650 (m : nat) (n : nat) : term32 m n.
Proof. exact (@lem91649 m n). Qed.
Lemma lem91651 (m : nat) (n : nat) : (term32 m n) = ((term33 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term32 m n)). Qed.
Lemma lem91653 (n : nat) : term34 n.
Proof. exact (@lem82 (Peano.lt n n)). Qed.
Lemma lem91656 (m : nat) (n : nat) : (term33 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem91651 m n) (@lem91650 m n)). Qed.
Lemma lem91657 (n : nat) : (term35 n) = (Peano.lt n n).
Proof. exact (@lem91656 n n). Qed.
Lemma lem91659 (n : nat) (h1 : term11 n) : (Peano.lt n n) = False.
Proof. exact (@lem91653 n (@lem91638 n h1)). Qed.
Lemma lem91660 (n : nat) (h1 : term11 n) : (term35 n) = False.
Proof. exact (TRANS (@lem91657 n) (@lem91659 n h1)). Qed.
Lemma lem91661 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem91662 (n : nat) (h1 : term11 n) : (term15 n) = (~ False).
Proof. exact (MK_COMB (@lem91661) (@lem91660 n h1)). Qed.
Lemma lem91664 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem91665 (n : nat) (h1 : term11 n) : (term15 n) = True.
Proof. exact (TRANS (@lem91662 n h1) (@lem91664)). Qed.
Lemma lem91666 (n : nat) (h1 : term11 n) : True = (term15 n).
Proof. exact (SYM (@lem91665 n h1)). Qed.
Lemma lem91667 (n : nat) (h1 : term11 n) : term15 n.
Proof. exact (EQ_MP (@lem91666 n h1) (@lem0)). Qed.
Lemma lem91669 (m : nat) : (term2 m) = False.
Proof. exact (EQ_MP (@lem91613 m) (@lem91612 m)). Qed.
Lemma lem91670 : term36 = False.
Proof. exact (@lem91669 (NUMERAL 0)). Qed.
Lemma lem91671 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem91672 : term7 = (~ False).
Proof. exact (MK_COMB (@lem91671) (@lem91670)). Qed.
Lemma lem91674 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem91675 : term7 = True.
Proof. exact (TRANS (@lem91672) (@lem91674)). Qed.
Lemma lem91676 : True = term7.
Proof. exact (SYM (@lem91675)). Qed.
Lemma lem91678 : term7.
Proof. exact (EQ_MP (@lem91676) (@lem0)). Qed.
Lemma lem91679 (n : nat) : term17 n.
Proof. exact (fun h0 : term11 n => @lem91667 n h0). Qed.
Lemma lem91684 : term21.
Proof. exact (fun n : nat => @lem91679 n). Qed.
Lemma lem91685 : term23.
Proof. exact (conj (@lem91678) (@lem91684)). Qed.
Lemma lem91686 : term28.
Proof. exact (@lem91637 (@lem91685)). Qed.
