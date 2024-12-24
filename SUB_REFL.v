Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUB_REFL_term_abbrevs.
Require Import SUB_0_spec.
Require Import SUB_SUC_spec.
Require Import thm0_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Lemma lem135647 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem135648 : term1.
Proof. exact (@lem135647 term2). Qed.
Lemma lem135649 : term3 = (term4 = (NUMERAL 0)).
Proof. exact (eq_refl term3). Qed.
Lemma lem135650 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem135651 : term5 = term6.
Proof. exact (MK_COMB (@lem135650) (@lem135649)). Qed.
Lemma lem135652 (n : nat) : (term7 n) = ((Nat.sub n n) = (NUMERAL 0)).
Proof. exact (eq_refl (term7 n)). Qed.
Lemma lem135653 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem135654 (n : nat) : (term8 n) = (term9 n).
Proof. exact (MK_COMB (@lem135653) (@lem135652 n)). Qed.
Lemma lem135655 (n : nat) : (term10 n) = ((term11 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term10 n)). Qed.
Lemma lem135656 (n : nat) : (term12 n) = (term13 n).
Proof. exact (MK_COMB (@lem135654 n) (@lem135655 n)). Qed.
Lemma lem135657 : term14 = term15.
Proof. exact (fun_ext (fun n : nat => @lem135656 n)). Qed.
Lemma lem135658 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem135659 : term16 = term17.
Proof. exact (MK_COMB (@lem135658) (@lem135657)). Qed.
Lemma lem135660 : term18 = term19.
Proof. exact (MK_COMB (@lem135651) (@lem135659)). Qed.
Lemma lem135661 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem135662 : term20 = term21.
Proof. exact (MK_COMB (@lem135661) (@lem135660)). Qed.
Lemma lem135663 (n : nat) : (term7 n) = ((Nat.sub n n) = (NUMERAL 0)).
Proof. exact (eq_refl (term7 n)). Qed.
Lemma lem135664 : term22 = term2.
Proof. exact (fun_ext (fun n : nat => @lem135663 n)). Qed.
Lemma lem135665 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem135666 : term23 = term24.
Proof. exact (MK_COMB (@lem135665) (@lem135664)). Qed.
Lemma lem135667 : term1 = term25.
Proof. exact (MK_COMB (@lem135662) (@lem135666)). Qed.
Lemma lem135668 : term25.
Proof. exact (EQ_MP (@lem135667) (@lem135648)). Qed.
Lemma lem135670 (m : nat) : term26 m.
Proof. exact (@lem135231 m). Qed.
Lemma lem135671 (m : nat) : (term26 m) = (term27 m).
Proof. exact (eq_refl (term26 m)). Qed.
Lemma lem135672 (m : nat) : term27 m.
Proof. exact (EQ_MP (@lem135671 m) (@lem135670 m)). Qed.
Lemma lem135684 (m : nat) : (term28 m) = (NUMERAL 0).
Proof. exact (proj1 (@lem135672 m)). Qed.
Lemma lem135685 : term4 = (NUMERAL 0).
Proof. exact (@lem135684 (NUMERAL 0)). Qed.
Lemma lem135686 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem135687 : term29 = term30.
Proof. exact (MK_COMB (@lem135686) (@lem135685)). Qed.
Lemma lem135688 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem135689 : (term4 = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem135687) (@lem135688)). Qed.
Lemma lem135691 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem135692 (x : nat) : (x = x) = True.
Proof. exact (@lem135691 nat x). Qed.
Lemma lem135693 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem135692 (NUMERAL 0)). Qed.
Lemma lem135694 : (term4 = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem135689) (@lem135693)). Qed.
Lemma lem135695 : True = (term4 = (NUMERAL 0)).
Proof. exact (SYM (@lem135694)). Qed.
Lemma lem135696 : term4 = (NUMERAL 0).
Proof. exact (EQ_MP (@lem135695) (@lem0)). Qed.
Lemma lem135702 (m : nat) : term31 m.
Proof. exact (@lem135645 m). Qed.
Lemma lem135703 (m : nat) : (term31 m) = (term32 m).
Proof. exact (eq_refl (term31 m)). Qed.
Lemma lem135704 (m : nat) : term32 m.
Proof. exact (EQ_MP (@lem135703 m) (@lem135702 m)). Qed.
Lemma lem135705 (m : nat) (n : nat) : term33 m n.
Proof. exact (@lem135704 m n). Qed.
Lemma lem135706 (m : nat) (n : nat) : (term33 m n) = ((term34 m n) = (Nat.sub m n)).
Proof. exact (eq_refl (term33 m n)). Qed.
Lemma lem135711 (m : nat) (n : nat) : (term34 m n) = (Nat.sub m n).
Proof. exact (EQ_MP (@lem135706 m n) (@lem135705 m n)). Qed.
Lemma lem135712 (n : nat) : (term11 n) = (Nat.sub n n).
Proof. exact (@lem135711 n n). Qed.
Lemma lem135714 (n : nat) (h1 : (Nat.sub n n) = (NUMERAL 0)) : (Nat.sub n n) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem135715 (n : nat) (h1 : (Nat.sub n n) = (NUMERAL 0)) : (term11 n) = (NUMERAL 0).
Proof. exact (TRANS (@lem135712 n) (@lem135714 n h1)). Qed.
Lemma lem135716 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem135717 (n : nat) (h1 : (Nat.sub n n) = (NUMERAL 0)) : (term35 n) = term30.
Proof. exact (MK_COMB (@lem135716) (@lem135715 n h1)). Qed.
Lemma lem135718 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem135719 (n : nat) (h1 : (Nat.sub n n) = (NUMERAL 0)) : ((term11 n) = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem135717 n h1) (@lem135718)). Qed.
Lemma lem135721 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem135722 (x : nat) : (x = x) = True.
Proof. exact (@lem135721 nat x). Qed.
Lemma lem135723 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem135722 (NUMERAL 0)). Qed.
Lemma lem135724 (n : nat) (h1 : (Nat.sub n n) = (NUMERAL 0)) : ((term11 n) = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem135719 n h1) (@lem135723)). Qed.
Lemma lem135725 (n : nat) (h1 : (Nat.sub n n) = (NUMERAL 0)) : True = ((term11 n) = (NUMERAL 0)).
Proof. exact (SYM (@lem135724 n h1)). Qed.
Lemma lem135726 (n : nat) (h1 : (Nat.sub n n) = (NUMERAL 0)) : (term11 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem135725 n h1) (@lem0)). Qed.
Lemma lem135727 (n : nat) : term13 n.
Proof. exact (fun h0 : (Nat.sub n n) = (NUMERAL 0) => @lem135726 n h0). Qed.
Lemma lem135732 : term17.
Proof. exact (fun n : nat => @lem135727 n). Qed.
Lemma lem135733 : term19.
Proof. exact (conj (@lem135696) (@lem135732)). Qed.
Lemma lem135734 : term24.
Proof. exact (@lem135668 (@lem135733)). Qed.
