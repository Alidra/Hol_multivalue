Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIST_REFL_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import SUB_REFL_spec.
Require Import dist_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1244731 : term0.
Proof. exact (proj1 (@lem77629)). Qed.
Lemma lem1244732 (n : nat) : term1 n.
Proof. exact (@lem1244731 n). Qed.
Lemma lem1244733 (n : nat) : (term1 n) = ((term2 n) = n).
Proof. exact (eq_refl (term1 n)). Qed.
Lemma lem1244735 (n : nat) : term3 n.
Proof. exact (@lem135734 n). Qed.
Lemma lem1244736 (n : nat) : (term3 n) = ((Nat.sub n n) = (NUMERAL 0)).
Proof. exact (eq_refl (term3 n)). Qed.
Lemma lem1244738 (n : nat) : term4 n.
Proof. exact (@lem1244710 n). Qed.
Lemma lem1244739 (n : nat) : (term4 n) = (term5 n).
Proof. exact (eq_refl (term4 n)). Qed.
Lemma lem1244740 (n : nat) : term5 n.
Proof. exact (EQ_MP (@lem1244739 n) (@lem1244738 n)). Qed.
Lemma lem1244741 (n : nat) (m : nat) : term6 n m.
Proof. exact (@lem1244740 n m). Qed.
Lemma lem1244742 (n : nat) (m : nat) : (term6 n m) = ((term7 m n) = (term8 n m)).
Proof. exact (eq_refl (term6 n m)). Qed.
Lemma lem1244751 (n : nat) (m : nat) : (term7 m n) = (term8 n m).
Proof. exact (EQ_MP (@lem1244742 n m) (@lem1244741 n m)). Qed.
Lemma lem1244752 (n : nat) : (term9 n) = (term10 n).
Proof. exact (@lem1244751 n n). Qed.
Lemma lem1244754 (n : nat) : (Nat.sub n n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem1244736 n) (@lem1244735 n)). Qed.
Lemma lem1244755 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1244756 (n : nat) : (term11 n) = term12.
Proof. exact (MK_COMB (@lem1244755) (@lem1244754 n)). Qed.
Lemma lem1244758 (n : nat) : (Nat.sub n n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem1244736 n) (@lem1244735 n)). Qed.
Lemma lem1244759 (n : nat) : (term10 n) = term13.
Proof. exact (MK_COMB (@lem1244756 n) (@lem1244758 n)). Qed.
Lemma lem1244761 (n : nat) : (term2 n) = n.
Proof. exact (EQ_MP (@lem1244733 n) (@lem1244732 n)). Qed.
Lemma lem1244762 : term13 = (NUMERAL 0).
Proof. exact (@lem1244761 (NUMERAL 0)). Qed.
Lemma lem1244763 (n : nat) : (term10 n) = (NUMERAL 0).
Proof. exact (TRANS (@lem1244759 n) (@lem1244762)). Qed.
Lemma lem1244764 (n : nat) : (term9 n) = (NUMERAL 0).
Proof. exact (TRANS (@lem1244752 n) (@lem1244763 n)). Qed.
Lemma lem1244765 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1244766 (n : nat) : (term14 n) = term15.
Proof. exact (MK_COMB (@lem1244765) (@lem1244764 n)). Qed.
Lemma lem1244767 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1244768 (n : nat) : ((term9 n) = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1244766 n) (@lem1244767)). Qed.
Lemma lem1244770 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1244771 (x : nat) : (x = x) = True.
Proof. exact (@lem1244770 nat x). Qed.
Lemma lem1244772 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1244771 (NUMERAL 0)). Qed.
Lemma lem1244773 (n : nat) : ((term9 n) = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem1244768 n) (@lem1244772)). Qed.
Lemma lem1244774 : term16 = term17.
Proof. exact (fun_ext (fun n : nat => @lem1244773 n)). Qed.
Lemma lem1244775 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1244776 : term18 = term19.
Proof. exact (MK_COMB (@lem1244775) (@lem1244774)). Qed.
Lemma lem1244778 {A : Type'} (t : Prop) : (term20 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1244779 (t : Prop) : (term21 t) = t.
Proof. exact (@lem1244778 nat t). Qed.
Lemma lem1244780 : term19 = True.
Proof. exact (@lem1244779 True). Qed.
Lemma lem1244781 : term18 = True.
Proof. exact (TRANS (@lem1244776) (@lem1244780)). Qed.
Lemma lem1244782 : True = term18.
Proof. exact (SYM (@lem1244781)). Qed.
Lemma lem1244783 : term18.
Proof. exact (EQ_MP (@lem1244782) (@lem0)). Qed.
