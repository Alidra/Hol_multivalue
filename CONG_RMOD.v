Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CONG_RMOD_term_abbrevs.
Require Import CONG_spec.
Require Import MOD_MOD_REFL_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem3070720 (m : nat) : term0 m.
Proof. exact (@lem183010 m). Qed.
Lemma lem3070721 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem3070722 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem3070721 m) (@lem3070720 m)). Qed.
Lemma lem3070723 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem3070722 m n). Qed.
Lemma lem3070724 (m : nat) (n : nat) : (term2 m n) = ((term3 m n) = (Nat.modulo m n)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem3070726 (x : nat) : term4 x.
Proof. exact (@lem3070637 x). Qed.
Lemma lem3070727 (x : nat) : (term4 x) = (term5 x).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem3070728 (x : nat) : term5 x.
Proof. exact (EQ_MP (@lem3070727 x) (@lem3070726 x)). Qed.
Lemma lem3070729 (x : nat) (y : nat) : term6 x y.
Proof. exact (@lem3070728 x y). Qed.
Lemma lem3070730 (x : nat) (y : nat) : (term6 x y) = (term7 x y).
Proof. exact (eq_refl (term6 x y)). Qed.
Lemma lem3070731 (x : nat) (y : nat) : term7 x y.
Proof. exact (EQ_MP (@lem3070730 x y) (@lem3070729 x y)). Qed.
Lemma lem3070732 (x : nat) (y : nat) (n : nat) : term8 x y n.
Proof. exact (@lem3070731 x y n). Qed.
Lemma lem3070733 (x : nat) (y : nat) (n : nat) : (term8 x y n) = ((term9 x y n) = ((Nat.modulo x n) = (Nat.modulo y n))).
Proof. exact (eq_refl (term8 x y n)). Qed.
Lemma lem3070750 (x : nat) (y : nat) (n : nat) : (term9 x y n) = ((Nat.modulo x n) = (Nat.modulo y n)).
Proof. exact (EQ_MP (@lem3070733 x y n) (@lem3070732 x y n)). Qed.
Lemma lem3070751 (x : nat) (y : nat) (n : nat) : (term10 x y n) = ((Nat.modulo x n) = (term3 y n)).
Proof. exact (@lem3070750 x (Nat.modulo y n) n). Qed.
Lemma lem3070755 (m : nat) (n : nat) : (term3 m n) = (Nat.modulo m n).
Proof. exact (EQ_MP (@lem3070724 m n) (@lem3070723 m n)). Qed.
Lemma lem3070756 (y : nat) (n : nat) : (term3 y n) = (Nat.modulo y n).
Proof. exact (@lem3070755 y n). Qed.
Lemma lem3070757 (x : nat) (n : nat) : (term11 x n) = (term11 x n).
Proof. exact (eq_refl (term11 x n)). Qed.
Lemma lem3070758 (x : nat) (y : nat) (n : nat) : ((Nat.modulo x n) = (term3 y n)) = ((Nat.modulo x n) = (Nat.modulo y n)).
Proof. exact (MK_COMB (@lem3070757 x n) (@lem3070756 y n)). Qed.
Lemma lem3070761 (x : nat) (y : nat) (n : nat) : (term10 x y n) = ((Nat.modulo x n) = (Nat.modulo y n)).
Proof. exact (TRANS (@lem3070751 x y n) (@lem3070758 x y n)). Qed.
Lemma lem3070762 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3070763 (x : nat) (y : nat) (n : nat) : (term12 x y n) = (term13 x y n).
Proof. exact (MK_COMB (@lem3070762) (@lem3070761 x y n)). Qed.
Lemma lem3070765 (x : nat) (y : nat) (n : nat) : (term9 x y n) = ((Nat.modulo x n) = (Nat.modulo y n)).
Proof. exact (EQ_MP (@lem3070733 x y n) (@lem3070732 x y n)). Qed.
Lemma lem3070768 (x : nat) (y : nat) (n : nat) : ((term10 x y n) = (term9 x y n)) = (((Nat.modulo x n) = (Nat.modulo y n)) = ((Nat.modulo x n) = (Nat.modulo y n))).
Proof. exact (MK_COMB (@lem3070763 x y n) (@lem3070765 x y n)). Qed.
Lemma lem3070770 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3070771 (x : Prop) : (x = x) = True.
Proof. exact (@lem3070770 Prop x). Qed.
Lemma lem3070772 (x : nat) (y : nat) (n : nat) : (((Nat.modulo x n) = (Nat.modulo y n)) = ((Nat.modulo x n) = (Nat.modulo y n))) = True.
Proof. exact (@lem3070771 ((Nat.modulo x n) = (Nat.modulo y n))). Qed.
Lemma lem3070773 (x : nat) (y : nat) (n : nat) : ((term10 x y n) = (term9 x y n)) = True.
Proof. exact (TRANS (@lem3070768 x y n) (@lem3070772 x y n)). Qed.
Lemma lem3070774 (x : nat) (y : nat) : (term14 x y) = term15.
Proof. exact (fun_ext (fun n : nat => @lem3070773 x y n)). Qed.
Lemma lem3070775 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3070776 (x : nat) (y : nat) : (term16 x y) = term17.
Proof. exact (MK_COMB (@lem3070775) (@lem3070774 x y)). Qed.
Lemma lem3070778 {A : Type'} (t : Prop) : (term18 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3070779 (t : Prop) : (term19 t) = t.
Proof. exact (@lem3070778 nat t). Qed.
Lemma lem3070780 : term17 = True.
Proof. exact (@lem3070779 True). Qed.
Lemma lem3070781 (x : nat) (y : nat) : (term16 x y) = True.
Proof. exact (TRANS (@lem3070776 x y) (@lem3070780)). Qed.
Lemma lem3070782 (x : nat) : (term20 x) = term15.
Proof. exact (fun_ext (fun y : nat => @lem3070781 x y)). Qed.
Lemma lem3070783 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3070784 (x : nat) : (term21 x) = term17.
Proof. exact (MK_COMB (@lem3070783) (@lem3070782 x)). Qed.
Lemma lem3070786 {A : Type'} (t : Prop) : (term18 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3070787 (t : Prop) : (term19 t) = t.
Proof. exact (@lem3070786 nat t). Qed.
Lemma lem3070788 : term17 = True.
Proof. exact (@lem3070787 True). Qed.
Lemma lem3070789 (x : nat) : (term21 x) = True.
Proof. exact (TRANS (@lem3070784 x) (@lem3070788)). Qed.
Lemma lem3070790 : term22 = term15.
Proof. exact (fun_ext (fun x : nat => @lem3070789 x)). Qed.
Lemma lem3070791 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3070792 : term23 = term17.
Proof. exact (MK_COMB (@lem3070791) (@lem3070790)). Qed.
Lemma lem3070794 {A : Type'} (t : Prop) : (term18 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3070795 (t : Prop) : (term19 t) = t.
Proof. exact (@lem3070794 nat t). Qed.
Lemma lem3070796 : term17 = True.
Proof. exact (@lem3070795 True). Qed.
Lemma lem3070797 : term23 = True.
Proof. exact (TRANS (@lem3070792) (@lem3070796)). Qed.
Lemma lem3070798 : True = term23.
Proof. exact (SYM (@lem3070797)). Qed.
Lemma lem3070799 : term23.
Proof. exact (EQ_MP (@lem3070798) (@lem0)). Qed.
