Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2405813_term_abbrevs.
Require Import INT_ADD_LINV_spec.
Require Import INT_ADD_RINV_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem2405769 (x : int) : term0 x.
Proof. exact (@lem2301245 x). Qed.
Lemma lem2405770 (x : int) : (term0 x) = ((term1 x) = term2).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2405772 (x : int) : term3 x.
Proof. exact (@lem2301157 x). Qed.
Lemma lem2405773 (x : int) : (term3 x) = ((term4 x) = term2).
Proof. exact (eq_refl (term3 x)). Qed.
Lemma lem2405780 (x : int) : (term4 x) = term2.
Proof. exact (EQ_MP (@lem2405773 x) (@lem2405772 x)). Qed.
Lemma lem2405781 (m : nat) : (term5 m) = term2.
Proof. exact (@lem2405780 (int_of_num m)). Qed.
Lemma lem2405782 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2405783 (m : nat) : (term6 m) = term7.
Proof. exact (MK_COMB (@lem2405782) (@lem2405781 m)). Qed.
Lemma lem2405784 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2405785 (m : nat) : ((term5 m) = term2) = (term2 = term2).
Proof. exact (MK_COMB (@lem2405783 m) (@lem2405784)). Qed.
Lemma lem2405787 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2405788 (x : int) : (x = x) = True.
Proof. exact (@lem2405787 int x). Qed.
Lemma lem2405789 : (term2 = term2) = True.
Proof. exact (@lem2405788 term2). Qed.
Lemma lem2405790 (m : nat) : ((term5 m) = term2) = True.
Proof. exact (TRANS (@lem2405785 m) (@lem2405789)). Qed.
Lemma lem2405791 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2405792 (m : nat) : (term8 m) = (and True).
Proof. exact (MK_COMB (@lem2405791) (@lem2405790 m)). Qed.
Lemma lem2405796 (x : int) : (term1 x) = term2.
Proof. exact (EQ_MP (@lem2405770 x) (@lem2405769 x)). Qed.
Lemma lem2405797 (m : nat) : (term9 m) = term2.
Proof. exact (@lem2405796 (int_of_num m)). Qed.
Lemma lem2405798 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2405799 (m : nat) : (term10 m) = term7.
Proof. exact (MK_COMB (@lem2405798) (@lem2405797 m)). Qed.
Lemma lem2405800 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem2405801 (m : nat) : ((term9 m) = term2) = (term2 = term2).
Proof. exact (MK_COMB (@lem2405799 m) (@lem2405800)). Qed.
Lemma lem2405803 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2405804 (x : int) : (x = x) = True.
Proof. exact (@lem2405803 int x). Qed.
Lemma lem2405805 : (term2 = term2) = True.
Proof. exact (@lem2405804 term2). Qed.
Lemma lem2405806 (m : nat) : ((term9 m) = term2) = True.
Proof. exact (TRANS (@lem2405801 m) (@lem2405805)). Qed.
Lemma lem2405807 (m : nat) : (term11 m) = (True /\ True).
Proof. exact (MK_COMB (@lem2405792 m) (@lem2405806 m)). Qed.
Lemma lem2405809 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2405810 : (True /\ True) = True.
Proof. exact (@lem2405809 True). Qed.
Lemma lem2405811 (m : nat) : (term11 m) = True.
Proof. exact (TRANS (@lem2405807 m) (@lem2405810)). Qed.
Lemma lem2405812 (m : nat) : True = (term11 m).
Proof. exact (SYM (@lem2405811 m)). Qed.
Lemma lem2405813 (m : nat) : term11 m.
Proof. exact (EQ_MP (@lem2405812 m) (@lem0)). Qed.
