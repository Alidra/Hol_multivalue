Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXP_ONE_term_abbrevs.
Require Import MULT_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm86199_spec.
Lemma lem87726 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem87727 : term1.
Proof. exact (@lem87726 term2). Qed.
Lemma lem87728 : term3 = (term4 = term5).
Proof. exact (eq_refl term3). Qed.
Lemma lem87729 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem87730 : term6 = term7.
Proof. exact (MK_COMB (@lem87729) (@lem87728)). Qed.
Lemma lem87731 (n : nat) : (term8 n) = ((term9 n) = term5).
Proof. exact (eq_refl (term8 n)). Qed.
Lemma lem87732 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem87733 (n : nat) : (term10 n) = (term11 n).
Proof. exact (MK_COMB (@lem87732) (@lem87731 n)). Qed.
Lemma lem87734 (n : nat) : (term12 n) = ((term13 n) = term5).
Proof. exact (eq_refl (term12 n)). Qed.
Lemma lem87735 (n : nat) : (term14 n) = (term15 n).
Proof. exact (MK_COMB (@lem87733 n) (@lem87734 n)). Qed.
Lemma lem87736 : term16 = term17.
Proof. exact (fun_ext (fun n : nat => @lem87735 n)). Qed.
Lemma lem87737 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem87738 : term18 = term19.
Proof. exact (MK_COMB (@lem87737) (@lem87736)). Qed.
Lemma lem87739 : term20 = term21.
Proof. exact (MK_COMB (@lem87730) (@lem87738)). Qed.
Lemma lem87740 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem87741 : term22 = term23.
Proof. exact (MK_COMB (@lem87740) (@lem87739)). Qed.
Lemma lem87742 (n : nat) : (term8 n) = ((term9 n) = term5).
Proof. exact (eq_refl (term8 n)). Qed.
Lemma lem87743 : term24 = term2.
Proof. exact (fun_ext (fun n : nat => @lem87742 n)). Qed.
Lemma lem87744 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem87745 : term25 = term26.
Proof. exact (MK_COMB (@lem87744) (@lem87743)). Qed.
Lemma lem87746 : term1 = term27.
Proof. exact (MK_COMB (@lem87741) (@lem87745)). Qed.
Lemma lem87747 : term27.
Proof. exact (EQ_MP (@lem87746) (@lem87727)). Qed.
Lemma lem87790 : term28.
Proof. exact (proj1 (@lem86199)). Qed.
Lemma lem87791 (m : nat) : term29 m.
Proof. exact (@lem87790 m). Qed.
Lemma lem87792 (m : nat) : (term29 m) = ((term30 m) = term5).
Proof. exact (eq_refl (term29 m)). Qed.
Lemma lem87797 (m : nat) : (term30 m) = term5.
Proof. exact (EQ_MP (@lem87792 m) (@lem87791 m)). Qed.
Lemma lem87798 : term4 = term5.
Proof. exact (@lem87797 term5). Qed.
Lemma lem87799 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem87800 : term31 = term32.
Proof. exact (MK_COMB (@lem87799) (@lem87798)). Qed.
Lemma lem87801 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem87802 : (term4 = term5) = (term5 = term5).
Proof. exact (MK_COMB (@lem87800) (@lem87801)). Qed.
Lemma lem87804 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem87805 (x : nat) : (x = x) = True.
Proof. exact (@lem87804 nat x). Qed.
Lemma lem87806 : (term5 = term5) = True.
Proof. exact (@lem87805 term5). Qed.
Lemma lem87807 : (term4 = term5) = True.
Proof. exact (TRANS (@lem87802) (@lem87806)). Qed.
Lemma lem87808 : True = (term4 = term5).
Proof. exact (SYM (@lem87807)). Qed.
Lemma lem87809 : term4 = term5.
Proof. exact (EQ_MP (@lem87808) (@lem0)). Qed.
Lemma lem87810 : term33.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem87811 : term34.
Proof. exact (proj2 (@lem87810)). Qed.
Lemma lem87832 : term35.
Proof. exact (proj1 (@lem87811)). Qed.
Lemma lem87833 (n : nat) : term36 n.
Proof. exact (@lem87832 n). Qed.
Lemma lem87834 (n : nat) : (term36 n) = ((term37 n) = n).
Proof. exact (eq_refl (term36 n)). Qed.
Lemma lem87844 : term38.
Proof. exact (proj2 (@lem86199)). Qed.
Lemma lem87845 (m : nat) : term39 m.
Proof. exact (@lem87844 m). Qed.
Lemma lem87846 (m : nat) : (term39 m) = (term40 m).
Proof. exact (eq_refl (term39 m)). Qed.
Lemma lem87847 (m : nat) : term40 m.
Proof. exact (EQ_MP (@lem87846 m) (@lem87845 m)). Qed.
Lemma lem87848 (m : nat) (n : nat) : term41 m n.
Proof. exact (@lem87847 m n). Qed.
Lemma lem87849 (m : nat) (n : nat) : (term41 m n) = ((term42 m n) = (term43 m n)).
Proof. exact (eq_refl (term41 m n)). Qed.
Lemma lem87858 (m : nat) (n : nat) : (term42 m n) = (term43 m n).
Proof. exact (EQ_MP (@lem87849 m n) (@lem87848 m n)). Qed.
Lemma lem87859 (n : nat) : (term13 n) = (term44 n).
Proof. exact (@lem87858 term5 n). Qed.
Lemma lem87861 (n : nat) : (term37 n) = n.
Proof. exact (EQ_MP (@lem87834 n) (@lem87833 n)). Qed.
Lemma lem87862 (n : nat) : (term44 n) = (term9 n).
Proof. exact (@lem87861 (term9 n)). Qed.
Lemma lem87864 (n : nat) (h1 : (term9 n) = term5) : (term9 n) = term5.
Proof. exact (h1). Qed.
Lemma lem87865 (n : nat) (h1 : (term9 n) = term5) : (term44 n) = term5.
Proof. exact (TRANS (@lem87862 n) (@lem87864 n h1)). Qed.
Lemma lem87866 (n : nat) (h1 : (term9 n) = term5) : (term13 n) = term5.
Proof. exact (TRANS (@lem87859 n) (@lem87865 n h1)). Qed.
Lemma lem87867 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem87868 (n : nat) (h1 : (term9 n) = term5) : (term45 n) = term32.
Proof. exact (MK_COMB (@lem87867) (@lem87866 n h1)). Qed.
Lemma lem87869 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem87870 (n : nat) (h1 : (term9 n) = term5) : ((term13 n) = term5) = (term5 = term5).
Proof. exact (MK_COMB (@lem87868 n h1) (@lem87869)). Qed.
Lemma lem87872 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem87873 (x : nat) : (x = x) = True.
Proof. exact (@lem87872 nat x). Qed.
Lemma lem87874 : (term5 = term5) = True.
Proof. exact (@lem87873 term5). Qed.
Lemma lem87875 (n : nat) (h1 : (term9 n) = term5) : ((term13 n) = term5) = True.
Proof. exact (TRANS (@lem87870 n h1) (@lem87874)). Qed.
Lemma lem87876 (n : nat) (h1 : (term9 n) = term5) : True = ((term13 n) = term5).
Proof. exact (SYM (@lem87875 n h1)). Qed.
Lemma lem87877 (n : nat) (h1 : (term9 n) = term5) : (term13 n) = term5.
Proof. exact (EQ_MP (@lem87876 n h1) (@lem0)). Qed.
Lemma lem87878 (n : nat) : term15 n.
Proof. exact (fun h0 : (term9 n) = term5 => @lem87877 n h0). Qed.
Lemma lem87883 : term19.
Proof. exact (fun n : nat => @lem87878 n). Qed.
Lemma lem87884 : term21.
Proof. exact (conj (@lem87809) (@lem87883)). Qed.
Lemma lem87885 : term26.
Proof. exact (@lem87747 (@lem87884)). Qed.
