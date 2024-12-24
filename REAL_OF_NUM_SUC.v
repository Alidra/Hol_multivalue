Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_OF_NUM_SUC_term_abbrevs.
Require Import ADD1_spec.
Require Import thm0_spec.
Require Import thm1340339_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1484028 (m : nat) : term0 m.
Proof. exact (@lem1340339 m). Qed.
Lemma lem1484029 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1484030 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem1484029 m) (@lem1484028 m)). Qed.
Lemma lem1484031 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem1484030 m n). Qed.
Lemma lem1484032 (m : nat) (n : nat) : (term2 m n) = ((term3 m n) = (term4 m n)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1484034 (m : nat) : term5 m.
Proof. exact (@lem80621 m). Qed.
Lemma lem1484035 (m : nat) : (term5 m) = ((S m) = (term6 m)).
Proof. exact (eq_refl (term5 m)). Qed.
Lemma lem1484044 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem1484032 m n) (@lem1484031 m n)). Qed.
Lemma lem1484045 (n : nat) : (term7 n) = (term8 n).
Proof. exact (@lem1484044 n term9). Qed.
Lemma lem1484046 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1484047 (n : nat) : (term10 n) = (term11 n).
Proof. exact (MK_COMB (@lem1484046) (@lem1484045 n)). Qed.
Lemma lem1484049 (m : nat) : (S m) = (term6 m).
Proof. exact (EQ_MP (@lem1484035 m) (@lem1484034 m)). Qed.
Lemma lem1484050 (n : nat) : (S n) = (term6 n).
Proof. exact (@lem1484049 n). Qed.
Lemma lem1484051 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1484052 (n : nat) : (term12 n) = (term8 n).
Proof. exact (MK_COMB (@lem1484051) (@lem1484050 n)). Qed.
Lemma lem1484053 (n : nat) : ((term7 n) = (term12 n)) = ((term8 n) = (term8 n)).
Proof. exact (MK_COMB (@lem1484047 n) (@lem1484052 n)). Qed.
Lemma lem1484055 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1484056 (x : real) : (x = x) = True.
Proof. exact (@lem1484055 real x). Qed.
Lemma lem1484057 (n : nat) : ((term8 n) = (term8 n)) = True.
Proof. exact (@lem1484056 (term8 n)). Qed.
Lemma lem1484058 (n : nat) : ((term7 n) = (term12 n)) = True.
Proof. exact (TRANS (@lem1484053 n) (@lem1484057 n)). Qed.
Lemma lem1484059 : term13 = term14.
Proof. exact (fun_ext (fun n : nat => @lem1484058 n)). Qed.
Lemma lem1484060 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1484061 : term15 = term16.
Proof. exact (MK_COMB (@lem1484060) (@lem1484059)). Qed.
Lemma lem1484063 {A : Type'} (t : Prop) : (term17 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1484064 (t : Prop) : (term18 t) = t.
Proof. exact (@lem1484063 nat t). Qed.
Lemma lem1484065 : term16 = True.
Proof. exact (@lem1484064 True). Qed.
Lemma lem1484066 : term15 = True.
Proof. exact (TRANS (@lem1484061) (@lem1484065)). Qed.
Lemma lem1484067 : True = term15.
Proof. exact (SYM (@lem1484066)). Qed.
Lemma lem1484068 : term15.
Proof. exact (EQ_MP (@lem1484067) (@lem0)). Qed.
