Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LTE_ANTISYM_term_abbrevs.
Require Import CONJ_SYM_spec.
Require Import LET_ANTISYM_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm82_spec.
Lemma lem93010 (m : nat) : term0 m.
Proof. exact (@lem93009 m). Qed.
Lemma lem93011 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem93012 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem93011 m) (@lem93010 m)). Qed.
Lemma lem93013 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem93012 m n). Qed.
Lemma lem93014 (n : nat) (m : nat) : (term2 m n) = (term3 n m).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem93015 (n : nat) (m : nat) : term3 n m.
Proof. exact (EQ_MP (@lem93014 n m) (@lem93013 m n)). Qed.
Lemma lem93016 (n : nat) (m : nat) : term4 n m.
Proof. exact (@lem82 (term5 n m)). Qed.
Lemma lem93018 (t1 : Prop) : term6 t1.
Proof. exact (@lem539 t1). Qed.
Lemma lem93019 (t1 : Prop) : (term6 t1) = (term7 t1).
Proof. exact (eq_refl (term6 t1)). Qed.
Lemma lem93020 (t1 : Prop) : term7 t1.
Proof. exact (EQ_MP (@lem93019 t1) (@lem93018 t1)). Qed.
Lemma lem93021 (t1 : Prop) (t2 : Prop) : term8 t1 t2.
Proof. exact (@lem93020 t1 t2). Qed.
Lemma lem93022 (t2 : Prop) (t1 : Prop) : (term8 t1 t2) = ((t1 /\ t2) = (t2 /\ t1)).
Proof. exact (eq_refl (term8 t1 t2)). Qed.
Lemma lem93035 (t2 : Prop) (t1 : Prop) : (t1 /\ t2) = (t2 /\ t1).
Proof. exact (EQ_MP (@lem93022 t2 t1) (@lem93021 t1 t2)). Qed.
Lemma lem93036 (m : nat) (n : nat) : (term9 n m) = (term5 m n).
Proof. exact (@lem93035 (Peano.le n m) (Peano.lt m n)). Qed.
Lemma lem93037 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem93038 (m : nat) (n : nat) : (term10 n m) = (term3 m n).
Proof. exact (MK_COMB (@lem93037) (@lem93036 m n)). Qed.
Lemma lem93039 (m : nat) : (term11 m) = (term12 m).
Proof. exact (fun_ext (fun n : nat => @lem93038 m n)). Qed.
Lemma lem93040 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem93041 (m : nat) : (term13 m) = (term14 m).
Proof. exact (MK_COMB (@lem93040) (@lem93039 m)). Qed.
Lemma lem93042 : term15 = term16.
Proof. exact (fun_ext (fun m : nat => @lem93041 m)). Qed.
Lemma lem93043 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem93044 : term17 = term18.
Proof. exact (MK_COMB (@lem93043) (@lem93042)). Qed.
Lemma lem93045 : term18 = term17.
Proof. exact (SYM (@lem93044)). Qed.
Lemma lem93055 (n : nat) (m : nat) : (term5 n m) = False.
Proof. exact (@lem93016 n m (@lem93015 n m)). Qed.
Lemma lem93056 (m : nat) (n : nat) : (term5 m n) = False.
Proof. exact (@lem93055 m n). Qed.
Lemma lem93057 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem93058 (m : nat) (n : nat) : (term3 m n) = (~ False).
Proof. exact (MK_COMB (@lem93057) (@lem93056 m n)). Qed.
Lemma lem93060 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem93061 (m : nat) (n : nat) : (term3 m n) = True.
Proof. exact (TRANS (@lem93058 m n) (@lem93060)). Qed.
Lemma lem93062 (m : nat) : (term12 m) = term19.
Proof. exact (fun_ext (fun n : nat => @lem93061 m n)). Qed.
Lemma lem93063 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem93064 (m : nat) : (term14 m) = term20.
Proof. exact (MK_COMB (@lem93063) (@lem93062 m)). Qed.
Lemma lem93066 {A : Type'} (t : Prop) : (term21 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem93067 (t : Prop) : (term22 t) = t.
Proof. exact (@lem93066 nat t). Qed.
Lemma lem93068 : term20 = True.
Proof. exact (@lem93067 True). Qed.
Lemma lem93069 (m : nat) : (term14 m) = True.
Proof. exact (TRANS (@lem93064 m) (@lem93068)). Qed.
Lemma lem93070 : term16 = term19.
Proof. exact (fun_ext (fun m : nat => @lem93069 m)). Qed.
Lemma lem93071 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem93072 : term18 = term20.
Proof. exact (MK_COMB (@lem93071) (@lem93070)). Qed.
Lemma lem93074 {A : Type'} (t : Prop) : (term21 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem93075 (t : Prop) : (term22 t) = t.
Proof. exact (@lem93074 nat t). Qed.
Lemma lem93076 : term20 = True.
Proof. exact (@lem93075 True). Qed.
Lemma lem93077 : term18 = True.
Proof. exact (TRANS (@lem93072) (@lem93076)). Qed.
Lemma lem93078 : True = term18.
Proof. exact (SYM (@lem93077)). Qed.
Lemma lem93079 : term18.
Proof. exact (EQ_MP (@lem93078) (@lem0)). Qed.
Lemma lem93080 : term17.
Proof. exact (EQ_MP (@lem93045) (@lem93079)). Qed.
