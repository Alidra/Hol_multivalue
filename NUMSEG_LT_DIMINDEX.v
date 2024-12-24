Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NUMSEG_LT_DIMINDEX_term_abbrevs.
Require Import DIMINDEX_NONZERO_spec.
Require Import NUMSEG_LT_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm82_spec.
Lemma lem7603371 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem7591719 A s). Qed.
Lemma lem7603372 {A : Type'} (s : A -> Prop) : (term0 A s) = (term1 A s).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem7603373 {A : Type'} (s : A -> Prop) : term1 A s.
Proof. exact (EQ_MP (@lem7603372 A s) (@lem7603371 A s)). Qed.
Lemma lem7603374 {A : Type'} (s : A -> Prop) : term2 A s.
Proof. exact (@lem82 ((@dimindex A s) = (NUMERAL 0))). Qed.
Lemma lem7603387 (n : nat) : term3 n.
Proof. exact (@lem5490796 n). Qed.
Lemma lem7603388 (n : nat) : (term3 n) = ((term4 n) = (term5 n)).
Proof. exact (eq_refl (term3 n)). Qed.
Lemma lem7603393 (n : nat) : (term4 n) = (term5 n).
Proof. exact (EQ_MP (@lem7603388 n) (@lem7603387 n)). Qed.
Lemma lem7603394 {N : Type'} : (term6 N) = (term7 N).
Proof. exact (@lem7603393 (@dimindex N (@UNIV N))). Qed.
Lemma lem7603398 {A : Type'} (s : A -> Prop) : ((@dimindex A s) = (NUMERAL 0)) = False.
Proof. exact (@lem7603374 A s (@lem7603373 A s)). Qed.
Lemma lem7603399 {N : Type'} (s : N -> Prop) : ((@dimindex N s) = (NUMERAL 0)) = False.
Proof. exact (@lem7603398 N s). Qed.
Lemma lem7603400 {N : Type'} : ((@dimindex N (@UNIV N)) = (NUMERAL 0)) = False.
Proof. exact (@lem7603399 N (@UNIV N)). Qed.
Lemma lem7603401 : (@COND (nat -> Prop)) = (@COND (nat -> Prop)).
Proof. exact (eq_refl (@COND (nat -> Prop))). Qed.
Lemma lem7603402 {N : Type'} : (term8 N) = (@COND (nat -> Prop) False).
Proof. exact (MK_COMB (@lem7603401) (@lem7603400 N)). Qed.
Lemma lem7603403 : (@EMPTY nat) = (@EMPTY nat).
Proof. exact (eq_refl (@EMPTY nat)). Qed.
Lemma lem7603404 {N : Type'} : (term9 N) = (@COND (nat -> Prop) False (@EMPTY nat)).
Proof. exact (MK_COMB (@lem7603402 N) (@lem7603403)). Qed.
Lemma lem7603405 {N : Type'} : (term10 N) = (term10 N).
Proof. exact (eq_refl (term10 N)). Qed.
Lemma lem7603406 {N : Type'} : (term7 N) = (term11 N).
Proof. exact (MK_COMB (@lem7603404 N) (@lem7603405 N)). Qed.
Lemma lem7603408 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7603409 (t1 : nat -> Prop) (t2 : nat -> Prop) : (@COND (nat -> Prop) False t1 t2) = t2.
Proof. exact (@lem7603408 (nat -> Prop) t1 t2). Qed.
Lemma lem7603410 {N : Type'} : (term11 N) = (term10 N).
Proof. exact (@lem7603409 (@EMPTY nat) (term10 N)). Qed.
Lemma lem7603411 {N : Type'} : (term7 N) = (term10 N).
Proof. exact (TRANS (@lem7603406 N) (@lem7603410 N)). Qed.
Lemma lem7603412 {N : Type'} : (term6 N) = (term10 N).
Proof. exact (TRANS (@lem7603394 N) (@lem7603411 N)). Qed.
Lemma lem7603413 : (@eq (nat -> Prop)) = (@eq (nat -> Prop)).
Proof. exact (eq_refl (@eq (nat -> Prop))). Qed.
Lemma lem7603414 {N : Type'} : (term12 N) = (term13 N).
Proof. exact (MK_COMB (@lem7603413) (@lem7603412 N)). Qed.
Lemma lem7603415 {N : Type'} : (term10 N) = (term10 N).
Proof. exact (eq_refl (term10 N)). Qed.
Lemma lem7603416 {N : Type'} : ((term6 N) = (term10 N)) = ((term10 N) = (term10 N)).
Proof. exact (MK_COMB (@lem7603414 N) (@lem7603415 N)). Qed.
Lemma lem7603418 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7603419 (x : nat -> Prop) : (x = x) = True.
Proof. exact (@lem7603418 (nat -> Prop) x). Qed.
Lemma lem7603420 {N : Type'} : ((term10 N) = (term10 N)) = True.
Proof. exact (@lem7603419 (term10 N)). Qed.
Lemma lem7603421 {N : Type'} : ((term6 N) = (term10 N)) = True.
Proof. exact (TRANS (@lem7603416 N) (@lem7603420 N)). Qed.
Lemma lem7603422 {N : Type'} : True = ((term6 N) = (term10 N)).
Proof. exact (SYM (@lem7603421 N)). Qed.
Lemma lem7603423 {N : Type'} : (term6 N) = (term10 N).
Proof. exact (EQ_MP (@lem7603422 N) (@lem0)). Qed.
