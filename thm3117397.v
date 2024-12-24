Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3117397_term_abbrevs.
Require Import INT_OF_NUM_ADD_spec.
Lemma lem3117386 (m : nat) (n : nat) (h1 : (term0 m n) = (term1 m n)) : (term0 m n) = (term1 m n).
Proof. exact (h1). Qed.
Lemma lem3117387 (m : nat) (n : nat) (h1 : (term0 m n) = (term1 m n)) : (term1 m n) = (term0 m n).
Proof. exact (SYM (@lem3117386 m n h1)). Qed.
Lemma lem3117388 (m : nat) (n : nat) (h1 : (term1 m n) = (term0 m n)) : (term1 m n) = (term0 m n).
Proof. exact (h1). Qed.
Lemma lem3117389 (m : nat) (n : nat) (h1 : (term1 m n) = (term0 m n)) : (term0 m n) = (term1 m n).
Proof. exact (SYM (@lem3117388 m n h1)). Qed.
Lemma lem3117390 (m : nat) (n : nat) : ((term0 m n) = (term1 m n)) = ((term1 m n) = (term0 m n)).
Proof. exact (prop_ext (fun h1 : (term0 m n) = (term1 m n) => @lem3117387 m n h1) (fun h1 : (term1 m n) = (term0 m n) => @lem3117389 m n h1)). Qed.
Lemma lem3117391 (m : nat) : (term2 m) = (term3 m).
Proof. exact (fun_ext (fun n : nat => @lem3117390 m n)). Qed.
Lemma lem3117392 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3117393 (m : nat) : (term4 m) = (term5 m).
Proof. exact (MK_COMB (@lem3117392) (@lem3117391 m)). Qed.
Lemma lem3117394 : term6 = term7.
Proof. exact (fun_ext (fun m : nat => @lem3117393 m)). Qed.
Lemma lem3117395 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3117396 : term8 = term9.
Proof. exact (MK_COMB (@lem3117395) (@lem3117394)). Qed.
Lemma lem3117397 : term9.
Proof. exact (EQ_MP (@lem3117396) (@lem2306816)). Qed.
