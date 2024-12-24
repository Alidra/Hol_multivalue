Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3117435_term_abbrevs.
Require Import INT_OF_NUM_MUL_spec.
Lemma lem3117400 (m : nat) (n : nat) (h1 : (term0 m n) = (term1 m n)) : (term0 m n) = (term1 m n).
Proof. exact (h1). Qed.
Lemma lem3117401 (m : nat) (n : nat) (h1 : (term0 m n) = (term1 m n)) : (term1 m n) = (term0 m n).
Proof. exact (SYM (@lem3117400 m n h1)). Qed.
Lemma lem3117402 (m : nat) (n : nat) (h1 : (term1 m n) = (term0 m n)) : (term1 m n) = (term0 m n).
Proof. exact (h1). Qed.
Lemma lem3117403 (m : nat) (n : nat) (h1 : (term1 m n) = (term0 m n)) : (term0 m n) = (term1 m n).
Proof. exact (SYM (@lem3117402 m n h1)). Qed.
Lemma lem3117404 (m : nat) (n : nat) : ((term0 m n) = (term1 m n)) = ((term1 m n) = (term0 m n)).
Proof. exact (prop_ext (fun h1 : (term0 m n) = (term1 m n) => @lem3117401 m n h1) (fun h1 : (term1 m n) = (term0 m n) => @lem3117403 m n h1)). Qed.
Lemma lem3117405 (m : nat) : (term2 m) = (term3 m).
Proof. exact (fun_ext (fun n : nat => @lem3117404 m n)). Qed.
Lemma lem3117406 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3117407 (m : nat) : (term4 m) = (term5 m).
Proof. exact (MK_COMB (@lem3117406) (@lem3117405 m)). Qed.
Lemma lem3117408 : term6 = term7.
Proof. exact (fun_ext (fun m : nat => @lem3117407 m)). Qed.
Lemma lem3117409 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3117410 : term8 = term9.
Proof. exact (MK_COMB (@lem3117409) (@lem3117408)). Qed.
Lemma lem3117411 : term9.
Proof. exact (EQ_MP (@lem3117410) (@lem2307381)). Qed.
Lemma lem3117432 (m : nat) : term10 m.
Proof. exact (@lem3117411 m). Qed.
Lemma lem3117433 (m : nat) : (term10 m) = (term5 m).
Proof. exact (eq_refl (term10 m)). Qed.
Lemma lem3117434 (m : nat) : term5 m.
Proof. exact (EQ_MP (@lem3117433 m) (@lem3117432 m)). Qed.
Lemma lem3117435 (m : nat) (n : nat) : term11 m n.
Proof. exact (@lem3117434 m n). Qed.
