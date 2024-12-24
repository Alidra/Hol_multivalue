Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3070956_term_abbrevs.
Require Import INT_OF_NUM_MUL_spec.
Lemma lem3070945 (m : nat) (n : nat) (h1 : (term0 m n) = (term1 m n)) : (term0 m n) = (term1 m n).
Proof. exact (h1). Qed.
Lemma lem3070946 (m : nat) (n : nat) (h1 : (term0 m n) = (term1 m n)) : (term1 m n) = (term0 m n).
Proof. exact (SYM (@lem3070945 m n h1)). Qed.
Lemma lem3070947 (m : nat) (n : nat) (h1 : (term1 m n) = (term0 m n)) : (term1 m n) = (term0 m n).
Proof. exact (h1). Qed.
Lemma lem3070948 (m : nat) (n : nat) (h1 : (term1 m n) = (term0 m n)) : (term0 m n) = (term1 m n).
Proof. exact (SYM (@lem3070947 m n h1)). Qed.
Lemma lem3070949 (m : nat) (n : nat) : ((term0 m n) = (term1 m n)) = ((term1 m n) = (term0 m n)).
Proof. exact (prop_ext (fun h1 : (term0 m n) = (term1 m n) => @lem3070946 m n h1) (fun h1 : (term1 m n) = (term0 m n) => @lem3070948 m n h1)). Qed.
Lemma lem3070950 (m : nat) : (term2 m) = (term3 m).
Proof. exact (fun_ext (fun n : nat => @lem3070949 m n)). Qed.
Lemma lem3070951 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3070952 (m : nat) : (term4 m) = (term5 m).
Proof. exact (MK_COMB (@lem3070951) (@lem3070950 m)). Qed.
Lemma lem3070953 : term6 = term7.
Proof. exact (fun_ext (fun m : nat => @lem3070952 m)). Qed.
Lemma lem3070954 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3070955 : term8 = term9.
Proof. exact (MK_COMB (@lem3070954) (@lem3070953)). Qed.
Lemma lem3070956 : term9.
Proof. exact (EQ_MP (@lem3070955) (@lem2307381)). Qed.
