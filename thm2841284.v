Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2841284_term_abbrevs.
Require Import INT_OF_NUM_LT_spec.
Lemma lem2841273 (m : nat) (n : nat) (h1 : (term0 m n) = (Peano.lt m n)) : (term0 m n) = (Peano.lt m n).
Proof. exact (h1). Qed.
Lemma lem2841274 (m : nat) (n : nat) (h1 : (term0 m n) = (Peano.lt m n)) : (Peano.lt m n) = (term0 m n).
Proof. exact (SYM (@lem2841273 m n h1)). Qed.
Lemma lem2841275 (m : nat) (n : nat) (h1 : (Peano.lt m n) = (term0 m n)) : (Peano.lt m n) = (term0 m n).
Proof. exact (h1). Qed.
Lemma lem2841276 (m : nat) (n : nat) (h1 : (Peano.lt m n) = (term0 m n)) : (term0 m n) = (Peano.lt m n).
Proof. exact (SYM (@lem2841275 m n h1)). Qed.
Lemma lem2841277 (m : nat) (n : nat) : ((term0 m n) = (Peano.lt m n)) = ((Peano.lt m n) = (term0 m n)).
Proof. exact (prop_ext (fun h1 : (term0 m n) = (Peano.lt m n) => @lem2841274 m n h1) (fun h1 : (Peano.lt m n) = (term0 m n) => @lem2841276 m n h1)). Qed.
Lemma lem2841278 (m : nat) : (term1 m) = (term2 m).
Proof. exact (fun_ext (fun n : nat => @lem2841277 m n)). Qed.
Lemma lem2841279 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2841280 (m : nat) : (term3 m) = (term4 m).
Proof. exact (MK_COMB (@lem2841279) (@lem2841278 m)). Qed.
Lemma lem2841281 : term5 = term6.
Proof. exact (fun_ext (fun m : nat => @lem2841280 m)). Qed.
Lemma lem2841282 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2841283 : term7 = term8.
Proof. exact (MK_COMB (@lem2841282) (@lem2841281)). Qed.
Lemma lem2841284 : term8.
Proof. exact (EQ_MP (@lem2841283) (@lem2307247)). Qed.
