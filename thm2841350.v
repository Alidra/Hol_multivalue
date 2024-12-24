Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2841350_term_abbrevs.
Require Import INT_OF_NUM_MAX_spec.
Lemma lem2841339 (m : nat) (n : nat) (h1 : (term0 m n) = (term1 m n)) : (term0 m n) = (term1 m n).
Proof. exact (h1). Qed.
Lemma lem2841340 (m : nat) (n : nat) (h1 : (term0 m n) = (term1 m n)) : (term1 m n) = (term0 m n).
Proof. exact (SYM (@lem2841339 m n h1)). Qed.
Lemma lem2841341 (m : nat) (n : nat) (h1 : (term1 m n) = (term0 m n)) : (term1 m n) = (term0 m n).
Proof. exact (h1). Qed.
Lemma lem2841342 (m : nat) (n : nat) (h1 : (term1 m n) = (term0 m n)) : (term0 m n) = (term1 m n).
Proof. exact (SYM (@lem2841341 m n h1)). Qed.
Lemma lem2841343 (m : nat) (n : nat) : ((term0 m n) = (term1 m n)) = ((term1 m n) = (term0 m n)).
Proof. exact (prop_ext (fun h1 : (term0 m n) = (term1 m n) => @lem2841340 m n h1) (fun h1 : (term1 m n) = (term0 m n) => @lem2841342 m n h1)). Qed.
Lemma lem2841344 (m : nat) : (term2 m) = (term3 m).
Proof. exact (fun_ext (fun n : nat => @lem2841343 m n)). Qed.
Lemma lem2841345 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2841346 (m : nat) : (term4 m) = (term5 m).
Proof. exact (MK_COMB (@lem2841345) (@lem2841344 m)). Qed.
Lemma lem2841347 : term6 = term7.
Proof. exact (fun_ext (fun m : nat => @lem2841346 m)). Qed.
Lemma lem2841348 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2841349 : term8 = term9.
Proof. exact (MK_COMB (@lem2841348) (@lem2841347)). Qed.
Lemma lem2841350 : term9.
Proof. exact (EQ_MP (@lem2841349) (@lem2307278)). Qed.
