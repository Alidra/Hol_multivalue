Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2841270_term_abbrevs.
Require Import INT_OF_NUM_LE_spec.
Lemma lem2841259 (m : nat) (n : nat) (h1 : (term0 m n) = (Peano.le m n)) : (term0 m n) = (Peano.le m n).
Proof. exact (h1). Qed.
Lemma lem2841260 (m : nat) (n : nat) (h1 : (term0 m n) = (Peano.le m n)) : (Peano.le m n) = (term0 m n).
Proof. exact (SYM (@lem2841259 m n h1)). Qed.
Lemma lem2841261 (m : nat) (n : nat) (h1 : (Peano.le m n) = (term0 m n)) : (Peano.le m n) = (term0 m n).
Proof. exact (h1). Qed.
Lemma lem2841262 (m : nat) (n : nat) (h1 : (Peano.le m n) = (term0 m n)) : (term0 m n) = (Peano.le m n).
Proof. exact (SYM (@lem2841261 m n h1)). Qed.
Lemma lem2841263 (m : nat) (n : nat) : ((term0 m n) = (Peano.le m n)) = ((Peano.le m n) = (term0 m n)).
Proof. exact (prop_ext (fun h1 : (term0 m n) = (Peano.le m n) => @lem2841260 m n h1) (fun h1 : (Peano.le m n) = (term0 m n) => @lem2841262 m n h1)). Qed.
Lemma lem2841264 (m : nat) : (term1 m) = (term2 m).
Proof. exact (fun_ext (fun n : nat => @lem2841263 m n)). Qed.
Lemma lem2841265 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2841266 (m : nat) : (term3 m) = (term4 m).
Proof. exact (MK_COMB (@lem2841265) (@lem2841264 m)). Qed.
Lemma lem2841267 : term5 = term6.
Proof. exact (fun_ext (fun m : nat => @lem2841266 m)). Qed.
Lemma lem2841268 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2841269 : term7 = term8.
Proof. exact (MK_COMB (@lem2841268) (@lem2841267)). Qed.
Lemma lem2841270 : term8.
Proof. exact (EQ_MP (@lem2841269) (@lem2307222)). Qed.
