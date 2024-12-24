Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2338239_term_abbrevs.
Require Import NOT_LE_spec.
Lemma lem2338228 (n : nat) (m : nat) (h1 : (term0 m n) = (Peano.lt n m)) : (term0 m n) = (Peano.lt n m).
Proof. exact (h1). Qed.
Lemma lem2338229 (n : nat) (m : nat) (h1 : (term0 m n) = (Peano.lt n m)) : (Peano.lt n m) = (term0 m n).
Proof. exact (SYM (@lem2338228 n m h1)). Qed.
Lemma lem2338230 (m : nat) (n : nat) (h1 : (Peano.lt n m) = (term0 m n)) : (Peano.lt n m) = (term0 m n).
Proof. exact (h1). Qed.
Lemma lem2338231 (m : nat) (n : nat) (h1 : (Peano.lt n m) = (term0 m n)) : (term0 m n) = (Peano.lt n m).
Proof. exact (SYM (@lem2338230 m n h1)). Qed.
Lemma lem2338232 (m : nat) (n : nat) : ((term0 m n) = (Peano.lt n m)) = ((Peano.lt n m) = (term0 m n)).
Proof. exact (prop_ext (fun h1 : (term0 m n) = (Peano.lt n m) => @lem2338229 n m h1) (fun h1 : (Peano.lt n m) = (term0 m n) => @lem2338231 m n h1)). Qed.
Lemma lem2338233 (m : nat) : (term1 m) = (term2 m).
Proof. exact (fun_ext (fun n : nat => @lem2338232 m n)). Qed.
Lemma lem2338234 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2338235 (m : nat) : (term3 m) = (term4 m).
Proof. exact (MK_COMB (@lem2338234) (@lem2338233 m)). Qed.
Lemma lem2338236 : term5 = term6.
Proof. exact (fun_ext (fun m : nat => @lem2338235 m)). Qed.
Lemma lem2338237 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2338238 : term7 = term8.
Proof. exact (MK_COMB (@lem2338237) (@lem2338236)). Qed.
Lemma lem2338239 : term8.
Proof. exact (EQ_MP (@lem2338238) (@lem97961)). Qed.
