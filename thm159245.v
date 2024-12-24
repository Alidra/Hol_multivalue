Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm159245_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import DIV_ZERO_spec.
Require Import MOD_ZERO_spec.
Require Import MULT_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem159157 : term0.
Proof. exact (proj1 (@lem77629)). Qed.
Lemma lem159158 (n : nat) : term1 n.
Proof. exact (@lem159157 n). Qed.
Lemma lem159159 (n : nat) : (term1 n) = ((term2 n) = n).
Proof. exact (eq_refl (term1 n)). Qed.
Lemma lem159191 : term3.
Proof. exact (proj1 (@lem81645)). Qed.
Lemma lem159192 (n : nat) : term4 n.
Proof. exact (@lem159191 n). Qed.
Lemma lem159193 (n : nat) : (term4 n) = ((term5 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term4 n)). Qed.
Lemma lem159195 (n : nat) : term6 n.
Proof. exact (@lem159121 n). Qed.
Lemma lem159196 (n : nat) : (term6 n) = ((term7 n) = n).
Proof. exact (eq_refl (term6 n)). Qed.
Lemma lem159198 (n : nat) : term8 n.
Proof. exact (@lem158192 n). Qed.
Lemma lem159199 (n : nat) : (term8 n) = ((term9 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term8 n)). Qed.
Lemma lem159204 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem159205 (m : nat) : (Nat.div m) = (Nat.div m).
Proof. exact (eq_refl (Nat.div m)). Qed.
Lemma lem159206 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.div m n) = (term9 m).
Proof. exact (MK_COMB (@lem159205 m) (@lem159204 n h1)). Qed.
Lemma lem159208 (n : nat) : (term9 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem159199 n) (@lem159198 n)). Qed.
Lemma lem159209 (m : nat) : (term9 m) = (NUMERAL 0).
Proof. exact (@lem159208 m). Qed.
Lemma lem159210 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.div m n) = (NUMERAL 0).
Proof. exact (TRANS (@lem159206 m n h1) (@lem159209 m)). Qed.
Lemma lem159211 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem159212 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term10 m n) = term11.
Proof. exact (MK_COMB (@lem159211) (@lem159210 m n h1)). Qed.
Lemma lem159214 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem159215 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term12 m n) = term13.
Proof. exact (MK_COMB (@lem159212 m n h1) (@lem159214 n h1)). Qed.
Lemma lem159217 (n : nat) : (term5 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem159193 n) (@lem159192 n)). Qed.
Lemma lem159218 : term13 = (NUMERAL 0).
Proof. exact (@lem159217 (NUMERAL 0)). Qed.
Lemma lem159219 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term12 m n) = (NUMERAL 0).
Proof. exact (TRANS (@lem159215 m n h1) (@lem159218)). Qed.
Lemma lem159220 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem159221 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term14 m n) = term15.
Proof. exact (MK_COMB (@lem159220) (@lem159219 m n h1)). Qed.
Lemma lem159223 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem159224 (m : nat) : (Nat.modulo m) = (Nat.modulo m).
Proof. exact (eq_refl (Nat.modulo m)). Qed.
Lemma lem159225 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.modulo m n) = (term7 m).
Proof. exact (MK_COMB (@lem159224 m) (@lem159223 n h1)). Qed.
Lemma lem159227 (n : nat) : (term7 n) = n.
Proof. exact (EQ_MP (@lem159196 n) (@lem159195 n)). Qed.
Lemma lem159228 (m : nat) : (term7 m) = m.
Proof. exact (@lem159227 m). Qed.
Lemma lem159229 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.modulo m n) = m.
Proof. exact (TRANS (@lem159225 m n h1) (@lem159228 m)). Qed.
Lemma lem159230 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term16 m n) = (term2 m).
Proof. exact (MK_COMB (@lem159221 m n h1) (@lem159229 m n h1)). Qed.
Lemma lem159232 (n : nat) : (term2 n) = n.
Proof. exact (EQ_MP (@lem159159 n) (@lem159158 n)). Qed.
Lemma lem159233 (m : nat) : (term2 m) = m.
Proof. exact (@lem159232 m). Qed.
Lemma lem159234 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term16 m n) = m.
Proof. exact (TRANS (@lem159230 m n h1) (@lem159233 m)). Qed.
Lemma lem159235 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem159236 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term17 m n) = (@eq nat m).
Proof. exact (MK_COMB (@lem159235) (@lem159234 m n h1)). Qed.
Lemma lem159237 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem159238 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : ((term16 m n) = m) = (m = m).
Proof. exact (MK_COMB (@lem159236 m n h1) (@lem159237 m)). Qed.
Lemma lem159240 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem159241 (x : nat) : (x = x) = True.
Proof. exact (@lem159240 nat x). Qed.
Lemma lem159242 (m : nat) : (m = m) = True.
Proof. exact (@lem159241 m). Qed.
Lemma lem159243 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : ((term16 m n) = m) = True.
Proof. exact (TRANS (@lem159238 m n h1) (@lem159242 m)). Qed.
Lemma lem159244 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : True = ((term16 m n) = m).
Proof. exact (SYM (@lem159243 m n h1)). Qed.
Lemma lem159245 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term16 m n) = m.
Proof. exact (EQ_MP (@lem159244 m n h1) (@lem0)). Qed.
