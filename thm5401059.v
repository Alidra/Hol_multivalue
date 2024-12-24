Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm5401059_term_abbrevs.
Require Import thm5400781_spec.
Require Import thm5400782_spec.
Lemma lem5401038 (m : nat) (p : nat) (n : nat) : (term0 p m n) = (term1 m p n).
Proof. exact (EQ_MP (@lem5400782 m p n) (@lem5400781 m n p)). Qed.
Lemma lem5401039 (m : nat) (x : nat) (n : nat) : (term2 x m n) = (term3 m x n).
Proof. exact (@lem5401038 m x (S n)). Qed.
Lemma lem5401042 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5401043 (m : nat) (x : nat) (n : nat) : (term4 x m n) = (term5 m x n).
Proof. exact (MK_COMB (@lem5401042) (@lem5401039 m x n)). Qed.
Lemma lem5401045 (m : nat) (p : nat) (n : nat) : (term0 p m n) = (term1 m p n).
Proof. exact (EQ_MP (@lem5400782 m p n) (@lem5400781 m n p)). Qed.
Lemma lem5401046 (m : nat) (x : nat) (n : nat) : (term0 x m n) = (term1 m x n).
Proof. exact (@lem5401045 m x n). Qed.
Lemma lem5401049 (m : nat) (x : nat) (n : nat) : ((term2 x m n) = (term0 x m n)) = ((term3 m x n) = (term1 m x n)).
Proof. exact (MK_COMB (@lem5401043 m x n) (@lem5401046 m x n)). Qed.
Lemma lem5401052 (m : nat) (n : nat) : (term6 m n) = (term7 m n).
Proof. exact (fun_ext (fun x : nat => @lem5401049 m x n)). Qed.
Lemma lem5401053 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5401054 (m : nat) (n : nat) : (term8 m n) = (term9 m n).
Proof. exact (MK_COMB (@lem5401053) (@lem5401052 m n)). Qed.
Lemma lem5401059 (m : nat) (n : nat) : (term9 m n) = (term8 m n).
Proof. exact (SYM (@lem5401054 m n)). Qed.
