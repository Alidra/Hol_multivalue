Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259001_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1246847_spec.
Require Import thm1246848_spec.
Require Import thm1246874_spec.
Require Import thm1246875_spec.
Require Import thm1823_spec.
Lemma lem1258979 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1258980 (d''' : nat) (d'' : nat) : (term0 d''' d'') = (term1 d''' d'').
Proof. exact (@lem1258979 ((term2 d''' d'') = (NUMERAL 0))). Qed.
Lemma lem1258984 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem1246875 m n) (@lem1246874 m n)). Qed.
Lemma lem1258985 (d''' : nat) (d'' : nat) : (term2 d''' d'') = (term5 d''' d'').
Proof. exact (@lem1258984 d''' (Nat.add d'' d'')). Qed.
Lemma lem1258986 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1258987 (d''' : nat) (d'' : nat) : (term6 d''' d'') = (term7 d''' d'').
Proof. exact (MK_COMB (@lem1258986) (@lem1258985 d''' d'')). Qed.
Lemma lem1258988 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1258989 (d''' : nat) (d'' : nat) : ((term2 d''' d'') = (NUMERAL 0)) = ((term5 d''' d'') = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1258987 d''' d'') (@lem1258988)). Qed.
Lemma lem1258991 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem1246848 n (@lem1246847 n)). Qed.
Lemma lem1258992 (d''' : nat) (d'' : nat) : ((term5 d''' d'') = (NUMERAL 0)) = False.
Proof. exact (@lem1258991 (term8 d''' d'')). Qed.
Lemma lem1258993 (d''' : nat) (d'' : nat) : ((term2 d''' d'') = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem1258989 d''' d'') (@lem1258992 d''' d'')). Qed.
Lemma lem1258994 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1258995 (d''' : nat) (d'' : nat) : (term1 d''' d'') = (~ False).
Proof. exact (MK_COMB (@lem1258994) (@lem1258993 d''' d'')). Qed.
Lemma lem1258997 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1258998 (d''' : nat) (d'' : nat) : (term1 d''' d'') = True.
Proof. exact (TRANS (@lem1258995 d''' d'') (@lem1258997)). Qed.
Lemma lem1258999 (d''' : nat) (d'' : nat) : (term0 d''' d'') = True.
Proof. exact (TRANS (@lem1258980 d''' d'') (@lem1258998 d''' d'')). Qed.
Lemma lem1259000 (d''' : nat) (d'' : nat) : True = (term0 d''' d'').
Proof. exact (SYM (@lem1258999 d''' d'')). Qed.
Lemma lem1259001 (d''' : nat) (d'' : nat) : term0 d''' d''.
Proof. exact (EQ_MP (@lem1259000 d''' d'') (@lem0)). Qed.
