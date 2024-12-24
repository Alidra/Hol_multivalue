Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259212_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1246847_spec.
Require Import thm1246848_spec.
Require Import thm1246874_spec.
Require Import thm1246875_spec.
Require Import thm1258497_spec.
Require Import thm1823_spec.
Lemma lem1259189 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1259190 (d''' : nat) (d'' : nat) : (term0 d''' d'') = (term1 d''' d'').
Proof. exact (@lem1259189 ((term2 d''' d'') = (NUMERAL 0))). Qed.
Lemma lem1259194 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem1246875 m n) (@lem1246874 m n)). Qed.
Lemma lem1259195 (d''' : nat) (d'' : nat) : (term2 d''' d'') = (term5 d''' d'').
Proof. exact (@lem1259194 d''' (Nat.add d'' d'')). Qed.
Lemma lem1259196 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1259197 (d''' : nat) (d'' : nat) : (term6 d''' d'') = (term7 d''' d'').
Proof. exact (MK_COMB (@lem1259196) (@lem1259195 d''' d'')). Qed.
Lemma lem1259198 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1259199 (d''' : nat) (d'' : nat) : ((term2 d''' d'') = (NUMERAL 0)) = ((term5 d''' d'') = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1259197 d''' d'') (@lem1259198)). Qed.
Lemma lem1259201 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem1246848 n (@lem1246847 n)). Qed.
Lemma lem1259202 (d''' : nat) (d'' : nat) : ((term5 d''' d'') = (NUMERAL 0)) = False.
Proof. exact (@lem1259201 (term8 d''' d'')). Qed.
Lemma lem1259203 (d''' : nat) (d'' : nat) : ((term2 d''' d'') = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem1259199 d''' d'') (@lem1259202 d''' d'')). Qed.
Lemma lem1259204 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1259205 (d''' : nat) (d'' : nat) : (term1 d''' d'') = (~ False).
Proof. exact (MK_COMB (@lem1259204) (@lem1259203 d''' d'')). Qed.
Lemma lem1259207 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1259208 (d''' : nat) (d'' : nat) : (term1 d''' d'') = True.
Proof. exact (TRANS (@lem1259205 d''' d'') (@lem1259207)). Qed.
Lemma lem1259209 (d''' : nat) (d'' : nat) : (term0 d''' d'') = True.
Proof. exact (TRANS (@lem1259190 d''' d'') (@lem1259208 d''' d'')). Qed.
Lemma lem1259210 (d''' : nat) (d'' : nat) : True = (term0 d''' d'').
Proof. exact (SYM (@lem1259209 d''' d'')). Qed.
Lemma lem1259211 (d''' : nat) (d'' : nat) : term0 d''' d''.
Proof. exact (EQ_MP (@lem1259210 d''' d'') (@lem0)). Qed.
Lemma lem1259212 (d''' : nat) (d'' : nat) (m : nat) (n : nat) (d' : nat) : term9 d''' d'' m n d'.
Proof. exact (EQ_MP (@lem1258497 d''' d'' m n d') (@lem1259211 d''' d'')). Qed.
