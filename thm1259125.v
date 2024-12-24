Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259125_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1246847_spec.
Require Import thm1246848_spec.
Require Import thm1246867_spec.
Require Import thm1246868_spec.
Require Import thm1823_spec.
Lemma lem1259097 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1259098 (d' : nat) (d''' : nat) : (term0 d' d''') = (term1 d' d''').
Proof. exact (@lem1259097 ((term2 d' d''') = (NUMERAL 0))). Qed.
Lemma lem1259102 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem1246868 m n) (@lem1246867 m n)). Qed.
Lemma lem1259103 (d' : nat) (d''' : nat) : (term3 d' d''') = (term4 d' d''').
Proof. exact (@lem1259102 d' d'''). Qed.
Lemma lem1259104 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1259105 (d' : nat) (d''' : nat) : (term2 d' d''') = (term5 d' d''').
Proof. exact (MK_COMB (@lem1259104 d') (@lem1259103 d' d''')). Qed.
Lemma lem1259107 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem1246868 m n) (@lem1246867 m n)). Qed.
Lemma lem1259108 (d' : nat) (d''' : nat) : (term5 d' d''') = (term6 d' d''').
Proof. exact (@lem1259107 d' (Nat.add d' d''')). Qed.
Lemma lem1259109 (d' : nat) (d''' : nat) : (term2 d' d''') = (term6 d' d''').
Proof. exact (TRANS (@lem1259105 d' d''') (@lem1259108 d' d''')). Qed.
Lemma lem1259110 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1259111 (d' : nat) (d''' : nat) : (term7 d' d''') = (term8 d' d''').
Proof. exact (MK_COMB (@lem1259110) (@lem1259109 d' d''')). Qed.
Lemma lem1259112 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1259113 (d' : nat) (d''' : nat) : ((term2 d' d''') = (NUMERAL 0)) = ((term6 d' d''') = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1259111 d' d''') (@lem1259112)). Qed.
Lemma lem1259115 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem1246848 n (@lem1246847 n)). Qed.
Lemma lem1259116 (d' : nat) (d''' : nat) : ((term6 d' d''') = (NUMERAL 0)) = False.
Proof. exact (@lem1259115 (term9 d' d''')). Qed.
Lemma lem1259117 (d' : nat) (d''' : nat) : ((term2 d' d''') = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem1259113 d' d''') (@lem1259116 d' d''')). Qed.
Lemma lem1259118 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1259119 (d' : nat) (d''' : nat) : (term1 d' d''') = (~ False).
Proof. exact (MK_COMB (@lem1259118) (@lem1259117 d' d''')). Qed.
Lemma lem1259121 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1259122 (d' : nat) (d''' : nat) : (term1 d' d''') = True.
Proof. exact (TRANS (@lem1259119 d' d''') (@lem1259121)). Qed.
Lemma lem1259123 (d' : nat) (d''' : nat) : (term0 d' d''') = True.
Proof. exact (TRANS (@lem1259098 d' d''') (@lem1259122 d' d''')). Qed.
Lemma lem1259124 (d' : nat) (d''' : nat) : True = (term0 d' d''').
Proof. exact (SYM (@lem1259123 d' d''')). Qed.
Lemma lem1259125 (d' : nat) (d''' : nat) : term0 d' d'''.
Proof. exact (EQ_MP (@lem1259124 d' d''') (@lem0)). Qed.
