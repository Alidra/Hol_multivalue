Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259169_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1246847_spec.
Require Import thm1246848_spec.
Require Import thm1246867_spec.
Require Import thm1246868_spec.
Require Import thm1823_spec.
Lemma lem1259129 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1259130 (d'' : nat) (d' : nat) (d''' : nat) : (term0 d'' d' d''') = (term1 d'' d' d''').
Proof. exact (@lem1259129 ((term2 d'' d' d''') = (NUMERAL 0))). Qed.
Lemma lem1259134 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem1246868 m n) (@lem1246867 m n)). Qed.
Lemma lem1259135 (d' : nat) (d''' : nat) : (term3 d' d''') = (term4 d' d''').
Proof. exact (@lem1259134 d' d'''). Qed.
Lemma lem1259136 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1259137 (d' : nat) (d''' : nat) : (term5 d' d''') = (term6 d' d''').
Proof. exact (MK_COMB (@lem1259136 d') (@lem1259135 d' d''')). Qed.
Lemma lem1259139 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem1246868 m n) (@lem1246867 m n)). Qed.
Lemma lem1259140 (d' : nat) (d''' : nat) : (term6 d' d''') = (term7 d' d''').
Proof. exact (@lem1259139 d' (Nat.add d' d''')). Qed.
Lemma lem1259141 (d' : nat) (d''' : nat) : (term5 d' d''') = (term7 d' d''').
Proof. exact (TRANS (@lem1259137 d' d''') (@lem1259140 d' d''')). Qed.
Lemma lem1259142 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1259143 (d'' : nat) (d' : nat) (d''' : nat) : (term8 d'' d' d''') = (term9 d'' d' d''').
Proof. exact (MK_COMB (@lem1259142 d'') (@lem1259141 d' d''')). Qed.
Lemma lem1259145 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem1246868 m n) (@lem1246867 m n)). Qed.
Lemma lem1259146 (d'' : nat) (d' : nat) (d''' : nat) : (term9 d'' d' d''') = (term10 d'' d' d''').
Proof. exact (@lem1259145 d'' (term11 d' d''')). Qed.
Lemma lem1259147 (d'' : nat) (d' : nat) (d''' : nat) : (term8 d'' d' d''') = (term10 d'' d' d''').
Proof. exact (TRANS (@lem1259143 d'' d' d''') (@lem1259146 d'' d' d''')). Qed.
Lemma lem1259148 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1259149 (d'' : nat) (d' : nat) (d''' : nat) : (term2 d'' d' d''') = (term12 d'' d' d''').
Proof. exact (MK_COMB (@lem1259148 d'') (@lem1259147 d'' d' d''')). Qed.
Lemma lem1259151 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem1246868 m n) (@lem1246867 m n)). Qed.
Lemma lem1259152 (d'' : nat) (d' : nat) (d''' : nat) : (term12 d'' d' d''') = (term13 d'' d' d''').
Proof. exact (@lem1259151 d'' (term14 d'' d' d''')). Qed.
Lemma lem1259153 (d'' : nat) (d' : nat) (d''' : nat) : (term2 d'' d' d''') = (term13 d'' d' d''').
Proof. exact (TRANS (@lem1259149 d'' d' d''') (@lem1259152 d'' d' d''')). Qed.
Lemma lem1259154 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1259155 (d'' : nat) (d' : nat) (d''' : nat) : (term15 d'' d' d''') = (term16 d'' d' d''').
Proof. exact (MK_COMB (@lem1259154) (@lem1259153 d'' d' d''')). Qed.
Lemma lem1259156 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1259157 (d'' : nat) (d' : nat) (d''' : nat) : ((term2 d'' d' d''') = (NUMERAL 0)) = ((term13 d'' d' d''') = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1259155 d'' d' d''') (@lem1259156)). Qed.
Lemma lem1259159 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem1246848 n (@lem1246847 n)). Qed.
Lemma lem1259160 (d'' : nat) (d' : nat) (d''' : nat) : ((term13 d'' d' d''') = (NUMERAL 0)) = False.
Proof. exact (@lem1259159 (term17 d'' d' d''')). Qed.
Lemma lem1259161 (d'' : nat) (d' : nat) (d''' : nat) : ((term2 d'' d' d''') = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem1259157 d'' d' d''') (@lem1259160 d'' d' d''')). Qed.
Lemma lem1259162 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1259163 (d'' : nat) (d' : nat) (d''' : nat) : (term1 d'' d' d''') = (~ False).
Proof. exact (MK_COMB (@lem1259162) (@lem1259161 d'' d' d''')). Qed.
Lemma lem1259165 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1259166 (d'' : nat) (d' : nat) (d''' : nat) : (term1 d'' d' d''') = True.
Proof. exact (TRANS (@lem1259163 d'' d' d''') (@lem1259165)). Qed.
Lemma lem1259167 (d'' : nat) (d' : nat) (d''' : nat) : (term0 d'' d' d''') = True.
Proof. exact (TRANS (@lem1259130 d'' d' d''') (@lem1259166 d'' d' d''')). Qed.
Lemma lem1259168 (d'' : nat) (d' : nat) (d''' : nat) : True = (term0 d'' d' d''').
Proof. exact (SYM (@lem1259167 d'' d' d''')). Qed.
Lemma lem1259169 (d'' : nat) (d' : nat) (d''' : nat) : term0 d'' d' d'''.
Proof. exact (EQ_MP (@lem1259168 d'' d' d''') (@lem0)). Qed.
