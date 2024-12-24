Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259061_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1246847_spec.
Require Import thm1246848_spec.
Require Import thm1246867_spec.
Require Import thm1246868_spec.
Require Import thm1823_spec.
Lemma lem1259021 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1259022 (d'' : nat) (d' : nat) (d''' : nat) : (term0 d'' d' d''') = (term1 d'' d' d''').
Proof. exact (@lem1259021 ((term2 d'' d' d''') = (NUMERAL 0))). Qed.
Lemma lem1259026 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem1246868 m n) (@lem1246867 m n)). Qed.
Lemma lem1259027 (d' : nat) (d''' : nat) : (term3 d' d''') = (term4 d' d''').
Proof. exact (@lem1259026 d' d'''). Qed.
Lemma lem1259028 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1259029 (d' : nat) (d''' : nat) : (term5 d' d''') = (term6 d' d''').
Proof. exact (MK_COMB (@lem1259028 d') (@lem1259027 d' d''')). Qed.
Lemma lem1259031 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem1246868 m n) (@lem1246867 m n)). Qed.
Lemma lem1259032 (d' : nat) (d''' : nat) : (term6 d' d''') = (term7 d' d''').
Proof. exact (@lem1259031 d' (Nat.add d' d''')). Qed.
Lemma lem1259033 (d' : nat) (d''' : nat) : (term5 d' d''') = (term7 d' d''').
Proof. exact (TRANS (@lem1259029 d' d''') (@lem1259032 d' d''')). Qed.
Lemma lem1259034 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1259035 (d'' : nat) (d' : nat) (d''' : nat) : (term8 d'' d' d''') = (term9 d'' d' d''').
Proof. exact (MK_COMB (@lem1259034 d'') (@lem1259033 d' d''')). Qed.
Lemma lem1259037 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem1246868 m n) (@lem1246867 m n)). Qed.
Lemma lem1259038 (d'' : nat) (d' : nat) (d''' : nat) : (term9 d'' d' d''') = (term10 d'' d' d''').
Proof. exact (@lem1259037 d'' (term11 d' d''')). Qed.
Lemma lem1259039 (d'' : nat) (d' : nat) (d''' : nat) : (term8 d'' d' d''') = (term10 d'' d' d''').
Proof. exact (TRANS (@lem1259035 d'' d' d''') (@lem1259038 d'' d' d''')). Qed.
Lemma lem1259040 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1259041 (d'' : nat) (d' : nat) (d''' : nat) : (term2 d'' d' d''') = (term12 d'' d' d''').
Proof. exact (MK_COMB (@lem1259040 d'') (@lem1259039 d'' d' d''')). Qed.
Lemma lem1259043 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem1246868 m n) (@lem1246867 m n)). Qed.
Lemma lem1259044 (d'' : nat) (d' : nat) (d''' : nat) : (term12 d'' d' d''') = (term13 d'' d' d''').
Proof. exact (@lem1259043 d'' (term14 d'' d' d''')). Qed.
Lemma lem1259045 (d'' : nat) (d' : nat) (d''' : nat) : (term2 d'' d' d''') = (term13 d'' d' d''').
Proof. exact (TRANS (@lem1259041 d'' d' d''') (@lem1259044 d'' d' d''')). Qed.
Lemma lem1259046 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1259047 (d'' : nat) (d' : nat) (d''' : nat) : (term15 d'' d' d''') = (term16 d'' d' d''').
Proof. exact (MK_COMB (@lem1259046) (@lem1259045 d'' d' d''')). Qed.
Lemma lem1259048 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1259049 (d'' : nat) (d' : nat) (d''' : nat) : ((term2 d'' d' d''') = (NUMERAL 0)) = ((term13 d'' d' d''') = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1259047 d'' d' d''') (@lem1259048)). Qed.
Lemma lem1259051 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem1246848 n (@lem1246847 n)). Qed.
Lemma lem1259052 (d'' : nat) (d' : nat) (d''' : nat) : ((term13 d'' d' d''') = (NUMERAL 0)) = False.
Proof. exact (@lem1259051 (term17 d'' d' d''')). Qed.
Lemma lem1259053 (d'' : nat) (d' : nat) (d''' : nat) : ((term2 d'' d' d''') = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem1259049 d'' d' d''') (@lem1259052 d'' d' d''')). Qed.
Lemma lem1259054 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1259055 (d'' : nat) (d' : nat) (d''' : nat) : (term1 d'' d' d''') = (~ False).
Proof. exact (MK_COMB (@lem1259054) (@lem1259053 d'' d' d''')). Qed.
Lemma lem1259057 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1259058 (d'' : nat) (d' : nat) (d''' : nat) : (term1 d'' d' d''') = True.
Proof. exact (TRANS (@lem1259055 d'' d' d''') (@lem1259057)). Qed.
Lemma lem1259059 (d'' : nat) (d' : nat) (d''' : nat) : (term0 d'' d' d''') = True.
Proof. exact (TRANS (@lem1259022 d'' d' d''') (@lem1259058 d'' d' d''')). Qed.
Lemma lem1259060 (d'' : nat) (d' : nat) (d''' : nat) : True = (term0 d'' d' d''').
Proof. exact (SYM (@lem1259059 d'' d' d''')). Qed.
Lemma lem1259061 (d'' : nat) (d' : nat) (d''' : nat) : term0 d'' d' d'''.
Proof. exact (EQ_MP (@lem1259060 d'' d' d''') (@lem0)). Qed.
