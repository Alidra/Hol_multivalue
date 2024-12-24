Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259093_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1246847_spec.
Require Import thm1246848_spec.
Require Import thm1246867_spec.
Require Import thm1246868_spec.
Require Import thm1823_spec.
Lemma lem1259065 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1259066 (d' : nat) (d''' : nat) : (term0 d' d''') = (term1 d' d''').
Proof. exact (@lem1259065 ((term2 d' d''') = (NUMERAL 0))). Qed.
Lemma lem1259070 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem1246868 m n) (@lem1246867 m n)). Qed.
Lemma lem1259071 (d' : nat) (d''' : nat) : (term3 d' d''') = (term4 d' d''').
Proof. exact (@lem1259070 d' d'''). Qed.
Lemma lem1259072 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1259073 (d' : nat) (d''' : nat) : (term2 d' d''') = (term5 d' d''').
Proof. exact (MK_COMB (@lem1259072 d') (@lem1259071 d' d''')). Qed.
Lemma lem1259075 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem1246868 m n) (@lem1246867 m n)). Qed.
Lemma lem1259076 (d' : nat) (d''' : nat) : (term5 d' d''') = (term6 d' d''').
Proof. exact (@lem1259075 d' (Nat.add d' d''')). Qed.
Lemma lem1259077 (d' : nat) (d''' : nat) : (term2 d' d''') = (term6 d' d''').
Proof. exact (TRANS (@lem1259073 d' d''') (@lem1259076 d' d''')). Qed.
Lemma lem1259078 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1259079 (d' : nat) (d''' : nat) : (term7 d' d''') = (term8 d' d''').
Proof. exact (MK_COMB (@lem1259078) (@lem1259077 d' d''')). Qed.
Lemma lem1259080 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1259081 (d' : nat) (d''' : nat) : ((term2 d' d''') = (NUMERAL 0)) = ((term6 d' d''') = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1259079 d' d''') (@lem1259080)). Qed.
Lemma lem1259083 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem1246848 n (@lem1246847 n)). Qed.
Lemma lem1259084 (d' : nat) (d''' : nat) : ((term6 d' d''') = (NUMERAL 0)) = False.
Proof. exact (@lem1259083 (term9 d' d''')). Qed.
Lemma lem1259085 (d' : nat) (d''' : nat) : ((term2 d' d''') = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem1259081 d' d''') (@lem1259084 d' d''')). Qed.
Lemma lem1259086 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1259087 (d' : nat) (d''' : nat) : (term1 d' d''') = (~ False).
Proof. exact (MK_COMB (@lem1259086) (@lem1259085 d' d''')). Qed.
Lemma lem1259089 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1259090 (d' : nat) (d''' : nat) : (term1 d' d''') = True.
Proof. exact (TRANS (@lem1259087 d' d''') (@lem1259089)). Qed.
Lemma lem1259091 (d' : nat) (d''' : nat) : (term0 d' d''') = True.
Proof. exact (TRANS (@lem1259066 d' d''') (@lem1259090 d' d''')). Qed.
Lemma lem1259092 (d' : nat) (d''' : nat) : True = (term0 d' d''').
Proof. exact (SYM (@lem1259091 d' d''')). Qed.
Lemma lem1259093 (d' : nat) (d''' : nat) : term0 d' d'''.
Proof. exact (EQ_MP (@lem1259092 d' d''') (@lem0)). Qed.
