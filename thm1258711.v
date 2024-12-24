Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1258711_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1246847_spec.
Require Import thm1246848_spec.
Require Import thm1246867_spec.
Require Import thm1246868_spec.
Require Import thm1823_spec.
Lemma lem1258683 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1258684 (d'' : nat) (d''' : nat) : (term0 d'' d''') = (term1 d'' d''').
Proof. exact (@lem1258683 ((term2 d'' d''') = (NUMERAL 0))). Qed.
Lemma lem1258688 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem1246868 m n) (@lem1246867 m n)). Qed.
Lemma lem1258689 (d'' : nat) (d''' : nat) : (term3 d'' d''') = (term4 d'' d''').
Proof. exact (@lem1258688 d'' d'''). Qed.
Lemma lem1258690 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1258691 (d'' : nat) (d''' : nat) : (term2 d'' d''') = (term5 d'' d''').
Proof. exact (MK_COMB (@lem1258690 d'') (@lem1258689 d'' d''')). Qed.
Lemma lem1258693 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem1246868 m n) (@lem1246867 m n)). Qed.
Lemma lem1258694 (d'' : nat) (d''' : nat) : (term5 d'' d''') = (term6 d'' d''').
Proof. exact (@lem1258693 d'' (Nat.add d'' d''')). Qed.
Lemma lem1258695 (d'' : nat) (d''' : nat) : (term2 d'' d''') = (term6 d'' d''').
Proof. exact (TRANS (@lem1258691 d'' d''') (@lem1258694 d'' d''')). Qed.
Lemma lem1258696 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1258697 (d'' : nat) (d''' : nat) : (term7 d'' d''') = (term8 d'' d''').
Proof. exact (MK_COMB (@lem1258696) (@lem1258695 d'' d''')). Qed.
Lemma lem1258698 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1258699 (d'' : nat) (d''' : nat) : ((term2 d'' d''') = (NUMERAL 0)) = ((term6 d'' d''') = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1258697 d'' d''') (@lem1258698)). Qed.
Lemma lem1258701 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem1246848 n (@lem1246847 n)). Qed.
Lemma lem1258702 (d'' : nat) (d''' : nat) : ((term6 d'' d''') = (NUMERAL 0)) = False.
Proof. exact (@lem1258701 (term9 d'' d''')). Qed.
Lemma lem1258703 (d'' : nat) (d''' : nat) : ((term2 d'' d''') = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem1258699 d'' d''') (@lem1258702 d'' d''')). Qed.
Lemma lem1258704 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1258705 (d'' : nat) (d''' : nat) : (term1 d'' d''') = (~ False).
Proof. exact (MK_COMB (@lem1258704) (@lem1258703 d'' d''')). Qed.
Lemma lem1258707 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1258708 (d'' : nat) (d''' : nat) : (term1 d'' d''') = True.
Proof. exact (TRANS (@lem1258705 d'' d''') (@lem1258707)). Qed.
Lemma lem1258709 (d'' : nat) (d''' : nat) : (term0 d'' d''') = True.
Proof. exact (TRANS (@lem1258684 d'' d''') (@lem1258708 d'' d''')). Qed.
Lemma lem1258710 (d'' : nat) (d''' : nat) : True = (term0 d'' d''').
Proof. exact (SYM (@lem1258709 d'' d''')). Qed.
Lemma lem1258711 (d'' : nat) (d''' : nat) : term0 d'' d'''.
Proof. exact (EQ_MP (@lem1258710 d'' d''') (@lem0)). Qed.
