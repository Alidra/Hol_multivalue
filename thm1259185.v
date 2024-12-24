Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259185_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1246847_spec.
Require Import thm1246848_spec.
Require Import thm1823_spec.
Lemma lem1259173 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1259174 (d''' : nat) : (term0 d''') = (term1 d''').
Proof. exact (@lem1259173 ((S d''') = (NUMERAL 0))). Qed.
Lemma lem1259176 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem1246848 n (@lem1246847 n)). Qed.
Lemma lem1259177 (d''' : nat) : ((S d''') = (NUMERAL 0)) = False.
Proof. exact (@lem1259176 d'''). Qed.
Lemma lem1259178 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1259179 (d''' : nat) : (term1 d''') = (~ False).
Proof. exact (MK_COMB (@lem1259178) (@lem1259177 d''')). Qed.
Lemma lem1259181 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1259182 (d''' : nat) : (term1 d''') = True.
Proof. exact (TRANS (@lem1259179 d''') (@lem1259181)). Qed.
Lemma lem1259183 (d''' : nat) : (term0 d''') = True.
Proof. exact (TRANS (@lem1259174 d''') (@lem1259182 d''')). Qed.
Lemma lem1259184 (d''' : nat) : True = (term0 d''').
Proof. exact (SYM (@lem1259183 d''')). Qed.
Lemma lem1259185 (d''' : nat) : term0 d'''.
Proof. exact (EQ_MP (@lem1259184 d''') (@lem0)). Qed.
