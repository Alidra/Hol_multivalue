Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1365073_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm1842_spec.
Require Import thm1857_spec.
Lemma lem1365062 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem1365063 : ((True /\ False) = False) = term0.
Proof. exact (@lem1365062 (True /\ False)). Qed.
Lemma lem1365065 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1365066 : (True /\ False) = False.
Proof. exact (@lem1365065 False). Qed.
Lemma lem1365067 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1365068 : term0 = (~ False).
Proof. exact (MK_COMB (@lem1365067) (@lem1365066)). Qed.
Lemma lem1365070 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1365071 : term0 = True.
Proof. exact (TRANS (@lem1365068) (@lem1365070)). Qed.
Lemma lem1365072 : ((True /\ False) = False) = True.
Proof. exact (TRANS (@lem1365063) (@lem1365071)). Qed.
Lemma lem1365073 : True = ((True /\ False) = False).
Proof. exact (SYM (@lem1365072)). Qed.
