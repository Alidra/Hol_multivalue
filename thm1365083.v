Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm1856_spec.
Lemma lem1365076 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem1365077 : ((True /\ True) = True) = (True /\ True).
Proof. exact (@lem1365076 (True /\ True)). Qed.
Lemma lem1365079 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1365080 : (True /\ True) = True.
Proof. exact (@lem1365079 True). Qed.
Lemma lem1365081 : ((True /\ True) = True) = True.
Proof. exact (TRANS (@lem1365077) (@lem1365080)). Qed.
Lemma lem1365082 : True = ((True /\ True) = True).
Proof. exact (SYM (@lem1365081)). Qed.
Lemma lem1365083 : (True /\ True) = True.
Proof. exact (EQ_MP (@lem1365082) (@lem0)). Qed.
