Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1032627_term_abbrevs.
Require Import thm1823_spec.
Lemma lem1032613 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1032614 (p : Prop) : (p -> False) = (~ p).
Proof. exact (@lem1032613 p). Qed.
Lemma lem1032615 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1032616 (p : Prop) : (term0 p) = (term1 p).
Proof. exact (MK_COMB (@lem1032615) (@lem1032614 p)). Qed.
Lemma lem1032623 (p : Prop) (q : Prop) : (term2 p q) = (term2 p q).
Proof. exact (eq_refl (term2 p q)). Qed.
Lemma lem1032624 (p : Prop) (q : Prop) : (term3 p q) = (term4 p q).
Proof. exact (MK_COMB (@lem1032616 p) (@lem1032623 p q)). Qed.
Lemma lem1032627 (p : Prop) (q : Prop) : (term4 p q) = (term3 p q).
Proof. exact (SYM (@lem1032624 p q)). Qed.
