Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm21816_term_abbrevs.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm1823_spec.
Lemma lem21798 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem21799 (a : Prop) : (term0 a) = (term1 a).
Proof. exact (@lem21798 (~ a)). Qed.
Lemma lem21801 (t : Prop) : (term1 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem21802 (a : Prop) : (term1 a) = a.
Proof. exact (@lem21801 a). Qed.
Lemma lem21803 (a : Prop) : (term0 a) = a.
Proof. exact (TRANS (@lem21799 a) (@lem21802 a)). Qed.
Lemma lem21804 (a : Prop) : (imp a) = (imp a).
Proof. exact (eq_refl (imp a)). Qed.
Lemma lem21805 (a : Prop) : (term2 a) = (a -> a).
Proof. exact (MK_COMB (@lem21804 a) (@lem21803 a)). Qed.
Lemma lem21807 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem21808 (a : Prop) : (a -> a) = True.
Proof. exact (@lem21807 a). Qed.
Lemma lem21809 (a : Prop) : (term2 a) = True.
Proof. exact (TRANS (@lem21805 a) (@lem21808 a)). Qed.
Lemma lem21810 (a : Prop) : True = (term2 a).
Proof. exact (SYM (@lem21809 a)). Qed.
Lemma lem21811 (a : Prop) : term2 a.
Proof. exact (EQ_MP (@lem21810 a) (@lem0)). Qed.
Lemma lem21816 : term3.
Proof. exact (fun a : Prop => @lem21811 a). Qed.
