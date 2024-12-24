Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1386578_term_abbrevs.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm1823_spec.
Lemma lem1386563 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1386564 (p : Prop) : (term0 p) = (term1 p).
Proof. exact (@lem1386563 (~ p)). Qed.
Lemma lem1386566 (t : Prop) : (term1 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem1386567 (p : Prop) : (term1 p) = p.
Proof. exact (@lem1386566 p). Qed.
Lemma lem1386568 (p : Prop) : (term0 p) = p.
Proof. exact (TRANS (@lem1386564 p) (@lem1386567 p)). Qed.
Lemma lem1386569 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1386570 (p : Prop) : (term2 p) = (imp p).
Proof. exact (MK_COMB (@lem1386569) (@lem1386568 p)). Qed.
Lemma lem1386571 (p : Prop) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem1386572 (p : Prop) : (term3 p) = (p -> p).
Proof. exact (MK_COMB (@lem1386570 p) (@lem1386571 p)). Qed.
Lemma lem1386574 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem1386575 (p : Prop) : (p -> p) = True.
Proof. exact (@lem1386574 p). Qed.
Lemma lem1386576 (p : Prop) : (term3 p) = True.
Proof. exact (TRANS (@lem1386572 p) (@lem1386575 p)). Qed.
Lemma lem1386577 (p : Prop) : True = (term3 p).
Proof. exact (SYM (@lem1386576 p)). Qed.
Lemma lem1386578 (p : Prop) : term3 p.
Proof. exact (EQ_MP (@lem1386577 p) (@lem0)). Qed.
