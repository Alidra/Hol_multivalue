Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm21179_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm1823_spec.
Require Import thm1857_spec.
Require Import thm21151_spec.
Lemma lem21162 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem21163 : (term0 = False) = term1.
Proof. exact (@lem21162 term0). Qed.
Lemma lem21165 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem21166 : term0 = term2.
Proof. exact (@lem21165 (~ False)). Qed.
Lemma lem21168 (t : Prop) : (term3 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem21169 : term2 = False.
Proof. exact (@lem21168 False). Qed.
Lemma lem21170 : term0 = False.
Proof. exact (TRANS (@lem21166) (@lem21169)). Qed.
Lemma lem21171 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem21172 : term1 = (~ False).
Proof. exact (MK_COMB (@lem21171) (@lem21170)). Qed.
Lemma lem21174 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem21175 : term1 = True.
Proof. exact (TRANS (@lem21172) (@lem21174)). Qed.
Lemma lem21176 : (term0 = False) = True.
Proof. exact (TRANS (@lem21163) (@lem21175)). Qed.
Lemma lem21177 : True = (term0 = False).
Proof. exact (SYM (@lem21176)). Qed.
Lemma lem21178 : term0 = False.
Proof. exact (EQ_MP (@lem21177) (@lem0)). Qed.
Lemma lem21179 (p : Prop) (h1 : p = False) : (term4 p) = p.
Proof. exact (EQ_MP (@lem21151 p h1) (@lem21178)). Qed.
