Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NOT_EXISTS_THM_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm1823_spec.
Require Import thm32_spec.
Require Import thm69_spec.
Require Import thm82_spec.
Lemma lem10599 {A : Type'} (P : A -> Prop) (h1 : term0 A P) : term0 A P.
Proof. exact (h1). Qed.
Lemma lem10600 {A : Type'} (P : A -> Prop) (h1 : term1 A P) : term1 A P.
Proof. exact (h1). Qed.
Lemma lem10601 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem10603 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem10604 {A : Type'} (P : A -> Prop) : (term2 A P) = (term3 A P).
Proof. exact (@lem10603 (term0 A P)). Qed.
Lemma lem10606 (t : Prop) : (term4 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem10607 {A : Type'} (P : A -> Prop) : (term3 A P) = (term5 A P).
Proof. exact (@lem10606 (term5 A P)). Qed.
Lemma lem10612 {A : Type'} (P : A -> Prop) : (term2 A P) = (term5 A P).
Proof. exact (TRANS (@lem10604 A P) (@lem10607 A P)). Qed.
Lemma lem10613 {A : Type'} (P : A -> Prop) : (term5 A P) = (term2 A P).
Proof. exact (SYM (@lem10612 A P)). Qed.
Lemma lem10614 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : term5 A P.
Proof. exact (ex_intro (term6 A P) x (@lem10601 A P x h1)). Qed.
Lemma lem10615 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : term2 A P.
Proof. exact (EQ_MP (@lem10613 A P) (@lem10614 A P x h1)). Qed.
Lemma lem10616 {A : Type'} (P : A -> Prop) (x : A) (h1 : term0 A P) (h2 : P x) : False.
Proof. exact (@lem10615 A P x h2 (@lem10599 A P h1)). Qed.
Lemma lem10617 {A : Type'} (x : A) (P : A -> Prop) (h1 : term0 A P) : term7 A P x.
Proof. exact (fun h0 : P x => @lem10616 A P x h1 h0). Qed.
Lemma lem10618 {A : Type'} (P : A -> Prop) (x : A) : (term7 A P x) = (term8 A P x).
Proof. exact (@lem69 (P x)). Qed.
Lemma lem10619 {A : Type'} (x : A) (P : A -> Prop) (h1 : term0 A P) : term8 A P x.
Proof. exact (EQ_MP (@lem10618 A P x) (@lem10617 A x P h1)). Qed.
Lemma lem10624 {A : Type'} (P : A -> Prop) (h1 : term0 A P) : term1 A P.
Proof. exact (fun x : A => @lem10619 A x P h1). Qed.
Lemma lem10625 {A : Type'} (P : A -> Prop) (h1 : term5 A P) : term5 A P.
Proof. exact (h1). Qed.
Lemma lem10626 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem10627 {A : Type'} (x : A) (P : A -> Prop) (h1 : term1 A P) : term9 A P x.
Proof. exact (@lem10600 A P h1 x). Qed.
Lemma lem10628 {A : Type'} (P : A -> Prop) (x : A) : (term9 A P x) = (term8 A P x).
Proof. exact (eq_refl (term9 A P x)). Qed.
Lemma lem10629 {A : Type'} (x : A) (P : A -> Prop) (h1 : term1 A P) : term8 A P x.
Proof. exact (EQ_MP (@lem10628 A P x) (@lem10627 A x P h1)). Qed.
Lemma lem10630 {A : Type'} (P : A -> Prop) (x : A) : term10 A P x.
Proof. exact (@lem82 (P x)). Qed.
Lemma lem10633 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem10634 {A : Type'} (P : A -> Prop) (x : A) : (term7 A P x) = (term8 A P x).
Proof. exact (@lem10633 (P x)). Qed.
Lemma lem10636 {A : Type'} (x : A) (P : A -> Prop) (h1 : term1 A P) : (P x) = False.
Proof. exact (@lem10630 A P x (@lem10629 A x P h1)). Qed.
Lemma lem10637 {A : Type'} (x : A) (P : A -> Prop) (h1 : term1 A P) : (P x) = False.
Proof. exact (@lem10636 A x P h1). Qed.
Lemma lem10638 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem10639 {A : Type'} (x : A) (P : A -> Prop) (h1 : term1 A P) : (term8 A P x) = (~ False).
Proof. exact (MK_COMB (@lem10638) (@lem10637 A x P h1)). Qed.
Lemma lem10641 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem10642 {A : Type'} (x : A) (P : A -> Prop) (h1 : term1 A P) : (term8 A P x) = True.
Proof. exact (TRANS (@lem10639 A x P h1) (@lem10641)). Qed.
Lemma lem10643 {A : Type'} (x : A) (P : A -> Prop) (h1 : term1 A P) : (term7 A P x) = True.
Proof. exact (TRANS (@lem10634 A P x) (@lem10642 A x P h1)). Qed.
Lemma lem10644 {A : Type'} (x : A) (P : A -> Prop) (h1 : term1 A P) : True = (term7 A P x).
Proof. exact (SYM (@lem10643 A x P h1)). Qed.
Lemma lem10645 {A : Type'} (x : A) (P : A -> Prop) (h1 : term1 A P) : term7 A P x.
Proof. exact (EQ_MP (@lem10644 A x P h1) (@lem0)). Qed.
Lemma lem10646 {A : Type'} (P : A -> Prop) (x : A) (h1 : term1 A P) (h2 : P x) : False.
Proof. exact (@lem10645 A x P h1 (@lem10626 A P x h2)). Qed.
Lemma lem10647 {A : Type'} (P : A -> Prop) (h1 : term1 A P) (h2 : term5 A P) : False.
Proof. exact (ex_elim (@lem10625 A P h2) (fun x : A => fun h0 : term6 A P x => @lem10646 A P x h1 h0)). Qed.
Lemma lem10648 {A : Type'} (P : A -> Prop) (h1 : term1 A P) : term11 A P.
Proof. exact (fun h0 : term5 A P => @lem10647 A P h1 h0). Qed.
Lemma lem10649 {A : Type'} (P : A -> Prop) : (term11 A P) = (term0 A P).
Proof. exact (@lem69 (term5 A P)). Qed.
Lemma lem10650 {A : Type'} (P : A -> Prop) (h1 : term1 A P) : term0 A P.
Proof. exact (EQ_MP (@lem10649 A P) (@lem10648 A P h1)). Qed.
Lemma lem10651 {A : Type'} (P : A -> Prop) : term12 A P.
Proof. exact (fun h0 : term1 A P => @lem10650 A P h0). Qed.
Lemma lem10652 {A : Type'} (P : A -> Prop) : term13 A P.
Proof. exact (fun h0 : term0 A P => @lem10624 A P h0). Qed.
Lemma lem10653 {A : Type'} (P : A -> Prop) : term14 A P.
Proof. exact (conj (@lem10652 A P) (@lem10651 A P)). Qed.
Lemma lem10654 {A : Type'} (P : A -> Prop) : (term14 A P) = ((term0 A P) = (term1 A P)).
Proof. exact (@lem32 (term0 A P) (term1 A P)). Qed.
Lemma lem10655 {A : Type'} (P : A -> Prop) : (term0 A P) = (term1 A P).
Proof. exact (EQ_MP (@lem10654 A P) (@lem10653 A P)). Qed.
Lemma lem10660 {A : Type'} : term15 A.
Proof. exact (fun P : A -> Prop => @lem10655 A P). Qed.
