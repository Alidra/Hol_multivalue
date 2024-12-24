Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import I_THM_term_abbrevs.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem15550 {A : Type'} : (@I A) = (term0 A).
Proof. exact (@I_def A). Qed.
Lemma lem15551 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem15552 {A : Type'} (x : A) : (@I A x) = (term1 A x).
Proof. exact (MK_COMB (@lem15550 A) (@lem15551 A x)). Qed.
Lemma lem15554 {A B : Type'} (f : A -> B) (y : A) : (term2 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem15555 {A : Type'} (f : A -> A) (y : A) : (term3 A f y) = (f y).
Proof. exact (@lem15554 A A f y). Qed.
Lemma lem15556 {A : Type'} (x : A) : (term4 A x) = (term1 A x).
Proof. exact (@lem15555 A (term0 A) x). Qed.
Lemma lem15557 {A : Type'} (x : A) : (term1 A x) = x.
Proof. exact (eq_refl (term1 A x)). Qed.
Lemma lem15558 {A : Type'} : (term5 A) = (term0 A).
Proof. exact (fun_ext (fun x : A => @lem15557 A x)). Qed.
Lemma lem15559 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem15560 {A : Type'} (x : A) : (term4 A x) = (term1 A x).
Proof. exact (MK_COMB (@lem15558 A) (@lem15559 A x)). Qed.
Lemma lem15561 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem15562 {A : Type'} (x : A) : (term6 A x) = (term7 A x).
Proof. exact (MK_COMB (@lem15561 A) (@lem15560 A x)). Qed.
Lemma lem15563 {A : Type'} (x : A) : (term1 A x) = x.
Proof. exact (eq_refl (term1 A x)). Qed.
Lemma lem15564 {A : Type'} (x : A) : ((term4 A x) = (term1 A x)) = ((term1 A x) = x).
Proof. exact (MK_COMB (@lem15562 A x) (@lem15563 A x)). Qed.
Lemma lem15565 {A : Type'} (x : A) : (term1 A x) = x.
Proof. exact (EQ_MP (@lem15564 A x) (@lem15556 A x)). Qed.
Lemma lem15566 {A : Type'} (x : A) : (@I A x) = x.
Proof. exact (TRANS (@lem15552 A x) (@lem15565 A x)). Qed.
Lemma lem15567 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem15568 {A : Type'} (x : A) : (term8 A x) = (@eq A x).
Proof. exact (MK_COMB (@lem15567 A) (@lem15566 A x)). Qed.
Lemma lem15569 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem15570 {A : Type'} (x : A) : ((@I A x) = x) = (x = x).
Proof. exact (MK_COMB (@lem15568 A x) (@lem15569 A x)). Qed.
Lemma lem15572 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem15573 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem15572 A x). Qed.
Lemma lem15574 {A : Type'} (x : A) : ((@I A x) = x) = True.
Proof. exact (TRANS (@lem15570 A x) (@lem15573 A x)). Qed.
Lemma lem15575 {A : Type'} : (term9 A) = (term10 A).
Proof. exact (fun_ext (fun x : A => @lem15574 A x)). Qed.
Lemma lem15576 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem15577 {A : Type'} : (term11 A) = (term12 A).
Proof. exact (MK_COMB (@lem15576 A) (@lem15575 A)). Qed.
Lemma lem15579 {A : Type'} (t : Prop) : (term13 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem15580 {A : Type'} (t : Prop) : (term13 A t) = t.
Proof. exact (@lem15579 A t). Qed.
Lemma lem15581 {A : Type'} : (term12 A) = True.
Proof. exact (@lem15580 A True). Qed.
Lemma lem15582 {A : Type'} : (term11 A) = True.
Proof. exact (TRANS (@lem15577 A) (@lem15581 A)). Qed.
Lemma lem15583 {A : Type'} : True = (term11 A).
Proof. exact (SYM (@lem15582 A)). Qed.
Lemma lem15584 {A : Type'} : term11 A.
Proof. exact (EQ_MP (@lem15583 A) (@lem0)). Qed.
