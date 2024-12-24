Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3354697_term_abbrevs.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1822_spec.
Require Import thm1855_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211668_spec.
Require Import thm3211669_spec.
Require Import thm3211724_spec.
Require Import thm3211725_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Lemma lem3354645 {A : Type'} (s : type686 A) (x : A) : (term0 A x s) = (term1 A s x).
Proof. exact (EQ_MP (@lem3211669 A s x) (@lem3211668 A s x)). Qed.
Lemma lem3354646 {A : Type'} (s : type686 A) (x : A) : (term0 A x s) = (term1 A s x).
Proof. exact (@lem3354645 A s x). Qed.
Lemma lem3354647 {A : Type'} (x : A) : (term2 A x) = (term3 A x).
Proof. exact (@lem3354646 A (@EMPTY (A -> Prop)) x). Qed.
Lemma lem3354655 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3354656 {A : Type'} (x : A -> Prop) : (@IN (A -> Prop) x (@EMPTY (A -> Prop))) = False.
Proof. exact (@lem3354655 (A -> Prop) x). Qed.
Lemma lem3354657 {A : Type'} (t : A -> Prop) : (@IN (A -> Prop) t (@EMPTY (A -> Prop))) = False.
Proof. exact (@lem3354656 A t). Qed.
Lemma lem3354658 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3354659 {A : Type'} (t : A -> Prop) : (term4 A t) = (imp False).
Proof. exact (MK_COMB (@lem3354658) (@lem3354657 A t)). Qed.
Lemma lem3354661 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3354662 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3354661 A P x). Qed.
Lemma lem3354663 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3354662 A t x). Qed.
Lemma lem3354664 {A : Type'} (t : A -> Prop) (x : A) : (term5 A x t) = (term6 A t x).
Proof. exact (MK_COMB (@lem3354659 A t) (@lem3354663 A t x)). Qed.
Lemma lem3354666 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem3354667 {A : Type'} (t : A -> Prop) (x : A) : (term6 A t x) = True.
Proof. exact (@lem3354666 (t x)). Qed.
Lemma lem3354668 {A : Type'} (x : A) (t : A -> Prop) : (term5 A x t) = True.
Proof. exact (TRANS (@lem3354664 A t x) (@lem3354667 A t x)). Qed.
Lemma lem3354669 {A : Type'} (x : A) : (term7 A x) = (term8 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3354668 A x t)). Qed.
Lemma lem3354670 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3354671 {A : Type'} (x : A) : (term3 A x) = (term9 A).
Proof. exact (MK_COMB (@lem3354670 A) (@lem3354669 A x)). Qed.
Lemma lem3354673 {A : Type'} (t : Prop) : (term10 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3354674 {A : Type'} (t : Prop) : (term11 A t) = t.
Proof. exact (@lem3354673 (A -> Prop) t). Qed.
Lemma lem3354675 {A : Type'} : (term9 A) = True.
Proof. exact (@lem3354674 A True). Qed.
Lemma lem3354676 {A : Type'} (x : A) : (term3 A x) = True.
Proof. exact (TRANS (@lem3354671 A x) (@lem3354675 A)). Qed.
Lemma lem3354677 {A : Type'} (x : A) : (term2 A x) = True.
Proof. exact (TRANS (@lem3354647 A x) (@lem3354676 A x)). Qed.
Lemma lem3354678 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3354679 {A : Type'} (x : A) : (term12 A x) = (@eq Prop True).
Proof. exact (MK_COMB (@lem3354678) (@lem3354677 A x)). Qed.
Lemma lem3354681 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem3354682 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem3354681 A x). Qed.
Lemma lem3354683 {A : Type'} (x : A) : ((term2 A x) = (@IN A x (@UNIV A))) = (True = True).
Proof. exact (MK_COMB (@lem3354679 A x) (@lem3354682 A x)). Qed.
Lemma lem3354685 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem3354686 : (True = True) = True.
Proof. exact (@lem3354685 True). Qed.
Lemma lem3354687 {A : Type'} (x : A) : ((term2 A x) = (@IN A x (@UNIV A))) = True.
Proof. exact (TRANS (@lem3354683 A x) (@lem3354686)). Qed.
Lemma lem3354688 {A : Type'} : (term13 A) = (term14 A).
Proof. exact (fun_ext (fun x : A => @lem3354687 A x)). Qed.
Lemma lem3354689 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3354690 {A : Type'} : (term15 A) = (term16 A).
Proof. exact (MK_COMB (@lem3354689 A) (@lem3354688 A)). Qed.
Lemma lem3354692 {A : Type'} (t : Prop) : (term10 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3354693 {A : Type'} (t : Prop) : (term10 A t) = t.
Proof. exact (@lem3354692 A t). Qed.
Lemma lem3354694 {A : Type'} : (term16 A) = True.
Proof. exact (@lem3354693 A True). Qed.
Lemma lem3354695 {A : Type'} : (term15 A) = True.
Proof. exact (TRANS (@lem3354690 A) (@lem3354694 A)). Qed.
Lemma lem3354696 {A : Type'} : True = (term15 A).
Proof. exact (SYM (@lem3354695 A)). Qed.
Lemma lem3354697 {A : Type'} : term15 A.
Proof. exact (EQ_MP (@lem3354696 A) (@lem0)). Qed.
