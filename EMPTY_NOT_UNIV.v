Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EMPTY_NOT_UNIV_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1857_spec.
Require Import thm3211724_spec.
Require Import thm3211725_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3216444 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3216445 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3216444 A s t). Qed.
Lemma lem3216446 {A : Type'} : ((@EMPTY A) = (@UNIV A)) = (term1 A).
Proof. exact (@lem3216445 A (@EMPTY A) (@UNIV A)). Qed.
Lemma lem3216455 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3216456 {A : Type'} : (term2 A) = (term3 A).
Proof. exact (MK_COMB (@lem3216455) (@lem3216446 A)). Qed.
Lemma lem3216457 {A : Type'} : (term3 A) = (term2 A).
Proof. exact (SYM (@lem3216456 A)). Qed.
Lemma lem3216465 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3216466 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3216465 A x). Qed.
Lemma lem3216467 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3216468 {A : Type'} (x : A) : (term4 A x) = (@eq Prop False).
Proof. exact (MK_COMB (@lem3216467) (@lem3216466 A x)). Qed.
Lemma lem3216470 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem3216471 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem3216470 A x). Qed.
Lemma lem3216472 {A : Type'} (x : A) : ((@IN A x (@EMPTY A)) = (@IN A x (@UNIV A))) = (False = True).
Proof. exact (MK_COMB (@lem3216468 A x) (@lem3216471 A x)). Qed.
Lemma lem3216474 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem3216475 : (False = True) = (~ True).
Proof. exact (@lem3216474 True). Qed.
Lemma lem3216477 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem3216478 : (False = True) = False.
Proof. exact (TRANS (@lem3216475) (@lem3216477)). Qed.
Lemma lem3216479 {A : Type'} (x : A) : ((@IN A x (@EMPTY A)) = (@IN A x (@UNIV A))) = False.
Proof. exact (TRANS (@lem3216472 A x) (@lem3216478)). Qed.
Lemma lem3216480 {A : Type'} : (term5 A) = (term6 A).
Proof. exact (fun_ext (fun x : A => @lem3216479 A x)). Qed.
Lemma lem3216481 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3216482 {A : Type'} : (term1 A) = (term7 A).
Proof. exact (MK_COMB (@lem3216481 A) (@lem3216480 A)). Qed.
Lemma lem3216484 {A : Type'} (t : Prop) : (term8 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3216485 {A : Type'} (t : Prop) : (term8 A t) = t.
Proof. exact (@lem3216484 A t). Qed.
Lemma lem3216486 {A : Type'} : (term7 A) = False.
Proof. exact (@lem3216485 A False). Qed.
Lemma lem3216487 {A : Type'} : (term1 A) = False.
Proof. exact (TRANS (@lem3216482 A) (@lem3216486 A)). Qed.
Lemma lem3216488 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3216489 {A : Type'} : (term3 A) = (~ False).
Proof. exact (MK_COMB (@lem3216488) (@lem3216487 A)). Qed.
Lemma lem3216491 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3216492 {A : Type'} : (term3 A) = True.
Proof. exact (TRANS (@lem3216489 A) (@lem3216491)). Qed.
Lemma lem3216493 {A : Type'} : True = (term3 A).
Proof. exact (SYM (@lem3216492 A)). Qed.
Lemma lem3216494 {A : Type'} : term3 A.
Proof. exact (EQ_MP (@lem3216493 A) (@lem0)). Qed.
Lemma lem3216495 {A : Type'} : term2 A.
Proof. exact (EQ_MP (@lem3216457 A) (@lem3216494 A)). Qed.
