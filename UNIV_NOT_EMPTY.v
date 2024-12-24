Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import UNIV_NOT_EMPTY_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1855_spec.
Require Import thm3211724_spec.
Require Import thm3211725_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3216382 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3216383 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3216382 A s t). Qed.
Lemma lem3216384 {A : Type'} : ((@UNIV A) = (@EMPTY A)) = (term1 A).
Proof. exact (@lem3216383 A (@UNIV A) (@EMPTY A)). Qed.
Lemma lem3216393 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3216394 {A : Type'} : (term2 A) = (term3 A).
Proof. exact (MK_COMB (@lem3216393) (@lem3216384 A)). Qed.
Lemma lem3216395 {A : Type'} : (term3 A) = (term2 A).
Proof. exact (SYM (@lem3216394 A)). Qed.
Lemma lem3216403 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem3216404 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem3216403 A x). Qed.
Lemma lem3216405 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3216406 {A : Type'} (x : A) : (term4 A x) = (@eq Prop True).
Proof. exact (MK_COMB (@lem3216405) (@lem3216404 A x)). Qed.
Lemma lem3216408 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3216409 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3216408 A x). Qed.
Lemma lem3216410 {A : Type'} (x : A) : ((@IN A x (@UNIV A)) = (@IN A x (@EMPTY A))) = (True = False).
Proof. exact (MK_COMB (@lem3216406 A x) (@lem3216409 A x)). Qed.
Lemma lem3216412 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem3216413 : (True = False) = False.
Proof. exact (@lem3216412 False). Qed.
Lemma lem3216414 {A : Type'} (x : A) : ((@IN A x (@UNIV A)) = (@IN A x (@EMPTY A))) = False.
Proof. exact (TRANS (@lem3216410 A x) (@lem3216413)). Qed.
Lemma lem3216415 {A : Type'} : (term5 A) = (term6 A).
Proof. exact (fun_ext (fun x : A => @lem3216414 A x)). Qed.
Lemma lem3216416 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3216417 {A : Type'} : (term1 A) = (term7 A).
Proof. exact (MK_COMB (@lem3216416 A) (@lem3216415 A)). Qed.
Lemma lem3216419 {A : Type'} (t : Prop) : (term8 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3216420 {A : Type'} (t : Prop) : (term8 A t) = t.
Proof. exact (@lem3216419 A t). Qed.
Lemma lem3216421 {A : Type'} : (term7 A) = False.
Proof. exact (@lem3216420 A False). Qed.
Lemma lem3216422 {A : Type'} : (term1 A) = False.
Proof. exact (TRANS (@lem3216417 A) (@lem3216421 A)). Qed.
Lemma lem3216423 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3216424 {A : Type'} : (term3 A) = (~ False).
Proof. exact (MK_COMB (@lem3216423) (@lem3216422 A)). Qed.
Lemma lem3216426 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3216427 {A : Type'} : (term3 A) = True.
Proof. exact (TRANS (@lem3216424 A) (@lem3216426)). Qed.
Lemma lem3216428 {A : Type'} : True = (term3 A).
Proof. exact (SYM (@lem3216427 A)). Qed.
Lemma lem3216429 {A : Type'} : term3 A.
Proof. exact (EQ_MP (@lem3216428 A) (@lem0)). Qed.
Lemma lem3216430 {A : Type'} : term2 A.
Proof. exact (EQ_MP (@lem3216395 A) (@lem3216429 A)). Qed.
