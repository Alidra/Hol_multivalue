Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIFF_UNIV_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1845_spec.
Require Import thm1857_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211701_spec.
Require Import thm3211702_spec.
Require Import thm3211724_spec.
Require Import thm3211725_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3269344 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3269345 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3269344 A s t). Qed.
Lemma lem3269346 {A : Type'} (s : A -> Prop) : ((@DIFF A s (@UNIV A)) = (@EMPTY A)) = (term1 A s).
Proof. exact (@lem3269345 A (@DIFF A s (@UNIV A)) (@EMPTY A)). Qed.
Lemma lem3269355 {A : Type'} : (term2 A) = (term3 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3269346 A s)). Qed.
Lemma lem3269356 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3269357 {A : Type'} : (term4 A) = (term5 A).
Proof. exact (MK_COMB (@lem3269356 A) (@lem3269355 A)). Qed.
Lemma lem3269362 {A : Type'} : (term5 A) = (term4 A).
Proof. exact (SYM (@lem3269357 A)). Qed.
Lemma lem3269374 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term6 A x s t) = (term7 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem3269375 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term6 A x s t) = (term7 A s x t).
Proof. exact (@lem3269374 A s x t). Qed.
Lemma lem3269376 {A : Type'} (s : A -> Prop) (x : A) : (term8 A x s) = (term9 A s x).
Proof. exact (@lem3269375 A s x (@UNIV A)). Qed.
Lemma lem3269380 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3269381 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3269380 A P x). Qed.
Lemma lem3269382 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3269381 A s x). Qed.
Lemma lem3269383 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3269384 {A : Type'} (s : A -> Prop) (x : A) : (term10 A x s) = (term11 A s x).
Proof. exact (MK_COMB (@lem3269383) (@lem3269382 A s x)). Qed.
Lemma lem3269386 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem3269387 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem3269386 A x). Qed.
Lemma lem3269388 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3269389 {A : Type'} (x : A) : (term12 A x) = (~ True).
Proof. exact (MK_COMB (@lem3269388) (@lem3269387 A x)). Qed.
Lemma lem3269391 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem3269392 {A : Type'} (x : A) : (term12 A x) = False.
Proof. exact (TRANS (@lem3269389 A x) (@lem3269391)). Qed.
Lemma lem3269393 {A : Type'} (s : A -> Prop) (x : A) : (term9 A s x) = (term13 A s x).
Proof. exact (MK_COMB (@lem3269384 A s x) (@lem3269392 A x)). Qed.
Lemma lem3269395 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem3269396 {A : Type'} (s : A -> Prop) (x : A) : (term13 A s x) = False.
Proof. exact (@lem3269395 (s x)). Qed.
Lemma lem3269397 {A : Type'} (s : A -> Prop) (x : A) : (term9 A s x) = False.
Proof. exact (TRANS (@lem3269393 A s x) (@lem3269396 A s x)). Qed.
Lemma lem3269398 {A : Type'} (x : A) (s : A -> Prop) : (term8 A x s) = False.
Proof. exact (TRANS (@lem3269376 A s x) (@lem3269397 A s x)). Qed.
Lemma lem3269399 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3269400 {A : Type'} (x : A) (s : A -> Prop) : (term14 A x s) = (@eq Prop False).
Proof. exact (MK_COMB (@lem3269399) (@lem3269398 A x s)). Qed.
Lemma lem3269402 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3269403 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3269402 A x). Qed.
Lemma lem3269404 {A : Type'} (s : A -> Prop) (x : A) : ((term8 A x s) = (@IN A x (@EMPTY A))) = (False = False).
Proof. exact (MK_COMB (@lem3269400 A x s) (@lem3269403 A x)). Qed.
Lemma lem3269406 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem3269407 : (False = False) = (~ False).
Proof. exact (@lem3269406 False). Qed.
Lemma lem3269409 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3269410 : (False = False) = True.
Proof. exact (TRANS (@lem3269407) (@lem3269409)). Qed.
Lemma lem3269411 {A : Type'} (s : A -> Prop) (x : A) : ((term8 A x s) = (@IN A x (@EMPTY A))) = True.
Proof. exact (TRANS (@lem3269404 A s x) (@lem3269410)). Qed.
Lemma lem3269412 {A : Type'} (s : A -> Prop) : (term15 A s) = (term16 A).
Proof. exact (fun_ext (fun x : A => @lem3269411 A s x)). Qed.
Lemma lem3269413 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3269414 {A : Type'} (s : A -> Prop) : (term1 A s) = (term17 A).
Proof. exact (MK_COMB (@lem3269413 A) (@lem3269412 A s)). Qed.
Lemma lem3269416 {A : Type'} (t : Prop) : (term18 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3269417 {A : Type'} (t : Prop) : (term18 A t) = t.
Proof. exact (@lem3269416 A t). Qed.
Lemma lem3269418 {A : Type'} : (term17 A) = True.
Proof. exact (@lem3269417 A True). Qed.
Lemma lem3269419 {A : Type'} (s : A -> Prop) : (term1 A s) = True.
Proof. exact (TRANS (@lem3269414 A s) (@lem3269418 A)). Qed.
Lemma lem3269420 {A : Type'} : (term3 A) = (term19 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3269419 A s)). Qed.
Lemma lem3269421 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3269422 {A : Type'} : (term5 A) = (term20 A).
Proof. exact (MK_COMB (@lem3269421 A) (@lem3269420 A)). Qed.
Lemma lem3269424 {A : Type'} (t : Prop) : (term18 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3269425 {A : Type'} (t : Prop) : (term21 A t) = t.
Proof. exact (@lem3269424 (A -> Prop) t). Qed.
Lemma lem3269426 {A : Type'} : (term20 A) = True.
Proof. exact (@lem3269425 A True). Qed.
Lemma lem3269427 {A : Type'} : (term5 A) = True.
Proof. exact (TRANS (@lem3269422 A) (@lem3269426 A)). Qed.
Lemma lem3269428 {A : Type'} : True = (term5 A).
Proof. exact (SYM (@lem3269427 A)). Qed.
Lemma lem3269429 {A : Type'} : term5 A.
Proof. exact (EQ_MP (@lem3269428 A) (@lem0)). Qed.
Lemma lem3269430 {A : Type'} : term4 A.
Proof. exact (EQ_MP (@lem3269362 A) (@lem3269429 A)). Qed.
