Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INSERT_UNIV_term_abbrevs.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1832_spec.
Require Import thm1855_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211724_spec.
Require Import thm3211725_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3278354 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3278355 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3278354 A s t). Qed.
Lemma lem3278356 {A : Type'} (x : A) : ((@INSERT A x (@UNIV A)) = (@UNIV A)) = (term1 A x).
Proof. exact (@lem3278355 A (@INSERT A x (@UNIV A)) (@UNIV A)). Qed.
Lemma lem3278365 {A : Type'} : (term2 A) = (term3 A).
Proof. exact (fun_ext (fun x : A => @lem3278356 A x)). Qed.
Lemma lem3278366 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3278367 {A : Type'} : (term4 A) = (term5 A).
Proof. exact (MK_COMB (@lem3278366 A) (@lem3278365 A)). Qed.
Lemma lem3278372 {A : Type'} : (term5 A) = (term4 A).
Proof. exact (SYM (@lem3278367 A)). Qed.
Lemma lem3278384 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term6 A x y s) = (term7 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3278385 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term6 A x y s) = (term7 A y x s).
Proof. exact (@lem3278384 A y x s). Qed.
Lemma lem3278386 {A : Type'} (x : A) (x' : A) : (term8 A x' x) = (term9 A x x').
Proof. exact (@lem3278385 A x x' (@UNIV A)). Qed.
Lemma lem3278392 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem3278393 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem3278392 A x). Qed.
Lemma lem3278394 {A : Type'} (x' : A) : (@IN A x' (@UNIV A)) = True.
Proof. exact (@lem3278393 A x'). Qed.
Lemma lem3278395 {A : Type'} (x' : A) (x : A) : (term10 A x' x) = (term10 A x' x).
Proof. exact (eq_refl (term10 A x' x)). Qed.
Lemma lem3278396 {A : Type'} (x' : A) (x : A) : (term9 A x x') = (term11 A x' x).
Proof. exact (MK_COMB (@lem3278395 A x' x) (@lem3278394 A x')). Qed.
Lemma lem3278398 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem3278399 {A : Type'} (x' : A) (x : A) : (term11 A x' x) = True.
Proof. exact (@lem3278398 (x' = x)). Qed.
Lemma lem3278400 {A : Type'} (x : A) (x' : A) : (term9 A x x') = True.
Proof. exact (TRANS (@lem3278396 A x' x) (@lem3278399 A x' x)). Qed.
Lemma lem3278401 {A : Type'} (x' : A) (x : A) : (term8 A x' x) = True.
Proof. exact (TRANS (@lem3278386 A x x') (@lem3278400 A x x')). Qed.
Lemma lem3278402 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3278403 {A : Type'} (x' : A) (x : A) : (term12 A x' x) = (@eq Prop True).
Proof. exact (MK_COMB (@lem3278402) (@lem3278401 A x' x)). Qed.
Lemma lem3278405 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem3278406 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem3278405 A x). Qed.
Lemma lem3278407 {A : Type'} (x' : A) : (@IN A x' (@UNIV A)) = True.
Proof. exact (@lem3278406 A x'). Qed.
Lemma lem3278408 {A : Type'} (x : A) (x' : A) : ((term8 A x' x) = (@IN A x' (@UNIV A))) = (True = True).
Proof. exact (MK_COMB (@lem3278403 A x' x) (@lem3278407 A x')). Qed.
Lemma lem3278410 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem3278411 : (True = True) = True.
Proof. exact (@lem3278410 True). Qed.
Lemma lem3278412 {A : Type'} (x : A) (x' : A) : ((term8 A x' x) = (@IN A x' (@UNIV A))) = True.
Proof. exact (TRANS (@lem3278408 A x x') (@lem3278411)). Qed.
Lemma lem3278413 {A : Type'} (x : A) : (term13 A x) = (term14 A).
Proof. exact (fun_ext (fun x' : A => @lem3278412 A x x')). Qed.
Lemma lem3278414 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3278415 {A : Type'} (x : A) : (term1 A x) = (term15 A).
Proof. exact (MK_COMB (@lem3278414 A) (@lem3278413 A x)). Qed.
Lemma lem3278417 {A : Type'} (t : Prop) : (term16 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3278418 {A : Type'} (t : Prop) : (term16 A t) = t.
Proof. exact (@lem3278417 A t). Qed.
Lemma lem3278419 {A : Type'} : (term15 A) = True.
Proof. exact (@lem3278418 A True). Qed.
Lemma lem3278420 {A : Type'} (x : A) : (term1 A x) = True.
Proof. exact (TRANS (@lem3278415 A x) (@lem3278419 A)). Qed.
Lemma lem3278421 {A : Type'} : (term3 A) = (term14 A).
Proof. exact (fun_ext (fun x : A => @lem3278420 A x)). Qed.
Lemma lem3278422 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3278423 {A : Type'} : (term5 A) = (term15 A).
Proof. exact (MK_COMB (@lem3278422 A) (@lem3278421 A)). Qed.
Lemma lem3278425 {A : Type'} (t : Prop) : (term16 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3278426 {A : Type'} (t : Prop) : (term16 A t) = t.
Proof. exact (@lem3278425 A t). Qed.
Lemma lem3278427 {A : Type'} : (term15 A) = True.
Proof. exact (@lem3278426 A True). Qed.
Lemma lem3278428 {A : Type'} : (term5 A) = True.
Proof. exact (TRANS (@lem3278423 A) (@lem3278427 A)). Qed.
Lemma lem3278429 {A : Type'} : True = (term5 A).
Proof. exact (SYM (@lem3278428 A)). Qed.
Lemma lem3278430 {A : Type'} : term5 A.
Proof. exact (EQ_MP (@lem3278429 A) (@lem0)). Qed.
Lemma lem3278431 {A : Type'} : term4 A.
Proof. exact (EQ_MP (@lem3278372 A) (@lem3278430 A)). Qed.
