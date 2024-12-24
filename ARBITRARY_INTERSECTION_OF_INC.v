Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ARBITRARY_INTERSECTION_OF_INC_term_abbrevs.
Require Import ARBITRARY_spec.
Require Import INTERSECTION_OF_INC_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem4858425 {A : Type'} (s : type686 A) : term0 A s.
Proof. exact (@lem4853019 A s). Qed.
Lemma lem4858426 {A : Type'} (s : type686 A) : (term0 A s) = ((@ARBITRARY A s) = True).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem4858428 {A : Type'} (P : type180 A) : term1 A P.
Proof. exact (@lem4842609 A P). Qed.
Lemma lem4858429 {A : Type'} (P : type180 A) : (term1 A P) = (term2 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem4858430 {A : Type'} (P : type180 A) : term2 A P.
Proof. exact (EQ_MP (@lem4858429 A P) (@lem4858428 A P)). Qed.
Lemma lem4858431 {A : Type'} (P : type180 A) (Q : type686 A) : term3 A P Q.
Proof. exact (@lem4858430 A P Q). Qed.
Lemma lem4858432 {A : Type'} (P : type180 A) (Q : type686 A) : (term3 A P Q) = (term4 A P Q).
Proof. exact (eq_refl (term3 A P Q)). Qed.
Lemma lem4858433 {A : Type'} (P : type180 A) (Q : type686 A) : term4 A P Q.
Proof. exact (EQ_MP (@lem4858432 A P Q) (@lem4858431 A P Q)). Qed.
Lemma lem4858434 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : term5 A P Q s.
Proof. exact (@lem4858433 A P Q s). Qed.
Lemma lem4858435 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term5 A P Q s) = (term6 A P Q s).
Proof. exact (eq_refl (term5 A P Q s)). Qed.
Lemma lem4858436 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : term6 A P Q s.
Proof. exact (EQ_MP (@lem4858435 A P Q s) (@lem4858434 A P Q s)). Qed.
Lemma lem4858437 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) (h1 : term7 A P Q s) : term7 A P Q s.
Proof. exact (h1). Qed.
Lemma lem4858438 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) (h1 : term7 A P Q s) : @INTERSECTION_OF A P Q s.
Proof. exact (@lem4858436 A P Q s (@lem4858437 A P Q s h1)). Qed.
Lemma lem4858439 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (@INTERSECTION_OF A P Q s) = ((@INTERSECTION_OF A P Q s) = True).
Proof. exact (@lem7 (@INTERSECTION_OF A P Q s)). Qed.
Lemma lem4858440 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) (h1 : term7 A P Q s) : (@INTERSECTION_OF A P Q s) = True.
Proof. exact (EQ_MP (@lem4858439 A P Q s) (@lem4858438 A P Q s h1)). Qed.
Lemma lem4858457 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term8 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4858458 (p : Prop) (q : Prop) (p' : Prop) : term9 p q p'.
Proof. exact (fun q' : Prop => @lem4858457 p q p' q'). Qed.
Lemma lem4858459 (p : Prop) (q : Prop) : term10 p q.
Proof. exact (fun p' : Prop => @lem4858458 p q p'). Qed.
Lemma lem4858460 {A : Type'} (P : type686 A) (s : A -> Prop) : term11 A P s.
Proof. exact (@lem4858459 (P s) (@INTERSECTION_OF A (@ARBITRARY A) P s)). Qed.
Lemma lem4858461 {A : Type'} (P : type686 A) (s : A -> Prop) (p' : Prop) : term12 A P s p'.
Proof. exact (@lem4858460 A P s p'). Qed.
Lemma lem4858462 {A : Type'} (P : type686 A) (s : A -> Prop) (p' : Prop) : (term12 A P s p') = (term13 A P s p').
Proof. exact (eq_refl (term12 A P s p')). Qed.
Lemma lem4858463 {A : Type'} (P : type686 A) (s : A -> Prop) (p' : Prop) : term13 A P s p'.
Proof. exact (EQ_MP (@lem4858462 A P s p') (@lem4858461 A P s p')). Qed.
Lemma lem4858464 {A : Type'} (P : type686 A) (s : A -> Prop) (p' : Prop) (q' : Prop) : term14 A P s p' q'.
Proof. exact (@lem4858463 A P s p' q'). Qed.
Lemma lem4858465 {A : Type'} (P : type686 A) (s : A -> Prop) (p' : Prop) (q' : Prop) : (term14 A P s p' q') = (term15 A P s p' q').
Proof. exact (eq_refl (term14 A P s p' q')). Qed.
Lemma lem4858466 {A : Type'} (P : type686 A) (s : A -> Prop) (p' : Prop) (q' : Prop) : term15 A P s p' q'.
Proof. exact (EQ_MP (@lem4858465 A P s p' q') (@lem4858464 A P s p' q')). Qed.
Lemma lem4858467 {A : Type'} (P : type686 A) (s : A -> Prop) : (P s) = (P s).
Proof. exact (eq_refl (P s)). Qed.
Lemma lem4858468 {A : Type'} (P : type686 A) (s : A -> Prop) (q' : Prop) : term16 A P s q'.
Proof. exact (@lem4858466 A P s (P s) q'). Qed.
Lemma lem4858469 {A : Type'} (P : type686 A) (s : A -> Prop) (q' : Prop) : term17 A P s q'.
Proof. exact (@lem4858468 A P s q' (@lem4858467 A P s)). Qed.
Lemma lem4858470 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : P s) : P s.
Proof. exact (h1). Qed.
Lemma lem4858471 {A : Type'} (P : type686 A) (s : A -> Prop) : (P s) = ((P s) = True).
Proof. exact (@lem7 (P s)). Qed.
Lemma lem4858474 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : term18 A P Q s.
Proof. exact (fun h0 : term7 A P Q s => @lem4858440 A P Q s h0). Qed.
Lemma lem4858475 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : term18 A P Q s.
Proof. exact (@lem4858474 A P Q s). Qed.
Lemma lem4858476 {A : Type'} (P : type686 A) (s : A -> Prop) : term19 A P s.
Proof. exact (@lem4858475 A (@ARBITRARY A) P s). Qed.
Lemma lem4858480 {A : Type'} (s : type686 A) : (@ARBITRARY A s) = True.
Proof. exact (EQ_MP (@lem4858426 A s) (@lem4858425 A s)). Qed.
Lemma lem4858481 {A : Type'} (s : type686 A) : (@ARBITRARY A s) = True.
Proof. exact (@lem4858480 A s). Qed.
Lemma lem4858482 {A : Type'} (s : A -> Prop) : (term20 A s) = True.
Proof. exact (@lem4858481 A (@INSERT (A -> Prop) s (@EMPTY (A -> Prop)))). Qed.
Lemma lem4858483 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4858484 {A : Type'} (s : A -> Prop) : (term21 A s) = (and True).
Proof. exact (MK_COMB (@lem4858483) (@lem4858482 A s)). Qed.
Lemma lem4858486 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : P s) : (P s) = True.
Proof. exact (EQ_MP (@lem4858471 A P s) (@lem4858470 A P s h1)). Qed.
Lemma lem4858487 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : P s) : (term22 A P s) = (True /\ True).
Proof. exact (MK_COMB (@lem4858484 A s) (@lem4858486 A P s h1)). Qed.
Lemma lem4858489 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4858490 : (True /\ True) = True.
Proof. exact (@lem4858489 True). Qed.
Lemma lem4858491 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : P s) : (term22 A P s) = True.
Proof. exact (TRANS (@lem4858487 A P s h1) (@lem4858490)). Qed.
Lemma lem4858492 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : P s) : True = (term22 A P s).
Proof. exact (SYM (@lem4858491 A P s h1)). Qed.
Lemma lem4858493 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : P s) : term22 A P s.
Proof. exact (EQ_MP (@lem4858492 A P s h1) (@lem0)). Qed.
Lemma lem4858494 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : P s) : (@INTERSECTION_OF A (@ARBITRARY A) P s) = True.
Proof. exact (@lem4858476 A P s (@lem4858493 A P s h1)). Qed.
Lemma lem4858495 {A : Type'} (P : type686 A) (s : A -> Prop) : term23 A P s.
Proof. exact (fun h0 : P s => @lem4858494 A P s h0). Qed.
Lemma lem4858496 {A : Type'} (P : type686 A) (s : A -> Prop) : term24 A P s.
Proof. exact (@lem4858469 A P s True). Qed.
Lemma lem4858497 {A : Type'} (P : type686 A) (s : A -> Prop) : (term25 A P s) = (term26 A P s).
Proof. exact (@lem4858496 A P s (@lem4858495 A P s)). Qed.
Lemma lem4858499 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4858500 {A : Type'} (P : type686 A) (s : A -> Prop) : (term26 A P s) = True.
Proof. exact (@lem4858499 (P s)). Qed.
Lemma lem4858501 {A : Type'} (P : type686 A) (s : A -> Prop) : (term25 A P s) = True.
Proof. exact (TRANS (@lem4858497 A P s) (@lem4858500 A P s)). Qed.
Lemma lem4858502 {A : Type'} (P : type686 A) : (term27 A P) = (term28 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4858501 A P s)). Qed.
Lemma lem4858503 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4858504 {A : Type'} (P : type686 A) : (term29 A P) = (term30 A).
Proof. exact (MK_COMB (@lem4858503 A) (@lem4858502 A P)). Qed.
Lemma lem4858506 {A : Type'} (t : Prop) : (term31 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4858507 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (@lem4858506 (A -> Prop) t). Qed.
Lemma lem4858508 {A : Type'} : (term30 A) = True.
Proof. exact (@lem4858507 A True). Qed.
Lemma lem4858509 {A : Type'} (P : type686 A) : (term29 A P) = True.
Proof. exact (TRANS (@lem4858504 A P) (@lem4858508 A)). Qed.
Lemma lem4858510 {A : Type'} : (term33 A) = (term34 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4858509 A P)). Qed.
Lemma lem4858511 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4858512 {A : Type'} : (term35 A) = (term36 A).
Proof. exact (MK_COMB (@lem4858511 A) (@lem4858510 A)). Qed.
Lemma lem4858514 {A : Type'} (t : Prop) : (term31 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4858515 {A : Type'} (t : Prop) : (term37 A t) = t.
Proof. exact (@lem4858514 (type686 A) t). Qed.
Lemma lem4858516 {A : Type'} : (term36 A) = True.
Proof. exact (@lem4858515 A True). Qed.
Lemma lem4858517 {A : Type'} : (term35 A) = True.
Proof. exact (TRANS (@lem4858512 A) (@lem4858516 A)). Qed.
Lemma lem4858518 {A : Type'} : True = (term35 A).
Proof. exact (SYM (@lem4858517 A)). Qed.
Lemma lem4858519 {A : Type'} : term35 A.
Proof. exact (EQ_MP (@lem4858518 A) (@lem0)). Qed.
