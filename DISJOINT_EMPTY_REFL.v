Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DISJOINT_EMPTY_REFL_term_abbrevs.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1845_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211710_spec.
Require Import thm3211711_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211738_spec.
Require Import thm3211739_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3265374 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3265375 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3265374 A s t). Qed.
Lemma lem3265376 {A : Type'} (s : A -> Prop) : (s = (@EMPTY A)) = (term1 A s).
Proof. exact (@lem3265375 A s (@EMPTY A)). Qed.
Lemma lem3265385 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3265386 {A : Type'} (s : A -> Prop) : (term2 A s) = (term3 A s).
Proof. exact (MK_COMB (@lem3265385) (@lem3265376 A s)). Qed.
Lemma lem3265388 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (EQ_MP (@lem3211739 A s t) (@lem3211738 A s t)). Qed.
Lemma lem3265389 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (@lem3265388 A s t). Qed.
Lemma lem3265390 {A : Type'} (s : A -> Prop) : (@DISJOINT A s s) = ((@INTER A s s) = (@EMPTY A)).
Proof. exact (@lem3265389 A s s). Qed.
Lemma lem3265394 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3265395 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3265394 A s t). Qed.
Lemma lem3265396 {A : Type'} (s : A -> Prop) : ((@INTER A s s) = (@EMPTY A)) = (term4 A s).
Proof. exact (@lem3265395 A (@INTER A s s) (@EMPTY A)). Qed.
Lemma lem3265401 {A : Type'} (s : A -> Prop) : (@DISJOINT A s s) = (term4 A s).
Proof. exact (TRANS (@lem3265390 A s) (@lem3265396 A s)). Qed.
Lemma lem3265406 {A : Type'} (s : A -> Prop) : ((s = (@EMPTY A)) = (@DISJOINT A s s)) = ((term1 A s) = (term4 A s)).
Proof. exact (MK_COMB (@lem3265386 A s) (@lem3265401 A s)). Qed.
Lemma lem3265411 {A : Type'} : (term5 A) = (term6 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3265406 A s)). Qed.
Lemma lem3265412 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3265413 {A : Type'} : (term7 A) = (term8 A).
Proof. exact (MK_COMB (@lem3265412 A) (@lem3265411 A)). Qed.
Lemma lem3265418 {A : Type'} : (term8 A) = (term7 A).
Proof. exact (SYM (@lem3265413 A)). Qed.
Lemma lem3265432 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3265433 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3265432 A P x). Qed.
Lemma lem3265434 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3265433 A s x). Qed.
Lemma lem3265435 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3265436 {A : Type'} (s : A -> Prop) (x : A) : (term9 A x s) = (term10 A s x).
Proof. exact (MK_COMB (@lem3265435) (@lem3265434 A s x)). Qed.
Lemma lem3265438 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3265439 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3265438 A x). Qed.
Lemma lem3265440 {A : Type'} (s : A -> Prop) (x : A) : ((@IN A x s) = (@IN A x (@EMPTY A))) = ((s x) = False).
Proof. exact (MK_COMB (@lem3265436 A s x) (@lem3265439 A x)). Qed.
Lemma lem3265442 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3265443 {A : Type'} (s : A -> Prop) (x : A) : ((s x) = False) = (term11 A s x).
Proof. exact (@lem3265442 (s x)). Qed.
Lemma lem3265444 {A : Type'} (s : A -> Prop) (x : A) : ((@IN A x s) = (@IN A x (@EMPTY A))) = (term11 A s x).
Proof. exact (TRANS (@lem3265440 A s x) (@lem3265443 A s x)). Qed.
Lemma lem3265445 {A : Type'} (s : A -> Prop) : (term12 A s) = (term13 A s).
Proof. exact (fun_ext (fun x : A => @lem3265444 A s x)). Qed.
Lemma lem3265446 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3265447 {A : Type'} (s : A -> Prop) : (term1 A s) = (term14 A s).
Proof. exact (MK_COMB (@lem3265446 A) (@lem3265445 A s)). Qed.
Lemma lem3265452 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3265453 {A : Type'} (s : A -> Prop) : (term3 A s) = (term15 A s).
Proof. exact (MK_COMB (@lem3265452) (@lem3265447 A s)). Qed.
Lemma lem3265461 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A x s t) = (term17 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3265462 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A x s t) = (term17 A s x t).
Proof. exact (@lem3265461 A s x t). Qed.
Lemma lem3265463 {A : Type'} (x : A) (s : A -> Prop) : (term18 A x s) = (term19 A x s).
Proof. exact (@lem3265462 A s x s). Qed.
Lemma lem3265465 (t : Prop) : (t /\ t) = t.
Proof. exact (proj2 (@lem1845 t)). Qed.
Lemma lem3265466 {A : Type'} (x : A) (s : A -> Prop) : (term19 A x s) = (@IN A x s).
Proof. exact (@lem3265465 (@IN A x s)). Qed.
Lemma lem3265468 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3265469 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3265468 A P x). Qed.
Lemma lem3265470 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3265469 A s x). Qed.
Lemma lem3265471 {A : Type'} (s : A -> Prop) (x : A) : (term19 A x s) = (s x).
Proof. exact (TRANS (@lem3265466 A x s) (@lem3265470 A s x)). Qed.
Lemma lem3265472 {A : Type'} (s : A -> Prop) (x : A) : (term18 A x s) = (s x).
Proof. exact (TRANS (@lem3265463 A x s) (@lem3265471 A s x)). Qed.
Lemma lem3265473 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3265474 {A : Type'} (s : A -> Prop) (x : A) : (term20 A x s) = (term10 A s x).
Proof. exact (MK_COMB (@lem3265473) (@lem3265472 A s x)). Qed.
Lemma lem3265476 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3265477 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3265476 A x). Qed.
Lemma lem3265478 {A : Type'} (s : A -> Prop) (x : A) : ((term18 A x s) = (@IN A x (@EMPTY A))) = ((s x) = False).
Proof. exact (MK_COMB (@lem3265474 A s x) (@lem3265477 A x)). Qed.
Lemma lem3265480 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3265481 {A : Type'} (s : A -> Prop) (x : A) : ((s x) = False) = (term11 A s x).
Proof. exact (@lem3265480 (s x)). Qed.
Lemma lem3265482 {A : Type'} (s : A -> Prop) (x : A) : ((term18 A x s) = (@IN A x (@EMPTY A))) = (term11 A s x).
Proof. exact (TRANS (@lem3265478 A s x) (@lem3265481 A s x)). Qed.
Lemma lem3265483 {A : Type'} (s : A -> Prop) : (term21 A s) = (term13 A s).
Proof. exact (fun_ext (fun x : A => @lem3265482 A s x)). Qed.
Lemma lem3265484 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3265485 {A : Type'} (s : A -> Prop) : (term4 A s) = (term14 A s).
Proof. exact (MK_COMB (@lem3265484 A) (@lem3265483 A s)). Qed.
Lemma lem3265490 {A : Type'} (s : A -> Prop) : ((term1 A s) = (term4 A s)) = ((term14 A s) = (term14 A s)).
Proof. exact (MK_COMB (@lem3265453 A s) (@lem3265485 A s)). Qed.
Lemma lem3265492 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3265493 (x : Prop) : (x = x) = True.
Proof. exact (@lem3265492 Prop x). Qed.
Lemma lem3265494 {A : Type'} (s : A -> Prop) : ((term14 A s) = (term14 A s)) = True.
Proof. exact (@lem3265493 (term14 A s)). Qed.
Lemma lem3265495 {A : Type'} (s : A -> Prop) : ((term1 A s) = (term4 A s)) = True.
Proof. exact (TRANS (@lem3265490 A s) (@lem3265494 A s)). Qed.
Lemma lem3265496 {A : Type'} : (term6 A) = (term22 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3265495 A s)). Qed.
Lemma lem3265497 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3265498 {A : Type'} : (term8 A) = (term23 A).
Proof. exact (MK_COMB (@lem3265497 A) (@lem3265496 A)). Qed.
Lemma lem3265500 {A : Type'} (t : Prop) : (term24 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3265501 {A : Type'} (t : Prop) : (term25 A t) = t.
Proof. exact (@lem3265500 (A -> Prop) t). Qed.
Lemma lem3265502 {A : Type'} : (term23 A) = True.
Proof. exact (@lem3265501 A True). Qed.
Lemma lem3265503 {A : Type'} : (term8 A) = True.
Proof. exact (TRANS (@lem3265498 A) (@lem3265502 A)). Qed.
Lemma lem3265504 {A : Type'} : True = (term8 A).
Proof. exact (SYM (@lem3265503 A)). Qed.
Lemma lem3265505 {A : Type'} : term8 A.
Proof. exact (EQ_MP (@lem3265504 A) (@lem0)). Qed.
Lemma lem3265506 {A : Type'} : term7 A.
Proof. exact (EQ_MP (@lem3265418 A) (@lem3265505 A)). Qed.
