Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INSERT_INSERT_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3276334 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3276335 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3276334 A s t). Qed.
Lemma lem3276336 {A : Type'} (x : A) (s : A -> Prop) : ((term1 A x s) = (@INSERT A x s)) = (term2 A x s).
Proof. exact (@lem3276335 A (term1 A x s) (@INSERT A x s)). Qed.
Lemma lem3276345 {A : Type'} (x : A) : (term3 A x) = (term4 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3276336 A x s)). Qed.
Lemma lem3276346 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3276347 {A : Type'} (x : A) : (term5 A x) = (term6 A x).
Proof. exact (MK_COMB (@lem3276346 A) (@lem3276345 A x)). Qed.
Lemma lem3276352 {A : Type'} : (term7 A) = (term8 A).
Proof. exact (fun_ext (fun x : A => @lem3276347 A x)). Qed.
Lemma lem3276353 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3276354 {A : Type'} : (term9 A) = (term10 A).
Proof. exact (MK_COMB (@lem3276353 A) (@lem3276352 A)). Qed.
Lemma lem3276359 {A : Type'} : (term10 A) = (term9 A).
Proof. exact (SYM (@lem3276354 A)). Qed.
Lemma lem3276375 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term11 A x y s) = (term12 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3276376 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term11 A x y s) = (term12 A y x s).
Proof. exact (@lem3276375 A y x s). Qed.
Lemma lem3276377 {A : Type'} (x' : A) (x : A) (s : A -> Prop) : (term13 A x' x s) = (term14 A x' x s).
Proof. exact (@lem3276376 A x x' (@INSERT A x s)). Qed.
Lemma lem3276383 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term11 A x y s) = (term12 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3276384 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term11 A x y s) = (term12 A y x s).
Proof. exact (@lem3276383 A y x s). Qed.
Lemma lem3276385 {A : Type'} (x : A) (x' : A) (s : A -> Prop) : (term11 A x' x s) = (term12 A x x' s).
Proof. exact (@lem3276384 A x x' s). Qed.
Lemma lem3276391 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3276392 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3276391 A P x). Qed.
Lemma lem3276393 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3276392 A s x'). Qed.
Lemma lem3276394 {A : Type'} (x' : A) (x : A) : (term15 A x' x) = (term15 A x' x).
Proof. exact (eq_refl (term15 A x' x)). Qed.
Lemma lem3276395 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term12 A x x' s) = (term16 A x s x').
Proof. exact (MK_COMB (@lem3276394 A x' x) (@lem3276393 A s x')). Qed.
Lemma lem3276398 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term11 A x' x s) = (term16 A x s x').
Proof. exact (TRANS (@lem3276385 A x x' s) (@lem3276395 A x s x')). Qed.
Lemma lem3276399 {A : Type'} (x' : A) (x : A) : (term15 A x' x) = (term15 A x' x).
Proof. exact (eq_refl (term15 A x' x)). Qed.
Lemma lem3276400 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term14 A x' x s) = (term17 A x s x').
Proof. exact (MK_COMB (@lem3276399 A x' x) (@lem3276398 A x s x')). Qed.
Lemma lem3276403 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term13 A x' x s) = (term17 A x s x').
Proof. exact (TRANS (@lem3276377 A x' x s) (@lem3276400 A x s x')). Qed.
Lemma lem3276404 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3276405 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term18 A x' x s) = (term19 A x s x').
Proof. exact (MK_COMB (@lem3276404) (@lem3276403 A x s x')). Qed.
Lemma lem3276407 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term11 A x y s) = (term12 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3276408 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term11 A x y s) = (term12 A y x s).
Proof. exact (@lem3276407 A y x s). Qed.
Lemma lem3276409 {A : Type'} (x : A) (x' : A) (s : A -> Prop) : (term11 A x' x s) = (term12 A x x' s).
Proof. exact (@lem3276408 A x x' s). Qed.
Lemma lem3276415 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3276416 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3276415 A P x). Qed.
Lemma lem3276417 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3276416 A s x'). Qed.
Lemma lem3276418 {A : Type'} (x' : A) (x : A) : (term15 A x' x) = (term15 A x' x).
Proof. exact (eq_refl (term15 A x' x)). Qed.
Lemma lem3276419 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term12 A x x' s) = (term16 A x s x').
Proof. exact (MK_COMB (@lem3276418 A x' x) (@lem3276417 A s x')). Qed.
Lemma lem3276422 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term11 A x' x s) = (term16 A x s x').
Proof. exact (TRANS (@lem3276409 A x x' s) (@lem3276419 A x s x')). Qed.
Lemma lem3276423 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term13 A x' x s) = (term11 A x' x s)) = ((term17 A x s x') = (term16 A x s x')).
Proof. exact (MK_COMB (@lem3276405 A x s x') (@lem3276422 A x s x')). Qed.
Lemma lem3276426 {A : Type'} (x : A) (s : A -> Prop) : (term20 A x s) = (term21 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3276423 A x s x')). Qed.
Lemma lem3276427 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3276428 {A : Type'} (x : A) (s : A -> Prop) : (term2 A x s) = (term22 A x s).
Proof. exact (MK_COMB (@lem3276427 A) (@lem3276426 A x s)). Qed.
Lemma lem3276433 {A : Type'} (x : A) : (term4 A x) = (term23 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3276428 A x s)). Qed.
Lemma lem3276434 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3276435 {A : Type'} (x : A) : (term6 A x) = (term24 A x).
Proof. exact (MK_COMB (@lem3276434 A) (@lem3276433 A x)). Qed.
Lemma lem3276440 {A : Type'} : (term8 A) = (term25 A).
Proof. exact (fun_ext (fun x : A => @lem3276435 A x)). Qed.
Lemma lem3276441 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3276442 {A : Type'} : (term10 A) = (term26 A).
Proof. exact (MK_COMB (@lem3276441 A) (@lem3276440 A)). Qed.
Lemma lem3276447 {A : Type'} : (term26 A) = (term10 A).
Proof. exact (SYM (@lem3276442 A)). Qed.
Lemma lem3276449 (p : Prop) : p = (term27 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3276450 {A : Type'} : (term26 A) = (term28 A).
Proof. exact (@lem3276449 (term26 A)). Qed.
Lemma lem3276451 {A : Type'} : (term28 A) = (term26 A).
Proof. exact (SYM (@lem3276450 A)). Qed.
Lemma lem3276452 {A : Type'} (h1 : term29 A) : term29 A.
Proof. exact (h1). Qed.
Lemma lem3276455 {A : Type'} (h1 : term28 A) : term28 A.
Proof. exact (h1). Qed.
Lemma lem3276456 {A : Type'} : term30 A.
Proof. exact (fun h0 : term28 A => @lem3276455 A h0). Qed.
Lemma lem3276457 {A : Type'} (h1 : term30 A) : term30 A.
Proof. exact (h1). Qed.
Lemma lem3276458 {A : Type'} (h1 : term28 A) : term28 A.
Proof. exact (h1). Qed.
Lemma lem3276459 {A : Type'} (h1 : term28 A) (h2 : term30 A) : term28 A.
Proof. exact (@lem3276457 A h2 (@lem3276458 A h1)). Qed.
Lemma lem3276460 {A : Type'} (h1 : term28 A) : term31 A.
Proof. exact (fun h0 : term30 A => @lem3276459 A h1 h0). Qed.
Lemma lem3276461 {A : Type'} (h1 : term30 A) : term30 A.
Proof. exact (h1). Qed.
Lemma lem3276462 {A : Type'} (h1 : term28 A) (h2 : term30 A) : term28 A.
Proof. exact (@lem3276460 A h1 (@lem3276461 A h2)). Qed.
Lemma lem3276463 {A : Type'} (h1 : term30 A) : term30 A.
Proof. exact (fun h0 : term28 A => @lem3276462 A h0 h1). Qed.
Lemma lem3276464 {A : Type'} : term32 A.
Proof. exact (fun h0 : term30 A => @lem3276463 A h0). Qed.
Lemma lem3276467 {A : Type'} : term30 A.
Proof. exact (@lem3276464 A (@lem3276456 A)). Qed.
Lemma lem3276468 {A : Type'} : term30 A.
Proof. exact (@lem3276467 A). Qed.
Lemma lem3276470 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3276471 {A : Type'} : (term28 A) = (term33 A).
Proof. exact (@lem3276470 (term29 A)). Qed.
Lemma lem3276473 (t : Prop) : (term34 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3276474 {A : Type'} : (term33 A) = (term26 A).
Proof. exact (@lem3276473 (term26 A)). Qed.
Lemma lem3276497 {A : Type'} : (term28 A) = (term26 A).
Proof. exact (TRANS (@lem3276471 A) (@lem3276474 A)). Qed.
Lemma lem3276514 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term17 A x s x') = (term16 A x s x')) = ((term17 A x s x') = (term16 A x s x')).
Proof. exact (eq_refl ((term17 A x s x') = (term16 A x s x'))). Qed.
Lemma lem3276515 {A : Type'} (x : A) (s : A -> Prop) : (term21 A x s) = (term21 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3276514 A x s x')). Qed.
Lemma lem3276516 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3276517 {A : Type'} (x : A) (s : A -> Prop) : (term22 A x s) = (term22 A x s).
Proof. exact (MK_COMB (@lem3276516 A) (@lem3276515 A x s)). Qed.
Lemma lem3276518 {A : Type'} (x : A) : (term23 A x) = (term23 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3276517 A x s)). Qed.
Lemma lem3276519 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3276520 {A : Type'} (x : A) : (term24 A x) = (term24 A x).
Proof. exact (MK_COMB (@lem3276519 A) (@lem3276518 A x)). Qed.
Lemma lem3276521 {A : Type'} : (term25 A) = (term25 A).
Proof. exact (fun_ext (fun x : A => @lem3276520 A x)). Qed.
Lemma lem3276522 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3276523 {A : Type'} : (term26 A) = (term26 A).
Proof. exact (MK_COMB (@lem3276522 A) (@lem3276521 A)). Qed.
Lemma lem3276550 {A : Type'} : (term28 A) = (term26 A).
Proof. exact (TRANS (@lem3276497 A) (@lem3276523 A)). Qed.
Lemma lem3276551 {A : Type'} : (term26 A) = (term28 A).
Proof. exact (SYM (@lem3276550 A)). Qed.
Lemma lem3276553 (p : Prop) : p = (term27 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3276554 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term17 A x s x') = (term16 A x s x')) = (term35 A x s x').
Proof. exact (@lem3276553 ((term17 A x s x') = (term16 A x s x'))). Qed.
Lemma lem3276555 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term35 A x s x') = ((term17 A x s x') = (term16 A x s x')).
Proof. exact (SYM (@lem3276554 A x s x')). Qed.
Lemma lem3276556 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term36 A x s x') : term36 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3276567 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term37 A x s x') = (term38 A x s x').
Proof. exact (@lem17160 (x' = x) (s x')). Qed.
Lemma lem3276572 {A : Type'} (x' : A) (x : A) : (term39 A x' x) = (term39 A x' x).
Proof. exact (eq_refl (term39 A x' x)). Qed.
Lemma lem3276573 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term40 A x s x') = (term41 A x s x').
Proof. exact (MK_COMB (@lem3276572 A x' x) (@lem3276567 A x s x')). Qed.
Lemma lem3276574 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term42 A x s x') = (term40 A x s x').
Proof. exact (@lem17160 (x' = x) (term16 A x s x')). Qed.
Lemma lem3276575 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term42 A x s x') = (term41 A x s x').
Proof. exact (TRANS (@lem3276574 A x s x') (@lem3276573 A x s x')). Qed.
Lemma lem3276587 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term37 A x s x') = (term38 A x s x').
Proof. exact (@lem17160 (x' = x) (s x')). Qed.
Lemma lem3276590 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term16 A x s x') = (term16 A x s x').
Proof. exact (eq_refl (term16 A x s x')). Qed.
Lemma lem3276591 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3276592 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term43 A x s x') = (term44 A x s x').
Proof. exact (MK_COMB (@lem3276591) (@lem3276575 A x s x')). Qed.
Lemma lem3276593 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term45 A x s x') = (term46 A x s x').
Proof. exact (MK_COMB (@lem3276592 A x s x') (@lem3276590 A x s x')). Qed.
Lemma lem3276595 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term47 A x s x') = (term47 A x s x').
Proof. exact (eq_refl (term47 A x s x')). Qed.
Lemma lem3276596 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term48 A x s x') = (term49 A x s x').
Proof. exact (MK_COMB (@lem3276595 A x s x') (@lem3276587 A x s x')). Qed.
Lemma lem3276597 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3276598 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term50 A x s x') = (term51 A x s x').
Proof. exact (MK_COMB (@lem3276597) (@lem3276596 A x s x')). Qed.
Lemma lem3276599 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term52 A x s x') = (term53 A x s x').
Proof. exact (MK_COMB (@lem3276598 A x s x') (@lem3276593 A x s x')). Qed.
Lemma lem3276600 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term36 A x s x') = (term52 A x s x').
Proof. exact (@lem17646 (term17 A x s x') (term16 A x s x')). Qed.
Lemma lem3276605 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term36 A x s x') = (term53 A x s x').
Proof. exact (TRANS (@lem3276600 A x s x') (@lem3276599 A x s x')). Qed.
Lemma lem3276686 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term36 A x s x') : term53 A x s x'.
Proof. exact (EQ_MP (@lem3276605 A x s x') (@lem3276556 A x s x' h1)). Qed.
Lemma lem3276687 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term49 A x s x') : term49 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3276688 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term46 A x s x') : term46 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3276689 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term49 A x s x') : term38 A x s x'.
Proof. exact (proj2 (@lem3276687 A x s x' h1)). Qed.
Lemma lem3276690 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term49 A x s x') : term17 A x s x'.
Proof. exact (proj1 (@lem3276687 A x s x' h1)). Qed.
Lemma lem3276694 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term16 A x s x') : term16 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3276697 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term46 A x s x') : term16 A x s x'.
Proof. exact (proj2 (@lem3276688 A x s x' h1)). Qed.
Lemma lem3276698 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term46 A x s x') : term41 A x s x'.
Proof. exact (proj1 (@lem3276688 A x s x' h1)). Qed.
Lemma lem3276699 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term46 A x s x') : term38 A x s x'.
Proof. exact (proj2 (@lem3276698 A x s x' h1)). Qed.
Lemma lem3276716 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3276728 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3276740 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3276756 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3276772 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3276774 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term49 A x s x') : term54 A x' x.
Proof. exact (proj1 (@lem3276689 A x s x' h1)). Qed.
Lemma lem3276778 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3276780 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term49 A x s x') : term54 A x' x.
Proof. exact (proj1 (@lem3276689 A x s x' h1)). Qed.
Lemma lem3276784 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3276788 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term49 A x s x') : term55 A s x'.
Proof. exact (proj2 (@lem3276689 A x s x' h1)). Qed.
Lemma lem3276790 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3276792 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term46 A x s x') : term54 A x' x.
Proof. exact (proj1 (@lem3276698 A x s x' h1)). Qed.
Lemma lem3276798 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3276804 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term46 A x s x') : term55 A s x'.
Proof. exact (proj2 (@lem3276699 A x s x' h1)). Qed.
Lemma lem3276806 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3276821 {A : Type'} (x : A) : (term56 A x) = (term56 A x).
Proof. exact (eq_refl (term56 A x)). Qed.
Lemma lem3276822 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term57 A x x') = (term58 A x).
Proof. exact (MK_COMB (@lem3276821 A x) (@lem3276778 A x' x h1)). Qed.
Lemma lem3276823 {A : Type'} (x : A) : (term58 A x) = (term59 A x).
Proof. exact (eq_refl (term58 A x)). Qed.
Lemma lem3276824 {A : Type'} (x : A) (x' : A) : (term60 A x x') = (term60 A x x').
Proof. exact (eq_refl (term60 A x x')). Qed.
Lemma lem3276825 {A : Type'} (x' : A) (x : A) : ((term57 A x x') = (term58 A x)) = ((term57 A x x') = (term59 A x)).
Proof. exact (MK_COMB (@lem3276824 A x x') (@lem3276823 A x)). Qed.
Lemma lem3276826 {A : Type'} (x' : A) (x : A) : (term57 A x x') = (term54 A x' x).
Proof. exact (eq_refl (term57 A x x')). Qed.
Lemma lem3276827 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3276828 {A : Type'} (x' : A) (x : A) : (term60 A x x') = (term61 A x' x).
Proof. exact (MK_COMB (@lem3276827) (@lem3276826 A x' x)). Qed.
Lemma lem3276829 {A : Type'} (x : A) : (term59 A x) = (term59 A x).
Proof. exact (eq_refl (term59 A x)). Qed.
Lemma lem3276830 {A : Type'} (x' : A) (x : A) : ((term57 A x x') = (term59 A x)) = ((term54 A x' x) = (term59 A x)).
Proof. exact (MK_COMB (@lem3276828 A x' x) (@lem3276829 A x)). Qed.
Lemma lem3276831 {A : Type'} (x' : A) (x : A) : ((term57 A x x') = (term58 A x)) = ((term54 A x' x) = (term59 A x)).
Proof. exact (TRANS (@lem3276825 A x' x) (@lem3276830 A x' x)). Qed.
Lemma lem3276832 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term54 A x' x) = (term59 A x).
Proof. exact (EQ_MP (@lem3276831 A x' x) (@lem3276822 A x' x h1)). Qed.
Lemma lem3276833 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term49 A x s x') (h2 : x' = x) : term59 A x.
Proof. exact (EQ_MP (@lem3276832 A x' x h2) (@lem3276774 A x s x' h1)). Qed.
Lemma lem3276861 {A : Type'} (x : A) : (term56 A x) = (term56 A x).
Proof. exact (eq_refl (term56 A x)). Qed.
Lemma lem3276862 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term57 A x x') = (term58 A x).
Proof. exact (MK_COMB (@lem3276861 A x) (@lem3276784 A x' x h1)). Qed.
Lemma lem3276863 {A : Type'} (x : A) : (term58 A x) = (term59 A x).
Proof. exact (eq_refl (term58 A x)). Qed.
Lemma lem3276864 {A : Type'} (x : A) (x' : A) : (term60 A x x') = (term60 A x x').
Proof. exact (eq_refl (term60 A x x')). Qed.
Lemma lem3276865 {A : Type'} (x' : A) (x : A) : ((term57 A x x') = (term58 A x)) = ((term57 A x x') = (term59 A x)).
Proof. exact (MK_COMB (@lem3276864 A x x') (@lem3276863 A x)). Qed.
Lemma lem3276866 {A : Type'} (x' : A) (x : A) : (term57 A x x') = (term54 A x' x).
Proof. exact (eq_refl (term57 A x x')). Qed.
Lemma lem3276867 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3276868 {A : Type'} (x' : A) (x : A) : (term60 A x x') = (term61 A x' x).
Proof. exact (MK_COMB (@lem3276867) (@lem3276866 A x' x)). Qed.
Lemma lem3276869 {A : Type'} (x : A) : (term59 A x) = (term59 A x).
Proof. exact (eq_refl (term59 A x)). Qed.
Lemma lem3276870 {A : Type'} (x' : A) (x : A) : ((term57 A x x') = (term59 A x)) = ((term54 A x' x) = (term59 A x)).
Proof. exact (MK_COMB (@lem3276868 A x' x) (@lem3276869 A x)). Qed.
Lemma lem3276871 {A : Type'} (x' : A) (x : A) : ((term57 A x x') = (term58 A x)) = ((term54 A x' x) = (term59 A x)).
Proof. exact (TRANS (@lem3276865 A x' x) (@lem3276870 A x' x)). Qed.
Lemma lem3276872 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term54 A x' x) = (term59 A x).
Proof. exact (EQ_MP (@lem3276871 A x' x) (@lem3276862 A x' x h1)). Qed.
Lemma lem3276873 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term49 A x s x') (h2 : x' = x) : term59 A x.
Proof. exact (EQ_MP (@lem3276872 A x' x h2) (@lem3276780 A x s x' h1)). Qed.
Lemma lem3276901 {A : Type'} (x : A) : (term56 A x) = (term56 A x).
Proof. exact (eq_refl (term56 A x)). Qed.
Lemma lem3276902 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term57 A x x') = (term58 A x).
Proof. exact (MK_COMB (@lem3276901 A x) (@lem3276798 A x' x h1)). Qed.
Lemma lem3276903 {A : Type'} (x : A) : (term58 A x) = (term59 A x).
Proof. exact (eq_refl (term58 A x)). Qed.
Lemma lem3276904 {A : Type'} (x : A) (x' : A) : (term60 A x x') = (term60 A x x').
Proof. exact (eq_refl (term60 A x x')). Qed.
Lemma lem3276905 {A : Type'} (x' : A) (x : A) : ((term57 A x x') = (term58 A x)) = ((term57 A x x') = (term59 A x)).
Proof. exact (MK_COMB (@lem3276904 A x x') (@lem3276903 A x)). Qed.
Lemma lem3276906 {A : Type'} (x' : A) (x : A) : (term57 A x x') = (term54 A x' x).
Proof. exact (eq_refl (term57 A x x')). Qed.
Lemma lem3276907 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3276908 {A : Type'} (x' : A) (x : A) : (term60 A x x') = (term61 A x' x).
Proof. exact (MK_COMB (@lem3276907) (@lem3276906 A x' x)). Qed.
Lemma lem3276909 {A : Type'} (x : A) : (term59 A x) = (term59 A x).
Proof. exact (eq_refl (term59 A x)). Qed.
Lemma lem3276910 {A : Type'} (x' : A) (x : A) : ((term57 A x x') = (term59 A x)) = ((term54 A x' x) = (term59 A x)).
Proof. exact (MK_COMB (@lem3276908 A x' x) (@lem3276909 A x)). Qed.
Lemma lem3276911 {A : Type'} (x' : A) (x : A) : ((term57 A x x') = (term58 A x)) = ((term54 A x' x) = (term59 A x)).
Proof. exact (TRANS (@lem3276905 A x' x) (@lem3276910 A x' x)). Qed.
Lemma lem3276912 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term54 A x' x) = (term59 A x).
Proof. exact (EQ_MP (@lem3276911 A x' x) (@lem3276902 A x' x h1)). Qed.
Lemma lem3276913 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term46 A x s x') (h2 : x' = x) : term59 A x.
Proof. exact (EQ_MP (@lem3276912 A x' x h2) (@lem3276792 A x s x' h1)). Qed.
Lemma lem3276955 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3276956 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3276955 A x). Qed.
Lemma lem3276957 {A : Type'} (x : A) : term62 A x.
Proof. exact (fun h0 : term59 A x => @lem3276956 A x). Qed.
Lemma lem3276959 (p : Prop) : (term63 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3276960 {A : Type'} (x : A) : (term62 A x) = (x = x).
Proof. exact (@lem3276959 (x = x)). Qed.
Lemma lem3276961 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3276960 A x) (@lem3276957 A x)). Qed.
Lemma lem3276964 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3276966 {A : Type'} (x : A) : (term59 A x) = (term64 A x).
Proof. exact (@lem3276964 (x = x)). Qed.
Lemma lem3276969 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term49 A x s x') (h2 : x' = x) : term64 A x.
Proof. exact (EQ_MP (@lem3276966 A x) (@lem3276833 A s x' x h1 h2)). Qed.
Lemma lem3276972 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term49 A x s x') (h2 : x' = x) : False.
Proof. exact (@lem3276969 A s x' x h1 h2 (@lem3276961 A x)). Qed.
Lemma lem3276973 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term49 A x s x') (h2 : x' = x) : term65.
Proof. exact (fun h0 : ~ False => @lem3276972 A s x' x h1 h2). Qed.
Lemma lem3276975 (p : Prop) : (term63 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3276976 : term65 = False.
Proof. exact (@lem3276975 False). Qed.
Lemma lem3276993 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3276994 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3276993 A x). Qed.
Lemma lem3276995 {A : Type'} (x : A) : term62 A x.
Proof. exact (fun h0 : term59 A x => @lem3276994 A x). Qed.
Lemma lem3276997 (p : Prop) : (term63 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3276998 {A : Type'} (x : A) : (term62 A x) = (x = x).
Proof. exact (@lem3276997 (x = x)). Qed.
Lemma lem3276999 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3276998 A x) (@lem3276995 A x)). Qed.
Lemma lem3277002 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3277004 {A : Type'} (x : A) : (term59 A x) = (term64 A x).
Proof. exact (@lem3277002 (x = x)). Qed.
Lemma lem3277007 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term49 A x s x') (h2 : x' = x) : term64 A x.
Proof. exact (EQ_MP (@lem3277004 A x) (@lem3276873 A s x' x h1 h2)). Qed.
Lemma lem3277010 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term49 A x s x') (h2 : x' = x) : False.
Proof. exact (@lem3277007 A s x' x h1 h2 (@lem3276999 A x)). Qed.
Lemma lem3277011 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term49 A x s x') (h2 : x' = x) : term65.
Proof. exact (fun h0 : ~ False => @lem3277010 A s x' x h1 h2). Qed.
Lemma lem3277013 (p : Prop) : (term63 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3277014 : term65 = False.
Proof. exact (@lem3277013 False). Qed.
Lemma lem3277031 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3277032 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : term66 A s x'.
Proof. exact (fun h0 : term55 A s x' => @lem3277031 A s x' h1). Qed.
Lemma lem3277034 (p : Prop) : (term63 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3277035 {A : Type'} (s : A -> Prop) (x' : A) : (term66 A s x') = (s x').
Proof. exact (@lem3277034 (s x')). Qed.
Lemma lem3277036 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (EQ_MP (@lem3277035 A s x') (@lem3277032 A s x' h1)). Qed.
Lemma lem3277039 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3277041 {A : Type'} (s : A -> Prop) (x' : A) : (term55 A s x') = (term67 A s x').
Proof. exact (@lem3277039 (s x')). Qed.
Lemma lem3277044 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term49 A x s x') : term67 A s x'.
Proof. exact (EQ_MP (@lem3277041 A s x') (@lem3276788 A x s x' h1)). Qed.
Lemma lem3277047 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term49 A x s x') : False.
Proof. exact (@lem3277044 A x s x' h2 (@lem3277036 A s x' h1)). Qed.
Lemma lem3277048 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term49 A x s x') : term65.
Proof. exact (fun h0 : ~ False => @lem3277047 A x s x' h1 h2). Qed.
Lemma lem3277050 (p : Prop) : (term63 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3277051 : term65 = False.
Proof. exact (@lem3277050 False). Qed.
Lemma lem3277052 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term49 A x s x') : False.
Proof. exact (EQ_MP (@lem3277051) (@lem3277048 A x s x' h1 h2)). Qed.
Lemma lem3277068 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3277069 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3277068 A x). Qed.
Lemma lem3277070 {A : Type'} (x : A) : term62 A x.
Proof. exact (fun h0 : term59 A x => @lem3277069 A x). Qed.
Lemma lem3277072 (p : Prop) : (term63 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3277073 {A : Type'} (x : A) : (term62 A x) = (x = x).
Proof. exact (@lem3277072 (x = x)). Qed.
Lemma lem3277074 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3277073 A x) (@lem3277070 A x)). Qed.
Lemma lem3277077 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3277079 {A : Type'} (x : A) : (term59 A x) = (term64 A x).
Proof. exact (@lem3277077 (x = x)). Qed.
Lemma lem3277082 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term46 A x s x') (h2 : x' = x) : term64 A x.
Proof. exact (EQ_MP (@lem3277079 A x) (@lem3276913 A s x' x h1 h2)). Qed.
Lemma lem3277085 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term46 A x s x') (h2 : x' = x) : False.
Proof. exact (@lem3277082 A s x' x h1 h2 (@lem3277074 A x)). Qed.
Lemma lem3277086 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term46 A x s x') (h2 : x' = x) : term65.
Proof. exact (fun h0 : ~ False => @lem3277085 A s x' x h1 h2). Qed.
Lemma lem3277088 (p : Prop) : (term63 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3277089 : term65 = False.
Proof. exact (@lem3277088 False). Qed.
Lemma lem3277106 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3277107 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : term66 A s x'.
Proof. exact (fun h0 : term55 A s x' => @lem3277106 A s x' h1). Qed.
Lemma lem3277109 (p : Prop) : (term63 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3277110 {A : Type'} (s : A -> Prop) (x' : A) : (term66 A s x') = (s x').
Proof. exact (@lem3277109 (s x')). Qed.
Lemma lem3277111 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (EQ_MP (@lem3277110 A s x') (@lem3277107 A s x' h1)). Qed.
Lemma lem3277114 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3277116 {A : Type'} (s : A -> Prop) (x' : A) : (term55 A s x') = (term67 A s x').
Proof. exact (@lem3277114 (s x')). Qed.
Lemma lem3277119 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term46 A x s x') : term67 A s x'.
Proof. exact (EQ_MP (@lem3277116 A s x') (@lem3276804 A x s x' h1)). Qed.
Lemma lem3277122 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term46 A x s x') : False.
Proof. exact (@lem3277119 A x s x' h2 (@lem3277111 A s x' h1)). Qed.
Lemma lem3277123 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term46 A x s x') : term65.
Proof. exact (fun h0 : ~ False => @lem3277122 A x s x' h1 h2). Qed.
Lemma lem3277125 (p : Prop) : (term63 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3277126 : term65 = False.
Proof. exact (@lem3277125 False). Qed.
Lemma lem3277127 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term46 A x s x') : False.
Proof. exact (EQ_MP (@lem3277126) (@lem3277123 A x s x' h1 h2)). Qed.
Lemma lem3277128 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term46 A x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3277089) (@lem3277086 A s x' x h1 h2)). Qed.
Lemma lem3277129 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term49 A x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3277014) (@lem3277011 A s x' x h1 h2)). Qed.
Lemma lem3277130 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term49 A x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3276976) (@lem3276973 A s x' x h1 h2)). Qed.
Lemma lem3277131 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term46 A x s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3277127 A x s x' h1 h2) (fun h3 : False => @lem3276806 A s x' h1)). Qed.
Lemma lem3277132 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term46 A x s x') : False.
Proof. exact (EQ_MP (@lem3277131 A x s x' h1 h2) (@lem3276806 A s x' h1)). Qed.
Lemma lem3277133 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term46 A x s x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3277128 A s x' x h1 h2) (fun h3 : False => @lem3276798 A x' x h2)). Qed.
Lemma lem3277134 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term46 A x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3277133 A s x' x h1 h2) (@lem3276798 A x' x h2)). Qed.
Lemma lem3277135 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term49 A x s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3277052 A x s x' h1 h2) (fun h3 : False => @lem3276790 A s x' h1)). Qed.
Lemma lem3277136 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term49 A x s x') : False.
Proof. exact (EQ_MP (@lem3277135 A x s x' h1 h2) (@lem3276790 A s x' h1)). Qed.
Lemma lem3277137 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term49 A x s x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3277129 A s x' x h1 h2) (fun h3 : False => @lem3276784 A x' x h2)). Qed.
Lemma lem3277138 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term49 A x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3277137 A s x' x h1 h2) (@lem3276784 A x' x h2)). Qed.
Lemma lem3277139 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term49 A x s x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3277130 A s x' x h1 h2) (fun h3 : False => @lem3276778 A x' x h2)). Qed.
Lemma lem3277140 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term49 A x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3277139 A s x' x h1 h2) (@lem3276778 A x' x h2)). Qed.
Lemma lem3277141 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term46 A x s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3277132 A x s x' h1 h2) (fun h3 : False => @lem3276772 A s x' h1)). Qed.
Lemma lem3277142 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term46 A x s x') : False.
Proof. exact (EQ_MP (@lem3277141 A x s x' h1 h2) (@lem3276772 A s x' h1)). Qed.
Lemma lem3277143 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term46 A x s x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3277134 A s x' x h1 h2) (fun h3 : False => @lem3276756 A x' x h2)). Qed.
Lemma lem3277144 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term46 A x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3277143 A s x' x h1 h2) (@lem3276756 A x' x h2)). Qed.
Lemma lem3277145 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term49 A x s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3277136 A x s x' h1 h2) (fun h3 : False => @lem3276740 A s x' h1)). Qed.
Lemma lem3277146 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term49 A x s x') : False.
Proof. exact (EQ_MP (@lem3277145 A x s x' h1 h2) (@lem3276740 A s x' h1)). Qed.
Lemma lem3277147 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term49 A x s x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3277138 A s x' x h1 h2) (fun h3 : False => @lem3276728 A x' x h2)). Qed.
Lemma lem3277148 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term49 A x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3277147 A s x' x h1 h2) (@lem3276728 A x' x h2)). Qed.
Lemma lem3277149 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term49 A x s x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3277140 A s x' x h1 h2) (fun h3 : False => @lem3276716 A x' x h2)). Qed.
Lemma lem3277150 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term49 A x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3277149 A s x' x h1 h2) (@lem3276716 A x' x h2)). Qed.
Lemma lem3277151 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term46 A x s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3277142 A x s x' h1 h2) (fun h3 : False => @lem3276772 A s x' h1)). Qed.
Lemma lem3277152 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term46 A x s x') : False.
Proof. exact (EQ_MP (@lem3277151 A x s x' h1 h2) (@lem3276772 A s x' h1)). Qed.
Lemma lem3277153 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term46 A x s x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3277144 A s x' x h1 h2) (fun h3 : False => @lem3276756 A x' x h2)). Qed.
Lemma lem3277154 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term46 A x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3277153 A s x' x h1 h2) (@lem3276756 A x' x h2)). Qed.
Lemma lem3277155 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term49 A x s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3277146 A x s x' h1 h2) (fun h3 : False => @lem3276740 A s x' h1)). Qed.
Lemma lem3277156 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term49 A x s x') : False.
Proof. exact (EQ_MP (@lem3277155 A x s x' h1 h2) (@lem3276740 A s x' h1)). Qed.
Lemma lem3277157 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term49 A x s x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3277148 A s x' x h1 h2) (fun h3 : False => @lem3276728 A x' x h2)). Qed.
Lemma lem3277158 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term49 A x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3277157 A s x' x h1 h2) (@lem3276728 A x' x h2)). Qed.
Lemma lem3277159 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term49 A x s x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3277150 A s x' x h1 h2) (fun h3 : False => @lem3276716 A x' x h2)). Qed.
Lemma lem3277160 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term49 A x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3277159 A s x' x h1 h2) (@lem3276716 A x' x h2)). Qed.
Lemma lem3277161 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term46 A x s x') : False.
Proof. exact (or_elim (@lem3276697 A x s x' h1) (fun h0 : x' = x => @lem3277154 A s x' x h1 h0) (fun h0 : s x' => @lem3277152 A x s x' h0 h1)). Qed.
Lemma lem3277162 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term49 A x s x') (h2 : term16 A x s x') : False.
Proof. exact (or_elim (@lem3276694 A x s x' h2) (fun h0 : x' = x => @lem3277158 A s x' x h1 h0) (fun h0 : s x' => @lem3277156 A x s x' h0 h1)). Qed.
Lemma lem3277163 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term49 A x s x') : False.
Proof. exact (or_elim (@lem3276690 A x s x' h1) (fun h0 : x' = x => @lem3277160 A s x' x h1 h0) (fun h0 : term16 A x s x' => @lem3277162 A x s x' h1 h0)). Qed.
Lemma lem3277164 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term36 A x s x') : False.
Proof. exact (or_elim (@lem3276686 A x s x' h1) (fun h0 : term49 A x s x' => @lem3277163 A x s x' h0) (fun h0 : term46 A x s x' => @lem3277161 A x s x' h0)). Qed.
Lemma lem3277165 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term36 A x s x') : (term36 A x s x') = False.
Proof. exact (prop_ext (fun h2 : term36 A x s x' => @lem3277164 A x s x' h1) (fun h2 : False => @lem3276556 A x s x' h1)). Qed.
Lemma lem3277166 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term36 A x s x') : False.
Proof. exact (EQ_MP (@lem3277165 A x s x' h1) (@lem3276556 A x s x' h1)). Qed.
Lemma lem3277167 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : term35 A x s x'.
Proof. exact (fun h0 : term36 A x s x' => @lem3277166 A x s x' h0). Qed.
Lemma lem3277168 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term17 A x s x') = (term16 A x s x').
Proof. exact (EQ_MP (@lem3276555 A x s x') (@lem3277167 A x s x')). Qed.
Lemma lem3277173 {A : Type'} (x : A) (s : A -> Prop) : term22 A x s.
Proof. exact (fun x' : A => @lem3277168 A x s x'). Qed.
Lemma lem3277178 {A : Type'} (x : A) : term24 A x.
Proof. exact (fun s : A -> Prop => @lem3277173 A x s). Qed.
Lemma lem3277183 {A : Type'} : term26 A.
Proof. exact (fun x : A => @lem3277178 A x). Qed.
Lemma lem3277184 {A : Type'} : term28 A.
Proof. exact (EQ_MP (@lem3276551 A) (@lem3277183 A)). Qed.
Lemma lem3277186 {A : Type'} : term28 A.
Proof. exact (@lem3276468 A (@lem3277184 A)). Qed.
Lemma lem3277187 {A : Type'} (h1 : term29 A) : False.
Proof. exact (@lem3277186 A (@lem3276452 A h1)). Qed.
Lemma lem3277188 {A : Type'} (h1 : term29 A) : (term29 A) = False.
Proof. exact (prop_ext (fun h2 : term29 A => @lem3277187 A h1) (fun h2 : False => @lem3276452 A h1)). Qed.
Lemma lem3277189 {A : Type'} (h1 : term29 A) : False.
Proof. exact (EQ_MP (@lem3277188 A h1) (@lem3276452 A h1)). Qed.
Lemma lem3277190 {A : Type'} : term28 A.
Proof. exact (fun h0 : term29 A => @lem3277189 A h0). Qed.
Lemma lem3277191 {A : Type'} : term26 A.
Proof. exact (EQ_MP (@lem3276451 A) (@lem3277190 A)). Qed.
Lemma lem3277192 {A : Type'} : term10 A.
Proof. exact (EQ_MP (@lem3276447 A) (@lem3277191 A)). Qed.
Lemma lem3277193 {A : Type'} : term9 A.
Proof. exact (EQ_MP (@lem3276359 A) (@lem3277192 A)). Qed.
