Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINREC_EXISTS_LEMMA_term_abbrevs.
Require Import FINITE_INDUCT_STRONG_spec.
Require Import IN_INSERT_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm1831_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211683_spec.
Require Import thm3211684_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm3791009_spec.
Require Import thm3791010_spec.
Require Import thm3791024_spec.
Require Import thm3791025_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem3807393 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3807394 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3807393 A s t). Qed.
Lemma lem3807395 {A : Type'} (x : A) (s : A -> Prop) : ((term1 A s x) = s) = (term2 A x s).
Proof. exact (@lem3807394 A (term1 A s x) s). Qed.
Lemma lem3807404 {A : Type'} (x : A) (s : A -> Prop) : (term3 A x s) = (term3 A x s).
Proof. exact (eq_refl (term3 A x s)). Qed.
Lemma lem3807405 {A : Type'} (x : A) (s : A -> Prop) : (term4 A x s) = (term5 A x s).
Proof. exact (MK_COMB (@lem3807404 A x s) (@lem3807395 A x s)). Qed.
Lemma lem3807408 {A : Type'} (x : A) (s : A -> Prop) : (term5 A x s) = (term4 A x s).
Proof. exact (SYM (@lem3807405 A x s)). Qed.
Lemma lem3807412 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3807413 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3807412 A P x). Qed.
Lemma lem3807414 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3807413 A s x). Qed.
Lemma lem3807415 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3807416 {A : Type'} (s : A -> Prop) (x : A) : (term6 A x s) = (term7 A s x).
Proof. exact (MK_COMB (@lem3807415) (@lem3807414 A s x)). Qed.
Lemma lem3807417 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3807418 {A : Type'} (s : A -> Prop) (x : A) : (term3 A x s) = (term8 A s x).
Proof. exact (MK_COMB (@lem3807417) (@lem3807416 A s x)). Qed.
Lemma lem3807426 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term9 A x s y) = (term10 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3807427 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term9 A x s y) = (term10 A s x y).
Proof. exact (@lem3807426 A s x y). Qed.
Lemma lem3807428 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term11 A x' s x) = (term12 A s x' x).
Proof. exact (@lem3807427 A (@INSERT A x s) x' x). Qed.
Lemma lem3807432 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term13 A x y s) = (term14 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3807433 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term13 A x y s) = (term14 A y x s).
Proof. exact (@lem3807432 A y x s). Qed.
Lemma lem3807434 {A : Type'} (x : A) (x' : A) (s : A -> Prop) : (term13 A x' x s) = (term14 A x x' s).
Proof. exact (@lem3807433 A x x' s). Qed.
Lemma lem3807440 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3807441 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3807440 A P x). Qed.
Lemma lem3807442 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3807441 A s x'). Qed.
Lemma lem3807443 {A : Type'} (x' : A) (x : A) : (term15 A x' x) = (term15 A x' x).
Proof. exact (eq_refl (term15 A x' x)). Qed.
Lemma lem3807444 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term14 A x x' s) = (term16 A x s x').
Proof. exact (MK_COMB (@lem3807443 A x' x) (@lem3807442 A s x')). Qed.
Lemma lem3807447 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term13 A x' x s) = (term16 A x s x').
Proof. exact (TRANS (@lem3807434 A x x' s) (@lem3807444 A x s x')). Qed.
Lemma lem3807448 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3807449 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term17 A x' x s) = (term18 A x s x').
Proof. exact (MK_COMB (@lem3807448) (@lem3807447 A x s x')). Qed.
Lemma lem3807452 {A : Type'} (x' : A) (x : A) : (term19 A x' x) = (term19 A x' x).
Proof. exact (eq_refl (term19 A x' x)). Qed.
Lemma lem3807453 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term12 A s x' x) = (term20 A s x' x).
Proof. exact (MK_COMB (@lem3807449 A x s x') (@lem3807452 A x' x)). Qed.
Lemma lem3807456 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term11 A x' s x) = (term20 A s x' x).
Proof. exact (TRANS (@lem3807428 A s x' x) (@lem3807453 A s x' x)). Qed.
Lemma lem3807457 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3807458 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term21 A x' s x) = (term22 A s x' x).
Proof. exact (MK_COMB (@lem3807457) (@lem3807456 A s x' x)). Qed.
Lemma lem3807460 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3807461 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3807460 A P x). Qed.
Lemma lem3807462 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3807461 A s x'). Qed.
Lemma lem3807463 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term11 A x' s x) = (@IN A x' s)) = ((term20 A s x' x) = (s x')).
Proof. exact (MK_COMB (@lem3807458 A s x' x) (@lem3807462 A s x')). Qed.
Lemma lem3807466 {A : Type'} (x : A) (s : A -> Prop) : (term23 A x s) = (term24 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3807463 A x s x')). Qed.
Lemma lem3807467 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3807468 {A : Type'} (x : A) (s : A -> Prop) : (term2 A x s) = (term25 A x s).
Proof. exact (MK_COMB (@lem3807467 A) (@lem3807466 A x s)). Qed.
Lemma lem3807473 {A : Type'} (x : A) (s : A -> Prop) : (term5 A x s) = (term26 A x s).
Proof. exact (MK_COMB (@lem3807418 A s x) (@lem3807468 A x s)). Qed.
Lemma lem3807476 {A : Type'} (x : A) (s : A -> Prop) : (term26 A x s) = (term5 A x s).
Proof. exact (SYM (@lem3807473 A x s)). Qed.
Lemma lem3807478 (p : Prop) : p = (term27 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3807479 {A : Type'} (x : A) (s : A -> Prop) : (term26 A x s) = (term28 A x s).
Proof. exact (@lem3807478 (term26 A x s)). Qed.
Lemma lem3807480 {A : Type'} (x : A) (s : A -> Prop) : (term28 A x s) = (term26 A x s).
Proof. exact (SYM (@lem3807479 A x s)). Qed.
Lemma lem3807481 {A : Type'} (x : A) (s : A -> Prop) (h1 : term29 A x s) : term29 A x s.
Proof. exact (h1). Qed.
Lemma lem3807484 {A : Type'} (x : A) (s : A -> Prop) (h1 : term28 A x s) : term28 A x s.
Proof. exact (h1). Qed.
Lemma lem3807485 {A : Type'} (x : A) (s : A -> Prop) : term30 A x s.
Proof. exact (fun h0 : term28 A x s => @lem3807484 A x s h0). Qed.
Lemma lem3807486 {A : Type'} (x : A) (s : A -> Prop) (h1 : term30 A x s) : term30 A x s.
Proof. exact (h1). Qed.
Lemma lem3807487 {A : Type'} (x : A) (s : A -> Prop) (h1 : term28 A x s) : term28 A x s.
Proof. exact (h1). Qed.
Lemma lem3807488 {A : Type'} (x : A) (s : A -> Prop) (h1 : term28 A x s) (h2 : term30 A x s) : term28 A x s.
Proof. exact (@lem3807486 A x s h2 (@lem3807487 A x s h1)). Qed.
Lemma lem3807489 {A : Type'} (x : A) (s : A -> Prop) (h1 : term28 A x s) : term31 A x s.
Proof. exact (fun h0 : term30 A x s => @lem3807488 A x s h1 h0). Qed.
Lemma lem3807490 {A : Type'} (x : A) (s : A -> Prop) (h1 : term30 A x s) : term30 A x s.
Proof. exact (h1). Qed.
Lemma lem3807491 {A : Type'} (x : A) (s : A -> Prop) (h1 : term28 A x s) (h2 : term30 A x s) : term28 A x s.
Proof. exact (@lem3807489 A x s h1 (@lem3807490 A x s h2)). Qed.
Lemma lem3807492 {A : Type'} (x : A) (s : A -> Prop) (h1 : term30 A x s) : term30 A x s.
Proof. exact (fun h0 : term28 A x s => @lem3807491 A x s h0 h1). Qed.
Lemma lem3807493 {A : Type'} (x : A) (s : A -> Prop) : term32 A x s.
Proof. exact (fun h0 : term30 A x s => @lem3807492 A x s h0). Qed.
Lemma lem3807496 {A : Type'} (x : A) (s : A -> Prop) : term30 A x s.
Proof. exact (@lem3807493 A x s (@lem3807485 A x s)). Qed.
Lemma lem3807497 {A : Type'} (x : A) (s : A -> Prop) : term30 A x s.
Proof. exact (@lem3807496 A x s). Qed.
Lemma lem3807507 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3807508 {A : Type'} (x : A) (s : A -> Prop) : (term28 A x s) = (term33 A x s).
Proof. exact (@lem3807507 (term29 A x s)). Qed.
Lemma lem3807510 (t : Prop) : (term34 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3807511 {A : Type'} (x : A) (s : A -> Prop) : (term33 A x s) = (term26 A x s).
Proof. exact (@lem3807510 (term26 A x s)). Qed.
Lemma lem3807514 {A : Type'} (x : A) (s : A -> Prop) : (term28 A x s) = (term26 A x s).
Proof. exact (TRANS (@lem3807508 A x s) (@lem3807511 A x s)). Qed.
Lemma lem3807523 {A : Type'} (s : A -> Prop) : (term35 A s) = (term36 A s).
Proof. exact (fun_ext (fun x : A => @lem3807514 A x s)). Qed.
Lemma lem3807524 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3807525 {A : Type'} (s : A -> Prop) : (term37 A s) = (term38 A s).
Proof. exact (MK_COMB (@lem3807524 A) (@lem3807523 A s)). Qed.
Lemma lem3807530 {A : Type'} : (term39 A) = (term40 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3807525 A s)). Qed.
Lemma lem3807531 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3807540 {A : Type'} : (term41 A) = (term42 A).
Proof. exact (MK_COMB (@lem3807531 A) (@lem3807530 A)). Qed.
Lemma lem3807555 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term20 A s x' x) = (s x')) = ((term20 A s x' x) = (s x')).
Proof. exact (eq_refl ((term20 A s x' x) = (s x'))). Qed.
Lemma lem3807556 {A : Type'} (x : A) (s : A -> Prop) : (term24 A x s) = (term24 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3807555 A x s x')). Qed.
Lemma lem3807557 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3807558 {A : Type'} (x : A) (s : A -> Prop) : (term25 A x s) = (term25 A x s).
Proof. exact (MK_COMB (@lem3807557 A) (@lem3807556 A x s)). Qed.
Lemma lem3807563 {A : Type'} (s : A -> Prop) (x : A) : (term8 A s x) = (term8 A s x).
Proof. exact (eq_refl (term8 A s x)). Qed.
Lemma lem3807564 {A : Type'} (x : A) (s : A -> Prop) : (term26 A x s) = (term26 A x s).
Proof. exact (MK_COMB (@lem3807563 A s x) (@lem3807558 A x s)). Qed.
Lemma lem3807565 {A : Type'} (s : A -> Prop) : (term36 A s) = (term36 A s).
Proof. exact (fun_ext (fun x : A => @lem3807564 A x s)). Qed.
Lemma lem3807566 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3807567 {A : Type'} (s : A -> Prop) : (term38 A s) = (term38 A s).
Proof. exact (MK_COMB (@lem3807566 A) (@lem3807565 A s)). Qed.
Lemma lem3807568 {A : Type'} : (term40 A) = (term40 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3807567 A s)). Qed.
Lemma lem3807569 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3807570 {A : Type'} : (term42 A) = (term42 A).
Proof. exact (MK_COMB (@lem3807569 A) (@lem3807568 A)). Qed.
Lemma lem3807597 {A : Type'} : (term41 A) = (term42 A).
Proof. exact (TRANS (@lem3807540 A) (@lem3807570 A)). Qed.
Lemma lem3807598 {A : Type'} : (term42 A) = (term41 A).
Proof. exact (SYM (@lem3807597 A)). Qed.
Lemma lem3807601 (p : Prop) : p = (term27 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3807602 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term20 A s x' x) = (s x')) = (term43 A x s x').
Proof. exact (@lem3807601 ((term20 A s x' x) = (s x'))). Qed.
Lemma lem3807603 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term43 A x s x') = ((term20 A s x' x) = (s x')).
Proof. exact (SYM (@lem3807602 A x s x')). Qed.
Lemma lem3807604 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term44 A x s x') : term44 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3807610 {A : Type'} (s : A -> Prop) (x : A) (h1 : term7 A s x) : term7 A s x.
Proof. exact (h1). Qed.
Lemma lem3807619 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term45 A x s x') = (term46 A x s x').
Proof. exact (@lem17160 (x' = x) (s x')). Qed.
Lemma lem3807626 {A : Type'} (x' : A) (x : A) : (term47 A x' x) = (x' = x).
Proof. exact (@lem16933 (x' = x)). Qed.
Lemma lem3807627 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3807628 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term48 A x s x') = (term49 A x s x').
Proof. exact (MK_COMB (@lem3807627) (@lem3807619 A x s x')). Qed.
Lemma lem3807629 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term50 A s x' x) = (term51 A s x' x).
Proof. exact (MK_COMB (@lem3807628 A x s x') (@lem3807626 A x' x)). Qed.
Lemma lem3807630 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term52 A s x' x) = (term50 A s x' x).
Proof. exact (@lem17045 (term16 A x s x') (term19 A x' x)). Qed.
Lemma lem3807631 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term52 A s x' x) = (term51 A s x' x).
Proof. exact (TRANS (@lem3807630 A s x' x) (@lem3807629 A s x' x)). Qed.
Lemma lem3807636 {A : Type'} (s : A -> Prop) (x' : A) : (s x') = (s x').
Proof. exact (eq_refl (s x')). Qed.
Lemma lem3807637 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3807638 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term53 A s x' x) = (term54 A s x' x).
Proof. exact (MK_COMB (@lem3807637) (@lem3807631 A s x' x)). Qed.
Lemma lem3807639 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term55 A x s x') = (term56 A x s x').
Proof. exact (MK_COMB (@lem3807638 A s x' x) (@lem3807636 A s x')). Qed.
Lemma lem3807644 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term57 A x s x') = (term57 A x s x').
Proof. exact (eq_refl (term57 A x s x')). Qed.
Lemma lem3807645 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term58 A x s x') = (term59 A x s x').
Proof. exact (MK_COMB (@lem3807644 A x s x') (@lem3807639 A x s x')). Qed.
Lemma lem3807646 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term44 A x s x') = (term58 A x s x').
Proof. exact (@lem17646 (term20 A s x' x) (s x')). Qed.
Lemma lem3807651 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term44 A x s x') = (term59 A x s x').
Proof. exact (TRANS (@lem3807646 A x s x') (@lem3807645 A x s x')). Qed.
Lemma lem3807658 {A : Type'} (s : A -> Prop) (x : A) (h1 : term7 A s x) : term7 A s x.
Proof. exact (h1). Qed.
Lemma lem3807720 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term44 A x s x') : term59 A x s x'.
Proof. exact (EQ_MP (@lem3807651 A x s x') (@lem3807604 A x s x' h1)). Qed.
Lemma lem3807721 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term60 A x s x') : term60 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3807722 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term56 A x s x') : term56 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3807724 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term60 A x s x') : term20 A s x' x.
Proof. exact (proj1 (@lem3807721 A x s x' h1)). Qed.
Lemma lem3807726 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term60 A x s x') : term16 A x s x'.
Proof. exact (proj1 (@lem3807724 A x s x' h1)). Qed.
Lemma lem3807730 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term56 A x s x') : term51 A s x' x.
Proof. exact (proj1 (@lem3807722 A x s x' h1)). Qed.
Lemma lem3807731 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term46 A x s x') : term46 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3807750 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3807766 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3807786 {A : Type'} (s : A -> Prop) (x : A) (h1 : term7 A s x) : term7 A s x.
Proof. exact (h1). Qed.
Lemma lem3807794 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3807800 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term60 A x s x') : term19 A x' x.
Proof. exact (proj2 (@lem3807724 A x s x' h1)). Qed.
Lemma lem3807802 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3807806 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term60 A x s x') : term7 A s x'.
Proof. exact (proj2 (@lem3807721 A x s x' h1)). Qed.
Lemma lem3807810 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3807818 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term46 A x s x') : term7 A s x'.
Proof. exact (proj2 (@lem3807731 A x s x' h1)). Qed.
Lemma lem3807820 {A : Type'} (s : A -> Prop) (x : A) (h1 : term7 A s x) : term7 A s x.
Proof. exact (h1). Qed.
Lemma lem3807822 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term56 A x s x') : s x'.
Proof. exact (proj2 (@lem3807722 A x s x' h1)). Qed.
Lemma lem3807824 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3807866 {A : Type'} (x : A) : (term61 A x) = (term61 A x).
Proof. exact (eq_refl (term61 A x)). Qed.
Lemma lem3807867 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term62 A x x') = (term63 A x).
Proof. exact (MK_COMB (@lem3807866 A x) (@lem3807802 A x' x h1)). Qed.
Lemma lem3807868 {A : Type'} (x : A) : (term63 A x) = (term64 A x).
Proof. exact (eq_refl (term63 A x)). Qed.
Lemma lem3807869 {A : Type'} (x : A) (x' : A) : (term65 A x x') = (term65 A x x').
Proof. exact (eq_refl (term65 A x x')). Qed.
Lemma lem3807870 {A : Type'} (x' : A) (x : A) : ((term62 A x x') = (term63 A x)) = ((term62 A x x') = (term64 A x)).
Proof. exact (MK_COMB (@lem3807869 A x x') (@lem3807868 A x)). Qed.
Lemma lem3807871 {A : Type'} (x' : A) (x : A) : (term62 A x x') = (term19 A x' x).
Proof. exact (eq_refl (term62 A x x')). Qed.
Lemma lem3807872 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3807873 {A : Type'} (x' : A) (x : A) : (term65 A x x') = (term66 A x' x).
Proof. exact (MK_COMB (@lem3807872) (@lem3807871 A x' x)). Qed.
Lemma lem3807874 {A : Type'} (x : A) : (term64 A x) = (term64 A x).
Proof. exact (eq_refl (term64 A x)). Qed.
Lemma lem3807875 {A : Type'} (x' : A) (x : A) : ((term62 A x x') = (term64 A x)) = ((term19 A x' x) = (term64 A x)).
Proof. exact (MK_COMB (@lem3807873 A x' x) (@lem3807874 A x)). Qed.
Lemma lem3807876 {A : Type'} (x' : A) (x : A) : ((term62 A x x') = (term63 A x)) = ((term19 A x' x) = (term64 A x)).
Proof. exact (TRANS (@lem3807870 A x' x) (@lem3807875 A x' x)). Qed.
Lemma lem3807877 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term19 A x' x) = (term64 A x).
Proof. exact (EQ_MP (@lem3807876 A x' x) (@lem3807867 A x' x h1)). Qed.
Lemma lem3807878 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term60 A x s x') (h2 : x' = x) : term64 A x.
Proof. exact (EQ_MP (@lem3807877 A x' x h2) (@lem3807800 A x s x' h1)). Qed.
Lemma lem3807906 {A : Type'} (s : A -> Prop) (x : A) (h1 : term7 A s x) : term7 A s x.
Proof. exact (h1). Qed.
Lemma lem3807907 {A : Type'} (s : A -> Prop) : (term67 A s) = (term67 A s).
Proof. exact (eq_refl (term67 A s)). Qed.
Lemma lem3807908 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term68 A s x') = (term68 A s x).
Proof. exact (MK_COMB (@lem3807907 A s) (@lem3807824 A x' x h1)). Qed.
Lemma lem3807909 {A : Type'} (s : A -> Prop) (x : A) : (term68 A s x) = (s x).
Proof. exact (eq_refl (term68 A s x)). Qed.
Lemma lem3807910 {A : Type'} (s : A -> Prop) (x' : A) : (term69 A s x') = (term69 A s x').
Proof. exact (eq_refl (term69 A s x')). Qed.
Lemma lem3807911 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term68 A s x') = (term68 A s x)) = ((term68 A s x') = (s x)).
Proof. exact (MK_COMB (@lem3807910 A s x') (@lem3807909 A s x)). Qed.
Lemma lem3807912 {A : Type'} (s : A -> Prop) (x' : A) : (term68 A s x') = (s x').
Proof. exact (eq_refl (term68 A s x')). Qed.
Lemma lem3807913 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3807914 {A : Type'} (s : A -> Prop) (x' : A) : (term69 A s x') = (term70 A s x').
Proof. exact (MK_COMB (@lem3807913) (@lem3807912 A s x')). Qed.
Lemma lem3807915 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3807916 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term68 A s x') = (s x)) = ((s x') = (s x)).
Proof. exact (MK_COMB (@lem3807914 A s x') (@lem3807915 A s x)). Qed.
Lemma lem3807917 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term68 A s x') = (term68 A s x)) = ((s x') = (s x)).
Proof. exact (TRANS (@lem3807911 A x' s x) (@lem3807916 A x' s x)). Qed.
Lemma lem3807918 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (s x') = (s x).
Proof. exact (EQ_MP (@lem3807917 A x' s x) (@lem3807908 A s x' x h1)). Qed.
Lemma lem3807935 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3807936 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3807935 A x). Qed.
Lemma lem3807937 {A : Type'} (x : A) : term71 A x.
Proof. exact (fun h0 : term64 A x => @lem3807936 A x). Qed.
Lemma lem3807939 (p : Prop) : (term72 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3807940 {A : Type'} (x : A) : (term71 A x) = (x = x).
Proof. exact (@lem3807939 (x = x)). Qed.
Lemma lem3807941 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3807940 A x) (@lem3807937 A x)). Qed.
Lemma lem3807944 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3807946 {A : Type'} (x : A) : (term64 A x) = (term73 A x).
Proof. exact (@lem3807944 (x = x)). Qed.
Lemma lem3807949 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term60 A x s x') (h2 : x' = x) : term73 A x.
Proof. exact (EQ_MP (@lem3807946 A x) (@lem3807878 A s x' x h1 h2)). Qed.
Lemma lem3807952 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term60 A x s x') (h2 : x' = x) : False.
Proof. exact (@lem3807949 A s x' x h1 h2 (@lem3807941 A x)). Qed.
Lemma lem3807953 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term60 A x s x') (h2 : x' = x) : term74.
Proof. exact (fun h0 : ~ False => @lem3807952 A s x' x h1 h2). Qed.
Lemma lem3807955 (p : Prop) : (term72 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3807956 : term74 = False.
Proof. exact (@lem3807955 False). Qed.
Lemma lem3807973 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3807974 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : term75 A s x'.
Proof. exact (fun h0 : term7 A s x' => @lem3807973 A s x' h1). Qed.
Lemma lem3807976 (p : Prop) : (term72 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3807977 {A : Type'} (s : A -> Prop) (x' : A) : (term75 A s x') = (s x').
Proof. exact (@lem3807976 (s x')). Qed.
Lemma lem3807978 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (EQ_MP (@lem3807977 A s x') (@lem3807974 A s x' h1)). Qed.
Lemma lem3807981 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3807983 {A : Type'} (s : A -> Prop) (x' : A) : (term7 A s x') = (term76 A s x').
Proof. exact (@lem3807981 (s x')). Qed.
Lemma lem3807986 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term60 A x s x') : term76 A s x'.
Proof. exact (EQ_MP (@lem3807983 A s x') (@lem3807806 A x s x' h1)). Qed.
Lemma lem3807989 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term60 A x s x') : False.
Proof. exact (@lem3807986 A x s x' h2 (@lem3807978 A s x' h1)). Qed.
Lemma lem3807990 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term60 A x s x') : term74.
Proof. exact (fun h0 : ~ False => @lem3807989 A x s x' h1 h2). Qed.
Lemma lem3807992 (p : Prop) : (term72 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3807993 : term74 = False.
Proof. exact (@lem3807992 False). Qed.
Lemma lem3807994 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term60 A x s x') : False.
Proof. exact (EQ_MP (@lem3807993) (@lem3807990 A x s x' h1 h2)). Qed.
Lemma lem3808010 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term56 A x s x') : s x'.
Proof. exact (proj2 (@lem3807722 A x s x' h1)). Qed.
Lemma lem3808011 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term56 A x s x') : term75 A s x'.
Proof. exact (fun h0 : term7 A s x' => @lem3808010 A x s x' h1). Qed.
Lemma lem3808013 (p : Prop) : (term72 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3808014 {A : Type'} (s : A -> Prop) (x' : A) : (term75 A s x') = (s x').
Proof. exact (@lem3808013 (s x')). Qed.
Lemma lem3808015 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term56 A x s x') : s x'.
Proof. exact (EQ_MP (@lem3808014 A s x') (@lem3808011 A x s x' h1)). Qed.
Lemma lem3808018 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3808020 {A : Type'} (s : A -> Prop) (x' : A) : (term7 A s x') = (term76 A s x').
Proof. exact (@lem3808018 (s x')). Qed.
Lemma lem3808023 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term46 A x s x') : term76 A s x'.
Proof. exact (EQ_MP (@lem3808020 A s x') (@lem3807818 A x s x' h1)). Qed.
Lemma lem3808026 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term46 A x s x') (h2 : term56 A x s x') : False.
Proof. exact (@lem3808023 A x s x' h1 (@lem3808015 A x s x' h2)). Qed.
Lemma lem3808027 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term46 A x s x') (h2 : term56 A x s x') : term74.
Proof. exact (fun h0 : ~ False => @lem3808026 A x s x' h1 h2). Qed.
Lemma lem3808029 (p : Prop) : (term72 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3808030 : term74 = False.
Proof. exact (@lem3808029 False). Qed.
Lemma lem3808031 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term46 A x s x') (h2 : term56 A x s x') : False.
Proof. exact (EQ_MP (@lem3808030) (@lem3808027 A x s x' h1 h2)). Qed.
Lemma lem3808033 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term56 A x s x') (h2 : x' = x) : s x.
Proof. exact (EQ_MP (@lem3807918 A s x' x h2) (@lem3807822 A x s x' h1)). Qed.
Lemma lem3808034 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term56 A x s x') (h2 : x' = x) : term75 A s x.
Proof. exact (fun h0 : term7 A s x => @lem3808033 A s x' x h1 h2). Qed.
Lemma lem3808036 (p : Prop) : (term72 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3808037 {A : Type'} (s : A -> Prop) (x : A) : (term75 A s x) = (s x).
Proof. exact (@lem3808036 (s x)). Qed.
Lemma lem3808038 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term56 A x s x') (h2 : x' = x) : s x.
Proof. exact (EQ_MP (@lem3808037 A s x) (@lem3808034 A s x' x h1 h2)). Qed.
Lemma lem3808041 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3808043 {A : Type'} (s : A -> Prop) (x : A) : (term7 A s x) = (term76 A s x).
Proof. exact (@lem3808041 (s x)). Qed.
Lemma lem3808046 {A : Type'} (s : A -> Prop) (x : A) (h1 : term7 A s x) : term76 A s x.
Proof. exact (EQ_MP (@lem3808043 A s x) (@lem3807906 A s x h1)). Qed.
Lemma lem3808049 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term7 A s x) (h2 : term56 A x s x') (h3 : x' = x) : False.
Proof. exact (@lem3808046 A s x h1 (@lem3808038 A s x' x h2 h3)). Qed.
Lemma lem3808050 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term7 A s x) (h2 : term56 A x s x') (h3 : x' = x) : term74.
Proof. exact (fun h0 : ~ False => @lem3808049 A s x' x h1 h2 h3). Qed.
Lemma lem3808052 (p : Prop) : (term72 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3808053 : term74 = False.
Proof. exact (@lem3808052 False). Qed.
Lemma lem3808054 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term7 A s x) (h2 : term56 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3808053) (@lem3808050 A s x' x h1 h2 h3)). Qed.
Lemma lem3808055 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term7 A s x) (h2 : term56 A x s x') (h3 : x' = x) : (term7 A s x) = False.
Proof. exact (prop_ext (fun h4 : term7 A s x => @lem3808054 A s x' x h1 h2 h3) (fun h4 : False => @lem3807906 A s x h1)). Qed.
Lemma lem3808057 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term7 A s x) (h2 : term56 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3808055 A s x' x h1 h2 h3) (@lem3807906 A s x h1)). Qed.
Lemma lem3808058 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term60 A x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3807956) (@lem3807953 A s x' x h1 h2)). Qed.
Lemma lem3808059 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term7 A s x) (h2 : term56 A x s x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3808057 A s x' x h1 h2 h3) (fun h4 : False => @lem3807824 A x' x h3)). Qed.
Lemma lem3808060 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term7 A s x) (h2 : term56 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3808059 A s x' x h1 h2 h3) (@lem3807824 A x' x h3)). Qed.
Lemma lem3808061 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term7 A s x) (h2 : term56 A x s x') (h3 : x' = x) : (term7 A s x) = False.
Proof. exact (prop_ext (fun h4 : term7 A s x => @lem3808060 A s x' x h1 h2 h3) (fun h4 : False => @lem3807820 A s x h1)). Qed.
Lemma lem3808062 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term7 A s x) (h2 : term56 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3808061 A s x' x h1 h2 h3) (@lem3807820 A s x h1)). Qed.
Lemma lem3808063 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term60 A x s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3807994 A x s x' h1 h2) (fun h3 : False => @lem3807810 A s x' h1)). Qed.
Lemma lem3808064 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term60 A x s x') : False.
Proof. exact (EQ_MP (@lem3808063 A x s x' h1 h2) (@lem3807810 A s x' h1)). Qed.
Lemma lem3808065 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term60 A x s x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3808058 A s x' x h1 h2) (fun h3 : False => @lem3807802 A x' x h2)). Qed.
Lemma lem3808066 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term60 A x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3808065 A s x' x h1 h2) (@lem3807802 A x' x h2)). Qed.
Lemma lem3808067 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term7 A s x) (h2 : term56 A x s x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3808062 A s x' x h1 h2 h3) (fun h4 : False => @lem3807794 A x' x h3)). Qed.
Lemma lem3808068 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term7 A s x) (h2 : term56 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3808067 A s x' x h1 h2 h3) (@lem3807794 A x' x h3)). Qed.
Lemma lem3808069 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term7 A s x) (h2 : term56 A x s x') (h3 : x' = x) : (term7 A s x) = False.
Proof. exact (prop_ext (fun h4 : term7 A s x => @lem3808068 A s x' x h1 h2 h3) (fun h4 : False => @lem3807786 A s x h1)). Qed.
Lemma lem3808070 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term7 A s x) (h2 : term56 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3808069 A s x' x h1 h2 h3) (@lem3807786 A s x h1)). Qed.
Lemma lem3808071 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term60 A x s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3808064 A x s x' h1 h2) (fun h3 : False => @lem3807766 A s x' h1)). Qed.
Lemma lem3808072 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term60 A x s x') : False.
Proof. exact (EQ_MP (@lem3808071 A x s x' h1 h2) (@lem3807766 A s x' h1)). Qed.
Lemma lem3808073 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term60 A x s x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3808066 A s x' x h1 h2) (fun h3 : False => @lem3807750 A x' x h2)). Qed.
Lemma lem3808074 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term60 A x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3808073 A s x' x h1 h2) (@lem3807750 A x' x h2)). Qed.
Lemma lem3808075 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term7 A s x) (h2 : term56 A x s x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3808070 A s x' x h1 h2 h3) (fun h4 : False => @lem3807794 A x' x h3)). Qed.
Lemma lem3808076 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term7 A s x) (h2 : term56 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3808075 A s x' x h1 h2 h3) (@lem3807794 A x' x h3)). Qed.
Lemma lem3808077 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term7 A s x) (h2 : term56 A x s x') (h3 : x' = x) : (term7 A s x) = False.
Proof. exact (prop_ext (fun h4 : term7 A s x => @lem3808076 A s x' x h1 h2 h3) (fun h4 : False => @lem3807786 A s x h1)). Qed.
Lemma lem3808078 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term7 A s x) (h2 : term56 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3808077 A s x' x h1 h2 h3) (@lem3807786 A s x h1)). Qed.
Lemma lem3808079 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term60 A x s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3808072 A x s x' h1 h2) (fun h3 : False => @lem3807766 A s x' h1)). Qed.
Lemma lem3808080 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term60 A x s x') : False.
Proof. exact (EQ_MP (@lem3808079 A x s x' h1 h2) (@lem3807766 A s x' h1)). Qed.
Lemma lem3808081 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term60 A x s x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3808074 A s x' x h1 h2) (fun h3 : False => @lem3807750 A x' x h2)). Qed.
Lemma lem3808082 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term60 A x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3808081 A s x' x h1 h2) (@lem3807750 A x' x h2)). Qed.
Lemma lem3808083 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term7 A s x) (h2 : term56 A x s x') : False.
Proof. exact (or_elim (@lem3807730 A x s x' h2) (fun h0 : term46 A x s x' => @lem3808031 A x s x' h0 h2) (fun h0 : x' = x => @lem3808078 A s x' x h1 h2 h0)). Qed.
Lemma lem3808084 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term60 A x s x') : False.
Proof. exact (or_elim (@lem3807726 A x s x' h1) (fun h0 : x' = x => @lem3808082 A s x' x h1 h0) (fun h0 : s x' => @lem3808080 A x s x' h0 h1)). Qed.
Lemma lem3808085 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term7 A s x) (h2 : term44 A x s x') : False.
Proof. exact (or_elim (@lem3807720 A x s x' h2) (fun h0 : term60 A x s x' => @lem3808084 A x s x' h0) (fun h0 : term56 A x s x' => @lem3808083 A x s x' h1 h0)). Qed.
Lemma lem3808086 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term7 A s x) (h2 : term44 A x s x') : (term7 A s x) = False.
Proof. exact (prop_ext (fun h3 : term7 A s x => @lem3808085 A x s x' h1 h2) (fun h3 : False => @lem3807658 A s x h1)). Qed.
Lemma lem3808087 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term7 A s x) (h2 : term44 A x s x') : False.
Proof. exact (EQ_MP (@lem3808086 A x s x' h1 h2) (@lem3807658 A s x h1)). Qed.
Lemma lem3808088 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term7 A s x) (h2 : term44 A x s x') : (term7 A s x) = False.
Proof. exact (prop_ext (fun h3 : term7 A s x => @lem3808087 A x s x' h1 h2) (fun h3 : False => @lem3807610 A s x h1)). Qed.
Lemma lem3808089 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term7 A s x) (h2 : term44 A x s x') : False.
Proof. exact (EQ_MP (@lem3808088 A x s x' h1 h2) (@lem3807610 A s x h1)). Qed.
Lemma lem3808090 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term7 A s x) (h2 : term44 A x s x') : (term44 A x s x') = False.
Proof. exact (prop_ext (fun h3 : term44 A x s x' => @lem3808089 A x s x' h1 h2) (fun h3 : False => @lem3807604 A x s x' h2)). Qed.
Lemma lem3808091 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term7 A s x) (h2 : term44 A x s x') : False.
Proof. exact (EQ_MP (@lem3808090 A x s x' h1 h2) (@lem3807604 A x s x' h2)). Qed.
Lemma lem3808092 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term7 A s x) : term43 A x s x'.
Proof. exact (fun h0 : term44 A x s x' => @lem3808091 A x s x' h1 h0). Qed.
Lemma lem3808093 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term7 A s x) : (term20 A s x' x) = (s x').
Proof. exact (EQ_MP (@lem3807603 A x s x') (@lem3808092 A x' s x h1)). Qed.
Lemma lem3808098 {A : Type'} (s : A -> Prop) (x : A) (h1 : term7 A s x) : term25 A x s.
Proof. exact (fun x' : A => @lem3808093 A x' s x h1). Qed.
Lemma lem3808099 {A : Type'} (x : A) (s : A -> Prop) : term26 A x s.
Proof. exact (fun h0 : term7 A s x => @lem3808098 A s x h0). Qed.
Lemma lem3808104 {A : Type'} (s : A -> Prop) : term38 A s.
Proof. exact (fun x : A => @lem3808099 A x s). Qed.
Lemma lem3808109 {A : Type'} : term42 A.
Proof. exact (fun s : A -> Prop => @lem3808104 A s). Qed.
Lemma lem3808110 {A : Type'} : term41 A.
Proof. exact (EQ_MP (@lem3807598 A) (@lem3808109 A)). Qed.
Lemma lem3808111 {A : Type'} (s : A -> Prop) : term77 A s.
Proof. exact (@lem3808110 A s). Qed.
Lemma lem3808112 {A : Type'} (s : A -> Prop) : (term77 A s) = (term37 A s).
Proof. exact (eq_refl (term77 A s)). Qed.
Lemma lem3808113 {A : Type'} (s : A -> Prop) : term37 A s.
Proof. exact (EQ_MP (@lem3808112 A s) (@lem3808111 A s)). Qed.
Lemma lem3808114 {A : Type'} (s : A -> Prop) (x : A) : term78 A s x.
Proof. exact (@lem3808113 A s x). Qed.
Lemma lem3808115 {A : Type'} (x : A) (s : A -> Prop) : (term78 A s x) = (term28 A x s).
Proof. exact (eq_refl (term78 A s x)). Qed.
Lemma lem3808116 {A : Type'} (x : A) (s : A -> Prop) : term28 A x s.
Proof. exact (EQ_MP (@lem3808115 A x s) (@lem3808114 A s x)). Qed.
Lemma lem3808118 {A : Type'} (x : A) (s : A -> Prop) : term28 A x s.
Proof. exact (@lem3807497 A x s (@lem3808116 A x s)). Qed.
Lemma lem3808119 {A : Type'} (x : A) (s : A -> Prop) (h1 : term29 A x s) : False.
Proof. exact (@lem3808118 A x s (@lem3807481 A x s h1)). Qed.
Lemma lem3808120 {A : Type'} (x : A) (s : A -> Prop) (h1 : term29 A x s) : (term29 A x s) = False.
Proof. exact (prop_ext (fun h2 : term29 A x s => @lem3808119 A x s h1) (fun h2 : False => @lem3807481 A x s h1)). Qed.
Lemma lem3808121 {A : Type'} (x : A) (s : A -> Prop) (h1 : term29 A x s) : False.
Proof. exact (EQ_MP (@lem3808120 A x s h1) (@lem3807481 A x s h1)). Qed.
Lemma lem3808122 {A : Type'} (x : A) (s : A -> Prop) : term28 A x s.
Proof. exact (fun h0 : term29 A x s => @lem3808121 A x s h0). Qed.
Lemma lem3808123 {A : Type'} (x : A) (s : A -> Prop) : term26 A x s.
Proof. exact (EQ_MP (@lem3807480 A x s) (@lem3808122 A x s)). Qed.
Lemma lem3808124 {A : Type'} (x : A) (s : A -> Prop) : term5 A x s.
Proof. exact (EQ_MP (@lem3807476 A x s) (@lem3808123 A x s)). Qed.
Lemma lem3808130 {A : Type'} (h1 : term79 A) : term79 A.
Proof. exact (h1). Qed.
Lemma lem3808131 {A : Type'} (P : type686 A) (h1 : term79 A) : term80 A P.
Proof. exact (@lem3808130 A h1 P). Qed.
Lemma lem3808132 {A : Type'} (P : type686 A) : (term80 A P) = (term81 A P).
Proof. exact (eq_refl (term80 A P)). Qed.
Lemma lem3808133 {A : Type'} (P : type686 A) (h1 : term79 A) : term81 A P.
Proof. exact (EQ_MP (@lem3808132 A P) (@lem3808131 A P h1)). Qed.
Lemma lem3808134 {A : Type'} (P : type686 A) (h1 : term82 A P) : term82 A P.
Proof. exact (h1). Qed.
Lemma lem3808135 {A : Type'} (P : type686 A) (h1 : term79 A) (h2 : term82 A P) : term83 A P.
Proof. exact (@lem3808133 A P h1 (@lem3808134 A P h2)). Qed.
Lemma lem3808136 {A : Type'} (P : type686 A) (h1 : term82 A P) : term84 A P.
Proof. exact (fun h0 : term79 A => @lem3808135 A P h0 h1). Qed.
Lemma lem3808137 {A : Type'} (h1 : term79 A) : term79 A.
Proof. exact (h1). Qed.
Lemma lem3808138 {A : Type'} (P : type686 A) (h1 : term79 A) (h2 : term82 A P) : term83 A P.
Proof. exact (@lem3808136 A P h2 (@lem3808137 A h1)). Qed.
Lemma lem3808139 {A : Type'} (P : type686 A) (h1 : term79 A) : term81 A P.
Proof. exact (fun h0 : term82 A P => @lem3808138 A P h1 h0). Qed.
Lemma lem3808140 {A : Type'} (h1 : term79 A) : term79 A.
Proof. exact (fun P : type686 A => @lem3808139 A P h1). Qed.
Lemma lem3808141 {A : Type'} : term85 A.
Proof. exact (fun h0 : term79 A => @lem3808140 A h0). Qed.
Lemma lem3808142 {A : Type'} : term79 A.
Proof. exact (@lem3808141 A (@lem3558722 A)). Qed.
Lemma lem3808143 {A : Type'} (P : type686 A) : term80 A P.
Proof. exact (@lem3808142 A P). Qed.
Lemma lem3808144 {A : Type'} (P : type686 A) : (term80 A P) = (term81 A P).
Proof. exact (eq_refl (term80 A P)). Qed.
Lemma lem3808147 {A : Type'} (P : type686 A) : term81 A P.
Proof. exact (EQ_MP (@lem3808144 A P) (@lem3808143 A P)). Qed.
Lemma lem3808148 {A : Type'} (P : type686 A) : term81 A P.
Proof. exact (@lem3808147 A P). Qed.
Lemma lem3808149 {A B : Type'} (f : type1411 A B) (b : B) : term86 A B f b.
Proof. exact (@lem3808148 A (term87 A B f b)). Qed.
Lemma lem3808150 {A B : Type'} (f : type1411 A B) (b : B) : (term88 A B f b) = (term89 A B f b).
Proof. exact (eq_refl (term88 A B f b)). Qed.
Lemma lem3808151 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3808152 {A B : Type'} (f : type1411 A B) (b : B) : (term90 A B f b) = (term91 A B f b).
Proof. exact (MK_COMB (@lem3808151) (@lem3808150 A B f b)). Qed.
Lemma lem3808153 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) : (term92 A B f b s) = (term93 A B f b s).
Proof. exact (eq_refl (term92 A B f b s)). Qed.
Lemma lem3808154 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3808155 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) : (term94 A B f b s) = (term95 A B f b s).
Proof. exact (MK_COMB (@lem3808154) (@lem3808153 A B f b s)). Qed.
Lemma lem3808156 {A : Type'} (x : A) (s : A -> Prop) : (term96 A x s) = (term96 A x s).
Proof. exact (eq_refl (term96 A x s)). Qed.
Lemma lem3808157 {A B : Type'} (f : type1411 A B) (b : B) (x : A) (s : A -> Prop) : (term97 A B f b x s) = (term98 A B f b x s).
Proof. exact (MK_COMB (@lem3808155 A B f b s) (@lem3808156 A x s)). Qed.
Lemma lem3808158 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3808159 {A B : Type'} (f : type1411 A B) (b : B) (x : A) (s : A -> Prop) : (term99 A B f b x s) = (term100 A B f b x s).
Proof. exact (MK_COMB (@lem3808158) (@lem3808157 A B f b x s)). Qed.
Lemma lem3808160 {A B : Type'} (f : type1411 A B) (b : B) (x : A) (s : A -> Prop) : (term101 A B f b x s) = (term102 A B f b x s).
Proof. exact (eq_refl (term101 A B f b x s)). Qed.
Lemma lem3808161 {A B : Type'} (f : type1411 A B) (b : B) (x : A) (s : A -> Prop) : (term103 A B f b x s) = (term104 A B f b x s).
Proof. exact (MK_COMB (@lem3808159 A B f b x s) (@lem3808160 A B f b x s)). Qed.
Lemma lem3808162 {A B : Type'} (f : type1411 A B) (b : B) (x : A) : (term105 A B f b x) = (term106 A B f b x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3808161 A B f b x s)). Qed.
Lemma lem3808163 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3808164 {A B : Type'} (f : type1411 A B) (b : B) (x : A) : (term107 A B f b x) = (term108 A B f b x).
Proof. exact (MK_COMB (@lem3808163 A) (@lem3808162 A B f b x)). Qed.
Lemma lem3808165 {A B : Type'} (f : type1411 A B) (b : B) : (term109 A B f b) = (term110 A B f b).
Proof. exact (fun_ext (fun x : A => @lem3808164 A B f b x)). Qed.
Lemma lem3808166 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3808167 {A B : Type'} (f : type1411 A B) (b : B) : (term111 A B f b) = (term112 A B f b).
Proof. exact (MK_COMB (@lem3808166 A) (@lem3808165 A B f b)). Qed.
Lemma lem3808168 {A B : Type'} (f : type1411 A B) (b : B) : (term113 A B f b) = (term114 A B f b).
Proof. exact (MK_COMB (@lem3808152 A B f b) (@lem3808167 A B f b)). Qed.
Lemma lem3808169 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3808170 {A B : Type'} (f : type1411 A B) (b : B) : (term115 A B f b) = (term116 A B f b).
Proof. exact (MK_COMB (@lem3808169) (@lem3808168 A B f b)). Qed.
Lemma lem3808171 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) : (term92 A B f b s) = (term93 A B f b s).
Proof. exact (eq_refl (term92 A B f b s)). Qed.
Lemma lem3808172 {A : Type'} (s : A -> Prop) : (term117 A s) = (term117 A s).
Proof. exact (eq_refl (term117 A s)). Qed.
Lemma lem3808173 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) : (term118 A B f b s) = (term119 A B f b s).
Proof. exact (MK_COMB (@lem3808172 A s) (@lem3808171 A B f b s)). Qed.
Lemma lem3808174 {A B : Type'} (f : type1411 A B) (b : B) : (term120 A B f b) = (term121 A B f b).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3808173 A B f b s)). Qed.
Lemma lem3808175 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3808176 {A B : Type'} (f : type1411 A B) (b : B) : (term122 A B f b) = (term123 A B f b).
Proof. exact (MK_COMB (@lem3808175 A) (@lem3808174 A B f b)). Qed.
Lemma lem3808177 {A B : Type'} (f : type1411 A B) (b : B) : (term86 A B f b) = (term124 A B f b).
Proof. exact (MK_COMB (@lem3808170 A B f b) (@lem3808176 A B f b)). Qed.
Lemma lem3808178 {A B : Type'} (f : type1411 A B) (b : B) : term124 A B f b.
Proof. exact (EQ_MP (@lem3808177 A B f b) (@lem3808149 A B f b)). Qed.
Lemma lem3808179 {A B : Type'} (f : type1411 A B) (b : B) (x : A) (s : A -> Prop) (h1 : term98 A B f b x s) : term98 A B f b x s.
Proof. exact (h1). Qed.
Lemma lem3808180 {A : Type'} (x : A) (s : A -> Prop) (h1 : term96 A x s) : term96 A x s.
Proof. exact (h1). Qed.
Lemma lem3808181 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (h1 : term93 A B f b s) : term93 A B f b s.
Proof. exact (h1). Qed.
Lemma lem3808182 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) (h1 : term125 A B f b s a) : term125 A B f b s a.
Proof. exact (h1). Qed.
Lemma lem3808183 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) (n : nat) (h1 : @FINREC A B f b s a n) : @FINREC A B f b s a n.
Proof. exact (h1). Qed.
Lemma lem3808185 {A : Type'} (x : A) (s : A -> Prop) (h1 : term6 A x s) : term6 A x s.
Proof. exact (h1). Qed.
Lemma lem3808187 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (a : B) (b : B) : (term126 A B f b s a) = (term127 A B s a b).
Proof. exact (EQ_MP (@lem3791010 A B f s a b) (@lem3791009 A B f s a b)). Qed.
Lemma lem3808188 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (a : B) (b : B) : (term126 A B f b s a) = (term127 A B s a b).
Proof. exact (@lem3808187 A B f s a b). Qed.
Lemma lem3808189 {A B : Type'} (f : type1411 A B) (b : B) : (term128 A B f b) = (term129 A B b).
Proof. exact (@lem3808188 A B f (@EMPTY A) b b). Qed.
Lemma lem3808193 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3808194 {A : Type'} (x : A -> Prop) : (x = x) = True.
Proof. exact (@lem3808193 (A -> Prop) x). Qed.
Lemma lem3808195 {A : Type'} : ((@EMPTY A) = (@EMPTY A)) = True.
Proof. exact (@lem3808194 A (@EMPTY A)). Qed.
Lemma lem3808196 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3808197 {A : Type'} : (term130 A) = (and True).
Proof. exact (MK_COMB (@lem3808196) (@lem3808195 A)). Qed.
Lemma lem3808199 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3808200 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem3808199 B x). Qed.
Lemma lem3808201 {B : Type'} (b : B) : (b = b) = True.
Proof. exact (@lem3808200 B b). Qed.
Lemma lem3808202 {A B : Type'} (b : B) : (term129 A B b) = (True /\ True).
Proof. exact (MK_COMB (@lem3808197 A) (@lem3808201 B b)). Qed.
Lemma lem3808204 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3808205 : (True /\ True) = True.
Proof. exact (@lem3808204 True). Qed.
Lemma lem3808206 {A B : Type'} (b : B) : (term129 A B b) = True.
Proof. exact (TRANS (@lem3808202 A B b) (@lem3808205)). Qed.
Lemma lem3808207 {A B : Type'} (f : type1411 A B) (b : B) : (term128 A B f b) = True.
Proof. exact (TRANS (@lem3808189 A B f b) (@lem3808206 A B b)). Qed.
Lemma lem3808208 {A B : Type'} (f : type1411 A B) (b : B) : True = (term128 A B f b).
Proof. exact (SYM (@lem3808207 A B f b)). Qed.
Lemma lem3808209 {A B : Type'} (f : type1411 A B) (b : B) : term128 A B f b.
Proof. exact (EQ_MP (@lem3808208 A B f b) (@lem0)). Qed.
Lemma lem3808210 {A B : Type'} (f : type1411 A B) (b : B) : term131 A B f b.
Proof. exact (ex_intro (term132 A B f b) (NUMERAL 0) (@lem3808209 A B f b)). Qed.
Lemma lem3808211 {A B : Type'} (f : type1411 A B) (b : B) : term89 A B f b.
Proof. exact (ex_intro (term133 A B f b) b (@lem3808210 A B f b)). Qed.
Lemma lem3808213 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (a : B) (f : type1411 A B) : (term134 A B f b s a n) = (term135 A B b s n a f).
Proof. exact (EQ_MP (@lem3791025 A B b s n a f) (@lem3791024 A B b s n a f)). Qed.
Lemma lem3808214 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (a : B) (f : type1411 A B) : (term134 A B f b s a n) = (term135 A B b s n a f).
Proof. exact (@lem3808213 A B b s n a f). Qed.
Lemma lem3808215 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (x : A) (a : B) (f : type1411 A B) : (term136 A B b s f x a n) = (term137 A B b s n x a f).
Proof. exact (@lem3808214 A B b (@INSERT A x s) n (f x a) f). Qed.
Lemma lem3808230 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (a : B) (n : nat) : (term137 A B b s n x a f) = (term136 A B b s f x a n).
Proof. exact (SYM (@lem3808215 A B b s n x a f)). Qed.
Lemma lem3808234 {A : Type'} (x : A) (s : A -> Prop) : term4 A x s.
Proof. exact (EQ_MP (@lem3807408 A x s) (@lem3808124 A x s)). Qed.
Lemma lem3808235 {A : Type'} (x : A) (s : A -> Prop) : term4 A x s.
Proof. exact (@lem3808234 A x s). Qed.
Lemma lem3808237 {A : Type'} (x : A) : term138 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem3808238 {A : Type'} (x : A) : (term138 A x) = (term139 A x).
Proof. exact (eq_refl (term138 A x)). Qed.
Lemma lem3808239 {A : Type'} (x : A) : term139 A x.
Proof. exact (EQ_MP (@lem3808238 A x) (@lem3808237 A x)). Qed.
Lemma lem3808240 {A : Type'} (x : A) (y : A) : term140 A x y.
Proof. exact (@lem3808239 A x y). Qed.
Lemma lem3808241 {A : Type'} (y : A) (x : A) : (term140 A x y) = (term141 A y x).
Proof. exact (eq_refl (term140 A x y)). Qed.
Lemma lem3808242 {A : Type'} (y : A) (x : A) : term141 A y x.
Proof. exact (EQ_MP (@lem3808241 A y x) (@lem3808240 A x y)). Qed.
Lemma lem3808243 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term142 A y x s.
Proof. exact (@lem3808242 A y x s). Qed.
Lemma lem3808244 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term142 A y x s) = ((term13 A x y s) = (term14 A y x s)).
Proof. exact (eq_refl (term142 A y x s)). Qed.
Lemma lem3808246 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) (n : nat) : (@FINREC A B f b s a n) = ((@FINREC A B f b s a n) = True).
Proof. exact (@lem7 (@FINREC A B f b s a n)). Qed.
Lemma lem3808248 {A : Type'} (x : A) (s : A -> Prop) : term143 A x s.
Proof. exact (@lem82 (@IN A x s)). Qed.
Lemma lem3808255 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term13 A x y s) = (term14 A y x s).
Proof. exact (EQ_MP (@lem3808244 A y x s) (@lem3808243 A y x s)). Qed.
Lemma lem3808256 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term13 A x y s) = (term14 A y x s).
Proof. exact (@lem3808255 A y x s). Qed.
Lemma lem3808257 {A : Type'} (x : A) (s : A -> Prop) : (term144 A x s) = (term145 A x s).
Proof. exact (@lem3808256 A x x s). Qed.
Lemma lem3808261 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3808262 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem3808261 A x). Qed.
Lemma lem3808263 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3808264 {A : Type'} (x : A) : (term146 A x) = (or True).
Proof. exact (MK_COMB (@lem3808263) (@lem3808262 A x)). Qed.
Lemma lem3808266 {A : Type'} (x : A) (s : A -> Prop) (h1 : term6 A x s) : (@IN A x s) = False.
Proof. exact (@lem3808248 A x s (@lem3808185 A x s h1)). Qed.
Lemma lem3808267 {A : Type'} (x : A) (s : A -> Prop) (h1 : term6 A x s) : (term145 A x s) = (True \/ False).
Proof. exact (MK_COMB (@lem3808264 A x) (@lem3808266 A x s h1)). Qed.
Lemma lem3808269 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem3808270 : (True \/ False) = True.
Proof. exact (@lem3808269 False). Qed.
Lemma lem3808271 {A : Type'} (x : A) (s : A -> Prop) (h1 : term6 A x s) : (term145 A x s) = True.
Proof. exact (TRANS (@lem3808267 A x s h1) (@lem3808270)). Qed.
Lemma lem3808272 {A : Type'} (x : A) (s : A -> Prop) (h1 : term6 A x s) : (term144 A x s) = True.
Proof. exact (TRANS (@lem3808257 A x s) (@lem3808271 A x s h1)). Qed.
Lemma lem3808273 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3808274 {A : Type'} (x : A) (s : A -> Prop) (h1 : term6 A x s) : (term147 A x s) = (and True).
Proof. exact (MK_COMB (@lem3808273) (@lem3808272 A x s h1)). Qed.
Lemma lem3808278 {A : Type'} (x : A) (s : A -> Prop) (h1 : term6 A x s) : (term1 A s x) = s.
Proof. exact (@lem3808235 A x s (@lem3808185 A x s h1)). Qed.
Lemma lem3808279 {A B : Type'} (f : type1411 A B) (b : B) : (@FINREC A B f b) = (@FINREC A B f b).
Proof. exact (eq_refl (@FINREC A B f b)). Qed.
Lemma lem3808280 {A B : Type'} (f : type1411 A B) (b : B) (x : A) (s : A -> Prop) (h1 : term6 A x s) : (term148 A B f b s x) = (@FINREC A B f b s).
Proof. exact (MK_COMB (@lem3808279 A B f b) (@lem3808278 A x s h1)). Qed.
Lemma lem3808281 {B : Type'} (a : B) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3808282 {A B : Type'} (f : type1411 A B) (b : B) (a : B) (x : A) (s : A -> Prop) (h1 : term6 A x s) : (term149 A B f b s x a) = (@FINREC A B f b s a).
Proof. exact (MK_COMB (@lem3808280 A B f b x s h1) (@lem3808281 B a)). Qed.
Lemma lem3808283 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem3808284 {A B : Type'} (f : type1411 A B) (b : B) (a : B) (n : nat) (x : A) (s : A -> Prop) (h1 : term6 A x s) : (term150 A B f b s x a n) = (@FINREC A B f b s a n).
Proof. exact (MK_COMB (@lem3808282 A B f b a x s h1) (@lem3808283 n)). Qed.
Lemma lem3808286 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) (n : nat) (h1 : @FINREC A B f b s a n) : (@FINREC A B f b s a n) = True.
Proof. exact (EQ_MP (@lem3808246 A B f b s a n) (@lem3808183 A B f b s a n h1)). Qed.
Lemma lem3808287 {A B : Type'} (x : A) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) (n : nat) (h1 : term6 A x s) (h2 : @FINREC A B f b s a n) : (term150 A B f b s x a n) = True.
Proof. exact (TRANS (@lem3808284 A B f b a n x s h1) (@lem3808286 A B f b s a n h2)). Qed.
Lemma lem3808288 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3808289 {A B : Type'} (x : A) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) (n : nat) (h1 : term6 A x s) (h2 : @FINREC A B f b s a n) : (term151 A B f b s x a n) = (and True).
Proof. exact (MK_COMB (@lem3808288) (@lem3808287 A B x f b s a n h1 h2)). Qed.
Lemma lem3808291 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3808292 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem3808291 B x). Qed.
Lemma lem3808293 {A B : Type'} (f : type1411 A B) (x : A) (a : B) : ((f x a) = (f x a)) = True.
Proof. exact (@lem3808292 B (f x a)). Qed.
Lemma lem3808294 {A B : Type'} (x : A) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) (n : nat) (h1 : term6 A x s) (h2 : @FINREC A B f b s a n) : (term152 A B b s n f x a) = (True /\ True).
Proof. exact (MK_COMB (@lem3808289 A B x f b s a n h1 h2) (@lem3808293 A B f x a)). Qed.
Lemma lem3808296 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3808297 : (True /\ True) = True.
Proof. exact (@lem3808296 True). Qed.
Lemma lem3808298 {A B : Type'} (x : A) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) (n : nat) (h1 : term6 A x s) (h2 : @FINREC A B f b s a n) : (term152 A B b s n f x a) = True.
Proof. exact (TRANS (@lem3808294 A B x f b s a n h1 h2) (@lem3808297)). Qed.
Lemma lem3808299 {A B : Type'} (x : A) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) (n : nat) (h1 : term6 A x s) (h2 : @FINREC A B f b s a n) : (term153 A B b s n f x a) = (True /\ True).
Proof. exact (MK_COMB (@lem3808274 A x s h1) (@lem3808298 A B x f b s a n h1 h2)). Qed.
Lemma lem3808301 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3808302 : (True /\ True) = True.
Proof. exact (@lem3808301 True). Qed.
Lemma lem3808303 {A B : Type'} (x : A) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) (n : nat) (h1 : term6 A x s) (h2 : @FINREC A B f b s a n) : (term153 A B b s n f x a) = True.
Proof. exact (TRANS (@lem3808299 A B x f b s a n h1 h2) (@lem3808302)). Qed.
Lemma lem3808304 {A B : Type'} (x : A) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) (n : nat) (h1 : term6 A x s) (h2 : @FINREC A B f b s a n) : True = (term153 A B b s n f x a).
Proof. exact (SYM (@lem3808303 A B x f b s a n h1 h2)). Qed.
Lemma lem3808305 {A B : Type'} (x : A) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) (n : nat) (h1 : term6 A x s) (h2 : @FINREC A B f b s a n) : term153 A B b s n f x a.
Proof. exact (EQ_MP (@lem3808304 A B x f b s a n h1 h2) (@lem0)). Qed.
Lemma lem3808306 {A B : Type'} (x : A) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) (n : nat) (h1 : term6 A x s) (h2 : @FINREC A B f b s a n) : term154 A B b s n a f x.
Proof. exact (ex_intro (term155 A B b s n a f x) a (@lem3808305 A B x f b s a n h1 h2)). Qed.
Lemma lem3808307 {A B : Type'} (x : A) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) (n : nat) (h1 : term6 A x s) (h2 : @FINREC A B f b s a n) : term137 A B b s n x a f.
Proof. exact (ex_intro (term156 A B b s n x a f) x (@lem3808306 A B x f b s a n h1 h2)). Qed.
Lemma lem3808308 {A B : Type'} (x : A) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) (n : nat) (h1 : term6 A x s) (h2 : @FINREC A B f b s a n) : term136 A B b s f x a n.
Proof. exact (EQ_MP (@lem3808230 A B b s f x a n) (@lem3808307 A B x f b s a n h1 h2)). Qed.
Lemma lem3808309 {A B : Type'} (x : A) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) (n : nat) (h1 : term6 A x s) (h2 : @FINREC A B f b s a n) : term157 A B b s f x a.
Proof. exact (ex_intro (term158 A B b s f x a) (S n) (@lem3808308 A B x f b s a n h1 h2)). Qed.
Lemma lem3808310 {A B : Type'} (x : A) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) (n : nat) (h1 : term6 A x s) (h2 : @FINREC A B f b s a n) : term102 A B f b x s.
Proof. exact (ex_intro (term159 A B f b x s) (f x a) (@lem3808309 A B x f b s a n h1 h2)). Qed.
Lemma lem3808311 {A B : Type'} (f : type1411 A B) (b : B) (x : A) (s : A -> Prop) (h1 : term98 A B f b x s) : term96 A x s.
Proof. exact (proj2 (@lem3808179 A B f b x s h1)). Qed.
Lemma lem3808312 {A B : Type'} (f : type1411 A B) (b : B) (x : A) (s : A -> Prop) (h1 : term98 A B f b x s) : term93 A B f b s.
Proof. exact (proj1 (@lem3808179 A B f b x s h1)). Qed.
Lemma lem3808314 {A : Type'} (x : A) (s : A -> Prop) (h1 : term96 A x s) : term6 A x s.
Proof. exact (proj1 (@lem3808180 A x s h1)). Qed.
Lemma lem3808315 {A B : Type'} (x : A) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) (n : nat) (h1 : term6 A x s) (h2 : @FINREC A B f b s a n) : (term6 A x s) = (term102 A B f b x s).
Proof. exact (prop_ext (fun h3 : term6 A x s => @lem3808310 A B x f b s a n h1 h2) (fun h3 : term102 A B f b x s => @lem3808185 A x s h1)). Qed.
Lemma lem3808316 {A B : Type'} (x : A) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) (n : nat) (h1 : term6 A x s) (h2 : @FINREC A B f b s a n) : term102 A B f b x s.
Proof. exact (EQ_MP (@lem3808315 A B x f b s a n h1 h2) (@lem3808185 A x s h1)). Qed.
Lemma lem3808317 {A B : Type'} (x : A) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) (n : nat) (h1 : term96 A x s) (h2 : @FINREC A B f b s a n) : (term6 A x s) = (term102 A B f b x s).
Proof. exact (prop_ext (fun h3 : term6 A x s => @lem3808316 A B x f b s a n h3 h2) (fun h3 : term102 A B f b x s => @lem3808314 A x s h1)). Qed.
Lemma lem3808318 {A B : Type'} (x : A) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) (n : nat) (h1 : term96 A x s) (h2 : @FINREC A B f b s a n) : term102 A B f b x s.
Proof. exact (EQ_MP (@lem3808317 A B x f b s a n h1 h2) (@lem3808314 A x s h1)). Qed.
Lemma lem3808319 {A B : Type'} (x : A) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) (n : nat) (h1 : term96 A x s) (h2 : @FINREC A B f b s a n) : (@FINREC A B f b s a n) = (term102 A B f b x s).
Proof. exact (prop_ext (fun h3 : @FINREC A B f b s a n => @lem3808318 A B x f b s a n h1 h2) (fun h3 : term102 A B f b x s => @lem3808183 A B f b s a n h2)). Qed.
Lemma lem3808320 {A B : Type'} (x : A) (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) (n : nat) (h1 : term96 A x s) (h2 : @FINREC A B f b s a n) : term102 A B f b x s.
Proof. exact (EQ_MP (@lem3808319 A B x f b s a n h1 h2) (@lem3808183 A B f b s a n h2)). Qed.
Lemma lem3808321 {A B : Type'} (f : type1411 A B) (b : B) (a : B) (x : A) (s : A -> Prop) (h1 : term125 A B f b s a) (h2 : term96 A x s) : term102 A B f b x s.
Proof. exact (ex_elim (@lem3808182 A B f b s a h1) (fun n : nat => fun h0 : term160 A B f b s a n => @lem3808320 A B x f b s a n h2 h0)). Qed.
Lemma lem3808322 {A B : Type'} (f : type1411 A B) (b : B) (x : A) (s : A -> Prop) (h1 : term93 A B f b s) (h2 : term96 A x s) : term102 A B f b x s.
Proof. exact (ex_elim (@lem3808181 A B f b s h1) (fun a : B => fun h0 : term161 A B f b s a => @lem3808321 A B f b a x s h0 h2)). Qed.
Lemma lem3808323 {A B : Type'} (f : type1411 A B) (b : B) (x : A) (s : A -> Prop) (h1 : term93 A B f b s) (h2 : term98 A B f b x s) : (term96 A x s) = (term102 A B f b x s).
Proof. exact (prop_ext (fun h3 : term96 A x s => @lem3808322 A B f b x s h1 h3) (fun h3 : term102 A B f b x s => @lem3808311 A B f b x s h2)). Qed.
Lemma lem3808324 {A B : Type'} (f : type1411 A B) (b : B) (x : A) (s : A -> Prop) (h1 : term93 A B f b s) (h2 : term98 A B f b x s) : term102 A B f b x s.
Proof. exact (EQ_MP (@lem3808323 A B f b x s h1 h2) (@lem3808311 A B f b x s h2)). Qed.
Lemma lem3808325 {A B : Type'} (f : type1411 A B) (b : B) (x : A) (s : A -> Prop) (h1 : term98 A B f b x s) : (term93 A B f b s) = (term102 A B f b x s).
Proof. exact (prop_ext (fun h2 : term93 A B f b s => @lem3808324 A B f b x s h2 h1) (fun h2 : term102 A B f b x s => @lem3808312 A B f b x s h1)). Qed.
Lemma lem3808326 {A B : Type'} (f : type1411 A B) (b : B) (x : A) (s : A -> Prop) (h1 : term98 A B f b x s) : term102 A B f b x s.
Proof. exact (EQ_MP (@lem3808325 A B f b x s h1) (@lem3808312 A B f b x s h1)). Qed.
Lemma lem3808327 {A B : Type'} (f : type1411 A B) (b : B) (x : A) (s : A -> Prop) : term104 A B f b x s.
Proof. exact (fun h0 : term98 A B f b x s => @lem3808326 A B f b x s h0). Qed.
Lemma lem3808332 {A B : Type'} (f : type1411 A B) (b : B) (x : A) : term108 A B f b x.
Proof. exact (fun s : A -> Prop => @lem3808327 A B f b x s). Qed.
Lemma lem3808337 {A B : Type'} (f : type1411 A B) (b : B) : term112 A B f b.
Proof. exact (fun x : A => @lem3808332 A B f b x). Qed.
Lemma lem3808338 {A B : Type'} (f : type1411 A B) (b : B) : term114 A B f b.
Proof. exact (conj (@lem3808211 A B f b) (@lem3808337 A B f b)). Qed.
Lemma lem3808339 {A B : Type'} (f : type1411 A B) (b : B) : term123 A B f b.
Proof. exact (@lem3808178 A B f b (@lem3808338 A B f b)). Qed.
Lemma lem3808344 {A B : Type'} (f : type1411 A B) : term162 A B f.
Proof. exact (fun b : B => @lem3808339 A B f b). Qed.
Lemma lem3808349 {A B : Type'} : term163 A B.
Proof. exact (fun f : type1411 A B => @lem3808344 A B f). Qed.
