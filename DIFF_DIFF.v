Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIFF_DIFF_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211701_spec.
Require Import thm3211702_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3269452 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3269453 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3269452 A s t). Qed.
Lemma lem3269454 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term1 A s t) = (@DIFF A s t)) = (term2 A s t).
Proof. exact (@lem3269453 A (term1 A s t) (@DIFF A s t)). Qed.
Lemma lem3269463 {A : Type'} (s : A -> Prop) : (term3 A s) = (term4 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3269454 A s t)). Qed.
Lemma lem3269464 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3269465 {A : Type'} (s : A -> Prop) : (term5 A s) = (term6 A s).
Proof. exact (MK_COMB (@lem3269464 A) (@lem3269463 A s)). Qed.
Lemma lem3269470 {A : Type'} : (term7 A) = (term8 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3269465 A s)). Qed.
Lemma lem3269471 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3269472 {A : Type'} : (term9 A) = (term10 A).
Proof. exact (MK_COMB (@lem3269471 A) (@lem3269470 A)). Qed.
Lemma lem3269477 {A : Type'} : (term10 A) = (term9 A).
Proof. exact (SYM (@lem3269472 A)). Qed.
Lemma lem3269493 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term11 A x s t) = (term12 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem3269494 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term11 A x s t) = (term12 A s x t).
Proof. exact (@lem3269493 A s x t). Qed.
Lemma lem3269495 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term13 A x s t) = (term14 A s x t).
Proof. exact (@lem3269494 A (@DIFF A s t) x t). Qed.
Lemma lem3269499 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term11 A x s t) = (term12 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem3269500 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term11 A x s t) = (term12 A s x t).
Proof. exact (@lem3269499 A s x t). Qed.
Lemma lem3269504 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3269505 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3269504 A P x). Qed.
Lemma lem3269506 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3269505 A s x). Qed.
Lemma lem3269507 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3269508 {A : Type'} (s : A -> Prop) (x : A) : (term15 A x s) = (term16 A s x).
Proof. exact (MK_COMB (@lem3269507) (@lem3269506 A s x)). Qed.
Lemma lem3269510 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3269511 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3269510 A P x). Qed.
Lemma lem3269512 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3269511 A t x). Qed.
Lemma lem3269513 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3269514 {A : Type'} (t : A -> Prop) (x : A) : (term17 A x t) = (term18 A t x).
Proof. exact (MK_COMB (@lem3269513) (@lem3269512 A t x)). Qed.
Lemma lem3269515 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term12 A s x t) = (term19 A s t x).
Proof. exact (MK_COMB (@lem3269508 A s x) (@lem3269514 A t x)). Qed.
Lemma lem3269518 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term11 A x s t) = (term19 A s t x).
Proof. exact (TRANS (@lem3269500 A s x t) (@lem3269515 A s t x)). Qed.
Lemma lem3269519 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3269520 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term20 A x s t) = (term21 A s t x).
Proof. exact (MK_COMB (@lem3269519) (@lem3269518 A s t x)). Qed.
Lemma lem3269522 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3269523 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3269522 A P x). Qed.
Lemma lem3269524 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3269523 A t x). Qed.
Lemma lem3269525 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3269526 {A : Type'} (t : A -> Prop) (x : A) : (term17 A x t) = (term18 A t x).
Proof. exact (MK_COMB (@lem3269525) (@lem3269524 A t x)). Qed.
Lemma lem3269527 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term14 A s x t) = (term22 A s t x).
Proof. exact (MK_COMB (@lem3269520 A s t x) (@lem3269526 A t x)). Qed.
Lemma lem3269530 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term13 A x s t) = (term22 A s t x).
Proof. exact (TRANS (@lem3269495 A s x t) (@lem3269527 A s t x)). Qed.
Lemma lem3269531 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3269532 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term23 A x s t) = (term24 A s t x).
Proof. exact (MK_COMB (@lem3269531) (@lem3269530 A s t x)). Qed.
Lemma lem3269534 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term11 A x s t) = (term12 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem3269535 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term11 A x s t) = (term12 A s x t).
Proof. exact (@lem3269534 A s x t). Qed.
Lemma lem3269539 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3269540 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3269539 A P x). Qed.
Lemma lem3269541 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3269540 A s x). Qed.
Lemma lem3269542 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3269543 {A : Type'} (s : A -> Prop) (x : A) : (term15 A x s) = (term16 A s x).
Proof. exact (MK_COMB (@lem3269542) (@lem3269541 A s x)). Qed.
Lemma lem3269545 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3269546 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3269545 A P x). Qed.
Lemma lem3269547 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3269546 A t x). Qed.
Lemma lem3269548 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3269549 {A : Type'} (t : A -> Prop) (x : A) : (term17 A x t) = (term18 A t x).
Proof. exact (MK_COMB (@lem3269548) (@lem3269547 A t x)). Qed.
Lemma lem3269550 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term12 A s x t) = (term19 A s t x).
Proof. exact (MK_COMB (@lem3269543 A s x) (@lem3269549 A t x)). Qed.
Lemma lem3269553 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term11 A x s t) = (term19 A s t x).
Proof. exact (TRANS (@lem3269535 A s x t) (@lem3269550 A s t x)). Qed.
Lemma lem3269554 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((term13 A x s t) = (term11 A x s t)) = ((term22 A s t x) = (term19 A s t x)).
Proof. exact (MK_COMB (@lem3269532 A s t x) (@lem3269553 A s t x)). Qed.
Lemma lem3269557 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term25 A s t) = (term26 A s t).
Proof. exact (fun_ext (fun x : A => @lem3269554 A s t x)). Qed.
Lemma lem3269558 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3269559 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term2 A s t) = (term27 A s t).
Proof. exact (MK_COMB (@lem3269558 A) (@lem3269557 A s t)). Qed.
Lemma lem3269564 {A : Type'} (s : A -> Prop) : (term4 A s) = (term28 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3269559 A s t)). Qed.
Lemma lem3269565 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3269566 {A : Type'} (s : A -> Prop) : (term6 A s) = (term29 A s).
Proof. exact (MK_COMB (@lem3269565 A) (@lem3269564 A s)). Qed.
Lemma lem3269571 {A : Type'} : (term8 A) = (term30 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3269566 A s)). Qed.
Lemma lem3269572 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3269573 {A : Type'} : (term10 A) = (term31 A).
Proof. exact (MK_COMB (@lem3269572 A) (@lem3269571 A)). Qed.
Lemma lem3269578 {A : Type'} : (term31 A) = (term10 A).
Proof. exact (SYM (@lem3269573 A)). Qed.
Lemma lem3269580 (p : Prop) : p = (term32 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3269581 {A : Type'} : (term31 A) = (term33 A).
Proof. exact (@lem3269580 (term31 A)). Qed.
Lemma lem3269582 {A : Type'} : (term33 A) = (term31 A).
Proof. exact (SYM (@lem3269581 A)). Qed.
Lemma lem3269583 {A : Type'} (h1 : term34 A) : term34 A.
Proof. exact (h1). Qed.
Lemma lem3269586 {A : Type'} (h1 : term33 A) : term33 A.
Proof. exact (h1). Qed.
Lemma lem3269587 {A : Type'} : term35 A.
Proof. exact (fun h0 : term33 A => @lem3269586 A h0). Qed.
Lemma lem3269588 {A : Type'} (h1 : term35 A) : term35 A.
Proof. exact (h1). Qed.
Lemma lem3269589 {A : Type'} (h1 : term33 A) : term33 A.
Proof. exact (h1). Qed.
Lemma lem3269590 {A : Type'} (h1 : term33 A) (h2 : term35 A) : term33 A.
Proof. exact (@lem3269588 A h2 (@lem3269589 A h1)). Qed.
Lemma lem3269591 {A : Type'} (h1 : term33 A) : term36 A.
Proof. exact (fun h0 : term35 A => @lem3269590 A h1 h0). Qed.
Lemma lem3269592 {A : Type'} (h1 : term35 A) : term35 A.
Proof. exact (h1). Qed.
Lemma lem3269593 {A : Type'} (h1 : term33 A) (h2 : term35 A) : term33 A.
Proof. exact (@lem3269591 A h1 (@lem3269592 A h2)). Qed.
Lemma lem3269594 {A : Type'} (h1 : term35 A) : term35 A.
Proof. exact (fun h0 : term33 A => @lem3269593 A h0 h1). Qed.
Lemma lem3269595 {A : Type'} : term37 A.
Proof. exact (fun h0 : term35 A => @lem3269594 A h0). Qed.
Lemma lem3269598 {A : Type'} : term35 A.
Proof. exact (@lem3269595 A (@lem3269587 A)). Qed.
Lemma lem3269599 {A : Type'} : term35 A.
Proof. exact (@lem3269598 A). Qed.
Lemma lem3269601 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3269602 {A : Type'} : (term33 A) = (term38 A).
Proof. exact (@lem3269601 (term34 A)). Qed.
Lemma lem3269604 (t : Prop) : (term39 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3269605 {A : Type'} : (term38 A) = (term31 A).
Proof. exact (@lem3269604 (term31 A)). Qed.
Lemma lem3269628 {A : Type'} : (term33 A) = (term31 A).
Proof. exact (TRANS (@lem3269602 A) (@lem3269605 A)). Qed.
Lemma lem3269651 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((term22 A s t x) = (term19 A s t x)) = ((term22 A s t x) = (term19 A s t x)).
Proof. exact (eq_refl ((term22 A s t x) = (term19 A s t x))). Qed.
Lemma lem3269652 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term26 A s t) = (term26 A s t).
Proof. exact (fun_ext (fun x : A => @lem3269651 A s t x)). Qed.
Lemma lem3269653 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3269654 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term27 A s t) = (term27 A s t).
Proof. exact (MK_COMB (@lem3269653 A) (@lem3269652 A s t)). Qed.
Lemma lem3269655 {A : Type'} (s : A -> Prop) : (term28 A s) = (term28 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3269654 A s t)). Qed.
Lemma lem3269656 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3269657 {A : Type'} (s : A -> Prop) : (term29 A s) = (term29 A s).
Proof. exact (MK_COMB (@lem3269656 A) (@lem3269655 A s)). Qed.
Lemma lem3269658 {A : Type'} : (term30 A) = (term30 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3269657 A s)). Qed.
Lemma lem3269659 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3269660 {A : Type'} : (term31 A) = (term31 A).
Proof. exact (MK_COMB (@lem3269659 A) (@lem3269658 A)). Qed.
Lemma lem3269687 {A : Type'} : (term33 A) = (term31 A).
Proof. exact (TRANS (@lem3269628 A) (@lem3269660 A)). Qed.
Lemma lem3269688 {A : Type'} : (term31 A) = (term33 A).
Proof. exact (SYM (@lem3269687 A)). Qed.
Lemma lem3269690 (p : Prop) : p = (term32 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3269691 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((term22 A s t x) = (term19 A s t x)) = (term40 A s t x).
Proof. exact (@lem3269690 ((term22 A s t x) = (term19 A s t x))). Qed.
Lemma lem3269692 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term40 A s t x) = ((term22 A s t x) = (term19 A s t x)).
Proof. exact (SYM (@lem3269691 A s t x)). Qed.
Lemma lem3269693 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term41 A s t x) : term41 A s t x.
Proof. exact (h1). Qed.
Lemma lem3269699 {A : Type'} (t : A -> Prop) (x : A) : (term42 A t x) = (t x).
Proof. exact (@lem16933 (t x)). Qed.
Lemma lem3269701 {A : Type'} (s : A -> Prop) (x : A) : (term43 A s x) = (term43 A s x).
Proof. exact (eq_refl (term43 A s x)). Qed.
Lemma lem3269702 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term44 A s t x) = (term45 A s t x).
Proof. exact (MK_COMB (@lem3269701 A s x) (@lem3269699 A t x)). Qed.
Lemma lem3269703 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term46 A s t x) = (term44 A s t x).
Proof. exact (@lem17045 (s x) (term18 A t x)). Qed.
Lemma lem3269704 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term46 A s t x) = (term45 A s t x).
Proof. exact (TRANS (@lem3269703 A s t x) (@lem3269702 A s t x)). Qed.
Lemma lem3269711 {A : Type'} (t : A -> Prop) (x : A) : (term42 A t x) = (t x).
Proof. exact (@lem16933 (t x)). Qed.
Lemma lem3269712 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3269713 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term47 A s t x) = (term48 A s t x).
Proof. exact (MK_COMB (@lem3269712) (@lem3269704 A s t x)). Qed.
Lemma lem3269714 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term49 A s t x) = (term50 A s t x).
Proof. exact (MK_COMB (@lem3269713 A s t x) (@lem3269711 A t x)). Qed.
Lemma lem3269715 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term51 A s t x) = (term49 A s t x).
Proof. exact (@lem17045 (term19 A s t x) (term18 A t x)). Qed.
Lemma lem3269716 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term51 A s t x) = (term50 A s t x).
Proof. exact (TRANS (@lem3269715 A s t x) (@lem3269714 A s t x)). Qed.
Lemma lem3269725 {A : Type'} (t : A -> Prop) (x : A) : (term42 A t x) = (t x).
Proof. exact (@lem16933 (t x)). Qed.
Lemma lem3269727 {A : Type'} (s : A -> Prop) (x : A) : (term43 A s x) = (term43 A s x).
Proof. exact (eq_refl (term43 A s x)). Qed.
Lemma lem3269728 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term44 A s t x) = (term45 A s t x).
Proof. exact (MK_COMB (@lem3269727 A s x) (@lem3269725 A t x)). Qed.
Lemma lem3269729 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term46 A s t x) = (term44 A s t x).
Proof. exact (@lem17045 (s x) (term18 A t x)). Qed.
Lemma lem3269730 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term46 A s t x) = (term45 A s t x).
Proof. exact (TRANS (@lem3269729 A s t x) (@lem3269728 A s t x)). Qed.
Lemma lem3269733 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term19 A s t x) = (term19 A s t x).
Proof. exact (eq_refl (term19 A s t x)). Qed.
Lemma lem3269734 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3269735 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term52 A s t x) = (term53 A s t x).
Proof. exact (MK_COMB (@lem3269734) (@lem3269716 A s t x)). Qed.
Lemma lem3269736 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term54 A s t x) = (term55 A s t x).
Proof. exact (MK_COMB (@lem3269735 A s t x) (@lem3269733 A s t x)). Qed.
Lemma lem3269738 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term56 A s t x) = (term56 A s t x).
Proof. exact (eq_refl (term56 A s t x)). Qed.
Lemma lem3269739 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term57 A s t x) = (term58 A s t x).
Proof. exact (MK_COMB (@lem3269738 A s t x) (@lem3269730 A s t x)). Qed.
Lemma lem3269740 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3269741 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term59 A s t x) = (term60 A s t x).
Proof. exact (MK_COMB (@lem3269740) (@lem3269739 A s t x)). Qed.
Lemma lem3269742 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term61 A s t x) = (term62 A s t x).
Proof. exact (MK_COMB (@lem3269741 A s t x) (@lem3269736 A s t x)). Qed.
Lemma lem3269743 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term41 A s t x) = (term61 A s t x).
Proof. exact (@lem17646 (term22 A s t x) (term19 A s t x)). Qed.
Lemma lem3269748 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term41 A s t x) = (term62 A s t x).
Proof. exact (TRANS (@lem3269743 A s t x) (@lem3269742 A s t x)). Qed.
Lemma lem3269817 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term41 A s t x) : term62 A s t x.
Proof. exact (EQ_MP (@lem3269748 A s t x) (@lem3269693 A s t x h1)). Qed.
Lemma lem3269818 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term58 A s t x) : term58 A s t x.
Proof. exact (h1). Qed.
Lemma lem3269819 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term55 A s t x) : term55 A s t x.
Proof. exact (h1). Qed.
Lemma lem3269820 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term58 A s t x) : term45 A s t x.
Proof. exact (proj2 (@lem3269818 A s t x h1)). Qed.
Lemma lem3269821 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term58 A s t x) : term22 A s t x.
Proof. exact (proj1 (@lem3269818 A s t x h1)). Qed.
Lemma lem3269823 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term58 A s t x) : term19 A s t x.
Proof. exact (proj1 (@lem3269821 A s t x h1)). Qed.
Lemma lem3269828 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term55 A s t x) : term19 A s t x.
Proof. exact (proj2 (@lem3269819 A s t x h1)). Qed.
Lemma lem3269829 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term55 A s t x) : term50 A s t x.
Proof. exact (proj1 (@lem3269819 A s t x h1)). Qed.
Lemma lem3269832 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term45 A s t x) : term45 A s t x.
Proof. exact (h1). Qed.
Lemma lem3269851 {A : Type'} (s : A -> Prop) (x : A) (h1 : term18 A s x) : term18 A s x.
Proof. exact (h1). Qed.
Lemma lem3269867 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3269879 {A : Type'} (s : A -> Prop) (x : A) (h1 : term18 A s x) : term18 A s x.
Proof. exact (h1). Qed.
Lemma lem3269891 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3269903 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3269911 {A : Type'} (s : A -> Prop) (x : A) (h1 : term18 A s x) : term18 A s x.
Proof. exact (h1). Qed.
Lemma lem3269913 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term58 A s t x) : term18 A t x.
Proof. exact (proj2 (@lem3269821 A s t x h1)). Qed.
Lemma lem3269919 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3269925 {A : Type'} (s : A -> Prop) (x : A) (h1 : term18 A s x) : term18 A s x.
Proof. exact (h1). Qed.
Lemma lem3269929 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term55 A s t x) : term18 A t x.
Proof. exact (proj2 (@lem3269828 A s t x h1)). Qed.
Lemma lem3269931 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3269935 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term55 A s t x) : term18 A t x.
Proof. exact (proj2 (@lem3269828 A s t x h1)). Qed.
Lemma lem3269937 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3269939 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term58 A s t x) : s x.
Proof. exact (proj1 (@lem3269823 A s t x h1)). Qed.
Lemma lem3269940 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term58 A s t x) : term63 A s x.
Proof. exact (fun h0 : term18 A s x => @lem3269939 A s t x h1). Qed.
Lemma lem3269942 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3269943 {A : Type'} (s : A -> Prop) (x : A) : (term63 A s x) = (s x).
Proof. exact (@lem3269942 (s x)). Qed.
Lemma lem3269944 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term58 A s t x) : s x.
Proof. exact (EQ_MP (@lem3269943 A s x) (@lem3269940 A s t x h1)). Qed.
Lemma lem3269947 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3269949 {A : Type'} (s : A -> Prop) (x : A) : (term18 A s x) = (term65 A s x).
Proof. exact (@lem3269947 (s x)). Qed.
Lemma lem3269952 {A : Type'} (s : A -> Prop) (x : A) (h1 : term18 A s x) : term65 A s x.
Proof. exact (EQ_MP (@lem3269949 A s x) (@lem3269911 A s x h1)). Qed.
Lemma lem3269955 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term18 A s x) (h2 : term58 A s t x) : False.
Proof. exact (@lem3269952 A s x h1 (@lem3269944 A s t x h2)). Qed.
Lemma lem3269956 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term18 A s x) (h2 : term58 A s t x) : term66.
Proof. exact (fun h0 : ~ False => @lem3269955 A s t x h1 h2). Qed.
Lemma lem3269958 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3269959 : term66 = False.
Proof. exact (@lem3269958 False). Qed.
Lemma lem3269960 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term18 A s x) (h2 : term58 A s t x) : False.
Proof. exact (EQ_MP (@lem3269959) (@lem3269956 A s t x h1 h2)). Qed.
Lemma lem3269962 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3269963 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : term63 A t x.
Proof. exact (fun h0 : term18 A t x => @lem3269962 A t x h1). Qed.
Lemma lem3269965 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3269966 {A : Type'} (t : A -> Prop) (x : A) : (term63 A t x) = (t x).
Proof. exact (@lem3269965 (t x)). Qed.
Lemma lem3269967 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem3269966 A t x) (@lem3269963 A t x h1)). Qed.
Lemma lem3269970 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3269972 {A : Type'} (t : A -> Prop) (x : A) : (term18 A t x) = (term65 A t x).
Proof. exact (@lem3269970 (t x)). Qed.
Lemma lem3269975 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term58 A s t x) : term65 A t x.
Proof. exact (EQ_MP (@lem3269972 A t x) (@lem3269913 A s t x h1)). Qed.
Lemma lem3269978 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term58 A s t x) : False.
Proof. exact (@lem3269975 A s t x h2 (@lem3269967 A t x h1)). Qed.
Lemma lem3269979 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term58 A s t x) : term66.
Proof. exact (fun h0 : ~ False => @lem3269978 A s t x h1 h2). Qed.
Lemma lem3269981 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3269982 : term66 = False.
Proof. exact (@lem3269981 False). Qed.
Lemma lem3269983 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term58 A s t x) : False.
Proof. exact (EQ_MP (@lem3269982) (@lem3269979 A s t x h1 h2)). Qed.
Lemma lem3269985 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term55 A s t x) : s x.
Proof. exact (proj1 (@lem3269828 A s t x h1)). Qed.
Lemma lem3269986 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term55 A s t x) : term63 A s x.
Proof. exact (fun h0 : term18 A s x => @lem3269985 A s t x h1). Qed.
Lemma lem3269988 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3269989 {A : Type'} (s : A -> Prop) (x : A) : (term63 A s x) = (s x).
Proof. exact (@lem3269988 (s x)). Qed.
Lemma lem3269990 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term55 A s t x) : s x.
Proof. exact (EQ_MP (@lem3269989 A s x) (@lem3269986 A s t x h1)). Qed.
Lemma lem3269993 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3269995 {A : Type'} (s : A -> Prop) (x : A) : (term18 A s x) = (term65 A s x).
Proof. exact (@lem3269993 (s x)). Qed.
Lemma lem3269998 {A : Type'} (s : A -> Prop) (x : A) (h1 : term18 A s x) : term65 A s x.
Proof. exact (EQ_MP (@lem3269995 A s x) (@lem3269925 A s x h1)). Qed.
Lemma lem3270001 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term18 A s x) (h2 : term55 A s t x) : False.
Proof. exact (@lem3269998 A s x h1 (@lem3269990 A s t x h2)). Qed.
Lemma lem3270002 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term18 A s x) (h2 : term55 A s t x) : term66.
Proof. exact (fun h0 : ~ False => @lem3270001 A s t x h1 h2). Qed.
Lemma lem3270004 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3270005 : term66 = False.
Proof. exact (@lem3270004 False). Qed.
Lemma lem3270006 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term18 A s x) (h2 : term55 A s t x) : False.
Proof. exact (EQ_MP (@lem3270005) (@lem3270002 A s t x h1 h2)). Qed.
Lemma lem3270008 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3270009 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : term63 A t x.
Proof. exact (fun h0 : term18 A t x => @lem3270008 A t x h1). Qed.
Lemma lem3270011 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3270012 {A : Type'} (t : A -> Prop) (x : A) : (term63 A t x) = (t x).
Proof. exact (@lem3270011 (t x)). Qed.
Lemma lem3270013 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem3270012 A t x) (@lem3270009 A t x h1)). Qed.
Lemma lem3270016 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3270018 {A : Type'} (t : A -> Prop) (x : A) : (term18 A t x) = (term65 A t x).
Proof. exact (@lem3270016 (t x)). Qed.
Lemma lem3270021 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term55 A s t x) : term65 A t x.
Proof. exact (EQ_MP (@lem3270018 A t x) (@lem3269929 A s t x h1)). Qed.
Lemma lem3270024 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term55 A s t x) : False.
Proof. exact (@lem3270021 A s t x h2 (@lem3270013 A t x h1)). Qed.
Lemma lem3270025 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term55 A s t x) : term66.
Proof. exact (fun h0 : ~ False => @lem3270024 A s t x h1 h2). Qed.
Lemma lem3270027 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3270028 : term66 = False.
Proof. exact (@lem3270027 False). Qed.
Lemma lem3270029 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term55 A s t x) : False.
Proof. exact (EQ_MP (@lem3270028) (@lem3270025 A s t x h1 h2)). Qed.
Lemma lem3270031 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3270032 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : term63 A t x.
Proof. exact (fun h0 : term18 A t x => @lem3270031 A t x h1). Qed.
Lemma lem3270034 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3270035 {A : Type'} (t : A -> Prop) (x : A) : (term63 A t x) = (t x).
Proof. exact (@lem3270034 (t x)). Qed.
Lemma lem3270036 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem3270035 A t x) (@lem3270032 A t x h1)). Qed.
Lemma lem3270039 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3270041 {A : Type'} (t : A -> Prop) (x : A) : (term18 A t x) = (term65 A t x).
Proof. exact (@lem3270039 (t x)). Qed.
Lemma lem3270044 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term55 A s t x) : term65 A t x.
Proof. exact (EQ_MP (@lem3270041 A t x) (@lem3269935 A s t x h1)). Qed.
Lemma lem3270047 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term55 A s t x) : False.
Proof. exact (@lem3270044 A s t x h2 (@lem3270036 A t x h1)). Qed.
Lemma lem3270048 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term55 A s t x) : term66.
Proof. exact (fun h0 : ~ False => @lem3270047 A s t x h1 h2). Qed.
Lemma lem3270050 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3270051 : term66 = False.
Proof. exact (@lem3270050 False). Qed.
Lemma lem3270052 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term55 A s t x) : False.
Proof. exact (EQ_MP (@lem3270051) (@lem3270048 A s t x h1 h2)). Qed.
Lemma lem3270053 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term55 A s t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3270052 A s t x h1 h2) (fun h3 : False => @lem3269937 A t x h1)). Qed.
Lemma lem3270054 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term55 A s t x) : False.
Proof. exact (EQ_MP (@lem3270053 A s t x h1 h2) (@lem3269937 A t x h1)). Qed.
Lemma lem3270055 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term55 A s t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3270029 A s t x h1 h2) (fun h3 : False => @lem3269931 A t x h1)). Qed.
Lemma lem3270056 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term55 A s t x) : False.
Proof. exact (EQ_MP (@lem3270055 A s t x h1 h2) (@lem3269931 A t x h1)). Qed.
Lemma lem3270057 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term18 A s x) (h2 : term55 A s t x) : (term18 A s x) = False.
Proof. exact (prop_ext (fun h3 : term18 A s x => @lem3270006 A s t x h1 h2) (fun h3 : False => @lem3269925 A s x h1)). Qed.
Lemma lem3270058 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term18 A s x) (h2 : term55 A s t x) : False.
Proof. exact (EQ_MP (@lem3270057 A s t x h1 h2) (@lem3269925 A s x h1)). Qed.
Lemma lem3270059 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term58 A s t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3269983 A s t x h1 h2) (fun h3 : False => @lem3269919 A t x h1)). Qed.
Lemma lem3270060 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term58 A s t x) : False.
Proof. exact (EQ_MP (@lem3270059 A s t x h1 h2) (@lem3269919 A t x h1)). Qed.
Lemma lem3270061 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term18 A s x) (h2 : term58 A s t x) : (term18 A s x) = False.
Proof. exact (prop_ext (fun h3 : term18 A s x => @lem3269960 A s t x h1 h2) (fun h3 : False => @lem3269911 A s x h1)). Qed.
Lemma lem3270062 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term18 A s x) (h2 : term58 A s t x) : False.
Proof. exact (EQ_MP (@lem3270061 A s t x h1 h2) (@lem3269911 A s x h1)). Qed.
Lemma lem3270063 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term55 A s t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3270054 A s t x h1 h2) (fun h3 : False => @lem3269903 A t x h1)). Qed.
Lemma lem3270064 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term55 A s t x) : False.
Proof. exact (EQ_MP (@lem3270063 A s t x h1 h2) (@lem3269903 A t x h1)). Qed.
Lemma lem3270065 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term55 A s t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3270056 A s t x h1 h2) (fun h3 : False => @lem3269891 A t x h1)). Qed.
Lemma lem3270066 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term55 A s t x) : False.
Proof. exact (EQ_MP (@lem3270065 A s t x h1 h2) (@lem3269891 A t x h1)). Qed.
Lemma lem3270067 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term18 A s x) (h2 : term55 A s t x) : (term18 A s x) = False.
Proof. exact (prop_ext (fun h3 : term18 A s x => @lem3270058 A s t x h1 h2) (fun h3 : False => @lem3269879 A s x h1)). Qed.
Lemma lem3270068 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term18 A s x) (h2 : term55 A s t x) : False.
Proof. exact (EQ_MP (@lem3270067 A s t x h1 h2) (@lem3269879 A s x h1)). Qed.
Lemma lem3270069 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term58 A s t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3270060 A s t x h1 h2) (fun h3 : False => @lem3269867 A t x h1)). Qed.
Lemma lem3270070 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term58 A s t x) : False.
Proof. exact (EQ_MP (@lem3270069 A s t x h1 h2) (@lem3269867 A t x h1)). Qed.
Lemma lem3270071 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term18 A s x) (h2 : term58 A s t x) : (term18 A s x) = False.
Proof. exact (prop_ext (fun h3 : term18 A s x => @lem3270062 A s t x h1 h2) (fun h3 : False => @lem3269851 A s x h1)). Qed.
Lemma lem3270072 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term18 A s x) (h2 : term58 A s t x) : False.
Proof. exact (EQ_MP (@lem3270071 A s t x h1 h2) (@lem3269851 A s x h1)). Qed.
Lemma lem3270073 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term55 A s t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3270064 A s t x h1 h2) (fun h3 : False => @lem3269903 A t x h1)). Qed.
Lemma lem3270074 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term55 A s t x) : False.
Proof. exact (EQ_MP (@lem3270073 A s t x h1 h2) (@lem3269903 A t x h1)). Qed.
Lemma lem3270075 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term55 A s t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3270066 A s t x h1 h2) (fun h3 : False => @lem3269891 A t x h1)). Qed.
Lemma lem3270076 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term55 A s t x) : False.
Proof. exact (EQ_MP (@lem3270075 A s t x h1 h2) (@lem3269891 A t x h1)). Qed.
Lemma lem3270077 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term18 A s x) (h2 : term55 A s t x) : (term18 A s x) = False.
Proof. exact (prop_ext (fun h3 : term18 A s x => @lem3270068 A s t x h1 h2) (fun h3 : False => @lem3269879 A s x h1)). Qed.
Lemma lem3270078 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term18 A s x) (h2 : term55 A s t x) : False.
Proof. exact (EQ_MP (@lem3270077 A s t x h1 h2) (@lem3269879 A s x h1)). Qed.
Lemma lem3270079 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term58 A s t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3270070 A s t x h1 h2) (fun h3 : False => @lem3269867 A t x h1)). Qed.
Lemma lem3270080 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term58 A s t x) : False.
Proof. exact (EQ_MP (@lem3270079 A s t x h1 h2) (@lem3269867 A t x h1)). Qed.
Lemma lem3270081 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term18 A s x) (h2 : term58 A s t x) : (term18 A s x) = False.
Proof. exact (prop_ext (fun h3 : term18 A s x => @lem3270072 A s t x h1 h2) (fun h3 : False => @lem3269851 A s x h1)). Qed.
Lemma lem3270082 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term18 A s x) (h2 : term58 A s t x) : False.
Proof. exact (EQ_MP (@lem3270081 A s t x h1 h2) (@lem3269851 A s x h1)). Qed.
Lemma lem3270083 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term55 A s t x) (h2 : term45 A s t x) : False.
Proof. exact (or_elim (@lem3269832 A s t x h2) (fun h0 : term18 A s x => @lem3270078 A s t x h0 h1) (fun h0 : t x => @lem3270076 A s t x h0 h1)). Qed.
Lemma lem3270084 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term55 A s t x) : False.
Proof. exact (or_elim (@lem3269829 A s t x h1) (fun h0 : term45 A s t x => @lem3270083 A s t x h1 h0) (fun h0 : t x => @lem3270074 A s t x h0 h1)). Qed.
Lemma lem3270085 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term58 A s t x) : False.
Proof. exact (or_elim (@lem3269820 A s t x h1) (fun h0 : term18 A s x => @lem3270082 A s t x h0 h1) (fun h0 : t x => @lem3270080 A s t x h0 h1)). Qed.
Lemma lem3270086 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term41 A s t x) : False.
Proof. exact (or_elim (@lem3269817 A s t x h1) (fun h0 : term58 A s t x => @lem3270085 A s t x h0) (fun h0 : term55 A s t x => @lem3270084 A s t x h0)). Qed.
Lemma lem3270087 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term41 A s t x) : (term41 A s t x) = False.
Proof. exact (prop_ext (fun h2 : term41 A s t x => @lem3270086 A s t x h1) (fun h2 : False => @lem3269693 A s t x h1)). Qed.
Lemma lem3270088 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term41 A s t x) : False.
Proof. exact (EQ_MP (@lem3270087 A s t x h1) (@lem3269693 A s t x h1)). Qed.
Lemma lem3270089 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term40 A s t x.
Proof. exact (fun h0 : term41 A s t x => @lem3270088 A s t x h0). Qed.
Lemma lem3270090 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term22 A s t x) = (term19 A s t x).
Proof. exact (EQ_MP (@lem3269692 A s t x) (@lem3270089 A s t x)). Qed.
Lemma lem3270095 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term27 A s t.
Proof. exact (fun x : A => @lem3270090 A s t x). Qed.
Lemma lem3270100 {A : Type'} (s : A -> Prop) : term29 A s.
Proof. exact (fun t : A -> Prop => @lem3270095 A s t). Qed.
Lemma lem3270105 {A : Type'} : term31 A.
Proof. exact (fun s : A -> Prop => @lem3270100 A s). Qed.
Lemma lem3270106 {A : Type'} : term33 A.
Proof. exact (EQ_MP (@lem3269688 A) (@lem3270105 A)). Qed.
Lemma lem3270108 {A : Type'} : term33 A.
Proof. exact (@lem3269599 A (@lem3270106 A)). Qed.
Lemma lem3270109 {A : Type'} (h1 : term34 A) : False.
Proof. exact (@lem3270108 A (@lem3269583 A h1)). Qed.
Lemma lem3270110 {A : Type'} (h1 : term34 A) : (term34 A) = False.
Proof. exact (prop_ext (fun h2 : term34 A => @lem3270109 A h1) (fun h2 : False => @lem3269583 A h1)). Qed.
Lemma lem3270111 {A : Type'} (h1 : term34 A) : False.
Proof. exact (EQ_MP (@lem3270110 A h1) (@lem3269583 A h1)). Qed.
Lemma lem3270112 {A : Type'} : term33 A.
Proof. exact (fun h0 : term34 A => @lem3270111 A h0). Qed.
Lemma lem3270113 {A : Type'} : term31 A.
Proof. exact (EQ_MP (@lem3269582 A) (@lem3270112 A)). Qed.
Lemma lem3270114 {A : Type'} : term10 A.
Proof. exact (EQ_MP (@lem3269578 A) (@lem3270113 A)). Qed.
Lemma lem3270115 {A : Type'} : term9 A.
Proof. exact (EQ_MP (@lem3269477 A) (@lem3270114 A)). Qed.
