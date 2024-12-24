Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import o_ASSOC_term_abbrevs.
Require Import o_DEF_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem15457 {A B C : Type'} (f : B -> C) : term0 A B C f.
Proof. exact (@lem15397 A B C f). Qed.
Lemma lem15458 {A B C : Type'} (f : B -> C) : (term0 A B C f) = (term1 A B C f).
Proof. exact (eq_refl (term0 A B C f)). Qed.
Lemma lem15459 {A B C : Type'} (f : B -> C) : term1 A B C f.
Proof. exact (EQ_MP (@lem15458 A B C f) (@lem15457 A B C f)). Qed.
Lemma lem15460 {A B C : Type'} (f : B -> C) (g : A -> B) : term2 A B C f g.
Proof. exact (@lem15459 A B C f g). Qed.
Lemma lem15461 {A B C : Type'} (f : B -> C) (g : A -> B) : (term2 A B C f g) = ((@o A B C f g) = (term3 A B C f g)).
Proof. exact (eq_refl (term2 A B C f g)). Qed.
Lemma lem15466 {A B C : Type'} (f : B -> C) (g : A -> B) : (@o A B C f g) = (term3 A B C f g).
Proof. exact (EQ_MP (@lem15461 A B C f g) (@lem15460 A B C f g)). Qed.
Lemma lem15467 {A C D : Type'} (f : C -> D) (g : A -> C) : (@o A C D f g) = (term3 A C D f g).
Proof. exact (@lem15466 A C D f g). Qed.
Lemma lem15468 {A B C D : Type'} (f : C -> D) (g : B -> C) (h : A -> B) : (term4 A B C D f g h) = (term5 A B C D f g h).
Proof. exact (@lem15467 A C D f (@o A B C g h)). Qed.
Lemma lem15470 {A B C : Type'} (f : B -> C) (g : A -> B) : (@o A B C f g) = (term3 A B C f g).
Proof. exact (EQ_MP (@lem15461 A B C f g) (@lem15460 A B C f g)). Qed.
Lemma lem15471 {A B C : Type'} (f : B -> C) (g : A -> B) : (@o A B C f g) = (term3 A B C f g).
Proof. exact (@lem15470 A B C f g). Qed.
Lemma lem15472 {A B C : Type'} (g : B -> C) (h : A -> B) : (@o A B C g h) = (term3 A B C g h).
Proof. exact (@lem15471 A B C g h). Qed.
Lemma lem15473 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem15474 {A B C : Type'} (g : B -> C) (h : A -> B) (x : A) : (@o A B C g h x) = (term6 A B C g h x).
Proof. exact (MK_COMB (@lem15472 A B C g h) (@lem15473 A x)). Qed.
Lemma lem15476 {A B : Type'} (f : A -> B) (y : A) : (term7 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem15477 {A C : Type'} (f : A -> C) (y : A) : (term7 A C f y) = (f y).
Proof. exact (@lem15476 A C f y). Qed.
Lemma lem15478 {A B C : Type'} (g : B -> C) (h : A -> B) (x : A) : (term8 A B C g h x) = (term6 A B C g h x).
Proof. exact (@lem15477 A C (term3 A B C g h) x). Qed.
Lemma lem15479 {A B C : Type'} (g : B -> C) (h : A -> B) (x : A) : (term6 A B C g h x) = (term9 A B C g h x).
Proof. exact (eq_refl (term6 A B C g h x)). Qed.
Lemma lem15480 {A B C : Type'} (g : B -> C) (h : A -> B) : (term10 A B C g h) = (term3 A B C g h).
Proof. exact (fun_ext (fun x : A => @lem15479 A B C g h x)). Qed.
Lemma lem15481 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem15482 {A B C : Type'} (g : B -> C) (h : A -> B) (x : A) : (term8 A B C g h x) = (term6 A B C g h x).
Proof. exact (MK_COMB (@lem15480 A B C g h) (@lem15481 A x)). Qed.
Lemma lem15483 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem15484 {A B C : Type'} (g : B -> C) (h : A -> B) (x : A) : (term11 A B C g h x) = (term12 A B C g h x).
Proof. exact (MK_COMB (@lem15483 C) (@lem15482 A B C g h x)). Qed.
Lemma lem15485 {A B C : Type'} (g : B -> C) (h : A -> B) (x : A) : (term6 A B C g h x) = (term9 A B C g h x).
Proof. exact (eq_refl (term6 A B C g h x)). Qed.
Lemma lem15486 {A B C : Type'} (g : B -> C) (h : A -> B) (x : A) : ((term8 A B C g h x) = (term6 A B C g h x)) = ((term6 A B C g h x) = (term9 A B C g h x)).
Proof. exact (MK_COMB (@lem15484 A B C g h x) (@lem15485 A B C g h x)). Qed.
Lemma lem15487 {A B C : Type'} (g : B -> C) (h : A -> B) (x : A) : (term6 A B C g h x) = (term9 A B C g h x).
Proof. exact (EQ_MP (@lem15486 A B C g h x) (@lem15478 A B C g h x)). Qed.
Lemma lem15488 {A B C : Type'} (g : B -> C) (h : A -> B) (x : A) : (@o A B C g h x) = (term9 A B C g h x).
Proof. exact (TRANS (@lem15474 A B C g h x) (@lem15487 A B C g h x)). Qed.
Lemma lem15489 {C D : Type'} (f : C -> D) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem15490 {A B C D : Type'} (f : C -> D) (g : B -> C) (h : A -> B) (x : A) : (term13 A B C D f g h x) = (term14 A B C D f g h x).
Proof. exact (MK_COMB (@lem15489 C D f) (@lem15488 A B C g h x)). Qed.
Lemma lem15491 {A B C D : Type'} (f : C -> D) (g : B -> C) (h : A -> B) : (term5 A B C D f g h) = (term15 A B C D f g h).
Proof. exact (fun_ext (fun x : A => @lem15490 A B C D f g h x)). Qed.
Lemma lem15492 {A B C D : Type'} (f : C -> D) (g : B -> C) (h : A -> B) : (term4 A B C D f g h) = (term15 A B C D f g h).
Proof. exact (TRANS (@lem15468 A B C D f g h) (@lem15491 A B C D f g h)). Qed.
Lemma lem15493 {A D : Type'} : (@eq (A -> D)) = (@eq (A -> D)).
Proof. exact (eq_refl (@eq (A -> D))). Qed.
Lemma lem15494 {A B C D : Type'} (f : C -> D) (g : B -> C) (h : A -> B) : (term16 A B C D f g h) = (term17 A B C D f g h).
Proof. exact (MK_COMB (@lem15493 A D) (@lem15492 A B C D f g h)). Qed.
Lemma lem15496 {A B C : Type'} (f : B -> C) (g : A -> B) : (@o A B C f g) = (term3 A B C f g).
Proof. exact (EQ_MP (@lem15461 A B C f g) (@lem15460 A B C f g)). Qed.
Lemma lem15497 {A B D : Type'} (f : B -> D) (g : A -> B) : (@o A B D f g) = (term3 A B D f g).
Proof. exact (@lem15496 A B D f g). Qed.
Lemma lem15498 {A B C D : Type'} (f : C -> D) (g : B -> C) (h : A -> B) : (term18 A B C D f g h) = (term19 A B C D f g h).
Proof. exact (@lem15497 A B D (@o B C D f g) h). Qed.
Lemma lem15500 {A B C : Type'} (f : B -> C) (g : A -> B) : (@o A B C f g) = (term3 A B C f g).
Proof. exact (EQ_MP (@lem15461 A B C f g) (@lem15460 A B C f g)). Qed.
Lemma lem15501 {B C D : Type'} (f : C -> D) (g : B -> C) : (@o B C D f g) = (term3 B C D f g).
Proof. exact (@lem15500 B C D f g). Qed.
Lemma lem15502 {A B : Type'} (h : A -> B) (x : A) : (h x) = (h x).
Proof. exact (eq_refl (h x)). Qed.
Lemma lem15503 {A B C D : Type'} (f : C -> D) (g : B -> C) (h : A -> B) (x : A) : (term20 A B C D f g h x) = (term21 A B C D f g h x).
Proof. exact (MK_COMB (@lem15501 B C D f g) (@lem15502 A B h x)). Qed.
Lemma lem15505 {A B : Type'} (f : A -> B) (y : A) : (term7 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem15506 {B D : Type'} (f : B -> D) (y : B) : (term7 B D f y) = (f y).
Proof. exact (@lem15505 B D f y). Qed.
Lemma lem15507 {A B C D : Type'} (f : C -> D) (g : B -> C) (h : A -> B) (x : A) : (term22 A B C D f g h x) = (term21 A B C D f g h x).
Proof. exact (@lem15506 B D (term3 B C D f g) (h x)). Qed.
Lemma lem15508 {B C D : Type'} (f : C -> D) (g : B -> C) (x : B) : (term6 B C D f g x) = (term9 B C D f g x).
Proof. exact (eq_refl (term6 B C D f g x)). Qed.
Lemma lem15509 {B C D : Type'} (f : C -> D) (g : B -> C) : (term10 B C D f g) = (term3 B C D f g).
Proof. exact (fun_ext (fun x : B => @lem15508 B C D f g x)). Qed.
Lemma lem15510 {A B : Type'} (h : A -> B) (x : A) : (h x) = (h x).
Proof. exact (eq_refl (h x)). Qed.
Lemma lem15511 {A B C D : Type'} (f : C -> D) (g : B -> C) (h : A -> B) (x : A) : (term22 A B C D f g h x) = (term21 A B C D f g h x).
Proof. exact (MK_COMB (@lem15509 B C D f g) (@lem15510 A B h x)). Qed.
Lemma lem15512 {D : Type'} : (@eq D) = (@eq D).
Proof. exact (eq_refl (@eq D)). Qed.
Lemma lem15513 {A B C D : Type'} (f : C -> D) (g : B -> C) (h : A -> B) (x : A) : (term23 A B C D f g h x) = (term24 A B C D f g h x).
Proof. exact (MK_COMB (@lem15512 D) (@lem15511 A B C D f g h x)). Qed.
Lemma lem15514 {A B C D : Type'} (f : C -> D) (g : B -> C) (h : A -> B) (x : A) : (term21 A B C D f g h x) = (term14 A B C D f g h x).
Proof. exact (eq_refl (term21 A B C D f g h x)). Qed.
Lemma lem15515 {A B C D : Type'} (f : C -> D) (g : B -> C) (h : A -> B) (x : A) : ((term22 A B C D f g h x) = (term21 A B C D f g h x)) = ((term21 A B C D f g h x) = (term14 A B C D f g h x)).
Proof. exact (MK_COMB (@lem15513 A B C D f g h x) (@lem15514 A B C D f g h x)). Qed.
Lemma lem15516 {A B C D : Type'} (f : C -> D) (g : B -> C) (h : A -> B) (x : A) : (term21 A B C D f g h x) = (term14 A B C D f g h x).
Proof. exact (EQ_MP (@lem15515 A B C D f g h x) (@lem15507 A B C D f g h x)). Qed.
Lemma lem15517 {A B C D : Type'} (f : C -> D) (g : B -> C) (h : A -> B) (x : A) : (term20 A B C D f g h x) = (term14 A B C D f g h x).
Proof. exact (TRANS (@lem15503 A B C D f g h x) (@lem15516 A B C D f g h x)). Qed.
Lemma lem15518 {A B C D : Type'} (f : C -> D) (g : B -> C) (h : A -> B) : (term19 A B C D f g h) = (term15 A B C D f g h).
Proof. exact (fun_ext (fun x : A => @lem15517 A B C D f g h x)). Qed.
Lemma lem15519 {A B C D : Type'} (f : C -> D) (g : B -> C) (h : A -> B) : (term18 A B C D f g h) = (term15 A B C D f g h).
Proof. exact (TRANS (@lem15498 A B C D f g h) (@lem15518 A B C D f g h)). Qed.
Lemma lem15520 {A B C D : Type'} (f : C -> D) (g : B -> C) (h : A -> B) : ((term4 A B C D f g h) = (term18 A B C D f g h)) = ((term15 A B C D f g h) = (term15 A B C D f g h)).
Proof. exact (MK_COMB (@lem15494 A B C D f g h) (@lem15519 A B C D f g h)). Qed.
Lemma lem15522 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem15523 {A D : Type'} (x : A -> D) : (x = x) = True.
Proof. exact (@lem15522 (A -> D) x). Qed.
Lemma lem15524 {A B C D : Type'} (f : C -> D) (g : B -> C) (h : A -> B) : ((term15 A B C D f g h) = (term15 A B C D f g h)) = True.
Proof. exact (@lem15523 A D (term15 A B C D f g h)). Qed.
Lemma lem15525 {A B C D : Type'} (f : C -> D) (g : B -> C) (h : A -> B) : ((term4 A B C D f g h) = (term18 A B C D f g h)) = True.
Proof. exact (TRANS (@lem15520 A B C D f g h) (@lem15524 A B C D f g h)). Qed.
Lemma lem15526 {A B C D : Type'} (f : C -> D) (g : B -> C) (h : A -> B) : True = ((term4 A B C D f g h) = (term18 A B C D f g h)).
Proof. exact (SYM (@lem15525 A B C D f g h)). Qed.
Lemma lem15527 {A B C D : Type'} (f : C -> D) (g : B -> C) (h : A -> B) : (term4 A B C D f g h) = (term18 A B C D f g h).
Proof. exact (EQ_MP (@lem15526 A B C D f g h) (@lem0)). Qed.
Lemma lem15532 {A B C D : Type'} (f : C -> D) (g : B -> C) : term25 A B C D f g.
Proof. exact (fun h : A -> B => @lem15527 A B C D f g h). Qed.
Lemma lem15537 {A B C D : Type'} (f : C -> D) : term26 A B C D f.
Proof. exact (fun g : B -> C => @lem15532 A B C D f g). Qed.
Lemma lem15542 {A B C D : Type'} : term27 A B C D.
Proof. exact (fun f : C -> D => @lem15537 A B C D f). Qed.
