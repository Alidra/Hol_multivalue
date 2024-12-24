Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CONSTR_REC_term_abbrevs.
Require Import CONJ_ASSOC_spec.
Require Import CONSTR_BOT_spec.
Require Import CONSTR_IND_spec.
Require Import CONSTR_INJ_spec.
Require Import EXISTS_UNIQUE_REFL_spec.
Require Import EXISTS_UNIQUE_THM_spec.
Require Import FORALL_AND_THM_spec.
Require Import FUN_EQ_THM_spec.
Require Import RIGHT_EXISTS_AND_THM_spec.
Require Import SKOLEM_THM_spec.
Require Import UNIQUE_SKOLEM_ALT_spec.
Require Import UNWIND_THM1_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1812_spec.
Require Import thm1813_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1833_spec.
Require Import thm1834_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm32_spec.
Require Import thm37_spec.
Require Import thm51_spec.
Require Import thm7_spec.
Require Import thm7058_spec.
Require Import thm7129_spec.
Require Import thm7362_spec.
Require Import thm7400_spec.
Require Import thm82_spec.
Require Import thm9102_spec.
Require Import thm9103_spec.
Require Import thm9104_spec.
Require Import thm9120_spec.
Lemma lem1061484 {A B : Type'} (P : type1413 A B) : term0 A B P.
Proof. exact (@lem13833 A B P). Qed.
Lemma lem1061485 {A B : Type'} (P : type1413 A B) : (term0 A B P) = ((term1 A B P) = (term2 A B P)).
Proof. exact (eq_refl (term0 A B P)). Qed.
Lemma lem1061487 {A B : Type'} (f : A -> B) : term3 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem1061488 {A B : Type'} (f : A -> B) : (term3 A B f) = (term4 A B f).
Proof. exact (eq_refl (term3 A B f)). Qed.
Lemma lem1061489 {A B : Type'} (f : A -> B) : term4 A B f.
Proof. exact (EQ_MP (@lem1061488 A B f) (@lem1061487 A B f)). Qed.
Lemma lem1061490 {A B : Type'} (f : A -> B) (g : A -> B) : term5 A B f g.
Proof. exact (@lem1061489 A B f g). Qed.
Lemma lem1061491 {A B : Type'} (f : A -> B) (g : A -> B) : (term5 A B f g) = ((f = g) = (term6 A B f g)).
Proof. exact (eq_refl (term5 A B f g)). Qed.
Lemma lem1061493 {A : Type'} (P : Prop) : term7 A P.
Proof. exact (@lem5751 A P). Qed.
Lemma lem1061494 {A : Type'} (P : Prop) : (term7 A P) = (term8 A P).
Proof. exact (eq_refl (term7 A P)). Qed.
Lemma lem1061495 {A : Type'} (P : Prop) : term8 A P.
Proof. exact (EQ_MP (@lem1061494 A P) (@lem1061493 A P)). Qed.
Lemma lem1061496 {A : Type'} (P : Prop) (Q : A -> Prop) : term9 A P Q.
Proof. exact (@lem1061495 A P Q). Qed.
Lemma lem1061497 {A : Type'} (P : Prop) (Q : A -> Prop) : (term9 A P Q) = ((term10 A P Q) = (term11 A P Q)).
Proof. exact (eq_refl (term9 A P Q)). Qed.
Lemma lem1061499 {A : Type'} (P : A -> Prop) : term12 A P.
Proof. exact (@lem4524 A P). Qed.
Lemma lem1061500 {A : Type'} (P : A -> Prop) : (term12 A P) = (term13 A P).
Proof. exact (eq_refl (term12 A P)). Qed.
Lemma lem1061501 {A : Type'} (P : A -> Prop) : term13 A P.
Proof. exact (EQ_MP (@lem1061500 A P) (@lem1061499 A P)). Qed.
Lemma lem1061502 {A : Type'} (P : A -> Prop) (a : A) : term14 A P a.
Proof. exact (@lem1061501 A P a). Qed.
Lemma lem1061503 {A : Type'} (P : A -> Prop) (a : A) : (term14 A P a) = ((term15 A a P) = (P a)).
Proof. exact (eq_refl (term14 A P a)). Qed.
Lemma lem1061508 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term16 t1 t2 t3) = (term17 t1 t2 t3)) : (term16 t1 t2 t3) = (term17 t1 t2 t3).
Proof. exact (h1). Qed.
Lemma lem1061509 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term16 t1 t2 t3) = (term17 t1 t2 t3)) : (term17 t1 t2 t3) = (term16 t1 t2 t3).
Proof. exact (SYM (@lem1061508 t1 t2 t3 h1)). Qed.
Lemma lem1061510 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term17 t1 t2 t3) = (term16 t1 t2 t3)) : (term17 t1 t2 t3) = (term16 t1 t2 t3).
Proof. exact (h1). Qed.
Lemma lem1061511 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term17 t1 t2 t3) = (term16 t1 t2 t3)) : (term16 t1 t2 t3) = (term17 t1 t2 t3).
Proof. exact (SYM (@lem1061510 t1 t2 t3 h1)). Qed.
Lemma lem1061512 (t1 : Prop) (t2 : Prop) (t3 : Prop) : ((term16 t1 t2 t3) = (term17 t1 t2 t3)) = ((term17 t1 t2 t3) = (term16 t1 t2 t3)).
Proof. exact (prop_ext (fun h1 : (term16 t1 t2 t3) = (term17 t1 t2 t3) => @lem1061509 t1 t2 t3 h1) (fun h1 : (term17 t1 t2 t3) = (term16 t1 t2 t3) => @lem1061511 t1 t2 t3 h1)). Qed.
Lemma lem1061513 (t1 : Prop) (t2 : Prop) : (term18 t1 t2) = (term19 t1 t2).
Proof. exact (fun_ext (fun t3 : Prop => @lem1061512 t1 t2 t3)). Qed.
Lemma lem1061514 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem1061515 (t1 : Prop) (t2 : Prop) : (term20 t1 t2) = (term21 t1 t2).
Proof. exact (MK_COMB (@lem1061514) (@lem1061513 t1 t2)). Qed.
Lemma lem1061516 (t1 : Prop) : (term22 t1) = (term23 t1).
Proof. exact (fun_ext (fun t2 : Prop => @lem1061515 t1 t2)). Qed.
Lemma lem1061517 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem1061518 (t1 : Prop) : (term24 t1) = (term25 t1).
Proof. exact (MK_COMB (@lem1061517) (@lem1061516 t1)). Qed.
Lemma lem1061519 : term26 = term27.
Proof. exact (fun_ext (fun t1 : Prop => @lem1061518 t1)). Qed.
Lemma lem1061520 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem1061521 : term28 = term29.
Proof. exact (MK_COMB (@lem1061520) (@lem1061519)). Qed.
Lemma lem1061522 : term29.
Proof. exact (EQ_MP (@lem1061521) (@lem512)). Qed.
Lemma lem1061523 (t1 : Prop) : term30 t1.
Proof. exact (@lem1061522 t1). Qed.
Lemma lem1061524 (t1 : Prop) : (term30 t1) = (term25 t1).
Proof. exact (eq_refl (term30 t1)). Qed.
Lemma lem1061525 (t1 : Prop) : term25 t1.
Proof. exact (EQ_MP (@lem1061524 t1) (@lem1061523 t1)). Qed.
Lemma lem1061526 (t1 : Prop) (t2 : Prop) : term31 t1 t2.
Proof. exact (@lem1061525 t1 t2). Qed.
Lemma lem1061527 (t1 : Prop) (t2 : Prop) : (term31 t1 t2) = (term21 t1 t2).
Proof. exact (eq_refl (term31 t1 t2)). Qed.
Lemma lem1061528 (t1 : Prop) (t2 : Prop) : term21 t1 t2.
Proof. exact (EQ_MP (@lem1061527 t1 t2) (@lem1061526 t1 t2)). Qed.
Lemma lem1061529 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term32 t1 t2 t3.
Proof. exact (@lem1061528 t1 t2 t3). Qed.
Lemma lem1061530 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term32 t1 t2 t3) = ((term17 t1 t2 t3) = (term16 t1 t2 t3)).
Proof. exact (eq_refl (term32 t1 t2 t3)). Qed.
Lemma lem1061532 {A : Type'} (c1 : nat) : term33 A c1.
Proof. exact (@lem1060638 A c1). Qed.
Lemma lem1061533 {A : Type'} (c1 : nat) : (term33 A c1) = (term34 A c1).
Proof. exact (eq_refl (term33 A c1)). Qed.
Lemma lem1061534 {A : Type'} (c1 : nat) : term34 A c1.
Proof. exact (EQ_MP (@lem1061533 A c1) (@lem1061532 A c1)). Qed.
Lemma lem1061535 {A : Type'} (c1 : nat) (i1 : A) : term35 A c1 i1.
Proof. exact (@lem1061534 A c1 i1). Qed.
Lemma lem1061536 {A : Type'} (c1 : nat) (i1 : A) : (term35 A c1 i1) = (term36 A c1 i1).
Proof. exact (eq_refl (term35 A c1 i1)). Qed.
Lemma lem1061537 {A : Type'} (c1 : nat) (i1 : A) : term36 A c1 i1.
Proof. exact (EQ_MP (@lem1061536 A c1 i1) (@lem1061535 A c1 i1)). Qed.
Lemma lem1061538 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) : term37 A c1 i1 r1.
Proof. exact (@lem1061537 A c1 i1 r1). Qed.
Lemma lem1061539 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) : (term37 A c1 i1 r1) = (term38 A c1 i1 r1).
Proof. exact (eq_refl (term37 A c1 i1 r1)). Qed.
Lemma lem1061540 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) : term38 A c1 i1 r1.
Proof. exact (EQ_MP (@lem1061539 A c1 i1 r1) (@lem1061538 A c1 i1 r1)). Qed.
Lemma lem1061541 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) (c2 : nat) : term39 A c1 i1 r1 c2.
Proof. exact (@lem1061540 A c1 i1 r1 c2). Qed.
Lemma lem1061542 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (r1 : type1614 A) : (term39 A c1 i1 r1 c2) = (term40 A c1 c2 i1 r1).
Proof. exact (eq_refl (term39 A c1 i1 r1 c2)). Qed.
Lemma lem1061543 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (r1 : type1614 A) : term40 A c1 c2 i1 r1.
Proof. exact (EQ_MP (@lem1061542 A c1 c2 i1 r1) (@lem1061541 A c1 i1 r1 c2)). Qed.
Lemma lem1061544 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (r1 : type1614 A) (i2 : A) : term41 A c1 c2 i1 r1 i2.
Proof. exact (@lem1061543 A c1 c2 i1 r1 i2). Qed.
Lemma lem1061545 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) : (term41 A c1 c2 i1 r1 i2) = (term42 A c1 c2 i1 i2 r1).
Proof. exact (eq_refl (term41 A c1 c2 i1 r1 i2)). Qed.
Lemma lem1061546 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) : term42 A c1 c2 i1 i2 r1.
Proof. exact (EQ_MP (@lem1061545 A c1 c2 i1 i2 r1) (@lem1061544 A c1 c2 i1 r1 i2)). Qed.
Lemma lem1061547 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : term43 A c1 c2 i1 i2 r1 r2.
Proof. exact (@lem1061546 A c1 c2 i1 i2 r1 r2). Qed.
Lemma lem1061548 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : (term43 A c1 c2 i1 i2 r1 r2) = (((@CONSTR A c1 i1 r1) = (@CONSTR A c2 i2 r2)) = (term44 A c1 c2 i1 i2 r1 r2)).
Proof. exact (eq_refl (term43 A c1 c2 i1 i2 r1 r2)). Qed.
Lemma lem1061550 {A : Type'} (c : nat) : term45 A c.
Proof. exact (@lem1060000 A c). Qed.
Lemma lem1061551 {A : Type'} (c : nat) : (term45 A c) = (term46 A c).
Proof. exact (eq_refl (term45 A c)). Qed.
Lemma lem1061552 {A : Type'} (c : nat) : term46 A c.
Proof. exact (EQ_MP (@lem1061551 A c) (@lem1061550 A c)). Qed.
Lemma lem1061553 {A : Type'} (c : nat) (i : A) : term47 A c i.
Proof. exact (@lem1061552 A c i). Qed.
Lemma lem1061554 {A : Type'} (c : nat) (i : A) : (term47 A c i) = (term48 A c i).
Proof. exact (eq_refl (term47 A c i)). Qed.
Lemma lem1061555 {A : Type'} (c : nat) (i : A) : term48 A c i.
Proof. exact (EQ_MP (@lem1061554 A c i) (@lem1061553 A c i)). Qed.
Lemma lem1061556 {A : Type'} (c : nat) (i : A) (r : type1614 A) : term49 A c i r.
Proof. exact (@lem1061555 A c i r). Qed.
Lemma lem1061557 {A : Type'} (c : nat) (i : A) (r : type1614 A) : (term49 A c i r) = (term50 A c i r).
Proof. exact (eq_refl (term49 A c i r)). Qed.
Lemma lem1061558 {A : Type'} (c : nat) (i : A) (r : type1614 A) : term50 A c i r.
Proof. exact (EQ_MP (@lem1061557 A c i r) (@lem1061556 A c i r)). Qed.
Lemma lem1061559 {A : Type'} (c : nat) (i : A) (r : type1614 A) : term51 A c i r.
Proof. exact (@lem82 ((@CONSTR A c i r) = (@BOTTOM A))). Qed.
Lemma lem1061572 {A : Type'} (P : Prop) : term7 A P.
Proof. exact (@lem5751 A P). Qed.
Lemma lem1061573 {A : Type'} (P : Prop) : (term7 A P) = (term8 A P).
Proof. exact (eq_refl (term7 A P)). Qed.
Lemma lem1061574 {A : Type'} (P : Prop) : term8 A P.
Proof. exact (EQ_MP (@lem1061573 A P) (@lem1061572 A P)). Qed.
Lemma lem1061575 {A : Type'} (P : Prop) (Q : A -> Prop) : term9 A P Q.
Proof. exact (@lem1061574 A P Q). Qed.
Lemma lem1061576 {A : Type'} (P : Prop) (Q : A -> Prop) : (term9 A P Q) = ((term10 A P Q) = (term11 A P Q)).
Proof. exact (eq_refl (term9 A P Q)). Qed.
Lemma lem1061578 {A : Type'} (P : A -> Prop) : term12 A P.
Proof. exact (@lem4524 A P). Qed.
Lemma lem1061579 {A : Type'} (P : A -> Prop) : (term12 A P) = (term13 A P).
Proof. exact (eq_refl (term12 A P)). Qed.
Lemma lem1061580 {A : Type'} (P : A -> Prop) : term13 A P.
Proof. exact (EQ_MP (@lem1061579 A P) (@lem1061578 A P)). Qed.
Lemma lem1061581 {A : Type'} (P : A -> Prop) (a : A) : term14 A P a.
Proof. exact (@lem1061580 A P a). Qed.
Lemma lem1061582 {A : Type'} (P : A -> Prop) (a : A) : (term14 A P a) = ((term15 A a P) = (P a)).
Proof. exact (eq_refl (term14 A P a)). Qed.
Lemma lem1061587 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term16 t1 t2 t3) = (term17 t1 t2 t3)) : (term16 t1 t2 t3) = (term17 t1 t2 t3).
Proof. exact (h1). Qed.
Lemma lem1061588 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term16 t1 t2 t3) = (term17 t1 t2 t3)) : (term17 t1 t2 t3) = (term16 t1 t2 t3).
Proof. exact (SYM (@lem1061587 t1 t2 t3 h1)). Qed.
Lemma lem1061589 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term17 t1 t2 t3) = (term16 t1 t2 t3)) : (term17 t1 t2 t3) = (term16 t1 t2 t3).
Proof. exact (h1). Qed.
Lemma lem1061590 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term17 t1 t2 t3) = (term16 t1 t2 t3)) : (term16 t1 t2 t3) = (term17 t1 t2 t3).
Proof. exact (SYM (@lem1061589 t1 t2 t3 h1)). Qed.
Lemma lem1061591 (t1 : Prop) (t2 : Prop) (t3 : Prop) : ((term16 t1 t2 t3) = (term17 t1 t2 t3)) = ((term17 t1 t2 t3) = (term16 t1 t2 t3)).
Proof. exact (prop_ext (fun h1 : (term16 t1 t2 t3) = (term17 t1 t2 t3) => @lem1061588 t1 t2 t3 h1) (fun h1 : (term17 t1 t2 t3) = (term16 t1 t2 t3) => @lem1061590 t1 t2 t3 h1)). Qed.
Lemma lem1061592 (t1 : Prop) (t2 : Prop) : (term18 t1 t2) = (term19 t1 t2).
Proof. exact (fun_ext (fun t3 : Prop => @lem1061591 t1 t2 t3)). Qed.
Lemma lem1061593 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem1061594 (t1 : Prop) (t2 : Prop) : (term20 t1 t2) = (term21 t1 t2).
Proof. exact (MK_COMB (@lem1061593) (@lem1061592 t1 t2)). Qed.
Lemma lem1061595 (t1 : Prop) : (term22 t1) = (term23 t1).
Proof. exact (fun_ext (fun t2 : Prop => @lem1061594 t1 t2)). Qed.
Lemma lem1061596 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem1061597 (t1 : Prop) : (term24 t1) = (term25 t1).
Proof. exact (MK_COMB (@lem1061596) (@lem1061595 t1)). Qed.
Lemma lem1061598 : term26 = term27.
Proof. exact (fun_ext (fun t1 : Prop => @lem1061597 t1)). Qed.
Lemma lem1061599 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem1061600 : term28 = term29.
Proof. exact (MK_COMB (@lem1061599) (@lem1061598)). Qed.
Lemma lem1061601 : term29.
Proof. exact (EQ_MP (@lem1061600) (@lem512)). Qed.
Lemma lem1061602 (t1 : Prop) : term30 t1.
Proof. exact (@lem1061601 t1). Qed.
Lemma lem1061603 (t1 : Prop) : (term30 t1) = (term25 t1).
Proof. exact (eq_refl (term30 t1)). Qed.
Lemma lem1061604 (t1 : Prop) : term25 t1.
Proof. exact (EQ_MP (@lem1061603 t1) (@lem1061602 t1)). Qed.
Lemma lem1061605 (t1 : Prop) (t2 : Prop) : term31 t1 t2.
Proof. exact (@lem1061604 t1 t2). Qed.
Lemma lem1061606 (t1 : Prop) (t2 : Prop) : (term31 t1 t2) = (term21 t1 t2).
Proof. exact (eq_refl (term31 t1 t2)). Qed.
Lemma lem1061607 (t1 : Prop) (t2 : Prop) : term21 t1 t2.
Proof. exact (EQ_MP (@lem1061606 t1 t2) (@lem1061605 t1 t2)). Qed.
Lemma lem1061608 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term32 t1 t2 t3.
Proof. exact (@lem1061607 t1 t2 t3). Qed.
Lemma lem1061609 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term32 t1 t2 t3) = ((term17 t1 t2 t3) = (term16 t1 t2 t3)).
Proof. exact (eq_refl (term32 t1 t2 t3)). Qed.
Lemma lem1061611 {A : Type'} (c1 : nat) : term33 A c1.
Proof. exact (@lem1060638 A c1). Qed.
Lemma lem1061612 {A : Type'} (c1 : nat) : (term33 A c1) = (term34 A c1).
Proof. exact (eq_refl (term33 A c1)). Qed.
Lemma lem1061613 {A : Type'} (c1 : nat) : term34 A c1.
Proof. exact (EQ_MP (@lem1061612 A c1) (@lem1061611 A c1)). Qed.
Lemma lem1061614 {A : Type'} (c1 : nat) (i1 : A) : term35 A c1 i1.
Proof. exact (@lem1061613 A c1 i1). Qed.
Lemma lem1061615 {A : Type'} (c1 : nat) (i1 : A) : (term35 A c1 i1) = (term36 A c1 i1).
Proof. exact (eq_refl (term35 A c1 i1)). Qed.
Lemma lem1061616 {A : Type'} (c1 : nat) (i1 : A) : term36 A c1 i1.
Proof. exact (EQ_MP (@lem1061615 A c1 i1) (@lem1061614 A c1 i1)). Qed.
Lemma lem1061617 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) : term37 A c1 i1 r1.
Proof. exact (@lem1061616 A c1 i1 r1). Qed.
Lemma lem1061618 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) : (term37 A c1 i1 r1) = (term38 A c1 i1 r1).
Proof. exact (eq_refl (term37 A c1 i1 r1)). Qed.
Lemma lem1061619 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) : term38 A c1 i1 r1.
Proof. exact (EQ_MP (@lem1061618 A c1 i1 r1) (@lem1061617 A c1 i1 r1)). Qed.
Lemma lem1061620 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) (c2 : nat) : term39 A c1 i1 r1 c2.
Proof. exact (@lem1061619 A c1 i1 r1 c2). Qed.
Lemma lem1061621 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (r1 : type1614 A) : (term39 A c1 i1 r1 c2) = (term40 A c1 c2 i1 r1).
Proof. exact (eq_refl (term39 A c1 i1 r1 c2)). Qed.
Lemma lem1061622 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (r1 : type1614 A) : term40 A c1 c2 i1 r1.
Proof. exact (EQ_MP (@lem1061621 A c1 c2 i1 r1) (@lem1061620 A c1 i1 r1 c2)). Qed.
Lemma lem1061623 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (r1 : type1614 A) (i2 : A) : term41 A c1 c2 i1 r1 i2.
Proof. exact (@lem1061622 A c1 c2 i1 r1 i2). Qed.
Lemma lem1061624 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) : (term41 A c1 c2 i1 r1 i2) = (term42 A c1 c2 i1 i2 r1).
Proof. exact (eq_refl (term41 A c1 c2 i1 r1 i2)). Qed.
Lemma lem1061625 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) : term42 A c1 c2 i1 i2 r1.
Proof. exact (EQ_MP (@lem1061624 A c1 c2 i1 i2 r1) (@lem1061623 A c1 c2 i1 r1 i2)). Qed.
Lemma lem1061626 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : term43 A c1 c2 i1 i2 r1 r2.
Proof. exact (@lem1061625 A c1 c2 i1 i2 r1 r2). Qed.
Lemma lem1061627 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : (term43 A c1 c2 i1 i2 r1 r2) = (((@CONSTR A c1 i1 r1) = (@CONSTR A c2 i2 r2)) = (term44 A c1 c2 i1 i2 r1 r2)).
Proof. exact (eq_refl (term43 A c1 c2 i1 i2 r1 r2)). Qed.
Lemma lem1061629 {A : Type'} (c : nat) : term45 A c.
Proof. exact (@lem1060000 A c). Qed.
Lemma lem1061630 {A : Type'} (c : nat) : (term45 A c) = (term46 A c).
Proof. exact (eq_refl (term45 A c)). Qed.
Lemma lem1061631 {A : Type'} (c : nat) : term46 A c.
Proof. exact (EQ_MP (@lem1061630 A c) (@lem1061629 A c)). Qed.
Lemma lem1061632 {A : Type'} (c : nat) (i : A) : term47 A c i.
Proof. exact (@lem1061631 A c i). Qed.
Lemma lem1061633 {A : Type'} (c : nat) (i : A) : (term47 A c i) = (term48 A c i).
Proof. exact (eq_refl (term47 A c i)). Qed.
Lemma lem1061634 {A : Type'} (c : nat) (i : A) : term48 A c i.
Proof. exact (EQ_MP (@lem1061633 A c i) (@lem1061632 A c i)). Qed.
Lemma lem1061635 {A : Type'} (c : nat) (i : A) (r : type1614 A) : term49 A c i r.
Proof. exact (@lem1061634 A c i r). Qed.
Lemma lem1061636 {A : Type'} (c : nat) (i : A) (r : type1614 A) : (term49 A c i r) = (term50 A c i r).
Proof. exact (eq_refl (term49 A c i r)). Qed.
Lemma lem1061637 {A : Type'} (c : nat) (i : A) (r : type1614 A) : term50 A c i r.
Proof. exact (EQ_MP (@lem1061636 A c i r) (@lem1061635 A c i r)). Qed.
Lemma lem1061638 {A : Type'} (c : nat) (i : A) (r : type1614 A) : term51 A c i r.
Proof. exact (@lem82 ((@CONSTR A c i r) = (@BOTTOM A))). Qed.
Lemma lem1061651 {A : Type'} (P : A -> Prop) : term52 A P.
Proof. exact (@lem4356 A P). Qed.
Lemma lem1061652 {A : Type'} (P : A -> Prop) : (term52 A P) = ((term53 A P) = (term54 A P)).
Proof. exact (eq_refl (term52 A P)). Qed.
Lemma lem1061654 {A B : Type'} (P : type1413 A B) : term55 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem1061655 {A B : Type'} (P : type1413 A B) : (term55 A B P) = ((term56 A B P) = (term57 A B P)).
Proof. exact (eq_refl (term55 A B P)). Qed.
Lemma lem1061657 {A : Type'} (P : A -> Prop) : term58 A P.
Proof. exact (@lem4997 A P). Qed.
Lemma lem1061658 {A : Type'} (P : A -> Prop) : (term58 A P) = (term59 A P).
Proof. exact (eq_refl (term58 A P)). Qed.
Lemma lem1061659 {A : Type'} (P : A -> Prop) : term59 A P.
Proof. exact (EQ_MP (@lem1061658 A P) (@lem1061657 A P)). Qed.
Lemma lem1061660 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term60 A P Q.
Proof. exact (@lem1061659 A P Q). Qed.
Lemma lem1061661 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term60 A P Q) = ((term61 A P Q) = (term62 A P Q)).
Proof. exact (eq_refl (term60 A P Q)). Qed.
Lemma lem1061663 {A : Type'} (P : A -> Prop) : term52 A P.
Proof. exact (@lem4356 A P). Qed.
Lemma lem1061664 {A : Type'} (P : A -> Prop) : (term52 A P) = ((term53 A P) = (term54 A P)).
Proof. exact (eq_refl (term52 A P)). Qed.
Lemma lem1061670 {A : Type'} (c : nat) (i : A) (r : type1614 A) (h1 : (@CONSTR A c i r) = (@BOTTOM A)) : (@CONSTR A c i r) = (@BOTTOM A).
Proof. exact (h1). Qed.
Lemma lem1061671 {A : Type'} (c : nat) (i : A) (r : type1614 A) (h1 : (@CONSTR A c i r) = (@BOTTOM A)) : (@BOTTOM A) = (@CONSTR A c i r).
Proof. exact (SYM (@lem1061670 A c i r h1)). Qed.
Lemma lem1061672 {A : Type'} (c : nat) (i : A) (r : type1614 A) (h1 : (@BOTTOM A) = (@CONSTR A c i r)) : (@BOTTOM A) = (@CONSTR A c i r).
Proof. exact (h1). Qed.
Lemma lem1061673 {A : Type'} (c : nat) (i : A) (r : type1614 A) (h1 : (@BOTTOM A) = (@CONSTR A c i r)) : (@CONSTR A c i r) = (@BOTTOM A).
Proof. exact (SYM (@lem1061672 A c i r h1)). Qed.
Lemma lem1061674 {A : Type'} (c : nat) (i : A) (r : type1614 A) : ((@CONSTR A c i r) = (@BOTTOM A)) = ((@BOTTOM A) = (@CONSTR A c i r)).
Proof. exact (prop_ext (fun h1 : (@CONSTR A c i r) = (@BOTTOM A) => @lem1061671 A c i r h1) (fun h1 : (@BOTTOM A) = (@CONSTR A c i r) => @lem1061673 A c i r h1)). Qed.
Lemma lem1061675 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1061676 {A : Type'} (c : nat) (i : A) (r : type1614 A) : (term50 A c i r) = (term63 A c i r).
Proof. exact (MK_COMB (@lem1061675) (@lem1061674 A c i r)). Qed.
Lemma lem1061677 {A : Type'} (c : nat) (i : A) : (term64 A c i) = (term65 A c i).
Proof. exact (fun_ext (fun r : type1614 A => @lem1061676 A c i r)). Qed.
Lemma lem1061678 {A : Type'} : (@all (nat -> recspace A)) = (@all (nat -> recspace A)).
Proof. exact (eq_refl (@all (nat -> recspace A))). Qed.
Lemma lem1061679 {A : Type'} (c : nat) (i : A) : (term48 A c i) = (term66 A c i).
Proof. exact (MK_COMB (@lem1061678 A) (@lem1061677 A c i)). Qed.
Lemma lem1061680 {A : Type'} (c : nat) : (term67 A c) = (term68 A c).
Proof. exact (fun_ext (fun i : A => @lem1061679 A c i)). Qed.
Lemma lem1061681 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1061682 {A : Type'} (c : nat) : (term46 A c) = (term69 A c).
Proof. exact (MK_COMB (@lem1061681 A) (@lem1061680 A c)). Qed.
Lemma lem1061683 {A : Type'} : (term70 A) = (term71 A).
Proof. exact (fun_ext (fun c : nat => @lem1061682 A c)). Qed.
Lemma lem1061684 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1061685 {A : Type'} : (term72 A) = (term73 A).
Proof. exact (MK_COMB (@lem1061684) (@lem1061683 A)). Qed.
Lemma lem1061686 {A : Type'} : term73 A.
Proof. exact (EQ_MP (@lem1061685 A) (@lem1060000 A)). Qed.
Lemma lem1061687 {A : Type'} (a : A) : term74 A a.
Proof. exact (@lem4476 A a). Qed.
Lemma lem1061688 {A : Type'} (a : A) : (term74 A a) = (term75 A a).
Proof. exact (eq_refl (term74 A a)). Qed.
Lemma lem1061689 {A : Type'} (a : A) : term75 A a.
Proof. exact (EQ_MP (@lem1061688 A a) (@lem1061687 A a)). Qed.
Lemma lem1061690 {A : Type'} (a : A) : (term75 A a) = ((term75 A a) = True).
Proof. exact (@lem7 (term75 A a)). Qed.
Lemma lem1061692 {A : Type'} (c : nat) : term76 A c.
Proof. exact (@lem1061686 A c). Qed.
Lemma lem1061693 {A : Type'} (c : nat) : (term76 A c) = (term69 A c).
Proof. exact (eq_refl (term76 A c)). Qed.
Lemma lem1061694 {A : Type'} (c : nat) : term69 A c.
Proof. exact (EQ_MP (@lem1061693 A c) (@lem1061692 A c)). Qed.
Lemma lem1061695 {A : Type'} (c : nat) (i : A) : term77 A c i.
Proof. exact (@lem1061694 A c i). Qed.
Lemma lem1061696 {A : Type'} (c : nat) (i : A) : (term77 A c i) = (term66 A c i).
Proof. exact (eq_refl (term77 A c i)). Qed.
Lemma lem1061697 {A : Type'} (c : nat) (i : A) : term66 A c i.
Proof. exact (EQ_MP (@lem1061696 A c i) (@lem1061695 A c i)). Qed.
Lemma lem1061698 {A : Type'} (c : nat) (i : A) (r : type1614 A) : term78 A c i r.
Proof. exact (@lem1061697 A c i r). Qed.
Lemma lem1061699 {A : Type'} (c : nat) (i : A) (r : type1614 A) : (term78 A c i r) = (term63 A c i r).
Proof. exact (eq_refl (term78 A c i r)). Qed.
Lemma lem1061700 {A : Type'} (c : nat) (i : A) (r : type1614 A) : term63 A c i r.
Proof. exact (EQ_MP (@lem1061699 A c i r) (@lem1061698 A c i r)). Qed.
Lemma lem1061701 {A : Type'} (c : nat) (i : A) (r : type1614 A) : term79 A c i r.
Proof. exact (@lem82 ((@BOTTOM A) = (@CONSTR A c i r))). Qed.
Lemma lem1061714 {A : Type'} (P : type1338 A) : term80 A P.
Proof. exact (@lem1061477 A P). Qed.
Lemma lem1061715 {A : Type'} (P : type1338 A) : (term80 A P) = (term81 A P).
Proof. exact (eq_refl (term80 A P)). Qed.
Lemma lem1061717 {A B : Type'} (a0 : recspace A) (a1 : B) (b : B) (h1 : term82 A B a0 a1 b) : term82 A B a0 a1 b.
Proof. exact (h1). Qed.
Lemma lem1061718 {A B : Type'} (a0 : recspace A) (a1 : B) (b : B) (h1 : term82 A B a0 a1 b) : a1 = b.
Proof. exact (proj2 (@lem1061717 A B a0 a1 b h1)). Qed.
Lemma lem1061719 {A B : Type'} (a0 : recspace A) (a1 : B) (b : B) (h1 : term82 A B a0 a1 b) : a0 = (@BOTTOM A).
Proof. exact (proj1 (@lem1061717 A B a0 a1 b h1)). Qed.
Lemma lem1061720 {A B : Type'} (Z : type1336 A B) (b : B) (h1 : Z (@BOTTOM A) b) : Z (@BOTTOM A) b.
Proof. exact (h1). Qed.
Lemma lem1061721 {A B : Type'} (Z : type1336 A B) : Z = Z.
Proof. exact (eq_refl Z). Qed.
Lemma lem1061722 {A B : Type'} (Z : type1336 A B) (a0 : recspace A) (a1 : B) (b : B) (h1 : term82 A B a0 a1 b) : (Z a0) = (Z (@BOTTOM A)).
Proof. exact (MK_COMB (@lem1061721 A B Z) (@lem1061719 A B a0 a1 b h1)). Qed.
Lemma lem1061723 {A B : Type'} (Z : type1336 A B) (a0 : recspace A) (a1 : B) (b : B) (h1 : term82 A B a0 a1 b) : (Z a0 a1) = (Z (@BOTTOM A) b).
Proof. exact (MK_COMB (@lem1061722 A B Z a0 a1 b h1) (@lem1061718 A B a0 a1 b h1)). Qed.
Lemma lem1061724 {A B : Type'} (Z : type1336 A B) (a0 : recspace A) (a1 : B) (b : B) (h1 : term82 A B a0 a1 b) : (Z (@BOTTOM A) b) = (Z a0 a1).
Proof. exact (SYM (@lem1061723 A B Z a0 a1 b h1)). Qed.
Lemma lem1061725 {A B : Type'} (a0 : recspace A) (a1 : B) (Z : type1336 A B) (b : B) (h1 : term82 A B a0 a1 b) (h2 : Z (@BOTTOM A) b) : Z a0 a1.
Proof. exact (EQ_MP (@lem1061724 A B Z a0 a1 b h1) (@lem1061720 A B Z b h2)). Qed.
Lemma lem1061726 {A B : Type'} (a0 : recspace A) (a1 : B) (Z : type1336 A B) (b : B) (h1 : Z (@BOTTOM A) b) : term83 A B b Z a0 a1.
Proof. exact (fun h0 : term82 A B a0 a1 b => @lem1061725 A B a0 a1 Z b h0 h1). Qed.
Lemma lem1061727 {A B : Type'} (a0 : recspace A) (a1 : B) (b : B) (h1 : term82 A B a0 a1 b) : term82 A B a0 a1 b.
Proof. exact (h1). Qed.
Lemma lem1061728 {A B : Type'} (a0 : recspace A) (a1 : B) (Z : type1336 A B) (b : B) (h1 : term82 A B a0 a1 b) (h2 : Z (@BOTTOM A) b) : Z a0 a1.
Proof. exact (@lem1061726 A B a0 a1 Z b h2 (@lem1061727 A B a0 a1 b h1)). Qed.
Lemma lem1061729 {A B : Type'} (a0 : recspace A) (a1 : B) (Z : type1336 A B) (b : B) (h1 : Z (@BOTTOM A) b) : term83 A B b Z a0 a1.
Proof. exact (fun h0 : term82 A B a0 a1 b => @lem1061728 A B a0 a1 Z b h0 h1). Qed.
Lemma lem1061730 {A B : Type'} (a0 : recspace A) (Z : type1336 A B) (b : B) (h1 : Z (@BOTTOM A) b) : term84 A B b Z a0.
Proof. exact (fun a1 : B => @lem1061729 A B a0 a1 Z b h1). Qed.
Lemma lem1061731 {A B : Type'} (Z : type1336 A B) (b : B) (h1 : Z (@BOTTOM A) b) : term85 A B b Z.
Proof. exact (fun a0 : recspace A => @lem1061730 A B a0 Z b h1). Qed.
Lemma lem1061732 {A B : Type'} (b : B) (Z : type1336 A B) (h1 : term85 A B b Z) : term85 A B b Z.
Proof. exact (h1). Qed.
Lemma lem1061733 {A B : Type'} (b : B) (Z : type1336 A B) (h1 : term85 A B b Z) : term86 A B b Z.
Proof. exact (@lem1061732 A B b Z h1 (@BOTTOM A)). Qed.
Lemma lem1061734 {A B : Type'} (b : B) (Z : type1336 A B) : (term86 A B b Z) = (term87 A B b Z).
Proof. exact (eq_refl (term86 A B b Z)). Qed.
Lemma lem1061735 {A B : Type'} (b : B) (Z : type1336 A B) (h1 : term85 A B b Z) : term87 A B b Z.
Proof. exact (EQ_MP (@lem1061734 A B b Z) (@lem1061733 A B b Z h1)). Qed.
Lemma lem1061736 {A B : Type'} (b : B) (Z : type1336 A B) (h1 : term85 A B b Z) : term88 A B Z b.
Proof. exact (@lem1061735 A B b Z h1 b). Qed.
Lemma lem1061737 {A B : Type'} (Z : type1336 A B) (b : B) : (term88 A B Z b) = (term89 A B Z b).
Proof. exact (eq_refl (term88 A B Z b)). Qed.
Lemma lem1061738 {A B : Type'} (b : B) (Z : type1336 A B) (h1 : term85 A B b Z) : term89 A B Z b.
Proof. exact (EQ_MP (@lem1061737 A B Z b) (@lem1061736 A B b Z h1)). Qed.
Lemma lem1061739 {A : Type'} : (@BOTTOM A) = (@BOTTOM A).
Proof. exact (eq_refl (@BOTTOM A)). Qed.
Lemma lem1061740 {B : Type'} (b : B) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem1061741 {A B : Type'} (b : B) : term90 A B b.
Proof. exact (conj (@lem1061739 A) (@lem1061740 B b)). Qed.
Lemma lem1061742 {A B : Type'} (b : B) (Z : type1336 A B) (h1 : term85 A B b Z) : Z (@BOTTOM A) b.
Proof. exact (@lem1061738 A B b Z h1 (@lem1061741 A B b)). Qed.
Lemma lem1061743 {A B : Type'} (Z : type1336 A B) (b : B) : term91 A B Z b.
Proof. exact (fun h0 : term85 A B b Z => @lem1061742 A B b Z h0). Qed.
Lemma lem1061744 {A B : Type'} (b : B) (Z : type1336 A B) : term92 A B b Z.
Proof. exact (fun h0 : Z (@BOTTOM A) b => @lem1061731 A B Z b h0). Qed.
Lemma lem1061745 {A B : Type'} (Z : type1336 A B) (b : B) : term93 A B Z b.
Proof. exact (conj (@lem1061744 A B b Z) (@lem1061743 A B Z b)). Qed.
Lemma lem1061746 {A B : Type'} (b : B) (Z : type1336 A B) : (term93 A B Z b) = ((Z (@BOTTOM A) b) = (term85 A B b Z)).
Proof. exact (@lem32 (Z (@BOTTOM A) b) (term85 A B b Z)). Qed.
Lemma lem1061747 {A B : Type'} (b : B) (Z : type1336 A B) : (Z (@BOTTOM A) b) = (term85 A B b Z).
Proof. exact (EQ_MP (@lem1061746 A B b Z) (@lem1061745 A B Z b)). Qed.
Lemma lem1061748 {A B : Type'} (b : B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) (h1 : term83 A B b Z a0 a1) : term83 A B b Z a0 a1.
Proof. exact (h1). Qed.
Lemma lem1061749 {A B : Type'} (a0 : recspace A) (a1 : B) (b : B) (h1 : term82 A B a0 a1 b) : term82 A B a0 a1 b.
Proof. exact (h1). Qed.
Lemma lem1061750 {A B : Type'} (b : B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) (h1 : term82 A B a0 a1 b) (h2 : term83 A B b Z a0 a1) : Z a0 a1.
Proof. exact (@lem1061748 A B b Z a0 a1 h2 (@lem1061749 A B a0 a1 b h1)). Qed.
Lemma lem1061751 {A B : Type'} (Z : type1336 A B) (a0 : recspace A) (a1 : B) (b : B) (h1 : term82 A B a0 a1 b) : term94 A B b Z a0 a1.
Proof. exact (fun h0 : term83 A B b Z a0 a1 => @lem1061750 A B b Z a0 a1 h1 h0). Qed.
Lemma lem1061752 {A B : Type'} (b : B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) (h1 : term83 A B b Z a0 a1) : term83 A B b Z a0 a1.
Proof. exact (h1). Qed.
Lemma lem1061753 {A B : Type'} (b : B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) (h1 : term82 A B a0 a1 b) (h2 : term83 A B b Z a0 a1) : Z a0 a1.
Proof. exact (@lem1061751 A B Z a0 a1 b h1 (@lem1061752 A B b Z a0 a1 h2)). Qed.
Lemma lem1061754 {A B : Type'} (b : B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) (h1 : term83 A B b Z a0 a1) : term83 A B b Z a0 a1.
Proof. exact (fun h0 : term82 A B a0 a1 b => @lem1061753 A B b Z a0 a1 h0 h1). Qed.
Lemma lem1061755 {A B : Type'} (b : B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) (h1 : term83 A B b Z a0 a1) : term83 A B b Z a0 a1.
Proof. exact (h1). Qed.
Lemma lem1061756 {A B : Type'} (a0 : recspace A) (a1 : B) (b : B) (h1 : term82 A B a0 a1 b) : term82 A B a0 a1 b.
Proof. exact (h1). Qed.
Lemma lem1061757 {A B : Type'} (b : B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) (h1 : term82 A B a0 a1 b) (h2 : term83 A B b Z a0 a1) : Z a0 a1.
Proof. exact (@lem1061755 A B b Z a0 a1 h2 (@lem1061756 A B a0 a1 b h1)). Qed.
Lemma lem1061758 {A B : Type'} (b : B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) (h1 : term83 A B b Z a0 a1) : term83 A B b Z a0 a1.
Proof. exact (fun h0 : term82 A B a0 a1 b => @lem1061757 A B b Z a0 a1 h0 h1). Qed.
Lemma lem1061759 {A B : Type'} (b : B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) : term95 A B b Z a0 a1.
Proof. exact (fun h0 : term83 A B b Z a0 a1 => @lem1061758 A B b Z a0 a1 h0). Qed.
Lemma lem1061760 {A B : Type'} (b : B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) : term95 A B b Z a0 a1.
Proof. exact (fun h0 : term83 A B b Z a0 a1 => @lem1061754 A B b Z a0 a1 h0). Qed.
Lemma lem1061761 {A B : Type'} (b : B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) : term96 A B b Z a0 a1.
Proof. exact (conj (@lem1061760 A B b Z a0 a1) (@lem1061759 A B b Z a0 a1)). Qed.
Lemma lem1061762 {A B : Type'} (b : B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) : (term96 A B b Z a0 a1) = ((term83 A B b Z a0 a1) = (term83 A B b Z a0 a1)).
Proof. exact (@lem32 (term83 A B b Z a0 a1) (term83 A B b Z a0 a1)). Qed.
Lemma lem1061763 {A B : Type'} (b : B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) : (term83 A B b Z a0 a1) = (term83 A B b Z a0 a1).
Proof. exact (EQ_MP (@lem1061762 A B b Z a0 a1) (@lem1061761 A B b Z a0 a1)). Qed.
Lemma lem1061764 {A B : Type'} (b : B) (Z : type1336 A B) (a0 : recspace A) : (term97 A B b Z a0) = (term97 A B b Z a0).
Proof. exact (fun_ext (fun a1 : B => @lem1061763 A B b Z a0 a1)). Qed.
Lemma lem1061765 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1061766 {A B : Type'} (b : B) (Z : type1336 A B) (a0 : recspace A) : (term84 A B b Z a0) = (term84 A B b Z a0).
Proof. exact (MK_COMB (@lem1061765 B) (@lem1061764 A B b Z a0)). Qed.
Lemma lem1061767 {A B : Type'} (b : B) (Z : type1336 A B) : (term98 A B b Z) = (term98 A B b Z).
Proof. exact (fun_ext (fun a0 : recspace A => @lem1061766 A B b Z a0)). Qed.
Lemma lem1061768 {A : Type'} : (@all (recspace A)) = (@all (recspace A)).
Proof. exact (eq_refl (@all (recspace A))). Qed.
Lemma lem1061769 {A B : Type'} (b : B) (Z : type1336 A B) : (term85 A B b Z) = (term85 A B b Z).
Proof. exact (MK_COMB (@lem1061768 A) (@lem1061767 A B b Z)). Qed.
Lemma lem1061770 {A B : Type'} (b : B) (Z : type1336 A B) : (Z (@BOTTOM A) b) = (term85 A B b Z).
Proof. exact (TRANS (@lem1061747 A B b Z) (@lem1061769 A B b Z)). Qed.
Lemma lem1061771 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (h1 : term99 A B a0 a1 Fn c i Z r y) : term99 A B a0 a1 Fn c i Z r y.
Proof. exact (h1). Qed.
Lemma lem1061772 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (h1 : term99 A B a0 a1 Fn c i Z r y) : term100 A B a1 Fn c i Z r y.
Proof. exact (proj2 (@lem1061771 A B a0 a1 Fn c i Z r y h1)). Qed.
Lemma lem1061773 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (h1 : term99 A B a0 a1 Fn c i Z r y) : a0 = (@CONSTR A c i r).
Proof. exact (proj1 (@lem1061771 A B a0 a1 Fn c i Z r y h1)). Qed.
Lemma lem1061774 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (h1 : term99 A B a0 a1 Fn c i Z r y) : term101 A B Z r y.
Proof. exact (proj2 (@lem1061772 A B a0 a1 Fn c i Z r y h1)). Qed.
Lemma lem1061775 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (h1 : term99 A B a0 a1 Fn c i Z r y) : a1 = (Fn c i r y).
Proof. exact (proj1 (@lem1061772 A B a0 a1 Fn c i Z r y h1)). Qed.
Lemma lem1061776 {A B : Type'} (Z : type1336 A B) (Fn : type1592 A B) (h1 : term102 A B Z Fn) : term102 A B Z Fn.
Proof. exact (h1). Qed.
Lemma lem1061777 {A B : Type'} (c : nat) (Z : type1336 A B) (Fn : type1592 A B) (h1 : term102 A B Z Fn) : term103 A B Z Fn c.
Proof. exact (@lem1061776 A B Z Fn h1 c). Qed.
Lemma lem1061778 {A B : Type'} (Z : type1336 A B) (Fn : type1592 A B) (c : nat) : (term103 A B Z Fn c) = (term104 A B Z Fn c).
Proof. exact (eq_refl (term103 A B Z Fn c)). Qed.
Lemma lem1061779 {A B : Type'} (c : nat) (Z : type1336 A B) (Fn : type1592 A B) (h1 : term102 A B Z Fn) : term104 A B Z Fn c.
Proof. exact (EQ_MP (@lem1061778 A B Z Fn c) (@lem1061777 A B c Z Fn h1)). Qed.
Lemma lem1061780 {A B : Type'} (c : nat) (i : A) (Z : type1336 A B) (Fn : type1592 A B) (h1 : term102 A B Z Fn) : term105 A B Z Fn c i.
Proof. exact (@lem1061779 A B c Z Fn h1 i). Qed.
Lemma lem1061781 {A B : Type'} (Z : type1336 A B) (Fn : type1592 A B) (c : nat) (i : A) : (term105 A B Z Fn c i) = (term106 A B Z Fn c i).
Proof. exact (eq_refl (term105 A B Z Fn c i)). Qed.
Lemma lem1061782 {A B : Type'} (c : nat) (i : A) (Z : type1336 A B) (Fn : type1592 A B) (h1 : term102 A B Z Fn) : term106 A B Z Fn c i.
Proof. exact (EQ_MP (@lem1061781 A B Z Fn c i) (@lem1061780 A B c i Z Fn h1)). Qed.
Lemma lem1061783 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (Z : type1336 A B) (Fn : type1592 A B) (h1 : term102 A B Z Fn) : term107 A B Z Fn c i r.
Proof. exact (@lem1061782 A B c i Z Fn h1 r). Qed.
Lemma lem1061784 {A B : Type'} (Z : type1336 A B) (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) : (term107 A B Z Fn c i r) = (term108 A B Z Fn c i r).
Proof. exact (eq_refl (term107 A B Z Fn c i r)). Qed.
Lemma lem1061785 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (Z : type1336 A B) (Fn : type1592 A B) (h1 : term102 A B Z Fn) : term108 A B Z Fn c i r.
Proof. exact (EQ_MP (@lem1061784 A B Z Fn c i r) (@lem1061783 A B c i r Z Fn h1)). Qed.
Lemma lem1061786 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Z : type1336 A B) (Fn : type1592 A B) (h1 : term102 A B Z Fn) : term109 A B Z Fn c i r y.
Proof. exact (@lem1061785 A B c i r Z Fn h1 y). Qed.
Lemma lem1061787 {A B : Type'} (Z : type1336 A B) (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (y : nat -> B) : (term109 A B Z Fn c i r y) = (term110 A B Z Fn c i r y).
Proof. exact (eq_refl (term109 A B Z Fn c i r y)). Qed.
Lemma lem1061788 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Z : type1336 A B) (Fn : type1592 A B) (h1 : term102 A B Z Fn) : term110 A B Z Fn c i r y.
Proof. exact (EQ_MP (@lem1061787 A B Z Fn c i r y) (@lem1061786 A B c i r y Z Fn h1)). Qed.
Lemma lem1061789 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (h1 : term102 A B Z Fn) (h2 : term99 A B a0 a1 Fn c i Z r y) : term111 A B Z Fn c i r y.
Proof. exact (@lem1061788 A B c i r y Z Fn h1 (@lem1061774 A B a0 a1 Fn c i Z r y h2)). Qed.
Lemma lem1061790 {A B : Type'} (Z : type1336 A B) : Z = Z.
Proof. exact (eq_refl Z). Qed.
Lemma lem1061791 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (h1 : term99 A B a0 a1 Fn c i Z r y) : (Z a0) = (term112 A B Z c i r).
Proof. exact (MK_COMB (@lem1061790 A B Z) (@lem1061773 A B a0 a1 Fn c i Z r y h1)). Qed.
Lemma lem1061792 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (h1 : term99 A B a0 a1 Fn c i Z r y) : (Z a0 a1) = (term111 A B Z Fn c i r y).
Proof. exact (MK_COMB (@lem1061791 A B a0 a1 Fn c i Z r y h1) (@lem1061775 A B a0 a1 Fn c i Z r y h1)). Qed.
Lemma lem1061793 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (h1 : term99 A B a0 a1 Fn c i Z r y) : (term111 A B Z Fn c i r y) = (Z a0 a1).
Proof. exact (SYM (@lem1061792 A B a0 a1 Fn c i Z r y h1)). Qed.
Lemma lem1061794 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (h1 : term102 A B Z Fn) (h2 : term99 A B a0 a1 Fn c i Z r y) : Z a0 a1.
Proof. exact (EQ_MP (@lem1061793 A B a0 a1 Fn c i Z r y h2) (@lem1061789 A B a0 a1 Fn c i Z r y h1 h2)). Qed.
Lemma lem1061795 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (a0 : recspace A) (a1 : B) (Z : type1336 A B) (Fn : type1592 A B) (h1 : term102 A B Z Fn) : term113 A B Fn c i r y Z a0 a1.
Proof. exact (fun h0 : term99 A B a0 a1 Fn c i Z r y => @lem1061794 A B a0 a1 Fn c i Z r y h1 h0). Qed.
Lemma lem1061796 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (h1 : term99 A B a0 a1 Fn c i Z r y) : term99 A B a0 a1 Fn c i Z r y.
Proof. exact (h1). Qed.
Lemma lem1061797 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (h1 : term102 A B Z Fn) (h2 : term99 A B a0 a1 Fn c i Z r y) : Z a0 a1.
Proof. exact (@lem1061795 A B c i r y a0 a1 Z Fn h1 (@lem1061796 A B a0 a1 Fn c i Z r y h2)). Qed.
Lemma lem1061798 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (a0 : recspace A) (a1 : B) (Z : type1336 A B) (Fn : type1592 A B) (h1 : term102 A B Z Fn) : term113 A B Fn c i r y Z a0 a1.
Proof. exact (fun h0 : term99 A B a0 a1 Fn c i Z r y => @lem1061797 A B a0 a1 Fn c i Z r y h1 h0). Qed.
Lemma lem1061799 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (a0 : recspace A) (a1 : B) (Z : type1336 A B) (Fn : type1592 A B) (h1 : term102 A B Z Fn) : term114 A B Fn c i r Z a0 a1.
Proof. exact (fun y : nat -> B => @lem1061798 A B c i r y a0 a1 Z Fn h1). Qed.
Lemma lem1061800 {A B : Type'} (c : nat) (i : A) (a0 : recspace A) (a1 : B) (Z : type1336 A B) (Fn : type1592 A B) (h1 : term102 A B Z Fn) : term115 A B Fn c i Z a0 a1.
Proof. exact (fun r : type1614 A => @lem1061799 A B c i r a0 a1 Z Fn h1). Qed.
Lemma lem1061801 {A B : Type'} (c : nat) (a0 : recspace A) (a1 : B) (Z : type1336 A B) (Fn : type1592 A B) (h1 : term102 A B Z Fn) : term116 A B Fn c Z a0 a1.
Proof. exact (fun i : A => @lem1061800 A B c i a0 a1 Z Fn h1). Qed.
Lemma lem1061802 {A B : Type'} (a0 : recspace A) (a1 : B) (Z : type1336 A B) (Fn : type1592 A B) (h1 : term102 A B Z Fn) : term117 A B Fn Z a0 a1.
Proof. exact (fun c : nat => @lem1061801 A B c a0 a1 Z Fn h1). Qed.
Lemma lem1061803 {A B : Type'} (a0 : recspace A) (Z : type1336 A B) (Fn : type1592 A B) (h1 : term102 A B Z Fn) : term118 A B Fn Z a0.
Proof. exact (fun a1 : B => @lem1061802 A B a0 a1 Z Fn h1). Qed.
Lemma lem1061804 {A B : Type'} (Z : type1336 A B) (Fn : type1592 A B) (h1 : term102 A B Z Fn) : term119 A B Fn Z.
Proof. exact (fun a0 : recspace A => @lem1061803 A B a0 Z Fn h1). Qed.
Lemma lem1061805 {A B : Type'} (Fn : type1592 A B) (Z : type1336 A B) (h1 : term119 A B Fn Z) : term119 A B Fn Z.
Proof. exact (h1). Qed.
Lemma lem1061806 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term119 A B Fn Z) : term120 A B Fn Z c i r.
Proof. exact (@lem1061805 A B Fn Z h1 (@CONSTR A c i r)). Qed.
Lemma lem1061807 {A B : Type'} (Fn : type1592 A B) (Z : type1336 A B) (c : nat) (i : A) (r : type1614 A) : (term120 A B Fn Z c i r) = (term121 A B Fn Z c i r).
Proof. exact (eq_refl (term120 A B Fn Z c i r)). Qed.
Lemma lem1061808 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term119 A B Fn Z) : term121 A B Fn Z c i r.
Proof. exact (EQ_MP (@lem1061807 A B Fn Z c i r) (@lem1061806 A B c i r Fn Z h1)). Qed.
Lemma lem1061809 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term119 A B Fn Z) : term122 A B Z Fn c i r y.
Proof. exact (@lem1061808 A B c i r Fn Z h1 (Fn c i r y)). Qed.
Lemma lem1061810 {A B : Type'} (Z : type1336 A B) (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (y : nat -> B) : (term122 A B Z Fn c i r y) = (term123 A B Z Fn c i r y).
Proof. exact (eq_refl (term122 A B Z Fn c i r y)). Qed.
Lemma lem1061811 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term119 A B Fn Z) : term123 A B Z Fn c i r y.
Proof. exact (EQ_MP (@lem1061810 A B Z Fn c i r y) (@lem1061809 A B c i r y Fn Z h1)). Qed.
Lemma lem1061812 {A B : Type'} (i : A) (r : type1614 A) (y : nat -> B) (c : nat) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term119 A B Fn Z) : term124 A B Z Fn i r y c.
Proof. exact (@lem1061811 A B c i r y Fn Z h1 c). Qed.
Lemma lem1061813 {A B : Type'} (Z : type1336 A B) (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (y : nat -> B) : (term124 A B Z Fn i r y c) = (term125 A B Z Fn c i r y).
Proof. exact (eq_refl (term124 A B Z Fn i r y c)). Qed.
Lemma lem1061814 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term119 A B Fn Z) : term125 A B Z Fn c i r y.
Proof. exact (EQ_MP (@lem1061813 A B Z Fn c i r y) (@lem1061812 A B i r y c Fn Z h1)). Qed.
Lemma lem1061815 {A B : Type'} (c : nat) (r : type1614 A) (y : nat -> B) (i : A) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term119 A B Fn Z) : term126 A B Z Fn c r y i.
Proof. exact (@lem1061814 A B c i r y Fn Z h1 i). Qed.
Lemma lem1061816 {A B : Type'} (Z : type1336 A B) (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (y : nat -> B) : (term126 A B Z Fn c r y i) = (term127 A B Z Fn c i r y).
Proof. exact (eq_refl (term126 A B Z Fn c r y i)). Qed.
Lemma lem1061817 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term119 A B Fn Z) : term127 A B Z Fn c i r y.
Proof. exact (EQ_MP (@lem1061816 A B Z Fn c i r y) (@lem1061815 A B c r y i Fn Z h1)). Qed.
Lemma lem1061818 {A B : Type'} (c : nat) (i : A) (y : nat -> B) (r : type1614 A) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term119 A B Fn Z) : term128 A B Z Fn c i y r.
Proof. exact (@lem1061817 A B c i r y Fn Z h1 r). Qed.
Lemma lem1061819 {A B : Type'} (Z : type1336 A B) (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (y : nat -> B) : (term128 A B Z Fn c i y r) = (term129 A B Z Fn c i r y).
Proof. exact (eq_refl (term128 A B Z Fn c i y r)). Qed.
Lemma lem1061820 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term119 A B Fn Z) : term129 A B Z Fn c i r y.
Proof. exact (EQ_MP (@lem1061819 A B Z Fn c i r y) (@lem1061818 A B c i y r Fn Z h1)). Qed.
Lemma lem1061821 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term119 A B Fn Z) : term130 A B Z Fn c i r y.
Proof. exact (@lem1061820 A B c i r y Fn Z h1 y). Qed.
Lemma lem1061822 {A B : Type'} (Z : type1336 A B) (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (y : nat -> B) : (term130 A B Z Fn c i r y) = (term131 A B Z Fn c i r y).
Proof. exact (eq_refl (term130 A B Z Fn c i r y)). Qed.
Lemma lem1061823 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term119 A B Fn Z) : term131 A B Z Fn c i r y.
Proof. exact (EQ_MP (@lem1061822 A B Z Fn c i r y) (@lem1061821 A B c i r y Fn Z h1)). Qed.
Lemma lem1061824 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (h1 : term101 A B Z r y) : term101 A B Z r y.
Proof. exact (h1). Qed.
Lemma lem1061825 {A B : Type'} (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (y : nat -> B) : (Fn c i r y) = (Fn c i r y).
Proof. exact (eq_refl (Fn c i r y)). Qed.
Lemma lem1061826 {A B : Type'} (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (h1 : term101 A B Z r y) : term132 A B Fn c i Z r y.
Proof. exact (conj (@lem1061825 A B Fn c i r y) (@lem1061824 A B Z r y h1)). Qed.
Lemma lem1061827 {A : Type'} (c : nat) (i : A) (r : type1614 A) : (@CONSTR A c i r) = (@CONSTR A c i r).
Proof. exact (eq_refl (@CONSTR A c i r)). Qed.
Lemma lem1061828 {A B : Type'} (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (h1 : term101 A B Z r y) : term133 A B Fn c i Z r y.
Proof. exact (conj (@lem1061827 A c i r) (@lem1061826 A B Fn c i Z r y h1)). Qed.
Lemma lem1061829 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term101 A B Z r y) (h2 : term119 A B Fn Z) : term111 A B Z Fn c i r y.
Proof. exact (@lem1061823 A B c i r y Fn Z h2 (@lem1061828 A B Fn c i Z r y h1)). Qed.
Lemma lem1061830 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term119 A B Fn Z) : term110 A B Z Fn c i r y.
Proof. exact (fun h0 : term101 A B Z r y => @lem1061829 A B c i r y Fn Z h0 h1). Qed.
Lemma lem1061831 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term119 A B Fn Z) : term108 A B Z Fn c i r.
Proof. exact (fun y : nat -> B => @lem1061830 A B c i r y Fn Z h1). Qed.
Lemma lem1061832 {A B : Type'} (c : nat) (i : A) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term119 A B Fn Z) : term106 A B Z Fn c i.
Proof. exact (fun r : type1614 A => @lem1061831 A B c i r Fn Z h1). Qed.
Lemma lem1061833 {A B : Type'} (c : nat) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term119 A B Fn Z) : term104 A B Z Fn c.
Proof. exact (fun i : A => @lem1061832 A B c i Fn Z h1). Qed.
Lemma lem1061834 {A B : Type'} (Fn : type1592 A B) (Z : type1336 A B) (h1 : term119 A B Fn Z) : term102 A B Z Fn.
Proof. exact (fun c : nat => @lem1061833 A B c Fn Z h1). Qed.
Lemma lem1061835 {A B : Type'} (Z : type1336 A B) (Fn : type1592 A B) : term134 A B Z Fn.
Proof. exact (fun h0 : term119 A B Fn Z => @lem1061834 A B Fn Z h0). Qed.
Lemma lem1061836 {A B : Type'} (Fn : type1592 A B) (Z : type1336 A B) : term135 A B Fn Z.
Proof. exact (fun h0 : term102 A B Z Fn => @lem1061804 A B Z Fn h0). Qed.
Lemma lem1061837 {A B : Type'} (Z : type1336 A B) (Fn : type1592 A B) : term136 A B Z Fn.
Proof. exact (conj (@lem1061836 A B Fn Z) (@lem1061835 A B Z Fn)). Qed.
Lemma lem1061838 {A B : Type'} (Fn : type1592 A B) (Z : type1336 A B) : (term136 A B Z Fn) = ((term102 A B Z Fn) = (term119 A B Fn Z)).
Proof. exact (@lem32 (term102 A B Z Fn) (term119 A B Fn Z)). Qed.
Lemma lem1061839 {A B : Type'} (Fn : type1592 A B) (Z : type1336 A B) : (term102 A B Z Fn) = (term119 A B Fn Z).
Proof. exact (EQ_MP (@lem1061838 A B Fn Z) (@lem1061837 A B Z Fn)). Qed.
Lemma lem1061840 {A B : Type'} (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) (h1 : term117 A B Fn Z a0 a1) : term117 A B Fn Z a0 a1.
Proof. exact (h1). Qed.
Lemma lem1061841 {A B : Type'} (c : nat) (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) (h1 : term117 A B Fn Z a0 a1) : term137 A B Fn Z a0 a1 c.
Proof. exact (@lem1061840 A B Fn Z a0 a1 h1 c). Qed.
Lemma lem1061842 {A B : Type'} (Fn : type1592 A B) (c : nat) (Z : type1336 A B) (a0 : recspace A) (a1 : B) : (term137 A B Fn Z a0 a1 c) = (term116 A B Fn c Z a0 a1).
Proof. exact (eq_refl (term137 A B Fn Z a0 a1 c)). Qed.
Lemma lem1061843 {A B : Type'} (c : nat) (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) (h1 : term117 A B Fn Z a0 a1) : term116 A B Fn c Z a0 a1.
Proof. exact (EQ_MP (@lem1061842 A B Fn c Z a0 a1) (@lem1061841 A B c Fn Z a0 a1 h1)). Qed.
Lemma lem1061844 {A B : Type'} (c : nat) (i : A) (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) (h1 : term117 A B Fn Z a0 a1) : term138 A B Fn c Z a0 a1 i.
Proof. exact (@lem1061843 A B c Fn Z a0 a1 h1 i). Qed.
Lemma lem1061845 {A B : Type'} (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (a0 : recspace A) (a1 : B) : (term138 A B Fn c Z a0 a1 i) = (term115 A B Fn c i Z a0 a1).
Proof. exact (eq_refl (term138 A B Fn c Z a0 a1 i)). Qed.
Lemma lem1061846 {A B : Type'} (c : nat) (i : A) (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) (h1 : term117 A B Fn Z a0 a1) : term115 A B Fn c i Z a0 a1.
Proof. exact (EQ_MP (@lem1061845 A B Fn c i Z a0 a1) (@lem1061844 A B c i Fn Z a0 a1 h1)). Qed.
Lemma lem1061847 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) (h1 : term117 A B Fn Z a0 a1) : term139 A B Fn c i Z a0 a1 r.
Proof. exact (@lem1061846 A B c i Fn Z a0 a1 h1 r). Qed.
Lemma lem1061848 {A B : Type'} (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (Z : type1336 A B) (a0 : recspace A) (a1 : B) : (term139 A B Fn c i Z a0 a1 r) = (term114 A B Fn c i r Z a0 a1).
Proof. exact (eq_refl (term139 A B Fn c i Z a0 a1 r)). Qed.
Lemma lem1061849 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) (h1 : term117 A B Fn Z a0 a1) : term114 A B Fn c i r Z a0 a1.
Proof. exact (EQ_MP (@lem1061848 A B Fn c i r Z a0 a1) (@lem1061847 A B c i r Fn Z a0 a1 h1)). Qed.
Lemma lem1061850 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) (h1 : term117 A B Fn Z a0 a1) : term140 A B Fn c i r Z a0 a1 y.
Proof. exact (@lem1061849 A B c i r Fn Z a0 a1 h1 y). Qed.
Lemma lem1061851 {A B : Type'} (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) : (term140 A B Fn c i r Z a0 a1 y) = (term113 A B Fn c i r y Z a0 a1).
Proof. exact (eq_refl (term140 A B Fn c i r Z a0 a1 y)). Qed.
Lemma lem1061852 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) (h1 : term117 A B Fn Z a0 a1) : term113 A B Fn c i r y Z a0 a1.
Proof. exact (EQ_MP (@lem1061851 A B Fn c i r y Z a0 a1) (@lem1061850 A B c i r y Fn Z a0 a1 h1)). Qed.
Lemma lem1061853 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (h1 : term99 A B a0 a1 Fn c i Z r y) : term99 A B a0 a1 Fn c i Z r y.
Proof. exact (h1). Qed.
Lemma lem1061854 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (h1 : term117 A B Fn Z a0 a1) (h2 : term99 A B a0 a1 Fn c i Z r y) : Z a0 a1.
Proof. exact (@lem1061852 A B c i r y Fn Z a0 a1 h1 (@lem1061853 A B a0 a1 Fn c i Z r y h2)). Qed.
Lemma lem1061855 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (h1 : term99 A B a0 a1 Fn c i Z r y) : term141 A B Fn Z a0 a1.
Proof. exact (fun h0 : term117 A B Fn Z a0 a1 => @lem1061854 A B a0 a1 Fn c i Z r y h0 h1). Qed.
Lemma lem1061856 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (h1 : term142 A B a0 a1 Fn c i Z r) : term142 A B a0 a1 Fn c i Z r.
Proof. exact (h1). Qed.
Lemma lem1061857 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (h1 : term142 A B a0 a1 Fn c i Z r) : term141 A B Fn Z a0 a1.
Proof. exact (ex_elim (@lem1061856 A B a0 a1 Fn c i Z r h1) (fun y : nat -> B => fun h0 : term143 A B a0 a1 Fn c i Z r y => @lem1061855 A B a0 a1 Fn c i Z r y h0)). Qed.
Lemma lem1061858 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (h1 : term144 A B a0 a1 Fn c i Z) : term144 A B a0 a1 Fn c i Z.
Proof. exact (h1). Qed.
Lemma lem1061859 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (h1 : term144 A B a0 a1 Fn c i Z) : term141 A B Fn Z a0 a1.
Proof. exact (ex_elim (@lem1061858 A B a0 a1 Fn c i Z h1) (fun r : type1614 A => fun h0 : term145 A B a0 a1 Fn c i Z r => @lem1061857 A B a0 a1 Fn c i Z r h0)). Qed.
Lemma lem1061860 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (Z : type1336 A B) (h1 : term146 A B a0 a1 Fn c Z) : term146 A B a0 a1 Fn c Z.
Proof. exact (h1). Qed.
Lemma lem1061861 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (Z : type1336 A B) (h1 : term146 A B a0 a1 Fn c Z) : term141 A B Fn Z a0 a1.
Proof. exact (ex_elim (@lem1061860 A B a0 a1 Fn c Z h1) (fun i : A => fun h0 : term147 A B a0 a1 Fn c Z i => @lem1061859 A B a0 a1 Fn c i Z h0)). Qed.
Lemma lem1061862 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term148 A B a0 a1 Fn Z) : term148 A B a0 a1 Fn Z.
Proof. exact (h1). Qed.
Lemma lem1061863 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term148 A B a0 a1 Fn Z) : term141 A B Fn Z a0 a1.
Proof. exact (ex_elim (@lem1061862 A B a0 a1 Fn Z h1) (fun c : nat => fun h0 : term149 A B a0 a1 Fn Z c => @lem1061861 A B a0 a1 Fn c Z h0)). Qed.
Lemma lem1061864 {A B : Type'} (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) (h1 : term117 A B Fn Z a0 a1) : term117 A B Fn Z a0 a1.
Proof. exact (h1). Qed.
Lemma lem1061865 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term117 A B Fn Z a0 a1) (h2 : term148 A B a0 a1 Fn Z) : Z a0 a1.
Proof. exact (@lem1061863 A B a0 a1 Fn Z h2 (@lem1061864 A B Fn Z a0 a1 h1)). Qed.
Lemma lem1061866 {A B : Type'} (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) (h1 : term117 A B Fn Z a0 a1) : term150 A B Fn Z a0 a1.
Proof. exact (fun h0 : term148 A B a0 a1 Fn Z => @lem1061865 A B a0 a1 Fn Z h1 h0). Qed.
Lemma lem1061867 {A B : Type'} (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) (h1 : term150 A B Fn Z a0 a1) : term150 A B Fn Z a0 a1.
Proof. exact (h1). Qed.
Lemma lem1061868 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (h1 : term99 A B a0 a1 Fn c i Z r y) : term99 A B a0 a1 Fn c i Z r y.
Proof. exact (h1). Qed.
Lemma lem1061869 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (h1 : term99 A B a0 a1 Fn c i Z r y) : term142 A B a0 a1 Fn c i Z r.
Proof. exact (ex_intro (term143 A B a0 a1 Fn c i Z r) y (@lem1061868 A B a0 a1 Fn c i Z r y h1)). Qed.
Lemma lem1061870 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (h1 : term99 A B a0 a1 Fn c i Z r y) : term144 A B a0 a1 Fn c i Z.
Proof. exact (ex_intro (term145 A B a0 a1 Fn c i Z) r (@lem1061869 A B a0 a1 Fn c i Z r y h1)). Qed.
Lemma lem1061871 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (h1 : term99 A B a0 a1 Fn c i Z r y) : term146 A B a0 a1 Fn c Z.
Proof. exact (ex_intro (term147 A B a0 a1 Fn c Z) i (@lem1061870 A B a0 a1 Fn c i Z r y h1)). Qed.
Lemma lem1061872 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (h1 : term99 A B a0 a1 Fn c i Z r y) : term148 A B a0 a1 Fn Z.
Proof. exact (ex_intro (term149 A B a0 a1 Fn Z) c (@lem1061871 A B a0 a1 Fn c i Z r y h1)). Qed.
Lemma lem1061873 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) (h1 : term99 A B a0 a1 Fn c i Z r y) (h2 : term150 A B Fn Z a0 a1) : Z a0 a1.
Proof. exact (@lem1061867 A B Fn Z a0 a1 h2 (@lem1061872 A B a0 a1 Fn c i Z r y h1)). Qed.
Lemma lem1061874 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) (h1 : term150 A B Fn Z a0 a1) : term113 A B Fn c i r y Z a0 a1.
Proof. exact (fun h0 : term99 A B a0 a1 Fn c i Z r y => @lem1061873 A B c i r y Fn Z a0 a1 h0 h1). Qed.
Lemma lem1061875 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) (h1 : term150 A B Fn Z a0 a1) : term114 A B Fn c i r Z a0 a1.
Proof. exact (fun y : nat -> B => @lem1061874 A B c i r y Fn Z a0 a1 h1). Qed.
Lemma lem1061876 {A B : Type'} (c : nat) (i : A) (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) (h1 : term150 A B Fn Z a0 a1) : term115 A B Fn c i Z a0 a1.
Proof. exact (fun r : type1614 A => @lem1061875 A B c i r Fn Z a0 a1 h1). Qed.
Lemma lem1061877 {A B : Type'} (c : nat) (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) (h1 : term150 A B Fn Z a0 a1) : term116 A B Fn c Z a0 a1.
Proof. exact (fun i : A => @lem1061876 A B c i Fn Z a0 a1 h1). Qed.
Lemma lem1061878 {A B : Type'} (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) (h1 : term150 A B Fn Z a0 a1) : term117 A B Fn Z a0 a1.
Proof. exact (fun c : nat => @lem1061877 A B c Fn Z a0 a1 h1). Qed.
Lemma lem1061879 {A B : Type'} (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) : term151 A B Fn Z a0 a1.
Proof. exact (fun h0 : term150 A B Fn Z a0 a1 => @lem1061878 A B Fn Z a0 a1 h0). Qed.
Lemma lem1061880 {A B : Type'} (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) : term152 A B Fn Z a0 a1.
Proof. exact (fun h0 : term117 A B Fn Z a0 a1 => @lem1061866 A B Fn Z a0 a1 h0). Qed.
Lemma lem1061881 {A B : Type'} (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) : term153 A B Fn Z a0 a1.
Proof. exact (conj (@lem1061880 A B Fn Z a0 a1) (@lem1061879 A B Fn Z a0 a1)). Qed.
Lemma lem1061882 {A B : Type'} (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) : (term153 A B Fn Z a0 a1) = ((term117 A B Fn Z a0 a1) = (term150 A B Fn Z a0 a1)).
Proof. exact (@lem32 (term117 A B Fn Z a0 a1) (term150 A B Fn Z a0 a1)). Qed.
Lemma lem1061883 {A B : Type'} (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) : (term117 A B Fn Z a0 a1) = (term150 A B Fn Z a0 a1).
Proof. exact (EQ_MP (@lem1061882 A B Fn Z a0 a1) (@lem1061881 A B Fn Z a0 a1)). Qed.
Lemma lem1061884 {A B : Type'} (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) : (term154 A B Fn Z a0) = (term155 A B Fn Z a0).
Proof. exact (fun_ext (fun a1 : B => @lem1061883 A B Fn Z a0 a1)). Qed.
Lemma lem1061885 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1061886 {A B : Type'} (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) : (term118 A B Fn Z a0) = (term156 A B Fn Z a0).
Proof. exact (MK_COMB (@lem1061885 B) (@lem1061884 A B Fn Z a0)). Qed.
Lemma lem1061887 {A B : Type'} (Fn : type1592 A B) (Z : type1336 A B) : (term157 A B Fn Z) = (term158 A B Fn Z).
Proof. exact (fun_ext (fun a0 : recspace A => @lem1061886 A B Fn Z a0)). Qed.
Lemma lem1061888 {A : Type'} : (@all (recspace A)) = (@all (recspace A)).
Proof. exact (eq_refl (@all (recspace A))). Qed.
Lemma lem1061889 {A B : Type'} (Fn : type1592 A B) (Z : type1336 A B) : (term119 A B Fn Z) = (term159 A B Fn Z).
Proof. exact (MK_COMB (@lem1061888 A) (@lem1061887 A B Fn Z)). Qed.
Lemma lem1061890 {A B : Type'} (Fn : type1592 A B) (Z : type1336 A B) : (term102 A B Z Fn) = (term159 A B Fn Z).
Proof. exact (TRANS (@lem1061839 A B Fn Z) (@lem1061889 A B Fn Z)). Qed.
Lemma lem1061892 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem9104 A x) (@lem9103 A x)). Qed.
Lemma lem1061893 (x : Prop) : (x = x) = True.
Proof. exact (@lem1061892 Prop x). Qed.
Lemma lem1061894 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) : ((term160 A B b Fn Z) = (term160 A B b Fn Z)) = True.
Proof. exact (@lem1061893 (term160 A B b Fn Z)). Qed.
Lemma lem1061895 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) : True = ((term160 A B b Fn Z) = (term160 A B b Fn Z)).
Proof. exact (SYM (@lem1061894 A B b Fn Z)). Qed.
Lemma lem1061896 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) : (term160 A B b Fn Z) = (term160 A B b Fn Z).
Proof. exact (EQ_MP (@lem1061895 A B b Fn Z) (@lem0)). Qed.
Lemma lem1061897 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1061898 {A B : Type'} (b : B) (Z : type1336 A B) : (term161 A B Z b) = (term162 A B b Z).
Proof. exact (MK_COMB (@lem1061897) (@lem1061770 A B b Z)). Qed.
Lemma lem1061899 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) : (term163 A B b Z Fn) = (term160 A B b Fn Z).
Proof. exact (MK_COMB (@lem1061898 A B b Z) (@lem1061890 A B Fn Z)). Qed.
Lemma lem1061900 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) : (term163 A B b Z Fn) = (term160 A B b Fn Z).
Proof. exact (TRANS (@lem1061899 A B b Fn Z) (@lem1061896 A B b Fn Z)). Qed.
Lemma lem1061901 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term160 A B b Fn Z) : term160 A B b Fn Z.
Proof. exact (h1). Qed.
Lemma lem1061902 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term160 A B b Fn Z) : term159 A B Fn Z.
Proof. exact (proj2 (@lem1061901 A B b Fn Z h1)). Qed.
Lemma lem1061903 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term160 A B b Fn Z) : term85 A B b Z.
Proof. exact (proj1 (@lem1061901 A B b Fn Z h1)). Qed.
Lemma lem1061904 {A B : Type'} (a0 : recspace A) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term160 A B b Fn Z) : term164 A B b Z a0.
Proof. exact (@lem1061903 A B b Fn Z h1 a0). Qed.
Lemma lem1061905 {A B : Type'} (b : B) (Z : type1336 A B) (a0 : recspace A) : (term164 A B b Z a0) = (term84 A B b Z a0).
Proof. exact (eq_refl (term164 A B b Z a0)). Qed.
Lemma lem1061906 {A B : Type'} (a0 : recspace A) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term160 A B b Fn Z) : term84 A B b Z a0.
Proof. exact (EQ_MP (@lem1061905 A B b Z a0) (@lem1061904 A B a0 b Fn Z h1)). Qed.
Lemma lem1061907 {A B : Type'} (a0 : recspace A) (a1 : B) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term160 A B b Fn Z) : term165 A B b Z a0 a1.
Proof. exact (@lem1061906 A B a0 b Fn Z h1 a1). Qed.
Lemma lem1061908 {A B : Type'} (b : B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) : (term165 A B b Z a0 a1) = (term83 A B b Z a0 a1).
Proof. exact (eq_refl (term165 A B b Z a0 a1)). Qed.
Lemma lem1061909 {A B : Type'} (a0 : recspace A) (a1 : B) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term160 A B b Fn Z) : term83 A B b Z a0 a1.
Proof. exact (EQ_MP (@lem1061908 A B b Z a0 a1) (@lem1061907 A B a0 a1 b Fn Z h1)). Qed.
Lemma lem1061910 {A B : Type'} (a0 : recspace A) (a1 : B) (b : B) (h1 : term82 A B a0 a1 b) : term82 A B a0 a1 b.
Proof. exact (h1). Qed.
Lemma lem1061911 {A B : Type'} (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) (b : B) (h1 : term160 A B b Fn Z) (h2 : term82 A B a0 a1 b) : Z a0 a1.
Proof. exact (@lem1061909 A B a0 a1 b Fn Z h1 (@lem1061910 A B a0 a1 b h2)). Qed.
Lemma lem1061912 {A B : Type'} (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) (b : B) (h1 : term82 A B a0 a1 b) : term166 A B b Fn Z a0 a1.
Proof. exact (fun h0 : term160 A B b Fn Z => @lem1061911 A B Fn Z a0 a1 b h0 h1). Qed.
Lemma lem1061913 {A B : Type'} (a0 : recspace A) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term160 A B b Fn Z) : term167 A B Fn Z a0.
Proof. exact (@lem1061902 A B b Fn Z h1 a0). Qed.
Lemma lem1061914 {A B : Type'} (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) : (term167 A B Fn Z a0) = (term156 A B Fn Z a0).
Proof. exact (eq_refl (term167 A B Fn Z a0)). Qed.
Lemma lem1061915 {A B : Type'} (a0 : recspace A) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term160 A B b Fn Z) : term156 A B Fn Z a0.
Proof. exact (EQ_MP (@lem1061914 A B Fn Z a0) (@lem1061913 A B a0 b Fn Z h1)). Qed.
Lemma lem1061916 {A B : Type'} (a0 : recspace A) (a1 : B) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term160 A B b Fn Z) : term168 A B Fn Z a0 a1.
Proof. exact (@lem1061915 A B a0 b Fn Z h1 a1). Qed.
Lemma lem1061917 {A B : Type'} (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) : (term168 A B Fn Z a0 a1) = (term150 A B Fn Z a0 a1).
Proof. exact (eq_refl (term168 A B Fn Z a0 a1)). Qed.
Lemma lem1061918 {A B : Type'} (a0 : recspace A) (a1 : B) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term160 A B b Fn Z) : term150 A B Fn Z a0 a1.
Proof. exact (EQ_MP (@lem1061917 A B Fn Z a0 a1) (@lem1061916 A B a0 a1 b Fn Z h1)). Qed.
Lemma lem1061919 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term148 A B a0 a1 Fn Z) : term148 A B a0 a1 Fn Z.
Proof. exact (h1). Qed.
Lemma lem1061920 {A B : Type'} (a0 : recspace A) (a1 : B) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term148 A B a0 a1 Fn Z) (h2 : term160 A B b Fn Z) : Z a0 a1.
Proof. exact (@lem1061918 A B a0 a1 b Fn Z h2 (@lem1061919 A B a0 a1 Fn Z h1)). Qed.
Lemma lem1061921 {A B : Type'} (b : B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term148 A B a0 a1 Fn Z) : term166 A B b Fn Z a0 a1.
Proof. exact (fun h0 : term160 A B b Fn Z => @lem1061920 A B a0 a1 b Fn Z h1 h0). Qed.
Lemma lem1061922 {A B : Type'} (b : B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term169 A B b a0 a1 Fn Z) : term169 A B b a0 a1 Fn Z.
Proof. exact (h1). Qed.
Lemma lem1061923 {A B : Type'} (b : B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term169 A B b a0 a1 Fn Z) : term166 A B b Fn Z a0 a1.
Proof. exact (or_elim (@lem1061922 A B b a0 a1 Fn Z h1) (fun h0 : term82 A B a0 a1 b => @lem1061912 A B Fn Z a0 a1 b h0) (fun h0 : term148 A B a0 a1 Fn Z => @lem1061921 A B b a0 a1 Fn Z h0)). Qed.
Lemma lem1061924 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term160 A B b Fn Z) : term160 A B b Fn Z.
Proof. exact (h1). Qed.
Lemma lem1061925 {A B : Type'} (b : B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term160 A B b Fn Z) (h2 : term169 A B b a0 a1 Fn Z) : Z a0 a1.
Proof. exact (@lem1061923 A B b a0 a1 Fn Z h2 (@lem1061924 A B b Fn Z h1)). Qed.
Lemma lem1061926 {A B : Type'} (a0 : recspace A) (a1 : B) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term160 A B b Fn Z) : term170 A B b Fn Z a0 a1.
Proof. exact (fun h0 : term169 A B b a0 a1 Fn Z => @lem1061925 A B b a0 a1 Fn Z h1 h0). Qed.
Lemma lem1061927 {A B : Type'} (a0 : recspace A) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term160 A B b Fn Z) : term171 A B b Fn Z a0.
Proof. exact (fun a1 : B => @lem1061926 A B a0 a1 b Fn Z h1). Qed.
Lemma lem1061928 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term160 A B b Fn Z) : term172 A B b Fn Z.
Proof. exact (fun a0 : recspace A => @lem1061927 A B a0 b Fn Z h1). Qed.
Lemma lem1061929 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term172 A B b Fn Z) : term172 A B b Fn Z.
Proof. exact (h1). Qed.
Lemma lem1061930 {A B : Type'} (a0 : recspace A) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term172 A B b Fn Z) : term173 A B b Fn Z a0.
Proof. exact (@lem1061929 A B b Fn Z h1 a0). Qed.
Lemma lem1061931 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) : (term173 A B b Fn Z a0) = (term171 A B b Fn Z a0).
Proof. exact (eq_refl (term173 A B b Fn Z a0)). Qed.
Lemma lem1061932 {A B : Type'} (a0 : recspace A) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term172 A B b Fn Z) : term171 A B b Fn Z a0.
Proof. exact (EQ_MP (@lem1061931 A B b Fn Z a0) (@lem1061930 A B a0 b Fn Z h1)). Qed.
Lemma lem1061933 {A B : Type'} (a0 : recspace A) (a1 : B) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term172 A B b Fn Z) : term174 A B b Fn Z a0 a1.
Proof. exact (@lem1061932 A B a0 b Fn Z h1 a1). Qed.
Lemma lem1061934 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) : (term174 A B b Fn Z a0 a1) = (term170 A B b Fn Z a0 a1).
Proof. exact (eq_refl (term174 A B b Fn Z a0 a1)). Qed.
Lemma lem1061935 {A B : Type'} (a0 : recspace A) (a1 : B) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term172 A B b Fn Z) : term170 A B b Fn Z a0 a1.
Proof. exact (EQ_MP (@lem1061934 A B b Fn Z a0 a1) (@lem1061933 A B a0 a1 b Fn Z h1)). Qed.
Lemma lem1061936 {A B : Type'} (b : B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term169 A B b a0 a1 Fn Z) : term169 A B b a0 a1 Fn Z.
Proof. exact (h1). Qed.
Lemma lem1061937 {A B : Type'} (b : B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term172 A B b Fn Z) (h2 : term169 A B b a0 a1 Fn Z) : Z a0 a1.
Proof. exact (@lem1061935 A B a0 a1 b Fn Z h1 (@lem1061936 A B b a0 a1 Fn Z h2)). Qed.
Lemma lem1061938 {A B : Type'} (b : B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term169 A B b a0 a1 Fn Z) : term175 A B b Fn Z a0 a1.
Proof. exact (fun h0 : term172 A B b Fn Z => @lem1061937 A B b a0 a1 Fn Z h0 h1). Qed.
Lemma lem1061939 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term148 A B a0 a1 Fn Z) : term148 A B a0 a1 Fn Z.
Proof. exact (h1). Qed.
Lemma lem1061940 {A B : Type'} (b : B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term148 A B a0 a1 Fn Z) : term169 A B b a0 a1 Fn Z.
Proof. exact (or_intro2 (term82 A B a0 a1 b) (@lem1061939 A B a0 a1 Fn Z h1)). Qed.
Lemma lem1061941 {A B : Type'} (b : B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term148 A B a0 a1 Fn Z) : (term169 A B b a0 a1 Fn Z) = (term175 A B b Fn Z a0 a1).
Proof. exact (prop_ext (fun h2 : term169 A B b a0 a1 Fn Z => @lem1061938 A B b a0 a1 Fn Z h2) (fun h2 : term175 A B b Fn Z a0 a1 => @lem1061940 A B b a0 a1 Fn Z h1)). Qed.
Lemma lem1061942 {A B : Type'} (b : B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term148 A B a0 a1 Fn Z) : term175 A B b Fn Z a0 a1.
Proof. exact (EQ_MP (@lem1061941 A B b a0 a1 Fn Z h1) (@lem1061940 A B b a0 a1 Fn Z h1)). Qed.
Lemma lem1061943 {A B : Type'} (a0 : recspace A) (a1 : B) (b : B) (h1 : term82 A B a0 a1 b) : term82 A B a0 a1 b.
Proof. exact (h1). Qed.
Lemma lem1061944 {A B : Type'} (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) (b : B) (h1 : term82 A B a0 a1 b) : term169 A B b a0 a1 Fn Z.
Proof. exact (or_intro1 (@lem1061943 A B a0 a1 b h1) (term148 A B a0 a1 Fn Z)). Qed.
Lemma lem1061945 {A B : Type'} (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) (b : B) (h1 : term82 A B a0 a1 b) : (term169 A B b a0 a1 Fn Z) = (term175 A B b Fn Z a0 a1).
Proof. exact (prop_ext (fun h2 : term169 A B b a0 a1 Fn Z => @lem1061938 A B b a0 a1 Fn Z h2) (fun h2 : term175 A B b Fn Z a0 a1 => @lem1061944 A B Fn Z a0 a1 b h1)). Qed.
Lemma lem1061946 {A B : Type'} (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) (b : B) (h1 : term82 A B a0 a1 b) : term175 A B b Fn Z a0 a1.
Proof. exact (EQ_MP (@lem1061945 A B Fn Z a0 a1 b h1) (@lem1061944 A B Fn Z a0 a1 b h1)). Qed.
Lemma lem1061947 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term172 A B b Fn Z) : term172 A B b Fn Z.
Proof. exact (h1). Qed.
Lemma lem1061948 {A B : Type'} (b : B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term172 A B b Fn Z) (h2 : term148 A B a0 a1 Fn Z) : Z a0 a1.
Proof. exact (@lem1061942 A B b a0 a1 Fn Z h2 (@lem1061947 A B b Fn Z h1)). Qed.
Lemma lem1061949 {A B : Type'} (a0 : recspace A) (a1 : B) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term172 A B b Fn Z) : term150 A B Fn Z a0 a1.
Proof. exact (fun h0 : term148 A B a0 a1 Fn Z => @lem1061948 A B b a0 a1 Fn Z h1 h0). Qed.
Lemma lem1061950 {A B : Type'} (a0 : recspace A) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term172 A B b Fn Z) : term156 A B Fn Z a0.
Proof. exact (fun a1 : B => @lem1061949 A B a0 a1 b Fn Z h1). Qed.
Lemma lem1061951 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term172 A B b Fn Z) : term159 A B Fn Z.
Proof. exact (fun a0 : recspace A => @lem1061950 A B a0 b Fn Z h1). Qed.
Lemma lem1061952 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term172 A B b Fn Z) : term172 A B b Fn Z.
Proof. exact (h1). Qed.
Lemma lem1061953 {A B : Type'} (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) (b : B) (h1 : term172 A B b Fn Z) (h2 : term82 A B a0 a1 b) : Z a0 a1.
Proof. exact (@lem1061946 A B Fn Z a0 a1 b h2 (@lem1061952 A B b Fn Z h1)). Qed.
Lemma lem1061954 {A B : Type'} (a0 : recspace A) (a1 : B) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term172 A B b Fn Z) : term83 A B b Z a0 a1.
Proof. exact (fun h0 : term82 A B a0 a1 b => @lem1061953 A B Fn Z a0 a1 b h1 h0). Qed.
Lemma lem1061955 {A B : Type'} (a0 : recspace A) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term172 A B b Fn Z) : term84 A B b Z a0.
Proof. exact (fun a1 : B => @lem1061954 A B a0 a1 b Fn Z h1). Qed.
Lemma lem1061956 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term172 A B b Fn Z) : term85 A B b Z.
Proof. exact (fun a0 : recspace A => @lem1061955 A B a0 b Fn Z h1). Qed.
Lemma lem1061957 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term172 A B b Fn Z) : term160 A B b Fn Z.
Proof. exact (conj (@lem1061956 A B b Fn Z h1) (@lem1061951 A B b Fn Z h1)). Qed.
Lemma lem1061958 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) : term176 A B b Fn Z.
Proof. exact (fun h0 : term172 A B b Fn Z => @lem1061957 A B b Fn Z h0). Qed.
Lemma lem1061959 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) : term177 A B b Fn Z.
Proof. exact (fun h0 : term160 A B b Fn Z => @lem1061928 A B b Fn Z h0). Qed.
Lemma lem1061960 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) : term178 A B b Fn Z.
Proof. exact (conj (@lem1061959 A B b Fn Z) (@lem1061958 A B b Fn Z)). Qed.
Lemma lem1061961 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) : (term178 A B b Fn Z) = ((term160 A B b Fn Z) = (term172 A B b Fn Z)).
Proof. exact (@lem32 (term160 A B b Fn Z) (term172 A B b Fn Z)). Qed.
Lemma lem1061962 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) : (term160 A B b Fn Z) = (term172 A B b Fn Z).
Proof. exact (EQ_MP (@lem1061961 A B b Fn Z) (@lem1061960 A B b Fn Z)). Qed.
Lemma lem1061963 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) : (term163 A B b Z Fn) = (term172 A B b Fn Z).
Proof. exact (TRANS (@lem1061900 A B b Fn Z) (@lem1061962 A B b Fn Z)). Qed.
Lemma lem1061964 {A B : Type'} (b : B) (Z : type1336 A B) (Fn : type1592 A B) : (term172 A B b Fn Z) = (term163 A B b Z Fn).
Proof. exact (SYM (@lem1061963 A B b Fn Z)). Qed.
Lemma lem1061965 {A B : Type'} (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : Z = (term179 A B b Fn)) : Z = (term179 A B b Fn).
Proof. exact (h1). Qed.
Lemma lem1061966 {A : Type'} (a0 : recspace A) : a0 = a0.
Proof. exact (eq_refl a0). Qed.
Lemma lem1061967 {A B : Type'} (a0 : recspace A) (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : Z = (term179 A B b Fn)) : (Z a0) = (term180 A B b Fn a0).
Proof. exact (MK_COMB (@lem1061965 A B Z b Fn h1) (@lem1061966 A a0)). Qed.
Lemma lem1061968 {A B : Type'} (b : B) (Fn : type1592 A B) (a0 : recspace A) : (term180 A B b Fn a0) = (term181 A B b Fn a0).
Proof. exact (eq_refl (term180 A B b Fn a0)). Qed.
Lemma lem1061969 {A B : Type'} (Z : type1336 A B) (a0 : recspace A) : (term182 A B Z a0) = (term182 A B Z a0).
Proof. exact (eq_refl (term182 A B Z a0)). Qed.
Lemma lem1061970 {A B : Type'} (Z : type1336 A B) (b : B) (Fn : type1592 A B) (a0 : recspace A) : ((Z a0) = (term180 A B b Fn a0)) = ((Z a0) = (term181 A B b Fn a0)).
Proof. exact (MK_COMB (@lem1061969 A B Z a0) (@lem1061968 A B b Fn a0)). Qed.
Lemma lem1061971 {A B : Type'} (a0 : recspace A) (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : Z = (term179 A B b Fn)) : (Z a0) = (term181 A B b Fn a0).
Proof. exact (EQ_MP (@lem1061970 A B Z b Fn a0) (@lem1061967 A B a0 Z b Fn h1)). Qed.
Lemma lem1061972 {B : Type'} (a1 : B) : a1 = a1.
Proof. exact (eq_refl a1). Qed.
Lemma lem1061973 {A B : Type'} (a0 : recspace A) (a1 : B) (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : Z = (term179 A B b Fn)) : (Z a0 a1) = (term183 A B b Fn a0 a1).
Proof. exact (MK_COMB (@lem1061971 A B a0 Z b Fn h1) (@lem1061972 B a1)). Qed.
Lemma lem1061974 {A B : Type'} (b : B) (Fn : type1592 A B) (a0 : recspace A) (a1 : B) : (term183 A B b Fn a0 a1) = (term184 A B b Fn a0 a1).
Proof. exact (eq_refl (term183 A B b Fn a0 a1)). Qed.
Lemma lem1061975 {A B : Type'} (Z : type1336 A B) (a0 : recspace A) (a1 : B) : (term185 A B Z a0 a1) = (term185 A B Z a0 a1).
Proof. exact (eq_refl (term185 A B Z a0 a1)). Qed.
Lemma lem1061976 {A B : Type'} (Z : type1336 A B) (b : B) (Fn : type1592 A B) (a0 : recspace A) (a1 : B) : ((Z a0 a1) = (term183 A B b Fn a0 a1)) = ((Z a0 a1) = (term184 A B b Fn a0 a1)).
Proof. exact (MK_COMB (@lem1061975 A B Z a0 a1) (@lem1061974 A B b Fn a0 a1)). Qed.
Lemma lem1061977 {A B : Type'} (a0 : recspace A) (a1 : B) (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : Z = (term179 A B b Fn)) : (Z a0 a1) = (term184 A B b Fn a0 a1).
Proof. exact (EQ_MP (@lem1061976 A B Z b Fn a0 a1) (@lem1061973 A B a0 a1 Z b Fn h1)). Qed.
Lemma lem1061978 {A B : Type'} (a0 : recspace A) (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : Z = (term179 A B b Fn)) : term186 A B Z b Fn a0.
Proof. exact (fun a1 : B => @lem1061977 A B a0 a1 Z b Fn h1). Qed.
Lemma lem1061979 {A B : Type'} (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : Z = (term179 A B b Fn)) : term187 A B Z b Fn.
Proof. exact (fun a0 : recspace A => @lem1061978 A B a0 Z b Fn h1). Qed.
Lemma lem1061980 {A B : Type'} (a0 : recspace A) (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : Z = (term179 A B b Fn)) : term188 A B Z b Fn a0.
Proof. exact (@lem1061979 A B Z b Fn h1 a0). Qed.
Lemma lem1061981 {A B : Type'} (Z : type1336 A B) (b : B) (Fn : type1592 A B) (a0 : recspace A) : (term188 A B Z b Fn a0) = (term186 A B Z b Fn a0).
Proof. exact (eq_refl (term188 A B Z b Fn a0)). Qed.
Lemma lem1061982 {A B : Type'} (a0 : recspace A) (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : Z = (term179 A B b Fn)) : term186 A B Z b Fn a0.
Proof. exact (EQ_MP (@lem1061981 A B Z b Fn a0) (@lem1061980 A B a0 Z b Fn h1)). Qed.
Lemma lem1061983 {A B : Type'} (a0 : recspace A) (a1 : B) (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : Z = (term179 A B b Fn)) : term189 A B Z b Fn a0 a1.
Proof. exact (@lem1061982 A B a0 Z b Fn h1 a1). Qed.
Lemma lem1061984 {A B : Type'} (Z : type1336 A B) (b : B) (Fn : type1592 A B) (a0 : recspace A) (a1 : B) : (term189 A B Z b Fn a0 a1) = ((Z a0 a1) = (term184 A B b Fn a0 a1)).
Proof. exact (eq_refl (term189 A B Z b Fn a0 a1)). Qed.
Lemma lem1061985 {A B : Type'} (a0 : recspace A) (a1 : B) (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : Z = (term179 A B b Fn)) : (Z a0 a1) = (term184 A B b Fn a0 a1).
Proof. exact (EQ_MP (@lem1061984 A B Z b Fn a0 a1) (@lem1061983 A B a0 a1 Z b Fn h1)). Qed.
Lemma lem1061988 {A B : Type'} (Z : type1336 A B) (b : B) (Fn : type1592 A B) (a0 : recspace A) (a1 : B) : term190 A B Z b Fn a0 a1.
Proof. exact (@lem37 (Z a0 a1) (term184 A B b Fn a0 a1)). Qed.
Lemma lem1061989 {A B : Type'} (a0 : recspace A) (a1 : B) (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : Z = (term179 A B b Fn)) : term191 A B Z b Fn a0 a1.
Proof. exact (@lem1061988 A B Z b Fn a0 a1 (@lem1061985 A B a0 a1 Z b Fn h1)). Qed.
Lemma lem1061990 {A B : Type'} (Z : type1336 A B) (a0 : recspace A) (a1 : B) (h1 : Z a0 a1) : Z a0 a1.
Proof. exact (h1). Qed.
Lemma lem1061991 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) (h1 : Z = (term179 A B b Fn)) (h2 : Z a0 a1) : term184 A B b Fn a0 a1.
Proof. exact (@lem1061989 A B a0 a1 Z b Fn h1 (@lem1061990 A B Z a0 a1 h2)). Qed.
Lemma lem1061992 {A B : Type'} (Z' : type1336 A B) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) (h1 : Z = (term179 A B b Fn)) (h2 : Z a0 a1) : term192 A B b Fn a0 a1 Z'.
Proof. exact (@lem1061991 A B b Fn Z a0 a1 h1 h2 Z'). Qed.
Lemma lem1061993 {A B : Type'} (b : B) (Fn : type1592 A B) (Z' : type1336 A B) (a0 : recspace A) (a1 : B) : (term192 A B b Fn a0 a1 Z') = (term175 A B b Fn Z' a0 a1).
Proof. exact (eq_refl (term192 A B b Fn a0 a1 Z')). Qed.
Lemma lem1061994 {A B : Type'} (Z' : type1336 A B) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) (h1 : Z = (term179 A B b Fn)) (h2 : Z a0 a1) : term175 A B b Fn Z' a0 a1.
Proof. exact (EQ_MP (@lem1061993 A B b Fn Z' a0 a1) (@lem1061992 A B Z' b Fn Z a0 a1 h1 h2)). Qed.
Lemma lem1061995 {A B : Type'} (b : B) (Fn : type1592 A B) (Z' : type1336 A B) (h1 : term172 A B b Fn Z') : term172 A B b Fn Z'.
Proof. exact (h1). Qed.
Lemma lem1061996 {A B : Type'} (Z' : type1336 A B) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) (h1 : term172 A B b Fn Z') (h2 : Z = (term179 A B b Fn)) (h3 : Z a0 a1) : Z' a0 a1.
Proof. exact (@lem1061994 A B Z' b Fn Z a0 a1 h2 h3 (@lem1061995 A B b Fn Z' h1)). Qed.
Lemma lem1061997 {A B : Type'} (a0 : recspace A) (a1 : B) (Z' : type1336 A B) (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : term172 A B b Fn Z') (h2 : Z = (term179 A B b Fn)) : term193 A B Z Z' a0 a1.
Proof. exact (fun h0 : Z a0 a1 => @lem1061996 A B Z' b Fn Z a0 a1 h1 h2 h0). Qed.
Lemma lem1061998 {A B : Type'} (a0 : recspace A) (Z' : type1336 A B) (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : term172 A B b Fn Z') (h2 : Z = (term179 A B b Fn)) : term194 A B Z Z' a0.
Proof. exact (fun a1 : B => @lem1061997 A B a0 a1 Z' Z b Fn h1 h2). Qed.
Lemma lem1061999 {A B : Type'} (Z' : type1336 A B) (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : term172 A B b Fn Z') (h2 : Z = (term179 A B b Fn)) : term195 A B Z Z'.
Proof. exact (fun a0 : recspace A => @lem1061998 A B a0 Z' Z b Fn h1 h2). Qed.
Lemma lem1062000 {A B : Type'} (Z' : type1336 A B) (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : Z = (term179 A B b Fn)) : term196 A B b Fn Z Z'.
Proof. exact (fun h0 : term172 A B b Fn Z' => @lem1061999 A B Z' Z b Fn h0 h1). Qed.
Lemma lem1062001 {A B : Type'} (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : Z = (term179 A B b Fn)) : term197 A B b Fn Z.
Proof. exact (fun Z' : type1336 A B => @lem1062000 A B Z' Z b Fn h1). Qed.
Lemma lem1062002 {A B : Type'} (b : B) (Fn : type1592 A B) (h1 : term198 A B b Fn) : term198 A B b Fn.
Proof. exact (h1). Qed.
Lemma lem1062003 {A B : Type'} (b : B) (Fn : type1592 A B) (Z' : type1336 A B) (h1 : term172 A B b Fn Z') : term172 A B b Fn Z'.
Proof. exact (h1). Qed.
Lemma lem1062004 {A B : Type'} (Z' : type1336 A B) (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : Z = (term179 A B b Fn)) : term199 A B b Fn Z Z'.
Proof. exact (@lem1062001 A B Z b Fn h1 Z'). Qed.
Lemma lem1062005 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (Z' : type1336 A B) : (term199 A B b Fn Z Z') = (term196 A B b Fn Z Z').
Proof. exact (eq_refl (term199 A B b Fn Z Z')). Qed.
Lemma lem1062006 {A B : Type'} (Z' : type1336 A B) (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : Z = (term179 A B b Fn)) : term196 A B b Fn Z Z'.
Proof. exact (EQ_MP (@lem1062005 A B b Fn Z Z') (@lem1062004 A B Z' Z b Fn h1)). Qed.
Lemma lem1062007 {A B : Type'} (Z' : type1336 A B) (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : term172 A B b Fn Z') (h2 : Z = (term179 A B b Fn)) : term195 A B Z Z'.
Proof. exact (@lem1062006 A B Z' Z b Fn h2 (@lem1062003 A B b Fn Z' h1)). Qed.
Lemma lem1062008 {A B : Type'} (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : term198 A B b Fn) : term200 A B b Fn Z.
Proof. exact (@lem1062002 A B b Fn h1 Z). Qed.
Lemma lem1062009 {A B : Type'} (Z : type1336 A B) (b : B) (Fn : type1592 A B) : (term200 A B b Fn Z) = (term201 A B Z b Fn).
Proof. exact (eq_refl (term200 A B b Fn Z)). Qed.
Lemma lem1062010 {A B : Type'} (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : term198 A B b Fn) : term201 A B Z b Fn.
Proof. exact (EQ_MP (@lem1062009 A B Z b Fn) (@lem1062008 A B Z b Fn h1)). Qed.
Lemma lem1062011 {A B : Type'} (Z : type1336 A B) (Z' : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : term198 A B b Fn) : term202 A B Z b Fn Z'.
Proof. exact (@lem1062010 A B Z b Fn h1 Z'). Qed.
Lemma lem1062012 {A B : Type'} (Z : type1336 A B) (b : B) (Fn : type1592 A B) (Z' : type1336 A B) : (term202 A B Z b Fn Z') = (term203 A B Z b Fn Z').
Proof. exact (eq_refl (term202 A B Z b Fn Z')). Qed.
Lemma lem1062013 {A B : Type'} (Z : type1336 A B) (Z' : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : term198 A B b Fn) : term203 A B Z b Fn Z'.
Proof. exact (EQ_MP (@lem1062012 A B Z b Fn Z') (@lem1062011 A B Z Z' b Fn h1)). Qed.
Lemma lem1062014 {A B : Type'} (Z' : type1336 A B) (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : term198 A B b Fn) (h2 : term172 A B b Fn Z') (h3 : Z = (term179 A B b Fn)) : term204 A B Z b Fn Z'.
Proof. exact (@lem1062013 A B Z Z' b Fn h1 (@lem1062007 A B Z' Z b Fn h2 h3)). Qed.
Lemma lem1062015 {A B : Type'} (a0 : recspace A) (b : B) (Fn : type1592 A B) (Z' : type1336 A B) (h1 : term172 A B b Fn Z') : term173 A B b Fn Z' a0.
Proof. exact (@lem1062003 A B b Fn Z' h1 a0). Qed.
Lemma lem1062016 {A B : Type'} (b : B) (Fn : type1592 A B) (Z' : type1336 A B) (a0 : recspace A) : (term173 A B b Fn Z' a0) = (term171 A B b Fn Z' a0).
Proof. exact (eq_refl (term173 A B b Fn Z' a0)). Qed.
Lemma lem1062017 {A B : Type'} (a0 : recspace A) (b : B) (Fn : type1592 A B) (Z' : type1336 A B) (h1 : term172 A B b Fn Z') : term171 A B b Fn Z' a0.
Proof. exact (EQ_MP (@lem1062016 A B b Fn Z' a0) (@lem1062015 A B a0 b Fn Z' h1)). Qed.
Lemma lem1062018 {A B : Type'} (a0 : recspace A) (a1 : B) (b : B) (Fn : type1592 A B) (Z' : type1336 A B) (h1 : term172 A B b Fn Z') : term174 A B b Fn Z' a0 a1.
Proof. exact (@lem1062017 A B a0 b Fn Z' h1 a1). Qed.
Lemma lem1062019 {A B : Type'} (b : B) (Fn : type1592 A B) (Z' : type1336 A B) (a0 : recspace A) (a1 : B) : (term174 A B b Fn Z' a0 a1) = (term170 A B b Fn Z' a0 a1).
Proof. exact (eq_refl (term174 A B b Fn Z' a0 a1)). Qed.
Lemma lem1062020 {A B : Type'} (a0 : recspace A) (a1 : B) (b : B) (Fn : type1592 A B) (Z' : type1336 A B) (h1 : term172 A B b Fn Z') : term170 A B b Fn Z' a0 a1.
Proof. exact (EQ_MP (@lem1062019 A B b Fn Z' a0 a1) (@lem1062018 A B a0 a1 b Fn Z' h1)). Qed.
Lemma lem1062021 {A B : Type'} (a0 : recspace A) (Z' : type1336 A B) (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : term198 A B b Fn) (h2 : term172 A B b Fn Z') (h3 : Z = (term179 A B b Fn)) : term205 A B Z b Fn Z' a0.
Proof. exact (@lem1062014 A B Z' Z b Fn h1 h2 h3 a0). Qed.
Lemma lem1062022 {A B : Type'} (Z : type1336 A B) (b : B) (a0 : recspace A) (Fn : type1592 A B) (Z' : type1336 A B) : (term205 A B Z b Fn Z' a0) = (term206 A B Z b a0 Fn Z').
Proof. exact (eq_refl (term205 A B Z b Fn Z' a0)). Qed.
Lemma lem1062023 {A B : Type'} (a0 : recspace A) (Z' : type1336 A B) (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : term198 A B b Fn) (h2 : term172 A B b Fn Z') (h3 : Z = (term179 A B b Fn)) : term206 A B Z b a0 Fn Z'.
Proof. exact (EQ_MP (@lem1062022 A B Z b a0 Fn Z') (@lem1062021 A B a0 Z' Z b Fn h1 h2 h3)). Qed.
Lemma lem1062024 {A B : Type'} (a0 : recspace A) (a1 : B) (Z' : type1336 A B) (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : term198 A B b Fn) (h2 : term172 A B b Fn Z') (h3 : Z = (term179 A B b Fn)) : term207 A B Z b a0 Fn Z' a1.
Proof. exact (@lem1062023 A B a0 Z' Z b Fn h1 h2 h3 a1). Qed.
Lemma lem1062025 {A B : Type'} (Z : type1336 A B) (b : B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z' : type1336 A B) : (term207 A B Z b a0 Fn Z' a1) = (term208 A B Z b a0 a1 Fn Z').
Proof. exact (eq_refl (term207 A B Z b a0 Fn Z' a1)). Qed.
Lemma lem1062026 {A B : Type'} (a0 : recspace A) (a1 : B) (Z' : type1336 A B) (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : term198 A B b Fn) (h2 : term172 A B b Fn Z') (h3 : Z = (term179 A B b Fn)) : term208 A B Z b a0 a1 Fn Z'.
Proof. exact (EQ_MP (@lem1062025 A B Z b a0 a1 Fn Z') (@lem1062024 A B a0 a1 Z' Z b Fn h1 h2 h3)). Qed.
Lemma lem1062027 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (Z' : type1336 A B) (a0 : recspace A) (a1 : B) : term209 A B b Fn Z Z' a0 a1.
Proof. exact (@lem51 (term169 A B b a0 a1 Fn Z') (term169 A B b a0 a1 Fn Z) (Z' a0 a1)). Qed.
Lemma lem1062028 {A B : Type'} (a0 : recspace A) (a1 : B) (Z' : type1336 A B) (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : term198 A B b Fn) (h2 : term172 A B b Fn Z') (h3 : Z = (term179 A B b Fn)) : term210 A B b Fn Z Z' a0 a1.
Proof. exact (@lem1062027 A B b Fn Z Z' a0 a1 (@lem1062026 A B a0 a1 Z' Z b Fn h1 h2 h3)). Qed.
Lemma lem1062029 {A B : Type'} (a0 : recspace A) (a1 : B) (Z' : type1336 A B) (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : term198 A B b Fn) (h2 : term172 A B b Fn Z') (h3 : Z = (term179 A B b Fn)) : term211 A B b Fn Z Z' a0 a1.
Proof. exact (@lem1062028 A B a0 a1 Z' Z b Fn h1 h2 h3 (@lem1062020 A B a0 a1 b Fn Z' h2)). Qed.
Lemma lem1062030 {A B : Type'} (b : B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term169 A B b a0 a1 Fn Z) : term169 A B b a0 a1 Fn Z.
Proof. exact (h1). Qed.
Lemma lem1062031 {A B : Type'} (Z' : type1336 A B) (b : B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term198 A B b Fn) (h2 : term172 A B b Fn Z') (h3 : Z = (term179 A B b Fn)) (h4 : term169 A B b a0 a1 Fn Z) : Z' a0 a1.
Proof. exact (@lem1062029 A B a0 a1 Z' Z b Fn h1 h2 h3 (@lem1062030 A B b a0 a1 Fn Z h4)). Qed.
Lemma lem1062032 {A B : Type'} (Z' : type1336 A B) (b : B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term198 A B b Fn) (h2 : Z = (term179 A B b Fn)) (h3 : term169 A B b a0 a1 Fn Z) : term175 A B b Fn Z' a0 a1.
Proof. exact (fun h0 : term172 A B b Fn Z' => @lem1062031 A B Z' b a0 a1 Fn Z h1 h0 h2 h3). Qed.
Lemma lem1062033 {A B : Type'} (b : B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term198 A B b Fn) (h2 : Z = (term179 A B b Fn)) (h3 : term169 A B b a0 a1 Fn Z) : term184 A B b Fn a0 a1.
Proof. exact (fun Z' : type1336 A B => @lem1062032 A B Z' b a0 a1 Fn Z h1 h2 h3). Qed.
Lemma lem1062034 {A B : Type'} (a0 : recspace A) (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : Z = (term179 A B b Fn)) : term188 A B Z b Fn a0.
Proof. exact (@lem1061979 A B Z b Fn h1 a0). Qed.
Lemma lem1062035 {A B : Type'} (Z : type1336 A B) (b : B) (Fn : type1592 A B) (a0 : recspace A) : (term188 A B Z b Fn a0) = (term186 A B Z b Fn a0).
Proof. exact (eq_refl (term188 A B Z b Fn a0)). Qed.
Lemma lem1062036 {A B : Type'} (a0 : recspace A) (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : Z = (term179 A B b Fn)) : term186 A B Z b Fn a0.
Proof. exact (EQ_MP (@lem1062035 A B Z b Fn a0) (@lem1062034 A B a0 Z b Fn h1)). Qed.
Lemma lem1062037 {A B : Type'} (a0 : recspace A) (a1 : B) (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : Z = (term179 A B b Fn)) : term189 A B Z b Fn a0 a1.
Proof. exact (@lem1062036 A B a0 Z b Fn h1 a1). Qed.
Lemma lem1062038 {A B : Type'} (Z : type1336 A B) (b : B) (Fn : type1592 A B) (a0 : recspace A) (a1 : B) : (term189 A B Z b Fn a0 a1) = ((Z a0 a1) = (term184 A B b Fn a0 a1)).
Proof. exact (eq_refl (term189 A B Z b Fn a0 a1)). Qed.
Lemma lem1062039 {A B : Type'} (a0 : recspace A) (a1 : B) (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : Z = (term179 A B b Fn)) : (Z a0 a1) = (term184 A B b Fn a0 a1).
Proof. exact (EQ_MP (@lem1062038 A B Z b Fn a0 a1) (@lem1062037 A B a0 a1 Z b Fn h1)). Qed.
Lemma lem1062040 {A B : Type'} (a0 : recspace A) (a1 : B) (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : Z = (term179 A B b Fn)) : (term184 A B b Fn a0 a1) = (Z a0 a1).
Proof. exact (SYM (@lem1062039 A B a0 a1 Z b Fn h1)). Qed.
Lemma lem1062041 {A B : Type'} (b : B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term198 A B b Fn) (h2 : Z = (term179 A B b Fn)) (h3 : term169 A B b a0 a1 Fn Z) : Z a0 a1.
Proof. exact (EQ_MP (@lem1062040 A B a0 a1 Z b Fn h2) (@lem1062033 A B b a0 a1 Fn Z h1 h2 h3)). Qed.
Lemma lem1062042 {A B : Type'} (a0 : recspace A) (a1 : B) (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : term198 A B b Fn) (h2 : Z = (term179 A B b Fn)) : term170 A B b Fn Z a0 a1.
Proof. exact (fun h0 : term169 A B b a0 a1 Fn Z => @lem1062041 A B b a0 a1 Fn Z h1 h2 h0). Qed.
Lemma lem1062043 {A B : Type'} (a0 : recspace A) (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : term198 A B b Fn) (h2 : Z = (term179 A B b Fn)) : term171 A B b Fn Z a0.
Proof. exact (fun a1 : B => @lem1062042 A B a0 a1 Z b Fn h1 h2). Qed.
Lemma lem1062044 {A B : Type'} (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : term198 A B b Fn) (h2 : Z = (term179 A B b Fn)) : term172 A B b Fn Z.
Proof. exact (fun a0 : recspace A => @lem1062043 A B a0 Z b Fn h1 h2). Qed.
Lemma lem1062047 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) : (term212 A B b Fn Z a0) = (term212 A B b Fn Z a0).
Proof. exact (eq_refl (term212 A B b Fn Z a0)). Qed.
Lemma lem1062048 {A B : Type'} (b : B) (a0 : recspace A) (Fn : type1592 A B) (Z : type1336 A B) : (term212 A B b Fn Z a0) = (term213 A B b a0 Fn Z).
Proof. exact (eq_refl (term212 A B b Fn Z a0)). Qed.
Lemma lem1062049 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) : (term214 A B b Fn Z a0) = (term214 A B b Fn Z a0).
Proof. exact (eq_refl (term214 A B b Fn Z a0)). Qed.
Lemma lem1062050 {A B : Type'} (b : B) (a0 : recspace A) (Fn : type1592 A B) (Z : type1336 A B) : ((term212 A B b Fn Z a0) = (term212 A B b Fn Z a0)) = ((term212 A B b Fn Z a0) = (term213 A B b a0 Fn Z)).
Proof. exact (MK_COMB (@lem1062049 A B b Fn Z a0) (@lem1062048 A B b a0 Fn Z)). Qed.
Lemma lem1062051 {A B : Type'} (b : B) (a0 : recspace A) (Fn : type1592 A B) (Z : type1336 A B) : (term212 A B b Fn Z a0) = (term213 A B b a0 Fn Z).
Proof. exact (EQ_MP (@lem1062050 A B b a0 Fn Z) (@lem1062047 A B b Fn Z a0)). Qed.
Lemma lem1062052 {B : Type'} (a1 : B) : a1 = a1.
Proof. exact (eq_refl a1). Qed.
Lemma lem1062053 {A B : Type'} (b : B) (a0 : recspace A) (Fn : type1592 A B) (Z : type1336 A B) (a1 : B) : (term215 A B b Fn Z a0 a1) = (term216 A B b a0 Fn Z a1).
Proof. exact (MK_COMB (@lem1062051 A B b a0 Fn Z) (@lem1062052 B a1)). Qed.
Lemma lem1062054 {A B : Type'} (b : B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z : type1336 A B) : (term216 A B b a0 Fn Z a1) = (term169 A B b a0 a1 Fn Z).
Proof. exact (eq_refl (term216 A B b a0 Fn Z a1)). Qed.
Lemma lem1062055 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) : (term217 A B b Fn Z a0 a1) = (term217 A B b Fn Z a0 a1).
Proof. exact (eq_refl (term217 A B b Fn Z a0 a1)). Qed.
Lemma lem1062056 {A B : Type'} (b : B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z : type1336 A B) : ((term215 A B b Fn Z a0 a1) = (term216 A B b a0 Fn Z a1)) = ((term215 A B b Fn Z a0 a1) = (term169 A B b a0 a1 Fn Z)).
Proof. exact (MK_COMB (@lem1062055 A B b Fn Z a0 a1) (@lem1062054 A B b a0 a1 Fn Z)). Qed.
Lemma lem1062057 {A B : Type'} (b : B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z : type1336 A B) : (term215 A B b Fn Z a0 a1) = (term169 A B b a0 a1 Fn Z).
Proof. exact (EQ_MP (@lem1062056 A B b a0 a1 Fn Z) (@lem1062053 A B b a0 Fn Z a1)). Qed.
Lemma lem1062058 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1062059 {A B : Type'} (b : B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z : type1336 A B) : (term218 A B b Fn Z a0 a1) = (term219 A B b a0 a1 Fn Z).
Proof. exact (MK_COMB (@lem1062058) (@lem1062057 A B b a0 a1 Fn Z)). Qed.
Lemma lem1062060 {A B : Type'} (Z : type1336 A B) (a0 : recspace A) (a1 : B) : (Z a0 a1) = (Z a0 a1).
Proof. exact (eq_refl (Z a0 a1)). Qed.
Lemma lem1062061 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) : (term220 A B b Fn Z a0 a1) = (term170 A B b Fn Z a0 a1).
Proof. exact (MK_COMB (@lem1062059 A B b a0 a1 Fn Z) (@lem1062060 A B Z a0 a1)). Qed.
Lemma lem1062062 {A B : Type'} (a0 : recspace A) (a1 : B) (b : B) (Fn : type1592 A B) (Z : type1336 A B) : (term221 A B a0 a1 b Fn Z) = (term221 A B a0 a1 b Fn Z).
Proof. exact (eq_refl (term221 A B a0 a1 b Fn Z)). Qed.
Lemma lem1062063 {A B : Type'} (b : B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z : type1336 A B) : (term222 A B b Fn Z a0 a1) = (term223 A B b a0 a1 Fn Z).
Proof. exact (MK_COMB (@lem1062062 A B a0 a1 b Fn Z) (@lem1062057 A B b a0 a1 Fn Z)). Qed.
Lemma lem1062064 {A B : Type'} (Z : type1336 A B) (a0 : recspace A) (a1 : B) : (term224 A B Z a0 a1) = (term224 A B Z a0 a1).
Proof. exact (eq_refl (term224 A B Z a0 a1)). Qed.
Lemma lem1062065 {A B : Type'} (b : B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z : type1336 A B) : (term225 A B b Fn Z a0 a1) = (term226 A B b a0 a1 Fn Z).
Proof. exact (MK_COMB (@lem1062064 A B Z a0 a1) (@lem1062057 A B b a0 a1 Fn Z)). Qed.
Lemma lem1062066 {A B : Type'} (b : B) (a0 : recspace A) (Fn : type1592 A B) (Z : type1336 A B) : (term227 A B b Fn Z a0) = (term228 A B b a0 Fn Z).
Proof. exact (fun_ext (fun a1 : B => @lem1062065 A B b a0 a1 Fn Z)). Qed.
Lemma lem1062067 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1062068 {A B : Type'} (b : B) (a0 : recspace A) (Fn : type1592 A B) (Z : type1336 A B) : (term229 A B b Fn Z a0) = (term230 A B b a0 Fn Z).
Proof. exact (MK_COMB (@lem1062067 B) (@lem1062066 A B b a0 Fn Z)). Qed.
Lemma lem1062069 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) : (term231 A B b Fn Z) = (term232 A B b Fn Z).
Proof. exact (fun_ext (fun a0 : recspace A => @lem1062068 A B b a0 Fn Z)). Qed.
Lemma lem1062070 {A : Type'} : (@all (recspace A)) = (@all (recspace A)).
Proof. exact (eq_refl (@all (recspace A))). Qed.
Lemma lem1062071 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) : (term233 A B b Fn Z) = (term234 A B b Fn Z).
Proof. exact (MK_COMB (@lem1062070 A) (@lem1062069 A B b Fn Z)). Qed.
Lemma lem1062072 {A B : Type'} (b : B) (a0 : recspace A) (Fn : type1592 A B) (Z : type1336 A B) : (term235 A B b Fn Z a0) = (term236 A B b a0 Fn Z).
Proof. exact (fun_ext (fun a1 : B => @lem1062063 A B b a0 a1 Fn Z)). Qed.
Lemma lem1062073 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1062074 {A B : Type'} (b : B) (a0 : recspace A) (Fn : type1592 A B) (Z : type1336 A B) : (term237 A B b Fn Z a0) = (term238 A B b a0 Fn Z).
Proof. exact (MK_COMB (@lem1062073 B) (@lem1062072 A B b a0 Fn Z)). Qed.
Lemma lem1062075 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) : (term239 A B b Fn Z) = (term240 A B b Fn Z).
Proof. exact (fun_ext (fun a0 : recspace A => @lem1062074 A B b a0 Fn Z)). Qed.
Lemma lem1062076 {A : Type'} : (@all (recspace A)) = (@all (recspace A)).
Proof. exact (eq_refl (@all (recspace A))). Qed.
Lemma lem1062077 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) : (term241 A B b Fn Z) = (term242 A B b Fn Z).
Proof. exact (MK_COMB (@lem1062076 A) (@lem1062075 A B b Fn Z)). Qed.
Lemma lem1062078 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) : (term243 A B b Fn Z a0) = (term244 A B b Fn Z a0).
Proof. exact (fun_ext (fun a1 : B => @lem1062061 A B b Fn Z a0 a1)). Qed.
Lemma lem1062079 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1062080 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) : (term245 A B b Fn Z a0) = (term171 A B b Fn Z a0).
Proof. exact (MK_COMB (@lem1062079 B) (@lem1062078 A B b Fn Z a0)). Qed.
Lemma lem1062081 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) : (term246 A B b Fn Z) = (term247 A B b Fn Z).
Proof. exact (fun_ext (fun a0 : recspace A => @lem1062080 A B b Fn Z a0)). Qed.
Lemma lem1062082 {A : Type'} : (@all (recspace A)) = (@all (recspace A)).
Proof. exact (eq_refl (@all (recspace A))). Qed.
Lemma lem1062083 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) : (term248 A B b Fn Z) = (term172 A B b Fn Z).
Proof. exact (MK_COMB (@lem1062082 A) (@lem1062081 A B b Fn Z)). Qed.
Lemma lem1062084 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) : (term172 A B b Fn Z) = (term248 A B b Fn Z).
Proof. exact (SYM (@lem1062083 A B b Fn Z)). Qed.
Lemma lem1062085 {A B : Type'} (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : term198 A B b Fn) (h2 : Z = (term179 A B b Fn)) : term248 A B b Fn Z.
Proof. exact (EQ_MP (@lem1062084 A B b Fn Z) (@lem1062044 A B Z b Fn h1 h2)). Qed.
Lemma lem1062086 {A B : Type'} (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : term198 A B b Fn) : term249 A B b Fn Z.
Proof. exact (@lem1062002 A B b Fn h1 (term250 A B b Fn Z)). Qed.
Lemma lem1062087 {A B : Type'} (Z : type1336 A B) (b : B) (Fn : type1592 A B) : (term249 A B b Fn Z) = (term251 A B Z b Fn).
Proof. exact (eq_refl (term249 A B b Fn Z)). Qed.
Lemma lem1062088 {A B : Type'} (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : term198 A B b Fn) : term251 A B Z b Fn.
Proof. exact (EQ_MP (@lem1062087 A B Z b Fn) (@lem1062086 A B Z b Fn h1)). Qed.
Lemma lem1062089 {A B : Type'} (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : term198 A B b Fn) : term252 A B b Fn Z.
Proof. exact (@lem1062088 A B Z b Fn h1 Z). Qed.
Lemma lem1062090 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) : (term252 A B b Fn Z) = (term253 A B b Fn Z).
Proof. exact (eq_refl (term252 A B b Fn Z)). Qed.
Lemma lem1062091 {A B : Type'} (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : term198 A B b Fn) : term253 A B b Fn Z.
Proof. exact (EQ_MP (@lem1062090 A B b Fn Z) (@lem1062089 A B Z b Fn h1)). Qed.
Lemma lem1062092 {A B : Type'} (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : term198 A B b Fn) (h2 : Z = (term179 A B b Fn)) : term242 A B b Fn Z.
Proof. exact (@lem1062091 A B Z b Fn h1 (@lem1062085 A B Z b Fn h1 h2)). Qed.
Lemma lem1062093 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) : (term242 A B b Fn Z) = (term241 A B b Fn Z).
Proof. exact (SYM (@lem1062077 A B b Fn Z)). Qed.
Lemma lem1062094 {A B : Type'} (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : term198 A B b Fn) (h2 : Z = (term179 A B b Fn)) : term241 A B b Fn Z.
Proof. exact (EQ_MP (@lem1062093 A B b Fn Z) (@lem1062092 A B Z b Fn h1 h2)). Qed.
Lemma lem1062095 {A B : Type'} (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : Z = (term179 A B b Fn)) : term254 A B b Fn Z.
Proof. exact (@lem1062001 A B Z b Fn h1 (term250 A B b Fn Z)). Qed.
Lemma lem1062096 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) : (term254 A B b Fn Z) = (term255 A B b Fn Z).
Proof. exact (eq_refl (term254 A B b Fn Z)). Qed.
Lemma lem1062097 {A B : Type'} (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : Z = (term179 A B b Fn)) : term255 A B b Fn Z.
Proof. exact (EQ_MP (@lem1062096 A B b Fn Z) (@lem1062095 A B Z b Fn h1)). Qed.
Lemma lem1062098 {A B : Type'} (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : term198 A B b Fn) (h2 : Z = (term179 A B b Fn)) : term233 A B b Fn Z.
Proof. exact (@lem1062097 A B Z b Fn h2 (@lem1062094 A B Z b Fn h1 h2)). Qed.
Lemma lem1062099 {A B : Type'} (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : term198 A B b Fn) (h2 : Z = (term179 A B b Fn)) : term234 A B b Fn Z.
Proof. exact (EQ_MP (@lem1062071 A B b Fn Z) (@lem1062098 A B Z b Fn h1 h2)). Qed.
Lemma lem1062100 {A B : Type'} (a0 : recspace A) (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : term198 A B b Fn) (h2 : Z = (term179 A B b Fn)) : term173 A B b Fn Z a0.
Proof. exact (@lem1062044 A B Z b Fn h1 h2 a0). Qed.
Lemma lem1062101 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) : (term173 A B b Fn Z a0) = (term171 A B b Fn Z a0).
Proof. exact (eq_refl (term173 A B b Fn Z a0)). Qed.
Lemma lem1062102 {A B : Type'} (a0 : recspace A) (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : term198 A B b Fn) (h2 : Z = (term179 A B b Fn)) : term171 A B b Fn Z a0.
Proof. exact (EQ_MP (@lem1062101 A B b Fn Z a0) (@lem1062100 A B a0 Z b Fn h1 h2)). Qed.
Lemma lem1062103 {A B : Type'} (a0 : recspace A) (a1 : B) (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : term198 A B b Fn) (h2 : Z = (term179 A B b Fn)) : term174 A B b Fn Z a0 a1.
Proof. exact (@lem1062102 A B a0 Z b Fn h1 h2 a1). Qed.
Lemma lem1062104 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) : (term174 A B b Fn Z a0 a1) = (term170 A B b Fn Z a0 a1).
Proof. exact (eq_refl (term174 A B b Fn Z a0 a1)). Qed.
Lemma lem1062105 {A B : Type'} (a0 : recspace A) (a1 : B) (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : term198 A B b Fn) (h2 : Z = (term179 A B b Fn)) : term170 A B b Fn Z a0 a1.
Proof. exact (EQ_MP (@lem1062104 A B b Fn Z a0 a1) (@lem1062103 A B a0 a1 Z b Fn h1 h2)). Qed.
Lemma lem1062106 {A B : Type'} (a0 : recspace A) (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : term198 A B b Fn) (h2 : Z = (term179 A B b Fn)) : term256 A B b Fn Z a0.
Proof. exact (@lem1062099 A B Z b Fn h1 h2 a0). Qed.
Lemma lem1062107 {A B : Type'} (b : B) (a0 : recspace A) (Fn : type1592 A B) (Z : type1336 A B) : (term256 A B b Fn Z a0) = (term230 A B b a0 Fn Z).
Proof. exact (eq_refl (term256 A B b Fn Z a0)). Qed.
Lemma lem1062108 {A B : Type'} (a0 : recspace A) (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : term198 A B b Fn) (h2 : Z = (term179 A B b Fn)) : term230 A B b a0 Fn Z.
Proof. exact (EQ_MP (@lem1062107 A B b a0 Fn Z) (@lem1062106 A B a0 Z b Fn h1 h2)). Qed.
Lemma lem1062109 {A B : Type'} (a0 : recspace A) (a1 : B) (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : term198 A B b Fn) (h2 : Z = (term179 A B b Fn)) : term257 A B b a0 Fn Z a1.
Proof. exact (@lem1062108 A B a0 Z b Fn h1 h2 a1). Qed.
Lemma lem1062110 {A B : Type'} (b : B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z : type1336 A B) : (term257 A B b a0 Fn Z a1) = (term226 A B b a0 a1 Fn Z).
Proof. exact (eq_refl (term257 A B b a0 Fn Z a1)). Qed.
Lemma lem1062111 {A B : Type'} (a0 : recspace A) (a1 : B) (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : term198 A B b Fn) (h2 : Z = (term179 A B b Fn)) : term226 A B b a0 a1 Fn Z.
Proof. exact (EQ_MP (@lem1062110 A B b a0 a1 Fn Z) (@lem1062109 A B a0 a1 Z b Fn h1 h2)). Qed.
Lemma lem1062112 {A B : Type'} (a0 : recspace A) (a1 : B) (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : term198 A B b Fn) (h2 : Z = (term179 A B b Fn)) : term258 A B b Fn Z a0 a1.
Proof. exact (conj (@lem1062111 A B a0 a1 Z b Fn h1 h2) (@lem1062105 A B a0 a1 Z b Fn h1 h2)). Qed.
Lemma lem1062113 {A B : Type'} (b : B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z : type1336 A B) : (term258 A B b Fn Z a0 a1) = ((Z a0 a1) = (term169 A B b a0 a1 Fn Z)).
Proof. exact (@lem32 (Z a0 a1) (term169 A B b a0 a1 Fn Z)). Qed.
Lemma lem1062114 {A B : Type'} (a0 : recspace A) (a1 : B) (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : term198 A B b Fn) (h2 : Z = (term179 A B b Fn)) : (Z a0 a1) = (term169 A B b a0 a1 Fn Z).
Proof. exact (EQ_MP (@lem1062113 A B b a0 a1 Fn Z) (@lem1062112 A B a0 a1 Z b Fn h1 h2)). Qed.
Lemma lem1062115 {A B : Type'} (a0 : recspace A) (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : term198 A B b Fn) (h2 : Z = (term179 A B b Fn)) : term259 A B b a0 Fn Z.
Proof. exact (fun a1 : B => @lem1062114 A B a0 a1 Z b Fn h1 h2). Qed.
Lemma lem1062120 {A B : Type'} (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : term198 A B b Fn) (h2 : Z = (term179 A B b Fn)) : term172 A B b Fn Z.
Proof. exact (fun a0 : recspace A => @lem1062043 A B a0 Z b Fn h1 h2). Qed.
Lemma lem1062121 {A B : Type'} (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : term198 A B b Fn) (h2 : Z = (term179 A B b Fn)) : term260 A B b Fn Z.
Proof. exact (fun a0 : recspace A => @lem1062115 A B a0 Z b Fn h1 h2). Qed.
Lemma lem1062122 {A B : Type'} (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : term198 A B b Fn) (h2 : Z = (term179 A B b Fn)) : term197 A B b Fn Z.
Proof. exact (fun Z' : type1336 A B => @lem1062000 A B Z' Z b Fn h2). Qed.
Lemma lem1062123 {A B : Type'} (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : term198 A B b Fn) (h2 : Z = (term179 A B b Fn)) : term163 A B b Z Fn.
Proof. exact (EQ_MP (@lem1061964 A B b Z Fn) (@lem1062120 A B Z b Fn h1 h2)). Qed.
Lemma lem1062137 {A B : Type'} (b : B) (Z : type1336 A B) (Fn : type1592 A B) : (term172 A B b Fn Z) = (term163 A B b Z Fn).
Proof. exact (SYM (@lem1061963 A B b Fn Z)). Qed.
Lemma lem1062138 {A B : Type'} (b : B) (Z : type1336 A B) (Fn : type1592 A B) : (term172 A B b Fn Z) = (term163 A B b Z Fn).
Proof. exact (@lem1062137 A B b Z Fn). Qed.
Lemma lem1062139 {A B : Type'} (b : B) (Z' : type1336 A B) (Fn : type1592 A B) : (term172 A B b Fn Z') = (term163 A B b Z' Fn).
Proof. exact (@lem1062138 A B b Z' Fn). Qed.
Lemma lem1062140 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1062141 {A B : Type'} (b : B) (Z' : type1336 A B) (Fn : type1592 A B) : (term261 A B b Fn Z') = (term262 A B b Z' Fn).
Proof. exact (MK_COMB (@lem1062140) (@lem1062139 A B b Z' Fn)). Qed.
Lemma lem1062180 {A B : Type'} (Z : type1336 A B) (Z' : type1336 A B) : (term195 A B Z Z') = (term195 A B Z Z').
Proof. exact (eq_refl (term195 A B Z Z')). Qed.
Lemma lem1062181 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (Z' : type1336 A B) : (term196 A B b Fn Z Z') = (term263 A B b Fn Z Z').
Proof. exact (MK_COMB (@lem1062141 A B b Z' Fn) (@lem1062180 A B Z Z')). Qed.
Lemma lem1062182 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) : (term264 A B b Fn Z) = (term265 A B b Fn Z).
Proof. exact (fun_ext (fun Z' : type1336 A B => @lem1062181 A B b Fn Z Z')). Qed.
Lemma lem1062183 {A B : Type'} : (@all ((recspace A) -> B -> Prop)) = (@all ((recspace A) -> B -> Prop)).
Proof. exact (eq_refl (@all ((recspace A) -> B -> Prop))). Qed.
Lemma lem1062184 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) : (term197 A B b Fn Z) = (term266 A B b Fn Z).
Proof. exact (MK_COMB (@lem1062183 A B) (@lem1062182 A B b Fn Z)). Qed.
Lemma lem1062185 {A B : Type'} (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : term198 A B b Fn) (h2 : Z = (term179 A B b Fn)) : term266 A B b Fn Z.
Proof. exact (EQ_MP (@lem1062184 A B b Fn Z) (@lem1062122 A B Z b Fn h1 h2)). Qed.
Lemma lem1062186 {A B : Type'} (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : term198 A B b Fn) (h2 : Z = (term179 A B b Fn)) : term267 A B b Fn Z.
Proof. exact (conj (@lem1062185 A B Z b Fn h1 h2) (@lem1062121 A B Z b Fn h1 h2)). Qed.
Lemma lem1062187 {A B : Type'} (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : term198 A B b Fn) (h2 : Z = (term179 A B b Fn)) : term268 A B b Fn Z.
Proof. exact (conj (@lem1062123 A B Z b Fn h1 h2) (@lem1062186 A B Z b Fn h1 h2)). Qed.
Lemma lem1062188 {A B : Type'} (Z : type1336 A B) (Z' : type1336 A B) (h1 : term195 A B Z Z') : term195 A B Z Z'.
Proof. exact (h1). Qed.
Lemma lem1062190 (A : Prop) (C : Prop) (B : Prop) (D : Prop) : term269 A C B D.
Proof. exact (fun h0 : term270 A B C D => @lem7129 A B C D h0). Qed.
Lemma lem1062192 {A B : Type'} (a0 : recspace A) (a1 : B) (b : B) : term271 A B a0 a1 b.
Proof. exact (@lem9120 (term82 A B a0 a1 b)). Qed.
Lemma lem1062193 {A B : Type'} (a0 : recspace A) (a1 : B) (b : B) : (term271 A B a0 a1 b) = (term272 A B a0 a1 b).
Proof. exact (eq_refl (term271 A B a0 a1 b)). Qed.
Lemma lem1062194 {A B : Type'} (a0 : recspace A) (a1 : B) (b : B) : term272 A B a0 a1 b.
Proof. exact (EQ_MP (@lem1062193 A B a0 a1 b) (@lem1062192 A B a0 a1 b)). Qed.
Lemma lem1062196 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term273 A P Q.
Proof. exact (fun h0 : term274 A P Q => @lem7400 A P Q h0). Qed.
Lemma lem1062197 (P : nat -> Prop) (Q : nat -> Prop) : term275 P Q.
Proof. exact (@lem1062196 nat P Q). Qed.
Lemma lem1062198 {A B : Type'} (Z : type1336 A B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z' : type1336 A B) : term276 A B Z a0 a1 Fn Z'.
Proof. exact (@lem1062197 (term149 A B a0 a1 Fn Z) (term149 A B a0 a1 Fn Z')). Qed.
Lemma lem1062199 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (Z : type1336 A B) : (term277 A B a0 a1 Fn Z c) = (term146 A B a0 a1 Fn c Z).
Proof. exact (eq_refl (term277 A B a0 a1 Fn Z c)). Qed.
Lemma lem1062200 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1062201 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (Z : type1336 A B) : (term278 A B a0 a1 Fn Z c) = (term279 A B a0 a1 Fn c Z).
Proof. exact (MK_COMB (@lem1062200) (@lem1062199 A B a0 a1 Fn c Z)). Qed.
Lemma lem1062202 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (Z' : type1336 A B) : (term277 A B a0 a1 Fn Z' c) = (term146 A B a0 a1 Fn c Z').
Proof. exact (eq_refl (term277 A B a0 a1 Fn Z' c)). Qed.
Lemma lem1062203 {A B : Type'} (Z : type1336 A B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (Z' : type1336 A B) : (term280 A B Z a0 a1 Fn Z' c) = (term281 A B Z a0 a1 Fn c Z').
Proof. exact (MK_COMB (@lem1062201 A B a0 a1 Fn c Z) (@lem1062202 A B a0 a1 Fn c Z')). Qed.
Lemma lem1062204 {A B : Type'} (Z : type1336 A B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z' : type1336 A B) : (term282 A B Z a0 a1 Fn Z') = (term283 A B Z a0 a1 Fn Z').
Proof. exact (fun_ext (fun c : nat => @lem1062203 A B Z a0 a1 Fn c Z')). Qed.
Lemma lem1062205 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1062206 {A B : Type'} (Z : type1336 A B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z' : type1336 A B) : (term284 A B Z a0 a1 Fn Z') = (term285 A B Z a0 a1 Fn Z').
Proof. exact (MK_COMB (@lem1062205) (@lem1062204 A B Z a0 a1 Fn Z')). Qed.
Lemma lem1062207 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1062208 {A B : Type'} (Z : type1336 A B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z' : type1336 A B) : (term286 A B Z a0 a1 Fn Z') = (term287 A B Z a0 a1 Fn Z').
Proof. exact (MK_COMB (@lem1062207) (@lem1062206 A B Z a0 a1 Fn Z')). Qed.
Lemma lem1062209 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (Z : type1336 A B) : (term277 A B a0 a1 Fn Z c) = (term146 A B a0 a1 Fn c Z).
Proof. exact (eq_refl (term277 A B a0 a1 Fn Z c)). Qed.
Lemma lem1062210 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z : type1336 A B) : (term288 A B a0 a1 Fn Z) = (term149 A B a0 a1 Fn Z).
Proof. exact (fun_ext (fun c : nat => @lem1062209 A B a0 a1 Fn c Z)). Qed.
Lemma lem1062211 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1062212 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z : type1336 A B) : (term289 A B a0 a1 Fn Z) = (term148 A B a0 a1 Fn Z).
Proof. exact (MK_COMB (@lem1062211) (@lem1062210 A B a0 a1 Fn Z)). Qed.
Lemma lem1062213 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1062214 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z : type1336 A B) : (term290 A B a0 a1 Fn Z) = (term291 A B a0 a1 Fn Z).
Proof. exact (MK_COMB (@lem1062213) (@lem1062212 A B a0 a1 Fn Z)). Qed.
Lemma lem1062215 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (Z' : type1336 A B) : (term277 A B a0 a1 Fn Z' c) = (term146 A B a0 a1 Fn c Z').
Proof. exact (eq_refl (term277 A B a0 a1 Fn Z' c)). Qed.
Lemma lem1062216 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z' : type1336 A B) : (term288 A B a0 a1 Fn Z') = (term149 A B a0 a1 Fn Z').
Proof. exact (fun_ext (fun c : nat => @lem1062215 A B a0 a1 Fn c Z')). Qed.
Lemma lem1062217 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1062218 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z' : type1336 A B) : (term289 A B a0 a1 Fn Z') = (term148 A B a0 a1 Fn Z').
Proof. exact (MK_COMB (@lem1062217) (@lem1062216 A B a0 a1 Fn Z')). Qed.
Lemma lem1062219 {A B : Type'} (Z : type1336 A B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z' : type1336 A B) : (term292 A B Z a0 a1 Fn Z') = (term293 A B Z a0 a1 Fn Z').
Proof. exact (MK_COMB (@lem1062214 A B a0 a1 Fn Z) (@lem1062218 A B a0 a1 Fn Z')). Qed.
Lemma lem1062220 {A B : Type'} (Z : type1336 A B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z' : type1336 A B) : (term276 A B Z a0 a1 Fn Z') = (term294 A B Z a0 a1 Fn Z').
Proof. exact (MK_COMB (@lem1062208 A B Z a0 a1 Fn Z') (@lem1062219 A B Z a0 a1 Fn Z')). Qed.
Lemma lem1062223 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term273 A P Q.
Proof. exact (fun h0 : term274 A P Q => @lem7400 A P Q h0). Qed.
Lemma lem1062224 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term273 A P Q.
Proof. exact (@lem1062223 A P Q). Qed.
Lemma lem1062225 {A B : Type'} (Z : type1336 A B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (Z' : type1336 A B) : term295 A B Z a0 a1 Fn c Z'.
Proof. exact (@lem1062224 A (term147 A B a0 a1 Fn c Z) (term147 A B a0 a1 Fn c Z')). Qed.
Lemma lem1062226 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) : (term296 A B a0 a1 Fn c Z i) = (term144 A B a0 a1 Fn c i Z).
Proof. exact (eq_refl (term296 A B a0 a1 Fn c Z i)). Qed.
Lemma lem1062227 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1062228 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) : (term297 A B a0 a1 Fn c Z i) = (term298 A B a0 a1 Fn c i Z).
Proof. exact (MK_COMB (@lem1062227) (@lem1062226 A B a0 a1 Fn c i Z)). Qed.
Lemma lem1062229 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z' : type1336 A B) : (term296 A B a0 a1 Fn c Z' i) = (term144 A B a0 a1 Fn c i Z').
Proof. exact (eq_refl (term296 A B a0 a1 Fn c Z' i)). Qed.
Lemma lem1062230 {A B : Type'} (Z : type1336 A B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z' : type1336 A B) : (term299 A B Z a0 a1 Fn c Z' i) = (term300 A B Z a0 a1 Fn c i Z').
Proof. exact (MK_COMB (@lem1062228 A B a0 a1 Fn c i Z) (@lem1062229 A B a0 a1 Fn c i Z')). Qed.
Lemma lem1062231 {A B : Type'} (Z : type1336 A B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (Z' : type1336 A B) : (term301 A B Z a0 a1 Fn c Z') = (term302 A B Z a0 a1 Fn c Z').
Proof. exact (fun_ext (fun i : A => @lem1062230 A B Z a0 a1 Fn c i Z')). Qed.
Lemma lem1062232 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1062233 {A B : Type'} (Z : type1336 A B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (Z' : type1336 A B) : (term303 A B Z a0 a1 Fn c Z') = (term304 A B Z a0 a1 Fn c Z').
Proof. exact (MK_COMB (@lem1062232 A) (@lem1062231 A B Z a0 a1 Fn c Z')). Qed.
Lemma lem1062234 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1062235 {A B : Type'} (Z : type1336 A B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (Z' : type1336 A B) : (term305 A B Z a0 a1 Fn c Z') = (term306 A B Z a0 a1 Fn c Z').
Proof. exact (MK_COMB (@lem1062234) (@lem1062233 A B Z a0 a1 Fn c Z')). Qed.
Lemma lem1062236 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) : (term296 A B a0 a1 Fn c Z i) = (term144 A B a0 a1 Fn c i Z).
Proof. exact (eq_refl (term296 A B a0 a1 Fn c Z i)). Qed.
Lemma lem1062237 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (Z : type1336 A B) : (term307 A B a0 a1 Fn c Z) = (term147 A B a0 a1 Fn c Z).
Proof. exact (fun_ext (fun i : A => @lem1062236 A B a0 a1 Fn c i Z)). Qed.
Lemma lem1062238 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1062239 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (Z : type1336 A B) : (term308 A B a0 a1 Fn c Z) = (term146 A B a0 a1 Fn c Z).
Proof. exact (MK_COMB (@lem1062238 A) (@lem1062237 A B a0 a1 Fn c Z)). Qed.
Lemma lem1062240 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1062241 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (Z : type1336 A B) : (term309 A B a0 a1 Fn c Z) = (term279 A B a0 a1 Fn c Z).
Proof. exact (MK_COMB (@lem1062240) (@lem1062239 A B a0 a1 Fn c Z)). Qed.
Lemma lem1062242 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z' : type1336 A B) : (term296 A B a0 a1 Fn c Z' i) = (term144 A B a0 a1 Fn c i Z').
Proof. exact (eq_refl (term296 A B a0 a1 Fn c Z' i)). Qed.
Lemma lem1062243 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (Z' : type1336 A B) : (term307 A B a0 a1 Fn c Z') = (term147 A B a0 a1 Fn c Z').
Proof. exact (fun_ext (fun i : A => @lem1062242 A B a0 a1 Fn c i Z')). Qed.
Lemma lem1062244 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1062245 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (Z' : type1336 A B) : (term308 A B a0 a1 Fn c Z') = (term146 A B a0 a1 Fn c Z').
Proof. exact (MK_COMB (@lem1062244 A) (@lem1062243 A B a0 a1 Fn c Z')). Qed.
Lemma lem1062246 {A B : Type'} (Z : type1336 A B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (Z' : type1336 A B) : (term310 A B Z a0 a1 Fn c Z') = (term281 A B Z a0 a1 Fn c Z').
Proof. exact (MK_COMB (@lem1062241 A B a0 a1 Fn c Z) (@lem1062245 A B a0 a1 Fn c Z')). Qed.
Lemma lem1062247 {A B : Type'} (Z : type1336 A B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (Z' : type1336 A B) : (term295 A B Z a0 a1 Fn c Z') = (term311 A B Z a0 a1 Fn c Z').
Proof. exact (MK_COMB (@lem1062235 A B Z a0 a1 Fn c Z') (@lem1062246 A B Z a0 a1 Fn c Z')). Qed.
Lemma lem1062250 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term273 A P Q.
Proof. exact (fun h0 : term274 A P Q => @lem7400 A P Q h0). Qed.
Lemma lem1062251 {A : Type'} (P : type963 A) (Q : type963 A) : term312 A P Q.
Proof. exact (@lem1062250 (type1614 A) P Q). Qed.
Lemma lem1062252 {A B : Type'} (Z : type1336 A B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z' : type1336 A B) : term313 A B Z a0 a1 Fn c i Z'.
Proof. exact (@lem1062251 A (term145 A B a0 a1 Fn c i Z) (term145 A B a0 a1 Fn c i Z')). Qed.
Lemma lem1062253 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : (term314 A B a0 a1 Fn c i Z r) = (term142 A B a0 a1 Fn c i Z r).
Proof. exact (eq_refl (term314 A B a0 a1 Fn c i Z r)). Qed.
Lemma lem1062254 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1062255 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : (term315 A B a0 a1 Fn c i Z r) = (term316 A B a0 a1 Fn c i Z r).
Proof. exact (MK_COMB (@lem1062254) (@lem1062253 A B a0 a1 Fn c i Z r)). Qed.
Lemma lem1062256 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z' : type1336 A B) (r : type1614 A) : (term314 A B a0 a1 Fn c i Z' r) = (term142 A B a0 a1 Fn c i Z' r).
Proof. exact (eq_refl (term314 A B a0 a1 Fn c i Z' r)). Qed.
Lemma lem1062257 {A B : Type'} (Z : type1336 A B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z' : type1336 A B) (r : type1614 A) : (term317 A B Z a0 a1 Fn c i Z' r) = (term318 A B Z a0 a1 Fn c i Z' r).
Proof. exact (MK_COMB (@lem1062255 A B a0 a1 Fn c i Z r) (@lem1062256 A B a0 a1 Fn c i Z' r)). Qed.
Lemma lem1062258 {A B : Type'} (Z : type1336 A B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z' : type1336 A B) : (term319 A B Z a0 a1 Fn c i Z') = (term320 A B Z a0 a1 Fn c i Z').
Proof. exact (fun_ext (fun r : type1614 A => @lem1062257 A B Z a0 a1 Fn c i Z' r)). Qed.
Lemma lem1062259 {A : Type'} : (@all (nat -> recspace A)) = (@all (nat -> recspace A)).
Proof. exact (eq_refl (@all (nat -> recspace A))). Qed.
Lemma lem1062260 {A B : Type'} (Z : type1336 A B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z' : type1336 A B) : (term321 A B Z a0 a1 Fn c i Z') = (term322 A B Z a0 a1 Fn c i Z').
Proof. exact (MK_COMB (@lem1062259 A) (@lem1062258 A B Z a0 a1 Fn c i Z')). Qed.
Lemma lem1062261 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1062262 {A B : Type'} (Z : type1336 A B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z' : type1336 A B) : (term323 A B Z a0 a1 Fn c i Z') = (term324 A B Z a0 a1 Fn c i Z').
Proof. exact (MK_COMB (@lem1062261) (@lem1062260 A B Z a0 a1 Fn c i Z')). Qed.
Lemma lem1062263 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : (term314 A B a0 a1 Fn c i Z r) = (term142 A B a0 a1 Fn c i Z r).
Proof. exact (eq_refl (term314 A B a0 a1 Fn c i Z r)). Qed.
Lemma lem1062264 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) : (term325 A B a0 a1 Fn c i Z) = (term145 A B a0 a1 Fn c i Z).
Proof. exact (fun_ext (fun r : type1614 A => @lem1062263 A B a0 a1 Fn c i Z r)). Qed.
Lemma lem1062265 {A : Type'} : (@ex (nat -> recspace A)) = (@ex (nat -> recspace A)).
Proof. exact (eq_refl (@ex (nat -> recspace A))). Qed.
Lemma lem1062266 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) : (term326 A B a0 a1 Fn c i Z) = (term144 A B a0 a1 Fn c i Z).
Proof. exact (MK_COMB (@lem1062265 A) (@lem1062264 A B a0 a1 Fn c i Z)). Qed.
Lemma lem1062267 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1062268 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) : (term327 A B a0 a1 Fn c i Z) = (term298 A B a0 a1 Fn c i Z).
Proof. exact (MK_COMB (@lem1062267) (@lem1062266 A B a0 a1 Fn c i Z)). Qed.
Lemma lem1062269 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z' : type1336 A B) (r : type1614 A) : (term314 A B a0 a1 Fn c i Z' r) = (term142 A B a0 a1 Fn c i Z' r).
Proof. exact (eq_refl (term314 A B a0 a1 Fn c i Z' r)). Qed.
Lemma lem1062270 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z' : type1336 A B) : (term325 A B a0 a1 Fn c i Z') = (term145 A B a0 a1 Fn c i Z').
Proof. exact (fun_ext (fun r : type1614 A => @lem1062269 A B a0 a1 Fn c i Z' r)). Qed.
Lemma lem1062271 {A : Type'} : (@ex (nat -> recspace A)) = (@ex (nat -> recspace A)).
Proof. exact (eq_refl (@ex (nat -> recspace A))). Qed.
Lemma lem1062272 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z' : type1336 A B) : (term326 A B a0 a1 Fn c i Z') = (term144 A B a0 a1 Fn c i Z').
Proof. exact (MK_COMB (@lem1062271 A) (@lem1062270 A B a0 a1 Fn c i Z')). Qed.
Lemma lem1062273 {A B : Type'} (Z : type1336 A B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z' : type1336 A B) : (term328 A B Z a0 a1 Fn c i Z') = (term300 A B Z a0 a1 Fn c i Z').
Proof. exact (MK_COMB (@lem1062268 A B a0 a1 Fn c i Z) (@lem1062272 A B a0 a1 Fn c i Z')). Qed.
Lemma lem1062274 {A B : Type'} (Z : type1336 A B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z' : type1336 A B) : (term313 A B Z a0 a1 Fn c i Z') = (term329 A B Z a0 a1 Fn c i Z').
Proof. exact (MK_COMB (@lem1062262 A B Z a0 a1 Fn c i Z') (@lem1062273 A B Z a0 a1 Fn c i Z')). Qed.
Lemma lem1062277 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term273 A P Q.
Proof. exact (fun h0 : term274 A P Q => @lem7400 A P Q h0). Qed.
Lemma lem1062278 {B : Type'} (P : type976 B) (Q : type976 B) : term330 B P Q.
Proof. exact (@lem1062277 (nat -> B) P Q). Qed.
Lemma lem1062279 {A B : Type'} (Z : type1336 A B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z' : type1336 A B) (r : type1614 A) : term331 A B Z a0 a1 Fn c i Z' r.
Proof. exact (@lem1062278 B (term143 A B a0 a1 Fn c i Z r) (term143 A B a0 a1 Fn c i Z' r)). Qed.
Lemma lem1062280 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (y : nat -> B) : (term332 A B a0 a1 Fn c i Z r y) = (term99 A B a0 a1 Fn c i Z r y).
Proof. exact (eq_refl (term332 A B a0 a1 Fn c i Z r y)). Qed.
Lemma lem1062281 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1062282 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (y : nat -> B) : (term333 A B a0 a1 Fn c i Z r y) = (term334 A B a0 a1 Fn c i Z r y).
Proof. exact (MK_COMB (@lem1062281) (@lem1062280 A B a0 a1 Fn c i Z r y)). Qed.
Lemma lem1062283 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z' : type1336 A B) (r : type1614 A) (y : nat -> B) : (term332 A B a0 a1 Fn c i Z' r y) = (term99 A B a0 a1 Fn c i Z' r y).
Proof. exact (eq_refl (term332 A B a0 a1 Fn c i Z' r y)). Qed.
Lemma lem1062284 {A B : Type'} (Z : type1336 A B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z' : type1336 A B) (r : type1614 A) (y : nat -> B) : (term335 A B Z a0 a1 Fn c i Z' r y) = (term336 A B Z a0 a1 Fn c i Z' r y).
Proof. exact (MK_COMB (@lem1062282 A B a0 a1 Fn c i Z r y) (@lem1062283 A B a0 a1 Fn c i Z' r y)). Qed.
Lemma lem1062285 {A B : Type'} (Z : type1336 A B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z' : type1336 A B) (r : type1614 A) : (term337 A B Z a0 a1 Fn c i Z' r) = (term338 A B Z a0 a1 Fn c i Z' r).
Proof. exact (fun_ext (fun y : nat -> B => @lem1062284 A B Z a0 a1 Fn c i Z' r y)). Qed.
Lemma lem1062286 {B : Type'} : (@all (nat -> B)) = (@all (nat -> B)).
Proof. exact (eq_refl (@all (nat -> B))). Qed.
Lemma lem1062287 {A B : Type'} (Z : type1336 A B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z' : type1336 A B) (r : type1614 A) : (term339 A B Z a0 a1 Fn c i Z' r) = (term340 A B Z a0 a1 Fn c i Z' r).
Proof. exact (MK_COMB (@lem1062286 B) (@lem1062285 A B Z a0 a1 Fn c i Z' r)). Qed.
Lemma lem1062288 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1062289 {A B : Type'} (Z : type1336 A B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z' : type1336 A B) (r : type1614 A) : (term341 A B Z a0 a1 Fn c i Z' r) = (term342 A B Z a0 a1 Fn c i Z' r).
Proof. exact (MK_COMB (@lem1062288) (@lem1062287 A B Z a0 a1 Fn c i Z' r)). Qed.
Lemma lem1062290 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (y : nat -> B) : (term332 A B a0 a1 Fn c i Z r y) = (term99 A B a0 a1 Fn c i Z r y).
Proof. exact (eq_refl (term332 A B a0 a1 Fn c i Z r y)). Qed.
Lemma lem1062291 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : (term343 A B a0 a1 Fn c i Z r) = (term143 A B a0 a1 Fn c i Z r).
Proof. exact (fun_ext (fun y : nat -> B => @lem1062290 A B a0 a1 Fn c i Z r y)). Qed.
Lemma lem1062292 {B : Type'} : (@ex (nat -> B)) = (@ex (nat -> B)).
Proof. exact (eq_refl (@ex (nat -> B))). Qed.
Lemma lem1062293 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : (term344 A B a0 a1 Fn c i Z r) = (term142 A B a0 a1 Fn c i Z r).
Proof. exact (MK_COMB (@lem1062292 B) (@lem1062291 A B a0 a1 Fn c i Z r)). Qed.
Lemma lem1062294 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1062295 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : (term345 A B a0 a1 Fn c i Z r) = (term316 A B a0 a1 Fn c i Z r).
Proof. exact (MK_COMB (@lem1062294) (@lem1062293 A B a0 a1 Fn c i Z r)). Qed.
Lemma lem1062296 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z' : type1336 A B) (r : type1614 A) (y : nat -> B) : (term332 A B a0 a1 Fn c i Z' r y) = (term99 A B a0 a1 Fn c i Z' r y).
Proof. exact (eq_refl (term332 A B a0 a1 Fn c i Z' r y)). Qed.
Lemma lem1062297 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z' : type1336 A B) (r : type1614 A) : (term343 A B a0 a1 Fn c i Z' r) = (term143 A B a0 a1 Fn c i Z' r).
Proof. exact (fun_ext (fun y : nat -> B => @lem1062296 A B a0 a1 Fn c i Z' r y)). Qed.
Lemma lem1062298 {B : Type'} : (@ex (nat -> B)) = (@ex (nat -> B)).
Proof. exact (eq_refl (@ex (nat -> B))). Qed.
Lemma lem1062299 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z' : type1336 A B) (r : type1614 A) : (term344 A B a0 a1 Fn c i Z' r) = (term142 A B a0 a1 Fn c i Z' r).
Proof. exact (MK_COMB (@lem1062298 B) (@lem1062297 A B a0 a1 Fn c i Z' r)). Qed.
Lemma lem1062300 {A B : Type'} (Z : type1336 A B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z' : type1336 A B) (r : type1614 A) : (term346 A B Z a0 a1 Fn c i Z' r) = (term318 A B Z a0 a1 Fn c i Z' r).
Proof. exact (MK_COMB (@lem1062295 A B a0 a1 Fn c i Z r) (@lem1062299 A B a0 a1 Fn c i Z' r)). Qed.
Lemma lem1062301 {A B : Type'} (Z : type1336 A B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z' : type1336 A B) (r : type1614 A) : (term331 A B Z a0 a1 Fn c i Z' r) = (term347 A B Z a0 a1 Fn c i Z' r).
Proof. exact (MK_COMB (@lem1062289 A B Z a0 a1 Fn c i Z' r) (@lem1062300 A B Z a0 a1 Fn c i Z' r)). Qed.
Lemma lem1062304 (A : Prop) (C : Prop) (B : Prop) (D : Prop) : term348 A C B D.
Proof. exact (fun h0 : term270 A B C D => @lem7058 A B C D h0). Qed.
Lemma lem1062306 {A : Type'} (a0 : recspace A) (c : nat) (i : A) (r : type1614 A) : term349 A a0 c i r.
Proof. exact (@lem9120 (a0 = (@CONSTR A c i r))). Qed.
Lemma lem1062307 {A : Type'} (a0 : recspace A) (c : nat) (i : A) (r : type1614 A) : (term349 A a0 c i r) = (term350 A a0 c i r).
Proof. exact (eq_refl (term349 A a0 c i r)). Qed.
Lemma lem1062308 {A : Type'} (a0 : recspace A) (c : nat) (i : A) (r : type1614 A) : term350 A a0 c i r.
Proof. exact (EQ_MP (@lem1062307 A a0 c i r) (@lem1062306 A a0 c i r)). Qed.
Lemma lem1062310 (A : Prop) (C : Prop) (B : Prop) (D : Prop) : term348 A C B D.
Proof. exact (fun h0 : term270 A B C D => @lem7058 A B C D h0). Qed.
Lemma lem1062312 {A B : Type'} (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (y : nat -> B) : term351 A B a1 Fn c i r y.
Proof. exact (@lem9120 (a1 = (Fn c i r y))). Qed.
Lemma lem1062313 {A B : Type'} (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (y : nat -> B) : (term351 A B a1 Fn c i r y) = (term352 A B a1 Fn c i r y).
Proof. exact (eq_refl (term351 A B a1 Fn c i r y)). Qed.
Lemma lem1062314 {A B : Type'} (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (y : nat -> B) : term352 A B a1 Fn c i r y.
Proof. exact (EQ_MP (@lem1062313 A B a1 Fn c i r y) (@lem1062312 A B a1 Fn c i r y)). Qed.
Lemma lem1062316 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term353 A P Q.
Proof. exact (fun h0 : term274 A P Q => @lem7362 A P Q h0). Qed.
Lemma lem1062317 (P : nat -> Prop) (Q : nat -> Prop) : term354 P Q.
Proof. exact (@lem1062316 nat P Q). Qed.
Lemma lem1062318 {A B : Type'} (Z : type1336 A B) (Z' : type1336 A B) (r : type1614 A) (y : nat -> B) : term355 A B Z Z' r y.
Proof. exact (@lem1062317 (term356 A B Z r y) (term356 A B Z' r y)). Qed.
Lemma lem1062319 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (n : nat) : (term357 A B Z r y n) = (term358 A B Z r y n).
Proof. exact (eq_refl (term357 A B Z r y n)). Qed.
Lemma lem1062320 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1062321 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (n : nat) : (term359 A B Z r y n) = (term360 A B Z r y n).
Proof. exact (MK_COMB (@lem1062320) (@lem1062319 A B Z r y n)). Qed.
Lemma lem1062322 {A B : Type'} (Z' : type1336 A B) (r : type1614 A) (y : nat -> B) (n : nat) : (term357 A B Z' r y n) = (term358 A B Z' r y n).
Proof. exact (eq_refl (term357 A B Z' r y n)). Qed.
Lemma lem1062323 {A B : Type'} (Z : type1336 A B) (Z' : type1336 A B) (r : type1614 A) (y : nat -> B) (n : nat) : (term361 A B Z Z' r y n) = (term362 A B Z Z' r y n).
Proof. exact (MK_COMB (@lem1062321 A B Z r y n) (@lem1062322 A B Z' r y n)). Qed.
Lemma lem1062324 {A B : Type'} (Z : type1336 A B) (Z' : type1336 A B) (r : type1614 A) (y : nat -> B) : (term363 A B Z Z' r y) = (term364 A B Z Z' r y).
Proof. exact (fun_ext (fun n : nat => @lem1062323 A B Z Z' r y n)). Qed.
Lemma lem1062325 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1062326 {A B : Type'} (Z : type1336 A B) (Z' : type1336 A B) (r : type1614 A) (y : nat -> B) : (term365 A B Z Z' r y) = (term366 A B Z Z' r y).
Proof. exact (MK_COMB (@lem1062325) (@lem1062324 A B Z Z' r y)). Qed.
Lemma lem1062327 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1062328 {A B : Type'} (Z : type1336 A B) (Z' : type1336 A B) (r : type1614 A) (y : nat -> B) : (term367 A B Z Z' r y) = (term368 A B Z Z' r y).
Proof. exact (MK_COMB (@lem1062327) (@lem1062326 A B Z Z' r y)). Qed.
Lemma lem1062329 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (n : nat) : (term357 A B Z r y n) = (term358 A B Z r y n).
Proof. exact (eq_refl (term357 A B Z r y n)). Qed.
Lemma lem1062330 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (y : nat -> B) : (term369 A B Z r y) = (term356 A B Z r y).
Proof. exact (fun_ext (fun n : nat => @lem1062329 A B Z r y n)). Qed.
Lemma lem1062331 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1062332 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (y : nat -> B) : (term370 A B Z r y) = (term101 A B Z r y).
Proof. exact (MK_COMB (@lem1062331) (@lem1062330 A B Z r y)). Qed.
Lemma lem1062333 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1062334 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (y : nat -> B) : (term371 A B Z r y) = (term372 A B Z r y).
Proof. exact (MK_COMB (@lem1062333) (@lem1062332 A B Z r y)). Qed.
Lemma lem1062335 {A B : Type'} (Z' : type1336 A B) (r : type1614 A) (y : nat -> B) (n : nat) : (term357 A B Z' r y n) = (term358 A B Z' r y n).
Proof. exact (eq_refl (term357 A B Z' r y n)). Qed.
Lemma lem1062336 {A B : Type'} (Z' : type1336 A B) (r : type1614 A) (y : nat -> B) : (term369 A B Z' r y) = (term356 A B Z' r y).
Proof. exact (fun_ext (fun n : nat => @lem1062335 A B Z' r y n)). Qed.
Lemma lem1062337 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1062338 {A B : Type'} (Z' : type1336 A B) (r : type1614 A) (y : nat -> B) : (term370 A B Z' r y) = (term101 A B Z' r y).
Proof. exact (MK_COMB (@lem1062337) (@lem1062336 A B Z' r y)). Qed.
Lemma lem1062339 {A B : Type'} (Z : type1336 A B) (Z' : type1336 A B) (r : type1614 A) (y : nat -> B) : (term373 A B Z Z' r y) = (term374 A B Z Z' r y).
Proof. exact (MK_COMB (@lem1062334 A B Z r y) (@lem1062338 A B Z' r y)). Qed.
Lemma lem1062340 {A B : Type'} (Z : type1336 A B) (Z' : type1336 A B) (r : type1614 A) (y : nat -> B) : (term355 A B Z Z' r y) = (term375 A B Z Z' r y).
Proof. exact (MK_COMB (@lem1062328 A B Z Z' r y) (@lem1062339 A B Z Z' r y)). Qed.
Lemma lem1062342 {A B : Type'} (a0 : recspace A) (Z : type1336 A B) (Z' : type1336 A B) (h1 : term195 A B Z Z') : term376 A B Z Z' a0.
Proof. exact (@lem1062188 A B Z Z' h1 a0). Qed.
Lemma lem1062343 {A B : Type'} (Z : type1336 A B) (Z' : type1336 A B) (a0 : recspace A) : (term376 A B Z Z' a0) = (term194 A B Z Z' a0).
Proof. exact (eq_refl (term376 A B Z Z' a0)). Qed.
Lemma lem1062344 {A B : Type'} (a0 : recspace A) (Z : type1336 A B) (Z' : type1336 A B) (h1 : term195 A B Z Z') : term194 A B Z Z' a0.
Proof. exact (EQ_MP (@lem1062343 A B Z Z' a0) (@lem1062342 A B a0 Z Z' h1)). Qed.
Lemma lem1062345 {A B : Type'} (a0 : recspace A) (a1 : B) (Z : type1336 A B) (Z' : type1336 A B) (h1 : term195 A B Z Z') : term377 A B Z Z' a0 a1.
Proof. exact (@lem1062344 A B a0 Z Z' h1 a1). Qed.
Lemma lem1062346 {A B : Type'} (Z : type1336 A B) (Z' : type1336 A B) (a0 : recspace A) (a1 : B) : (term377 A B Z Z' a0 a1) = (term193 A B Z Z' a0 a1).
Proof. exact (eq_refl (term377 A B Z Z' a0 a1)). Qed.
Lemma lem1062347 {A B : Type'} (a0 : recspace A) (a1 : B) (Z : type1336 A B) (Z' : type1336 A B) (h1 : term195 A B Z Z') : term193 A B Z Z' a0 a1.
Proof. exact (EQ_MP (@lem1062346 A B Z Z' a0 a1) (@lem1062345 A B a0 a1 Z Z' h1)). Qed.
Lemma lem1062348 {A B : Type'} (Z : type1336 A B) (Z' : type1336 A B) (a0 : recspace A) (a1 : B) : (term193 A B Z Z' a0 a1) = ((term193 A B Z Z' a0 a1) = True).
Proof. exact (@lem7 (term193 A B Z Z' a0 a1)). Qed.
Lemma lem1062355 {A B : Type'} (a0 : recspace A) (a1 : B) (Z : type1336 A B) (Z' : type1336 A B) (h1 : term195 A B Z Z') : (term193 A B Z Z' a0 a1) = True.
Proof. exact (EQ_MP (@lem1062348 A B Z Z' a0 a1) (@lem1062347 A B a0 a1 Z Z' h1)). Qed.
Lemma lem1062356 {A B : Type'} (a0 : recspace A) (a1 : B) (Z : type1336 A B) (Z' : type1336 A B) (h1 : term195 A B Z Z') : (term193 A B Z Z' a0 a1) = True.
Proof. exact (@lem1062355 A B a0 a1 Z Z' h1). Qed.
Lemma lem1062357 {A B : Type'} (r : type1614 A) (y : nat -> B) (n : nat) (Z : type1336 A B) (Z' : type1336 A B) (h1 : term195 A B Z Z') : (term362 A B Z Z' r y n) = True.
Proof. exact (@lem1062356 A B (r n) (y n) Z Z' h1). Qed.
Lemma lem1062358 {A B : Type'} (r : type1614 A) (y : nat -> B) (Z : type1336 A B) (Z' : type1336 A B) (h1 : term195 A B Z Z') : (term364 A B Z Z' r y) = term378.
Proof. exact (fun_ext (fun n : nat => @lem1062357 A B r y n Z Z' h1)). Qed.
Lemma lem1062359 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1062360 {A B : Type'} (r : type1614 A) (y : nat -> B) (Z : type1336 A B) (Z' : type1336 A B) (h1 : term195 A B Z Z') : (term366 A B Z Z' r y) = term379.
Proof. exact (MK_COMB (@lem1062359) (@lem1062358 A B r y Z Z' h1)). Qed.
Lemma lem1062362 {A : Type'} (t : Prop) : (term380 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1062363 (t : Prop) : (term381 t) = t.
Proof. exact (@lem1062362 nat t). Qed.
Lemma lem1062364 : term379 = True.
Proof. exact (@lem1062363 True). Qed.
Lemma lem1062365 {A B : Type'} (r : type1614 A) (y : nat -> B) (Z : type1336 A B) (Z' : type1336 A B) (h1 : term195 A B Z Z') : (term366 A B Z Z' r y) = True.
Proof. exact (TRANS (@lem1062360 A B r y Z Z' h1) (@lem1062364)). Qed.
Lemma lem1062366 {A B : Type'} (r : type1614 A) (y : nat -> B) (Z : type1336 A B) (Z' : type1336 A B) (h1 : term195 A B Z Z') : True = (term366 A B Z Z' r y).
Proof. exact (SYM (@lem1062365 A B r y Z Z' h1)). Qed.
Lemma lem1062367 {A B : Type'} (r : type1614 A) (y : nat -> B) (Z : type1336 A B) (Z' : type1336 A B) (h1 : term195 A B Z Z') : term366 A B Z Z' r y.
Proof. exact (EQ_MP (@lem1062366 A B r y Z Z' h1) (@lem0)). Qed.
Lemma lem1062369 {A B : Type'} (Z : type1336 A B) (Z' : type1336 A B) (r : type1614 A) (y : nat -> B) : term375 A B Z Z' r y.
Proof. exact (EQ_MP (@lem1062340 A B Z Z' r y) (@lem1062318 A B Z Z' r y)). Qed.
Lemma lem1062370 {A B : Type'} (r : type1614 A) (y : nat -> B) (Z : type1336 A B) (Z' : type1336 A B) (h1 : term195 A B Z Z') : term374 A B Z Z' r y.
Proof. exact (@lem1062369 A B Z Z' r y (@lem1062367 A B r y Z Z' h1)). Qed.
Lemma lem1062371 {A B : Type'} (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Z : type1336 A B) (Z' : type1336 A B) (h1 : term195 A B Z Z') : term382 A B a1 Fn c i Z Z' r y.
Proof. exact (conj (@lem1062314 A B a1 Fn c i r y) (@lem1062370 A B r y Z Z' h1)). Qed.
Lemma lem1062373 {A B : Type'} (Z : type1336 A B) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z' : type1336 A B) (r : type1614 A) (y : nat -> B) : term383 A B Z a1 Fn c i Z' r y.
Proof. exact (@lem1062310 (a1 = (Fn c i r y)) (term101 A B Z r y) (a1 = (Fn c i r y)) (term101 A B Z' r y)). Qed.
Lemma lem1062374 {A B : Type'} (Z : type1336 A B) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z' : type1336 A B) (r : type1614 A) (y : nat -> B) : term383 A B Z a1 Fn c i Z' r y.
Proof. exact (@lem1062373 A B Z a1 Fn c i Z' r y). Qed.
Lemma lem1062375 {A B : Type'} (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Z : type1336 A B) (Z' : type1336 A B) (h1 : term195 A B Z Z') : term384 A B Z a1 Fn c i Z' r y.
Proof. exact (@lem1062374 A B Z a1 Fn c i Z' r y (@lem1062371 A B a1 Fn c i r y Z Z' h1)). Qed.
Lemma lem1062376 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Z : type1336 A B) (Z' : type1336 A B) (h1 : term195 A B Z Z') : term385 A B a0 Z a1 Fn c i Z' r y.
Proof. exact (conj (@lem1062308 A a0 c i r) (@lem1062375 A B a1 Fn c i r y Z Z' h1)). Qed.
Lemma lem1062378 {A B : Type'} (Z : type1336 A B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z' : type1336 A B) (r : type1614 A) (y : nat -> B) : term386 A B Z a0 a1 Fn c i Z' r y.
Proof. exact (@lem1062304 (a0 = (@CONSTR A c i r)) (term100 A B a1 Fn c i Z r y) (a0 = (@CONSTR A c i r)) (term100 A B a1 Fn c i Z' r y)). Qed.
Lemma lem1062379 {A B : Type'} (Z : type1336 A B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z' : type1336 A B) (r : type1614 A) (y : nat -> B) : term386 A B Z a0 a1 Fn c i Z' r y.
Proof. exact (@lem1062378 A B Z a0 a1 Fn c i Z' r y). Qed.
Lemma lem1062380 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Z : type1336 A B) (Z' : type1336 A B) (h1 : term195 A B Z Z') : term336 A B Z a0 a1 Fn c i Z' r y.
Proof. exact (@lem1062379 A B Z a0 a1 Fn c i Z' r y (@lem1062376 A B a0 a1 Fn c i r y Z Z' h1)). Qed.
Lemma lem1062385 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (Z : type1336 A B) (Z' : type1336 A B) (h1 : term195 A B Z Z') : term340 A B Z a0 a1 Fn c i Z' r.
Proof. exact (fun y : nat -> B => @lem1062380 A B a0 a1 Fn c i r y Z Z' h1). Qed.
Lemma lem1062387 {A B : Type'} (Z : type1336 A B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z' : type1336 A B) (r : type1614 A) : term347 A B Z a0 a1 Fn c i Z' r.
Proof. exact (EQ_MP (@lem1062301 A B Z a0 a1 Fn c i Z' r) (@lem1062279 A B Z a0 a1 Fn c i Z' r)). Qed.
Lemma lem1062388 {A B : Type'} (Z : type1336 A B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z' : type1336 A B) (r : type1614 A) : term347 A B Z a0 a1 Fn c i Z' r.
Proof. exact (@lem1062387 A B Z a0 a1 Fn c i Z' r). Qed.
Lemma lem1062389 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (Z : type1336 A B) (Z' : type1336 A B) (h1 : term195 A B Z Z') : term318 A B Z a0 a1 Fn c i Z' r.
Proof. exact (@lem1062388 A B Z a0 a1 Fn c i Z' r (@lem1062385 A B a0 a1 Fn c i r Z Z' h1)). Qed.
Lemma lem1062394 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (Z' : type1336 A B) (h1 : term195 A B Z Z') : term322 A B Z a0 a1 Fn c i Z'.
Proof. exact (fun r : type1614 A => @lem1062389 A B a0 a1 Fn c i r Z Z' h1). Qed.
Lemma lem1062396 {A B : Type'} (Z : type1336 A B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z' : type1336 A B) : term329 A B Z a0 a1 Fn c i Z'.
Proof. exact (EQ_MP (@lem1062274 A B Z a0 a1 Fn c i Z') (@lem1062252 A B Z a0 a1 Fn c i Z')). Qed.
Lemma lem1062397 {A B : Type'} (Z : type1336 A B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z' : type1336 A B) : term329 A B Z a0 a1 Fn c i Z'.
Proof. exact (@lem1062396 A B Z a0 a1 Fn c i Z'). Qed.
Lemma lem1062398 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (Z' : type1336 A B) (h1 : term195 A B Z Z') : term300 A B Z a0 a1 Fn c i Z'.
Proof. exact (@lem1062397 A B Z a0 a1 Fn c i Z' (@lem1062394 A B a0 a1 Fn c i Z Z' h1)). Qed.
Lemma lem1062403 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (Z : type1336 A B) (Z' : type1336 A B) (h1 : term195 A B Z Z') : term304 A B Z a0 a1 Fn c Z'.
Proof. exact (fun i : A => @lem1062398 A B a0 a1 Fn c i Z Z' h1). Qed.
Lemma lem1062405 {A B : Type'} (Z : type1336 A B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (Z' : type1336 A B) : term311 A B Z a0 a1 Fn c Z'.
Proof. exact (EQ_MP (@lem1062247 A B Z a0 a1 Fn c Z') (@lem1062225 A B Z a0 a1 Fn c Z')). Qed.
Lemma lem1062406 {A B : Type'} (Z : type1336 A B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (Z' : type1336 A B) : term311 A B Z a0 a1 Fn c Z'.
Proof. exact (@lem1062405 A B Z a0 a1 Fn c Z'). Qed.
Lemma lem1062407 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (c : nat) (Z : type1336 A B) (Z' : type1336 A B) (h1 : term195 A B Z Z') : term281 A B Z a0 a1 Fn c Z'.
Proof. exact (@lem1062406 A B Z a0 a1 Fn c Z' (@lem1062403 A B a0 a1 Fn c Z Z' h1)). Qed.
Lemma lem1062412 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z : type1336 A B) (Z' : type1336 A B) (h1 : term195 A B Z Z') : term285 A B Z a0 a1 Fn Z'.
Proof. exact (fun c : nat => @lem1062407 A B a0 a1 Fn c Z Z' h1). Qed.
Lemma lem1062414 {A B : Type'} (Z : type1336 A B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z' : type1336 A B) : term294 A B Z a0 a1 Fn Z'.
Proof. exact (EQ_MP (@lem1062220 A B Z a0 a1 Fn Z') (@lem1062198 A B Z a0 a1 Fn Z')). Qed.
Lemma lem1062415 {A B : Type'} (Z : type1336 A B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z' : type1336 A B) : term294 A B Z a0 a1 Fn Z'.
Proof. exact (@lem1062414 A B Z a0 a1 Fn Z'). Qed.
Lemma lem1062416 {A B : Type'} (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z : type1336 A B) (Z' : type1336 A B) (h1 : term195 A B Z Z') : term293 A B Z a0 a1 Fn Z'.
Proof. exact (@lem1062415 A B Z a0 a1 Fn Z' (@lem1062412 A B a0 a1 Fn Z Z' h1)). Qed.
Lemma lem1062417 {A B : Type'} (b : B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z : type1336 A B) (Z' : type1336 A B) (h1 : term195 A B Z Z') : term387 A B b Z a0 a1 Fn Z'.
Proof. exact (conj (@lem1062194 A B a0 a1 b) (@lem1062416 A B a0 a1 Fn Z Z' h1)). Qed.
Lemma lem1062419 {A B : Type'} (Z : type1336 A B) (b : B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z' : type1336 A B) : term388 A B Z b a0 a1 Fn Z'.
Proof. exact (@lem1062190 (term82 A B a0 a1 b) (term148 A B a0 a1 Fn Z) (term82 A B a0 a1 b) (term148 A B a0 a1 Fn Z')). Qed.
Lemma lem1062420 {A B : Type'} (Z : type1336 A B) (b : B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z' : type1336 A B) : term388 A B Z b a0 a1 Fn Z'.
Proof. exact (@lem1062419 A B Z b a0 a1 Fn Z'). Qed.
Lemma lem1062421 {A B : Type'} (b : B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z : type1336 A B) (Z' : type1336 A B) (h1 : term195 A B Z Z') : term208 A B Z b a0 a1 Fn Z'.
Proof. exact (@lem1062420 A B Z b a0 a1 Fn Z' (@lem1062417 A B b a0 a1 Fn Z Z' h1)). Qed.
Lemma lem1062426 {A B : Type'} (b : B) (a0 : recspace A) (Fn : type1592 A B) (Z : type1336 A B) (Z' : type1336 A B) (h1 : term195 A B Z Z') : term206 A B Z b a0 Fn Z'.
Proof. exact (fun a1 : B => @lem1062421 A B b a0 a1 Fn Z Z' h1). Qed.
Lemma lem1062431 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (Z' : type1336 A B) (h1 : term195 A B Z Z') : term204 A B Z b Fn Z'.
Proof. exact (fun a0 : recspace A => @lem1062426 A B b a0 Fn Z Z' h1). Qed.
Lemma lem1062432 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (Z' : type1336 A B) (h1 : term195 A B Z Z') : (term195 A B Z Z') = (term204 A B Z b Fn Z').
Proof. exact (prop_ext (fun h2 : term195 A B Z Z' => @lem1062431 A B b Fn Z Z' h1) (fun h2 : term204 A B Z b Fn Z' => @lem1062188 A B Z Z' h1)). Qed.
Lemma lem1062433 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (Z' : type1336 A B) (h1 : term195 A B Z Z') : term204 A B Z b Fn Z'.
Proof. exact (EQ_MP (@lem1062432 A B b Fn Z Z' h1) (@lem1062188 A B Z Z' h1)). Qed.
Lemma lem1062434 {A B : Type'} (Z : type1336 A B) (b : B) (Fn : type1592 A B) (Z' : type1336 A B) : term203 A B Z b Fn Z'.
Proof. exact (fun h0 : term195 A B Z Z' => @lem1062433 A B b Fn Z Z' h0). Qed.
Lemma lem1062439 {A B : Type'} (Z : type1336 A B) (b : B) (Fn : type1592 A B) : term201 A B Z b Fn.
Proof. exact (fun Z' : type1336 A B => @lem1062434 A B Z b Fn Z'). Qed.
Lemma lem1062444 {A B : Type'} (b : B) (Fn : type1592 A B) : term198 A B b Fn.
Proof. exact (fun Z : type1336 A B => @lem1062439 A B Z b Fn). Qed.
Lemma lem1062445 {A B : Type'} (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : Z = (term179 A B b Fn)) : (term198 A B b Fn) = (term268 A B b Fn Z).
Proof. exact (prop_ext (fun h2 : term198 A B b Fn => @lem1062187 A B Z b Fn h2 h1) (fun h2 : term268 A B b Fn Z => @lem1062444 A B b Fn)). Qed.
Lemma lem1062446 {A B : Type'} (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : Z = (term179 A B b Fn)) : term268 A B b Fn Z.
Proof. exact (EQ_MP (@lem1062445 A B Z b Fn h1) (@lem1062444 A B b Fn)). Qed.
Lemma lem1062447 {A B : Type'} (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : Z = (term179 A B b Fn)) : Z = (term179 A B b Fn).
Proof. exact (h1). Qed.
Lemma lem1062448 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) : term389 A B b Fn Z.
Proof. exact (fun h0 : Z = (term179 A B b Fn) => @lem1062446 A B Z b Fn h0). Qed.
Lemma lem1062449 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) : term389 A B b Fn Z.
Proof. exact (@lem1062448 A B b Fn Z). Qed.
Lemma lem1062450 {A B : Type'} (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : Z = (term179 A B b Fn)) : term268 A B b Fn Z.
Proof. exact (@lem1062449 A B b Fn Z (@lem1062447 A B Z b Fn h1)). Qed.
Lemma lem1062451 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) : (term390 A B b Fn Z) = (term268 A B b Fn Z).
Proof. exact (eq_refl (term390 A B b Fn Z)). Qed.
Lemma lem1062452 {A B : Type'} : term391 A B.
Proof. exact (@lem9102 (type1336 A B)). Qed.
Lemma lem1062453 {A B : Type'} (b : B) (Fn : type1592 A B) : term392 A B b Fn.
Proof. exact (@lem1062452 A B (term393 A B b Fn)). Qed.
Lemma lem1062454 {A B : Type'} (b : B) (Fn : type1592 A B) : (term392 A B b Fn) = (term394 A B b Fn).
Proof. exact (eq_refl (term392 A B b Fn)). Qed.
Lemma lem1062455 {A B : Type'} (b : B) (Fn : type1592 A B) : term394 A B b Fn.
Proof. exact (EQ_MP (@lem1062454 A B b Fn) (@lem1062453 A B b Fn)). Qed.
Lemma lem1062456 {A B : Type'} (b : B) (Fn : type1592 A B) : term395 A B b Fn.
Proof. exact (@lem1062455 A B b Fn (term179 A B b Fn)). Qed.
Lemma lem1062457 {A B : Type'} (b : B) (Fn : type1592 A B) : (term395 A B b Fn) = (term396 A B b Fn).
Proof. exact (eq_refl (term395 A B b Fn)). Qed.
Lemma lem1062458 {A B : Type'} (b : B) (Fn : type1592 A B) : term396 A B b Fn.
Proof. exact (EQ_MP (@lem1062457 A B b Fn) (@lem1062456 A B b Fn)). Qed.
Lemma lem1062459 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) : (term268 A B b Fn Z) = (term390 A B b Fn Z).
Proof. exact (SYM (@lem1062451 A B b Fn Z)). Qed.
Lemma lem1062460 {A B : Type'} (Z : type1336 A B) (b : B) (Fn : type1592 A B) (h1 : Z = (term179 A B b Fn)) : term390 A B b Fn Z.
Proof. exact (EQ_MP (@lem1062459 A B b Fn Z) (@lem1062450 A B Z b Fn h1)). Qed.
Lemma lem1062461 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) : term397 A B b Fn Z.
Proof. exact (fun h0 : Z = (term179 A B b Fn) => @lem1062460 A B Z b Fn h0). Qed.
Lemma lem1062462 {A B : Type'} (b : B) (Fn : type1592 A B) : term398 A B b Fn.
Proof. exact (fun Z : type1336 A B => @lem1062461 A B b Fn Z). Qed.
Lemma lem1062463 {A B : Type'} (b : B) (Fn : type1592 A B) : term399 A B b Fn.
Proof. exact (@lem1062458 A B b Fn (@lem1062462 A B b Fn)). Qed.
Lemma lem1062464 {A B : Type'} (b : B) (Fn : type1592 A B) (h1 : term399 A B b Fn) : term399 A B b Fn.
Proof. exact (h1). Qed.
Lemma lem1062465 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term268 A B b Fn Z) : term268 A B b Fn Z.
Proof. exact (h1). Qed.
Lemma lem1062466 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term267 A B b Fn Z) : term267 A B b Fn Z.
Proof. exact (h1). Qed.
Lemma lem1062467 {A B : Type'} (b : B) (Z : type1336 A B) (Fn : type1592 A B) (h1 : term163 A B b Z Fn) : term163 A B b Z Fn.
Proof. exact (h1). Qed.
Lemma lem1062468 {A B : Type'} (Z : type1336 A B) (Fn : type1592 A B) (h1 : term102 A B Z Fn) : term102 A B Z Fn.
Proof. exact (h1). Qed.
Lemma lem1062470 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term267 A B b Fn Z) : term267 A B b Fn Z.
Proof. exact (h1). Qed.
Lemma lem1062471 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) : term260 A B b Fn Z.
Proof. exact (h1). Qed.
Lemma lem1062474 {A B : Type'} (b : B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : (Z a0 a1) = (term169 A B b a0 a1 Fn Z)) : (Z a0 a1) = (term169 A B b a0 a1 Fn Z).
Proof. exact (h1). Qed.
Lemma lem1062475 {A B : Type'} (b : B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : (Z a0 a1) = (term169 A B b a0 a1 Fn Z)) : (term169 A B b a0 a1 Fn Z) = (Z a0 a1).
Proof. exact (SYM (@lem1062474 A B b a0 a1 Fn Z h1)). Qed.
Lemma lem1062476 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) (h1 : (term169 A B b a0 a1 Fn Z) = (Z a0 a1)) : (term169 A B b a0 a1 Fn Z) = (Z a0 a1).
Proof. exact (h1). Qed.
Lemma lem1062477 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) (h1 : (term169 A B b a0 a1 Fn Z) = (Z a0 a1)) : (Z a0 a1) = (term169 A B b a0 a1 Fn Z).
Proof. exact (SYM (@lem1062476 A B b Fn Z a0 a1 h1)). Qed.
Lemma lem1062478 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) : ((Z a0 a1) = (term169 A B b a0 a1 Fn Z)) = ((term169 A B b a0 a1 Fn Z) = (Z a0 a1)).
Proof. exact (prop_ext (fun h1 : (Z a0 a1) = (term169 A B b a0 a1 Fn Z) => @lem1062475 A B b a0 a1 Fn Z h1) (fun h1 : (term169 A B b a0 a1 Fn Z) = (Z a0 a1) => @lem1062477 A B b Fn Z a0 a1 h1)). Qed.
Lemma lem1062479 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) : (term400 A B b a0 Fn Z) = (term401 A B b Fn Z a0).
Proof. exact (fun_ext (fun a1 : B => @lem1062478 A B b Fn Z a0 a1)). Qed.
Lemma lem1062480 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1062481 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) : (term259 A B b a0 Fn Z) = (term402 A B b Fn Z a0).
Proof. exact (MK_COMB (@lem1062480 B) (@lem1062479 A B b Fn Z a0)). Qed.
Lemma lem1062482 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) : (term403 A B b Fn Z) = (term404 A B b Fn Z).
Proof. exact (fun_ext (fun a0 : recspace A => @lem1062481 A B b Fn Z a0)). Qed.
Lemma lem1062483 {A : Type'} : (@all (recspace A)) = (@all (recspace A)).
Proof. exact (eq_refl (@all (recspace A))). Qed.
Lemma lem1062484 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) : (term260 A B b Fn Z) = (term405 A B b Fn Z).
Proof. exact (MK_COMB (@lem1062483 A) (@lem1062482 A B b Fn Z)). Qed.
Lemma lem1062485 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) : term405 A B b Fn Z.
Proof. exact (EQ_MP (@lem1062484 A B b Fn Z) (@lem1062471 A B b Fn Z h1)). Qed.
Lemma lem1062487 {A B : Type'} (Z : type1336 A B) (h1 : term406 A B Z) : term406 A B Z.
Proof. exact (h1). Qed.
Lemma lem1062489 {A : Type'} (P : type1338 A) : term81 A P.
Proof. exact (EQ_MP (@lem1061715 A P) (@lem1061714 A P)). Qed.
Lemma lem1062490 {A : Type'} (P : type1338 A) : term81 A P.
Proof. exact (@lem1062489 A P). Qed.
Lemma lem1062491 {A B : Type'} (Z : type1336 A B) : term407 A B Z.
Proof. exact (@lem1062490 A (term408 A B Z)). Qed.
Lemma lem1062492 {A B : Type'} (Z : type1336 A B) : (term409 A B Z) = (term410 A B Z).
Proof. exact (eq_refl (term409 A B Z)). Qed.
Lemma lem1062493 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1062494 {A B : Type'} (Z : type1336 A B) : (term411 A B Z) = (term412 A B Z).
Proof. exact (MK_COMB (@lem1062493) (@lem1062492 A B Z)). Qed.
Lemma lem1062495 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (n : nat) : (term413 A B Z r n) = (term414 A B Z r n).
Proof. exact (eq_refl (term413 A B Z r n)). Qed.
Lemma lem1062496 {A B : Type'} (Z : type1336 A B) (r : type1614 A) : (term415 A B Z r) = (term416 A B Z r).
Proof. exact (fun_ext (fun n : nat => @lem1062495 A B Z r n)). Qed.
Lemma lem1062497 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1062498 {A B : Type'} (Z : type1336 A B) (r : type1614 A) : (term417 A B Z r) = (term418 A B Z r).
Proof. exact (MK_COMB (@lem1062497) (@lem1062496 A B Z r)). Qed.
Lemma lem1062499 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1062500 {A B : Type'} (Z : type1336 A B) (r : type1614 A) : (term419 A B Z r) = (term420 A B Z r).
Proof. exact (MK_COMB (@lem1062499) (@lem1062498 A B Z r)). Qed.
Lemma lem1062501 {A B : Type'} (Z : type1336 A B) (c : nat) (i : A) (r : type1614 A) : (term421 A B Z c i r) = (term422 A B Z c i r).
Proof. exact (eq_refl (term421 A B Z c i r)). Qed.
Lemma lem1062502 {A B : Type'} (Z : type1336 A B) (c : nat) (i : A) (r : type1614 A) : (term423 A B Z c i r) = (term424 A B Z c i r).
Proof. exact (MK_COMB (@lem1062500 A B Z r) (@lem1062501 A B Z c i r)). Qed.
Lemma lem1062503 {A B : Type'} (Z : type1336 A B) (c : nat) (i : A) : (term425 A B Z c i) = (term426 A B Z c i).
Proof. exact (fun_ext (fun r : type1614 A => @lem1062502 A B Z c i r)). Qed.
Lemma lem1062504 {A : Type'} : (@all (nat -> recspace A)) = (@all (nat -> recspace A)).
Proof. exact (eq_refl (@all (nat -> recspace A))). Qed.
Lemma lem1062505 {A B : Type'} (Z : type1336 A B) (c : nat) (i : A) : (term427 A B Z c i) = (term428 A B Z c i).
Proof. exact (MK_COMB (@lem1062504 A) (@lem1062503 A B Z c i)). Qed.
Lemma lem1062506 {A B : Type'} (Z : type1336 A B) (c : nat) : (term429 A B Z c) = (term430 A B Z c).
Proof. exact (fun_ext (fun i : A => @lem1062505 A B Z c i)). Qed.
Lemma lem1062507 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1062508 {A B : Type'} (Z : type1336 A B) (c : nat) : (term431 A B Z c) = (term432 A B Z c).
Proof. exact (MK_COMB (@lem1062507 A) (@lem1062506 A B Z c)). Qed.
Lemma lem1062509 {A B : Type'} (Z : type1336 A B) : (term433 A B Z) = (term434 A B Z).
Proof. exact (fun_ext (fun c : nat => @lem1062508 A B Z c)). Qed.
Lemma lem1062510 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1062511 {A B : Type'} (Z : type1336 A B) : (term435 A B Z) = (term436 A B Z).
Proof. exact (MK_COMB (@lem1062510) (@lem1062509 A B Z)). Qed.
Lemma lem1062512 {A B : Type'} (Z : type1336 A B) : (term437 A B Z) = (term438 A B Z).
Proof. exact (MK_COMB (@lem1062494 A B Z) (@lem1062511 A B Z)). Qed.
Lemma lem1062513 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1062514 {A B : Type'} (Z : type1336 A B) : (term439 A B Z) = (term440 A B Z).
Proof. exact (MK_COMB (@lem1062513) (@lem1062512 A B Z)). Qed.
Lemma lem1062515 {A B : Type'} (Z : type1336 A B) (x : recspace A) : (term441 A B Z x) = (term442 A B Z x).
Proof. exact (eq_refl (term441 A B Z x)). Qed.
Lemma lem1062516 {A B : Type'} (Z : type1336 A B) : (term443 A B Z) = (term408 A B Z).
Proof. exact (fun_ext (fun x : recspace A => @lem1062515 A B Z x)). Qed.
Lemma lem1062517 {A : Type'} : (@all (recspace A)) = (@all (recspace A)).
Proof. exact (eq_refl (@all (recspace A))). Qed.
Lemma lem1062518 {A B : Type'} (Z : type1336 A B) : (term444 A B Z) = (term406 A B Z).
Proof. exact (MK_COMB (@lem1062517 A) (@lem1062516 A B Z)). Qed.
Lemma lem1062519 {A B : Type'} (Z : type1336 A B) : (term407 A B Z) = (term445 A B Z).
Proof. exact (MK_COMB (@lem1062514 A B Z) (@lem1062518 A B Z)). Qed.
Lemma lem1062520 {A B : Type'} (Z : type1336 A B) : term445 A B Z.
Proof. exact (EQ_MP (@lem1062519 A B Z) (@lem1062491 A B Z)). Qed.
Lemma lem1062521 {A B : Type'} (Z : type1336 A B) (h1 : term445 A B Z) : term445 A B Z.
Proof. exact (h1). Qed.
Lemma lem1062522 {A B : Type'} (Z : type1336 A B) (h1 : term445 A B Z) : term445 A B Z.
Proof. exact (h1). Qed.
Lemma lem1062523 {A B : Type'} (Z : type1336 A B) (h1 : term438 A B Z) : term438 A B Z.
Proof. exact (h1). Qed.
Lemma lem1062524 {A B : Type'} (Z : type1336 A B) (h1 : term438 A B Z) (h2 : term445 A B Z) : term406 A B Z.
Proof. exact (@lem1062522 A B Z h2 (@lem1062523 A B Z h1)). Qed.
Lemma lem1062525 {A B : Type'} (Z : type1336 A B) (h1 : term438 A B Z) : term446 A B Z.
Proof. exact (fun h0 : term445 A B Z => @lem1062524 A B Z h1 h0). Qed.
Lemma lem1062526 {A B : Type'} (Z : type1336 A B) (h1 : term445 A B Z) : term445 A B Z.
Proof. exact (h1). Qed.
Lemma lem1062527 {A B : Type'} (Z : type1336 A B) (h1 : term438 A B Z) (h2 : term445 A B Z) : term406 A B Z.
Proof. exact (@lem1062525 A B Z h1 (@lem1062526 A B Z h2)). Qed.
Lemma lem1062528 {A B : Type'} (Z : type1336 A B) (h1 : term445 A B Z) : term445 A B Z.
Proof. exact (fun h0 : term438 A B Z => @lem1062527 A B Z h0 h1). Qed.
Lemma lem1062529 {A B : Type'} (Z : type1336 A B) : term447 A B Z.
Proof. exact (fun h0 : term445 A B Z => @lem1062528 A B Z h0). Qed.
Lemma lem1062532 {A B : Type'} (Z : type1336 A B) (h1 : term445 A B Z) : term445 A B Z.
Proof. exact (@lem1062529 A B Z (@lem1062521 A B Z h1)). Qed.
Lemma lem1062533 {A B : Type'} (Z : type1336 A B) (h1 : term445 A B Z) : term445 A B Z.
Proof. exact (@lem1062532 A B Z h1). Qed.
Lemma lem1062536 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) (h1 : (term169 A B b a0 a1 Fn Z) = (Z a0 a1)) : (term169 A B b a0 a1 Fn Z) = (Z a0 a1).
Proof. exact (h1). Qed.
Lemma lem1062537 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) (h1 : (term169 A B b a0 a1 Fn Z) = (Z a0 a1)) : (Z a0 a1) = (term169 A B b a0 a1 Fn Z).
Proof. exact (SYM (@lem1062536 A B b Fn Z a0 a1 h1)). Qed.
Lemma lem1062538 {A B : Type'} (b : B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : (Z a0 a1) = (term169 A B b a0 a1 Fn Z)) : (Z a0 a1) = (term169 A B b a0 a1 Fn Z).
Proof. exact (h1). Qed.
Lemma lem1062539 {A B : Type'} (b : B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : (Z a0 a1) = (term169 A B b a0 a1 Fn Z)) : (term169 A B b a0 a1 Fn Z) = (Z a0 a1).
Proof. exact (SYM (@lem1062538 A B b a0 a1 Fn Z h1)). Qed.
Lemma lem1062540 {A B : Type'} (b : B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z : type1336 A B) : ((term169 A B b a0 a1 Fn Z) = (Z a0 a1)) = ((Z a0 a1) = (term169 A B b a0 a1 Fn Z)).
Proof. exact (prop_ext (fun h1 : (term169 A B b a0 a1 Fn Z) = (Z a0 a1) => @lem1062537 A B b Fn Z a0 a1 h1) (fun h1 : (Z a0 a1) = (term169 A B b a0 a1 Fn Z) => @lem1062539 A B b a0 a1 Fn Z h1)). Qed.
Lemma lem1062541 {A B : Type'} (b : B) (a0 : recspace A) (Fn : type1592 A B) (Z : type1336 A B) : (term401 A B b Fn Z a0) = (term400 A B b a0 Fn Z).
Proof. exact (fun_ext (fun a1 : B => @lem1062540 A B b a0 a1 Fn Z)). Qed.
Lemma lem1062542 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1062543 {A B : Type'} (b : B) (a0 : recspace A) (Fn : type1592 A B) (Z : type1336 A B) : (term402 A B b Fn Z a0) = (term259 A B b a0 Fn Z).
Proof. exact (MK_COMB (@lem1062542 B) (@lem1062541 A B b a0 Fn Z)). Qed.
Lemma lem1062544 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) : (term404 A B b Fn Z) = (term403 A B b Fn Z).
Proof. exact (fun_ext (fun a0 : recspace A => @lem1062543 A B b a0 Fn Z)). Qed.
Lemma lem1062545 {A : Type'} : (@all (recspace A)) = (@all (recspace A)).
Proof. exact (eq_refl (@all (recspace A))). Qed.
Lemma lem1062546 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) : (term405 A B b Fn Z) = (term260 A B b Fn Z).
Proof. exact (MK_COMB (@lem1062545 A) (@lem1062544 A B b Fn Z)). Qed.
Lemma lem1062547 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) : term260 A B b Fn Z.
Proof. exact (EQ_MP (@lem1062546 A B b Fn Z) (@lem1062485 A B b Fn Z h1)). Qed.
Lemma lem1062548 {A B : Type'} (a0 : recspace A) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) : term448 A B b Fn Z a0.
Proof. exact (@lem1062547 A B b Fn Z h1 a0). Qed.
Lemma lem1062549 {A B : Type'} (b : B) (a0 : recspace A) (Fn : type1592 A B) (Z : type1336 A B) : (term448 A B b Fn Z a0) = (term259 A B b a0 Fn Z).
Proof. exact (eq_refl (term448 A B b Fn Z a0)). Qed.
Lemma lem1062550 {A B : Type'} (a0 : recspace A) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) : term259 A B b a0 Fn Z.
Proof. exact (EQ_MP (@lem1062549 A B b a0 Fn Z) (@lem1062548 A B a0 b Fn Z h1)). Qed.
Lemma lem1062551 {A B : Type'} (a0 : recspace A) (a1 : B) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) : term449 A B b a0 Fn Z a1.
Proof. exact (@lem1062550 A B a0 b Fn Z h1 a1). Qed.
Lemma lem1062552 {A B : Type'} (b : B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z : type1336 A B) : (term449 A B b a0 Fn Z a1) = ((Z a0 a1) = (term169 A B b a0 a1 Fn Z)).
Proof. exact (eq_refl (term449 A B b a0 Fn Z a1)). Qed.
Lemma lem1062555 {A B : Type'} (a0 : recspace A) (a1 : B) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) : (Z a0 a1) = (term169 A B b a0 a1 Fn Z).
Proof. exact (EQ_MP (@lem1062552 A B b a0 a1 Fn Z) (@lem1062551 A B a0 a1 b Fn Z h1)). Qed.
Lemma lem1062556 {A B : Type'} (a0 : recspace A) (a1 : B) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) : (Z a0 a1) = (term169 A B b a0 a1 Fn Z).
Proof. exact (@lem1062555 A B a0 a1 b Fn Z h1). Qed.
Lemma lem1062557 {A B : Type'} (y : B) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) : (Z (@BOTTOM A) y) = (term450 A B b y Fn Z).
Proof. exact (@lem1062556 A B (@BOTTOM A) y b Fn Z h1). Qed.
Lemma lem1062558 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) : (term451 A B Z) = (term452 A B b Fn Z).
Proof. exact (fun_ext (fun y : B => @lem1062557 A B y b Fn Z h1)). Qed.
Lemma lem1062559 {B : Type'} : (@ex1 B) = (@ex1 B).
Proof. exact (eq_refl (@ex1 B)). Qed.
Lemma lem1062560 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) : (term410 A B Z) = (term453 A B b Fn Z).
Proof. exact (MK_COMB (@lem1062559 B) (@lem1062558 A B b Fn Z h1)). Qed.
Lemma lem1062561 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) : (term453 A B b Fn Z) = (term410 A B Z).
Proof. exact (SYM (@lem1062560 A B b Fn Z h1)). Qed.
Lemma lem1062567 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1062568 {A : Type'} (x : recspace A) : (x = x) = True.
Proof. exact (@lem1062567 (recspace A) x). Qed.
Lemma lem1062569 {A : Type'} : ((@BOTTOM A) = (@BOTTOM A)) = True.
Proof. exact (@lem1062568 A (@BOTTOM A)). Qed.
Lemma lem1062570 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1062571 {A : Type'} : (term454 A) = (and True).
Proof. exact (MK_COMB (@lem1062570) (@lem1062569 A)). Qed.
Lemma lem1062574 {B : Type'} (y : B) (b : B) : (y = b) = (y = b).
Proof. exact (eq_refl (y = b)). Qed.
Lemma lem1062575 {A B : Type'} (y : B) (b : B) : (term455 A B y b) = (term456 B y b).
Proof. exact (MK_COMB (@lem1062571 A) (@lem1062574 B y b)). Qed.
Lemma lem1062577 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1062578 {B : Type'} (y : B) (b : B) : (term456 B y b) = (y = b).
Proof. exact (@lem1062577 (y = b)). Qed.
Lemma lem1062581 {A B : Type'} (y : B) (b : B) : (term455 A B y b) = (y = b).
Proof. exact (TRANS (@lem1062575 A B y b) (@lem1062578 B y b)). Qed.
Lemma lem1062582 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1062583 {A B : Type'} (y : B) (b : B) : (term457 A B y b) = (term458 B y b).
Proof. exact (MK_COMB (@lem1062582) (@lem1062581 A B y b)). Qed.
Lemma lem1062603 {A : Type'} (c : nat) (i : A) (r : type1614 A) : ((@BOTTOM A) = (@CONSTR A c i r)) = False.
Proof. exact (@lem1061701 A c i r (@lem1061700 A c i r)). Qed.
Lemma lem1062604 {A : Type'} (c : nat) (i : A) (r : type1614 A) : ((@BOTTOM A) = (@CONSTR A c i r)) = False.
Proof. exact (@lem1062603 A c i r). Qed.
Lemma lem1062605 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1062606 {A : Type'} (c : nat) (i : A) (r : type1614 A) : (term459 A c i r) = (and False).
Proof. exact (MK_COMB (@lem1062605) (@lem1062604 A c i r)). Qed.
Lemma lem1062615 {A B : Type'} (y : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (y' : nat -> B) : (term100 A B y Fn c i Z r y') = (term100 A B y Fn c i Z r y').
Proof. exact (eq_refl (term100 A B y Fn c i Z r y')). Qed.
Lemma lem1062616 {A B : Type'} (y : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (y' : nat -> B) : (term460 A B y Fn c i Z r y') = (term461 A B y Fn c i Z r y').
Proof. exact (MK_COMB (@lem1062606 A c i r) (@lem1062615 A B y Fn c i Z r y')). Qed.
Lemma lem1062618 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1062619 {A B : Type'} (y : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (y' : nat -> B) : (term461 A B y Fn c i Z r y') = False.
Proof. exact (@lem1062618 (term100 A B y Fn c i Z r y')). Qed.
Lemma lem1062620 {A B : Type'} (y : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (y' : nat -> B) : (term460 A B y Fn c i Z r y') = False.
Proof. exact (TRANS (@lem1062616 A B y Fn c i Z r y') (@lem1062619 A B y Fn c i Z r y')). Qed.
Lemma lem1062621 {A B : Type'} (y : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : (term462 A B y Fn c i Z r) = (term463 B).
Proof. exact (fun_ext (fun y' : nat -> B => @lem1062620 A B y Fn c i Z r y')). Qed.
Lemma lem1062622 {B : Type'} : (@ex (nat -> B)) = (@ex (nat -> B)).
Proof. exact (eq_refl (@ex (nat -> B))). Qed.
Lemma lem1062623 {A B : Type'} (y : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : (term464 A B y Fn c i Z r) = (term465 B).
Proof. exact (MK_COMB (@lem1062622 B) (@lem1062621 A B y Fn c i Z r)). Qed.
Lemma lem1062625 {A : Type'} (t : Prop) : (term466 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem1062626 {B : Type'} (t : Prop) : (term467 B t) = t.
Proof. exact (@lem1062625 (nat -> B) t). Qed.
Lemma lem1062627 {B : Type'} : (term465 B) = False.
Proof. exact (@lem1062626 B False). Qed.
Lemma lem1062628 {A B : Type'} (y : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : (term464 A B y Fn c i Z r) = False.
Proof. exact (TRANS (@lem1062623 A B y Fn c i Z r) (@lem1062627 B)). Qed.
Lemma lem1062629 {A B : Type'} (y : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) : (term468 A B y Fn c i Z) = (term469 A).
Proof. exact (fun_ext (fun r : type1614 A => @lem1062628 A B y Fn c i Z r)). Qed.
Lemma lem1062630 {A : Type'} : (@ex (nat -> recspace A)) = (@ex (nat -> recspace A)).
Proof. exact (eq_refl (@ex (nat -> recspace A))). Qed.
Lemma lem1062631 {A B : Type'} (y : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) : (term470 A B y Fn c i Z) = (term471 A).
Proof. exact (MK_COMB (@lem1062630 A) (@lem1062629 A B y Fn c i Z)). Qed.
Lemma lem1062633 {A : Type'} (t : Prop) : (term466 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem1062634 {A : Type'} (t : Prop) : (term472 A t) = t.
Proof. exact (@lem1062633 (type1614 A) t). Qed.
Lemma lem1062635 {A : Type'} : (term471 A) = False.
Proof. exact (@lem1062634 A False). Qed.
Lemma lem1062636 {A B : Type'} (y : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) : (term470 A B y Fn c i Z) = False.
Proof. exact (TRANS (@lem1062631 A B y Fn c i Z) (@lem1062635 A)). Qed.
Lemma lem1062637 {A B : Type'} (y : B) (Fn : type1592 A B) (c : nat) (Z : type1336 A B) : (term473 A B y Fn c Z) = (term474 A).
Proof. exact (fun_ext (fun i : A => @lem1062636 A B y Fn c i Z)). Qed.
Lemma lem1062638 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1062639 {A B : Type'} (y : B) (Fn : type1592 A B) (c : nat) (Z : type1336 A B) : (term475 A B y Fn c Z) = (term476 A).
Proof. exact (MK_COMB (@lem1062638 A) (@lem1062637 A B y Fn c Z)). Qed.
Lemma lem1062641 {A : Type'} (t : Prop) : (term466 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem1062642 {A : Type'} (t : Prop) : (term466 A t) = t.
Proof. exact (@lem1062641 A t). Qed.
Lemma lem1062643 {A : Type'} : (term476 A) = False.
Proof. exact (@lem1062642 A False). Qed.
Lemma lem1062644 {A B : Type'} (y : B) (Fn : type1592 A B) (c : nat) (Z : type1336 A B) : (term475 A B y Fn c Z) = False.
Proof. exact (TRANS (@lem1062639 A B y Fn c Z) (@lem1062643 A)). Qed.
Lemma lem1062645 {A B : Type'} (y : B) (Fn : type1592 A B) (Z : type1336 A B) : (term477 A B y Fn Z) = term478.
Proof. exact (fun_ext (fun c : nat => @lem1062644 A B y Fn c Z)). Qed.
Lemma lem1062646 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1062647 {A B : Type'} (y : B) (Fn : type1592 A B) (Z : type1336 A B) : (term479 A B y Fn Z) = term480.
Proof. exact (MK_COMB (@lem1062646) (@lem1062645 A B y Fn Z)). Qed.
Lemma lem1062649 {A : Type'} (t : Prop) : (term466 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem1062650 (t : Prop) : (term481 t) = t.
Proof. exact (@lem1062649 nat t). Qed.
Lemma lem1062651 : term480 = False.
Proof. exact (@lem1062650 False). Qed.
Lemma lem1062652 {A B : Type'} (y : B) (Fn : type1592 A B) (Z : type1336 A B) : (term479 A B y Fn Z) = False.
Proof. exact (TRANS (@lem1062647 A B y Fn Z) (@lem1062651)). Qed.
Lemma lem1062653 {A B : Type'} (Fn : type1592 A B) (Z : type1336 A B) (y : B) (b : B) : (term450 A B b y Fn Z) = (term482 B y b).
Proof. exact (MK_COMB (@lem1062583 A B y b) (@lem1062652 A B y Fn Z)). Qed.
Lemma lem1062655 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem1062656 {B : Type'} (y : B) (b : B) : (term482 B y b) = (y = b).
Proof. exact (@lem1062655 (y = b)). Qed.
Lemma lem1062659 {A B : Type'} (Fn : type1592 A B) (Z : type1336 A B) (y : B) (b : B) : (term450 A B b y Fn Z) = (y = b).
Proof. exact (TRANS (@lem1062653 A B Fn Z y b) (@lem1062656 B y b)). Qed.
Lemma lem1062660 {A B : Type'} (Fn : type1592 A B) (Z : type1336 A B) (b : B) : (term452 A B b Fn Z) = (term483 B b).
Proof. exact (fun_ext (fun y : B => @lem1062659 A B Fn Z y b)). Qed.
Lemma lem1062661 {B : Type'} : (@ex1 B) = (@ex1 B).
Proof. exact (eq_refl (@ex1 B)). Qed.
Lemma lem1062662 {A B : Type'} (Fn : type1592 A B) (Z : type1336 A B) (b : B) : (term453 A B b Fn Z) = (term75 B b).
Proof. exact (MK_COMB (@lem1062661 B) (@lem1062660 A B Fn Z b)). Qed.
Lemma lem1062664 {A : Type'} (a : A) : (term75 A a) = True.
Proof. exact (EQ_MP (@lem1061690 A a) (@lem1061689 A a)). Qed.
Lemma lem1062665 {B : Type'} (a : B) : (term75 B a) = True.
Proof. exact (@lem1062664 B a). Qed.
Lemma lem1062666 {B : Type'} (b : B) : (term75 B b) = True.
Proof. exact (@lem1062665 B b). Qed.
Lemma lem1062667 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) : (term453 A B b Fn Z) = True.
Proof. exact (TRANS (@lem1062662 A B Fn Z b) (@lem1062666 B b)). Qed.
Lemma lem1062668 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) : True = (term453 A B b Fn Z).
Proof. exact (SYM (@lem1062667 A B b Fn Z)). Qed.
Lemma lem1062669 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) : term453 A B b Fn Z.
Proof. exact (EQ_MP (@lem1062668 A B b Fn Z) (@lem0)). Qed.
Lemma lem1062670 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) : term410 A B Z.
Proof. exact (EQ_MP (@lem1062561 A B b Fn Z h1) (@lem1062669 A B b Fn Z)). Qed.
Lemma lem1062671 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (h1 : term418 A B Z r) : term418 A B Z r.
Proof. exact (h1). Qed.
Lemma lem1062677 {A : Type'} (P : A -> Prop) : (term53 A P) = (term54 A P).
Proof. exact (EQ_MP (@lem1061664 A P) (@lem1061663 A P)). Qed.
Lemma lem1062678 {B : Type'} (P : B -> Prop) : (term53 B P) = (term54 B P).
Proof. exact (@lem1062677 B P). Qed.
Lemma lem1062679 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (n : nat) : (term484 A B Z r n) = (term485 A B Z r n).
Proof. exact (@lem1062678 B (term486 A B Z r n)). Qed.
Lemma lem1062680 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (n : nat) (y : B) : (term487 A B Z r n y) = (term488 A B Z r n y).
Proof. exact (eq_refl (term487 A B Z r n y)). Qed.
Lemma lem1062681 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (n : nat) : (term489 A B Z r n) = (term486 A B Z r n).
Proof. exact (fun_ext (fun y : B => @lem1062680 A B Z r n y)). Qed.
Lemma lem1062682 {B : Type'} : (@ex1 B) = (@ex1 B).
Proof. exact (eq_refl (@ex1 B)). Qed.
Lemma lem1062683 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (n : nat) : (term484 A B Z r n) = (term414 A B Z r n).
Proof. exact (MK_COMB (@lem1062682 B) (@lem1062681 A B Z r n)). Qed.
Lemma lem1062684 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1062685 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (n : nat) : (term490 A B Z r n) = (term491 A B Z r n).
Proof. exact (MK_COMB (@lem1062684) (@lem1062683 A B Z r n)). Qed.
Lemma lem1062686 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (n : nat) (y : B) : (term487 A B Z r n y) = (term488 A B Z r n y).
Proof. exact (eq_refl (term487 A B Z r n y)). Qed.
Lemma lem1062687 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (n : nat) : (term489 A B Z r n) = (term486 A B Z r n).
Proof. exact (fun_ext (fun y : B => @lem1062686 A B Z r n y)). Qed.
Lemma lem1062688 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem1062689 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (n : nat) : (term492 A B Z r n) = (term493 A B Z r n).
Proof. exact (MK_COMB (@lem1062688 B) (@lem1062687 A B Z r n)). Qed.
Lemma lem1062690 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1062691 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (n : nat) : (term494 A B Z r n) = (term495 A B Z r n).
Proof. exact (MK_COMB (@lem1062690) (@lem1062689 A B Z r n)). Qed.
Lemma lem1062692 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (n : nat) (y : B) : (term487 A B Z r n y) = (term488 A B Z r n y).
Proof. exact (eq_refl (term487 A B Z r n y)). Qed.
Lemma lem1062693 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1062694 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (n : nat) (y : B) : (term496 A B Z r n y) = (term497 A B Z r n y).
Proof. exact (MK_COMB (@lem1062693) (@lem1062692 A B Z r n y)). Qed.
Lemma lem1062695 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (n : nat) (x' : B) : (term487 A B Z r n x') = (term488 A B Z r n x').
Proof. exact (eq_refl (term487 A B Z r n x')). Qed.
Lemma lem1062696 {A B : Type'} (y : B) (Z : type1336 A B) (r : type1614 A) (n : nat) (x' : B) : (term498 A B y Z r n x') = (term499 A B y Z r n x').
Proof. exact (MK_COMB (@lem1062694 A B Z r n y) (@lem1062695 A B Z r n x')). Qed.
Lemma lem1062697 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1062698 {A B : Type'} (y : B) (Z : type1336 A B) (r : type1614 A) (n : nat) (x' : B) : (term500 A B y Z r n x') = (term501 A B y Z r n x').
Proof. exact (MK_COMB (@lem1062697) (@lem1062696 A B y Z r n x')). Qed.
Lemma lem1062699 {B : Type'} (y : B) (x' : B) : (y = x') = (y = x').
Proof. exact (eq_refl (y = x')). Qed.
Lemma lem1062700 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (n : nat) (y : B) (x' : B) : (term502 A B Z r n y x') = (term503 A B Z r n y x').
Proof. exact (MK_COMB (@lem1062698 A B y Z r n x') (@lem1062699 B y x')). Qed.
Lemma lem1062701 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (n : nat) (y : B) : (term504 A B Z r n y) = (term505 A B Z r n y).
Proof. exact (fun_ext (fun x' : B => @lem1062700 A B Z r n y x')). Qed.
Lemma lem1062702 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1062703 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (n : nat) (y : B) : (term506 A B Z r n y) = (term507 A B Z r n y).
Proof. exact (MK_COMB (@lem1062702 B) (@lem1062701 A B Z r n y)). Qed.
Lemma lem1062704 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (n : nat) : (term508 A B Z r n) = (term509 A B Z r n).
Proof. exact (fun_ext (fun y : B => @lem1062703 A B Z r n y)). Qed.
Lemma lem1062705 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1062706 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (n : nat) : (term510 A B Z r n) = (term511 A B Z r n).
Proof. exact (MK_COMB (@lem1062705 B) (@lem1062704 A B Z r n)). Qed.
Lemma lem1062707 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (n : nat) : (term485 A B Z r n) = (term512 A B Z r n).
Proof. exact (MK_COMB (@lem1062691 A B Z r n) (@lem1062706 A B Z r n)). Qed.
Lemma lem1062708 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (n : nat) : ((term484 A B Z r n) = (term485 A B Z r n)) = ((term414 A B Z r n) = (term512 A B Z r n)).
Proof. exact (MK_COMB (@lem1062685 A B Z r n) (@lem1062707 A B Z r n)). Qed.
Lemma lem1062709 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (n : nat) : (term414 A B Z r n) = (term512 A B Z r n).
Proof. exact (EQ_MP (@lem1062708 A B Z r n) (@lem1062679 A B Z r n)). Qed.
Lemma lem1062730 {A B : Type'} (Z : type1336 A B) (r : type1614 A) : (term416 A B Z r) = (term513 A B Z r).
Proof. exact (fun_ext (fun n : nat => @lem1062709 A B Z r n)). Qed.
Lemma lem1062731 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1062732 {A B : Type'} (Z : type1336 A B) (r : type1614 A) : (term418 A B Z r) = (term514 A B Z r).
Proof. exact (MK_COMB (@lem1062731) (@lem1062730 A B Z r)). Qed.
Lemma lem1062734 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term61 A P Q) = (term62 A P Q).
Proof. exact (EQ_MP (@lem1061661 A P Q) (@lem1061660 A P Q)). Qed.
Lemma lem1062735 (P : nat -> Prop) (Q : nat -> Prop) : (term515 P Q) = (term516 P Q).
Proof. exact (@lem1062734 nat P Q). Qed.
Lemma lem1062736 {A B : Type'} (Z : type1336 A B) (r : type1614 A) : (term517 A B Z r) = (term518 A B Z r).
Proof. exact (@lem1062735 (term519 A B Z r) (term520 A B Z r)). Qed.
Lemma lem1062737 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (n : nat) : (term521 A B Z r n) = (term493 A B Z r n).
Proof. exact (eq_refl (term521 A B Z r n)). Qed.
Lemma lem1062738 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1062739 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (n : nat) : (term522 A B Z r n) = (term495 A B Z r n).
Proof. exact (MK_COMB (@lem1062738) (@lem1062737 A B Z r n)). Qed.
Lemma lem1062740 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (n : nat) : (term523 A B Z r n) = (term511 A B Z r n).
Proof. exact (eq_refl (term523 A B Z r n)). Qed.
Lemma lem1062741 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (n : nat) : (term524 A B Z r n) = (term512 A B Z r n).
Proof. exact (MK_COMB (@lem1062739 A B Z r n) (@lem1062740 A B Z r n)). Qed.
Lemma lem1062742 {A B : Type'} (Z : type1336 A B) (r : type1614 A) : (term525 A B Z r) = (term513 A B Z r).
Proof. exact (fun_ext (fun n : nat => @lem1062741 A B Z r n)). Qed.
Lemma lem1062743 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1062744 {A B : Type'} (Z : type1336 A B) (r : type1614 A) : (term517 A B Z r) = (term514 A B Z r).
Proof. exact (MK_COMB (@lem1062743) (@lem1062742 A B Z r)). Qed.
Lemma lem1062745 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1062746 {A B : Type'} (Z : type1336 A B) (r : type1614 A) : (term526 A B Z r) = (term527 A B Z r).
Proof. exact (MK_COMB (@lem1062745) (@lem1062744 A B Z r)). Qed.
Lemma lem1062747 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (n : nat) : (term521 A B Z r n) = (term493 A B Z r n).
Proof. exact (eq_refl (term521 A B Z r n)). Qed.
Lemma lem1062748 {A B : Type'} (Z : type1336 A B) (r : type1614 A) : (term528 A B Z r) = (term519 A B Z r).
Proof. exact (fun_ext (fun n : nat => @lem1062747 A B Z r n)). Qed.
Lemma lem1062749 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1062750 {A B : Type'} (Z : type1336 A B) (r : type1614 A) : (term529 A B Z r) = (term530 A B Z r).
Proof. exact (MK_COMB (@lem1062749) (@lem1062748 A B Z r)). Qed.
Lemma lem1062751 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1062752 {A B : Type'} (Z : type1336 A B) (r : type1614 A) : (term531 A B Z r) = (term532 A B Z r).
Proof. exact (MK_COMB (@lem1062751) (@lem1062750 A B Z r)). Qed.
Lemma lem1062753 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (n : nat) : (term523 A B Z r n) = (term511 A B Z r n).
Proof. exact (eq_refl (term523 A B Z r n)). Qed.
Lemma lem1062754 {A B : Type'} (Z : type1336 A B) (r : type1614 A) : (term533 A B Z r) = (term520 A B Z r).
Proof. exact (fun_ext (fun n : nat => @lem1062753 A B Z r n)). Qed.
Lemma lem1062755 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1062756 {A B : Type'} (Z : type1336 A B) (r : type1614 A) : (term534 A B Z r) = (term535 A B Z r).
Proof. exact (MK_COMB (@lem1062755) (@lem1062754 A B Z r)). Qed.
Lemma lem1062757 {A B : Type'} (Z : type1336 A B) (r : type1614 A) : (term518 A B Z r) = (term536 A B Z r).
Proof. exact (MK_COMB (@lem1062752 A B Z r) (@lem1062756 A B Z r)). Qed.
Lemma lem1062758 {A B : Type'} (Z : type1336 A B) (r : type1614 A) : ((term517 A B Z r) = (term518 A B Z r)) = ((term514 A B Z r) = (term536 A B Z r)).
Proof. exact (MK_COMB (@lem1062746 A B Z r) (@lem1062757 A B Z r)). Qed.
Lemma lem1062759 {A B : Type'} (Z : type1336 A B) (r : type1614 A) : (term514 A B Z r) = (term536 A B Z r).
Proof. exact (EQ_MP (@lem1062758 A B Z r) (@lem1062736 A B Z r)). Qed.
Lemma lem1062788 {A B : Type'} (Z : type1336 A B) (r : type1614 A) : (term418 A B Z r) = (term536 A B Z r).
Proof. exact (TRANS (@lem1062732 A B Z r) (@lem1062759 A B Z r)). Qed.
Lemma lem1062789 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (h1 : term418 A B Z r) : term536 A B Z r.
Proof. exact (EQ_MP (@lem1062788 A B Z r) (@lem1062671 A B Z r h1)). Qed.
Lemma lem1062790 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (h1 : term536 A B Z r) : term536 A B Z r.
Proof. exact (h1). Qed.
Lemma lem1062791 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (h1 : term535 A B Z r) : term535 A B Z r.
Proof. exact (h1). Qed.
Lemma lem1062792 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (h1 : term530 A B Z r) : term530 A B Z r.
Proof. exact (h1). Qed.
Lemma lem1062793 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (h1 : term530 A B Z r) : term530 A B Z r.
Proof. exact (h1). Qed.
Lemma lem1062795 {A B : Type'} (P : type1413 A B) : (term56 A B P) = (term57 A B P).
Proof. exact (EQ_MP (@lem1061655 A B P) (@lem1061654 A B P)). Qed.
Lemma lem1062796 {B : Type'} (P : type1597 B) : (term537 B P) = (term538 B P).
Proof. exact (@lem1062795 nat B P). Qed.
Lemma lem1062797 {A B : Type'} (Z : type1336 A B) (r : type1614 A) : (term539 A B Z r) = (term540 A B Z r).
Proof. exact (@lem1062796 B (term541 A B Z r)). Qed.
Lemma lem1062798 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (n : nat) : (term542 A B Z r n) = (term486 A B Z r n).
Proof. exact (eq_refl (term542 A B Z r n)). Qed.
Lemma lem1062799 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1062800 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (n : nat) (y : B) : (term543 A B Z r n y) = (term487 A B Z r n y).
Proof. exact (MK_COMB (@lem1062798 A B Z r n) (@lem1062799 B y)). Qed.
Lemma lem1062801 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (n : nat) (y : B) : (term487 A B Z r n y) = (term488 A B Z r n y).
Proof. exact (eq_refl (term487 A B Z r n y)). Qed.
Lemma lem1062802 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (n : nat) (y : B) : (term543 A B Z r n y) = (term488 A B Z r n y).
Proof. exact (TRANS (@lem1062800 A B Z r n y) (@lem1062801 A B Z r n y)). Qed.
Lemma lem1062803 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (n : nat) : (term544 A B Z r n) = (term486 A B Z r n).
Proof. exact (fun_ext (fun y : B => @lem1062802 A B Z r n y)). Qed.
Lemma lem1062804 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem1062805 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (n : nat) : (term545 A B Z r n) = (term493 A B Z r n).
Proof. exact (MK_COMB (@lem1062804 B) (@lem1062803 A B Z r n)). Qed.
Lemma lem1062806 {A B : Type'} (Z : type1336 A B) (r : type1614 A) : (term546 A B Z r) = (term519 A B Z r).
Proof. exact (fun_ext (fun n : nat => @lem1062805 A B Z r n)). Qed.
Lemma lem1062807 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1062808 {A B : Type'} (Z : type1336 A B) (r : type1614 A) : (term539 A B Z r) = (term530 A B Z r).
Proof. exact (MK_COMB (@lem1062807) (@lem1062806 A B Z r)). Qed.
Lemma lem1062809 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1062810 {A B : Type'} (Z : type1336 A B) (r : type1614 A) : (term547 A B Z r) = (term548 A B Z r).
Proof. exact (MK_COMB (@lem1062809) (@lem1062808 A B Z r)). Qed.
Lemma lem1062811 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (n : nat) : (term542 A B Z r n) = (term486 A B Z r n).
Proof. exact (eq_refl (term542 A B Z r n)). Qed.
Lemma lem1062812 {B : Type'} (y : nat -> B) (n : nat) : (y n) = (y n).
Proof. exact (eq_refl (y n)). Qed.
Lemma lem1062813 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (n : nat) : (term549 A B Z r y n) = (term550 A B Z r y n).
Proof. exact (MK_COMB (@lem1062811 A B Z r n) (@lem1062812 B y n)). Qed.
Lemma lem1062814 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (n : nat) : (term550 A B Z r y n) = (term358 A B Z r y n).
Proof. exact (eq_refl (term550 A B Z r y n)). Qed.
Lemma lem1062815 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (n : nat) : (term549 A B Z r y n) = (term358 A B Z r y n).
Proof. exact (TRANS (@lem1062813 A B Z r y n) (@lem1062814 A B Z r y n)). Qed.
Lemma lem1062816 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (y : nat -> B) : (term551 A B Z r y) = (term356 A B Z r y).
Proof. exact (fun_ext (fun n : nat => @lem1062815 A B Z r y n)). Qed.
Lemma lem1062817 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1062818 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (y : nat -> B) : (term552 A B Z r y) = (term101 A B Z r y).
Proof. exact (MK_COMB (@lem1062817) (@lem1062816 A B Z r y)). Qed.
Lemma lem1062819 {A B : Type'} (Z : type1336 A B) (r : type1614 A) : (term553 A B Z r) = (term554 A B Z r).
Proof. exact (fun_ext (fun y : nat -> B => @lem1062818 A B Z r y)). Qed.
Lemma lem1062820 {B : Type'} : (@ex (nat -> B)) = (@ex (nat -> B)).
Proof. exact (eq_refl (@ex (nat -> B))). Qed.
Lemma lem1062821 {A B : Type'} (Z : type1336 A B) (r : type1614 A) : (term540 A B Z r) = (term555 A B Z r).
Proof. exact (MK_COMB (@lem1062820 B) (@lem1062819 A B Z r)). Qed.
Lemma lem1062822 {A B : Type'} (Z : type1336 A B) (r : type1614 A) : ((term539 A B Z r) = (term540 A B Z r)) = ((term530 A B Z r) = (term555 A B Z r)).
Proof. exact (MK_COMB (@lem1062810 A B Z r) (@lem1062821 A B Z r)). Qed.
Lemma lem1062823 {A B : Type'} (Z : type1336 A B) (r : type1614 A) : (term530 A B Z r) = (term555 A B Z r).
Proof. exact (EQ_MP (@lem1062822 A B Z r) (@lem1062797 A B Z r)). Qed.
Lemma lem1062832 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (h1 : term530 A B Z r) : term555 A B Z r.
Proof. exact (EQ_MP (@lem1062823 A B Z r) (@lem1062793 A B Z r h1)). Qed.
Lemma lem1062833 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (h1 : term555 A B Z r) : term555 A B Z r.
Proof. exact (h1). Qed.
Lemma lem1062834 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (h1 : term101 A B Z r y) : term101 A B Z r y.
Proof. exact (h1). Qed.
Lemma lem1062836 {A : Type'} (P : A -> Prop) : (term53 A P) = (term54 A P).
Proof. exact (EQ_MP (@lem1061652 A P) (@lem1061651 A P)). Qed.
Lemma lem1062837 {B : Type'} (P : B -> Prop) : (term53 B P) = (term54 B P).
Proof. exact (@lem1062836 B P). Qed.
Lemma lem1062838 {A B : Type'} (Z : type1336 A B) (c : nat) (i : A) (r : type1614 A) : (term556 A B Z c i r) = (term557 A B Z c i r).
Proof. exact (@lem1062837 B (term558 A B Z c i r)). Qed.
Lemma lem1062839 {A B : Type'} (Z : type1336 A B) (c : nat) (i : A) (r : type1614 A) (y : B) : (term559 A B Z c i r y) = (term560 A B Z c i r y).
Proof. exact (eq_refl (term559 A B Z c i r y)). Qed.
Lemma lem1062840 {A B : Type'} (Z : type1336 A B) (c : nat) (i : A) (r : type1614 A) : (term561 A B Z c i r) = (term558 A B Z c i r).
Proof. exact (fun_ext (fun y : B => @lem1062839 A B Z c i r y)). Qed.
Lemma lem1062841 {B : Type'} : (@ex1 B) = (@ex1 B).
Proof. exact (eq_refl (@ex1 B)). Qed.
Lemma lem1062842 {A B : Type'} (Z : type1336 A B) (c : nat) (i : A) (r : type1614 A) : (term556 A B Z c i r) = (term422 A B Z c i r).
Proof. exact (MK_COMB (@lem1062841 B) (@lem1062840 A B Z c i r)). Qed.
Lemma lem1062843 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1062844 {A B : Type'} (Z : type1336 A B) (c : nat) (i : A) (r : type1614 A) : (term562 A B Z c i r) = (term563 A B Z c i r).
Proof. exact (MK_COMB (@lem1062843) (@lem1062842 A B Z c i r)). Qed.
Lemma lem1062845 {A B : Type'} (Z : type1336 A B) (c : nat) (i : A) (r : type1614 A) (y : B) : (term559 A B Z c i r y) = (term560 A B Z c i r y).
Proof. exact (eq_refl (term559 A B Z c i r y)). Qed.
Lemma lem1062846 {A B : Type'} (Z : type1336 A B) (c : nat) (i : A) (r : type1614 A) : (term561 A B Z c i r) = (term558 A B Z c i r).
Proof. exact (fun_ext (fun y : B => @lem1062845 A B Z c i r y)). Qed.
Lemma lem1062847 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem1062848 {A B : Type'} (Z : type1336 A B) (c : nat) (i : A) (r : type1614 A) : (term564 A B Z c i r) = (term565 A B Z c i r).
Proof. exact (MK_COMB (@lem1062847 B) (@lem1062846 A B Z c i r)). Qed.
Lemma lem1062849 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1062850 {A B : Type'} (Z : type1336 A B) (c : nat) (i : A) (r : type1614 A) : (term566 A B Z c i r) = (term567 A B Z c i r).
Proof. exact (MK_COMB (@lem1062849) (@lem1062848 A B Z c i r)). Qed.
Lemma lem1062851 {A B : Type'} (Z : type1336 A B) (c : nat) (i : A) (r : type1614 A) (y : B) : (term559 A B Z c i r y) = (term560 A B Z c i r y).
Proof. exact (eq_refl (term559 A B Z c i r y)). Qed.
Lemma lem1062852 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1062853 {A B : Type'} (Z : type1336 A B) (c : nat) (i : A) (r : type1614 A) (y : B) : (term568 A B Z c i r y) = (term569 A B Z c i r y).
Proof. exact (MK_COMB (@lem1062852) (@lem1062851 A B Z c i r y)). Qed.
Lemma lem1062854 {A B : Type'} (Z : type1336 A B) (c : nat) (i : A) (r : type1614 A) (x' : B) : (term559 A B Z c i r x') = (term560 A B Z c i r x').
Proof. exact (eq_refl (term559 A B Z c i r x')). Qed.
Lemma lem1062855 {A B : Type'} (y : B) (Z : type1336 A B) (c : nat) (i : A) (r : type1614 A) (x' : B) : (term570 A B y Z c i r x') = (term571 A B y Z c i r x').
Proof. exact (MK_COMB (@lem1062853 A B Z c i r y) (@lem1062854 A B Z c i r x')). Qed.
Lemma lem1062856 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1062857 {A B : Type'} (y : B) (Z : type1336 A B) (c : nat) (i : A) (r : type1614 A) (x' : B) : (term572 A B y Z c i r x') = (term573 A B y Z c i r x').
Proof. exact (MK_COMB (@lem1062856) (@lem1062855 A B y Z c i r x')). Qed.
Lemma lem1062858 {B : Type'} (y : B) (x' : B) : (y = x') = (y = x').
Proof. exact (eq_refl (y = x')). Qed.
Lemma lem1062859 {A B : Type'} (Z : type1336 A B) (c : nat) (i : A) (r : type1614 A) (y : B) (x' : B) : (term574 A B Z c i r y x') = (term575 A B Z c i r y x').
Proof. exact (MK_COMB (@lem1062857 A B y Z c i r x') (@lem1062858 B y x')). Qed.
Lemma lem1062860 {A B : Type'} (Z : type1336 A B) (c : nat) (i : A) (r : type1614 A) (y : B) : (term576 A B Z c i r y) = (term577 A B Z c i r y).
Proof. exact (fun_ext (fun x' : B => @lem1062859 A B Z c i r y x')). Qed.
Lemma lem1062861 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1062862 {A B : Type'} (Z : type1336 A B) (c : nat) (i : A) (r : type1614 A) (y : B) : (term578 A B Z c i r y) = (term579 A B Z c i r y).
Proof. exact (MK_COMB (@lem1062861 B) (@lem1062860 A B Z c i r y)). Qed.
Lemma lem1062863 {A B : Type'} (Z : type1336 A B) (c : nat) (i : A) (r : type1614 A) : (term580 A B Z c i r) = (term581 A B Z c i r).
Proof. exact (fun_ext (fun y : B => @lem1062862 A B Z c i r y)). Qed.
Lemma lem1062864 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1062865 {A B : Type'} (Z : type1336 A B) (c : nat) (i : A) (r : type1614 A) : (term582 A B Z c i r) = (term583 A B Z c i r).
Proof. exact (MK_COMB (@lem1062864 B) (@lem1062863 A B Z c i r)). Qed.
Lemma lem1062866 {A B : Type'} (Z : type1336 A B) (c : nat) (i : A) (r : type1614 A) : (term557 A B Z c i r) = (term584 A B Z c i r).
Proof. exact (MK_COMB (@lem1062850 A B Z c i r) (@lem1062865 A B Z c i r)). Qed.
Lemma lem1062867 {A B : Type'} (Z : type1336 A B) (c : nat) (i : A) (r : type1614 A) : ((term556 A B Z c i r) = (term557 A B Z c i r)) = ((term422 A B Z c i r) = (term584 A B Z c i r)).
Proof. exact (MK_COMB (@lem1062844 A B Z c i r) (@lem1062866 A B Z c i r)). Qed.
Lemma lem1062868 {A B : Type'} (Z : type1336 A B) (c : nat) (i : A) (r : type1614 A) : (term422 A B Z c i r) = (term584 A B Z c i r).
Proof. exact (EQ_MP (@lem1062867 A B Z c i r) (@lem1062838 A B Z c i r)). Qed.
Lemma lem1062889 {A B : Type'} (Z : type1336 A B) (c : nat) (i : A) (r : type1614 A) : (term584 A B Z c i r) = (term422 A B Z c i r).
Proof. exact (SYM (@lem1062868 A B Z c i r)). Qed.
Lemma lem1062980 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) (h1 : (term169 A B b a0 a1 Fn Z) = (Z a0 a1)) : (term169 A B b a0 a1 Fn Z) = (Z a0 a1).
Proof. exact (h1). Qed.
Lemma lem1062981 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (a0 : recspace A) (a1 : B) (h1 : (term169 A B b a0 a1 Fn Z) = (Z a0 a1)) : (Z a0 a1) = (term169 A B b a0 a1 Fn Z).
Proof. exact (SYM (@lem1062980 A B b Fn Z a0 a1 h1)). Qed.
Lemma lem1062982 {A B : Type'} (b : B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : (Z a0 a1) = (term169 A B b a0 a1 Fn Z)) : (Z a0 a1) = (term169 A B b a0 a1 Fn Z).
Proof. exact (h1). Qed.
Lemma lem1062983 {A B : Type'} (b : B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : (Z a0 a1) = (term169 A B b a0 a1 Fn Z)) : (term169 A B b a0 a1 Fn Z) = (Z a0 a1).
Proof. exact (SYM (@lem1062982 A B b a0 a1 Fn Z h1)). Qed.
Lemma lem1062984 {A B : Type'} (b : B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z : type1336 A B) : ((term169 A B b a0 a1 Fn Z) = (Z a0 a1)) = ((Z a0 a1) = (term169 A B b a0 a1 Fn Z)).
Proof. exact (prop_ext (fun h1 : (term169 A B b a0 a1 Fn Z) = (Z a0 a1) => @lem1062981 A B b Fn Z a0 a1 h1) (fun h1 : (Z a0 a1) = (term169 A B b a0 a1 Fn Z) => @lem1062983 A B b a0 a1 Fn Z h1)). Qed.
Lemma lem1062985 {A B : Type'} (b : B) (a0 : recspace A) (Fn : type1592 A B) (Z : type1336 A B) : (term401 A B b Fn Z a0) = (term400 A B b a0 Fn Z).
Proof. exact (fun_ext (fun a1 : B => @lem1062984 A B b a0 a1 Fn Z)). Qed.
Lemma lem1062986 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1062987 {A B : Type'} (b : B) (a0 : recspace A) (Fn : type1592 A B) (Z : type1336 A B) : (term402 A B b Fn Z a0) = (term259 A B b a0 Fn Z).
Proof. exact (MK_COMB (@lem1062986 B) (@lem1062985 A B b a0 Fn Z)). Qed.
Lemma lem1062988 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) : (term404 A B b Fn Z) = (term403 A B b Fn Z).
Proof. exact (fun_ext (fun a0 : recspace A => @lem1062987 A B b a0 Fn Z)). Qed.
Lemma lem1062989 {A : Type'} : (@all (recspace A)) = (@all (recspace A)).
Proof. exact (eq_refl (@all (recspace A))). Qed.
Lemma lem1062990 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) : (term405 A B b Fn Z) = (term260 A B b Fn Z).
Proof. exact (MK_COMB (@lem1062989 A) (@lem1062988 A B b Fn Z)). Qed.
Lemma lem1062991 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) : term260 A B b Fn Z.
Proof. exact (EQ_MP (@lem1062990 A B b Fn Z) (@lem1062485 A B b Fn Z h1)). Qed.
Lemma lem1062992 {A B : Type'} (a0 : recspace A) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) : term448 A B b Fn Z a0.
Proof. exact (@lem1062991 A B b Fn Z h1 a0). Qed.
Lemma lem1062993 {A B : Type'} (b : B) (a0 : recspace A) (Fn : type1592 A B) (Z : type1336 A B) : (term448 A B b Fn Z a0) = (term259 A B b a0 Fn Z).
Proof. exact (eq_refl (term448 A B b Fn Z a0)). Qed.
Lemma lem1062994 {A B : Type'} (a0 : recspace A) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) : term259 A B b a0 Fn Z.
Proof. exact (EQ_MP (@lem1062993 A B b a0 Fn Z) (@lem1062992 A B a0 b Fn Z h1)). Qed.
Lemma lem1062995 {A B : Type'} (a0 : recspace A) (a1 : B) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) : term449 A B b a0 Fn Z a1.
Proof. exact (@lem1062994 A B a0 b Fn Z h1 a1). Qed.
Lemma lem1062996 {A B : Type'} (b : B) (a0 : recspace A) (a1 : B) (Fn : type1592 A B) (Z : type1336 A B) : (term449 A B b a0 Fn Z a1) = ((Z a0 a1) = (term169 A B b a0 a1 Fn Z)).
Proof. exact (eq_refl (term449 A B b a0 Fn Z a1)). Qed.
Lemma lem1063005 {A B : Type'} (a0 : recspace A) (a1 : B) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) : (Z a0 a1) = (term169 A B b a0 a1 Fn Z).
Proof. exact (EQ_MP (@lem1062996 A B b a0 a1 Fn Z) (@lem1062995 A B a0 a1 b Fn Z h1)). Qed.
Lemma lem1063006 {A B : Type'} (a0 : recspace A) (a1 : B) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) : (Z a0 a1) = (term169 A B b a0 a1 Fn Z).
Proof. exact (@lem1063005 A B a0 a1 b Fn Z h1). Qed.
Lemma lem1063007 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : B) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) : (term560 A B Z c i r y) = (term585 A B b c i r y Fn Z).
Proof. exact (@lem1063006 A B (@CONSTR A c i r) y b Fn Z h1). Qed.
Lemma lem1063008 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) : (term558 A B Z c i r) = (term586 A B b c i r Fn Z).
Proof. exact (fun_ext (fun y : B => @lem1063007 A B c i r y b Fn Z h1)). Qed.
Lemma lem1063009 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem1063010 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) : (term565 A B Z c i r) = (term587 A B b c i r Fn Z).
Proof. exact (MK_COMB (@lem1063009 B) (@lem1063008 A B c i r b Fn Z h1)). Qed.
Lemma lem1063011 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1063012 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) : (term567 A B Z c i r) = (term588 A B b c i r Fn Z).
Proof. exact (MK_COMB (@lem1063011) (@lem1063010 A B c i r b Fn Z h1)). Qed.
Lemma lem1063026 {A B : Type'} (a0 : recspace A) (a1 : B) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) : (Z a0 a1) = (term169 A B b a0 a1 Fn Z).
Proof. exact (EQ_MP (@lem1062996 A B b a0 a1 Fn Z) (@lem1062995 A B a0 a1 b Fn Z h1)). Qed.
Lemma lem1063027 {A B : Type'} (a0 : recspace A) (a1 : B) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) : (Z a0 a1) = (term169 A B b a0 a1 Fn Z).
Proof. exact (@lem1063026 A B a0 a1 b Fn Z h1). Qed.
Lemma lem1063028 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : B) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) : (term560 A B Z c i r y) = (term585 A B b c i r y Fn Z).
Proof. exact (@lem1063027 A B (@CONSTR A c i r) y b Fn Z h1). Qed.
Lemma lem1063029 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1063030 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : B) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) : (term569 A B Z c i r y) = (term589 A B b c i r y Fn Z).
Proof. exact (MK_COMB (@lem1063029) (@lem1063028 A B c i r y b Fn Z h1)). Qed.
Lemma lem1063032 {A B : Type'} (a0 : recspace A) (a1 : B) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) : (Z a0 a1) = (term169 A B b a0 a1 Fn Z).
Proof. exact (EQ_MP (@lem1062996 A B b a0 a1 Fn Z) (@lem1062995 A B a0 a1 b Fn Z h1)). Qed.
Lemma lem1063033 {A B : Type'} (a0 : recspace A) (a1 : B) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) : (Z a0 a1) = (term169 A B b a0 a1 Fn Z).
Proof. exact (@lem1063032 A B a0 a1 b Fn Z h1). Qed.
Lemma lem1063034 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (x' : B) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) : (term560 A B Z c i r x') = (term585 A B b c i r x' Fn Z).
Proof. exact (@lem1063033 A B (@CONSTR A c i r) x' b Fn Z h1). Qed.
Lemma lem1063035 {A B : Type'} (y : B) (c : nat) (i : A) (r : type1614 A) (x' : B) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) : (term571 A B y Z c i r x') = (term590 A B y b c i r x' Fn Z).
Proof. exact (MK_COMB (@lem1063030 A B c i r y b Fn Z h1) (@lem1063034 A B c i r x' b Fn Z h1)). Qed.
Lemma lem1063036 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1063037 {A B : Type'} (y : B) (c : nat) (i : A) (r : type1614 A) (x' : B) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) : (term573 A B y Z c i r x') = (term591 A B y b c i r x' Fn Z).
Proof. exact (MK_COMB (@lem1063036) (@lem1063035 A B y c i r x' b Fn Z h1)). Qed.
Lemma lem1063040 {B : Type'} (y : B) (x' : B) : (y = x') = (y = x').
Proof. exact (eq_refl (y = x')). Qed.
Lemma lem1063041 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : B) (x' : B) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) : (term575 A B Z c i r y x') = (term592 A B b c i r Fn Z y x').
Proof. exact (MK_COMB (@lem1063037 A B y c i r x' b Fn Z h1) (@lem1063040 B y x')). Qed.
Lemma lem1063042 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : B) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) : (term577 A B Z c i r y) = (term593 A B b c i r Fn Z y).
Proof. exact (fun_ext (fun x' : B => @lem1063041 A B c i r y x' b Fn Z h1)). Qed.
Lemma lem1063043 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1063044 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : B) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) : (term579 A B Z c i r y) = (term594 A B b c i r Fn Z y).
Proof. exact (MK_COMB (@lem1063043 B) (@lem1063042 A B c i r y b Fn Z h1)). Qed.
Lemma lem1063045 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) : (term581 A B Z c i r) = (term595 A B b c i r Fn Z).
Proof. exact (fun_ext (fun y : B => @lem1063044 A B c i r y b Fn Z h1)). Qed.
Lemma lem1063046 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1063047 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) : (term583 A B Z c i r) = (term596 A B b c i r Fn Z).
Proof. exact (MK_COMB (@lem1063046 B) (@lem1063045 A B c i r b Fn Z h1)). Qed.
Lemma lem1063048 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) : (term584 A B Z c i r) = (term597 A B b c i r Fn Z).
Proof. exact (MK_COMB (@lem1063012 A B c i r b Fn Z h1) (@lem1063047 A B c i r b Fn Z h1)). Qed.
Lemma lem1063049 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) : (term597 A B b c i r Fn Z) = (term584 A B Z c i r).
Proof. exact (SYM (@lem1063048 A B c i r b Fn Z h1)). Qed.
Lemma lem1063055 {A : Type'} (c : nat) (i : A) (r : type1614 A) : ((@CONSTR A c i r) = (@BOTTOM A)) = False.
Proof. exact (@lem1061638 A c i r (@lem1061637 A c i r)). Qed.
Lemma lem1063056 {A : Type'} (c : nat) (i : A) (r : type1614 A) : ((@CONSTR A c i r) = (@BOTTOM A)) = False.
Proof. exact (@lem1063055 A c i r). Qed.
Lemma lem1063057 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1063058 {A : Type'} (c : nat) (i : A) (r : type1614 A) : (term598 A c i r) = (and False).
Proof. exact (MK_COMB (@lem1063057) (@lem1063056 A c i r)). Qed.
Lemma lem1063061 {A B : Type'} (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (b : B) : ((Fn c i r y) = b) = ((Fn c i r y) = b).
Proof. exact (eq_refl ((Fn c i r y) = b)). Qed.
Lemma lem1063062 {A B : Type'} (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (b : B) : (term599 A B Fn c i r y b) = (term600 A B Fn c i r y b).
Proof. exact (MK_COMB (@lem1063058 A c i r) (@lem1063061 A B Fn c i r y b)). Qed.
Lemma lem1063064 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1063065 {A B : Type'} (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (b : B) : (term600 A B Fn c i r y b) = False.
Proof. exact (@lem1063064 ((Fn c i r y) = b)). Qed.
Lemma lem1063066 {A B : Type'} (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (b : B) : (term599 A B Fn c i r y b) = False.
Proof. exact (TRANS (@lem1063062 A B Fn c i r y b) (@lem1063065 A B Fn c i r y b)). Qed.
Lemma lem1063067 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1063068 {A B : Type'} (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (b : B) : (term601 A B Fn c i r y b) = (or False).
Proof. exact (MK_COMB (@lem1063067) (@lem1063066 A B Fn c i r y b)). Qed.
Lemma lem1063088 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : ((@CONSTR A c1 i1 r1) = (@CONSTR A c2 i2 r2)) = (term44 A c1 c2 i1 i2 r1 r2).
Proof. exact (EQ_MP (@lem1061627 A c1 c2 i1 i2 r1 r2) (@lem1061626 A c1 c2 i1 i2 r1 r2)). Qed.
Lemma lem1063089 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : ((@CONSTR A c1 i1 r1) = (@CONSTR A c2 i2 r2)) = (term44 A c1 c2 i1 i2 r1 r2).
Proof. exact (@lem1063088 A c1 c2 i1 i2 r1 r2). Qed.
Lemma lem1063090 {A : Type'} (c : nat) (c' : nat) (i : A) (i' : A) (r : type1614 A) (r' : type1614 A) : ((@CONSTR A c i r) = (@CONSTR A c' i' r')) = (term44 A c c' i i' r r').
Proof. exact (@lem1063089 A c c' i i' r r'). Qed.
Lemma lem1063101 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1063102 {A : Type'} (c : nat) (c' : nat) (i : A) (i' : A) (r : type1614 A) (r' : type1614 A) : (term602 A c i r c' i' r') = (term603 A c c' i i' r r').
Proof. exact (MK_COMB (@lem1063101) (@lem1063090 A c c' i i' r r')). Qed.
Lemma lem1063111 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y' : nat -> B) : (term604 A B c i r y Fn c' i' Z r' y') = (term604 A B c i r y Fn c' i' Z r' y').
Proof. exact (eq_refl (term604 A B c i r y Fn c' i' Z r' y')). Qed.
Lemma lem1063112 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y' : nat -> B) : (term605 A B c i r y Fn c' i' Z r' y') = (term606 A B c i r y Fn c' i' Z r' y').
Proof. exact (MK_COMB (@lem1063102 A c c' i i' r r') (@lem1063111 A B c i r y Fn c' i' Z r' y')). Qed.
Lemma lem1063114 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term17 t1 t2 t3) = (term16 t1 t2 t3).
Proof. exact (EQ_MP (@lem1061609 t1 t2 t3) (@lem1061608 t1 t2 t3)). Qed.
Lemma lem1063115 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y' : nat -> B) : (term606 A B c i r y Fn c' i' Z r' y') = (term607 A B c i r y Fn c' i' Z r' y').
Proof. exact (@lem1063114 (c = c') (term608 A i i' r r') (term604 A B c i r y Fn c' i' Z r' y')). Qed.
Lemma lem1063121 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term17 t1 t2 t3) = (term16 t1 t2 t3).
Proof. exact (EQ_MP (@lem1061609 t1 t2 t3) (@lem1061608 t1 t2 t3)). Qed.
Lemma lem1063122 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y' : nat -> B) : (term609 A B c i r y Fn c' i' Z r' y') = (term610 A B c i r y Fn c' i' Z r' y').
Proof. exact (@lem1063121 (i = i') (r = r') (term604 A B c i r y Fn c' i' Z r' y')). Qed.
Lemma lem1063139 (c : nat) (c' : nat) : (term611 c c') = (term611 c c').
Proof. exact (eq_refl (term611 c c')). Qed.
Lemma lem1063140 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y' : nat -> B) : (term607 A B c i r y Fn c' i' Z r' y') = (term612 A B c i r y Fn c' i' Z r' y').
Proof. exact (MK_COMB (@lem1063139 c c') (@lem1063122 A B c i r y Fn c' i' Z r' y')). Qed.
Lemma lem1063143 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y' : nat -> B) : (term606 A B c i r y Fn c' i' Z r' y') = (term612 A B c i r y Fn c' i' Z r' y').
Proof. exact (TRANS (@lem1063115 A B c i r y Fn c' i' Z r' y') (@lem1063140 A B c i r y Fn c' i' Z r' y')). Qed.
Lemma lem1063144 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y' : nat -> B) : (term605 A B c i r y Fn c' i' Z r' y') = (term612 A B c i r y Fn c' i' Z r' y').
Proof. exact (TRANS (@lem1063112 A B c i r y Fn c' i' Z r' y') (@lem1063143 A B c i r y Fn c' i' Z r' y')). Qed.
Lemma lem1063145 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term613 A B c i r y Fn c' i' Z r') = (term614 A B c i r y Fn c' i' Z r').
Proof. exact (fun_ext (fun y' : nat -> B => @lem1063144 A B c i r y Fn c' i' Z r' y')). Qed.
Lemma lem1063146 {B : Type'} : (@ex (nat -> B)) = (@ex (nat -> B)).
Proof. exact (eq_refl (@ex (nat -> B))). Qed.
Lemma lem1063147 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term615 A B c i r y Fn c' i' Z r') = (term616 A B c i r y Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1063146 B) (@lem1063145 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1063152 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term617 A B c i r y Fn c' i' Z) = (term618 A B c i r y Fn c' i' Z).
Proof. exact (fun_ext (fun r' : type1614 A => @lem1063147 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1063153 {A : Type'} : (@ex (nat -> recspace A)) = (@ex (nat -> recspace A)).
Proof. exact (eq_refl (@ex (nat -> recspace A))). Qed.
Lemma lem1063154 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term619 A B c i r y Fn c' i' Z) = (term620 A B c i r y Fn c' i' Z).
Proof. exact (MK_COMB (@lem1063153 A) (@lem1063152 A B c i r y Fn c' i' Z)). Qed.
Lemma lem1063159 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) : (term621 A B c i r y Fn c' Z) = (term622 A B c i r y Fn c' Z).
Proof. exact (fun_ext (fun i' : A => @lem1063154 A B c i r y Fn c' i' Z)). Qed.
Lemma lem1063160 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1063161 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) : (term623 A B c i r y Fn c' Z) = (term624 A B c i r y Fn c' Z).
Proof. exact (MK_COMB (@lem1063160 A) (@lem1063159 A B c i r y Fn c' Z)). Qed.
Lemma lem1063166 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (Z : type1336 A B) : (term625 A B c i r y Fn Z) = (term626 A B c i r y Fn Z).
Proof. exact (fun_ext (fun c' : nat => @lem1063161 A B c i r y Fn c' Z)). Qed.
Lemma lem1063167 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1063168 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (Z : type1336 A B) : (term627 A B c i r y Fn Z) = (term628 A B c i r y Fn Z).
Proof. exact (MK_COMB (@lem1063167) (@lem1063166 A B c i r y Fn Z)). Qed.
Lemma lem1063173 {A B : Type'} (b : B) (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (Z : type1336 A B) : (term629 A B b c i r y Fn Z) = (term630 A B c i r y Fn Z).
Proof. exact (MK_COMB (@lem1063068 A B Fn c i r y b) (@lem1063168 A B c i r y Fn Z)). Qed.
Lemma lem1063175 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem1063176 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (Z : type1336 A B) : (term630 A B c i r y Fn Z) = (term628 A B c i r y Fn Z).
Proof. exact (@lem1063175 (term628 A B c i r y Fn Z)). Qed.
Lemma lem1063213 {A B : Type'} (b : B) (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (Z : type1336 A B) : (term629 A B b c i r y Fn Z) = (term628 A B c i r y Fn Z).
Proof. exact (TRANS (@lem1063173 A B b c i r y Fn Z) (@lem1063176 A B c i r y Fn Z)). Qed.
Lemma lem1063214 {A B : Type'} (b : B) (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (Z : type1336 A B) : (term628 A B c i r y Fn Z) = (term629 A B b c i r y Fn Z).
Proof. exact (SYM (@lem1063213 A B b c i r y Fn Z)). Qed.
Lemma lem1063230 {A : Type'} (P : Prop) (Q : A -> Prop) : (term10 A P Q) = (term11 A P Q).
Proof. exact (EQ_MP (@lem1061576 A P Q) (@lem1061575 A P Q)). Qed.
Lemma lem1063231 {B : Type'} (P : Prop) (Q : type976 B) : (term631 B P Q) = (term632 B P Q).
Proof. exact (@lem1063230 (nat -> B) P Q). Qed.
Lemma lem1063232 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term633 A B c i r y Fn c' i' Z r') = (term634 A B c i r y Fn c' i' Z r').
Proof. exact (@lem1063231 B (c = c') (term635 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1063233 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y' : nat -> B) : (term636 A B c i r y Fn c' i' Z r' y') = (term610 A B c i r y Fn c' i' Z r' y').
Proof. exact (eq_refl (term636 A B c i r y Fn c' i' Z r' y')). Qed.
Lemma lem1063234 (c : nat) (c' : nat) : (term611 c c') = (term611 c c').
Proof. exact (eq_refl (term611 c c')). Qed.
Lemma lem1063235 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y' : nat -> B) : (term637 A B c i r y Fn c' i' Z r' y') = (term612 A B c i r y Fn c' i' Z r' y').
Proof. exact (MK_COMB (@lem1063234 c c') (@lem1063233 A B c i r y Fn c' i' Z r' y')). Qed.
Lemma lem1063236 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term638 A B c i r y Fn c' i' Z r') = (term614 A B c i r y Fn c' i' Z r').
Proof. exact (fun_ext (fun y' : nat -> B => @lem1063235 A B c i r y Fn c' i' Z r' y')). Qed.
Lemma lem1063237 {B : Type'} : (@ex (nat -> B)) = (@ex (nat -> B)).
Proof. exact (eq_refl (@ex (nat -> B))). Qed.
Lemma lem1063238 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term633 A B c i r y Fn c' i' Z r') = (term616 A B c i r y Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1063237 B) (@lem1063236 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1063239 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1063240 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term639 A B c i r y Fn c' i' Z r') = (term640 A B c i r y Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1063239) (@lem1063238 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1063241 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y' : nat -> B) : (term636 A B c i r y Fn c' i' Z r' y') = (term610 A B c i r y Fn c' i' Z r' y').
Proof. exact (eq_refl (term636 A B c i r y Fn c' i' Z r' y')). Qed.
Lemma lem1063242 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term641 A B c i r y Fn c' i' Z r') = (term635 A B c i r y Fn c' i' Z r').
Proof. exact (fun_ext (fun y' : nat -> B => @lem1063241 A B c i r y Fn c' i' Z r' y')). Qed.
Lemma lem1063243 {B : Type'} : (@ex (nat -> B)) = (@ex (nat -> B)).
Proof. exact (eq_refl (@ex (nat -> B))). Qed.
Lemma lem1063244 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term642 A B c i r y Fn c' i' Z r') = (term643 A B c i r y Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1063243 B) (@lem1063242 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1063245 (c : nat) (c' : nat) : (term611 c c') = (term611 c c').
Proof. exact (eq_refl (term611 c c')). Qed.
Lemma lem1063246 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term634 A B c i r y Fn c' i' Z r') = (term644 A B c i r y Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1063245 c c') (@lem1063244 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1063247 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : ((term633 A B c i r y Fn c' i' Z r') = (term634 A B c i r y Fn c' i' Z r')) = ((term616 A B c i r y Fn c' i' Z r') = (term644 A B c i r y Fn c' i' Z r')).
Proof. exact (MK_COMB (@lem1063240 A B c i r y Fn c' i' Z r') (@lem1063246 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1063248 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term616 A B c i r y Fn c' i' Z r') = (term644 A B c i r y Fn c' i' Z r').
Proof. exact (EQ_MP (@lem1063247 A B c i r y Fn c' i' Z r') (@lem1063232 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1063256 {A : Type'} (P : Prop) (Q : A -> Prop) : (term10 A P Q) = (term11 A P Q).
Proof. exact (EQ_MP (@lem1061576 A P Q) (@lem1061575 A P Q)). Qed.
Lemma lem1063257 {B : Type'} (P : Prop) (Q : type976 B) : (term631 B P Q) = (term632 B P Q).
Proof. exact (@lem1063256 (nat -> B) P Q). Qed.
Lemma lem1063258 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term645 A B c i r y Fn c' i' Z r') = (term646 A B c i r y Fn c' i' Z r').
Proof. exact (@lem1063257 B (i = i') (term647 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1063259 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y' : nat -> B) : (term648 A B c i r y Fn c' i' Z r' y') = (term649 A B c i r y Fn c' i' Z r' y').
Proof. exact (eq_refl (term648 A B c i r y Fn c' i' Z r' y')). Qed.
Lemma lem1063260 {A : Type'} (i : A) (i' : A) : (term650 A i i') = (term650 A i i').
Proof. exact (eq_refl (term650 A i i')). Qed.
Lemma lem1063261 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y' : nat -> B) : (term651 A B c i r y Fn c' i' Z r' y') = (term610 A B c i r y Fn c' i' Z r' y').
Proof. exact (MK_COMB (@lem1063260 A i i') (@lem1063259 A B c i r y Fn c' i' Z r' y')). Qed.
Lemma lem1063262 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term652 A B c i r y Fn c' i' Z r') = (term635 A B c i r y Fn c' i' Z r').
Proof. exact (fun_ext (fun y' : nat -> B => @lem1063261 A B c i r y Fn c' i' Z r' y')). Qed.
Lemma lem1063263 {B : Type'} : (@ex (nat -> B)) = (@ex (nat -> B)).
Proof. exact (eq_refl (@ex (nat -> B))). Qed.
Lemma lem1063264 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term645 A B c i r y Fn c' i' Z r') = (term643 A B c i r y Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1063263 B) (@lem1063262 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1063265 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1063266 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term653 A B c i r y Fn c' i' Z r') = (term654 A B c i r y Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1063265) (@lem1063264 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1063267 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y' : nat -> B) : (term648 A B c i r y Fn c' i' Z r' y') = (term649 A B c i r y Fn c' i' Z r' y').
Proof. exact (eq_refl (term648 A B c i r y Fn c' i' Z r' y')). Qed.
Lemma lem1063268 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term655 A B c i r y Fn c' i' Z r') = (term647 A B c i r y Fn c' i' Z r').
Proof. exact (fun_ext (fun y' : nat -> B => @lem1063267 A B c i r y Fn c' i' Z r' y')). Qed.
Lemma lem1063269 {B : Type'} : (@ex (nat -> B)) = (@ex (nat -> B)).
Proof. exact (eq_refl (@ex (nat -> B))). Qed.
Lemma lem1063270 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term656 A B c i r y Fn c' i' Z r') = (term657 A B c i r y Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1063269 B) (@lem1063268 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1063271 {A : Type'} (i : A) (i' : A) : (term650 A i i') = (term650 A i i').
Proof. exact (eq_refl (term650 A i i')). Qed.
Lemma lem1063272 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term646 A B c i r y Fn c' i' Z r') = (term658 A B c i r y Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1063271 A i i') (@lem1063270 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1063273 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : ((term645 A B c i r y Fn c' i' Z r') = (term646 A B c i r y Fn c' i' Z r')) = ((term643 A B c i r y Fn c' i' Z r') = (term658 A B c i r y Fn c' i' Z r')).
Proof. exact (MK_COMB (@lem1063266 A B c i r y Fn c' i' Z r') (@lem1063272 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1063274 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term643 A B c i r y Fn c' i' Z r') = (term658 A B c i r y Fn c' i' Z r').
Proof. exact (EQ_MP (@lem1063273 A B c i r y Fn c' i' Z r') (@lem1063258 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1063282 {A : Type'} (P : Prop) (Q : A -> Prop) : (term10 A P Q) = (term11 A P Q).
Proof. exact (EQ_MP (@lem1061576 A P Q) (@lem1061575 A P Q)). Qed.
Lemma lem1063283 {B : Type'} (P : Prop) (Q : type976 B) : (term631 B P Q) = (term632 B P Q).
Proof. exact (@lem1063282 (nat -> B) P Q). Qed.
Lemma lem1063284 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term659 A B c i r y Fn c' i' Z r') = (term660 A B c i r y Fn c' i' Z r').
Proof. exact (@lem1063283 B (r = r') (term661 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1063285 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y' : nat -> B) : (term662 A B c i r y Fn c' i' Z r' y') = (term604 A B c i r y Fn c' i' Z r' y').
Proof. exact (eq_refl (term662 A B c i r y Fn c' i' Z r' y')). Qed.
Lemma lem1063286 {A : Type'} (r : type1614 A) (r' : type1614 A) : (term663 A r r') = (term663 A r r').
Proof. exact (eq_refl (term663 A r r')). Qed.
Lemma lem1063287 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y' : nat -> B) : (term664 A B c i r y Fn c' i' Z r' y') = (term649 A B c i r y Fn c' i' Z r' y').
Proof. exact (MK_COMB (@lem1063286 A r r') (@lem1063285 A B c i r y Fn c' i' Z r' y')). Qed.
Lemma lem1063288 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term665 A B c i r y Fn c' i' Z r') = (term647 A B c i r y Fn c' i' Z r').
Proof. exact (fun_ext (fun y' : nat -> B => @lem1063287 A B c i r y Fn c' i' Z r' y')). Qed.
Lemma lem1063289 {B : Type'} : (@ex (nat -> B)) = (@ex (nat -> B)).
Proof. exact (eq_refl (@ex (nat -> B))). Qed.
Lemma lem1063290 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term659 A B c i r y Fn c' i' Z r') = (term657 A B c i r y Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1063289 B) (@lem1063288 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1063291 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1063292 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term666 A B c i r y Fn c' i' Z r') = (term667 A B c i r y Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1063291) (@lem1063290 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1063293 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y' : nat -> B) : (term662 A B c i r y Fn c' i' Z r' y') = (term604 A B c i r y Fn c' i' Z r' y').
Proof. exact (eq_refl (term662 A B c i r y Fn c' i' Z r' y')). Qed.
Lemma lem1063294 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term668 A B c i r y Fn c' i' Z r') = (term661 A B c i r y Fn c' i' Z r').
Proof. exact (fun_ext (fun y' : nat -> B => @lem1063293 A B c i r y Fn c' i' Z r' y')). Qed.
Lemma lem1063295 {B : Type'} : (@ex (nat -> B)) = (@ex (nat -> B)).
Proof. exact (eq_refl (@ex (nat -> B))). Qed.
Lemma lem1063296 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term669 A B c i r y Fn c' i' Z r') = (term670 A B c i r y Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1063295 B) (@lem1063294 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1063297 {A : Type'} (r : type1614 A) (r' : type1614 A) : (term663 A r r') = (term663 A r r').
Proof. exact (eq_refl (term663 A r r')). Qed.
Lemma lem1063298 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term660 A B c i r y Fn c' i' Z r') = (term671 A B c i r y Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1063297 A r r') (@lem1063296 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1063299 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : ((term659 A B c i r y Fn c' i' Z r') = (term660 A B c i r y Fn c' i' Z r')) = ((term657 A B c i r y Fn c' i' Z r') = (term671 A B c i r y Fn c' i' Z r')).
Proof. exact (MK_COMB (@lem1063292 A B c i r y Fn c' i' Z r') (@lem1063298 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1063300 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term657 A B c i r y Fn c' i' Z r') = (term671 A B c i r y Fn c' i' Z r').
Proof. exact (EQ_MP (@lem1063299 A B c i r y Fn c' i' Z r') (@lem1063284 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1063339 {A : Type'} (i : A) (i' : A) : (term650 A i i') = (term650 A i i').
Proof. exact (eq_refl (term650 A i i')). Qed.
Lemma lem1063340 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term658 A B c i r y Fn c' i' Z r') = (term672 A B c i r y Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1063339 A i i') (@lem1063300 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1063343 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term643 A B c i r y Fn c' i' Z r') = (term672 A B c i r y Fn c' i' Z r').
Proof. exact (TRANS (@lem1063274 A B c i r y Fn c' i' Z r') (@lem1063340 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1063344 (c : nat) (c' : nat) : (term611 c c') = (term611 c c').
Proof. exact (eq_refl (term611 c c')). Qed.
Lemma lem1063345 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term644 A B c i r y Fn c' i' Z r') = (term673 A B c i r y Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1063344 c c') (@lem1063343 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1063348 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term616 A B c i r y Fn c' i' Z r') = (term673 A B c i r y Fn c' i' Z r').
Proof. exact (TRANS (@lem1063248 A B c i r y Fn c' i' Z r') (@lem1063345 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1063349 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term618 A B c i r y Fn c' i' Z) = (term674 A B c i r y Fn c' i' Z).
Proof. exact (fun_ext (fun r' : type1614 A => @lem1063348 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1063350 {A : Type'} : (@ex (nat -> recspace A)) = (@ex (nat -> recspace A)).
Proof. exact (eq_refl (@ex (nat -> recspace A))). Qed.
Lemma lem1063351 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term620 A B c i r y Fn c' i' Z) = (term675 A B c i r y Fn c' i' Z).
Proof. exact (MK_COMB (@lem1063350 A) (@lem1063349 A B c i r y Fn c' i' Z)). Qed.
Lemma lem1063355 {A : Type'} (P : Prop) (Q : A -> Prop) : (term10 A P Q) = (term11 A P Q).
Proof. exact (EQ_MP (@lem1061576 A P Q) (@lem1061575 A P Q)). Qed.
Lemma lem1063356 {A : Type'} (P : Prop) (Q : type963 A) : (term676 A P Q) = (term677 A P Q).
Proof. exact (@lem1063355 (type1614 A) P Q). Qed.
Lemma lem1063357 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term678 A B c i r y Fn c' i' Z) = (term679 A B c i r y Fn c' i' Z).
Proof. exact (@lem1063356 A (c = c') (term680 A B c i r y Fn c' i' Z)). Qed.
Lemma lem1063358 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term681 A B c i r y Fn c' i' Z r') = (term672 A B c i r y Fn c' i' Z r').
Proof. exact (eq_refl (term681 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1063359 (c : nat) (c' : nat) : (term611 c c') = (term611 c c').
Proof. exact (eq_refl (term611 c c')). Qed.
Lemma lem1063360 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term682 A B c i r y Fn c' i' Z r') = (term673 A B c i r y Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1063359 c c') (@lem1063358 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1063361 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term683 A B c i r y Fn c' i' Z) = (term674 A B c i r y Fn c' i' Z).
Proof. exact (fun_ext (fun r' : type1614 A => @lem1063360 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1063362 {A : Type'} : (@ex (nat -> recspace A)) = (@ex (nat -> recspace A)).
Proof. exact (eq_refl (@ex (nat -> recspace A))). Qed.
Lemma lem1063363 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term678 A B c i r y Fn c' i' Z) = (term675 A B c i r y Fn c' i' Z).
Proof. exact (MK_COMB (@lem1063362 A) (@lem1063361 A B c i r y Fn c' i' Z)). Qed.
Lemma lem1063364 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1063365 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term684 A B c i r y Fn c' i' Z) = (term685 A B c i r y Fn c' i' Z).
Proof. exact (MK_COMB (@lem1063364) (@lem1063363 A B c i r y Fn c' i' Z)). Qed.
Lemma lem1063366 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term681 A B c i r y Fn c' i' Z r') = (term672 A B c i r y Fn c' i' Z r').
Proof. exact (eq_refl (term681 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1063367 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term686 A B c i r y Fn c' i' Z) = (term680 A B c i r y Fn c' i' Z).
Proof. exact (fun_ext (fun r' : type1614 A => @lem1063366 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1063368 {A : Type'} : (@ex (nat -> recspace A)) = (@ex (nat -> recspace A)).
Proof. exact (eq_refl (@ex (nat -> recspace A))). Qed.
Lemma lem1063369 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term687 A B c i r y Fn c' i' Z) = (term688 A B c i r y Fn c' i' Z).
Proof. exact (MK_COMB (@lem1063368 A) (@lem1063367 A B c i r y Fn c' i' Z)). Qed.
Lemma lem1063370 (c : nat) (c' : nat) : (term611 c c') = (term611 c c').
Proof. exact (eq_refl (term611 c c')). Qed.
Lemma lem1063371 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term679 A B c i r y Fn c' i' Z) = (term689 A B c i r y Fn c' i' Z).
Proof. exact (MK_COMB (@lem1063370 c c') (@lem1063369 A B c i r y Fn c' i' Z)). Qed.
Lemma lem1063372 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : ((term678 A B c i r y Fn c' i' Z) = (term679 A B c i r y Fn c' i' Z)) = ((term675 A B c i r y Fn c' i' Z) = (term689 A B c i r y Fn c' i' Z)).
Proof. exact (MK_COMB (@lem1063365 A B c i r y Fn c' i' Z) (@lem1063371 A B c i r y Fn c' i' Z)). Qed.
Lemma lem1063373 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term675 A B c i r y Fn c' i' Z) = (term689 A B c i r y Fn c' i' Z).
Proof. exact (EQ_MP (@lem1063372 A B c i r y Fn c' i' Z) (@lem1063357 A B c i r y Fn c' i' Z)). Qed.
Lemma lem1063381 {A : Type'} (P : Prop) (Q : A -> Prop) : (term10 A P Q) = (term11 A P Q).
Proof. exact (EQ_MP (@lem1061576 A P Q) (@lem1061575 A P Q)). Qed.
Lemma lem1063382 {A : Type'} (P : Prop) (Q : type963 A) : (term676 A P Q) = (term677 A P Q).
Proof. exact (@lem1063381 (type1614 A) P Q). Qed.
Lemma lem1063383 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term690 A B c i r y Fn c' i' Z) = (term691 A B c i r y Fn c' i' Z).
Proof. exact (@lem1063382 A (i = i') (term692 A B c i r y Fn c' i' Z)). Qed.
Lemma lem1063384 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term693 A B c i r y Fn c' i' Z r') = (term671 A B c i r y Fn c' i' Z r').
Proof. exact (eq_refl (term693 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1063385 {A : Type'} (i : A) (i' : A) : (term650 A i i') = (term650 A i i').
Proof. exact (eq_refl (term650 A i i')). Qed.
Lemma lem1063386 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term694 A B c i r y Fn c' i' Z r') = (term672 A B c i r y Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1063385 A i i') (@lem1063384 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1063387 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term695 A B c i r y Fn c' i' Z) = (term680 A B c i r y Fn c' i' Z).
Proof. exact (fun_ext (fun r' : type1614 A => @lem1063386 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1063388 {A : Type'} : (@ex (nat -> recspace A)) = (@ex (nat -> recspace A)).
Proof. exact (eq_refl (@ex (nat -> recspace A))). Qed.
Lemma lem1063389 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term690 A B c i r y Fn c' i' Z) = (term688 A B c i r y Fn c' i' Z).
Proof. exact (MK_COMB (@lem1063388 A) (@lem1063387 A B c i r y Fn c' i' Z)). Qed.
Lemma lem1063390 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1063391 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term696 A B c i r y Fn c' i' Z) = (term697 A B c i r y Fn c' i' Z).
Proof. exact (MK_COMB (@lem1063390) (@lem1063389 A B c i r y Fn c' i' Z)). Qed.
Lemma lem1063392 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term693 A B c i r y Fn c' i' Z r') = (term671 A B c i r y Fn c' i' Z r').
Proof. exact (eq_refl (term693 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1063393 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term698 A B c i r y Fn c' i' Z) = (term692 A B c i r y Fn c' i' Z).
Proof. exact (fun_ext (fun r' : type1614 A => @lem1063392 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1063394 {A : Type'} : (@ex (nat -> recspace A)) = (@ex (nat -> recspace A)).
Proof. exact (eq_refl (@ex (nat -> recspace A))). Qed.
Lemma lem1063395 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term699 A B c i r y Fn c' i' Z) = (term700 A B c i r y Fn c' i' Z).
Proof. exact (MK_COMB (@lem1063394 A) (@lem1063393 A B c i r y Fn c' i' Z)). Qed.
Lemma lem1063396 {A : Type'} (i : A) (i' : A) : (term650 A i i') = (term650 A i i').
Proof. exact (eq_refl (term650 A i i')). Qed.
Lemma lem1063397 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term691 A B c i r y Fn c' i' Z) = (term701 A B c i r y Fn c' i' Z).
Proof. exact (MK_COMB (@lem1063396 A i i') (@lem1063395 A B c i r y Fn c' i' Z)). Qed.
Lemma lem1063398 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : ((term690 A B c i r y Fn c' i' Z) = (term691 A B c i r y Fn c' i' Z)) = ((term688 A B c i r y Fn c' i' Z) = (term701 A B c i r y Fn c' i' Z)).
Proof. exact (MK_COMB (@lem1063391 A B c i r y Fn c' i' Z) (@lem1063397 A B c i r y Fn c' i' Z)). Qed.
Lemma lem1063399 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term688 A B c i r y Fn c' i' Z) = (term701 A B c i r y Fn c' i' Z).
Proof. exact (EQ_MP (@lem1063398 A B c i r y Fn c' i' Z) (@lem1063383 A B c i r y Fn c' i' Z)). Qed.
Lemma lem1063405 {A : Type'} (P : A -> Prop) (a : A) : (term15 A a P) = (P a).
Proof. exact (EQ_MP (@lem1061582 A P a) (@lem1061581 A P a)). Qed.
Lemma lem1063406 {A : Type'} (P : type963 A) (a : type1614 A) : (term702 A a P) = (P a).
Proof. exact (@lem1063405 (type1614 A) P a). Qed.
Lemma lem1063407 {A B : Type'} (c : nat) (i : A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r : type1614 A) : (term703 A B c i r y Fn c' i' Z) = (term704 A B c i y Fn c' i' Z r).
Proof. exact (@lem1063406 A (term705 A B c i r y Fn c' i' Z) r). Qed.
Lemma lem1063408 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term706 A B c i r y Fn c' i' Z r') = (term670 A B c i r y Fn c' i' Z r').
Proof. exact (eq_refl (term706 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1063409 {A : Type'} (r : type1614 A) (r' : type1614 A) : (term663 A r r') = (term663 A r r').
Proof. exact (eq_refl (term663 A r r')). Qed.
Lemma lem1063410 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term707 A B c i r y Fn c' i' Z r') = (term671 A B c i r y Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1063409 A r r') (@lem1063408 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1063411 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term708 A B c i r y Fn c' i' Z) = (term692 A B c i r y Fn c' i' Z).
Proof. exact (fun_ext (fun r' : type1614 A => @lem1063410 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1063412 {A : Type'} : (@ex (nat -> recspace A)) = (@ex (nat -> recspace A)).
Proof. exact (eq_refl (@ex (nat -> recspace A))). Qed.
Lemma lem1063413 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term703 A B c i r y Fn c' i' Z) = (term700 A B c i r y Fn c' i' Z).
Proof. exact (MK_COMB (@lem1063412 A) (@lem1063411 A B c i r y Fn c' i' Z)). Qed.
Lemma lem1063414 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1063415 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term709 A B c i r y Fn c' i' Z) = (term710 A B c i r y Fn c' i' Z).
Proof. exact (MK_COMB (@lem1063414) (@lem1063413 A B c i r y Fn c' i' Z)). Qed.
Lemma lem1063416 {A B : Type'} (c : nat) (i : A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r : type1614 A) : (term704 A B c i y Fn c' i' Z r) = (term711 A B c i y Fn c' i' Z r).
Proof. exact (eq_refl (term704 A B c i y Fn c' i' Z r)). Qed.
Lemma lem1063417 {A B : Type'} (c : nat) (i : A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r : type1614 A) : ((term703 A B c i r y Fn c' i' Z) = (term704 A B c i y Fn c' i' Z r)) = ((term700 A B c i r y Fn c' i' Z) = (term711 A B c i y Fn c' i' Z r)).
Proof. exact (MK_COMB (@lem1063415 A B c i r y Fn c' i' Z) (@lem1063416 A B c i y Fn c' i' Z r)). Qed.
Lemma lem1063418 {A B : Type'} (c : nat) (i : A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r : type1614 A) : (term700 A B c i r y Fn c' i' Z) = (term711 A B c i y Fn c' i' Z r).
Proof. exact (EQ_MP (@lem1063417 A B c i y Fn c' i' Z r) (@lem1063407 A B c i y Fn c' i' Z r)). Qed.
Lemma lem1063453 {A : Type'} (i : A) (i' : A) : (term650 A i i') = (term650 A i i').
Proof. exact (eq_refl (term650 A i i')). Qed.
Lemma lem1063454 {A B : Type'} (c : nat) (i : A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r : type1614 A) : (term701 A B c i r y Fn c' i' Z) = (term712 A B c i y Fn c' i' Z r).
Proof. exact (MK_COMB (@lem1063453 A i i') (@lem1063418 A B c i y Fn c' i' Z r)). Qed.
Lemma lem1063457 {A B : Type'} (c : nat) (i : A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r : type1614 A) : (term688 A B c i r y Fn c' i' Z) = (term712 A B c i y Fn c' i' Z r).
Proof. exact (TRANS (@lem1063399 A B c i r y Fn c' i' Z) (@lem1063454 A B c i y Fn c' i' Z r)). Qed.
Lemma lem1063458 (c : nat) (c' : nat) : (term611 c c') = (term611 c c').
Proof. exact (eq_refl (term611 c c')). Qed.
Lemma lem1063459 {A B : Type'} (c : nat) (i : A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r : type1614 A) : (term689 A B c i r y Fn c' i' Z) = (term713 A B c i y Fn c' i' Z r).
Proof. exact (MK_COMB (@lem1063458 c c') (@lem1063457 A B c i y Fn c' i' Z r)). Qed.
Lemma lem1063462 {A B : Type'} (c : nat) (i : A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r : type1614 A) : (term675 A B c i r y Fn c' i' Z) = (term713 A B c i y Fn c' i' Z r).
Proof. exact (TRANS (@lem1063373 A B c i r y Fn c' i' Z) (@lem1063459 A B c i y Fn c' i' Z r)). Qed.
Lemma lem1063463 {A B : Type'} (c : nat) (i : A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r : type1614 A) : (term620 A B c i r y Fn c' i' Z) = (term713 A B c i y Fn c' i' Z r).
Proof. exact (TRANS (@lem1063351 A B c i r y Fn c' i' Z) (@lem1063462 A B c i y Fn c' i' Z r)). Qed.
Lemma lem1063464 {A B : Type'} (c : nat) (i : A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) (r : type1614 A) : (term622 A B c i r y Fn c' Z) = (term714 A B c i y Fn c' Z r).
Proof. exact (fun_ext (fun i' : A => @lem1063463 A B c i y Fn c' i' Z r)). Qed.
Lemma lem1063465 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1063466 {A B : Type'} (c : nat) (i : A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) (r : type1614 A) : (term624 A B c i r y Fn c' Z) = (term715 A B c i y Fn c' Z r).
Proof. exact (MK_COMB (@lem1063465 A) (@lem1063464 A B c i y Fn c' Z r)). Qed.
Lemma lem1063470 {A : Type'} (P : Prop) (Q : A -> Prop) : (term10 A P Q) = (term11 A P Q).
Proof. exact (EQ_MP (@lem1061576 A P Q) (@lem1061575 A P Q)). Qed.
Lemma lem1063471 {A : Type'} (P : Prop) (Q : A -> Prop) : (term10 A P Q) = (term11 A P Q).
Proof. exact (@lem1063470 A P Q). Qed.
Lemma lem1063472 {A B : Type'} (c : nat) (i : A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) (r : type1614 A) : (term716 A B c i y Fn c' Z r) = (term717 A B c i y Fn c' Z r).
Proof. exact (@lem1063471 A (c = c') (term718 A B c i y Fn c' Z r)). Qed.
Lemma lem1063473 {A B : Type'} (c : nat) (i : A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r : type1614 A) : (term719 A B c i y Fn c' Z r i') = (term712 A B c i y Fn c' i' Z r).
Proof. exact (eq_refl (term719 A B c i y Fn c' Z r i')). Qed.
Lemma lem1063474 (c : nat) (c' : nat) : (term611 c c') = (term611 c c').
Proof. exact (eq_refl (term611 c c')). Qed.
Lemma lem1063475 {A B : Type'} (c : nat) (i : A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r : type1614 A) : (term720 A B c i y Fn c' Z r i') = (term713 A B c i y Fn c' i' Z r).
Proof. exact (MK_COMB (@lem1063474 c c') (@lem1063473 A B c i y Fn c' i' Z r)). Qed.
Lemma lem1063476 {A B : Type'} (c : nat) (i : A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) (r : type1614 A) : (term721 A B c i y Fn c' Z r) = (term714 A B c i y Fn c' Z r).
Proof. exact (fun_ext (fun i' : A => @lem1063475 A B c i y Fn c' i' Z r)). Qed.
Lemma lem1063477 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1063478 {A B : Type'} (c : nat) (i : A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) (r : type1614 A) : (term716 A B c i y Fn c' Z r) = (term715 A B c i y Fn c' Z r).
Proof. exact (MK_COMB (@lem1063477 A) (@lem1063476 A B c i y Fn c' Z r)). Qed.
Lemma lem1063479 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1063480 {A B : Type'} (c : nat) (i : A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) (r : type1614 A) : (term722 A B c i y Fn c' Z r) = (term723 A B c i y Fn c' Z r).
Proof. exact (MK_COMB (@lem1063479) (@lem1063478 A B c i y Fn c' Z r)). Qed.
Lemma lem1063481 {A B : Type'} (c : nat) (i : A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r : type1614 A) : (term719 A B c i y Fn c' Z r i') = (term712 A B c i y Fn c' i' Z r).
Proof. exact (eq_refl (term719 A B c i y Fn c' Z r i')). Qed.
Lemma lem1063482 {A B : Type'} (c : nat) (i : A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) (r : type1614 A) : (term724 A B c i y Fn c' Z r) = (term718 A B c i y Fn c' Z r).
Proof. exact (fun_ext (fun i' : A => @lem1063481 A B c i y Fn c' i' Z r)). Qed.
Lemma lem1063483 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1063484 {A B : Type'} (c : nat) (i : A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) (r : type1614 A) : (term725 A B c i y Fn c' Z r) = (term726 A B c i y Fn c' Z r).
Proof. exact (MK_COMB (@lem1063483 A) (@lem1063482 A B c i y Fn c' Z r)). Qed.
Lemma lem1063485 (c : nat) (c' : nat) : (term611 c c') = (term611 c c').
Proof. exact (eq_refl (term611 c c')). Qed.
Lemma lem1063486 {A B : Type'} (c : nat) (i : A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) (r : type1614 A) : (term717 A B c i y Fn c' Z r) = (term727 A B c i y Fn c' Z r).
Proof. exact (MK_COMB (@lem1063485 c c') (@lem1063484 A B c i y Fn c' Z r)). Qed.
Lemma lem1063487 {A B : Type'} (c : nat) (i : A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) (r : type1614 A) : ((term716 A B c i y Fn c' Z r) = (term717 A B c i y Fn c' Z r)) = ((term715 A B c i y Fn c' Z r) = (term727 A B c i y Fn c' Z r)).
Proof. exact (MK_COMB (@lem1063480 A B c i y Fn c' Z r) (@lem1063486 A B c i y Fn c' Z r)). Qed.
Lemma lem1063488 {A B : Type'} (c : nat) (i : A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) (r : type1614 A) : (term715 A B c i y Fn c' Z r) = (term727 A B c i y Fn c' Z r).
Proof. exact (EQ_MP (@lem1063487 A B c i y Fn c' Z r) (@lem1063472 A B c i y Fn c' Z r)). Qed.
Lemma lem1063494 {A : Type'} (P : A -> Prop) (a : A) : (term15 A a P) = (P a).
Proof. exact (EQ_MP (@lem1061582 A P a) (@lem1061581 A P a)). Qed.
Lemma lem1063495 {A : Type'} (P : A -> Prop) (a : A) : (term15 A a P) = (P a).
Proof. exact (@lem1063494 A P a). Qed.
Lemma lem1063496 {A B : Type'} (c : nat) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) (r : type1614 A) (i : A) : (term728 A B c i y Fn c' Z r) = (term729 A B c y Fn c' Z r i).
Proof. exact (@lem1063495 A (term730 A B c i y Fn c' Z r) i). Qed.
Lemma lem1063497 {A B : Type'} (c : nat) (i : A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r : type1614 A) : (term731 A B c i y Fn c' Z r i') = (term711 A B c i y Fn c' i' Z r).
Proof. exact (eq_refl (term731 A B c i y Fn c' Z r i')). Qed.
Lemma lem1063498 {A : Type'} (i : A) (i' : A) : (term650 A i i') = (term650 A i i').
Proof. exact (eq_refl (term650 A i i')). Qed.
Lemma lem1063499 {A B : Type'} (c : nat) (i : A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r : type1614 A) : (term732 A B c i y Fn c' Z r i') = (term712 A B c i y Fn c' i' Z r).
Proof. exact (MK_COMB (@lem1063498 A i i') (@lem1063497 A B c i y Fn c' i' Z r)). Qed.
Lemma lem1063500 {A B : Type'} (c : nat) (i : A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) (r : type1614 A) : (term733 A B c i y Fn c' Z r) = (term718 A B c i y Fn c' Z r).
Proof. exact (fun_ext (fun i' : A => @lem1063499 A B c i y Fn c' i' Z r)). Qed.
Lemma lem1063501 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1063502 {A B : Type'} (c : nat) (i : A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) (r : type1614 A) : (term728 A B c i y Fn c' Z r) = (term726 A B c i y Fn c' Z r).
Proof. exact (MK_COMB (@lem1063501 A) (@lem1063500 A B c i y Fn c' Z r)). Qed.
Lemma lem1063503 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1063504 {A B : Type'} (c : nat) (i : A) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) (r : type1614 A) : (term734 A B c i y Fn c' Z r) = (term735 A B c i y Fn c' Z r).
Proof. exact (MK_COMB (@lem1063503) (@lem1063502 A B c i y Fn c' Z r)). Qed.
Lemma lem1063505 {A B : Type'} (c : nat) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : (term729 A B c y Fn c' Z r i) = (term736 A B c y Fn c' i Z r).
Proof. exact (eq_refl (term729 A B c y Fn c' Z r i)). Qed.
Lemma lem1063506 {A B : Type'} (c : nat) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : ((term728 A B c i y Fn c' Z r) = (term729 A B c y Fn c' Z r i)) = ((term726 A B c i y Fn c' Z r) = (term736 A B c y Fn c' i Z r)).
Proof. exact (MK_COMB (@lem1063504 A B c i y Fn c' Z r) (@lem1063505 A B c y Fn c' i Z r)). Qed.
Lemma lem1063507 {A B : Type'} (c : nat) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : (term726 A B c i y Fn c' Z r) = (term736 A B c y Fn c' i Z r).
Proof. exact (EQ_MP (@lem1063506 A B c y Fn c' i Z r) (@lem1063496 A B c y Fn c' Z r i)). Qed.
Lemma lem1063542 (c : nat) (c' : nat) : (term611 c c') = (term611 c c').
Proof. exact (eq_refl (term611 c c')). Qed.
Lemma lem1063543 {A B : Type'} (c : nat) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : (term727 A B c i y Fn c' Z r) = (term737 A B c y Fn c' i Z r).
Proof. exact (MK_COMB (@lem1063542 c c') (@lem1063507 A B c y Fn c' i Z r)). Qed.
Lemma lem1063546 {A B : Type'} (c : nat) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : (term715 A B c i y Fn c' Z r) = (term737 A B c y Fn c' i Z r).
Proof. exact (TRANS (@lem1063488 A B c i y Fn c' Z r) (@lem1063543 A B c y Fn c' i Z r)). Qed.
Lemma lem1063547 {A B : Type'} (c : nat) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : (term624 A B c i r y Fn c' Z) = (term737 A B c y Fn c' i Z r).
Proof. exact (TRANS (@lem1063466 A B c i y Fn c' Z r) (@lem1063546 A B c y Fn c' i Z r)). Qed.
Lemma lem1063548 {A B : Type'} (c : nat) (y : nat -> B) (Fn : type1592 A B) (i : A) (Z : type1336 A B) (r : type1614 A) : (term626 A B c i r y Fn Z) = (term738 A B c y Fn i Z r).
Proof. exact (fun_ext (fun c' : nat => @lem1063547 A B c y Fn c' i Z r)). Qed.
Lemma lem1063549 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1063550 {A B : Type'} (c : nat) (y : nat -> B) (Fn : type1592 A B) (i : A) (Z : type1336 A B) (r : type1614 A) : (term628 A B c i r y Fn Z) = (term739 A B c y Fn i Z r).
Proof. exact (MK_COMB (@lem1063549) (@lem1063548 A B c y Fn i Z r)). Qed.
Lemma lem1063552 {A : Type'} (P : A -> Prop) (a : A) : (term15 A a P) = (P a).
Proof. exact (EQ_MP (@lem1061582 A P a) (@lem1061581 A P a)). Qed.
Lemma lem1063553 (P : nat -> Prop) (a : nat) : (term740 a P) = (P a).
Proof. exact (@lem1063552 nat P a). Qed.
Lemma lem1063554 {A B : Type'} (y : nat -> B) (Fn : type1592 A B) (i : A) (Z : type1336 A B) (r : type1614 A) (c : nat) : (term741 A B c y Fn i Z r) = (term742 A B y Fn i Z r c).
Proof. exact (@lem1063553 (term743 A B c y Fn i Z r) c). Qed.
Lemma lem1063555 {A B : Type'} (c : nat) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : (term744 A B c y Fn i Z r c') = (term736 A B c y Fn c' i Z r).
Proof. exact (eq_refl (term744 A B c y Fn i Z r c')). Qed.
Lemma lem1063556 (c : nat) (c' : nat) : (term611 c c') = (term611 c c').
Proof. exact (eq_refl (term611 c c')). Qed.
Lemma lem1063557 {A B : Type'} (c : nat) (y : nat -> B) (Fn : type1592 A B) (c' : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : (term745 A B c y Fn i Z r c') = (term737 A B c y Fn c' i Z r).
Proof. exact (MK_COMB (@lem1063556 c c') (@lem1063555 A B c y Fn c' i Z r)). Qed.
Lemma lem1063558 {A B : Type'} (c : nat) (y : nat -> B) (Fn : type1592 A B) (i : A) (Z : type1336 A B) (r : type1614 A) : (term746 A B c y Fn i Z r) = (term738 A B c y Fn i Z r).
Proof. exact (fun_ext (fun c' : nat => @lem1063557 A B c y Fn c' i Z r)). Qed.
Lemma lem1063559 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1063560 {A B : Type'} (c : nat) (y : nat -> B) (Fn : type1592 A B) (i : A) (Z : type1336 A B) (r : type1614 A) : (term741 A B c y Fn i Z r) = (term739 A B c y Fn i Z r).
Proof. exact (MK_COMB (@lem1063559) (@lem1063558 A B c y Fn i Z r)). Qed.
Lemma lem1063561 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1063562 {A B : Type'} (c : nat) (y : nat -> B) (Fn : type1592 A B) (i : A) (Z : type1336 A B) (r : type1614 A) : (term747 A B c y Fn i Z r) = (term748 A B c y Fn i Z r).
Proof. exact (MK_COMB (@lem1063561) (@lem1063560 A B c y Fn i Z r)). Qed.
Lemma lem1063563 {A B : Type'} (y : nat -> B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : (term742 A B y Fn i Z r c) = (term749 A B y Fn c i Z r).
Proof. exact (eq_refl (term742 A B y Fn i Z r c)). Qed.
Lemma lem1063564 {A B : Type'} (y : nat -> B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : ((term741 A B c y Fn i Z r) = (term742 A B y Fn i Z r c)) = ((term739 A B c y Fn i Z r) = (term749 A B y Fn c i Z r)).
Proof. exact (MK_COMB (@lem1063562 A B c y Fn i Z r) (@lem1063563 A B y Fn c i Z r)). Qed.
Lemma lem1063565 {A B : Type'} (y : nat -> B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : (term739 A B c y Fn i Z r) = (term749 A B y Fn c i Z r).
Proof. exact (EQ_MP (@lem1063564 A B y Fn c i Z r) (@lem1063554 A B y Fn i Z r c)). Qed.
Lemma lem1063600 {A B : Type'} (y : nat -> B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : (term628 A B c i r y Fn Z) = (term749 A B y Fn c i Z r).
Proof. exact (TRANS (@lem1063550 A B c y Fn i Z r) (@lem1063565 A B y Fn c i Z r)). Qed.
Lemma lem1063601 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Fn : type1592 A B) (Z : type1336 A B) : (term749 A B y Fn c i Z r) = (term628 A B c i r y Fn Z).
Proof. exact (SYM (@lem1063600 A B y Fn c i Z r)). Qed.
Lemma lem1063640 {A B : Type'} (n : nat) (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (h1 : term101 A B Z r y) : term357 A B Z r y n.
Proof. exact (@lem1062834 A B Z r y h1 n). Qed.
Lemma lem1063641 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (n : nat) : (term357 A B Z r y n) = (term358 A B Z r y n).
Proof. exact (eq_refl (term357 A B Z r y n)). Qed.
Lemma lem1063642 {A B : Type'} (n : nat) (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (h1 : term101 A B Z r y) : term358 A B Z r y n.
Proof. exact (EQ_MP (@lem1063641 A B Z r y n) (@lem1063640 A B n Z r y h1)). Qed.
Lemma lem1063643 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (n : nat) : (term358 A B Z r y n) = ((term358 A B Z r y n) = True).
Proof. exact (@lem7 (term358 A B Z r y n)). Qed.
Lemma lem1063648 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1063649 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem1063648 B x). Qed.
Lemma lem1063650 {A B : Type'} (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (y : nat -> B) : ((Fn c i r y) = (Fn c i r y)) = True.
Proof. exact (@lem1063649 B (Fn c i r y)). Qed.
Lemma lem1063651 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1063652 {A B : Type'} (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (y : nat -> B) : (term750 A B Fn c i r y) = (and True).
Proof. exact (MK_COMB (@lem1063651) (@lem1063650 A B Fn c i r y)). Qed.
Lemma lem1063658 {A B : Type'} (n : nat) (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (h1 : term101 A B Z r y) : (term358 A B Z r y n) = True.
Proof. exact (EQ_MP (@lem1063643 A B Z r y n) (@lem1063642 A B n Z r y h1)). Qed.
Lemma lem1063659 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (h1 : term101 A B Z r y) : (term356 A B Z r y) = term378.
Proof. exact (fun_ext (fun n : nat => @lem1063658 A B n Z r y h1)). Qed.
Lemma lem1063660 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1063661 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (h1 : term101 A B Z r y) : (term101 A B Z r y) = term379.
Proof. exact (MK_COMB (@lem1063660) (@lem1063659 A B Z r y h1)). Qed.
Lemma lem1063663 {A : Type'} (t : Prop) : (term380 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1063664 (t : Prop) : (term381 t) = t.
Proof. exact (@lem1063663 nat t). Qed.
Lemma lem1063665 : term379 = True.
Proof. exact (@lem1063664 True). Qed.
Lemma lem1063666 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (h1 : term101 A B Z r y) : (term101 A B Z r y) = True.
Proof. exact (TRANS (@lem1063661 A B Z r y h1) (@lem1063665)). Qed.
Lemma lem1063667 {A B : Type'} (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (h1 : term101 A B Z r y) : (term132 A B Fn c i Z r y) = (True /\ True).
Proof. exact (MK_COMB (@lem1063652 A B Fn c i r y) (@lem1063666 A B Z r y h1)). Qed.
Lemma lem1063669 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1063670 : (True /\ True) = True.
Proof. exact (@lem1063669 True). Qed.
Lemma lem1063671 {A B : Type'} (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (h1 : term101 A B Z r y) : (term132 A B Fn c i Z r y) = True.
Proof. exact (TRANS (@lem1063667 A B Fn c i Z r y h1) (@lem1063670)). Qed.
Lemma lem1063672 {A B : Type'} (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (h1 : term101 A B Z r y) : True = (term132 A B Fn c i Z r y).
Proof. exact (SYM (@lem1063671 A B Fn c i Z r y h1)). Qed.
Lemma lem1063673 {A B : Type'} (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (h1 : term101 A B Z r y) : term132 A B Fn c i Z r y.
Proof. exact (EQ_MP (@lem1063672 A B Fn c i Z r y h1) (@lem0)). Qed.
Lemma lem1063674 {A B : Type'} (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (h1 : term101 A B Z r y) : term749 A B y Fn c i Z r.
Proof. exact (ex_intro (term751 A B y Fn c i Z r) y (@lem1063673 A B Fn c i Z r y h1)). Qed.
Lemma lem1063675 {A B : Type'} (c : nat) (i : A) (Fn : type1592 A B) (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (h1 : term101 A B Z r y) : term628 A B c i r y Fn Z.
Proof. exact (EQ_MP (@lem1063601 A B c i r y Fn Z) (@lem1063674 A B Fn c i Z r y h1)). Qed.
Lemma lem1063676 {A B : Type'} (b : B) (c : nat) (i : A) (Fn : type1592 A B) (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (h1 : term101 A B Z r y) : term629 A B b c i r y Fn Z.
Proof. exact (EQ_MP (@lem1063214 A B b c i r y Fn Z) (@lem1063675 A B c i Fn Z r y h1)). Qed.
Lemma lem1063677 {A B : Type'} (b : B) (c : nat) (i : A) (Fn : type1592 A B) (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (h1 : term101 A B Z r y) : term587 A B b c i r Fn Z.
Proof. exact (ex_intro (term586 A B b c i r Fn Z) (Fn c i r y) (@lem1063676 A B b c i Fn Z r y h1)). Qed.
Lemma lem1063695 {A : Type'} (c : nat) (i : A) (r : type1614 A) : ((@CONSTR A c i r) = (@BOTTOM A)) = False.
Proof. exact (@lem1061559 A c i r (@lem1061558 A c i r)). Qed.
Lemma lem1063696 {A : Type'} (c : nat) (i : A) (r : type1614 A) : ((@CONSTR A c i r) = (@BOTTOM A)) = False.
Proof. exact (@lem1063695 A c i r). Qed.
Lemma lem1063697 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1063698 {A : Type'} (c : nat) (i : A) (r : type1614 A) : (term598 A c i r) = (and False).
Proof. exact (MK_COMB (@lem1063697) (@lem1063696 A c i r)). Qed.
Lemma lem1063701 {B : Type'} (y : B) (b : B) : (y = b) = (y = b).
Proof. exact (eq_refl (y = b)). Qed.
Lemma lem1063702 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : B) (b : B) : (term752 A B c i r y b) = (term753 B y b).
Proof. exact (MK_COMB (@lem1063698 A c i r) (@lem1063701 B y b)). Qed.
Lemma lem1063704 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1063705 {B : Type'} (y : B) (b : B) : (term753 B y b) = False.
Proof. exact (@lem1063704 (y = b)). Qed.
Lemma lem1063706 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : B) (b : B) : (term752 A B c i r y b) = False.
Proof. exact (TRANS (@lem1063702 A B c i r y b) (@lem1063705 B y b)). Qed.
Lemma lem1063707 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1063708 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : B) (b : B) : (term754 A B c i r y b) = (or False).
Proof. exact (MK_COMB (@lem1063707) (@lem1063706 A B c i r y b)). Qed.
Lemma lem1063728 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : ((@CONSTR A c1 i1 r1) = (@CONSTR A c2 i2 r2)) = (term44 A c1 c2 i1 i2 r1 r2).
Proof. exact (EQ_MP (@lem1061548 A c1 c2 i1 i2 r1 r2) (@lem1061547 A c1 c2 i1 i2 r1 r2)). Qed.
Lemma lem1063729 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : ((@CONSTR A c1 i1 r1) = (@CONSTR A c2 i2 r2)) = (term44 A c1 c2 i1 i2 r1 r2).
Proof. exact (@lem1063728 A c1 c2 i1 i2 r1 r2). Qed.
Lemma lem1063730 {A : Type'} (c : nat) (c' : nat) (i : A) (i' : A) (r : type1614 A) (r' : type1614 A) : ((@CONSTR A c i r) = (@CONSTR A c' i' r')) = (term44 A c c' i i' r r').
Proof. exact (@lem1063729 A c c' i i' r r'). Qed.
Lemma lem1063741 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1063742 {A : Type'} (c : nat) (c' : nat) (i : A) (i' : A) (r : type1614 A) (r' : type1614 A) : (term602 A c i r c' i' r') = (term603 A c c' i i' r r').
Proof. exact (MK_COMB (@lem1063741) (@lem1063730 A c c' i i' r r')). Qed.
Lemma lem1063751 {A B : Type'} (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y' : nat -> B) : (term100 A B y Fn c' i' Z r' y') = (term100 A B y Fn c' i' Z r' y').
Proof. exact (eq_refl (term100 A B y Fn c' i' Z r' y')). Qed.
Lemma lem1063752 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y' : nat -> B) : (term755 A B c i r y Fn c' i' Z r' y') = (term756 A B c i r y Fn c' i' Z r' y').
Proof. exact (MK_COMB (@lem1063742 A c c' i i' r r') (@lem1063751 A B y Fn c' i' Z r' y')). Qed.
Lemma lem1063754 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term17 t1 t2 t3) = (term16 t1 t2 t3).
Proof. exact (EQ_MP (@lem1061530 t1 t2 t3) (@lem1061529 t1 t2 t3)). Qed.
Lemma lem1063755 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y' : nat -> B) : (term756 A B c i r y Fn c' i' Z r' y') = (term757 A B c i r y Fn c' i' Z r' y').
Proof. exact (@lem1063754 (c = c') (term608 A i i' r r') (term100 A B y Fn c' i' Z r' y')). Qed.
Lemma lem1063761 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term17 t1 t2 t3) = (term16 t1 t2 t3).
Proof. exact (EQ_MP (@lem1061530 t1 t2 t3) (@lem1061529 t1 t2 t3)). Qed.
Lemma lem1063762 {A B : Type'} (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y' : nat -> B) : (term758 A B i r y Fn c' i' Z r' y') = (term759 A B i r y Fn c' i' Z r' y').
Proof. exact (@lem1063761 (i = i') (r = r') (term100 A B y Fn c' i' Z r' y')). Qed.
Lemma lem1063779 (c : nat) (c' : nat) : (term611 c c') = (term611 c c').
Proof. exact (eq_refl (term611 c c')). Qed.
Lemma lem1063780 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y' : nat -> B) : (term757 A B c i r y Fn c' i' Z r' y') = (term760 A B c i r y Fn c' i' Z r' y').
Proof. exact (MK_COMB (@lem1063779 c c') (@lem1063762 A B i r y Fn c' i' Z r' y')). Qed.
Lemma lem1063783 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y' : nat -> B) : (term756 A B c i r y Fn c' i' Z r' y') = (term760 A B c i r y Fn c' i' Z r' y').
Proof. exact (TRANS (@lem1063755 A B c i r y Fn c' i' Z r' y') (@lem1063780 A B c i r y Fn c' i' Z r' y')). Qed.
Lemma lem1063784 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y' : nat -> B) : (term755 A B c i r y Fn c' i' Z r' y') = (term760 A B c i r y Fn c' i' Z r' y').
Proof. exact (TRANS (@lem1063752 A B c i r y Fn c' i' Z r' y') (@lem1063783 A B c i r y Fn c' i' Z r' y')). Qed.
Lemma lem1063785 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term761 A B c i r y Fn c' i' Z r') = (term762 A B c i r y Fn c' i' Z r').
Proof. exact (fun_ext (fun y' : nat -> B => @lem1063784 A B c i r y Fn c' i' Z r' y')). Qed.
Lemma lem1063786 {B : Type'} : (@ex (nat -> B)) = (@ex (nat -> B)).
Proof. exact (eq_refl (@ex (nat -> B))). Qed.
Lemma lem1063787 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term763 A B c i r y Fn c' i' Z r') = (term764 A B c i r y Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1063786 B) (@lem1063785 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1063792 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term765 A B c i r y Fn c' i' Z) = (term766 A B c i r y Fn c' i' Z).
Proof. exact (fun_ext (fun r' : type1614 A => @lem1063787 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1063793 {A : Type'} : (@ex (nat -> recspace A)) = (@ex (nat -> recspace A)).
Proof. exact (eq_refl (@ex (nat -> recspace A))). Qed.
Lemma lem1063794 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term767 A B c i r y Fn c' i' Z) = (term768 A B c i r y Fn c' i' Z).
Proof. exact (MK_COMB (@lem1063793 A) (@lem1063792 A B c i r y Fn c' i' Z)). Qed.
Lemma lem1063799 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) : (term769 A B c i r y Fn c' Z) = (term770 A B c i r y Fn c' Z).
Proof. exact (fun_ext (fun i' : A => @lem1063794 A B c i r y Fn c' i' Z)). Qed.
Lemma lem1063800 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1063801 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) : (term771 A B c i r y Fn c' Z) = (term772 A B c i r y Fn c' Z).
Proof. exact (MK_COMB (@lem1063800 A) (@lem1063799 A B c i r y Fn c' Z)). Qed.
Lemma lem1063806 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (Z : type1336 A B) : (term773 A B c i r y Fn Z) = (term774 A B c i r y Fn Z).
Proof. exact (fun_ext (fun c' : nat => @lem1063801 A B c i r y Fn c' Z)). Qed.
Lemma lem1063807 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1063808 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (Z : type1336 A B) : (term775 A B c i r y Fn Z) = (term776 A B c i r y Fn Z).
Proof. exact (MK_COMB (@lem1063807) (@lem1063806 A B c i r y Fn Z)). Qed.
Lemma lem1063813 {A B : Type'} (b : B) (c : nat) (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (Z : type1336 A B) : (term585 A B b c i r y Fn Z) = (term777 A B c i r y Fn Z).
Proof. exact (MK_COMB (@lem1063708 A B c i r y b) (@lem1063808 A B c i r y Fn Z)). Qed.
Lemma lem1063815 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem1063816 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (Z : type1336 A B) : (term777 A B c i r y Fn Z) = (term776 A B c i r y Fn Z).
Proof. exact (@lem1063815 (term776 A B c i r y Fn Z)). Qed.
Lemma lem1063853 {A B : Type'} (b : B) (c : nat) (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (Z : type1336 A B) : (term585 A B b c i r y Fn Z) = (term776 A B c i r y Fn Z).
Proof. exact (TRANS (@lem1063813 A B b c i r y Fn Z) (@lem1063816 A B c i r y Fn Z)). Qed.
Lemma lem1063854 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1063855 {A B : Type'} (b : B) (c : nat) (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (Z : type1336 A B) : (term589 A B b c i r y Fn Z) = (term778 A B c i r y Fn Z).
Proof. exact (MK_COMB (@lem1063854) (@lem1063853 A B b c i r y Fn Z)). Qed.
Lemma lem1063861 {A : Type'} (c : nat) (i : A) (r : type1614 A) : ((@CONSTR A c i r) = (@BOTTOM A)) = False.
Proof. exact (@lem1061559 A c i r (@lem1061558 A c i r)). Qed.
Lemma lem1063862 {A : Type'} (c : nat) (i : A) (r : type1614 A) : ((@CONSTR A c i r) = (@BOTTOM A)) = False.
Proof. exact (@lem1063861 A c i r). Qed.
Lemma lem1063863 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1063864 {A : Type'} (c : nat) (i : A) (r : type1614 A) : (term598 A c i r) = (and False).
Proof. exact (MK_COMB (@lem1063863) (@lem1063862 A c i r)). Qed.
Lemma lem1063867 {B : Type'} (x' : B) (b : B) : (x' = b) = (x' = b).
Proof. exact (eq_refl (x' = b)). Qed.
Lemma lem1063868 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (x' : B) (b : B) : (term752 A B c i r x' b) = (term753 B x' b).
Proof. exact (MK_COMB (@lem1063864 A c i r) (@lem1063867 B x' b)). Qed.
Lemma lem1063870 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1063871 {B : Type'} (x' : B) (b : B) : (term753 B x' b) = False.
Proof. exact (@lem1063870 (x' = b)). Qed.
Lemma lem1063872 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (x' : B) (b : B) : (term752 A B c i r x' b) = False.
Proof. exact (TRANS (@lem1063868 A B c i r x' b) (@lem1063871 B x' b)). Qed.
Lemma lem1063873 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1063874 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (x' : B) (b : B) : (term754 A B c i r x' b) = (or False).
Proof. exact (MK_COMB (@lem1063873) (@lem1063872 A B c i r x' b)). Qed.
Lemma lem1063894 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : ((@CONSTR A c1 i1 r1) = (@CONSTR A c2 i2 r2)) = (term44 A c1 c2 i1 i2 r1 r2).
Proof. exact (EQ_MP (@lem1061548 A c1 c2 i1 i2 r1 r2) (@lem1061547 A c1 c2 i1 i2 r1 r2)). Qed.
Lemma lem1063895 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : ((@CONSTR A c1 i1 r1) = (@CONSTR A c2 i2 r2)) = (term44 A c1 c2 i1 i2 r1 r2).
Proof. exact (@lem1063894 A c1 c2 i1 i2 r1 r2). Qed.
Lemma lem1063896 {A : Type'} (c : nat) (c' : nat) (i : A) (i' : A) (r : type1614 A) (r' : type1614 A) : ((@CONSTR A c i r) = (@CONSTR A c' i' r')) = (term44 A c c' i i' r r').
Proof. exact (@lem1063895 A c c' i i' r r'). Qed.
Lemma lem1063907 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1063908 {A : Type'} (c : nat) (c' : nat) (i : A) (i' : A) (r : type1614 A) (r' : type1614 A) : (term602 A c i r c' i' r') = (term603 A c c' i i' r r').
Proof. exact (MK_COMB (@lem1063907) (@lem1063896 A c c' i i' r r')). Qed.
Lemma lem1063917 {A B : Type'} (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y : nat -> B) : (term100 A B x' Fn c' i' Z r' y) = (term100 A B x' Fn c' i' Z r' y).
Proof. exact (eq_refl (term100 A B x' Fn c' i' Z r' y)). Qed.
Lemma lem1063918 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y : nat -> B) : (term755 A B c i r x' Fn c' i' Z r' y) = (term756 A B c i r x' Fn c' i' Z r' y).
Proof. exact (MK_COMB (@lem1063908 A c c' i i' r r') (@lem1063917 A B x' Fn c' i' Z r' y)). Qed.
Lemma lem1063920 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term17 t1 t2 t3) = (term16 t1 t2 t3).
Proof. exact (EQ_MP (@lem1061530 t1 t2 t3) (@lem1061529 t1 t2 t3)). Qed.
Lemma lem1063921 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y : nat -> B) : (term756 A B c i r x' Fn c' i' Z r' y) = (term757 A B c i r x' Fn c' i' Z r' y).
Proof. exact (@lem1063920 (c = c') (term608 A i i' r r') (term100 A B x' Fn c' i' Z r' y)). Qed.
Lemma lem1063927 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term17 t1 t2 t3) = (term16 t1 t2 t3).
Proof. exact (EQ_MP (@lem1061530 t1 t2 t3) (@lem1061529 t1 t2 t3)). Qed.
Lemma lem1063928 {A B : Type'} (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y : nat -> B) : (term758 A B i r x' Fn c' i' Z r' y) = (term759 A B i r x' Fn c' i' Z r' y).
Proof. exact (@lem1063927 (i = i') (r = r') (term100 A B x' Fn c' i' Z r' y)). Qed.
Lemma lem1063945 (c : nat) (c' : nat) : (term611 c c') = (term611 c c').
Proof. exact (eq_refl (term611 c c')). Qed.
Lemma lem1063946 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y : nat -> B) : (term757 A B c i r x' Fn c' i' Z r' y) = (term760 A B c i r x' Fn c' i' Z r' y).
Proof. exact (MK_COMB (@lem1063945 c c') (@lem1063928 A B i r x' Fn c' i' Z r' y)). Qed.
Lemma lem1063949 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y : nat -> B) : (term756 A B c i r x' Fn c' i' Z r' y) = (term760 A B c i r x' Fn c' i' Z r' y).
Proof. exact (TRANS (@lem1063921 A B c i r x' Fn c' i' Z r' y) (@lem1063946 A B c i r x' Fn c' i' Z r' y)). Qed.
Lemma lem1063950 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y : nat -> B) : (term755 A B c i r x' Fn c' i' Z r' y) = (term760 A B c i r x' Fn c' i' Z r' y).
Proof. exact (TRANS (@lem1063918 A B c i r x' Fn c' i' Z r' y) (@lem1063949 A B c i r x' Fn c' i' Z r' y)). Qed.
Lemma lem1063951 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term761 A B c i r x' Fn c' i' Z r') = (term762 A B c i r x' Fn c' i' Z r').
Proof. exact (fun_ext (fun y : nat -> B => @lem1063950 A B c i r x' Fn c' i' Z r' y)). Qed.
Lemma lem1063952 {B : Type'} : (@ex (nat -> B)) = (@ex (nat -> B)).
Proof. exact (eq_refl (@ex (nat -> B))). Qed.
Lemma lem1063953 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term763 A B c i r x' Fn c' i' Z r') = (term764 A B c i r x' Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1063952 B) (@lem1063951 A B c i r x' Fn c' i' Z r')). Qed.
Lemma lem1063958 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term765 A B c i r x' Fn c' i' Z) = (term766 A B c i r x' Fn c' i' Z).
Proof. exact (fun_ext (fun r' : type1614 A => @lem1063953 A B c i r x' Fn c' i' Z r')). Qed.
Lemma lem1063959 {A : Type'} : (@ex (nat -> recspace A)) = (@ex (nat -> recspace A)).
Proof. exact (eq_refl (@ex (nat -> recspace A))). Qed.
Lemma lem1063960 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term767 A B c i r x' Fn c' i' Z) = (term768 A B c i r x' Fn c' i' Z).
Proof. exact (MK_COMB (@lem1063959 A) (@lem1063958 A B c i r x' Fn c' i' Z)). Qed.
Lemma lem1063965 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) : (term769 A B c i r x' Fn c' Z) = (term770 A B c i r x' Fn c' Z).
Proof. exact (fun_ext (fun i' : A => @lem1063960 A B c i r x' Fn c' i' Z)). Qed.
Lemma lem1063966 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1063967 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) : (term771 A B c i r x' Fn c' Z) = (term772 A B c i r x' Fn c' Z).
Proof. exact (MK_COMB (@lem1063966 A) (@lem1063965 A B c i r x' Fn c' Z)). Qed.
Lemma lem1063972 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (Z : type1336 A B) : (term773 A B c i r x' Fn Z) = (term774 A B c i r x' Fn Z).
Proof. exact (fun_ext (fun c' : nat => @lem1063967 A B c i r x' Fn c' Z)). Qed.
Lemma lem1063973 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1063974 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (Z : type1336 A B) : (term775 A B c i r x' Fn Z) = (term776 A B c i r x' Fn Z).
Proof. exact (MK_COMB (@lem1063973) (@lem1063972 A B c i r x' Fn Z)). Qed.
Lemma lem1063979 {A B : Type'} (b : B) (c : nat) (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (Z : type1336 A B) : (term585 A B b c i r x' Fn Z) = (term777 A B c i r x' Fn Z).
Proof. exact (MK_COMB (@lem1063874 A B c i r x' b) (@lem1063974 A B c i r x' Fn Z)). Qed.
Lemma lem1063981 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem1063982 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (Z : type1336 A B) : (term777 A B c i r x' Fn Z) = (term776 A B c i r x' Fn Z).
Proof. exact (@lem1063981 (term776 A B c i r x' Fn Z)). Qed.
Lemma lem1064019 {A B : Type'} (b : B) (c : nat) (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (Z : type1336 A B) : (term585 A B b c i r x' Fn Z) = (term776 A B c i r x' Fn Z).
Proof. exact (TRANS (@lem1063979 A B b c i r x' Fn Z) (@lem1063982 A B c i r x' Fn Z)). Qed.
Lemma lem1064020 {A B : Type'} (b : B) (y : B) (c : nat) (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (Z : type1336 A B) : (term590 A B y b c i r x' Fn Z) = (term779 A B y c i r x' Fn Z).
Proof. exact (MK_COMB (@lem1063855 A B b c i r y Fn Z) (@lem1064019 A B b c i r x' Fn Z)). Qed.
Lemma lem1064023 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1064024 {A B : Type'} (b : B) (y : B) (c : nat) (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (Z : type1336 A B) : (term591 A B y b c i r x' Fn Z) = (term780 A B y c i r x' Fn Z).
Proof. exact (MK_COMB (@lem1064023) (@lem1064020 A B b y c i r x' Fn Z)). Qed.
Lemma lem1064027 {B : Type'} (y : B) (x' : B) : (y = x') = (y = x').
Proof. exact (eq_refl (y = x')). Qed.
Lemma lem1064028 {A B : Type'} (b : B) (c : nat) (i : A) (r : type1614 A) (Fn : type1592 A B) (Z : type1336 A B) (y : B) (x' : B) : (term592 A B b c i r Fn Z y x') = (term781 A B c i r Fn Z y x').
Proof. exact (MK_COMB (@lem1064024 A B b y c i r x' Fn Z) (@lem1064027 B y x')). Qed.
Lemma lem1064031 {A B : Type'} (b : B) (c : nat) (i : A) (r : type1614 A) (Fn : type1592 A B) (Z : type1336 A B) (y : B) : (term593 A B b c i r Fn Z y) = (term782 A B c i r Fn Z y).
Proof. exact (fun_ext (fun x' : B => @lem1064028 A B b c i r Fn Z y x')). Qed.
Lemma lem1064032 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1064033 {A B : Type'} (b : B) (c : nat) (i : A) (r : type1614 A) (Fn : type1592 A B) (Z : type1336 A B) (y : B) : (term594 A B b c i r Fn Z y) = (term783 A B c i r Fn Z y).
Proof. exact (MK_COMB (@lem1064032 B) (@lem1064031 A B b c i r Fn Z y)). Qed.
Lemma lem1064038 {A B : Type'} (b : B) (c : nat) (i : A) (r : type1614 A) (Fn : type1592 A B) (Z : type1336 A B) : (term595 A B b c i r Fn Z) = (term784 A B c i r Fn Z).
Proof. exact (fun_ext (fun y : B => @lem1064033 A B b c i r Fn Z y)). Qed.
Lemma lem1064039 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1064040 {A B : Type'} (b : B) (c : nat) (i : A) (r : type1614 A) (Fn : type1592 A B) (Z : type1336 A B) : (term596 A B b c i r Fn Z) = (term785 A B c i r Fn Z).
Proof. exact (MK_COMB (@lem1064039 B) (@lem1064038 A B b c i r Fn Z)). Qed.
Lemma lem1064045 {A B : Type'} (b : B) (c : nat) (i : A) (r : type1614 A) (Fn : type1592 A B) (Z : type1336 A B) : (term785 A B c i r Fn Z) = (term596 A B b c i r Fn Z).
Proof. exact (SYM (@lem1064040 A B b c i r Fn Z)). Qed.
Lemma lem1064073 {A : Type'} (P : Prop) (Q : A -> Prop) : (term10 A P Q) = (term11 A P Q).
Proof. exact (EQ_MP (@lem1061497 A P Q) (@lem1061496 A P Q)). Qed.
Lemma lem1064074 {B : Type'} (P : Prop) (Q : type976 B) : (term631 B P Q) = (term632 B P Q).
Proof. exact (@lem1064073 (nat -> B) P Q). Qed.
Lemma lem1064075 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term786 A B c i r y Fn c' i' Z r') = (term787 A B c i r y Fn c' i' Z r').
Proof. exact (@lem1064074 B (c = c') (term788 A B i r y Fn c' i' Z r')). Qed.
Lemma lem1064076 {A B : Type'} (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y' : nat -> B) : (term789 A B i r y Fn c' i' Z r' y') = (term759 A B i r y Fn c' i' Z r' y').
Proof. exact (eq_refl (term789 A B i r y Fn c' i' Z r' y')). Qed.
Lemma lem1064077 (c : nat) (c' : nat) : (term611 c c') = (term611 c c').
Proof. exact (eq_refl (term611 c c')). Qed.
Lemma lem1064078 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y' : nat -> B) : (term790 A B c i r y Fn c' i' Z r' y') = (term760 A B c i r y Fn c' i' Z r' y').
Proof. exact (MK_COMB (@lem1064077 c c') (@lem1064076 A B i r y Fn c' i' Z r' y')). Qed.
Lemma lem1064079 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term791 A B c i r y Fn c' i' Z r') = (term762 A B c i r y Fn c' i' Z r').
Proof. exact (fun_ext (fun y' : nat -> B => @lem1064078 A B c i r y Fn c' i' Z r' y')). Qed.
Lemma lem1064080 {B : Type'} : (@ex (nat -> B)) = (@ex (nat -> B)).
Proof. exact (eq_refl (@ex (nat -> B))). Qed.
Lemma lem1064081 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term786 A B c i r y Fn c' i' Z r') = (term764 A B c i r y Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1064080 B) (@lem1064079 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1064082 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1064083 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term792 A B c i r y Fn c' i' Z r') = (term793 A B c i r y Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1064082) (@lem1064081 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1064084 {A B : Type'} (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y' : nat -> B) : (term789 A B i r y Fn c' i' Z r' y') = (term759 A B i r y Fn c' i' Z r' y').
Proof. exact (eq_refl (term789 A B i r y Fn c' i' Z r' y')). Qed.
Lemma lem1064085 {A B : Type'} (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term794 A B i r y Fn c' i' Z r') = (term788 A B i r y Fn c' i' Z r').
Proof. exact (fun_ext (fun y' : nat -> B => @lem1064084 A B i r y Fn c' i' Z r' y')). Qed.
Lemma lem1064086 {B : Type'} : (@ex (nat -> B)) = (@ex (nat -> B)).
Proof. exact (eq_refl (@ex (nat -> B))). Qed.
Lemma lem1064087 {A B : Type'} (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term795 A B i r y Fn c' i' Z r') = (term796 A B i r y Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1064086 B) (@lem1064085 A B i r y Fn c' i' Z r')). Qed.
Lemma lem1064088 (c : nat) (c' : nat) : (term611 c c') = (term611 c c').
Proof. exact (eq_refl (term611 c c')). Qed.
Lemma lem1064089 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term787 A B c i r y Fn c' i' Z r') = (term797 A B c i r y Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1064088 c c') (@lem1064087 A B i r y Fn c' i' Z r')). Qed.
Lemma lem1064090 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : ((term786 A B c i r y Fn c' i' Z r') = (term787 A B c i r y Fn c' i' Z r')) = ((term764 A B c i r y Fn c' i' Z r') = (term797 A B c i r y Fn c' i' Z r')).
Proof. exact (MK_COMB (@lem1064083 A B c i r y Fn c' i' Z r') (@lem1064089 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1064091 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term764 A B c i r y Fn c' i' Z r') = (term797 A B c i r y Fn c' i' Z r').
Proof. exact (EQ_MP (@lem1064090 A B c i r y Fn c' i' Z r') (@lem1064075 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1064099 {A : Type'} (P : Prop) (Q : A -> Prop) : (term10 A P Q) = (term11 A P Q).
Proof. exact (EQ_MP (@lem1061497 A P Q) (@lem1061496 A P Q)). Qed.
Lemma lem1064100 {B : Type'} (P : Prop) (Q : type976 B) : (term631 B P Q) = (term632 B P Q).
Proof. exact (@lem1064099 (nat -> B) P Q). Qed.
Lemma lem1064101 {A B : Type'} (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term798 A B i r y Fn c' i' Z r') = (term799 A B i r y Fn c' i' Z r').
Proof. exact (@lem1064100 B (i = i') (term800 A B r y Fn c' i' Z r')). Qed.
Lemma lem1064102 {A B : Type'} (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y' : nat -> B) : (term801 A B r y Fn c' i' Z r' y') = (term802 A B r y Fn c' i' Z r' y').
Proof. exact (eq_refl (term801 A B r y Fn c' i' Z r' y')). Qed.
Lemma lem1064103 {A : Type'} (i : A) (i' : A) : (term650 A i i') = (term650 A i i').
Proof. exact (eq_refl (term650 A i i')). Qed.
Lemma lem1064104 {A B : Type'} (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y' : nat -> B) : (term803 A B i r y Fn c' i' Z r' y') = (term759 A B i r y Fn c' i' Z r' y').
Proof. exact (MK_COMB (@lem1064103 A i i') (@lem1064102 A B r y Fn c' i' Z r' y')). Qed.
Lemma lem1064105 {A B : Type'} (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term804 A B i r y Fn c' i' Z r') = (term788 A B i r y Fn c' i' Z r').
Proof. exact (fun_ext (fun y' : nat -> B => @lem1064104 A B i r y Fn c' i' Z r' y')). Qed.
Lemma lem1064106 {B : Type'} : (@ex (nat -> B)) = (@ex (nat -> B)).
Proof. exact (eq_refl (@ex (nat -> B))). Qed.
Lemma lem1064107 {A B : Type'} (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term798 A B i r y Fn c' i' Z r') = (term796 A B i r y Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1064106 B) (@lem1064105 A B i r y Fn c' i' Z r')). Qed.
Lemma lem1064108 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1064109 {A B : Type'} (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term805 A B i r y Fn c' i' Z r') = (term806 A B i r y Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1064108) (@lem1064107 A B i r y Fn c' i' Z r')). Qed.
Lemma lem1064110 {A B : Type'} (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y' : nat -> B) : (term801 A B r y Fn c' i' Z r' y') = (term802 A B r y Fn c' i' Z r' y').
Proof. exact (eq_refl (term801 A B r y Fn c' i' Z r' y')). Qed.
Lemma lem1064111 {A B : Type'} (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term807 A B r y Fn c' i' Z r') = (term800 A B r y Fn c' i' Z r').
Proof. exact (fun_ext (fun y' : nat -> B => @lem1064110 A B r y Fn c' i' Z r' y')). Qed.
Lemma lem1064112 {B : Type'} : (@ex (nat -> B)) = (@ex (nat -> B)).
Proof. exact (eq_refl (@ex (nat -> B))). Qed.
Lemma lem1064113 {A B : Type'} (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term808 A B r y Fn c' i' Z r') = (term809 A B r y Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1064112 B) (@lem1064111 A B r y Fn c' i' Z r')). Qed.
Lemma lem1064114 {A : Type'} (i : A) (i' : A) : (term650 A i i') = (term650 A i i').
Proof. exact (eq_refl (term650 A i i')). Qed.
Lemma lem1064115 {A B : Type'} (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term799 A B i r y Fn c' i' Z r') = (term810 A B i r y Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1064114 A i i') (@lem1064113 A B r y Fn c' i' Z r')). Qed.
Lemma lem1064116 {A B : Type'} (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : ((term798 A B i r y Fn c' i' Z r') = (term799 A B i r y Fn c' i' Z r')) = ((term796 A B i r y Fn c' i' Z r') = (term810 A B i r y Fn c' i' Z r')).
Proof. exact (MK_COMB (@lem1064109 A B i r y Fn c' i' Z r') (@lem1064115 A B i r y Fn c' i' Z r')). Qed.
Lemma lem1064117 {A B : Type'} (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term796 A B i r y Fn c' i' Z r') = (term810 A B i r y Fn c' i' Z r').
Proof. exact (EQ_MP (@lem1064116 A B i r y Fn c' i' Z r') (@lem1064101 A B i r y Fn c' i' Z r')). Qed.
Lemma lem1064125 {A : Type'} (P : Prop) (Q : A -> Prop) : (term10 A P Q) = (term11 A P Q).
Proof. exact (EQ_MP (@lem1061497 A P Q) (@lem1061496 A P Q)). Qed.
Lemma lem1064126 {B : Type'} (P : Prop) (Q : type976 B) : (term631 B P Q) = (term632 B P Q).
Proof. exact (@lem1064125 (nat -> B) P Q). Qed.
Lemma lem1064127 {A B : Type'} (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term811 A B r y Fn c' i' Z r') = (term812 A B r y Fn c' i' Z r').
Proof. exact (@lem1064126 B (r = r') (term813 A B y Fn c' i' Z r')). Qed.
Lemma lem1064128 {A B : Type'} (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y' : nat -> B) : (term814 A B y Fn c' i' Z r' y') = (term100 A B y Fn c' i' Z r' y').
Proof. exact (eq_refl (term814 A B y Fn c' i' Z r' y')). Qed.
Lemma lem1064129 {A : Type'} (r : type1614 A) (r' : type1614 A) : (term663 A r r') = (term663 A r r').
Proof. exact (eq_refl (term663 A r r')). Qed.
Lemma lem1064130 {A B : Type'} (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y' : nat -> B) : (term815 A B r y Fn c' i' Z r' y') = (term802 A B r y Fn c' i' Z r' y').
Proof. exact (MK_COMB (@lem1064129 A r r') (@lem1064128 A B y Fn c' i' Z r' y')). Qed.
Lemma lem1064131 {A B : Type'} (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term816 A B r y Fn c' i' Z r') = (term800 A B r y Fn c' i' Z r').
Proof. exact (fun_ext (fun y' : nat -> B => @lem1064130 A B r y Fn c' i' Z r' y')). Qed.
Lemma lem1064132 {B : Type'} : (@ex (nat -> B)) = (@ex (nat -> B)).
Proof. exact (eq_refl (@ex (nat -> B))). Qed.
Lemma lem1064133 {A B : Type'} (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term811 A B r y Fn c' i' Z r') = (term809 A B r y Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1064132 B) (@lem1064131 A B r y Fn c' i' Z r')). Qed.
Lemma lem1064134 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1064135 {A B : Type'} (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term817 A B r y Fn c' i' Z r') = (term818 A B r y Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1064134) (@lem1064133 A B r y Fn c' i' Z r')). Qed.
Lemma lem1064136 {A B : Type'} (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y' : nat -> B) : (term814 A B y Fn c' i' Z r' y') = (term100 A B y Fn c' i' Z r' y').
Proof. exact (eq_refl (term814 A B y Fn c' i' Z r' y')). Qed.
Lemma lem1064137 {A B : Type'} (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term819 A B y Fn c' i' Z r') = (term813 A B y Fn c' i' Z r').
Proof. exact (fun_ext (fun y' : nat -> B => @lem1064136 A B y Fn c' i' Z r' y')). Qed.
Lemma lem1064138 {B : Type'} : (@ex (nat -> B)) = (@ex (nat -> B)).
Proof. exact (eq_refl (@ex (nat -> B))). Qed.
Lemma lem1064139 {A B : Type'} (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term820 A B y Fn c' i' Z r') = (term821 A B y Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1064138 B) (@lem1064137 A B y Fn c' i' Z r')). Qed.
Lemma lem1064140 {A : Type'} (r : type1614 A) (r' : type1614 A) : (term663 A r r') = (term663 A r r').
Proof. exact (eq_refl (term663 A r r')). Qed.
Lemma lem1064141 {A B : Type'} (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term812 A B r y Fn c' i' Z r') = (term822 A B r y Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1064140 A r r') (@lem1064139 A B y Fn c' i' Z r')). Qed.
Lemma lem1064142 {A B : Type'} (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : ((term811 A B r y Fn c' i' Z r') = (term812 A B r y Fn c' i' Z r')) = ((term809 A B r y Fn c' i' Z r') = (term822 A B r y Fn c' i' Z r')).
Proof. exact (MK_COMB (@lem1064135 A B r y Fn c' i' Z r') (@lem1064141 A B r y Fn c' i' Z r')). Qed.
Lemma lem1064143 {A B : Type'} (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term809 A B r y Fn c' i' Z r') = (term822 A B r y Fn c' i' Z r').
Proof. exact (EQ_MP (@lem1064142 A B r y Fn c' i' Z r') (@lem1064127 A B r y Fn c' i' Z r')). Qed.
Lemma lem1064182 {A : Type'} (i : A) (i' : A) : (term650 A i i') = (term650 A i i').
Proof. exact (eq_refl (term650 A i i')). Qed.
Lemma lem1064183 {A B : Type'} (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term810 A B i r y Fn c' i' Z r') = (term823 A B i r y Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1064182 A i i') (@lem1064143 A B r y Fn c' i' Z r')). Qed.
Lemma lem1064186 {A B : Type'} (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term796 A B i r y Fn c' i' Z r') = (term823 A B i r y Fn c' i' Z r').
Proof. exact (TRANS (@lem1064117 A B i r y Fn c' i' Z r') (@lem1064183 A B i r y Fn c' i' Z r')). Qed.
Lemma lem1064187 (c : nat) (c' : nat) : (term611 c c') = (term611 c c').
Proof. exact (eq_refl (term611 c c')). Qed.
Lemma lem1064188 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term797 A B c i r y Fn c' i' Z r') = (term824 A B c i r y Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1064187 c c') (@lem1064186 A B i r y Fn c' i' Z r')). Qed.
Lemma lem1064191 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term764 A B c i r y Fn c' i' Z r') = (term824 A B c i r y Fn c' i' Z r').
Proof. exact (TRANS (@lem1064091 A B c i r y Fn c' i' Z r') (@lem1064188 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1064192 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term766 A B c i r y Fn c' i' Z) = (term825 A B c i r y Fn c' i' Z).
Proof. exact (fun_ext (fun r' : type1614 A => @lem1064191 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1064193 {A : Type'} : (@ex (nat -> recspace A)) = (@ex (nat -> recspace A)).
Proof. exact (eq_refl (@ex (nat -> recspace A))). Qed.
Lemma lem1064194 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term768 A B c i r y Fn c' i' Z) = (term826 A B c i r y Fn c' i' Z).
Proof. exact (MK_COMB (@lem1064193 A) (@lem1064192 A B c i r y Fn c' i' Z)). Qed.
Lemma lem1064198 {A : Type'} (P : Prop) (Q : A -> Prop) : (term10 A P Q) = (term11 A P Q).
Proof. exact (EQ_MP (@lem1061497 A P Q) (@lem1061496 A P Q)). Qed.
Lemma lem1064199 {A : Type'} (P : Prop) (Q : type963 A) : (term676 A P Q) = (term677 A P Q).
Proof. exact (@lem1064198 (type1614 A) P Q). Qed.
Lemma lem1064200 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term827 A B c i r y Fn c' i' Z) = (term828 A B c i r y Fn c' i' Z).
Proof. exact (@lem1064199 A (c = c') (term829 A B i r y Fn c' i' Z)). Qed.
Lemma lem1064201 {A B : Type'} (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term830 A B i r y Fn c' i' Z r') = (term823 A B i r y Fn c' i' Z r').
Proof. exact (eq_refl (term830 A B i r y Fn c' i' Z r')). Qed.
Lemma lem1064202 (c : nat) (c' : nat) : (term611 c c') = (term611 c c').
Proof. exact (eq_refl (term611 c c')). Qed.
Lemma lem1064203 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term831 A B c i r y Fn c' i' Z r') = (term824 A B c i r y Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1064202 c c') (@lem1064201 A B i r y Fn c' i' Z r')). Qed.
Lemma lem1064204 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term832 A B c i r y Fn c' i' Z) = (term825 A B c i r y Fn c' i' Z).
Proof. exact (fun_ext (fun r' : type1614 A => @lem1064203 A B c i r y Fn c' i' Z r')). Qed.
Lemma lem1064205 {A : Type'} : (@ex (nat -> recspace A)) = (@ex (nat -> recspace A)).
Proof. exact (eq_refl (@ex (nat -> recspace A))). Qed.
Lemma lem1064206 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term827 A B c i r y Fn c' i' Z) = (term826 A B c i r y Fn c' i' Z).
Proof. exact (MK_COMB (@lem1064205 A) (@lem1064204 A B c i r y Fn c' i' Z)). Qed.
Lemma lem1064207 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1064208 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term833 A B c i r y Fn c' i' Z) = (term834 A B c i r y Fn c' i' Z).
Proof. exact (MK_COMB (@lem1064207) (@lem1064206 A B c i r y Fn c' i' Z)). Qed.
Lemma lem1064209 {A B : Type'} (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term830 A B i r y Fn c' i' Z r') = (term823 A B i r y Fn c' i' Z r').
Proof. exact (eq_refl (term830 A B i r y Fn c' i' Z r')). Qed.
Lemma lem1064210 {A B : Type'} (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term835 A B i r y Fn c' i' Z) = (term829 A B i r y Fn c' i' Z).
Proof. exact (fun_ext (fun r' : type1614 A => @lem1064209 A B i r y Fn c' i' Z r')). Qed.
Lemma lem1064211 {A : Type'} : (@ex (nat -> recspace A)) = (@ex (nat -> recspace A)).
Proof. exact (eq_refl (@ex (nat -> recspace A))). Qed.
Lemma lem1064212 {A B : Type'} (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term836 A B i r y Fn c' i' Z) = (term837 A B i r y Fn c' i' Z).
Proof. exact (MK_COMB (@lem1064211 A) (@lem1064210 A B i r y Fn c' i' Z)). Qed.
Lemma lem1064213 (c : nat) (c' : nat) : (term611 c c') = (term611 c c').
Proof. exact (eq_refl (term611 c c')). Qed.
Lemma lem1064214 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term828 A B c i r y Fn c' i' Z) = (term838 A B c i r y Fn c' i' Z).
Proof. exact (MK_COMB (@lem1064213 c c') (@lem1064212 A B i r y Fn c' i' Z)). Qed.
Lemma lem1064215 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : ((term827 A B c i r y Fn c' i' Z) = (term828 A B c i r y Fn c' i' Z)) = ((term826 A B c i r y Fn c' i' Z) = (term838 A B c i r y Fn c' i' Z)).
Proof. exact (MK_COMB (@lem1064208 A B c i r y Fn c' i' Z) (@lem1064214 A B c i r y Fn c' i' Z)). Qed.
Lemma lem1064216 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term826 A B c i r y Fn c' i' Z) = (term838 A B c i r y Fn c' i' Z).
Proof. exact (EQ_MP (@lem1064215 A B c i r y Fn c' i' Z) (@lem1064200 A B c i r y Fn c' i' Z)). Qed.
Lemma lem1064224 {A : Type'} (P : Prop) (Q : A -> Prop) : (term10 A P Q) = (term11 A P Q).
Proof. exact (EQ_MP (@lem1061497 A P Q) (@lem1061496 A P Q)). Qed.
Lemma lem1064225 {A : Type'} (P : Prop) (Q : type963 A) : (term676 A P Q) = (term677 A P Q).
Proof. exact (@lem1064224 (type1614 A) P Q). Qed.
Lemma lem1064226 {A B : Type'} (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term839 A B i r y Fn c' i' Z) = (term840 A B i r y Fn c' i' Z).
Proof. exact (@lem1064225 A (i = i') (term841 A B r y Fn c' i' Z)). Qed.
Lemma lem1064227 {A B : Type'} (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term842 A B r y Fn c' i' Z r') = (term822 A B r y Fn c' i' Z r').
Proof. exact (eq_refl (term842 A B r y Fn c' i' Z r')). Qed.
Lemma lem1064228 {A : Type'} (i : A) (i' : A) : (term650 A i i') = (term650 A i i').
Proof. exact (eq_refl (term650 A i i')). Qed.
Lemma lem1064229 {A B : Type'} (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term843 A B i r y Fn c' i' Z r') = (term823 A B i r y Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1064228 A i i') (@lem1064227 A B r y Fn c' i' Z r')). Qed.
Lemma lem1064230 {A B : Type'} (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term844 A B i r y Fn c' i' Z) = (term829 A B i r y Fn c' i' Z).
Proof. exact (fun_ext (fun r' : type1614 A => @lem1064229 A B i r y Fn c' i' Z r')). Qed.
Lemma lem1064231 {A : Type'} : (@ex (nat -> recspace A)) = (@ex (nat -> recspace A)).
Proof. exact (eq_refl (@ex (nat -> recspace A))). Qed.
Lemma lem1064232 {A B : Type'} (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term839 A B i r y Fn c' i' Z) = (term837 A B i r y Fn c' i' Z).
Proof. exact (MK_COMB (@lem1064231 A) (@lem1064230 A B i r y Fn c' i' Z)). Qed.
Lemma lem1064233 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1064234 {A B : Type'} (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term845 A B i r y Fn c' i' Z) = (term846 A B i r y Fn c' i' Z).
Proof. exact (MK_COMB (@lem1064233) (@lem1064232 A B i r y Fn c' i' Z)). Qed.
Lemma lem1064235 {A B : Type'} (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term842 A B r y Fn c' i' Z r') = (term822 A B r y Fn c' i' Z r').
Proof. exact (eq_refl (term842 A B r y Fn c' i' Z r')). Qed.
Lemma lem1064236 {A B : Type'} (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term847 A B r y Fn c' i' Z) = (term841 A B r y Fn c' i' Z).
Proof. exact (fun_ext (fun r' : type1614 A => @lem1064235 A B r y Fn c' i' Z r')). Qed.
Lemma lem1064237 {A : Type'} : (@ex (nat -> recspace A)) = (@ex (nat -> recspace A)).
Proof. exact (eq_refl (@ex (nat -> recspace A))). Qed.
Lemma lem1064238 {A B : Type'} (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term848 A B r y Fn c' i' Z) = (term849 A B r y Fn c' i' Z).
Proof. exact (MK_COMB (@lem1064237 A) (@lem1064236 A B r y Fn c' i' Z)). Qed.
Lemma lem1064239 {A : Type'} (i : A) (i' : A) : (term650 A i i') = (term650 A i i').
Proof. exact (eq_refl (term650 A i i')). Qed.
Lemma lem1064240 {A B : Type'} (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term840 A B i r y Fn c' i' Z) = (term850 A B i r y Fn c' i' Z).
Proof. exact (MK_COMB (@lem1064239 A i i') (@lem1064238 A B r y Fn c' i' Z)). Qed.
Lemma lem1064241 {A B : Type'} (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : ((term839 A B i r y Fn c' i' Z) = (term840 A B i r y Fn c' i' Z)) = ((term837 A B i r y Fn c' i' Z) = (term850 A B i r y Fn c' i' Z)).
Proof. exact (MK_COMB (@lem1064234 A B i r y Fn c' i' Z) (@lem1064240 A B i r y Fn c' i' Z)). Qed.
Lemma lem1064242 {A B : Type'} (i : A) (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term837 A B i r y Fn c' i' Z) = (term850 A B i r y Fn c' i' Z).
Proof. exact (EQ_MP (@lem1064241 A B i r y Fn c' i' Z) (@lem1064226 A B i r y Fn c' i' Z)). Qed.
Lemma lem1064248 {A : Type'} (P : A -> Prop) (a : A) : (term15 A a P) = (P a).
Proof. exact (EQ_MP (@lem1061503 A P a) (@lem1061502 A P a)). Qed.
Lemma lem1064249 {A : Type'} (P : type963 A) (a : type1614 A) : (term702 A a P) = (P a).
Proof. exact (@lem1064248 (type1614 A) P a). Qed.
Lemma lem1064250 {A B : Type'} (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r : type1614 A) : (term851 A B r y Fn c' i' Z) = (term852 A B y Fn c' i' Z r).
Proof. exact (@lem1064249 A (term853 A B y Fn c' i' Z) r). Qed.
Lemma lem1064251 {A B : Type'} (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term852 A B y Fn c' i' Z r') = (term821 A B y Fn c' i' Z r').
Proof. exact (eq_refl (term852 A B y Fn c' i' Z r')). Qed.
Lemma lem1064252 {A : Type'} (r : type1614 A) (r' : type1614 A) : (term663 A r r') = (term663 A r r').
Proof. exact (eq_refl (term663 A r r')). Qed.
Lemma lem1064253 {A B : Type'} (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term854 A B r y Fn c' i' Z r') = (term822 A B r y Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1064252 A r r') (@lem1064251 A B y Fn c' i' Z r')). Qed.
Lemma lem1064254 {A B : Type'} (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term855 A B r y Fn c' i' Z) = (term841 A B r y Fn c' i' Z).
Proof. exact (fun_ext (fun r' : type1614 A => @lem1064253 A B r y Fn c' i' Z r')). Qed.
Lemma lem1064255 {A : Type'} : (@ex (nat -> recspace A)) = (@ex (nat -> recspace A)).
Proof. exact (eq_refl (@ex (nat -> recspace A))). Qed.
Lemma lem1064256 {A B : Type'} (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term851 A B r y Fn c' i' Z) = (term849 A B r y Fn c' i' Z).
Proof. exact (MK_COMB (@lem1064255 A) (@lem1064254 A B r y Fn c' i' Z)). Qed.
Lemma lem1064257 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1064258 {A B : Type'} (r : type1614 A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term856 A B r y Fn c' i' Z) = (term857 A B r y Fn c' i' Z).
Proof. exact (MK_COMB (@lem1064257) (@lem1064256 A B r y Fn c' i' Z)). Qed.
Lemma lem1064259 {A B : Type'} (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r : type1614 A) : (term852 A B y Fn c' i' Z r) = (term821 A B y Fn c' i' Z r).
Proof. exact (eq_refl (term852 A B y Fn c' i' Z r)). Qed.
Lemma lem1064260 {A B : Type'} (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r : type1614 A) : ((term851 A B r y Fn c' i' Z) = (term852 A B y Fn c' i' Z r)) = ((term849 A B r y Fn c' i' Z) = (term821 A B y Fn c' i' Z r)).
Proof. exact (MK_COMB (@lem1064258 A B r y Fn c' i' Z) (@lem1064259 A B y Fn c' i' Z r)). Qed.
Lemma lem1064261 {A B : Type'} (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r : type1614 A) : (term849 A B r y Fn c' i' Z) = (term821 A B y Fn c' i' Z r).
Proof. exact (EQ_MP (@lem1064260 A B y Fn c' i' Z r) (@lem1064250 A B y Fn c' i' Z r)). Qed.
Lemma lem1064296 {A : Type'} (i : A) (i' : A) : (term650 A i i') = (term650 A i i').
Proof. exact (eq_refl (term650 A i i')). Qed.
Lemma lem1064297 {A B : Type'} (i : A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r : type1614 A) : (term850 A B i r y Fn c' i' Z) = (term858 A B i y Fn c' i' Z r).
Proof. exact (MK_COMB (@lem1064296 A i i') (@lem1064261 A B y Fn c' i' Z r)). Qed.
Lemma lem1064300 {A B : Type'} (i : A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r : type1614 A) : (term837 A B i r y Fn c' i' Z) = (term858 A B i y Fn c' i' Z r).
Proof. exact (TRANS (@lem1064242 A B i r y Fn c' i' Z) (@lem1064297 A B i y Fn c' i' Z r)). Qed.
Lemma lem1064301 (c : nat) (c' : nat) : (term611 c c') = (term611 c c').
Proof. exact (eq_refl (term611 c c')). Qed.
Lemma lem1064302 {A B : Type'} (c : nat) (i : A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r : type1614 A) : (term838 A B c i r y Fn c' i' Z) = (term859 A B c i y Fn c' i' Z r).
Proof. exact (MK_COMB (@lem1064301 c c') (@lem1064300 A B i y Fn c' i' Z r)). Qed.
Lemma lem1064305 {A B : Type'} (c : nat) (i : A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r : type1614 A) : (term826 A B c i r y Fn c' i' Z) = (term859 A B c i y Fn c' i' Z r).
Proof. exact (TRANS (@lem1064216 A B c i r y Fn c' i' Z) (@lem1064302 A B c i y Fn c' i' Z r)). Qed.
Lemma lem1064306 {A B : Type'} (c : nat) (i : A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r : type1614 A) : (term768 A B c i r y Fn c' i' Z) = (term859 A B c i y Fn c' i' Z r).
Proof. exact (TRANS (@lem1064194 A B c i r y Fn c' i' Z) (@lem1064305 A B c i y Fn c' i' Z r)). Qed.
Lemma lem1064307 {A B : Type'} (c : nat) (i : A) (y : B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) (r : type1614 A) : (term770 A B c i r y Fn c' Z) = (term860 A B c i y Fn c' Z r).
Proof. exact (fun_ext (fun i' : A => @lem1064306 A B c i y Fn c' i' Z r)). Qed.
Lemma lem1064308 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1064309 {A B : Type'} (c : nat) (i : A) (y : B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) (r : type1614 A) : (term772 A B c i r y Fn c' Z) = (term861 A B c i y Fn c' Z r).
Proof. exact (MK_COMB (@lem1064308 A) (@lem1064307 A B c i y Fn c' Z r)). Qed.
Lemma lem1064313 {A : Type'} (P : Prop) (Q : A -> Prop) : (term10 A P Q) = (term11 A P Q).
Proof. exact (EQ_MP (@lem1061497 A P Q) (@lem1061496 A P Q)). Qed.
Lemma lem1064314 {A : Type'} (P : Prop) (Q : A -> Prop) : (term10 A P Q) = (term11 A P Q).
Proof. exact (@lem1064313 A P Q). Qed.
Lemma lem1064315 {A B : Type'} (c : nat) (i : A) (y : B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) (r : type1614 A) : (term862 A B c i y Fn c' Z r) = (term863 A B c i y Fn c' Z r).
Proof. exact (@lem1064314 A (c = c') (term864 A B i y Fn c' Z r)). Qed.
Lemma lem1064316 {A B : Type'} (i : A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r : type1614 A) : (term865 A B i y Fn c' Z r i') = (term858 A B i y Fn c' i' Z r).
Proof. exact (eq_refl (term865 A B i y Fn c' Z r i')). Qed.
Lemma lem1064317 (c : nat) (c' : nat) : (term611 c c') = (term611 c c').
Proof. exact (eq_refl (term611 c c')). Qed.
Lemma lem1064318 {A B : Type'} (c : nat) (i : A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r : type1614 A) : (term866 A B c i y Fn c' Z r i') = (term859 A B c i y Fn c' i' Z r).
Proof. exact (MK_COMB (@lem1064317 c c') (@lem1064316 A B i y Fn c' i' Z r)). Qed.
Lemma lem1064319 {A B : Type'} (c : nat) (i : A) (y : B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) (r : type1614 A) : (term867 A B c i y Fn c' Z r) = (term860 A B c i y Fn c' Z r).
Proof. exact (fun_ext (fun i' : A => @lem1064318 A B c i y Fn c' i' Z r)). Qed.
Lemma lem1064320 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1064321 {A B : Type'} (c : nat) (i : A) (y : B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) (r : type1614 A) : (term862 A B c i y Fn c' Z r) = (term861 A B c i y Fn c' Z r).
Proof. exact (MK_COMB (@lem1064320 A) (@lem1064319 A B c i y Fn c' Z r)). Qed.
Lemma lem1064322 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1064323 {A B : Type'} (c : nat) (i : A) (y : B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) (r : type1614 A) : (term868 A B c i y Fn c' Z r) = (term869 A B c i y Fn c' Z r).
Proof. exact (MK_COMB (@lem1064322) (@lem1064321 A B c i y Fn c' Z r)). Qed.
Lemma lem1064324 {A B : Type'} (i : A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r : type1614 A) : (term865 A B i y Fn c' Z r i') = (term858 A B i y Fn c' i' Z r).
Proof. exact (eq_refl (term865 A B i y Fn c' Z r i')). Qed.
Lemma lem1064325 {A B : Type'} (i : A) (y : B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) (r : type1614 A) : (term870 A B i y Fn c' Z r) = (term864 A B i y Fn c' Z r).
Proof. exact (fun_ext (fun i' : A => @lem1064324 A B i y Fn c' i' Z r)). Qed.
Lemma lem1064326 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1064327 {A B : Type'} (i : A) (y : B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) (r : type1614 A) : (term871 A B i y Fn c' Z r) = (term872 A B i y Fn c' Z r).
Proof. exact (MK_COMB (@lem1064326 A) (@lem1064325 A B i y Fn c' Z r)). Qed.
Lemma lem1064328 (c : nat) (c' : nat) : (term611 c c') = (term611 c c').
Proof. exact (eq_refl (term611 c c')). Qed.
Lemma lem1064329 {A B : Type'} (c : nat) (i : A) (y : B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) (r : type1614 A) : (term863 A B c i y Fn c' Z r) = (term873 A B c i y Fn c' Z r).
Proof. exact (MK_COMB (@lem1064328 c c') (@lem1064327 A B i y Fn c' Z r)). Qed.
Lemma lem1064330 {A B : Type'} (c : nat) (i : A) (y : B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) (r : type1614 A) : ((term862 A B c i y Fn c' Z r) = (term863 A B c i y Fn c' Z r)) = ((term861 A B c i y Fn c' Z r) = (term873 A B c i y Fn c' Z r)).
Proof. exact (MK_COMB (@lem1064323 A B c i y Fn c' Z r) (@lem1064329 A B c i y Fn c' Z r)). Qed.
Lemma lem1064331 {A B : Type'} (c : nat) (i : A) (y : B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) (r : type1614 A) : (term861 A B c i y Fn c' Z r) = (term873 A B c i y Fn c' Z r).
Proof. exact (EQ_MP (@lem1064330 A B c i y Fn c' Z r) (@lem1064315 A B c i y Fn c' Z r)). Qed.
Lemma lem1064337 {A : Type'} (P : A -> Prop) (a : A) : (term15 A a P) = (P a).
Proof. exact (EQ_MP (@lem1061503 A P a) (@lem1061502 A P a)). Qed.
Lemma lem1064338 {A : Type'} (P : A -> Prop) (a : A) : (term15 A a P) = (P a).
Proof. exact (@lem1064337 A P a). Qed.
Lemma lem1064339 {A B : Type'} (y : B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) (r : type1614 A) (i : A) : (term874 A B i y Fn c' Z r) = (term875 A B y Fn c' Z r i).
Proof. exact (@lem1064338 A (term876 A B y Fn c' Z r) i). Qed.
Lemma lem1064340 {A B : Type'} (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r : type1614 A) : (term875 A B y Fn c' Z r i') = (term821 A B y Fn c' i' Z r).
Proof. exact (eq_refl (term875 A B y Fn c' Z r i')). Qed.
Lemma lem1064341 {A : Type'} (i : A) (i' : A) : (term650 A i i') = (term650 A i i').
Proof. exact (eq_refl (term650 A i i')). Qed.
Lemma lem1064342 {A B : Type'} (i : A) (y : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r : type1614 A) : (term877 A B i y Fn c' Z r i') = (term858 A B i y Fn c' i' Z r).
Proof. exact (MK_COMB (@lem1064341 A i i') (@lem1064340 A B y Fn c' i' Z r)). Qed.
Lemma lem1064343 {A B : Type'} (i : A) (y : B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) (r : type1614 A) : (term878 A B i y Fn c' Z r) = (term864 A B i y Fn c' Z r).
Proof. exact (fun_ext (fun i' : A => @lem1064342 A B i y Fn c' i' Z r)). Qed.
Lemma lem1064344 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1064345 {A B : Type'} (i : A) (y : B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) (r : type1614 A) : (term874 A B i y Fn c' Z r) = (term872 A B i y Fn c' Z r).
Proof. exact (MK_COMB (@lem1064344 A) (@lem1064343 A B i y Fn c' Z r)). Qed.
Lemma lem1064346 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1064347 {A B : Type'} (i : A) (y : B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) (r : type1614 A) : (term879 A B i y Fn c' Z r) = (term880 A B i y Fn c' Z r).
Proof. exact (MK_COMB (@lem1064346) (@lem1064345 A B i y Fn c' Z r)). Qed.
Lemma lem1064348 {A B : Type'} (y : B) (Fn : type1592 A B) (c' : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : (term875 A B y Fn c' Z r i) = (term821 A B y Fn c' i Z r).
Proof. exact (eq_refl (term875 A B y Fn c' Z r i)). Qed.
Lemma lem1064349 {A B : Type'} (y : B) (Fn : type1592 A B) (c' : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : ((term874 A B i y Fn c' Z r) = (term875 A B y Fn c' Z r i)) = ((term872 A B i y Fn c' Z r) = (term821 A B y Fn c' i Z r)).
Proof. exact (MK_COMB (@lem1064347 A B i y Fn c' Z r) (@lem1064348 A B y Fn c' i Z r)). Qed.
Lemma lem1064350 {A B : Type'} (y : B) (Fn : type1592 A B) (c' : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : (term872 A B i y Fn c' Z r) = (term821 A B y Fn c' i Z r).
Proof. exact (EQ_MP (@lem1064349 A B y Fn c' i Z r) (@lem1064339 A B y Fn c' Z r i)). Qed.
Lemma lem1064385 (c : nat) (c' : nat) : (term611 c c') = (term611 c c').
Proof. exact (eq_refl (term611 c c')). Qed.
Lemma lem1064386 {A B : Type'} (c : nat) (y : B) (Fn : type1592 A B) (c' : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : (term873 A B c i y Fn c' Z r) = (term881 A B c y Fn c' i Z r).
Proof. exact (MK_COMB (@lem1064385 c c') (@lem1064350 A B y Fn c' i Z r)). Qed.
Lemma lem1064389 {A B : Type'} (c : nat) (y : B) (Fn : type1592 A B) (c' : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : (term861 A B c i y Fn c' Z r) = (term881 A B c y Fn c' i Z r).
Proof. exact (TRANS (@lem1064331 A B c i y Fn c' Z r) (@lem1064386 A B c y Fn c' i Z r)). Qed.
Lemma lem1064390 {A B : Type'} (c : nat) (y : B) (Fn : type1592 A B) (c' : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : (term772 A B c i r y Fn c' Z) = (term881 A B c y Fn c' i Z r).
Proof. exact (TRANS (@lem1064309 A B c i y Fn c' Z r) (@lem1064389 A B c y Fn c' i Z r)). Qed.
Lemma lem1064391 {A B : Type'} (c : nat) (y : B) (Fn : type1592 A B) (i : A) (Z : type1336 A B) (r : type1614 A) : (term774 A B c i r y Fn Z) = (term882 A B c y Fn i Z r).
Proof. exact (fun_ext (fun c' : nat => @lem1064390 A B c y Fn c' i Z r)). Qed.
Lemma lem1064392 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1064393 {A B : Type'} (c : nat) (y : B) (Fn : type1592 A B) (i : A) (Z : type1336 A B) (r : type1614 A) : (term776 A B c i r y Fn Z) = (term883 A B c y Fn i Z r).
Proof. exact (MK_COMB (@lem1064392) (@lem1064391 A B c y Fn i Z r)). Qed.
Lemma lem1064395 {A : Type'} (P : A -> Prop) (a : A) : (term15 A a P) = (P a).
Proof. exact (EQ_MP (@lem1061503 A P a) (@lem1061502 A P a)). Qed.
Lemma lem1064396 (P : nat -> Prop) (a : nat) : (term740 a P) = (P a).
Proof. exact (@lem1064395 nat P a). Qed.
Lemma lem1064397 {A B : Type'} (y : B) (Fn : type1592 A B) (i : A) (Z : type1336 A B) (r : type1614 A) (c : nat) : (term884 A B c y Fn i Z r) = (term885 A B y Fn i Z r c).
Proof. exact (@lem1064396 (term886 A B y Fn i Z r) c). Qed.
Lemma lem1064398 {A B : Type'} (y : B) (Fn : type1592 A B) (c' : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : (term885 A B y Fn i Z r c') = (term821 A B y Fn c' i Z r).
Proof. exact (eq_refl (term885 A B y Fn i Z r c')). Qed.
Lemma lem1064399 (c : nat) (c' : nat) : (term611 c c') = (term611 c c').
Proof. exact (eq_refl (term611 c c')). Qed.
Lemma lem1064400 {A B : Type'} (c : nat) (y : B) (Fn : type1592 A B) (c' : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : (term887 A B c y Fn i Z r c') = (term881 A B c y Fn c' i Z r).
Proof. exact (MK_COMB (@lem1064399 c c') (@lem1064398 A B y Fn c' i Z r)). Qed.
Lemma lem1064401 {A B : Type'} (c : nat) (y : B) (Fn : type1592 A B) (i : A) (Z : type1336 A B) (r : type1614 A) : (term888 A B c y Fn i Z r) = (term882 A B c y Fn i Z r).
Proof. exact (fun_ext (fun c' : nat => @lem1064400 A B c y Fn c' i Z r)). Qed.
Lemma lem1064402 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1064403 {A B : Type'} (c : nat) (y : B) (Fn : type1592 A B) (i : A) (Z : type1336 A B) (r : type1614 A) : (term884 A B c y Fn i Z r) = (term883 A B c y Fn i Z r).
Proof. exact (MK_COMB (@lem1064402) (@lem1064401 A B c y Fn i Z r)). Qed.
Lemma lem1064404 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1064405 {A B : Type'} (c : nat) (y : B) (Fn : type1592 A B) (i : A) (Z : type1336 A B) (r : type1614 A) : (term889 A B c y Fn i Z r) = (term890 A B c y Fn i Z r).
Proof. exact (MK_COMB (@lem1064404) (@lem1064403 A B c y Fn i Z r)). Qed.
Lemma lem1064406 {A B : Type'} (y : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : (term885 A B y Fn i Z r c) = (term821 A B y Fn c i Z r).
Proof. exact (eq_refl (term885 A B y Fn i Z r c)). Qed.
Lemma lem1064407 {A B : Type'} (y : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : ((term884 A B c y Fn i Z r) = (term885 A B y Fn i Z r c)) = ((term883 A B c y Fn i Z r) = (term821 A B y Fn c i Z r)).
Proof. exact (MK_COMB (@lem1064405 A B c y Fn i Z r) (@lem1064406 A B y Fn c i Z r)). Qed.
Lemma lem1064408 {A B : Type'} (y : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : (term883 A B c y Fn i Z r) = (term821 A B y Fn c i Z r).
Proof. exact (EQ_MP (@lem1064407 A B y Fn c i Z r) (@lem1064397 A B y Fn i Z r c)). Qed.
Lemma lem1064443 {A B : Type'} (y : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : (term776 A B c i r y Fn Z) = (term821 A B y Fn c i Z r).
Proof. exact (TRANS (@lem1064393 A B c y Fn i Z r) (@lem1064408 A B y Fn c i Z r)). Qed.
Lemma lem1064444 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1064445 {A B : Type'} (y : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : (term778 A B c i r y Fn Z) = (term891 A B y Fn c i Z r).
Proof. exact (MK_COMB (@lem1064444) (@lem1064443 A B y Fn c i Z r)). Qed.
Lemma lem1064461 {A : Type'} (P : Prop) (Q : A -> Prop) : (term10 A P Q) = (term11 A P Q).
Proof. exact (EQ_MP (@lem1061497 A P Q) (@lem1061496 A P Q)). Qed.
Lemma lem1064462 {B : Type'} (P : Prop) (Q : type976 B) : (term631 B P Q) = (term632 B P Q).
Proof. exact (@lem1064461 (nat -> B) P Q). Qed.
Lemma lem1064463 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term786 A B c i r x' Fn c' i' Z r') = (term787 A B c i r x' Fn c' i' Z r').
Proof. exact (@lem1064462 B (c = c') (term788 A B i r x' Fn c' i' Z r')). Qed.
Lemma lem1064464 {A B : Type'} (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y : nat -> B) : (term789 A B i r x' Fn c' i' Z r' y) = (term759 A B i r x' Fn c' i' Z r' y).
Proof. exact (eq_refl (term789 A B i r x' Fn c' i' Z r' y)). Qed.
Lemma lem1064465 (c : nat) (c' : nat) : (term611 c c') = (term611 c c').
Proof. exact (eq_refl (term611 c c')). Qed.
Lemma lem1064466 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y : nat -> B) : (term790 A B c i r x' Fn c' i' Z r' y) = (term760 A B c i r x' Fn c' i' Z r' y).
Proof. exact (MK_COMB (@lem1064465 c c') (@lem1064464 A B i r x' Fn c' i' Z r' y)). Qed.
Lemma lem1064467 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term791 A B c i r x' Fn c' i' Z r') = (term762 A B c i r x' Fn c' i' Z r').
Proof. exact (fun_ext (fun y : nat -> B => @lem1064466 A B c i r x' Fn c' i' Z r' y)). Qed.
Lemma lem1064468 {B : Type'} : (@ex (nat -> B)) = (@ex (nat -> B)).
Proof. exact (eq_refl (@ex (nat -> B))). Qed.
Lemma lem1064469 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term786 A B c i r x' Fn c' i' Z r') = (term764 A B c i r x' Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1064468 B) (@lem1064467 A B c i r x' Fn c' i' Z r')). Qed.
Lemma lem1064470 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1064471 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term792 A B c i r x' Fn c' i' Z r') = (term793 A B c i r x' Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1064470) (@lem1064469 A B c i r x' Fn c' i' Z r')). Qed.
Lemma lem1064472 {A B : Type'} (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y : nat -> B) : (term789 A B i r x' Fn c' i' Z r' y) = (term759 A B i r x' Fn c' i' Z r' y).
Proof. exact (eq_refl (term789 A B i r x' Fn c' i' Z r' y)). Qed.
Lemma lem1064473 {A B : Type'} (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term794 A B i r x' Fn c' i' Z r') = (term788 A B i r x' Fn c' i' Z r').
Proof. exact (fun_ext (fun y : nat -> B => @lem1064472 A B i r x' Fn c' i' Z r' y)). Qed.
Lemma lem1064474 {B : Type'} : (@ex (nat -> B)) = (@ex (nat -> B)).
Proof. exact (eq_refl (@ex (nat -> B))). Qed.
Lemma lem1064475 {A B : Type'} (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term795 A B i r x' Fn c' i' Z r') = (term796 A B i r x' Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1064474 B) (@lem1064473 A B i r x' Fn c' i' Z r')). Qed.
Lemma lem1064476 (c : nat) (c' : nat) : (term611 c c') = (term611 c c').
Proof. exact (eq_refl (term611 c c')). Qed.
Lemma lem1064477 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term787 A B c i r x' Fn c' i' Z r') = (term797 A B c i r x' Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1064476 c c') (@lem1064475 A B i r x' Fn c' i' Z r')). Qed.
Lemma lem1064478 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : ((term786 A B c i r x' Fn c' i' Z r') = (term787 A B c i r x' Fn c' i' Z r')) = ((term764 A B c i r x' Fn c' i' Z r') = (term797 A B c i r x' Fn c' i' Z r')).
Proof. exact (MK_COMB (@lem1064471 A B c i r x' Fn c' i' Z r') (@lem1064477 A B c i r x' Fn c' i' Z r')). Qed.
Lemma lem1064479 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term764 A B c i r x' Fn c' i' Z r') = (term797 A B c i r x' Fn c' i' Z r').
Proof. exact (EQ_MP (@lem1064478 A B c i r x' Fn c' i' Z r') (@lem1064463 A B c i r x' Fn c' i' Z r')). Qed.
Lemma lem1064487 {A : Type'} (P : Prop) (Q : A -> Prop) : (term10 A P Q) = (term11 A P Q).
Proof. exact (EQ_MP (@lem1061497 A P Q) (@lem1061496 A P Q)). Qed.
Lemma lem1064488 {B : Type'} (P : Prop) (Q : type976 B) : (term631 B P Q) = (term632 B P Q).
Proof. exact (@lem1064487 (nat -> B) P Q). Qed.
Lemma lem1064489 {A B : Type'} (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term798 A B i r x' Fn c' i' Z r') = (term799 A B i r x' Fn c' i' Z r').
Proof. exact (@lem1064488 B (i = i') (term800 A B r x' Fn c' i' Z r')). Qed.
Lemma lem1064490 {A B : Type'} (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y : nat -> B) : (term801 A B r x' Fn c' i' Z r' y) = (term802 A B r x' Fn c' i' Z r' y).
Proof. exact (eq_refl (term801 A B r x' Fn c' i' Z r' y)). Qed.
Lemma lem1064491 {A : Type'} (i : A) (i' : A) : (term650 A i i') = (term650 A i i').
Proof. exact (eq_refl (term650 A i i')). Qed.
Lemma lem1064492 {A B : Type'} (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y : nat -> B) : (term803 A B i r x' Fn c' i' Z r' y) = (term759 A B i r x' Fn c' i' Z r' y).
Proof. exact (MK_COMB (@lem1064491 A i i') (@lem1064490 A B r x' Fn c' i' Z r' y)). Qed.
Lemma lem1064493 {A B : Type'} (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term804 A B i r x' Fn c' i' Z r') = (term788 A B i r x' Fn c' i' Z r').
Proof. exact (fun_ext (fun y : nat -> B => @lem1064492 A B i r x' Fn c' i' Z r' y)). Qed.
Lemma lem1064494 {B : Type'} : (@ex (nat -> B)) = (@ex (nat -> B)).
Proof. exact (eq_refl (@ex (nat -> B))). Qed.
Lemma lem1064495 {A B : Type'} (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term798 A B i r x' Fn c' i' Z r') = (term796 A B i r x' Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1064494 B) (@lem1064493 A B i r x' Fn c' i' Z r')). Qed.
Lemma lem1064496 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1064497 {A B : Type'} (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term805 A B i r x' Fn c' i' Z r') = (term806 A B i r x' Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1064496) (@lem1064495 A B i r x' Fn c' i' Z r')). Qed.
Lemma lem1064498 {A B : Type'} (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y : nat -> B) : (term801 A B r x' Fn c' i' Z r' y) = (term802 A B r x' Fn c' i' Z r' y).
Proof. exact (eq_refl (term801 A B r x' Fn c' i' Z r' y)). Qed.
Lemma lem1064499 {A B : Type'} (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term807 A B r x' Fn c' i' Z r') = (term800 A B r x' Fn c' i' Z r').
Proof. exact (fun_ext (fun y : nat -> B => @lem1064498 A B r x' Fn c' i' Z r' y)). Qed.
Lemma lem1064500 {B : Type'} : (@ex (nat -> B)) = (@ex (nat -> B)).
Proof. exact (eq_refl (@ex (nat -> B))). Qed.
Lemma lem1064501 {A B : Type'} (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term808 A B r x' Fn c' i' Z r') = (term809 A B r x' Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1064500 B) (@lem1064499 A B r x' Fn c' i' Z r')). Qed.
Lemma lem1064502 {A : Type'} (i : A) (i' : A) : (term650 A i i') = (term650 A i i').
Proof. exact (eq_refl (term650 A i i')). Qed.
Lemma lem1064503 {A B : Type'} (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term799 A B i r x' Fn c' i' Z r') = (term810 A B i r x' Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1064502 A i i') (@lem1064501 A B r x' Fn c' i' Z r')). Qed.
Lemma lem1064504 {A B : Type'} (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : ((term798 A B i r x' Fn c' i' Z r') = (term799 A B i r x' Fn c' i' Z r')) = ((term796 A B i r x' Fn c' i' Z r') = (term810 A B i r x' Fn c' i' Z r')).
Proof. exact (MK_COMB (@lem1064497 A B i r x' Fn c' i' Z r') (@lem1064503 A B i r x' Fn c' i' Z r')). Qed.
Lemma lem1064505 {A B : Type'} (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term796 A B i r x' Fn c' i' Z r') = (term810 A B i r x' Fn c' i' Z r').
Proof. exact (EQ_MP (@lem1064504 A B i r x' Fn c' i' Z r') (@lem1064489 A B i r x' Fn c' i' Z r')). Qed.
Lemma lem1064513 {A : Type'} (P : Prop) (Q : A -> Prop) : (term10 A P Q) = (term11 A P Q).
Proof. exact (EQ_MP (@lem1061497 A P Q) (@lem1061496 A P Q)). Qed.
Lemma lem1064514 {B : Type'} (P : Prop) (Q : type976 B) : (term631 B P Q) = (term632 B P Q).
Proof. exact (@lem1064513 (nat -> B) P Q). Qed.
Lemma lem1064515 {A B : Type'} (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term811 A B r x' Fn c' i' Z r') = (term812 A B r x' Fn c' i' Z r').
Proof. exact (@lem1064514 B (r = r') (term813 A B x' Fn c' i' Z r')). Qed.
Lemma lem1064516 {A B : Type'} (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y : nat -> B) : (term814 A B x' Fn c' i' Z r' y) = (term100 A B x' Fn c' i' Z r' y).
Proof. exact (eq_refl (term814 A B x' Fn c' i' Z r' y)). Qed.
Lemma lem1064517 {A : Type'} (r : type1614 A) (r' : type1614 A) : (term663 A r r') = (term663 A r r').
Proof. exact (eq_refl (term663 A r r')). Qed.
Lemma lem1064518 {A B : Type'} (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y : nat -> B) : (term815 A B r x' Fn c' i' Z r' y) = (term802 A B r x' Fn c' i' Z r' y).
Proof. exact (MK_COMB (@lem1064517 A r r') (@lem1064516 A B x' Fn c' i' Z r' y)). Qed.
Lemma lem1064519 {A B : Type'} (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term816 A B r x' Fn c' i' Z r') = (term800 A B r x' Fn c' i' Z r').
Proof. exact (fun_ext (fun y : nat -> B => @lem1064518 A B r x' Fn c' i' Z r' y)). Qed.
Lemma lem1064520 {B : Type'} : (@ex (nat -> B)) = (@ex (nat -> B)).
Proof. exact (eq_refl (@ex (nat -> B))). Qed.
Lemma lem1064521 {A B : Type'} (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term811 A B r x' Fn c' i' Z r') = (term809 A B r x' Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1064520 B) (@lem1064519 A B r x' Fn c' i' Z r')). Qed.
Lemma lem1064522 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1064523 {A B : Type'} (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term817 A B r x' Fn c' i' Z r') = (term818 A B r x' Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1064522) (@lem1064521 A B r x' Fn c' i' Z r')). Qed.
Lemma lem1064524 {A B : Type'} (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) (y : nat -> B) : (term814 A B x' Fn c' i' Z r' y) = (term100 A B x' Fn c' i' Z r' y).
Proof. exact (eq_refl (term814 A B x' Fn c' i' Z r' y)). Qed.
Lemma lem1064525 {A B : Type'} (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term819 A B x' Fn c' i' Z r') = (term813 A B x' Fn c' i' Z r').
Proof. exact (fun_ext (fun y : nat -> B => @lem1064524 A B x' Fn c' i' Z r' y)). Qed.
Lemma lem1064526 {B : Type'} : (@ex (nat -> B)) = (@ex (nat -> B)).
Proof. exact (eq_refl (@ex (nat -> B))). Qed.
Lemma lem1064527 {A B : Type'} (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term820 A B x' Fn c' i' Z r') = (term821 A B x' Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1064526 B) (@lem1064525 A B x' Fn c' i' Z r')). Qed.
Lemma lem1064528 {A : Type'} (r : type1614 A) (r' : type1614 A) : (term663 A r r') = (term663 A r r').
Proof. exact (eq_refl (term663 A r r')). Qed.
Lemma lem1064529 {A B : Type'} (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term812 A B r x' Fn c' i' Z r') = (term822 A B r x' Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1064528 A r r') (@lem1064527 A B x' Fn c' i' Z r')). Qed.
Lemma lem1064530 {A B : Type'} (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : ((term811 A B r x' Fn c' i' Z r') = (term812 A B r x' Fn c' i' Z r')) = ((term809 A B r x' Fn c' i' Z r') = (term822 A B r x' Fn c' i' Z r')).
Proof. exact (MK_COMB (@lem1064523 A B r x' Fn c' i' Z r') (@lem1064529 A B r x' Fn c' i' Z r')). Qed.
Lemma lem1064531 {A B : Type'} (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term809 A B r x' Fn c' i' Z r') = (term822 A B r x' Fn c' i' Z r').
Proof. exact (EQ_MP (@lem1064530 A B r x' Fn c' i' Z r') (@lem1064515 A B r x' Fn c' i' Z r')). Qed.
Lemma lem1064570 {A : Type'} (i : A) (i' : A) : (term650 A i i') = (term650 A i i').
Proof. exact (eq_refl (term650 A i i')). Qed.
Lemma lem1064571 {A B : Type'} (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term810 A B i r x' Fn c' i' Z r') = (term823 A B i r x' Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1064570 A i i') (@lem1064531 A B r x' Fn c' i' Z r')). Qed.
Lemma lem1064574 {A B : Type'} (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term796 A B i r x' Fn c' i' Z r') = (term823 A B i r x' Fn c' i' Z r').
Proof. exact (TRANS (@lem1064505 A B i r x' Fn c' i' Z r') (@lem1064571 A B i r x' Fn c' i' Z r')). Qed.
Lemma lem1064575 (c : nat) (c' : nat) : (term611 c c') = (term611 c c').
Proof. exact (eq_refl (term611 c c')). Qed.
Lemma lem1064576 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term797 A B c i r x' Fn c' i' Z r') = (term824 A B c i r x' Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1064575 c c') (@lem1064574 A B i r x' Fn c' i' Z r')). Qed.
Lemma lem1064579 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term764 A B c i r x' Fn c' i' Z r') = (term824 A B c i r x' Fn c' i' Z r').
Proof. exact (TRANS (@lem1064479 A B c i r x' Fn c' i' Z r') (@lem1064576 A B c i r x' Fn c' i' Z r')). Qed.
Lemma lem1064580 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term766 A B c i r x' Fn c' i' Z) = (term825 A B c i r x' Fn c' i' Z).
Proof. exact (fun_ext (fun r' : type1614 A => @lem1064579 A B c i r x' Fn c' i' Z r')). Qed.
Lemma lem1064581 {A : Type'} : (@ex (nat -> recspace A)) = (@ex (nat -> recspace A)).
Proof. exact (eq_refl (@ex (nat -> recspace A))). Qed.
Lemma lem1064582 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term768 A B c i r x' Fn c' i' Z) = (term826 A B c i r x' Fn c' i' Z).
Proof. exact (MK_COMB (@lem1064581 A) (@lem1064580 A B c i r x' Fn c' i' Z)). Qed.
Lemma lem1064586 {A : Type'} (P : Prop) (Q : A -> Prop) : (term10 A P Q) = (term11 A P Q).
Proof. exact (EQ_MP (@lem1061497 A P Q) (@lem1061496 A P Q)). Qed.
Lemma lem1064587 {A : Type'} (P : Prop) (Q : type963 A) : (term676 A P Q) = (term677 A P Q).
Proof. exact (@lem1064586 (type1614 A) P Q). Qed.
Lemma lem1064588 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term827 A B c i r x' Fn c' i' Z) = (term828 A B c i r x' Fn c' i' Z).
Proof. exact (@lem1064587 A (c = c') (term829 A B i r x' Fn c' i' Z)). Qed.
Lemma lem1064589 {A B : Type'} (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term830 A B i r x' Fn c' i' Z r') = (term823 A B i r x' Fn c' i' Z r').
Proof. exact (eq_refl (term830 A B i r x' Fn c' i' Z r')). Qed.
Lemma lem1064590 (c : nat) (c' : nat) : (term611 c c') = (term611 c c').
Proof. exact (eq_refl (term611 c c')). Qed.
Lemma lem1064591 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term831 A B c i r x' Fn c' i' Z r') = (term824 A B c i r x' Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1064590 c c') (@lem1064589 A B i r x' Fn c' i' Z r')). Qed.
Lemma lem1064592 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term832 A B c i r x' Fn c' i' Z) = (term825 A B c i r x' Fn c' i' Z).
Proof. exact (fun_ext (fun r' : type1614 A => @lem1064591 A B c i r x' Fn c' i' Z r')). Qed.
Lemma lem1064593 {A : Type'} : (@ex (nat -> recspace A)) = (@ex (nat -> recspace A)).
Proof. exact (eq_refl (@ex (nat -> recspace A))). Qed.
Lemma lem1064594 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term827 A B c i r x' Fn c' i' Z) = (term826 A B c i r x' Fn c' i' Z).
Proof. exact (MK_COMB (@lem1064593 A) (@lem1064592 A B c i r x' Fn c' i' Z)). Qed.
Lemma lem1064595 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1064596 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term833 A B c i r x' Fn c' i' Z) = (term834 A B c i r x' Fn c' i' Z).
Proof. exact (MK_COMB (@lem1064595) (@lem1064594 A B c i r x' Fn c' i' Z)). Qed.
Lemma lem1064597 {A B : Type'} (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term830 A B i r x' Fn c' i' Z r') = (term823 A B i r x' Fn c' i' Z r').
Proof. exact (eq_refl (term830 A B i r x' Fn c' i' Z r')). Qed.
Lemma lem1064598 {A B : Type'} (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term835 A B i r x' Fn c' i' Z) = (term829 A B i r x' Fn c' i' Z).
Proof. exact (fun_ext (fun r' : type1614 A => @lem1064597 A B i r x' Fn c' i' Z r')). Qed.
Lemma lem1064599 {A : Type'} : (@ex (nat -> recspace A)) = (@ex (nat -> recspace A)).
Proof. exact (eq_refl (@ex (nat -> recspace A))). Qed.
Lemma lem1064600 {A B : Type'} (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term836 A B i r x' Fn c' i' Z) = (term837 A B i r x' Fn c' i' Z).
Proof. exact (MK_COMB (@lem1064599 A) (@lem1064598 A B i r x' Fn c' i' Z)). Qed.
Lemma lem1064601 (c : nat) (c' : nat) : (term611 c c') = (term611 c c').
Proof. exact (eq_refl (term611 c c')). Qed.
Lemma lem1064602 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term828 A B c i r x' Fn c' i' Z) = (term838 A B c i r x' Fn c' i' Z).
Proof. exact (MK_COMB (@lem1064601 c c') (@lem1064600 A B i r x' Fn c' i' Z)). Qed.
Lemma lem1064603 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : ((term827 A B c i r x' Fn c' i' Z) = (term828 A B c i r x' Fn c' i' Z)) = ((term826 A B c i r x' Fn c' i' Z) = (term838 A B c i r x' Fn c' i' Z)).
Proof. exact (MK_COMB (@lem1064596 A B c i r x' Fn c' i' Z) (@lem1064602 A B c i r x' Fn c' i' Z)). Qed.
Lemma lem1064604 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term826 A B c i r x' Fn c' i' Z) = (term838 A B c i r x' Fn c' i' Z).
Proof. exact (EQ_MP (@lem1064603 A B c i r x' Fn c' i' Z) (@lem1064588 A B c i r x' Fn c' i' Z)). Qed.
Lemma lem1064612 {A : Type'} (P : Prop) (Q : A -> Prop) : (term10 A P Q) = (term11 A P Q).
Proof. exact (EQ_MP (@lem1061497 A P Q) (@lem1061496 A P Q)). Qed.
Lemma lem1064613 {A : Type'} (P : Prop) (Q : type963 A) : (term676 A P Q) = (term677 A P Q).
Proof. exact (@lem1064612 (type1614 A) P Q). Qed.
Lemma lem1064614 {A B : Type'} (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term839 A B i r x' Fn c' i' Z) = (term840 A B i r x' Fn c' i' Z).
Proof. exact (@lem1064613 A (i = i') (term841 A B r x' Fn c' i' Z)). Qed.
Lemma lem1064615 {A B : Type'} (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term842 A B r x' Fn c' i' Z r') = (term822 A B r x' Fn c' i' Z r').
Proof. exact (eq_refl (term842 A B r x' Fn c' i' Z r')). Qed.
Lemma lem1064616 {A : Type'} (i : A) (i' : A) : (term650 A i i') = (term650 A i i').
Proof. exact (eq_refl (term650 A i i')). Qed.
Lemma lem1064617 {A B : Type'} (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term843 A B i r x' Fn c' i' Z r') = (term823 A B i r x' Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1064616 A i i') (@lem1064615 A B r x' Fn c' i' Z r')). Qed.
Lemma lem1064618 {A B : Type'} (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term844 A B i r x' Fn c' i' Z) = (term829 A B i r x' Fn c' i' Z).
Proof. exact (fun_ext (fun r' : type1614 A => @lem1064617 A B i r x' Fn c' i' Z r')). Qed.
Lemma lem1064619 {A : Type'} : (@ex (nat -> recspace A)) = (@ex (nat -> recspace A)).
Proof. exact (eq_refl (@ex (nat -> recspace A))). Qed.
Lemma lem1064620 {A B : Type'} (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term839 A B i r x' Fn c' i' Z) = (term837 A B i r x' Fn c' i' Z).
Proof. exact (MK_COMB (@lem1064619 A) (@lem1064618 A B i r x' Fn c' i' Z)). Qed.
Lemma lem1064621 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1064622 {A B : Type'} (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term845 A B i r x' Fn c' i' Z) = (term846 A B i r x' Fn c' i' Z).
Proof. exact (MK_COMB (@lem1064621) (@lem1064620 A B i r x' Fn c' i' Z)). Qed.
Lemma lem1064623 {A B : Type'} (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term842 A B r x' Fn c' i' Z r') = (term822 A B r x' Fn c' i' Z r').
Proof. exact (eq_refl (term842 A B r x' Fn c' i' Z r')). Qed.
Lemma lem1064624 {A B : Type'} (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term847 A B r x' Fn c' i' Z) = (term841 A B r x' Fn c' i' Z).
Proof. exact (fun_ext (fun r' : type1614 A => @lem1064623 A B r x' Fn c' i' Z r')). Qed.
Lemma lem1064625 {A : Type'} : (@ex (nat -> recspace A)) = (@ex (nat -> recspace A)).
Proof. exact (eq_refl (@ex (nat -> recspace A))). Qed.
Lemma lem1064626 {A B : Type'} (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term848 A B r x' Fn c' i' Z) = (term849 A B r x' Fn c' i' Z).
Proof. exact (MK_COMB (@lem1064625 A) (@lem1064624 A B r x' Fn c' i' Z)). Qed.
Lemma lem1064627 {A : Type'} (i : A) (i' : A) : (term650 A i i') = (term650 A i i').
Proof. exact (eq_refl (term650 A i i')). Qed.
Lemma lem1064628 {A B : Type'} (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term840 A B i r x' Fn c' i' Z) = (term850 A B i r x' Fn c' i' Z).
Proof. exact (MK_COMB (@lem1064627 A i i') (@lem1064626 A B r x' Fn c' i' Z)). Qed.
Lemma lem1064629 {A B : Type'} (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : ((term839 A B i r x' Fn c' i' Z) = (term840 A B i r x' Fn c' i' Z)) = ((term837 A B i r x' Fn c' i' Z) = (term850 A B i r x' Fn c' i' Z)).
Proof. exact (MK_COMB (@lem1064622 A B i r x' Fn c' i' Z) (@lem1064628 A B i r x' Fn c' i' Z)). Qed.
Lemma lem1064630 {A B : Type'} (i : A) (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term837 A B i r x' Fn c' i' Z) = (term850 A B i r x' Fn c' i' Z).
Proof. exact (EQ_MP (@lem1064629 A B i r x' Fn c' i' Z) (@lem1064614 A B i r x' Fn c' i' Z)). Qed.
Lemma lem1064636 {A : Type'} (P : A -> Prop) (a : A) : (term15 A a P) = (P a).
Proof. exact (EQ_MP (@lem1061503 A P a) (@lem1061502 A P a)). Qed.
Lemma lem1064637 {A : Type'} (P : type963 A) (a : type1614 A) : (term702 A a P) = (P a).
Proof. exact (@lem1064636 (type1614 A) P a). Qed.
Lemma lem1064638 {A B : Type'} (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r : type1614 A) : (term851 A B r x' Fn c' i' Z) = (term852 A B x' Fn c' i' Z r).
Proof. exact (@lem1064637 A (term853 A B x' Fn c' i' Z) r). Qed.
Lemma lem1064639 {A B : Type'} (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term852 A B x' Fn c' i' Z r') = (term821 A B x' Fn c' i' Z r').
Proof. exact (eq_refl (term852 A B x' Fn c' i' Z r')). Qed.
Lemma lem1064640 {A : Type'} (r : type1614 A) (r' : type1614 A) : (term663 A r r') = (term663 A r r').
Proof. exact (eq_refl (term663 A r r')). Qed.
Lemma lem1064641 {A B : Type'} (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r' : type1614 A) : (term854 A B r x' Fn c' i' Z r') = (term822 A B r x' Fn c' i' Z r').
Proof. exact (MK_COMB (@lem1064640 A r r') (@lem1064639 A B x' Fn c' i' Z r')). Qed.
Lemma lem1064642 {A B : Type'} (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term855 A B r x' Fn c' i' Z) = (term841 A B r x' Fn c' i' Z).
Proof. exact (fun_ext (fun r' : type1614 A => @lem1064641 A B r x' Fn c' i' Z r')). Qed.
Lemma lem1064643 {A : Type'} : (@ex (nat -> recspace A)) = (@ex (nat -> recspace A)).
Proof. exact (eq_refl (@ex (nat -> recspace A))). Qed.
Lemma lem1064644 {A B : Type'} (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term851 A B r x' Fn c' i' Z) = (term849 A B r x' Fn c' i' Z).
Proof. exact (MK_COMB (@lem1064643 A) (@lem1064642 A B r x' Fn c' i' Z)). Qed.
Lemma lem1064645 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1064646 {A B : Type'} (r : type1614 A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) : (term856 A B r x' Fn c' i' Z) = (term857 A B r x' Fn c' i' Z).
Proof. exact (MK_COMB (@lem1064645) (@lem1064644 A B r x' Fn c' i' Z)). Qed.
Lemma lem1064647 {A B : Type'} (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r : type1614 A) : (term852 A B x' Fn c' i' Z r) = (term821 A B x' Fn c' i' Z r).
Proof. exact (eq_refl (term852 A B x' Fn c' i' Z r)). Qed.
Lemma lem1064648 {A B : Type'} (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r : type1614 A) : ((term851 A B r x' Fn c' i' Z) = (term852 A B x' Fn c' i' Z r)) = ((term849 A B r x' Fn c' i' Z) = (term821 A B x' Fn c' i' Z r)).
Proof. exact (MK_COMB (@lem1064646 A B r x' Fn c' i' Z) (@lem1064647 A B x' Fn c' i' Z r)). Qed.
Lemma lem1064649 {A B : Type'} (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r : type1614 A) : (term849 A B r x' Fn c' i' Z) = (term821 A B x' Fn c' i' Z r).
Proof. exact (EQ_MP (@lem1064648 A B x' Fn c' i' Z r) (@lem1064638 A B x' Fn c' i' Z r)). Qed.
Lemma lem1064684 {A : Type'} (i : A) (i' : A) : (term650 A i i') = (term650 A i i').
Proof. exact (eq_refl (term650 A i i')). Qed.
Lemma lem1064685 {A B : Type'} (i : A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r : type1614 A) : (term850 A B i r x' Fn c' i' Z) = (term858 A B i x' Fn c' i' Z r).
Proof. exact (MK_COMB (@lem1064684 A i i') (@lem1064649 A B x' Fn c' i' Z r)). Qed.
Lemma lem1064688 {A B : Type'} (i : A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r : type1614 A) : (term837 A B i r x' Fn c' i' Z) = (term858 A B i x' Fn c' i' Z r).
Proof. exact (TRANS (@lem1064630 A B i r x' Fn c' i' Z) (@lem1064685 A B i x' Fn c' i' Z r)). Qed.
Lemma lem1064689 (c : nat) (c' : nat) : (term611 c c') = (term611 c c').
Proof. exact (eq_refl (term611 c c')). Qed.
Lemma lem1064690 {A B : Type'} (c : nat) (i : A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r : type1614 A) : (term838 A B c i r x' Fn c' i' Z) = (term859 A B c i x' Fn c' i' Z r).
Proof. exact (MK_COMB (@lem1064689 c c') (@lem1064688 A B i x' Fn c' i' Z r)). Qed.
Lemma lem1064693 {A B : Type'} (c : nat) (i : A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r : type1614 A) : (term826 A B c i r x' Fn c' i' Z) = (term859 A B c i x' Fn c' i' Z r).
Proof. exact (TRANS (@lem1064604 A B c i r x' Fn c' i' Z) (@lem1064690 A B c i x' Fn c' i' Z r)). Qed.
Lemma lem1064694 {A B : Type'} (c : nat) (i : A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r : type1614 A) : (term768 A B c i r x' Fn c' i' Z) = (term859 A B c i x' Fn c' i' Z r).
Proof. exact (TRANS (@lem1064582 A B c i r x' Fn c' i' Z) (@lem1064693 A B c i x' Fn c' i' Z r)). Qed.
Lemma lem1064695 {A B : Type'} (c : nat) (i : A) (x' : B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) (r : type1614 A) : (term770 A B c i r x' Fn c' Z) = (term860 A B c i x' Fn c' Z r).
Proof. exact (fun_ext (fun i' : A => @lem1064694 A B c i x' Fn c' i' Z r)). Qed.
Lemma lem1064696 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1064697 {A B : Type'} (c : nat) (i : A) (x' : B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) (r : type1614 A) : (term772 A B c i r x' Fn c' Z) = (term861 A B c i x' Fn c' Z r).
Proof. exact (MK_COMB (@lem1064696 A) (@lem1064695 A B c i x' Fn c' Z r)). Qed.
Lemma lem1064701 {A : Type'} (P : Prop) (Q : A -> Prop) : (term10 A P Q) = (term11 A P Q).
Proof. exact (EQ_MP (@lem1061497 A P Q) (@lem1061496 A P Q)). Qed.
Lemma lem1064702 {A : Type'} (P : Prop) (Q : A -> Prop) : (term10 A P Q) = (term11 A P Q).
Proof. exact (@lem1064701 A P Q). Qed.
Lemma lem1064703 {A B : Type'} (c : nat) (i : A) (x' : B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) (r : type1614 A) : (term862 A B c i x' Fn c' Z r) = (term863 A B c i x' Fn c' Z r).
Proof. exact (@lem1064702 A (c = c') (term864 A B i x' Fn c' Z r)). Qed.
Lemma lem1064704 {A B : Type'} (i : A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r : type1614 A) : (term865 A B i x' Fn c' Z r i') = (term858 A B i x' Fn c' i' Z r).
Proof. exact (eq_refl (term865 A B i x' Fn c' Z r i')). Qed.
Lemma lem1064705 (c : nat) (c' : nat) : (term611 c c') = (term611 c c').
Proof. exact (eq_refl (term611 c c')). Qed.
Lemma lem1064706 {A B : Type'} (c : nat) (i : A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r : type1614 A) : (term866 A B c i x' Fn c' Z r i') = (term859 A B c i x' Fn c' i' Z r).
Proof. exact (MK_COMB (@lem1064705 c c') (@lem1064704 A B i x' Fn c' i' Z r)). Qed.
Lemma lem1064707 {A B : Type'} (c : nat) (i : A) (x' : B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) (r : type1614 A) : (term867 A B c i x' Fn c' Z r) = (term860 A B c i x' Fn c' Z r).
Proof. exact (fun_ext (fun i' : A => @lem1064706 A B c i x' Fn c' i' Z r)). Qed.
Lemma lem1064708 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1064709 {A B : Type'} (c : nat) (i : A) (x' : B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) (r : type1614 A) : (term862 A B c i x' Fn c' Z r) = (term861 A B c i x' Fn c' Z r).
Proof. exact (MK_COMB (@lem1064708 A) (@lem1064707 A B c i x' Fn c' Z r)). Qed.
Lemma lem1064710 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1064711 {A B : Type'} (c : nat) (i : A) (x' : B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) (r : type1614 A) : (term868 A B c i x' Fn c' Z r) = (term869 A B c i x' Fn c' Z r).
Proof. exact (MK_COMB (@lem1064710) (@lem1064709 A B c i x' Fn c' Z r)). Qed.
Lemma lem1064712 {A B : Type'} (i : A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r : type1614 A) : (term865 A B i x' Fn c' Z r i') = (term858 A B i x' Fn c' i' Z r).
Proof. exact (eq_refl (term865 A B i x' Fn c' Z r i')). Qed.
Lemma lem1064713 {A B : Type'} (i : A) (x' : B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) (r : type1614 A) : (term870 A B i x' Fn c' Z r) = (term864 A B i x' Fn c' Z r).
Proof. exact (fun_ext (fun i' : A => @lem1064712 A B i x' Fn c' i' Z r)). Qed.
Lemma lem1064714 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1064715 {A B : Type'} (i : A) (x' : B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) (r : type1614 A) : (term871 A B i x' Fn c' Z r) = (term872 A B i x' Fn c' Z r).
Proof. exact (MK_COMB (@lem1064714 A) (@lem1064713 A B i x' Fn c' Z r)). Qed.
Lemma lem1064716 (c : nat) (c' : nat) : (term611 c c') = (term611 c c').
Proof. exact (eq_refl (term611 c c')). Qed.
Lemma lem1064717 {A B : Type'} (c : nat) (i : A) (x' : B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) (r : type1614 A) : (term863 A B c i x' Fn c' Z r) = (term873 A B c i x' Fn c' Z r).
Proof. exact (MK_COMB (@lem1064716 c c') (@lem1064715 A B i x' Fn c' Z r)). Qed.
Lemma lem1064718 {A B : Type'} (c : nat) (i : A) (x' : B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) (r : type1614 A) : ((term862 A B c i x' Fn c' Z r) = (term863 A B c i x' Fn c' Z r)) = ((term861 A B c i x' Fn c' Z r) = (term873 A B c i x' Fn c' Z r)).
Proof. exact (MK_COMB (@lem1064711 A B c i x' Fn c' Z r) (@lem1064717 A B c i x' Fn c' Z r)). Qed.
Lemma lem1064719 {A B : Type'} (c : nat) (i : A) (x' : B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) (r : type1614 A) : (term861 A B c i x' Fn c' Z r) = (term873 A B c i x' Fn c' Z r).
Proof. exact (EQ_MP (@lem1064718 A B c i x' Fn c' Z r) (@lem1064703 A B c i x' Fn c' Z r)). Qed.
Lemma lem1064725 {A : Type'} (P : A -> Prop) (a : A) : (term15 A a P) = (P a).
Proof. exact (EQ_MP (@lem1061503 A P a) (@lem1061502 A P a)). Qed.
Lemma lem1064726 {A : Type'} (P : A -> Prop) (a : A) : (term15 A a P) = (P a).
Proof. exact (@lem1064725 A P a). Qed.
Lemma lem1064727 {A B : Type'} (x' : B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) (r : type1614 A) (i : A) : (term874 A B i x' Fn c' Z r) = (term875 A B x' Fn c' Z r i).
Proof. exact (@lem1064726 A (term876 A B x' Fn c' Z r) i). Qed.
Lemma lem1064728 {A B : Type'} (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r : type1614 A) : (term875 A B x' Fn c' Z r i') = (term821 A B x' Fn c' i' Z r).
Proof. exact (eq_refl (term875 A B x' Fn c' Z r i')). Qed.
Lemma lem1064729 {A : Type'} (i : A) (i' : A) : (term650 A i i') = (term650 A i i').
Proof. exact (eq_refl (term650 A i i')). Qed.
Lemma lem1064730 {A B : Type'} (i : A) (x' : B) (Fn : type1592 A B) (c' : nat) (i' : A) (Z : type1336 A B) (r : type1614 A) : (term877 A B i x' Fn c' Z r i') = (term858 A B i x' Fn c' i' Z r).
Proof. exact (MK_COMB (@lem1064729 A i i') (@lem1064728 A B x' Fn c' i' Z r)). Qed.
Lemma lem1064731 {A B : Type'} (i : A) (x' : B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) (r : type1614 A) : (term878 A B i x' Fn c' Z r) = (term864 A B i x' Fn c' Z r).
Proof. exact (fun_ext (fun i' : A => @lem1064730 A B i x' Fn c' i' Z r)). Qed.
Lemma lem1064732 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1064733 {A B : Type'} (i : A) (x' : B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) (r : type1614 A) : (term874 A B i x' Fn c' Z r) = (term872 A B i x' Fn c' Z r).
Proof. exact (MK_COMB (@lem1064732 A) (@lem1064731 A B i x' Fn c' Z r)). Qed.
Lemma lem1064734 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1064735 {A B : Type'} (i : A) (x' : B) (Fn : type1592 A B) (c' : nat) (Z : type1336 A B) (r : type1614 A) : (term879 A B i x' Fn c' Z r) = (term880 A B i x' Fn c' Z r).
Proof. exact (MK_COMB (@lem1064734) (@lem1064733 A B i x' Fn c' Z r)). Qed.
Lemma lem1064736 {A B : Type'} (x' : B) (Fn : type1592 A B) (c' : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : (term875 A B x' Fn c' Z r i) = (term821 A B x' Fn c' i Z r).
Proof. exact (eq_refl (term875 A B x' Fn c' Z r i)). Qed.
Lemma lem1064737 {A B : Type'} (x' : B) (Fn : type1592 A B) (c' : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : ((term874 A B i x' Fn c' Z r) = (term875 A B x' Fn c' Z r i)) = ((term872 A B i x' Fn c' Z r) = (term821 A B x' Fn c' i Z r)).
Proof. exact (MK_COMB (@lem1064735 A B i x' Fn c' Z r) (@lem1064736 A B x' Fn c' i Z r)). Qed.
Lemma lem1064738 {A B : Type'} (x' : B) (Fn : type1592 A B) (c' : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : (term872 A B i x' Fn c' Z r) = (term821 A B x' Fn c' i Z r).
Proof. exact (EQ_MP (@lem1064737 A B x' Fn c' i Z r) (@lem1064727 A B x' Fn c' Z r i)). Qed.
Lemma lem1064773 (c : nat) (c' : nat) : (term611 c c') = (term611 c c').
Proof. exact (eq_refl (term611 c c')). Qed.
Lemma lem1064774 {A B : Type'} (c : nat) (x' : B) (Fn : type1592 A B) (c' : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : (term873 A B c i x' Fn c' Z r) = (term881 A B c x' Fn c' i Z r).
Proof. exact (MK_COMB (@lem1064773 c c') (@lem1064738 A B x' Fn c' i Z r)). Qed.
Lemma lem1064777 {A B : Type'} (c : nat) (x' : B) (Fn : type1592 A B) (c' : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : (term861 A B c i x' Fn c' Z r) = (term881 A B c x' Fn c' i Z r).
Proof. exact (TRANS (@lem1064719 A B c i x' Fn c' Z r) (@lem1064774 A B c x' Fn c' i Z r)). Qed.
Lemma lem1064778 {A B : Type'} (c : nat) (x' : B) (Fn : type1592 A B) (c' : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : (term772 A B c i r x' Fn c' Z) = (term881 A B c x' Fn c' i Z r).
Proof. exact (TRANS (@lem1064697 A B c i x' Fn c' Z r) (@lem1064777 A B c x' Fn c' i Z r)). Qed.
Lemma lem1064779 {A B : Type'} (c : nat) (x' : B) (Fn : type1592 A B) (i : A) (Z : type1336 A B) (r : type1614 A) : (term774 A B c i r x' Fn Z) = (term882 A B c x' Fn i Z r).
Proof. exact (fun_ext (fun c' : nat => @lem1064778 A B c x' Fn c' i Z r)). Qed.
Lemma lem1064780 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1064781 {A B : Type'} (c : nat) (x' : B) (Fn : type1592 A B) (i : A) (Z : type1336 A B) (r : type1614 A) : (term776 A B c i r x' Fn Z) = (term883 A B c x' Fn i Z r).
Proof. exact (MK_COMB (@lem1064780) (@lem1064779 A B c x' Fn i Z r)). Qed.
Lemma lem1064783 {A : Type'} (P : A -> Prop) (a : A) : (term15 A a P) = (P a).
Proof. exact (EQ_MP (@lem1061503 A P a) (@lem1061502 A P a)). Qed.
Lemma lem1064784 (P : nat -> Prop) (a : nat) : (term740 a P) = (P a).
Proof. exact (@lem1064783 nat P a). Qed.
Lemma lem1064785 {A B : Type'} (x' : B) (Fn : type1592 A B) (i : A) (Z : type1336 A B) (r : type1614 A) (c : nat) : (term884 A B c x' Fn i Z r) = (term885 A B x' Fn i Z r c).
Proof. exact (@lem1064784 (term886 A B x' Fn i Z r) c). Qed.
Lemma lem1064786 {A B : Type'} (x' : B) (Fn : type1592 A B) (c' : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : (term885 A B x' Fn i Z r c') = (term821 A B x' Fn c' i Z r).
Proof. exact (eq_refl (term885 A B x' Fn i Z r c')). Qed.
Lemma lem1064787 (c : nat) (c' : nat) : (term611 c c') = (term611 c c').
Proof. exact (eq_refl (term611 c c')). Qed.
Lemma lem1064788 {A B : Type'} (c : nat) (x' : B) (Fn : type1592 A B) (c' : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : (term887 A B c x' Fn i Z r c') = (term881 A B c x' Fn c' i Z r).
Proof. exact (MK_COMB (@lem1064787 c c') (@lem1064786 A B x' Fn c' i Z r)). Qed.
Lemma lem1064789 {A B : Type'} (c : nat) (x' : B) (Fn : type1592 A B) (i : A) (Z : type1336 A B) (r : type1614 A) : (term888 A B c x' Fn i Z r) = (term882 A B c x' Fn i Z r).
Proof. exact (fun_ext (fun c' : nat => @lem1064788 A B c x' Fn c' i Z r)). Qed.
Lemma lem1064790 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1064791 {A B : Type'} (c : nat) (x' : B) (Fn : type1592 A B) (i : A) (Z : type1336 A B) (r : type1614 A) : (term884 A B c x' Fn i Z r) = (term883 A B c x' Fn i Z r).
Proof. exact (MK_COMB (@lem1064790) (@lem1064789 A B c x' Fn i Z r)). Qed.
Lemma lem1064792 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1064793 {A B : Type'} (c : nat) (x' : B) (Fn : type1592 A B) (i : A) (Z : type1336 A B) (r : type1614 A) : (term889 A B c x' Fn i Z r) = (term890 A B c x' Fn i Z r).
Proof. exact (MK_COMB (@lem1064792) (@lem1064791 A B c x' Fn i Z r)). Qed.
Lemma lem1064794 {A B : Type'} (x' : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : (term885 A B x' Fn i Z r c) = (term821 A B x' Fn c i Z r).
Proof. exact (eq_refl (term885 A B x' Fn i Z r c)). Qed.
Lemma lem1064795 {A B : Type'} (x' : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : ((term884 A B c x' Fn i Z r) = (term885 A B x' Fn i Z r c)) = ((term883 A B c x' Fn i Z r) = (term821 A B x' Fn c i Z r)).
Proof. exact (MK_COMB (@lem1064793 A B c x' Fn i Z r) (@lem1064794 A B x' Fn c i Z r)). Qed.
Lemma lem1064796 {A B : Type'} (x' : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : (term883 A B c x' Fn i Z r) = (term821 A B x' Fn c i Z r).
Proof. exact (EQ_MP (@lem1064795 A B x' Fn c i Z r) (@lem1064785 A B x' Fn i Z r c)). Qed.
Lemma lem1064831 {A B : Type'} (x' : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : (term776 A B c i r x' Fn Z) = (term821 A B x' Fn c i Z r).
Proof. exact (TRANS (@lem1064781 A B c x' Fn i Z r) (@lem1064796 A B x' Fn c i Z r)). Qed.
Lemma lem1064832 {A B : Type'} (y : B) (x' : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : (term779 A B y c i r x' Fn Z) = (term892 A B y x' Fn c i Z r).
Proof. exact (MK_COMB (@lem1064445 A B y Fn c i Z r) (@lem1064831 A B x' Fn c i Z r)). Qed.
Lemma lem1064835 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1064836 {A B : Type'} (y : B) (x' : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : (term780 A B y c i r x' Fn Z) = (term893 A B y x' Fn c i Z r).
Proof. exact (MK_COMB (@lem1064835) (@lem1064832 A B y x' Fn c i Z r)). Qed.
Lemma lem1064839 {B : Type'} (y : B) (x' : B) : (y = x') = (y = x').
Proof. exact (eq_refl (y = x')). Qed.
Lemma lem1064840 {A B : Type'} (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (y : B) (x' : B) : (term781 A B c i r Fn Z y x') = (term894 A B Fn c i Z r y x').
Proof. exact (MK_COMB (@lem1064836 A B y x' Fn c i Z r) (@lem1064839 B y x')). Qed.
Lemma lem1064843 {A B : Type'} (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (y : B) : (term782 A B c i r Fn Z y) = (term895 A B Fn c i Z r y).
Proof. exact (fun_ext (fun x' : B => @lem1064840 A B Fn c i Z r y x')). Qed.
Lemma lem1064844 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1064845 {A B : Type'} (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (y : B) : (term783 A B c i r Fn Z y) = (term896 A B Fn c i Z r y).
Proof. exact (MK_COMB (@lem1064844 B) (@lem1064843 A B Fn c i Z r y)). Qed.
Lemma lem1064850 {A B : Type'} (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : (term784 A B c i r Fn Z) = (term897 A B Fn c i Z r).
Proof. exact (fun_ext (fun y : B => @lem1064845 A B Fn c i Z r y)). Qed.
Lemma lem1064851 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1064852 {A B : Type'} (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) : (term785 A B c i r Fn Z) = (term898 A B Fn c i Z r).
Proof. exact (MK_COMB (@lem1064851 B) (@lem1064850 A B Fn c i Z r)). Qed.
Lemma lem1064857 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (Fn : type1592 A B) (Z : type1336 A B) : (term898 A B Fn c i Z r) = (term785 A B c i r Fn Z).
Proof. exact (SYM (@lem1064852 A B Fn c i Z r)). Qed.
Lemma lem1064858 {A B : Type'} (y' : B) (x' : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (h1 : term892 A B y' x' Fn c i Z r) : term892 A B y' x' Fn c i Z r.
Proof. exact (h1). Qed.
Lemma lem1064859 {A B : Type'} (x' : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (h1 : term821 A B x' Fn c i Z r) : term821 A B x' Fn c i Z r.
Proof. exact (h1). Qed.
Lemma lem1064860 {A B : Type'} (y' : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (h1 : term821 A B y' Fn c i Z r) : term821 A B y' Fn c i Z r.
Proof. exact (h1). Qed.
Lemma lem1064861 {A B : Type'} (y' : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (y'' : nat -> B) (h1 : term100 A B y' Fn c i Z r y'') : term100 A B y' Fn c i Z r y''.
Proof. exact (h1). Qed.
Lemma lem1064862 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (y'' : nat -> B) (h1 : term101 A B Z r y'') : term101 A B Z r y''.
Proof. exact (h1). Qed.
Lemma lem1064863 {A B : Type'} (y' : B) (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (y'' : nat -> B) (h1 : y' = (Fn c i r y'')) : y' = (Fn c i r y'').
Proof. exact (h1). Qed.
Lemma lem1064864 {A B : Type'} (x' : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (y''' : nat -> B) (h1 : term100 A B x' Fn c i Z r y''') : term100 A B x' Fn c i Z r y'''.
Proof. exact (h1). Qed.
Lemma lem1064865 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (y''' : nat -> B) (h1 : term101 A B Z r y''') : term101 A B Z r y'''.
Proof. exact (h1). Qed.
Lemma lem1064866 {A B : Type'} (x' : B) (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (y''' : nat -> B) (h1 : x' = (Fn c i r y''')) : x' = (Fn c i r y''').
Proof. exact (h1). Qed.
Lemma lem1064923 {A B : Type'} (y' : B) (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (y'' : nat -> B) (h1 : y' = (Fn c i r y'')) : y' = (Fn c i r y'').
Proof. exact (h1). Qed.
Lemma lem1064924 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem1064925 {A B : Type'} (y' : B) (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (y'' : nat -> B) (h1 : y' = (Fn c i r y'')) : (@eq B y') = (term899 A B Fn c i r y'').
Proof. exact (MK_COMB (@lem1064924 B) (@lem1064923 A B y' Fn c i r y'' h1)). Qed.
Lemma lem1064927 {A B : Type'} (x' : B) (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (y''' : nat -> B) (h1 : x' = (Fn c i r y''')) : x' = (Fn c i r y''').
Proof. exact (h1). Qed.
Lemma lem1064928 {A B : Type'} (x' : B) (y''' : nat -> B) (y' : B) (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (y'' : nat -> B) (h1 : x' = (Fn c i r y''')) (h2 : y' = (Fn c i r y'')) : (y' = x') = ((Fn c i r y'') = (Fn c i r y''')).
Proof. exact (MK_COMB (@lem1064925 A B y' Fn c i r y'' h2) (@lem1064927 A B x' Fn c i r y''' h1)). Qed.
Lemma lem1064931 {A B : Type'} (x' : B) (y''' : nat -> B) (y' : B) (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (y'' : nat -> B) (h1 : x' = (Fn c i r y''')) (h2 : y' = (Fn c i r y'')) : ((Fn c i r y'') = (Fn c i r y''')) = (y' = x').
Proof. exact (SYM (@lem1064928 A B x' y''' y' Fn c i r y'' h1 h2)). Qed.
Lemma lem1064932 {A B : Type'} (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) : (Fn c i r) = (Fn c i r).
Proof. exact (eq_refl (Fn c i r)). Qed.
Lemma lem1064936 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term6 A B f g).
Proof. exact (EQ_MP (@lem1061491 A B f g) (@lem1061490 A B f g)). Qed.
Lemma lem1064937 {B : Type'} (f : nat -> B) (g : nat -> B) : (f = g) = (term900 B f g).
Proof. exact (@lem1064936 nat B f g). Qed.
Lemma lem1064938 {B : Type'} (y'' : nat -> B) (y''' : nat -> B) : (y'' = y''') = (term900 B y'' y''').
Proof. exact (@lem1064937 B y'' y'''). Qed.
Lemma lem1064939 {B : Type'} (y'' : nat -> B) (y''' : nat -> B) : (term900 B y'' y''') = (y'' = y''').
Proof. exact (SYM (@lem1064938 B y'' y''')). Qed.
Lemma lem1064940 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (h1 : term535 A B Z r) : term535 A B Z r.
Proof. exact (h1). Qed.
Lemma lem1064941 {A B : Type'} (n : nat) (Z : type1336 A B) (r : type1614 A) (h1 : term535 A B Z r) : term523 A B Z r n.
Proof. exact (@lem1064940 A B Z r h1 n). Qed.
Lemma lem1064942 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (n : nat) : (term523 A B Z r n) = (term511 A B Z r n).
Proof. exact (eq_refl (term523 A B Z r n)). Qed.
Lemma lem1064943 {A B : Type'} (n : nat) (Z : type1336 A B) (r : type1614 A) (h1 : term535 A B Z r) : term511 A B Z r n.
Proof. exact (EQ_MP (@lem1064942 A B Z r n) (@lem1064941 A B n Z r h1)). Qed.
Lemma lem1064944 {A B : Type'} (n : nat) (y : B) (Z : type1336 A B) (r : type1614 A) (h1 : term535 A B Z r) : term901 A B Z r n y.
Proof. exact (@lem1064943 A B n Z r h1 y). Qed.
Lemma lem1064945 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (n : nat) (y : B) : (term901 A B Z r n y) = (term507 A B Z r n y).
Proof. exact (eq_refl (term901 A B Z r n y)). Qed.
Lemma lem1064946 {A B : Type'} (n : nat) (y : B) (Z : type1336 A B) (r : type1614 A) (h1 : term535 A B Z r) : term507 A B Z r n y.
Proof. exact (EQ_MP (@lem1064945 A B Z r n y) (@lem1064944 A B n y Z r h1)). Qed.
Lemma lem1064947 {A B : Type'} (n : nat) (y : B) (x' : B) (Z : type1336 A B) (r : type1614 A) (h1 : term535 A B Z r) : term902 A B Z r n y x'.
Proof. exact (@lem1064946 A B n y Z r h1 x'). Qed.
Lemma lem1064948 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (n : nat) (y : B) (x' : B) : (term902 A B Z r n y x') = (term503 A B Z r n y x').
Proof. exact (eq_refl (term902 A B Z r n y x')). Qed.
Lemma lem1064949 {A B : Type'} (n : nat) (y : B) (x' : B) (Z : type1336 A B) (r : type1614 A) (h1 : term535 A B Z r) : term503 A B Z r n y x'.
Proof. exact (EQ_MP (@lem1064948 A B Z r n y x') (@lem1064947 A B n y x' Z r h1)). Qed.
Lemma lem1064950 {A B : Type'} (y : B) (Z : type1336 A B) (r : type1614 A) (n : nat) (x' : B) (h1 : term499 A B y Z r n x') : term499 A B y Z r n x'.
Proof. exact (h1). Qed.
Lemma lem1064951 {A B : Type'} (y : B) (Z : type1336 A B) (r : type1614 A) (n : nat) (x' : B) (h1 : term535 A B Z r) (h2 : term499 A B y Z r n x') : y = x'.
Proof. exact (@lem1064949 A B n y x' Z r h1 (@lem1064950 A B y Z r n x' h2)). Qed.
Lemma lem1064952 {A B : Type'} (y : B) (Z : type1336 A B) (r : type1614 A) (n : nat) (x' : B) (h1 : term499 A B y Z r n x') : term903 A B Z r y x'.
Proof. exact (fun h0 : term535 A B Z r => @lem1064951 A B y Z r n x' h0 h1). Qed.
Lemma lem1064953 {A B : Type'} (y : B) (Z : type1336 A B) (r : type1614 A) (x' : B) (h1 : term904 A B y Z r x') : term904 A B y Z r x'.
Proof. exact (h1). Qed.
Lemma lem1064954 {A B : Type'} (y : B) (Z : type1336 A B) (r : type1614 A) (x' : B) (h1 : term904 A B y Z r x') : term903 A B Z r y x'.
Proof. exact (ex_elim (@lem1064953 A B y Z r x' h1) (fun n : nat => fun h0 : term905 A B y Z r x' n => @lem1064952 A B y Z r n x' h0)). Qed.
Lemma lem1064955 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (h1 : term535 A B Z r) : term535 A B Z r.
Proof. exact (h1). Qed.
Lemma lem1064956 {A B : Type'} (y : B) (Z : type1336 A B) (r : type1614 A) (x' : B) (h1 : term535 A B Z r) (h2 : term904 A B y Z r x') : y = x'.
Proof. exact (@lem1064954 A B y Z r x' h2 (@lem1064955 A B Z r h1)). Qed.
Lemma lem1064957 {A B : Type'} (y : B) (x' : B) (Z : type1336 A B) (r : type1614 A) (h1 : term535 A B Z r) : term906 A B Z r y x'.
Proof. exact (fun h0 : term904 A B y Z r x' => @lem1064956 A B y Z r x' h1 h0). Qed.
Lemma lem1064958 {A B : Type'} (y : B) (Z : type1336 A B) (r : type1614 A) (h1 : term535 A B Z r) : term907 A B Z r y.
Proof. exact (fun x' : B => @lem1064957 A B y x' Z r h1). Qed.
Lemma lem1064959 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (h1 : term535 A B Z r) : term908 A B Z r.
Proof. exact (fun y : B => @lem1064958 A B y Z r h1). Qed.
Lemma lem1064960 {A B : Type'} (Z : type1336 A B) (r : type1614 A) : term909 A B Z r.
Proof. exact (fun h0 : term535 A B Z r => @lem1064959 A B Z r h0). Qed.
Lemma lem1064961 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (h1 : term535 A B Z r) : term908 A B Z r.
Proof. exact (@lem1064960 A B Z r (@lem1062791 A B Z r h1)). Qed.
Lemma lem1064962 {A B : Type'} (y : B) (Z : type1336 A B) (r : type1614 A) (h1 : term535 A B Z r) : term910 A B Z r y.
Proof. exact (@lem1064961 A B Z r h1 y). Qed.
Lemma lem1064963 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (y : B) : (term910 A B Z r y) = (term907 A B Z r y).
Proof. exact (eq_refl (term910 A B Z r y)). Qed.
Lemma lem1064964 {A B : Type'} (y : B) (Z : type1336 A B) (r : type1614 A) (h1 : term535 A B Z r) : term907 A B Z r y.
Proof. exact (EQ_MP (@lem1064963 A B Z r y) (@lem1064962 A B y Z r h1)). Qed.
Lemma lem1064965 {A B : Type'} (y : B) (x' : B) (Z : type1336 A B) (r : type1614 A) (h1 : term535 A B Z r) : term911 A B Z r y x'.
Proof. exact (@lem1064964 A B y Z r h1 x'). Qed.
Lemma lem1064966 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (y : B) (x' : B) : (term911 A B Z r y x') = (term906 A B Z r y x').
Proof. exact (eq_refl (term911 A B Z r y x')). Qed.
Lemma lem1064969 {A B : Type'} (y : B) (x' : B) (Z : type1336 A B) (r : type1614 A) (h1 : term535 A B Z r) : term906 A B Z r y x'.
Proof. exact (EQ_MP (@lem1064966 A B Z r y x') (@lem1064965 A B y x' Z r h1)). Qed.
Lemma lem1064970 {A B : Type'} (y : B) (x' : B) (Z : type1336 A B) (r : type1614 A) (h1 : term535 A B Z r) : term906 A B Z r y x'.
Proof. exact (@lem1064969 A B y x' Z r h1). Qed.
Lemma lem1064971 {A B : Type'} (y'' : nat -> B) (y''' : nat -> B) (w : nat) (Z : type1336 A B) (r : type1614 A) (h1 : term535 A B Z r) : term912 A B Z r y'' y''' w.
Proof. exact (@lem1064970 A B (y'' w) (y''' w) Z r h1). Qed.
Lemma lem1065015 {A B : Type'} (n : nat) (Z : type1336 A B) (r : type1614 A) (y'' : nat -> B) (h1 : term101 A B Z r y'') : term357 A B Z r y'' n.
Proof. exact (@lem1064862 A B Z r y'' h1 n). Qed.
Lemma lem1065016 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (y'' : nat -> B) (n : nat) : (term357 A B Z r y'' n) = (term358 A B Z r y'' n).
Proof. exact (eq_refl (term357 A B Z r y'' n)). Qed.
Lemma lem1065017 {A B : Type'} (n : nat) (Z : type1336 A B) (r : type1614 A) (y'' : nat -> B) (h1 : term101 A B Z r y'') : term358 A B Z r y'' n.
Proof. exact (EQ_MP (@lem1065016 A B Z r y'' n) (@lem1065015 A B n Z r y'' h1)). Qed.
Lemma lem1065018 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (y'' : nat -> B) (n : nat) : (term358 A B Z r y'' n) = ((term358 A B Z r y'' n) = True).
Proof. exact (@lem7 (term358 A B Z r y'' n)). Qed.
Lemma lem1065020 {A B : Type'} (n : nat) (Z : type1336 A B) (r : type1614 A) (y''' : nat -> B) (h1 : term101 A B Z r y''') : term357 A B Z r y''' n.
Proof. exact (@lem1064865 A B Z r y''' h1 n). Qed.
Lemma lem1065021 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (y''' : nat -> B) (n : nat) : (term357 A B Z r y''' n) = (term358 A B Z r y''' n).
Proof. exact (eq_refl (term357 A B Z r y''' n)). Qed.
Lemma lem1065022 {A B : Type'} (n : nat) (Z : type1336 A B) (r : type1614 A) (y''' : nat -> B) (h1 : term101 A B Z r y''') : term358 A B Z r y''' n.
Proof. exact (EQ_MP (@lem1065021 A B Z r y''' n) (@lem1065020 A B n Z r y''' h1)). Qed.
Lemma lem1065023 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (y''' : nat -> B) (n : nat) : (term358 A B Z r y''' n) = ((term358 A B Z r y''' n) = True).
Proof. exact (@lem7 (term358 A B Z r y''' n)). Qed.
Lemma lem1065028 {A B : Type'} (n : nat) (Z : type1336 A B) (r : type1614 A) (y'' : nat -> B) (h1 : term101 A B Z r y'') : (term358 A B Z r y'' n) = True.
Proof. exact (EQ_MP (@lem1065018 A B Z r y'' n) (@lem1065017 A B n Z r y'' h1)). Qed.
Lemma lem1065029 {A B : Type'} (w : nat) (Z : type1336 A B) (r : type1614 A) (y'' : nat -> B) (h1 : term101 A B Z r y'') : (term358 A B Z r y'' w) = True.
Proof. exact (@lem1065028 A B w Z r y'' h1). Qed.
Lemma lem1065030 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1065031 {A B : Type'} (w : nat) (Z : type1336 A B) (r : type1614 A) (y'' : nat -> B) (h1 : term101 A B Z r y'') : (term913 A B Z r y'' w) = (and True).
Proof. exact (MK_COMB (@lem1065030) (@lem1065029 A B w Z r y'' h1)). Qed.
Lemma lem1065033 {A B : Type'} (n : nat) (Z : type1336 A B) (r : type1614 A) (y''' : nat -> B) (h1 : term101 A B Z r y''') : (term358 A B Z r y''' n) = True.
Proof. exact (EQ_MP (@lem1065023 A B Z r y''' n) (@lem1065022 A B n Z r y''' h1)). Qed.
Lemma lem1065034 {A B : Type'} (w : nat) (Z : type1336 A B) (r : type1614 A) (y''' : nat -> B) (h1 : term101 A B Z r y''') : (term358 A B Z r y''' w) = True.
Proof. exact (@lem1065033 A B w Z r y''' h1). Qed.
Lemma lem1065035 {A B : Type'} (w : nat) (y'' : nat -> B) (Z : type1336 A B) (r : type1614 A) (y''' : nat -> B) (h1 : term101 A B Z r y'') (h2 : term101 A B Z r y''') : (term914 A B y'' Z r y''' w) = (True /\ True).
Proof. exact (MK_COMB (@lem1065031 A B w Z r y'' h1) (@lem1065034 A B w Z r y''' h2)). Qed.
Lemma lem1065037 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1065038 : (True /\ True) = True.
Proof. exact (@lem1065037 True). Qed.
Lemma lem1065039 {A B : Type'} (w : nat) (y'' : nat -> B) (Z : type1336 A B) (r : type1614 A) (y''' : nat -> B) (h1 : term101 A B Z r y'') (h2 : term101 A B Z r y''') : (term914 A B y'' Z r y''' w) = True.
Proof. exact (TRANS (@lem1065035 A B w y'' Z r y''' h1 h2) (@lem1065038)). Qed.
Lemma lem1065040 {A B : Type'} (w : nat) (y'' : nat -> B) (Z : type1336 A B) (r : type1614 A) (y''' : nat -> B) (h1 : term101 A B Z r y'') (h2 : term101 A B Z r y''') : True = (term914 A B y'' Z r y''' w).
Proof. exact (SYM (@lem1065039 A B w y'' Z r y''' h1 h2)). Qed.
Lemma lem1065041 {A B : Type'} (w : nat) (y'' : nat -> B) (Z : type1336 A B) (r : type1614 A) (y''' : nat -> B) (h1 : term101 A B Z r y'') (h2 : term101 A B Z r y''') : term914 A B y'' Z r y''' w.
Proof. exact (EQ_MP (@lem1065040 A B w y'' Z r y''' h1 h2) (@lem0)). Qed.
Lemma lem1065042 {A B : Type'} (w : nat) (y'' : nat -> B) (Z : type1336 A B) (r : type1614 A) (y''' : nat -> B) (h1 : term101 A B Z r y'') (h2 : term101 A B Z r y''') : term915 A B y'' Z r y''' w.
Proof. exact (ex_intro (term916 A B y'' Z r y''' w) w (@lem1065041 A B w y'' Z r y''' h1 h2)). Qed.
Lemma lem1065043 {A B : Type'} (w : nat) (y'' : nat -> B) (Z : type1336 A B) (r : type1614 A) (y''' : nat -> B) (h1 : term535 A B Z r) (h2 : term101 A B Z r y'') (h3 : term101 A B Z r y''') : (y'' w) = (y''' w).
Proof. exact (@lem1064971 A B y'' y''' w Z r h1 (@lem1065042 A B w y'' Z r y''' h2 h3)). Qed.
Lemma lem1065048 {A B : Type'} (y'' : nat -> B) (Z : type1336 A B) (r : type1614 A) (y''' : nat -> B) (h1 : term535 A B Z r) (h2 : term101 A B Z r y'') (h3 : term101 A B Z r y''') : term900 B y'' y'''.
Proof. exact (fun w : nat => @lem1065043 A B w y'' Z r y''' h1 h2 h3). Qed.
Lemma lem1065049 {A B : Type'} (y'' : nat -> B) (Z : type1336 A B) (r : type1614 A) (y''' : nat -> B) (h1 : term535 A B Z r) (h2 : term101 A B Z r y'') (h3 : term101 A B Z r y''') : y'' = y'''.
Proof. exact (EQ_MP (@lem1064939 B y'' y''') (@lem1065048 A B y'' Z r y''' h1 h2 h3)). Qed.
Lemma lem1065050 {A B : Type'} (Fn : type1592 A B) (c : nat) (i : A) (y'' : nat -> B) (Z : type1336 A B) (r : type1614 A) (y''' : nat -> B) (h1 : term535 A B Z r) (h2 : term101 A B Z r y'') (h3 : term101 A B Z r y''') : (Fn c i r y'') = (Fn c i r y''').
Proof. exact (MK_COMB (@lem1064932 A B Fn c i r) (@lem1065049 A B y'' Z r y''' h1 h2 h3)). Qed.
Lemma lem1065051 {A B : Type'} (Z : type1336 A B) (x' : B) (y''' : nat -> B) (y' : B) (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (y'' : nat -> B) (h1 : term535 A B Z r) (h2 : term101 A B Z r y'') (h3 : term101 A B Z r y''') (h4 : x' = (Fn c i r y''')) (h5 : y' = (Fn c i r y'')) : y' = x'.
Proof. exact (EQ_MP (@lem1064931 A B x' y''' y' Fn c i r y'' h4 h5) (@lem1065050 A B Fn c i y'' Z r y''' h1 h2 h3)). Qed.
Lemma lem1065052 {A B : Type'} (y' : B) (x' : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (h1 : term892 A B y' x' Fn c i Z r) : term821 A B x' Fn c i Z r.
Proof. exact (proj2 (@lem1064858 A B y' x' Fn c i Z r h1)). Qed.
Lemma lem1065053 {A B : Type'} (y' : B) (x' : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (h1 : term892 A B y' x' Fn c i Z r) : term821 A B y' Fn c i Z r.
Proof. exact (proj1 (@lem1064858 A B y' x' Fn c i Z r h1)). Qed.
Lemma lem1065054 {A B : Type'} (x' : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (y''' : nat -> B) (h1 : term100 A B x' Fn c i Z r y''') : term101 A B Z r y'''.
Proof. exact (proj2 (@lem1064864 A B x' Fn c i Z r y''' h1)). Qed.
Lemma lem1065055 {A B : Type'} (x' : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (y''' : nat -> B) (h1 : term100 A B x' Fn c i Z r y''') : x' = (Fn c i r y''').
Proof. exact (proj1 (@lem1064864 A B x' Fn c i Z r y''' h1)). Qed.
Lemma lem1065056 {A B : Type'} (Z : type1336 A B) (x' : B) (y''' : nat -> B) (y' : B) (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (y'' : nat -> B) (h1 : term535 A B Z r) (h2 : term101 A B Z r y'') (h3 : term101 A B Z r y''') (h4 : x' = (Fn c i r y''')) (h5 : y' = (Fn c i r y'')) : (term101 A B Z r y''') = (y' = x').
Proof. exact (prop_ext (fun h6 : term101 A B Z r y''' => @lem1065051 A B Z x' y''' y' Fn c i r y'' h1 h2 h3 h4 h5) (fun h6 : y' = x' => @lem1064865 A B Z r y''' h3)). Qed.
Lemma lem1065057 {A B : Type'} (Z : type1336 A B) (x' : B) (y''' : nat -> B) (y' : B) (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (y'' : nat -> B) (h1 : term535 A B Z r) (h2 : term101 A B Z r y'') (h3 : term101 A B Z r y''') (h4 : x' = (Fn c i r y''')) (h5 : y' = (Fn c i r y'')) : y' = x'.
Proof. exact (EQ_MP (@lem1065056 A B Z x' y''' y' Fn c i r y'' h1 h2 h3 h4 h5) (@lem1064865 A B Z r y''' h3)). Qed.
Lemma lem1065058 {A B : Type'} (Z : type1336 A B) (x' : B) (y''' : nat -> B) (y' : B) (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (y'' : nat -> B) (h1 : term535 A B Z r) (h2 : term101 A B Z r y'') (h3 : term101 A B Z r y''') (h4 : x' = (Fn c i r y''')) (h5 : y' = (Fn c i r y'')) : (x' = (Fn c i r y''')) = (y' = x').
Proof. exact (prop_ext (fun h6 : x' = (Fn c i r y''') => @lem1065057 A B Z x' y''' y' Fn c i r y'' h1 h2 h3 h4 h5) (fun h6 : y' = x' => @lem1064866 A B x' Fn c i r y''' h4)). Qed.
Lemma lem1065059 {A B : Type'} (Z : type1336 A B) (x' : B) (y''' : nat -> B) (y' : B) (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (y'' : nat -> B) (h1 : term535 A B Z r) (h2 : term101 A B Z r y'') (h3 : term101 A B Z r y''') (h4 : x' = (Fn c i r y''')) (h5 : y' = (Fn c i r y'')) : y' = x'.
Proof. exact (EQ_MP (@lem1065058 A B Z x' y''' y' Fn c i r y'' h1 h2 h3 h4 h5) (@lem1064866 A B x' Fn c i r y''' h4)). Qed.
Lemma lem1065060 {A B : Type'} (Z : type1336 A B) (x' : B) (y''' : nat -> B) (y' : B) (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (y'' : nat -> B) (h1 : term535 A B Z r) (h2 : term101 A B Z r y'') (h3 : term100 A B x' Fn c i Z r y''') (h4 : x' = (Fn c i r y''')) (h5 : y' = (Fn c i r y'')) : (term101 A B Z r y''') = (y' = x').
Proof. exact (prop_ext (fun h6 : term101 A B Z r y''' => @lem1065059 A B Z x' y''' y' Fn c i r y'' h1 h2 h6 h4 h5) (fun h6 : y' = x' => @lem1065054 A B x' Fn c i Z r y''' h3)). Qed.
Lemma lem1065061 {A B : Type'} (Z : type1336 A B) (x' : B) (y''' : nat -> B) (y' : B) (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (y'' : nat -> B) (h1 : term535 A B Z r) (h2 : term101 A B Z r y'') (h3 : term100 A B x' Fn c i Z r y''') (h4 : x' = (Fn c i r y''')) (h5 : y' = (Fn c i r y'')) : y' = x'.
Proof. exact (EQ_MP (@lem1065060 A B Z x' y''' y' Fn c i r y'' h1 h2 h3 h4 h5) (@lem1065054 A B x' Fn c i Z r y''' h3)). Qed.
Lemma lem1065062 {A B : Type'} (x' : B) (Z : type1336 A B) (y''' : nat -> B) (y' : B) (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (y'' : nat -> B) (h1 : term535 A B Z r) (h2 : term101 A B Z r y'') (h3 : term100 A B x' Fn c i Z r y''') (h4 : y' = (Fn c i r y'')) : (x' = (Fn c i r y''')) = (y' = x').
Proof. exact (prop_ext (fun h5 : x' = (Fn c i r y''') => @lem1065061 A B Z x' y''' y' Fn c i r y'' h1 h2 h3 h5 h4) (fun h5 : y' = x' => @lem1065055 A B x' Fn c i Z r y''' h3)). Qed.
Lemma lem1065063 {A B : Type'} (x' : B) (Z : type1336 A B) (y''' : nat -> B) (y' : B) (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (y'' : nat -> B) (h1 : term535 A B Z r) (h2 : term101 A B Z r y'') (h3 : term100 A B x' Fn c i Z r y''') (h4 : y' = (Fn c i r y'')) : y' = x'.
Proof. exact (EQ_MP (@lem1065062 A B x' Z y''' y' Fn c i r y'' h1 h2 h3 h4) (@lem1065055 A B x' Fn c i Z r y''' h3)). Qed.
Lemma lem1065064 {A B : Type'} (x' : B) (Z : type1336 A B) (y' : B) (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (y'' : nat -> B) (h1 : term535 A B Z r) (h2 : term101 A B Z r y'') (h3 : term821 A B x' Fn c i Z r) (h4 : y' = (Fn c i r y'')) : y' = x'.
Proof. exact (ex_elim (@lem1064859 A B x' Fn c i Z r h3) (fun y''' : nat -> B => fun h0 : term813 A B x' Fn c i Z r y''' => @lem1065063 A B x' Z y''' y' Fn c i r y'' h1 h2 h0 h4)). Qed.
Lemma lem1065065 {A B : Type'} (y' : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (y'' : nat -> B) (h1 : term100 A B y' Fn c i Z r y'') : term101 A B Z r y''.
Proof. exact (proj2 (@lem1064861 A B y' Fn c i Z r y'' h1)). Qed.
Lemma lem1065066 {A B : Type'} (y' : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (y'' : nat -> B) (h1 : term100 A B y' Fn c i Z r y'') : y' = (Fn c i r y'').
Proof. exact (proj1 (@lem1064861 A B y' Fn c i Z r y'' h1)). Qed.
Lemma lem1065067 {A B : Type'} (x' : B) (Z : type1336 A B) (y' : B) (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (y'' : nat -> B) (h1 : term535 A B Z r) (h2 : term101 A B Z r y'') (h3 : term821 A B x' Fn c i Z r) (h4 : y' = (Fn c i r y'')) : (term101 A B Z r y'') = (y' = x').
Proof. exact (prop_ext (fun h5 : term101 A B Z r y'' => @lem1065064 A B x' Z y' Fn c i r y'' h1 h2 h3 h4) (fun h5 : y' = x' => @lem1064862 A B Z r y'' h2)). Qed.
Lemma lem1065068 {A B : Type'} (x' : B) (Z : type1336 A B) (y' : B) (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (y'' : nat -> B) (h1 : term535 A B Z r) (h2 : term101 A B Z r y'') (h3 : term821 A B x' Fn c i Z r) (h4 : y' = (Fn c i r y'')) : y' = x'.
Proof. exact (EQ_MP (@lem1065067 A B x' Z y' Fn c i r y'' h1 h2 h3 h4) (@lem1064862 A B Z r y'' h2)). Qed.
Lemma lem1065069 {A B : Type'} (x' : B) (Z : type1336 A B) (y' : B) (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (y'' : nat -> B) (h1 : term535 A B Z r) (h2 : term101 A B Z r y'') (h3 : term821 A B x' Fn c i Z r) (h4 : y' = (Fn c i r y'')) : (y' = (Fn c i r y'')) = (y' = x').
Proof. exact (prop_ext (fun h5 : y' = (Fn c i r y'') => @lem1065068 A B x' Z y' Fn c i r y'' h1 h2 h3 h4) (fun h5 : y' = x' => @lem1064863 A B y' Fn c i r y'' h4)). Qed.
Lemma lem1065070 {A B : Type'} (x' : B) (Z : type1336 A B) (y' : B) (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (y'' : nat -> B) (h1 : term535 A B Z r) (h2 : term101 A B Z r y'') (h3 : term821 A B x' Fn c i Z r) (h4 : y' = (Fn c i r y'')) : y' = x'.
Proof. exact (EQ_MP (@lem1065069 A B x' Z y' Fn c i r y'' h1 h2 h3 h4) (@lem1064863 A B y' Fn c i r y'' h4)). Qed.
Lemma lem1065071 {A B : Type'} (x' : B) (Z : type1336 A B) (y' : B) (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (y'' : nat -> B) (h1 : term535 A B Z r) (h2 : term821 A B x' Fn c i Z r) (h3 : term100 A B y' Fn c i Z r y'') (h4 : y' = (Fn c i r y'')) : (term101 A B Z r y'') = (y' = x').
Proof. exact (prop_ext (fun h5 : term101 A B Z r y'' => @lem1065070 A B x' Z y' Fn c i r y'' h1 h5 h2 h4) (fun h5 : y' = x' => @lem1065065 A B y' Fn c i Z r y'' h3)). Qed.
Lemma lem1065072 {A B : Type'} (x' : B) (Z : type1336 A B) (y' : B) (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (y'' : nat -> B) (h1 : term535 A B Z r) (h2 : term821 A B x' Fn c i Z r) (h3 : term100 A B y' Fn c i Z r y'') (h4 : y' = (Fn c i r y'')) : y' = x'.
Proof. exact (EQ_MP (@lem1065071 A B x' Z y' Fn c i r y'' h1 h2 h3 h4) (@lem1065065 A B y' Fn c i Z r y'' h3)). Qed.
Lemma lem1065073 {A B : Type'} (x' : B) (y' : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (y'' : nat -> B) (h1 : term535 A B Z r) (h2 : term821 A B x' Fn c i Z r) (h3 : term100 A B y' Fn c i Z r y'') : (y' = (Fn c i r y'')) = (y' = x').
Proof. exact (prop_ext (fun h4 : y' = (Fn c i r y'') => @lem1065072 A B x' Z y' Fn c i r y'' h1 h2 h3 h4) (fun h4 : y' = x' => @lem1065066 A B y' Fn c i Z r y'' h3)). Qed.
Lemma lem1065074 {A B : Type'} (x' : B) (y' : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (y'' : nat -> B) (h1 : term535 A B Z r) (h2 : term821 A B x' Fn c i Z r) (h3 : term100 A B y' Fn c i Z r y'') : y' = x'.
Proof. exact (EQ_MP (@lem1065073 A B x' y' Fn c i Z r y'' h1 h2 h3) (@lem1065066 A B y' Fn c i Z r y'' h3)). Qed.
Lemma lem1065075 {A B : Type'} (x' : B) (y' : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (h1 : term535 A B Z r) (h2 : term821 A B x' Fn c i Z r) (h3 : term821 A B y' Fn c i Z r) : y' = x'.
Proof. exact (ex_elim (@lem1064860 A B y' Fn c i Z r h3) (fun y'' : nat -> B => fun h0 : term813 A B y' Fn c i Z r y'' => @lem1065074 A B x' y' Fn c i Z r y'' h1 h2 h0)). Qed.
Lemma lem1065076 {A B : Type'} (y' : B) (x' : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (h1 : term535 A B Z r) (h2 : term821 A B y' Fn c i Z r) (h3 : term892 A B y' x' Fn c i Z r) : (term821 A B x' Fn c i Z r) = (y' = x').
Proof. exact (prop_ext (fun h4 : term821 A B x' Fn c i Z r => @lem1065075 A B x' y' Fn c i Z r h1 h4 h2) (fun h4 : y' = x' => @lem1065052 A B y' x' Fn c i Z r h3)). Qed.
Lemma lem1065077 {A B : Type'} (y' : B) (x' : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (h1 : term535 A B Z r) (h2 : term821 A B y' Fn c i Z r) (h3 : term892 A B y' x' Fn c i Z r) : y' = x'.
Proof. exact (EQ_MP (@lem1065076 A B y' x' Fn c i Z r h1 h2 h3) (@lem1065052 A B y' x' Fn c i Z r h3)). Qed.
Lemma lem1065078 {A B : Type'} (y' : B) (x' : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (h1 : term535 A B Z r) (h2 : term892 A B y' x' Fn c i Z r) : (term821 A B y' Fn c i Z r) = (y' = x').
Proof. exact (prop_ext (fun h3 : term821 A B y' Fn c i Z r => @lem1065077 A B y' x' Fn c i Z r h1 h3 h2) (fun h3 : y' = x' => @lem1065053 A B y' x' Fn c i Z r h2)). Qed.
Lemma lem1065079 {A B : Type'} (y' : B) (x' : B) (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (h1 : term535 A B Z r) (h2 : term892 A B y' x' Fn c i Z r) : y' = x'.
Proof. exact (EQ_MP (@lem1065078 A B y' x' Fn c i Z r h1 h2) (@lem1065053 A B y' x' Fn c i Z r h2)). Qed.
Lemma lem1065080 {A B : Type'} (Fn : type1592 A B) (c : nat) (i : A) (y' : B) (x' : B) (Z : type1336 A B) (r : type1614 A) (h1 : term535 A B Z r) : term894 A B Fn c i Z r y' x'.
Proof. exact (fun h0 : term892 A B y' x' Fn c i Z r => @lem1065079 A B y' x' Fn c i Z r h1 h0). Qed.
Lemma lem1065085 {A B : Type'} (Fn : type1592 A B) (c : nat) (i : A) (y' : B) (Z : type1336 A B) (r : type1614 A) (h1 : term535 A B Z r) : term896 A B Fn c i Z r y'.
Proof. exact (fun x' : B => @lem1065080 A B Fn c i y' x' Z r h1). Qed.
Lemma lem1065090 {A B : Type'} (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (h1 : term535 A B Z r) : term898 A B Fn c i Z r.
Proof. exact (fun y' : B => @lem1065085 A B Fn c i y' Z r h1). Qed.
Lemma lem1065091 {A B : Type'} (c : nat) (i : A) (Fn : type1592 A B) (Z : type1336 A B) (r : type1614 A) (h1 : term535 A B Z r) : term785 A B c i r Fn Z.
Proof. exact (EQ_MP (@lem1064857 A B c i r Fn Z) (@lem1065090 A B Fn c i Z r h1)). Qed.
Lemma lem1065092 {A B : Type'} (b : B) (c : nat) (i : A) (Fn : type1592 A B) (Z : type1336 A B) (r : type1614 A) (h1 : term535 A B Z r) : term596 A B b c i r Fn Z.
Proof. exact (EQ_MP (@lem1064045 A B b c i r Fn Z) (@lem1065091 A B c i Fn Z r h1)). Qed.
Lemma lem1065093 {A B : Type'} (b : B) (c : nat) (i : A) (Fn : type1592 A B) (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (h1 : term535 A B Z r) (h2 : term101 A B Z r y) : term597 A B b c i r Fn Z.
Proof. exact (conj (@lem1063677 A B b c i Fn Z r y h2) (@lem1065092 A B b c i Fn Z r h1)). Qed.
Lemma lem1065094 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term535 A B Z r) (h2 : term101 A B Z r y) (h3 : term260 A B b Fn Z) : term584 A B Z c i r.
Proof. exact (EQ_MP (@lem1063049 A B c i r b Fn Z h3) (@lem1065093 A B b c i Fn Z r y h1 h2)). Qed.
Lemma lem1065095 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term535 A B Z r) (h2 : term101 A B Z r y) (h3 : term260 A B b Fn Z) : term422 A B Z c i r.
Proof. exact (EQ_MP (@lem1062889 A B Z c i r) (@lem1065094 A B c i r y b Fn Z h1 h2 h3)). Qed.
Lemma lem1065096 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term535 A B Z r) (h2 : term101 A B Z r y) (h3 : term260 A B b Fn Z) : (term101 A B Z r y) = (term422 A B Z c i r).
Proof. exact (prop_ext (fun h4 : term101 A B Z r y => @lem1065095 A B c i r y b Fn Z h1 h2 h3) (fun h4 : term422 A B Z c i r => @lem1062834 A B Z r y h2)). Qed.
Lemma lem1065097 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term535 A B Z r) (h2 : term101 A B Z r y) (h3 : term260 A B b Fn Z) : term422 A B Z c i r.
Proof. exact (EQ_MP (@lem1065096 A B c i r y b Fn Z h1 h2 h3) (@lem1062834 A B Z r y h2)). Qed.
Lemma lem1065098 {A B : Type'} (c : nat) (i : A) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (r : type1614 A) (h1 : term535 A B Z r) (h2 : term260 A B b Fn Z) (h3 : term555 A B Z r) : term422 A B Z c i r.
Proof. exact (ex_elim (@lem1062833 A B Z r h3) (fun y : nat -> B => fun h0 : term554 A B Z r y => @lem1065097 A B c i r y b Fn Z h1 h0 h2)). Qed.
Lemma lem1065099 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term535 A B Z r) (h2 : term260 A B b Fn Z) : term917 A B Z c i r.
Proof. exact (fun h0 : term555 A B Z r => @lem1065098 A B c i b Fn Z r h1 h2 h0). Qed.
Lemma lem1065100 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term535 A B Z r) (h2 : term530 A B Z r) (h3 : term260 A B b Fn Z) : term422 A B Z c i r.
Proof. exact (@lem1065099 A B c i r b Fn Z h1 h3 (@lem1062832 A B Z r h2)). Qed.
Lemma lem1065101 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term535 A B Z r) (h2 : term260 A B b Fn Z) : term918 A B Z c i r.
Proof. exact (fun h0 : term530 A B Z r => @lem1065100 A B c i r b Fn Z h1 h0 h2). Qed.
Lemma lem1065102 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (h1 : term536 A B Z r) : term535 A B Z r.
Proof. exact (proj2 (@lem1062790 A B Z r h1)). Qed.
Lemma lem1065103 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (h1 : term536 A B Z r) : term530 A B Z r.
Proof. exact (proj1 (@lem1062790 A B Z r h1)). Qed.
Lemma lem1065104 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term535 A B Z r) (h2 : term260 A B b Fn Z) : (term535 A B Z r) = (term918 A B Z c i r).
Proof. exact (prop_ext (fun h3 : term535 A B Z r => @lem1065101 A B c i r b Fn Z h1 h2) (fun h3 : term918 A B Z c i r => @lem1062791 A B Z r h1)). Qed.
Lemma lem1065105 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term535 A B Z r) (h2 : term260 A B b Fn Z) : term918 A B Z c i r.
Proof. exact (EQ_MP (@lem1065104 A B c i r b Fn Z h1 h2) (@lem1062791 A B Z r h1)). Qed.
Lemma lem1065106 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term535 A B Z r) (h2 : term530 A B Z r) (h3 : term260 A B b Fn Z) : term422 A B Z c i r.
Proof. exact (@lem1065105 A B c i r b Fn Z h1 h3 (@lem1062792 A B Z r h2)). Qed.
Lemma lem1065107 {A B : Type'} (c : nat) (i : A) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (r : type1614 A) (h1 : term530 A B Z r) (h2 : term260 A B b Fn Z) (h3 : term536 A B Z r) : (term535 A B Z r) = (term422 A B Z c i r).
Proof. exact (prop_ext (fun h4 : term535 A B Z r => @lem1065106 A B c i r b Fn Z h4 h1 h2) (fun h4 : term422 A B Z c i r => @lem1065102 A B Z r h3)). Qed.
Lemma lem1065108 {A B : Type'} (c : nat) (i : A) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (r : type1614 A) (h1 : term530 A B Z r) (h2 : term260 A B b Fn Z) (h3 : term536 A B Z r) : term422 A B Z c i r.
Proof. exact (EQ_MP (@lem1065107 A B c i b Fn Z r h1 h2 h3) (@lem1065102 A B Z r h3)). Qed.
Lemma lem1065109 {A B : Type'} (c : nat) (i : A) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (r : type1614 A) (h1 : term260 A B b Fn Z) (h2 : term536 A B Z r) : (term530 A B Z r) = (term422 A B Z c i r).
Proof. exact (prop_ext (fun h3 : term530 A B Z r => @lem1065108 A B c i b Fn Z r h3 h1 h2) (fun h3 : term422 A B Z c i r => @lem1065103 A B Z r h2)). Qed.
Lemma lem1065110 {A B : Type'} (c : nat) (i : A) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (r : type1614 A) (h1 : term260 A B b Fn Z) (h2 : term536 A B Z r) : term422 A B Z c i r.
Proof. exact (EQ_MP (@lem1065109 A B c i b Fn Z r h1 h2) (@lem1065103 A B Z r h2)). Qed.
Lemma lem1065111 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) : term919 A B Z c i r.
Proof. exact (fun h0 : term536 A B Z r => @lem1065110 A B c i b Fn Z r h1 h0). Qed.
Lemma lem1065112 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term418 A B Z r) (h2 : term260 A B b Fn Z) : term422 A B Z c i r.
Proof. exact (@lem1065111 A B c i r b Fn Z h2 (@lem1062789 A B Z r h1)). Qed.
Lemma lem1065113 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) : term424 A B Z c i r.
Proof. exact (fun h0 : term418 A B Z r => @lem1065112 A B c i r b Fn Z h0 h1). Qed.
Lemma lem1065118 {A B : Type'} (c : nat) (i : A) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) : term428 A B Z c i.
Proof. exact (fun r : type1614 A => @lem1065113 A B c i r b Fn Z h1). Qed.
Lemma lem1065123 {A B : Type'} (c : nat) (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) : term432 A B Z c.
Proof. exact (fun i : A => @lem1065118 A B c i b Fn Z h1). Qed.
Lemma lem1065128 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) : term436 A B Z.
Proof. exact (fun c : nat => @lem1065123 A B c b Fn Z h1). Qed.
Lemma lem1065129 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) : term438 A B Z.
Proof. exact (conj (@lem1062670 A B b Fn Z h1) (@lem1065128 A B b Fn Z h1)). Qed.
Lemma lem1065130 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) (h2 : term445 A B Z) : term406 A B Z.
Proof. exact (@lem1062533 A B Z h2 (@lem1065129 A B b Fn Z h1)). Qed.
Lemma lem1065131 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) : term446 A B Z.
Proof. exact (fun h0 : term445 A B Z => @lem1065130 A B b Fn Z h1 h0). Qed.
Lemma lem1065132 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term260 A B b Fn Z) : term406 A B Z.
Proof. exact (@lem1065131 A B b Fn Z h1 (@lem1062520 A B Z)). Qed.
Lemma lem1065136 {A B : Type'} (P : type1413 A B) : (term1 A B P) = (term2 A B P).
Proof. exact (EQ_MP (@lem1061485 A B P) (@lem1061484 A B P)). Qed.
Lemma lem1065137 {A B : Type'} (P : type1336 A B) : (term406 A B P) = (term920 A B P).
Proof. exact (@lem1065136 (recspace A) B P). Qed.
Lemma lem1065138 {A B : Type'} (Z : type1336 A B) : (term406 A B Z) = (term920 A B Z).
Proof. exact (@lem1065137 A B Z). Qed.
Lemma lem1065155 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1065156 {A B : Type'} (Z : type1336 A B) : (term921 A B Z) = (term922 A B Z).
Proof. exact (MK_COMB (@lem1065155) (@lem1065138 A B Z)). Qed.
Lemma lem1065175 {A B : Type'} (Fn : type1592 A B) : (term923 A B Fn) = (term923 A B Fn).
Proof. exact (eq_refl (term923 A B Fn)). Qed.
Lemma lem1065176 {A B : Type'} (Z : type1336 A B) (Fn : type1592 A B) : (term924 A B Z Fn) = (term925 A B Z Fn).
Proof. exact (MK_COMB (@lem1065156 A B Z) (@lem1065175 A B Fn)). Qed.
Lemma lem1065179 {A B : Type'} (Z : type1336 A B) (Fn : type1592 A B) : (term925 A B Z Fn) = (term924 A B Z Fn).
Proof. exact (SYM (@lem1065176 A B Z Fn)). Qed.
Lemma lem1065180 {A B : Type'} (Z : type1336 A B) (h1 : term920 A B Z) : term920 A B Z.
Proof. exact (h1). Qed.
Lemma lem1065181 {A B : Type'} (Z : type1336 A B) (fn : type1337 A B) (h1 : term926 A B Z fn) : term926 A B Z fn.
Proof. exact (h1). Qed.
Lemma lem1065184 {A B : Type'} (Z : type1336 A B) (fn : type1337 A B) (x : recspace A) (y : B) (h1 : (Z x y) = ((fn x) = y)) : (Z x y) = ((fn x) = y).
Proof. exact (h1). Qed.
Lemma lem1065185 {A B : Type'} (Z : type1336 A B) (fn : type1337 A B) (x : recspace A) (y : B) (h1 : (Z x y) = ((fn x) = y)) : ((fn x) = y) = (Z x y).
Proof. exact (SYM (@lem1065184 A B Z fn x y h1)). Qed.
Lemma lem1065186 {A B : Type'} (fn : type1337 A B) (Z : type1336 A B) (x : recspace A) (y : B) (h1 : ((fn x) = y) = (Z x y)) : ((fn x) = y) = (Z x y).
Proof. exact (h1). Qed.
Lemma lem1065187 {A B : Type'} (fn : type1337 A B) (Z : type1336 A B) (x : recspace A) (y : B) (h1 : ((fn x) = y) = (Z x y)) : (Z x y) = ((fn x) = y).
Proof. exact (SYM (@lem1065186 A B fn Z x y h1)). Qed.
Lemma lem1065188 {A B : Type'} (fn : type1337 A B) (Z : type1336 A B) (x : recspace A) (y : B) : ((Z x y) = ((fn x) = y)) = (((fn x) = y) = (Z x y)).
Proof. exact (prop_ext (fun h1 : (Z x y) = ((fn x) = y) => @lem1065185 A B Z fn x y h1) (fun h1 : ((fn x) = y) = (Z x y) => @lem1065187 A B fn Z x y h1)). Qed.
Lemma lem1065189 {A B : Type'} (fn : type1337 A B) (Z : type1336 A B) (x : recspace A) : (term927 A B Z fn x) = (term928 A B fn Z x).
Proof. exact (fun_ext (fun y : B => @lem1065188 A B fn Z x y)). Qed.
Lemma lem1065190 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1065191 {A B : Type'} (fn : type1337 A B) (Z : type1336 A B) (x : recspace A) : (term929 A B Z fn x) = (term930 A B fn Z x).
Proof. exact (MK_COMB (@lem1065190 B) (@lem1065189 A B fn Z x)). Qed.
Lemma lem1065192 {A B : Type'} (fn : type1337 A B) (Z : type1336 A B) : (term931 A B Z fn) = (term932 A B fn Z).
Proof. exact (fun_ext (fun x : recspace A => @lem1065191 A B fn Z x)). Qed.
Lemma lem1065193 {A : Type'} : (@all (recspace A)) = (@all (recspace A)).
Proof. exact (eq_refl (@all (recspace A))). Qed.
Lemma lem1065194 {A B : Type'} (fn : type1337 A B) (Z : type1336 A B) : (term926 A B Z fn) = (term933 A B fn Z).
Proof. exact (MK_COMB (@lem1065193 A) (@lem1065192 A B fn Z)). Qed.
Lemma lem1065195 {A B : Type'} (Z : type1336 A B) (fn : type1337 A B) (h1 : term926 A B Z fn) : term933 A B fn Z.
Proof. exact (EQ_MP (@lem1065194 A B fn Z) (@lem1065181 A B Z fn h1)). Qed.
Lemma lem1065223 {A B : Type'} (x : recspace A) (Z : type1336 A B) (fn : type1337 A B) (h1 : term926 A B Z fn) : term934 A B fn Z x.
Proof. exact (@lem1065195 A B Z fn h1 x). Qed.
Lemma lem1065224 {A B : Type'} (fn : type1337 A B) (Z : type1336 A B) (x : recspace A) : (term934 A B fn Z x) = (term930 A B fn Z x).
Proof. exact (eq_refl (term934 A B fn Z x)). Qed.
Lemma lem1065225 {A B : Type'} (x : recspace A) (Z : type1336 A B) (fn : type1337 A B) (h1 : term926 A B Z fn) : term930 A B fn Z x.
Proof. exact (EQ_MP (@lem1065224 A B fn Z x) (@lem1065223 A B x Z fn h1)). Qed.
Lemma lem1065226 {A B : Type'} (x : recspace A) (y : B) (Z : type1336 A B) (fn : type1337 A B) (h1 : term926 A B Z fn) : term935 A B fn Z x y.
Proof. exact (@lem1065225 A B x Z fn h1 y). Qed.
Lemma lem1065227 {A B : Type'} (fn : type1337 A B) (Z : type1336 A B) (x : recspace A) (y : B) : (term935 A B fn Z x y) = (((fn x) = y) = (Z x y)).
Proof. exact (eq_refl (term935 A B fn Z x y)). Qed.
Lemma lem1065242 {A B : Type'} (x : recspace A) (y : B) (Z : type1336 A B) (fn : type1337 A B) (h1 : term926 A B Z fn) : ((fn x) = y) = (Z x y).
Proof. exact (EQ_MP (@lem1065227 A B fn Z x y) (@lem1065226 A B x y Z fn h1)). Qed.
Lemma lem1065243 {A B : Type'} (x : recspace A) (y : B) (Z : type1336 A B) (fn : type1337 A B) (h1 : term926 A B Z fn) : ((fn x) = y) = (Z x y).
Proof. exact (@lem1065242 A B x y Z fn h1). Qed.
Lemma lem1065244 {A B : Type'} (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (Z : type1336 A B) (fn : type1337 A B) (h1 : term926 A B Z fn) : ((term936 A B fn c i r) = (term937 A B Fn c i fn r)) = (term938 A B Z Fn c i fn r).
Proof. exact (@lem1065243 A B (@CONSTR A c i r) (term937 A B Fn c i fn r) Z fn h1). Qed.
Lemma lem1065245 {A B : Type'} (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (fn : type1337 A B) (h1 : term926 A B Z fn) : (term939 A B Fn c i fn) = (term940 A B Z Fn c i fn).
Proof. exact (fun_ext (fun r : type1614 A => @lem1065244 A B Fn c i r Z fn h1)). Qed.
Lemma lem1065246 {A : Type'} : (@all (nat -> recspace A)) = (@all (nat -> recspace A)).
Proof. exact (eq_refl (@all (nat -> recspace A))). Qed.
Lemma lem1065247 {A B : Type'} (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (fn : type1337 A B) (h1 : term926 A B Z fn) : (term941 A B Fn c i fn) = (term942 A B Z Fn c i fn).
Proof. exact (MK_COMB (@lem1065246 A) (@lem1065245 A B Fn c i Z fn h1)). Qed.
Lemma lem1065252 {A B : Type'} (Fn : type1592 A B) (c : nat) (Z : type1336 A B) (fn : type1337 A B) (h1 : term926 A B Z fn) : (term943 A B Fn c fn) = (term944 A B Z Fn c fn).
Proof. exact (fun_ext (fun i : A => @lem1065247 A B Fn c i Z fn h1)). Qed.
Lemma lem1065253 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1065254 {A B : Type'} (Fn : type1592 A B) (c : nat) (Z : type1336 A B) (fn : type1337 A B) (h1 : term926 A B Z fn) : (term945 A B Fn c fn) = (term946 A B Z Fn c fn).
Proof. exact (MK_COMB (@lem1065253 A) (@lem1065252 A B Fn c Z fn h1)). Qed.
Lemma lem1065259 {A B : Type'} (Fn : type1592 A B) (Z : type1336 A B) (fn : type1337 A B) (h1 : term926 A B Z fn) : (term947 A B Fn fn) = (term948 A B Z Fn fn).
Proof. exact (fun_ext (fun c : nat => @lem1065254 A B Fn c Z fn h1)). Qed.
Lemma lem1065260 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1065261 {A B : Type'} (Fn : type1592 A B) (Z : type1336 A B) (fn : type1337 A B) (h1 : term926 A B Z fn) : (term949 A B Fn fn) = (term950 A B Z Fn fn).
Proof. exact (MK_COMB (@lem1065260) (@lem1065259 A B Fn Z fn h1)). Qed.
Lemma lem1065266 {A B : Type'} (Fn : type1592 A B) (Z : type1336 A B) (fn : type1337 A B) (h1 : term926 A B Z fn) : (term950 A B Z Fn fn) = (term949 A B Fn fn).
Proof. exact (SYM (@lem1065261 A B Fn Z fn h1)). Qed.
Lemma lem1065285 {A B : Type'} (Z : type1336 A B) (Fn : type1592 A B) (h1 : term102 A B Z Fn) : term102 A B Z Fn.
Proof. exact (h1). Qed.
Lemma lem1065286 {A B : Type'} (c : nat) (Z : type1336 A B) (Fn : type1592 A B) (h1 : term102 A B Z Fn) : term103 A B Z Fn c.
Proof. exact (@lem1065285 A B Z Fn h1 c). Qed.
Lemma lem1065287 {A B : Type'} (Z : type1336 A B) (Fn : type1592 A B) (c : nat) : (term103 A B Z Fn c) = (term104 A B Z Fn c).
Proof. exact (eq_refl (term103 A B Z Fn c)). Qed.
Lemma lem1065288 {A B : Type'} (c : nat) (Z : type1336 A B) (Fn : type1592 A B) (h1 : term102 A B Z Fn) : term104 A B Z Fn c.
Proof. exact (EQ_MP (@lem1065287 A B Z Fn c) (@lem1065286 A B c Z Fn h1)). Qed.
Lemma lem1065289 {A B : Type'} (c : nat) (i : A) (Z : type1336 A B) (Fn : type1592 A B) (h1 : term102 A B Z Fn) : term105 A B Z Fn c i.
Proof. exact (@lem1065288 A B c Z Fn h1 i). Qed.
Lemma lem1065290 {A B : Type'} (Z : type1336 A B) (Fn : type1592 A B) (c : nat) (i : A) : (term105 A B Z Fn c i) = (term106 A B Z Fn c i).
Proof. exact (eq_refl (term105 A B Z Fn c i)). Qed.
Lemma lem1065291 {A B : Type'} (c : nat) (i : A) (Z : type1336 A B) (Fn : type1592 A B) (h1 : term102 A B Z Fn) : term106 A B Z Fn c i.
Proof. exact (EQ_MP (@lem1065290 A B Z Fn c i) (@lem1065289 A B c i Z Fn h1)). Qed.
Lemma lem1065292 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (Z : type1336 A B) (Fn : type1592 A B) (h1 : term102 A B Z Fn) : term107 A B Z Fn c i r.
Proof. exact (@lem1065291 A B c i Z Fn h1 r). Qed.
Lemma lem1065293 {A B : Type'} (Z : type1336 A B) (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) : (term107 A B Z Fn c i r) = (term108 A B Z Fn c i r).
Proof. exact (eq_refl (term107 A B Z Fn c i r)). Qed.
Lemma lem1065294 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (Z : type1336 A B) (Fn : type1592 A B) (h1 : term102 A B Z Fn) : term108 A B Z Fn c i r.
Proof. exact (EQ_MP (@lem1065293 A B Z Fn c i r) (@lem1065292 A B c i r Z Fn h1)). Qed.
Lemma lem1065295 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Z : type1336 A B) (Fn : type1592 A B) (h1 : term102 A B Z Fn) : term109 A B Z Fn c i r y.
Proof. exact (@lem1065294 A B c i r Z Fn h1 y). Qed.
Lemma lem1065296 {A B : Type'} (Z : type1336 A B) (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (y : nat -> B) : (term109 A B Z Fn c i r y) = (term110 A B Z Fn c i r y).
Proof. exact (eq_refl (term109 A B Z Fn c i r y)). Qed.
Lemma lem1065297 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Z : type1336 A B) (Fn : type1592 A B) (h1 : term102 A B Z Fn) : term110 A B Z Fn c i r y.
Proof. exact (EQ_MP (@lem1065296 A B Z Fn c i r y) (@lem1065295 A B c i r y Z Fn h1)). Qed.
Lemma lem1065298 {A B : Type'} (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (h1 : term101 A B Z r y) : term101 A B Z r y.
Proof. exact (h1). Qed.
Lemma lem1065299 {A B : Type'} (c : nat) (i : A) (Fn : type1592 A B) (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (h1 : term102 A B Z Fn) (h2 : term101 A B Z r y) : term111 A B Z Fn c i r y.
Proof. exact (@lem1065297 A B c i r y Z Fn h1 (@lem1065298 A B Z r y h2)). Qed.
Lemma lem1065300 {A B : Type'} (Fn : type1592 A B) (c : nat) (i : A) (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (h1 : term101 A B Z r y) : term951 A B Z Fn c i r y.
Proof. exact (fun h0 : term102 A B Z Fn => @lem1065299 A B c i Fn Z r y h0 h1). Qed.
Lemma lem1065301 {A B : Type'} (Z : type1336 A B) (Fn : type1592 A B) (h1 : term102 A B Z Fn) : term102 A B Z Fn.
Proof. exact (h1). Qed.
Lemma lem1065302 {A B : Type'} (c : nat) (i : A) (Fn : type1592 A B) (Z : type1336 A B) (r : type1614 A) (y : nat -> B) (h1 : term102 A B Z Fn) (h2 : term101 A B Z r y) : term111 A B Z Fn c i r y.
Proof. exact (@lem1065300 A B Fn c i Z r y h2 (@lem1065301 A B Z Fn h1)). Qed.
Lemma lem1065303 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Z : type1336 A B) (Fn : type1592 A B) (h1 : term102 A B Z Fn) : term110 A B Z Fn c i r y.
Proof. exact (fun h0 : term101 A B Z r y => @lem1065302 A B c i Fn Z r y h1 h0). Qed.
Lemma lem1065304 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (Z : type1336 A B) (Fn : type1592 A B) (h1 : term102 A B Z Fn) : term108 A B Z Fn c i r.
Proof. exact (fun y : nat -> B => @lem1065303 A B c i r y Z Fn h1). Qed.
Lemma lem1065305 {A B : Type'} (c : nat) (i : A) (Z : type1336 A B) (Fn : type1592 A B) (h1 : term102 A B Z Fn) : term106 A B Z Fn c i.
Proof. exact (fun r : type1614 A => @lem1065304 A B c i r Z Fn h1). Qed.
Lemma lem1065306 {A B : Type'} (c : nat) (Z : type1336 A B) (Fn : type1592 A B) (h1 : term102 A B Z Fn) : term104 A B Z Fn c.
Proof. exact (fun i : A => @lem1065305 A B c i Z Fn h1). Qed.
Lemma lem1065307 {A B : Type'} (Z : type1336 A B) (Fn : type1592 A B) (h1 : term102 A B Z Fn) : term102 A B Z Fn.
Proof. exact (fun c : nat => @lem1065306 A B c Z Fn h1). Qed.
Lemma lem1065308 {A B : Type'} (Z : type1336 A B) (Fn : type1592 A B) : term952 A B Z Fn.
Proof. exact (fun h0 : term102 A B Z Fn => @lem1065307 A B Z Fn h0). Qed.
Lemma lem1065309 {A B : Type'} (Z : type1336 A B) (Fn : type1592 A B) (h1 : term102 A B Z Fn) : term102 A B Z Fn.
Proof. exact (@lem1065308 A B Z Fn (@lem1062468 A B Z Fn h1)). Qed.
Lemma lem1065310 {A B : Type'} (c : nat) (Z : type1336 A B) (Fn : type1592 A B) (h1 : term102 A B Z Fn) : term103 A B Z Fn c.
Proof. exact (@lem1065309 A B Z Fn h1 c). Qed.
Lemma lem1065311 {A B : Type'} (Z : type1336 A B) (Fn : type1592 A B) (c : nat) : (term103 A B Z Fn c) = (term104 A B Z Fn c).
Proof. exact (eq_refl (term103 A B Z Fn c)). Qed.
Lemma lem1065312 {A B : Type'} (c : nat) (Z : type1336 A B) (Fn : type1592 A B) (h1 : term102 A B Z Fn) : term104 A B Z Fn c.
Proof. exact (EQ_MP (@lem1065311 A B Z Fn c) (@lem1065310 A B c Z Fn h1)). Qed.
Lemma lem1065313 {A B : Type'} (c : nat) (i : A) (Z : type1336 A B) (Fn : type1592 A B) (h1 : term102 A B Z Fn) : term105 A B Z Fn c i.
Proof. exact (@lem1065312 A B c Z Fn h1 i). Qed.
Lemma lem1065314 {A B : Type'} (Z : type1336 A B) (Fn : type1592 A B) (c : nat) (i : A) : (term105 A B Z Fn c i) = (term106 A B Z Fn c i).
Proof. exact (eq_refl (term105 A B Z Fn c i)). Qed.
Lemma lem1065315 {A B : Type'} (c : nat) (i : A) (Z : type1336 A B) (Fn : type1592 A B) (h1 : term102 A B Z Fn) : term106 A B Z Fn c i.
Proof. exact (EQ_MP (@lem1065314 A B Z Fn c i) (@lem1065313 A B c i Z Fn h1)). Qed.
Lemma lem1065316 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (Z : type1336 A B) (Fn : type1592 A B) (h1 : term102 A B Z Fn) : term107 A B Z Fn c i r.
Proof. exact (@lem1065315 A B c i Z Fn h1 r). Qed.
Lemma lem1065317 {A B : Type'} (Z : type1336 A B) (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) : (term107 A B Z Fn c i r) = (term108 A B Z Fn c i r).
Proof. exact (eq_refl (term107 A B Z Fn c i r)). Qed.
Lemma lem1065318 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (Z : type1336 A B) (Fn : type1592 A B) (h1 : term102 A B Z Fn) : term108 A B Z Fn c i r.
Proof. exact (EQ_MP (@lem1065317 A B Z Fn c i r) (@lem1065316 A B c i r Z Fn h1)). Qed.
Lemma lem1065319 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Z : type1336 A B) (Fn : type1592 A B) (h1 : term102 A B Z Fn) : term109 A B Z Fn c i r y.
Proof. exact (@lem1065318 A B c i r Z Fn h1 y). Qed.
Lemma lem1065320 {A B : Type'} (Z : type1336 A B) (Fn : type1592 A B) (c : nat) (i : A) (r : type1614 A) (y : nat -> B) : (term109 A B Z Fn c i r y) = (term110 A B Z Fn c i r y).
Proof. exact (eq_refl (term109 A B Z Fn c i r y)). Qed.
Lemma lem1065323 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Z : type1336 A B) (Fn : type1592 A B) (h1 : term102 A B Z Fn) : term110 A B Z Fn c i r y.
Proof. exact (EQ_MP (@lem1065320 A B Z Fn c i r y) (@lem1065319 A B c i r y Z Fn h1)). Qed.
Lemma lem1065324 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (y : nat -> B) (Z : type1336 A B) (Fn : type1592 A B) (h1 : term102 A B Z Fn) : term110 A B Z Fn c i r y.
Proof. exact (@lem1065323 A B c i r y Z Fn h1). Qed.
Lemma lem1065325 {A B : Type'} (c : nat) (i : A) (fn : type1337 A B) (r : type1614 A) (Z : type1336 A B) (Fn : type1592 A B) (h1 : term102 A B Z Fn) : term953 A B Z Fn c i fn r.
Proof. exact (@lem1065324 A B c i r (term954 A B fn r) Z Fn h1). Qed.
Lemma lem1065328 {A B : Type'} (fn : type1337 A B) (Z : type1336 A B) (x : recspace A) (y : B) (h1 : ((fn x) = y) = (Z x y)) : ((fn x) = y) = (Z x y).
Proof. exact (h1). Qed.
Lemma lem1065329 {A B : Type'} (fn : type1337 A B) (Z : type1336 A B) (x : recspace A) (y : B) (h1 : ((fn x) = y) = (Z x y)) : (Z x y) = ((fn x) = y).
Proof. exact (SYM (@lem1065328 A B fn Z x y h1)). Qed.
Lemma lem1065330 {A B : Type'} (Z : type1336 A B) (fn : type1337 A B) (x : recspace A) (y : B) (h1 : (Z x y) = ((fn x) = y)) : (Z x y) = ((fn x) = y).
Proof. exact (h1). Qed.
Lemma lem1065331 {A B : Type'} (Z : type1336 A B) (fn : type1337 A B) (x : recspace A) (y : B) (h1 : (Z x y) = ((fn x) = y)) : ((fn x) = y) = (Z x y).
Proof. exact (SYM (@lem1065330 A B Z fn x y h1)). Qed.
Lemma lem1065332 {A B : Type'} (Z : type1336 A B) (fn : type1337 A B) (x : recspace A) (y : B) : (((fn x) = y) = (Z x y)) = ((Z x y) = ((fn x) = y)).
Proof. exact (prop_ext (fun h1 : ((fn x) = y) = (Z x y) => @lem1065329 A B fn Z x y h1) (fun h1 : (Z x y) = ((fn x) = y) => @lem1065331 A B Z fn x y h1)). Qed.
Lemma lem1065333 {A B : Type'} (Z : type1336 A B) (fn : type1337 A B) (x : recspace A) : (term928 A B fn Z x) = (term927 A B Z fn x).
Proof. exact (fun_ext (fun y : B => @lem1065332 A B Z fn x y)). Qed.
Lemma lem1065334 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1065335 {A B : Type'} (Z : type1336 A B) (fn : type1337 A B) (x : recspace A) : (term930 A B fn Z x) = (term929 A B Z fn x).
Proof. exact (MK_COMB (@lem1065334 B) (@lem1065333 A B Z fn x)). Qed.
Lemma lem1065336 {A B : Type'} (Z : type1336 A B) (fn : type1337 A B) : (term932 A B fn Z) = (term931 A B Z fn).
Proof. exact (fun_ext (fun x : recspace A => @lem1065335 A B Z fn x)). Qed.
Lemma lem1065337 {A : Type'} : (@all (recspace A)) = (@all (recspace A)).
Proof. exact (eq_refl (@all (recspace A))). Qed.
Lemma lem1065338 {A B : Type'} (Z : type1336 A B) (fn : type1337 A B) : (term933 A B fn Z) = (term926 A B Z fn).
Proof. exact (MK_COMB (@lem1065337 A) (@lem1065336 A B Z fn)). Qed.
Lemma lem1065339 {A B : Type'} (Z : type1336 A B) (fn : type1337 A B) (h1 : term926 A B Z fn) : term926 A B Z fn.
Proof. exact (EQ_MP (@lem1065338 A B Z fn) (@lem1065195 A B Z fn h1)). Qed.
Lemma lem1065340 {A B : Type'} (x : recspace A) (Z : type1336 A B) (fn : type1337 A B) (h1 : term926 A B Z fn) : term955 A B Z fn x.
Proof. exact (@lem1065339 A B Z fn h1 x). Qed.
Lemma lem1065341 {A B : Type'} (Z : type1336 A B) (fn : type1337 A B) (x : recspace A) : (term955 A B Z fn x) = (term929 A B Z fn x).
Proof. exact (eq_refl (term955 A B Z fn x)). Qed.
Lemma lem1065342 {A B : Type'} (x : recspace A) (Z : type1336 A B) (fn : type1337 A B) (h1 : term926 A B Z fn) : term929 A B Z fn x.
Proof. exact (EQ_MP (@lem1065341 A B Z fn x) (@lem1065340 A B x Z fn h1)). Qed.
Lemma lem1065343 {A B : Type'} (x : recspace A) (y : B) (Z : type1336 A B) (fn : type1337 A B) (h1 : term926 A B Z fn) : term956 A B Z fn x y.
Proof. exact (@lem1065342 A B x Z fn h1 y). Qed.
Lemma lem1065344 {A B : Type'} (Z : type1336 A B) (fn : type1337 A B) (x : recspace A) (y : B) : (term956 A B Z fn x y) = ((Z x y) = ((fn x) = y)).
Proof. exact (eq_refl (term956 A B Z fn x y)). Qed.
Lemma lem1065347 {A B : Type'} (x : recspace A) (y : B) (Z : type1336 A B) (fn : type1337 A B) (h1 : term926 A B Z fn) : (Z x y) = ((fn x) = y).
Proof. exact (EQ_MP (@lem1065344 A B Z fn x y) (@lem1065343 A B x y Z fn h1)). Qed.
Lemma lem1065348 {A B : Type'} (x : recspace A) (y : B) (Z : type1336 A B) (fn : type1337 A B) (h1 : term926 A B Z fn) : (Z x y) = ((fn x) = y).
Proof. exact (@lem1065347 A B x y Z fn h1). Qed.
Lemma lem1065349 {A B : Type'} (r : type1614 A) (n : nat) (Z : type1336 A B) (fn : type1337 A B) (h1 : term926 A B Z fn) : (term957 A B Z fn r n) = ((term958 A B fn r n) = (term959 A B fn r n)).
Proof. exact (@lem1065348 A B (r n) (term959 A B fn r n) Z fn h1). Qed.
Lemma lem1065350 {A B : Type'} (r : type1614 A) (n : nat) (Z : type1336 A B) (fn : type1337 A B) (h1 : term926 A B Z fn) : ((term958 A B fn r n) = (term959 A B fn r n)) = (term957 A B Z fn r n).
Proof. exact (SYM (@lem1065349 A B r n Z fn h1)). Qed.
Lemma lem1065354 {A B : Type'} (f : A -> B) (y : A) : (term960 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1065355 {B : Type'} (f : nat -> B) (y : nat) : (term961 B f y) = (f y).
Proof. exact (@lem1065354 nat B f y). Qed.
Lemma lem1065356 {A B : Type'} (fn : type1337 A B) (r : type1614 A) (n : nat) : (term962 A B fn r n) = (term959 A B fn r n).
Proof. exact (@lem1065355 B (term954 A B fn r) n). Qed.
Lemma lem1065357 {A B : Type'} (fn : type1337 A B) (r : type1614 A) (n : nat) : (term959 A B fn r n) = (term958 A B fn r n).
Proof. exact (eq_refl (term959 A B fn r n)). Qed.
Lemma lem1065358 {A B : Type'} (fn : type1337 A B) (r : type1614 A) : (term963 A B fn r) = (term954 A B fn r).
Proof. exact (fun_ext (fun n : nat => @lem1065357 A B fn r n)). Qed.
Lemma lem1065359 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1065360 {A B : Type'} (fn : type1337 A B) (r : type1614 A) (n : nat) : (term962 A B fn r n) = (term959 A B fn r n).
Proof. exact (MK_COMB (@lem1065358 A B fn r) (@lem1065359 n)). Qed.
Lemma lem1065361 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem1065362 {A B : Type'} (fn : type1337 A B) (r : type1614 A) (n : nat) : (term964 A B fn r n) = (term965 A B fn r n).
Proof. exact (MK_COMB (@lem1065361 B) (@lem1065360 A B fn r n)). Qed.
Lemma lem1065363 {A B : Type'} (fn : type1337 A B) (r : type1614 A) (n : nat) : (term959 A B fn r n) = (term958 A B fn r n).
Proof. exact (eq_refl (term959 A B fn r n)). Qed.
Lemma lem1065364 {A B : Type'} (fn : type1337 A B) (r : type1614 A) (n : nat) : ((term962 A B fn r n) = (term959 A B fn r n)) = ((term959 A B fn r n) = (term958 A B fn r n)).
Proof. exact (MK_COMB (@lem1065362 A B fn r n) (@lem1065363 A B fn r n)). Qed.
Lemma lem1065365 {A B : Type'} (fn : type1337 A B) (r : type1614 A) (n : nat) : (term959 A B fn r n) = (term958 A B fn r n).
Proof. exact (EQ_MP (@lem1065364 A B fn r n) (@lem1065356 A B fn r n)). Qed.
Lemma lem1065366 {A B : Type'} (fn : type1337 A B) (r : type1614 A) (n : nat) : (term966 A B fn r n) = (term966 A B fn r n).
Proof. exact (eq_refl (term966 A B fn r n)). Qed.
Lemma lem1065367 {A B : Type'} (fn : type1337 A B) (r : type1614 A) (n : nat) : ((term958 A B fn r n) = (term959 A B fn r n)) = ((term958 A B fn r n) = (term958 A B fn r n)).
Proof. exact (MK_COMB (@lem1065366 A B fn r n) (@lem1065365 A B fn r n)). Qed.
Lemma lem1065369 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1065370 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem1065369 B x). Qed.
Lemma lem1065371 {A B : Type'} (fn : type1337 A B) (r : type1614 A) (n : nat) : ((term958 A B fn r n) = (term958 A B fn r n)) = True.
Proof. exact (@lem1065370 B (term958 A B fn r n)). Qed.
Lemma lem1065372 {A B : Type'} (fn : type1337 A B) (r : type1614 A) (n : nat) : ((term958 A B fn r n) = (term959 A B fn r n)) = True.
Proof. exact (TRANS (@lem1065367 A B fn r n) (@lem1065371 A B fn r n)). Qed.
Lemma lem1065373 {A B : Type'} (fn : type1337 A B) (r : type1614 A) (n : nat) : True = ((term958 A B fn r n) = (term959 A B fn r n)).
Proof. exact (SYM (@lem1065372 A B fn r n)). Qed.
Lemma lem1065374 {A B : Type'} (fn : type1337 A B) (r : type1614 A) (n : nat) : (term958 A B fn r n) = (term959 A B fn r n).
Proof. exact (EQ_MP (@lem1065373 A B fn r n) (@lem0)). Qed.
Lemma lem1065375 {A B : Type'} (r : type1614 A) (n : nat) (Z : type1336 A B) (fn : type1337 A B) (h1 : term926 A B Z fn) : term957 A B Z fn r n.
Proof. exact (EQ_MP (@lem1065350 A B r n Z fn h1) (@lem1065374 A B fn r n)). Qed.
Lemma lem1065380 {A B : Type'} (r : type1614 A) (Z : type1336 A B) (fn : type1337 A B) (h1 : term926 A B Z fn) : term967 A B Z fn r.
Proof. exact (fun n : nat => @lem1065375 A B r n Z fn h1). Qed.
Lemma lem1065381 {A B : Type'} (c : nat) (i : A) (r : type1614 A) (Fn : type1592 A B) (Z : type1336 A B) (fn : type1337 A B) (h1 : term102 A B Z Fn) (h2 : term926 A B Z fn) : term938 A B Z Fn c i fn r.
Proof. exact (@lem1065325 A B c i fn r Z Fn h1 (@lem1065380 A B r Z fn h2)). Qed.
Lemma lem1065386 {A B : Type'} (c : nat) (i : A) (Fn : type1592 A B) (Z : type1336 A B) (fn : type1337 A B) (h1 : term102 A B Z Fn) (h2 : term926 A B Z fn) : term942 A B Z Fn c i fn.
Proof. exact (fun r : type1614 A => @lem1065381 A B c i r Fn Z fn h1 h2). Qed.
Lemma lem1065391 {A B : Type'} (c : nat) (Fn : type1592 A B) (Z : type1336 A B) (fn : type1337 A B) (h1 : term102 A B Z Fn) (h2 : term926 A B Z fn) : term946 A B Z Fn c fn.
Proof. exact (fun i : A => @lem1065386 A B c i Fn Z fn h1 h2). Qed.
Lemma lem1065396 {A B : Type'} (Fn : type1592 A B) (Z : type1336 A B) (fn : type1337 A B) (h1 : term102 A B Z Fn) (h2 : term926 A B Z fn) : term950 A B Z Fn fn.
Proof. exact (fun c : nat => @lem1065391 A B c Fn Z fn h1 h2). Qed.
Lemma lem1065397 {A B : Type'} (Fn : type1592 A B) (Z : type1336 A B) (fn : type1337 A B) (h1 : term102 A B Z Fn) (h2 : term926 A B Z fn) : term949 A B Fn fn.
Proof. exact (EQ_MP (@lem1065266 A B Fn Z fn h2) (@lem1065396 A B Fn Z fn h1 h2)). Qed.
Lemma lem1065398 {A B : Type'} (Fn : type1592 A B) (Z : type1336 A B) (fn : type1337 A B) (h1 : term102 A B Z Fn) (h2 : term926 A B Z fn) : term923 A B Fn.
Proof. exact (ex_intro (term968 A B Fn) fn (@lem1065397 A B Fn Z fn h1 h2)). Qed.
Lemma lem1065399 {A B : Type'} (Fn : type1592 A B) (Z : type1336 A B) (h1 : term102 A B Z Fn) (h2 : term920 A B Z) : term923 A B Fn.
Proof. exact (ex_elim (@lem1065180 A B Z h2) (fun fn : type1337 A B => fun h0 : term969 A B Z fn => @lem1065398 A B Fn Z fn h1 h0)). Qed.
Lemma lem1065400 {A B : Type'} (Z : type1336 A B) (Fn : type1592 A B) (h1 : term102 A B Z Fn) : term925 A B Z Fn.
Proof. exact (fun h0 : term920 A B Z => @lem1065399 A B Fn Z h1 h0). Qed.
Lemma lem1065401 {A B : Type'} (Z : type1336 A B) (Fn : type1592 A B) (h1 : term102 A B Z Fn) : term924 A B Z Fn.
Proof. exact (EQ_MP (@lem1065179 A B Z Fn) (@lem1065400 A B Z Fn h1)). Qed.
Lemma lem1065402 {A B : Type'} (Fn : type1592 A B) (Z : type1336 A B) (h1 : term102 A B Z Fn) (h2 : term406 A B Z) : term923 A B Fn.
Proof. exact (@lem1065401 A B Z Fn h1 (@lem1062487 A B Z h2)). Qed.
Lemma lem1065403 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term102 A B Z Fn) (h2 : term260 A B b Fn Z) : (term406 A B Z) = (term923 A B Fn).
Proof. exact (prop_ext (fun h3 : term406 A B Z => @lem1065402 A B Fn Z h1 h3) (fun h3 : term923 A B Fn => @lem1065132 A B b Fn Z h2)). Qed.
Lemma lem1065404 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term102 A B Z Fn) (h2 : term260 A B b Fn Z) : term923 A B Fn.
Proof. exact (EQ_MP (@lem1065403 A B b Fn Z h1 h2) (@lem1065132 A B b Fn Z h2)). Qed.
Lemma lem1065405 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term267 A B b Fn Z) : term260 A B b Fn Z.
Proof. exact (proj2 (@lem1062470 A B b Fn Z h1)). Qed.
Lemma lem1065407 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term102 A B Z Fn) (h2 : term267 A B b Fn Z) : (term260 A B b Fn Z) = (term923 A B Fn).
Proof. exact (prop_ext (fun h3 : term260 A B b Fn Z => @lem1065404 A B b Fn Z h1 h3) (fun h3 : term923 A B Fn => @lem1065405 A B b Fn Z h2)). Qed.
Lemma lem1065408 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term102 A B Z Fn) (h2 : term267 A B b Fn Z) : term923 A B Fn.
Proof. exact (EQ_MP (@lem1065407 A B b Fn Z h1 h2) (@lem1065405 A B b Fn Z h2)). Qed.
Lemma lem1065409 {A B : Type'} (b : B) (Z : type1336 A B) (Fn : type1592 A B) (h1 : term102 A B Z Fn) : term970 A B b Z Fn.
Proof. exact (fun h0 : term267 A B b Fn Z => @lem1065408 A B b Fn Z h1 h0). Qed.
Lemma lem1065410 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term268 A B b Fn Z) : term267 A B b Fn Z.
Proof. exact (proj2 (@lem1062465 A B b Fn Z h1)). Qed.
Lemma lem1065411 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term268 A B b Fn Z) : term163 A B b Z Fn.
Proof. exact (proj1 (@lem1062465 A B b Fn Z h1)). Qed.
Lemma lem1065412 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term102 A B Z Fn) (h2 : term267 A B b Fn Z) : term923 A B Fn.
Proof. exact (@lem1065409 A B b Z Fn h1 (@lem1062466 A B b Fn Z h2)). Qed.
Lemma lem1065413 {A B : Type'} (b : B) (Z : type1336 A B) (Fn : type1592 A B) (h1 : term163 A B b Z Fn) : term102 A B Z Fn.
Proof. exact (proj2 (@lem1062467 A B b Z Fn h1)). Qed.
Lemma lem1065415 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term102 A B Z Fn) (h2 : term267 A B b Fn Z) : (term102 A B Z Fn) = (term923 A B Fn).
Proof. exact (prop_ext (fun h3 : term102 A B Z Fn => @lem1065412 A B b Fn Z h1 h2) (fun h3 : term923 A B Fn => @lem1062468 A B Z Fn h1)). Qed.
Lemma lem1065416 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term102 A B Z Fn) (h2 : term267 A B b Fn Z) : term923 A B Fn.
Proof. exact (EQ_MP (@lem1065415 A B b Fn Z h1 h2) (@lem1062468 A B Z Fn h1)). Qed.
Lemma lem1065417 {A B : Type'} (b : B) (Z : type1336 A B) (Fn : type1592 A B) (h1 : term267 A B b Fn Z) (h2 : term163 A B b Z Fn) : (term102 A B Z Fn) = (term923 A B Fn).
Proof. exact (prop_ext (fun h3 : term102 A B Z Fn => @lem1065416 A B b Fn Z h3 h1) (fun h3 : term923 A B Fn => @lem1065413 A B b Z Fn h2)). Qed.
Lemma lem1065418 {A B : Type'} (b : B) (Z : type1336 A B) (Fn : type1592 A B) (h1 : term267 A B b Fn Z) (h2 : term163 A B b Z Fn) : term923 A B Fn.
Proof. exact (EQ_MP (@lem1065417 A B b Z Fn h1 h2) (@lem1065413 A B b Z Fn h2)). Qed.
Lemma lem1065419 {A B : Type'} (b : B) (Z : type1336 A B) (Fn : type1592 A B) (h1 : term268 A B b Fn Z) (h2 : term163 A B b Z Fn) : (term267 A B b Fn Z) = (term923 A B Fn).
Proof. exact (prop_ext (fun h3 : term267 A B b Fn Z => @lem1065418 A B b Z Fn h3 h2) (fun h3 : term923 A B Fn => @lem1065410 A B b Fn Z h1)). Qed.
Lemma lem1065420 {A B : Type'} (b : B) (Z : type1336 A B) (Fn : type1592 A B) (h1 : term268 A B b Fn Z) (h2 : term163 A B b Z Fn) : term923 A B Fn.
Proof. exact (EQ_MP (@lem1065419 A B b Z Fn h1 h2) (@lem1065410 A B b Fn Z h1)). Qed.
Lemma lem1065421 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term268 A B b Fn Z) : (term163 A B b Z Fn) = (term923 A B Fn).
Proof. exact (prop_ext (fun h2 : term163 A B b Z Fn => @lem1065420 A B b Z Fn h1 h2) (fun h2 : term923 A B Fn => @lem1065411 A B b Fn Z h1)). Qed.
Lemma lem1065422 {A B : Type'} (b : B) (Fn : type1592 A B) (Z : type1336 A B) (h1 : term268 A B b Fn Z) : term923 A B Fn.
Proof. exact (EQ_MP (@lem1065421 A B b Fn Z h1) (@lem1065411 A B b Fn Z h1)). Qed.
Lemma lem1065423 {A B : Type'} (b : B) (Fn : type1592 A B) (h1 : term399 A B b Fn) : term923 A B Fn.
Proof. exact (ex_elim (@lem1062464 A B b Fn h1) (fun Z : type1336 A B => fun h0 : term393 A B b Fn Z => @lem1065422 A B b Fn Z h0)). Qed.
Lemma lem1065424 {A B : Type'} (b : B) (Fn : type1592 A B) : term971 A B b Fn.
Proof. exact (fun h0 : term399 A B b Fn => @lem1065423 A B b Fn h0). Qed.
Lemma lem1065425 {A B : Type'} (Fn : type1592 A B) : term923 A B Fn.
Proof. exact (@lem1065424 A B (@el B) Fn (@lem1062463 A B (@el B) Fn)). Qed.
Lemma lem1065430 {A B : Type'} : term972 A B.
Proof. exact (fun Fn : type1592 A B => @lem1065425 A B Fn). Qed.
