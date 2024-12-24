Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm89762_term_abbrevs.
Require Import BETA_THM_spec.
Require Import SKOLEM_THM_spec.
Require Import thm75635_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem89513 {A B : Type'} (f : A -> B) : term0 A B f.
Proof. exact (@lem421 A B f). Qed.
Lemma lem89514 {A B : Type'} (f : A -> B) : (term0 A B f) = (term1 A B f).
Proof. exact (eq_refl (term0 A B f)). Qed.
Lemma lem89515 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (EQ_MP (@lem89514 A B f) (@lem89513 A B f)). Qed.
Lemma lem89516 {A B : Type'} (f : A -> B) (y : A) : term2 A B f y.
Proof. exact (@lem89515 A B f y). Qed.
Lemma lem89517 {A B : Type'} (f : A -> B) (y : A) : (term2 A B f y) = ((term3 A B f y) = (f y)).
Proof. exact (eq_refl (term2 A B f y)). Qed.
Lemma lem89520 (lt : type1605) (_2244 : type1605) (h1 : lt = (term4 _2244)) : lt = (term4 _2244).
Proof. exact (h1). Qed.
Lemma lem89521 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem89522 (m : nat) (lt : type1605) (_2244 : type1605) (h1 : lt = (term4 _2244)) : (lt m) = (term5 _2244 m).
Proof. exact (MK_COMB (@lem89520 lt _2244 h1) (@lem89521 m)). Qed.
Lemma lem89524 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem89517 A B f y) (@lem89516 A B f y)). Qed.
Lemma lem89525 (f : type1605) (y : nat) : (term6 f y) = (f y).
Proof. exact (@lem89524 nat (nat -> Prop) f y). Qed.
Lemma lem89526 (_2244 : type1605) (m : nat) : (term7 _2244 m) = (term5 _2244 m).
Proof. exact (@lem89525 (term4 _2244) m). Qed.
Lemma lem89527 (_2244 : type1605) (_2242 : nat) : (term5 _2244 _2242) = (term8 _2244 _2242).
Proof. exact (eq_refl (term5 _2244 _2242)). Qed.
Lemma lem89528 (_2244 : type1605) : (term9 _2244) = (term4 _2244).
Proof. exact (fun_ext (fun _2242 : nat => @lem89527 _2244 _2242)). Qed.
Lemma lem89529 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem89530 (_2244 : type1605) (m : nat) : (term7 _2244 m) = (term5 _2244 m).
Proof. exact (MK_COMB (@lem89528 _2244) (@lem89529 m)). Qed.
Lemma lem89531 : (@eq (nat -> Prop)) = (@eq (nat -> Prop)).
Proof. exact (eq_refl (@eq (nat -> Prop))). Qed.
Lemma lem89532 (_2244 : type1605) (m : nat) : (term10 _2244 m) = (term11 _2244 m).
Proof. exact (MK_COMB (@lem89531) (@lem89530 _2244 m)). Qed.
Lemma lem89533 (_2244 : type1605) (m : nat) : (term5 _2244 m) = (term8 _2244 m).
Proof. exact (eq_refl (term5 _2244 m)). Qed.
Lemma lem89534 (_2244 : type1605) (m : nat) : ((term7 _2244 m) = (term5 _2244 m)) = ((term5 _2244 m) = (term8 _2244 m)).
Proof. exact (MK_COMB (@lem89532 _2244 m) (@lem89533 _2244 m)). Qed.
Lemma lem89535 (_2244 : type1605) (m : nat) : (term5 _2244 m) = (term8 _2244 m).
Proof. exact (EQ_MP (@lem89534 _2244 m) (@lem89526 _2244 m)). Qed.
Lemma lem89536 (m : nat) (lt : type1605) (_2244 : type1605) (h1 : lt = (term4 _2244)) : (lt m) = (term8 _2244 m).
Proof. exact (TRANS (@lem89522 m lt _2244 h1) (@lem89535 _2244 m)). Qed.
Lemma lem89537 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem89538 (m : nat) (lt : type1605) (_2244 : type1605) (h1 : lt = (term4 _2244)) : (term12 lt m) = (term13 _2244 m).
Proof. exact (MK_COMB (@lem89536 m lt _2244 h1) (@lem89537)). Qed.
Lemma lem89540 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem89517 A B f y) (@lem89516 A B f y)). Qed.
Lemma lem89541 (f : nat -> Prop) (y : nat) : (term14 f y) = (f y).
Proof. exact (@lem89540 nat Prop f y). Qed.
Lemma lem89542 (_2244 : type1605) (m : nat) : (term15 _2244 m) = (term13 _2244 m).
Proof. exact (@lem89541 (term8 _2244 m) (NUMERAL 0)). Qed.
Lemma lem89543 (_2244 : type1605) (_2243 : nat) (m : nat) : (term16 _2244 m _2243) = (_2244 _2243 m).
Proof. exact (eq_refl (term16 _2244 m _2243)). Qed.
Lemma lem89544 (_2244 : type1605) (m : nat) : (term17 _2244 m) = (term8 _2244 m).
Proof. exact (fun_ext (fun _2243 : nat => @lem89543 _2244 _2243 m)). Qed.
Lemma lem89545 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem89546 (_2244 : type1605) (m : nat) : (term15 _2244 m) = (term13 _2244 m).
Proof. exact (MK_COMB (@lem89544 _2244 m) (@lem89545)). Qed.
Lemma lem89547 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem89548 (_2244 : type1605) (m : nat) : (term18 _2244 m) = (term19 _2244 m).
Proof. exact (MK_COMB (@lem89547) (@lem89546 _2244 m)). Qed.
Lemma lem89549 (_2244 : type1605) (m : nat) : (term13 _2244 m) = (term20 _2244 m).
Proof. exact (eq_refl (term13 _2244 m)). Qed.
Lemma lem89550 (_2244 : type1605) (m : nat) : ((term15 _2244 m) = (term13 _2244 m)) = ((term13 _2244 m) = (term20 _2244 m)).
Proof. exact (MK_COMB (@lem89548 _2244 m) (@lem89549 _2244 m)). Qed.
Lemma lem89551 (_2244 : type1605) (m : nat) : (term13 _2244 m) = (term20 _2244 m).
Proof. exact (EQ_MP (@lem89550 _2244 m) (@lem89542 _2244 m)). Qed.
Lemma lem89552 (m : nat) (lt : type1605) (_2244 : type1605) (h1 : lt = (term4 _2244)) : (term12 lt m) = (term20 _2244 m).
Proof. exact (TRANS (@lem89538 m lt _2244 h1) (@lem89551 _2244 m)). Qed.
Lemma lem89553 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem89554 (m : nat) (lt : type1605) (_2244 : type1605) (h1 : lt = (term4 _2244)) : (term21 lt m) = (term22 _2244 m).
Proof. exact (MK_COMB (@lem89553) (@lem89552 m lt _2244 h1)). Qed.
Lemma lem89555 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem89556 (m : nat) (lt : type1605) (_2244 : type1605) (h1 : lt = (term4 _2244)) : ((term12 lt m) = False) = ((term20 _2244 m) = False).
Proof. exact (MK_COMB (@lem89554 m lt _2244 h1) (@lem89555)). Qed.
Lemma lem89557 (lt : type1605) (_2244 : type1605) (h1 : lt = (term4 _2244)) : (term23 lt) = (term24 _2244).
Proof. exact (fun_ext (fun m : nat => @lem89556 m lt _2244 h1)). Qed.
Lemma lem89558 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem89559 (lt : type1605) (_2244 : type1605) (h1 : lt = (term4 _2244)) : (term25 lt) = (term26 _2244).
Proof. exact (MK_COMB (@lem89558) (@lem89557 lt _2244 h1)). Qed.
Lemma lem89560 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem89561 (lt : type1605) (_2244 : type1605) (h1 : lt = (term4 _2244)) : (term27 lt) = (term28 _2244).
Proof. exact (MK_COMB (@lem89560) (@lem89559 lt _2244 h1)). Qed.
Lemma lem89563 (lt : type1605) (_2244 : type1605) (h1 : lt = (term4 _2244)) : lt = (term4 _2244).
Proof. exact (h1). Qed.
Lemma lem89564 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem89565 (m : nat) (lt : type1605) (_2244 : type1605) (h1 : lt = (term4 _2244)) : (lt m) = (term5 _2244 m).
Proof. exact (MK_COMB (@lem89563 lt _2244 h1) (@lem89564 m)). Qed.
Lemma lem89567 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem89517 A B f y) (@lem89516 A B f y)). Qed.
Lemma lem89568 (f : type1605) (y : nat) : (term6 f y) = (f y).
Proof. exact (@lem89567 nat (nat -> Prop) f y). Qed.
Lemma lem89569 (_2244 : type1605) (m : nat) : (term7 _2244 m) = (term5 _2244 m).
Proof. exact (@lem89568 (term4 _2244) m). Qed.
Lemma lem89570 (_2244 : type1605) (_2242 : nat) : (term5 _2244 _2242) = (term8 _2244 _2242).
Proof. exact (eq_refl (term5 _2244 _2242)). Qed.
Lemma lem89571 (_2244 : type1605) : (term9 _2244) = (term4 _2244).
Proof. exact (fun_ext (fun _2242 : nat => @lem89570 _2244 _2242)). Qed.
Lemma lem89572 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem89573 (_2244 : type1605) (m : nat) : (term7 _2244 m) = (term5 _2244 m).
Proof. exact (MK_COMB (@lem89571 _2244) (@lem89572 m)). Qed.
Lemma lem89574 : (@eq (nat -> Prop)) = (@eq (nat -> Prop)).
Proof. exact (eq_refl (@eq (nat -> Prop))). Qed.
Lemma lem89575 (_2244 : type1605) (m : nat) : (term10 _2244 m) = (term11 _2244 m).
Proof. exact (MK_COMB (@lem89574) (@lem89573 _2244 m)). Qed.
Lemma lem89576 (_2244 : type1605) (m : nat) : (term5 _2244 m) = (term8 _2244 m).
Proof. exact (eq_refl (term5 _2244 m)). Qed.
Lemma lem89577 (_2244 : type1605) (m : nat) : ((term7 _2244 m) = (term5 _2244 m)) = ((term5 _2244 m) = (term8 _2244 m)).
Proof. exact (MK_COMB (@lem89575 _2244 m) (@lem89576 _2244 m)). Qed.
Lemma lem89578 (_2244 : type1605) (m : nat) : (term5 _2244 m) = (term8 _2244 m).
Proof. exact (EQ_MP (@lem89577 _2244 m) (@lem89569 _2244 m)). Qed.
Lemma lem89579 (m : nat) (lt : type1605) (_2244 : type1605) (h1 : lt = (term4 _2244)) : (lt m) = (term8 _2244 m).
Proof. exact (TRANS (@lem89565 m lt _2244 h1) (@lem89578 _2244 m)). Qed.
Lemma lem89580 (n : nat) : (S n) = (S n).
Proof. exact (eq_refl (S n)). Qed.
Lemma lem89581 (m : nat) (n : nat) (lt : type1605) (_2244 : type1605) (h1 : lt = (term4 _2244)) : (term29 lt m n) = (term30 _2244 m n).
Proof. exact (MK_COMB (@lem89579 m lt _2244 h1) (@lem89580 n)). Qed.
Lemma lem89583 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem89517 A B f y) (@lem89516 A B f y)). Qed.
Lemma lem89584 (f : nat -> Prop) (y : nat) : (term14 f y) = (f y).
Proof. exact (@lem89583 nat Prop f y). Qed.
Lemma lem89585 (_2244 : type1605) (m : nat) (n : nat) : (term31 _2244 m n) = (term30 _2244 m n).
Proof. exact (@lem89584 (term8 _2244 m) (S n)). Qed.
Lemma lem89586 (_2244 : type1605) (_2243 : nat) (m : nat) : (term16 _2244 m _2243) = (_2244 _2243 m).
Proof. exact (eq_refl (term16 _2244 m _2243)). Qed.
Lemma lem89587 (_2244 : type1605) (m : nat) : (term17 _2244 m) = (term8 _2244 m).
Proof. exact (fun_ext (fun _2243 : nat => @lem89586 _2244 _2243 m)). Qed.
Lemma lem89588 (n : nat) : (S n) = (S n).
Proof. exact (eq_refl (S n)). Qed.
Lemma lem89589 (_2244 : type1605) (m : nat) (n : nat) : (term31 _2244 m n) = (term30 _2244 m n).
Proof. exact (MK_COMB (@lem89587 _2244 m) (@lem89588 n)). Qed.
Lemma lem89590 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem89591 (_2244 : type1605) (m : nat) (n : nat) : (term32 _2244 m n) = (term33 _2244 m n).
Proof. exact (MK_COMB (@lem89590) (@lem89589 _2244 m n)). Qed.
Lemma lem89592 (_2244 : type1605) (n : nat) (m : nat) : (term30 _2244 m n) = (term34 _2244 n m).
Proof. exact (eq_refl (term30 _2244 m n)). Qed.
Lemma lem89593 (_2244 : type1605) (n : nat) (m : nat) : ((term31 _2244 m n) = (term30 _2244 m n)) = ((term30 _2244 m n) = (term34 _2244 n m)).
Proof. exact (MK_COMB (@lem89591 _2244 m n) (@lem89592 _2244 n m)). Qed.
Lemma lem89594 (_2244 : type1605) (n : nat) (m : nat) : (term30 _2244 m n) = (term34 _2244 n m).
Proof. exact (EQ_MP (@lem89593 _2244 n m) (@lem89585 _2244 m n)). Qed.
Lemma lem89595 (n : nat) (m : nat) (lt : type1605) (_2244 : type1605) (h1 : lt = (term4 _2244)) : (term29 lt m n) = (term34 _2244 n m).
Proof. exact (TRANS (@lem89581 m n lt _2244 h1) (@lem89594 _2244 n m)). Qed.
Lemma lem89596 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem89597 (n : nat) (m : nat) (lt : type1605) (_2244 : type1605) (h1 : lt = (term4 _2244)) : (term35 lt m n) = (term36 _2244 n m).
Proof. exact (MK_COMB (@lem89596) (@lem89595 n m lt _2244 h1)). Qed.
Lemma lem89599 (lt : type1605) (_2244 : type1605) (h1 : lt = (term4 _2244)) : lt = (term4 _2244).
Proof. exact (h1). Qed.
Lemma lem89600 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem89601 (m : nat) (lt : type1605) (_2244 : type1605) (h1 : lt = (term4 _2244)) : (lt m) = (term5 _2244 m).
Proof. exact (MK_COMB (@lem89599 lt _2244 h1) (@lem89600 m)). Qed.
Lemma lem89603 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem89517 A B f y) (@lem89516 A B f y)). Qed.
Lemma lem89604 (f : type1605) (y : nat) : (term6 f y) = (f y).
Proof. exact (@lem89603 nat (nat -> Prop) f y). Qed.
Lemma lem89605 (_2244 : type1605) (m : nat) : (term7 _2244 m) = (term5 _2244 m).
Proof. exact (@lem89604 (term4 _2244) m). Qed.
Lemma lem89606 (_2244 : type1605) (_2242 : nat) : (term5 _2244 _2242) = (term8 _2244 _2242).
Proof. exact (eq_refl (term5 _2244 _2242)). Qed.
Lemma lem89607 (_2244 : type1605) : (term9 _2244) = (term4 _2244).
Proof. exact (fun_ext (fun _2242 : nat => @lem89606 _2244 _2242)). Qed.
Lemma lem89608 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem89609 (_2244 : type1605) (m : nat) : (term7 _2244 m) = (term5 _2244 m).
Proof. exact (MK_COMB (@lem89607 _2244) (@lem89608 m)). Qed.
Lemma lem89610 : (@eq (nat -> Prop)) = (@eq (nat -> Prop)).
Proof. exact (eq_refl (@eq (nat -> Prop))). Qed.
Lemma lem89611 (_2244 : type1605) (m : nat) : (term10 _2244 m) = (term11 _2244 m).
Proof. exact (MK_COMB (@lem89610) (@lem89609 _2244 m)). Qed.
Lemma lem89612 (_2244 : type1605) (m : nat) : (term5 _2244 m) = (term8 _2244 m).
Proof. exact (eq_refl (term5 _2244 m)). Qed.
Lemma lem89613 (_2244 : type1605) (m : nat) : ((term7 _2244 m) = (term5 _2244 m)) = ((term5 _2244 m) = (term8 _2244 m)).
Proof. exact (MK_COMB (@lem89611 _2244 m) (@lem89612 _2244 m)). Qed.
Lemma lem89614 (_2244 : type1605) (m : nat) : (term5 _2244 m) = (term8 _2244 m).
Proof. exact (EQ_MP (@lem89613 _2244 m) (@lem89605 _2244 m)). Qed.
Lemma lem89615 (m : nat) (lt : type1605) (_2244 : type1605) (h1 : lt = (term4 _2244)) : (lt m) = (term8 _2244 m).
Proof. exact (TRANS (@lem89601 m lt _2244 h1) (@lem89614 _2244 m)). Qed.
Lemma lem89616 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem89617 (m : nat) (n : nat) (lt : type1605) (_2244 : type1605) (h1 : lt = (term4 _2244)) : (lt m n) = (term16 _2244 m n).
Proof. exact (MK_COMB (@lem89615 m lt _2244 h1) (@lem89616 n)). Qed.
Lemma lem89619 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem89517 A B f y) (@lem89516 A B f y)). Qed.
Lemma lem89620 (f : nat -> Prop) (y : nat) : (term14 f y) = (f y).
Proof. exact (@lem89619 nat Prop f y). Qed.
Lemma lem89621 (_2244 : type1605) (m : nat) (n : nat) : (term37 _2244 m n) = (term16 _2244 m n).
Proof. exact (@lem89620 (term8 _2244 m) n). Qed.
Lemma lem89622 (_2244 : type1605) (_2243 : nat) (m : nat) : (term16 _2244 m _2243) = (_2244 _2243 m).
Proof. exact (eq_refl (term16 _2244 m _2243)). Qed.
Lemma lem89623 (_2244 : type1605) (m : nat) : (term17 _2244 m) = (term8 _2244 m).
Proof. exact (fun_ext (fun _2243 : nat => @lem89622 _2244 _2243 m)). Qed.
Lemma lem89624 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem89625 (_2244 : type1605) (m : nat) (n : nat) : (term37 _2244 m n) = (term16 _2244 m n).
Proof. exact (MK_COMB (@lem89623 _2244 m) (@lem89624 n)). Qed.
Lemma lem89626 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem89627 (_2244 : type1605) (m : nat) (n : nat) : (term38 _2244 m n) = (term39 _2244 m n).
Proof. exact (MK_COMB (@lem89626) (@lem89625 _2244 m n)). Qed.
Lemma lem89628 (_2244 : type1605) (n : nat) (m : nat) : (term16 _2244 m n) = (_2244 n m).
Proof. exact (eq_refl (term16 _2244 m n)). Qed.
Lemma lem89629 (_2244 : type1605) (n : nat) (m : nat) : ((term37 _2244 m n) = (term16 _2244 m n)) = ((term16 _2244 m n) = (_2244 n m)).
Proof. exact (MK_COMB (@lem89627 _2244 m n) (@lem89628 _2244 n m)). Qed.
Lemma lem89630 (_2244 : type1605) (n : nat) (m : nat) : (term16 _2244 m n) = (_2244 n m).
Proof. exact (EQ_MP (@lem89629 _2244 n m) (@lem89621 _2244 m n)). Qed.
Lemma lem89631 (n : nat) (m : nat) (lt : type1605) (_2244 : type1605) (h1 : lt = (term4 _2244)) : (lt m n) = (_2244 n m).
Proof. exact (TRANS (@lem89617 m n lt _2244 h1) (@lem89630 _2244 n m)). Qed.
Lemma lem89632 (m : nat) (n : nat) : (term40 m n) = (term40 m n).
Proof. exact (eq_refl (term40 m n)). Qed.
Lemma lem89633 (n : nat) (m : nat) (lt : type1605) (_2244 : type1605) (h1 : lt = (term4 _2244)) : (term41 lt m n) = (term42 _2244 n m).
Proof. exact (MK_COMB (@lem89632 m n) (@lem89631 n m lt _2244 h1)). Qed.
Lemma lem89634 (n : nat) (m : nat) (lt : type1605) (_2244 : type1605) (h1 : lt = (term4 _2244)) : ((term29 lt m n) = (term41 lt m n)) = ((term34 _2244 n m) = (term42 _2244 n m)).
Proof. exact (MK_COMB (@lem89597 n m lt _2244 h1) (@lem89633 n m lt _2244 h1)). Qed.
Lemma lem89635 (m : nat) (lt : type1605) (_2244 : type1605) (h1 : lt = (term4 _2244)) : (term43 lt m) = (term44 _2244 m).
Proof. exact (fun_ext (fun n : nat => @lem89634 n m lt _2244 h1)). Qed.
Lemma lem89636 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem89637 (m : nat) (lt : type1605) (_2244 : type1605) (h1 : lt = (term4 _2244)) : (term45 lt m) = (term46 _2244 m).
Proof. exact (MK_COMB (@lem89636) (@lem89635 m lt _2244 h1)). Qed.
Lemma lem89638 (lt : type1605) (_2244 : type1605) (h1 : lt = (term4 _2244)) : (term47 lt) = (term48 _2244).
Proof. exact (fun_ext (fun m : nat => @lem89637 m lt _2244 h1)). Qed.
Lemma lem89639 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem89640 (lt : type1605) (_2244 : type1605) (h1 : lt = (term4 _2244)) : (term49 lt) = (term50 _2244).
Proof. exact (MK_COMB (@lem89639) (@lem89638 lt _2244 h1)). Qed.
Lemma lem89641 (lt : type1605) (_2244 : type1605) (h1 : lt = (term4 _2244)) : (term51 lt) = (term52 _2244).
Proof. exact (MK_COMB (@lem89561 lt _2244 h1) (@lem89640 lt _2244 h1)). Qed.
Lemma lem89642 (_2244 : type1605) (h1 : (term53 _2244) = term54) : (term53 _2244) = term54.
Proof. exact (h1). Qed.
Lemma lem89643 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem89644 (m : nat) (_2244 : type1605) (h1 : (term53 _2244) = term54) : (term20 _2244 m) = (term55 m).
Proof. exact (MK_COMB (@lem89642 _2244 h1) (@lem89643 m)). Qed.
Lemma lem89645 (m : nat) : (term55 m) = False.
Proof. exact (eq_refl (term55 m)). Qed.
Lemma lem89646 (_2244 : type1605) (m : nat) : (term22 _2244 m) = (term22 _2244 m).
Proof. exact (eq_refl (term22 _2244 m)). Qed.
Lemma lem89647 (_2244 : type1605) (m : nat) : ((term20 _2244 m) = (term55 m)) = ((term20 _2244 m) = False).
Proof. exact (MK_COMB (@lem89646 _2244 m) (@lem89645 m)). Qed.
Lemma lem89648 (m : nat) (_2244 : type1605) (h1 : (term53 _2244) = term54) : (term20 _2244 m) = False.
Proof. exact (EQ_MP (@lem89647 _2244 m) (@lem89644 m _2244 h1)). Qed.
Lemma lem89649 (_2244 : type1605) (h1 : (term53 _2244) = term54) : term26 _2244.
Proof. exact (fun m : nat => @lem89648 m _2244 h1). Qed.
Lemma lem89650 (_2244 : type1605) (h1 : term56 _2244) : term56 _2244.
Proof. exact (h1). Qed.
Lemma lem89651 (n : nat) (_2244 : type1605) (h1 : term56 _2244) : term57 _2244 n.
Proof. exact (@lem89650 _2244 h1 n). Qed.
Lemma lem89652 (_2244 : type1605) (n : nat) : (term57 _2244 n) = ((term58 _2244 n) = (term59 _2244 n)).
Proof. exact (eq_refl (term57 _2244 n)). Qed.
Lemma lem89653 (n : nat) (_2244 : type1605) (h1 : term56 _2244) : (term58 _2244 n) = (term59 _2244 n).
Proof. exact (EQ_MP (@lem89652 _2244 n) (@lem89651 n _2244 h1)). Qed.
Lemma lem89654 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem89655 (n : nat) (m : nat) (_2244 : type1605) (h1 : term56 _2244) : (term34 _2244 n m) = (term60 _2244 n m).
Proof. exact (MK_COMB (@lem89653 n _2244 h1) (@lem89654 m)). Qed.
Lemma lem89656 (_2244 : type1605) (n : nat) (m : nat) : (term60 _2244 n m) = (term42 _2244 n m).
Proof. exact (eq_refl (term60 _2244 n m)). Qed.
Lemma lem89657 (_2244 : type1605) (n : nat) (m : nat) : (term36 _2244 n m) = (term36 _2244 n m).
Proof. exact (eq_refl (term36 _2244 n m)). Qed.
Lemma lem89658 (_2244 : type1605) (n : nat) (m : nat) : ((term34 _2244 n m) = (term60 _2244 n m)) = ((term34 _2244 n m) = (term42 _2244 n m)).
Proof. exact (MK_COMB (@lem89657 _2244 n m) (@lem89656 _2244 n m)). Qed.
Lemma lem89659 (n : nat) (m : nat) (_2244 : type1605) (h1 : term56 _2244) : (term34 _2244 n m) = (term42 _2244 n m).
Proof. exact (EQ_MP (@lem89658 _2244 n m) (@lem89655 n m _2244 h1)). Qed.
Lemma lem89660 (m : nat) (_2244 : type1605) (h1 : term56 _2244) : term46 _2244 m.
Proof. exact (fun n : nat => @lem89659 n m _2244 h1). Qed.
Lemma lem89661 (_2244 : type1605) (h1 : term56 _2244) : term50 _2244.
Proof. exact (fun m : nat => @lem89660 m _2244 h1). Qed.
Lemma lem89662 (_2244 : type1605) (h1 : term61 _2244) : term61 _2244.
Proof. exact (h1). Qed.
Lemma lem89663 (_2244 : type1605) (h1 : term61 _2244) : term56 _2244.
Proof. exact (proj2 (@lem89662 _2244 h1)). Qed.
Lemma lem89664 (_2244 : type1605) (h1 : term61 _2244) : (term53 _2244) = term54.
Proof. exact (proj1 (@lem89662 _2244 h1)). Qed.
Lemma lem89665 (_2244 : type1605) (h1 : term61 _2244) : ((term53 _2244) = term54) = (term26 _2244).
Proof. exact (prop_ext (fun h2 : (term53 _2244) = term54 => @lem89649 _2244 h2) (fun h2 : term26 _2244 => @lem89664 _2244 h1)). Qed.
Lemma lem89666 (_2244 : type1605) (h1 : term61 _2244) : term26 _2244.
Proof. exact (EQ_MP (@lem89665 _2244 h1) (@lem89664 _2244 h1)). Qed.
Lemma lem89667 (_2244 : type1605) (h1 : term61 _2244) : (term56 _2244) = (term50 _2244).
Proof. exact (prop_ext (fun h2 : term56 _2244 => @lem89661 _2244 h2) (fun h2 : term50 _2244 => @lem89663 _2244 h1)). Qed.
Lemma lem89668 (_2244 : type1605) (h1 : term61 _2244) : term50 _2244.
Proof. exact (EQ_MP (@lem89667 _2244 h1) (@lem89663 _2244 h1)). Qed.
Lemma lem89669 (_2244 : type1605) (h1 : term61 _2244) : term52 _2244.
Proof. exact (conj (@lem89666 _2244 h1) (@lem89668 _2244 h1)). Qed.
Lemma lem89670 {A : Type'} (e : A) : term62 A e.
Proof. exact (@lem75635 A e). Qed.
Lemma lem89671 {A : Type'} (e : A) : (term62 A e) = (term63 A e).
Proof. exact (eq_refl (term62 A e)). Qed.
Lemma lem89672 {A : Type'} (e : A) : term63 A e.
Proof. exact (EQ_MP (@lem89671 A e) (@lem89670 A e)). Qed.
Lemma lem89673 {A : Type'} (e : A) (f : type1423 A) : term64 A e f.
Proof. exact (@lem89672 A e f). Qed.
Lemma lem89674 {A : Type'} (e : A) (f : type1423 A) : (term64 A e f) = (term65 A e f).
Proof. exact (eq_refl (term64 A e f)). Qed.
Lemma lem89675 {A : Type'} (e : A) (f : type1423 A) : term65 A e f.
Proof. exact (EQ_MP (@lem89674 A e f) (@lem89673 A e f)). Qed.
Lemma lem89676 (e : nat -> Prop) (f : type990) : term66 e f.
Proof. exact (@lem89675 (nat -> Prop) e f). Qed.
Lemma lem89677 : term67.
Proof. exact (@lem89676 term54 term68). Qed.
Lemma lem89678 (fn : type1605) (n : nat) : (term69 fn n) = (term70 fn n).
Proof. exact (eq_refl (term69 fn n)). Qed.
Lemma lem89679 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem89680 (fn : type1605) (n : nat) : (term71 fn n) = (term72 fn n).
Proof. exact (MK_COMB (@lem89678 fn n) (@lem89679 n)). Qed.
Lemma lem89681 (fn : type1605) (n : nat) : (term72 fn n) = (term59 fn n).
Proof. exact (eq_refl (term72 fn n)). Qed.
Lemma lem89682 (fn : type1605) (n : nat) : (term71 fn n) = (term59 fn n).
Proof. exact (TRANS (@lem89680 fn n) (@lem89681 fn n)). Qed.
Lemma lem89683 (fn : type1605) (n : nat) : (term73 fn n) = (term73 fn n).
Proof. exact (eq_refl (term73 fn n)). Qed.
Lemma lem89684 (fn : type1605) (n : nat) : ((term58 fn n) = (term71 fn n)) = ((term58 fn n) = (term59 fn n)).
Proof. exact (MK_COMB (@lem89683 fn n) (@lem89682 fn n)). Qed.
Lemma lem89685 (fn : type1605) : (term74 fn) = (term75 fn).
Proof. exact (fun_ext (fun n : nat => @lem89684 fn n)). Qed.
Lemma lem89686 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem89687 (fn : type1605) : (term76 fn) = (term56 fn).
Proof. exact (MK_COMB (@lem89686) (@lem89685 fn)). Qed.
Lemma lem89688 (fn : type1605) : (term77 fn) = (term77 fn).
Proof. exact (eq_refl (term77 fn)). Qed.
Lemma lem89689 (fn : type1605) : (term78 fn) = (term61 fn).
Proof. exact (MK_COMB (@lem89688 fn) (@lem89687 fn)). Qed.
Lemma lem89690 : term79 = term80.
Proof. exact (fun_ext (fun fn : type1605 => @lem89689 fn)). Qed.
Lemma lem89691 : (@ex (nat -> nat -> Prop)) = (@ex (nat -> nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> nat -> Prop))). Qed.
Lemma lem89692 : term67 = term81.
Proof. exact (MK_COMB (@lem89691) (@lem89690)). Qed.
Lemma lem89693 : term81.
Proof. exact (EQ_MP (@lem89692) (@lem89677)). Qed.
Lemma lem89694 (_2244 : type1605) (h1 : term61 _2244) : term61 _2244.
Proof. exact (h1). Qed.
Lemma lem89695 (_2244 : type1605) (h1 : term61 _2244) : term56 _2244.
Proof. exact (proj2 (@lem89694 _2244 h1)). Qed.
Lemma lem89696 (_2244 : type1605) (h1 : term61 _2244) : (term53 _2244) = term54.
Proof. exact (proj1 (@lem89694 _2244 h1)). Qed.
Lemma lem89697 (_2244 : type1605) (h1 : term61 _2244) : term61 _2244.
Proof. exact (conj (@lem89696 _2244 h1) (@lem89695 _2244 h1)). Qed.
Lemma lem89698 (_2244 : type1605) (h1 : term61 _2244) : term81.
Proof. exact (ex_intro term80 _2244 (@lem89697 _2244 h1)). Qed.
Lemma lem89699 (h1 : term81) : term81.
Proof. exact (h1). Qed.
Lemma lem89700 (h1 : term81) : term81.
Proof. exact (ex_elim (@lem89699 h1) (fun _2244 : type1605 => fun h0 : term80 _2244 => @lem89698 _2244 h0)). Qed.
Lemma lem89701 : term81 = term81.
Proof. exact (prop_ext (fun h1 : term81 => @lem89700 h1) (fun h1 : term81 => @lem89693)). Qed.
Lemma lem89702 : term81.
Proof. exact (EQ_MP (@lem89701) (@lem89693)). Qed.
Lemma lem89703 (_2244 : type1605) (h1 : term61 _2244) : term82.
Proof. exact (ex_intro term83 _2244 (@lem89669 _2244 h1)). Qed.
Lemma lem89704 (h1 : term81) : term81.
Proof. exact (h1). Qed.
Lemma lem89705 (h1 : term81) : term82.
Proof. exact (ex_elim (@lem89704 h1) (fun _2244 : type1605 => fun h0 : term80 _2244 => @lem89703 _2244 h0)). Qed.
Lemma lem89706 : term81 = term82.
Proof. exact (prop_ext (fun h1 : term81 => @lem89705 h1) (fun h1 : term82 => @lem89702)). Qed.
Lemma lem89707 : term82.
Proof. exact (EQ_MP (@lem89706) (@lem89702)). Qed.
Lemma lem89708 (_2244 : type1605) (h1 : term52 _2244) : term52 _2244.
Proof. exact (h1). Qed.
Lemma lem89709 (lt : type1605) (_2244 : type1605) (h1 : lt = (term4 _2244)) : (term52 _2244) = (term51 lt).
Proof. exact (SYM (@lem89641 lt _2244 h1)). Qed.
Lemma lem89710 (lt : type1605) (_2244 : type1605) (h1 : term52 _2244) (h2 : lt = (term4 _2244)) : term51 lt.
Proof. exact (EQ_MP (@lem89709 lt _2244 h2) (@lem89708 _2244 h1)). Qed.
Lemma lem89711 (lt : type1605) (_2244 : type1605) (h1 : term52 _2244) (h2 : lt = (term4 _2244)) : term84.
Proof. exact (ex_intro term85 lt (@lem89710 lt _2244 h1 h2)). Qed.
Lemma lem89712 (_2244 : type1605) : (term4 _2244) = (term4 _2244).
Proof. exact (eq_refl (term4 _2244)). Qed.
Lemma lem89713 (lt : type1605) (_2244 : type1605) (h1 : term52 _2244) : term86 lt _2244.
Proof. exact (fun h0 : lt = (term4 _2244) => @lem89711 lt _2244 h1 h0). Qed.
Lemma lem89714 (_2244 : type1605) (h1 : term52 _2244) : term87 _2244.
Proof. exact (@lem89713 (term4 _2244) _2244 h1). Qed.
Lemma lem89715 (_2244 : type1605) (h1 : term52 _2244) : term84.
Proof. exact (@lem89714 _2244 h1 (@lem89712 _2244)). Qed.
Lemma lem89716 (h1 : term82) : term82.
Proof. exact (h1). Qed.
Lemma lem89717 (h1 : term82) : term84.
Proof. exact (ex_elim (@lem89716 h1) (fun _2244 : type1605 => fun h0 : term83 _2244 => @lem89715 _2244 h0)). Qed.
Lemma lem89718 : term82 = term84.
Proof. exact (prop_ext (fun h1 : term82 => @lem89717 h1) (fun h1 : term84 => @lem89707)). Qed.
Lemma lem89719 : term84.
Proof. exact (EQ_MP (@lem89718) (@lem89707)). Qed.
Lemma lem89720 : term88.
Proof. exact (fun _2248 : nat => @lem89719). Qed.
Lemma lem89721 {A B : Type'} (P : type1413 A B) : term89 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem89722 {A B : Type'} (P : type1413 A B) : (term89 A B P) = ((term90 A B P) = (term91 A B P)).
Proof. exact (eq_refl (term89 A B P)). Qed.
Lemma lem89725 {A B : Type'} (P : type1413 A B) : (term90 A B P) = (term91 A B P).
Proof. exact (EQ_MP (@lem89722 A B P) (@lem89721 A B P)). Qed.
Lemma lem89726 (P : type1580) : (term92 P) = (term93 P).
Proof. exact (@lem89725 nat type1605 P). Qed.
Lemma lem89727 : term94 = term95.
Proof. exact (@lem89726 term96). Qed.
Lemma lem89728 (_2248 : nat) : (term97 _2248) = term85.
Proof. exact (eq_refl (term97 _2248)). Qed.
Lemma lem89729 (lt : type1605) : lt = lt.
Proof. exact (eq_refl lt). Qed.
Lemma lem89730 (_2248 : nat) (lt : type1605) : (term98 _2248 lt) = (term99 lt).
Proof. exact (MK_COMB (@lem89728 _2248) (@lem89729 lt)). Qed.
Lemma lem89731 (lt : type1605) : (term99 lt) = (term51 lt).
Proof. exact (eq_refl (term99 lt)). Qed.
Lemma lem89732 (_2248 : nat) (lt : type1605) : (term98 _2248 lt) = (term51 lt).
Proof. exact (TRANS (@lem89730 _2248 lt) (@lem89731 lt)). Qed.
Lemma lem89733 (_2248 : nat) : (term100 _2248) = term85.
Proof. exact (fun_ext (fun lt : type1605 => @lem89732 _2248 lt)). Qed.
Lemma lem89734 : (@ex (nat -> nat -> Prop)) = (@ex (nat -> nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> nat -> Prop))). Qed.
Lemma lem89735 (_2248 : nat) : (term101 _2248) = term84.
Proof. exact (MK_COMB (@lem89734) (@lem89733 _2248)). Qed.
Lemma lem89736 : term102 = term103.
Proof. exact (fun_ext (fun _2248 : nat => @lem89735 _2248)). Qed.
Lemma lem89737 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem89738 : term94 = term88.
Proof. exact (MK_COMB (@lem89737) (@lem89736)). Qed.
Lemma lem89739 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem89740 : term104 = term105.
Proof. exact (MK_COMB (@lem89739) (@lem89738)). Qed.
Lemma lem89741 (_2248 : nat) : (term97 _2248) = term85.
Proof. exact (eq_refl (term97 _2248)). Qed.
Lemma lem89742 (lt : type1601) (_2248 : nat) : (lt _2248) = (lt _2248).
Proof. exact (eq_refl (lt _2248)). Qed.
Lemma lem89743 (lt : type1601) (_2248 : nat) : (term106 lt _2248) = (term107 lt _2248).
Proof. exact (MK_COMB (@lem89741 _2248) (@lem89742 lt _2248)). Qed.
Lemma lem89744 (lt : type1601) (_2248 : nat) : (term107 lt _2248) = (term108 lt _2248).
Proof. exact (eq_refl (term107 lt _2248)). Qed.
Lemma lem89745 (lt : type1601) (_2248 : nat) : (term106 lt _2248) = (term108 lt _2248).
Proof. exact (TRANS (@lem89743 lt _2248) (@lem89744 lt _2248)). Qed.
Lemma lem89746 (lt : type1601) : (term109 lt) = (term110 lt).
Proof. exact (fun_ext (fun _2248 : nat => @lem89745 lt _2248)). Qed.
Lemma lem89747 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem89748 (lt : type1601) : (term111 lt) = (term112 lt).
Proof. exact (MK_COMB (@lem89747) (@lem89746 lt)). Qed.
Lemma lem89749 : term113 = term114.
Proof. exact (fun_ext (fun lt : type1601 => @lem89748 lt)). Qed.
Lemma lem89750 : (@ex (nat -> nat -> nat -> Prop)) = (@ex (nat -> nat -> nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> nat -> nat -> Prop))). Qed.
Lemma lem89751 : term95 = term115.
Proof. exact (MK_COMB (@lem89750) (@lem89749)). Qed.
Lemma lem89752 : (term94 = term95) = (term88 = term115).
Proof. exact (MK_COMB (@lem89740) (@lem89751)). Qed.
Lemma lem89753 : term88 = term115.
Proof. exact (EQ_MP (@lem89752) (@lem89727)). Qed.
Lemma lem89754 : term115.
Proof. exact (EQ_MP (@lem89753) (@lem89720)). Qed.
Lemma lem89756 {A : Type'} : (@ex A) = (term116 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem89757 : (@ex (nat -> nat -> nat -> Prop)) = term117.
Proof. exact (@lem89756 type1601). Qed.
Lemma lem89758 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem89759 : term115 = term118.
Proof. exact (MK_COMB (@lem89757) (@lem89758)). Qed.
Lemma lem89760 : term118 = term119.
Proof. exact (eq_refl term118). Qed.
Lemma lem89761 : term115 = term119.
Proof. exact (TRANS (@lem89759) (@lem89760)). Qed.
Lemma lem89762 : term119.
Proof. exact (EQ_MP (@lem89761) (@lem89754)). Qed.
