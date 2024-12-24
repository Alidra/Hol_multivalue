Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_INDEX_NUMSEG_term_abbrevs.
Require Import CARD_EQ_BIJECTIONS_spec.
Require Import CARD_NUMSEG_1_spec.
Require Import DISJ_ACI_spec.
Require Import FINITE_IMAGE_spec.
Require Import FINITE_NUMSEG_spec.
Require Import MONO_EXISTS_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm1820_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19490_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm32_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211656_spec.
Require Import thm3211657_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Lemma lem5418341 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem5418342 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term1 A P Q) : term1 A P Q.
Proof. exact (h1). Qed.
Lemma lem5418343 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term1 A P Q) (h2 : term0 A P Q) : term2 A P Q.
Proof. exact (@lem5418341 A P Q h2 (@lem5418342 A P Q h1)). Qed.
Lemma lem5418344 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term1 A P Q) : term3 A P Q.
Proof. exact (fun h0 : term0 A P Q => @lem5418343 A P Q h1 h0). Qed.
Lemma lem5418345 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem5418346 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term1 A P Q) (h2 : term0 A P Q) : term2 A P Q.
Proof. exact (@lem5418344 A P Q h1 (@lem5418345 A P Q h2)). Qed.
Lemma lem5418347 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (fun h0 : term1 A P Q => @lem5418346 A P Q h0 h1). Qed.
Lemma lem5418348 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term4 A P Q.
Proof. exact (fun h0 : term0 A P Q => @lem5418347 A P Q h0). Qed.
Lemma lem5418350 {A : Type'} : term5 A.
Proof. exact (@lem5073217 nat A). Qed.
Lemma lem5418351 {A : Type'} (s : A -> Prop) : term6 A s.
Proof. exact (@lem5418350 A (term7 A s)). Qed.
Lemma lem5418352 {A : Type'} (s : A -> Prop) : (term6 A s) = (term8 A s).
Proof. exact (eq_refl (term6 A s)). Qed.
Lemma lem5418353 {A : Type'} (s : A -> Prop) : term8 A s.
Proof. exact (EQ_MP (@lem5418352 A s) (@lem5418351 A s)). Qed.
Lemma lem5418354 {A : Type'} (s : A -> Prop) : term9 A s.
Proof. exact (@lem5418353 A s s). Qed.
Lemma lem5418355 {A : Type'} (s : A -> Prop) : (term9 A s) = (term10 A s).
Proof. exact (eq_refl (term9 A s)). Qed.
Lemma lem5418356 {A : Type'} (s : A -> Prop) : term10 A s.
Proof. exact (EQ_MP (@lem5418355 A s) (@lem5418354 A s)). Qed.
Lemma lem5418367 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem5418369 (p : Prop) : p = (term11 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5418370 {A : Type'} (s : A -> Prop) : (term12 A s) = (term13 A s).
Proof. exact (@lem5418369 (term12 A s)). Qed.
Lemma lem5418371 {A : Type'} (s : A -> Prop) : (term13 A s) = (term12 A s).
Proof. exact (SYM (@lem5418370 A s)). Qed.
Lemma lem5418372 {A : Type'} (s : A -> Prop) (h1 : term14 A s) : term14 A s.
Proof. exact (h1). Qed.
Lemma lem5418373 {A B : Type'} : term15 A B.
Proof. exact (@lem3615104 A B). Qed.
Lemma lem5418374 {A : Type'} : term16 A.
Proof. exact (@lem3615104 A A). Qed.
Lemma lem5418375 {A : Type'} : term17 A.
Proof. exact (@lem3615104 nat A). Qed.
Lemma lem5418378 {A B : Type'} (s : A -> Prop) (h1 : term18 A B s) : term18 A B s.
Proof. exact (h1). Qed.
Lemma lem5418379 {A B : Type'} (s : A -> Prop) : term19 A B s.
Proof. exact (fun h0 : term18 A B s => @lem5418378 A B s h0). Qed.
Lemma lem5418380 {A B : Type'} (s : A -> Prop) (h1 : term19 A B s) : term19 A B s.
Proof. exact (h1). Qed.
Lemma lem5418381 {A B : Type'} (s : A -> Prop) (h1 : term18 A B s) : term18 A B s.
Proof. exact (h1). Qed.
Lemma lem5418382 {A B : Type'} (s : A -> Prop) (h1 : term18 A B s) (h2 : term19 A B s) : term18 A B s.
Proof. exact (@lem5418380 A B s h2 (@lem5418381 A B s h1)). Qed.
Lemma lem5418383 {A B : Type'} (s : A -> Prop) (h1 : term18 A B s) : term20 A B s.
Proof. exact (fun h0 : term19 A B s => @lem5418382 A B s h1 h0). Qed.
Lemma lem5418384 {A B : Type'} (s : A -> Prop) (h1 : term19 A B s) : term19 A B s.
Proof. exact (h1). Qed.
Lemma lem5418385 {A B : Type'} (s : A -> Prop) (h1 : term18 A B s) (h2 : term19 A B s) : term18 A B s.
Proof. exact (@lem5418383 A B s h1 (@lem5418384 A B s h2)). Qed.
Lemma lem5418386 {A B : Type'} (s : A -> Prop) (h1 : term19 A B s) : term19 A B s.
Proof. exact (fun h0 : term18 A B s => @lem5418385 A B s h0 h1). Qed.
Lemma lem5418387 {A B : Type'} (s : A -> Prop) : term21 A B s.
Proof. exact (fun h0 : term19 A B s => @lem5418386 A B s h0). Qed.
Lemma lem5418390 {A B : Type'} (s : A -> Prop) : term19 A B s.
Proof. exact (@lem5418387 A B s (@lem5418379 A B s)). Qed.
Lemma lem5418391 {A B : Type'} (s : A -> Prop) : term19 A B s.
Proof. exact (@lem5418390 A B s). Qed.
Lemma lem5418499 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5418500 {A : Type'} : (term22 A) = (term23 A).
Proof. exact (@lem5418499 (term17 A)). Qed.
Lemma lem5418511 {A B : Type'} : (term24 A B) = (term24 A B).
Proof. exact (eq_refl (term24 A B)). Qed.
Lemma lem5418512 {A B : Type'} : (term25 A B) = (term26 A B).
Proof. exact (MK_COMB (@lem5418511 A B) (@lem5418500 A)). Qed.
Lemma lem5418515 {A : Type'} : (term27 A) = (term27 A).
Proof. exact (eq_refl (term27 A)). Qed.
Lemma lem5418516 {A B : Type'} : (term28 A B) = (term29 A B).
Proof. exact (MK_COMB (@lem5418515 A) (@lem5418512 A B)). Qed.
Lemma lem5418519 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem5418520 {A B : Type'} : (term31 A B) = (term32 A B).
Proof. exact (MK_COMB (@lem5418519) (@lem5418516 A B)). Qed.
Lemma lem5418523 {A : Type'} (s : A -> Prop) : (term33 A s) = (term33 A s).
Proof. exact (eq_refl (term33 A s)). Qed.
Lemma lem5418524 {A B : Type'} (s : A -> Prop) : (term18 A B s) = (term34 A B s).
Proof. exact (MK_COMB (@lem5418523 A s) (@lem5418520 A B)). Qed.
Lemma lem5418527 {A B : Type'} : (term35 A B) = (term36 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5418524 A B s)). Qed.
Lemma lem5418528 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5418537 {A B : Type'} : (term37 A B) = (term38 A B).
Proof. exact (MK_COMB (@lem5418528 A) (@lem5418527 A B)). Qed.
Lemma lem5418542 {A : Type'} (f : nat -> A) (s : nat -> Prop) : (term39 A f s) = (term39 A f s).
Proof. exact (eq_refl (term39 A f s)). Qed.
Lemma lem5418543 {A : Type'} (f : nat -> A) : (term40 A f) = (term40 A f).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem5418542 A f s)). Qed.
Lemma lem5418544 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5418545 {A : Type'} (f : nat -> A) : (term41 A f) = (term41 A f).
Proof. exact (MK_COMB (@lem5418544) (@lem5418543 A f)). Qed.
Lemma lem5418546 {A : Type'} : (term42 A) = (term42 A).
Proof. exact (fun_ext (fun f : nat -> A => @lem5418545 A f)). Qed.
Lemma lem5418547 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem5418548 {A : Type'} : (term17 A) = (term17 A).
Proof. exact (MK_COMB (@lem5418547 A) (@lem5418546 A)). Qed.
Lemma lem5418549 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5418550 {A : Type'} : (term23 A) = (term23 A).
Proof. exact (MK_COMB (@lem5418549) (@lem5418548 A)). Qed.
Lemma lem5418555 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term43 A B f s) = (term43 A B f s).
Proof. exact (eq_refl (term43 A B f s)). Qed.
Lemma lem5418556 {A B : Type'} (f : A -> B) : (term44 A B f) = (term44 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5418555 A B f s)). Qed.
Lemma lem5418557 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5418558 {A B : Type'} (f : A -> B) : (term45 A B f) = (term45 A B f).
Proof. exact (MK_COMB (@lem5418557 A) (@lem5418556 A B f)). Qed.
Lemma lem5418559 {A B : Type'} : (term46 A B) = (term46 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem5418558 A B f)). Qed.
Lemma lem5418560 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5418561 {A B : Type'} : (term15 A B) = (term15 A B).
Proof. exact (MK_COMB (@lem5418560 A B) (@lem5418559 A B)). Qed.
Lemma lem5418562 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5418563 {A B : Type'} : (term24 A B) = (term24 A B).
Proof. exact (MK_COMB (@lem5418562) (@lem5418561 A B)). Qed.
Lemma lem5418564 {A B : Type'} : (term26 A B) = (term26 A B).
Proof. exact (MK_COMB (@lem5418563 A B) (@lem5418550 A)). Qed.
Lemma lem5418569 {A : Type'} (f : A -> A) (s : A -> Prop) : (term47 A f s) = (term47 A f s).
Proof. exact (eq_refl (term47 A f s)). Qed.
Lemma lem5418570 {A : Type'} (f : A -> A) : (term48 A f) = (term48 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5418569 A f s)). Qed.
Lemma lem5418571 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5418572 {A : Type'} (f : A -> A) : (term49 A f) = (term49 A f).
Proof. exact (MK_COMB (@lem5418571 A) (@lem5418570 A f)). Qed.
Lemma lem5418573 {A : Type'} : (term50 A) = (term50 A).
Proof. exact (fun_ext (fun f : A -> A => @lem5418572 A f)). Qed.
Lemma lem5418574 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem5418575 {A : Type'} : (term16 A) = (term16 A).
Proof. exact (MK_COMB (@lem5418574 A) (@lem5418573 A)). Qed.
Lemma lem5418576 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5418577 {A : Type'} : (term27 A) = (term27 A).
Proof. exact (MK_COMB (@lem5418576) (@lem5418575 A)). Qed.
Lemma lem5418578 {A B : Type'} : (term29 A B) = (term29 A B).
Proof. exact (MK_COMB (@lem5418577 A) (@lem5418564 A B)). Qed.
Lemma lem5418579 (m : nat) (n : nat) : (term51 m n) = (term51 m n).
Proof. exact (eq_refl (term51 m n)). Qed.
Lemma lem5418580 (m : nat) : (term52 m) = (term52 m).
Proof. exact (fun_ext (fun n : nat => @lem5418579 m n)). Qed.
Lemma lem5418581 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5418582 (m : nat) : (term53 m) = (term53 m).
Proof. exact (MK_COMB (@lem5418581) (@lem5418580 m)). Qed.
Lemma lem5418583 : term54 = term54.
Proof. exact (fun_ext (fun m : nat => @lem5418582 m)). Qed.
Lemma lem5418584 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5418585 : term55 = term55.
Proof. exact (MK_COMB (@lem5418584) (@lem5418583)). Qed.
Lemma lem5418586 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5418587 : term30 = term30.
Proof. exact (MK_COMB (@lem5418586) (@lem5418585)). Qed.
Lemma lem5418588 {A B : Type'} : (term32 A B) = (term32 A B).
Proof. exact (MK_COMB (@lem5418587) (@lem5418578 A B)). Qed.
Lemma lem5418589 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem5418590 {A : Type'} (f : nat -> A) (s : A -> Prop) : (s = (term56 A f s)) = (s = (term56 A f s)).
Proof. exact (eq_refl (s = (term56 A f s))). Qed.
Lemma lem5418603 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) : (term57 A s f i j) = (term57 A s f i j).
Proof. exact (eq_refl (term57 A s f i j)). Qed.
Lemma lem5418604 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) : (term58 A s f i) = (term58 A s f i).
Proof. exact (fun_ext (fun j : nat => @lem5418603 A s f i j)). Qed.
Lemma lem5418605 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5418606 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) : (term59 A s f i) = (term59 A s f i).
Proof. exact (MK_COMB (@lem5418605) (@lem5418604 A s f i)). Qed.
Lemma lem5418607 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term60 A s f) = (term60 A s f).
Proof. exact (fun_ext (fun i : nat => @lem5418606 A s f i)). Qed.
Lemma lem5418608 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5418609 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term61 A s f) = (term61 A s f).
Proof. exact (MK_COMB (@lem5418608) (@lem5418607 A s f)). Qed.
Lemma lem5418610 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5418611 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term62 A s f) = (term62 A s f).
Proof. exact (MK_COMB (@lem5418610) (@lem5418609 A s f)). Qed.
Lemma lem5418612 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term63 A f s) = (term63 A f s).
Proof. exact (MK_COMB (@lem5418611 A s f) (@lem5418590 A f s)). Qed.
Lemma lem5418613 {A : Type'} (s : A -> Prop) : (term64 A s) = (term64 A s).
Proof. exact (fun_ext (fun f : nat -> A => @lem5418612 A f s)). Qed.
Lemma lem5418614 {A : Type'} : (@ex (nat -> A)) = (@ex (nat -> A)).
Proof. exact (eq_refl (@ex (nat -> A))). Qed.
Lemma lem5418615 {A : Type'} (s : A -> Prop) : (term65 A s) = (term65 A s).
Proof. exact (MK_COMB (@lem5418614 A) (@lem5418613 A s)). Qed.
Lemma lem5418616 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5418617 {A : Type'} (s : A -> Prop) : (term66 A s) = (term66 A s).
Proof. exact (MK_COMB (@lem5418616) (@lem5418615 A s)). Qed.
Lemma lem5418618 {A : Type'} (s : A -> Prop) : (term12 A s) = (term12 A s).
Proof. exact (MK_COMB (@lem5418617 A s) (@lem5418589 A s)). Qed.
Lemma lem5418619 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5418620 {A : Type'} (s : A -> Prop) : (term14 A s) = (term14 A s).
Proof. exact (MK_COMB (@lem5418619) (@lem5418618 A s)). Qed.
Lemma lem5418621 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5418622 {A : Type'} (s : A -> Prop) : (term33 A s) = (term33 A s).
Proof. exact (MK_COMB (@lem5418621) (@lem5418620 A s)). Qed.
Lemma lem5418623 {A B : Type'} (s : A -> Prop) : (term34 A B s) = (term34 A B s).
Proof. exact (MK_COMB (@lem5418622 A s) (@lem5418588 A B)). Qed.
Lemma lem5418624 {A B : Type'} : (term36 A B) = (term36 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5418623 A B s)). Qed.
Lemma lem5418625 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5418626 {A B : Type'} : (term38 A B) = (term38 A B).
Proof. exact (MK_COMB (@lem5418625 A) (@lem5418624 A B)). Qed.
Lemma lem5418725 {A B : Type'} : (term37 A B) = (term38 A B).
Proof. exact (TRANS (@lem5418537 A B) (@lem5418626 A B)). Qed.
Lemma lem5418726 {A B : Type'} : (term38 A B) = (term37 A B).
Proof. exact (SYM (@lem5418725 A B)). Qed.
Lemma lem5418727 {A : Type'} (s : A -> Prop) (h1 : term14 A s) : term14 A s.
Proof. exact (h1). Qed.
Lemma lem5418728 (h1 : term55) : term55.
Proof. exact (h1). Qed.
Lemma lem5418731 {A : Type'} (h1 : term17 A) : term17 A.
Proof. exact (h1). Qed.
Lemma lem5418739 {A : Type'} (s : A -> Prop) (i : nat) (f : nat -> A) (j : nat) : (term67 A s i f j) = (term68 A s i f j).
Proof. exact (@lem17045 (term69 A j s) ((f i) = (f j))). Qed.
Lemma lem5418741 {A : Type'} (i : nat) (s : A -> Prop) : (term70 A i s) = (term70 A i s).
Proof. exact (eq_refl (term70 A i s)). Qed.
Lemma lem5418742 {A : Type'} (s : A -> Prop) (i : nat) (f : nat -> A) (j : nat) : (term71 A s i f j) = (term72 A s i f j).
Proof. exact (MK_COMB (@lem5418741 A i s) (@lem5418739 A s i f j)). Qed.
Lemma lem5418743 {A : Type'} (s : A -> Prop) (i : nat) (f : nat -> A) (j : nat) : (term73 A s i f j) = (term71 A s i f j).
Proof. exact (@lem17045 (term69 A i s) (term74 A s i f j)). Qed.
Lemma lem5418744 {A : Type'} (s : A -> Prop) (i : nat) (f : nat -> A) (j : nat) : (term73 A s i f j) = (term72 A s i f j).
Proof. exact (TRANS (@lem5418743 A s i f j) (@lem5418742 A s i f j)). Qed.
Lemma lem5418745 (i : nat) (j : nat) : (i = j) = (i = j).
Proof. exact (eq_refl (i = j)). Qed.
Lemma lem5418746 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5418747 {A : Type'} (s : A -> Prop) (i : nat) (f : nat -> A) (j : nat) : (term75 A s i f j) = (term76 A s i f j).
Proof. exact (MK_COMB (@lem5418746) (@lem5418744 A s i f j)). Qed.
Lemma lem5418748 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) : (term77 A s f i j) = (term78 A s f i j).
Proof. exact (MK_COMB (@lem5418747 A s i f j) (@lem5418745 i j)). Qed.
Lemma lem5418749 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) : (term57 A s f i j) = (term77 A s f i j).
Proof. exact (@lem17265 (term79 A s i f j) (i = j)). Qed.
Lemma lem5418750 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) : (term57 A s f i j) = (term78 A s f i j).
Proof. exact (TRANS (@lem5418749 A s f i j) (@lem5418748 A s f i j)). Qed.
Lemma lem5418751 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) : (term58 A s f i) = (term80 A s f i).
Proof. exact (fun_ext (fun j : nat => @lem5418750 A s f i j)). Qed.
Lemma lem5418752 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5418753 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) : (term59 A s f i) = (term81 A s f i).
Proof. exact (MK_COMB (@lem5418752) (@lem5418751 A s f i)). Qed.
Lemma lem5418754 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term60 A s f) = (term82 A s f).
Proof. exact (fun_ext (fun i : nat => @lem5418753 A s f i)). Qed.
Lemma lem5418755 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5418756 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term61 A s f) = (term83 A s f).
Proof. exact (MK_COMB (@lem5418755) (@lem5418754 A s f)). Qed.
Lemma lem5418757 {A : Type'} (f : nat -> A) (s : A -> Prop) : (s = (term56 A f s)) = (s = (term56 A f s)).
Proof. exact (eq_refl (s = (term56 A f s))). Qed.
Lemma lem5418758 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5418759 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term62 A s f) = (term84 A s f).
Proof. exact (MK_COMB (@lem5418758) (@lem5418756 A s f)). Qed.
Lemma lem5418760 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term63 A f s) = (term85 A f s).
Proof. exact (MK_COMB (@lem5418759 A s f) (@lem5418757 A f s)). Qed.
Lemma lem5418761 {A : Type'} (s : A -> Prop) : (term64 A s) = (term86 A s).
Proof. exact (fun_ext (fun f : nat -> A => @lem5418760 A f s)). Qed.
Lemma lem5418762 {A : Type'} : (@ex (nat -> A)) = (@ex (nat -> A)).
Proof. exact (eq_refl (@ex (nat -> A))). Qed.
Lemma lem5418763 {A : Type'} (s : A -> Prop) : (term65 A s) = (term87 A s).
Proof. exact (MK_COMB (@lem5418762 A) (@lem5418761 A s)). Qed.
Lemma lem5418764 {A : Type'} (s : A -> Prop) : (term88 A s) = (term88 A s).
Proof. exact (eq_refl (term88 A s)). Qed.
Lemma lem5418765 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5418766 {A : Type'} (s : A -> Prop) : (term89 A s) = (term90 A s).
Proof. exact (MK_COMB (@lem5418765) (@lem5418763 A s)). Qed.
Lemma lem5418767 {A : Type'} (s : A -> Prop) : (term91 A s) = (term92 A s).
Proof. exact (MK_COMB (@lem5418766 A s) (@lem5418764 A s)). Qed.
Lemma lem5418768 {A : Type'} (s : A -> Prop) : (term14 A s) = (term91 A s).
Proof. exact (@lem17362 (term65 A s) (@FINITE A s)). Qed.
Lemma lem5418769 {A : Type'} (s : A -> Prop) : (term14 A s) = (term92 A s).
Proof. exact (TRANS (@lem5418768 A s) (@lem5418767 A s)). Qed.
Lemma lem5418872 {A : Type'} (P : A -> Prop) (Q : Prop) : (term93 A P Q) = (term94 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5418873 {A : Type'} (P : type976 A) (Q : Prop) : (term95 A P Q) = (term96 A P Q).
Proof. exact (@lem5418872 (nat -> A) P Q). Qed.
Lemma lem5418874 {A : Type'} (s : A -> Prop) : (term97 A s) = (term98 A s).
Proof. exact (@lem5418873 A (term86 A s) (term88 A s)). Qed.
Lemma lem5418875 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term99 A s f) = (term85 A f s).
Proof. exact (eq_refl (term99 A s f)). Qed.
Lemma lem5418876 {A : Type'} (s : A -> Prop) : (term100 A s) = (term86 A s).
Proof. exact (fun_ext (fun f : nat -> A => @lem5418875 A f s)). Qed.
Lemma lem5418877 {A : Type'} : (@ex (nat -> A)) = (@ex (nat -> A)).
Proof. exact (eq_refl (@ex (nat -> A))). Qed.
Lemma lem5418878 {A : Type'} (s : A -> Prop) : (term101 A s) = (term87 A s).
Proof. exact (MK_COMB (@lem5418877 A) (@lem5418876 A s)). Qed.
Lemma lem5418879 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5418880 {A : Type'} (s : A -> Prop) : (term102 A s) = (term90 A s).
Proof. exact (MK_COMB (@lem5418879) (@lem5418878 A s)). Qed.
Lemma lem5418881 {A : Type'} (s : A -> Prop) : (term88 A s) = (term88 A s).
Proof. exact (eq_refl (term88 A s)). Qed.
Lemma lem5418882 {A : Type'} (s : A -> Prop) : (term97 A s) = (term92 A s).
Proof. exact (MK_COMB (@lem5418880 A s) (@lem5418881 A s)). Qed.
Lemma lem5418883 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5418884 {A : Type'} (s : A -> Prop) : (term103 A s) = (term104 A s).
Proof. exact (MK_COMB (@lem5418883) (@lem5418882 A s)). Qed.
Lemma lem5418885 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term99 A s f) = (term85 A f s).
Proof. exact (eq_refl (term99 A s f)). Qed.
Lemma lem5418886 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5418887 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term105 A s f) = (term106 A f s).
Proof. exact (MK_COMB (@lem5418886) (@lem5418885 A f s)). Qed.
Lemma lem5418888 {A : Type'} (s : A -> Prop) : (term88 A s) = (term88 A s).
Proof. exact (eq_refl (term88 A s)). Qed.
Lemma lem5418889 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term107 A f s) = (term108 A f s).
Proof. exact (MK_COMB (@lem5418887 A f s) (@lem5418888 A s)). Qed.
Lemma lem5418890 {A : Type'} (s : A -> Prop) : (term109 A s) = (term110 A s).
Proof. exact (fun_ext (fun f : nat -> A => @lem5418889 A f s)). Qed.
Lemma lem5418891 {A : Type'} : (@ex (nat -> A)) = (@ex (nat -> A)).
Proof. exact (eq_refl (@ex (nat -> A))). Qed.
Lemma lem5418892 {A : Type'} (s : A -> Prop) : (term98 A s) = (term111 A s).
Proof. exact (MK_COMB (@lem5418891 A) (@lem5418890 A s)). Qed.
Lemma lem5418893 {A : Type'} (s : A -> Prop) : ((term97 A s) = (term98 A s)) = ((term92 A s) = (term111 A s)).
Proof. exact (MK_COMB (@lem5418884 A s) (@lem5418892 A s)). Qed.
Lemma lem5418895 {A : Type'} (s : A -> Prop) : (term92 A s) = (term111 A s).
Proof. exact (EQ_MP (@lem5418893 A s) (@lem5418874 A s)). Qed.
Lemma lem5418896 {A : Type'} (s : A -> Prop) : (term14 A s) = (term111 A s).
Proof. exact (TRANS (@lem5418769 A s) (@lem5418895 A s)). Qed.
Lemma lem5418897 {A : Type'} (s : A -> Prop) (h1 : term14 A s) : term111 A s.
Proof. exact (EQ_MP (@lem5418896 A s) (@lem5418727 A s h1)). Qed.
Lemma lem5418898 (m : nat) (n : nat) : (term51 m n) = (term51 m n).
Proof. exact (eq_refl (term51 m n)). Qed.
Lemma lem5418899 (m : nat) : (term52 m) = (term52 m).
Proof. exact (fun_ext (fun n : nat => @lem5418898 m n)). Qed.
Lemma lem5418900 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5418901 (m : nat) : (term53 m) = (term53 m).
Proof. exact (MK_COMB (@lem5418900) (@lem5418899 m)). Qed.
Lemma lem5418902 : term54 = term54.
Proof. exact (fun_ext (fun m : nat => @lem5418901 m)). Qed.
Lemma lem5418903 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5418916 : term55 = term55.
Proof. exact (MK_COMB (@lem5418903) (@lem5418902)). Qed.
Lemma lem5418917 (h1 : term55) : term55.
Proof. exact (EQ_MP (@lem5418916) (@lem5418728 h1)). Qed.
Lemma lem5419064 {A : Type'} (f : nat -> A) (s : nat -> Prop) : (term39 A f s) = (term112 A f s).
Proof. exact (@lem17265 (@FINITE nat s) (term113 A f s)). Qed.
Lemma lem5419065 {A : Type'} (f : nat -> A) : (term40 A f) = (term114 A f).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem5419064 A f s)). Qed.
Lemma lem5419066 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5419067 {A : Type'} (f : nat -> A) : (term41 A f) = (term115 A f).
Proof. exact (MK_COMB (@lem5419066) (@lem5419065 A f)). Qed.
Lemma lem5419068 {A : Type'} : (term42 A) = (term116 A).
Proof. exact (fun_ext (fun f : nat -> A => @lem5419067 A f)). Qed.
Lemma lem5419069 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem5419126 {A : Type'} : (term17 A) = (term117 A).
Proof. exact (MK_COMB (@lem5419069 A) (@lem5419068 A)). Qed.
Lemma lem5419127 {A : Type'} (h1 : term17 A) : term117 A.
Proof. exact (EQ_MP (@lem5419126 A) (@lem5418731 A h1)). Qed.
Lemma lem5419128 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term108 A f s) : term108 A f s.
Proof. exact (h1). Qed.
Lemma lem5419135 (m : nat) (n : nat) : (term51 m n) = (term51 m n).
Proof. exact (eq_refl (term51 m n)). Qed.
Lemma lem5419136 (m : nat) : (term52 m) = (term52 m).
Proof. exact (fun_ext (fun n : nat => @lem5419135 m n)). Qed.
Lemma lem5419137 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5419138 (m : nat) : (term53 m) = (term53 m).
Proof. exact (MK_COMB (@lem5419137) (@lem5419136 m)). Qed.
Lemma lem5419139 : term54 = term54.
Proof. exact (fun_ext (fun m : nat => @lem5419138 m)). Qed.
Lemma lem5419140 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5419141 : term55 = term55.
Proof. exact (MK_COMB (@lem5419140) (@lem5419139)). Qed.
Lemma lem5419142 (h1 : term55) : term55.
Proof. exact (EQ_MP (@lem5419141) (@lem5418917 h1)). Qed.
Lemma lem5419201 {A : Type'} (f : nat -> A) (s : nat -> Prop) : (term112 A f s) = (term112 A f s).
Proof. exact (eq_refl (term112 A f s)). Qed.
Lemma lem5419202 {A : Type'} (f : nat -> A) : (term114 A f) = (term114 A f).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem5419201 A f s)). Qed.
Lemma lem5419203 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5419204 {A : Type'} (f : nat -> A) : (term115 A f) = (term115 A f).
Proof. exact (MK_COMB (@lem5419203) (@lem5419202 A f)). Qed.
Lemma lem5419205 {A : Type'} : (term116 A) = (term116 A).
Proof. exact (fun_ext (fun f : nat -> A => @lem5419204 A f)). Qed.
Lemma lem5419206 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem5419207 {A : Type'} : (term117 A) = (term117 A).
Proof. exact (MK_COMB (@lem5419206 A) (@lem5419205 A)). Qed.
Lemma lem5419208 {A : Type'} (h1 : term17 A) : term117 A.
Proof. exact (EQ_MP (@lem5419207 A) (@lem5419127 A h1)). Qed.
Lemma lem5419213 {A : Type'} (s : A -> Prop) : (term88 A s) = (term88 A s).
Proof. exact (eq_refl (term88 A s)). Qed.
Lemma lem5419232 {A : Type'} (f : nat -> A) (s : A -> Prop) : (s = (term56 A f s)) = (s = (term56 A f s)).
Proof. exact (eq_refl (s = (term56 A f s))). Qed.
Lemma lem5419237 (i : nat) (j : nat) : (i = j) = (i = j).
Proof. exact (eq_refl (i = j)). Qed.
Lemma lem5419238 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5419239 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem5419244 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5419245 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem5419244 nat A f x). Qed.
Lemma lem5419247 {A : Type'} (f : nat -> A) (i : nat) : (f i) = (@I (nat -> A) f i).
Proof. exact (@lem5419245 A f i). Qed.
Lemma lem5419252 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5419253 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem5419252 nat A f x). Qed.
Lemma lem5419255 {A : Type'} (f : nat -> A) (j : nat) : (f j) = (@I (nat -> A) f j).
Proof. exact (@lem5419253 A f j). Qed.
Lemma lem5419256 {A : Type'} (f : nat -> A) (i : nat) : (term118 A f i) = (term119 A f i).
Proof. exact (MK_COMB (@lem5419239 A) (@lem5419247 A f i)). Qed.
Lemma lem5419257 {A : Type'} (i : nat) (f : nat -> A) (j : nat) : ((f i) = (f j)) = ((@I (nat -> A) f i) = (@I (nat -> A) f j)).
Proof. exact (MK_COMB (@lem5419256 A f i) (@lem5419255 A f j)). Qed.
Lemma lem5419258 {A : Type'} (i : nat) (f : nat -> A) (j : nat) : (term120 A i f j) = (term121 A i f j).
Proof. exact (MK_COMB (@lem5419238) (@lem5419257 A i f j)). Qed.
Lemma lem5419277 {A : Type'} (j : nat) (s : A -> Prop) : (term70 A j s) = (term70 A j s).
Proof. exact (eq_refl (term70 A j s)). Qed.
Lemma lem5419278 {A : Type'} (s : A -> Prop) (i : nat) (f : nat -> A) (j : nat) : (term68 A s i f j) = (term122 A s i f j).
Proof. exact (MK_COMB (@lem5419277 A j s) (@lem5419258 A i f j)). Qed.
Lemma lem5419297 {A : Type'} (i : nat) (s : A -> Prop) : (term70 A i s) = (term70 A i s).
Proof. exact (eq_refl (term70 A i s)). Qed.
Lemma lem5419298 {A : Type'} (s : A -> Prop) (i : nat) (f : nat -> A) (j : nat) : (term72 A s i f j) = (term123 A s i f j).
Proof. exact (MK_COMB (@lem5419297 A i s) (@lem5419278 A s i f j)). Qed.
Lemma lem5419299 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5419300 {A : Type'} (s : A -> Prop) (i : nat) (f : nat -> A) (j : nat) : (term76 A s i f j) = (term124 A s i f j).
Proof. exact (MK_COMB (@lem5419299) (@lem5419298 A s i f j)). Qed.
Lemma lem5419301 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) : (term78 A s f i j) = (term125 A s f i j).
Proof. exact (MK_COMB (@lem5419300 A s i f j) (@lem5419237 i j)). Qed.
Lemma lem5419302 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) : (term80 A s f i) = (term126 A s f i).
Proof. exact (fun_ext (fun j : nat => @lem5419301 A s f i j)). Qed.
Lemma lem5419303 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5419304 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) : (term81 A s f i) = (term127 A s f i).
Proof. exact (MK_COMB (@lem5419303) (@lem5419302 A s f i)). Qed.
Lemma lem5419305 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term82 A s f) = (term128 A s f).
Proof. exact (fun_ext (fun i : nat => @lem5419304 A s f i)). Qed.
Lemma lem5419306 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5419307 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term83 A s f) = (term129 A s f).
Proof. exact (MK_COMB (@lem5419306) (@lem5419305 A s f)). Qed.
Lemma lem5419308 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5419309 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term84 A s f) = (term130 A s f).
Proof. exact (MK_COMB (@lem5419308) (@lem5419307 A s f)). Qed.
Lemma lem5419310 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term85 A f s) = (term131 A f s).
Proof. exact (MK_COMB (@lem5419309 A s f) (@lem5419232 A f s)). Qed.
Lemma lem5419311 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5419312 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term106 A f s) = (term132 A f s).
Proof. exact (MK_COMB (@lem5419311) (@lem5419310 A f s)). Qed.
Lemma lem5419313 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term108 A f s) = (term133 A f s).
Proof. exact (MK_COMB (@lem5419312 A f s) (@lem5419213 A s)). Qed.
Lemma lem5419314 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term108 A f s) : term133 A f s.
Proof. exact (EQ_MP (@lem5419313 A f s) (@lem5419128 A f s h1)). Qed.
Lemma lem5419316 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term108 A f s) : term131 A f s.
Proof. exact (proj1 (@lem5419314 A f s h1)). Qed.
Lemma lem5419320 (m : nat) (n : nat) : (term51 m n) = (term51 m n).
Proof. exact (eq_refl (term51 m n)). Qed.
Lemma lem5419321 (m : nat) : (term52 m) = (term52 m).
Proof. exact (fun_ext (fun n : nat => @lem5419320 m n)). Qed.
Lemma lem5419322 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5419323 (m : nat) : (term53 m) = (term53 m).
Proof. exact (MK_COMB (@lem5419322) (@lem5419321 m)). Qed.
Lemma lem5419324 : term54 = term54.
Proof. exact (fun_ext (fun m : nat => @lem5419323 m)). Qed.
Lemma lem5419325 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5419327 : term55 = term55.
Proof. exact (MK_COMB (@lem5419325) (@lem5419324)). Qed.
Lemma lem5419328 (h1 : term55) : term55.
Proof. exact (EQ_MP (@lem5419327) (@lem5419142 h1)). Qed.
Lemma lem5419368 {A : Type'} (f : nat -> A) (s : nat -> Prop) : (term112 A f s) = (term112 A f s).
Proof. exact (eq_refl (term112 A f s)). Qed.
Lemma lem5419369 {A : Type'} (f : nat -> A) : (term114 A f) = (term114 A f).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem5419368 A f s)). Qed.
Lemma lem5419370 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem5419371 {A : Type'} (f : nat -> A) : (term115 A f) = (term115 A f).
Proof. exact (MK_COMB (@lem5419370) (@lem5419369 A f)). Qed.
Lemma lem5419372 {A : Type'} : (term116 A) = (term116 A).
Proof. exact (fun_ext (fun f : nat -> A => @lem5419371 A f)). Qed.
Lemma lem5419373 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem5419375 {A : Type'} : (term117 A) = (term117 A).
Proof. exact (MK_COMB (@lem5419373 A) (@lem5419372 A)). Qed.
Lemma lem5419376 {A : Type'} (h1 : term17 A) : term117 A.
Proof. exact (EQ_MP (@lem5419375 A) (@lem5419208 A h1)). Qed.
Lemma lem5419413 (_69915 : nat) (h1 : term55) : term134 _69915.
Proof. exact (@lem5419328 h1 _69915). Qed.
Lemma lem5419414 (_69915 : nat) : (term134 _69915) = (term53 _69915).
Proof. exact (eq_refl (term134 _69915)). Qed.
Lemma lem5419415 (_69915 : nat) (h1 : term55) : term53 _69915.
Proof. exact (EQ_MP (@lem5419414 _69915) (@lem5419413 _69915 h1)). Qed.
Lemma lem5419416 (_69915 : nat) (_69916 : nat) (h1 : term55) : term135 _69915 _69916.
Proof. exact (@lem5419415 _69915 h1 _69916). Qed.
Lemma lem5419417 (_69915 : nat) (_69916 : nat) : (term135 _69915 _69916) = (term51 _69915 _69916).
Proof. exact (eq_refl (term135 _69915 _69916)). Qed.
Lemma lem5419431 {A : Type'} (_69921 : nat -> A) (h1 : term17 A) : term136 A _69921.
Proof. exact (@lem5419376 A h1 _69921). Qed.
Lemma lem5419432 {A : Type'} (_69921 : nat -> A) : (term136 A _69921) = (term115 A _69921).
Proof. exact (eq_refl (term136 A _69921)). Qed.
Lemma lem5419433 {A : Type'} (_69921 : nat -> A) (h1 : term17 A) : term115 A _69921.
Proof. exact (EQ_MP (@lem5419432 A _69921) (@lem5419431 A _69921 h1)). Qed.
Lemma lem5419434 {A : Type'} (_69921 : nat -> A) (_69922 : nat -> Prop) (h1 : term17 A) : term137 A _69921 _69922.
Proof. exact (@lem5419433 A _69921 h1 _69922). Qed.
Lemma lem5419435 {A : Type'} (_69921 : nat -> A) (_69922 : nat -> Prop) : (term137 A _69921 _69922) = (term112 A _69921 _69922).
Proof. exact (eq_refl (term137 A _69921 _69922)). Qed.
Lemma lem5419462 {A : Type'} (_69921 : nat -> A) (_69922 : nat -> Prop) (h1 : term17 A) : term112 A _69921 _69922.
Proof. exact (EQ_MP (@lem5419435 A _69921 _69922) (@lem5419434 A _69921 _69922 h1)). Qed.
Lemma lem5419464 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term108 A f s) : term88 A s.
Proof. exact (proj2 (@lem5419314 A f s h1)). Qed.
Lemma lem5419516 {A : Type'} : (@FINITE A) = (@FINITE A).
Proof. exact (eq_refl (@FINITE A)). Qed.
Lemma lem5419517 {A : Type'} (_69931 : A -> Prop) (_69932 : A -> Prop) (h1 : _69931 = _69932) : _69931 = _69932.
Proof. exact (h1). Qed.
Lemma lem5419518 {A : Type'} (_69931 : A -> Prop) (_69932 : A -> Prop) (h1 : _69931 = _69932) : (@FINITE A _69931) = (@FINITE A _69932).
Proof. exact (MK_COMB (@lem5419516 A) (@lem5419517 A _69931 _69932 h1)). Qed.
Lemma lem5419520 (b : Prop) (a : Prop) : term138 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem5419521 {A : Type'} (_69932 : A -> Prop) (_69931 : A -> Prop) : term139 A _69932 _69931.
Proof. exact (@lem5419520 (@FINITE A _69932) (@FINITE A _69931)). Qed.
Lemma lem5419522 {A : Type'} (_69931 : A -> Prop) (_69932 : A -> Prop) (h1 : _69931 = _69932) : term140 A _69932 _69931.
Proof. exact (@lem5419521 A _69932 _69931 (@lem5419518 A _69931 _69932 h1)). Qed.
Lemma lem5419523 {A : Type'} (_69932 : A -> Prop) (_69931 : A -> Prop) : term141 A _69932 _69931.
Proof. exact (fun h0 : _69931 = _69932 => @lem5419522 A _69931 _69932 h0). Qed.
Lemma lem5419525 (a : Prop) (b : Prop) : (a -> b) = (term142 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5419526 {A : Type'} (_69932 : A -> Prop) (_69931 : A -> Prop) : (term141 A _69932 _69931) = (term143 A _69932 _69931).
Proof. exact (@lem5419525 (_69931 = _69932) (term140 A _69932 _69931)). Qed.
Lemma lem5419527 {A : Type'} (_69932 : A -> Prop) (_69931 : A -> Prop) : term143 A _69932 _69931.
Proof. exact (EQ_MP (@lem5419526 A _69932 _69931) (@lem5419523 A _69932 _69931)). Qed.
Lemma lem5419644 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) : term144 A x y z.
Proof. exact (@lem21385 (A -> Prop) x y z). Qed.
Lemma lem5419656 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term108 A f s) : s = (term56 A f s).
Proof. exact (proj2 (@lem5419316 A f s h1)). Qed.
Lemma lem5419657 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term108 A f s) : term145 A f s.
Proof. exact (fun h0 : term146 A f s => @lem5419656 A f s h1). Qed.
Lemma lem5419659 (p : Prop) : (term147 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5419660 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term145 A f s) = (s = (term56 A f s)).
Proof. exact (@lem5419659 (s = (term56 A f s))). Qed.
Lemma lem5419661 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term108 A f s) : s = (term56 A f s).
Proof. exact (EQ_MP (@lem5419660 A f s) (@lem5419657 A f s h1)). Qed.
Lemma lem5419663 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem21386 (A -> Prop) x). Qed.
Lemma lem5419664 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem5419663 A x). Qed.
Lemma lem5419665 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (@lem5419664 A s). Qed.
Lemma lem5419666 {A : Type'} (s : A -> Prop) : term148 A s.
Proof. exact (fun h0 : term149 A s => @lem5419665 A s). Qed.
Lemma lem5419668 (p : Prop) : (term147 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5419669 {A : Type'} (s : A -> Prop) : (term148 A s) = (s = s).
Proof. exact (@lem5419668 (s = s)). Qed.
Lemma lem5419670 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (EQ_MP (@lem5419669 A s) (@lem5419666 A s)). Qed.
Lemma lem5419688 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5419689 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term150 A x y z) = (term151 A y x z).
Proof. exact (@lem5419688 (y = z) (term152 A x z)). Qed.
Lemma lem5419699 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term153 A x y) = (term153 A x y).
Proof. exact (eq_refl (term153 A x y)). Qed.
Lemma lem5419700 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term144 A x y z) = (term154 A y x z).
Proof. exact (MK_COMB (@lem5419699 A x y) (@lem5419689 A y x z)). Qed.
Lemma lem5419704 (q : Prop) (p : Prop) (r : Prop) : (term155 p q r) = (term155 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5419705 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term154 A y x z) = (term156 A y x z).
Proof. exact (@lem5419704 (y = z) (term152 A x y) (term152 A x z)). Qed.
Lemma lem5419727 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term144 A x y z) = (term156 A y x z).
Proof. exact (TRANS (@lem5419700 A y x z) (@lem5419705 A y x z)). Qed.
Lemma lem5419728 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5419729 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term157 A x y z) = (term158 A y x z).
Proof. exact (MK_COMB (@lem5419728) (@lem5419727 A y x z)). Qed.
Lemma lem5419751 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term156 A y x z) = (term156 A y x z).
Proof. exact (eq_refl (term156 A y x z)). Qed.
Lemma lem5419752 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : ((term144 A x y z) = (term156 A y x z)) = ((term156 A y x z) = (term156 A y x z)).
Proof. exact (MK_COMB (@lem5419729 A y x z) (@lem5419751 A y x z)). Qed.
Lemma lem5419754 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5419755 (x : Prop) : (x = x) = True.
Proof. exact (@lem5419754 Prop x). Qed.
Lemma lem5419756 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : ((term156 A y x z) = (term156 A y x z)) = True.
Proof. exact (@lem5419755 (term156 A y x z)). Qed.
Lemma lem5419757 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : ((term144 A x y z) = (term156 A y x z)) = True.
Proof. exact (TRANS (@lem5419752 A y x z) (@lem5419756 A y x z)). Qed.
Lemma lem5419758 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : True = ((term144 A x y z) = (term156 A y x z)).
Proof. exact (SYM (@lem5419757 A y x z)). Qed.
Lemma lem5419759 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term144 A x y z) = (term156 A y x z).
Proof. exact (EQ_MP (@lem5419758 A y x z) (@lem0)). Qed.
Lemma lem5419760 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : term156 A y x z.
Proof. exact (EQ_MP (@lem5419759 A y x z) (@lem5419644 A x y z)). Qed.
Lemma lem5419762 (b : Prop) (a : Prop) : (a \/ b) = (term159 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5419763 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term156 A y x z) = (term160 A x y z).
Proof. exact (@lem5419762 (term161 A y x z) (y = z)). Qed.
Lemma lem5419765 (a : Prop) (b : Prop) : (term162 a b) = (term163 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5419766 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term164 A y x z) = (term165 A y x z).
Proof. exact (@lem5419765 (term152 A x y) (term152 A x z)). Qed.
Lemma lem5419768 (a : Prop) : (term166 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5419769 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term167 A x y) = (x = y).
Proof. exact (@lem5419768 (x = y)). Qed.
Lemma lem5419770 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5419771 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term168 A x y) = (term169 A x y).
Proof. exact (MK_COMB (@lem5419770) (@lem5419769 A x y)). Qed.
Lemma lem5419773 (a : Prop) : (term166 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5419774 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term167 A x z) = (x = z).
Proof. exact (@lem5419773 (x = z)). Qed.
Lemma lem5419775 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term165 A y x z) = (term170 A y x z).
Proof. exact (MK_COMB (@lem5419771 A x y) (@lem5419774 A x z)). Qed.
Lemma lem5419776 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term164 A y x z) = (term170 A y x z).
Proof. exact (TRANS (@lem5419766 A y x z) (@lem5419775 A y x z)). Qed.
Lemma lem5419777 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5419778 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term171 A y x z) = (term172 A y x z).
Proof. exact (MK_COMB (@lem5419777) (@lem5419776 A y x z)). Qed.
Lemma lem5419779 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem5419780 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term160 A x y z) = (term173 A x y z).
Proof. exact (MK_COMB (@lem5419778 A y x z) (@lem5419779 A y z)). Qed.
Lemma lem5419781 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term156 A y x z) = (term173 A x y z).
Proof. exact (TRANS (@lem5419763 A x y z) (@lem5419780 A x y z)). Qed.
Lemma lem5419783 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term108 A f s) : term174 A f s.
Proof. exact (conj (@lem5419661 A f s h1) (@lem5419670 A s)). Qed.
Lemma lem5419785 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) : term173 A x y z.
Proof. exact (EQ_MP (@lem5419781 A x y z) (@lem5419760 A y x z)). Qed.
Lemma lem5419786 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) : term173 A x y z.
Proof. exact (@lem5419785 A x y z). Qed.
Lemma lem5419787 {A : Type'} (f : nat -> A) (s : A -> Prop) : term175 A f s.
Proof. exact (@lem5419786 A s (term56 A f s) s). Qed.
Lemma lem5419790 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term108 A f s) : (term56 A f s) = s.
Proof. exact (@lem5419787 A f s (@lem5419783 A f s h1)). Qed.
Lemma lem5419791 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term108 A f s) : term176 A f s.
Proof. exact (fun h0 : term177 A f s => @lem5419790 A f s h1). Qed.
Lemma lem5419793 (p : Prop) : (term147 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5419794 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term176 A f s) = ((term56 A f s) = s).
Proof. exact (@lem5419793 ((term56 A f s) = s)). Qed.
Lemma lem5419795 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term108 A f s) : (term56 A f s) = s.
Proof. exact (EQ_MP (@lem5419794 A f s) (@lem5419791 A f s h1)). Qed.
Lemma lem5419797 (_69915 : nat) (_69916 : nat) (h1 : term55) : term51 _69915 _69916.
Proof. exact (EQ_MP (@lem5419417 _69915 _69916) (@lem5419416 _69915 _69916 h1)). Qed.
Lemma lem5419798 {A : Type'} (s : A -> Prop) (h1 : term55) : term178 A s.
Proof. exact (@lem5419797 term179 (@CARD A s) h1). Qed.
Lemma lem5419799 {A : Type'} (s : A -> Prop) (h1 : term55) : term180 A s.
Proof. exact (fun h0 : term181 A s => @lem5419798 A s h1). Qed.
Lemma lem5419801 (p : Prop) : (term147 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5419802 {A : Type'} (s : A -> Prop) : (term180 A s) = (term178 A s).
Proof. exact (@lem5419801 (term178 A s)). Qed.
Lemma lem5419803 {A : Type'} (s : A -> Prop) (h1 : term55) : term178 A s.
Proof. exact (EQ_MP (@lem5419802 A s) (@lem5419799 A s h1)). Qed.
Lemma lem5419809 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5419810 {A : Type'} (_69921 : nat -> A) (_69922 : nat -> Prop) : (term112 A _69921 _69922) = (term182 A _69921 _69922).
Proof. exact (@lem5419809 (term113 A _69921 _69922) (term183 _69922)). Qed.
Lemma lem5419816 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5419817 {A : Type'} (_69921 : nat -> A) (_69922 : nat -> Prop) : (term184 A _69921 _69922) = (term185 A _69921 _69922).
Proof. exact (MK_COMB (@lem5419816) (@lem5419810 A _69921 _69922)). Qed.
Lemma lem5419823 {A : Type'} (_69921 : nat -> A) (_69922 : nat -> Prop) : (term182 A _69921 _69922) = (term182 A _69921 _69922).
Proof. exact (eq_refl (term182 A _69921 _69922)). Qed.
Lemma lem5419824 {A : Type'} (_69921 : nat -> A) (_69922 : nat -> Prop) : ((term112 A _69921 _69922) = (term182 A _69921 _69922)) = ((term182 A _69921 _69922) = (term182 A _69921 _69922)).
Proof. exact (MK_COMB (@lem5419817 A _69921 _69922) (@lem5419823 A _69921 _69922)). Qed.
Lemma lem5419826 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5419827 (x : Prop) : (x = x) = True.
Proof. exact (@lem5419826 Prop x). Qed.
Lemma lem5419828 {A : Type'} (_69921 : nat -> A) (_69922 : nat -> Prop) : ((term182 A _69921 _69922) = (term182 A _69921 _69922)) = True.
Proof. exact (@lem5419827 (term182 A _69921 _69922)). Qed.
Lemma lem5419829 {A : Type'} (_69921 : nat -> A) (_69922 : nat -> Prop) : ((term112 A _69921 _69922) = (term182 A _69921 _69922)) = True.
Proof. exact (TRANS (@lem5419824 A _69921 _69922) (@lem5419828 A _69921 _69922)). Qed.
Lemma lem5419830 {A : Type'} (_69921 : nat -> A) (_69922 : nat -> Prop) : True = ((term112 A _69921 _69922) = (term182 A _69921 _69922)).
Proof. exact (SYM (@lem5419829 A _69921 _69922)). Qed.
Lemma lem5419831 {A : Type'} (_69921 : nat -> A) (_69922 : nat -> Prop) : (term112 A _69921 _69922) = (term182 A _69921 _69922).
Proof. exact (EQ_MP (@lem5419830 A _69921 _69922) (@lem0)). Qed.
Lemma lem5419832 {A : Type'} (_69921 : nat -> A) (_69922 : nat -> Prop) (h1 : term17 A) : term182 A _69921 _69922.
Proof. exact (EQ_MP (@lem5419831 A _69921 _69922) (@lem5419462 A _69921 _69922 h1)). Qed.
Lemma lem5419834 (b : Prop) (a : Prop) : (a \/ b) = (term159 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5419835 {A : Type'} (_69921 : nat -> A) (_69922 : nat -> Prop) : (term182 A _69921 _69922) = (term186 A _69921 _69922).
Proof. exact (@lem5419834 (term183 _69922) (term113 A _69921 _69922)). Qed.
Lemma lem5419837 (a : Prop) : (term166 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5419838 (_69922 : nat -> Prop) : (term187 _69922) = (@FINITE nat _69922).
Proof. exact (@lem5419837 (@FINITE nat _69922)). Qed.
Lemma lem5419839 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5419840 (_69922 : nat -> Prop) : (term188 _69922) = (term189 _69922).
Proof. exact (MK_COMB (@lem5419839) (@lem5419838 _69922)). Qed.
Lemma lem5419841 {A : Type'} (_69921 : nat -> A) (_69922 : nat -> Prop) : (term113 A _69921 _69922) = (term113 A _69921 _69922).
Proof. exact (eq_refl (term113 A _69921 _69922)). Qed.
Lemma lem5419842 {A : Type'} (_69921 : nat -> A) (_69922 : nat -> Prop) : (term186 A _69921 _69922) = (term39 A _69921 _69922).
Proof. exact (MK_COMB (@lem5419840 _69922) (@lem5419841 A _69921 _69922)). Qed.
Lemma lem5419843 {A : Type'} (_69921 : nat -> A) (_69922 : nat -> Prop) : (term182 A _69921 _69922) = (term39 A _69921 _69922).
Proof. exact (TRANS (@lem5419835 A _69921 _69922) (@lem5419842 A _69921 _69922)). Qed.
Lemma lem5419846 {A : Type'} (_69921 : nat -> A) (_69922 : nat -> Prop) (h1 : term17 A) : term39 A _69921 _69922.
Proof. exact (EQ_MP (@lem5419843 A _69921 _69922) (@lem5419832 A _69921 _69922 h1)). Qed.
Lemma lem5419847 {A : Type'} (_69921 : nat -> A) (s : A -> Prop) (h1 : term17 A) : term190 A _69921 s.
Proof. exact (@lem5419846 A _69921 (term7 A s) h1). Qed.
Lemma lem5419850 {A : Type'} (_69921 : nat -> A) (s : A -> Prop) (h1 : term17 A) (h2 : term55) : term191 A _69921 s.
Proof. exact (@lem5419847 A _69921 s h1 (@lem5419803 A s h2)). Qed.
Lemma lem5419851 {A : Type'} (_69921 : nat -> A) (s : A -> Prop) (h1 : term17 A) (h2 : term55) : term191 A _69921 s.
Proof. exact (@lem5419850 A _69921 s h1 h2). Qed.
Lemma lem5419852 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term17 A) (h2 : term55) : term191 A f s.
Proof. exact (@lem5419851 A f s h1 h2). Qed.
Lemma lem5419853 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term17 A) (h2 : term55) : term192 A f s.
Proof. exact (fun h0 : term193 A f s => @lem5419852 A f s h1 h2). Qed.
Lemma lem5419855 (p : Prop) : (term147 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5419856 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term192 A f s) = (term191 A f s).
Proof. exact (@lem5419855 (term191 A f s)). Qed.
Lemma lem5419857 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term17 A) (h2 : term55) : term191 A f s.
Proof. exact (EQ_MP (@lem5419856 A f s) (@lem5419853 A f s h1 h2)). Qed.
Lemma lem5419863 (q : Prop) (p : Prop) (r : Prop) : (term155 p q r) = (term155 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5419864 {A : Type'} (_69932 : A -> Prop) (_69931 : A -> Prop) : (term143 A _69932 _69931) = (term194 A _69932 _69931).
Proof. exact (@lem5419863 (@FINITE A _69932) (term152 A _69931 _69932) (term88 A _69931)). Qed.
Lemma lem5419882 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5419883 {A : Type'} (_69932 : A -> Prop) (_69931 : A -> Prop) : (term195 A _69932 _69931) = (term196 A _69932 _69931).
Proof. exact (MK_COMB (@lem5419882) (@lem5419864 A _69932 _69931)). Qed.
Lemma lem5419901 {A : Type'} (_69932 : A -> Prop) (_69931 : A -> Prop) : (term194 A _69932 _69931) = (term194 A _69932 _69931).
Proof. exact (eq_refl (term194 A _69932 _69931)). Qed.
Lemma lem5419902 {A : Type'} (_69932 : A -> Prop) (_69931 : A -> Prop) : ((term143 A _69932 _69931) = (term194 A _69932 _69931)) = ((term194 A _69932 _69931) = (term194 A _69932 _69931)).
Proof. exact (MK_COMB (@lem5419883 A _69932 _69931) (@lem5419901 A _69932 _69931)). Qed.
Lemma lem5419904 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5419905 (x : Prop) : (x = x) = True.
Proof. exact (@lem5419904 Prop x). Qed.
Lemma lem5419906 {A : Type'} (_69932 : A -> Prop) (_69931 : A -> Prop) : ((term194 A _69932 _69931) = (term194 A _69932 _69931)) = True.
Proof. exact (@lem5419905 (term194 A _69932 _69931)). Qed.
Lemma lem5419907 {A : Type'} (_69932 : A -> Prop) (_69931 : A -> Prop) : ((term143 A _69932 _69931) = (term194 A _69932 _69931)) = True.
Proof. exact (TRANS (@lem5419902 A _69932 _69931) (@lem5419906 A _69932 _69931)). Qed.
Lemma lem5419908 {A : Type'} (_69932 : A -> Prop) (_69931 : A -> Prop) : True = ((term143 A _69932 _69931) = (term194 A _69932 _69931)).
Proof. exact (SYM (@lem5419907 A _69932 _69931)). Qed.
Lemma lem5419909 {A : Type'} (_69932 : A -> Prop) (_69931 : A -> Prop) : (term143 A _69932 _69931) = (term194 A _69932 _69931).
Proof. exact (EQ_MP (@lem5419908 A _69932 _69931) (@lem0)). Qed.
Lemma lem5419910 {A : Type'} (_69932 : A -> Prop) (_69931 : A -> Prop) : term194 A _69932 _69931.
Proof. exact (EQ_MP (@lem5419909 A _69932 _69931) (@lem5419527 A _69932 _69931)). Qed.
Lemma lem5419912 (b : Prop) (a : Prop) : (a \/ b) = (term159 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5419913 {A : Type'} (_69931 : A -> Prop) (_69932 : A -> Prop) : (term194 A _69932 _69931) = (term197 A _69931 _69932).
Proof. exact (@lem5419912 (term198 A _69932 _69931) (@FINITE A _69932)). Qed.
Lemma lem5419915 (a : Prop) (b : Prop) : (term162 a b) = (term163 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5419916 {A : Type'} (_69932 : A -> Prop) (_69931 : A -> Prop) : (term199 A _69932 _69931) = (term200 A _69932 _69931).
Proof. exact (@lem5419915 (term152 A _69931 _69932) (term88 A _69931)). Qed.
Lemma lem5419918 (a : Prop) : (term166 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5419919 {A : Type'} (_69931 : A -> Prop) (_69932 : A -> Prop) : (term167 A _69931 _69932) = (_69931 = _69932).
Proof. exact (@lem5419918 (_69931 = _69932)). Qed.
Lemma lem5419920 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5419921 {A : Type'} (_69931 : A -> Prop) (_69932 : A -> Prop) : (term168 A _69931 _69932) = (term169 A _69931 _69932).
Proof. exact (MK_COMB (@lem5419920) (@lem5419919 A _69931 _69932)). Qed.
Lemma lem5419923 (a : Prop) : (term166 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5419924 {A : Type'} (_69931 : A -> Prop) : (term201 A _69931) = (@FINITE A _69931).
Proof. exact (@lem5419923 (@FINITE A _69931)). Qed.
Lemma lem5419925 {A : Type'} (_69932 : A -> Prop) (_69931 : A -> Prop) : (term200 A _69932 _69931) = (term202 A _69932 _69931).
Proof. exact (MK_COMB (@lem5419921 A _69931 _69932) (@lem5419924 A _69931)). Qed.
Lemma lem5419926 {A : Type'} (_69932 : A -> Prop) (_69931 : A -> Prop) : (term199 A _69932 _69931) = (term202 A _69932 _69931).
Proof. exact (TRANS (@lem5419916 A _69932 _69931) (@lem5419925 A _69932 _69931)). Qed.
Lemma lem5419927 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5419928 {A : Type'} (_69932 : A -> Prop) (_69931 : A -> Prop) : (term203 A _69932 _69931) = (term204 A _69932 _69931).
Proof. exact (MK_COMB (@lem5419927) (@lem5419926 A _69932 _69931)). Qed.
Lemma lem5419929 {A : Type'} (_69932 : A -> Prop) : (@FINITE A _69932) = (@FINITE A _69932).
Proof. exact (eq_refl (@FINITE A _69932)). Qed.
Lemma lem5419930 {A : Type'} (_69931 : A -> Prop) (_69932 : A -> Prop) : (term197 A _69931 _69932) = (term205 A _69931 _69932).
Proof. exact (MK_COMB (@lem5419928 A _69932 _69931) (@lem5419929 A _69932)). Qed.
Lemma lem5419931 {A : Type'} (_69931 : A -> Prop) (_69932 : A -> Prop) : (term194 A _69932 _69931) = (term205 A _69931 _69932).
Proof. exact (TRANS (@lem5419913 A _69931 _69932) (@lem5419930 A _69931 _69932)). Qed.
Lemma lem5419933 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term17 A) (h2 : term55) (h3 : term108 A f s) : term206 A f s.
Proof. exact (conj (@lem5419795 A f s h3) (@lem5419857 A f s h1 h2)). Qed.
Lemma lem5419935 {A : Type'} (_69931 : A -> Prop) (_69932 : A -> Prop) : term205 A _69931 _69932.
Proof. exact (EQ_MP (@lem5419931 A _69931 _69932) (@lem5419910 A _69932 _69931)). Qed.
Lemma lem5419936 {A : Type'} (_69931 : A -> Prop) (_69932 : A -> Prop) : term205 A _69931 _69932.
Proof. exact (@lem5419935 A _69931 _69932). Qed.
Lemma lem5419937 {A : Type'} (f : nat -> A) (s : A -> Prop) : term207 A f s.
Proof. exact (@lem5419936 A (term56 A f s) s). Qed.
Lemma lem5419940 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term17 A) (h2 : term55) (h3 : term108 A f s) : @FINITE A s.
Proof. exact (@lem5419937 A f s (@lem5419933 A f s h1 h2 h3)). Qed.
Lemma lem5419941 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term17 A) (h2 : term55) (h3 : term108 A f s) : term208 A s.
Proof. exact (fun h0 : term88 A s => @lem5419940 A f s h1 h2 h3). Qed.
Lemma lem5419943 (p : Prop) : (term147 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5419944 {A : Type'} (s : A -> Prop) : (term208 A s) = (@FINITE A s).
Proof. exact (@lem5419943 (@FINITE A s)). Qed.
Lemma lem5419945 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term17 A) (h2 : term55) (h3 : term108 A f s) : @FINITE A s.
Proof. exact (EQ_MP (@lem5419944 A s) (@lem5419941 A f s h1 h2 h3)). Qed.
Lemma lem5419948 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5419950 {A : Type'} (s : A -> Prop) : (term88 A s) = (term209 A s).
Proof. exact (@lem5419948 (@FINITE A s)). Qed.
Lemma lem5419953 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term108 A f s) : term209 A s.
Proof. exact (EQ_MP (@lem5419950 A s) (@lem5419464 A f s h1)). Qed.
Lemma lem5419956 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term17 A) (h2 : term55) (h3 : term108 A f s) : False.
Proof. exact (@lem5419953 A f s h3 (@lem5419945 A f s h1 h2 h3)). Qed.
Lemma lem5419957 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term17 A) (h2 : term55) (h3 : term108 A f s) : term210.
Proof. exact (fun h0 : ~ False => @lem5419956 A f s h1 h2 h3). Qed.
Lemma lem5419959 (p : Prop) : (term147 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5419960 : term210 = False.
Proof. exact (@lem5419959 False). Qed.
Lemma lem5419961 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term17 A) (h2 : term55) (h3 : term108 A f s) : False.
Proof. exact (EQ_MP (@lem5419960) (@lem5419957 A f s h1 h2 h3)). Qed.
Lemma lem5419962 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term17 A) (h2 : term55) (h3 : term108 A f s) : term55 = False.
Proof. exact (prop_ext (fun h4 : term55 => @lem5419961 A f s h1 h2 h3) (fun h4 : False => @lem5419328 h2)). Qed.
Lemma lem5419963 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term17 A) (h2 : term55) (h3 : term108 A f s) : False.
Proof. exact (EQ_MP (@lem5419962 A f s h1 h2 h3) (@lem5419328 h2)). Qed.
Lemma lem5419964 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term17 A) (h2 : term55) (h3 : term108 A f s) : term55 = False.
Proof. exact (prop_ext (fun h4 : term55 => @lem5419963 A f s h1 h2 h3) (fun h4 : False => @lem5419142 h2)). Qed.
Lemma lem5419965 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term17 A) (h2 : term55) (h3 : term108 A f s) : False.
Proof. exact (EQ_MP (@lem5419964 A f s h1 h2 h3) (@lem5419142 h2)). Qed.
Lemma lem5419966 {A : Type'} (s : A -> Prop) (h1 : term17 A) (h2 : term55) (h3 : term14 A s) : False.
Proof. exact (ex_elim (@lem5418897 A s h3) (fun f : nat -> A => fun h0 : term110 A s f => @lem5419965 A f s h1 h2 h0)). Qed.
Lemma lem5419967 {A : Type'} (s : A -> Prop) (h1 : term17 A) (h2 : term55) (h3 : term14 A s) : term55 = False.
Proof. exact (prop_ext (fun h4 : term55 => @lem5419966 A s h1 h2 h3) (fun h4 : False => @lem5418917 h2)). Qed.
Lemma lem5419968 {A : Type'} (s : A -> Prop) (h1 : term17 A) (h2 : term55) (h3 : term14 A s) : False.
Proof. exact (EQ_MP (@lem5419967 A s h1 h2 h3) (@lem5418917 h2)). Qed.
Lemma lem5419969 {A : Type'} (s : A -> Prop) (h1 : term55) (h2 : term14 A s) : term22 A.
Proof. exact (fun h0 : term17 A => @lem5419968 A s h0 h1 h2). Qed.
Lemma lem5419970 {A : Type'} : (term22 A) = (term23 A).
Proof. exact (@lem69 (term17 A)). Qed.
Lemma lem5419971 {A : Type'} (s : A -> Prop) (h1 : term55) (h2 : term14 A s) : term23 A.
Proof. exact (EQ_MP (@lem5419970 A) (@lem5419969 A s h1 h2)). Qed.
Lemma lem5419972 {A B : Type'} (s : A -> Prop) (h1 : term55) (h2 : term14 A s) : term26 A B.
Proof. exact (fun h0 : term15 A B => @lem5419971 A s h1 h2). Qed.
Lemma lem5419973 {A B : Type'} (s : A -> Prop) (h1 : term55) (h2 : term14 A s) : term29 A B.
Proof. exact (fun h0 : term16 A => @lem5419972 A B s h1 h2). Qed.
Lemma lem5419974 {A B : Type'} (s : A -> Prop) (h1 : term14 A s) : term32 A B.
Proof. exact (fun h0 : term55 => @lem5419973 A B s h0 h1). Qed.
Lemma lem5419975 {A B : Type'} (s : A -> Prop) : term34 A B s.
Proof. exact (fun h0 : term14 A s => @lem5419974 A B s h0). Qed.
Lemma lem5419980 {A B : Type'} : term38 A B.
Proof. exact (fun s : A -> Prop => @lem5419975 A B s). Qed.
Lemma lem5419981 {A B : Type'} : term37 A B.
Proof. exact (EQ_MP (@lem5418726 A B) (@lem5419980 A B)). Qed.
Lemma lem5419982 {A B : Type'} (s : A -> Prop) : term211 A B s.
Proof. exact (@lem5419981 A B s). Qed.
Lemma lem5419983 {A B : Type'} (s : A -> Prop) : (term211 A B s) = (term18 A B s).
Proof. exact (eq_refl (term211 A B s)). Qed.
Lemma lem5419984 {A B : Type'} (s : A -> Prop) : term18 A B s.
Proof. exact (EQ_MP (@lem5419983 A B s) (@lem5419982 A B s)). Qed.
Lemma lem5419986 {A B : Type'} (s : A -> Prop) : term18 A B s.
Proof. exact (@lem5418391 A B s (@lem5419984 A B s)). Qed.
Lemma lem5419987 {A B : Type'} (s : A -> Prop) (h1 : term14 A s) : term31 A B.
Proof. exact (@lem5419986 A B s (@lem5418372 A s h1)). Qed.
Lemma lem5419988 {A B : Type'} (s : A -> Prop) (h1 : term14 A s) : term28 A B.
Proof. exact (@lem5419987 A B s h1 (@lem5329299)). Qed.
Lemma lem5419989 {A B : Type'} (s : A -> Prop) (h1 : term14 A s) : term25 A B.
Proof. exact (@lem5419988 A B s h1 (@lem5418374 A)). Qed.
Lemma lem5419990 {A : Type'} (s : A -> Prop) (h1 : term14 A s) : term22 A.
Proof. exact (@lem5419989 A Prop s h1 (@lem5418373 A Prop)). Qed.
Lemma lem5419991 {A : Type'} (s : A -> Prop) (h1 : term14 A s) : False.
Proof. exact (@lem5419990 A s h1 (@lem5418375 A)). Qed.
Lemma lem5419992 {A : Type'} (s : A -> Prop) (h1 : term14 A s) : (term14 A s) = False.
Proof. exact (prop_ext (fun h2 : term14 A s => @lem5419991 A s h1) (fun h2 : False => @lem5418372 A s h1)). Qed.
Lemma lem5419993 {A : Type'} (s : A -> Prop) (h1 : term14 A s) : False.
Proof. exact (EQ_MP (@lem5419992 A s h1) (@lem5418372 A s h1)). Qed.
Lemma lem5419994 {A : Type'} (s : A -> Prop) : term13 A s.
Proof. exact (fun h0 : term14 A s => @lem5419993 A s h0). Qed.
Lemma lem5419995 {A : Type'} (s : A -> Prop) : term12 A s.
Proof. exact (EQ_MP (@lem5418371 A s) (@lem5419994 A s)). Qed.
Lemma lem5419996 (n : nat) : term212 n.
Proof. exact (@lem5397152 n). Qed.
Lemma lem5419997 (n : nat) : (term212 n) = ((term213 n) = n).
Proof. exact (eq_refl (term212 n)). Qed.
Lemma lem5419999 (m : nat) : term134 m.
Proof. exact (@lem5329299 m). Qed.
Lemma lem5420000 (m : nat) : (term134 m) = (term53 m).
Proof. exact (eq_refl (term134 m)). Qed.
Lemma lem5420001 (m : nat) : term53 m.
Proof. exact (EQ_MP (@lem5420000 m) (@lem5419999 m)). Qed.
Lemma lem5420002 (m : nat) (n : nat) : term135 m n.
Proof. exact (@lem5420001 m n). Qed.
Lemma lem5420003 (m : nat) (n : nat) : (term135 m n) = (term51 m n).
Proof. exact (eq_refl (term135 m n)). Qed.
Lemma lem5420004 (m : nat) (n : nat) : term51 m n.
Proof. exact (EQ_MP (@lem5420003 m n) (@lem5420002 m n)). Qed.
Lemma lem5420005 (m : nat) (n : nat) : (term51 m n) = ((term51 m n) = True).
Proof. exact (@lem7 (term51 m n)). Qed.
Lemma lem5420007 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem5420016 (m : nat) (n : nat) : (term51 m n) = True.
Proof. exact (EQ_MP (@lem5420005 m n) (@lem5420004 m n)). Qed.
Lemma lem5420017 {A : Type'} (s : A -> Prop) : (term178 A s) = True.
Proof. exact (@lem5420016 term179 (@CARD A s)). Qed.
Lemma lem5420018 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5420019 {A : Type'} (s : A -> Prop) : (term214 A s) = (and True).
Proof. exact (MK_COMB (@lem5420018) (@lem5420017 A s)). Qed.
Lemma lem5420023 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem5420007 A s) (@lem5418367 A s h1)). Qed.
Lemma lem5420024 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5420025 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term215 A s) = (and True).
Proof. exact (MK_COMB (@lem5420024) (@lem5420023 A s h1)). Qed.
Lemma lem5420029 (n : nat) : (term213 n) = n.
Proof. exact (EQ_MP (@lem5419997 n) (@lem5419996 n)). Qed.
Lemma lem5420030 {A : Type'} (s : A -> Prop) : (term216 A s) = (@CARD A s).
Proof. exact (@lem5420029 (@CARD A s)). Qed.
Lemma lem5420031 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem5420032 {A : Type'} (s : A -> Prop) : (term217 A s) = (term218 A s).
Proof. exact (MK_COMB (@lem5420031) (@lem5420030 A s)). Qed.
Lemma lem5420033 {A : Type'} (s : A -> Prop) : (@CARD A s) = (@CARD A s).
Proof. exact (eq_refl (@CARD A s)). Qed.
Lemma lem5420034 {A : Type'} (s : A -> Prop) : ((term216 A s) = (@CARD A s)) = ((@CARD A s) = (@CARD A s)).
Proof. exact (MK_COMB (@lem5420032 A s) (@lem5420033 A s)). Qed.
Lemma lem5420036 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5420037 (x : nat) : (x = x) = True.
Proof. exact (@lem5420036 nat x). Qed.
Lemma lem5420038 {A : Type'} (s : A -> Prop) : ((@CARD A s) = (@CARD A s)) = True.
Proof. exact (@lem5420037 (@CARD A s)). Qed.
Lemma lem5420039 {A : Type'} (s : A -> Prop) : ((term216 A s) = (@CARD A s)) = True.
Proof. exact (TRANS (@lem5420034 A s) (@lem5420038 A s)). Qed.
Lemma lem5420040 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term219 A s) = (True /\ True).
Proof. exact (MK_COMB (@lem5420025 A s h1) (@lem5420039 A s)). Qed.
Lemma lem5420042 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5420043 : (True /\ True) = True.
Proof. exact (@lem5420042 True). Qed.
Lemma lem5420044 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term219 A s) = True.
Proof. exact (TRANS (@lem5420040 A s h1) (@lem5420043)). Qed.
Lemma lem5420045 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term220 A s) = (True /\ True).
Proof. exact (MK_COMB (@lem5420019 A s) (@lem5420044 A s h1)). Qed.
Lemma lem5420047 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5420048 : (True /\ True) = True.
Proof. exact (@lem5420047 True). Qed.
Lemma lem5420049 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term220 A s) = True.
Proof. exact (TRANS (@lem5420045 A s h1) (@lem5420048)). Qed.
Lemma lem5420050 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5420051 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term221 A s) = (imp True).
Proof. exact (MK_COMB (@lem5420050) (@lem5420049 A s h1)). Qed.
Lemma lem5420082 {A : Type'} (s : A -> Prop) : (term222 A s) = (term222 A s).
Proof. exact (eq_refl (term222 A s)). Qed.
Lemma lem5420083 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term10 A s) = (term223 A s).
Proof. exact (MK_COMB (@lem5420051 A s h1) (@lem5420082 A s)). Qed.
Lemma lem5420085 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem5420086 {A : Type'} (s : A -> Prop) : (term223 A s) = (term222 A s).
Proof. exact (@lem5420085 (term222 A s)). Qed.
Lemma lem5420117 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term10 A s) = (term222 A s).
Proof. exact (TRANS (@lem5420083 A s h1) (@lem5420086 A s)). Qed.
Lemma lem5420118 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5420119 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term224 A s) = (term225 A s).
Proof. exact (MK_COMB (@lem5420118) (@lem5420117 A s h1)). Qed.
Lemma lem5420146 {A : Type'} (s : A -> Prop) : (term65 A s) = (term65 A s).
Proof. exact (eq_refl (term65 A s)). Qed.
Lemma lem5420147 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term226 A s) = (term227 A s).
Proof. exact (MK_COMB (@lem5420119 A s h1) (@lem5420146 A s)). Qed.
Lemma lem5420150 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term227 A s) = (term226 A s).
Proof. exact (SYM (@lem5420147 A s h1)). Qed.
Lemma lem5420152 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term0 A P Q.
Proof. exact (@lem5418348 A P Q (@lem7401 A P Q)). Qed.
Lemma lem5420153 {A : Type'} (P : type976 A) (Q : type976 A) : term228 A P Q.
Proof. exact (@lem5420152 (nat -> A) P Q). Qed.
Lemma lem5420154 {A : Type'} (s : A -> Prop) : term229 A s.
Proof. exact (@lem5420153 A (term230 A s) (term64 A s)). Qed.
Lemma lem5420155 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term231 A s f) = (term232 A s f).
Proof. exact (eq_refl (term231 A s f)). Qed.
Lemma lem5420156 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5420157 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term233 A s f) = (term234 A s f).
Proof. exact (MK_COMB (@lem5420156) (@lem5420155 A s f)). Qed.
Lemma lem5420158 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term235 A s f) = (term63 A f s).
Proof. exact (eq_refl (term235 A s f)). Qed.
Lemma lem5420159 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term236 A s f) = (term237 A f s).
Proof. exact (MK_COMB (@lem5420157 A s f) (@lem5420158 A f s)). Qed.
Lemma lem5420160 {A : Type'} (s : A -> Prop) : (term238 A s) = (term239 A s).
Proof. exact (fun_ext (fun f : nat -> A => @lem5420159 A f s)). Qed.
Lemma lem5420161 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem5420162 {A : Type'} (s : A -> Prop) : (term240 A s) = (term241 A s).
Proof. exact (MK_COMB (@lem5420161 A) (@lem5420160 A s)). Qed.
Lemma lem5420163 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5420164 {A : Type'} (s : A -> Prop) : (term242 A s) = (term243 A s).
Proof. exact (MK_COMB (@lem5420163) (@lem5420162 A s)). Qed.
Lemma lem5420165 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term231 A s f) = (term232 A s f).
Proof. exact (eq_refl (term231 A s f)). Qed.
Lemma lem5420166 {A : Type'} (s : A -> Prop) : (term244 A s) = (term230 A s).
Proof. exact (fun_ext (fun f : nat -> A => @lem5420165 A s f)). Qed.
Lemma lem5420167 {A : Type'} : (@ex (nat -> A)) = (@ex (nat -> A)).
Proof. exact (eq_refl (@ex (nat -> A))). Qed.
Lemma lem5420168 {A : Type'} (s : A -> Prop) : (term245 A s) = (term222 A s).
Proof. exact (MK_COMB (@lem5420167 A) (@lem5420166 A s)). Qed.
Lemma lem5420169 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5420170 {A : Type'} (s : A -> Prop) : (term246 A s) = (term225 A s).
Proof. exact (MK_COMB (@lem5420169) (@lem5420168 A s)). Qed.
Lemma lem5420171 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term235 A s f) = (term63 A f s).
Proof. exact (eq_refl (term235 A s f)). Qed.
Lemma lem5420172 {A : Type'} (s : A -> Prop) : (term247 A s) = (term64 A s).
Proof. exact (fun_ext (fun f : nat -> A => @lem5420171 A f s)). Qed.
Lemma lem5420173 {A : Type'} : (@ex (nat -> A)) = (@ex (nat -> A)).
Proof. exact (eq_refl (@ex (nat -> A))). Qed.
Lemma lem5420174 {A : Type'} (s : A -> Prop) : (term248 A s) = (term65 A s).
Proof. exact (MK_COMB (@lem5420173 A) (@lem5420172 A s)). Qed.
Lemma lem5420175 {A : Type'} (s : A -> Prop) : (term249 A s) = (term227 A s).
Proof. exact (MK_COMB (@lem5420170 A s) (@lem5420174 A s)). Qed.
Lemma lem5420176 {A : Type'} (s : A -> Prop) : (term229 A s) = (term250 A s).
Proof. exact (MK_COMB (@lem5420164 A s) (@lem5420175 A s)). Qed.
Lemma lem5420177 {A : Type'} (s : A -> Prop) : term250 A s.
Proof. exact (EQ_MP (@lem5420176 A s) (@lem5420154 A s)). Qed.
Lemma lem5420241 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term251 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem5420242 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term251 A s t).
Proof. exact (@lem5420241 A s t). Qed.
Lemma lem5420243 {A : Type'} (f : nat -> A) (s : A -> Prop) : (s = (term56 A f s)) = (term252 A f s).
Proof. exact (@lem5420242 A s (term56 A f s)). Qed.
Lemma lem5420252 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term62 A s f) = (term62 A s f).
Proof. exact (eq_refl (term62 A s f)). Qed.
Lemma lem5420253 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term63 A f s) = (term253 A f s).
Proof. exact (MK_COMB (@lem5420252 A s f) (@lem5420243 A f s)). Qed.
Lemma lem5420256 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term234 A s f) = (term234 A s f).
Proof. exact (eq_refl (term234 A s f)). Qed.
Lemma lem5420257 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term237 A f s) = (term254 A f s).
Proof. exact (MK_COMB (@lem5420256 A s f) (@lem5420253 A f s)). Qed.
Lemma lem5420260 {A : Type'} (s : A -> Prop) : (term239 A s) = (term255 A s).
Proof. exact (fun_ext (fun f : nat -> A => @lem5420257 A f s)). Qed.
Lemma lem5420261 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem5420262 {A : Type'} (s : A -> Prop) : (term241 A s) = (term256 A s).
Proof. exact (MK_COMB (@lem5420261 A) (@lem5420260 A s)). Qed.
Lemma lem5420267 {A : Type'} (s : A -> Prop) : (term256 A s) = (term241 A s).
Proof. exact (SYM (@lem5420262 A s)). Qed.
Lemma lem5420287 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5420288 (P : nat -> Prop) (x : nat) : (@IN nat x P) = (P x).
Proof. exact (@lem5420287 nat P x). Qed.
Lemma lem5420289 {A : Type'} (s : A -> Prop) (x : nat) : (term69 A x s) = (term257 A s x).
Proof. exact (@lem5420288 (term7 A s) x). Qed.
Lemma lem5420290 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5420291 {A : Type'} (s : A -> Prop) (x : nat) : (term258 A x s) = (term259 A s x).
Proof. exact (MK_COMB (@lem5420290) (@lem5420289 A s x)). Qed.
Lemma lem5420295 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5420296 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5420295 A P x). Qed.
Lemma lem5420297 {A : Type'} (s : A -> Prop) (f : nat -> A) (x : nat) : (term260 A f x s) = (term261 A s f x).
Proof. exact (@lem5420296 A s (f x)). Qed.
Lemma lem5420298 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5420299 {A : Type'} (s : A -> Prop) (f : nat -> A) (x : nat) : (term262 A f x s) = (term263 A s f x).
Proof. exact (MK_COMB (@lem5420298) (@lem5420297 A s f x)). Qed.
Lemma lem5420302 {A : Type'} (g : A -> nat) (f : nat -> A) (x : nat) : ((term264 A g f x) = x) = ((term264 A g f x) = x).
Proof. exact (eq_refl ((term264 A g f x) = x)). Qed.
Lemma lem5420303 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : nat -> A) (x : nat) : (term265 A s g f x) = (term266 A s g f x).
Proof. exact (MK_COMB (@lem5420299 A s f x) (@lem5420302 A g f x)). Qed.
Lemma lem5420306 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : nat -> A) (x : nat) : (term267 A s g f x) = (term268 A s g f x).
Proof. exact (MK_COMB (@lem5420291 A s x) (@lem5420303 A s g f x)). Qed.
Lemma lem5420309 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : nat -> A) : (term269 A s g f) = (term270 A s g f).
Proof. exact (fun_ext (fun x : nat => @lem5420306 A s g f x)). Qed.
Lemma lem5420310 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5420311 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : nat -> A) : (term271 A s g f) = (term272 A s g f).
Proof. exact (MK_COMB (@lem5420310) (@lem5420309 A s g f)). Qed.
Lemma lem5420316 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5420317 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : nat -> A) : (term273 A s g f) = (term274 A s g f).
Proof. exact (MK_COMB (@lem5420316) (@lem5420311 A s g f)). Qed.
Lemma lem5420325 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5420326 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5420325 A P x). Qed.
Lemma lem5420327 {A : Type'} (s : A -> Prop) (y : A) : (@IN A y s) = (s y).
Proof. exact (@lem5420326 A s y). Qed.
Lemma lem5420328 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5420329 {A : Type'} (s : A -> Prop) (y : A) : (term275 A y s) = (term276 A s y).
Proof. exact (MK_COMB (@lem5420328) (@lem5420327 A s y)). Qed.
Lemma lem5420333 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5420334 (P : nat -> Prop) (x : nat) : (@IN nat x P) = (P x).
Proof. exact (@lem5420333 nat P x). Qed.
Lemma lem5420335 {A : Type'} (s : A -> Prop) (g : A -> nat) (y : A) : (term277 A g y s) = (term278 A s g y).
Proof. exact (@lem5420334 (term7 A s) (g y)). Qed.
Lemma lem5420336 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5420337 {A : Type'} (s : A -> Prop) (g : A -> nat) (y : A) : (term279 A g y s) = (term280 A s g y).
Proof. exact (MK_COMB (@lem5420336) (@lem5420335 A s g y)). Qed.
Lemma lem5420340 {A : Type'} (f : nat -> A) (g : A -> nat) (y : A) : ((term281 A f g y) = y) = ((term281 A f g y) = y).
Proof. exact (eq_refl ((term281 A f g y) = y)). Qed.
Lemma lem5420341 {A : Type'} (s : A -> Prop) (f : nat -> A) (g : A -> nat) (y : A) : (term282 A s f g y) = (term283 A s f g y).
Proof. exact (MK_COMB (@lem5420337 A s g y) (@lem5420340 A f g y)). Qed.
Lemma lem5420344 {A : Type'} (s : A -> Prop) (f : nat -> A) (g : A -> nat) (y : A) : (term284 A s f g y) = (term285 A s f g y).
Proof. exact (MK_COMB (@lem5420329 A s y) (@lem5420341 A s f g y)). Qed.
Lemma lem5420347 {A : Type'} (s : A -> Prop) (f : nat -> A) (g : A -> nat) : (term286 A s f g) = (term287 A s f g).
Proof. exact (fun_ext (fun y : A => @lem5420344 A s f g y)). Qed.
Lemma lem5420348 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5420349 {A : Type'} (s : A -> Prop) (f : nat -> A) (g : A -> nat) : (term288 A s f g) = (term289 A s f g).
Proof. exact (MK_COMB (@lem5420348 A) (@lem5420347 A s f g)). Qed.
Lemma lem5420354 {A : Type'} (s : A -> Prop) (f : nat -> A) (g : A -> nat) : (term290 A s f g) = (term291 A s f g).
Proof. exact (MK_COMB (@lem5420317 A s g f) (@lem5420349 A s f g)). Qed.
Lemma lem5420357 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term292 A s f) = (term293 A s f).
Proof. exact (fun_ext (fun g : A -> nat => @lem5420354 A s f g)). Qed.
Lemma lem5420358 {A : Type'} : (@ex (A -> nat)) = (@ex (A -> nat)).
Proof. exact (eq_refl (@ex (A -> nat))). Qed.
Lemma lem5420359 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term232 A s f) = (term294 A s f).
Proof. exact (MK_COMB (@lem5420358 A) (@lem5420357 A s f)). Qed.
Lemma lem5420364 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5420365 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term234 A s f) = (term295 A s f).
Proof. exact (MK_COMB (@lem5420364) (@lem5420359 A s f)). Qed.
Lemma lem5420381 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5420382 (P : nat -> Prop) (x : nat) : (@IN nat x P) = (P x).
Proof. exact (@lem5420381 nat P x). Qed.
Lemma lem5420383 {A : Type'} (s : A -> Prop) (i : nat) : (term69 A i s) = (term257 A s i).
Proof. exact (@lem5420382 (term7 A s) i). Qed.
Lemma lem5420384 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5420385 {A : Type'} (s : A -> Prop) (i : nat) : (term296 A i s) = (term297 A s i).
Proof. exact (MK_COMB (@lem5420384) (@lem5420383 A s i)). Qed.
Lemma lem5420389 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5420390 (P : nat -> Prop) (x : nat) : (@IN nat x P) = (P x).
Proof. exact (@lem5420389 nat P x). Qed.
Lemma lem5420391 {A : Type'} (s : A -> Prop) (j : nat) : (term69 A j s) = (term257 A s j).
Proof. exact (@lem5420390 (term7 A s) j). Qed.
Lemma lem5420392 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5420393 {A : Type'} (s : A -> Prop) (j : nat) : (term296 A j s) = (term297 A s j).
Proof. exact (MK_COMB (@lem5420392) (@lem5420391 A s j)). Qed.
Lemma lem5420396 {A : Type'} (i : nat) (f : nat -> A) (j : nat) : ((f i) = (f j)) = ((f i) = (f j)).
Proof. exact (eq_refl ((f i) = (f j))). Qed.
Lemma lem5420397 {A : Type'} (s : A -> Prop) (i : nat) (f : nat -> A) (j : nat) : (term74 A s i f j) = (term298 A s i f j).
Proof. exact (MK_COMB (@lem5420393 A s j) (@lem5420396 A i f j)). Qed.
Lemma lem5420400 {A : Type'} (s : A -> Prop) (i : nat) (f : nat -> A) (j : nat) : (term79 A s i f j) = (term299 A s i f j).
Proof. exact (MK_COMB (@lem5420385 A s i) (@lem5420397 A s i f j)). Qed.
Lemma lem5420403 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5420404 {A : Type'} (s : A -> Prop) (i : nat) (f : nat -> A) (j : nat) : (term300 A s i f j) = (term301 A s i f j).
Proof. exact (MK_COMB (@lem5420403) (@lem5420400 A s i f j)). Qed.
Lemma lem5420407 (i : nat) (j : nat) : (i = j) = (i = j).
Proof. exact (eq_refl (i = j)). Qed.
Lemma lem5420408 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) : (term57 A s f i j) = (term302 A s f i j).
Proof. exact (MK_COMB (@lem5420404 A s i f j) (@lem5420407 i j)). Qed.
Lemma lem5420411 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) : (term58 A s f i) = (term303 A s f i).
Proof. exact (fun_ext (fun j : nat => @lem5420408 A s f i j)). Qed.
Lemma lem5420412 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5420413 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) : (term59 A s f i) = (term304 A s f i).
Proof. exact (MK_COMB (@lem5420412) (@lem5420411 A s f i)). Qed.
Lemma lem5420418 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term60 A s f) = (term305 A s f).
Proof. exact (fun_ext (fun i : nat => @lem5420413 A s f i)). Qed.
Lemma lem5420419 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5420420 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term61 A s f) = (term306 A s f).
Proof. exact (MK_COMB (@lem5420419) (@lem5420418 A s f)). Qed.
Lemma lem5420425 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5420426 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term62 A s f) = (term307 A s f).
Proof. exact (MK_COMB (@lem5420425) (@lem5420420 A s f)). Qed.
Lemma lem5420434 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5420435 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5420434 A P x). Qed.
Lemma lem5420436 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem5420435 A s x). Qed.
Lemma lem5420437 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5420438 {A : Type'} (s : A -> Prop) (x : A) : (term308 A x s) = (term309 A s x).
Proof. exact (MK_COMB (@lem5420437) (@lem5420436 A s x)). Qed.
Lemma lem5420440 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term310 A B y f s) = (term311 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem5420441 {A : Type'} (y : A) (f : nat -> A) (s : nat -> Prop) : (term312 A y f s) = (term313 A y f s).
Proof. exact (@lem5420440 nat A y f s). Qed.
Lemma lem5420442 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term314 A x f s) = (term315 A x f s).
Proof. exact (@lem5420441 A x f (term7 A s)). Qed.
Lemma lem5420452 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5420453 (P : nat -> Prop) (x : nat) : (@IN nat x P) = (P x).
Proof. exact (@lem5420452 nat P x). Qed.
Lemma lem5420454 {A : Type'} (s : A -> Prop) (x : nat) : (term69 A x s) = (term257 A s x).
Proof. exact (@lem5420453 (term7 A s) x). Qed.
Lemma lem5420455 {A : Type'} (x : A) (f : nat -> A) (x' : nat) : (term316 A x f x') = (term316 A x f x').
Proof. exact (eq_refl (term316 A x f x')). Qed.
Lemma lem5420456 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) (x' : nat) : (term317 A x f x' s) = (term318 A x f s x').
Proof. exact (MK_COMB (@lem5420455 A x f x') (@lem5420454 A s x')). Qed.
Lemma lem5420459 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term319 A x f s) = (term320 A x f s).
Proof. exact (fun_ext (fun x' : nat => @lem5420456 A x f s x')). Qed.
Lemma lem5420460 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5420461 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term315 A x f s) = (term321 A x f s).
Proof. exact (MK_COMB (@lem5420460) (@lem5420459 A x f s)). Qed.
Lemma lem5420466 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term314 A x f s) = (term321 A x f s).
Proof. exact (TRANS (@lem5420442 A x f s) (@lem5420461 A x f s)). Qed.
Lemma lem5420467 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : ((@IN A x s) = (term314 A x f s)) = ((s x) = (term321 A x f s)).
Proof. exact (MK_COMB (@lem5420438 A s x) (@lem5420466 A x f s)). Qed.
Lemma lem5420470 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term322 A f s) = (term323 A f s).
Proof. exact (fun_ext (fun x : A => @lem5420467 A x f s)). Qed.
Lemma lem5420471 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5420472 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term252 A f s) = (term324 A f s).
Proof. exact (MK_COMB (@lem5420471 A) (@lem5420470 A f s)). Qed.
Lemma lem5420477 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term253 A f s) = (term325 A f s).
Proof. exact (MK_COMB (@lem5420426 A s f) (@lem5420472 A f s)). Qed.
Lemma lem5420480 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term254 A f s) = (term326 A f s).
Proof. exact (MK_COMB (@lem5420365 A s f) (@lem5420477 A f s)). Qed.
Lemma lem5420483 {A : Type'} (s : A -> Prop) : (term255 A s) = (term327 A s).
Proof. exact (fun_ext (fun f : nat -> A => @lem5420480 A f s)). Qed.
Lemma lem5420484 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem5420485 {A : Type'} (s : A -> Prop) : (term256 A s) = (term328 A s).
Proof. exact (MK_COMB (@lem5420484 A) (@lem5420483 A s)). Qed.
Lemma lem5420490 {A : Type'} (s : A -> Prop) : (term328 A s) = (term256 A s).
Proof. exact (SYM (@lem5420485 A s)). Qed.
Lemma lem5420492 (p : Prop) : p = (term11 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5420493 {A : Type'} (s : A -> Prop) : (term328 A s) = (term329 A s).
Proof. exact (@lem5420492 (term328 A s)). Qed.
Lemma lem5420494 {A : Type'} (s : A -> Prop) : (term329 A s) = (term328 A s).
Proof. exact (SYM (@lem5420493 A s)). Qed.
Lemma lem5420495 {A : Type'} (s : A -> Prop) (h1 : term330 A s) : term330 A s.
Proof. exact (h1). Qed.
Lemma lem5420498 {A : Type'} (s : A -> Prop) (h1 : term329 A s) : term329 A s.
Proof. exact (h1). Qed.
Lemma lem5420499 {A : Type'} (s : A -> Prop) : term331 A s.
Proof. exact (fun h0 : term329 A s => @lem5420498 A s h0). Qed.
Lemma lem5420500 {A : Type'} (s : A -> Prop) (h1 : term331 A s) : term331 A s.
Proof. exact (h1). Qed.
Lemma lem5420501 {A : Type'} (s : A -> Prop) (h1 : term329 A s) : term329 A s.
Proof. exact (h1). Qed.
Lemma lem5420502 {A : Type'} (s : A -> Prop) (h1 : term329 A s) (h2 : term331 A s) : term329 A s.
Proof. exact (@lem5420500 A s h2 (@lem5420501 A s h1)). Qed.
Lemma lem5420503 {A : Type'} (s : A -> Prop) (h1 : term329 A s) : term332 A s.
Proof. exact (fun h0 : term331 A s => @lem5420502 A s h1 h0). Qed.
Lemma lem5420504 {A : Type'} (s : A -> Prop) (h1 : term331 A s) : term331 A s.
Proof. exact (h1). Qed.
Lemma lem5420505 {A : Type'} (s : A -> Prop) (h1 : term329 A s) (h2 : term331 A s) : term329 A s.
Proof. exact (@lem5420503 A s h1 (@lem5420504 A s h2)). Qed.
Lemma lem5420506 {A : Type'} (s : A -> Prop) (h1 : term331 A s) : term331 A s.
Proof. exact (fun h0 : term329 A s => @lem5420505 A s h0 h1). Qed.
Lemma lem5420507 {A : Type'} (s : A -> Prop) : term333 A s.
Proof. exact (fun h0 : term331 A s => @lem5420506 A s h0). Qed.
Lemma lem5420510 {A : Type'} (s : A -> Prop) : term331 A s.
Proof. exact (@lem5420507 A s (@lem5420499 A s)). Qed.
Lemma lem5420511 {A : Type'} (s : A -> Prop) : term331 A s.
Proof. exact (@lem5420510 A s). Qed.
Lemma lem5420517 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5420518 {A : Type'} (s : A -> Prop) : (term329 A s) = (term334 A s).
Proof. exact (@lem5420517 (term330 A s)). Qed.
Lemma lem5420520 (t : Prop) : (term166 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5420521 {A : Type'} (s : A -> Prop) : (term334 A s) = (term328 A s).
Proof. exact (@lem5420520 (term328 A s)). Qed.
Lemma lem5420526 {A : Type'} (s : A -> Prop) : (term329 A s) = (term328 A s).
Proof. exact (TRANS (@lem5420518 A s) (@lem5420521 A s)). Qed.
Lemma lem5420665 {A : Type'} : (term335 A) = (term336 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5420526 A s)). Qed.
Lemma lem5420666 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5420675 {A : Type'} : (term337 A) = (term338 A).
Proof. exact (MK_COMB (@lem5420666 A) (@lem5420665 A)). Qed.
Lemma lem5420680 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) (x' : nat) : (term318 A x f s x') = (term318 A x f s x').
Proof. exact (eq_refl (term318 A x f s x')). Qed.
Lemma lem5420681 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term320 A x f s) = (term320 A x f s).
Proof. exact (fun_ext (fun x' : nat => @lem5420680 A x f s x')). Qed.
Lemma lem5420682 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5420683 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term321 A x f s) = (term321 A x f s).
Proof. exact (MK_COMB (@lem5420682) (@lem5420681 A x f s)). Qed.
Lemma lem5420686 {A : Type'} (s : A -> Prop) (x : A) : (term309 A s x) = (term309 A s x).
Proof. exact (eq_refl (term309 A s x)). Qed.
Lemma lem5420687 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : ((s x) = (term321 A x f s)) = ((s x) = (term321 A x f s)).
Proof. exact (MK_COMB (@lem5420686 A s x) (@lem5420683 A x f s)). Qed.
Lemma lem5420688 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term323 A f s) = (term323 A f s).
Proof. exact (fun_ext (fun x : A => @lem5420687 A x f s)). Qed.
Lemma lem5420689 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5420690 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term324 A f s) = (term324 A f s).
Proof. exact (MK_COMB (@lem5420689 A) (@lem5420688 A f s)). Qed.
Lemma lem5420703 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) : (term302 A s f i j) = (term302 A s f i j).
Proof. exact (eq_refl (term302 A s f i j)). Qed.
Lemma lem5420704 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) : (term303 A s f i) = (term303 A s f i).
Proof. exact (fun_ext (fun j : nat => @lem5420703 A s f i j)). Qed.
Lemma lem5420705 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5420706 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) : (term304 A s f i) = (term304 A s f i).
Proof. exact (MK_COMB (@lem5420705) (@lem5420704 A s f i)). Qed.
Lemma lem5420707 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term305 A s f) = (term305 A s f).
Proof. exact (fun_ext (fun i : nat => @lem5420706 A s f i)). Qed.
Lemma lem5420708 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5420709 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term306 A s f) = (term306 A s f).
Proof. exact (MK_COMB (@lem5420708) (@lem5420707 A s f)). Qed.
Lemma lem5420710 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5420711 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term307 A s f) = (term307 A s f).
Proof. exact (MK_COMB (@lem5420710) (@lem5420709 A s f)). Qed.
Lemma lem5420712 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term325 A f s) = (term325 A f s).
Proof. exact (MK_COMB (@lem5420711 A s f) (@lem5420690 A f s)). Qed.
Lemma lem5420721 {A : Type'} (s : A -> Prop) (f : nat -> A) (g : A -> nat) (y : A) : (term285 A s f g y) = (term285 A s f g y).
Proof. exact (eq_refl (term285 A s f g y)). Qed.
Lemma lem5420722 {A : Type'} (s : A -> Prop) (f : nat -> A) (g : A -> nat) : (term287 A s f g) = (term287 A s f g).
Proof. exact (fun_ext (fun y : A => @lem5420721 A s f g y)). Qed.
Lemma lem5420723 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5420724 {A : Type'} (s : A -> Prop) (f : nat -> A) (g : A -> nat) : (term289 A s f g) = (term289 A s f g).
Proof. exact (MK_COMB (@lem5420723 A) (@lem5420722 A s f g)). Qed.
Lemma lem5420733 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : nat -> A) (x : nat) : (term268 A s g f x) = (term268 A s g f x).
Proof. exact (eq_refl (term268 A s g f x)). Qed.
Lemma lem5420734 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : nat -> A) : (term270 A s g f) = (term270 A s g f).
Proof. exact (fun_ext (fun x : nat => @lem5420733 A s g f x)). Qed.
Lemma lem5420735 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5420736 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : nat -> A) : (term272 A s g f) = (term272 A s g f).
Proof. exact (MK_COMB (@lem5420735) (@lem5420734 A s g f)). Qed.
Lemma lem5420737 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5420738 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : nat -> A) : (term274 A s g f) = (term274 A s g f).
Proof. exact (MK_COMB (@lem5420737) (@lem5420736 A s g f)). Qed.
Lemma lem5420739 {A : Type'} (s : A -> Prop) (f : nat -> A) (g : A -> nat) : (term291 A s f g) = (term291 A s f g).
Proof. exact (MK_COMB (@lem5420738 A s g f) (@lem5420724 A s f g)). Qed.
Lemma lem5420740 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term293 A s f) = (term293 A s f).
Proof. exact (fun_ext (fun g : A -> nat => @lem5420739 A s f g)). Qed.
Lemma lem5420741 {A : Type'} : (@ex (A -> nat)) = (@ex (A -> nat)).
Proof. exact (eq_refl (@ex (A -> nat))). Qed.
Lemma lem5420742 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term294 A s f) = (term294 A s f).
Proof. exact (MK_COMB (@lem5420741 A) (@lem5420740 A s f)). Qed.
Lemma lem5420743 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5420744 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term295 A s f) = (term295 A s f).
Proof. exact (MK_COMB (@lem5420743) (@lem5420742 A s f)). Qed.
Lemma lem5420745 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term326 A f s) = (term326 A f s).
Proof. exact (MK_COMB (@lem5420744 A s f) (@lem5420712 A f s)). Qed.
Lemma lem5420746 {A : Type'} (s : A -> Prop) : (term327 A s) = (term327 A s).
Proof. exact (fun_ext (fun f : nat -> A => @lem5420745 A f s)). Qed.
Lemma lem5420747 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem5420748 {A : Type'} (s : A -> Prop) : (term328 A s) = (term328 A s).
Proof. exact (MK_COMB (@lem5420747 A) (@lem5420746 A s)). Qed.
Lemma lem5420749 {A : Type'} : (term336 A) = (term336 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5420748 A s)). Qed.
Lemma lem5420750 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5420751 {A : Type'} : (term338 A) = (term338 A).
Proof. exact (MK_COMB (@lem5420750 A) (@lem5420749 A)). Qed.
Lemma lem5420830 {A : Type'} : (term337 A) = (term338 A).
Proof. exact (TRANS (@lem5420675 A) (@lem5420751 A)). Qed.
Lemma lem5420831 {A : Type'} : (term338 A) = (term337 A).
Proof. exact (SYM (@lem5420830 A)). Qed.
Lemma lem5420832 {A : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term294 A s f) : term294 A s f.
Proof. exact (h1). Qed.
Lemma lem5420834 (p : Prop) : p = (term11 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5420835 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term325 A f s) = (term339 A f s).
Proof. exact (@lem5420834 (term325 A f s)). Qed.
Lemma lem5420836 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term339 A f s) = (term325 A f s).
Proof. exact (SYM (@lem5420835 A f s)). Qed.
Lemma lem5420837 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term340 A f s) : term340 A f s.
Proof. exact (h1). Qed.
Lemma lem5420848 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : nat -> A) (x : nat) : (term268 A s g f x) = (term341 A s g f x).
Proof. exact (@lem17265 (term257 A s x) (term266 A s g f x)). Qed.
Lemma lem5420849 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : nat -> A) : (term270 A s g f) = (term342 A s g f).
Proof. exact (fun_ext (fun x : nat => @lem5420848 A s g f x)). Qed.
Lemma lem5420850 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5420851 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : nat -> A) : (term272 A s g f) = (term343 A s g f).
Proof. exact (MK_COMB (@lem5420850) (@lem5420849 A s g f)). Qed.
Lemma lem5420862 {A : Type'} (s : A -> Prop) (f : nat -> A) (g : A -> nat) (y : A) : (term285 A s f g y) = (term344 A s f g y).
Proof. exact (@lem17265 (s y) (term283 A s f g y)). Qed.
Lemma lem5420863 {A : Type'} (s : A -> Prop) (f : nat -> A) (g : A -> nat) : (term287 A s f g) = (term345 A s f g).
Proof. exact (fun_ext (fun y : A => @lem5420862 A s f g y)). Qed.
Lemma lem5420864 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5420865 {A : Type'} (s : A -> Prop) (f : nat -> A) (g : A -> nat) : (term289 A s f g) = (term346 A s f g).
Proof. exact (MK_COMB (@lem5420864 A) (@lem5420863 A s f g)). Qed.
Lemma lem5420866 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5420867 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : nat -> A) : (term274 A s g f) = (term347 A s g f).
Proof. exact (MK_COMB (@lem5420866) (@lem5420851 A s g f)). Qed.
Lemma lem5420868 {A : Type'} (s : A -> Prop) (f : nat -> A) (g : A -> nat) : (term291 A s f g) = (term348 A s f g).
Proof. exact (MK_COMB (@lem5420867 A s g f) (@lem5420865 A s f g)). Qed.
Lemma lem5420869 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term293 A s f) = (term349 A s f).
Proof. exact (fun_ext (fun g : A -> nat => @lem5420868 A s f g)). Qed.
Lemma lem5420870 {A : Type'} : (@ex (A -> nat)) = (@ex (A -> nat)).
Proof. exact (eq_refl (@ex (A -> nat))). Qed.
Lemma lem5421019 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term294 A s f) = (term350 A s f).
Proof. exact (MK_COMB (@lem5420870 A) (@lem5420869 A s f)). Qed.
Lemma lem5421020 {A : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term294 A s f) : term350 A s f.
Proof. exact (EQ_MP (@lem5421019 A s f) (@lem5420832 A s f h1)). Qed.
Lemma lem5421035 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) : (term351 A s f i j) = (term352 A s f i j).
Proof. exact (@lem17362 (term299 A s i f j) (i = j)). Qed.
Lemma lem5421036 (P : nat -> Prop) : (term353 P) = (term354 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem5421037 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) : (term355 A s f i) = (term356 A s f i).
Proof. exact (@lem5421036 (term303 A s f i)). Qed.
Lemma lem5421038 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) : (term357 A s f i j) = (term302 A s f i j).
Proof. exact (eq_refl (term357 A s f i j)). Qed.
Lemma lem5421039 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5421040 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) : (term358 A s f i j) = (term351 A s f i j).
Proof. exact (MK_COMB (@lem5421039) (@lem5421038 A s f i j)). Qed.
Lemma lem5421041 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) : (term358 A s f i j) = (term352 A s f i j).
Proof. exact (TRANS (@lem5421040 A s f i j) (@lem5421035 A s f i j)). Qed.
Lemma lem5421042 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) : (term359 A s f i) = (term360 A s f i).
Proof. exact (fun_ext (fun j : nat => @lem5421041 A s f i j)). Qed.
Lemma lem5421043 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5421044 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) : (term356 A s f i) = (term361 A s f i).
Proof. exact (MK_COMB (@lem5421043) (@lem5421042 A s f i)). Qed.
Lemma lem5421045 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) : (term355 A s f i) = (term361 A s f i).
Proof. exact (TRANS (@lem5421037 A s f i) (@lem5421044 A s f i)). Qed.
Lemma lem5421046 (P : nat -> Prop) : (term353 P) = (term354 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem5421047 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term362 A s f) = (term363 A s f).
Proof. exact (@lem5421046 (term305 A s f)). Qed.
Lemma lem5421048 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) : (term364 A s f i) = (term304 A s f i).
Proof. exact (eq_refl (term364 A s f i)). Qed.
Lemma lem5421049 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5421050 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) : (term365 A s f i) = (term355 A s f i).
Proof. exact (MK_COMB (@lem5421049) (@lem5421048 A s f i)). Qed.
Lemma lem5421051 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) : (term365 A s f i) = (term361 A s f i).
Proof. exact (TRANS (@lem5421050 A s f i) (@lem5421045 A s f i)). Qed.
Lemma lem5421052 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term366 A s f) = (term367 A s f).
Proof. exact (fun_ext (fun i : nat => @lem5421051 A s f i)). Qed.
Lemma lem5421053 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5421054 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term363 A s f) = (term368 A s f).
Proof. exact (MK_COMB (@lem5421053) (@lem5421052 A s f)). Qed.
Lemma lem5421055 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term362 A s f) = (term368 A s f).
Proof. exact (TRANS (@lem5421047 A s f) (@lem5421054 A s f)). Qed.
Lemma lem5421066 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) (x' : nat) : (term369 A x f s x') = (term370 A x f s x').
Proof. exact (@lem17045 (x = (f x')) (term257 A s x')). Qed.
Lemma lem5421069 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) (x' : nat) : (term318 A x f s x') = (term318 A x f s x').
Proof. exact (eq_refl (term318 A x f s x')). Qed.
Lemma lem5421070 (P : nat -> Prop) : (term371 P) = (term372 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem5421071 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term373 A x f s) = (term374 A x f s).
Proof. exact (@lem5421070 (term320 A x f s)). Qed.
Lemma lem5421072 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) (x' : nat) : (term375 A x f s x') = (term318 A x f s x').
Proof. exact (eq_refl (term375 A x f s x')). Qed.
Lemma lem5421073 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5421074 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) (x' : nat) : (term376 A x f s x') = (term369 A x f s x').
Proof. exact (MK_COMB (@lem5421073) (@lem5421072 A x f s x')). Qed.
Lemma lem5421075 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) (x' : nat) : (term376 A x f s x') = (term370 A x f s x').
Proof. exact (TRANS (@lem5421074 A x f s x') (@lem5421066 A x f s x')). Qed.
Lemma lem5421076 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term377 A x f s) = (term378 A x f s).
Proof. exact (fun_ext (fun x' : nat => @lem5421075 A x f s x')). Qed.
Lemma lem5421077 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5421078 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term374 A x f s) = (term379 A x f s).
Proof. exact (MK_COMB (@lem5421077) (@lem5421076 A x f s)). Qed.
Lemma lem5421079 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term373 A x f s) = (term379 A x f s).
Proof. exact (TRANS (@lem5421071 A x f s) (@lem5421078 A x f s)). Qed.
Lemma lem5421080 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term320 A x f s) = (term320 A x f s).
Proof. exact (fun_ext (fun x' : nat => @lem5421069 A x f s x')). Qed.
Lemma lem5421081 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5421082 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term321 A x f s) = (term321 A x f s).
Proof. exact (MK_COMB (@lem5421081) (@lem5421080 A x f s)). Qed.
Lemma lem5421084 {A : Type'} (s : A -> Prop) (x : A) : (term380 A s x) = (term380 A s x).
Proof. exact (eq_refl (term380 A s x)). Qed.
Lemma lem5421085 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term381 A x f s) = (term381 A x f s).
Proof. exact (MK_COMB (@lem5421084 A s x) (@lem5421082 A x f s)). Qed.
Lemma lem5421087 {A : Type'} (s : A -> Prop) (x : A) : (term382 A s x) = (term382 A s x).
Proof. exact (eq_refl (term382 A s x)). Qed.
Lemma lem5421088 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term383 A x f s) = (term384 A x f s).
Proof. exact (MK_COMB (@lem5421087 A s x) (@lem5421079 A x f s)). Qed.
Lemma lem5421089 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5421090 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term385 A x f s) = (term386 A x f s).
Proof. exact (MK_COMB (@lem5421089) (@lem5421088 A x f s)). Qed.
Lemma lem5421091 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term387 A x f s) = (term388 A x f s).
Proof. exact (MK_COMB (@lem5421090 A x f s) (@lem5421085 A x f s)). Qed.
Lemma lem5421092 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term389 A x f s) = (term387 A x f s).
Proof. exact (@lem17646 (s x) (term321 A x f s)). Qed.
Lemma lem5421093 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term389 A x f s) = (term388 A x f s).
Proof. exact (TRANS (@lem5421092 A x f s) (@lem5421091 A x f s)). Qed.
Lemma lem5421094 {A : Type'} (P : A -> Prop) : (term390 A P) = (term391 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem5421095 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term392 A f s) = (term393 A f s).
Proof. exact (@lem5421094 A (term323 A f s)). Qed.
Lemma lem5421096 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term394 A f s x) = ((s x) = (term321 A x f s)).
Proof. exact (eq_refl (term394 A f s x)). Qed.
Lemma lem5421097 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5421098 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term395 A f s x) = (term389 A x f s).
Proof. exact (MK_COMB (@lem5421097) (@lem5421096 A x f s)). Qed.
Lemma lem5421099 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term395 A f s x) = (term388 A x f s).
Proof. exact (TRANS (@lem5421098 A x f s) (@lem5421093 A x f s)). Qed.
Lemma lem5421100 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term396 A f s) = (term397 A f s).
Proof. exact (fun_ext (fun x : A => @lem5421099 A x f s)). Qed.
Lemma lem5421101 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5421102 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term393 A f s) = (term398 A f s).
Proof. exact (MK_COMB (@lem5421101 A) (@lem5421100 A f s)). Qed.
Lemma lem5421103 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term392 A f s) = (term398 A f s).
Proof. exact (TRANS (@lem5421095 A f s) (@lem5421102 A f s)). Qed.
Lemma lem5421104 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5421105 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term399 A s f) = (term400 A s f).
Proof. exact (MK_COMB (@lem5421104) (@lem5421055 A s f)). Qed.
Lemma lem5421106 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term401 A f s) = (term402 A f s).
Proof. exact (MK_COMB (@lem5421105 A s f) (@lem5421103 A f s)). Qed.
Lemma lem5421107 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term340 A f s) = (term401 A f s).
Proof. exact (@lem17045 (term306 A s f) (term324 A f s)). Qed.
Lemma lem5421108 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term340 A f s) = (term402 A f s).
Proof. exact (TRANS (@lem5421107 A f s) (@lem5421106 A f s)). Qed.
Lemma lem5421162 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term403 A P Q) = (term404 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem5421163 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term403 A P Q) = (term404 A P Q).
Proof. exact (@lem5421162 A P Q). Qed.
Lemma lem5421164 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term405 A f s) = (term406 A f s).
Proof. exact (@lem5421163 A (term407 A f s) (term408 A f s)). Qed.
Lemma lem5421165 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term409 A f s x) = (term384 A x f s).
Proof. exact (eq_refl (term409 A f s x)). Qed.
Lemma lem5421166 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5421167 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term410 A f s x) = (term386 A x f s).
Proof. exact (MK_COMB (@lem5421166) (@lem5421165 A x f s)). Qed.
Lemma lem5421168 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term411 A f s x) = (term381 A x f s).
Proof. exact (eq_refl (term411 A f s x)). Qed.
Lemma lem5421169 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term412 A f s x) = (term388 A x f s).
Proof. exact (MK_COMB (@lem5421167 A x f s) (@lem5421168 A x f s)). Qed.
Lemma lem5421170 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term413 A f s) = (term397 A f s).
Proof. exact (fun_ext (fun x : A => @lem5421169 A x f s)). Qed.
Lemma lem5421171 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5421172 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term405 A f s) = (term398 A f s).
Proof. exact (MK_COMB (@lem5421171 A) (@lem5421170 A f s)). Qed.
Lemma lem5421173 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5421174 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term414 A f s) = (term415 A f s).
Proof. exact (MK_COMB (@lem5421173) (@lem5421172 A f s)). Qed.
Lemma lem5421175 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term409 A f s x) = (term384 A x f s).
Proof. exact (eq_refl (term409 A f s x)). Qed.
Lemma lem5421176 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term416 A f s) = (term407 A f s).
Proof. exact (fun_ext (fun x : A => @lem5421175 A x f s)). Qed.
Lemma lem5421177 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5421178 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term417 A f s) = (term418 A f s).
Proof. exact (MK_COMB (@lem5421177 A) (@lem5421176 A f s)). Qed.
Lemma lem5421179 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5421180 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term419 A f s) = (term420 A f s).
Proof. exact (MK_COMB (@lem5421179) (@lem5421178 A f s)). Qed.
Lemma lem5421181 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term411 A f s x) = (term381 A x f s).
Proof. exact (eq_refl (term411 A f s x)). Qed.
Lemma lem5421182 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term421 A f s) = (term408 A f s).
Proof. exact (fun_ext (fun x : A => @lem5421181 A x f s)). Qed.
Lemma lem5421183 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5421184 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term422 A f s) = (term423 A f s).
Proof. exact (MK_COMB (@lem5421183 A) (@lem5421182 A f s)). Qed.
Lemma lem5421185 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term406 A f s) = (term424 A f s).
Proof. exact (MK_COMB (@lem5421180 A f s) (@lem5421184 A f s)). Qed.
Lemma lem5421186 {A : Type'} (f : nat -> A) (s : A -> Prop) : ((term405 A f s) = (term406 A f s)) = ((term398 A f s) = (term424 A f s)).
Proof. exact (MK_COMB (@lem5421174 A f s) (@lem5421185 A f s)). Qed.
Lemma lem5421187 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term398 A f s) = (term424 A f s).
Proof. exact (EQ_MP (@lem5421186 A f s) (@lem5421164 A f s)). Qed.
Lemma lem5421360 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term400 A s f) = (term400 A s f).
Proof. exact (eq_refl (term400 A s f)). Qed.
Lemma lem5421361 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term402 A f s) = (term425 A f s).
Proof. exact (MK_COMB (@lem5421360 A s f) (@lem5421187 A f s)). Qed.
Lemma lem5421363 {A : Type'} (P : Prop) (Q : A -> Prop) : (term426 A P Q) = (term427 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5421364 (P : Prop) (Q : nat -> Prop) : (term428 P Q) = (term429 P Q).
Proof. exact (@lem5421363 nat P Q). Qed.
Lemma lem5421365 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term430 A x f s) = (term431 A x f s).
Proof. exact (@lem5421364 (term432 A s x) (term320 A x f s)). Qed.
Lemma lem5421366 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) (x' : nat) : (term375 A x f s x') = (term318 A x f s x').
Proof. exact (eq_refl (term375 A x f s x')). Qed.
Lemma lem5421367 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term433 A x f s) = (term320 A x f s).
Proof. exact (fun_ext (fun x' : nat => @lem5421366 A x f s x')). Qed.
Lemma lem5421368 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5421369 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term434 A x f s) = (term321 A x f s).
Proof. exact (MK_COMB (@lem5421368) (@lem5421367 A x f s)). Qed.
Lemma lem5421370 {A : Type'} (s : A -> Prop) (x : A) : (term380 A s x) = (term380 A s x).
Proof. exact (eq_refl (term380 A s x)). Qed.
Lemma lem5421371 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term430 A x f s) = (term381 A x f s).
Proof. exact (MK_COMB (@lem5421370 A s x) (@lem5421369 A x f s)). Qed.
Lemma lem5421372 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5421373 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term435 A x f s) = (term436 A x f s).
Proof. exact (MK_COMB (@lem5421372) (@lem5421371 A x f s)). Qed.
Lemma lem5421374 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) (x' : nat) : (term375 A x f s x') = (term318 A x f s x').
Proof. exact (eq_refl (term375 A x f s x')). Qed.
Lemma lem5421375 {A : Type'} (s : A -> Prop) (x : A) : (term380 A s x) = (term380 A s x).
Proof. exact (eq_refl (term380 A s x)). Qed.
Lemma lem5421376 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) (x' : nat) : (term437 A x f s x') = (term438 A x f s x').
Proof. exact (MK_COMB (@lem5421375 A s x) (@lem5421374 A x f s x')). Qed.
Lemma lem5421377 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term439 A x f s) = (term440 A x f s).
Proof. exact (fun_ext (fun x' : nat => @lem5421376 A x f s x')). Qed.
Lemma lem5421378 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5421379 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term431 A x f s) = (term441 A x f s).
Proof. exact (MK_COMB (@lem5421378) (@lem5421377 A x f s)). Qed.
Lemma lem5421380 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : ((term430 A x f s) = (term431 A x f s)) = ((term381 A x f s) = (term441 A x f s)).
Proof. exact (MK_COMB (@lem5421373 A x f s) (@lem5421379 A x f s)). Qed.
Lemma lem5421381 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term381 A x f s) = (term441 A x f s).
Proof. exact (EQ_MP (@lem5421380 A x f s) (@lem5421365 A x f s)). Qed.
Lemma lem5421382 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term408 A f s) = (term442 A f s).
Proof. exact (fun_ext (fun x : A => @lem5421381 A x f s)). Qed.
Lemma lem5421383 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5421384 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term423 A f s) = (term443 A f s).
Proof. exact (MK_COMB (@lem5421383 A) (@lem5421382 A f s)). Qed.
Lemma lem5421385 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term420 A f s) = (term420 A f s).
Proof. exact (eq_refl (term420 A f s)). Qed.
Lemma lem5421386 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term424 A f s) = (term444 A f s).
Proof. exact (MK_COMB (@lem5421385 A f s) (@lem5421384 A f s)). Qed.
Lemma lem5421388 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term404 A P Q) = (term403 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5421389 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term404 A P Q) = (term403 A P Q).
Proof. exact (@lem5421388 A P Q). Qed.
Lemma lem5421390 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term445 A f s) = (term446 A f s).
Proof. exact (@lem5421389 A (term407 A f s) (term442 A f s)). Qed.
Lemma lem5421391 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term409 A f s x) = (term384 A x f s).
Proof. exact (eq_refl (term409 A f s x)). Qed.
Lemma lem5421392 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term416 A f s) = (term407 A f s).
Proof. exact (fun_ext (fun x : A => @lem5421391 A x f s)). Qed.
Lemma lem5421393 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5421394 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term417 A f s) = (term418 A f s).
Proof. exact (MK_COMB (@lem5421393 A) (@lem5421392 A f s)). Qed.
Lemma lem5421395 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5421396 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term419 A f s) = (term420 A f s).
Proof. exact (MK_COMB (@lem5421395) (@lem5421394 A f s)). Qed.
Lemma lem5421397 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term447 A f s x) = (term441 A x f s).
Proof. exact (eq_refl (term447 A f s x)). Qed.
Lemma lem5421398 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term448 A f s) = (term442 A f s).
Proof. exact (fun_ext (fun x : A => @lem5421397 A x f s)). Qed.
Lemma lem5421399 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5421400 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term449 A f s) = (term443 A f s).
Proof. exact (MK_COMB (@lem5421399 A) (@lem5421398 A f s)). Qed.
Lemma lem5421401 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term445 A f s) = (term444 A f s).
Proof. exact (MK_COMB (@lem5421396 A f s) (@lem5421400 A f s)). Qed.
Lemma lem5421402 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5421403 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term450 A f s) = (term451 A f s).
Proof. exact (MK_COMB (@lem5421402) (@lem5421401 A f s)). Qed.
Lemma lem5421404 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term409 A f s x) = (term384 A x f s).
Proof. exact (eq_refl (term409 A f s x)). Qed.
Lemma lem5421405 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5421406 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term410 A f s x) = (term386 A x f s).
Proof. exact (MK_COMB (@lem5421405) (@lem5421404 A x f s)). Qed.
Lemma lem5421407 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term447 A f s x) = (term441 A x f s).
Proof. exact (eq_refl (term447 A f s x)). Qed.
Lemma lem5421408 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term452 A f s x) = (term453 A x f s).
Proof. exact (MK_COMB (@lem5421406 A x f s) (@lem5421407 A x f s)). Qed.
Lemma lem5421409 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term454 A f s) = (term455 A f s).
Proof. exact (fun_ext (fun x : A => @lem5421408 A x f s)). Qed.
Lemma lem5421410 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5421411 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term446 A f s) = (term456 A f s).
Proof. exact (MK_COMB (@lem5421410 A) (@lem5421409 A f s)). Qed.
Lemma lem5421412 {A : Type'} (f : nat -> A) (s : A -> Prop) : ((term445 A f s) = (term446 A f s)) = ((term444 A f s) = (term456 A f s)).
Proof. exact (MK_COMB (@lem5421403 A f s) (@lem5421411 A f s)). Qed.
Lemma lem5421413 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term444 A f s) = (term456 A f s).
Proof. exact (EQ_MP (@lem5421412 A f s) (@lem5421390 A f s)). Qed.
Lemma lem5421415 {A : Type'} (P : Prop) (Q : A -> Prop) : (term457 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5421416 (P : Prop) (Q : nat -> Prop) : (term459 P Q) = (term460 P Q).
Proof. exact (@lem5421415 nat P Q). Qed.
Lemma lem5421417 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term461 A x f s) = (term462 A x f s).
Proof. exact (@lem5421416 (term384 A x f s) (term440 A x f s)). Qed.
Lemma lem5421418 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) (x' : nat) : (term463 A x f s x') = (term438 A x f s x').
Proof. exact (eq_refl (term463 A x f s x')). Qed.
Lemma lem5421419 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term464 A x f s) = (term440 A x f s).
Proof. exact (fun_ext (fun x' : nat => @lem5421418 A x f s x')). Qed.
Lemma lem5421420 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5421421 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term465 A x f s) = (term441 A x f s).
Proof. exact (MK_COMB (@lem5421420) (@lem5421419 A x f s)). Qed.
Lemma lem5421422 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term386 A x f s) = (term386 A x f s).
Proof. exact (eq_refl (term386 A x f s)). Qed.
Lemma lem5421423 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term461 A x f s) = (term453 A x f s).
Proof. exact (MK_COMB (@lem5421422 A x f s) (@lem5421421 A x f s)). Qed.
Lemma lem5421424 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5421425 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term466 A x f s) = (term467 A x f s).
Proof. exact (MK_COMB (@lem5421424) (@lem5421423 A x f s)). Qed.
Lemma lem5421426 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) (x' : nat) : (term463 A x f s x') = (term438 A x f s x').
Proof. exact (eq_refl (term463 A x f s x')). Qed.
Lemma lem5421427 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term386 A x f s) = (term386 A x f s).
Proof. exact (eq_refl (term386 A x f s)). Qed.
Lemma lem5421428 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) (x' : nat) : (term468 A x f s x') = (term469 A x f s x').
Proof. exact (MK_COMB (@lem5421427 A x f s) (@lem5421426 A x f s x')). Qed.
Lemma lem5421429 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term470 A x f s) = (term471 A x f s).
Proof. exact (fun_ext (fun x' : nat => @lem5421428 A x f s x')). Qed.
Lemma lem5421430 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5421431 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term462 A x f s) = (term472 A x f s).
Proof. exact (MK_COMB (@lem5421430) (@lem5421429 A x f s)). Qed.
Lemma lem5421432 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : ((term461 A x f s) = (term462 A x f s)) = ((term453 A x f s) = (term472 A x f s)).
Proof. exact (MK_COMB (@lem5421425 A x f s) (@lem5421431 A x f s)). Qed.
Lemma lem5421433 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term453 A x f s) = (term472 A x f s).
Proof. exact (EQ_MP (@lem5421432 A x f s) (@lem5421417 A x f s)). Qed.
Lemma lem5421434 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term455 A f s) = (term473 A f s).
Proof. exact (fun_ext (fun x : A => @lem5421433 A x f s)). Qed.
Lemma lem5421435 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5421436 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term456 A f s) = (term474 A f s).
Proof. exact (MK_COMB (@lem5421435 A) (@lem5421434 A f s)). Qed.
Lemma lem5421437 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term444 A f s) = (term474 A f s).
Proof. exact (TRANS (@lem5421413 A f s) (@lem5421436 A f s)). Qed.
Lemma lem5421438 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term424 A f s) = (term474 A f s).
Proof. exact (TRANS (@lem5421386 A f s) (@lem5421437 A f s)). Qed.
Lemma lem5421439 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term400 A s f) = (term400 A s f).
Proof. exact (eq_refl (term400 A s f)). Qed.
Lemma lem5421440 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term425 A f s) = (term475 A f s).
Proof. exact (MK_COMB (@lem5421439 A s f) (@lem5421438 A f s)). Qed.
Lemma lem5421444 {A : Type'} (P : A -> Prop) (Q : Prop) : (term476 A P Q) = (term477 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5421445 (P : nat -> Prop) (Q : Prop) : (term478 P Q) = (term479 P Q).
Proof. exact (@lem5421444 nat P Q). Qed.
Lemma lem5421446 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term480 A f s) = (term481 A f s).
Proof. exact (@lem5421445 (term367 A s f) (term474 A f s)). Qed.
Lemma lem5421447 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) : (term482 A s f i) = (term361 A s f i).
Proof. exact (eq_refl (term482 A s f i)). Qed.
Lemma lem5421448 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term483 A s f) = (term367 A s f).
Proof. exact (fun_ext (fun i : nat => @lem5421447 A s f i)). Qed.
Lemma lem5421449 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5421450 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term484 A s f) = (term368 A s f).
Proof. exact (MK_COMB (@lem5421449) (@lem5421448 A s f)). Qed.
Lemma lem5421451 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5421452 {A : Type'} (s : A -> Prop) (f : nat -> A) : (term485 A s f) = (term400 A s f).
Proof. exact (MK_COMB (@lem5421451) (@lem5421450 A s f)). Qed.
Lemma lem5421453 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term474 A f s) = (term474 A f s).
Proof. exact (eq_refl (term474 A f s)). Qed.
Lemma lem5421454 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term480 A f s) = (term475 A f s).
Proof. exact (MK_COMB (@lem5421452 A s f) (@lem5421453 A f s)). Qed.
Lemma lem5421455 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5421456 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term486 A f s) = (term487 A f s).
Proof. exact (MK_COMB (@lem5421455) (@lem5421454 A f s)). Qed.
Lemma lem5421457 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) : (term482 A s f i) = (term361 A s f i).
Proof. exact (eq_refl (term482 A s f i)). Qed.
Lemma lem5421458 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5421459 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) : (term488 A s f i) = (term489 A s f i).
Proof. exact (MK_COMB (@lem5421458) (@lem5421457 A s f i)). Qed.
Lemma lem5421460 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term474 A f s) = (term474 A f s).
Proof. exact (eq_refl (term474 A f s)). Qed.
Lemma lem5421461 {A : Type'} (i : nat) (f : nat -> A) (s : A -> Prop) : (term490 A i f s) = (term491 A i f s).
Proof. exact (MK_COMB (@lem5421459 A s f i) (@lem5421460 A f s)). Qed.
Lemma lem5421462 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term492 A f s) = (term493 A f s).
Proof. exact (fun_ext (fun i : nat => @lem5421461 A i f s)). Qed.
Lemma lem5421463 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5421464 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term481 A f s) = (term494 A f s).
Proof. exact (MK_COMB (@lem5421463) (@lem5421462 A f s)). Qed.
Lemma lem5421465 {A : Type'} (f : nat -> A) (s : A -> Prop) : ((term480 A f s) = (term481 A f s)) = ((term475 A f s) = (term494 A f s)).
Proof. exact (MK_COMB (@lem5421456 A f s) (@lem5421464 A f s)). Qed.
Lemma lem5421466 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term475 A f s) = (term494 A f s).
Proof. exact (EQ_MP (@lem5421465 A f s) (@lem5421446 A f s)). Qed.
Lemma lem5421470 {A : Type'} (P : A -> Prop) (Q : Prop) : (term476 A P Q) = (term477 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5421471 (P : nat -> Prop) (Q : Prop) : (term478 P Q) = (term479 P Q).
Proof. exact (@lem5421470 nat P Q). Qed.
Lemma lem5421472 {A : Type'} (i : nat) (f : nat -> A) (s : A -> Prop) : (term495 A i f s) = (term496 A i f s).
Proof. exact (@lem5421471 (term360 A s f i) (term474 A f s)). Qed.
Lemma lem5421473 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) : (term497 A s f i j) = (term352 A s f i j).
Proof. exact (eq_refl (term497 A s f i j)). Qed.
Lemma lem5421474 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) : (term498 A s f i) = (term360 A s f i).
Proof. exact (fun_ext (fun j : nat => @lem5421473 A s f i j)). Qed.
Lemma lem5421475 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5421476 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) : (term499 A s f i) = (term361 A s f i).
Proof. exact (MK_COMB (@lem5421475) (@lem5421474 A s f i)). Qed.
Lemma lem5421477 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5421478 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) : (term500 A s f i) = (term489 A s f i).
Proof. exact (MK_COMB (@lem5421477) (@lem5421476 A s f i)). Qed.
Lemma lem5421479 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term474 A f s) = (term474 A f s).
Proof. exact (eq_refl (term474 A f s)). Qed.
Lemma lem5421480 {A : Type'} (i : nat) (f : nat -> A) (s : A -> Prop) : (term495 A i f s) = (term491 A i f s).
Proof. exact (MK_COMB (@lem5421478 A s f i) (@lem5421479 A f s)). Qed.
Lemma lem5421481 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5421482 {A : Type'} (i : nat) (f : nat -> A) (s : A -> Prop) : (term501 A i f s) = (term502 A i f s).
Proof. exact (MK_COMB (@lem5421481) (@lem5421480 A i f s)). Qed.
Lemma lem5421483 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) : (term497 A s f i j) = (term352 A s f i j).
Proof. exact (eq_refl (term497 A s f i j)). Qed.
Lemma lem5421484 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5421485 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) : (term503 A s f i j) = (term504 A s f i j).
Proof. exact (MK_COMB (@lem5421484) (@lem5421483 A s f i j)). Qed.
Lemma lem5421486 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term474 A f s) = (term474 A f s).
Proof. exact (eq_refl (term474 A f s)). Qed.
Lemma lem5421487 {A : Type'} (i : nat) (j : nat) (f : nat -> A) (s : A -> Prop) : (term505 A i j f s) = (term506 A i j f s).
Proof. exact (MK_COMB (@lem5421485 A s f i j) (@lem5421486 A f s)). Qed.
Lemma lem5421488 {A : Type'} (i : nat) (f : nat -> A) (s : A -> Prop) : (term507 A i f s) = (term508 A i f s).
Proof. exact (fun_ext (fun j : nat => @lem5421487 A i j f s)). Qed.
Lemma lem5421489 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5421490 {A : Type'} (i : nat) (f : nat -> A) (s : A -> Prop) : (term496 A i f s) = (term509 A i f s).
Proof. exact (MK_COMB (@lem5421489) (@lem5421488 A i f s)). Qed.
Lemma lem5421491 {A : Type'} (i : nat) (f : nat -> A) (s : A -> Prop) : ((term495 A i f s) = (term496 A i f s)) = ((term491 A i f s) = (term509 A i f s)).
Proof. exact (MK_COMB (@lem5421482 A i f s) (@lem5421490 A i f s)). Qed.
Lemma lem5421492 {A : Type'} (i : nat) (f : nat -> A) (s : A -> Prop) : (term491 A i f s) = (term509 A i f s).
Proof. exact (EQ_MP (@lem5421491 A i f s) (@lem5421472 A i f s)). Qed.
Lemma lem5421494 {A : Type'} (P : Prop) (Q : A -> Prop) : (term457 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5421495 {A : Type'} (P : Prop) (Q : A -> Prop) : (term457 A P Q) = (term458 A P Q).
Proof. exact (@lem5421494 A P Q). Qed.
Lemma lem5421496 {A : Type'} (i : nat) (j : nat) (f : nat -> A) (s : A -> Prop) : (term510 A i j f s) = (term511 A i j f s).
Proof. exact (@lem5421495 A (term352 A s f i j) (term473 A f s)). Qed.
Lemma lem5421497 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term512 A f s x) = (term472 A x f s).
Proof. exact (eq_refl (term512 A f s x)). Qed.
Lemma lem5421498 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term513 A f s) = (term473 A f s).
Proof. exact (fun_ext (fun x : A => @lem5421497 A x f s)). Qed.
Lemma lem5421499 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5421500 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term514 A f s) = (term474 A f s).
Proof. exact (MK_COMB (@lem5421499 A) (@lem5421498 A f s)). Qed.
Lemma lem5421501 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) : (term504 A s f i j) = (term504 A s f i j).
Proof. exact (eq_refl (term504 A s f i j)). Qed.
Lemma lem5421502 {A : Type'} (i : nat) (j : nat) (f : nat -> A) (s : A -> Prop) : (term510 A i j f s) = (term506 A i j f s).
Proof. exact (MK_COMB (@lem5421501 A s f i j) (@lem5421500 A f s)). Qed.
Lemma lem5421503 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5421504 {A : Type'} (i : nat) (j : nat) (f : nat -> A) (s : A -> Prop) : (term515 A i j f s) = (term516 A i j f s).
Proof. exact (MK_COMB (@lem5421503) (@lem5421502 A i j f s)). Qed.
Lemma lem5421505 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term512 A f s x) = (term472 A x f s).
Proof. exact (eq_refl (term512 A f s x)). Qed.
Lemma lem5421506 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) : (term504 A s f i j) = (term504 A s f i j).
Proof. exact (eq_refl (term504 A s f i j)). Qed.
Lemma lem5421507 {A : Type'} (i : nat) (j : nat) (x : A) (f : nat -> A) (s : A -> Prop) : (term517 A i j f s x) = (term518 A i j x f s).
Proof. exact (MK_COMB (@lem5421506 A s f i j) (@lem5421505 A x f s)). Qed.
Lemma lem5421508 {A : Type'} (i : nat) (j : nat) (f : nat -> A) (s : A -> Prop) : (term519 A i j f s) = (term520 A i j f s).
Proof. exact (fun_ext (fun x : A => @lem5421507 A i j x f s)). Qed.
Lemma lem5421509 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5421510 {A : Type'} (i : nat) (j : nat) (f : nat -> A) (s : A -> Prop) : (term511 A i j f s) = (term521 A i j f s).
Proof. exact (MK_COMB (@lem5421509 A) (@lem5421508 A i j f s)). Qed.
Lemma lem5421511 {A : Type'} (i : nat) (j : nat) (f : nat -> A) (s : A -> Prop) : ((term510 A i j f s) = (term511 A i j f s)) = ((term506 A i j f s) = (term521 A i j f s)).
Proof. exact (MK_COMB (@lem5421504 A i j f s) (@lem5421510 A i j f s)). Qed.
Lemma lem5421512 {A : Type'} (i : nat) (j : nat) (f : nat -> A) (s : A -> Prop) : (term506 A i j f s) = (term521 A i j f s).
Proof. exact (EQ_MP (@lem5421511 A i j f s) (@lem5421496 A i j f s)). Qed.
Lemma lem5421514 {A : Type'} (P : Prop) (Q : A -> Prop) : (term457 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5421515 (P : Prop) (Q : nat -> Prop) : (term459 P Q) = (term460 P Q).
Proof. exact (@lem5421514 nat P Q). Qed.
Lemma lem5421516 {A : Type'} (i : nat) (j : nat) (x : A) (f : nat -> A) (s : A -> Prop) : (term522 A i j x f s) = (term523 A i j x f s).
Proof. exact (@lem5421515 (term352 A s f i j) (term471 A x f s)). Qed.
Lemma lem5421517 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) (x' : nat) : (term524 A x f s x') = (term469 A x f s x').
Proof. exact (eq_refl (term524 A x f s x')). Qed.
Lemma lem5421518 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term525 A x f s) = (term471 A x f s).
Proof. exact (fun_ext (fun x' : nat => @lem5421517 A x f s x')). Qed.
Lemma lem5421519 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5421520 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term526 A x f s) = (term472 A x f s).
Proof. exact (MK_COMB (@lem5421519) (@lem5421518 A x f s)). Qed.
Lemma lem5421521 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) : (term504 A s f i j) = (term504 A s f i j).
Proof. exact (eq_refl (term504 A s f i j)). Qed.
Lemma lem5421522 {A : Type'} (i : nat) (j : nat) (x : A) (f : nat -> A) (s : A -> Prop) : (term522 A i j x f s) = (term518 A i j x f s).
Proof. exact (MK_COMB (@lem5421521 A s f i j) (@lem5421520 A x f s)). Qed.
Lemma lem5421523 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5421524 {A : Type'} (i : nat) (j : nat) (x : A) (f : nat -> A) (s : A -> Prop) : (term527 A i j x f s) = (term528 A i j x f s).
Proof. exact (MK_COMB (@lem5421523) (@lem5421522 A i j x f s)). Qed.
Lemma lem5421525 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) (x' : nat) : (term524 A x f s x') = (term469 A x f s x').
Proof. exact (eq_refl (term524 A x f s x')). Qed.
Lemma lem5421526 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) : (term504 A s f i j) = (term504 A s f i j).
Proof. exact (eq_refl (term504 A s f i j)). Qed.
Lemma lem5421527 {A : Type'} (i : nat) (j : nat) (x : A) (f : nat -> A) (s : A -> Prop) (x' : nat) : (term529 A i j x f s x') = (term530 A i j x f s x').
Proof. exact (MK_COMB (@lem5421526 A s f i j) (@lem5421525 A x f s x')). Qed.
Lemma lem5421528 {A : Type'} (i : nat) (j : nat) (x : A) (f : nat -> A) (s : A -> Prop) : (term531 A i j x f s) = (term532 A i j x f s).
Proof. exact (fun_ext (fun x' : nat => @lem5421527 A i j x f s x')). Qed.
Lemma lem5421529 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5421530 {A : Type'} (i : nat) (j : nat) (x : A) (f : nat -> A) (s : A -> Prop) : (term523 A i j x f s) = (term533 A i j x f s).
Proof. exact (MK_COMB (@lem5421529) (@lem5421528 A i j x f s)). Qed.
Lemma lem5421531 {A : Type'} (i : nat) (j : nat) (x : A) (f : nat -> A) (s : A -> Prop) : ((term522 A i j x f s) = (term523 A i j x f s)) = ((term518 A i j x f s) = (term533 A i j x f s)).
Proof. exact (MK_COMB (@lem5421524 A i j x f s) (@lem5421530 A i j x f s)). Qed.
Lemma lem5421532 {A : Type'} (i : nat) (j : nat) (x : A) (f : nat -> A) (s : A -> Prop) : (term518 A i j x f s) = (term533 A i j x f s).
Proof. exact (EQ_MP (@lem5421531 A i j x f s) (@lem5421516 A i j x f s)). Qed.
Lemma lem5421533 {A : Type'} (i : nat) (j : nat) (f : nat -> A) (s : A -> Prop) : (term520 A i j f s) = (term534 A i j f s).
Proof. exact (fun_ext (fun x : A => @lem5421532 A i j x f s)). Qed.
Lemma lem5421534 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5421535 {A : Type'} (i : nat) (j : nat) (f : nat -> A) (s : A -> Prop) : (term521 A i j f s) = (term535 A i j f s).
Proof. exact (MK_COMB (@lem5421534 A) (@lem5421533 A i j f s)). Qed.
Lemma lem5421536 {A : Type'} (i : nat) (j : nat) (f : nat -> A) (s : A -> Prop) : (term506 A i j f s) = (term535 A i j f s).
Proof. exact (TRANS (@lem5421512 A i j f s) (@lem5421535 A i j f s)). Qed.
Lemma lem5421537 {A : Type'} (i : nat) (f : nat -> A) (s : A -> Prop) : (term508 A i f s) = (term536 A i f s).
Proof. exact (fun_ext (fun j : nat => @lem5421536 A i j f s)). Qed.
Lemma lem5421538 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5421539 {A : Type'} (i : nat) (f : nat -> A) (s : A -> Prop) : (term509 A i f s) = (term537 A i f s).
Proof. exact (MK_COMB (@lem5421538) (@lem5421537 A i f s)). Qed.
Lemma lem5421540 {A : Type'} (i : nat) (f : nat -> A) (s : A -> Prop) : (term491 A i f s) = (term537 A i f s).
Proof. exact (TRANS (@lem5421492 A i f s) (@lem5421539 A i f s)). Qed.
Lemma lem5421541 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term493 A f s) = (term538 A f s).
Proof. exact (fun_ext (fun i : nat => @lem5421540 A i f s)). Qed.
Lemma lem5421542 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5421543 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term494 A f s) = (term539 A f s).
Proof. exact (MK_COMB (@lem5421542) (@lem5421541 A f s)). Qed.
Lemma lem5421544 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term475 A f s) = (term539 A f s).
Proof. exact (TRANS (@lem5421466 A f s) (@lem5421543 A f s)). Qed.
Lemma lem5421545 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term425 A f s) = (term539 A f s).
Proof. exact (TRANS (@lem5421440 A f s) (@lem5421544 A f s)). Qed.
Lemma lem5421546 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term402 A f s) = (term539 A f s).
Proof. exact (TRANS (@lem5421361 A f s) (@lem5421545 A f s)). Qed.
Lemma lem5421547 {A : Type'} (f : nat -> A) (s : A -> Prop) : (term340 A f s) = (term539 A f s).
Proof. exact (TRANS (@lem5421108 A f s) (@lem5421546 A f s)). Qed.
Lemma lem5421548 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term340 A f s) : term539 A f s.
Proof. exact (EQ_MP (@lem5421547 A f s) (@lem5420837 A f s h1)). Qed.
Lemma lem5421549 {A : Type'} (i : nat) (f : nat -> A) (s : A -> Prop) (h1 : term537 A i f s) : term537 A i f s.
Proof. exact (h1). Qed.
Lemma lem5421550 {A : Type'} (i : nat) (j : nat) (f : nat -> A) (s : A -> Prop) (h1 : term535 A i j f s) : term535 A i j f s.
Proof. exact (h1). Qed.
Lemma lem5421551 {A : Type'} (i : nat) (j : nat) (x : A) (f : nat -> A) (s : A -> Prop) (h1 : term533 A i j x f s) : term533 A i j x f s.
Proof. exact (h1). Qed.
Lemma lem5421552 {A : Type'} (i : nat) (j : nat) (x : A) (f : nat -> A) (s : A -> Prop) (x' : nat) (h1 : term530 A i j x f s x') : term530 A i j x f s x'.
Proof. exact (h1). Qed.
Lemma lem5421553 {A : Type'} (s : A -> Prop) (f : nat -> A) (g : A -> nat) (h1 : term348 A s f g) : term348 A s f g.
Proof. exact (h1). Qed.
Lemma lem5421576 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) (x' : nat) : (term318 A x f s x') = (term318 A x f s x').
Proof. exact (eq_refl (term318 A x f s x')). Qed.
Lemma lem5421577 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5421582 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5421583 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem5421582 A Prop f x). Qed.
Lemma lem5421585 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem5421583 A s x). Qed.
Lemma lem5421586 {A : Type'} (s : A -> Prop) (x : A) : (term432 A s x) = (term540 A s x).
Proof. exact (MK_COMB (@lem5421577) (@lem5421585 A s x)). Qed.
Lemma lem5421587 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5421588 {A : Type'} (s : A -> Prop) (x : A) : (term380 A s x) = (term541 A s x).
Proof. exact (MK_COMB (@lem5421587) (@lem5421586 A s x)). Qed.
Lemma lem5421589 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) (x' : nat) : (term438 A x f s x') = (term542 A x f s x').
Proof. exact (MK_COMB (@lem5421588 A s x) (@lem5421576 A x f s x')). Qed.
Lemma lem5421616 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) (x' : nat) : (term370 A x f s x') = (term370 A x f s x').
Proof. exact (eq_refl (term370 A x f s x')). Qed.
Lemma lem5421617 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term378 A x f s) = (term378 A x f s).
Proof. exact (fun_ext (fun x' : nat => @lem5421616 A x f s x')). Qed.
Lemma lem5421618 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5421619 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term379 A x f s) = (term379 A x f s).
Proof. exact (MK_COMB (@lem5421618) (@lem5421617 A x f s)). Qed.
Lemma lem5421624 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5421625 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem5421624 A Prop f x). Qed.
Lemma lem5421627 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem5421625 A s x). Qed.
Lemma lem5421628 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5421629 {A : Type'} (s : A -> Prop) (x : A) : (term382 A s x) = (term543 A s x).
Proof. exact (MK_COMB (@lem5421628) (@lem5421627 A s x)). Qed.
Lemma lem5421630 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term384 A x f s) = (term544 A x f s).
Proof. exact (MK_COMB (@lem5421629 A s x) (@lem5421619 A x f s)). Qed.
Lemma lem5421631 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5421632 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term386 A x f s) = (term545 A x f s).
Proof. exact (MK_COMB (@lem5421631) (@lem5421630 A x f s)). Qed.
Lemma lem5421633 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) (x' : nat) : (term469 A x f s x') = (term546 A x f s x').
Proof. exact (MK_COMB (@lem5421632 A x f s) (@lem5421589 A x f s x')). Qed.
Lemma lem5421686 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) : (term504 A s f i j) = (term504 A s f i j).
Proof. exact (eq_refl (term504 A s f i j)). Qed.
Lemma lem5421687 {A : Type'} (i : nat) (j : nat) (x : A) (f : nat -> A) (s : A -> Prop) (x' : nat) : (term530 A i j x f s x') = (term547 A i j x f s x').
Proof. exact (MK_COMB (@lem5421686 A s f i j) (@lem5421633 A x f s x')). Qed.
Lemma lem5421688 {A : Type'} (i : nat) (j : nat) (x : A) (f : nat -> A) (s : A -> Prop) (x' : nat) (h1 : term530 A i j x f s x') : term547 A i j x f s x'.
Proof. exact (EQ_MP (@lem5421687 A i j x f s x') (@lem5421552 A i j x f s x' h1)). Qed.
Lemma lem5421715 {A : Type'} (s : A -> Prop) (f : nat -> A) (g : A -> nat) (y : A) : (term283 A s f g y) = (term283 A s f g y).
Proof. exact (eq_refl (term283 A s f g y)). Qed.
Lemma lem5421716 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5421721 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5421722 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem5421721 A Prop f x). Qed.
Lemma lem5421724 {A : Type'} (s : A -> Prop) (y : A) : (s y) = (@I (A -> Prop) s y).
Proof. exact (@lem5421722 A s y). Qed.
Lemma lem5421725 {A : Type'} (s : A -> Prop) (y : A) : (term432 A s y) = (term540 A s y).
Proof. exact (MK_COMB (@lem5421716) (@lem5421724 A s y)). Qed.
Lemma lem5421726 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5421727 {A : Type'} (s : A -> Prop) (y : A) : (term548 A s y) = (term549 A s y).
Proof. exact (MK_COMB (@lem5421726) (@lem5421725 A s y)). Qed.
Lemma lem5421728 {A : Type'} (s : A -> Prop) (f : nat -> A) (g : A -> nat) (y : A) : (term344 A s f g y) = (term550 A s f g y).
Proof. exact (MK_COMB (@lem5421727 A s y) (@lem5421715 A s f g y)). Qed.
Lemma lem5421729 {A : Type'} (s : A -> Prop) (f : nat -> A) (g : A -> nat) : (term345 A s f g) = (term551 A s f g).
Proof. exact (fun_ext (fun y : A => @lem5421728 A s f g y)). Qed.
Lemma lem5421730 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5421731 {A : Type'} (s : A -> Prop) (f : nat -> A) (g : A -> nat) : (term346 A s f g) = (term552 A s f g).
Proof. exact (MK_COMB (@lem5421730 A) (@lem5421729 A s f g)). Qed.
Lemma lem5421740 {A : Type'} (g : A -> nat) (f : nat -> A) (x : nat) : ((term264 A g f x) = x) = ((term264 A g f x) = x).
Proof. exact (eq_refl ((term264 A g f x) = x)). Qed.
Lemma lem5421747 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5421748 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem5421747 A Prop f x). Qed.
Lemma lem5421750 {A : Type'} (s : A -> Prop) (f : nat -> A) (x : nat) : (term261 A s f x) = (term553 A s f x).
Proof. exact (@lem5421748 A s (f x)). Qed.
Lemma lem5421751 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5421752 {A : Type'} (s : A -> Prop) (f : nat -> A) (x : nat) : (term263 A s f x) = (term554 A s f x).
Proof. exact (MK_COMB (@lem5421751) (@lem5421750 A s f x)). Qed.
Lemma lem5421753 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : nat -> A) (x : nat) : (term266 A s g f x) = (term555 A s g f x).
Proof. exact (MK_COMB (@lem5421752 A s f x) (@lem5421740 A g f x)). Qed.
Lemma lem5421770 {A : Type'} (s : A -> Prop) (x : nat) : (term556 A s x) = (term556 A s x).
Proof. exact (eq_refl (term556 A s x)). Qed.
Lemma lem5421771 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : nat -> A) (x : nat) : (term341 A s g f x) = (term557 A s g f x).
Proof. exact (MK_COMB (@lem5421770 A s x) (@lem5421753 A s g f x)). Qed.
Lemma lem5421772 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : nat -> A) : (term342 A s g f) = (term558 A s g f).
Proof. exact (fun_ext (fun x : nat => @lem5421771 A s g f x)). Qed.
Lemma lem5421773 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5421774 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : nat -> A) : (term343 A s g f) = (term559 A s g f).
Proof. exact (MK_COMB (@lem5421773) (@lem5421772 A s g f)). Qed.
Lemma lem5421775 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5421776 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : nat -> A) : (term347 A s g f) = (term560 A s g f).
Proof. exact (MK_COMB (@lem5421775) (@lem5421774 A s g f)). Qed.
Lemma lem5421777 {A : Type'} (s : A -> Prop) (f : nat -> A) (g : A -> nat) : (term348 A s f g) = (term561 A s f g).
Proof. exact (MK_COMB (@lem5421776 A s g f) (@lem5421731 A s f g)). Qed.
Lemma lem5421778 {A : Type'} (s : A -> Prop) (f : nat -> A) (g : A -> nat) (h1 : term348 A s f g) : term561 A s f g.
Proof. exact (EQ_MP (@lem5421777 A s f g) (@lem5421553 A s f g h1)). Qed.
Lemma lem5421779 {A : Type'} (s : A -> Prop) (f : nat -> A) (g : A -> nat) (h1 : term348 A s f g) : term552 A s f g.
Proof. exact (proj2 (@lem5421778 A s f g h1)). Qed.
Lemma lem5421780 {A : Type'} (s : A -> Prop) (f : nat -> A) (g : A -> nat) (h1 : term348 A s f g) : term559 A s g f.
Proof. exact (proj1 (@lem5421778 A s f g h1)). Qed.
Lemma lem5421781 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) (h1 : term352 A s f i j) : term352 A s f i j.
Proof. exact (h1). Qed.
Lemma lem5421782 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) (x' : nat) (h1 : term546 A x f s x') : term546 A x f s x'.
Proof. exact (h1). Qed.
Lemma lem5421784 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) (h1 : term352 A s f i j) : term299 A s i f j.
Proof. exact (proj1 (@lem5421781 A s f i j h1)). Qed.
Lemma lem5421785 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) (h1 : term352 A s f i j) : term298 A s i f j.
Proof. exact (proj2 (@lem5421784 A s f i j h1)). Qed.
Lemma lem5421789 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) (h1 : term544 A x f s) : term544 A x f s.
Proof. exact (h1). Qed.
Lemma lem5421790 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) (x' : nat) (h1 : term542 A x f s x') : term542 A x f s x'.
Proof. exact (h1). Qed.
Lemma lem5421791 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) (h1 : term544 A x f s) : term379 A x f s.
Proof. exact (proj2 (@lem5421789 A x f s h1)). Qed.
Lemma lem5421793 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) (x' : nat) (h1 : term542 A x f s x') : term318 A x f s x'.
Proof. exact (proj2 (@lem5421790 A x f s x' h1)). Qed.
Lemma lem5421814 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : nat -> A) (x : nat) : (term557 A s g f x) = (term562 A s g f x).
Proof. exact (@lem19490 (term553 A s f x) (term563 A s x) ((term264 A g f x) = x)). Qed.
Lemma lem5421815 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : nat -> A) : (term558 A s g f) = (term564 A s g f).
Proof. exact (fun_ext (fun x : nat => @lem5421814 A s g f x)). Qed.
Lemma lem5421816 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5421818 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : nat -> A) : (term559 A s g f) = (term565 A s g f).
Proof. exact (MK_COMB (@lem5421816) (@lem5421815 A s g f)). Qed.
Lemma lem5421819 {A : Type'} (s : A -> Prop) (f : nat -> A) (g : A -> nat) (h1 : term348 A s f g) : term565 A s g f.
Proof. exact (EQ_MP (@lem5421818 A s g f) (@lem5421780 A s f g h1)). Qed.
Lemma lem5421899 {A : Type'} (s : A -> Prop) (f : nat -> A) (g : A -> nat) (y : A) : (term550 A s f g y) = (term566 A s f g y).
Proof. exact (@lem19490 (term278 A s g y) (term540 A s y) ((term281 A f g y) = y)). Qed.
Lemma lem5421900 {A : Type'} (s : A -> Prop) (f : nat -> A) (g : A -> nat) : (term551 A s f g) = (term567 A s f g).
Proof. exact (fun_ext (fun y : A => @lem5421899 A s f g y)). Qed.
Lemma lem5421901 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5421903 {A : Type'} (s : A -> Prop) (f : nat -> A) (g : A -> nat) : (term552 A s f g) = (term568 A s f g).
Proof. exact (MK_COMB (@lem5421901 A) (@lem5421900 A s f g)). Qed.
Lemma lem5421904 {A : Type'} (s : A -> Prop) (f : nat -> A) (g : A -> nat) (h1 : term348 A s f g) : term568 A s f g.
Proof. exact (EQ_MP (@lem5421903 A s f g) (@lem5421779 A s f g h1)). Qed.
Lemma lem5421916 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) (x' : nat) : (term370 A x f s x') = (term370 A x f s x').
Proof. exact (eq_refl (term370 A x f s x')). Qed.
Lemma lem5421917 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term378 A x f s) = (term378 A x f s).
Proof. exact (fun_ext (fun x' : nat => @lem5421916 A x f s x')). Qed.
Lemma lem5421918 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5421920 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) : (term379 A x f s) = (term379 A x f s).
Proof. exact (MK_COMB (@lem5421918) (@lem5421917 A x f s)). Qed.
Lemma lem5421921 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) (h1 : term544 A x f s) : term379 A x f s.
Proof. exact (EQ_MP (@lem5421920 A x f s) (@lem5421791 A x f s h1)). Qed.
Lemma lem5421939 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : nat -> A) (x : nat) : (term557 A s g f x) = (term562 A s g f x).
Proof. exact (@lem19490 (term553 A s f x) (term563 A s x) ((term264 A g f x) = x)). Qed.
Lemma lem5421940 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : nat -> A) : (term558 A s g f) = (term564 A s g f).
Proof. exact (fun_ext (fun x : nat => @lem5421939 A s g f x)). Qed.
Lemma lem5421941 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5421943 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : nat -> A) : (term559 A s g f) = (term565 A s g f).
Proof. exact (MK_COMB (@lem5421941) (@lem5421940 A s g f)). Qed.
Lemma lem5421944 {A : Type'} (s : A -> Prop) (f : nat -> A) (g : A -> nat) (h1 : term348 A s f g) : term565 A s g f.
Proof. exact (EQ_MP (@lem5421943 A s g f) (@lem5421780 A s f g h1)). Qed.
Lemma lem5421980 {A : Type'} (_69961 : nat) (s : A -> Prop) (f : nat -> A) (g : A -> nat) (h1 : term348 A s f g) : term569 A s g f _69961.
Proof. exact (@lem5421819 A s f g h1 _69961). Qed.
Lemma lem5421981 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : nat -> A) (_69961 : nat) : (term569 A s g f _69961) = (term562 A s g f _69961).
Proof. exact (eq_refl (term569 A s g f _69961)). Qed.
Lemma lem5421982 {A : Type'} (_69961 : nat) (s : A -> Prop) (f : nat -> A) (g : A -> nat) (h1 : term348 A s f g) : term562 A s g f _69961.
Proof. exact (EQ_MP (@lem5421981 A s g f _69961) (@lem5421980 A _69961 s f g h1)). Qed.
Lemma lem5421989 {A : Type'} (_69964 : A) (s : A -> Prop) (f : nat -> A) (g : A -> nat) (h1 : term348 A s f g) : term570 A s f g _69964.
Proof. exact (@lem5421904 A s f g h1 _69964). Qed.
Lemma lem5421990 {A : Type'} (s : A -> Prop) (f : nat -> A) (g : A -> nat) (_69964 : A) : (term570 A s f g _69964) = (term566 A s f g _69964).
Proof. exact (eq_refl (term570 A s f g _69964)). Qed.
Lemma lem5421991 {A : Type'} (_69964 : A) (s : A -> Prop) (f : nat -> A) (g : A -> nat) (h1 : term348 A s f g) : term566 A s f g _69964.
Proof. exact (EQ_MP (@lem5421990 A s f g _69964) (@lem5421989 A _69964 s f g h1)). Qed.
Lemma lem5421992 {A : Type'} (_69965 : nat) (x : A) (f : nat -> A) (s : A -> Prop) (h1 : term544 A x f s) : term571 A x f s _69965.
Proof. exact (@lem5421921 A x f s h1 _69965). Qed.
Lemma lem5421993 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) (_69965 : nat) : (term571 A x f s _69965) = (term370 A x f s _69965).
Proof. exact (eq_refl (term571 A x f s _69965)). Qed.
Lemma lem5421995 {A : Type'} (_69966 : nat) (s : A -> Prop) (f : nat -> A) (g : A -> nat) (h1 : term348 A s f g) : term569 A s g f _69966.
Proof. exact (@lem5421944 A s f g h1 _69966). Qed.
Lemma lem5421996 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : nat -> A) (_69966 : nat) : (term569 A s g f _69966) = (term562 A s g f _69966).
Proof. exact (eq_refl (term569 A s g f _69966)). Qed.
Lemma lem5421997 {A : Type'} (_69966 : nat) (s : A -> Prop) (f : nat -> A) (g : A -> nat) (h1 : term348 A s f g) : term562 A s g f _69966.
Proof. exact (EQ_MP (@lem5421996 A s g f _69966) (@lem5421995 A _69966 s f g h1)). Qed.
Lemma lem5422014 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) (h1 : term352 A s f i j) : term572 i j.
Proof. exact (proj2 (@lem5421781 A s f i j h1)). Qed.
Lemma lem5422044 {A : Type'} (_69961 : nat) (s : A -> Prop) (f : nat -> A) (g : A -> nat) (h1 : term348 A s f g) : term573 A s g f _69961.
Proof. exact (proj2 (@lem5421982 A _69961 s f g h1)). Qed.
Lemma lem5422052 {A : Type'} (_69965 : nat) (x : A) (f : nat -> A) (s : A -> Prop) (h1 : term544 A x f s) : term370 A x f s _69965.
Proof. exact (EQ_MP (@lem5421993 A x f s _69965) (@lem5421992 A _69965 x f s h1)). Qed.
Lemma lem5422058 {A : Type'} (_69964 : A) (s : A -> Prop) (f : nat -> A) (g : A -> nat) (h1 : term348 A s f g) : term574 A s g _69964.
Proof. exact (proj1 (@lem5421991 A _69964 s f g h1)). Qed.
Lemma lem5422064 {A : Type'} (_69964 : A) (s : A -> Prop) (f : nat -> A) (g : A -> nat) (h1 : term348 A s f g) : term575 A s f g _69964.
Proof. exact (proj2 (@lem5421991 A _69964 s f g h1)). Qed.
Lemma lem5422078 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) (x' : nat) (h1 : term542 A x f s x') : term540 A s x.
Proof. exact (proj1 (@lem5421790 A x f s x' h1)). Qed.
Lemma lem5422080 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) (x' : nat) (h1 : term542 A x f s x') : x = (f x').
Proof. exact (proj1 (@lem5421793 A x f s x' h1)). Qed.
Lemma lem5422121 {A : Type'} (s : A -> Prop) : (term576 A s) = (term576 A s).
Proof. exact (eq_refl (term576 A s)). Qed.
Lemma lem5422122 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) (x' : nat) (h1 : term542 A x f s x') : (term577 A s x) = (term578 A s f x').
Proof. exact (MK_COMB (@lem5422121 A s) (@lem5422080 A x f s x' h1)). Qed.
Lemma lem5422123 {A : Type'} (s : A -> Prop) (f : nat -> A) (x' : nat) : (term578 A s f x') = (term579 A s f x').
Proof. exact (eq_refl (term578 A s f x')). Qed.
Lemma lem5422124 {A : Type'} (s : A -> Prop) (x : A) : (term580 A s x) = (term580 A s x).
Proof. exact (eq_refl (term580 A s x)). Qed.
Lemma lem5422125 {A : Type'} (x : A) (s : A -> Prop) (f : nat -> A) (x' : nat) : ((term577 A s x) = (term578 A s f x')) = ((term577 A s x) = (term579 A s f x')).
Proof. exact (MK_COMB (@lem5422124 A s x) (@lem5422123 A s f x')). Qed.
Lemma lem5422126 {A : Type'} (s : A -> Prop) (x : A) : (term577 A s x) = (term540 A s x).
Proof. exact (eq_refl (term577 A s x)). Qed.
Lemma lem5422127 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5422128 {A : Type'} (s : A -> Prop) (x : A) : (term580 A s x) = (term581 A s x).
Proof. exact (MK_COMB (@lem5422127) (@lem5422126 A s x)). Qed.
Lemma lem5422129 {A : Type'} (s : A -> Prop) (f : nat -> A) (x' : nat) : (term579 A s f x') = (term579 A s f x').
Proof. exact (eq_refl (term579 A s f x')). Qed.
Lemma lem5422130 {A : Type'} (x : A) (s : A -> Prop) (f : nat -> A) (x' : nat) : ((term577 A s x) = (term579 A s f x')) = ((term540 A s x) = (term579 A s f x')).
Proof. exact (MK_COMB (@lem5422128 A s x) (@lem5422129 A s f x')). Qed.
Lemma lem5422131 {A : Type'} (x : A) (s : A -> Prop) (f : nat -> A) (x' : nat) : ((term577 A s x) = (term578 A s f x')) = ((term540 A s x) = (term579 A s f x')).
Proof. exact (TRANS (@lem5422125 A x s f x') (@lem5422130 A x s f x')). Qed.
Lemma lem5422132 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) (x' : nat) (h1 : term542 A x f s x') : (term540 A s x) = (term579 A s f x').
Proof. exact (EQ_MP (@lem5422131 A x s f x') (@lem5422122 A x f s x' h1)). Qed.
Lemma lem5422133 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) (x' : nat) (h1 : term542 A x f s x') : term579 A s f x'.
Proof. exact (EQ_MP (@lem5422132 A x f s x' h1) (@lem5422078 A x f s x' h1)). Qed.
Lemma lem5422189 {A : Type'} (_69966 : nat) (s : A -> Prop) (f : nat -> A) (g : A -> nat) (h1 : term348 A s f g) : term582 A s f _69966.
Proof. exact (proj1 (@lem5421997 A _69966 s f g h1)). Qed.
Lemma lem5422249 {A : Type'} (g : A -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem5422250 {A : Type'} (_69992 : A) (_69993 : A) (h1 : _69992 = _69993) : _69992 = _69993.
Proof. exact (h1). Qed.
Lemma lem5422251 {A : Type'} (g : A -> nat) (_69992 : A) (_69993 : A) (h1 : _69992 = _69993) : (g _69992) = (g _69993).
Proof. exact (MK_COMB (@lem5422249 A g) (@lem5422250 A _69992 _69993 h1)). Qed.
Lemma lem5422252 {A : Type'} (_69992 : A) (g : A -> nat) (_69993 : A) : term583 A _69992 g _69993.
Proof. exact (fun h0 : _69992 = _69993 => @lem5422251 A g _69992 _69993 h0). Qed.
Lemma lem5422254 (a : Prop) (b : Prop) : (a -> b) = (term142 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5422255 {A : Type'} (_69992 : A) (g : A -> nat) (_69993 : A) : (term583 A _69992 g _69993) = (term584 A _69992 g _69993).
Proof. exact (@lem5422254 (_69992 = _69993) ((g _69992) = (g _69993))). Qed.
Lemma lem5422256 {A : Type'} (_69992 : A) (g : A -> nat) (_69993 : A) : term584 A _69992 g _69993.
Proof. exact (EQ_MP (@lem5422255 A _69992 g _69993) (@lem5422252 A _69992 g _69993)). Qed.
Lemma lem5422290 (x : nat) (y : nat) (z : nat) : term585 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem5422296 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) (h1 : term352 A s f i j) : (f i) = (f j).
Proof. exact (proj2 (@lem5421785 A s f i j h1)). Qed.
Lemma lem5422297 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) (h1 : term352 A s f i j) : term586 A i f j.
Proof. exact (fun h0 : term120 A i f j => @lem5422296 A s f i j h1). Qed.
Lemma lem5422299 (p : Prop) : (term147 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5422300 {A : Type'} (i : nat) (f : nat -> A) (j : nat) : (term586 A i f j) = ((f i) = (f j)).
Proof. exact (@lem5422299 ((f i) = (f j))). Qed.
Lemma lem5422301 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) (h1 : term352 A s f i j) : (f i) = (f j).
Proof. exact (EQ_MP (@lem5422300 A i f j) (@lem5422297 A s f i j h1)). Qed.
Lemma lem5422307 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5422308 {A : Type'} (g : A -> nat) (_69992 : A) (_69993 : A) : (term584 A _69992 g _69993) = (term587 A g _69992 _69993).
Proof. exact (@lem5422307 ((g _69992) = (g _69993)) (term588 A _69992 _69993)). Qed.
Lemma lem5422318 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5422319 {A : Type'} (g : A -> nat) (_69992 : A) (_69993 : A) : (term589 A _69992 g _69993) = (term590 A g _69992 _69993).
Proof. exact (MK_COMB (@lem5422318) (@lem5422308 A g _69992 _69993)). Qed.
Lemma lem5422329 {A : Type'} (g : A -> nat) (_69992 : A) (_69993 : A) : (term587 A g _69992 _69993) = (term587 A g _69992 _69993).
Proof. exact (eq_refl (term587 A g _69992 _69993)). Qed.
Lemma lem5422330 {A : Type'} (g : A -> nat) (_69992 : A) (_69993 : A) : ((term584 A _69992 g _69993) = (term587 A g _69992 _69993)) = ((term587 A g _69992 _69993) = (term587 A g _69992 _69993)).
Proof. exact (MK_COMB (@lem5422319 A g _69992 _69993) (@lem5422329 A g _69992 _69993)). Qed.
Lemma lem5422332 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5422333 (x : Prop) : (x = x) = True.
Proof. exact (@lem5422332 Prop x). Qed.
Lemma lem5422334 {A : Type'} (g : A -> nat) (_69992 : A) (_69993 : A) : ((term587 A g _69992 _69993) = (term587 A g _69992 _69993)) = True.
Proof. exact (@lem5422333 (term587 A g _69992 _69993)). Qed.
Lemma lem5422335 {A : Type'} (g : A -> nat) (_69992 : A) (_69993 : A) : ((term584 A _69992 g _69993) = (term587 A g _69992 _69993)) = True.
Proof. exact (TRANS (@lem5422330 A g _69992 _69993) (@lem5422334 A g _69992 _69993)). Qed.
Lemma lem5422336 {A : Type'} (g : A -> nat) (_69992 : A) (_69993 : A) : True = ((term584 A _69992 g _69993) = (term587 A g _69992 _69993)).
Proof. exact (SYM (@lem5422335 A g _69992 _69993)). Qed.
Lemma lem5422337 {A : Type'} (g : A -> nat) (_69992 : A) (_69993 : A) : (term584 A _69992 g _69993) = (term587 A g _69992 _69993).
Proof. exact (EQ_MP (@lem5422336 A g _69992 _69993) (@lem0)). Qed.
Lemma lem5422338 {A : Type'} (g : A -> nat) (_69992 : A) (_69993 : A) : term587 A g _69992 _69993.
Proof. exact (EQ_MP (@lem5422337 A g _69992 _69993) (@lem5422256 A _69992 g _69993)). Qed.
Lemma lem5422340 (b : Prop) (a : Prop) : (a \/ b) = (term159 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5422341 {A : Type'} (_69992 : A) (g : A -> nat) (_69993 : A) : (term587 A g _69992 _69993) = (term591 A _69992 g _69993).
Proof. exact (@lem5422340 (term588 A _69992 _69993) ((g _69992) = (g _69993))). Qed.
Lemma lem5422343 (a : Prop) : (term166 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5422344 {A : Type'} (_69992 : A) (_69993 : A) : (term592 A _69992 _69993) = (_69992 = _69993).
Proof. exact (@lem5422343 (_69992 = _69993)). Qed.
Lemma lem5422345 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5422346 {A : Type'} (_69992 : A) (_69993 : A) : (term593 A _69992 _69993) = (term594 A _69992 _69993).
Proof. exact (MK_COMB (@lem5422345) (@lem5422344 A _69992 _69993)). Qed.
Lemma lem5422347 {A : Type'} (_69992 : A) (g : A -> nat) (_69993 : A) : ((g _69992) = (g _69993)) = ((g _69992) = (g _69993)).
Proof. exact (eq_refl ((g _69992) = (g _69993))). Qed.
Lemma lem5422348 {A : Type'} (_69992 : A) (g : A -> nat) (_69993 : A) : (term591 A _69992 g _69993) = (term583 A _69992 g _69993).
Proof. exact (MK_COMB (@lem5422346 A _69992 _69993) (@lem5422347 A _69992 g _69993)). Qed.
Lemma lem5422349 {A : Type'} (_69992 : A) (g : A -> nat) (_69993 : A) : (term587 A g _69992 _69993) = (term583 A _69992 g _69993).
Proof. exact (TRANS (@lem5422341 A _69992 g _69993) (@lem5422348 A _69992 g _69993)). Qed.
Lemma lem5422352 {A : Type'} (_69992 : A) (g : A -> nat) (_69993 : A) : term583 A _69992 g _69993.
Proof. exact (EQ_MP (@lem5422349 A _69992 g _69993) (@lem5422338 A g _69992 _69993)). Qed.
Lemma lem5422353 {A : Type'} (_69992 : A) (g : A -> nat) (_69993 : A) : term583 A _69992 g _69993.
Proof. exact (@lem5422352 A _69992 g _69993). Qed.
Lemma lem5422354 {A : Type'} (i : nat) (g : A -> nat) (f : nat -> A) (j : nat) : term595 A i g f j.
Proof. exact (@lem5422353 A (f i) g (f j)). Qed.
Lemma lem5422357 {A : Type'} (g : A -> nat) (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) (h1 : term352 A s f i j) : (term264 A g f i) = (term264 A g f j).
Proof. exact (@lem5422354 A i g f j (@lem5422301 A s f i j h1)). Qed.
Lemma lem5422358 {A : Type'} (g : A -> nat) (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) (h1 : term352 A s f i j) : term596 A i g f j.
Proof. exact (fun h0 : term597 A i g f j => @lem5422357 A g s f i j h1). Qed.
Lemma lem5422360 (p : Prop) : (term147 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5422361 {A : Type'} (i : nat) (g : A -> nat) (f : nat -> A) (j : nat) : (term596 A i g f j) = ((term264 A g f i) = (term264 A g f j)).
Proof. exact (@lem5422360 ((term264 A g f i) = (term264 A g f j))). Qed.
Lemma lem5422362 {A : Type'} (g : A -> nat) (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) (h1 : term352 A s f i j) : (term264 A g f i) = (term264 A g f j).
Proof. exact (EQ_MP (@lem5422361 A i g f j) (@lem5422358 A g s f i j h1)). Qed.
Lemma lem5422364 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) (h1 : term352 A s f i j) : term257 A s i.
Proof. exact (proj1 (@lem5421784 A s f i j h1)). Qed.
Lemma lem5422365 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) (h1 : term352 A s f i j) : term598 A s i.
Proof. exact (fun h0 : term563 A s i => @lem5422364 A s f i j h1). Qed.
Lemma lem5422367 (p : Prop) : (term147 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5422368 {A : Type'} (s : A -> Prop) (i : nat) : (term598 A s i) = (term257 A s i).
Proof. exact (@lem5422367 (term257 A s i)). Qed.
Lemma lem5422369 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) (h1 : term352 A s f i j) : term257 A s i.
Proof. exact (EQ_MP (@lem5422368 A s i) (@lem5422365 A s f i j h1)). Qed.
Lemma lem5422375 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5422376 {A : Type'} (g : A -> nat) (f : nat -> A) (s : A -> Prop) (_69961 : nat) : (term573 A s g f _69961) = (term599 A g f s _69961).
Proof. exact (@lem5422375 ((term264 A g f _69961) = _69961) (term563 A s _69961)). Qed.
Lemma lem5422384 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5422385 {A : Type'} (g : A -> nat) (f : nat -> A) (s : A -> Prop) (_69961 : nat) : (term600 A s g f _69961) = (term601 A g f s _69961).
Proof. exact (MK_COMB (@lem5422384) (@lem5422376 A g f s _69961)). Qed.
Lemma lem5422393 {A : Type'} (g : A -> nat) (f : nat -> A) (s : A -> Prop) (_69961 : nat) : (term599 A g f s _69961) = (term599 A g f s _69961).
Proof. exact (eq_refl (term599 A g f s _69961)). Qed.
Lemma lem5422394 {A : Type'} (g : A -> nat) (f : nat -> A) (s : A -> Prop) (_69961 : nat) : ((term573 A s g f _69961) = (term599 A g f s _69961)) = ((term599 A g f s _69961) = (term599 A g f s _69961)).
Proof. exact (MK_COMB (@lem5422385 A g f s _69961) (@lem5422393 A g f s _69961)). Qed.
Lemma lem5422396 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5422397 (x : Prop) : (x = x) = True.
Proof. exact (@lem5422396 Prop x). Qed.
Lemma lem5422398 {A : Type'} (g : A -> nat) (f : nat -> A) (s : A -> Prop) (_69961 : nat) : ((term599 A g f s _69961) = (term599 A g f s _69961)) = True.
Proof. exact (@lem5422397 (term599 A g f s _69961)). Qed.
Lemma lem5422399 {A : Type'} (g : A -> nat) (f : nat -> A) (s : A -> Prop) (_69961 : nat) : ((term573 A s g f _69961) = (term599 A g f s _69961)) = True.
Proof. exact (TRANS (@lem5422394 A g f s _69961) (@lem5422398 A g f s _69961)). Qed.
Lemma lem5422400 {A : Type'} (g : A -> nat) (f : nat -> A) (s : A -> Prop) (_69961 : nat) : True = ((term573 A s g f _69961) = (term599 A g f s _69961)).
Proof. exact (SYM (@lem5422399 A g f s _69961)). Qed.
Lemma lem5422401 {A : Type'} (g : A -> nat) (f : nat -> A) (s : A -> Prop) (_69961 : nat) : (term573 A s g f _69961) = (term599 A g f s _69961).
Proof. exact (EQ_MP (@lem5422400 A g f s _69961) (@lem0)). Qed.
Lemma lem5422402 {A : Type'} (_69961 : nat) (s : A -> Prop) (f : nat -> A) (g : A -> nat) (h1 : term348 A s f g) : term599 A g f s _69961.
Proof. exact (EQ_MP (@lem5422401 A g f s _69961) (@lem5422044 A _69961 s f g h1)). Qed.
Lemma lem5422404 (b : Prop) (a : Prop) : (a \/ b) = (term159 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5422405 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : nat -> A) (_69961 : nat) : (term599 A g f s _69961) = (term602 A s g f _69961).
Proof. exact (@lem5422404 (term563 A s _69961) ((term264 A g f _69961) = _69961)). Qed.
Lemma lem5422407 (a : Prop) : (term166 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5422408 {A : Type'} (s : A -> Prop) (_69961 : nat) : (term603 A s _69961) = (term257 A s _69961).
Proof. exact (@lem5422407 (term257 A s _69961)). Qed.
Lemma lem5422409 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5422410 {A : Type'} (s : A -> Prop) (_69961 : nat) : (term604 A s _69961) = (term259 A s _69961).
Proof. exact (MK_COMB (@lem5422409) (@lem5422408 A s _69961)). Qed.
Lemma lem5422411 {A : Type'} (g : A -> nat) (f : nat -> A) (_69961 : nat) : ((term264 A g f _69961) = _69961) = ((term264 A g f _69961) = _69961).
Proof. exact (eq_refl ((term264 A g f _69961) = _69961)). Qed.
Lemma lem5422412 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : nat -> A) (_69961 : nat) : (term602 A s g f _69961) = (term605 A s g f _69961).
Proof. exact (MK_COMB (@lem5422410 A s _69961) (@lem5422411 A g f _69961)). Qed.
Lemma lem5422413 {A : Type'} (s : A -> Prop) (g : A -> nat) (f : nat -> A) (_69961 : nat) : (term599 A g f s _69961) = (term605 A s g f _69961).
Proof. exact (TRANS (@lem5422405 A s g f _69961) (@lem5422412 A s g f _69961)). Qed.
Lemma lem5422416 {A : Type'} (_69961 : nat) (s : A -> Prop) (f : nat -> A) (g : A -> nat) (h1 : term348 A s f g) : term605 A s g f _69961.
Proof. exact (EQ_MP (@lem5422413 A s g f _69961) (@lem5422402 A _69961 s f g h1)). Qed.
Lemma lem5422417 {A : Type'} (i : nat) (s : A -> Prop) (f : nat -> A) (g : A -> nat) (h1 : term348 A s f g) : term605 A s g f i.
Proof. exact (@lem5422416 A i s f g h1). Qed.
Lemma lem5422420 {A : Type'} (g : A -> nat) (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) (h1 : term348 A s f g) (h2 : term352 A s f i j) : (term264 A g f i) = i.
Proof. exact (@lem5422417 A i s f g h1 (@lem5422369 A s f i j h2)). Qed.
Lemma lem5422421 {A : Type'} (g : A -> nat) (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) (h1 : term348 A s f g) (h2 : term352 A s f i j) : term606 A g f i.
Proof. exact (fun h0 : term607 A g f i => @lem5422420 A g s f i j h1 h2). Qed.
Lemma lem5422423 (p : Prop) : (term147 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5422424 {A : Type'} (g : A -> nat) (f : nat -> A) (i : nat) : (term606 A g f i) = ((term264 A g f i) = i).
Proof. exact (@lem5422423 ((term264 A g f i) = i)). Qed.
Lemma lem5422425 {A : Type'} (g : A -> nat) (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) (h1 : term348 A s f g) (h2 : term352 A s f i j) : (term264 A g f i) = i.
Proof. exact (EQ_MP (@lem5422424 A g f i) (@lem5422421 A g s f i j h1 h2)). Qed.
Lemma lem5422443 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5422444 (y : nat) (x : nat) (z : nat) : (term608 x y z) = (term609 y x z).
Proof. exact (@lem5422443 (y = z) (term572 x z)). Qed.
Lemma lem5422454 (x : nat) (y : nat) : (term610 x y) = (term610 x y).
Proof. exact (eq_refl (term610 x y)). Qed.
Lemma lem5422455 (y : nat) (x : nat) (z : nat) : (term585 x y z) = (term611 y x z).
Proof. exact (MK_COMB (@lem5422454 x y) (@lem5422444 y x z)). Qed.
Lemma lem5422459 (q : Prop) (p : Prop) (r : Prop) : (term155 p q r) = (term155 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5422460 (y : nat) (x : nat) (z : nat) : (term611 y x z) = (term612 y x z).
Proof. exact (@lem5422459 (y = z) (term572 x y) (term572 x z)). Qed.
Lemma lem5422482 (y : nat) (x : nat) (z : nat) : (term585 x y z) = (term612 y x z).
Proof. exact (TRANS (@lem5422455 y x z) (@lem5422460 y x z)). Qed.
Lemma lem5422483 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5422484 (y : nat) (x : nat) (z : nat) : (term613 x y z) = (term614 y x z).
Proof. exact (MK_COMB (@lem5422483) (@lem5422482 y x z)). Qed.
Lemma lem5422506 (y : nat) (x : nat) (z : nat) : (term612 y x z) = (term612 y x z).
Proof. exact (eq_refl (term612 y x z)). Qed.
Lemma lem5422507 (y : nat) (x : nat) (z : nat) : ((term585 x y z) = (term612 y x z)) = ((term612 y x z) = (term612 y x z)).
Proof. exact (MK_COMB (@lem5422484 y x z) (@lem5422506 y x z)). Qed.
Lemma lem5422509 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5422510 (x : Prop) : (x = x) = True.
Proof. exact (@lem5422509 Prop x). Qed.
Lemma lem5422511 (y : nat) (x : nat) (z : nat) : ((term612 y x z) = (term612 y x z)) = True.
Proof. exact (@lem5422510 (term612 y x z)). Qed.
Lemma lem5422512 (y : nat) (x : nat) (z : nat) : ((term585 x y z) = (term612 y x z)) = True.
Proof. exact (TRANS (@lem5422507 y x z) (@lem5422511 y x z)). Qed.
Lemma lem5422513 (y : nat) (x : nat) (z : nat) : True = ((term585 x y z) = (term612 y x z)).
Proof. exact (SYM (@lem5422512 y x z)). Qed.
Lemma lem5422514 (y : nat) (x : nat) (z : nat) : (term585 x y z) = (term612 y x z).
Proof. exact (EQ_MP (@lem5422513 y x z) (@lem0)). Qed.
Lemma lem5422515 (y : nat) (x : nat) (z : nat) : term612 y x z.
Proof. exact (EQ_MP (@lem5422514 y x z) (@lem5422290 x y z)). Qed.
Lemma lem5422517 (b : Prop) (a : Prop) : (a \/ b) = (term159 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5422518 (x : nat) (y : nat) (z : nat) : (term612 y x z) = (term615 x y z).
Proof. exact (@lem5422517 (term616 y x z) (y = z)). Qed.
Lemma lem5422520 (a : Prop) (b : Prop) : (term162 a b) = (term163 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5422521 (y : nat) (x : nat) (z : nat) : (term617 y x z) = (term618 y x z).
Proof. exact (@lem5422520 (term572 x y) (term572 x z)). Qed.
Lemma lem5422523 (a : Prop) : (term166 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5422524 (x : nat) (y : nat) : (term619 x y) = (x = y).
Proof. exact (@lem5422523 (x = y)). Qed.
Lemma lem5422525 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5422526 (x : nat) (y : nat) : (term620 x y) = (term621 x y).
Proof. exact (MK_COMB (@lem5422525) (@lem5422524 x y)). Qed.
Lemma lem5422528 (a : Prop) : (term166 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5422529 (x : nat) (z : nat) : (term619 x z) = (x = z).
Proof. exact (@lem5422528 (x = z)). Qed.
Lemma lem5422530 (y : nat) (x : nat) (z : nat) : (term618 y x z) = (term622 y x z).
Proof. exact (MK_COMB (@lem5422526 x y) (@lem5422529 x z)). Qed.
Lemma lem5422531 (y : nat) (x : nat) (z : nat) : (term617 y x z) = (term622 y x z).
Proof. exact (TRANS (@lem5422521 y x z) (@lem5422530 y x z)). Qed.
Lemma lem5422532 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5422533 (y : nat) (x : nat) (z : nat) : (term623 y x z) = (term624 y x z).
Proof. exact (MK_COMB (@lem5422532) (@lem5422531 y x z)). Qed.
Lemma lem5422534 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem5422535 (x : nat) (y : nat) (z : nat) : (term615 x y z) = (term625 x y z).
Proof. exact (MK_COMB (@lem5422533 y x z) (@lem5422534 y z)). Qed.
Lemma lem5422536 (x : nat) (y : nat) (z : nat) : (term612 y x z) = (term625 x y z).
Proof. exact (TRANS (@lem5422518 x y z) (@lem5422535 x y z)). Qed.
Lemma lem5422538 {A : Type'} (g : A -> nat) (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) (h1 : term348 A s f g) (h2 : term352 A s f i j) : term626 A j g f i.
Proof. exact (conj (@lem5422362 A g s f i j h2) (@lem5422425 A g s f i j h1 h2)). Qed.
Lemma lem5422540 (x : nat) (y : nat) (z : nat) : term625 x y z.
Proof. exact (EQ_MP (@lem5422536 x y z) (@lem5422515 y x z)). Qed.
Lemma lem5422541 {A : Type'} (g : A -> nat) (f : nat -> A) (j : nat) (i : nat) : term627 A g f j i.
Proof. exact (@lem5422540 (term264 A g f i) (term264 A g f j) i). Qed.
Lemma lem5422544 {A : Type'} (g : A -> nat) (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) (h1 : term348 A s f g) (h2 : term352 A s f i j) : (term264 A g f j) = i.
Proof. exact (@lem5422541 A g f j i (@lem5422538 A g s f i j h1 h2)). Qed.
Lemma lem5422545 {A : Type'} (g : A -> nat) (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) (h1 : term348 A s f g) (h2 : term352 A s f i j) : term628 A g f j i.
Proof. exact (fun h0 : term629 A g f j i => @lem5422544 A g s f i j h1 h2). Qed.
Lemma lem5422547 (p : Prop) : (term147 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5422548 {A : Type'} (g : A -> nat) (f : nat -> A) (j : nat) (i : nat) : (term628 A g f j i) = ((term264 A g f j) = i).
Proof. exact (@lem5422547 ((term264 A g f j) = i)). Qed.
Lemma lem5422549 {A : Type'} (g : A -> nat) (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) (h1 : term348 A s f g) (h2 : term352 A s f i j) : (term264 A g f j) = i.
Proof. exact (EQ_MP (@lem5422548 A g f j i) (@lem5422545 A g s f i j h1 h2)). Qed.
Lemma lem5422551 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) (h1 : term352 A s f i j) : term257 A s j.
Proof. exact (proj1 (@lem5421785 A s f i j h1)). Qed.
Lemma lem5422552 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) (h1 : term352 A s f i j) : term598 A s j.
Proof. exact (fun h0 : term563 A s j => @lem5422551 A s f i j h1). Qed.
Lemma lem5422554 (p : Prop) : (term147 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5422555 {A : Type'} (s : A -> Prop) (j : nat) : (term598 A s j) = (term257 A s j).
Proof. exact (@lem5422554 (term257 A s j)). Qed.
Lemma lem5422556 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) (h1 : term352 A s f i j) : term257 A s j.
Proof. exact (EQ_MP (@lem5422555 A s j) (@lem5422552 A s f i j h1)). Qed.
Lemma lem5422558 {A : Type'} (_69961 : nat) (s : A -> Prop) (f : nat -> A) (g : A -> nat) (h1 : term348 A s f g) : term605 A s g f _69961.
Proof. exact (EQ_MP (@lem5422413 A s g f _69961) (@lem5422402 A _69961 s f g h1)). Qed.
Lemma lem5422559 {A : Type'} (j : nat) (s : A -> Prop) (f : nat -> A) (g : A -> nat) (h1 : term348 A s f g) : term605 A s g f j.
Proof. exact (@lem5422558 A j s f g h1). Qed.
Lemma lem5422562 {A : Type'} (g : A -> nat) (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) (h1 : term348 A s f g) (h2 : term352 A s f i j) : (term264 A g f j) = j.
Proof. exact (@lem5422559 A j s f g h1 (@lem5422556 A s f i j h2)). Qed.
Lemma lem5422563 {A : Type'} (g : A -> nat) (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) (h1 : term348 A s f g) (h2 : term352 A s f i j) : term606 A g f j.
Proof. exact (fun h0 : term607 A g f j => @lem5422562 A g s f i j h1 h2). Qed.
Lemma lem5422565 (p : Prop) : (term147 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5422566 {A : Type'} (g : A -> nat) (f : nat -> A) (j : nat) : (term606 A g f j) = ((term264 A g f j) = j).
Proof. exact (@lem5422565 ((term264 A g f j) = j)). Qed.
Lemma lem5422567 {A : Type'} (g : A -> nat) (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) (h1 : term348 A s f g) (h2 : term352 A s f i j) : (term264 A g f j) = j.
Proof. exact (EQ_MP (@lem5422566 A g f j) (@lem5422563 A g s f i j h1 h2)). Qed.
Lemma lem5422568 {A : Type'} (g : A -> nat) (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) (h1 : term348 A s f g) (h2 : term352 A s f i j) : term630 A i g f j.
Proof. exact (conj (@lem5422549 A g s f i j h1 h2) (@lem5422567 A g s f i j h1 h2)). Qed.
Lemma lem5422570 (x : nat) (y : nat) (z : nat) : term625 x y z.
Proof. exact (EQ_MP (@lem5422536 x y z) (@lem5422515 y x z)). Qed.
Lemma lem5422571 {A : Type'} (g : A -> nat) (f : nat -> A) (i : nat) (j : nat) : term631 A g f i j.
Proof. exact (@lem5422570 (term264 A g f j) i j). Qed.
Lemma lem5422574 {A : Type'} (g : A -> nat) (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) (h1 : term348 A s f g) (h2 : term352 A s f i j) : i = j.
Proof. exact (@lem5422571 A g f i j (@lem5422568 A g s f i j h1 h2)). Qed.
Lemma lem5422575 {A : Type'} (g : A -> nat) (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) (h1 : term348 A s f g) (h2 : term352 A s f i j) : term632 i j.
Proof. exact (fun h0 : term572 i j => @lem5422574 A g s f i j h1 h2). Qed.
Lemma lem5422577 (p : Prop) : (term147 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5422578 (i : nat) (j : nat) : (term632 i j) = (i = j).
Proof. exact (@lem5422577 (i = j)). Qed.
Lemma lem5422579 {A : Type'} (g : A -> nat) (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) (h1 : term348 A s f g) (h2 : term352 A s f i j) : i = j.
Proof. exact (EQ_MP (@lem5422578 i j) (@lem5422575 A g s f i j h1 h2)). Qed.
Lemma lem5422582 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5422584 (i : nat) (j : nat) : (term572 i j) = (term633 i j).
Proof. exact (@lem5422582 (i = j)). Qed.
Lemma lem5422587 {A : Type'} (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) (h1 : term352 A s f i j) : term633 i j.
Proof. exact (EQ_MP (@lem5422584 i j) (@lem5422014 A s f i j h1)). Qed.
Lemma lem5422590 {A : Type'} (g : A -> nat) (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) (h1 : term348 A s f g) (h2 : term352 A s f i j) : False.
Proof. exact (@lem5422587 A s f i j h2 (@lem5422579 A g s f i j h1 h2)). Qed.
Lemma lem5422591 {A : Type'} (g : A -> nat) (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) (h1 : term348 A s f g) (h2 : term352 A s f i j) : term210.
Proof. exact (fun h0 : ~ False => @lem5422590 A g s f i j h1 h2). Qed.
Lemma lem5422593 (p : Prop) : (term147 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5422594 : term210 = False.
Proof. exact (@lem5422593 False). Qed.
Lemma lem5422595 {A : Type'} (g : A -> nat) (s : A -> Prop) (f : nat -> A) (i : nat) (j : nat) (h1 : term348 A s f g) (h2 : term352 A s f i j) : False.
Proof. exact (EQ_MP (@lem5422594) (@lem5422591 A g s f i j h1 h2)). Qed.
Lemma lem5422686 {A : Type'} (x : A) (y : A) (z : A) : term634 A x y z.
Proof. exact (@lem21385 A x y z). Qed.
Lemma lem5422688 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) (h1 : term544 A x f s) : @I (A -> Prop) s x.
Proof. exact (proj1 (@lem5421789 A x f s h1)). Qed.
Lemma lem5422689 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) (h1 : term544 A x f s) : term635 A s x.
Proof. exact (fun h0 : term540 A s x => @lem5422688 A x f s h1). Qed.
Lemma lem5422691 (p : Prop) : (term147 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5422692 {A : Type'} (s : A -> Prop) (x : A) : (term635 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem5422691 (@I (A -> Prop) s x)). Qed.
Lemma lem5422693 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) (h1 : term544 A x f s) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem5422692 A s x) (@lem5422689 A x f s h1)). Qed.
Lemma lem5422699 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5422700 {A : Type'} (f : nat -> A) (g : A -> nat) (s : A -> Prop) (_69964 : A) : (term575 A s f g _69964) = (term636 A f g s _69964).
Proof. exact (@lem5422699 ((term281 A f g _69964) = _69964) (term540 A s _69964)). Qed.
Lemma lem5422708 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5422709 {A : Type'} (f : nat -> A) (g : A -> nat) (s : A -> Prop) (_69964 : A) : (term637 A s f g _69964) = (term638 A f g s _69964).
Proof. exact (MK_COMB (@lem5422708) (@lem5422700 A f g s _69964)). Qed.
Lemma lem5422717 {A : Type'} (f : nat -> A) (g : A -> nat) (s : A -> Prop) (_69964 : A) : (term636 A f g s _69964) = (term636 A f g s _69964).
Proof. exact (eq_refl (term636 A f g s _69964)). Qed.
Lemma lem5422718 {A : Type'} (f : nat -> A) (g : A -> nat) (s : A -> Prop) (_69964 : A) : ((term575 A s f g _69964) = (term636 A f g s _69964)) = ((term636 A f g s _69964) = (term636 A f g s _69964)).
Proof. exact (MK_COMB (@lem5422709 A f g s _69964) (@lem5422717 A f g s _69964)). Qed.
Lemma lem5422720 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5422721 (x : Prop) : (x = x) = True.
Proof. exact (@lem5422720 Prop x). Qed.
Lemma lem5422722 {A : Type'} (f : nat -> A) (g : A -> nat) (s : A -> Prop) (_69964 : A) : ((term636 A f g s _69964) = (term636 A f g s _69964)) = True.
Proof. exact (@lem5422721 (term636 A f g s _69964)). Qed.
Lemma lem5422723 {A : Type'} (f : nat -> A) (g : A -> nat) (s : A -> Prop) (_69964 : A) : ((term575 A s f g _69964) = (term636 A f g s _69964)) = True.
Proof. exact (TRANS (@lem5422718 A f g s _69964) (@lem5422722 A f g s _69964)). Qed.
Lemma lem5422724 {A : Type'} (f : nat -> A) (g : A -> nat) (s : A -> Prop) (_69964 : A) : True = ((term575 A s f g _69964) = (term636 A f g s _69964)).
Proof. exact (SYM (@lem5422723 A f g s _69964)). Qed.
Lemma lem5422725 {A : Type'} (f : nat -> A) (g : A -> nat) (s : A -> Prop) (_69964 : A) : (term575 A s f g _69964) = (term636 A f g s _69964).
Proof. exact (EQ_MP (@lem5422724 A f g s _69964) (@lem0)). Qed.
Lemma lem5422726 {A : Type'} (_69964 : A) (s : A -> Prop) (f : nat -> A) (g : A -> nat) (h1 : term348 A s f g) : term636 A f g s _69964.
Proof. exact (EQ_MP (@lem5422725 A f g s _69964) (@lem5422064 A _69964 s f g h1)). Qed.
Lemma lem5422728 (b : Prop) (a : Prop) : (a \/ b) = (term159 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5422729 {A : Type'} (s : A -> Prop) (f : nat -> A) (g : A -> nat) (_69964 : A) : (term636 A f g s _69964) = (term639 A s f g _69964).
Proof. exact (@lem5422728 (term540 A s _69964) ((term281 A f g _69964) = _69964)). Qed.
Lemma lem5422731 (a : Prop) : (term166 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5422732 {A : Type'} (s : A -> Prop) (_69964 : A) : (term640 A s _69964) = (@I (A -> Prop) s _69964).
Proof. exact (@lem5422731 (@I (A -> Prop) s _69964)). Qed.
Lemma lem5422733 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5422734 {A : Type'} (s : A -> Prop) (_69964 : A) : (term641 A s _69964) = (term642 A s _69964).
Proof. exact (MK_COMB (@lem5422733) (@lem5422732 A s _69964)). Qed.
Lemma lem5422735 {A : Type'} (f : nat -> A) (g : A -> nat) (_69964 : A) : ((term281 A f g _69964) = _69964) = ((term281 A f g _69964) = _69964).
Proof. exact (eq_refl ((term281 A f g _69964) = _69964)). Qed.
Lemma lem5422736 {A : Type'} (s : A -> Prop) (f : nat -> A) (g : A -> nat) (_69964 : A) : (term639 A s f g _69964) = (term643 A s f g _69964).
Proof. exact (MK_COMB (@lem5422734 A s _69964) (@lem5422735 A f g _69964)). Qed.
Lemma lem5422737 {A : Type'} (s : A -> Prop) (f : nat -> A) (g : A -> nat) (_69964 : A) : (term636 A f g s _69964) = (term643 A s f g _69964).
Proof. exact (TRANS (@lem5422729 A s f g _69964) (@lem5422736 A s f g _69964)). Qed.
Lemma lem5422740 {A : Type'} (_69964 : A) (s : A -> Prop) (f : nat -> A) (g : A -> nat) (h1 : term348 A s f g) : term643 A s f g _69964.
Proof. exact (EQ_MP (@lem5422737 A s f g _69964) (@lem5422726 A _69964 s f g h1)). Qed.
Lemma lem5422741 {A : Type'} (_69964 : A) (s : A -> Prop) (f : nat -> A) (g : A -> nat) (h1 : term348 A s f g) : term643 A s f g _69964.
Proof. exact (@lem5422740 A _69964 s f g h1). Qed.
Lemma lem5422742 {A : Type'} (x : A) (s : A -> Prop) (f : nat -> A) (g : A -> nat) (h1 : term348 A s f g) : term643 A s f g x.
Proof. exact (@lem5422741 A x s f g h1). Qed.
Lemma lem5422745 {A : Type'} (g : A -> nat) (x : A) (f : nat -> A) (s : A -> Prop) (h1 : term348 A s f g) (h2 : term544 A x f s) : (term281 A f g x) = x.
Proof. exact (@lem5422742 A x s f g h1 (@lem5422693 A x f s h2)). Qed.
Lemma lem5422746 {A : Type'} (g : A -> nat) (x : A) (f : nat -> A) (s : A -> Prop) (h1 : term348 A s f g) (h2 : term544 A x f s) : term644 A f g x.
Proof. exact (fun h0 : term645 A f g x => @lem5422745 A g x f s h1 h2). Qed.
Lemma lem5422748 (p : Prop) : (term147 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5422749 {A : Type'} (f : nat -> A) (g : A -> nat) (x : A) : (term644 A f g x) = ((term281 A f g x) = x).
Proof. exact (@lem5422748 ((term281 A f g x) = x)). Qed.
Lemma lem5422750 {A : Type'} (g : A -> nat) (x : A) (f : nat -> A) (s : A -> Prop) (h1 : term348 A s f g) (h2 : term544 A x f s) : (term281 A f g x) = x.
Proof. exact (EQ_MP (@lem5422749 A f g x) (@lem5422746 A g x f s h1 h2)). Qed.
Lemma lem5422752 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem5422753 {A : Type'} (x : A) : x = x.
Proof. exact (@lem5422752 A x). Qed.
Lemma lem5422754 {A : Type'} (f : nat -> A) (g : A -> nat) (x : A) : (term281 A f g x) = (term281 A f g x).
Proof. exact (@lem5422753 A (term281 A f g x)). Qed.
Lemma lem5422755 {A : Type'} (f : nat -> A) (g : A -> nat) (x : A) : term646 A f g x.
Proof. exact (fun h0 : term647 A f g x => @lem5422754 A f g x). Qed.
Lemma lem5422757 (p : Prop) : (term147 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5422758 {A : Type'} (f : nat -> A) (g : A -> nat) (x : A) : (term646 A f g x) = ((term281 A f g x) = (term281 A f g x)).
Proof. exact (@lem5422757 ((term281 A f g x) = (term281 A f g x))). Qed.
Lemma lem5422759 {A : Type'} (f : nat -> A) (g : A -> nat) (x : A) : (term281 A f g x) = (term281 A f g x).
Proof. exact (EQ_MP (@lem5422758 A f g x) (@lem5422755 A f g x)). Qed.
Lemma lem5422777 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5422778 {A : Type'} (y : A) (x : A) (z : A) : (term648 A x y z) = (term649 A y x z).
Proof. exact (@lem5422777 (y = z) (term588 A x z)). Qed.
Lemma lem5422788 {A : Type'} (x : A) (y : A) : (term650 A x y) = (term650 A x y).
Proof. exact (eq_refl (term650 A x y)). Qed.
Lemma lem5422789 {A : Type'} (y : A) (x : A) (z : A) : (term634 A x y z) = (term651 A y x z).
Proof. exact (MK_COMB (@lem5422788 A x y) (@lem5422778 A y x z)). Qed.
Lemma lem5422793 (q : Prop) (p : Prop) (r : Prop) : (term155 p q r) = (term155 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5422794 {A : Type'} (y : A) (x : A) (z : A) : (term651 A y x z) = (term652 A y x z).
Proof. exact (@lem5422793 (y = z) (term588 A x y) (term588 A x z)). Qed.
Lemma lem5422816 {A : Type'} (y : A) (x : A) (z : A) : (term634 A x y z) = (term652 A y x z).
Proof. exact (TRANS (@lem5422789 A y x z) (@lem5422794 A y x z)). Qed.
Lemma lem5422817 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5422818 {A : Type'} (y : A) (x : A) (z : A) : (term653 A x y z) = (term654 A y x z).
Proof. exact (MK_COMB (@lem5422817) (@lem5422816 A y x z)). Qed.
Lemma lem5422840 {A : Type'} (y : A) (x : A) (z : A) : (term652 A y x z) = (term652 A y x z).
Proof. exact (eq_refl (term652 A y x z)). Qed.
Lemma lem5422841 {A : Type'} (y : A) (x : A) (z : A) : ((term634 A x y z) = (term652 A y x z)) = ((term652 A y x z) = (term652 A y x z)).
Proof. exact (MK_COMB (@lem5422818 A y x z) (@lem5422840 A y x z)). Qed.
Lemma lem5422843 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5422844 (x : Prop) : (x = x) = True.
Proof. exact (@lem5422843 Prop x). Qed.
Lemma lem5422845 {A : Type'} (y : A) (x : A) (z : A) : ((term652 A y x z) = (term652 A y x z)) = True.
Proof. exact (@lem5422844 (term652 A y x z)). Qed.
Lemma lem5422846 {A : Type'} (y : A) (x : A) (z : A) : ((term634 A x y z) = (term652 A y x z)) = True.
Proof. exact (TRANS (@lem5422841 A y x z) (@lem5422845 A y x z)). Qed.
Lemma lem5422847 {A : Type'} (y : A) (x : A) (z : A) : True = ((term634 A x y z) = (term652 A y x z)).
Proof. exact (SYM (@lem5422846 A y x z)). Qed.
Lemma lem5422848 {A : Type'} (y : A) (x : A) (z : A) : (term634 A x y z) = (term652 A y x z).
Proof. exact (EQ_MP (@lem5422847 A y x z) (@lem0)). Qed.
Lemma lem5422849 {A : Type'} (y : A) (x : A) (z : A) : term652 A y x z.
Proof. exact (EQ_MP (@lem5422848 A y x z) (@lem5422686 A x y z)). Qed.
Lemma lem5422851 (b : Prop) (a : Prop) : (a \/ b) = (term159 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5422852 {A : Type'} (x : A) (y : A) (z : A) : (term652 A y x z) = (term655 A x y z).
Proof. exact (@lem5422851 (term656 A y x z) (y = z)). Qed.
Lemma lem5422854 (a : Prop) (b : Prop) : (term162 a b) = (term163 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5422855 {A : Type'} (y : A) (x : A) (z : A) : (term657 A y x z) = (term658 A y x z).
Proof. exact (@lem5422854 (term588 A x y) (term588 A x z)). Qed.
Lemma lem5422857 (a : Prop) : (term166 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5422858 {A : Type'} (x : A) (y : A) : (term592 A x y) = (x = y).
Proof. exact (@lem5422857 (x = y)). Qed.
Lemma lem5422859 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5422860 {A : Type'} (x : A) (y : A) : (term659 A x y) = (term660 A x y).
Proof. exact (MK_COMB (@lem5422859) (@lem5422858 A x y)). Qed.
Lemma lem5422862 (a : Prop) : (term166 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5422863 {A : Type'} (x : A) (z : A) : (term592 A x z) = (x = z).
Proof. exact (@lem5422862 (x = z)). Qed.
Lemma lem5422864 {A : Type'} (y : A) (x : A) (z : A) : (term658 A y x z) = (term661 A y x z).
Proof. exact (MK_COMB (@lem5422860 A x y) (@lem5422863 A x z)). Qed.
Lemma lem5422865 {A : Type'} (y : A) (x : A) (z : A) : (term657 A y x z) = (term661 A y x z).
Proof. exact (TRANS (@lem5422855 A y x z) (@lem5422864 A y x z)). Qed.
Lemma lem5422866 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5422867 {A : Type'} (y : A) (x : A) (z : A) : (term662 A y x z) = (term663 A y x z).
Proof. exact (MK_COMB (@lem5422866) (@lem5422865 A y x z)). Qed.
Lemma lem5422868 {A : Type'} (y : A) (z : A) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem5422869 {A : Type'} (x : A) (y : A) (z : A) : (term655 A x y z) = (term664 A x y z).
Proof. exact (MK_COMB (@lem5422867 A y x z) (@lem5422868 A y z)). Qed.
Lemma lem5422870 {A : Type'} (x : A) (y : A) (z : A) : (term652 A y x z) = (term664 A x y z).
Proof. exact (TRANS (@lem5422852 A x y z) (@lem5422869 A x y z)). Qed.
Lemma lem5422872 {A : Type'} (g : A -> nat) (x : A) (f : nat -> A) (s : A -> Prop) (h1 : term348 A s f g) (h2 : term544 A x f s) : term665 A f g x.
Proof. exact (conj (@lem5422750 A g x f s h1 h2) (@lem5422759 A f g x)). Qed.
Lemma lem5422874 {A : Type'} (x : A) (y : A) (z : A) : term664 A x y z.
Proof. exact (EQ_MP (@lem5422870 A x y z) (@lem5422849 A y x z)). Qed.
Lemma lem5422875 {A : Type'} (x : A) (y : A) (z : A) : term664 A x y z.
Proof. exact (@lem5422874 A x y z). Qed.
Lemma lem5422876 {A : Type'} (f : nat -> A) (g : A -> nat) (x : A) : term666 A f g x.
Proof. exact (@lem5422875 A (term281 A f g x) x (term281 A f g x)). Qed.
Lemma lem5422879 {A : Type'} (g : A -> nat) (x : A) (f : nat -> A) (s : A -> Prop) (h1 : term348 A s f g) (h2 : term544 A x f s) : x = (term281 A f g x).
Proof. exact (@lem5422876 A f g x (@lem5422872 A g x f s h1 h2)). Qed.
Lemma lem5422880 {A : Type'} (g : A -> nat) (x : A) (f : nat -> A) (s : A -> Prop) (h1 : term348 A s f g) (h2 : term544 A x f s) : term667 A f g x.
Proof. exact (fun h0 : term668 A f g x => @lem5422879 A g x f s h1 h2). Qed.
Lemma lem5422882 (p : Prop) : (term147 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5422883 {A : Type'} (f : nat -> A) (g : A -> nat) (x : A) : (term667 A f g x) = (x = (term281 A f g x)).
Proof. exact (@lem5422882 (x = (term281 A f g x))). Qed.
Lemma lem5422884 {A : Type'} (g : A -> nat) (x : A) (f : nat -> A) (s : A -> Prop) (h1 : term348 A s f g) (h2 : term544 A x f s) : x = (term281 A f g x).
Proof. exact (EQ_MP (@lem5422883 A f g x) (@lem5422880 A g x f s h1 h2)). Qed.
Lemma lem5422886 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) (h1 : term544 A x f s) : @I (A -> Prop) s x.
Proof. exact (proj1 (@lem5421789 A x f s h1)). Qed.
Lemma lem5422887 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) (h1 : term544 A x f s) : term635 A s x.
Proof. exact (fun h0 : term540 A s x => @lem5422886 A x f s h1). Qed.
Lemma lem5422889 (p : Prop) : (term147 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5422890 {A : Type'} (s : A -> Prop) (x : A) : (term635 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem5422889 (@I (A -> Prop) s x)). Qed.
Lemma lem5422891 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) (h1 : term544 A x f s) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem5422890 A s x) (@lem5422887 A x f s h1)). Qed.
Lemma lem5422897 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5422898 {A : Type'} (g : A -> nat) (s : A -> Prop) (_69964 : A) : (term574 A s g _69964) = (term669 A g s _69964).
Proof. exact (@lem5422897 (term278 A s g _69964) (term540 A s _69964)). Qed.
Lemma lem5422904 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5422905 {A : Type'} (g : A -> nat) (s : A -> Prop) (_69964 : A) : (term670 A s g _69964) = (term671 A g s _69964).
Proof. exact (MK_COMB (@lem5422904) (@lem5422898 A g s _69964)). Qed.
Lemma lem5422911 {A : Type'} (g : A -> nat) (s : A -> Prop) (_69964 : A) : (term669 A g s _69964) = (term669 A g s _69964).
Proof. exact (eq_refl (term669 A g s _69964)). Qed.
Lemma lem5422912 {A : Type'} (g : A -> nat) (s : A -> Prop) (_69964 : A) : ((term574 A s g _69964) = (term669 A g s _69964)) = ((term669 A g s _69964) = (term669 A g s _69964)).
Proof. exact (MK_COMB (@lem5422905 A g s _69964) (@lem5422911 A g s _69964)). Qed.
Lemma lem5422914 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5422915 (x : Prop) : (x = x) = True.
Proof. exact (@lem5422914 Prop x). Qed.
Lemma lem5422916 {A : Type'} (g : A -> nat) (s : A -> Prop) (_69964 : A) : ((term669 A g s _69964) = (term669 A g s _69964)) = True.
Proof. exact (@lem5422915 (term669 A g s _69964)). Qed.
Lemma lem5422917 {A : Type'} (g : A -> nat) (s : A -> Prop) (_69964 : A) : ((term574 A s g _69964) = (term669 A g s _69964)) = True.
Proof. exact (TRANS (@lem5422912 A g s _69964) (@lem5422916 A g s _69964)). Qed.
Lemma lem5422918 {A : Type'} (g : A -> nat) (s : A -> Prop) (_69964 : A) : True = ((term574 A s g _69964) = (term669 A g s _69964)).
Proof. exact (SYM (@lem5422917 A g s _69964)). Qed.
Lemma lem5422919 {A : Type'} (g : A -> nat) (s : A -> Prop) (_69964 : A) : (term574 A s g _69964) = (term669 A g s _69964).
Proof. exact (EQ_MP (@lem5422918 A g s _69964) (@lem0)). Qed.
Lemma lem5422920 {A : Type'} (_69964 : A) (s : A -> Prop) (f : nat -> A) (g : A -> nat) (h1 : term348 A s f g) : term669 A g s _69964.
Proof. exact (EQ_MP (@lem5422919 A g s _69964) (@lem5422058 A _69964 s f g h1)). Qed.
Lemma lem5422922 (b : Prop) (a : Prop) : (a \/ b) = (term159 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5422923 {A : Type'} (s : A -> Prop) (g : A -> nat) (_69964 : A) : (term669 A g s _69964) = (term672 A s g _69964).
Proof. exact (@lem5422922 (term540 A s _69964) (term278 A s g _69964)). Qed.
Lemma lem5422925 (a : Prop) : (term166 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5422926 {A : Type'} (s : A -> Prop) (_69964 : A) : (term640 A s _69964) = (@I (A -> Prop) s _69964).
Proof. exact (@lem5422925 (@I (A -> Prop) s _69964)). Qed.
Lemma lem5422927 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5422928 {A : Type'} (s : A -> Prop) (_69964 : A) : (term641 A s _69964) = (term642 A s _69964).
Proof. exact (MK_COMB (@lem5422927) (@lem5422926 A s _69964)). Qed.
Lemma lem5422929 {A : Type'} (s : A -> Prop) (g : A -> nat) (_69964 : A) : (term278 A s g _69964) = (term278 A s g _69964).
Proof. exact (eq_refl (term278 A s g _69964)). Qed.
Lemma lem5422930 {A : Type'} (s : A -> Prop) (g : A -> nat) (_69964 : A) : (term672 A s g _69964) = (term673 A s g _69964).
Proof. exact (MK_COMB (@lem5422928 A s _69964) (@lem5422929 A s g _69964)). Qed.
Lemma lem5422931 {A : Type'} (s : A -> Prop) (g : A -> nat) (_69964 : A) : (term669 A g s _69964) = (term673 A s g _69964).
Proof. exact (TRANS (@lem5422923 A s g _69964) (@lem5422930 A s g _69964)). Qed.
Lemma lem5422934 {A : Type'} (_69964 : A) (s : A -> Prop) (f : nat -> A) (g : A -> nat) (h1 : term348 A s f g) : term673 A s g _69964.
Proof. exact (EQ_MP (@lem5422931 A s g _69964) (@lem5422920 A _69964 s f g h1)). Qed.
Lemma lem5422935 {A : Type'} (_69964 : A) (s : A -> Prop) (f : nat -> A) (g : A -> nat) (h1 : term348 A s f g) : term673 A s g _69964.
Proof. exact (@lem5422934 A _69964 s f g h1). Qed.
Lemma lem5422936 {A : Type'} (x : A) (s : A -> Prop) (f : nat -> A) (g : A -> nat) (h1 : term348 A s f g) : term673 A s g x.
Proof. exact (@lem5422935 A x s f g h1). Qed.
Lemma lem5422939 {A : Type'} (g : A -> nat) (x : A) (f : nat -> A) (s : A -> Prop) (h1 : term348 A s f g) (h2 : term544 A x f s) : term278 A s g x.
Proof. exact (@lem5422936 A x s f g h1 (@lem5422891 A x f s h2)). Qed.
Lemma lem5422940 {A : Type'} (g : A -> nat) (x : A) (f : nat -> A) (s : A -> Prop) (h1 : term348 A s f g) (h2 : term544 A x f s) : term674 A s g x.
Proof. exact (fun h0 : term675 A s g x => @lem5422939 A g x f s h1 h2). Qed.
Lemma lem5422942 (p : Prop) : (term147 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5422943 {A : Type'} (s : A -> Prop) (g : A -> nat) (x : A) : (term674 A s g x) = (term278 A s g x).
Proof. exact (@lem5422942 (term278 A s g x)). Qed.
Lemma lem5422944 {A : Type'} (g : A -> nat) (x : A) (f : nat -> A) (s : A -> Prop) (h1 : term348 A s f g) (h2 : term544 A x f s) : term278 A s g x.
Proof. exact (EQ_MP (@lem5422943 A s g x) (@lem5422940 A g x f s h1 h2)). Qed.
Lemma lem5422946 (a : Prop) (b : Prop) : (term676 a b) = (term677 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5422947 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) (_69965 : nat) : (term370 A x f s _69965) = (term369 A x f s _69965).
Proof. exact (@lem5422946 (x = (f _69965)) (term257 A s _69965)). Qed.
Lemma lem5422949 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5422950 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) (_69965 : nat) : (term369 A x f s _69965) = (term678 A x f s _69965).
Proof. exact (@lem5422949 (term318 A x f s _69965)). Qed.
Lemma lem5422951 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) (_69965 : nat) : (term370 A x f s _69965) = (term678 A x f s _69965).
Proof. exact (TRANS (@lem5422947 A x f s _69965) (@lem5422950 A x f s _69965)). Qed.
Lemma lem5422953 {A : Type'} (g : A -> nat) (x : A) (f : nat -> A) (s : A -> Prop) (h1 : term348 A s f g) (h2 : term544 A x f s) : term679 A f s g x.
Proof. exact (conj (@lem5422884 A g x f s h1 h2) (@lem5422944 A g x f s h1 h2)). Qed.
Lemma lem5422955 {A : Type'} (_69965 : nat) (x : A) (f : nat -> A) (s : A -> Prop) (h1 : term544 A x f s) : term678 A x f s _69965.
Proof. exact (EQ_MP (@lem5422951 A x f s _69965) (@lem5422052 A _69965 x f s h1)). Qed.
Lemma lem5422956 {A : Type'} (g : A -> nat) (x : A) (f : nat -> A) (s : A -> Prop) (h1 : term544 A x f s) : term680 A f s g x.
Proof. exact (@lem5422955 A (g x) x f s h1). Qed.
Lemma lem5422959 {A : Type'} (g : A -> nat) (x : A) (f : nat -> A) (s : A -> Prop) (h1 : term348 A s f g) (h2 : term544 A x f s) : False.
Proof. exact (@lem5422956 A g x f s h2 (@lem5422953 A g x f s h1 h2)). Qed.
Lemma lem5422960 {A : Type'} (g : A -> nat) (x : A) (f : nat -> A) (s : A -> Prop) (h1 : term348 A s f g) (h2 : term544 A x f s) : term210.
Proof. exact (fun h0 : ~ False => @lem5422959 A g x f s h1 h2). Qed.
Lemma lem5422962 (p : Prop) : (term147 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5422963 : term210 = False.
Proof. exact (@lem5422962 False). Qed.
Lemma lem5422964 {A : Type'} (g : A -> nat) (x : A) (f : nat -> A) (s : A -> Prop) (h1 : term348 A s f g) (h2 : term544 A x f s) : False.
Proof. exact (EQ_MP (@lem5422963) (@lem5422960 A g x f s h1 h2)). Qed.
Lemma lem5423057 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) (x' : nat) (h1 : term542 A x f s x') : term257 A s x'.
Proof. exact (proj2 (@lem5421793 A x f s x' h1)). Qed.
Lemma lem5423058 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) (x' : nat) (h1 : term542 A x f s x') : term598 A s x'.
Proof. exact (fun h0 : term563 A s x' => @lem5423057 A x f s x' h1). Qed.
Lemma lem5423060 (p : Prop) : (term147 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5423061 {A : Type'} (s : A -> Prop) (x' : nat) : (term598 A s x') = (term257 A s x').
Proof. exact (@lem5423060 (term257 A s x')). Qed.
Lemma lem5423062 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) (x' : nat) (h1 : term542 A x f s x') : term257 A s x'.
Proof. exact (EQ_MP (@lem5423061 A s x') (@lem5423058 A x f s x' h1)). Qed.
Lemma lem5423068 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5423069 {A : Type'} (f : nat -> A) (s : A -> Prop) (_69966 : nat) : (term582 A s f _69966) = (term681 A f s _69966).
Proof. exact (@lem5423068 (term553 A s f _69966) (term563 A s _69966)). Qed.
Lemma lem5423075 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5423076 {A : Type'} (f : nat -> A) (s : A -> Prop) (_69966 : nat) : (term682 A s f _69966) = (term683 A f s _69966).
Proof. exact (MK_COMB (@lem5423075) (@lem5423069 A f s _69966)). Qed.
Lemma lem5423082 {A : Type'} (f : nat -> A) (s : A -> Prop) (_69966 : nat) : (term681 A f s _69966) = (term681 A f s _69966).
Proof. exact (eq_refl (term681 A f s _69966)). Qed.
Lemma lem5423083 {A : Type'} (f : nat -> A) (s : A -> Prop) (_69966 : nat) : ((term582 A s f _69966) = (term681 A f s _69966)) = ((term681 A f s _69966) = (term681 A f s _69966)).
Proof. exact (MK_COMB (@lem5423076 A f s _69966) (@lem5423082 A f s _69966)). Qed.
Lemma lem5423085 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5423086 (x : Prop) : (x = x) = True.
Proof. exact (@lem5423085 Prop x). Qed.
Lemma lem5423087 {A : Type'} (f : nat -> A) (s : A -> Prop) (_69966 : nat) : ((term681 A f s _69966) = (term681 A f s _69966)) = True.
Proof. exact (@lem5423086 (term681 A f s _69966)). Qed.
Lemma lem5423088 {A : Type'} (f : nat -> A) (s : A -> Prop) (_69966 : nat) : ((term582 A s f _69966) = (term681 A f s _69966)) = True.
Proof. exact (TRANS (@lem5423083 A f s _69966) (@lem5423087 A f s _69966)). Qed.
Lemma lem5423089 {A : Type'} (f : nat -> A) (s : A -> Prop) (_69966 : nat) : True = ((term582 A s f _69966) = (term681 A f s _69966)).
Proof. exact (SYM (@lem5423088 A f s _69966)). Qed.
Lemma lem5423090 {A : Type'} (f : nat -> A) (s : A -> Prop) (_69966 : nat) : (term582 A s f _69966) = (term681 A f s _69966).
Proof. exact (EQ_MP (@lem5423089 A f s _69966) (@lem0)). Qed.
Lemma lem5423091 {A : Type'} (_69966 : nat) (s : A -> Prop) (f : nat -> A) (g : A -> nat) (h1 : term348 A s f g) : term681 A f s _69966.
Proof. exact (EQ_MP (@lem5423090 A f s _69966) (@lem5422189 A _69966 s f g h1)). Qed.
Lemma lem5423093 (b : Prop) (a : Prop) : (a \/ b) = (term159 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5423094 {A : Type'} (s : A -> Prop) (f : nat -> A) (_69966 : nat) : (term681 A f s _69966) = (term684 A s f _69966).
Proof. exact (@lem5423093 (term563 A s _69966) (term553 A s f _69966)). Qed.
Lemma lem5423096 (a : Prop) : (term166 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5423097 {A : Type'} (s : A -> Prop) (_69966 : nat) : (term603 A s _69966) = (term257 A s _69966).
Proof. exact (@lem5423096 (term257 A s _69966)). Qed.
Lemma lem5423098 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5423099 {A : Type'} (s : A -> Prop) (_69966 : nat) : (term604 A s _69966) = (term259 A s _69966).
Proof. exact (MK_COMB (@lem5423098) (@lem5423097 A s _69966)). Qed.
Lemma lem5423100 {A : Type'} (s : A -> Prop) (f : nat -> A) (_69966 : nat) : (term553 A s f _69966) = (term553 A s f _69966).
Proof. exact (eq_refl (term553 A s f _69966)). Qed.
Lemma lem5423101 {A : Type'} (s : A -> Prop) (f : nat -> A) (_69966 : nat) : (term684 A s f _69966) = (term685 A s f _69966).
Proof. exact (MK_COMB (@lem5423099 A s _69966) (@lem5423100 A s f _69966)). Qed.
Lemma lem5423102 {A : Type'} (s : A -> Prop) (f : nat -> A) (_69966 : nat) : (term681 A f s _69966) = (term685 A s f _69966).
Proof. exact (TRANS (@lem5423094 A s f _69966) (@lem5423101 A s f _69966)). Qed.
Lemma lem5423105 {A : Type'} (_69966 : nat) (s : A -> Prop) (f : nat -> A) (g : A -> nat) (h1 : term348 A s f g) : term685 A s f _69966.
Proof. exact (EQ_MP (@lem5423102 A s f _69966) (@lem5423091 A _69966 s f g h1)). Qed.
Lemma lem5423106 {A : Type'} (x' : nat) (s : A -> Prop) (f : nat -> A) (g : A -> nat) (h1 : term348 A s f g) : term685 A s f x'.
Proof. exact (@lem5423105 A x' s f g h1). Qed.
Lemma lem5423109 {A : Type'} (g : A -> nat) (x : A) (f : nat -> A) (s : A -> Prop) (x' : nat) (h1 : term348 A s f g) (h2 : term542 A x f s x') : term553 A s f x'.
Proof. exact (@lem5423106 A x' s f g h1 (@lem5423062 A x f s x' h2)). Qed.
Lemma lem5423110 {A : Type'} (g : A -> nat) (x : A) (f : nat -> A) (s : A -> Prop) (x' : nat) (h1 : term348 A s f g) (h2 : term542 A x f s x') : term686 A s f x'.
Proof. exact (fun h0 : term579 A s f x' => @lem5423109 A g x f s x' h1 h2). Qed.
Lemma lem5423112 (p : Prop) : (term147 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5423113 {A : Type'} (s : A -> Prop) (f : nat -> A) (x' : nat) : (term686 A s f x') = (term553 A s f x').
Proof. exact (@lem5423112 (term553 A s f x')). Qed.
Lemma lem5423114 {A : Type'} (g : A -> nat) (x : A) (f : nat -> A) (s : A -> Prop) (x' : nat) (h1 : term348 A s f g) (h2 : term542 A x f s x') : term553 A s f x'.
Proof. exact (EQ_MP (@lem5423113 A s f x') (@lem5423110 A g x f s x' h1 h2)). Qed.
Lemma lem5423117 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5423119 {A : Type'} (s : A -> Prop) (f : nat -> A) (x' : nat) : (term579 A s f x') = (term687 A s f x').
Proof. exact (@lem5423117 (term553 A s f x')). Qed.
Lemma lem5423122 {A : Type'} (x : A) (f : nat -> A) (s : A -> Prop) (x' : nat) (h1 : term542 A x f s x') : term687 A s f x'.
Proof. exact (EQ_MP (@lem5423119 A s f x') (@lem5422133 A x f s x' h1)). Qed.
Lemma lem5423125 {A : Type'} (g : A -> nat) (x : A) (f : nat -> A) (s : A -> Prop) (x' : nat) (h1 : term348 A s f g) (h2 : term542 A x f s x') : False.
Proof. exact (@lem5423122 A x f s x' h2 (@lem5423114 A g x f s x' h1 h2)). Qed.
Lemma lem5423126 {A : Type'} (g : A -> nat) (x : A) (f : nat -> A) (s : A -> Prop) (x' : nat) (h1 : term348 A s f g) (h2 : term542 A x f s x') : term210.
Proof. exact (fun h0 : ~ False => @lem5423125 A g x f s x' h1 h2). Qed.
Lemma lem5423128 (p : Prop) : (term147 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5423129 : term210 = False.
Proof. exact (@lem5423128 False). Qed.
Lemma lem5423131 {A : Type'} (g : A -> nat) (x : A) (f : nat -> A) (s : A -> Prop) (x' : nat) (h1 : term348 A s f g) (h2 : term542 A x f s x') : False.
Proof. exact (EQ_MP (@lem5423129) (@lem5423126 A g x f s x' h1 h2)). Qed.
Lemma lem5423132 {A : Type'} (g : A -> nat) (x : A) (f : nat -> A) (s : A -> Prop) (x' : nat) (h1 : term348 A s f g) (h2 : term546 A x f s x') : False.
Proof. exact (or_elim (@lem5421782 A x f s x' h2) (fun h0 : term544 A x f s => @lem5422964 A g x f s h1 h0) (fun h0 : term542 A x f s x' => @lem5423131 A g x f s x' h1 h0)). Qed.
Lemma lem5423133 {A : Type'} (g : A -> nat) (i : nat) (j : nat) (x : A) (f : nat -> A) (s : A -> Prop) (x' : nat) (h1 : term348 A s f g) (h2 : term530 A i j x f s x') : False.
Proof. exact (or_elim (@lem5421688 A i j x f s x' h2) (fun h0 : term352 A s f i j => @lem5422595 A g s f i j h1 h0) (fun h0 : term546 A x f s x' => @lem5423132 A g x f s x' h1 h0)). Qed.
Lemma lem5423134 {A : Type'} (i : nat) (j : nat) (x : A) (f : nat -> A) (s : A -> Prop) (x' : nat) (h1 : term294 A s f) (h2 : term530 A i j x f s x') : False.
Proof. exact (ex_elim (@lem5421020 A s f h1) (fun g : A -> nat => fun h0 : term349 A s f g => @lem5423133 A g i j x f s x' h0 h2)). Qed.
Lemma lem5423135 {A : Type'} (i : nat) (j : nat) (x : A) (f : nat -> A) (s : A -> Prop) (h1 : term294 A s f) (h2 : term533 A i j x f s) : False.
Proof. exact (ex_elim (@lem5421551 A i j x f s h2) (fun x' : nat => fun h0 : term532 A i j x f s x' => @lem5423134 A i j x f s x' h1 h0)). Qed.
Lemma lem5423136 {A : Type'} (i : nat) (j : nat) (s : A -> Prop) (f : nat -> A) (h1 : term535 A i j f s) (h2 : term294 A s f) : False.
Proof. exact (ex_elim (@lem5421550 A i j f s h1) (fun x : A => fun h0 : term534 A i j f s x => @lem5423135 A i j x f s h2 h0)). Qed.
Lemma lem5423137 {A : Type'} (i : nat) (f : nat -> A) (s : A -> Prop) (h1 : term294 A s f) (h2 : term537 A i f s) : False.
Proof. exact (ex_elim (@lem5421549 A i f s h2) (fun j : nat => fun h0 : term536 A i f s j => @lem5423136 A i j s f h0 h1)). Qed.
Lemma lem5423138 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term294 A s f) (h2 : term340 A f s) : False.
Proof. exact (ex_elim (@lem5421548 A f s h2) (fun i : nat => fun h0 : term538 A f s i => @lem5423137 A i f s h1 h0)). Qed.
Lemma lem5423139 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term294 A s f) (h2 : term340 A f s) : (term340 A f s) = False.
Proof. exact (prop_ext (fun h3 : term340 A f s => @lem5423138 A f s h1 h2) (fun h3 : False => @lem5420837 A f s h2)). Qed.
Lemma lem5423140 {A : Type'} (f : nat -> A) (s : A -> Prop) (h1 : term294 A s f) (h2 : term340 A f s) : False.
Proof. exact (EQ_MP (@lem5423139 A f s h1 h2) (@lem5420837 A f s h2)). Qed.
Lemma lem5423141 {A : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term294 A s f) : term339 A f s.
Proof. exact (fun h0 : term340 A f s => @lem5423140 A f s h1 h0). Qed.
Lemma lem5423142 {A : Type'} (s : A -> Prop) (f : nat -> A) (h1 : term294 A s f) : term325 A f s.
Proof. exact (EQ_MP (@lem5420836 A f s) (@lem5423141 A s f h1)). Qed.
Lemma lem5423143 {A : Type'} (f : nat -> A) (s : A -> Prop) : term326 A f s.
Proof. exact (fun h0 : term294 A s f => @lem5423142 A s f h0). Qed.
Lemma lem5423148 {A : Type'} (s : A -> Prop) : term328 A s.
Proof. exact (fun f : nat -> A => @lem5423143 A f s). Qed.
Lemma lem5423153 {A : Type'} : term338 A.
Proof. exact (fun s : A -> Prop => @lem5423148 A s). Qed.
Lemma lem5423154 {A : Type'} : term337 A.
Proof. exact (EQ_MP (@lem5420831 A) (@lem5423153 A)). Qed.
Lemma lem5423155 {A : Type'} (s : A -> Prop) : term688 A s.
Proof. exact (@lem5423154 A s). Qed.
Lemma lem5423156 {A : Type'} (s : A -> Prop) : (term688 A s) = (term329 A s).
Proof. exact (eq_refl (term688 A s)). Qed.
Lemma lem5423157 {A : Type'} (s : A -> Prop) : term329 A s.
Proof. exact (EQ_MP (@lem5423156 A s) (@lem5423155 A s)). Qed.
Lemma lem5423159 {A : Type'} (s : A -> Prop) : term329 A s.
Proof. exact (@lem5420511 A s (@lem5423157 A s)). Qed.
Lemma lem5423160 {A : Type'} (s : A -> Prop) (h1 : term330 A s) : False.
Proof. exact (@lem5423159 A s (@lem5420495 A s h1)). Qed.
Lemma lem5423161 {A : Type'} (s : A -> Prop) (h1 : term330 A s) : (term330 A s) = False.
Proof. exact (prop_ext (fun h2 : term330 A s => @lem5423160 A s h1) (fun h2 : False => @lem5420495 A s h1)). Qed.
Lemma lem5423162 {A : Type'} (s : A -> Prop) (h1 : term330 A s) : False.
Proof. exact (EQ_MP (@lem5423161 A s h1) (@lem5420495 A s h1)). Qed.
Lemma lem5423163 {A : Type'} (s : A -> Prop) : term329 A s.
Proof. exact (fun h0 : term330 A s => @lem5423162 A s h0). Qed.
Lemma lem5423164 {A : Type'} (s : A -> Prop) : term328 A s.
Proof. exact (EQ_MP (@lem5420494 A s) (@lem5423163 A s)). Qed.
Lemma lem5423165 {A : Type'} (s : A -> Prop) : term256 A s.
Proof. exact (EQ_MP (@lem5420490 A s) (@lem5423164 A s)). Qed.
Lemma lem5423166 {A : Type'} (s : A -> Prop) : term241 A s.
Proof. exact (EQ_MP (@lem5420267 A s) (@lem5423165 A s)). Qed.
Lemma lem5423167 {A : Type'} (s : A -> Prop) : term227 A s.
Proof. exact (@lem5420177 A s (@lem5423166 A s)). Qed.
Lemma lem5423168 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : term226 A s.
Proof. exact (EQ_MP (@lem5420150 A s h1) (@lem5423167 A s)). Qed.
Lemma lem5423169 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : term65 A s.
Proof. exact (@lem5423168 A s h1 (@lem5418356 A s)). Qed.
Lemma lem5423170 {A : Type'} (s : A -> Prop) : term689 A s.
Proof. exact (fun h0 : @FINITE A s => @lem5423169 A s h0). Qed.
Lemma lem5423171 {A : Type'} (s : A -> Prop) : term690 A s.
Proof. exact (conj (@lem5423170 A s) (@lem5419995 A s)). Qed.
Lemma lem5423172 {A : Type'} (s : A -> Prop) : (term690 A s) = ((@FINITE A s) = (term65 A s)).
Proof. exact (@lem32 (@FINITE A s) (term65 A s)). Qed.
Lemma lem5423173 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (term65 A s).
Proof. exact (EQ_MP (@lem5423172 A s) (@lem5423171 A s)). Qed.
Lemma lem5423178 {A : Type'} : term691 A.
Proof. exact (fun s : A -> Prop => @lem5423173 A s). Qed.
