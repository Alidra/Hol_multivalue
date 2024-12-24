Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_SWAP_NUMSEG_term_abbrevs.
Require Import FINITE_NUMSEG_spec.
Require Import NSUM_SWAP_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Lemma lem7047543 (m : nat) : term0 m.
Proof. exact (@lem5329299 m). Qed.
Lemma lem7047544 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem7047545 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem7047544 m) (@lem7047543 m)). Qed.
Lemma lem7047546 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem7047545 m n). Qed.
Lemma lem7047547 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem7047548 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem7047547 m n) (@lem7047546 m n)). Qed.
Lemma lem7047549 (m : nat) (n : nat) : (term3 m n) = ((term3 m n) = True).
Proof. exact (@lem7 (term3 m n)). Qed.
Lemma lem7047551 {A B : Type'} (h1 : term4 A B) : term4 A B.
Proof. exact (h1). Qed.
Lemma lem7047552 {A B : Type'} (f : type1415 A B) (h1 : term4 A B) : term5 A B f.
Proof. exact (@lem7047551 A B h1 f). Qed.
Lemma lem7047553 {A B : Type'} (f : type1415 A B) : (term5 A B f) = (term6 A B f).
Proof. exact (eq_refl (term5 A B f)). Qed.
Lemma lem7047554 {A B : Type'} (f : type1415 A B) (h1 : term4 A B) : term6 A B f.
Proof. exact (EQ_MP (@lem7047553 A B f) (@lem7047552 A B f h1)). Qed.
Lemma lem7047555 {A B : Type'} (f : type1415 A B) (s : A -> Prop) (h1 : term4 A B) : term7 A B f s.
Proof. exact (@lem7047554 A B f h1 s). Qed.
Lemma lem7047556 {A B : Type'} (s : A -> Prop) (f : type1415 A B) : (term7 A B f s) = (term8 A B s f).
Proof. exact (eq_refl (term7 A B f s)). Qed.
Lemma lem7047557 {A B : Type'} (s : A -> Prop) (f : type1415 A B) (h1 : term4 A B) : term8 A B s f.
Proof. exact (EQ_MP (@lem7047556 A B s f) (@lem7047555 A B f s h1)). Qed.
Lemma lem7047558 {A B : Type'} (s : A -> Prop) (f : type1415 A B) (t : B -> Prop) (h1 : term4 A B) : term9 A B s f t.
Proof. exact (@lem7047557 A B s f h1 t). Qed.
Lemma lem7047559 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : type1415 A B) : (term9 A B s f t) = (term10 A B t s f).
Proof. exact (eq_refl (term9 A B s f t)). Qed.
Lemma lem7047560 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : type1415 A B) (h1 : term4 A B) : term10 A B t s f.
Proof. exact (EQ_MP (@lem7047559 A B t s f) (@lem7047558 A B s f t h1)). Qed.
Lemma lem7047561 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term11 A B s t) : term11 A B s t.
Proof. exact (h1). Qed.
Lemma lem7047562 {A B : Type'} (f : type1415 A B) (s : A -> Prop) (t : B -> Prop) (h1 : term4 A B) (h2 : term11 A B s t) : (term12 A B s t f) = (term13 A B t s f).
Proof. exact (@lem7047560 A B t s f h1 (@lem7047561 A B s t h2)). Qed.
Lemma lem7047563 {A B : Type'} (f : type1415 A B) (s : A -> Prop) (t : B -> Prop) (h1 : term11 A B s t) : term14 A B t s f.
Proof. exact (fun h0 : term4 A B => @lem7047562 A B f s t h0 h1). Qed.
Lemma lem7047564 {A B : Type'} (h1 : term4 A B) : term4 A B.
Proof. exact (h1). Qed.
Lemma lem7047565 {A B : Type'} (f : type1415 A B) (s : A -> Prop) (t : B -> Prop) (h1 : term4 A B) (h2 : term11 A B s t) : (term12 A B s t f) = (term13 A B t s f).
Proof. exact (@lem7047563 A B f s t h2 (@lem7047564 A B h1)). Qed.
Lemma lem7047566 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : type1415 A B) (h1 : term4 A B) : term10 A B t s f.
Proof. exact (fun h0 : term11 A B s t => @lem7047565 A B f s t h1 h0). Qed.
Lemma lem7047567 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term4 A B) : term15 A B t s.
Proof. exact (fun f : type1415 A B => @lem7047566 A B t s f h1). Qed.
Lemma lem7047568 {A B : Type'} (t : B -> Prop) (h1 : term4 A B) : term16 A B t.
Proof. exact (fun s : A -> Prop => @lem7047567 A B t s h1). Qed.
Lemma lem7047569 {A B : Type'} (h1 : term4 A B) : term17 A B.
Proof. exact (fun t : B -> Prop => @lem7047568 A B t h1). Qed.
Lemma lem7047570 {A B : Type'} : term18 A B.
Proof. exact (fun h0 : term4 A B => @lem7047569 A B h0). Qed.
Lemma lem7047571 {A B : Type'} : term17 A B.
Proof. exact (@lem7047570 A B (@lem6961567 A B)). Qed.
Lemma lem7047572 {A B : Type'} (t : B -> Prop) : term19 A B t.
Proof. exact (@lem7047571 A B t). Qed.
Lemma lem7047573 {A B : Type'} (t : B -> Prop) : (term19 A B t) = (term16 A B t).
Proof. exact (eq_refl (term19 A B t)). Qed.
Lemma lem7047574 {A B : Type'} (t : B -> Prop) : term16 A B t.
Proof. exact (EQ_MP (@lem7047573 A B t) (@lem7047572 A B t)). Qed.
Lemma lem7047575 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term20 A B t s.
Proof. exact (@lem7047574 A B t s). Qed.
Lemma lem7047576 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term20 A B t s) = (term15 A B t s).
Proof. exact (eq_refl (term20 A B t s)). Qed.
Lemma lem7047577 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term15 A B t s.
Proof. exact (EQ_MP (@lem7047576 A B t s) (@lem7047575 A B t s)). Qed.
Lemma lem7047578 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : type1415 A B) : term21 A B t s f.
Proof. exact (@lem7047577 A B t s f). Qed.
Lemma lem7047579 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : type1415 A B) : (term21 A B t s f) = (term10 A B t s f).
Proof. exact (eq_refl (term21 A B t s f)). Qed.
Lemma lem7047582 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : type1415 A B) : term10 A B t s f.
Proof. exact (EQ_MP (@lem7047579 A B t s f) (@lem7047578 A B t s f)). Qed.
Lemma lem7047583 (t : nat -> Prop) (s : nat -> Prop) (f : type1606) : term22 t s f.
Proof. exact (@lem7047582 nat nat t s f). Qed.
Lemma lem7047584 (c : nat) (d : nat) (a : nat) (b : nat) (f : type1606) : term23 c d a b f.
Proof. exact (@lem7047583 (dotdot c d) (dotdot a b) f). Qed.
Lemma lem7047588 (m : nat) (n : nat) : (term3 m n) = True.
Proof. exact (EQ_MP (@lem7047549 m n) (@lem7047548 m n)). Qed.
Lemma lem7047589 (a : nat) (b : nat) : (term3 a b) = True.
Proof. exact (@lem7047588 a b). Qed.
Lemma lem7047590 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7047591 (a : nat) (b : nat) : (term24 a b) = (and True).
Proof. exact (MK_COMB (@lem7047590) (@lem7047589 a b)). Qed.
Lemma lem7047593 (m : nat) (n : nat) : (term3 m n) = True.
Proof. exact (EQ_MP (@lem7047549 m n) (@lem7047548 m n)). Qed.
Lemma lem7047594 (c : nat) (d : nat) : (term3 c d) = True.
Proof. exact (@lem7047593 c d). Qed.
Lemma lem7047595 (a : nat) (b : nat) (c : nat) (d : nat) : (term25 a b c d) = (True /\ True).
Proof. exact (MK_COMB (@lem7047591 a b) (@lem7047594 c d)). Qed.
Lemma lem7047597 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7047598 : (True /\ True) = True.
Proof. exact (@lem7047597 True). Qed.
Lemma lem7047599 (a : nat) (b : nat) (c : nat) (d : nat) : (term25 a b c d) = True.
Proof. exact (TRANS (@lem7047595 a b c d) (@lem7047598)). Qed.
Lemma lem7047600 (a : nat) (b : nat) (c : nat) (d : nat) : True = (term25 a b c d).
Proof. exact (SYM (@lem7047599 a b c d)). Qed.
Lemma lem7047601 (a : nat) (b : nat) (c : nat) (d : nat) : term25 a b c d.
Proof. exact (EQ_MP (@lem7047600 a b c d) (@lem0)). Qed.
Lemma lem7047602 (c : nat) (d : nat) (a : nat) (b : nat) (f : type1606) : (term26 a b c d f) = (term27 c d a b f).
Proof. exact (@lem7047584 c d a b f (@lem7047601 a b c d)). Qed.
Lemma lem7047607 (c : nat) (d : nat) (a : nat) (b : nat) : term28 c d a b.
Proof. exact (fun f : type1606 => @lem7047602 c d a b f). Qed.
Lemma lem7047612 (c : nat) (a : nat) (b : nat) : term29 c a b.
Proof. exact (fun d : nat => @lem7047607 c d a b). Qed.
Lemma lem7047617 (a : nat) (b : nat) : term30 a b.
Proof. exact (fun c : nat => @lem7047612 c a b). Qed.
Lemma lem7047622 (a : nat) : term31 a.
Proof. exact (fun b : nat => @lem7047617 a b). Qed.
Lemma lem7047627 : term32.
Proof. exact (fun a : nat => @lem7047622 a). Qed.
