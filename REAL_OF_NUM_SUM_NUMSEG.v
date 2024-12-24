Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_OF_NUM_SUM_NUMSEG_term_abbrevs.
Require Import FINITE_NUMSEG_spec.
Require Import REAL_OF_NUM_SUM_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Lemma lem7226537 (m : nat) : term0 m.
Proof. exact (@lem5329299 m). Qed.
Lemma lem7226538 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem7226539 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem7226538 m) (@lem7226537 m)). Qed.
Lemma lem7226540 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem7226539 m n). Qed.
Lemma lem7226541 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem7226542 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem7226541 m n) (@lem7226540 m n)). Qed.
Lemma lem7226543 (m : nat) (n : nat) : (term3 m n) = ((term3 m n) = True).
Proof. exact (@lem7 (term3 m n)). Qed.
Lemma lem7226545 {_134498 : Type'} (f : _134498 -> nat) : term4 _134498 f.
Proof. exact (@lem7169057 _134498 f). Qed.
Lemma lem7226546 {_134498 : Type'} (f : _134498 -> nat) : (term4 _134498 f) = (term5 _134498 f).
Proof. exact (eq_refl (term4 _134498 f)). Qed.
Lemma lem7226547 {_134498 : Type'} (f : _134498 -> nat) : term5 _134498 f.
Proof. exact (EQ_MP (@lem7226546 _134498 f) (@lem7226545 _134498 f)). Qed.
Lemma lem7226548 {_134498 : Type'} (f : _134498 -> nat) (s : _134498 -> Prop) : term6 _134498 f s.
Proof. exact (@lem7226547 _134498 f s). Qed.
Lemma lem7226549 {_134498 : Type'} (s : _134498 -> Prop) (f : _134498 -> nat) : (term6 _134498 f s) = (term7 _134498 s f).
Proof. exact (eq_refl (term6 _134498 f s)). Qed.
Lemma lem7226550 {_134498 : Type'} (s : _134498 -> Prop) (f : _134498 -> nat) : term7 _134498 s f.
Proof. exact (EQ_MP (@lem7226549 _134498 s f) (@lem7226548 _134498 f s)). Qed.
Lemma lem7226551 {_134498 : Type'} (s : _134498 -> Prop) (h1 : @FINITE _134498 s) : @FINITE _134498 s.
Proof. exact (h1). Qed.
Lemma lem7226552 {_134498 : Type'} (f : _134498 -> nat) (s : _134498 -> Prop) (h1 : @FINITE _134498 s) : (term8 _134498 s f) = (term9 _134498 s f).
Proof. exact (@lem7226550 _134498 s f (@lem7226551 _134498 s h1)). Qed.
Lemma lem7226573 {_134498 : Type'} (s : _134498 -> Prop) (f : _134498 -> nat) : term7 _134498 s f.
Proof. exact (fun h0 : @FINITE _134498 s => @lem7226552 _134498 f s h0). Qed.
Lemma lem7226574 (s : nat -> Prop) (f : nat -> nat) : term10 s f.
Proof. exact (@lem7226573 nat s f). Qed.
Lemma lem7226575 (m : nat) (n : nat) (f : nat -> nat) : term11 m n f.
Proof. exact (@lem7226574 (dotdot m n) f). Qed.
Lemma lem7226577 (m : nat) (n : nat) : (term3 m n) = True.
Proof. exact (EQ_MP (@lem7226543 m n) (@lem7226542 m n)). Qed.
Lemma lem7226578 (m : nat) (n : nat) : True = (term3 m n).
Proof. exact (SYM (@lem7226577 m n)). Qed.
Lemma lem7226579 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem7226578 m n) (@lem0)). Qed.
Lemma lem7226580 (m : nat) (n : nat) (f : nat -> nat) : (term12 m n f) = (term13 m n f).
Proof. exact (@lem7226575 m n f (@lem7226579 m n)). Qed.
Lemma lem7226581 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7226582 (m : nat) (n : nat) (f : nat -> nat) : (term14 m n f) = (term15 m n f).
Proof. exact (MK_COMB (@lem7226581) (@lem7226580 m n f)). Qed.
Lemma lem7226583 (m : nat) (n : nat) (f : nat -> nat) : (term13 m n f) = (term13 m n f).
Proof. exact (eq_refl (term13 m n f)). Qed.
Lemma lem7226584 (m : nat) (n : nat) (f : nat -> nat) : ((term12 m n f) = (term13 m n f)) = ((term13 m n f) = (term13 m n f)).
Proof. exact (MK_COMB (@lem7226582 m n f) (@lem7226583 m n f)). Qed.
Lemma lem7226586 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7226587 (x : real) : (x = x) = True.
Proof. exact (@lem7226586 real x). Qed.
Lemma lem7226588 (m : nat) (n : nat) (f : nat -> nat) : ((term13 m n f) = (term13 m n f)) = True.
Proof. exact (@lem7226587 (term13 m n f)). Qed.
Lemma lem7226591 (m : nat) (n : nat) (f : nat -> nat) : (term16 m n f) = (term16 m n f).
Proof. exact (eq_refl (term16 m n f)). Qed.
Lemma lem7226592 (m : nat) (n : nat) (f : nat -> nat) : (term16 m n f) = (((term13 m n f) = (term13 m n f)) = True).
Proof. exact (eq_refl (term16 m n f)). Qed.
Lemma lem7226593 (m : nat) (n : nat) (f : nat -> nat) : (term17 m n f) = (term17 m n f).
Proof. exact (eq_refl (term17 m n f)). Qed.
Lemma lem7226594 (m : nat) (n : nat) (f : nat -> nat) : ((term16 m n f) = (term16 m n f)) = ((term16 m n f) = (((term13 m n f) = (term13 m n f)) = True)).
Proof. exact (MK_COMB (@lem7226593 m n f) (@lem7226592 m n f)). Qed.
Lemma lem7226595 (m : nat) (n : nat) (f : nat -> nat) : (term16 m n f) = (((term13 m n f) = (term13 m n f)) = True).
Proof. exact (eq_refl (term16 m n f)). Qed.
Lemma lem7226596 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7226597 (m : nat) (n : nat) (f : nat -> nat) : (term17 m n f) = (term18 m n f).
Proof. exact (MK_COMB (@lem7226596) (@lem7226595 m n f)). Qed.
Lemma lem7226598 (m : nat) (n : nat) (f : nat -> nat) : (((term13 m n f) = (term13 m n f)) = True) = (((term13 m n f) = (term13 m n f)) = True).
Proof. exact (eq_refl (((term13 m n f) = (term13 m n f)) = True)). Qed.
Lemma lem7226599 (m : nat) (n : nat) (f : nat -> nat) : ((term16 m n f) = (((term13 m n f) = (term13 m n f)) = True)) = ((((term13 m n f) = (term13 m n f)) = True) = (((term13 m n f) = (term13 m n f)) = True)).
Proof. exact (MK_COMB (@lem7226597 m n f) (@lem7226598 m n f)). Qed.
Lemma lem7226600 (m : nat) (n : nat) (f : nat -> nat) : ((term16 m n f) = (term16 m n f)) = ((((term13 m n f) = (term13 m n f)) = True) = (((term13 m n f) = (term13 m n f)) = True)).
Proof. exact (TRANS (@lem7226594 m n f) (@lem7226599 m n f)). Qed.
Lemma lem7226601 (m : nat) (n : nat) (f : nat -> nat) : (((term13 m n f) = (term13 m n f)) = True) = (((term13 m n f) = (term13 m n f)) = True).
Proof. exact (EQ_MP (@lem7226600 m n f) (@lem7226591 m n f)). Qed.
Lemma lem7226602 (m : nat) (n : nat) (f : nat -> nat) : ((term13 m n f) = (term13 m n f)) = True.
Proof. exact (EQ_MP (@lem7226601 m n f) (@lem7226588 m n f)). Qed.
Lemma lem7226603 (m : nat) (n : nat) (f : nat -> nat) : ((term12 m n f) = (term13 m n f)) = True.
Proof. exact (TRANS (@lem7226584 m n f) (@lem7226602 m n f)). Qed.
Lemma lem7226604 (m : nat) (f : nat -> nat) : (term19 m f) = term20.
Proof. exact (fun_ext (fun n : nat => @lem7226603 m n f)). Qed.
Lemma lem7226605 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7226606 (m : nat) (f : nat -> nat) : (term21 m f) = term22.
Proof. exact (MK_COMB (@lem7226605) (@lem7226604 m f)). Qed.
Lemma lem7226608 {A : Type'} (t : Prop) : (term23 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7226609 (t : Prop) : (term24 t) = t.
Proof. exact (@lem7226608 nat t). Qed.
Lemma lem7226610 : term22 = True.
Proof. exact (@lem7226609 True). Qed.
Lemma lem7226611 (m : nat) (f : nat -> nat) : (term21 m f) = True.
Proof. exact (TRANS (@lem7226606 m f) (@lem7226610)). Qed.
Lemma lem7226612 (f : nat -> nat) : (term25 f) = term20.
Proof. exact (fun_ext (fun m : nat => @lem7226611 m f)). Qed.
Lemma lem7226613 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7226614 (f : nat -> nat) : (term26 f) = term22.
Proof. exact (MK_COMB (@lem7226613) (@lem7226612 f)). Qed.
Lemma lem7226616 {A : Type'} (t : Prop) : (term23 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7226617 (t : Prop) : (term24 t) = t.
Proof. exact (@lem7226616 nat t). Qed.
Lemma lem7226618 : term22 = True.
Proof. exact (@lem7226617 True). Qed.
Lemma lem7226619 (f : nat -> nat) : (term26 f) = True.
Proof. exact (TRANS (@lem7226614 f) (@lem7226618)). Qed.
Lemma lem7226620 : term27 = term28.
Proof. exact (fun_ext (fun f : nat -> nat => @lem7226619 f)). Qed.
Lemma lem7226621 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7226622 : term29 = term30.
Proof. exact (MK_COMB (@lem7226621) (@lem7226620)). Qed.
Lemma lem7226624 {A : Type'} (t : Prop) : (term23 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7226625 (t : Prop) : (term31 t) = t.
Proof. exact (@lem7226624 (nat -> nat) t). Qed.
Lemma lem7226626 : term30 = True.
Proof. exact (@lem7226625 True). Qed.
Lemma lem7226627 : term29 = True.
Proof. exact (TRANS (@lem7226622) (@lem7226626)). Qed.
Lemma lem7226628 : True = term29.
Proof. exact (SYM (@lem7226627)). Qed.
Lemma lem7226629 : term29.
Proof. exact (EQ_MP (@lem7226628) (@lem0)). Qed.
