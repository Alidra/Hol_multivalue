Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_REFLECT_term_abbrevs.
Require Import ITERATE_REFLECT_spec.
Require Import MONOIDAL_ADD_spec.
Require Import thm0_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm6920357_spec.
Require Import thm6920371_spec.
Require Import thm6920431_spec.
Require Import thm6921992_spec.
Lemma lem7052482 {A : Type'} (op : type1400 A) : term0 A op.
Proof. exact (@lem6377849 A op). Qed.
Lemma lem7052483 {A : Type'} (op : type1400 A) : (term0 A op) = (term1 A op).
Proof. exact (eq_refl (term0 A op)). Qed.
Lemma lem7052486 {A : Type'} (op : type1400 A) : term1 A op.
Proof. exact (EQ_MP (@lem7052483 A op) (@lem7052482 A op)). Qed.
Lemma lem7052487 (op : type1606) : term2 op.
Proof. exact (@lem7052486 nat op). Qed.
Lemma lem7052488 : term3.
Proof. exact (@lem7052487 Nat.add). Qed.
Lemma lem7052489 : term4.
Proof. exact (@lem7052488 (@lem6924403)). Qed.
Lemma lem7052490 (x : nat -> nat) : term5 x.
Proof. exact (@lem7052489 x). Qed.
Lemma lem7052491 (x : nat -> nat) : (term5 x) = (term6 x).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem7052492 (x : nat -> nat) : term6 x.
Proof. exact (EQ_MP (@lem7052491 x) (@lem7052490 x)). Qed.
Lemma lem7052493 (x : nat -> nat) (m : nat) : term7 x m.
Proof. exact (@lem7052492 x m). Qed.
Lemma lem7052494 (m : nat) (x : nat -> nat) : (term7 x m) = (term8 m x).
Proof. exact (eq_refl (term7 x m)). Qed.
Lemma lem7052495 (m : nat) (x : nat -> nat) : term8 m x.
Proof. exact (EQ_MP (@lem7052494 m x) (@lem7052493 x m)). Qed.
Lemma lem7052496 (m : nat) (x : nat -> nat) (n : nat) : term9 m x n.
Proof. exact (@lem7052495 m x n). Qed.
Lemma lem7052497 (m : nat) (x : nat -> nat) (n : nat) : (term9 m x n) = ((term10 m n x) = (term11 m x n)).
Proof. exact (eq_refl (term9 m x n)). Qed.
Lemma lem7052502 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem7052503 : (@nsum nat) = (@iterate nat nat Nat.add).
Proof. exact (@lem7052502 nat). Qed.
Lemma lem7052504 (m : nat) (n : nat) : (dotdot m n) = (dotdot m n).
Proof. exact (eq_refl (dotdot m n)). Qed.
Lemma lem7052505 (m : nat) (n : nat) : (term12 m n) = (term13 m n).
Proof. exact (MK_COMB (@lem7052503) (@lem7052504 m n)). Qed.
Lemma lem7052506 (x : nat -> nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7052507 (m : nat) (n : nat) (x : nat -> nat) : (term14 m n x) = (term10 m n x).
Proof. exact (MK_COMB (@lem7052505 m n) (@lem7052506 x)). Qed.
Lemma lem7052508 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7052509 (m : nat) (n : nat) (x : nat -> nat) : (term15 m n x) = (term16 m n x).
Proof. exact (MK_COMB (@lem7052508) (@lem7052507 m n x)). Qed.
Lemma lem7052511 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem7052512 : (@nsum nat) = (@iterate nat nat Nat.add).
Proof. exact (@lem7052511 nat). Qed.
Lemma lem7052513 (n : nat) (m : nat) : (term17 n m) = (term17 n m).
Proof. exact (eq_refl (term17 n m)). Qed.
Lemma lem7052514 (n : nat) (m : nat) : (term18 n m) = (term19 n m).
Proof. exact (MK_COMB (@lem7052512) (@lem7052513 n m)). Qed.
Lemma lem7052515 (x : nat -> nat) (n : nat) : (term20 x n) = (term20 x n).
Proof. exact (eq_refl (term20 x n)). Qed.
Lemma lem7052516 (m : nat) (x : nat -> nat) (n : nat) : (term21 m x n) = (term22 m x n).
Proof. exact (MK_COMB (@lem7052514 n m) (@lem7052515 x n)). Qed.
Lemma lem7052517 (n : nat) (m : nat) : (term23 n m) = (term23 n m).
Proof. exact (eq_refl (term23 n m)). Qed.
Lemma lem7052518 (m : nat) (x : nat -> nat) (n : nat) : (term24 m x n) = (term25 m x n).
Proof. exact (MK_COMB (@lem7052517 n m) (@lem7052516 m x n)). Qed.
Lemma lem7052519 (m : nat) (x : nat -> nat) (n : nat) : ((term14 m n x) = (term24 m x n)) = ((term10 m n x) = (term25 m x n)).
Proof. exact (MK_COMB (@lem7052509 m n x) (@lem7052518 m x n)). Qed.
Lemma lem7052522 (m : nat) (x : nat -> nat) (n : nat) : ((term10 m n x) = (term25 m x n)) = ((term14 m n x) = (term24 m x n)).
Proof. exact (SYM (@lem7052519 m x n)). Qed.
Lemma lem7052524 (m : nat) (x : nat -> nat) (n : nat) : (term10 m n x) = (term11 m x n).
Proof. exact (EQ_MP (@lem7052497 m x n) (@lem7052496 m x n)). Qed.
Lemma lem7052525 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7052526 (m : nat) (x : nat -> nat) (n : nat) : (term16 m n x) = (term26 m x n).
Proof. exact (MK_COMB (@lem7052525) (@lem7052524 m x n)). Qed.
Lemma lem7052527 (m : nat) (x : nat -> nat) (n : nat) : (term25 m x n) = (term25 m x n).
Proof. exact (eq_refl (term25 m x n)). Qed.
Lemma lem7052528 (m : nat) (x : nat -> nat) (n : nat) : ((term10 m n x) = (term25 m x n)) = ((term11 m x n) = (term25 m x n)).
Proof. exact (MK_COMB (@lem7052526 m x n) (@lem7052527 m x n)). Qed.
Lemma lem7052529 (m : nat) (x : nat -> nat) (n : nat) : ((term11 m x n) = (term25 m x n)) = ((term10 m n x) = (term25 m x n)).
Proof. exact (SYM (@lem7052528 m x n)). Qed.
Lemma lem7052533 : (@neutral nat Nat.add) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem6920431) (@lem6921992)). Qed.
Lemma lem7052534 (n : nat) (m : nat) : (term27 n m) = (term27 n m).
Proof. exact (eq_refl (term27 n m)). Qed.
Lemma lem7052535 (n : nat) (m : nat) : (term28 n m) = (term23 n m).
Proof. exact (MK_COMB (@lem7052534 n m) (@lem7052533)). Qed.
Lemma lem7052536 (m : nat) (x : nat -> nat) (n : nat) : (term22 m x n) = (term22 m x n).
Proof. exact (eq_refl (term22 m x n)). Qed.
Lemma lem7052537 (m : nat) (x : nat -> nat) (n : nat) : (term11 m x n) = (term25 m x n).
Proof. exact (MK_COMB (@lem7052535 n m) (@lem7052536 m x n)). Qed.
Lemma lem7052538 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7052539 (m : nat) (x : nat -> nat) (n : nat) : (term26 m x n) = (term29 m x n).
Proof. exact (MK_COMB (@lem7052538) (@lem7052537 m x n)). Qed.
Lemma lem7052540 (m : nat) (x : nat -> nat) (n : nat) : (term25 m x n) = (term25 m x n).
Proof. exact (eq_refl (term25 m x n)). Qed.
Lemma lem7052541 (m : nat) (x : nat -> nat) (n : nat) : ((term11 m x n) = (term25 m x n)) = ((term25 m x n) = (term25 m x n)).
Proof. exact (MK_COMB (@lem7052539 m x n) (@lem7052540 m x n)). Qed.
Lemma lem7052543 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7052544 (x : nat) : (x = x) = True.
Proof. exact (@lem7052543 nat x). Qed.
Lemma lem7052545 (m : nat) (x : nat -> nat) (n : nat) : ((term25 m x n) = (term25 m x n)) = True.
Proof. exact (@lem7052544 (term25 m x n)). Qed.
Lemma lem7052546 (m : nat) (x : nat -> nat) (n : nat) : ((term11 m x n) = (term25 m x n)) = True.
Proof. exact (TRANS (@lem7052541 m x n) (@lem7052545 m x n)). Qed.
Lemma lem7052547 (m : nat) (x : nat -> nat) (n : nat) : True = ((term11 m x n) = (term25 m x n)).
Proof. exact (SYM (@lem7052546 m x n)). Qed.
Lemma lem7052548 (m : nat) (x : nat -> nat) (n : nat) : (term11 m x n) = (term25 m x n).
Proof. exact (EQ_MP (@lem7052547 m x n) (@lem0)). Qed.
Lemma lem7052549 (m : nat) (x : nat -> nat) (n : nat) : (term10 m n x) = (term25 m x n).
Proof. exact (EQ_MP (@lem7052529 m x n) (@lem7052548 m x n)). Qed.
Lemma lem7052550 (m : nat) (x : nat -> nat) (n : nat) : (term14 m n x) = (term24 m x n).
Proof. exact (EQ_MP (@lem7052522 m x n) (@lem7052549 m x n)). Qed.
Lemma lem7052555 (m : nat) (x : nat -> nat) : term30 m x.
Proof. exact (fun n : nat => @lem7052550 m x n). Qed.
Lemma lem7052560 (x : nat -> nat) : term31 x.
Proof. exact (fun m : nat => @lem7052555 m x). Qed.
Lemma lem7052565 : term32.
Proof. exact (fun x : nat -> nat => @lem7052560 x). Qed.
