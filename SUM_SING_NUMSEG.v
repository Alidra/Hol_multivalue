Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_SING_NUMSEG_term_abbrevs.
Require Import NUMSEG_SING_spec.
Require Import SUM_SING_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem7221509 (n : nat) : term0 n.
Proof. exact (@lem5374366 n). Qed.
Lemma lem7221510 (n : nat) : (term0 n) = ((dotdot n n) = (@INSERT nat n (@EMPTY nat))).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem7221512 {_133036 : Type'} (f : _133036 -> real) : term1 _133036 f.
Proof. exact (@lem7123532 _133036 f). Qed.
Lemma lem7221513 {_133036 : Type'} (f : _133036 -> real) : (term1 _133036 f) = (term2 _133036 f).
Proof. exact (eq_refl (term1 _133036 f)). Qed.
Lemma lem7221514 {_133036 : Type'} (f : _133036 -> real) : term2 _133036 f.
Proof. exact (EQ_MP (@lem7221513 _133036 f) (@lem7221512 _133036 f)). Qed.
Lemma lem7221515 {_133036 : Type'} (f : _133036 -> real) (x : _133036) : term3 _133036 f x.
Proof. exact (@lem7221514 _133036 f x). Qed.
Lemma lem7221516 {_133036 : Type'} (f : _133036 -> real) (x : _133036) : (term3 _133036 f x) = ((term4 _133036 x f) = (f x)).
Proof. exact (eq_refl (term3 _133036 f x)). Qed.
Lemma lem7221529 (n : nat) : (dotdot n n) = (@INSERT nat n (@EMPTY nat)).
Proof. exact (EQ_MP (@lem7221510 n) (@lem7221509 n)). Qed.
Lemma lem7221530 : (@sum nat) = (@sum nat).
Proof. exact (eq_refl (@sum nat)). Qed.
Lemma lem7221531 (n : nat) : (term5 n) = (term6 n).
Proof. exact (MK_COMB (@lem7221530) (@lem7221529 n)). Qed.
Lemma lem7221532 (f : nat -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7221533 (n : nat) (f : nat -> real) : (term7 n f) = (term8 n f).
Proof. exact (MK_COMB (@lem7221531 n) (@lem7221532 f)). Qed.
Lemma lem7221535 {_133036 : Type'} (f : _133036 -> real) (x : _133036) : (term4 _133036 x f) = (f x).
Proof. exact (EQ_MP (@lem7221516 _133036 f x) (@lem7221515 _133036 f x)). Qed.
Lemma lem7221536 (f : nat -> real) (x : nat) : (term8 x f) = (f x).
Proof. exact (@lem7221535 nat f x). Qed.
Lemma lem7221537 (f : nat -> real) (n : nat) : (term8 n f) = (f n).
Proof. exact (@lem7221536 f n). Qed.
Lemma lem7221538 (f : nat -> real) (n : nat) : (term7 n f) = (f n).
Proof. exact (TRANS (@lem7221533 n f) (@lem7221537 f n)). Qed.
Lemma lem7221539 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7221540 (f : nat -> real) (n : nat) : (term9 n f) = (term10 f n).
Proof. exact (MK_COMB (@lem7221539) (@lem7221538 f n)). Qed.
Lemma lem7221541 (f : nat -> real) (n : nat) : (f n) = (f n).
Proof. exact (eq_refl (f n)). Qed.
Lemma lem7221542 (f : nat -> real) (n : nat) : ((term7 n f) = (f n)) = ((f n) = (f n)).
Proof. exact (MK_COMB (@lem7221540 f n) (@lem7221541 f n)). Qed.
Lemma lem7221544 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7221545 (x : real) : (x = x) = True.
Proof. exact (@lem7221544 real x). Qed.
Lemma lem7221546 (f : nat -> real) (n : nat) : ((f n) = (f n)) = True.
Proof. exact (@lem7221545 (f n)). Qed.
Lemma lem7221547 (f : nat -> real) (n : nat) : ((term7 n f) = (f n)) = True.
Proof. exact (TRANS (@lem7221542 f n) (@lem7221546 f n)). Qed.
Lemma lem7221548 (f : nat -> real) : (term11 f) = term12.
Proof. exact (fun_ext (fun n : nat => @lem7221547 f n)). Qed.
Lemma lem7221549 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7221550 (f : nat -> real) : (term13 f) = term14.
Proof. exact (MK_COMB (@lem7221549) (@lem7221548 f)). Qed.
Lemma lem7221552 {A : Type'} (t : Prop) : (term15 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7221553 (t : Prop) : (term16 t) = t.
Proof. exact (@lem7221552 nat t). Qed.
Lemma lem7221554 : term14 = True.
Proof. exact (@lem7221553 True). Qed.
Lemma lem7221555 (f : nat -> real) : (term13 f) = True.
Proof. exact (TRANS (@lem7221550 f) (@lem7221554)). Qed.
Lemma lem7221556 : term17 = term18.
Proof. exact (fun_ext (fun f : nat -> real => @lem7221555 f)). Qed.
Lemma lem7221557 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7221558 : term19 = term20.
Proof. exact (MK_COMB (@lem7221557) (@lem7221556)). Qed.
Lemma lem7221560 {A : Type'} (t : Prop) : (term15 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7221561 (t : Prop) : (term21 t) = t.
Proof. exact (@lem7221560 (nat -> real) t). Qed.
Lemma lem7221562 : term20 = True.
Proof. exact (@lem7221561 True). Qed.
Lemma lem7221563 : term19 = True.
Proof. exact (TRANS (@lem7221558) (@lem7221562)). Qed.
Lemma lem7221564 : True = term19.
Proof. exact (SYM (@lem7221563)). Qed.
Lemma lem7221565 : term19.
Proof. exact (EQ_MP (@lem7221564) (@lem0)). Qed.
