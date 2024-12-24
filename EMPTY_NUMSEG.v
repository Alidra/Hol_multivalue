Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EMPTY_NUMSEG_term_abbrevs.
Require Import NUMSEG_EMPTY_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1823_spec.
Lemma lem5376448 (m : nat) : term0 m.
Proof. exact (@lem5376447 m). Qed.
Lemma lem5376449 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem5376450 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem5376449 m) (@lem5376448 m)). Qed.
Lemma lem5376451 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem5376450 m n). Qed.
Lemma lem5376452 (n : nat) (m : nat) : (term2 m n) = (((dotdot m n) = (@EMPTY nat)) = (Peano.lt n m)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem5376465 (n : nat) (m : nat) : ((dotdot m n) = (@EMPTY nat)) = (Peano.lt n m).
Proof. exact (EQ_MP (@lem5376452 n m) (@lem5376451 m n)). Qed.
Lemma lem5376466 (n : nat) (m : nat) : (term3 n m) = (term3 n m).
Proof. exact (eq_refl (term3 n m)). Qed.
Lemma lem5376467 (n : nat) (m : nat) : (term4 m n) = (term5 n m).
Proof. exact (MK_COMB (@lem5376466 n m) (@lem5376465 n m)). Qed.
Lemma lem5376469 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem5376470 (n : nat) (m : nat) : (term5 n m) = True.
Proof. exact (@lem5376469 (Peano.lt n m)). Qed.
Lemma lem5376471 (m : nat) (n : nat) : (term4 m n) = True.
Proof. exact (TRANS (@lem5376467 n m) (@lem5376470 n m)). Qed.
Lemma lem5376472 (m : nat) : (term6 m) = term7.
Proof. exact (fun_ext (fun n : nat => @lem5376471 m n)). Qed.
Lemma lem5376473 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5376474 (m : nat) : (term8 m) = term9.
Proof. exact (MK_COMB (@lem5376473) (@lem5376472 m)). Qed.
Lemma lem5376476 {A : Type'} (t : Prop) : (term10 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5376477 (t : Prop) : (term11 t) = t.
Proof. exact (@lem5376476 nat t). Qed.
Lemma lem5376478 : term9 = True.
Proof. exact (@lem5376477 True). Qed.
Lemma lem5376479 (m : nat) : (term8 m) = True.
Proof. exact (TRANS (@lem5376474 m) (@lem5376478)). Qed.
Lemma lem5376480 : term12 = term7.
Proof. exact (fun_ext (fun m : nat => @lem5376479 m)). Qed.
Lemma lem5376481 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5376482 : term13 = term9.
Proof. exact (MK_COMB (@lem5376481) (@lem5376480)). Qed.
Lemma lem5376484 {A : Type'} (t : Prop) : (term10 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5376485 (t : Prop) : (term11 t) = t.
Proof. exact (@lem5376484 nat t). Qed.
Lemma lem5376486 : term9 = True.
Proof. exact (@lem5376485 True). Qed.
Lemma lem5376487 : term13 = True.
Proof. exact (TRANS (@lem5376482) (@lem5376486)). Qed.
Lemma lem5376488 : True = term13.
Proof. exact (SYM (@lem5376487)). Qed.
Lemma lem5376489 : term13.
Proof. exact (EQ_MP (@lem5376488) (@lem0)). Qed.
