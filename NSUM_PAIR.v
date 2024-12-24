Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_PAIR_term_abbrevs.
Require Import ITERATE_PAIR_spec.
Require Import MONOIDAL_ADD_spec.
Require Import thm0_spec.
Require Import thm1823_spec.
Require Import thm6920357_spec.
Require Import thm6920371_spec.
Lemma lem7052395 {_123774 : Type'} (op : type1400 _123774) : term0 _123774 op.
Proof. exact (@lem6220935 _123774 op). Qed.
Lemma lem7052396 {_123774 : Type'} (op : type1400 _123774) : (term0 _123774 op) = (term1 _123774 op).
Proof. exact (eq_refl (term0 _123774 op)). Qed.
Lemma lem7052399 {_123774 : Type'} (op : type1400 _123774) : term1 _123774 op.
Proof. exact (EQ_MP (@lem7052396 _123774 op) (@lem7052395 _123774 op)). Qed.
Lemma lem7052400 (op : type1606) : term2 op.
Proof. exact (@lem7052399 nat op). Qed.
Lemma lem7052401 : term3.
Proof. exact (@lem7052400 Nat.add). Qed.
Lemma lem7052402 : term4.
Proof. exact (@lem7052401 (@lem6924403)). Qed.
Lemma lem7052434 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem7052435 : (@nsum nat) = (@iterate nat nat Nat.add).
Proof. exact (@lem7052434 nat). Qed.
Lemma lem7052436 (m : nat) (n : nat) : (term5 m n) = (term5 m n).
Proof. exact (eq_refl (term5 m n)). Qed.
Lemma lem7052437 (m : nat) (n : nat) : (term6 m n) = (term7 m n).
Proof. exact (MK_COMB (@lem7052435) (@lem7052436 m n)). Qed.
Lemma lem7052438 (f : nat -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7052439 (m : nat) (n : nat) (f : nat -> nat) : (term8 m n f) = (term9 m n f).
Proof. exact (MK_COMB (@lem7052437 m n) (@lem7052438 f)). Qed.
Lemma lem7052440 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7052441 (m : nat) (n : nat) (f : nat -> nat) : (term10 m n f) = (term11 m n f).
Proof. exact (MK_COMB (@lem7052440) (@lem7052439 m n f)). Qed.
Lemma lem7052443 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem7052444 : (@nsum nat) = (@iterate nat nat Nat.add).
Proof. exact (@lem7052443 nat). Qed.
Lemma lem7052445 (m : nat) (n : nat) : (dotdot m n) = (dotdot m n).
Proof. exact (eq_refl (dotdot m n)). Qed.
Lemma lem7052446 (m : nat) (n : nat) : (term12 m n) = (term13 m n).
Proof. exact (MK_COMB (@lem7052444) (@lem7052445 m n)). Qed.
Lemma lem7052447 (f : nat -> nat) : (term14 f) = (term14 f).
Proof. exact (eq_refl (term14 f)). Qed.
Lemma lem7052448 (m : nat) (n : nat) (f : nat -> nat) : (term15 m n f) = (term16 m n f).
Proof. exact (MK_COMB (@lem7052446 m n) (@lem7052447 f)). Qed.
Lemma lem7052449 (m : nat) (n : nat) (f : nat -> nat) : ((term8 m n f) = (term15 m n f)) = ((term9 m n f) = (term16 m n f)).
Proof. exact (MK_COMB (@lem7052441 m n f) (@lem7052448 m n f)). Qed.
Lemma lem7052452 (m : nat) (f : nat -> nat) : (term17 m f) = (term18 m f).
Proof. exact (fun_ext (fun n : nat => @lem7052449 m n f)). Qed.
Lemma lem7052453 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7052454 (m : nat) (f : nat -> nat) : (term19 m f) = (term20 m f).
Proof. exact (MK_COMB (@lem7052453) (@lem7052452 m f)). Qed.
Lemma lem7052459 (f : nat -> nat) : (term21 f) = (term22 f).
Proof. exact (fun_ext (fun m : nat => @lem7052454 m f)). Qed.
Lemma lem7052460 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7052461 (f : nat -> nat) : (term23 f) = (term24 f).
Proof. exact (MK_COMB (@lem7052460) (@lem7052459 f)). Qed.
Lemma lem7052466 : term25 = term26.
Proof. exact (fun_ext (fun f : nat -> nat => @lem7052461 f)). Qed.
Lemma lem7052467 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7052468 : term27 = term4.
Proof. exact (MK_COMB (@lem7052467) (@lem7052466)). Qed.
Lemma lem7052473 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem7052474 : term29 = term30.
Proof. exact (MK_COMB (@lem7052473) (@lem7052468)). Qed.
Lemma lem7052476 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem7052477 : term30 = True.
Proof. exact (@lem7052476 term4). Qed.
Lemma lem7052478 : term29 = True.
Proof. exact (TRANS (@lem7052474) (@lem7052477)). Qed.
Lemma lem7052479 : True = term29.
Proof. exact (SYM (@lem7052478)). Qed.
Lemma lem7052480 : term29.
Proof. exact (EQ_MP (@lem7052479) (@lem0)). Qed.
Lemma lem7052481 : term27.
Proof. exact (@lem7052480 (@lem7052402)). Qed.
