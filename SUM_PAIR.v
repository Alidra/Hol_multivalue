Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_PAIR_term_abbrevs.
Require Import ITERATE_PAIR_spec.
Require Import MONOIDAL_REAL_ADD_spec.
Require Import thm0_spec.
Require Import thm1823_spec.
Require Import thm7064097_spec.
Require Import thm7064111_spec.
Lemma lem7226366 {_123774 : Type'} (op : type1400 _123774) : term0 _123774 op.
Proof. exact (@lem6220935 _123774 op). Qed.
Lemma lem7226367 {_123774 : Type'} (op : type1400 _123774) : (term0 _123774 op) = (term1 _123774 op).
Proof. exact (eq_refl (term0 _123774 op)). Qed.
Lemma lem7226370 {_123774 : Type'} (op : type1400 _123774) : term1 _123774 op.
Proof. exact (EQ_MP (@lem7226367 _123774 op) (@lem7226366 _123774 op)). Qed.
Lemma lem7226371 (op : type1627) : term2 op.
Proof. exact (@lem7226370 real op). Qed.
Lemma lem7226372 : term3.
Proof. exact (@lem7226371 real_add). Qed.
Lemma lem7226373 : term4.
Proof. exact (@lem7226372 (@lem7067132)). Qed.
Lemma lem7226405 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7226406 : (@sum nat) = (@iterate real nat real_add).
Proof. exact (@lem7226405 nat). Qed.
Lemma lem7226407 (m : nat) (n : nat) : (term5 m n) = (term5 m n).
Proof. exact (eq_refl (term5 m n)). Qed.
Lemma lem7226408 (m : nat) (n : nat) : (term6 m n) = (term7 m n).
Proof. exact (MK_COMB (@lem7226406) (@lem7226407 m n)). Qed.
Lemma lem7226409 (f : nat -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7226410 (m : nat) (n : nat) (f : nat -> real) : (term8 m n f) = (term9 m n f).
Proof. exact (MK_COMB (@lem7226408 m n) (@lem7226409 f)). Qed.
Lemma lem7226411 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7226412 (m : nat) (n : nat) (f : nat -> real) : (term10 m n f) = (term11 m n f).
Proof. exact (MK_COMB (@lem7226411) (@lem7226410 m n f)). Qed.
Lemma lem7226414 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7226415 : (@sum nat) = (@iterate real nat real_add).
Proof. exact (@lem7226414 nat). Qed.
Lemma lem7226416 (m : nat) (n : nat) : (dotdot m n) = (dotdot m n).
Proof. exact (eq_refl (dotdot m n)). Qed.
Lemma lem7226417 (m : nat) (n : nat) : (term12 m n) = (term13 m n).
Proof. exact (MK_COMB (@lem7226415) (@lem7226416 m n)). Qed.
Lemma lem7226418 (f : nat -> real) : (term14 f) = (term14 f).
Proof. exact (eq_refl (term14 f)). Qed.
Lemma lem7226419 (m : nat) (n : nat) (f : nat -> real) : (term15 m n f) = (term16 m n f).
Proof. exact (MK_COMB (@lem7226417 m n) (@lem7226418 f)). Qed.
Lemma lem7226420 (m : nat) (n : nat) (f : nat -> real) : ((term8 m n f) = (term15 m n f)) = ((term9 m n f) = (term16 m n f)).
Proof. exact (MK_COMB (@lem7226412 m n f) (@lem7226419 m n f)). Qed.
Lemma lem7226423 (m : nat) (f : nat -> real) : (term17 m f) = (term18 m f).
Proof. exact (fun_ext (fun n : nat => @lem7226420 m n f)). Qed.
Lemma lem7226424 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7226425 (m : nat) (f : nat -> real) : (term19 m f) = (term20 m f).
Proof. exact (MK_COMB (@lem7226424) (@lem7226423 m f)). Qed.
Lemma lem7226430 (f : nat -> real) : (term21 f) = (term22 f).
Proof. exact (fun_ext (fun m : nat => @lem7226425 m f)). Qed.
Lemma lem7226431 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7226432 (f : nat -> real) : (term23 f) = (term24 f).
Proof. exact (MK_COMB (@lem7226431) (@lem7226430 f)). Qed.
Lemma lem7226437 : term25 = term26.
Proof. exact (fun_ext (fun f : nat -> real => @lem7226432 f)). Qed.
Lemma lem7226438 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7226439 : term27 = term4.
Proof. exact (MK_COMB (@lem7226438) (@lem7226437)). Qed.
Lemma lem7226444 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem7226445 : term29 = term30.
Proof. exact (MK_COMB (@lem7226444) (@lem7226439)). Qed.
Lemma lem7226447 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem7226448 : term30 = True.
Proof. exact (@lem7226447 term4). Qed.
Lemma lem7226449 : term29 = True.
Proof. exact (TRANS (@lem7226445) (@lem7226448)). Qed.
Lemma lem7226450 : True = term29.
Proof. exact (SYM (@lem7226449)). Qed.
Lemma lem7226451 : term29.
Proof. exact (EQ_MP (@lem7226450) (@lem0)). Qed.
Lemma lem7226452 : term27.
Proof. exact (@lem7226451 (@lem7226373)). Qed.
