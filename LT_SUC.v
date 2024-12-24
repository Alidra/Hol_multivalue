Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LT_SUC_term_abbrevs.
Require Import LE_SUC_LT_spec.
Require Import LT_SUC_LE_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem91361 (m : nat) : term0 m.
Proof. exact (@lem91144 m). Qed.
Lemma lem91362 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem91363 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem91362 m) (@lem91361 m)). Qed.
Lemma lem91364 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem91363 m n). Qed.
Lemma lem91365 (m : nat) (n : nat) : (term2 m n) = ((term3 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem91367 (m : nat) : term4 m.
Proof. exact (@lem91305 m). Qed.
Lemma lem91368 (m : nat) : (term4 m) = (term5 m).
Proof. exact (eq_refl (term4 m)). Qed.
Lemma lem91369 (m : nat) : term5 m.
Proof. exact (EQ_MP (@lem91368 m) (@lem91367 m)). Qed.
Lemma lem91370 (m : nat) (n : nat) : term6 m n.
Proof. exact (@lem91369 m n). Qed.
Lemma lem91371 (m : nat) (n : nat) : (term6 m n) = ((term7 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term6 m n)). Qed.
Lemma lem91384 (m : nat) (n : nat) : (term7 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem91371 m n) (@lem91370 m n)). Qed.
Lemma lem91385 (m : nat) (n : nat) : (term8 m n) = (term3 m n).
Proof. exact (@lem91384 (S m) n). Qed.
Lemma lem91387 (m : nat) (n : nat) : (term3 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem91365 m n) (@lem91364 m n)). Qed.
Lemma lem91388 (m : nat) (n : nat) : (term8 m n) = (Peano.lt m n).
Proof. exact (TRANS (@lem91385 m n) (@lem91387 m n)). Qed.
Lemma lem91389 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem91390 (m : nat) (n : nat) : (term9 m n) = (term10 m n).
Proof. exact (MK_COMB (@lem91389) (@lem91388 m n)). Qed.
Lemma lem91391 (m : nat) (n : nat) : (Peano.lt m n) = (Peano.lt m n).
Proof. exact (eq_refl (Peano.lt m n)). Qed.
Lemma lem91392 (m : nat) (n : nat) : ((term8 m n) = (Peano.lt m n)) = ((Peano.lt m n) = (Peano.lt m n)).
Proof. exact (MK_COMB (@lem91390 m n) (@lem91391 m n)). Qed.
Lemma lem91394 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem91395 (x : Prop) : (x = x) = True.
Proof. exact (@lem91394 Prop x). Qed.
Lemma lem91396 (m : nat) (n : nat) : ((Peano.lt m n) = (Peano.lt m n)) = True.
Proof. exact (@lem91395 (Peano.lt m n)). Qed.
Lemma lem91397 (m : nat) (n : nat) : ((term8 m n) = (Peano.lt m n)) = True.
Proof. exact (TRANS (@lem91392 m n) (@lem91396 m n)). Qed.
Lemma lem91398 (m : nat) : (term11 m) = term12.
Proof. exact (fun_ext (fun n : nat => @lem91397 m n)). Qed.
Lemma lem91399 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem91400 (m : nat) : (term13 m) = term14.
Proof. exact (MK_COMB (@lem91399) (@lem91398 m)). Qed.
Lemma lem91402 {A : Type'} (t : Prop) : (term15 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem91403 (t : Prop) : (term16 t) = t.
Proof. exact (@lem91402 nat t). Qed.
Lemma lem91404 : term14 = True.
Proof. exact (@lem91403 True). Qed.
Lemma lem91405 (m : nat) : (term13 m) = True.
Proof. exact (TRANS (@lem91400 m) (@lem91404)). Qed.
Lemma lem91406 : term17 = term12.
Proof. exact (fun_ext (fun m : nat => @lem91405 m)). Qed.
Lemma lem91407 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem91408 : term18 = term14.
Proof. exact (MK_COMB (@lem91407) (@lem91406)). Qed.
Lemma lem91410 {A : Type'} (t : Prop) : (term15 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem91411 (t : Prop) : (term16 t) = t.
Proof. exact (@lem91410 nat t). Qed.
Lemma lem91412 : term14 = True.
Proof. exact (@lem91411 True). Qed.
Lemma lem91413 : term18 = True.
Proof. exact (TRANS (@lem91408) (@lem91412)). Qed.
Lemma lem91414 : True = term18.
Proof. exact (SYM (@lem91413)). Qed.
Lemma lem91415 : term18.
Proof. exact (EQ_MP (@lem91414) (@lem0)). Qed.
