Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LE_SUC_term_abbrevs.
Require Import LE_SUC_LT_spec.
Require Import LT_SUC_LE_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem91306 (m : nat) : term0 m.
Proof. exact (@lem91305 m). Qed.
Lemma lem91307 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem91308 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem91307 m) (@lem91306 m)). Qed.
Lemma lem91309 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem91308 m n). Qed.
Lemma lem91310 (m : nat) (n : nat) : (term2 m n) = ((term3 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem91312 (m : nat) : term4 m.
Proof. exact (@lem91144 m). Qed.
Lemma lem91313 (m : nat) : (term4 m) = (term5 m).
Proof. exact (eq_refl (term4 m)). Qed.
Lemma lem91314 (m : nat) : term5 m.
Proof. exact (EQ_MP (@lem91313 m) (@lem91312 m)). Qed.
Lemma lem91315 (m : nat) (n : nat) : term6 m n.
Proof. exact (@lem91314 m n). Qed.
Lemma lem91316 (m : nat) (n : nat) : (term6 m n) = ((term7 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term6 m n)). Qed.
Lemma lem91329 (m : nat) (n : nat) : (term7 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem91316 m n) (@lem91315 m n)). Qed.
Lemma lem91330 (m : nat) (n : nat) : (term8 m n) = (term3 m n).
Proof. exact (@lem91329 m (S n)). Qed.
Lemma lem91332 (m : nat) (n : nat) : (term3 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem91310 m n) (@lem91309 m n)). Qed.
Lemma lem91333 (m : nat) (n : nat) : (term8 m n) = (Peano.le m n).
Proof. exact (TRANS (@lem91330 m n) (@lem91332 m n)). Qed.
Lemma lem91334 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem91335 (m : nat) (n : nat) : (term9 m n) = (term10 m n).
Proof. exact (MK_COMB (@lem91334) (@lem91333 m n)). Qed.
Lemma lem91336 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem91337 (m : nat) (n : nat) : ((term8 m n) = (Peano.le m n)) = ((Peano.le m n) = (Peano.le m n)).
Proof. exact (MK_COMB (@lem91335 m n) (@lem91336 m n)). Qed.
Lemma lem91339 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem91340 (x : Prop) : (x = x) = True.
Proof. exact (@lem91339 Prop x). Qed.
Lemma lem91341 (m : nat) (n : nat) : ((Peano.le m n) = (Peano.le m n)) = True.
Proof. exact (@lem91340 (Peano.le m n)). Qed.
Lemma lem91342 (m : nat) (n : nat) : ((term8 m n) = (Peano.le m n)) = True.
Proof. exact (TRANS (@lem91337 m n) (@lem91341 m n)). Qed.
Lemma lem91343 (m : nat) : (term11 m) = term12.
Proof. exact (fun_ext (fun n : nat => @lem91342 m n)). Qed.
Lemma lem91344 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem91345 (m : nat) : (term13 m) = term14.
Proof. exact (MK_COMB (@lem91344) (@lem91343 m)). Qed.
Lemma lem91347 {A : Type'} (t : Prop) : (term15 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem91348 (t : Prop) : (term16 t) = t.
Proof. exact (@lem91347 nat t). Qed.
Lemma lem91349 : term14 = True.
Proof. exact (@lem91348 True). Qed.
Lemma lem91350 (m : nat) : (term13 m) = True.
Proof. exact (TRANS (@lem91345 m) (@lem91349)). Qed.
Lemma lem91351 : term17 = term12.
Proof. exact (fun_ext (fun m : nat => @lem91350 m)). Qed.
Lemma lem91352 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem91353 : term18 = term14.
Proof. exact (MK_COMB (@lem91352) (@lem91351)). Qed.
Lemma lem91355 {A : Type'} (t : Prop) : (term15 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem91356 (t : Prop) : (term16 t) = t.
Proof. exact (@lem91355 nat t). Qed.
Lemma lem91357 : term14 = True.
Proof. exact (@lem91356 True). Qed.
Lemma lem91358 : term18 = True.
Proof. exact (TRANS (@lem91353) (@lem91357)). Qed.
Lemma lem91359 : True = term18.
Proof. exact (SYM (@lem91358)). Qed.
Lemma lem91360 : term18.
Proof. exact (EQ_MP (@lem91359) (@lem0)). Qed.
