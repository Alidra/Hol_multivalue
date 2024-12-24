Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_ADD_SYM_term_abbrevs.
Require Import ADD_SYM_spec.
Require Import NADD_EQ_REFL_spec.
Require Import nadd_add_spec.
Require Import thm0_spec.
Require Import thm7_spec.
Lemma lem1274425 (x : nadd) : term0 x.
Proof. exact (@lem1267990 x). Qed.
Lemma lem1274426 (x : nadd) : (term0 x) = (nadd_eq x x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1274427 (x : nadd) : nadd_eq x x.
Proof. exact (EQ_MP (@lem1274426 x) (@lem1274425 x)). Qed.
Lemma lem1274428 (x : nadd) : (nadd_eq x x) = ((nadd_eq x x) = True).
Proof. exact (@lem7 (nadd_eq x x)). Qed.
Lemma lem1274430 (m : nat) : term1 m.
Proof. exact (@lem77775 m). Qed.
Lemma lem1274431 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem1274432 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem1274431 m) (@lem1274430 m)). Qed.
Lemma lem1274433 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem1274432 m n). Qed.
Lemma lem1274434 (n : nat) (m : nat) : (term3 m n) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem1274436 (x : nadd) : term4 x.
Proof. exact (@lem1273759 x). Qed.
Lemma lem1274437 (x : nadd) : (term4 x) = (term5 x).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem1274438 (x : nadd) : term5 x.
Proof. exact (EQ_MP (@lem1274437 x) (@lem1274436 x)). Qed.
Lemma lem1274439 (x : nadd) (y : nadd) : term6 x y.
Proof. exact (@lem1274438 x y). Qed.
Lemma lem1274440 (x : nadd) (y : nadd) : (term6 x y) = ((nadd_add x y) = (term7 x y)).
Proof. exact (eq_refl (term6 x y)). Qed.
Lemma lem1274443 (x : nadd) (y : nadd) : (nadd_add x y) = (term7 x y).
Proof. exact (EQ_MP (@lem1274440 x y) (@lem1274439 x y)). Qed.
Lemma lem1274444 : nadd_eq = nadd_eq.
Proof. exact (eq_refl nadd_eq). Qed.
Lemma lem1274445 (x : nadd) (y : nadd) : (term8 x y) = (term9 x y).
Proof. exact (MK_COMB (@lem1274444) (@lem1274443 x y)). Qed.
Lemma lem1274447 (x : nadd) (y : nadd) : (nadd_add x y) = (term7 x y).
Proof. exact (EQ_MP (@lem1274440 x y) (@lem1274439 x y)). Qed.
Lemma lem1274448 (y : nadd) (x : nadd) : (nadd_add y x) = (term7 y x).
Proof. exact (@lem1274447 y x). Qed.
Lemma lem1274449 (y : nadd) (x : nadd) : (term10 y x) = (term11 y x).
Proof. exact (MK_COMB (@lem1274445 x y) (@lem1274448 y x)). Qed.
Lemma lem1274450 (y : nadd) (x : nadd) : (term11 y x) = (term10 y x).
Proof. exact (SYM (@lem1274449 y x)). Qed.
Lemma lem1274452 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem1274434 n m) (@lem1274433 m n)). Qed.
Lemma lem1274453 (x : nadd) (y : nadd) (n : nat) : (term12 y x n) = (term12 x y n).
Proof. exact (@lem1274452 (dest_nadd x n) (dest_nadd y n)). Qed.
Lemma lem1274454 (x : nadd) (y : nadd) : (term13 y x) = (term13 x y).
Proof. exact (fun_ext (fun n : nat => @lem1274453 x y n)). Qed.
Lemma lem1274455 : mk_nadd = mk_nadd.
Proof. exact (eq_refl mk_nadd). Qed.
Lemma lem1274456 (x : nadd) (y : nadd) : (term7 y x) = (term7 x y).
Proof. exact (MK_COMB (@lem1274455) (@lem1274454 x y)). Qed.
Lemma lem1274457 (x : nadd) (y : nadd) : (term9 x y) = (term9 x y).
Proof. exact (eq_refl (term9 x y)). Qed.
Lemma lem1274458 (x : nadd) (y : nadd) : (term11 y x) = (term14 x y).
Proof. exact (MK_COMB (@lem1274457 x y) (@lem1274456 x y)). Qed.
Lemma lem1274459 (y : nadd) (x : nadd) : (term14 x y) = (term11 y x).
Proof. exact (SYM (@lem1274458 x y)). Qed.
Lemma lem1274461 (x : nadd) : (nadd_eq x x) = True.
Proof. exact (EQ_MP (@lem1274428 x) (@lem1274427 x)). Qed.
Lemma lem1274462 (x : nadd) (y : nadd) : (term14 x y) = True.
Proof. exact (@lem1274461 (term7 x y)). Qed.
Lemma lem1274463 (x : nadd) (y : nadd) : True = (term14 x y).
Proof. exact (SYM (@lem1274462 x y)). Qed.
Lemma lem1274464 (x : nadd) (y : nadd) : term14 x y.
Proof. exact (EQ_MP (@lem1274463 x y) (@lem0)). Qed.
Lemma lem1274465 (y : nadd) (x : nadd) : term11 y x.
Proof. exact (EQ_MP (@lem1274459 y x) (@lem1274464 x y)). Qed.
Lemma lem1274466 (y : nadd) (x : nadd) : term10 y x.
Proof. exact (EQ_MP (@lem1274450 y x) (@lem1274465 y x)). Qed.
Lemma lem1274471 (x : nadd) : term15 x.
Proof. exact (fun y : nadd => @lem1274466 y x). Qed.
Lemma lem1274476 : term16.
Proof. exact (fun x : nadd => @lem1274471 x). Qed.
