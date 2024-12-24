Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ADD_SUBR_term_abbrevs.
Require Import ADD_SUBR2_spec.
Require Import ADD_SYM_spec.
Lemma lem136306 (m : nat) : term0 m.
Proof. exact (@lem77775 m). Qed.
Lemma lem136307 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem136308 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem136307 m) (@lem136306 m)). Qed.
Lemma lem136309 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem136308 m n). Qed.
Lemma lem136310 (n : nat) (m : nat) : (term2 m n) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem136323 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem136310 n m) (@lem136309 m n)). Qed.
Lemma lem136324 (n : nat) : (Nat.sub n) = (Nat.sub n).
Proof. exact (eq_refl (Nat.sub n)). Qed.
Lemma lem136325 (n : nat) (m : nat) : (term3 m n) = (term4 n m).
Proof. exact (MK_COMB (@lem136324 n) (@lem136323 n m)). Qed.
Lemma lem136326 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem136327 (n : nat) (m : nat) : (term5 m n) = (term6 n m).
Proof. exact (MK_COMB (@lem136326) (@lem136325 n m)). Qed.
Lemma lem136328 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem136329 (n : nat) (m : nat) : ((term3 m n) = (NUMERAL 0)) = ((term4 n m) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem136327 n m) (@lem136328)). Qed.
Lemma lem136330 (m : nat) : (term7 m) = (term8 m).
Proof. exact (fun_ext (fun n : nat => @lem136329 n m)). Qed.
Lemma lem136331 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem136332 (m : nat) : (term9 m) = (term10 m).
Proof. exact (MK_COMB (@lem136331) (@lem136330 m)). Qed.
Lemma lem136333 : term11 = term12.
Proof. exact (fun_ext (fun m : nat => @lem136332 m)). Qed.
Lemma lem136334 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem136335 : term13 = term14.
Proof. exact (MK_COMB (@lem136334) (@lem136333)). Qed.
Lemma lem136336 : term14 = term13.
Proof. exact (SYM (@lem136335)). Qed.
Lemma lem136337 (m : nat) : term15 m.
Proof. exact (@lem136305 m). Qed.
Lemma lem136338 (m : nat) : (term15 m) = (term16 m).
Proof. exact (eq_refl (term15 m)). Qed.
Lemma lem136339 (m : nat) : term16 m.
Proof. exact (EQ_MP (@lem136338 m) (@lem136337 m)). Qed.
Lemma lem136340 (m : nat) (n : nat) : term17 m n.
Proof. exact (@lem136339 m n). Qed.
Lemma lem136341 (m : nat) (n : nat) : (term17 m n) = ((term4 m n) = (NUMERAL 0)).
Proof. exact (eq_refl (term17 m n)). Qed.
Lemma lem136344 (m : nat) (n : nat) : (term4 m n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem136341 m n) (@lem136340 m n)). Qed.
Lemma lem136345 (n : nat) (m : nat) : (term4 n m) = (NUMERAL 0).
Proof. exact (@lem136344 n m). Qed.
Lemma lem136350 (m : nat) : term10 m.
Proof. exact (fun n : nat => @lem136345 n m). Qed.
Lemma lem136355 : term14.
Proof. exact (fun m : nat => @lem136350 m). Qed.
Lemma lem136356 : term13.
Proof. exact (EQ_MP (@lem136336) (@lem136355)). Qed.
