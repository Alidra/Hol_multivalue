Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DECIMAL_term_abbrevs.
Lemma lem1977650 : DECIMAL = term0.
Proof. exact (@DECIMAL_def). Qed.
Lemma lem1977651 (_27701 : nat) : _27701 = _27701.
Proof. exact (eq_refl _27701). Qed.
Lemma lem1977652 (_27701 : nat) : (DECIMAL _27701) = (term1 _27701).
Proof. exact (MK_COMB (@lem1977650) (@lem1977651 _27701)). Qed.
Lemma lem1977653 (_27701 : nat) : (term1 _27701) = (term2 _27701).
Proof. exact (eq_refl (term1 _27701)). Qed.
Lemma lem1977654 (_27701 : nat) : (DECIMAL _27701) = (term2 _27701).
Proof. exact (TRANS (@lem1977652 _27701) (@lem1977653 _27701)). Qed.
Lemma lem1977655 (_27702 : nat) : _27702 = _27702.
Proof. exact (eq_refl _27702). Qed.
Lemma lem1977656 (_27701 : nat) (_27702 : nat) : (DECIMAL _27701 _27702) = (term3 _27701 _27702).
Proof. exact (MK_COMB (@lem1977654 _27701) (@lem1977655 _27702)). Qed.
Lemma lem1977657 (_27701 : nat) (_27702 : nat) : (term3 _27701 _27702) = (term4 _27701 _27702).
Proof. exact (eq_refl (term3 _27701 _27702)). Qed.
Lemma lem1977658 (_27701 : nat) (_27702 : nat) : (DECIMAL _27701 _27702) = (term4 _27701 _27702).
Proof. exact (TRANS (@lem1977656 _27701 _27702) (@lem1977657 _27701 _27702)). Qed.
Lemma lem1977659 (_27701 : nat) : term5 _27701.
Proof. exact (fun _27702 : nat => @lem1977658 _27701 _27702). Qed.
Lemma lem1977660 : term6.
Proof. exact (fun _27701 : nat => @lem1977659 _27701). Qed.
Lemma lem1977661 (_27701 : nat) : term7 _27701.
Proof. exact (@lem1977660 _27701). Qed.
Lemma lem1977662 (_27701 : nat) : (term7 _27701) = (term5 _27701).
Proof. exact (eq_refl (term7 _27701)). Qed.
Lemma lem1977663 (_27701 : nat) : term5 _27701.
Proof. exact (EQ_MP (@lem1977662 _27701) (@lem1977661 _27701)). Qed.
Lemma lem1977664 (_27701 : nat) (_27702 : nat) : term8 _27701 _27702.
Proof. exact (@lem1977663 _27701 _27702). Qed.
Lemma lem1977665 (_27701 : nat) (_27702 : nat) : (term8 _27701 _27702) = ((DECIMAL _27701 _27702) = (term4 _27701 _27702)).
Proof. exact (eq_refl (term8 _27701 _27702)). Qed.
Lemma lem1977666 (_27701 : nat) (_27702 : nat) : (DECIMAL _27701 _27702) = (term4 _27701 _27702).
Proof. exact (EQ_MP (@lem1977665 _27701 _27702) (@lem1977664 _27701 _27702)). Qed.
Lemma lem1977709 (x : nat) (y : nat) : (DECIMAL x y) = (term4 x y).
Proof. exact (@lem1977666 x y). Qed.
Lemma lem1977710 (x : nat) : term5 x.
Proof. exact (fun y : nat => @lem1977709 x y). Qed.
Lemma lem1977711 : term6.
Proof. exact (fun x : nat => @lem1977710 x). Qed.
