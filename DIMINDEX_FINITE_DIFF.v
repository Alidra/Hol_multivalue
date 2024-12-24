Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIMINDEX_FINITE_DIFF_term_abbrevs.
Require Import DIMINDEX_HAS_SIZE_FINITE_DIFF_spec.
Require Import HAS_SIZE_spec.
Require Import dimindex_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Lemma lem7917621 {_100044 : Type'} (s : _100044 -> Prop) : term0 _100044 s.
Proof. exact (@lem3863773 _100044 s). Qed.
Lemma lem7917622 {_100044 : Type'} (s : _100044 -> Prop) : (term0 _100044 s) = (term1 _100044 s).
Proof. exact (eq_refl (term0 _100044 s)). Qed.
Lemma lem7917623 {_100044 : Type'} (s : _100044 -> Prop) : term1 _100044 s.
Proof. exact (EQ_MP (@lem7917622 _100044 s) (@lem7917621 _100044 s)). Qed.
Lemma lem7917624 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : term2 _100044 s n.
Proof. exact (@lem7917623 _100044 s n). Qed.
Lemma lem7917625 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term2 _100044 s n) = ((@HAS_SIZE _100044 s n) = (term3 _100044 s n)).
Proof. exact (eq_refl (term2 _100044 s n)). Qed.
Lemma lem7917628 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term3 _100044 s n).
Proof. exact (EQ_MP (@lem7917625 _100044 s n) (@lem7917624 _100044 s n)). Qed.
Lemma lem7917629 {M N : Type'} (s : type31 M N) (n : nat) : (@HAS_SIZE (finite_diff M N) s n) = (term4 M N s n).
Proof. exact (@lem7917628 (finite_diff M N) s n). Qed.
Lemma lem7917630 {M N : Type'} : (term5 M N) = (term6 M N).
Proof. exact (@lem7917629 M N (@UNIV (finite_diff M N)) (term7 M N)). Qed.
Lemma lem7917635 {M N : Type'} : term6 M N.
Proof. exact (EQ_MP (@lem7917630 M N) (@lem7917620 M N)). Qed.
Lemma lem7917637 {M N : Type'} : @FINITE (finite_diff M N) (@UNIV (finite_diff M N)).
Proof. exact (proj1 (@lem7917635 M N)). Qed.
Lemma lem7917638 {M N : Type'} : (@FINITE (finite_diff M N) (@UNIV (finite_diff M N))) = ((@FINITE (finite_diff M N) (@UNIV (finite_diff M N))) = True).
Proof. exact (@lem7 (@FINITE (finite_diff M N) (@UNIV (finite_diff M N)))). Qed.
Lemma lem7917640 {A : Type'} (s : A -> Prop) : term8 A s.
Proof. exact (@lem7590231 A s). Qed.
Lemma lem7917641 {A : Type'} (s : A -> Prop) : (term8 A s) = ((@dimindex A s) = (term9 A)).
Proof. exact (eq_refl (term8 A s)). Qed.
Lemma lem7917644 {A : Type'} (s : A -> Prop) : (@dimindex A s) = (term9 A).
Proof. exact (EQ_MP (@lem7917641 A s) (@lem7917640 A s)). Qed.
Lemma lem7917645 {M N : Type'} (s : type31 M N) : (@dimindex (finite_diff M N) s) = (term10 M N).
Proof. exact (@lem7917644 (finite_diff M N) s). Qed.
Lemma lem7917646 {M N : Type'} : (@dimindex (finite_diff M N) (@UNIV (finite_diff M N))) = (term10 M N).
Proof. exact (@lem7917645 M N (@UNIV (finite_diff M N))). Qed.
Lemma lem7917647 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7917648 {M N : Type'} : (term11 M N) = (term12 M N).
Proof. exact (MK_COMB (@lem7917647) (@lem7917646 M N)). Qed.
Lemma lem7917649 {M N : Type'} : (term7 M N) = (term7 M N).
Proof. exact (eq_refl (term7 M N)). Qed.
Lemma lem7917650 {M N : Type'} : ((@dimindex (finite_diff M N) (@UNIV (finite_diff M N))) = (term7 M N)) = ((term10 M N) = (term7 M N)).
Proof. exact (MK_COMB (@lem7917648 M N) (@lem7917649 M N)). Qed.
Lemma lem7917651 {M N : Type'} : ((term10 M N) = (term7 M N)) = ((@dimindex (finite_diff M N) (@UNIV (finite_diff M N))) = (term7 M N)).
Proof. exact (SYM (@lem7917650 M N)). Qed.
Lemma lem7917655 {M N : Type'} : (@FINITE (finite_diff M N) (@UNIV (finite_diff M N))) = True.
Proof. exact (EQ_MP (@lem7917638 M N) (@lem7917637 M N)). Qed.
Lemma lem7917656 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem7917657 {M N : Type'} : (term13 M N) = (@COND nat True).
Proof. exact (MK_COMB (@lem7917656) (@lem7917655 M N)). Qed.
Lemma lem7917659 {M N : Type'} : (@CARD (finite_diff M N) (@UNIV (finite_diff M N))) = (term7 M N).
Proof. exact (proj2 (@lem7917635 M N)). Qed.
Lemma lem7917660 {M N : Type'} : (term14 M N) = (term15 M N).
Proof. exact (MK_COMB (@lem7917657 M N) (@lem7917659 M N)). Qed.
Lemma lem7917661 : term16 = term16.
Proof. exact (eq_refl term16). Qed.
Lemma lem7917662 {M N : Type'} : (term10 M N) = (term17 M N).
Proof. exact (MK_COMB (@lem7917660 M N) (@lem7917661)). Qed.
Lemma lem7917664 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem7917665 (t2 : nat) (t1 : nat) : (@COND nat True t1 t2) = t1.
Proof. exact (@lem7917664 nat t2 t1). Qed.
Lemma lem7917666 {M N : Type'} : (term17 M N) = (term7 M N).
Proof. exact (@lem7917665 term16 (term7 M N)). Qed.
Lemma lem7917667 {M N : Type'} : (term10 M N) = (term7 M N).
Proof. exact (TRANS (@lem7917662 M N) (@lem7917666 M N)). Qed.
Lemma lem7917668 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7917669 {M N : Type'} : (term12 M N) = (term18 M N).
Proof. exact (MK_COMB (@lem7917668) (@lem7917667 M N)). Qed.
Lemma lem7917670 {M N : Type'} : (term7 M N) = (term7 M N).
Proof. exact (eq_refl (term7 M N)). Qed.
Lemma lem7917671 {M N : Type'} : ((term10 M N) = (term7 M N)) = ((term7 M N) = (term7 M N)).
Proof. exact (MK_COMB (@lem7917669 M N) (@lem7917670 M N)). Qed.
Lemma lem7917673 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7917674 (x : nat) : (x = x) = True.
Proof. exact (@lem7917673 nat x). Qed.
Lemma lem7917675 {M N : Type'} : ((term7 M N) = (term7 M N)) = True.
Proof. exact (@lem7917674 (term7 M N)). Qed.
Lemma lem7917676 {M N : Type'} : ((term10 M N) = (term7 M N)) = True.
Proof. exact (TRANS (@lem7917671 M N) (@lem7917675 M N)). Qed.
Lemma lem7917677 {M N : Type'} : True = ((term10 M N) = (term7 M N)).
Proof. exact (SYM (@lem7917676 M N)). Qed.
Lemma lem7917678 {M N : Type'} : (term10 M N) = (term7 M N).
Proof. exact (EQ_MP (@lem7917677 M N) (@lem0)). Qed.
Lemma lem7917679 {M N : Type'} : (@dimindex (finite_diff M N) (@UNIV (finite_diff M N))) = (term7 M N).
Proof. exact (EQ_MP (@lem7917651 M N) (@lem7917678 M N)). Qed.
