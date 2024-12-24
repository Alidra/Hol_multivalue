Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HAS_SIZE_term_abbrevs.
Lemma lem3863712 {_100044 : Type'} : (@HAS_SIZE _100044) = (term0 _100044).
Proof. exact (@HAS_SIZE_def _100044). Qed.
Lemma lem3863713 {_100044 : Type'} (_44754 : _100044 -> Prop) : _44754 = _44754.
Proof. exact (eq_refl _44754). Qed.
Lemma lem3863714 {_100044 : Type'} (_44754 : _100044 -> Prop) : (@HAS_SIZE _100044 _44754) = (term1 _100044 _44754).
Proof. exact (MK_COMB (@lem3863712 _100044) (@lem3863713 _100044 _44754)). Qed.
Lemma lem3863715 {_100044 : Type'} (_44754 : _100044 -> Prop) : (term1 _100044 _44754) = (term2 _100044 _44754).
Proof. exact (eq_refl (term1 _100044 _44754)). Qed.
Lemma lem3863716 {_100044 : Type'} (_44754 : _100044 -> Prop) : (@HAS_SIZE _100044 _44754) = (term2 _100044 _44754).
Proof. exact (TRANS (@lem3863714 _100044 _44754) (@lem3863715 _100044 _44754)). Qed.
Lemma lem3863717 (_44755 : nat) : _44755 = _44755.
Proof. exact (eq_refl _44755). Qed.
Lemma lem3863718 {_100044 : Type'} (_44754 : _100044 -> Prop) (_44755 : nat) : (@HAS_SIZE _100044 _44754 _44755) = (term3 _100044 _44754 _44755).
Proof. exact (MK_COMB (@lem3863716 _100044 _44754) (@lem3863717 _44755)). Qed.
Lemma lem3863719 {_100044 : Type'} (_44754 : _100044 -> Prop) (_44755 : nat) : (term3 _100044 _44754 _44755) = (term4 _100044 _44754 _44755).
Proof. exact (eq_refl (term3 _100044 _44754 _44755)). Qed.
Lemma lem3863720 {_100044 : Type'} (_44754 : _100044 -> Prop) (_44755 : nat) : (@HAS_SIZE _100044 _44754 _44755) = (term4 _100044 _44754 _44755).
Proof. exact (TRANS (@lem3863718 _100044 _44754 _44755) (@lem3863719 _100044 _44754 _44755)). Qed.
Lemma lem3863721 {_100044 : Type'} (_44754 : _100044 -> Prop) : term5 _100044 _44754.
Proof. exact (fun _44755 : nat => @lem3863720 _100044 _44754 _44755). Qed.
Lemma lem3863722 {_100044 : Type'} : term6 _100044.
Proof. exact (fun _44754 : _100044 -> Prop => @lem3863721 _100044 _44754). Qed.
Lemma lem3863723 {_100044 : Type'} (_44754 : _100044 -> Prop) : term7 _100044 _44754.
Proof. exact (@lem3863722 _100044 _44754). Qed.
Lemma lem3863724 {_100044 : Type'} (_44754 : _100044 -> Prop) : (term7 _100044 _44754) = (term5 _100044 _44754).
Proof. exact (eq_refl (term7 _100044 _44754)). Qed.
Lemma lem3863725 {_100044 : Type'} (_44754 : _100044 -> Prop) : term5 _100044 _44754.
Proof. exact (EQ_MP (@lem3863724 _100044 _44754) (@lem3863723 _100044 _44754)). Qed.
Lemma lem3863726 {_100044 : Type'} (_44754 : _100044 -> Prop) (_44755 : nat) : term8 _100044 _44754 _44755.
Proof. exact (@lem3863725 _100044 _44754 _44755). Qed.
Lemma lem3863727 {_100044 : Type'} (_44754 : _100044 -> Prop) (_44755 : nat) : (term8 _100044 _44754 _44755) = ((@HAS_SIZE _100044 _44754 _44755) = (term4 _100044 _44754 _44755)).
Proof. exact (eq_refl (term8 _100044 _44754 _44755)). Qed.
Lemma lem3863728 {_100044 : Type'} (_44754 : _100044 -> Prop) (_44755 : nat) : (@HAS_SIZE _100044 _44754 _44755) = (term4 _100044 _44754 _44755).
Proof. exact (EQ_MP (@lem3863727 _100044 _44754 _44755) (@lem3863726 _100044 _44754 _44755)). Qed.
Lemma lem3863771 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term4 _100044 s n).
Proof. exact (@lem3863728 _100044 s n). Qed.
Lemma lem3863772 {_100044 : Type'} (s : _100044 -> Prop) : term5 _100044 s.
Proof. exact (fun n : nat => @lem3863771 _100044 s n). Qed.
Lemma lem3863773 {_100044 : Type'} : term6 _100044.
Proof. exact (fun s : _100044 -> Prop => @lem3863772 _100044 s). Qed.
