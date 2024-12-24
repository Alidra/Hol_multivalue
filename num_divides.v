Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import num_divides_term_abbrevs.
Lemma lem2836598 : num_divides = term0.
Proof. exact (@num_divides_def). Qed.
Lemma lem2836599 (_31139 : nat) : _31139 = _31139.
Proof. exact (eq_refl _31139). Qed.
Lemma lem2836600 (_31139 : nat) : (num_divides _31139) = (term1 _31139).
Proof. exact (MK_COMB (@lem2836598) (@lem2836599 _31139)). Qed.
Lemma lem2836601 (_31139 : nat) : (term1 _31139) = (term2 _31139).
Proof. exact (eq_refl (term1 _31139)). Qed.
Lemma lem2836602 (_31139 : nat) : (num_divides _31139) = (term2 _31139).
Proof. exact (TRANS (@lem2836600 _31139) (@lem2836601 _31139)). Qed.
Lemma lem2836603 (_31140 : nat) : _31140 = _31140.
Proof. exact (eq_refl _31140). Qed.
Lemma lem2836604 (_31139 : nat) (_31140 : nat) : (num_divides _31139 _31140) = (term3 _31139 _31140).
Proof. exact (MK_COMB (@lem2836602 _31139) (@lem2836603 _31140)). Qed.
Lemma lem2836605 (_31139 : nat) (_31140 : nat) : (term3 _31139 _31140) = (term4 _31139 _31140).
Proof. exact (eq_refl (term3 _31139 _31140)). Qed.
Lemma lem2836606 (_31139 : nat) (_31140 : nat) : (num_divides _31139 _31140) = (term4 _31139 _31140).
Proof. exact (TRANS (@lem2836604 _31139 _31140) (@lem2836605 _31139 _31140)). Qed.
Lemma lem2836607 (_31139 : nat) : term5 _31139.
Proof. exact (fun _31140 : nat => @lem2836606 _31139 _31140). Qed.
Lemma lem2836608 : term6.
Proof. exact (fun _31139 : nat => @lem2836607 _31139). Qed.
Lemma lem2836609 (_31139 : nat) : term7 _31139.
Proof. exact (@lem2836608 _31139). Qed.
Lemma lem2836610 (_31139 : nat) : (term7 _31139) = (term5 _31139).
Proof. exact (eq_refl (term7 _31139)). Qed.
Lemma lem2836611 (_31139 : nat) : term5 _31139.
Proof. exact (EQ_MP (@lem2836610 _31139) (@lem2836609 _31139)). Qed.
Lemma lem2836612 (_31139 : nat) (_31140 : nat) : term8 _31139 _31140.
Proof. exact (@lem2836611 _31139 _31140). Qed.
Lemma lem2836613 (_31139 : nat) (_31140 : nat) : (term8 _31139 _31140) = ((num_divides _31139 _31140) = (term4 _31139 _31140)).
Proof. exact (eq_refl (term8 _31139 _31140)). Qed.
Lemma lem2836614 (_31139 : nat) (_31140 : nat) : (num_divides _31139 _31140) = (term4 _31139 _31140).
Proof. exact (EQ_MP (@lem2836613 _31139 _31140) (@lem2836612 _31139 _31140)). Qed.
Lemma lem2836657 (a : nat) (b : nat) : (num_divides a b) = (term4 a b).
Proof. exact (@lem2836614 a b). Qed.
Lemma lem2836658 (a : nat) : term5 a.
Proof. exact (fun b : nat => @lem2836657 a b). Qed.
Lemma lem2836659 : term6.
Proof. exact (fun a : nat => @lem2836658 a). Qed.
