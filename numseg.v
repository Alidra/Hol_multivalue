Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import numseg_term_abbrevs.
Lemma lem5329016 : dotdot = term0.
Proof. exact (@dotdot_def). Qed.
Lemma lem5329017 (_69692 : nat) : _69692 = _69692.
Proof. exact (eq_refl _69692). Qed.
Lemma lem5329018 (_69692 : nat) : (dotdot _69692) = (term1 _69692).
Proof. exact (MK_COMB (@lem5329016) (@lem5329017 _69692)). Qed.
Lemma lem5329019 (_69692 : nat) : (term1 _69692) = (term2 _69692).
Proof. exact (eq_refl (term1 _69692)). Qed.
Lemma lem5329020 (_69692 : nat) : (dotdot _69692) = (term2 _69692).
Proof. exact (TRANS (@lem5329018 _69692) (@lem5329019 _69692)). Qed.
Lemma lem5329021 (_69693 : nat) : _69693 = _69693.
Proof. exact (eq_refl _69693). Qed.
Lemma lem5329022 (_69692 : nat) (_69693 : nat) : (dotdot _69692 _69693) = (term3 _69692 _69693).
Proof. exact (MK_COMB (@lem5329020 _69692) (@lem5329021 _69693)). Qed.
Lemma lem5329023 (_69692 : nat) (_69693 : nat) : (term3 _69692 _69693) = (term4 _69692 _69693).
Proof. exact (eq_refl (term3 _69692 _69693)). Qed.
Lemma lem5329024 (_69692 : nat) (_69693 : nat) : (dotdot _69692 _69693) = (term4 _69692 _69693).
Proof. exact (TRANS (@lem5329022 _69692 _69693) (@lem5329023 _69692 _69693)). Qed.
Lemma lem5329025 (_69692 : nat) : term5 _69692.
Proof. exact (fun _69693 : nat => @lem5329024 _69692 _69693). Qed.
Lemma lem5329026 : term6.
Proof. exact (fun _69692 : nat => @lem5329025 _69692). Qed.
Lemma lem5329027 (_69692 : nat) : term7 _69692.
Proof. exact (@lem5329026 _69692). Qed.
Lemma lem5329028 (_69692 : nat) : (term7 _69692) = (term5 _69692).
Proof. exact (eq_refl (term7 _69692)). Qed.
Lemma lem5329029 (_69692 : nat) : term5 _69692.
Proof. exact (EQ_MP (@lem5329028 _69692) (@lem5329027 _69692)). Qed.
Lemma lem5329030 (_69692 : nat) (_69693 : nat) : term8 _69692 _69693.
Proof. exact (@lem5329029 _69692 _69693). Qed.
Lemma lem5329031 (_69692 : nat) (_69693 : nat) : (term8 _69692 _69693) = ((dotdot _69692 _69693) = (term4 _69692 _69693)).
Proof. exact (eq_refl (term8 _69692 _69693)). Qed.
Lemma lem5329032 (_69692 : nat) (_69693 : nat) : (dotdot _69692 _69693) = (term4 _69692 _69693).
Proof. exact (EQ_MP (@lem5329031 _69692 _69693) (@lem5329030 _69692 _69693)). Qed.
Lemma lem5329075 (m : nat) (n : nat) : (dotdot m n) = (term4 m n).
Proof. exact (@lem5329032 m n). Qed.
Lemma lem5329076 (m : nat) : term5 m.
Proof. exact (fun n : nat => @lem5329075 m n). Qed.
Lemma lem5329077 : term6.
Proof. exact (fun m : nat => @lem5329076 m). Qed.
