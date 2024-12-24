Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NUMSUM_term_abbrevs.
Lemma lem1053042 : NUMSUM = term0.
Proof. exact (@NUMSUM_def). Qed.
Lemma lem1053043 (_17342 : Prop) : _17342 = _17342.
Proof. exact (eq_refl _17342). Qed.
Lemma lem1053044 (_17342 : Prop) : (NUMSUM _17342) = (term1 _17342).
Proof. exact (MK_COMB (@lem1053042) (@lem1053043 _17342)). Qed.
Lemma lem1053045 (_17342 : Prop) : (term1 _17342) = (term2 _17342).
Proof. exact (eq_refl (term1 _17342)). Qed.
Lemma lem1053046 (_17342 : Prop) : (NUMSUM _17342) = (term2 _17342).
Proof. exact (TRANS (@lem1053044 _17342) (@lem1053045 _17342)). Qed.
Lemma lem1053047 (_17343 : nat) : _17343 = _17343.
Proof. exact (eq_refl _17343). Qed.
Lemma lem1053048 (_17342 : Prop) (_17343 : nat) : (NUMSUM _17342 _17343) = (term3 _17342 _17343).
Proof. exact (MK_COMB (@lem1053046 _17342) (@lem1053047 _17343)). Qed.
Lemma lem1053049 (_17342 : Prop) (_17343 : nat) : (term3 _17342 _17343) = (term4 _17342 _17343).
Proof. exact (eq_refl (term3 _17342 _17343)). Qed.
Lemma lem1053050 (_17342 : Prop) (_17343 : nat) : (NUMSUM _17342 _17343) = (term4 _17342 _17343).
Proof. exact (TRANS (@lem1053048 _17342 _17343) (@lem1053049 _17342 _17343)). Qed.
Lemma lem1053051 (_17342 : Prop) : term5 _17342.
Proof. exact (fun _17343 : nat => @lem1053050 _17342 _17343). Qed.
Lemma lem1053052 : term6.
Proof. exact (fun _17342 : Prop => @lem1053051 _17342). Qed.
Lemma lem1053053 (_17342 : Prop) : term7 _17342.
Proof. exact (@lem1053052 _17342). Qed.
Lemma lem1053054 (_17342 : Prop) : (term7 _17342) = (term5 _17342).
Proof. exact (eq_refl (term7 _17342)). Qed.
Lemma lem1053055 (_17342 : Prop) : term5 _17342.
Proof. exact (EQ_MP (@lem1053054 _17342) (@lem1053053 _17342)). Qed.
Lemma lem1053056 (_17342 : Prop) (_17343 : nat) : term8 _17342 _17343.
Proof. exact (@lem1053055 _17342 _17343). Qed.
Lemma lem1053057 (_17342 : Prop) (_17343 : nat) : (term8 _17342 _17343) = ((NUMSUM _17342 _17343) = (term4 _17342 _17343)).
Proof. exact (eq_refl (term8 _17342 _17343)). Qed.
Lemma lem1053058 (_17342 : Prop) (_17343 : nat) : (NUMSUM _17342 _17343) = (term4 _17342 _17343).
Proof. exact (EQ_MP (@lem1053057 _17342 _17343) (@lem1053056 _17342 _17343)). Qed.
Lemma lem1053101 (b : Prop) (x : nat) : (NUMSUM b x) = (term4 b x).
Proof. exact (@lem1053058 b x). Qed.
Lemma lem1053102 (b : Prop) : term5 b.
Proof. exact (fun x : nat => @lem1053101 b x). Qed.
Lemma lem1053103 : term6.
Proof. exact (fun b : Prop => @lem1053102 b). Qed.
