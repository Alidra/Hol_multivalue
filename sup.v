Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import sup_term_abbrevs.
Lemma lem5133894 : sup = term0.
Proof. exact (@sup_def). Qed.
Lemma lem5133895 (_67045 : real -> Prop) : _67045 = _67045.
Proof. exact (eq_refl _67045). Qed.
Lemma lem5133896 (_67045 : real -> Prop) : (sup _67045) = (term1 _67045).
Proof. exact (MK_COMB (@lem5133894) (@lem5133895 _67045)). Qed.
Lemma lem5133897 (_67045 : real -> Prop) : (term1 _67045) = (term2 _67045).
Proof. exact (eq_refl (term1 _67045)). Qed.
Lemma lem5133898 (_67045 : real -> Prop) : (sup _67045) = (term2 _67045).
Proof. exact (TRANS (@lem5133896 _67045) (@lem5133897 _67045)). Qed.
Lemma lem5133899 : term3.
Proof. exact (fun _67045 : real -> Prop => @lem5133898 _67045). Qed.
Lemma lem5133900 (_67045 : real -> Prop) : term4 _67045.
Proof. exact (@lem5133899 _67045). Qed.
Lemma lem5133901 (_67045 : real -> Prop) : (term4 _67045) = ((sup _67045) = (term2 _67045)).
Proof. exact (eq_refl (term4 _67045)). Qed.
Lemma lem5133902 (_67045 : real -> Prop) : (sup _67045) = (term2 _67045).
Proof. exact (EQ_MP (@lem5133901 _67045) (@lem5133900 _67045)). Qed.
Lemma lem5133932 (s : real -> Prop) : (sup s) = (term2 s).
Proof. exact (@lem5133902 s). Qed.
Lemma lem5133933 : term3.
Proof. exact (fun s : real -> Prop => @lem5133932 s). Qed.
