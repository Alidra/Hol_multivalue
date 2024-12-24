Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import has_sup_term_abbrevs.
Lemma lem5291153 : has_sup = term0.
Proof. exact (@has_sup_def). Qed.
Lemma lem5291154 (_69266 : real -> Prop) : _69266 = _69266.
Proof. exact (eq_refl _69266). Qed.
Lemma lem5291155 (_69266 : real -> Prop) : (has_sup _69266) = (term1 _69266).
Proof. exact (MK_COMB (@lem5291153) (@lem5291154 _69266)). Qed.
Lemma lem5291156 (_69266 : real -> Prop) : (term1 _69266) = (term2 _69266).
Proof. exact (eq_refl (term1 _69266)). Qed.
Lemma lem5291157 (_69266 : real -> Prop) : (has_sup _69266) = (term2 _69266).
Proof. exact (TRANS (@lem5291155 _69266) (@lem5291156 _69266)). Qed.
Lemma lem5291158 (_69267 : real) : _69267 = _69267.
Proof. exact (eq_refl _69267). Qed.
Lemma lem5291159 (_69266 : real -> Prop) (_69267 : real) : (has_sup _69266 _69267) = (term3 _69266 _69267).
Proof. exact (MK_COMB (@lem5291157 _69266) (@lem5291158 _69267)). Qed.
Lemma lem5291160 (_69266 : real -> Prop) (_69267 : real) : (term3 _69266 _69267) = (term4 _69266 _69267).
Proof. exact (eq_refl (term3 _69266 _69267)). Qed.
Lemma lem5291161 (_69266 : real -> Prop) (_69267 : real) : (has_sup _69266 _69267) = (term4 _69266 _69267).
Proof. exact (TRANS (@lem5291159 _69266 _69267) (@lem5291160 _69266 _69267)). Qed.
Lemma lem5291162 (_69266 : real -> Prop) : term5 _69266.
Proof. exact (fun _69267 : real => @lem5291161 _69266 _69267). Qed.
Lemma lem5291163 : term6.
Proof. exact (fun _69266 : real -> Prop => @lem5291162 _69266). Qed.
Lemma lem5291164 (_69266 : real -> Prop) : term7 _69266.
Proof. exact (@lem5291163 _69266). Qed.
Lemma lem5291165 (_69266 : real -> Prop) : (term7 _69266) = (term5 _69266).
Proof. exact (eq_refl (term7 _69266)). Qed.
Lemma lem5291166 (_69266 : real -> Prop) : term5 _69266.
Proof. exact (EQ_MP (@lem5291165 _69266) (@lem5291164 _69266)). Qed.
Lemma lem5291167 (_69266 : real -> Prop) (_69267 : real) : term8 _69266 _69267.
Proof. exact (@lem5291166 _69266 _69267). Qed.
Lemma lem5291168 (_69266 : real -> Prop) (_69267 : real) : (term8 _69266 _69267) = ((has_sup _69266 _69267) = (term4 _69266 _69267)).
Proof. exact (eq_refl (term8 _69266 _69267)). Qed.
Lemma lem5291169 (_69266 : real -> Prop) (_69267 : real) : (has_sup _69266 _69267) = (term4 _69266 _69267).
Proof. exact (EQ_MP (@lem5291168 _69266 _69267) (@lem5291167 _69266 _69267)). Qed.
Lemma lem5291212 (s : real -> Prop) (b : real) : (has_sup s b) = (term4 s b).
Proof. exact (@lem5291169 s b). Qed.
Lemma lem5291213 (s : real -> Prop) : term5 s.
Proof. exact (fun b : real => @lem5291212 s b). Qed.
Lemma lem5291214 : term6.
Proof. exact (fun s : real -> Prop => @lem5291213 s). Qed.
