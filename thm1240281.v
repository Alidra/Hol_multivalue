Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1240281_term_abbrevs.
Require Import thm1239855_spec.
Lemma lem1240268 (char' : type1335) (_22730' : type1539) (h1 : char' = (term0 _22730')) : char' = (term0 _22730').
Proof. exact (h1). Qed.
Lemma lem1240269 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1240270 (_22730' : type1539) (h1 : _22730' = term2) : (term3 _22730') = term4.
Proof. exact (MK_COMB (@lem1240269) (@lem1239855 _22730' h1)). Qed.
Lemma lem1240271 : term4 = term5.
Proof. exact (eq_refl term4). Qed.
Lemma lem1240272 (_22730' : type1539) : (term6 _22730') = (term6 _22730').
Proof. exact (eq_refl (term6 _22730')). Qed.
Lemma lem1240273 (_22730' : type1539) : ((term3 _22730') = term4) = ((term3 _22730') = term5).
Proof. exact (MK_COMB (@lem1240272 _22730') (@lem1240271)). Qed.
Lemma lem1240274 (_22730' : type1539) : (term3 _22730') = (term0 _22730').
Proof. exact (eq_refl (term3 _22730')). Qed.
Lemma lem1240275 : (@eq ((recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))))) -> Prop)) = (@eq ((recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))))) -> Prop)).
Proof. exact (eq_refl (@eq ((recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))))) -> Prop))). Qed.
Lemma lem1240276 (_22730' : type1539) : (term6 _22730') = (term7 _22730').
Proof. exact (MK_COMB (@lem1240275) (@lem1240274 _22730')). Qed.
Lemma lem1240277 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem1240278 (_22730' : type1539) : ((term3 _22730') = term5) = ((term0 _22730') = term5).
Proof. exact (MK_COMB (@lem1240276 _22730') (@lem1240277)). Qed.
Lemma lem1240279 (_22730' : type1539) : ((term3 _22730') = term4) = ((term0 _22730') = term5).
Proof. exact (TRANS (@lem1240273 _22730') (@lem1240278 _22730')). Qed.
Lemma lem1240280 (_22730' : type1539) (h1 : _22730' = term2) : (term0 _22730') = term5.
Proof. exact (EQ_MP (@lem1240279 _22730') (@lem1240270 _22730' h1)). Qed.
Lemma lem1240281 (char' : type1335) (_22730' : type1539) (h1 : _22730' = term2) (h2 : char' = (term0 _22730')) : char' = term5.
Proof. exact (TRANS (@lem1240268 char' _22730' h2) (@lem1240280 _22730' h1)). Qed.
