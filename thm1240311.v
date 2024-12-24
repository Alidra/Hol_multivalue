Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1240311_term_abbrevs.
Require Import thm1239855_spec.
Lemma lem1240300 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1240301 (_22730' : type1539) (h1 : _22730' = term1) : (term2 _22730') = term3.
Proof. exact (MK_COMB (@lem1240300) (@lem1239855 _22730' h1)). Qed.
Lemma lem1240302 : term3 = term4.
Proof. exact (eq_refl term3). Qed.
Lemma lem1240303 (_22730' : type1539) : (term5 _22730') = (term5 _22730').
Proof. exact (eq_refl (term5 _22730')). Qed.
Lemma lem1240304 (_22730' : type1539) : ((term2 _22730') = term3) = ((term2 _22730') = term4).
Proof. exact (MK_COMB (@lem1240303 _22730') (@lem1240302)). Qed.
Lemma lem1240305 (_22730' : type1539) : (term2 _22730') = (term6 _22730').
Proof. exact (eq_refl (term2 _22730')). Qed.
Lemma lem1240306 : (@eq (Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Ascii.ascii)) = (@eq (Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Ascii.ascii)).
Proof. exact (eq_refl (@eq (Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Ascii.ascii))). Qed.
Lemma lem1240307 (_22730' : type1539) : (term5 _22730') = (term7 _22730').
Proof. exact (MK_COMB (@lem1240306) (@lem1240305 _22730')). Qed.
Lemma lem1240308 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1240309 (_22730' : type1539) : ((term2 _22730') = term4) = ((term6 _22730') = term4).
Proof. exact (MK_COMB (@lem1240307 _22730') (@lem1240308)). Qed.
Lemma lem1240310 (_22730' : type1539) : ((term2 _22730') = term3) = ((term6 _22730') = term4).
Proof. exact (TRANS (@lem1240304 _22730') (@lem1240309 _22730')). Qed.
Lemma lem1240311 (_22730' : type1539) (h1 : _22730' = term1) : (term6 _22730') = term4.
Proof. exact (EQ_MP (@lem1240310 _22730') (@lem1240301 _22730' h1)). Qed.
