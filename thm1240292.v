Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1240292_term_abbrevs.
Require Import thm1240267_spec.
Require Import thm1240281_spec.
Lemma lem1240282 (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (_22730' a0 a1 a2 a3 a4 a5 a6 a7) = (_22730' a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (eq_refl (_22730' a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1240283 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (char' : type1335) (_22730' : type1539) (h1 : _22730' = term0) (h2 : char' = (term1 _22730')) : (term2 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7) = (term3 _22730' a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (MK_COMB (@lem1240281 char' _22730' h1 h2) (@lem1240282 _22730' a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1240284 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (char' : type1335) (_22730' : type1539) (h1 : _22730' = term0) (h2 : char' = (term1 _22730')) : term3 _22730' a0 a1 a2 a3 a4 a5 a6 a7.
Proof. exact (EQ_MP (@lem1240283 a0 a1 a2 a3 a4 a5 a6 a7 char' _22730' h1 h2) (@lem1240267 a0 a1 a2 a3 a4 a5 a6 a7 char' _22730' h2)). Qed.
Lemma lem1240285 (_22730' : type1539) : (term1 _22730') = (term1 _22730').
Proof. exact (eq_refl (term1 _22730')). Qed.
Lemma lem1240286 (char' : type1335) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (_22730' : type1539) (h1 : _22730' = term0) : term4 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7.
Proof. exact (fun h0 : char' = (term1 _22730') => @lem1240284 a0 a1 a2 a3 a4 a5 a6 a7 char' _22730' h1 h0). Qed.
Lemma lem1240287 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (_22730' : type1539) (h1 : _22730' = term0) : term5 _22730' a0 a1 a2 a3 a4 a5 a6 a7.
Proof. exact (@lem1240286 (term1 _22730') a0 a1 a2 a3 a4 a5 a6 a7 _22730' h1). Qed.
Lemma lem1240288 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (_22730' : type1539) (h1 : _22730' = term0) : term3 _22730' a0 a1 a2 a3 a4 a5 a6 a7.
Proof. exact (@lem1240287 a0 a1 a2 a3 a4 a5 a6 a7 _22730' h1 (@lem1240285 _22730')). Qed.
Lemma lem1240289 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1240290 (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : term6 _22730' a0 a1 a2 a3 a4 a5 a6 a7.
Proof. exact (fun h0 : _22730' = term0 => @lem1240288 a0 a1 a2 a3 a4 a5 a6 a7 _22730' h0). Qed.
Lemma lem1240291 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : term7 a0 a1 a2 a3 a4 a5 a6 a7.
Proof. exact (@lem1240290 term0 a0 a1 a2 a3 a4 a5 a6 a7). Qed.
Lemma lem1240292 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : term8 a0 a1 a2 a3 a4 a5 a6 a7.
Proof. exact (@lem1240291 a0 a1 a2 a3 a4 a5 a6 a7 (@lem1240289)). Qed.
