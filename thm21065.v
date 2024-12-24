Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm21065_term_abbrevs.
Require Import thm21033_spec.
Lemma lem21053 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem21054 (p : Prop) (h1 : p = False) : (term1 p) = term2.
Proof. exact (MK_COMB (@lem21053) (@lem21033 p h1)). Qed.
Lemma lem21055 : term2 = (term3 = (~ False)).
Proof. exact (eq_refl term2). Qed.
Lemma lem21056 (p : Prop) : (term4 p) = (term4 p).
Proof. exact (eq_refl (term4 p)). Qed.
Lemma lem21057 (p : Prop) : ((term1 p) = term2) = ((term1 p) = (term3 = (~ False))).
Proof. exact (MK_COMB (@lem21056 p) (@lem21055)). Qed.
Lemma lem21058 (p : Prop) : (term1 p) = ((term5 p) = (~ p)).
Proof. exact (eq_refl (term1 p)). Qed.
Lemma lem21059 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem21060 (p : Prop) : (term4 p) = (term6 p).
Proof. exact (MK_COMB (@lem21059) (@lem21058 p)). Qed.
Lemma lem21061 : (term3 = (~ False)) = (term3 = (~ False)).
Proof. exact (eq_refl (term3 = (~ False))). Qed.
Lemma lem21062 (p : Prop) : ((term1 p) = (term3 = (~ False))) = (((term5 p) = (~ p)) = (term3 = (~ False))).
Proof. exact (MK_COMB (@lem21060 p) (@lem21061)). Qed.
Lemma lem21063 (p : Prop) : ((term1 p) = term2) = (((term5 p) = (~ p)) = (term3 = (~ False))).
Proof. exact (TRANS (@lem21057 p) (@lem21062 p)). Qed.
Lemma lem21064 (p : Prop) (h1 : p = False) : ((term5 p) = (~ p)) = (term3 = (~ False)).
Proof. exact (EQ_MP (@lem21063 p) (@lem21054 p h1)). Qed.
Lemma lem21065 (p : Prop) (h1 : p = False) : (term3 = (~ False)) = ((term5 p) = (~ p)).
Proof. exact (SYM (@lem21064 p h1)). Qed.
