Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2338267_term_abbrevs.
Require Import INT_FORALL_POS_spec.
Lemma lem2338259 (P : int -> Prop) (h1 : (term0 P) = (term1 P)) : (term0 P) = (term1 P).
Proof. exact (h1). Qed.
Lemma lem2338260 (P : int -> Prop) (h1 : (term0 P) = (term1 P)) : (term1 P) = (term0 P).
Proof. exact (SYM (@lem2338259 P h1)). Qed.
Lemma lem2338261 (P : int -> Prop) (h1 : (term1 P) = (term0 P)) : (term1 P) = (term0 P).
Proof. exact (h1). Qed.
Lemma lem2338262 (P : int -> Prop) (h1 : (term1 P) = (term0 P)) : (term0 P) = (term1 P).
Proof. exact (SYM (@lem2338261 P h1)). Qed.
Lemma lem2338263 (P : int -> Prop) : ((term0 P) = (term1 P)) = ((term1 P) = (term0 P)).
Proof. exact (prop_ext (fun h1 : (term0 P) = (term1 P) => @lem2338260 P h1) (fun h1 : (term1 P) = (term0 P) => @lem2338262 P h1)). Qed.
Lemma lem2338264 : term2 = term3.
Proof. exact (fun_ext (fun P : int -> Prop => @lem2338263 P)). Qed.
Lemma lem2338265 : (@all (int -> Prop)) = (@all (int -> Prop)).
Proof. exact (eq_refl (@all (int -> Prop))). Qed.
Lemma lem2338266 : term4 = term5.
Proof. exact (MK_COMB (@lem2338265) (@lem2338264)). Qed.
Lemma lem2338267 : term5.
Proof. exact (EQ_MP (@lem2338266) (@lem2315380)). Qed.
