Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FACT_NZ_term_abbrevs.
Require Import FACT_LT_spec.
Require Import LT_NZ_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Lemma lem146252 (n : nat) (h1 : (term0 n) = (term1 n)) : (term0 n) = (term1 n).
Proof. exact (h1). Qed.
Lemma lem146253 (n : nat) (h1 : (term0 n) = (term1 n)) : (term1 n) = (term0 n).
Proof. exact (SYM (@lem146252 n h1)). Qed.
Lemma lem146254 (n : nat) (h1 : (term1 n) = (term0 n)) : (term1 n) = (term0 n).
Proof. exact (h1). Qed.
Lemma lem146255 (n : nat) (h1 : (term1 n) = (term0 n)) : (term0 n) = (term1 n).
Proof. exact (SYM (@lem146254 n h1)). Qed.
Lemma lem146256 (n : nat) : ((term0 n) = (term1 n)) = ((term1 n) = (term0 n)).
Proof. exact (prop_ext (fun h1 : (term0 n) = (term1 n) => @lem146253 n h1) (fun h1 : (term1 n) = (term0 n) => @lem146255 n h1)). Qed.
Lemma lem146257 : term2 = term3.
Proof. exact (fun_ext (fun n : nat => @lem146256 n)). Qed.
Lemma lem146258 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem146259 : term4 = term5.
Proof. exact (MK_COMB (@lem146258) (@lem146257)). Qed.
Lemma lem146260 : term5.
Proof. exact (EQ_MP (@lem146259) (@lem98731)). Qed.
Lemma lem146261 (n : nat) : term6 n.
Proof. exact (@lem146212 n). Qed.
Lemma lem146262 (n : nat) : (term6 n) = (term7 n).
Proof. exact (eq_refl (term6 n)). Qed.
Lemma lem146263 (n : nat) : term7 n.
Proof. exact (EQ_MP (@lem146262 n) (@lem146261 n)). Qed.
Lemma lem146264 (n : nat) : (term7 n) = ((term7 n) = True).
Proof. exact (@lem7 (term7 n)). Qed.
Lemma lem146266 (n : nat) : term8 n.
Proof. exact (@lem146260 n). Qed.
Lemma lem146267 (n : nat) : (term8 n) = ((term1 n) = (term0 n)).
Proof. exact (eq_refl (term8 n)). Qed.
Lemma lem146274 (n : nat) : (term1 n) = (term0 n).
Proof. exact (EQ_MP (@lem146267 n) (@lem146266 n)). Qed.
Lemma lem146275 (n : nat) : (term9 n) = (term7 n).
Proof. exact (@lem146274 (Factorial.fact n)). Qed.
Lemma lem146277 (n : nat) : (term7 n) = True.
Proof. exact (EQ_MP (@lem146264 n) (@lem146263 n)). Qed.
Lemma lem146278 (n : nat) : (term9 n) = True.
Proof. exact (TRANS (@lem146275 n) (@lem146277 n)). Qed.
Lemma lem146279 : term10 = term11.
Proof. exact (fun_ext (fun n : nat => @lem146278 n)). Qed.
Lemma lem146280 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem146281 : term12 = term13.
Proof. exact (MK_COMB (@lem146280) (@lem146279)). Qed.
Lemma lem146283 {A : Type'} (t : Prop) : (term14 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem146284 (t : Prop) : (term15 t) = t.
Proof. exact (@lem146283 nat t). Qed.
Lemma lem146285 : term13 = True.
Proof. exact (@lem146284 True). Qed.
Lemma lem146286 : term12 = True.
Proof. exact (TRANS (@lem146281) (@lem146285)). Qed.
Lemma lem146287 : True = term12.
Proof. exact (SYM (@lem146286)). Qed.
Lemma lem146288 : term12.
Proof. exact (EQ_MP (@lem146287) (@lem0)). Qed.
