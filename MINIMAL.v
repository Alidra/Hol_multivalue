Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MINIMAL_term_abbrevs.
Require Import minimal_spec.
Require Import num_WOP_spec.
Require Import thm0_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm9425_spec.
Lemma lem273062 (P : nat -> Prop) (h1 : (term0 P) = (term1 P)) : (term0 P) = (term1 P).
Proof. exact (h1). Qed.
Lemma lem273063 (P : nat -> Prop) (h1 : (term0 P) = (term1 P)) : (term1 P) = (term0 P).
Proof. exact (SYM (@lem273062 P h1)). Qed.
Lemma lem273064 (P : nat -> Prop) (h1 : (term1 P) = (term0 P)) : (term1 P) = (term0 P).
Proof. exact (h1). Qed.
Lemma lem273065 (P : nat -> Prop) (h1 : (term1 P) = (term0 P)) : (term0 P) = (term1 P).
Proof. exact (SYM (@lem273064 P h1)). Qed.
Lemma lem273066 (P : nat -> Prop) : ((term0 P) = (term1 P)) = ((term1 P) = (term0 P)).
Proof. exact (prop_ext (fun h1 : (term0 P) = (term1 P) => @lem273063 P h1) (fun h1 : (term1 P) = (term0 P) => @lem273065 P h1)). Qed.
Lemma lem273067 : term2 = term3.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem273066 P)). Qed.
Lemma lem273068 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem273069 : term4 = term5.
Proof. exact (MK_COMB (@lem273068) (@lem273067)). Qed.
Lemma lem273070 : term5.
Proof. exact (EQ_MP (@lem273069) (@lem116994)). Qed.
Lemma lem273071 (P : nat -> Prop) : term6 P.
Proof. exact (@lem273070 P). Qed.
Lemma lem273072 (P : nat -> Prop) : (term6 P) = ((term1 P) = (term0 P)).
Proof. exact (eq_refl (term6 P)). Qed.
Lemma lem273074 (P : nat -> Prop) : term7 P.
Proof. exact (@lem273060 P). Qed.
Lemma lem273075 (P : nat -> Prop) : (term7 P) = ((minimal P) = (term8 P)).
Proof. exact (eq_refl (term7 P)). Qed.
Lemma lem273086 (P : nat -> Prop) : (minimal P) = (term8 P).
Proof. exact (EQ_MP (@lem273075 P) (@lem273074 P)). Qed.
Lemma lem273095 (P : nat -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem273096 (P : nat -> Prop) : (term9 P) = (term10 P).
Proof. exact (MK_COMB (@lem273095 P) (@lem273086 P)). Qed.
Lemma lem273097 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem273098 (P : nat -> Prop) : (term11 P) = (term12 P).
Proof. exact (MK_COMB (@lem273097) (@lem273096 P)). Qed.
Lemma lem273106 (P : nat -> Prop) : (minimal P) = (term8 P).
Proof. exact (EQ_MP (@lem273075 P) (@lem273074 P)). Qed.
Lemma lem273115 (m : nat) : (Peano.lt m) = (Peano.lt m).
Proof. exact (eq_refl (Peano.lt m)). Qed.
Lemma lem273116 (m : nat) (P : nat -> Prop) : (term13 m P) = (term14 m P).
Proof. exact (MK_COMB (@lem273115 m) (@lem273106 P)). Qed.
Lemma lem273117 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem273118 (m : nat) (P : nat -> Prop) : (term15 m P) = (term16 m P).
Proof. exact (MK_COMB (@lem273117) (@lem273116 m P)). Qed.
Lemma lem273119 (P : nat -> Prop) (m : nat) : (term17 P m) = (term17 P m).
Proof. exact (eq_refl (term17 P m)). Qed.
Lemma lem273120 (P : nat -> Prop) (m : nat) : (term18 P m) = (term19 P m).
Proof. exact (MK_COMB (@lem273118 m P) (@lem273119 P m)). Qed.
Lemma lem273123 (P : nat -> Prop) : (term20 P) = (term21 P).
Proof. exact (fun_ext (fun m : nat => @lem273120 P m)). Qed.
Lemma lem273124 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem273125 (P : nat -> Prop) : (term22 P) = (term23 P).
Proof. exact (MK_COMB (@lem273124) (@lem273123 P)). Qed.
Lemma lem273130 (P : nat -> Prop) : (term24 P) = (term25 P).
Proof. exact (MK_COMB (@lem273098 P) (@lem273125 P)). Qed.
Lemma lem273133 (P : nat -> Prop) : (term26 P) = (term26 P).
Proof. exact (eq_refl (term26 P)). Qed.
Lemma lem273134 (P : nat -> Prop) : ((term0 P) = (term24 P)) = ((term0 P) = (term25 P)).
Proof. exact (MK_COMB (@lem273133 P) (@lem273130 P)). Qed.
Lemma lem273137 (P : nat -> Prop) : ((term0 P) = (term25 P)) = ((term0 P) = (term24 P)).
Proof. exact (SYM (@lem273134 P)). Qed.
Lemma lem273138 (P : nat -> Prop) : (term27 P) = (ex P).
Proof. exact (@lem9425 nat P). Qed.
Lemma lem273139 (P : nat -> Prop) : (term28 P) = (term1 P).
Proof. exact (@lem273138 (term29 P)). Qed.
Lemma lem273140 (P : nat -> Prop) : (term28 P) = (term25 P).
Proof. exact (eq_refl (term28 P)). Qed.
Lemma lem273141 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem273142 (P : nat -> Prop) : (term30 P) = (term31 P).
Proof. exact (MK_COMB (@lem273141) (@lem273140 P)). Qed.
Lemma lem273143 (P : nat -> Prop) : (term1 P) = (term1 P).
Proof. exact (eq_refl (term1 P)). Qed.
Lemma lem273144 (P : nat -> Prop) : ((term28 P) = (term1 P)) = ((term25 P) = (term1 P)).
Proof. exact (MK_COMB (@lem273142 P) (@lem273143 P)). Qed.
Lemma lem273145 (P : nat -> Prop) : (term25 P) = (term1 P).
Proof. exact (EQ_MP (@lem273144 P) (@lem273139 P)). Qed.
Lemma lem273146 (P : nat -> Prop) : (term26 P) = (term26 P).
Proof. exact (eq_refl (term26 P)). Qed.
Lemma lem273147 (P : nat -> Prop) : ((term0 P) = (term25 P)) = ((term0 P) = (term1 P)).
Proof. exact (MK_COMB (@lem273146 P) (@lem273145 P)). Qed.
Lemma lem273148 (P : nat -> Prop) : ((term0 P) = (term1 P)) = ((term0 P) = (term25 P)).
Proof. exact (SYM (@lem273147 P)). Qed.
Lemma lem273156 (P : nat -> Prop) : (term1 P) = (term0 P).
Proof. exact (EQ_MP (@lem273072 P) (@lem273071 P)). Qed.
Lemma lem273161 (P : nat -> Prop) : (term26 P) = (term26 P).
Proof. exact (eq_refl (term26 P)). Qed.
Lemma lem273162 (P : nat -> Prop) : ((term0 P) = (term1 P)) = ((term0 P) = (term0 P)).
Proof. exact (MK_COMB (@lem273161 P) (@lem273156 P)). Qed.
Lemma lem273164 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem273165 (x : Prop) : (x = x) = True.
Proof. exact (@lem273164 Prop x). Qed.
Lemma lem273166 (P : nat -> Prop) : ((term0 P) = (term0 P)) = True.
Proof. exact (@lem273165 (term0 P)). Qed.
Lemma lem273167 (P : nat -> Prop) : ((term0 P) = (term1 P)) = True.
Proof. exact (TRANS (@lem273162 P) (@lem273166 P)). Qed.
Lemma lem273168 (P : nat -> Prop) : True = ((term0 P) = (term1 P)).
Proof. exact (SYM (@lem273167 P)). Qed.
Lemma lem273169 (P : nat -> Prop) : (term0 P) = (term1 P).
Proof. exact (EQ_MP (@lem273168 P) (@lem0)). Qed.
Lemma lem273170 (P : nat -> Prop) : (term0 P) = (term25 P).
Proof. exact (EQ_MP (@lem273148 P) (@lem273169 P)). Qed.
Lemma lem273171 (P : nat -> Prop) : (term0 P) = (term24 P).
Proof. exact (EQ_MP (@lem273137 P) (@lem273170 P)). Qed.
Lemma lem273176 : term32.
Proof. exact (fun P : nat -> Prop => @lem273171 P). Qed.
