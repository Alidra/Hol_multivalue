Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ARBITRARY_UNION_OF_EMPTY_term_abbrevs.
Require Import ARBITRARY_spec.
Require Import UNION_OF_EMPTY_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Lemma lem4858244 {A : Type'} (s : type686 A) : term0 A s.
Proof. exact (@lem4853019 A s). Qed.
Lemma lem4858245 {A : Type'} (s : type686 A) : (term0 A s) = ((@ARBITRARY A s) = True).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem4858247 {A : Type'} (P : type180 A) : term1 A P.
Proof. exact (@lem4851738 A P). Qed.
Lemma lem4858248 {A : Type'} (P : type180 A) : (term1 A P) = (term2 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem4858249 {A : Type'} (P : type180 A) : term2 A P.
Proof. exact (EQ_MP (@lem4858248 A P) (@lem4858247 A P)). Qed.
Lemma lem4858250 {A : Type'} (P : type180 A) (Q : type686 A) : term3 A P Q.
Proof. exact (@lem4858249 A P Q). Qed.
Lemma lem4858251 {A : Type'} (P : type180 A) (Q : type686 A) : (term3 A P Q) = (term4 A P Q).
Proof. exact (eq_refl (term3 A P Q)). Qed.
Lemma lem4858252 {A : Type'} (P : type180 A) (Q : type686 A) : term4 A P Q.
Proof. exact (EQ_MP (@lem4858251 A P Q) (@lem4858250 A P Q)). Qed.
Lemma lem4858253 {A : Type'} (P : type180 A) (h1 : P (@EMPTY (A -> Prop))) : P (@EMPTY (A -> Prop)).
Proof. exact (h1). Qed.
Lemma lem4858254 {A : Type'} (Q : type686 A) (P : type180 A) (h1 : P (@EMPTY (A -> Prop))) : @UNION_OF A P Q (@EMPTY A).
Proof. exact (@lem4858252 A P Q (@lem4858253 A P h1)). Qed.
Lemma lem4858255 {A : Type'} (P : type180 A) (Q : type686 A) : (@UNION_OF A P Q (@EMPTY A)) = ((@UNION_OF A P Q (@EMPTY A)) = True).
Proof. exact (@lem7 (@UNION_OF A P Q (@EMPTY A))). Qed.
Lemma lem4858256 {A : Type'} (Q : type686 A) (P : type180 A) (h1 : P (@EMPTY (A -> Prop))) : (@UNION_OF A P Q (@EMPTY A)) = True.
Proof. exact (EQ_MP (@lem4858255 A P Q) (@lem4858254 A Q P h1)). Qed.
Lemma lem4858267 {A : Type'} (P : type180 A) (Q : type686 A) : term5 A P Q.
Proof. exact (fun h0 : P (@EMPTY (A -> Prop)) => @lem4858256 A Q P h0). Qed.
Lemma lem4858268 {A : Type'} (P : type180 A) (Q : type686 A) : term5 A P Q.
Proof. exact (@lem4858267 A P Q). Qed.
Lemma lem4858269 {A : Type'} (P : type686 A) : term6 A P.
Proof. exact (@lem4858268 A (@ARBITRARY A) P). Qed.
Lemma lem4858271 {A : Type'} (s : type686 A) : (@ARBITRARY A s) = True.
Proof. exact (EQ_MP (@lem4858245 A s) (@lem4858244 A s)). Qed.
Lemma lem4858272 {A : Type'} (s : type686 A) : (@ARBITRARY A s) = True.
Proof. exact (@lem4858271 A s). Qed.
Lemma lem4858273 {A : Type'} : (@ARBITRARY A (@EMPTY (A -> Prop))) = True.
Proof. exact (@lem4858272 A (@EMPTY (A -> Prop))). Qed.
Lemma lem4858274 {A : Type'} : True = (@ARBITRARY A (@EMPTY (A -> Prop))).
Proof. exact (SYM (@lem4858273 A)). Qed.
Lemma lem4858275 {A : Type'} : @ARBITRARY A (@EMPTY (A -> Prop)).
Proof. exact (EQ_MP (@lem4858274 A) (@lem0)). Qed.
Lemma lem4858276 {A : Type'} (P : type686 A) : (@UNION_OF A (@ARBITRARY A) P (@EMPTY A)) = True.
Proof. exact (@lem4858269 A P (@lem4858275 A)). Qed.
Lemma lem4858277 {A : Type'} : (term7 A) = (term8 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4858276 A P)). Qed.
Lemma lem4858278 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4858279 {A : Type'} : (term9 A) = (term10 A).
Proof. exact (MK_COMB (@lem4858278 A) (@lem4858277 A)). Qed.
Lemma lem4858281 {A : Type'} (t : Prop) : (term11 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4858282 {A : Type'} (t : Prop) : (term12 A t) = t.
Proof. exact (@lem4858281 (type686 A) t). Qed.
Lemma lem4858283 {A : Type'} : (term10 A) = True.
Proof. exact (@lem4858282 A True). Qed.
Lemma lem4858284 {A : Type'} : (term9 A) = True.
Proof. exact (TRANS (@lem4858279 A) (@lem4858283 A)). Qed.
Lemma lem4858285 {A : Type'} : True = (term9 A).
Proof. exact (SYM (@lem4858284 A)). Qed.
Lemma lem4858286 {A : Type'} : term9 A.
Proof. exact (EQ_MP (@lem4858285 A) (@lem0)). Qed.
