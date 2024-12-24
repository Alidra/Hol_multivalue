Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ARBITRARY_INTERSECTION_OF_EMPTY_term_abbrevs.
Require Import ARBITRARY_spec.
Require Import INTERSECTION_OF_EMPTY_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Lemma lem4858287 {A : Type'} (s : type686 A) : term0 A s.
Proof. exact (@lem4853019 A s). Qed.
Lemma lem4858288 {A : Type'} (s : type686 A) : (term0 A s) = ((@ARBITRARY A s) = True).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem4858290 {A : Type'} (P : type180 A) : term1 A P.
Proof. exact (@lem4851880 A P). Qed.
Lemma lem4858291 {A : Type'} (P : type180 A) : (term1 A P) = (term2 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem4858292 {A : Type'} (P : type180 A) : term2 A P.
Proof. exact (EQ_MP (@lem4858291 A P) (@lem4858290 A P)). Qed.
Lemma lem4858293 {A : Type'} (P : type180 A) (Q : type686 A) : term3 A P Q.
Proof. exact (@lem4858292 A P Q). Qed.
Lemma lem4858294 {A : Type'} (P : type180 A) (Q : type686 A) : (term3 A P Q) = (term4 A P Q).
Proof. exact (eq_refl (term3 A P Q)). Qed.
Lemma lem4858295 {A : Type'} (P : type180 A) (Q : type686 A) : term4 A P Q.
Proof. exact (EQ_MP (@lem4858294 A P Q) (@lem4858293 A P Q)). Qed.
Lemma lem4858296 {A : Type'} (P : type180 A) (h1 : P (@EMPTY (A -> Prop))) : P (@EMPTY (A -> Prop)).
Proof. exact (h1). Qed.
Lemma lem4858297 {A : Type'} (Q : type686 A) (P : type180 A) (h1 : P (@EMPTY (A -> Prop))) : @INTERSECTION_OF A P Q (@UNIV A).
Proof. exact (@lem4858295 A P Q (@lem4858296 A P h1)). Qed.
Lemma lem4858298 {A : Type'} (P : type180 A) (Q : type686 A) : (@INTERSECTION_OF A P Q (@UNIV A)) = ((@INTERSECTION_OF A P Q (@UNIV A)) = True).
Proof. exact (@lem7 (@INTERSECTION_OF A P Q (@UNIV A))). Qed.
Lemma lem4858299 {A : Type'} (Q : type686 A) (P : type180 A) (h1 : P (@EMPTY (A -> Prop))) : (@INTERSECTION_OF A P Q (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem4858298 A P Q) (@lem4858297 A Q P h1)). Qed.
Lemma lem4858310 {A : Type'} (P : type180 A) (Q : type686 A) : term5 A P Q.
Proof. exact (fun h0 : P (@EMPTY (A -> Prop)) => @lem4858299 A Q P h0). Qed.
Lemma lem4858311 {A : Type'} (P : type180 A) (Q : type686 A) : term5 A P Q.
Proof. exact (@lem4858310 A P Q). Qed.
Lemma lem4858312 {A : Type'} (P : type686 A) : term6 A P.
Proof. exact (@lem4858311 A (@ARBITRARY A) P). Qed.
Lemma lem4858314 {A : Type'} (s : type686 A) : (@ARBITRARY A s) = True.
Proof. exact (EQ_MP (@lem4858288 A s) (@lem4858287 A s)). Qed.
Lemma lem4858315 {A : Type'} (s : type686 A) : (@ARBITRARY A s) = True.
Proof. exact (@lem4858314 A s). Qed.
Lemma lem4858316 {A : Type'} : (@ARBITRARY A (@EMPTY (A -> Prop))) = True.
Proof. exact (@lem4858315 A (@EMPTY (A -> Prop))). Qed.
Lemma lem4858317 {A : Type'} : True = (@ARBITRARY A (@EMPTY (A -> Prop))).
Proof. exact (SYM (@lem4858316 A)). Qed.
Lemma lem4858318 {A : Type'} : @ARBITRARY A (@EMPTY (A -> Prop)).
Proof. exact (EQ_MP (@lem4858317 A) (@lem0)). Qed.
Lemma lem4858319 {A : Type'} (P : type686 A) : (@INTERSECTION_OF A (@ARBITRARY A) P (@UNIV A)) = True.
Proof. exact (@lem4858312 A P (@lem4858318 A)). Qed.
Lemma lem4858320 {A : Type'} : (term7 A) = (term8 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4858319 A P)). Qed.
Lemma lem4858321 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4858322 {A : Type'} : (term9 A) = (term10 A).
Proof. exact (MK_COMB (@lem4858321 A) (@lem4858320 A)). Qed.
Lemma lem4858324 {A : Type'} (t : Prop) : (term11 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4858325 {A : Type'} (t : Prop) : (term12 A t) = t.
Proof. exact (@lem4858324 (type686 A) t). Qed.
Lemma lem4858326 {A : Type'} : (term10 A) = True.
Proof. exact (@lem4858325 A True). Qed.
Lemma lem4858327 {A : Type'} : (term9 A) = True.
Proof. exact (TRANS (@lem4858322 A) (@lem4858326 A)). Qed.
Lemma lem4858328 {A : Type'} : True = (term9 A).
Proof. exact (SYM (@lem4858327 A)). Qed.
Lemma lem4858329 {A : Type'} : term9 A.
Proof. exact (EQ_MP (@lem4858328 A) (@lem0)). Qed.
