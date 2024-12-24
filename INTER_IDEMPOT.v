Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INTER_IDEMPOT_term_abbrevs.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1845_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211710_spec.
Require Import thm3211711_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3255273 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3255274 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3255273 A s t). Qed.
Lemma lem3255275 {A : Type'} (s : A -> Prop) : ((@INTER A s s) = s) = (term1 A s).
Proof. exact (@lem3255274 A (@INTER A s s) s). Qed.
Lemma lem3255284 {A : Type'} : (term2 A) = (term3 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3255275 A s)). Qed.
Lemma lem3255285 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3255286 {A : Type'} : (term4 A) = (term5 A).
Proof. exact (MK_COMB (@lem3255285 A) (@lem3255284 A)). Qed.
Lemma lem3255291 {A : Type'} : (term5 A) = (term4 A).
Proof. exact (SYM (@lem3255286 A)). Qed.
Lemma lem3255303 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term6 A x s t) = (term7 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3255304 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term6 A x s t) = (term7 A s x t).
Proof. exact (@lem3255303 A s x t). Qed.
Lemma lem3255305 {A : Type'} (x : A) (s : A -> Prop) : (term8 A x s) = (term9 A x s).
Proof. exact (@lem3255304 A s x s). Qed.
Lemma lem3255307 (t : Prop) : (t /\ t) = t.
Proof. exact (proj2 (@lem1845 t)). Qed.
Lemma lem3255308 {A : Type'} (x : A) (s : A -> Prop) : (term9 A x s) = (@IN A x s).
Proof. exact (@lem3255307 (@IN A x s)). Qed.
Lemma lem3255310 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3255311 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3255310 A P x). Qed.
Lemma lem3255312 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3255311 A s x). Qed.
Lemma lem3255313 {A : Type'} (s : A -> Prop) (x : A) : (term9 A x s) = (s x).
Proof. exact (TRANS (@lem3255308 A x s) (@lem3255312 A s x)). Qed.
Lemma lem3255314 {A : Type'} (s : A -> Prop) (x : A) : (term8 A x s) = (s x).
Proof. exact (TRANS (@lem3255305 A x s) (@lem3255313 A s x)). Qed.
Lemma lem3255315 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3255316 {A : Type'} (s : A -> Prop) (x : A) : (term10 A x s) = (term11 A s x).
Proof. exact (MK_COMB (@lem3255315) (@lem3255314 A s x)). Qed.
Lemma lem3255318 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3255319 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3255318 A P x). Qed.
Lemma lem3255320 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3255319 A s x). Qed.
Lemma lem3255321 {A : Type'} (s : A -> Prop) (x : A) : ((term8 A x s) = (@IN A x s)) = ((s x) = (s x)).
Proof. exact (MK_COMB (@lem3255316 A s x) (@lem3255320 A s x)). Qed.
Lemma lem3255323 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3255324 (x : Prop) : (x = x) = True.
Proof. exact (@lem3255323 Prop x). Qed.
Lemma lem3255325 {A : Type'} (s : A -> Prop) (x : A) : ((s x) = (s x)) = True.
Proof. exact (@lem3255324 (s x)). Qed.
Lemma lem3255326 {A : Type'} (x : A) (s : A -> Prop) : ((term8 A x s) = (@IN A x s)) = True.
Proof. exact (TRANS (@lem3255321 A s x) (@lem3255325 A s x)). Qed.
Lemma lem3255327 {A : Type'} (s : A -> Prop) : (term12 A s) = (term13 A).
Proof. exact (fun_ext (fun x : A => @lem3255326 A x s)). Qed.
Lemma lem3255328 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3255329 {A : Type'} (s : A -> Prop) : (term1 A s) = (term14 A).
Proof. exact (MK_COMB (@lem3255328 A) (@lem3255327 A s)). Qed.
Lemma lem3255331 {A : Type'} (t : Prop) : (term15 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3255332 {A : Type'} (t : Prop) : (term15 A t) = t.
Proof. exact (@lem3255331 A t). Qed.
Lemma lem3255333 {A : Type'} : (term14 A) = True.
Proof. exact (@lem3255332 A True). Qed.
Lemma lem3255334 {A : Type'} (s : A -> Prop) : (term1 A s) = True.
Proof. exact (TRANS (@lem3255329 A s) (@lem3255333 A)). Qed.
Lemma lem3255335 {A : Type'} : (term3 A) = (term16 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3255334 A s)). Qed.
Lemma lem3255336 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3255337 {A : Type'} : (term5 A) = (term17 A).
Proof. exact (MK_COMB (@lem3255336 A) (@lem3255335 A)). Qed.
Lemma lem3255339 {A : Type'} (t : Prop) : (term15 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3255340 {A : Type'} (t : Prop) : (term18 A t) = t.
Proof. exact (@lem3255339 (A -> Prop) t). Qed.
Lemma lem3255341 {A : Type'} : (term17 A) = True.
Proof. exact (@lem3255340 A True). Qed.
Lemma lem3255342 {A : Type'} : (term5 A) = True.
Proof. exact (TRANS (@lem3255337 A) (@lem3255341 A)). Qed.
Lemma lem3255343 {A : Type'} : True = (term5 A).
Proof. exact (SYM (@lem3255342 A)). Qed.
Lemma lem3255344 {A : Type'} : term5 A.
Proof. exact (EQ_MP (@lem3255343 A) (@lem0)). Qed.
Lemma lem3255345 {A : Type'} : term4 A.
Proof. exact (EQ_MP (@lem3255291 A) (@lem3255344 A)). Qed.
