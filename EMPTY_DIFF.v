Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EMPTY_DIFF_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1844_spec.
Require Import thm1857_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211701_spec.
Require Import thm3211702_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3269243 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3269244 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3269243 A s t). Qed.
Lemma lem3269245 {A : Type'} (s : A -> Prop) : ((@DIFF A (@EMPTY A) s) = (@EMPTY A)) = (term1 A s).
Proof. exact (@lem3269244 A (@DIFF A (@EMPTY A) s) (@EMPTY A)). Qed.
Lemma lem3269254 {A : Type'} : (term2 A) = (term3 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3269245 A s)). Qed.
Lemma lem3269255 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3269256 {A : Type'} : (term4 A) = (term5 A).
Proof. exact (MK_COMB (@lem3269255 A) (@lem3269254 A)). Qed.
Lemma lem3269261 {A : Type'} : (term5 A) = (term4 A).
Proof. exact (SYM (@lem3269256 A)). Qed.
Lemma lem3269273 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term6 A x s t) = (term7 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem3269274 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term6 A x s t) = (term7 A s x t).
Proof. exact (@lem3269273 A s x t). Qed.
Lemma lem3269275 {A : Type'} (x : A) (s : A -> Prop) : (term8 A x s) = (term9 A x s).
Proof. exact (@lem3269274 A (@EMPTY A) x s). Qed.
Lemma lem3269279 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3269280 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3269279 A x). Qed.
Lemma lem3269281 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3269282 {A : Type'} (x : A) : (term10 A x) = (and False).
Proof. exact (MK_COMB (@lem3269281) (@lem3269280 A x)). Qed.
Lemma lem3269284 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3269285 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3269284 A P x). Qed.
Lemma lem3269286 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3269285 A s x). Qed.
Lemma lem3269287 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3269288 {A : Type'} (s : A -> Prop) (x : A) : (term11 A x s) = (term12 A s x).
Proof. exact (MK_COMB (@lem3269287) (@lem3269286 A s x)). Qed.
Lemma lem3269289 {A : Type'} (s : A -> Prop) (x : A) : (term9 A x s) = (term13 A s x).
Proof. exact (MK_COMB (@lem3269282 A x) (@lem3269288 A s x)). Qed.
Lemma lem3269291 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem3269292 {A : Type'} (s : A -> Prop) (x : A) : (term13 A s x) = False.
Proof. exact (@lem3269291 (term12 A s x)). Qed.
Lemma lem3269293 {A : Type'} (x : A) (s : A -> Prop) : (term9 A x s) = False.
Proof. exact (TRANS (@lem3269289 A s x) (@lem3269292 A s x)). Qed.
Lemma lem3269294 {A : Type'} (x : A) (s : A -> Prop) : (term8 A x s) = False.
Proof. exact (TRANS (@lem3269275 A x s) (@lem3269293 A x s)). Qed.
Lemma lem3269295 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3269296 {A : Type'} (x : A) (s : A -> Prop) : (term14 A x s) = (@eq Prop False).
Proof. exact (MK_COMB (@lem3269295) (@lem3269294 A x s)). Qed.
Lemma lem3269298 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3269299 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3269298 A x). Qed.
Lemma lem3269300 {A : Type'} (s : A -> Prop) (x : A) : ((term8 A x s) = (@IN A x (@EMPTY A))) = (False = False).
Proof. exact (MK_COMB (@lem3269296 A x s) (@lem3269299 A x)). Qed.
Lemma lem3269302 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem3269303 : (False = False) = (~ False).
Proof. exact (@lem3269302 False). Qed.
Lemma lem3269305 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3269306 : (False = False) = True.
Proof. exact (TRANS (@lem3269303) (@lem3269305)). Qed.
Lemma lem3269307 {A : Type'} (s : A -> Prop) (x : A) : ((term8 A x s) = (@IN A x (@EMPTY A))) = True.
Proof. exact (TRANS (@lem3269300 A s x) (@lem3269306)). Qed.
Lemma lem3269308 {A : Type'} (s : A -> Prop) : (term15 A s) = (term16 A).
Proof. exact (fun_ext (fun x : A => @lem3269307 A s x)). Qed.
Lemma lem3269309 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3269310 {A : Type'} (s : A -> Prop) : (term1 A s) = (term17 A).
Proof. exact (MK_COMB (@lem3269309 A) (@lem3269308 A s)). Qed.
Lemma lem3269312 {A : Type'} (t : Prop) : (term18 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3269313 {A : Type'} (t : Prop) : (term18 A t) = t.
Proof. exact (@lem3269312 A t). Qed.
Lemma lem3269314 {A : Type'} : (term17 A) = True.
Proof. exact (@lem3269313 A True). Qed.
Lemma lem3269315 {A : Type'} (s : A -> Prop) : (term1 A s) = True.
Proof. exact (TRANS (@lem3269310 A s) (@lem3269314 A)). Qed.
Lemma lem3269316 {A : Type'} : (term3 A) = (term19 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3269315 A s)). Qed.
Lemma lem3269317 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3269318 {A : Type'} : (term5 A) = (term20 A).
Proof. exact (MK_COMB (@lem3269317 A) (@lem3269316 A)). Qed.
Lemma lem3269320 {A : Type'} (t : Prop) : (term18 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3269321 {A : Type'} (t : Prop) : (term21 A t) = t.
Proof. exact (@lem3269320 (A -> Prop) t). Qed.
Lemma lem3269322 {A : Type'} : (term20 A) = True.
Proof. exact (@lem3269321 A True). Qed.
Lemma lem3269323 {A : Type'} : (term5 A) = True.
Proof. exact (TRANS (@lem3269318 A) (@lem3269322 A)). Qed.
Lemma lem3269324 {A : Type'} : True = (term5 A).
Proof. exact (SYM (@lem3269323 A)). Qed.
Lemma lem3269325 {A : Type'} : term5 A.
Proof. exact (EQ_MP (@lem3269324 A) (@lem0)). Qed.
Lemma lem3269326 {A : Type'} : term4 A.
Proof. exact (EQ_MP (@lem3269261 A) (@lem3269325 A)). Qed.
