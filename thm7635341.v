Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7635341_term_abbrevs.
Require Import EXTENSION_spec.
Require Import IN_IMAGE_spec.
Require Import IN_UNIV_spec.
Require Import thm1855_spec.
Require Import thm7_spec.
Lemma lem7635265 {A B : Type'} (y : B) : term0 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem7635266 {A B : Type'} (y : B) : (term0 A B y) = (term1 A B y).
Proof. exact (eq_refl (term0 A B y)). Qed.
Lemma lem7635267 {A B : Type'} (y : B) : term1 A B y.
Proof. exact (EQ_MP (@lem7635266 A B y) (@lem7635265 A B y)). Qed.
Lemma lem7635268 {A B : Type'} (y : B) (s : A -> Prop) : term2 A B y s.
Proof. exact (@lem7635267 A B y s). Qed.
Lemma lem7635269 {A B : Type'} (y : B) (s : A -> Prop) : (term2 A B y s) = (term3 A B y s).
Proof. exact (eq_refl (term2 A B y s)). Qed.
Lemma lem7635270 {A B : Type'} (y : B) (s : A -> Prop) : term3 A B y s.
Proof. exact (EQ_MP (@lem7635269 A B y s) (@lem7635268 A B y s)). Qed.
Lemma lem7635271 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term4 A B y s f.
Proof. exact (@lem7635270 A B y s f). Qed.
Lemma lem7635272 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term4 A B y s f) = ((term5 A B y f s) = (term6 A B y f s)).
Proof. exact (eq_refl (term4 A B y s f)). Qed.
Lemma lem7635274 {A : Type'} (x : A) : term7 A x.
Proof. exact (@lem3204818 A x). Qed.
Lemma lem7635275 {A : Type'} (x : A) : (term7 A x) = (@IN A x (@UNIV A)).
Proof. exact (eq_refl (term7 A x)). Qed.
Lemma lem7635276 {A : Type'} (x : A) : @IN A x (@UNIV A).
Proof. exact (EQ_MP (@lem7635275 A x) (@lem7635274 A x)). Qed.
Lemma lem7635277 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = ((@IN A x (@UNIV A)) = True).
Proof. exact (@lem7 (@IN A x (@UNIV A))). Qed.
Lemma lem7635279 {A : Type'} (s : A -> Prop) : term8 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem7635280 {A : Type'} (s : A -> Prop) : (term8 A s) = (term9 A s).
Proof. exact (eq_refl (term8 A s)). Qed.
Lemma lem7635281 {A : Type'} (s : A -> Prop) : term9 A s.
Proof. exact (EQ_MP (@lem7635280 A s) (@lem7635279 A s)). Qed.
Lemma lem7635282 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term10 A s t.
Proof. exact (@lem7635281 A s t). Qed.
Lemma lem7635283 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term10 A s t) = ((s = t) = (term11 A s t)).
Proof. exact (eq_refl (term10 A s t)). Qed.
Lemma lem7635288 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term11 A s t).
Proof. exact (EQ_MP (@lem7635283 A s t) (@lem7635282 A s t)). Qed.
Lemma lem7635289 {A B : Type'} (s : type49 A B) (t : type49 A B) : (s = t) = (term12 A B s t).
Proof. exact (@lem7635288 (finite_sum A B) s t). Qed.
Lemma lem7635290 {A B : Type'} : ((@UNIV (finite_sum A B)) = (term13 A B)) = (term14 A B).
Proof. exact (@lem7635289 A B (@UNIV (finite_sum A B)) (term13 A B)). Qed.
Lemma lem7635300 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem7635277 A x) (@lem7635276 A x)). Qed.
Lemma lem7635301 {A B : Type'} (x : finite_sum A B) : (@IN (finite_sum A B) x (@UNIV (finite_sum A B))) = True.
Proof. exact (@lem7635300 (finite_sum A B) x). Qed.
Lemma lem7635302 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7635303 {A B : Type'} (x : finite_sum A B) : (term15 A B x) = (@eq Prop True).
Proof. exact (MK_COMB (@lem7635302) (@lem7635301 A B x)). Qed.
Lemma lem7635305 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term5 A B y f s) = (term6 A B y f s).
Proof. exact (EQ_MP (@lem7635272 A B y f s) (@lem7635271 A B y s f)). Qed.
Lemma lem7635306 {A B : Type'} (y : finite_sum A B) (f : type1559 A B) (s : nat -> Prop) : (term16 A B y f s) = (term17 A B y f s).
Proof. exact (@lem7635305 nat (finite_sum A B) y f s). Qed.
Lemma lem7635307 {A B : Type'} (x : finite_sum A B) : (term18 A B x) = (term19 A B x).
Proof. exact (@lem7635306 A B x (@mk_finite_sum A B) (term20 A B)). Qed.
Lemma lem7635318 {A B : Type'} (x : finite_sum A B) : ((@IN (finite_sum A B) x (@UNIV (finite_sum A B))) = (term18 A B x)) = (True = (term19 A B x)).
Proof. exact (MK_COMB (@lem7635303 A B x) (@lem7635307 A B x)). Qed.
Lemma lem7635320 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem7635321 {A B : Type'} (x : finite_sum A B) : (True = (term19 A B x)) = (term19 A B x).
Proof. exact (@lem7635320 (term19 A B x)). Qed.
Lemma lem7635332 {A B : Type'} (x : finite_sum A B) : ((@IN (finite_sum A B) x (@UNIV (finite_sum A B))) = (term18 A B x)) = (term19 A B x).
Proof. exact (TRANS (@lem7635318 A B x) (@lem7635321 A B x)). Qed.
Lemma lem7635333 {A B : Type'} : (term21 A B) = (term22 A B).
Proof. exact (fun_ext (fun x : finite_sum A B => @lem7635332 A B x)). Qed.
Lemma lem7635334 {A B : Type'} : (@all (finite_sum A B)) = (@all (finite_sum A B)).
Proof. exact (eq_refl (@all (finite_sum A B))). Qed.
Lemma lem7635335 {A B : Type'} : (term14 A B) = (term23 A B).
Proof. exact (MK_COMB (@lem7635334 A B) (@lem7635333 A B)). Qed.
Lemma lem7635340 {A B : Type'} : ((@UNIV (finite_sum A B)) = (term13 A B)) = (term23 A B).
Proof. exact (TRANS (@lem7635290 A B) (@lem7635335 A B)). Qed.
Lemma lem7635341 {A B : Type'} : (term23 A B) = ((@UNIV (finite_sum A B)) = (term13 A B)).
Proof. exact (SYM (@lem7635340 A B)). Qed.