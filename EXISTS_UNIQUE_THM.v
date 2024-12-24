Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXISTS_UNIQUE_THM_term_abbrevs.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem4216 {A : Type'} : (@ex1 A) = (term0 A).
Proof. exact (@ex1_def A). Qed.
Lemma lem4233 {A : Type'} (P : A -> Prop) : (term1 A P) = (term1 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem4234 {A : Type'} (P : A -> Prop) : (term2 A P) = (term3 A P).
Proof. exact (MK_COMB (@lem4216 A) (@lem4233 A P)). Qed.
Lemma lem4236 {A B : Type'} (f : A -> B) (y : A) : (term4 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4237 {A : Type'} (f : type686 A) (y : A -> Prop) : (term5 A f y) = (f y).
Proof. exact (@lem4236 (A -> Prop) Prop f y). Qed.
Lemma lem4238 {A : Type'} (P : A -> Prop) : (term6 A P) = (term3 A P).
Proof. exact (@lem4237 A (term0 A) (term1 A P)). Qed.
Lemma lem4239 {A : Type'} (P : A -> Prop) : (term7 A P) = (term8 A P).
Proof. exact (eq_refl (term7 A P)). Qed.
Lemma lem4240 {A : Type'} : (term9 A) = (term0 A).
Proof. exact (fun_ext (fun P : A -> Prop => @lem4239 A P)). Qed.
Lemma lem4241 {A : Type'} (P : A -> Prop) : (term1 A P) = (term1 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem4242 {A : Type'} (P : A -> Prop) : (term6 A P) = (term3 A P).
Proof. exact (MK_COMB (@lem4240 A) (@lem4241 A P)). Qed.
Lemma lem4243 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4244 {A : Type'} (P : A -> Prop) : (term10 A P) = (term11 A P).
Proof. exact (MK_COMB (@lem4243) (@lem4242 A P)). Qed.
Lemma lem4245 {A : Type'} (P : A -> Prop) : (term3 A P) = (term12 A P).
Proof. exact (eq_refl (term3 A P)). Qed.
Lemma lem4246 {A : Type'} (P : A -> Prop) : ((term6 A P) = (term3 A P)) = ((term3 A P) = (term12 A P)).
Proof. exact (MK_COMB (@lem4244 A P) (@lem4245 A P)). Qed.
Lemma lem4247 {A : Type'} (P : A -> Prop) : (term3 A P) = (term12 A P).
Proof. exact (EQ_MP (@lem4246 A P) (@lem4238 A P)). Qed.
Lemma lem4267 {A B : Type'} (f : A -> B) (y : A) : (term4 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4268 {A : Type'} (f : A -> Prop) (y : A) : (term13 A f y) = (f y).
Proof. exact (@lem4267 A Prop f y). Qed.
Lemma lem4269 {A : Type'} (P : A -> Prop) (x : A) : (term13 A P x) = (P x).
Proof. exact (@lem4268 A P x). Qed.
Lemma lem4270 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4271 {A : Type'} (P : A -> Prop) (x : A) : (term14 A P x) = (term15 A P x).
Proof. exact (MK_COMB (@lem4270) (@lem4269 A P x)). Qed.
Lemma lem4273 {A B : Type'} (f : A -> B) (y : A) : (term4 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4274 {A : Type'} (f : A -> Prop) (y : A) : (term13 A f y) = (f y).
Proof. exact (@lem4273 A Prop f y). Qed.
Lemma lem4275 {A : Type'} (P : A -> Prop) (y : A) : (term13 A P y) = (P y).
Proof. exact (@lem4274 A P y). Qed.
Lemma lem4276 {A : Type'} (x : A) (P : A -> Prop) (y : A) : (term16 A x P y) = (term17 A x P y).
Proof. exact (MK_COMB (@lem4271 A P x) (@lem4275 A P y)). Qed.
Lemma lem4279 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4280 {A : Type'} (x : A) (P : A -> Prop) (y : A) : (term18 A x P y) = (term19 A x P y).
Proof. exact (MK_COMB (@lem4279) (@lem4276 A x P y)). Qed.
Lemma lem4283 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4284 {A : Type'} (P : A -> Prop) (x : A) (y : A) : (term20 A P x y) = (term21 A P x y).
Proof. exact (MK_COMB (@lem4280 A x P y) (@lem4283 A x y)). Qed.
Lemma lem4287 {A : Type'} (P : A -> Prop) (x : A) : (term22 A P x) = (term23 A P x).
Proof. exact (fun_ext (fun y : A => @lem4284 A P x y)). Qed.
Lemma lem4288 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4289 {A : Type'} (P : A -> Prop) (x : A) : (term24 A P x) = (term25 A P x).
Proof. exact (MK_COMB (@lem4288 A) (@lem4287 A P x)). Qed.
Lemma lem4294 {A : Type'} (P : A -> Prop) : (term26 A P) = (term27 A P).
Proof. exact (fun_ext (fun x : A => @lem4289 A P x)). Qed.
Lemma lem4295 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4296 {A : Type'} (P : A -> Prop) : (term28 A P) = (term29 A P).
Proof. exact (MK_COMB (@lem4295 A) (@lem4294 A P)). Qed.
Lemma lem4301 {A : Type'} (P : A -> Prop) : (term30 A P) = (term30 A P).
Proof. exact (eq_refl (term30 A P)). Qed.
Lemma lem4302 {A : Type'} (P : A -> Prop) : (term12 A P) = (term31 A P).
Proof. exact (MK_COMB (@lem4301 A P) (@lem4296 A P)). Qed.
Lemma lem4305 {A : Type'} (P : A -> Prop) : (term3 A P) = (term31 A P).
Proof. exact (TRANS (@lem4247 A P) (@lem4302 A P)). Qed.
Lemma lem4306 {A : Type'} (P : A -> Prop) : (term2 A P) = (term31 A P).
Proof. exact (TRANS (@lem4234 A P) (@lem4305 A P)). Qed.
Lemma lem4307 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4308 {A : Type'} (P : A -> Prop) : (term32 A P) = (term33 A P).
Proof. exact (MK_COMB (@lem4307) (@lem4306 A P)). Qed.
Lemma lem4329 {A : Type'} (P : A -> Prop) : (term31 A P) = (term31 A P).
Proof. exact (eq_refl (term31 A P)). Qed.
Lemma lem4330 {A : Type'} (P : A -> Prop) : ((term2 A P) = (term31 A P)) = ((term31 A P) = (term31 A P)).
Proof. exact (MK_COMB (@lem4308 A P) (@lem4329 A P)). Qed.
Lemma lem4332 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4333 (x : Prop) : (x = x) = True.
Proof. exact (@lem4332 Prop x). Qed.
Lemma lem4334 {A : Type'} (P : A -> Prop) : ((term31 A P) = (term31 A P)) = True.
Proof. exact (@lem4333 (term31 A P)). Qed.
Lemma lem4337 {A : Type'} (P : A -> Prop) : (term34 A P) = (term34 A P).
Proof. exact (eq_refl (term34 A P)). Qed.
Lemma lem4338 {A : Type'} (P : A -> Prop) : (term34 A P) = (((term31 A P) = (term31 A P)) = True).
Proof. exact (eq_refl (term34 A P)). Qed.
Lemma lem4339 {A : Type'} (P : A -> Prop) : (term35 A P) = (term35 A P).
Proof. exact (eq_refl (term35 A P)). Qed.
Lemma lem4340 {A : Type'} (P : A -> Prop) : ((term34 A P) = (term34 A P)) = ((term34 A P) = (((term31 A P) = (term31 A P)) = True)).
Proof. exact (MK_COMB (@lem4339 A P) (@lem4338 A P)). Qed.
Lemma lem4341 {A : Type'} (P : A -> Prop) : (term34 A P) = (((term31 A P) = (term31 A P)) = True).
Proof. exact (eq_refl (term34 A P)). Qed.
Lemma lem4342 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4343 {A : Type'} (P : A -> Prop) : (term35 A P) = (term36 A P).
Proof. exact (MK_COMB (@lem4342) (@lem4341 A P)). Qed.
Lemma lem4344 {A : Type'} (P : A -> Prop) : (((term31 A P) = (term31 A P)) = True) = (((term31 A P) = (term31 A P)) = True).
Proof. exact (eq_refl (((term31 A P) = (term31 A P)) = True)). Qed.
Lemma lem4345 {A : Type'} (P : A -> Prop) : ((term34 A P) = (((term31 A P) = (term31 A P)) = True)) = ((((term31 A P) = (term31 A P)) = True) = (((term31 A P) = (term31 A P)) = True)).
Proof. exact (MK_COMB (@lem4343 A P) (@lem4344 A P)). Qed.
Lemma lem4346 {A : Type'} (P : A -> Prop) : ((term34 A P) = (term34 A P)) = ((((term31 A P) = (term31 A P)) = True) = (((term31 A P) = (term31 A P)) = True)).
Proof. exact (TRANS (@lem4340 A P) (@lem4345 A P)). Qed.
Lemma lem4347 {A : Type'} (P : A -> Prop) : (((term31 A P) = (term31 A P)) = True) = (((term31 A P) = (term31 A P)) = True).
Proof. exact (EQ_MP (@lem4346 A P) (@lem4337 A P)). Qed.
Lemma lem4348 {A : Type'} (P : A -> Prop) : ((term31 A P) = (term31 A P)) = True.
Proof. exact (EQ_MP (@lem4347 A P) (@lem4334 A P)). Qed.
Lemma lem4349 {A : Type'} (P : A -> Prop) : ((term2 A P) = (term31 A P)) = True.
Proof. exact (TRANS (@lem4330 A P) (@lem4348 A P)). Qed.
Lemma lem4350 {A : Type'} (P : A -> Prop) : True = ((term2 A P) = (term31 A P)).
Proof. exact (SYM (@lem4349 A P)). Qed.
Lemma lem4351 {A : Type'} (P : A -> Prop) : (term2 A P) = (term31 A P).
Proof. exact (EQ_MP (@lem4350 A P) (@lem0)). Qed.
Lemma lem4356 {A : Type'} : term37 A.
Proof. exact (fun P : A -> Prop => @lem4351 A P). Qed.
