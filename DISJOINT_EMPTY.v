Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DISJOINT_EMPTY_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1845_spec.
Require Import thm1857_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211710_spec.
Require Import thm3211711_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211738_spec.
Require Import thm3211739_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3265183 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (EQ_MP (@lem3211739 A s t) (@lem3211738 A s t)). Qed.
Lemma lem3265184 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (@lem3265183 A s t). Qed.
Lemma lem3265185 {A : Type'} (s : A -> Prop) : (@DISJOINT A (@EMPTY A) s) = ((@INTER A (@EMPTY A) s) = (@EMPTY A)).
Proof. exact (@lem3265184 A (@EMPTY A) s). Qed.
Lemma lem3265189 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3265190 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3265189 A s t). Qed.
Lemma lem3265191 {A : Type'} (s : A -> Prop) : ((@INTER A (@EMPTY A) s) = (@EMPTY A)) = (term1 A s).
Proof. exact (@lem3265190 A (@INTER A (@EMPTY A) s) (@EMPTY A)). Qed.
Lemma lem3265196 {A : Type'} (s : A -> Prop) : (@DISJOINT A (@EMPTY A) s) = (term1 A s).
Proof. exact (TRANS (@lem3265185 A s) (@lem3265191 A s)). Qed.
Lemma lem3265201 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3265202 {A : Type'} (s : A -> Prop) : (term2 A s) = (term3 A s).
Proof. exact (MK_COMB (@lem3265201) (@lem3265196 A s)). Qed.
Lemma lem3265204 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (EQ_MP (@lem3211739 A s t) (@lem3211738 A s t)). Qed.
Lemma lem3265205 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (@lem3265204 A s t). Qed.
Lemma lem3265206 {A : Type'} (s : A -> Prop) : (@DISJOINT A s (@EMPTY A)) = ((@INTER A s (@EMPTY A)) = (@EMPTY A)).
Proof. exact (@lem3265205 A s (@EMPTY A)). Qed.
Lemma lem3265210 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3265211 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3265210 A s t). Qed.
Lemma lem3265212 {A : Type'} (s : A -> Prop) : ((@INTER A s (@EMPTY A)) = (@EMPTY A)) = (term4 A s).
Proof. exact (@lem3265211 A (@INTER A s (@EMPTY A)) (@EMPTY A)). Qed.
Lemma lem3265217 {A : Type'} (s : A -> Prop) : (@DISJOINT A s (@EMPTY A)) = (term4 A s).
Proof. exact (TRANS (@lem3265206 A s) (@lem3265212 A s)). Qed.
Lemma lem3265222 {A : Type'} (s : A -> Prop) : (term5 A s) = (term6 A s).
Proof. exact (MK_COMB (@lem3265202 A s) (@lem3265217 A s)). Qed.
Lemma lem3265225 {A : Type'} : (term7 A) = (term8 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3265222 A s)). Qed.
Lemma lem3265226 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3265227 {A : Type'} : (term9 A) = (term10 A).
Proof. exact (MK_COMB (@lem3265226 A) (@lem3265225 A)). Qed.
Lemma lem3265232 {A : Type'} : (term10 A) = (term9 A).
Proof. exact (SYM (@lem3265227 A)). Qed.
Lemma lem3265246 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term11 A x s t) = (term12 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3265247 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term11 A x s t) = (term12 A s x t).
Proof. exact (@lem3265246 A s x t). Qed.
Lemma lem3265248 {A : Type'} (x : A) (s : A -> Prop) : (term13 A x s) = (term14 A x s).
Proof. exact (@lem3265247 A (@EMPTY A) x s). Qed.
Lemma lem3265252 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3265253 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3265252 A x). Qed.
Lemma lem3265254 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3265255 {A : Type'} (x : A) : (term15 A x) = (and False).
Proof. exact (MK_COMB (@lem3265254) (@lem3265253 A x)). Qed.
Lemma lem3265257 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3265258 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3265257 A P x). Qed.
Lemma lem3265259 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3265258 A s x). Qed.
Lemma lem3265260 {A : Type'} (s : A -> Prop) (x : A) : (term14 A x s) = (term16 A s x).
Proof. exact (MK_COMB (@lem3265255 A x) (@lem3265259 A s x)). Qed.
Lemma lem3265262 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem3265263 {A : Type'} (s : A -> Prop) (x : A) : (term16 A s x) = False.
Proof. exact (@lem3265262 (s x)). Qed.
Lemma lem3265264 {A : Type'} (x : A) (s : A -> Prop) : (term14 A x s) = False.
Proof. exact (TRANS (@lem3265260 A s x) (@lem3265263 A s x)). Qed.
Lemma lem3265265 {A : Type'} (x : A) (s : A -> Prop) : (term13 A x s) = False.
Proof. exact (TRANS (@lem3265248 A x s) (@lem3265264 A x s)). Qed.
Lemma lem3265266 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3265267 {A : Type'} (x : A) (s : A -> Prop) : (term17 A x s) = (@eq Prop False).
Proof. exact (MK_COMB (@lem3265266) (@lem3265265 A x s)). Qed.
Lemma lem3265269 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3265270 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3265269 A x). Qed.
Lemma lem3265271 {A : Type'} (s : A -> Prop) (x : A) : ((term13 A x s) = (@IN A x (@EMPTY A))) = (False = False).
Proof. exact (MK_COMB (@lem3265267 A x s) (@lem3265270 A x)). Qed.
Lemma lem3265273 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem3265274 : (False = False) = (~ False).
Proof. exact (@lem3265273 False). Qed.
Lemma lem3265276 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3265277 : (False = False) = True.
Proof. exact (TRANS (@lem3265274) (@lem3265276)). Qed.
Lemma lem3265278 {A : Type'} (s : A -> Prop) (x : A) : ((term13 A x s) = (@IN A x (@EMPTY A))) = True.
Proof. exact (TRANS (@lem3265271 A s x) (@lem3265277)). Qed.
Lemma lem3265279 {A : Type'} (s : A -> Prop) : (term18 A s) = (term19 A).
Proof. exact (fun_ext (fun x : A => @lem3265278 A s x)). Qed.
Lemma lem3265280 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3265281 {A : Type'} (s : A -> Prop) : (term1 A s) = (term20 A).
Proof. exact (MK_COMB (@lem3265280 A) (@lem3265279 A s)). Qed.
Lemma lem3265283 {A : Type'} (t : Prop) : (term21 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3265284 {A : Type'} (t : Prop) : (term21 A t) = t.
Proof. exact (@lem3265283 A t). Qed.
Lemma lem3265285 {A : Type'} : (term20 A) = True.
Proof. exact (@lem3265284 A True). Qed.
Lemma lem3265286 {A : Type'} (s : A -> Prop) : (term1 A s) = True.
Proof. exact (TRANS (@lem3265281 A s) (@lem3265285 A)). Qed.
Lemma lem3265287 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3265288 {A : Type'} (s : A -> Prop) : (term3 A s) = (and True).
Proof. exact (MK_COMB (@lem3265287) (@lem3265286 A s)). Qed.
Lemma lem3265296 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term11 A x s t) = (term12 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3265297 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term11 A x s t) = (term12 A s x t).
Proof. exact (@lem3265296 A s x t). Qed.
Lemma lem3265298 {A : Type'} (s : A -> Prop) (x : A) : (term22 A x s) = (term23 A s x).
Proof. exact (@lem3265297 A s x (@EMPTY A)). Qed.
Lemma lem3265302 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3265303 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3265302 A P x). Qed.
Lemma lem3265304 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3265303 A s x). Qed.
Lemma lem3265305 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3265306 {A : Type'} (s : A -> Prop) (x : A) : (term24 A x s) = (term25 A s x).
Proof. exact (MK_COMB (@lem3265305) (@lem3265304 A s x)). Qed.
Lemma lem3265308 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3265309 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3265308 A x). Qed.
Lemma lem3265310 {A : Type'} (s : A -> Prop) (x : A) : (term23 A s x) = (term26 A s x).
Proof. exact (MK_COMB (@lem3265306 A s x) (@lem3265309 A x)). Qed.
Lemma lem3265312 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem3265313 {A : Type'} (s : A -> Prop) (x : A) : (term26 A s x) = False.
Proof. exact (@lem3265312 (s x)). Qed.
Lemma lem3265314 {A : Type'} (s : A -> Prop) (x : A) : (term23 A s x) = False.
Proof. exact (TRANS (@lem3265310 A s x) (@lem3265313 A s x)). Qed.
Lemma lem3265315 {A : Type'} (x : A) (s : A -> Prop) : (term22 A x s) = False.
Proof. exact (TRANS (@lem3265298 A s x) (@lem3265314 A s x)). Qed.
Lemma lem3265316 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3265317 {A : Type'} (x : A) (s : A -> Prop) : (term27 A x s) = (@eq Prop False).
Proof. exact (MK_COMB (@lem3265316) (@lem3265315 A x s)). Qed.
Lemma lem3265319 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3265320 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3265319 A x). Qed.
Lemma lem3265321 {A : Type'} (s : A -> Prop) (x : A) : ((term22 A x s) = (@IN A x (@EMPTY A))) = (False = False).
Proof. exact (MK_COMB (@lem3265317 A x s) (@lem3265320 A x)). Qed.
Lemma lem3265323 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem3265324 : (False = False) = (~ False).
Proof. exact (@lem3265323 False). Qed.
Lemma lem3265326 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3265327 : (False = False) = True.
Proof. exact (TRANS (@lem3265324) (@lem3265326)). Qed.
Lemma lem3265328 {A : Type'} (s : A -> Prop) (x : A) : ((term22 A x s) = (@IN A x (@EMPTY A))) = True.
Proof. exact (TRANS (@lem3265321 A s x) (@lem3265327)). Qed.
Lemma lem3265329 {A : Type'} (s : A -> Prop) : (term28 A s) = (term19 A).
Proof. exact (fun_ext (fun x : A => @lem3265328 A s x)). Qed.
Lemma lem3265330 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3265331 {A : Type'} (s : A -> Prop) : (term4 A s) = (term20 A).
Proof. exact (MK_COMB (@lem3265330 A) (@lem3265329 A s)). Qed.
Lemma lem3265333 {A : Type'} (t : Prop) : (term21 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3265334 {A : Type'} (t : Prop) : (term21 A t) = t.
Proof. exact (@lem3265333 A t). Qed.
Lemma lem3265335 {A : Type'} : (term20 A) = True.
Proof. exact (@lem3265334 A True). Qed.
Lemma lem3265336 {A : Type'} (s : A -> Prop) : (term4 A s) = True.
Proof. exact (TRANS (@lem3265331 A s) (@lem3265335 A)). Qed.
Lemma lem3265337 {A : Type'} (s : A -> Prop) : (term6 A s) = (True /\ True).
Proof. exact (MK_COMB (@lem3265288 A s) (@lem3265336 A s)). Qed.
Lemma lem3265339 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3265340 : (True /\ True) = True.
Proof. exact (@lem3265339 True). Qed.
Lemma lem3265341 {A : Type'} (s : A -> Prop) : (term6 A s) = True.
Proof. exact (TRANS (@lem3265337 A s) (@lem3265340)). Qed.
Lemma lem3265342 {A : Type'} : (term8 A) = (term29 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3265341 A s)). Qed.
Lemma lem3265343 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3265344 {A : Type'} : (term10 A) = (term30 A).
Proof. exact (MK_COMB (@lem3265343 A) (@lem3265342 A)). Qed.
Lemma lem3265346 {A : Type'} (t : Prop) : (term21 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3265347 {A : Type'} (t : Prop) : (term31 A t) = t.
Proof. exact (@lem3265346 (A -> Prop) t). Qed.
Lemma lem3265348 {A : Type'} : (term30 A) = True.
Proof. exact (@lem3265347 A True). Qed.
Lemma lem3265349 {A : Type'} : (term10 A) = True.
Proof. exact (TRANS (@lem3265344 A) (@lem3265348 A)). Qed.
Lemma lem3265350 {A : Type'} : True = (term10 A).
Proof. exact (SYM (@lem3265349 A)). Qed.
Lemma lem3265351 {A : Type'} : term10 A.
Proof. exact (EQ_MP (@lem3265350 A) (@lem0)). Qed.
Lemma lem3265352 {A : Type'} : term9 A.
Proof. exact (EQ_MP (@lem3265232 A) (@lem3265351 A)). Qed.
