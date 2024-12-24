Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm4377358_term_abbrevs.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1843_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211668_spec.
Require Import thm3211669_spec.
Require Import thm3211724_spec.
Require Import thm3211725_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm4372329_spec.
Lemma lem4377187 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4377188 {_104961 : Type'} (s : type686 _104961) (t : type686 _104961) : (s = t) = (term1 _104961 s t).
Proof. exact (@lem4377187 (_104961 -> Prop) s t). Qed.
Lemma lem4377189 {_104961 : Type'} (f : type686 _104961) : (f = (@EMPTY (_104961 -> Prop))) = (term2 _104961 f).
Proof. exact (@lem4377188 _104961 f (@EMPTY (_104961 -> Prop))). Qed.
Lemma lem4377198 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4377199 {_104961 : Type'} (f : type686 _104961) : (term3 _104961 f) = (term4 _104961 f).
Proof. exact (MK_COMB (@lem4377198) (@lem4377189 _104961 f)). Qed.
Lemma lem4377216 {_104960 _104961 : Type'} (s : _104960 -> Prop) : (term5 _104960 _104961 s) = (term5 _104960 _104961 s).
Proof. exact (eq_refl (term5 _104960 _104961 s)). Qed.
Lemma lem4377217 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term6 _104960 _104961 f s) = (term7 _104960 _104961 f s).
Proof. exact (MK_COMB (@lem4377199 _104961 f) (@lem4377216 _104960 _104961 s)). Qed.
Lemma lem4377220 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term7 _104960 _104961 f s) = (term6 _104960 _104961 f s).
Proof. exact (SYM (@lem4377217 _104960 _104961 f s)). Qed.
Lemma lem4377230 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4377231 {_104961 : Type'} (P : type686 _104961) (x : _104961 -> Prop) : (@IN (_104961 -> Prop) x P) = (P x).
Proof. exact (@lem4377230 (_104961 -> Prop) P x). Qed.
Lemma lem4377232 {_104961 : Type'} (f : type686 _104961) (x : _104961 -> Prop) : (@IN (_104961 -> Prop) x f) = (f x).
Proof. exact (@lem4377231 _104961 f x). Qed.
Lemma lem4377233 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4377234 {_104961 : Type'} (f : type686 _104961) (x : _104961 -> Prop) : (term8 _104961 x f) = (term9 _104961 f x).
Proof. exact (MK_COMB (@lem4377233) (@lem4377232 _104961 f x)). Qed.
Lemma lem4377236 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4377237 {_104961 : Type'} (x : _104961 -> Prop) : (@IN (_104961 -> Prop) x (@EMPTY (_104961 -> Prop))) = False.
Proof. exact (@lem4377236 (_104961 -> Prop) x). Qed.
Lemma lem4377238 {_104961 : Type'} (f : type686 _104961) (x : _104961 -> Prop) : ((@IN (_104961 -> Prop) x f) = (@IN (_104961 -> Prop) x (@EMPTY (_104961 -> Prop)))) = ((f x) = False).
Proof. exact (MK_COMB (@lem4377234 _104961 f x) (@lem4377237 _104961 x)). Qed.
Lemma lem4377240 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4377241 {_104961 : Type'} (f : type686 _104961) (x : _104961 -> Prop) : ((f x) = False) = (term10 _104961 f x).
Proof. exact (@lem4377240 (f x)). Qed.
Lemma lem4377242 {_104961 : Type'} (f : type686 _104961) (x : _104961 -> Prop) : ((@IN (_104961 -> Prop) x f) = (@IN (_104961 -> Prop) x (@EMPTY (_104961 -> Prop)))) = (term10 _104961 f x).
Proof. exact (TRANS (@lem4377238 _104961 f x) (@lem4377241 _104961 f x)). Qed.
Lemma lem4377243 {_104961 : Type'} (f : type686 _104961) : (term11 _104961 f) = (term12 _104961 f).
Proof. exact (fun_ext (fun x : _104961 -> Prop => @lem4377242 _104961 f x)). Qed.
Lemma lem4377244 {_104961 : Type'} : (@all (_104961 -> Prop)) = (@all (_104961 -> Prop)).
Proof. exact (eq_refl (@all (_104961 -> Prop))). Qed.
Lemma lem4377245 {_104961 : Type'} (f : type686 _104961) : (term2 _104961 f) = (term13 _104961 f).
Proof. exact (MK_COMB (@lem4377244 _104961) (@lem4377243 _104961 f)). Qed.
Lemma lem4377250 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4377251 {_104961 : Type'} (f : type686 _104961) : (term4 _104961 f) = (term14 _104961 f).
Proof. exact (MK_COMB (@lem4377250) (@lem4377245 _104961 f)). Qed.
Lemma lem4377265 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4377266 {_104960 : Type'} (P : _104960 -> Prop) (x : _104960) : (@IN _104960 x P) = (P x).
Proof. exact (@lem4377265 _104960 P x). Qed.
Lemma lem4377267 {_104960 : Type'} (s : _104960 -> Prop) (p1 : _104960) : (@IN _104960 p1 s) = (s p1).
Proof. exact (@lem4377266 _104960 s p1). Qed.
Lemma lem4377268 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4377269 {_104960 : Type'} (s : _104960 -> Prop) (p1 : _104960) : (term15 _104960 p1 s) = (term16 _104960 s p1).
Proof. exact (MK_COMB (@lem4377268) (@lem4377267 _104960 s p1)). Qed.
Lemma lem4377271 {A : Type'} (s : type686 A) (x : A) : (term17 A x s) = (term18 A s x).
Proof. exact (EQ_MP (@lem3211669 A s x) (@lem3211668 A s x)). Qed.
Lemma lem4377272 {_104961 : Type'} (s : type686 _104961) (x : _104961) : (term17 _104961 x s) = (term18 _104961 s x).
Proof. exact (@lem4377271 _104961 s x). Qed.
Lemma lem4377273 {_104961 : Type'} (p2 : _104961) : (term19 _104961 p2) = (term20 _104961 p2).
Proof. exact (@lem4377272 _104961 (@EMPTY (_104961 -> Prop)) p2). Qed.
Lemma lem4377281 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4377282 {_104961 : Type'} (x : _104961 -> Prop) : (@IN (_104961 -> Prop) x (@EMPTY (_104961 -> Prop))) = False.
Proof. exact (@lem4377281 (_104961 -> Prop) x). Qed.
Lemma lem4377283 {_104961 : Type'} (t : _104961 -> Prop) : (@IN (_104961 -> Prop) t (@EMPTY (_104961 -> Prop))) = False.
Proof. exact (@lem4377282 _104961 t). Qed.
Lemma lem4377284 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4377285 {_104961 : Type'} (t : _104961 -> Prop) : (term21 _104961 t) = (imp False).
Proof. exact (MK_COMB (@lem4377284) (@lem4377283 _104961 t)). Qed.
Lemma lem4377287 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4377288 {_104961 : Type'} (P : _104961 -> Prop) (x : _104961) : (@IN _104961 x P) = (P x).
Proof. exact (@lem4377287 _104961 P x). Qed.
Lemma lem4377289 {_104961 : Type'} (t : _104961 -> Prop) (p2 : _104961) : (@IN _104961 p2 t) = (t p2).
Proof. exact (@lem4377288 _104961 t p2). Qed.
Lemma lem4377290 {_104961 : Type'} (t : _104961 -> Prop) (p2 : _104961) : (term22 _104961 p2 t) = (term23 _104961 t p2).
Proof. exact (MK_COMB (@lem4377285 _104961 t) (@lem4377289 _104961 t p2)). Qed.
Lemma lem4377292 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem4377293 {_104961 : Type'} (t : _104961 -> Prop) (p2 : _104961) : (term23 _104961 t p2) = True.
Proof. exact (@lem4377292 (t p2)). Qed.
Lemma lem4377294 {_104961 : Type'} (p2 : _104961) (t : _104961 -> Prop) : (term22 _104961 p2 t) = True.
Proof. exact (TRANS (@lem4377290 _104961 t p2) (@lem4377293 _104961 t p2)). Qed.
Lemma lem4377295 {_104961 : Type'} (p2 : _104961) : (term24 _104961 p2) = (term25 _104961).
Proof. exact (fun_ext (fun t : _104961 -> Prop => @lem4377294 _104961 p2 t)). Qed.
Lemma lem4377296 {_104961 : Type'} : (@all (_104961 -> Prop)) = (@all (_104961 -> Prop)).
Proof. exact (eq_refl (@all (_104961 -> Prop))). Qed.
Lemma lem4377297 {_104961 : Type'} (p2 : _104961) : (term20 _104961 p2) = (term26 _104961).
Proof. exact (MK_COMB (@lem4377296 _104961) (@lem4377295 _104961 p2)). Qed.
Lemma lem4377299 {A : Type'} (t : Prop) : (term27 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4377300 {_104961 : Type'} (t : Prop) : (term28 _104961 t) = t.
Proof. exact (@lem4377299 (_104961 -> Prop) t). Qed.
Lemma lem4377301 {_104961 : Type'} : (term26 _104961) = True.
Proof. exact (@lem4377300 _104961 True). Qed.
Lemma lem4377302 {_104961 : Type'} (p2 : _104961) : (term20 _104961 p2) = True.
Proof. exact (TRANS (@lem4377297 _104961 p2) (@lem4377301 _104961)). Qed.
Lemma lem4377303 {_104961 : Type'} (p2 : _104961) : (term19 _104961 p2) = True.
Proof. exact (TRANS (@lem4377273 _104961 p2) (@lem4377302 _104961 p2)). Qed.
Lemma lem4377304 {_104960 _104961 : Type'} (p2 : _104961) (s : _104960 -> Prop) (p1 : _104960) : (term29 _104960 _104961 p1 s p2) = (term30 _104960 s p1).
Proof. exact (MK_COMB (@lem4377269 _104960 s p1) (@lem4377303 _104961 p2)). Qed.
Lemma lem4377306 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem4377307 {_104960 : Type'} (s : _104960 -> Prop) (p1 : _104960) : (term30 _104960 s p1) = (s p1).
Proof. exact (@lem4377306 (s p1)). Qed.
Lemma lem4377308 {_104960 _104961 : Type'} (p2 : _104961) (s : _104960 -> Prop) (p1 : _104960) : (term29 _104960 _104961 p1 s p2) = (s p1).
Proof. exact (TRANS (@lem4377304 _104960 _104961 p2 s p1) (@lem4377307 _104960 s p1)). Qed.
Lemma lem4377309 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4377310 {_104960 _104961 : Type'} (p2 : _104961) (s : _104960 -> Prop) (p1 : _104960) : (term31 _104960 _104961 p1 s p2) = (term32 _104960 s p1).
Proof. exact (MK_COMB (@lem4377309) (@lem4377308 _104960 _104961 p2 s p1)). Qed.
Lemma lem4377314 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4377315 {_104960 : Type'} (P : _104960 -> Prop) (x : _104960) : (@IN _104960 x P) = (P x).
Proof. exact (@lem4377314 _104960 P x). Qed.
Lemma lem4377316 {_104960 : Type'} (s : _104960 -> Prop) (p1 : _104960) : (@IN _104960 p1 s) = (s p1).
Proof. exact (@lem4377315 _104960 s p1). Qed.
Lemma lem4377317 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4377318 {_104960 : Type'} (s : _104960 -> Prop) (p1 : _104960) : (term15 _104960 p1 s) = (term16 _104960 s p1).
Proof. exact (MK_COMB (@lem4377317) (@lem4377316 _104960 s p1)). Qed.
Lemma lem4377320 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem4377321 {_104961 : Type'} (x : _104961) : (@IN _104961 x (@UNIV _104961)) = True.
Proof. exact (@lem4377320 _104961 x). Qed.
Lemma lem4377322 {_104961 : Type'} (p2 : _104961) : (@IN _104961 p2 (@UNIV _104961)) = True.
Proof. exact (@lem4377321 _104961 p2). Qed.
Lemma lem4377323 {_104960 _104961 : Type'} (p2 : _104961) (s : _104960 -> Prop) (p1 : _104960) : (term33 _104960 _104961 p1 s p2) = (term30 _104960 s p1).
Proof. exact (MK_COMB (@lem4377318 _104960 s p1) (@lem4377322 _104961 p2)). Qed.
Lemma lem4377325 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem4377326 {_104960 : Type'} (s : _104960 -> Prop) (p1 : _104960) : (term30 _104960 s p1) = (s p1).
Proof. exact (@lem4377325 (s p1)). Qed.
Lemma lem4377327 {_104960 _104961 : Type'} (p2 : _104961) (s : _104960 -> Prop) (p1 : _104960) : (term33 _104960 _104961 p1 s p2) = (s p1).
Proof. exact (TRANS (@lem4377323 _104960 _104961 p2 s p1) (@lem4377326 _104960 s p1)). Qed.
Lemma lem4377328 {_104960 _104961 : Type'} (p2 : _104961) (s : _104960 -> Prop) (p1 : _104960) : ((term29 _104960 _104961 p1 s p2) = (term33 _104960 _104961 p1 s p2)) = ((s p1) = (s p1)).
Proof. exact (MK_COMB (@lem4377310 _104960 _104961 p2 s p1) (@lem4377327 _104960 _104961 p2 s p1)). Qed.
Lemma lem4377330 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4377331 (x : Prop) : (x = x) = True.
Proof. exact (@lem4377330 Prop x). Qed.
Lemma lem4377332 {_104960 : Type'} (s : _104960 -> Prop) (p1 : _104960) : ((s p1) = (s p1)) = True.
Proof. exact (@lem4377331 (s p1)). Qed.
Lemma lem4377333 {_104960 _104961 : Type'} (p1 : _104960) (s : _104960 -> Prop) (p2 : _104961) : ((term29 _104960 _104961 p1 s p2) = (term33 _104960 _104961 p1 s p2)) = True.
Proof. exact (TRANS (@lem4377328 _104960 _104961 p2 s p1) (@lem4377332 _104960 s p1)). Qed.
Lemma lem4377334 {_104960 _104961 : Type'} (p1 : _104960) (s : _104960 -> Prop) : (term34 _104960 _104961 p1 s) = (term35 _104961).
Proof. exact (fun_ext (fun p2 : _104961 => @lem4377333 _104960 _104961 p1 s p2)). Qed.
Lemma lem4377335 {_104961 : Type'} : (@all _104961) = (@all _104961).
Proof. exact (eq_refl (@all _104961)). Qed.
Lemma lem4377336 {_104960 _104961 : Type'} (p1 : _104960) (s : _104960 -> Prop) : (term36 _104960 _104961 p1 s) = (term37 _104961).
Proof. exact (MK_COMB (@lem4377335 _104961) (@lem4377334 _104960 _104961 p1 s)). Qed.
Lemma lem4377338 {A : Type'} (t : Prop) : (term27 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4377339 {_104961 : Type'} (t : Prop) : (term27 _104961 t) = t.
Proof. exact (@lem4377338 _104961 t). Qed.
Lemma lem4377340 {_104961 : Type'} : (term37 _104961) = True.
Proof. exact (@lem4377339 _104961 True). Qed.
Lemma lem4377341 {_104960 _104961 : Type'} (p1 : _104960) (s : _104960 -> Prop) : (term36 _104960 _104961 p1 s) = True.
Proof. exact (TRANS (@lem4377336 _104960 _104961 p1 s) (@lem4377340 _104961)). Qed.
Lemma lem4377342 {_104960 _104961 : Type'} (s : _104960 -> Prop) : (term38 _104960 _104961 s) = (term35 _104960).
Proof. exact (fun_ext (fun p1 : _104960 => @lem4377341 _104960 _104961 p1 s)). Qed.
Lemma lem4377343 {_104960 : Type'} : (@all _104960) = (@all _104960).
Proof. exact (eq_refl (@all _104960)). Qed.
Lemma lem4377344 {_104960 _104961 : Type'} (s : _104960 -> Prop) : (term5 _104960 _104961 s) = (term37 _104960).
Proof. exact (MK_COMB (@lem4377343 _104960) (@lem4377342 _104960 _104961 s)). Qed.
Lemma lem4377346 {A : Type'} (t : Prop) : (term27 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4377347 {_104960 : Type'} (t : Prop) : (term27 _104960 t) = t.
Proof. exact (@lem4377346 _104960 t). Qed.
Lemma lem4377348 {_104960 : Type'} : (term37 _104960) = True.
Proof. exact (@lem4377347 _104960 True). Qed.
Lemma lem4377349 {_104960 _104961 : Type'} (s : _104960 -> Prop) : (term5 _104960 _104961 s) = True.
Proof. exact (TRANS (@lem4377344 _104960 _104961 s) (@lem4377348 _104960)). Qed.
Lemma lem4377350 {_104960 _104961 : Type'} (s : _104960 -> Prop) (f : type686 _104961) : (term7 _104960 _104961 f s) = (term39 _104961 f).
Proof. exact (MK_COMB (@lem4377251 _104961 f) (@lem4377349 _104960 _104961 s)). Qed.
Lemma lem4377352 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4377353 {_104961 : Type'} (f : type686 _104961) : (term39 _104961 f) = True.
Proof. exact (@lem4377352 (term13 _104961 f)). Qed.
Lemma lem4377354 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term7 _104960 _104961 f s) = True.
Proof. exact (TRANS (@lem4377350 _104960 _104961 s f) (@lem4377353 _104961 f)). Qed.
Lemma lem4377355 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : True = (term7 _104960 _104961 f s).
Proof. exact (SYM (@lem4377354 _104960 _104961 f s)). Qed.
Lemma lem4377356 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : term7 _104960 _104961 f s.
Proof. exact (EQ_MP (@lem4377355 _104960 _104961 f s) (@lem0)). Qed.
Lemma lem4377357 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : term6 _104960 _104961 f s.
Proof. exact (EQ_MP (@lem4377220 _104960 _104961 f s) (@lem4377356 _104960 _104961 f s)). Qed.
Lemma lem4377358 {_104960 _104961 : Type'} (s : _104960 -> Prop) (f : type686 _104961) (h1 : f = (@EMPTY (_104961 -> Prop))) : term5 _104960 _104961 s.
Proof. exact (@lem4377357 _104960 _104961 f s (@lem4372329 _104961 f h1)). Qed.
