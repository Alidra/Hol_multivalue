Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm8051509_term_abbrevs.
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
Require Import thm8048867_spec.
Require Import thm8048932_spec.
Lemma lem8051198 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (h1 : term0 _142951 _142952 f) (h2 : g = (@EMPTY ((cart _142951 _142953) -> Prop))) : term1 _142951 _142952 _142953 g f.
Proof. exact (conj (@lem8048932 _142951 _142953 g h2) (@lem8048867 _142951 _142952 f h1)). Qed.
Lemma lem8051206 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term2 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem8051207 {_142951 _142953 : Type'} (s : type56 _142951 _142953) (t : type56 _142951 _142953) : (s = t) = (term3 _142951 _142953 s t).
Proof. exact (@lem8051206 (type24 _142951 _142953) s t). Qed.
Lemma lem8051208 {_142951 _142953 : Type'} (g : type56 _142951 _142953) : (g = (@EMPTY ((cart _142951 _142953) -> Prop))) = (term4 _142951 _142953 g).
Proof. exact (@lem8051207 _142951 _142953 g (@EMPTY ((cart _142951 _142953) -> Prop))). Qed.
Lemma lem8051217 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8051218 {_142951 _142953 : Type'} (g : type56 _142951 _142953) : (term5 _142951 _142953 g) = (term6 _142951 _142953 g).
Proof. exact (MK_COMB (@lem8051217) (@lem8051208 _142951 _142953 g)). Qed.
Lemma lem8051222 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term2 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem8051223 {_142951 _142952 : Type'} (s : type56 _142951 _142952) (t : type56 _142951 _142952) : (s = t) = (term3 _142951 _142952 s t).
Proof. exact (@lem8051222 (type24 _142951 _142952) s t). Qed.
Lemma lem8051224 {_142951 _142952 : Type'} (f : type56 _142951 _142952) : (f = (@EMPTY ((cart _142951 _142952) -> Prop))) = (term4 _142951 _142952 f).
Proof. exact (@lem8051223 _142951 _142952 f (@EMPTY ((cart _142951 _142952) -> Prop))). Qed.
Lemma lem8051233 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8051234 {_142951 _142952 : Type'} (f : type56 _142951 _142952) : (term0 _142951 _142952 f) = (term7 _142951 _142952 f).
Proof. exact (MK_COMB (@lem8051233) (@lem8051224 _142951 _142952 f)). Qed.
Lemma lem8051235 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) : (term1 _142951 _142952 _142953 g f) = (term8 _142951 _142952 _142953 g f).
Proof. exact (MK_COMB (@lem8051218 _142951 _142953 g) (@lem8051234 _142951 _142952 f)). Qed.
Lemma lem8051238 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8051239 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) : (term9 _142951 _142952 _142953 g f) = (term10 _142951 _142952 _142953 g f).
Proof. exact (MK_COMB (@lem8051238) (@lem8051235 _142951 _142952 _142953 g f)). Qed.
Lemma lem8051262 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) : (term11 _142951 _142952 _142953 f) = (term11 _142951 _142952 _142953 f).
Proof. exact (eq_refl (term11 _142951 _142952 _142953 f)). Qed.
Lemma lem8051263 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) : (term12 _142951 _142952 _142953 g f) = (term13 _142951 _142952 _142953 g f).
Proof. exact (MK_COMB (@lem8051239 _142951 _142952 _142953 g f) (@lem8051262 _142951 _142952 _142953 f)). Qed.
Lemma lem8051266 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) : (term13 _142951 _142952 _142953 g f) = (term12 _142951 _142952 _142953 g f).
Proof. exact (SYM (@lem8051263 _142951 _142952 _142953 g f)). Qed.
Lemma lem8051278 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8051279 {_142951 _142953 : Type'} (P : type56 _142951 _142953) (x : type24 _142951 _142953) : (@IN ((cart _142951 _142953) -> Prop) x P) = (P x).
Proof. exact (@lem8051278 (type24 _142951 _142953) P x). Qed.
Lemma lem8051280 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (x : type24 _142951 _142953) : (@IN ((cart _142951 _142953) -> Prop) x g) = (g x).
Proof. exact (@lem8051279 _142951 _142953 g x). Qed.
Lemma lem8051281 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8051282 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (x : type24 _142951 _142953) : (term14 _142951 _142953 x g) = (term15 _142951 _142953 g x).
Proof. exact (MK_COMB (@lem8051281) (@lem8051280 _142951 _142953 g x)). Qed.
Lemma lem8051284 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem8051285 {_142951 _142953 : Type'} (x : type24 _142951 _142953) : (@IN ((cart _142951 _142953) -> Prop) x (@EMPTY ((cart _142951 _142953) -> Prop))) = False.
Proof. exact (@lem8051284 (type24 _142951 _142953) x). Qed.
Lemma lem8051286 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (x : type24 _142951 _142953) : ((@IN ((cart _142951 _142953) -> Prop) x g) = (@IN ((cart _142951 _142953) -> Prop) x (@EMPTY ((cart _142951 _142953) -> Prop)))) = ((g x) = False).
Proof. exact (MK_COMB (@lem8051282 _142951 _142953 g x) (@lem8051285 _142951 _142953 x)). Qed.
Lemma lem8051288 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem8051289 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (x : type24 _142951 _142953) : ((g x) = False) = (term16 _142951 _142953 g x).
Proof. exact (@lem8051288 (g x)). Qed.
Lemma lem8051290 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (x : type24 _142951 _142953) : ((@IN ((cart _142951 _142953) -> Prop) x g) = (@IN ((cart _142951 _142953) -> Prop) x (@EMPTY ((cart _142951 _142953) -> Prop)))) = (term16 _142951 _142953 g x).
Proof. exact (TRANS (@lem8051286 _142951 _142953 g x) (@lem8051289 _142951 _142953 g x)). Qed.
Lemma lem8051291 {_142951 _142953 : Type'} (g : type56 _142951 _142953) : (term17 _142951 _142953 g) = (term18 _142951 _142953 g).
Proof. exact (fun_ext (fun x : type24 _142951 _142953 => @lem8051290 _142951 _142953 g x)). Qed.
Lemma lem8051292 {_142951 _142953 : Type'} : (@all ((cart _142951 _142953) -> Prop)) = (@all ((cart _142951 _142953) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142951 _142953) -> Prop))). Qed.
Lemma lem8051293 {_142951 _142953 : Type'} (g : type56 _142951 _142953) : (term4 _142951 _142953 g) = (term19 _142951 _142953 g).
Proof. exact (MK_COMB (@lem8051292 _142951 _142953) (@lem8051291 _142951 _142953 g)). Qed.
Lemma lem8051298 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8051299 {_142951 _142953 : Type'} (g : type56 _142951 _142953) : (term6 _142951 _142953 g) = (term20 _142951 _142953 g).
Proof. exact (MK_COMB (@lem8051298) (@lem8051293 _142951 _142953 g)). Qed.
Lemma lem8051307 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8051308 {_142951 _142952 : Type'} (P : type56 _142951 _142952) (x : type24 _142951 _142952) : (@IN ((cart _142951 _142952) -> Prop) x P) = (P x).
Proof. exact (@lem8051307 (type24 _142951 _142952) P x). Qed.
Lemma lem8051309 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : type24 _142951 _142952) : (@IN ((cart _142951 _142952) -> Prop) x f) = (f x).
Proof. exact (@lem8051308 _142951 _142952 f x). Qed.
Lemma lem8051310 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8051311 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : type24 _142951 _142952) : (term14 _142951 _142952 x f) = (term15 _142951 _142952 f x).
Proof. exact (MK_COMB (@lem8051310) (@lem8051309 _142951 _142952 f x)). Qed.
Lemma lem8051313 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem8051314 {_142951 _142952 : Type'} (x : type24 _142951 _142952) : (@IN ((cart _142951 _142952) -> Prop) x (@EMPTY ((cart _142951 _142952) -> Prop))) = False.
Proof. exact (@lem8051313 (type24 _142951 _142952) x). Qed.
Lemma lem8051315 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : type24 _142951 _142952) : ((@IN ((cart _142951 _142952) -> Prop) x f) = (@IN ((cart _142951 _142952) -> Prop) x (@EMPTY ((cart _142951 _142952) -> Prop)))) = ((f x) = False).
Proof. exact (MK_COMB (@lem8051311 _142951 _142952 f x) (@lem8051314 _142951 _142952 x)). Qed.
Lemma lem8051317 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem8051318 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : type24 _142951 _142952) : ((f x) = False) = (term16 _142951 _142952 f x).
Proof. exact (@lem8051317 (f x)). Qed.
Lemma lem8051319 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : type24 _142951 _142952) : ((@IN ((cart _142951 _142952) -> Prop) x f) = (@IN ((cart _142951 _142952) -> Prop) x (@EMPTY ((cart _142951 _142952) -> Prop)))) = (term16 _142951 _142952 f x).
Proof. exact (TRANS (@lem8051315 _142951 _142952 f x) (@lem8051318 _142951 _142952 f x)). Qed.
Lemma lem8051320 {_142951 _142952 : Type'} (f : type56 _142951 _142952) : (term17 _142951 _142952 f) = (term18 _142951 _142952 f).
Proof. exact (fun_ext (fun x : type24 _142951 _142952 => @lem8051319 _142951 _142952 f x)). Qed.
Lemma lem8051321 {_142951 _142952 : Type'} : (@all ((cart _142951 _142952) -> Prop)) = (@all ((cart _142951 _142952) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142951 _142952) -> Prop))). Qed.
Lemma lem8051322 {_142951 _142952 : Type'} (f : type56 _142951 _142952) : (term4 _142951 _142952 f) = (term19 _142951 _142952 f).
Proof. exact (MK_COMB (@lem8051321 _142951 _142952) (@lem8051320 _142951 _142952 f)). Qed.
Lemma lem8051327 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8051328 {_142951 _142952 : Type'} (f : type56 _142951 _142952) : (term7 _142951 _142952 f) = (term21 _142951 _142952 f).
Proof. exact (MK_COMB (@lem8051327) (@lem8051322 _142951 _142952 f)). Qed.
Lemma lem8051329 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) : (term8 _142951 _142952 _142953 g f) = (term22 _142951 _142952 _142953 g f).
Proof. exact (MK_COMB (@lem8051299 _142951 _142953 g) (@lem8051328 _142951 _142952 f)). Qed.
Lemma lem8051332 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8051333 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) : (term10 _142951 _142952 _142953 g f) = (term23 _142951 _142952 _142953 g f).
Proof. exact (MK_COMB (@lem8051332) (@lem8051329 _142951 _142952 _142953 g f)). Qed.
Lemma lem8051347 {A : Type'} (s : type686 A) (x : A) : (term24 A x s) = (term25 A s x).
Proof. exact (EQ_MP (@lem3211669 A s x) (@lem3211668 A s x)). Qed.
Lemma lem8051348 {_142951 _142952 : Type'} (s : type56 _142951 _142952) (x : cart _142951 _142952) : (term26 _142951 _142952 x s) = (term27 _142951 _142952 s x).
Proof. exact (@lem8051347 (cart _142951 _142952) s x). Qed.
Lemma lem8051349 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) : (term26 _142951 _142952 x f) = (term27 _142951 _142952 f x).
Proof. exact (@lem8051348 _142951 _142952 f x). Qed.
Lemma lem8051357 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8051358 {_142951 _142952 : Type'} (P : type56 _142951 _142952) (x : type24 _142951 _142952) : (@IN ((cart _142951 _142952) -> Prop) x P) = (P x).
Proof. exact (@lem8051357 (type24 _142951 _142952) P x). Qed.
Lemma lem8051359 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (t : type24 _142951 _142952) : (@IN ((cart _142951 _142952) -> Prop) t f) = (f t).
Proof. exact (@lem8051358 _142951 _142952 f t). Qed.
Lemma lem8051360 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8051361 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (t : type24 _142951 _142952) : (term28 _142951 _142952 t f) = (term29 _142951 _142952 f t).
Proof. exact (MK_COMB (@lem8051360) (@lem8051359 _142951 _142952 f t)). Qed.
Lemma lem8051363 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8051364 {_142951 _142952 : Type'} (P : type24 _142951 _142952) (x : cart _142951 _142952) : (@IN (cart _142951 _142952) x P) = (P x).
Proof. exact (@lem8051363 (cart _142951 _142952) P x). Qed.
Lemma lem8051365 {_142951 _142952 : Type'} (t : type24 _142951 _142952) (x : cart _142951 _142952) : (@IN (cart _142951 _142952) x t) = (t x).
Proof. exact (@lem8051364 _142951 _142952 t x). Qed.
Lemma lem8051366 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (t : type24 _142951 _142952) (x : cart _142951 _142952) : (term30 _142951 _142952 f x t) = (term31 _142951 _142952 f t x).
Proof. exact (MK_COMB (@lem8051361 _142951 _142952 f t) (@lem8051365 _142951 _142952 t x)). Qed.
Lemma lem8051369 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) : (term32 _142951 _142952 f x) = (term33 _142951 _142952 f x).
Proof. exact (fun_ext (fun t : type24 _142951 _142952 => @lem8051366 _142951 _142952 f t x)). Qed.
Lemma lem8051370 {_142951 _142952 : Type'} : (@all ((cart _142951 _142952) -> Prop)) = (@all ((cart _142951 _142952) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142951 _142952) -> Prop))). Qed.
Lemma lem8051371 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) : (term27 _142951 _142952 f x) = (term34 _142951 _142952 f x).
Proof. exact (MK_COMB (@lem8051370 _142951 _142952) (@lem8051369 _142951 _142952 f x)). Qed.
Lemma lem8051376 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) : (term26 _142951 _142952 x f) = (term34 _142951 _142952 f x).
Proof. exact (TRANS (@lem8051349 _142951 _142952 f x) (@lem8051371 _142951 _142952 f x)). Qed.
Lemma lem8051377 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8051378 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) : (term35 _142951 _142952 x f) = (term36 _142951 _142952 f x).
Proof. exact (MK_COMB (@lem8051377) (@lem8051376 _142951 _142952 f x)). Qed.
Lemma lem8051380 {A : Type'} (s : type686 A) (x : A) : (term24 A x s) = (term25 A s x).
Proof. exact (EQ_MP (@lem3211669 A s x) (@lem3211668 A s x)). Qed.
Lemma lem8051381 {_142951 _142953 : Type'} (s : type56 _142951 _142953) (x : cart _142951 _142953) : (term26 _142951 _142953 x s) = (term27 _142951 _142953 s x).
Proof. exact (@lem8051380 (cart _142951 _142953) s x). Qed.
Lemma lem8051382 {_142951 _142953 : Type'} (y : cart _142951 _142953) : (term37 _142951 _142953 y) = (term38 _142951 _142953 y).
Proof. exact (@lem8051381 _142951 _142953 (@EMPTY ((cart _142951 _142953) -> Prop)) y). Qed.
Lemma lem8051390 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem8051391 {_142951 _142953 : Type'} (x : type24 _142951 _142953) : (@IN ((cart _142951 _142953) -> Prop) x (@EMPTY ((cart _142951 _142953) -> Prop))) = False.
Proof. exact (@lem8051390 (type24 _142951 _142953) x). Qed.
Lemma lem8051392 {_142951 _142953 : Type'} (t : type24 _142951 _142953) : (@IN ((cart _142951 _142953) -> Prop) t (@EMPTY ((cart _142951 _142953) -> Prop))) = False.
Proof. exact (@lem8051391 _142951 _142953 t). Qed.
Lemma lem8051393 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8051394 {_142951 _142953 : Type'} (t : type24 _142951 _142953) : (term39 _142951 _142953 t) = (imp False).
Proof. exact (MK_COMB (@lem8051393) (@lem8051392 _142951 _142953 t)). Qed.
Lemma lem8051396 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8051397 {_142951 _142953 : Type'} (P : type24 _142951 _142953) (x : cart _142951 _142953) : (@IN (cart _142951 _142953) x P) = (P x).
Proof. exact (@lem8051396 (cart _142951 _142953) P x). Qed.
Lemma lem8051398 {_142951 _142953 : Type'} (t : type24 _142951 _142953) (y : cart _142951 _142953) : (@IN (cart _142951 _142953) y t) = (t y).
Proof. exact (@lem8051397 _142951 _142953 t y). Qed.
Lemma lem8051399 {_142951 _142953 : Type'} (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term40 _142951 _142953 y t) = (term41 _142951 _142953 t y).
Proof. exact (MK_COMB (@lem8051394 _142951 _142953 t) (@lem8051398 _142951 _142953 t y)). Qed.
Lemma lem8051401 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem8051402 {_142951 _142953 : Type'} (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term41 _142951 _142953 t y) = True.
Proof. exact (@lem8051401 (t y)). Qed.
Lemma lem8051403 {_142951 _142953 : Type'} (y : cart _142951 _142953) (t : type24 _142951 _142953) : (term40 _142951 _142953 y t) = True.
Proof. exact (TRANS (@lem8051399 _142951 _142953 t y) (@lem8051402 _142951 _142953 t y)). Qed.
Lemma lem8051404 {_142951 _142953 : Type'} (y : cart _142951 _142953) : (term42 _142951 _142953 y) = (term43 _142951 _142953).
Proof. exact (fun_ext (fun t : type24 _142951 _142953 => @lem8051403 _142951 _142953 y t)). Qed.
Lemma lem8051405 {_142951 _142953 : Type'} : (@all ((cart _142951 _142953) -> Prop)) = (@all ((cart _142951 _142953) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142951 _142953) -> Prop))). Qed.
Lemma lem8051406 {_142951 _142953 : Type'} (y : cart _142951 _142953) : (term38 _142951 _142953 y) = (term44 _142951 _142953).
Proof. exact (MK_COMB (@lem8051405 _142951 _142953) (@lem8051404 _142951 _142953 y)). Qed.
Lemma lem8051408 {A : Type'} (t : Prop) : (term45 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8051409 {_142951 _142953 : Type'} (t : Prop) : (term46 _142951 _142953 t) = t.
Proof. exact (@lem8051408 (type24 _142951 _142953) t). Qed.
Lemma lem8051410 {_142951 _142953 : Type'} : (term44 _142951 _142953) = True.
Proof. exact (@lem8051409 _142951 _142953 True). Qed.
Lemma lem8051411 {_142951 _142953 : Type'} (y : cart _142951 _142953) : (term38 _142951 _142953 y) = True.
Proof. exact (TRANS (@lem8051406 _142951 _142953 y) (@lem8051410 _142951 _142953)). Qed.
Lemma lem8051412 {_142951 _142953 : Type'} (y : cart _142951 _142953) : (term37 _142951 _142953 y) = True.
Proof. exact (TRANS (@lem8051382 _142951 _142953 y) (@lem8051411 _142951 _142953 y)). Qed.
Lemma lem8051413 {_142951 _142952 _142953 : Type'} (y : cart _142951 _142953) (f : type56 _142951 _142952) (x : cart _142951 _142952) : (term47 _142951 _142952 _142953 x f y) = (term48 _142951 _142952 f x).
Proof. exact (MK_COMB (@lem8051378 _142951 _142952 f x) (@lem8051412 _142951 _142953 y)). Qed.
Lemma lem8051415 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem8051416 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) : (term48 _142951 _142952 f x) = (term34 _142951 _142952 f x).
Proof. exact (@lem8051415 (term34 _142951 _142952 f x)). Qed.
Lemma lem8051423 {_142951 _142952 _142953 : Type'} (y : cart _142951 _142953) (f : type56 _142951 _142952) (x : cart _142951 _142952) : (term47 _142951 _142952 _142953 x f y) = (term34 _142951 _142952 f x).
Proof. exact (TRANS (@lem8051413 _142951 _142952 _142953 y f x) (@lem8051416 _142951 _142952 f x)). Qed.
Lemma lem8051424 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8051425 {_142951 _142952 _142953 : Type'} (y : cart _142951 _142953) (f : type56 _142951 _142952) (x : cart _142951 _142952) : (term49 _142951 _142952 _142953 x f y) = (term50 _142951 _142952 f x).
Proof. exact (MK_COMB (@lem8051424) (@lem8051423 _142951 _142952 _142953 y f x)). Qed.
Lemma lem8051433 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8051434 {_142951 _142952 : Type'} (P : type56 _142951 _142952) (x : type24 _142951 _142952) : (@IN ((cart _142951 _142952) -> Prop) x P) = (P x).
Proof. exact (@lem8051433 (type24 _142951 _142952) P x). Qed.
Lemma lem8051435 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (s : type24 _142951 _142952) : (@IN ((cart _142951 _142952) -> Prop) s f) = (f s).
Proof. exact (@lem8051434 _142951 _142952 f s). Qed.
Lemma lem8051436 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8051437 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (s : type24 _142951 _142952) : (term28 _142951 _142952 s f) = (term29 _142951 _142952 f s).
Proof. exact (MK_COMB (@lem8051436) (@lem8051435 _142951 _142952 f s)). Qed.
Lemma lem8051441 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8051442 {_142951 _142952 : Type'} (P : type24 _142951 _142952) (x : cart _142951 _142952) : (@IN (cart _142951 _142952) x P) = (P x).
Proof. exact (@lem8051441 (cart _142951 _142952) P x). Qed.
Lemma lem8051443 {_142951 _142952 : Type'} (s : type24 _142951 _142952) (x : cart _142951 _142952) : (@IN (cart _142951 _142952) x s) = (s x).
Proof. exact (@lem8051442 _142951 _142952 s x). Qed.
Lemma lem8051444 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8051445 {_142951 _142952 : Type'} (s : type24 _142951 _142952) (x : cart _142951 _142952) : (term51 _142951 _142952 x s) = (term52 _142951 _142952 s x).
Proof. exact (MK_COMB (@lem8051444) (@lem8051443 _142951 _142952 s x)). Qed.
Lemma lem8051447 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem8051448 {_142951 _142953 : Type'} (x : cart _142951 _142953) : (@IN (cart _142951 _142953) x (@UNIV (cart _142951 _142953))) = True.
Proof. exact (@lem8051447 (cart _142951 _142953) x). Qed.
Lemma lem8051449 {_142951 _142953 : Type'} (y : cart _142951 _142953) : (@IN (cart _142951 _142953) y (@UNIV (cart _142951 _142953))) = True.
Proof. exact (@lem8051448 _142951 _142953 y). Qed.
Lemma lem8051450 {_142951 _142952 _142953 : Type'} (y : cart _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) : (term53 _142951 _142952 _142953 x s y) = (term54 _142951 _142952 s x).
Proof. exact (MK_COMB (@lem8051445 _142951 _142952 s x) (@lem8051449 _142951 _142953 y)). Qed.
Lemma lem8051452 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem8051453 {_142951 _142952 : Type'} (s : type24 _142951 _142952) (x : cart _142951 _142952) : (term54 _142951 _142952 s x) = (s x).
Proof. exact (@lem8051452 (s x)). Qed.
Lemma lem8051454 {_142951 _142952 _142953 : Type'} (y : cart _142951 _142953) (s : type24 _142951 _142952) (x : cart _142951 _142952) : (term53 _142951 _142952 _142953 x s y) = (s x).
Proof. exact (TRANS (@lem8051450 _142951 _142952 _142953 y s x) (@lem8051453 _142951 _142952 s x)). Qed.
Lemma lem8051455 {_142951 _142952 _142953 : Type'} (y : cart _142951 _142953) (f : type56 _142951 _142952) (s : type24 _142951 _142952) (x : cart _142951 _142952) : (term55 _142951 _142952 _142953 f x s y) = (term31 _142951 _142952 f s x).
Proof. exact (MK_COMB (@lem8051437 _142951 _142952 f s) (@lem8051454 _142951 _142952 _142953 y s x)). Qed.
Lemma lem8051458 {_142951 _142952 _142953 : Type'} (y : cart _142951 _142953) (f : type56 _142951 _142952) (x : cart _142951 _142952) : (term56 _142951 _142952 _142953 f x y) = (term33 _142951 _142952 f x).
Proof. exact (fun_ext (fun s : type24 _142951 _142952 => @lem8051455 _142951 _142952 _142953 y f s x)). Qed.
Lemma lem8051459 {_142951 _142952 : Type'} : (@all ((cart _142951 _142952) -> Prop)) = (@all ((cart _142951 _142952) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142951 _142952) -> Prop))). Qed.
Lemma lem8051460 {_142951 _142952 _142953 : Type'} (y : cart _142951 _142953) (f : type56 _142951 _142952) (x : cart _142951 _142952) : (term57 _142951 _142952 _142953 f x y) = (term34 _142951 _142952 f x).
Proof. exact (MK_COMB (@lem8051459 _142951 _142952) (@lem8051458 _142951 _142952 _142953 y f x)). Qed.
Lemma lem8051465 {_142951 _142952 _142953 : Type'} (y : cart _142951 _142953) (f : type56 _142951 _142952) (x : cart _142951 _142952) : ((term47 _142951 _142952 _142953 x f y) = (term57 _142951 _142952 _142953 f x y)) = ((term34 _142951 _142952 f x) = (term34 _142951 _142952 f x)).
Proof. exact (MK_COMB (@lem8051425 _142951 _142952 _142953 y f x) (@lem8051460 _142951 _142952 _142953 y f x)). Qed.
Lemma lem8051467 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem8051468 (x : Prop) : (x = x) = True.
Proof. exact (@lem8051467 Prop x). Qed.
Lemma lem8051469 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) : ((term34 _142951 _142952 f x) = (term34 _142951 _142952 f x)) = True.
Proof. exact (@lem8051468 (term34 _142951 _142952 f x)). Qed.
Lemma lem8051472 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) : (term58 _142951 _142952 f x) = (term58 _142951 _142952 f x).
Proof. exact (eq_refl (term58 _142951 _142952 f x)). Qed.
Lemma lem8051473 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) : (term58 _142951 _142952 f x) = (((term34 _142951 _142952 f x) = (term34 _142951 _142952 f x)) = True).
Proof. exact (eq_refl (term58 _142951 _142952 f x)). Qed.
Lemma lem8051474 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) : (term59 _142951 _142952 f x) = (term59 _142951 _142952 f x).
Proof. exact (eq_refl (term59 _142951 _142952 f x)). Qed.
Lemma lem8051475 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) : ((term58 _142951 _142952 f x) = (term58 _142951 _142952 f x)) = ((term58 _142951 _142952 f x) = (((term34 _142951 _142952 f x) = (term34 _142951 _142952 f x)) = True)).
Proof. exact (MK_COMB (@lem8051474 _142951 _142952 f x) (@lem8051473 _142951 _142952 f x)). Qed.
Lemma lem8051476 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) : (term58 _142951 _142952 f x) = (((term34 _142951 _142952 f x) = (term34 _142951 _142952 f x)) = True).
Proof. exact (eq_refl (term58 _142951 _142952 f x)). Qed.
Lemma lem8051477 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8051478 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) : (term59 _142951 _142952 f x) = (term60 _142951 _142952 f x).
Proof. exact (MK_COMB (@lem8051477) (@lem8051476 _142951 _142952 f x)). Qed.
Lemma lem8051479 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) : (((term34 _142951 _142952 f x) = (term34 _142951 _142952 f x)) = True) = (((term34 _142951 _142952 f x) = (term34 _142951 _142952 f x)) = True).
Proof. exact (eq_refl (((term34 _142951 _142952 f x) = (term34 _142951 _142952 f x)) = True)). Qed.
Lemma lem8051480 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) : ((term58 _142951 _142952 f x) = (((term34 _142951 _142952 f x) = (term34 _142951 _142952 f x)) = True)) = ((((term34 _142951 _142952 f x) = (term34 _142951 _142952 f x)) = True) = (((term34 _142951 _142952 f x) = (term34 _142951 _142952 f x)) = True)).
Proof. exact (MK_COMB (@lem8051478 _142951 _142952 f x) (@lem8051479 _142951 _142952 f x)). Qed.
Lemma lem8051481 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) : ((term58 _142951 _142952 f x) = (term58 _142951 _142952 f x)) = ((((term34 _142951 _142952 f x) = (term34 _142951 _142952 f x)) = True) = (((term34 _142951 _142952 f x) = (term34 _142951 _142952 f x)) = True)).
Proof. exact (TRANS (@lem8051475 _142951 _142952 f x) (@lem8051480 _142951 _142952 f x)). Qed.
Lemma lem8051482 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) : (((term34 _142951 _142952 f x) = (term34 _142951 _142952 f x)) = True) = (((term34 _142951 _142952 f x) = (term34 _142951 _142952 f x)) = True).
Proof. exact (EQ_MP (@lem8051481 _142951 _142952 f x) (@lem8051472 _142951 _142952 f x)). Qed.
Lemma lem8051483 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) : ((term34 _142951 _142952 f x) = (term34 _142951 _142952 f x)) = True.
Proof. exact (EQ_MP (@lem8051482 _142951 _142952 f x) (@lem8051469 _142951 _142952 f x)). Qed.
Lemma lem8051484 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) (y : cart _142951 _142953) : ((term47 _142951 _142952 _142953 x f y) = (term57 _142951 _142952 _142953 f x y)) = True.
Proof. exact (TRANS (@lem8051465 _142951 _142952 _142953 y f x) (@lem8051483 _142951 _142952 f x)). Qed.
Lemma lem8051485 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) : (term61 _142951 _142952 _142953 f x) = (term62 _142951 _142953).
Proof. exact (fun_ext (fun y : cart _142951 _142953 => @lem8051484 _142951 _142952 _142953 f x y)). Qed.
Lemma lem8051486 {_142951 _142953 : Type'} : (@all (cart _142951 _142953)) = (@all (cart _142951 _142953)).
Proof. exact (eq_refl (@all (cart _142951 _142953))). Qed.
Lemma lem8051487 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) : (term63 _142951 _142952 _142953 f x) = (term64 _142951 _142953).
Proof. exact (MK_COMB (@lem8051486 _142951 _142953) (@lem8051485 _142951 _142952 _142953 f x)). Qed.
Lemma lem8051489 {A : Type'} (t : Prop) : (term45 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8051490 {_142951 _142953 : Type'} (t : Prop) : (term65 _142951 _142953 t) = t.
Proof. exact (@lem8051489 (cart _142951 _142953) t). Qed.
Lemma lem8051491 {_142951 _142953 : Type'} : (term64 _142951 _142953) = True.
Proof. exact (@lem8051490 _142951 _142953 True). Qed.
Lemma lem8051492 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) : (term63 _142951 _142952 _142953 f x) = True.
Proof. exact (TRANS (@lem8051487 _142951 _142952 _142953 f x) (@lem8051491 _142951 _142953)). Qed.
Lemma lem8051493 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) : (term66 _142951 _142952 _142953 f) = (term62 _142951 _142952).
Proof. exact (fun_ext (fun x : cart _142951 _142952 => @lem8051492 _142951 _142952 _142953 f x)). Qed.
Lemma lem8051494 {_142951 _142952 : Type'} : (@all (cart _142951 _142952)) = (@all (cart _142951 _142952)).
Proof. exact (eq_refl (@all (cart _142951 _142952))). Qed.
Lemma lem8051495 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) : (term11 _142951 _142952 _142953 f) = (term64 _142951 _142952).
Proof. exact (MK_COMB (@lem8051494 _142951 _142952) (@lem8051493 _142951 _142952 _142953 f)). Qed.
Lemma lem8051497 {A : Type'} (t : Prop) : (term45 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8051498 {_142951 _142952 : Type'} (t : Prop) : (term65 _142951 _142952 t) = t.
Proof. exact (@lem8051497 (cart _142951 _142952) t). Qed.
Lemma lem8051499 {_142951 _142952 : Type'} : (term64 _142951 _142952) = True.
Proof. exact (@lem8051498 _142951 _142952 True). Qed.
Lemma lem8051500 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) : (term11 _142951 _142952 _142953 f) = True.
Proof. exact (TRANS (@lem8051495 _142951 _142952 _142953 f) (@lem8051499 _142951 _142952)). Qed.
Lemma lem8051501 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) : (term13 _142951 _142952 _142953 g f) = (term67 _142951 _142952 _142953 g f).
Proof. exact (MK_COMB (@lem8051333 _142951 _142952 _142953 g f) (@lem8051500 _142951 _142952 _142953 f)). Qed.
Lemma lem8051503 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem8051504 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) : (term67 _142951 _142952 _142953 g f) = True.
Proof. exact (@lem8051503 (term22 _142951 _142952 _142953 g f)). Qed.
Lemma lem8051505 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) : (term13 _142951 _142952 _142953 g f) = True.
Proof. exact (TRANS (@lem8051501 _142951 _142952 _142953 g f) (@lem8051504 _142951 _142952 _142953 g f)). Qed.
Lemma lem8051506 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) : True = (term13 _142951 _142952 _142953 g f).
Proof. exact (SYM (@lem8051505 _142951 _142952 _142953 g f)). Qed.
Lemma lem8051507 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) : term13 _142951 _142952 _142953 g f.
Proof. exact (EQ_MP (@lem8051506 _142951 _142952 _142953 g f) (@lem0)). Qed.
Lemma lem8051508 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) : term12 _142951 _142952 _142953 g f.
Proof. exact (EQ_MP (@lem8051266 _142951 _142952 _142953 g f) (@lem8051507 _142951 _142952 _142953 g f)). Qed.
Lemma lem8051509 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (h1 : term0 _142951 _142952 f) (h2 : g = (@EMPTY ((cart _142951 _142953) -> Prop))) : term11 _142951 _142952 _142953 f.
Proof. exact (@lem8051508 _142951 _142952 _142953 g f (@lem8051198 _142951 _142952 _142953 f g h1 h2)). Qed.
