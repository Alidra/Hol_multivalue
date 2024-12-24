Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ISO_FUN_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import FUN_EQ_THM_spec.
Require Import ISO_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm18392_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Lemma lem1075240 {A B : Type'} (f : A -> B) : term0 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem1075241 {A B : Type'} (f : A -> B) : (term0 A B f) = (term1 A B f).
Proof. exact (eq_refl (term0 A B f)). Qed.
Lemma lem1075242 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (EQ_MP (@lem1075241 A B f) (@lem1075240 A B f)). Qed.
Lemma lem1075243 {A B : Type'} (f : A -> B) (g : A -> B) : term2 A B f g.
Proof. exact (@lem1075242 A B f g). Qed.
Lemma lem1075244 {A B : Type'} (f : A -> B) (g : A -> B) : (term2 A B f g) = ((f = g) = (term3 A B f g)).
Proof. exact (eq_refl (term2 A B f g)). Qed.
Lemma lem1075246 {A B : Type'} (g : B -> A) : term4 A B g.
Proof. exact (@lem1075149 A B g). Qed.
Lemma lem1075247 {A B : Type'} (g : B -> A) : (term4 A B g) = (term5 A B g).
Proof. exact (eq_refl (term4 A B g)). Qed.
Lemma lem1075248 {A B : Type'} (g : B -> A) : term5 A B g.
Proof. exact (EQ_MP (@lem1075247 A B g) (@lem1075246 A B g)). Qed.
Lemma lem1075249 {A B : Type'} (g : B -> A) (f : A -> B) : term6 A B g f.
Proof. exact (@lem1075248 A B g f). Qed.
Lemma lem1075250 {A B : Type'} (g : B -> A) (f : A -> B) : (term6 A B g f) = ((@ExtensionalityFacts.is_inverse A B f g) = (term7 A B g f)).
Proof. exact (eq_refl (term6 A B g f)). Qed.
Lemma lem1075257 {A B : Type'} (g : B -> A) (f : A -> B) : (@ExtensionalityFacts.is_inverse A B f g) = (term7 A B g f).
Proof. exact (EQ_MP (@lem1075250 A B g f) (@lem1075249 A B g f)). Qed.
Lemma lem1075258 {A A' : Type'} (g : A' -> A) (f : A -> A') : (@ExtensionalityFacts.is_inverse A A' f g) = (term7 A A' g f).
Proof. exact (@lem1075257 A A' g f). Qed.
Lemma lem1075259 {A A' : Type'} (f' : A' -> A) (f : A -> A') : (@ExtensionalityFacts.is_inverse A A' f f') = (term7 A A' f' f).
Proof. exact (@lem1075258 A A' f' f). Qed.
Lemma lem1075278 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1075279 {A A' : Type'} (f' : A' -> A) (f : A -> A') : (term8 A A' f f') = (term9 A A' f' f).
Proof. exact (MK_COMB (@lem1075278) (@lem1075259 A A' f' f)). Qed.
Lemma lem1075281 {A B : Type'} (g : B -> A) (f : A -> B) : (@ExtensionalityFacts.is_inverse A B f g) = (term7 A B g f).
Proof. exact (EQ_MP (@lem1075250 A B g f) (@lem1075249 A B g f)). Qed.
Lemma lem1075282 {B B' : Type'} (g : B' -> B) (f : B -> B') : (@ExtensionalityFacts.is_inverse B B' f g) = (term7 B B' g f).
Proof. exact (@lem1075281 B B' g f). Qed.
Lemma lem1075283 {B B' : Type'} (g' : B' -> B) (g : B -> B') : (@ExtensionalityFacts.is_inverse B B' g g') = (term7 B B' g' g).
Proof. exact (@lem1075282 B B' g' g). Qed.
Lemma lem1075302 {A A' B B' : Type'} (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') : (term10 A A' B B' f f' g g') = (term11 A A' B B' f' f g' g).
Proof. exact (MK_COMB (@lem1075279 A A' f' f) (@lem1075283 B B' g' g)). Qed.
Lemma lem1075305 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1075306 {A A' B B' : Type'} (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') : (term12 A A' B B' f f' g g') = (term13 A A' B B' f' f g' g).
Proof. exact (MK_COMB (@lem1075305) (@lem1075302 A A' B B' f' f g' g)). Qed.
Lemma lem1075308 {A B : Type'} (g : B -> A) (f : A -> B) : (@ExtensionalityFacts.is_inverse A B f g) = (term7 A B g f).
Proof. exact (EQ_MP (@lem1075250 A B g f) (@lem1075249 A B g f)). Qed.
Lemma lem1075309 {A A' B B' : Type'} (g : type816 A A' B B') (f : type574 A A' B B') : (@ExtensionalityFacts.is_inverse (A -> B) (A' -> B') f g) = (term14 A A' B B' g f).
Proof. exact (@lem1075308 (A -> B) (A' -> B') g f). Qed.
Lemma lem1075310 {A A' B B' : Type'} (g' : B' -> B) (f : A -> A') (g : B -> B') (f' : A' -> A) : (term15 A A' B B' g f' g' f) = (term16 A A' B B' g' f g f').
Proof. exact (@lem1075309 A A' B B' (term17 A A' B B' g' f) (term18 A A' B B' g f')). Qed.
Lemma lem1075320 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term3 A B f g).
Proof. exact (EQ_MP (@lem1075244 A B f g) (@lem1075243 A B f g)). Qed.
Lemma lem1075321 {A' B' : Type'} (f : A' -> B') (g : A' -> B') : (f = g) = (term3 A' B' f g).
Proof. exact (@lem1075320 A' B' f g). Qed.
Lemma lem1075322 {A A' B B' : Type'} (g : B -> B') (f' : A' -> A) (g' : B' -> B) (f : A -> A') (x : A' -> B') : ((term19 A A' B B' g f' g' f x) = x) = (term20 A A' B B' g f' g' f x).
Proof. exact (@lem1075321 A' B' (term19 A A' B B' g f' g' f x) x). Qed.
Lemma lem1075332 {A B : Type'} (f : A -> B) (y : A) : (term21 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1075333 {A A' B B' : Type'} (f : type574 A A' B B') (y : A -> B) : (term22 A A' B B' f y) = (f y).
Proof. exact (@lem1075332 (A -> B) (A' -> B') f y). Qed.
Lemma lem1075334 {A A' B B' : Type'} (g : B -> B') (f' : A' -> A) (g' : B' -> B) (f : A -> A') (x : A' -> B') : (term23 A A' B B' g f' g' f x) = (term19 A A' B B' g f' g' f x).
Proof. exact (@lem1075333 A A' B B' (term18 A A' B B' g f') (term24 A A' B B' g' f x)). Qed.
Lemma lem1075335 {A A' B B' : Type'} (g : B -> B') (h : A -> B) (f' : A' -> A) : (term25 A A' B B' g f' h) = (term26 A A' B B' g h f').
Proof. exact (eq_refl (term25 A A' B B' g f' h)). Qed.
Lemma lem1075336 {A A' B B' : Type'} (g : B -> B') (f' : A' -> A) : (term27 A A' B B' g f') = (term18 A A' B B' g f').
Proof. exact (fun_ext (fun h : A -> B => @lem1075335 A A' B B' g h f')). Qed.
Lemma lem1075337 {A A' B B' : Type'} (g' : B' -> B) (f : A -> A') (x : A' -> B') : (term24 A A' B B' g' f x) = (term24 A A' B B' g' f x).
Proof. exact (eq_refl (term24 A A' B B' g' f x)). Qed.
Lemma lem1075338 {A A' B B' : Type'} (g : B -> B') (f' : A' -> A) (g' : B' -> B) (f : A -> A') (x : A' -> B') : (term23 A A' B B' g f' g' f x) = (term19 A A' B B' g f' g' f x).
Proof. exact (MK_COMB (@lem1075336 A A' B B' g f') (@lem1075337 A A' B B' g' f x)). Qed.
Lemma lem1075339 {A' B' : Type'} : (@eq (A' -> B')) = (@eq (A' -> B')).
Proof. exact (eq_refl (@eq (A' -> B'))). Qed.
Lemma lem1075340 {A A' B B' : Type'} (g : B -> B') (f' : A' -> A) (g' : B' -> B) (f : A -> A') (x : A' -> B') : (term28 A A' B B' g f' g' f x) = (term29 A A' B B' g f' g' f x).
Proof. exact (MK_COMB (@lem1075339 A' B') (@lem1075338 A A' B B' g f' g' f x)). Qed.
Lemma lem1075341 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (x : A' -> B') (f' : A' -> A) : (term19 A A' B B' g f' g' f x) = (term30 A A' B B' g g' f x f').
Proof. exact (eq_refl (term19 A A' B B' g f' g' f x)). Qed.
Lemma lem1075342 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (x : A' -> B') (f' : A' -> A) : ((term23 A A' B B' g f' g' f x) = (term19 A A' B B' g f' g' f x)) = ((term19 A A' B B' g f' g' f x) = (term30 A A' B B' g g' f x f')).
Proof. exact (MK_COMB (@lem1075340 A A' B B' g f' g' f x) (@lem1075341 A A' B B' g g' f x f')). Qed.
Lemma lem1075343 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (x : A' -> B') (f' : A' -> A) : (term19 A A' B B' g f' g' f x) = (term30 A A' B B' g g' f x f').
Proof. exact (EQ_MP (@lem1075342 A A' B B' g g' f x f') (@lem1075334 A A' B B' g f' g' f x)). Qed.
Lemma lem1075345 {A B : Type'} (f : A -> B) (y : A) : (term21 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1075346 {A A' B B' : Type'} (f : type816 A A' B B') (y : A' -> B') : (term31 A A' B B' f y) = (f y).
Proof. exact (@lem1075345 (A' -> B') (A -> B) f y). Qed.
Lemma lem1075347 {A A' B B' : Type'} (g' : B' -> B) (f : A -> A') (x : A' -> B') : (term32 A A' B B' g' f x) = (term24 A A' B B' g' f x).
Proof. exact (@lem1075346 A A' B B' (term17 A A' B B' g' f) x). Qed.
Lemma lem1075348 {A A' B B' : Type'} (g' : B' -> B) (h : A' -> B') (f : A -> A') : (term24 A A' B B' g' f h) = (term33 A A' B B' g' h f).
Proof. exact (eq_refl (term24 A A' B B' g' f h)). Qed.
Lemma lem1075349 {A A' B B' : Type'} (g' : B' -> B) (f : A -> A') : (term34 A A' B B' g' f) = (term17 A A' B B' g' f).
Proof. exact (fun_ext (fun h : A' -> B' => @lem1075348 A A' B B' g' h f)). Qed.
Lemma lem1075350 {A' B' : Type'} (x : A' -> B') : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1075351 {A A' B B' : Type'} (g' : B' -> B) (f : A -> A') (x : A' -> B') : (term32 A A' B B' g' f x) = (term24 A A' B B' g' f x).
Proof. exact (MK_COMB (@lem1075349 A A' B B' g' f) (@lem1075350 A' B' x)). Qed.
Lemma lem1075352 {A B : Type'} : (@eq (A -> B)) = (@eq (A -> B)).
Proof. exact (eq_refl (@eq (A -> B))). Qed.
Lemma lem1075353 {A A' B B' : Type'} (g' : B' -> B) (f : A -> A') (x : A' -> B') : (term35 A A' B B' g' f x) = (term36 A A' B B' g' f x).
Proof. exact (MK_COMB (@lem1075352 A B) (@lem1075351 A A' B B' g' f x)). Qed.
Lemma lem1075354 {A A' B B' : Type'} (g' : B' -> B) (x : A' -> B') (f : A -> A') : (term24 A A' B B' g' f x) = (term33 A A' B B' g' x f).
Proof. exact (eq_refl (term24 A A' B B' g' f x)). Qed.
Lemma lem1075355 {A A' B B' : Type'} (g' : B' -> B) (x : A' -> B') (f : A -> A') : ((term32 A A' B B' g' f x) = (term24 A A' B B' g' f x)) = ((term24 A A' B B' g' f x) = (term33 A A' B B' g' x f)).
Proof. exact (MK_COMB (@lem1075353 A A' B B' g' f x) (@lem1075354 A A' B B' g' x f)). Qed.
Lemma lem1075356 {A A' B B' : Type'} (g' : B' -> B) (x : A' -> B') (f : A -> A') : (term24 A A' B B' g' f x) = (term33 A A' B B' g' x f).
Proof. exact (EQ_MP (@lem1075355 A A' B B' g' x f) (@lem1075347 A A' B B' g' f x)). Qed.
Lemma lem1075357 {A A' : Type'} (f' : A' -> A) (a' : A') : (f' a') = (f' a').
Proof. exact (eq_refl (f' a')). Qed.
Lemma lem1075358 {A A' B B' : Type'} (g' : B' -> B) (x : A' -> B') (f : A -> A') (f' : A' -> A) (a' : A') : (term37 A A' B B' g' f x f' a') = (term38 A A' B B' g' x f f' a').
Proof. exact (MK_COMB (@lem1075356 A A' B B' g' x f) (@lem1075357 A A' f' a')). Qed.
Lemma lem1075360 {A B : Type'} (f : A -> B) (y : A) : (term21 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1075361 {A B : Type'} (f : A -> B) (y : A) : (term21 A B f y) = (f y).
Proof. exact (@lem1075360 A B f y). Qed.
Lemma lem1075362 {A A' B B' : Type'} (g' : B' -> B) (x : A' -> B') (f : A -> A') (f' : A' -> A) (a' : A') : (term39 A A' B B' g' x f f' a') = (term38 A A' B B' g' x f f' a').
Proof. exact (@lem1075361 A B (term33 A A' B B' g' x f) (f' a')). Qed.
Lemma lem1075363 {A A' B B' : Type'} (g' : B' -> B) (x : A' -> B') (f : A -> A') (a : A) : (term40 A A' B B' g' x f a) = (term41 A A' B B' g' x f a).
Proof. exact (eq_refl (term40 A A' B B' g' x f a)). Qed.
Lemma lem1075364 {A A' B B' : Type'} (g' : B' -> B) (x : A' -> B') (f : A -> A') : (term42 A A' B B' g' x f) = (term33 A A' B B' g' x f).
Proof. exact (fun_ext (fun a : A => @lem1075363 A A' B B' g' x f a)). Qed.
Lemma lem1075365 {A A' : Type'} (f' : A' -> A) (a' : A') : (f' a') = (f' a').
Proof. exact (eq_refl (f' a')). Qed.
Lemma lem1075366 {A A' B B' : Type'} (g' : B' -> B) (x : A' -> B') (f : A -> A') (f' : A' -> A) (a' : A') : (term39 A A' B B' g' x f f' a') = (term38 A A' B B' g' x f f' a').
Proof. exact (MK_COMB (@lem1075364 A A' B B' g' x f) (@lem1075365 A A' f' a')). Qed.
Lemma lem1075367 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem1075368 {A A' B B' : Type'} (g' : B' -> B) (x : A' -> B') (f : A -> A') (f' : A' -> A) (a' : A') : (term43 A A' B B' g' x f f' a') = (term44 A A' B B' g' x f f' a').
Proof. exact (MK_COMB (@lem1075367 B) (@lem1075366 A A' B B' g' x f f' a')). Qed.
Lemma lem1075369 {A A' B B' : Type'} (g' : B' -> B) (x : A' -> B') (f : A -> A') (f' : A' -> A) (a' : A') : (term38 A A' B B' g' x f f' a') = (term45 A A' B B' g' x f f' a').
Proof. exact (eq_refl (term38 A A' B B' g' x f f' a')). Qed.
Lemma lem1075370 {A A' B B' : Type'} (g' : B' -> B) (x : A' -> B') (f : A -> A') (f' : A' -> A) (a' : A') : ((term39 A A' B B' g' x f f' a') = (term38 A A' B B' g' x f f' a')) = ((term38 A A' B B' g' x f f' a') = (term45 A A' B B' g' x f f' a')).
Proof. exact (MK_COMB (@lem1075368 A A' B B' g' x f f' a') (@lem1075369 A A' B B' g' x f f' a')). Qed.
Lemma lem1075371 {A A' B B' : Type'} (g' : B' -> B) (x : A' -> B') (f : A -> A') (f' : A' -> A) (a' : A') : (term38 A A' B B' g' x f f' a') = (term45 A A' B B' g' x f f' a').
Proof. exact (EQ_MP (@lem1075370 A A' B B' g' x f f' a') (@lem1075362 A A' B B' g' x f f' a')). Qed.
Lemma lem1075372 {A A' B B' : Type'} (g' : B' -> B) (x : A' -> B') (f : A -> A') (f' : A' -> A) (a' : A') : (term37 A A' B B' g' f x f' a') = (term45 A A' B B' g' x f f' a').
Proof. exact (TRANS (@lem1075358 A A' B B' g' x f f' a') (@lem1075371 A A' B B' g' x f f' a')). Qed.
Lemma lem1075373 {B B' : Type'} (g : B -> B') : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem1075374 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (x : A' -> B') (f : A -> A') (f' : A' -> A) (a' : A') : (term46 A A' B B' g g' f x f' a') = (term47 A A' B B' g g' x f f' a').
Proof. exact (MK_COMB (@lem1075373 B B' g) (@lem1075372 A A' B B' g' x f f' a')). Qed.
Lemma lem1075375 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (x : A' -> B') (f : A -> A') (f' : A' -> A) : (term30 A A' B B' g g' f x f') = (term48 A A' B B' g g' x f f').
Proof. exact (fun_ext (fun a' : A' => @lem1075374 A A' B B' g g' x f f' a')). Qed.
Lemma lem1075376 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (x : A' -> B') (f : A -> A') (f' : A' -> A) : (term19 A A' B B' g f' g' f x) = (term48 A A' B B' g g' x f f').
Proof. exact (TRANS (@lem1075343 A A' B B' g g' f x f') (@lem1075375 A A' B B' g g' x f f')). Qed.
Lemma lem1075377 {A' : Type'} (x : A') : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1075378 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (x : A' -> B') (f : A -> A') (f' : A' -> A) (x' : A') : (term49 A A' B B' g f' g' f x x') = (term50 A A' B B' g g' x f f' x').
Proof. exact (MK_COMB (@lem1075376 A A' B B' g g' x f f') (@lem1075377 A' x')). Qed.
Lemma lem1075380 {A B : Type'} (f : A -> B) (y : A) : (term21 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1075381 {A' B' : Type'} (f : A' -> B') (y : A') : (term21 A' B' f y) = (f y).
Proof. exact (@lem1075380 A' B' f y). Qed.
Lemma lem1075382 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (x : A' -> B') (f : A -> A') (f' : A' -> A) (x' : A') : (term51 A A' B B' g g' x f f' x') = (term50 A A' B B' g g' x f f' x').
Proof. exact (@lem1075381 A' B' (term48 A A' B B' g g' x f f') x'). Qed.
Lemma lem1075383 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (x : A' -> B') (f : A -> A') (f' : A' -> A) (a' : A') : (term50 A A' B B' g g' x f f' a') = (term47 A A' B B' g g' x f f' a').
Proof. exact (eq_refl (term50 A A' B B' g g' x f f' a')). Qed.
Lemma lem1075384 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (x : A' -> B') (f : A -> A') (f' : A' -> A) : (term52 A A' B B' g g' x f f') = (term48 A A' B B' g g' x f f').
Proof. exact (fun_ext (fun a' : A' => @lem1075383 A A' B B' g g' x f f' a')). Qed.
Lemma lem1075385 {A' : Type'} (x : A') : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1075386 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (x : A' -> B') (f : A -> A') (f' : A' -> A) (x' : A') : (term51 A A' B B' g g' x f f' x') = (term50 A A' B B' g g' x f f' x').
Proof. exact (MK_COMB (@lem1075384 A A' B B' g g' x f f') (@lem1075385 A' x')). Qed.
Lemma lem1075387 {B' : Type'} : (@eq B') = (@eq B').
Proof. exact (eq_refl (@eq B')). Qed.
Lemma lem1075388 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (x : A' -> B') (f : A -> A') (f' : A' -> A) (x' : A') : (term53 A A' B B' g g' x f f' x') = (term54 A A' B B' g g' x f f' x').
Proof. exact (MK_COMB (@lem1075387 B') (@lem1075386 A A' B B' g g' x f f' x')). Qed.
Lemma lem1075389 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (x : A' -> B') (f : A -> A') (f' : A' -> A) (x' : A') : (term50 A A' B B' g g' x f f' x') = (term47 A A' B B' g g' x f f' x').
Proof. exact (eq_refl (term50 A A' B B' g g' x f f' x')). Qed.
Lemma lem1075390 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (x : A' -> B') (f : A -> A') (f' : A' -> A) (x' : A') : ((term51 A A' B B' g g' x f f' x') = (term50 A A' B B' g g' x f f' x')) = ((term50 A A' B B' g g' x f f' x') = (term47 A A' B B' g g' x f f' x')).
Proof. exact (MK_COMB (@lem1075388 A A' B B' g g' x f f' x') (@lem1075389 A A' B B' g g' x f f' x')). Qed.
Lemma lem1075391 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (x : A' -> B') (f : A -> A') (f' : A' -> A) (x' : A') : (term50 A A' B B' g g' x f f' x') = (term47 A A' B B' g g' x f f' x').
Proof. exact (EQ_MP (@lem1075390 A A' B B' g g' x f f' x') (@lem1075382 A A' B B' g g' x f f' x')). Qed.
Lemma lem1075392 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (x : A' -> B') (f : A -> A') (f' : A' -> A) (x' : A') : (term49 A A' B B' g f' g' f x x') = (term47 A A' B B' g g' x f f' x').
Proof. exact (TRANS (@lem1075378 A A' B B' g g' x f f' x') (@lem1075391 A A' B B' g g' x f f' x')). Qed.
Lemma lem1075393 {B' : Type'} : (@eq B') = (@eq B').
Proof. exact (eq_refl (@eq B')). Qed.
Lemma lem1075394 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (x : A' -> B') (f : A -> A') (f' : A' -> A) (x' : A') : (term55 A A' B B' g f' g' f x x') = (term56 A A' B B' g g' x f f' x').
Proof. exact (MK_COMB (@lem1075393 B') (@lem1075392 A A' B B' g g' x f f' x')). Qed.
Lemma lem1075395 {A' B' : Type'} (x : A' -> B') (x' : A') : (x x') = (x x').
Proof. exact (eq_refl (x x')). Qed.
Lemma lem1075396 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) (x : A' -> B') (x' : A') : ((term49 A A' B B' g f' g' f x x') = (x x')) = ((term47 A A' B B' g g' x f f' x') = (x x')).
Proof. exact (MK_COMB (@lem1075394 A A' B B' g g' x f f' x') (@lem1075395 A' B' x x')). Qed.
Lemma lem1075401 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) (x : A' -> B') : (term57 A A' B B' g f' g' f x) = (term58 A A' B B' g g' f f' x).
Proof. exact (fun_ext (fun x' : A' => @lem1075396 A A' B B' g g' f f' x x')). Qed.
Lemma lem1075402 {A' : Type'} : (@all A') = (@all A').
Proof. exact (eq_refl (@all A')). Qed.
Lemma lem1075403 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) (x : A' -> B') : (term20 A A' B B' g f' g' f x) = (term59 A A' B B' g g' f f' x).
Proof. exact (MK_COMB (@lem1075402 A') (@lem1075401 A A' B B' g g' f f' x)). Qed.
Lemma lem1075408 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) (x : A' -> B') : ((term19 A A' B B' g f' g' f x) = x) = (term59 A A' B B' g g' f f' x).
Proof. exact (TRANS (@lem1075322 A A' B B' g f' g' f x) (@lem1075403 A A' B B' g g' f f' x)). Qed.
Lemma lem1075409 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) : (term60 A A' B B' g f' g' f) = (term61 A A' B B' g g' f f').
Proof. exact (fun_ext (fun x : A' -> B' => @lem1075408 A A' B B' g g' f f' x)). Qed.
Lemma lem1075410 {A' B' : Type'} : (@all (A' -> B')) = (@all (A' -> B')).
Proof. exact (eq_refl (@all (A' -> B'))). Qed.
Lemma lem1075411 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) : (term62 A A' B B' g f' g' f) = (term63 A A' B B' g g' f f').
Proof. exact (MK_COMB (@lem1075410 A' B') (@lem1075409 A A' B B' g g' f f')). Qed.
Lemma lem1075416 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1075417 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) : (term64 A A' B B' g f' g' f) = (term65 A A' B B' g g' f f').
Proof. exact (MK_COMB (@lem1075416) (@lem1075411 A A' B B' g g' f f')). Qed.
Lemma lem1075425 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term3 A B f g).
Proof. exact (EQ_MP (@lem1075244 A B f g) (@lem1075243 A B f g)). Qed.
Lemma lem1075426 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term3 A B f g).
Proof. exact (@lem1075425 A B f g). Qed.
Lemma lem1075427 {A A' B B' : Type'} (g' : B' -> B) (f : A -> A') (g : B -> B') (f' : A' -> A) (y : A -> B) : ((term66 A A' B B' g' f g f' y) = y) = (term67 A A' B B' g' f g f' y).
Proof. exact (@lem1075426 A B (term66 A A' B B' g' f g f' y) y). Qed.
Lemma lem1075437 {A B : Type'} (f : A -> B) (y : A) : (term21 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1075438 {A A' B B' : Type'} (f : type816 A A' B B') (y : A' -> B') : (term31 A A' B B' f y) = (f y).
Proof. exact (@lem1075437 (A' -> B') (A -> B) f y). Qed.
Lemma lem1075439 {A A' B B' : Type'} (g' : B' -> B) (f : A -> A') (g : B -> B') (f' : A' -> A) (y : A -> B) : (term68 A A' B B' g' f g f' y) = (term66 A A' B B' g' f g f' y).
Proof. exact (@lem1075438 A A' B B' (term17 A A' B B' g' f) (term25 A A' B B' g f' y)). Qed.
Lemma lem1075440 {A A' B B' : Type'} (g' : B' -> B) (h : A' -> B') (f : A -> A') : (term24 A A' B B' g' f h) = (term33 A A' B B' g' h f).
Proof. exact (eq_refl (term24 A A' B B' g' f h)). Qed.
Lemma lem1075441 {A A' B B' : Type'} (g' : B' -> B) (f : A -> A') : (term34 A A' B B' g' f) = (term17 A A' B B' g' f).
Proof. exact (fun_ext (fun h : A' -> B' => @lem1075440 A A' B B' g' h f)). Qed.
Lemma lem1075442 {A A' B B' : Type'} (g : B -> B') (f' : A' -> A) (y : A -> B) : (term25 A A' B B' g f' y) = (term25 A A' B B' g f' y).
Proof. exact (eq_refl (term25 A A' B B' g f' y)). Qed.
Lemma lem1075443 {A A' B B' : Type'} (g' : B' -> B) (f : A -> A') (g : B -> B') (f' : A' -> A) (y : A -> B) : (term68 A A' B B' g' f g f' y) = (term66 A A' B B' g' f g f' y).
Proof. exact (MK_COMB (@lem1075441 A A' B B' g' f) (@lem1075442 A A' B B' g f' y)). Qed.
Lemma lem1075444 {A B : Type'} : (@eq (A -> B)) = (@eq (A -> B)).
Proof. exact (eq_refl (@eq (A -> B))). Qed.
Lemma lem1075445 {A A' B B' : Type'} (g' : B' -> B) (f : A -> A') (g : B -> B') (f' : A' -> A) (y : A -> B) : (term69 A A' B B' g' f g f' y) = (term70 A A' B B' g' f g f' y).
Proof. exact (MK_COMB (@lem1075444 A B) (@lem1075443 A A' B B' g' f g f' y)). Qed.
Lemma lem1075446 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (y : A -> B) (f : A -> A') : (term66 A A' B B' g' f g f' y) = (term71 A A' B B' g' g f' y f).
Proof. exact (eq_refl (term66 A A' B B' g' f g f' y)). Qed.
Lemma lem1075447 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (y : A -> B) (f : A -> A') : ((term68 A A' B B' g' f g f' y) = (term66 A A' B B' g' f g f' y)) = ((term66 A A' B B' g' f g f' y) = (term71 A A' B B' g' g f' y f)).
Proof. exact (MK_COMB (@lem1075445 A A' B B' g' f g f' y) (@lem1075446 A A' B B' g' g f' y f)). Qed.
Lemma lem1075448 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (y : A -> B) (f : A -> A') : (term66 A A' B B' g' f g f' y) = (term71 A A' B B' g' g f' y f).
Proof. exact (EQ_MP (@lem1075447 A A' B B' g' g f' y f) (@lem1075439 A A' B B' g' f g f' y)). Qed.
Lemma lem1075450 {A B : Type'} (f : A -> B) (y : A) : (term21 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1075451 {A A' B B' : Type'} (f : type574 A A' B B') (y : A -> B) : (term22 A A' B B' f y) = (f y).
Proof. exact (@lem1075450 (A -> B) (A' -> B') f y). Qed.
Lemma lem1075452 {A A' B B' : Type'} (g : B -> B') (f' : A' -> A) (y : A -> B) : (term72 A A' B B' g f' y) = (term25 A A' B B' g f' y).
Proof. exact (@lem1075451 A A' B B' (term18 A A' B B' g f') y). Qed.
Lemma lem1075453 {A A' B B' : Type'} (g : B -> B') (h : A -> B) (f' : A' -> A) : (term25 A A' B B' g f' h) = (term26 A A' B B' g h f').
Proof. exact (eq_refl (term25 A A' B B' g f' h)). Qed.
Lemma lem1075454 {A A' B B' : Type'} (g : B -> B') (f' : A' -> A) : (term27 A A' B B' g f') = (term18 A A' B B' g f').
Proof. exact (fun_ext (fun h : A -> B => @lem1075453 A A' B B' g h f')). Qed.
Lemma lem1075455 {A B : Type'} (y : A -> B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1075456 {A A' B B' : Type'} (g : B -> B') (f' : A' -> A) (y : A -> B) : (term72 A A' B B' g f' y) = (term25 A A' B B' g f' y).
Proof. exact (MK_COMB (@lem1075454 A A' B B' g f') (@lem1075455 A B y)). Qed.
Lemma lem1075457 {A' B' : Type'} : (@eq (A' -> B')) = (@eq (A' -> B')).
Proof. exact (eq_refl (@eq (A' -> B'))). Qed.
Lemma lem1075458 {A A' B B' : Type'} (g : B -> B') (f' : A' -> A) (y : A -> B) : (term73 A A' B B' g f' y) = (term74 A A' B B' g f' y).
Proof. exact (MK_COMB (@lem1075457 A' B') (@lem1075456 A A' B B' g f' y)). Qed.
Lemma lem1075459 {A A' B B' : Type'} (g : B -> B') (y : A -> B) (f' : A' -> A) : (term25 A A' B B' g f' y) = (term26 A A' B B' g y f').
Proof. exact (eq_refl (term25 A A' B B' g f' y)). Qed.
Lemma lem1075460 {A A' B B' : Type'} (g : B -> B') (y : A -> B) (f' : A' -> A) : ((term72 A A' B B' g f' y) = (term25 A A' B B' g f' y)) = ((term25 A A' B B' g f' y) = (term26 A A' B B' g y f')).
Proof. exact (MK_COMB (@lem1075458 A A' B B' g f' y) (@lem1075459 A A' B B' g y f')). Qed.
Lemma lem1075461 {A A' B B' : Type'} (g : B -> B') (y : A -> B) (f' : A' -> A) : (term25 A A' B B' g f' y) = (term26 A A' B B' g y f').
Proof. exact (EQ_MP (@lem1075460 A A' B B' g y f') (@lem1075452 A A' B B' g f' y)). Qed.
Lemma lem1075462 {A A' : Type'} (f : A -> A') (a : A) : (f a) = (f a).
Proof. exact (eq_refl (f a)). Qed.
Lemma lem1075463 {A A' B B' : Type'} (g : B -> B') (y : A -> B) (f' : A' -> A) (f : A -> A') (a : A) : (term75 A A' B B' g f' y f a) = (term76 A A' B B' g y f' f a).
Proof. exact (MK_COMB (@lem1075461 A A' B B' g y f') (@lem1075462 A A' f a)). Qed.
Lemma lem1075465 {A B : Type'} (f : A -> B) (y : A) : (term21 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1075466 {A' B' : Type'} (f : A' -> B') (y : A') : (term21 A' B' f y) = (f y).
Proof. exact (@lem1075465 A' B' f y). Qed.
Lemma lem1075467 {A A' B B' : Type'} (g : B -> B') (y : A -> B) (f' : A' -> A) (f : A -> A') (a : A) : (term77 A A' B B' g y f' f a) = (term76 A A' B B' g y f' f a).
Proof. exact (@lem1075466 A' B' (term26 A A' B B' g y f') (f a)). Qed.
Lemma lem1075468 {A A' B B' : Type'} (g : B -> B') (y : A -> B) (f' : A' -> A) (a' : A') : (term78 A A' B B' g y f' a') = (term79 A A' B B' g y f' a').
Proof. exact (eq_refl (term78 A A' B B' g y f' a')). Qed.
Lemma lem1075469 {A A' B B' : Type'} (g : B -> B') (y : A -> B) (f' : A' -> A) : (term80 A A' B B' g y f') = (term26 A A' B B' g y f').
Proof. exact (fun_ext (fun a' : A' => @lem1075468 A A' B B' g y f' a')). Qed.
Lemma lem1075470 {A A' : Type'} (f : A -> A') (a : A) : (f a) = (f a).
Proof. exact (eq_refl (f a)). Qed.
Lemma lem1075471 {A A' B B' : Type'} (g : B -> B') (y : A -> B) (f' : A' -> A) (f : A -> A') (a : A) : (term77 A A' B B' g y f' f a) = (term76 A A' B B' g y f' f a).
Proof. exact (MK_COMB (@lem1075469 A A' B B' g y f') (@lem1075470 A A' f a)). Qed.
Lemma lem1075472 {B' : Type'} : (@eq B') = (@eq B').
Proof. exact (eq_refl (@eq B')). Qed.
Lemma lem1075473 {A A' B B' : Type'} (g : B -> B') (y : A -> B) (f' : A' -> A) (f : A -> A') (a : A) : (term81 A A' B B' g y f' f a) = (term82 A A' B B' g y f' f a).
Proof. exact (MK_COMB (@lem1075472 B') (@lem1075471 A A' B B' g y f' f a)). Qed.
Lemma lem1075474 {A A' B B' : Type'} (g : B -> B') (y : A -> B) (f' : A' -> A) (f : A -> A') (a : A) : (term76 A A' B B' g y f' f a) = (term83 A A' B B' g y f' f a).
Proof. exact (eq_refl (term76 A A' B B' g y f' f a)). Qed.
Lemma lem1075475 {A A' B B' : Type'} (g : B -> B') (y : A -> B) (f' : A' -> A) (f : A -> A') (a : A) : ((term77 A A' B B' g y f' f a) = (term76 A A' B B' g y f' f a)) = ((term76 A A' B B' g y f' f a) = (term83 A A' B B' g y f' f a)).
Proof. exact (MK_COMB (@lem1075473 A A' B B' g y f' f a) (@lem1075474 A A' B B' g y f' f a)). Qed.
Lemma lem1075476 {A A' B B' : Type'} (g : B -> B') (y : A -> B) (f' : A' -> A) (f : A -> A') (a : A) : (term76 A A' B B' g y f' f a) = (term83 A A' B B' g y f' f a).
Proof. exact (EQ_MP (@lem1075475 A A' B B' g y f' f a) (@lem1075467 A A' B B' g y f' f a)). Qed.
Lemma lem1075477 {A A' B B' : Type'} (g : B -> B') (y : A -> B) (f' : A' -> A) (f : A -> A') (a : A) : (term75 A A' B B' g f' y f a) = (term83 A A' B B' g y f' f a).
Proof. exact (TRANS (@lem1075463 A A' B B' g y f' f a) (@lem1075476 A A' B B' g y f' f a)). Qed.
Lemma lem1075478 {B B' : Type'} (g' : B' -> B) : g' = g'.
Proof. exact (eq_refl g'). Qed.
Lemma lem1075479 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (y : A -> B) (f' : A' -> A) (f : A -> A') (a : A) : (term84 A A' B B' g' g f' y f a) = (term85 A A' B B' g' g y f' f a).
Proof. exact (MK_COMB (@lem1075478 B B' g') (@lem1075477 A A' B B' g y f' f a)). Qed.
Lemma lem1075480 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (y : A -> B) (f' : A' -> A) (f : A -> A') : (term71 A A' B B' g' g f' y f) = (term86 A A' B B' g' g y f' f).
Proof. exact (fun_ext (fun a : A => @lem1075479 A A' B B' g' g y f' f a)). Qed.
Lemma lem1075481 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (y : A -> B) (f' : A' -> A) (f : A -> A') : (term66 A A' B B' g' f g f' y) = (term86 A A' B B' g' g y f' f).
Proof. exact (TRANS (@lem1075448 A A' B B' g' g f' y f) (@lem1075480 A A' B B' g' g y f' f)). Qed.
Lemma lem1075482 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1075483 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (y : A -> B) (f' : A' -> A) (f : A -> A') (x : A) : (term87 A A' B B' g' f g f' y x) = (term88 A A' B B' g' g y f' f x).
Proof. exact (MK_COMB (@lem1075481 A A' B B' g' g y f' f) (@lem1075482 A x)). Qed.
Lemma lem1075485 {A B : Type'} (f : A -> B) (y : A) : (term21 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1075486 {A B : Type'} (f : A -> B) (y : A) : (term21 A B f y) = (f y).
Proof. exact (@lem1075485 A B f y). Qed.
Lemma lem1075487 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (y : A -> B) (f' : A' -> A) (f : A -> A') (x : A) : (term89 A A' B B' g' g y f' f x) = (term88 A A' B B' g' g y f' f x).
Proof. exact (@lem1075486 A B (term86 A A' B B' g' g y f' f) x). Qed.
Lemma lem1075488 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (y : A -> B) (f' : A' -> A) (f : A -> A') (a : A) : (term88 A A' B B' g' g y f' f a) = (term85 A A' B B' g' g y f' f a).
Proof. exact (eq_refl (term88 A A' B B' g' g y f' f a)). Qed.
Lemma lem1075489 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (y : A -> B) (f' : A' -> A) (f : A -> A') : (term90 A A' B B' g' g y f' f) = (term86 A A' B B' g' g y f' f).
Proof. exact (fun_ext (fun a : A => @lem1075488 A A' B B' g' g y f' f a)). Qed.
Lemma lem1075490 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1075491 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (y : A -> B) (f' : A' -> A) (f : A -> A') (x : A) : (term89 A A' B B' g' g y f' f x) = (term88 A A' B B' g' g y f' f x).
Proof. exact (MK_COMB (@lem1075489 A A' B B' g' g y f' f) (@lem1075490 A x)). Qed.
Lemma lem1075492 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem1075493 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (y : A -> B) (f' : A' -> A) (f : A -> A') (x : A) : (term91 A A' B B' g' g y f' f x) = (term92 A A' B B' g' g y f' f x).
Proof. exact (MK_COMB (@lem1075492 B) (@lem1075491 A A' B B' g' g y f' f x)). Qed.
Lemma lem1075494 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (y : A -> B) (f' : A' -> A) (f : A -> A') (x : A) : (term88 A A' B B' g' g y f' f x) = (term85 A A' B B' g' g y f' f x).
Proof. exact (eq_refl (term88 A A' B B' g' g y f' f x)). Qed.
Lemma lem1075495 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (y : A -> B) (f' : A' -> A) (f : A -> A') (x : A) : ((term89 A A' B B' g' g y f' f x) = (term88 A A' B B' g' g y f' f x)) = ((term88 A A' B B' g' g y f' f x) = (term85 A A' B B' g' g y f' f x)).
Proof. exact (MK_COMB (@lem1075493 A A' B B' g' g y f' f x) (@lem1075494 A A' B B' g' g y f' f x)). Qed.
Lemma lem1075496 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (y : A -> B) (f' : A' -> A) (f : A -> A') (x : A) : (term88 A A' B B' g' g y f' f x) = (term85 A A' B B' g' g y f' f x).
Proof. exact (EQ_MP (@lem1075495 A A' B B' g' g y f' f x) (@lem1075487 A A' B B' g' g y f' f x)). Qed.
Lemma lem1075497 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (y : A -> B) (f' : A' -> A) (f : A -> A') (x : A) : (term87 A A' B B' g' f g f' y x) = (term85 A A' B B' g' g y f' f x).
Proof. exact (TRANS (@lem1075483 A A' B B' g' g y f' f x) (@lem1075496 A A' B B' g' g y f' f x)). Qed.
Lemma lem1075498 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem1075499 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (y : A -> B) (f' : A' -> A) (f : A -> A') (x : A) : (term93 A A' B B' g' f g f' y x) = (term94 A A' B B' g' g y f' f x).
Proof. exact (MK_COMB (@lem1075498 B) (@lem1075497 A A' B B' g' g y f' f x)). Qed.
Lemma lem1075500 {A B : Type'} (y : A -> B) (x : A) : (y x) = (y x).
Proof. exact (eq_refl (y x)). Qed.
Lemma lem1075501 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (y : A -> B) (x : A) : ((term87 A A' B B' g' f g f' y x) = (y x)) = ((term85 A A' B B' g' g y f' f x) = (y x)).
Proof. exact (MK_COMB (@lem1075499 A A' B B' g' g y f' f x) (@lem1075500 A B y x)). Qed.
Lemma lem1075506 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (y : A -> B) : (term95 A A' B B' g' f g f' y) = (term96 A A' B B' g' g f' f y).
Proof. exact (fun_ext (fun x : A => @lem1075501 A A' B B' g' g f' f y x)). Qed.
Lemma lem1075507 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1075508 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (y : A -> B) : (term67 A A' B B' g' f g f' y) = (term97 A A' B B' g' g f' f y).
Proof. exact (MK_COMB (@lem1075507 A) (@lem1075506 A A' B B' g' g f' f y)). Qed.
Lemma lem1075513 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (y : A -> B) : ((term66 A A' B B' g' f g f' y) = y) = (term97 A A' B B' g' g f' f y).
Proof. exact (TRANS (@lem1075427 A A' B B' g' f g f' y) (@lem1075508 A A' B B' g' g f' f y)). Qed.
Lemma lem1075514 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term98 A A' B B' g' f g f') = (term99 A A' B B' g' g f' f).
Proof. exact (fun_ext (fun y : A -> B => @lem1075513 A A' B B' g' g f' f y)). Qed.
Lemma lem1075515 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem1075516 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term100 A A' B B' g' f g f') = (term101 A A' B B' g' g f' f).
Proof. exact (MK_COMB (@lem1075515 A B) (@lem1075514 A A' B B' g' g f' f)). Qed.
Lemma lem1075521 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term16 A A' B B' g' f g f') = (term102 A A' B B' g' g f' f).
Proof. exact (MK_COMB (@lem1075417 A A' B B' g g' f f') (@lem1075516 A A' B B' g' g f' f)). Qed.
Lemma lem1075524 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term15 A A' B B' g f' g' f) = (term102 A A' B B' g' g f' f).
Proof. exact (TRANS (@lem1075310 A A' B B' g' f g f') (@lem1075521 A A' B B' g' g f' f)). Qed.
Lemma lem1075525 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term103 A A' B B' g f' g' f) = (term104 A A' B B' g' g f' f).
Proof. exact (MK_COMB (@lem1075306 A A' B B' f' f g' g) (@lem1075524 A A' B B' g' g f' f)). Qed.
Lemma lem1075528 {A A' B B' : Type'} (g : B -> B') (f' : A' -> A) (g' : B' -> B) (f : A -> A') : (term104 A A' B B' g' g f' f) = (term103 A A' B B' g f' g' f).
Proof. exact (SYM (@lem1075525 A A' B B' g' g f' f)). Qed.
Lemma lem1075530 (p : Prop) : p = (term105 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1075531 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term104 A A' B B' g' g f' f) = (term106 A A' B B' g' g f' f).
Proof. exact (@lem1075530 (term104 A A' B B' g' g f' f)). Qed.
Lemma lem1075532 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term106 A A' B B' g' g f' f) = (term104 A A' B B' g' g f' f).
Proof. exact (SYM (@lem1075531 A A' B B' g' g f' f)). Qed.
Lemma lem1075533 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (h1 : term107 A A' B B' g' g f' f) : term107 A A' B B' g' g f' f.
Proof. exact (h1). Qed.
Lemma lem1075536 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (h1 : term106 A A' B B' g' g f' f) : term106 A A' B B' g' g f' f.
Proof. exact (h1). Qed.
Lemma lem1075537 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : term108 A A' B B' g' g f' f.
Proof. exact (fun h0 : term106 A A' B B' g' g f' f => @lem1075536 A A' B B' g' g f' f h0). Qed.
Lemma lem1075538 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (h1 : term108 A A' B B' g' g f' f) : term108 A A' B B' g' g f' f.
Proof. exact (h1). Qed.
Lemma lem1075539 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (h1 : term106 A A' B B' g' g f' f) : term106 A A' B B' g' g f' f.
Proof. exact (h1). Qed.
Lemma lem1075540 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (h1 : term106 A A' B B' g' g f' f) (h2 : term108 A A' B B' g' g f' f) : term106 A A' B B' g' g f' f.
Proof. exact (@lem1075538 A A' B B' g' g f' f h2 (@lem1075539 A A' B B' g' g f' f h1)). Qed.
Lemma lem1075541 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (h1 : term106 A A' B B' g' g f' f) : term109 A A' B B' g' g f' f.
Proof. exact (fun h0 : term108 A A' B B' g' g f' f => @lem1075540 A A' B B' g' g f' f h1 h0). Qed.
Lemma lem1075542 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (h1 : term108 A A' B B' g' g f' f) : term108 A A' B B' g' g f' f.
Proof. exact (h1). Qed.
Lemma lem1075543 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (h1 : term106 A A' B B' g' g f' f) (h2 : term108 A A' B B' g' g f' f) : term106 A A' B B' g' g f' f.
Proof. exact (@lem1075541 A A' B B' g' g f' f h1 (@lem1075542 A A' B B' g' g f' f h2)). Qed.
Lemma lem1075544 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (h1 : term108 A A' B B' g' g f' f) : term108 A A' B B' g' g f' f.
Proof. exact (fun h0 : term106 A A' B B' g' g f' f => @lem1075543 A A' B B' g' g f' f h0 h1). Qed.
Lemma lem1075545 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : term110 A A' B B' g' g f' f.
Proof. exact (fun h0 : term108 A A' B B' g' g f' f => @lem1075544 A A' B B' g' g f' f h0). Qed.
Lemma lem1075548 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : term108 A A' B B' g' g f' f.
Proof. exact (@lem1075545 A A' B B' g' g f' f (@lem1075537 A A' B B' g' g f' f)). Qed.
Lemma lem1075549 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : term108 A A' B B' g' g f' f.
Proof. exact (@lem1075548 A A' B B' g' g f' f). Qed.
Lemma lem1075567 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1075568 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term106 A A' B B' g' g f' f) = (term111 A A' B B' g' g f' f).
Proof. exact (@lem1075567 (term107 A A' B B' g' g f' f)). Qed.
Lemma lem1075570 (t : Prop) : (term112 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem1075571 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term111 A A' B B' g' g f' f) = (term104 A A' B B' g' g f' f).
Proof. exact (@lem1075570 (term104 A A' B B' g' g f' f)). Qed.
Lemma lem1075574 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term106 A A' B B' g' g f' f) = (term104 A A' B B' g' g f' f).
Proof. exact (TRANS (@lem1075568 A A' B B' g' g f' f) (@lem1075571 A A' B B' g' g f' f)). Qed.
Lemma lem1075615 {A A' B B' : Type'} (g : B -> B') (f' : A' -> A) (f : A -> A') : (term113 A A' B B' g f' f) = (term114 A A' B B' g f' f).
Proof. exact (fun_ext (fun g' : B' -> B => @lem1075574 A A' B B' g' g f' f)). Qed.
Lemma lem1075616 {B B' : Type'} : (@all (B' -> B)) = (@all (B' -> B)).
Proof. exact (eq_refl (@all (B' -> B))). Qed.
Lemma lem1075617 {A A' B B' : Type'} (g : B -> B') (f' : A' -> A) (f : A -> A') : (term115 A A' B B' g f' f) = (term116 A A' B B' g f' f).
Proof. exact (MK_COMB (@lem1075616 B B') (@lem1075615 A A' B B' g f' f)). Qed.
Lemma lem1075622 {A A' B B' : Type'} (f' : A' -> A) (f : A -> A') : (term117 A A' B B' f' f) = (term118 A A' B B' f' f).
Proof. exact (fun_ext (fun g : B -> B' => @lem1075617 A A' B B' g f' f)). Qed.
Lemma lem1075623 {B B' : Type'} : (@all (B -> B')) = (@all (B -> B')).
Proof. exact (eq_refl (@all (B -> B'))). Qed.
Lemma lem1075624 {A A' B B' : Type'} (f' : A' -> A) (f : A -> A') : (term119 A A' B B' f' f) = (term120 A A' B B' f' f).
Proof. exact (MK_COMB (@lem1075623 B B') (@lem1075622 A A' B B' f' f)). Qed.
Lemma lem1075629 {A A' B B' : Type'} (f : A -> A') : (term121 A A' B B' f) = (term122 A A' B B' f).
Proof. exact (fun_ext (fun f' : A' -> A => @lem1075624 A A' B B' f' f)). Qed.
Lemma lem1075630 {A A' : Type'} : (@all (A' -> A)) = (@all (A' -> A)).
Proof. exact (eq_refl (@all (A' -> A))). Qed.
Lemma lem1075631 {A A' B B' : Type'} (f : A -> A') : (term123 A A' B B' f) = (term124 A A' B B' f).
Proof. exact (MK_COMB (@lem1075630 A A') (@lem1075629 A A' B B' f)). Qed.
Lemma lem1075636 {A A' B B' : Type'} : (term125 A A' B B') = (term126 A A' B B').
Proof. exact (fun_ext (fun f : A -> A' => @lem1075631 A A' B B' f)). Qed.
Lemma lem1075637 {A A' : Type'} : (@all (A -> A')) = (@all (A -> A')).
Proof. exact (eq_refl (@all (A -> A'))). Qed.
Lemma lem1075646 {A A' B B' : Type'} : (term127 A A' B B') = (term128 A A' B B').
Proof. exact (MK_COMB (@lem1075637 A A') (@lem1075636 A A' B B')). Qed.
Lemma lem1075647 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (y : A -> B) (x : A) : ((term85 A A' B B' g' g y f' f x) = (y x)) = ((term85 A A' B B' g' g y f' f x) = (y x)).
Proof. exact (eq_refl ((term85 A A' B B' g' g y f' f x) = (y x))). Qed.
Lemma lem1075648 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (y : A -> B) : (term96 A A' B B' g' g f' f y) = (term96 A A' B B' g' g f' f y).
Proof. exact (fun_ext (fun x : A => @lem1075647 A A' B B' g' g f' f y x)). Qed.
Lemma lem1075649 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1075650 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (y : A -> B) : (term97 A A' B B' g' g f' f y) = (term97 A A' B B' g' g f' f y).
Proof. exact (MK_COMB (@lem1075649 A) (@lem1075648 A A' B B' g' g f' f y)). Qed.
Lemma lem1075651 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term99 A A' B B' g' g f' f) = (term99 A A' B B' g' g f' f).
Proof. exact (fun_ext (fun y : A -> B => @lem1075650 A A' B B' g' g f' f y)). Qed.
Lemma lem1075652 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem1075653 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term101 A A' B B' g' g f' f) = (term101 A A' B B' g' g f' f).
Proof. exact (MK_COMB (@lem1075652 A B) (@lem1075651 A A' B B' g' g f' f)). Qed.
Lemma lem1075654 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) (x : A' -> B') (x' : A') : ((term47 A A' B B' g g' x f f' x') = (x x')) = ((term47 A A' B B' g g' x f f' x') = (x x')).
Proof. exact (eq_refl ((term47 A A' B B' g g' x f f' x') = (x x'))). Qed.
Lemma lem1075655 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) (x : A' -> B') : (term58 A A' B B' g g' f f' x) = (term58 A A' B B' g g' f f' x).
Proof. exact (fun_ext (fun x' : A' => @lem1075654 A A' B B' g g' f f' x x')). Qed.
Lemma lem1075656 {A' : Type'} : (@all A') = (@all A').
Proof. exact (eq_refl (@all A')). Qed.
Lemma lem1075657 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) (x : A' -> B') : (term59 A A' B B' g g' f f' x) = (term59 A A' B B' g g' f f' x).
Proof. exact (MK_COMB (@lem1075656 A') (@lem1075655 A A' B B' g g' f f' x)). Qed.
Lemma lem1075658 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) : (term61 A A' B B' g g' f f') = (term61 A A' B B' g g' f f').
Proof. exact (fun_ext (fun x : A' -> B' => @lem1075657 A A' B B' g g' f f' x)). Qed.
Lemma lem1075659 {A' B' : Type'} : (@all (A' -> B')) = (@all (A' -> B')).
Proof. exact (eq_refl (@all (A' -> B'))). Qed.
Lemma lem1075660 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) : (term63 A A' B B' g g' f f') = (term63 A A' B B' g g' f f').
Proof. exact (MK_COMB (@lem1075659 A' B') (@lem1075658 A A' B B' g g' f f')). Qed.
Lemma lem1075661 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1075662 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) : (term65 A A' B B' g g' f f') = (term65 A A' B B' g g' f f').
Proof. exact (MK_COMB (@lem1075661) (@lem1075660 A A' B B' g g' f f')). Qed.
Lemma lem1075663 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term102 A A' B B' g' g f' f) = (term102 A A' B B' g' g f' f).
Proof. exact (MK_COMB (@lem1075662 A A' B B' g g' f f') (@lem1075653 A A' B B' g' g f' f)). Qed.
Lemma lem1075664 {B B' : Type'} (g' : B' -> B) (g : B -> B') (y : B) : ((term129 B B' g' g y) = y) = ((term129 B B' g' g y) = y).
Proof. exact (eq_refl ((term129 B B' g' g y) = y)). Qed.
Lemma lem1075665 {B B' : Type'} (g' : B' -> B) (g : B -> B') : (term130 B B' g' g) = (term130 B B' g' g).
Proof. exact (fun_ext (fun y : B => @lem1075664 B B' g' g y)). Qed.
Lemma lem1075666 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1075667 {B B' : Type'} (g' : B' -> B) (g : B -> B') : (term131 B B' g' g) = (term131 B B' g' g).
Proof. exact (MK_COMB (@lem1075666 B) (@lem1075665 B B' g' g)). Qed.
Lemma lem1075668 {B B' : Type'} (g : B -> B') (g' : B' -> B) (x : B') : ((term132 B B' g g' x) = x) = ((term132 B B' g g' x) = x).
Proof. exact (eq_refl ((term132 B B' g g' x) = x)). Qed.
Lemma lem1075669 {B B' : Type'} (g : B -> B') (g' : B' -> B) : (term133 B B' g g') = (term133 B B' g g').
Proof. exact (fun_ext (fun x : B' => @lem1075668 B B' g g' x)). Qed.
Lemma lem1075670 {B' : Type'} : (@all B') = (@all B').
Proof. exact (eq_refl (@all B')). Qed.
Lemma lem1075671 {B B' : Type'} (g : B -> B') (g' : B' -> B) : (term134 B B' g g') = (term134 B B' g g').
Proof. exact (MK_COMB (@lem1075670 B') (@lem1075669 B B' g g')). Qed.
Lemma lem1075672 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1075673 {B B' : Type'} (g : B -> B') (g' : B' -> B) : (term135 B B' g g') = (term135 B B' g g').
Proof. exact (MK_COMB (@lem1075672) (@lem1075671 B B' g g')). Qed.
Lemma lem1075674 {B B' : Type'} (g' : B' -> B) (g : B -> B') : (term7 B B' g' g) = (term7 B B' g' g).
Proof. exact (MK_COMB (@lem1075673 B B' g g') (@lem1075667 B B' g' g)). Qed.
Lemma lem1075675 {A A' : Type'} (f' : A' -> A) (f : A -> A') (y : A) : ((term129 A A' f' f y) = y) = ((term129 A A' f' f y) = y).
Proof. exact (eq_refl ((term129 A A' f' f y) = y)). Qed.
Lemma lem1075676 {A A' : Type'} (f' : A' -> A) (f : A -> A') : (term130 A A' f' f) = (term130 A A' f' f).
Proof. exact (fun_ext (fun y : A => @lem1075675 A A' f' f y)). Qed.
Lemma lem1075677 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1075678 {A A' : Type'} (f' : A' -> A) (f : A -> A') : (term131 A A' f' f) = (term131 A A' f' f).
Proof. exact (MK_COMB (@lem1075677 A) (@lem1075676 A A' f' f)). Qed.
Lemma lem1075679 {A A' : Type'} (f : A -> A') (f' : A' -> A) (x : A') : ((term132 A A' f f' x) = x) = ((term132 A A' f f' x) = x).
Proof. exact (eq_refl ((term132 A A' f f' x) = x)). Qed.
Lemma lem1075680 {A A' : Type'} (f : A -> A') (f' : A' -> A) : (term133 A A' f f') = (term133 A A' f f').
Proof. exact (fun_ext (fun x : A' => @lem1075679 A A' f f' x)). Qed.
Lemma lem1075681 {A' : Type'} : (@all A') = (@all A').
Proof. exact (eq_refl (@all A')). Qed.
Lemma lem1075682 {A A' : Type'} (f : A -> A') (f' : A' -> A) : (term134 A A' f f') = (term134 A A' f f').
Proof. exact (MK_COMB (@lem1075681 A') (@lem1075680 A A' f f')). Qed.
Lemma lem1075683 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1075684 {A A' : Type'} (f : A -> A') (f' : A' -> A) : (term135 A A' f f') = (term135 A A' f f').
Proof. exact (MK_COMB (@lem1075683) (@lem1075682 A A' f f')). Qed.
Lemma lem1075685 {A A' : Type'} (f' : A' -> A) (f : A -> A') : (term7 A A' f' f) = (term7 A A' f' f).
Proof. exact (MK_COMB (@lem1075684 A A' f f') (@lem1075678 A A' f' f)). Qed.
Lemma lem1075686 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1075687 {A A' : Type'} (f' : A' -> A) (f : A -> A') : (term9 A A' f' f) = (term9 A A' f' f).
Proof. exact (MK_COMB (@lem1075686) (@lem1075685 A A' f' f)). Qed.
Lemma lem1075688 {A A' B B' : Type'} (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') : (term11 A A' B B' f' f g' g) = (term11 A A' B B' f' f g' g).
Proof. exact (MK_COMB (@lem1075687 A A' f' f) (@lem1075674 B B' g' g)). Qed.
Lemma lem1075689 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1075690 {A A' B B' : Type'} (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') : (term13 A A' B B' f' f g' g) = (term13 A A' B B' f' f g' g).
Proof. exact (MK_COMB (@lem1075689) (@lem1075688 A A' B B' f' f g' g)). Qed.
Lemma lem1075691 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term104 A A' B B' g' g f' f) = (term104 A A' B B' g' g f' f).
Proof. exact (MK_COMB (@lem1075690 A A' B B' f' f g' g) (@lem1075663 A A' B B' g' g f' f)). Qed.
Lemma lem1075692 {A A' B B' : Type'} (g : B -> B') (f' : A' -> A) (f : A -> A') : (term114 A A' B B' g f' f) = (term114 A A' B B' g f' f).
Proof. exact (fun_ext (fun g' : B' -> B => @lem1075691 A A' B B' g' g f' f)). Qed.
Lemma lem1075693 {B B' : Type'} : (@all (B' -> B)) = (@all (B' -> B)).
Proof. exact (eq_refl (@all (B' -> B))). Qed.
Lemma lem1075694 {A A' B B' : Type'} (g : B -> B') (f' : A' -> A) (f : A -> A') : (term116 A A' B B' g f' f) = (term116 A A' B B' g f' f).
Proof. exact (MK_COMB (@lem1075693 B B') (@lem1075692 A A' B B' g f' f)). Qed.
Lemma lem1075695 {A A' B B' : Type'} (f' : A' -> A) (f : A -> A') : (term118 A A' B B' f' f) = (term118 A A' B B' f' f).
Proof. exact (fun_ext (fun g : B -> B' => @lem1075694 A A' B B' g f' f)). Qed.
Lemma lem1075696 {B B' : Type'} : (@all (B -> B')) = (@all (B -> B')).
Proof. exact (eq_refl (@all (B -> B'))). Qed.
Lemma lem1075697 {A A' B B' : Type'} (f' : A' -> A) (f : A -> A') : (term120 A A' B B' f' f) = (term120 A A' B B' f' f).
Proof. exact (MK_COMB (@lem1075696 B B') (@lem1075695 A A' B B' f' f)). Qed.
Lemma lem1075698 {A A' B B' : Type'} (f : A -> A') : (term122 A A' B B' f) = (term122 A A' B B' f).
Proof. exact (fun_ext (fun f' : A' -> A => @lem1075697 A A' B B' f' f)). Qed.
Lemma lem1075699 {A A' : Type'} : (@all (A' -> A)) = (@all (A' -> A)).
Proof. exact (eq_refl (@all (A' -> A))). Qed.
Lemma lem1075700 {A A' B B' : Type'} (f : A -> A') : (term124 A A' B B' f) = (term124 A A' B B' f).
Proof. exact (MK_COMB (@lem1075699 A A') (@lem1075698 A A' B B' f)). Qed.
Lemma lem1075701 {A A' B B' : Type'} : (term126 A A' B B') = (term126 A A' B B').
Proof. exact (fun_ext (fun f : A -> A' => @lem1075700 A A' B B' f)). Qed.
Lemma lem1075702 {A A' : Type'} : (@all (A -> A')) = (@all (A -> A')).
Proof. exact (eq_refl (@all (A -> A'))). Qed.
Lemma lem1075703 {A A' B B' : Type'} : (term128 A A' B B') = (term128 A A' B B').
Proof. exact (MK_COMB (@lem1075702 A A') (@lem1075701 A A' B B')). Qed.
Lemma lem1075788 {A A' B B' : Type'} : (term127 A A' B B') = (term128 A A' B B').
Proof. exact (TRANS (@lem1075646 A A' B B') (@lem1075703 A A' B B')). Qed.
Lemma lem1075789 {A A' B B' : Type'} : (term128 A A' B B') = (term127 A A' B B').
Proof. exact (SYM (@lem1075788 A A' B B')). Qed.
Lemma lem1075790 {A A' B B' : Type'} (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : term11 A A' B B' f' f g' g.
Proof. exact (h1). Qed.
Lemma lem1075792 (p : Prop) : p = (term105 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1075793 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term102 A A' B B' g' g f' f) = (term136 A A' B B' g' g f' f).
Proof. exact (@lem1075792 (term102 A A' B B' g' g f' f)). Qed.
Lemma lem1075794 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term136 A A' B B' g' g f' f) = (term102 A A' B B' g' g f' f).
Proof. exact (SYM (@lem1075793 A A' B B' g' g f' f)). Qed.
Lemma lem1075795 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (h1 : term137 A A' B B' g' g f' f) : term137 A A' B B' g' g f' f.
Proof. exact (h1). Qed.
Lemma lem1075796 {A A' : Type'} (f : A -> A') (f' : A' -> A) (x : A') : ((term132 A A' f f' x) = x) = ((term132 A A' f f' x) = x).
Proof. exact (eq_refl ((term132 A A' f f' x) = x)). Qed.
Lemma lem1075797 {A A' : Type'} (f : A -> A') (f' : A' -> A) : (term133 A A' f f') = (term133 A A' f f').
Proof. exact (fun_ext (fun x : A' => @lem1075796 A A' f f' x)). Qed.
Lemma lem1075798 {A' : Type'} : (@all A') = (@all A').
Proof. exact (eq_refl (@all A')). Qed.
Lemma lem1075799 {A A' : Type'} (f : A -> A') (f' : A' -> A) : (term134 A A' f f') = (term134 A A' f f').
Proof. exact (MK_COMB (@lem1075798 A') (@lem1075797 A A' f f')). Qed.
Lemma lem1075800 {A A' : Type'} (f' : A' -> A) (f : A -> A') (y : A) : ((term129 A A' f' f y) = y) = ((term129 A A' f' f y) = y).
Proof. exact (eq_refl ((term129 A A' f' f y) = y)). Qed.
Lemma lem1075801 {A A' : Type'} (f' : A' -> A) (f : A -> A') : (term130 A A' f' f) = (term130 A A' f' f).
Proof. exact (fun_ext (fun y : A => @lem1075800 A A' f' f y)). Qed.
Lemma lem1075802 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1075803 {A A' : Type'} (f' : A' -> A) (f : A -> A') : (term131 A A' f' f) = (term131 A A' f' f).
Proof. exact (MK_COMB (@lem1075802 A) (@lem1075801 A A' f' f)). Qed.
Lemma lem1075804 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1075805 {A A' : Type'} (f : A -> A') (f' : A' -> A) : (term135 A A' f f') = (term135 A A' f f').
Proof. exact (MK_COMB (@lem1075804) (@lem1075799 A A' f f')). Qed.
Lemma lem1075806 {A A' : Type'} (f' : A' -> A) (f : A -> A') : (term7 A A' f' f) = (term7 A A' f' f).
Proof. exact (MK_COMB (@lem1075805 A A' f f') (@lem1075803 A A' f' f)). Qed.
Lemma lem1075807 {B B' : Type'} (g : B -> B') (g' : B' -> B) (x : B') : ((term132 B B' g g' x) = x) = ((term132 B B' g g' x) = x).
Proof. exact (eq_refl ((term132 B B' g g' x) = x)). Qed.
Lemma lem1075808 {B B' : Type'} (g : B -> B') (g' : B' -> B) : (term133 B B' g g') = (term133 B B' g g').
Proof. exact (fun_ext (fun x : B' => @lem1075807 B B' g g' x)). Qed.
Lemma lem1075809 {B' : Type'} : (@all B') = (@all B').
Proof. exact (eq_refl (@all B')). Qed.
Lemma lem1075810 {B B' : Type'} (g : B -> B') (g' : B' -> B) : (term134 B B' g g') = (term134 B B' g g').
Proof. exact (MK_COMB (@lem1075809 B') (@lem1075808 B B' g g')). Qed.
Lemma lem1075811 {B B' : Type'} (g' : B' -> B) (g : B -> B') (y : B) : ((term129 B B' g' g y) = y) = ((term129 B B' g' g y) = y).
Proof. exact (eq_refl ((term129 B B' g' g y) = y)). Qed.
Lemma lem1075812 {B B' : Type'} (g' : B' -> B) (g : B -> B') : (term130 B B' g' g) = (term130 B B' g' g).
Proof. exact (fun_ext (fun y : B => @lem1075811 B B' g' g y)). Qed.
Lemma lem1075813 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1075814 {B B' : Type'} (g' : B' -> B) (g : B -> B') : (term131 B B' g' g) = (term131 B B' g' g).
Proof. exact (MK_COMB (@lem1075813 B) (@lem1075812 B B' g' g)). Qed.
Lemma lem1075815 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1075816 {B B' : Type'} (g : B -> B') (g' : B' -> B) : (term135 B B' g g') = (term135 B B' g g').
Proof. exact (MK_COMB (@lem1075815) (@lem1075810 B B' g g')). Qed.
Lemma lem1075817 {B B' : Type'} (g' : B' -> B) (g : B -> B') : (term7 B B' g' g) = (term7 B B' g' g).
Proof. exact (MK_COMB (@lem1075816 B B' g g') (@lem1075814 B B' g' g)). Qed.
Lemma lem1075818 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1075819 {A A' : Type'} (f' : A' -> A) (f : A -> A') : (term9 A A' f' f) = (term9 A A' f' f).
Proof. exact (MK_COMB (@lem1075818) (@lem1075806 A A' f' f)). Qed.
Lemma lem1075840 {A A' B B' : Type'} (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') : (term11 A A' B B' f' f g' g) = (term11 A A' B B' f' f g' g).
Proof. exact (MK_COMB (@lem1075819 A A' f' f) (@lem1075817 B B' g' g)). Qed.
Lemma lem1075841 {A A' B B' : Type'} (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : term11 A A' B B' f' f g' g.
Proof. exact (EQ_MP (@lem1075840 A A' B B' f' f g' g) (@lem1075790 A A' B B' f' f g' g h1)). Qed.
Lemma lem1075843 {A' : Type'} (P : A' -> Prop) : (term138 A' P) = (term139 A' P).
Proof. exact (@lem18392 A' P). Qed.
Lemma lem1075844 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) (x : A' -> B') : (term140 A A' B B' g g' f f' x) = (term141 A A' B B' g g' f f' x).
Proof. exact (@lem1075843 A' (term58 A A' B B' g g' f f' x)). Qed.
Lemma lem1075845 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) (x : A' -> B') (x' : A') : (term142 A A' B B' g g' f f' x x') = ((term47 A A' B B' g g' x f f' x') = (x x')).
Proof. exact (eq_refl (term142 A A' B B' g g' f f' x x')). Qed.
Lemma lem1075846 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1075848 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) (x : A' -> B') (x' : A') : (term143 A A' B B' g g' f f' x x') = (term144 A A' B B' g g' f f' x x').
Proof. exact (MK_COMB (@lem1075846) (@lem1075845 A A' B B' g g' f f' x x')). Qed.
Lemma lem1075849 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) (x : A' -> B') : (term145 A A' B B' g g' f f' x) = (term146 A A' B B' g g' f f' x).
Proof. exact (fun_ext (fun x' : A' => @lem1075848 A A' B B' g g' f f' x x')). Qed.
Lemma lem1075850 {A' : Type'} : (@ex A') = (@ex A').
Proof. exact (eq_refl (@ex A')). Qed.
Lemma lem1075851 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) (x : A' -> B') : (term141 A A' B B' g g' f f' x) = (term147 A A' B B' g g' f f' x).
Proof. exact (MK_COMB (@lem1075850 A') (@lem1075849 A A' B B' g g' f f' x)). Qed.
Lemma lem1075852 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) (x : A' -> B') : (term140 A A' B B' g g' f f' x) = (term147 A A' B B' g g' f f' x).
Proof. exact (TRANS (@lem1075844 A A' B B' g g' f f' x) (@lem1075851 A A' B B' g g' f f' x)). Qed.
Lemma lem1075853 {A' B' : Type'} (P : type572 A' B') : (term148 A' B' P) = (term149 A' B' P).
Proof. exact (@lem18392 (A' -> B') P). Qed.
Lemma lem1075854 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) : (term150 A A' B B' g g' f f') = (term151 A A' B B' g g' f f').
Proof. exact (@lem1075853 A' B' (term61 A A' B B' g g' f f')). Qed.
Lemma lem1075855 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) (x : A' -> B') : (term152 A A' B B' g g' f f' x) = (term59 A A' B B' g g' f f' x).
Proof. exact (eq_refl (term152 A A' B B' g g' f f' x)). Qed.
Lemma lem1075856 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1075857 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) (x : A' -> B') : (term153 A A' B B' g g' f f' x) = (term140 A A' B B' g g' f f' x).
Proof. exact (MK_COMB (@lem1075856) (@lem1075855 A A' B B' g g' f f' x)). Qed.
Lemma lem1075858 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) (x : A' -> B') : (term153 A A' B B' g g' f f' x) = (term147 A A' B B' g g' f f' x).
Proof. exact (TRANS (@lem1075857 A A' B B' g g' f f' x) (@lem1075852 A A' B B' g g' f f' x)). Qed.
Lemma lem1075859 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) : (term154 A A' B B' g g' f f') = (term155 A A' B B' g g' f f').
Proof. exact (fun_ext (fun x : A' -> B' => @lem1075858 A A' B B' g g' f f' x)). Qed.
Lemma lem1075860 {A' B' : Type'} : (@ex (A' -> B')) = (@ex (A' -> B')).
Proof. exact (eq_refl (@ex (A' -> B'))). Qed.
Lemma lem1075861 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) : (term151 A A' B B' g g' f f') = (term156 A A' B B' g g' f f').
Proof. exact (MK_COMB (@lem1075860 A' B') (@lem1075859 A A' B B' g g' f f')). Qed.
Lemma lem1075862 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) : (term150 A A' B B' g g' f f') = (term156 A A' B B' g g' f f').
Proof. exact (TRANS (@lem1075854 A A' B B' g g' f f') (@lem1075861 A A' B B' g g' f f')). Qed.
Lemma lem1075864 {A : Type'} (P : A -> Prop) : (term138 A P) = (term139 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem1075865 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (y : A -> B) : (term157 A A' B B' g' g f' f y) = (term158 A A' B B' g' g f' f y).
Proof. exact (@lem1075864 A (term96 A A' B B' g' g f' f y)). Qed.
Lemma lem1075866 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (y : A -> B) (x : A) : (term159 A A' B B' g' g f' f y x) = ((term85 A A' B B' g' g y f' f x) = (y x)).
Proof. exact (eq_refl (term159 A A' B B' g' g f' f y x)). Qed.
Lemma lem1075867 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1075869 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (y : A -> B) (x : A) : (term160 A A' B B' g' g f' f y x) = (term161 A A' B B' g' g f' f y x).
Proof. exact (MK_COMB (@lem1075867) (@lem1075866 A A' B B' g' g f' f y x)). Qed.
Lemma lem1075870 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (y : A -> B) : (term162 A A' B B' g' g f' f y) = (term163 A A' B B' g' g f' f y).
Proof. exact (fun_ext (fun x : A => @lem1075869 A A' B B' g' g f' f y x)). Qed.
Lemma lem1075871 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1075872 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (y : A -> B) : (term158 A A' B B' g' g f' f y) = (term164 A A' B B' g' g f' f y).
Proof. exact (MK_COMB (@lem1075871 A) (@lem1075870 A A' B B' g' g f' f y)). Qed.
Lemma lem1075873 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (y : A -> B) : (term157 A A' B B' g' g f' f y) = (term164 A A' B B' g' g f' f y).
Proof. exact (TRANS (@lem1075865 A A' B B' g' g f' f y) (@lem1075872 A A' B B' g' g f' f y)). Qed.
Lemma lem1075874 {A B : Type'} (P : type572 A B) : (term148 A B P) = (term149 A B P).
Proof. exact (@lem18392 (A -> B) P). Qed.
Lemma lem1075875 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term165 A A' B B' g' g f' f) = (term166 A A' B B' g' g f' f).
Proof. exact (@lem1075874 A B (term99 A A' B B' g' g f' f)). Qed.
Lemma lem1075876 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (y : A -> B) : (term167 A A' B B' g' g f' f y) = (term97 A A' B B' g' g f' f y).
Proof. exact (eq_refl (term167 A A' B B' g' g f' f y)). Qed.
Lemma lem1075877 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1075878 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (y : A -> B) : (term168 A A' B B' g' g f' f y) = (term157 A A' B B' g' g f' f y).
Proof. exact (MK_COMB (@lem1075877) (@lem1075876 A A' B B' g' g f' f y)). Qed.
Lemma lem1075879 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (y : A -> B) : (term168 A A' B B' g' g f' f y) = (term164 A A' B B' g' g f' f y).
Proof. exact (TRANS (@lem1075878 A A' B B' g' g f' f y) (@lem1075873 A A' B B' g' g f' f y)). Qed.
Lemma lem1075880 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term169 A A' B B' g' g f' f) = (term170 A A' B B' g' g f' f).
Proof. exact (fun_ext (fun y : A -> B => @lem1075879 A A' B B' g' g f' f y)). Qed.
Lemma lem1075881 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem1075882 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term166 A A' B B' g' g f' f) = (term171 A A' B B' g' g f' f).
Proof. exact (MK_COMB (@lem1075881 A B) (@lem1075880 A A' B B' g' g f' f)). Qed.
Lemma lem1075883 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term165 A A' B B' g' g f' f) = (term171 A A' B B' g' g f' f).
Proof. exact (TRANS (@lem1075875 A A' B B' g' g f' f) (@lem1075882 A A' B B' g' g f' f)). Qed.
Lemma lem1075884 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1075885 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) : (term172 A A' B B' g g' f f') = (term173 A A' B B' g g' f f').
Proof. exact (MK_COMB (@lem1075884) (@lem1075862 A A' B B' g g' f f')). Qed.
Lemma lem1075886 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term174 A A' B B' g' g f' f) = (term175 A A' B B' g' g f' f).
Proof. exact (MK_COMB (@lem1075885 A A' B B' g g' f f') (@lem1075883 A A' B B' g' g f' f)). Qed.
Lemma lem1075887 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term137 A A' B B' g' g f' f) = (term174 A A' B B' g' g f' f).
Proof. exact (@lem17045 (term63 A A' B B' g g' f f') (term101 A A' B B' g' g f' f)). Qed.
Lemma lem1075888 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term137 A A' B B' g' g f' f) = (term175 A A' B B' g' g f' f).
Proof. exact (TRANS (@lem1075887 A A' B B' g' g f' f) (@lem1075886 A A' B B' g' g f' f)). Qed.
Lemma lem1075909 {A : Type'} (P : A -> Prop) (Q : Prop) : (term176 A P Q) = (term177 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem1075910 {A' B' : Type'} (P : type572 A' B') (Q : Prop) : (term178 A' B' P Q) = (term179 A' B' P Q).
Proof. exact (@lem1075909 (A' -> B') P Q). Qed.
Lemma lem1075911 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term180 A A' B B' g' g f' f) = (term181 A A' B B' g' g f' f).
Proof. exact (@lem1075910 A' B' (term155 A A' B B' g g' f f') (term171 A A' B B' g' g f' f)). Qed.
Lemma lem1075912 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) (x : A' -> B') : (term182 A A' B B' g g' f f' x) = (term147 A A' B B' g g' f f' x).
Proof. exact (eq_refl (term182 A A' B B' g g' f f' x)). Qed.
Lemma lem1075913 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) : (term183 A A' B B' g g' f f') = (term155 A A' B B' g g' f f').
Proof. exact (fun_ext (fun x : A' -> B' => @lem1075912 A A' B B' g g' f f' x)). Qed.
Lemma lem1075914 {A' B' : Type'} : (@ex (A' -> B')) = (@ex (A' -> B')).
Proof. exact (eq_refl (@ex (A' -> B'))). Qed.
Lemma lem1075915 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) : (term184 A A' B B' g g' f f') = (term156 A A' B B' g g' f f').
Proof. exact (MK_COMB (@lem1075914 A' B') (@lem1075913 A A' B B' g g' f f')). Qed.
Lemma lem1075916 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1075917 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) : (term185 A A' B B' g g' f f') = (term173 A A' B B' g g' f f').
Proof. exact (MK_COMB (@lem1075916) (@lem1075915 A A' B B' g g' f f')). Qed.
Lemma lem1075918 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term171 A A' B B' g' g f' f) = (term171 A A' B B' g' g f' f).
Proof. exact (eq_refl (term171 A A' B B' g' g f' f)). Qed.
Lemma lem1075919 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term180 A A' B B' g' g f' f) = (term175 A A' B B' g' g f' f).
Proof. exact (MK_COMB (@lem1075917 A A' B B' g g' f f') (@lem1075918 A A' B B' g' g f' f)). Qed.
Lemma lem1075920 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1075921 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term186 A A' B B' g' g f' f) = (term187 A A' B B' g' g f' f).
Proof. exact (MK_COMB (@lem1075920) (@lem1075919 A A' B B' g' g f' f)). Qed.
Lemma lem1075922 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) (x : A' -> B') : (term182 A A' B B' g g' f f' x) = (term147 A A' B B' g g' f f' x).
Proof. exact (eq_refl (term182 A A' B B' g g' f f' x)). Qed.
Lemma lem1075923 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1075924 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) (x : A' -> B') : (term188 A A' B B' g g' f f' x) = (term189 A A' B B' g g' f f' x).
Proof. exact (MK_COMB (@lem1075923) (@lem1075922 A A' B B' g g' f f' x)). Qed.
Lemma lem1075925 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term171 A A' B B' g' g f' f) = (term171 A A' B B' g' g f' f).
Proof. exact (eq_refl (term171 A A' B B' g' g f' f)). Qed.
Lemma lem1075926 {A A' B B' : Type'} (x : A' -> B') (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term190 A A' B B' x g' g f' f) = (term191 A A' B B' x g' g f' f).
Proof. exact (MK_COMB (@lem1075924 A A' B B' g g' f f' x) (@lem1075925 A A' B B' g' g f' f)). Qed.
Lemma lem1075927 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term192 A A' B B' g' g f' f) = (term193 A A' B B' g' g f' f).
Proof. exact (fun_ext (fun x : A' -> B' => @lem1075926 A A' B B' x g' g f' f)). Qed.
Lemma lem1075928 {A' B' : Type'} : (@ex (A' -> B')) = (@ex (A' -> B')).
Proof. exact (eq_refl (@ex (A' -> B'))). Qed.
Lemma lem1075929 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term181 A A' B B' g' g f' f) = (term194 A A' B B' g' g f' f).
Proof. exact (MK_COMB (@lem1075928 A' B') (@lem1075927 A A' B B' g' g f' f)). Qed.
Lemma lem1075930 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : ((term180 A A' B B' g' g f' f) = (term181 A A' B B' g' g f' f)) = ((term175 A A' B B' g' g f' f) = (term194 A A' B B' g' g f' f)).
Proof. exact (MK_COMB (@lem1075921 A A' B B' g' g f' f) (@lem1075929 A A' B B' g' g f' f)). Qed.
Lemma lem1075931 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term175 A A' B B' g' g f' f) = (term194 A A' B B' g' g f' f).
Proof. exact (EQ_MP (@lem1075930 A A' B B' g' g f' f) (@lem1075911 A A' B B' g' g f' f)). Qed.
Lemma lem1075935 {A : Type'} (P : A -> Prop) (Q : Prop) : (term176 A P Q) = (term177 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem1075936 {A' : Type'} (P : A' -> Prop) (Q : Prop) : (term176 A' P Q) = (term177 A' P Q).
Proof. exact (@lem1075935 A' P Q). Qed.
Lemma lem1075937 {A A' B B' : Type'} (x : A' -> B') (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term195 A A' B B' x g' g f' f) = (term196 A A' B B' x g' g f' f).
Proof. exact (@lem1075936 A' (term146 A A' B B' g g' f f' x) (term171 A A' B B' g' g f' f)). Qed.
Lemma lem1075938 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) (x : A' -> B') (x' : A') : (term197 A A' B B' g g' f f' x x') = (term144 A A' B B' g g' f f' x x').
Proof. exact (eq_refl (term197 A A' B B' g g' f f' x x')). Qed.
Lemma lem1075939 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) (x : A' -> B') : (term198 A A' B B' g g' f f' x) = (term146 A A' B B' g g' f f' x).
Proof. exact (fun_ext (fun x' : A' => @lem1075938 A A' B B' g g' f f' x x')). Qed.
Lemma lem1075940 {A' : Type'} : (@ex A') = (@ex A').
Proof. exact (eq_refl (@ex A')). Qed.
Lemma lem1075941 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) (x : A' -> B') : (term199 A A' B B' g g' f f' x) = (term147 A A' B B' g g' f f' x).
Proof. exact (MK_COMB (@lem1075940 A') (@lem1075939 A A' B B' g g' f f' x)). Qed.
Lemma lem1075942 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1075943 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) (x : A' -> B') : (term200 A A' B B' g g' f f' x) = (term189 A A' B B' g g' f f' x).
Proof. exact (MK_COMB (@lem1075942) (@lem1075941 A A' B B' g g' f f' x)). Qed.
Lemma lem1075944 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term171 A A' B B' g' g f' f) = (term171 A A' B B' g' g f' f).
Proof. exact (eq_refl (term171 A A' B B' g' g f' f)). Qed.
Lemma lem1075945 {A A' B B' : Type'} (x : A' -> B') (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term195 A A' B B' x g' g f' f) = (term191 A A' B B' x g' g f' f).
Proof. exact (MK_COMB (@lem1075943 A A' B B' g g' f f' x) (@lem1075944 A A' B B' g' g f' f)). Qed.
Lemma lem1075946 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1075947 {A A' B B' : Type'} (x : A' -> B') (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term201 A A' B B' x g' g f' f) = (term202 A A' B B' x g' g f' f).
Proof. exact (MK_COMB (@lem1075946) (@lem1075945 A A' B B' x g' g f' f)). Qed.
Lemma lem1075948 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) (x : A' -> B') (x' : A') : (term197 A A' B B' g g' f f' x x') = (term144 A A' B B' g g' f f' x x').
Proof. exact (eq_refl (term197 A A' B B' g g' f f' x x')). Qed.
Lemma lem1075949 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1075950 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) (x : A' -> B') (x' : A') : (term203 A A' B B' g g' f f' x x') = (term204 A A' B B' g g' f f' x x').
Proof. exact (MK_COMB (@lem1075949) (@lem1075948 A A' B B' g g' f f' x x')). Qed.
Lemma lem1075951 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term171 A A' B B' g' g f' f) = (term171 A A' B B' g' g f' f).
Proof. exact (eq_refl (term171 A A' B B' g' g f' f)). Qed.
Lemma lem1075952 {A A' B B' : Type'} (x : A' -> B') (x' : A') (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term205 A A' B B' x x' g' g f' f) = (term206 A A' B B' x x' g' g f' f).
Proof. exact (MK_COMB (@lem1075950 A A' B B' g g' f f' x x') (@lem1075951 A A' B B' g' g f' f)). Qed.
Lemma lem1075953 {A A' B B' : Type'} (x : A' -> B') (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term207 A A' B B' x g' g f' f) = (term208 A A' B B' x g' g f' f).
Proof. exact (fun_ext (fun x' : A' => @lem1075952 A A' B B' x x' g' g f' f)). Qed.
Lemma lem1075954 {A' : Type'} : (@ex A') = (@ex A').
Proof. exact (eq_refl (@ex A')). Qed.
Lemma lem1075955 {A A' B B' : Type'} (x : A' -> B') (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term196 A A' B B' x g' g f' f) = (term209 A A' B B' x g' g f' f).
Proof. exact (MK_COMB (@lem1075954 A') (@lem1075953 A A' B B' x g' g f' f)). Qed.
Lemma lem1075956 {A A' B B' : Type'} (x : A' -> B') (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : ((term195 A A' B B' x g' g f' f) = (term196 A A' B B' x g' g f' f)) = ((term191 A A' B B' x g' g f' f) = (term209 A A' B B' x g' g f' f)).
Proof. exact (MK_COMB (@lem1075947 A A' B B' x g' g f' f) (@lem1075955 A A' B B' x g' g f' f)). Qed.
Lemma lem1075957 {A A' B B' : Type'} (x : A' -> B') (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term191 A A' B B' x g' g f' f) = (term209 A A' B B' x g' g f' f).
Proof. exact (EQ_MP (@lem1075956 A A' B B' x g' g f' f) (@lem1075937 A A' B B' x g' g f' f)). Qed.
Lemma lem1075959 {A : Type'} (P : Prop) (Q : A -> Prop) : (term210 A P Q) = (term211 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1075960 {A B : Type'} (P : Prop) (Q : type572 A B) : (term212 A B P Q) = (term213 A B P Q).
Proof. exact (@lem1075959 (A -> B) P Q). Qed.
Lemma lem1075961 {A A' B B' : Type'} (x : A' -> B') (x' : A') (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term214 A A' B B' x x' g' g f' f) = (term215 A A' B B' x x' g' g f' f).
Proof. exact (@lem1075960 A B (term144 A A' B B' g g' f f' x x') (term170 A A' B B' g' g f' f)). Qed.
Lemma lem1075962 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (y : A -> B) : (term216 A A' B B' g' g f' f y) = (term164 A A' B B' g' g f' f y).
Proof. exact (eq_refl (term216 A A' B B' g' g f' f y)). Qed.
Lemma lem1075963 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term217 A A' B B' g' g f' f) = (term170 A A' B B' g' g f' f).
Proof. exact (fun_ext (fun y : A -> B => @lem1075962 A A' B B' g' g f' f y)). Qed.
Lemma lem1075964 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem1075965 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term218 A A' B B' g' g f' f) = (term171 A A' B B' g' g f' f).
Proof. exact (MK_COMB (@lem1075964 A B) (@lem1075963 A A' B B' g' g f' f)). Qed.
Lemma lem1075966 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) (x : A' -> B') (x' : A') : (term204 A A' B B' g g' f f' x x') = (term204 A A' B B' g g' f f' x x').
Proof. exact (eq_refl (term204 A A' B B' g g' f f' x x')). Qed.
Lemma lem1075967 {A A' B B' : Type'} (x : A' -> B') (x' : A') (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term214 A A' B B' x x' g' g f' f) = (term206 A A' B B' x x' g' g f' f).
Proof. exact (MK_COMB (@lem1075966 A A' B B' g g' f f' x x') (@lem1075965 A A' B B' g' g f' f)). Qed.
Lemma lem1075968 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1075969 {A A' B B' : Type'} (x : A' -> B') (x' : A') (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term219 A A' B B' x x' g' g f' f) = (term220 A A' B B' x x' g' g f' f).
Proof. exact (MK_COMB (@lem1075968) (@lem1075967 A A' B B' x x' g' g f' f)). Qed.
Lemma lem1075970 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (y : A -> B) : (term216 A A' B B' g' g f' f y) = (term164 A A' B B' g' g f' f y).
Proof. exact (eq_refl (term216 A A' B B' g' g f' f y)). Qed.
Lemma lem1075971 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) (x : A' -> B') (x' : A') : (term204 A A' B B' g g' f f' x x') = (term204 A A' B B' g g' f f' x x').
Proof. exact (eq_refl (term204 A A' B B' g g' f f' x x')). Qed.
Lemma lem1075972 {A A' B B' : Type'} (x : A' -> B') (x' : A') (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (y : A -> B) : (term221 A A' B B' x x' g' g f' f y) = (term222 A A' B B' x x' g' g f' f y).
Proof. exact (MK_COMB (@lem1075971 A A' B B' g g' f f' x x') (@lem1075970 A A' B B' g' g f' f y)). Qed.
Lemma lem1075973 {A A' B B' : Type'} (x : A' -> B') (x' : A') (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term223 A A' B B' x x' g' g f' f) = (term224 A A' B B' x x' g' g f' f).
Proof. exact (fun_ext (fun y : A -> B => @lem1075972 A A' B B' x x' g' g f' f y)). Qed.
Lemma lem1075974 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem1075975 {A A' B B' : Type'} (x : A' -> B') (x' : A') (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term215 A A' B B' x x' g' g f' f) = (term225 A A' B B' x x' g' g f' f).
Proof. exact (MK_COMB (@lem1075974 A B) (@lem1075973 A A' B B' x x' g' g f' f)). Qed.
Lemma lem1075976 {A A' B B' : Type'} (x : A' -> B') (x' : A') (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : ((term214 A A' B B' x x' g' g f' f) = (term215 A A' B B' x x' g' g f' f)) = ((term206 A A' B B' x x' g' g f' f) = (term225 A A' B B' x x' g' g f' f)).
Proof. exact (MK_COMB (@lem1075969 A A' B B' x x' g' g f' f) (@lem1075975 A A' B B' x x' g' g f' f)). Qed.
Lemma lem1075977 {A A' B B' : Type'} (x : A' -> B') (x' : A') (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term206 A A' B B' x x' g' g f' f) = (term225 A A' B B' x x' g' g f' f).
Proof. exact (EQ_MP (@lem1075976 A A' B B' x x' g' g f' f) (@lem1075961 A A' B B' x x' g' g f' f)). Qed.
Lemma lem1075979 {A : Type'} (P : Prop) (Q : A -> Prop) : (term210 A P Q) = (term211 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1075980 {A : Type'} (P : Prop) (Q : A -> Prop) : (term210 A P Q) = (term211 A P Q).
Proof. exact (@lem1075979 A P Q). Qed.
Lemma lem1075981 {A A' B B' : Type'} (x : A' -> B') (x' : A') (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (y : A -> B) : (term226 A A' B B' x x' g' g f' f y) = (term227 A A' B B' x x' g' g f' f y).
Proof. exact (@lem1075980 A (term144 A A' B B' g g' f f' x x') (term163 A A' B B' g' g f' f y)). Qed.
Lemma lem1075982 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (y : A -> B) (x : A) : (term228 A A' B B' g' g f' f y x) = (term161 A A' B B' g' g f' f y x).
Proof. exact (eq_refl (term228 A A' B B' g' g f' f y x)). Qed.
Lemma lem1075983 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (y : A -> B) : (term229 A A' B B' g' g f' f y) = (term163 A A' B B' g' g f' f y).
Proof. exact (fun_ext (fun x : A => @lem1075982 A A' B B' g' g f' f y x)). Qed.
Lemma lem1075984 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1075985 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (y : A -> B) : (term230 A A' B B' g' g f' f y) = (term164 A A' B B' g' g f' f y).
Proof. exact (MK_COMB (@lem1075984 A) (@lem1075983 A A' B B' g' g f' f y)). Qed.
Lemma lem1075986 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) (x : A' -> B') (x' : A') : (term204 A A' B B' g g' f f' x x') = (term204 A A' B B' g g' f f' x x').
Proof. exact (eq_refl (term204 A A' B B' g g' f f' x x')). Qed.
Lemma lem1075987 {A A' B B' : Type'} (x : A' -> B') (x' : A') (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (y : A -> B) : (term226 A A' B B' x x' g' g f' f y) = (term222 A A' B B' x x' g' g f' f y).
Proof. exact (MK_COMB (@lem1075986 A A' B B' g g' f f' x x') (@lem1075985 A A' B B' g' g f' f y)). Qed.
Lemma lem1075988 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1075989 {A A' B B' : Type'} (x : A' -> B') (x' : A') (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (y : A -> B) : (term231 A A' B B' x x' g' g f' f y) = (term232 A A' B B' x x' g' g f' f y).
Proof. exact (MK_COMB (@lem1075988) (@lem1075987 A A' B B' x x' g' g f' f y)). Qed.
Lemma lem1075990 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (y : A -> B) (x : A) : (term228 A A' B B' g' g f' f y x) = (term161 A A' B B' g' g f' f y x).
Proof. exact (eq_refl (term228 A A' B B' g' g f' f y x)). Qed.
Lemma lem1075991 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) (x : A' -> B') (x' : A') : (term204 A A' B B' g g' f f' x x') = (term204 A A' B B' g g' f f' x x').
Proof. exact (eq_refl (term204 A A' B B' g g' f f' x x')). Qed.
Lemma lem1075992 {A A' B B' : Type'} (x : A' -> B') (x' : A') (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (y : A -> B) (x'' : A) : (term233 A A' B B' x x' g' g f' f y x'') = (term234 A A' B B' x x' g' g f' f y x'').
Proof. exact (MK_COMB (@lem1075991 A A' B B' g g' f f' x x') (@lem1075990 A A' B B' g' g f' f y x'')). Qed.
Lemma lem1075993 {A A' B B' : Type'} (x : A' -> B') (x' : A') (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (y : A -> B) : (term235 A A' B B' x x' g' g f' f y) = (term236 A A' B B' x x' g' g f' f y).
Proof. exact (fun_ext (fun x'' : A => @lem1075992 A A' B B' x x' g' g f' f y x'')). Qed.
Lemma lem1075994 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1075995 {A A' B B' : Type'} (x : A' -> B') (x' : A') (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (y : A -> B) : (term227 A A' B B' x x' g' g f' f y) = (term237 A A' B B' x x' g' g f' f y).
Proof. exact (MK_COMB (@lem1075994 A) (@lem1075993 A A' B B' x x' g' g f' f y)). Qed.
Lemma lem1075996 {A A' B B' : Type'} (x : A' -> B') (x' : A') (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (y : A -> B) : ((term226 A A' B B' x x' g' g f' f y) = (term227 A A' B B' x x' g' g f' f y)) = ((term222 A A' B B' x x' g' g f' f y) = (term237 A A' B B' x x' g' g f' f y)).
Proof. exact (MK_COMB (@lem1075989 A A' B B' x x' g' g f' f y) (@lem1075995 A A' B B' x x' g' g f' f y)). Qed.
Lemma lem1075997 {A A' B B' : Type'} (x : A' -> B') (x' : A') (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (y : A -> B) : (term222 A A' B B' x x' g' g f' f y) = (term237 A A' B B' x x' g' g f' f y).
Proof. exact (EQ_MP (@lem1075996 A A' B B' x x' g' g f' f y) (@lem1075981 A A' B B' x x' g' g f' f y)). Qed.
Lemma lem1075998 {A A' B B' : Type'} (x : A' -> B') (x' : A') (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term224 A A' B B' x x' g' g f' f) = (term238 A A' B B' x x' g' g f' f).
Proof. exact (fun_ext (fun y : A -> B => @lem1075997 A A' B B' x x' g' g f' f y)). Qed.
Lemma lem1075999 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem1076000 {A A' B B' : Type'} (x : A' -> B') (x' : A') (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term225 A A' B B' x x' g' g f' f) = (term239 A A' B B' x x' g' g f' f).
Proof. exact (MK_COMB (@lem1075999 A B) (@lem1075998 A A' B B' x x' g' g f' f)). Qed.
Lemma lem1076001 {A A' B B' : Type'} (x : A' -> B') (x' : A') (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term206 A A' B B' x x' g' g f' f) = (term239 A A' B B' x x' g' g f' f).
Proof. exact (TRANS (@lem1075977 A A' B B' x x' g' g f' f) (@lem1076000 A A' B B' x x' g' g f' f)). Qed.
Lemma lem1076002 {A A' B B' : Type'} (x : A' -> B') (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term208 A A' B B' x g' g f' f) = (term240 A A' B B' x g' g f' f).
Proof. exact (fun_ext (fun x' : A' => @lem1076001 A A' B B' x x' g' g f' f)). Qed.
Lemma lem1076003 {A' : Type'} : (@ex A') = (@ex A').
Proof. exact (eq_refl (@ex A')). Qed.
Lemma lem1076004 {A A' B B' : Type'} (x : A' -> B') (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term209 A A' B B' x g' g f' f) = (term241 A A' B B' x g' g f' f).
Proof. exact (MK_COMB (@lem1076003 A') (@lem1076002 A A' B B' x g' g f' f)). Qed.
Lemma lem1076005 {A A' B B' : Type'} (x : A' -> B') (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term191 A A' B B' x g' g f' f) = (term241 A A' B B' x g' g f' f).
Proof. exact (TRANS (@lem1075957 A A' B B' x g' g f' f) (@lem1076004 A A' B B' x g' g f' f)). Qed.
Lemma lem1076006 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term193 A A' B B' g' g f' f) = (term242 A A' B B' g' g f' f).
Proof. exact (fun_ext (fun x : A' -> B' => @lem1076005 A A' B B' x g' g f' f)). Qed.
Lemma lem1076007 {A' B' : Type'} : (@ex (A' -> B')) = (@ex (A' -> B')).
Proof. exact (eq_refl (@ex (A' -> B'))). Qed.
Lemma lem1076008 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term194 A A' B B' g' g f' f) = (term243 A A' B B' g' g f' f).
Proof. exact (MK_COMB (@lem1076007 A' B') (@lem1076006 A A' B B' g' g f' f)). Qed.
Lemma lem1076010 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term175 A A' B B' g' g f' f) = (term243 A A' B B' g' g f' f).
Proof. exact (TRANS (@lem1075931 A A' B B' g' g f' f) (@lem1076008 A A' B B' g' g f' f)). Qed.
Lemma lem1076011 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term137 A A' B B' g' g f' f) = (term243 A A' B B' g' g f' f).
Proof. exact (TRANS (@lem1075888 A A' B B' g' g f' f) (@lem1076010 A A' B B' g' g f' f)). Qed.
Lemma lem1076012 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (h1 : term137 A A' B B' g' g f' f) : term243 A A' B B' g' g f' f.
Proof. exact (EQ_MP (@lem1076011 A A' B B' g' g f' f) (@lem1075795 A A' B B' g' g f' f h1)). Qed.
Lemma lem1076013 {A A' B B' : Type'} (x : A' -> B') (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (h1 : term241 A A' B B' x g' g f' f) : term241 A A' B B' x g' g f' f.
Proof. exact (h1). Qed.
Lemma lem1076014 {A A' B B' : Type'} (x : A' -> B') (x' : A') (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (h1 : term239 A A' B B' x x' g' g f' f) : term239 A A' B B' x x' g' g f' f.
Proof. exact (h1). Qed.
Lemma lem1076015 {A A' B B' : Type'} (x : A' -> B') (x' : A') (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (y : A -> B) (h1 : term237 A A' B B' x x' g' g f' f y) : term237 A A' B B' x x' g' g f' f y.
Proof. exact (h1). Qed.
Lemma lem1076025 {B B' : Type'} (g' : B' -> B) (g : B -> B') (y : B) : ((term129 B B' g' g y) = y) = ((term129 B B' g' g y) = y).
Proof. exact (eq_refl ((term129 B B' g' g y) = y)). Qed.
Lemma lem1076026 {B B' : Type'} (g' : B' -> B) (g : B -> B') : (term130 B B' g' g) = (term130 B B' g' g).
Proof. exact (fun_ext (fun y : B => @lem1076025 B B' g' g y)). Qed.
Lemma lem1076027 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1076028 {B B' : Type'} (g' : B' -> B) (g : B -> B') : (term131 B B' g' g) = (term131 B B' g' g).
Proof. exact (MK_COMB (@lem1076027 B) (@lem1076026 B B' g' g)). Qed.
Lemma lem1076037 {B B' : Type'} (g : B -> B') (g' : B' -> B) (x : B') : ((term132 B B' g g' x) = x) = ((term132 B B' g g' x) = x).
Proof. exact (eq_refl ((term132 B B' g g' x) = x)). Qed.
Lemma lem1076038 {B B' : Type'} (g : B -> B') (g' : B' -> B) : (term133 B B' g g') = (term133 B B' g g').
Proof. exact (fun_ext (fun x : B' => @lem1076037 B B' g g' x)). Qed.
Lemma lem1076039 {B' : Type'} : (@all B') = (@all B').
Proof. exact (eq_refl (@all B')). Qed.
Lemma lem1076040 {B B' : Type'} (g : B -> B') (g' : B' -> B) : (term134 B B' g g') = (term134 B B' g g').
Proof. exact (MK_COMB (@lem1076039 B') (@lem1076038 B B' g g')). Qed.
Lemma lem1076041 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1076042 {B B' : Type'} (g : B -> B') (g' : B' -> B) : (term135 B B' g g') = (term135 B B' g g').
Proof. exact (MK_COMB (@lem1076041) (@lem1076040 B B' g g')). Qed.
Lemma lem1076043 {B B' : Type'} (g' : B' -> B) (g : B -> B') : (term7 B B' g' g) = (term7 B B' g' g).
Proof. exact (MK_COMB (@lem1076042 B B' g g') (@lem1076028 B B' g' g)). Qed.
Lemma lem1076052 {A A' : Type'} (f' : A' -> A) (f : A -> A') (y : A) : ((term129 A A' f' f y) = y) = ((term129 A A' f' f y) = y).
Proof. exact (eq_refl ((term129 A A' f' f y) = y)). Qed.
Lemma lem1076053 {A A' : Type'} (f' : A' -> A) (f : A -> A') : (term130 A A' f' f) = (term130 A A' f' f).
Proof. exact (fun_ext (fun y : A => @lem1076052 A A' f' f y)). Qed.
Lemma lem1076054 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1076055 {A A' : Type'} (f' : A' -> A) (f : A -> A') : (term131 A A' f' f) = (term131 A A' f' f).
Proof. exact (MK_COMB (@lem1076054 A) (@lem1076053 A A' f' f)). Qed.
Lemma lem1076064 {A A' : Type'} (f : A -> A') (f' : A' -> A) (x : A') : ((term132 A A' f f' x) = x) = ((term132 A A' f f' x) = x).
Proof. exact (eq_refl ((term132 A A' f f' x) = x)). Qed.
Lemma lem1076065 {A A' : Type'} (f : A -> A') (f' : A' -> A) : (term133 A A' f f') = (term133 A A' f f').
Proof. exact (fun_ext (fun x : A' => @lem1076064 A A' f f' x)). Qed.
Lemma lem1076066 {A' : Type'} : (@all A') = (@all A').
Proof. exact (eq_refl (@all A')). Qed.
Lemma lem1076067 {A A' : Type'} (f : A -> A') (f' : A' -> A) : (term134 A A' f f') = (term134 A A' f f').
Proof. exact (MK_COMB (@lem1076066 A') (@lem1076065 A A' f f')). Qed.
Lemma lem1076068 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1076069 {A A' : Type'} (f : A -> A') (f' : A' -> A) : (term135 A A' f f') = (term135 A A' f f').
Proof. exact (MK_COMB (@lem1076068) (@lem1076067 A A' f f')). Qed.
Lemma lem1076070 {A A' : Type'} (f' : A' -> A) (f : A -> A') : (term7 A A' f' f) = (term7 A A' f' f).
Proof. exact (MK_COMB (@lem1076069 A A' f f') (@lem1076055 A A' f' f)). Qed.
Lemma lem1076071 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1076072 {A A' : Type'} (f' : A' -> A) (f : A -> A') : (term9 A A' f' f) = (term9 A A' f' f).
Proof. exact (MK_COMB (@lem1076071) (@lem1076070 A A' f' f)). Qed.
Lemma lem1076073 {A A' B B' : Type'} (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') : (term11 A A' B B' f' f g' g) = (term11 A A' B B' f' f g' g).
Proof. exact (MK_COMB (@lem1076072 A A' f' f) (@lem1076043 B B' g' g)). Qed.
Lemma lem1076074 {A A' B B' : Type'} (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : term11 A A' B B' f' f g' g.
Proof. exact (EQ_MP (@lem1076073 A A' B B' f' f g' g) (@lem1075841 A A' B B' f' f g' g h1)). Qed.
Lemma lem1076116 {A A' B B' : Type'} (x : A' -> B') (x' : A') (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (y : A -> B) (x'' : A) (h1 : term234 A A' B B' x x' g' g f' f y x'') : term234 A A' B B' x x' g' g f' f y x''.
Proof. exact (h1). Qed.
Lemma lem1076117 {A A' B B' : Type'} (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : term7 B B' g' g.
Proof. exact (proj2 (@lem1076074 A A' B B' f' f g' g h1)). Qed.
Lemma lem1076118 {A A' B B' : Type'} (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : term7 A A' f' f.
Proof. exact (proj1 (@lem1076074 A A' B B' f' f g' g h1)). Qed.
Lemma lem1076119 {A A' B B' : Type'} (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : term131 B B' g' g.
Proof. exact (proj2 (@lem1076117 A A' B B' f' f g' g h1)). Qed.
Lemma lem1076120 {A A' B B' : Type'} (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : term134 B B' g g'.
Proof. exact (proj1 (@lem1076117 A A' B B' f' f g' g h1)). Qed.
Lemma lem1076121 {A A' B B' : Type'} (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : term131 A A' f' f.
Proof. exact (proj2 (@lem1076118 A A' B B' f' f g' g h1)). Qed.
Lemma lem1076122 {A A' B B' : Type'} (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : term134 A A' f f'.
Proof. exact (proj1 (@lem1076118 A A' B B' f' f g' g h1)). Qed.
Lemma lem1076126 {B B' : Type'} (g : B -> B') (g' : B' -> B) (x : B') : ((term132 B B' g g' x) = x) = ((term132 B B' g g' x) = x).
Proof. exact (eq_refl ((term132 B B' g g' x) = x)). Qed.
Lemma lem1076127 {B B' : Type'} (g : B -> B') (g' : B' -> B) : (term133 B B' g g') = (term133 B B' g g').
Proof. exact (fun_ext (fun x : B' => @lem1076126 B B' g g' x)). Qed.
Lemma lem1076128 {B' : Type'} : (@all B') = (@all B').
Proof. exact (eq_refl (@all B')). Qed.
Lemma lem1076130 {B B' : Type'} (g : B -> B') (g' : B' -> B) : (term134 B B' g g') = (term134 B B' g g').
Proof. exact (MK_COMB (@lem1076128 B') (@lem1076127 B B' g g')). Qed.
Lemma lem1076131 {A A' B B' : Type'} (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : term134 B B' g g'.
Proof. exact (EQ_MP (@lem1076130 B B' g g') (@lem1076120 A A' B B' f' f g' g h1)). Qed.
Lemma lem1076140 {A A' : Type'} (f : A -> A') (f' : A' -> A) (x : A') : ((term132 A A' f f' x) = x) = ((term132 A A' f f' x) = x).
Proof. exact (eq_refl ((term132 A A' f f' x) = x)). Qed.
Lemma lem1076141 {A A' : Type'} (f : A -> A') (f' : A' -> A) : (term133 A A' f f') = (term133 A A' f f').
Proof. exact (fun_ext (fun x : A' => @lem1076140 A A' f f' x)). Qed.
Lemma lem1076142 {A' : Type'} : (@all A') = (@all A').
Proof. exact (eq_refl (@all A')). Qed.
Lemma lem1076144 {A A' : Type'} (f : A -> A') (f' : A' -> A) : (term134 A A' f f') = (term134 A A' f f').
Proof. exact (MK_COMB (@lem1076142 A') (@lem1076141 A A' f f')). Qed.
Lemma lem1076145 {A A' B B' : Type'} (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : term134 A A' f f'.
Proof. exact (EQ_MP (@lem1076144 A A' f f') (@lem1076122 A A' B B' f' f g' g h1)). Qed.
Lemma lem1076156 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) (x : A' -> B') (x' : A') (h1 : term144 A A' B B' g g' f f' x x') : term144 A A' B B' g g' f f' x x'.
Proof. exact (h1). Qed.
Lemma lem1076165 {B B' : Type'} (g' : B' -> B) (g : B -> B') (y : B) : ((term129 B B' g' g y) = y) = ((term129 B B' g' g y) = y).
Proof. exact (eq_refl ((term129 B B' g' g y) = y)). Qed.
Lemma lem1076166 {B B' : Type'} (g' : B' -> B) (g : B -> B') : (term130 B B' g' g) = (term130 B B' g' g).
Proof. exact (fun_ext (fun y : B => @lem1076165 B B' g' g y)). Qed.
Lemma lem1076167 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1076169 {B B' : Type'} (g' : B' -> B) (g : B -> B') : (term131 B B' g' g) = (term131 B B' g' g).
Proof. exact (MK_COMB (@lem1076167 B) (@lem1076166 B B' g' g)). Qed.
Lemma lem1076170 {A A' B B' : Type'} (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : term131 B B' g' g.
Proof. exact (EQ_MP (@lem1076169 B B' g' g) (@lem1076119 A A' B B' f' f g' g h1)). Qed.
Lemma lem1076179 {A A' : Type'} (f' : A' -> A) (f : A -> A') (y : A) : ((term129 A A' f' f y) = y) = ((term129 A A' f' f y) = y).
Proof. exact (eq_refl ((term129 A A' f' f y) = y)). Qed.
Lemma lem1076180 {A A' : Type'} (f' : A' -> A) (f : A -> A') : (term130 A A' f' f) = (term130 A A' f' f).
Proof. exact (fun_ext (fun y : A => @lem1076179 A A' f' f y)). Qed.
Lemma lem1076181 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1076183 {A A' : Type'} (f' : A' -> A) (f : A -> A') : (term131 A A' f' f) = (term131 A A' f' f).
Proof. exact (MK_COMB (@lem1076181 A) (@lem1076180 A A' f' f)). Qed.
Lemma lem1076184 {A A' B B' : Type'} (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : term131 A A' f' f.
Proof. exact (EQ_MP (@lem1076183 A A' f' f) (@lem1076121 A A' B B' f' f g' g h1)). Qed.
Lemma lem1076188 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (y : A -> B) (x'' : A) (h1 : term161 A A' B B' g' g f' f y x'') : term161 A A' B B' g' g f' f y x''.
Proof. exact (h1). Qed.
Lemma lem1076189 {A A' B B' : Type'} (_17583 : B') (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : term244 B B' g g' _17583.
Proof. exact (@lem1076131 A A' B B' f' f g' g h1 _17583). Qed.
Lemma lem1076190 {B B' : Type'} (g : B -> B') (g' : B' -> B) (_17583 : B') : (term244 B B' g g' _17583) = ((term132 B B' g g' _17583) = _17583).
Proof. exact (eq_refl (term244 B B' g g' _17583)). Qed.
Lemma lem1076195 {A A' B B' : Type'} (_17585 : A') (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : term244 A A' f f' _17585.
Proof. exact (@lem1076145 A A' B B' f' f g' g h1 _17585). Qed.
Lemma lem1076196 {A A' : Type'} (f : A -> A') (f' : A' -> A) (_17585 : A') : (term244 A A' f f' _17585) = ((term132 A A' f f' _17585) = _17585).
Proof. exact (eq_refl (term244 A A' f f' _17585)). Qed.
Lemma lem1076204 {A A' B B' : Type'} (_17588 : B) (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : term245 B B' g' g _17588.
Proof. exact (@lem1076170 A A' B B' f' f g' g h1 _17588). Qed.
Lemma lem1076205 {B B' : Type'} (g' : B' -> B) (g : B -> B') (_17588 : B) : (term245 B B' g' g _17588) = ((term129 B B' g' g _17588) = _17588).
Proof. exact (eq_refl (term245 B B' g' g _17588)). Qed.
Lemma lem1076210 {A A' B B' : Type'} (_17590 : A) (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : term245 A A' f' f _17590.
Proof. exact (@lem1076184 A A' B B' f' f g' g h1 _17590). Qed.
Lemma lem1076211 {A A' : Type'} (f' : A' -> A) (f : A -> A') (_17590 : A) : (term245 A A' f' f _17590) = ((term129 A A' f' f _17590) = _17590).
Proof. exact (eq_refl (term245 A A' f' f _17590)). Qed.
Lemma lem1076222 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) (x : A' -> B') (x' : A') (h1 : term144 A A' B B' g g' f f' x x') : term144 A A' B B' g g' f f' x x'.
Proof. exact (h1). Qed.
Lemma lem1076232 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (y : A -> B) (x'' : A) (h1 : term161 A A' B B' g' g f' f y x'') : term161 A A' B B' g' g f' f y x''.
Proof. exact (h1). Qed.
Lemma lem1076233 {A' B' : Type'} (x : A' -> B') : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1076234 {A' : Type'} (_17591 : A') (_17592 : A') (h1 : _17591 = _17592) : _17591 = _17592.
Proof. exact (h1). Qed.
Lemma lem1076235 {A' B' : Type'} (x : A' -> B') (_17591 : A') (_17592 : A') (h1 : _17591 = _17592) : (x _17591) = (x _17592).
Proof. exact (MK_COMB (@lem1076233 A' B' x) (@lem1076234 A' _17591 _17592 h1)). Qed.
Lemma lem1076236 {A' B' : Type'} (_17591 : A') (x : A' -> B') (_17592 : A') : term246 A' B' _17591 x _17592.
Proof. exact (fun h0 : _17591 = _17592 => @lem1076235 A' B' x _17591 _17592 h0). Qed.
Lemma lem1076238 (a : Prop) (b : Prop) : (a -> b) = (term247 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1076239 {A' B' : Type'} (_17591 : A') (x : A' -> B') (_17592 : A') : (term246 A' B' _17591 x _17592) = (term248 A' B' _17591 x _17592).
Proof. exact (@lem1076238 (_17591 = _17592) ((x _17591) = (x _17592))). Qed.
Lemma lem1076240 {A' B' : Type'} (_17591 : A') (x : A' -> B') (_17592 : A') : term248 A' B' _17591 x _17592.
Proof. exact (EQ_MP (@lem1076239 A' B' _17591 x _17592) (@lem1076236 A' B' _17591 x _17592)). Qed.
Lemma lem1076274 {B' : Type'} (x : B') (y : B') (z : B') : term249 B' x y z.
Proof. exact (@lem21385 B' x y z). Qed.
Lemma lem1076282 {A A' B B' : Type'} (_17583 : B') (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : (term132 B B' g g' _17583) = _17583.
Proof. exact (EQ_MP (@lem1076190 B B' g g' _17583) (@lem1076189 A A' B B' _17583 f' f g' g h1)). Qed.
Lemma lem1076283 {A A' B B' : Type'} (_17583 : B') (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : (term132 B B' g g' _17583) = _17583.
Proof. exact (@lem1076282 A A' B B' _17583 f' f g' g h1). Qed.
Lemma lem1076284 {A A' B B' : Type'} (x : A' -> B') (x' : A') (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : (term47 A A' B B' g g' x f f' x') = (term250 A A' B' x f f' x').
Proof. exact (@lem1076283 A A' B B' (term250 A A' B' x f f' x') f' f g' g h1). Qed.
Lemma lem1076285 {A A' B B' : Type'} (x : A' -> B') (x' : A') (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : term251 A A' B B' g g' x f f' x'.
Proof. exact (fun h0 : term252 A A' B B' g g' x f f' x' => @lem1076284 A A' B B' x x' f' f g' g h1). Qed.
Lemma lem1076287 (p : Prop) : (term253 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1076288 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (x : A' -> B') (f : A -> A') (f' : A' -> A) (x' : A') : (term251 A A' B B' g g' x f f' x') = ((term47 A A' B B' g g' x f f' x') = (term250 A A' B' x f f' x')).
Proof. exact (@lem1076287 ((term47 A A' B B' g g' x f f' x') = (term250 A A' B' x f f' x'))). Qed.
Lemma lem1076289 {A A' B B' : Type'} (x : A' -> B') (x' : A') (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : (term47 A A' B B' g g' x f f' x') = (term250 A A' B' x f f' x').
Proof. exact (EQ_MP (@lem1076288 A A' B B' g g' x f f' x') (@lem1076285 A A' B B' x x' f' f g' g h1)). Qed.
Lemma lem1076291 {B' : Type'} (x : B') : x = x.
Proof. exact (@lem21386 B' x). Qed.
Lemma lem1076292 {B' : Type'} (x : B') : x = x.
Proof. exact (@lem1076291 B' x). Qed.
Lemma lem1076293 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (x : A' -> B') (f : A -> A') (f' : A' -> A) (x' : A') : (term47 A A' B B' g g' x f f' x') = (term47 A A' B B' g g' x f f' x').
Proof. exact (@lem1076292 B' (term47 A A' B B' g g' x f f' x')). Qed.
Lemma lem1076294 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (x : A' -> B') (f : A -> A') (f' : A' -> A) (x' : A') : term254 A A' B B' g g' x f f' x'.
Proof. exact (fun h0 : term255 A A' B B' g g' x f f' x' => @lem1076293 A A' B B' g g' x f f' x'). Qed.
Lemma lem1076296 (p : Prop) : (term253 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1076297 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (x : A' -> B') (f : A -> A') (f' : A' -> A) (x' : A') : (term254 A A' B B' g g' x f f' x') = ((term47 A A' B B' g g' x f f' x') = (term47 A A' B B' g g' x f f' x')).
Proof. exact (@lem1076296 ((term47 A A' B B' g g' x f f' x') = (term47 A A' B B' g g' x f f' x'))). Qed.
Lemma lem1076298 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (x : A' -> B') (f : A -> A') (f' : A' -> A) (x' : A') : (term47 A A' B B' g g' x f f' x') = (term47 A A' B B' g g' x f f' x').
Proof. exact (EQ_MP (@lem1076297 A A' B B' g g' x f f' x') (@lem1076294 A A' B B' g g' x f f' x')). Qed.
Lemma lem1076316 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1076317 {B' : Type'} (y : B') (x : B') (z : B') : (term256 B' x y z) = (term257 B' y x z).
Proof. exact (@lem1076316 (y = z) (term258 B' x z)). Qed.
Lemma lem1076327 {B' : Type'} (x : B') (y : B') : (term259 B' x y) = (term259 B' x y).
Proof. exact (eq_refl (term259 B' x y)). Qed.
Lemma lem1076328 {B' : Type'} (y : B') (x : B') (z : B') : (term249 B' x y z) = (term260 B' y x z).
Proof. exact (MK_COMB (@lem1076327 B' x y) (@lem1076317 B' y x z)). Qed.
Lemma lem1076332 (q : Prop) (p : Prop) (r : Prop) : (term261 p q r) = (term261 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1076333 {B' : Type'} (y : B') (x : B') (z : B') : (term260 B' y x z) = (term262 B' y x z).
Proof. exact (@lem1076332 (y = z) (term258 B' x y) (term258 B' x z)). Qed.
Lemma lem1076355 {B' : Type'} (y : B') (x : B') (z : B') : (term249 B' x y z) = (term262 B' y x z).
Proof. exact (TRANS (@lem1076328 B' y x z) (@lem1076333 B' y x z)). Qed.
Lemma lem1076356 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1076357 {B' : Type'} (y : B') (x : B') (z : B') : (term263 B' x y z) = (term264 B' y x z).
Proof. exact (MK_COMB (@lem1076356) (@lem1076355 B' y x z)). Qed.
Lemma lem1076379 {B' : Type'} (y : B') (x : B') (z : B') : (term262 B' y x z) = (term262 B' y x z).
Proof. exact (eq_refl (term262 B' y x z)). Qed.
Lemma lem1076380 {B' : Type'} (y : B') (x : B') (z : B') : ((term249 B' x y z) = (term262 B' y x z)) = ((term262 B' y x z) = (term262 B' y x z)).
Proof. exact (MK_COMB (@lem1076357 B' y x z) (@lem1076379 B' y x z)). Qed.
Lemma lem1076382 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1076383 (x : Prop) : (x = x) = True.
Proof. exact (@lem1076382 Prop x). Qed.
Lemma lem1076384 {B' : Type'} (y : B') (x : B') (z : B') : ((term262 B' y x z) = (term262 B' y x z)) = True.
Proof. exact (@lem1076383 (term262 B' y x z)). Qed.
Lemma lem1076385 {B' : Type'} (y : B') (x : B') (z : B') : ((term249 B' x y z) = (term262 B' y x z)) = True.
Proof. exact (TRANS (@lem1076380 B' y x z) (@lem1076384 B' y x z)). Qed.
Lemma lem1076386 {B' : Type'} (y : B') (x : B') (z : B') : True = ((term249 B' x y z) = (term262 B' y x z)).
Proof. exact (SYM (@lem1076385 B' y x z)). Qed.
Lemma lem1076387 {B' : Type'} (y : B') (x : B') (z : B') : (term249 B' x y z) = (term262 B' y x z).
Proof. exact (EQ_MP (@lem1076386 B' y x z) (@lem0)). Qed.
Lemma lem1076388 {B' : Type'} (y : B') (x : B') (z : B') : term262 B' y x z.
Proof. exact (EQ_MP (@lem1076387 B' y x z) (@lem1076274 B' x y z)). Qed.
Lemma lem1076390 (b : Prop) (a : Prop) : (a \/ b) = (term265 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1076391 {B' : Type'} (x : B') (y : B') (z : B') : (term262 B' y x z) = (term266 B' x y z).
Proof. exact (@lem1076390 (term267 B' y x z) (y = z)). Qed.
Lemma lem1076393 (a : Prop) (b : Prop) : (term268 a b) = (term269 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1076394 {B' : Type'} (y : B') (x : B') (z : B') : (term270 B' y x z) = (term271 B' y x z).
Proof. exact (@lem1076393 (term258 B' x y) (term258 B' x z)). Qed.
Lemma lem1076396 (a : Prop) : (term112 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1076397 {B' : Type'} (x : B') (y : B') : (term272 B' x y) = (x = y).
Proof. exact (@lem1076396 (x = y)). Qed.
Lemma lem1076398 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1076399 {B' : Type'} (x : B') (y : B') : (term273 B' x y) = (term274 B' x y).
Proof. exact (MK_COMB (@lem1076398) (@lem1076397 B' x y)). Qed.
Lemma lem1076401 (a : Prop) : (term112 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1076402 {B' : Type'} (x : B') (z : B') : (term272 B' x z) = (x = z).
Proof. exact (@lem1076401 (x = z)). Qed.
Lemma lem1076403 {B' : Type'} (y : B') (x : B') (z : B') : (term271 B' y x z) = (term275 B' y x z).
Proof. exact (MK_COMB (@lem1076399 B' x y) (@lem1076402 B' x z)). Qed.
Lemma lem1076404 {B' : Type'} (y : B') (x : B') (z : B') : (term270 B' y x z) = (term275 B' y x z).
Proof. exact (TRANS (@lem1076394 B' y x z) (@lem1076403 B' y x z)). Qed.
Lemma lem1076405 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1076406 {B' : Type'} (y : B') (x : B') (z : B') : (term276 B' y x z) = (term277 B' y x z).
Proof. exact (MK_COMB (@lem1076405) (@lem1076404 B' y x z)). Qed.
Lemma lem1076407 {B' : Type'} (y : B') (z : B') : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1076408 {B' : Type'} (x : B') (y : B') (z : B') : (term266 B' x y z) = (term278 B' x y z).
Proof. exact (MK_COMB (@lem1076406 B' y x z) (@lem1076407 B' y z)). Qed.
Lemma lem1076409 {B' : Type'} (x : B') (y : B') (z : B') : (term262 B' y x z) = (term278 B' x y z).
Proof. exact (TRANS (@lem1076391 B' x y z) (@lem1076408 B' x y z)). Qed.
Lemma lem1076411 {A A' B B' : Type'} (x : A' -> B') (x' : A') (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : term279 A A' B B' g g' x f f' x'.
Proof. exact (conj (@lem1076289 A A' B B' x x' f' f g' g h1) (@lem1076298 A A' B B' g g' x f f' x')). Qed.
Lemma lem1076413 {B' : Type'} (x : B') (y : B') (z : B') : term278 B' x y z.
Proof. exact (EQ_MP (@lem1076409 B' x y z) (@lem1076388 B' y x z)). Qed.
Lemma lem1076414 {B' : Type'} (x : B') (y : B') (z : B') : term278 B' x y z.
Proof. exact (@lem1076413 B' x y z). Qed.
Lemma lem1076415 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (x : A' -> B') (f : A -> A') (f' : A' -> A) (x' : A') : term280 A A' B B' g g' x f f' x'.
Proof. exact (@lem1076414 B' (term47 A A' B B' g g' x f f' x') (term250 A A' B' x f f' x') (term47 A A' B B' g g' x f f' x')). Qed.
Lemma lem1076418 {A A' B B' : Type'} (x : A' -> B') (x' : A') (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : (term250 A A' B' x f f' x') = (term47 A A' B B' g g' x f f' x').
Proof. exact (@lem1076415 A A' B B' g g' x f f' x' (@lem1076411 A A' B B' x x' f' f g' g h1)). Qed.
Lemma lem1076419 {A A' B B' : Type'} (x : A' -> B') (x' : A') (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : (term250 A A' B' x f f' x') = (term47 A A' B B' g g' x f f' x').
Proof. exact (@lem1076418 A A' B B' x x' f' f g' g h1). Qed.
Lemma lem1076420 {A A' B B' : Type'} (x : A' -> B') (x' : A') (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : term281 A A' B B' g g' x f f' x'.
Proof. exact (fun h0 : term282 A A' B B' g g' x f f' x' => @lem1076419 A A' B B' x x' f' f g' g h1). Qed.
Lemma lem1076422 (p : Prop) : (term253 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1076423 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (x : A' -> B') (f : A -> A') (f' : A' -> A) (x' : A') : (term281 A A' B B' g g' x f f' x') = ((term250 A A' B' x f f' x') = (term47 A A' B B' g g' x f f' x')).
Proof. exact (@lem1076422 ((term250 A A' B' x f f' x') = (term47 A A' B B' g g' x f f' x'))). Qed.
Lemma lem1076424 {A A' B B' : Type'} (x : A' -> B') (x' : A') (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : (term250 A A' B' x f f' x') = (term47 A A' B B' g g' x f f' x').
Proof. exact (EQ_MP (@lem1076423 A A' B B' g g' x f f' x') (@lem1076420 A A' B B' x x' f' f g' g h1)). Qed.
Lemma lem1076426 {A A' B B' : Type'} (_17585 : A') (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : (term132 A A' f f' _17585) = _17585.
Proof. exact (EQ_MP (@lem1076196 A A' f f' _17585) (@lem1076195 A A' B B' _17585 f' f g' g h1)). Qed.
Lemma lem1076427 {A A' B B' : Type'} (_17585 : A') (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : (term132 A A' f f' _17585) = _17585.
Proof. exact (@lem1076426 A A' B B' _17585 f' f g' g h1). Qed.
Lemma lem1076428 {A A' B B' : Type'} (x' : A') (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : (term132 A A' f f' x') = x'.
Proof. exact (@lem1076427 A A' B B' x' f' f g' g h1). Qed.
Lemma lem1076429 {A A' B B' : Type'} (x' : A') (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : term283 A A' f f' x'.
Proof. exact (fun h0 : term284 A A' f f' x' => @lem1076428 A A' B B' x' f' f g' g h1). Qed.
Lemma lem1076431 (p : Prop) : (term253 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1076432 {A A' : Type'} (f : A -> A') (f' : A' -> A) (x' : A') : (term283 A A' f f' x') = ((term132 A A' f f' x') = x').
Proof. exact (@lem1076431 ((term132 A A' f f' x') = x')). Qed.
Lemma lem1076433 {A A' B B' : Type'} (x' : A') (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : (term132 A A' f f' x') = x'.
Proof. exact (EQ_MP (@lem1076432 A A' f f' x') (@lem1076429 A A' B B' x' f' f g' g h1)). Qed.
Lemma lem1076439 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1076440 {A' B' : Type'} (x : A' -> B') (_17591 : A') (_17592 : A') : (term248 A' B' _17591 x _17592) = (term285 A' B' x _17591 _17592).
Proof. exact (@lem1076439 ((x _17591) = (x _17592)) (term258 A' _17591 _17592)). Qed.
Lemma lem1076450 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1076451 {A' B' : Type'} (x : A' -> B') (_17591 : A') (_17592 : A') : (term286 A' B' _17591 x _17592) = (term287 A' B' x _17591 _17592).
Proof. exact (MK_COMB (@lem1076450) (@lem1076440 A' B' x _17591 _17592)). Qed.
Lemma lem1076461 {A' B' : Type'} (x : A' -> B') (_17591 : A') (_17592 : A') : (term285 A' B' x _17591 _17592) = (term285 A' B' x _17591 _17592).
Proof. exact (eq_refl (term285 A' B' x _17591 _17592)). Qed.
Lemma lem1076462 {A' B' : Type'} (x : A' -> B') (_17591 : A') (_17592 : A') : ((term248 A' B' _17591 x _17592) = (term285 A' B' x _17591 _17592)) = ((term285 A' B' x _17591 _17592) = (term285 A' B' x _17591 _17592)).
Proof. exact (MK_COMB (@lem1076451 A' B' x _17591 _17592) (@lem1076461 A' B' x _17591 _17592)). Qed.
Lemma lem1076464 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1076465 (x : Prop) : (x = x) = True.
Proof. exact (@lem1076464 Prop x). Qed.
Lemma lem1076466 {A' B' : Type'} (x : A' -> B') (_17591 : A') (_17592 : A') : ((term285 A' B' x _17591 _17592) = (term285 A' B' x _17591 _17592)) = True.
Proof. exact (@lem1076465 (term285 A' B' x _17591 _17592)). Qed.
Lemma lem1076467 {A' B' : Type'} (x : A' -> B') (_17591 : A') (_17592 : A') : ((term248 A' B' _17591 x _17592) = (term285 A' B' x _17591 _17592)) = True.
Proof. exact (TRANS (@lem1076462 A' B' x _17591 _17592) (@lem1076466 A' B' x _17591 _17592)). Qed.
Lemma lem1076468 {A' B' : Type'} (x : A' -> B') (_17591 : A') (_17592 : A') : True = ((term248 A' B' _17591 x _17592) = (term285 A' B' x _17591 _17592)).
Proof. exact (SYM (@lem1076467 A' B' x _17591 _17592)). Qed.
Lemma lem1076469 {A' B' : Type'} (x : A' -> B') (_17591 : A') (_17592 : A') : (term248 A' B' _17591 x _17592) = (term285 A' B' x _17591 _17592).
Proof. exact (EQ_MP (@lem1076468 A' B' x _17591 _17592) (@lem0)). Qed.
Lemma lem1076470 {A' B' : Type'} (x : A' -> B') (_17591 : A') (_17592 : A') : term285 A' B' x _17591 _17592.
Proof. exact (EQ_MP (@lem1076469 A' B' x _17591 _17592) (@lem1076240 A' B' _17591 x _17592)). Qed.
Lemma lem1076472 (b : Prop) (a : Prop) : (a \/ b) = (term265 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1076473 {A' B' : Type'} (_17591 : A') (x : A' -> B') (_17592 : A') : (term285 A' B' x _17591 _17592) = (term288 A' B' _17591 x _17592).
Proof. exact (@lem1076472 (term258 A' _17591 _17592) ((x _17591) = (x _17592))). Qed.
Lemma lem1076475 (a : Prop) : (term112 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1076476 {A' : Type'} (_17591 : A') (_17592 : A') : (term272 A' _17591 _17592) = (_17591 = _17592).
Proof. exact (@lem1076475 (_17591 = _17592)). Qed.
Lemma lem1076477 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1076478 {A' : Type'} (_17591 : A') (_17592 : A') : (term289 A' _17591 _17592) = (term290 A' _17591 _17592).
Proof. exact (MK_COMB (@lem1076477) (@lem1076476 A' _17591 _17592)). Qed.
Lemma lem1076479 {A' B' : Type'} (_17591 : A') (x : A' -> B') (_17592 : A') : ((x _17591) = (x _17592)) = ((x _17591) = (x _17592)).
Proof. exact (eq_refl ((x _17591) = (x _17592))). Qed.
Lemma lem1076480 {A' B' : Type'} (_17591 : A') (x : A' -> B') (_17592 : A') : (term288 A' B' _17591 x _17592) = (term246 A' B' _17591 x _17592).
Proof. exact (MK_COMB (@lem1076478 A' _17591 _17592) (@lem1076479 A' B' _17591 x _17592)). Qed.
Lemma lem1076481 {A' B' : Type'} (_17591 : A') (x : A' -> B') (_17592 : A') : (term285 A' B' x _17591 _17592) = (term246 A' B' _17591 x _17592).
Proof. exact (TRANS (@lem1076473 A' B' _17591 x _17592) (@lem1076480 A' B' _17591 x _17592)). Qed.
Lemma lem1076484 {A' B' : Type'} (_17591 : A') (x : A' -> B') (_17592 : A') : term246 A' B' _17591 x _17592.
Proof. exact (EQ_MP (@lem1076481 A' B' _17591 x _17592) (@lem1076470 A' B' x _17591 _17592)). Qed.
Lemma lem1076485 {A' B' : Type'} (_17591 : A') (x : A' -> B') (_17592 : A') : term246 A' B' _17591 x _17592.
Proof. exact (@lem1076484 A' B' _17591 x _17592). Qed.
Lemma lem1076486 {A A' B' : Type'} (f : A -> A') (f' : A' -> A) (x : A' -> B') (x' : A') : term291 A A' B' f f' x x'.
Proof. exact (@lem1076485 A' B' (term132 A A' f f' x') x x'). Qed.
Lemma lem1076489 {A A' B B' : Type'} (x : A' -> B') (x' : A') (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : (term250 A A' B' x f f' x') = (x x').
Proof. exact (@lem1076486 A A' B' f f' x x' (@lem1076433 A A' B B' x' f' f g' g h1)). Qed.
Lemma lem1076490 {A A' B B' : Type'} (x : A' -> B') (x' : A') (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : (term250 A A' B' x f f' x') = (x x').
Proof. exact (@lem1076489 A A' B B' x x' f' f g' g h1). Qed.
Lemma lem1076491 {A A' B B' : Type'} (x : A' -> B') (x' : A') (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : term292 A A' B' f f' x x'.
Proof. exact (fun h0 : term293 A A' B' f f' x x' => @lem1076490 A A' B B' x x' f' f g' g h1). Qed.
Lemma lem1076493 (p : Prop) : (term253 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1076494 {A A' B' : Type'} (f : A -> A') (f' : A' -> A) (x : A' -> B') (x' : A') : (term292 A A' B' f f' x x') = ((term250 A A' B' x f f' x') = (x x')).
Proof. exact (@lem1076493 ((term250 A A' B' x f f' x') = (x x'))). Qed.
Lemma lem1076495 {A A' B B' : Type'} (x : A' -> B') (x' : A') (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : (term250 A A' B' x f f' x') = (x x').
Proof. exact (EQ_MP (@lem1076494 A A' B' f f' x x') (@lem1076491 A A' B B' x x' f' f g' g h1)). Qed.
Lemma lem1076496 {A A' B B' : Type'} (x : A' -> B') (x' : A') (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : term294 A A' B B' g g' f f' x x'.
Proof. exact (conj (@lem1076424 A A' B B' x x' f' f g' g h1) (@lem1076495 A A' B B' x x' f' f g' g h1)). Qed.
Lemma lem1076498 {B' : Type'} (x : B') (y : B') (z : B') : term278 B' x y z.
Proof. exact (EQ_MP (@lem1076409 B' x y z) (@lem1076388 B' y x z)). Qed.
Lemma lem1076499 {B' : Type'} (x : B') (y : B') (z : B') : term278 B' x y z.
Proof. exact (@lem1076498 B' x y z). Qed.
Lemma lem1076500 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) (x : A' -> B') (x' : A') : term295 A A' B B' g g' f f' x x'.
Proof. exact (@lem1076499 B' (term250 A A' B' x f f' x') (term47 A A' B B' g g' x f f' x') (x x')). Qed.
Lemma lem1076503 {A A' B B' : Type'} (x : A' -> B') (x' : A') (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : (term47 A A' B B' g g' x f f' x') = (x x').
Proof. exact (@lem1076500 A A' B B' g g' f f' x x' (@lem1076496 A A' B B' x x' f' f g' g h1)). Qed.
Lemma lem1076504 {A A' B B' : Type'} (x : A' -> B') (x' : A') (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : (term47 A A' B B' g g' x f f' x') = (x x').
Proof. exact (@lem1076503 A A' B B' x x' f' f g' g h1). Qed.
Lemma lem1076505 {A A' B B' : Type'} (x : A' -> B') (x' : A') (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : term296 A A' B B' g g' f f' x x'.
Proof. exact (fun h0 : term144 A A' B B' g g' f f' x x' => @lem1076504 A A' B B' x x' f' f g' g h1). Qed.
Lemma lem1076507 (p : Prop) : (term253 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1076508 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) (x : A' -> B') (x' : A') : (term296 A A' B B' g g' f f' x x') = ((term47 A A' B B' g g' x f f' x') = (x x')).
Proof. exact (@lem1076507 ((term47 A A' B B' g g' x f f' x') = (x x'))). Qed.
Lemma lem1076509 {A A' B B' : Type'} (x : A' -> B') (x' : A') (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : (term47 A A' B B' g g' x f f' x') = (x x').
Proof. exact (EQ_MP (@lem1076508 A A' B B' g g' f f' x x') (@lem1076505 A A' B B' x x' f' f g' g h1)). Qed.
Lemma lem1076512 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1076514 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) (x : A' -> B') (x' : A') : (term144 A A' B B' g g' f f' x x') = (term297 A A' B B' g g' f f' x x').
Proof. exact (@lem1076512 ((term47 A A' B B' g g' x f f' x') = (x x'))). Qed.
Lemma lem1076517 {A A' B B' : Type'} (g : B -> B') (g' : B' -> B) (f : A -> A') (f' : A' -> A) (x : A' -> B') (x' : A') (h1 : term144 A A' B B' g g' f f' x x') : term297 A A' B B' g g' f f' x x'.
Proof. exact (EQ_MP (@lem1076514 A A' B B' g g' f f' x x') (@lem1076222 A A' B B' g g' f f' x x' h1)). Qed.
Lemma lem1076520 {A A' B B' : Type'} (x : A' -> B') (x' : A') (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term144 A A' B B' g g' f f' x x') (h2 : term11 A A' B B' f' f g' g) : False.
Proof. exact (@lem1076517 A A' B B' g g' f f' x x' h1 (@lem1076509 A A' B B' x x' f' f g' g h2)). Qed.
Lemma lem1076521 {A A' B B' : Type'} (x : A' -> B') (x' : A') (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term144 A A' B B' g g' f f' x x') (h2 : term11 A A' B B' f' f g' g) : term298.
Proof. exact (fun h0 : ~ False => @lem1076520 A A' B B' x x' f' f g' g h1 h2). Qed.
Lemma lem1076523 (p : Prop) : (term253 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1076524 : term298 = False.
Proof. exact (@lem1076523 False). Qed.
Lemma lem1076525 {A A' B B' : Type'} (x : A' -> B') (x' : A') (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term144 A A' B B' g g' f f' x x') (h2 : term11 A A' B B' f' f g' g) : False.
Proof. exact (EQ_MP (@lem1076524) (@lem1076521 A A' B B' x x' f' f g' g h1 h2)). Qed.
Lemma lem1076526 {A B : Type'} (y : A -> B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1076527 {A : Type'} (_17601 : A) (_17602 : A) (h1 : _17601 = _17602) : _17601 = _17602.
Proof. exact (h1). Qed.
Lemma lem1076528 {A B : Type'} (y : A -> B) (_17601 : A) (_17602 : A) (h1 : _17601 = _17602) : (y _17601) = (y _17602).
Proof. exact (MK_COMB (@lem1076526 A B y) (@lem1076527 A _17601 _17602 h1)). Qed.
Lemma lem1076529 {A B : Type'} (_17601 : A) (y : A -> B) (_17602 : A) : term246 A B _17601 y _17602.
Proof. exact (fun h0 : _17601 = _17602 => @lem1076528 A B y _17601 _17602 h0). Qed.
Lemma lem1076531 (a : Prop) (b : Prop) : (a -> b) = (term247 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1076532 {A B : Type'} (_17601 : A) (y : A -> B) (_17602 : A) : (term246 A B _17601 y _17602) = (term248 A B _17601 y _17602).
Proof. exact (@lem1076531 (_17601 = _17602) ((y _17601) = (y _17602))). Qed.
Lemma lem1076533 {A B : Type'} (_17601 : A) (y : A -> B) (_17602 : A) : term248 A B _17601 y _17602.
Proof. exact (EQ_MP (@lem1076532 A B _17601 y _17602) (@lem1076529 A B _17601 y _17602)). Qed.
Lemma lem1076569 {B : Type'} (x : B) (y : B) (z : B) : term249 B x y z.
Proof. exact (@lem21385 B x y z). Qed.
Lemma lem1076575 {A A' B B' : Type'} (_17588 : B) (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : (term129 B B' g' g _17588) = _17588.
Proof. exact (EQ_MP (@lem1076205 B B' g' g _17588) (@lem1076204 A A' B B' _17588 f' f g' g h1)). Qed.
Lemma lem1076576 {A A' B B' : Type'} (_17588 : B) (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : (term129 B B' g' g _17588) = _17588.
Proof. exact (@lem1076575 A A' B B' _17588 f' f g' g h1). Qed.
Lemma lem1076577 {A A' B B' : Type'} (y : A -> B) (x'' : A) (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : (term85 A A' B B' g' g y f' f x'') = (term299 A A' B y f' f x'').
Proof. exact (@lem1076576 A A' B B' (term299 A A' B y f' f x'') f' f g' g h1). Qed.
Lemma lem1076578 {A A' B B' : Type'} (y : A -> B) (x'' : A) (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : term300 A A' B B' g' g y f' f x''.
Proof. exact (fun h0 : term301 A A' B B' g' g y f' f x'' => @lem1076577 A A' B B' y x'' f' f g' g h1). Qed.
Lemma lem1076580 (p : Prop) : (term253 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1076581 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (y : A -> B) (f' : A' -> A) (f : A -> A') (x'' : A) : (term300 A A' B B' g' g y f' f x'') = ((term85 A A' B B' g' g y f' f x'') = (term299 A A' B y f' f x'')).
Proof. exact (@lem1076580 ((term85 A A' B B' g' g y f' f x'') = (term299 A A' B y f' f x''))). Qed.
Lemma lem1076582 {A A' B B' : Type'} (y : A -> B) (x'' : A) (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : (term85 A A' B B' g' g y f' f x'') = (term299 A A' B y f' f x'').
Proof. exact (EQ_MP (@lem1076581 A A' B B' g' g y f' f x'') (@lem1076578 A A' B B' y x'' f' f g' g h1)). Qed.
Lemma lem1076584 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem1076585 {B : Type'} (x : B) : x = x.
Proof. exact (@lem1076584 B x). Qed.
Lemma lem1076586 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (y : A -> B) (f' : A' -> A) (f : A -> A') (x'' : A) : (term85 A A' B B' g' g y f' f x'') = (term85 A A' B B' g' g y f' f x'').
Proof. exact (@lem1076585 B (term85 A A' B B' g' g y f' f x'')). Qed.
Lemma lem1076587 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (y : A -> B) (f' : A' -> A) (f : A -> A') (x'' : A) : term302 A A' B B' g' g y f' f x''.
Proof. exact (fun h0 : term303 A A' B B' g' g y f' f x'' => @lem1076586 A A' B B' g' g y f' f x''). Qed.
Lemma lem1076589 (p : Prop) : (term253 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1076590 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (y : A -> B) (f' : A' -> A) (f : A -> A') (x'' : A) : (term302 A A' B B' g' g y f' f x'') = ((term85 A A' B B' g' g y f' f x'') = (term85 A A' B B' g' g y f' f x'')).
Proof. exact (@lem1076589 ((term85 A A' B B' g' g y f' f x'') = (term85 A A' B B' g' g y f' f x''))). Qed.
Lemma lem1076591 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (y : A -> B) (f' : A' -> A) (f : A -> A') (x'' : A) : (term85 A A' B B' g' g y f' f x'') = (term85 A A' B B' g' g y f' f x'').
Proof. exact (EQ_MP (@lem1076590 A A' B B' g' g y f' f x'') (@lem1076587 A A' B B' g' g y f' f x'')). Qed.
Lemma lem1076609 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1076610 {B : Type'} (y : B) (x : B) (z : B) : (term256 B x y z) = (term257 B y x z).
Proof. exact (@lem1076609 (y = z) (term258 B x z)). Qed.
Lemma lem1076620 {B : Type'} (x : B) (y : B) : (term259 B x y) = (term259 B x y).
Proof. exact (eq_refl (term259 B x y)). Qed.
Lemma lem1076621 {B : Type'} (y : B) (x : B) (z : B) : (term249 B x y z) = (term260 B y x z).
Proof. exact (MK_COMB (@lem1076620 B x y) (@lem1076610 B y x z)). Qed.
Lemma lem1076625 (q : Prop) (p : Prop) (r : Prop) : (term261 p q r) = (term261 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1076626 {B : Type'} (y : B) (x : B) (z : B) : (term260 B y x z) = (term262 B y x z).
Proof. exact (@lem1076625 (y = z) (term258 B x y) (term258 B x z)). Qed.
Lemma lem1076648 {B : Type'} (y : B) (x : B) (z : B) : (term249 B x y z) = (term262 B y x z).
Proof. exact (TRANS (@lem1076621 B y x z) (@lem1076626 B y x z)). Qed.
Lemma lem1076649 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1076650 {B : Type'} (y : B) (x : B) (z : B) : (term263 B x y z) = (term264 B y x z).
Proof. exact (MK_COMB (@lem1076649) (@lem1076648 B y x z)). Qed.
Lemma lem1076672 {B : Type'} (y : B) (x : B) (z : B) : (term262 B y x z) = (term262 B y x z).
Proof. exact (eq_refl (term262 B y x z)). Qed.
Lemma lem1076673 {B : Type'} (y : B) (x : B) (z : B) : ((term249 B x y z) = (term262 B y x z)) = ((term262 B y x z) = (term262 B y x z)).
Proof. exact (MK_COMB (@lem1076650 B y x z) (@lem1076672 B y x z)). Qed.
Lemma lem1076675 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1076676 (x : Prop) : (x = x) = True.
Proof. exact (@lem1076675 Prop x). Qed.
Lemma lem1076677 {B : Type'} (y : B) (x : B) (z : B) : ((term262 B y x z) = (term262 B y x z)) = True.
Proof. exact (@lem1076676 (term262 B y x z)). Qed.
Lemma lem1076678 {B : Type'} (y : B) (x : B) (z : B) : ((term249 B x y z) = (term262 B y x z)) = True.
Proof. exact (TRANS (@lem1076673 B y x z) (@lem1076677 B y x z)). Qed.
Lemma lem1076679 {B : Type'} (y : B) (x : B) (z : B) : True = ((term249 B x y z) = (term262 B y x z)).
Proof. exact (SYM (@lem1076678 B y x z)). Qed.
Lemma lem1076680 {B : Type'} (y : B) (x : B) (z : B) : (term249 B x y z) = (term262 B y x z).
Proof. exact (EQ_MP (@lem1076679 B y x z) (@lem0)). Qed.
Lemma lem1076681 {B : Type'} (y : B) (x : B) (z : B) : term262 B y x z.
Proof. exact (EQ_MP (@lem1076680 B y x z) (@lem1076569 B x y z)). Qed.
Lemma lem1076683 (b : Prop) (a : Prop) : (a \/ b) = (term265 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1076684 {B : Type'} (x : B) (y : B) (z : B) : (term262 B y x z) = (term266 B x y z).
Proof. exact (@lem1076683 (term267 B y x z) (y = z)). Qed.
Lemma lem1076686 (a : Prop) (b : Prop) : (term268 a b) = (term269 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1076687 {B : Type'} (y : B) (x : B) (z : B) : (term270 B y x z) = (term271 B y x z).
Proof. exact (@lem1076686 (term258 B x y) (term258 B x z)). Qed.
Lemma lem1076689 (a : Prop) : (term112 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1076690 {B : Type'} (x : B) (y : B) : (term272 B x y) = (x = y).
Proof. exact (@lem1076689 (x = y)). Qed.
Lemma lem1076691 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1076692 {B : Type'} (x : B) (y : B) : (term273 B x y) = (term274 B x y).
Proof. exact (MK_COMB (@lem1076691) (@lem1076690 B x y)). Qed.
Lemma lem1076694 (a : Prop) : (term112 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1076695 {B : Type'} (x : B) (z : B) : (term272 B x z) = (x = z).
Proof. exact (@lem1076694 (x = z)). Qed.
Lemma lem1076696 {B : Type'} (y : B) (x : B) (z : B) : (term271 B y x z) = (term275 B y x z).
Proof. exact (MK_COMB (@lem1076692 B x y) (@lem1076695 B x z)). Qed.
Lemma lem1076697 {B : Type'} (y : B) (x : B) (z : B) : (term270 B y x z) = (term275 B y x z).
Proof. exact (TRANS (@lem1076687 B y x z) (@lem1076696 B y x z)). Qed.
Lemma lem1076698 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1076699 {B : Type'} (y : B) (x : B) (z : B) : (term276 B y x z) = (term277 B y x z).
Proof. exact (MK_COMB (@lem1076698) (@lem1076697 B y x z)). Qed.
Lemma lem1076700 {B : Type'} (y : B) (z : B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1076701 {B : Type'} (x : B) (y : B) (z : B) : (term266 B x y z) = (term278 B x y z).
Proof. exact (MK_COMB (@lem1076699 B y x z) (@lem1076700 B y z)). Qed.
Lemma lem1076702 {B : Type'} (x : B) (y : B) (z : B) : (term262 B y x z) = (term278 B x y z).
Proof. exact (TRANS (@lem1076684 B x y z) (@lem1076701 B x y z)). Qed.
Lemma lem1076704 {A A' B B' : Type'} (y : A -> B) (x'' : A) (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : term304 A A' B B' g' g y f' f x''.
Proof. exact (conj (@lem1076582 A A' B B' y x'' f' f g' g h1) (@lem1076591 A A' B B' g' g y f' f x'')). Qed.
Lemma lem1076706 {B : Type'} (x : B) (y : B) (z : B) : term278 B x y z.
Proof. exact (EQ_MP (@lem1076702 B x y z) (@lem1076681 B y x z)). Qed.
Lemma lem1076707 {B : Type'} (x : B) (y : B) (z : B) : term278 B x y z.
Proof. exact (@lem1076706 B x y z). Qed.
Lemma lem1076708 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (y : A -> B) (f' : A' -> A) (f : A -> A') (x'' : A) : term305 A A' B B' g' g y f' f x''.
Proof. exact (@lem1076707 B (term85 A A' B B' g' g y f' f x'') (term299 A A' B y f' f x'') (term85 A A' B B' g' g y f' f x'')). Qed.
Lemma lem1076711 {A A' B B' : Type'} (y : A -> B) (x'' : A) (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : (term299 A A' B y f' f x'') = (term85 A A' B B' g' g y f' f x'').
Proof. exact (@lem1076708 A A' B B' g' g y f' f x'' (@lem1076704 A A' B B' y x'' f' f g' g h1)). Qed.
Lemma lem1076712 {A A' B B' : Type'} (y : A -> B) (x'' : A) (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : (term299 A A' B y f' f x'') = (term85 A A' B B' g' g y f' f x'').
Proof. exact (@lem1076711 A A' B B' y x'' f' f g' g h1). Qed.
Lemma lem1076713 {A A' B B' : Type'} (y : A -> B) (x'' : A) (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : term306 A A' B B' g' g y f' f x''.
Proof. exact (fun h0 : term307 A A' B B' g' g y f' f x'' => @lem1076712 A A' B B' y x'' f' f g' g h1). Qed.
Lemma lem1076715 (p : Prop) : (term253 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1076716 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (y : A -> B) (f' : A' -> A) (f : A -> A') (x'' : A) : (term306 A A' B B' g' g y f' f x'') = ((term299 A A' B y f' f x'') = (term85 A A' B B' g' g y f' f x'')).
Proof. exact (@lem1076715 ((term299 A A' B y f' f x'') = (term85 A A' B B' g' g y f' f x''))). Qed.
Lemma lem1076717 {A A' B B' : Type'} (y : A -> B) (x'' : A) (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : (term299 A A' B y f' f x'') = (term85 A A' B B' g' g y f' f x'').
Proof. exact (EQ_MP (@lem1076716 A A' B B' g' g y f' f x'') (@lem1076713 A A' B B' y x'' f' f g' g h1)). Qed.
Lemma lem1076719 {A A' B B' : Type'} (_17590 : A) (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : (term129 A A' f' f _17590) = _17590.
Proof. exact (EQ_MP (@lem1076211 A A' f' f _17590) (@lem1076210 A A' B B' _17590 f' f g' g h1)). Qed.
Lemma lem1076720 {A A' B B' : Type'} (_17590 : A) (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : (term129 A A' f' f _17590) = _17590.
Proof. exact (@lem1076719 A A' B B' _17590 f' f g' g h1). Qed.
Lemma lem1076721 {A A' B B' : Type'} (x'' : A) (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : (term129 A A' f' f x'') = x''.
Proof. exact (@lem1076720 A A' B B' x'' f' f g' g h1). Qed.
Lemma lem1076722 {A A' B B' : Type'} (x'' : A) (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : term308 A A' f' f x''.
Proof. exact (fun h0 : term309 A A' f' f x'' => @lem1076721 A A' B B' x'' f' f g' g h1). Qed.
Lemma lem1076724 (p : Prop) : (term253 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1076725 {A A' : Type'} (f' : A' -> A) (f : A -> A') (x'' : A) : (term308 A A' f' f x'') = ((term129 A A' f' f x'') = x'').
Proof. exact (@lem1076724 ((term129 A A' f' f x'') = x'')). Qed.
Lemma lem1076726 {A A' B B' : Type'} (x'' : A) (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : (term129 A A' f' f x'') = x''.
Proof. exact (EQ_MP (@lem1076725 A A' f' f x'') (@lem1076722 A A' B B' x'' f' f g' g h1)). Qed.
Lemma lem1076732 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1076733 {A B : Type'} (y : A -> B) (_17601 : A) (_17602 : A) : (term248 A B _17601 y _17602) = (term285 A B y _17601 _17602).
Proof. exact (@lem1076732 ((y _17601) = (y _17602)) (term258 A _17601 _17602)). Qed.
Lemma lem1076743 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1076744 {A B : Type'} (y : A -> B) (_17601 : A) (_17602 : A) : (term286 A B _17601 y _17602) = (term287 A B y _17601 _17602).
Proof. exact (MK_COMB (@lem1076743) (@lem1076733 A B y _17601 _17602)). Qed.
Lemma lem1076754 {A B : Type'} (y : A -> B) (_17601 : A) (_17602 : A) : (term285 A B y _17601 _17602) = (term285 A B y _17601 _17602).
Proof. exact (eq_refl (term285 A B y _17601 _17602)). Qed.
Lemma lem1076755 {A B : Type'} (y : A -> B) (_17601 : A) (_17602 : A) : ((term248 A B _17601 y _17602) = (term285 A B y _17601 _17602)) = ((term285 A B y _17601 _17602) = (term285 A B y _17601 _17602)).
Proof. exact (MK_COMB (@lem1076744 A B y _17601 _17602) (@lem1076754 A B y _17601 _17602)). Qed.
Lemma lem1076757 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1076758 (x : Prop) : (x = x) = True.
Proof. exact (@lem1076757 Prop x). Qed.
Lemma lem1076759 {A B : Type'} (y : A -> B) (_17601 : A) (_17602 : A) : ((term285 A B y _17601 _17602) = (term285 A B y _17601 _17602)) = True.
Proof. exact (@lem1076758 (term285 A B y _17601 _17602)). Qed.
Lemma lem1076760 {A B : Type'} (y : A -> B) (_17601 : A) (_17602 : A) : ((term248 A B _17601 y _17602) = (term285 A B y _17601 _17602)) = True.
Proof. exact (TRANS (@lem1076755 A B y _17601 _17602) (@lem1076759 A B y _17601 _17602)). Qed.
Lemma lem1076761 {A B : Type'} (y : A -> B) (_17601 : A) (_17602 : A) : True = ((term248 A B _17601 y _17602) = (term285 A B y _17601 _17602)).
Proof. exact (SYM (@lem1076760 A B y _17601 _17602)). Qed.
Lemma lem1076762 {A B : Type'} (y : A -> B) (_17601 : A) (_17602 : A) : (term248 A B _17601 y _17602) = (term285 A B y _17601 _17602).
Proof. exact (EQ_MP (@lem1076761 A B y _17601 _17602) (@lem0)). Qed.
Lemma lem1076763 {A B : Type'} (y : A -> B) (_17601 : A) (_17602 : A) : term285 A B y _17601 _17602.
Proof. exact (EQ_MP (@lem1076762 A B y _17601 _17602) (@lem1076533 A B _17601 y _17602)). Qed.
Lemma lem1076765 (b : Prop) (a : Prop) : (a \/ b) = (term265 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1076766 {A B : Type'} (_17601 : A) (y : A -> B) (_17602 : A) : (term285 A B y _17601 _17602) = (term288 A B _17601 y _17602).
Proof. exact (@lem1076765 (term258 A _17601 _17602) ((y _17601) = (y _17602))). Qed.
Lemma lem1076768 (a : Prop) : (term112 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1076769 {A : Type'} (_17601 : A) (_17602 : A) : (term272 A _17601 _17602) = (_17601 = _17602).
Proof. exact (@lem1076768 (_17601 = _17602)). Qed.
Lemma lem1076770 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1076771 {A : Type'} (_17601 : A) (_17602 : A) : (term289 A _17601 _17602) = (term290 A _17601 _17602).
Proof. exact (MK_COMB (@lem1076770) (@lem1076769 A _17601 _17602)). Qed.
Lemma lem1076772 {A B : Type'} (_17601 : A) (y : A -> B) (_17602 : A) : ((y _17601) = (y _17602)) = ((y _17601) = (y _17602)).
Proof. exact (eq_refl ((y _17601) = (y _17602))). Qed.
Lemma lem1076773 {A B : Type'} (_17601 : A) (y : A -> B) (_17602 : A) : (term288 A B _17601 y _17602) = (term246 A B _17601 y _17602).
Proof. exact (MK_COMB (@lem1076771 A _17601 _17602) (@lem1076772 A B _17601 y _17602)). Qed.
Lemma lem1076774 {A B : Type'} (_17601 : A) (y : A -> B) (_17602 : A) : (term285 A B y _17601 _17602) = (term246 A B _17601 y _17602).
Proof. exact (TRANS (@lem1076766 A B _17601 y _17602) (@lem1076773 A B _17601 y _17602)). Qed.
Lemma lem1076777 {A B : Type'} (_17601 : A) (y : A -> B) (_17602 : A) : term246 A B _17601 y _17602.
Proof. exact (EQ_MP (@lem1076774 A B _17601 y _17602) (@lem1076763 A B y _17601 _17602)). Qed.
Lemma lem1076778 {A B : Type'} (_17601 : A) (y : A -> B) (_17602 : A) : term246 A B _17601 y _17602.
Proof. exact (@lem1076777 A B _17601 y _17602). Qed.
Lemma lem1076779 {A A' B : Type'} (f' : A' -> A) (f : A -> A') (y : A -> B) (x'' : A) : term310 A A' B f' f y x''.
Proof. exact (@lem1076778 A B (term129 A A' f' f x'') y x''). Qed.
Lemma lem1076782 {A A' B B' : Type'} (y : A -> B) (x'' : A) (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : (term299 A A' B y f' f x'') = (y x'').
Proof. exact (@lem1076779 A A' B f' f y x'' (@lem1076726 A A' B B' x'' f' f g' g h1)). Qed.
Lemma lem1076783 {A A' B B' : Type'} (y : A -> B) (x'' : A) (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : (term299 A A' B y f' f x'') = (y x'').
Proof. exact (@lem1076782 A A' B B' y x'' f' f g' g h1). Qed.
Lemma lem1076784 {A A' B B' : Type'} (y : A -> B) (x'' : A) (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : term311 A A' B f' f y x''.
Proof. exact (fun h0 : term312 A A' B f' f y x'' => @lem1076783 A A' B B' y x'' f' f g' g h1). Qed.
Lemma lem1076786 (p : Prop) : (term253 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1076787 {A A' B : Type'} (f' : A' -> A) (f : A -> A') (y : A -> B) (x'' : A) : (term311 A A' B f' f y x'') = ((term299 A A' B y f' f x'') = (y x'')).
Proof. exact (@lem1076786 ((term299 A A' B y f' f x'') = (y x''))). Qed.
Lemma lem1076788 {A A' B B' : Type'} (y : A -> B) (x'' : A) (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : (term299 A A' B y f' f x'') = (y x'').
Proof. exact (EQ_MP (@lem1076787 A A' B f' f y x'') (@lem1076784 A A' B B' y x'' f' f g' g h1)). Qed.
Lemma lem1076789 {A A' B B' : Type'} (y : A -> B) (x'' : A) (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : term313 A A' B B' g' g f' f y x''.
Proof. exact (conj (@lem1076717 A A' B B' y x'' f' f g' g h1) (@lem1076788 A A' B B' y x'' f' f g' g h1)). Qed.
Lemma lem1076791 {B : Type'} (x : B) (y : B) (z : B) : term278 B x y z.
Proof. exact (EQ_MP (@lem1076702 B x y z) (@lem1076681 B y x z)). Qed.
Lemma lem1076792 {B : Type'} (x : B) (y : B) (z : B) : term278 B x y z.
Proof. exact (@lem1076791 B x y z). Qed.
Lemma lem1076793 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (y : A -> B) (x'' : A) : term314 A A' B B' g' g f' f y x''.
Proof. exact (@lem1076792 B (term299 A A' B y f' f x'') (term85 A A' B B' g' g y f' f x'') (y x'')). Qed.
Lemma lem1076796 {A A' B B' : Type'} (y : A -> B) (x'' : A) (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : (term85 A A' B B' g' g y f' f x'') = (y x'').
Proof. exact (@lem1076793 A A' B B' g' g f' f y x'' (@lem1076789 A A' B B' y x'' f' f g' g h1)). Qed.
Lemma lem1076797 {A A' B B' : Type'} (y : A -> B) (x'' : A) (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : (term85 A A' B B' g' g y f' f x'') = (y x'').
Proof. exact (@lem1076796 A A' B B' y x'' f' f g' g h1). Qed.
Lemma lem1076798 {A A' B B' : Type'} (y : A -> B) (x'' : A) (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : term315 A A' B B' g' g f' f y x''.
Proof. exact (fun h0 : term161 A A' B B' g' g f' f y x'' => @lem1076797 A A' B B' y x'' f' f g' g h1). Qed.
Lemma lem1076800 (p : Prop) : (term253 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1076801 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (y : A -> B) (x'' : A) : (term315 A A' B B' g' g f' f y x'') = ((term85 A A' B B' g' g y f' f x'') = (y x'')).
Proof. exact (@lem1076800 ((term85 A A' B B' g' g y f' f x'') = (y x''))). Qed.
Lemma lem1076802 {A A' B B' : Type'} (y : A -> B) (x'' : A) (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : (term85 A A' B B' g' g y f' f x'') = (y x'').
Proof. exact (EQ_MP (@lem1076801 A A' B B' g' g f' f y x'') (@lem1076798 A A' B B' y x'' f' f g' g h1)). Qed.
Lemma lem1076805 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1076807 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (y : A -> B) (x'' : A) : (term161 A A' B B' g' g f' f y x'') = (term316 A A' B B' g' g f' f y x'').
Proof. exact (@lem1076805 ((term85 A A' B B' g' g y f' f x'') = (y x''))). Qed.
Lemma lem1076810 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (y : A -> B) (x'' : A) (h1 : term161 A A' B B' g' g f' f y x'') : term316 A A' B B' g' g f' f y x''.
Proof. exact (EQ_MP (@lem1076807 A A' B B' g' g f' f y x'') (@lem1076232 A A' B B' g' g f' f y x'' h1)). Qed.
Lemma lem1076813 {A A' B B' : Type'} (y : A -> B) (x'' : A) (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term161 A A' B B' g' g f' f y x'') (h2 : term11 A A' B B' f' f g' g) : False.
Proof. exact (@lem1076810 A A' B B' g' g f' f y x'' h1 (@lem1076802 A A' B B' y x'' f' f g' g h2)). Qed.
Lemma lem1076814 {A A' B B' : Type'} (y : A -> B) (x'' : A) (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term161 A A' B B' g' g f' f y x'') (h2 : term11 A A' B B' f' f g' g) : term298.
Proof. exact (fun h0 : ~ False => @lem1076813 A A' B B' y x'' f' f g' g h1 h2). Qed.
Lemma lem1076816 (p : Prop) : (term253 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1076817 : term298 = False.
Proof. exact (@lem1076816 False). Qed.
Lemma lem1076818 {A A' B B' : Type'} (y : A -> B) (x'' : A) (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term161 A A' B B' g' g f' f y x'') (h2 : term11 A A' B B' f' f g' g) : False.
Proof. exact (EQ_MP (@lem1076817) (@lem1076814 A A' B B' y x'' f' f g' g h1 h2)). Qed.
Lemma lem1076819 {A A' B B' : Type'} (y : A -> B) (x'' : A) (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term161 A A' B B' g' g f' f y x'') (h2 : term11 A A' B B' f' f g' g) : (term161 A A' B B' g' g f' f y x'') = False.
Proof. exact (prop_ext (fun h3 : term161 A A' B B' g' g f' f y x'' => @lem1076818 A A' B B' y x'' f' f g' g h1 h2) (fun h3 : False => @lem1076232 A A' B B' g' g f' f y x'' h1)). Qed.
Lemma lem1076820 {A A' B B' : Type'} (y : A -> B) (x'' : A) (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term161 A A' B B' g' g f' f y x'') (h2 : term11 A A' B B' f' f g' g) : False.
Proof. exact (EQ_MP (@lem1076819 A A' B B' y x'' f' f g' g h1 h2) (@lem1076232 A A' B B' g' g f' f y x'' h1)). Qed.
Lemma lem1076821 {A A' B B' : Type'} (x : A' -> B') (x' : A') (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term144 A A' B B' g g' f f' x x') (h2 : term11 A A' B B' f' f g' g) : (term144 A A' B B' g g' f f' x x') = False.
Proof. exact (prop_ext (fun h3 : term144 A A' B B' g g' f f' x x' => @lem1076525 A A' B B' x x' f' f g' g h1 h2) (fun h3 : False => @lem1076222 A A' B B' g g' f f' x x' h1)). Qed.
Lemma lem1076822 {A A' B B' : Type'} (x : A' -> B') (x' : A') (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term144 A A' B B' g g' f f' x x') (h2 : term11 A A' B B' f' f g' g) : False.
Proof. exact (EQ_MP (@lem1076821 A A' B B' x x' f' f g' g h1 h2) (@lem1076222 A A' B B' g g' f f' x x' h1)). Qed.
Lemma lem1076823 {A A' B B' : Type'} (y : A -> B) (x'' : A) (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term161 A A' B B' g' g f' f y x'') (h2 : term11 A A' B B' f' f g' g) : (term161 A A' B B' g' g f' f y x'') = False.
Proof. exact (prop_ext (fun h3 : term161 A A' B B' g' g f' f y x'' => @lem1076820 A A' B B' y x'' f' f g' g h1 h2) (fun h3 : False => @lem1076188 A A' B B' g' g f' f y x'' h1)). Qed.
Lemma lem1076824 {A A' B B' : Type'} (y : A -> B) (x'' : A) (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term161 A A' B B' g' g f' f y x'') (h2 : term11 A A' B B' f' f g' g) : False.
Proof. exact (EQ_MP (@lem1076823 A A' B B' y x'' f' f g' g h1 h2) (@lem1076188 A A' B B' g' g f' f y x'' h1)). Qed.
Lemma lem1076825 {A A' B B' : Type'} (x : A' -> B') (x' : A') (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term144 A A' B B' g g' f f' x x') (h2 : term11 A A' B B' f' f g' g) : (term144 A A' B B' g g' f f' x x') = False.
Proof. exact (prop_ext (fun h3 : term144 A A' B B' g g' f f' x x' => @lem1076822 A A' B B' x x' f' f g' g h1 h2) (fun h3 : False => @lem1076156 A A' B B' g g' f f' x x' h1)). Qed.
Lemma lem1076826 {A A' B B' : Type'} (x : A' -> B') (x' : A') (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term144 A A' B B' g g' f f' x x') (h2 : term11 A A' B B' f' f g' g) : False.
Proof. exact (EQ_MP (@lem1076825 A A' B B' x x' f' f g' g h1 h2) (@lem1076156 A A' B B' g g' f f' x x' h1)). Qed.
Lemma lem1076827 {A A' B B' : Type'} (y : A -> B) (x'' : A) (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term161 A A' B B' g' g f' f y x'') (h2 : term11 A A' B B' f' f g' g) : (term161 A A' B B' g' g f' f y x'') = False.
Proof. exact (prop_ext (fun h3 : term161 A A' B B' g' g f' f y x'' => @lem1076824 A A' B B' y x'' f' f g' g h1 h2) (fun h3 : False => @lem1076188 A A' B B' g' g f' f y x'' h1)). Qed.
Lemma lem1076828 {A A' B B' : Type'} (y : A -> B) (x'' : A) (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term161 A A' B B' g' g f' f y x'') (h2 : term11 A A' B B' f' f g' g) : False.
Proof. exact (EQ_MP (@lem1076827 A A' B B' y x'' f' f g' g h1 h2) (@lem1076188 A A' B B' g' g f' f y x'' h1)). Qed.
Lemma lem1076829 {A A' B B' : Type'} (x : A' -> B') (x' : A') (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term144 A A' B B' g g' f f' x x') (h2 : term11 A A' B B' f' f g' g) : (term144 A A' B B' g g' f f' x x') = False.
Proof. exact (prop_ext (fun h3 : term144 A A' B B' g g' f f' x x' => @lem1076826 A A' B B' x x' f' f g' g h1 h2) (fun h3 : False => @lem1076156 A A' B B' g g' f f' x x' h1)). Qed.
Lemma lem1076830 {A A' B B' : Type'} (x : A' -> B') (x' : A') (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term144 A A' B B' g g' f f' x x') (h2 : term11 A A' B B' f' f g' g) : False.
Proof. exact (EQ_MP (@lem1076829 A A' B B' x x' f' f g' g h1 h2) (@lem1076156 A A' B B' g g' f f' x x' h1)). Qed.
Lemma lem1076831 {A A' B B' : Type'} (x : A' -> B') (x' : A') (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (y : A -> B) (x'' : A) (h1 : term11 A A' B B' f' f g' g) (h2 : term234 A A' B B' x x' g' g f' f y x'') : False.
Proof. exact (or_elim (@lem1076116 A A' B B' x x' g' g f' f y x'' h2) (fun h0 : term144 A A' B B' g g' f f' x x' => @lem1076830 A A' B B' x x' f' f g' g h0 h1) (fun h0 : term161 A A' B B' g' g f' f y x'' => @lem1076828 A A' B B' y x'' f' f g' g h0 h1)). Qed.
Lemma lem1076832 {A A' B B' : Type'} (x : A' -> B') (x' : A') (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (y : A -> B) (x'' : A) (h1 : term11 A A' B B' f' f g' g) (h2 : term234 A A' B B' x x' g' g f' f y x'') : (term234 A A' B B' x x' g' g f' f y x'') = False.
Proof. exact (prop_ext (fun h3 : term234 A A' B B' x x' g' g f' f y x'' => @lem1076831 A A' B B' x x' g' g f' f y x'' h1 h2) (fun h3 : False => @lem1076116 A A' B B' x x' g' g f' f y x'' h2)). Qed.
Lemma lem1076833 {A A' B B' : Type'} (x : A' -> B') (x' : A') (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (y : A -> B) (x'' : A) (h1 : term11 A A' B B' f' f g' g) (h2 : term234 A A' B B' x x' g' g f' f y x'') : False.
Proof. exact (EQ_MP (@lem1076832 A A' B B' x x' g' g f' f y x'' h1 h2) (@lem1076116 A A' B B' x x' g' g f' f y x'' h2)). Qed.
Lemma lem1076834 {A A' B B' : Type'} (x : A' -> B') (x' : A') (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (y : A -> B) (x'' : A) (h1 : term11 A A' B B' f' f g' g) (h2 : term234 A A' B B' x x' g' g f' f y x'') : (term11 A A' B B' f' f g' g) = False.
Proof. exact (prop_ext (fun h3 : term11 A A' B B' f' f g' g => @lem1076833 A A' B B' x x' g' g f' f y x'' h1 h2) (fun h3 : False => @lem1076074 A A' B B' f' f g' g h1)). Qed.
Lemma lem1076835 {A A' B B' : Type'} (x : A' -> B') (x' : A') (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (y : A -> B) (x'' : A) (h1 : term11 A A' B B' f' f g' g) (h2 : term234 A A' B B' x x' g' g f' f y x'') : False.
Proof. exact (EQ_MP (@lem1076834 A A' B B' x x' g' g f' f y x'' h1 h2) (@lem1076074 A A' B B' f' f g' g h1)). Qed.
Lemma lem1076836 {A A' B B' : Type'} (x : A' -> B') (x' : A') (y : A -> B) (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term237 A A' B B' x x' g' g f' f y) (h2 : term11 A A' B B' f' f g' g) : False.
Proof. exact (ex_elim (@lem1076015 A A' B B' x x' g' g f' f y h1) (fun x'' : A => fun h0 : term236 A A' B B' x x' g' g f' f y x'' => @lem1076835 A A' B B' x x' g' g f' f y x'' h2 h0)). Qed.
Lemma lem1076837 {A A' B B' : Type'} (x : A' -> B') (x' : A') (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term239 A A' B B' x x' g' g f' f) (h2 : term11 A A' B B' f' f g' g) : False.
Proof. exact (ex_elim (@lem1076014 A A' B B' x x' g' g f' f h1) (fun y : A -> B => fun h0 : term238 A A' B B' x x' g' g f' f y => @lem1076836 A A' B B' x x' y f' f g' g h0 h2)). Qed.
Lemma lem1076838 {A A' B B' : Type'} (x : A' -> B') (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term241 A A' B B' x g' g f' f) (h2 : term11 A A' B B' f' f g' g) : False.
Proof. exact (ex_elim (@lem1076013 A A' B B' x g' g f' f h1) (fun x' : A' => fun h0 : term240 A A' B B' x g' g f' f x' => @lem1076837 A A' B B' x x' f' f g' g h0 h2)). Qed.
Lemma lem1076839 {A A' B B' : Type'} (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term137 A A' B B' g' g f' f) (h2 : term11 A A' B B' f' f g' g) : False.
Proof. exact (ex_elim (@lem1076012 A A' B B' g' g f' f h1) (fun x : A' -> B' => fun h0 : term242 A A' B B' g' g f' f x => @lem1076838 A A' B B' x f' f g' g h0 h2)). Qed.
Lemma lem1076840 {A A' B B' : Type'} (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term137 A A' B B' g' g f' f) (h2 : term11 A A' B B' f' f g' g) : (term11 A A' B B' f' f g' g) = False.
Proof. exact (prop_ext (fun h3 : term11 A A' B B' f' f g' g => @lem1076839 A A' B B' f' f g' g h1 h2) (fun h3 : False => @lem1075841 A A' B B' f' f g' g h2)). Qed.
Lemma lem1076841 {A A' B B' : Type'} (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term137 A A' B B' g' g f' f) (h2 : term11 A A' B B' f' f g' g) : False.
Proof. exact (EQ_MP (@lem1076840 A A' B B' f' f g' g h1 h2) (@lem1075841 A A' B B' f' f g' g h2)). Qed.
Lemma lem1076842 {A A' B B' : Type'} (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term137 A A' B B' g' g f' f) (h2 : term11 A A' B B' f' f g' g) : (term137 A A' B B' g' g f' f) = False.
Proof. exact (prop_ext (fun h3 : term137 A A' B B' g' g f' f => @lem1076841 A A' B B' f' f g' g h1 h2) (fun h3 : False => @lem1075795 A A' B B' g' g f' f h1)). Qed.
Lemma lem1076843 {A A' B B' : Type'} (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term137 A A' B B' g' g f' f) (h2 : term11 A A' B B' f' f g' g) : False.
Proof. exact (EQ_MP (@lem1076842 A A' B B' f' f g' g h1 h2) (@lem1075795 A A' B B' g' g f' f h1)). Qed.
Lemma lem1076844 {A A' B B' : Type'} (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : term136 A A' B B' g' g f' f.
Proof. exact (fun h0 : term137 A A' B B' g' g f' f => @lem1076843 A A' B B' f' f g' g h0 h1). Qed.
Lemma lem1076845 {A A' B B' : Type'} (f' : A' -> A) (f : A -> A') (g' : B' -> B) (g : B -> B') (h1 : term11 A A' B B' f' f g' g) : term102 A A' B B' g' g f' f.
Proof. exact (EQ_MP (@lem1075794 A A' B B' g' g f' f) (@lem1076844 A A' B B' f' f g' g h1)). Qed.
Lemma lem1076846 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : term104 A A' B B' g' g f' f.
Proof. exact (fun h0 : term11 A A' B B' f' f g' g => @lem1076845 A A' B B' f' f g' g h0). Qed.
Lemma lem1076851 {A A' B B' : Type'} (g : B -> B') (f' : A' -> A) (f : A -> A') : term116 A A' B B' g f' f.
Proof. exact (fun g' : B' -> B => @lem1076846 A A' B B' g' g f' f). Qed.
Lemma lem1076856 {A A' B B' : Type'} (f' : A' -> A) (f : A -> A') : term120 A A' B B' f' f.
Proof. exact (fun g : B -> B' => @lem1076851 A A' B B' g f' f). Qed.
Lemma lem1076861 {A A' B B' : Type'} (f : A -> A') : term124 A A' B B' f.
Proof. exact (fun f' : A' -> A => @lem1076856 A A' B B' f' f). Qed.
Lemma lem1076866 {A A' B B' : Type'} : term128 A A' B B'.
Proof. exact (fun f : A -> A' => @lem1076861 A A' B B' f). Qed.
Lemma lem1076867 {A A' B B' : Type'} : term127 A A' B B'.
Proof. exact (EQ_MP (@lem1075789 A A' B B') (@lem1076866 A A' B B')). Qed.
Lemma lem1076868 {A A' B B' : Type'} (f : A -> A') : term317 A A' B B' f.
Proof. exact (@lem1076867 A A' B B' f). Qed.
Lemma lem1076869 {A A' B B' : Type'} (f : A -> A') : (term317 A A' B B' f) = (term123 A A' B B' f).
Proof. exact (eq_refl (term317 A A' B B' f)). Qed.
Lemma lem1076870 {A A' B B' : Type'} (f : A -> A') : term123 A A' B B' f.
Proof. exact (EQ_MP (@lem1076869 A A' B B' f) (@lem1076868 A A' B B' f)). Qed.
Lemma lem1076871 {A A' B B' : Type'} (f : A -> A') (f' : A' -> A) : term318 A A' B B' f f'.
Proof. exact (@lem1076870 A A' B B' f f'). Qed.
Lemma lem1076872 {A A' B B' : Type'} (f' : A' -> A) (f : A -> A') : (term318 A A' B B' f f') = (term119 A A' B B' f' f).
Proof. exact (eq_refl (term318 A A' B B' f f')). Qed.
Lemma lem1076873 {A A' B B' : Type'} (f' : A' -> A) (f : A -> A') : term119 A A' B B' f' f.
Proof. exact (EQ_MP (@lem1076872 A A' B B' f' f) (@lem1076871 A A' B B' f f')). Qed.
Lemma lem1076874 {A A' B B' : Type'} (f' : A' -> A) (f : A -> A') (g : B -> B') : term319 A A' B B' f' f g.
Proof. exact (@lem1076873 A A' B B' f' f g). Qed.
Lemma lem1076875 {A A' B B' : Type'} (g : B -> B') (f' : A' -> A) (f : A -> A') : (term319 A A' B B' f' f g) = (term115 A A' B B' g f' f).
Proof. exact (eq_refl (term319 A A' B B' f' f g)). Qed.
Lemma lem1076876 {A A' B B' : Type'} (g : B -> B') (f' : A' -> A) (f : A -> A') : term115 A A' B B' g f' f.
Proof. exact (EQ_MP (@lem1076875 A A' B B' g f' f) (@lem1076874 A A' B B' f' f g)). Qed.
Lemma lem1076877 {A A' B B' : Type'} (g : B -> B') (f' : A' -> A) (f : A -> A') (g' : B' -> B) : term320 A A' B B' g f' f g'.
Proof. exact (@lem1076876 A A' B B' g f' f g'). Qed.
Lemma lem1076878 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : (term320 A A' B B' g f' f g') = (term106 A A' B B' g' g f' f).
Proof. exact (eq_refl (term320 A A' B B' g f' f g')). Qed.
Lemma lem1076879 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : term106 A A' B B' g' g f' f.
Proof. exact (EQ_MP (@lem1076878 A A' B B' g' g f' f) (@lem1076877 A A' B B' g f' f g')). Qed.
Lemma lem1076881 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : term106 A A' B B' g' g f' f.
Proof. exact (@lem1075549 A A' B B' g' g f' f (@lem1076879 A A' B B' g' g f' f)). Qed.
Lemma lem1076882 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (h1 : term107 A A' B B' g' g f' f) : False.
Proof. exact (@lem1076881 A A' B B' g' g f' f (@lem1075533 A A' B B' g' g f' f h1)). Qed.
Lemma lem1076883 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (h1 : term107 A A' B B' g' g f' f) : (term107 A A' B B' g' g f' f) = False.
Proof. exact (prop_ext (fun h2 : term107 A A' B B' g' g f' f => @lem1076882 A A' B B' g' g f' f h1) (fun h2 : False => @lem1075533 A A' B B' g' g f' f h1)). Qed.
Lemma lem1076884 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') (h1 : term107 A A' B B' g' g f' f) : False.
Proof. exact (EQ_MP (@lem1076883 A A' B B' g' g f' f h1) (@lem1075533 A A' B B' g' g f' f h1)). Qed.
Lemma lem1076885 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : term106 A A' B B' g' g f' f.
Proof. exact (fun h0 : term107 A A' B B' g' g f' f => @lem1076884 A A' B B' g' g f' f h0). Qed.
Lemma lem1076886 {A A' B B' : Type'} (g' : B' -> B) (g : B -> B') (f' : A' -> A) (f : A -> A') : term104 A A' B B' g' g f' f.
Proof. exact (EQ_MP (@lem1075532 A A' B B' g' g f' f) (@lem1076885 A A' B B' g' g f' f)). Qed.
Lemma lem1076887 {A A' B B' : Type'} (g : B -> B') (f' : A' -> A) (g' : B' -> B) (f : A -> A') : term103 A A' B B' g f' g' f.
Proof. exact (EQ_MP (@lem1075528 A A' B B' g f' g' f) (@lem1076886 A A' B B' g' g f' f)). Qed.
