Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm358361_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import MONO_EXISTS_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18940_spec.
Require Import thm18941_spec.
Require Import thm18946_spec.
Require Import thm18947_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm19699_spec.
Require Import thm19732_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm307612_spec.
Require Import thm309905_spec.
Require Import thm339314_spec.
Require Import thm51_spec.
Require Import thm7_spec.
Require Import thm9425_spec.
Lemma lem354322 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem354323 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term1 A P Q) : term1 A P Q.
Proof. exact (h1). Qed.
Lemma lem354324 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term1 A P Q) (h2 : term0 A P Q) : term2 A P Q.
Proof. exact (@lem354322 A P Q h2 (@lem354323 A P Q h1)). Qed.
Lemma lem354325 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term1 A P Q) : term3 A P Q.
Proof. exact (fun h0 : term0 A P Q => @lem354324 A P Q h1 h0). Qed.
Lemma lem354326 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem354327 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term1 A P Q) (h2 : term0 A P Q) : term2 A P Q.
Proof. exact (@lem354325 A P Q h1 (@lem354326 A P Q h2)). Qed.
Lemma lem354328 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (fun h0 : term1 A P Q => @lem354327 A P Q h0 h1). Qed.
Lemma lem354329 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term4 A P Q.
Proof. exact (fun h0 : term0 A P Q => @lem354328 A P Q h0). Qed.
Lemma lem354331 {A : Type'} (lt2 : type1402 A) (h1 : @WF A lt2) : @WF A lt2.
Proof. exact (h1). Qed.
Lemma lem354332 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (h1 : term5 A B lt2 P) : term5 A B lt2 P.
Proof. exact (h1). Qed.
Lemma lem354333 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (h1 : term6 A B lt2 P) : term6 A B lt2 P.
Proof. exact (h1). Qed.
Lemma lem354334 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (h1 : term7 A B lt2 P) : term7 A B lt2 P.
Proof. exact (h1). Qed.
Lemma lem354335 {A B : Type'} (P : type547 A B) (h1 : term8 A B P) : term8 A B P.
Proof. exact (h1). Qed.
Lemma lem354341 {A B : Type'} (lt2 : type1402 A) : term9 A B lt2.
Proof. exact (fun h0 : @WF A lt2 => @lem339314 A B lt2 h0). Qed.
Lemma lem354342 {A B : Type'} (lt2 : type1402 A) : term9 A B lt2.
Proof. exact (@lem354341 A B lt2). Qed.
Lemma lem354343 {A B : Type'} (lt2 : type1402 A) (h1 : @WF A lt2) : term10 A B lt2.
Proof. exact (@lem354342 A B lt2 (@lem354331 A lt2 h1)). Qed.
Lemma lem354344 {A B : Type'} (lt2 : type1402 A) (h1 : term10 A B lt2) : term10 A B lt2.
Proof. exact (h1). Qed.
Lemma lem354345 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (h1 : term10 A B lt2) : term11 A B lt2 H.
Proof. exact (@lem354344 A B lt2 h1 H). Qed.
Lemma lem354346 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term11 A B lt2 H) = (term12 A B lt2 H).
Proof. exact (eq_refl (term11 A B lt2 H)). Qed.
Lemma lem354347 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (h1 : term10 A B lt2) : term12 A B lt2 H.
Proof. exact (EQ_MP (@lem354346 A B lt2 H) (@lem354345 A B H lt2 h1)). Qed.
Lemma lem354348 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) (h1 : term13 A B lt2 H) : term13 A B lt2 H.
Proof. exact (h1). Qed.
Lemma lem354349 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (h1 : term13 A B lt2 H) (h2 : term10 A B lt2) : term14 A B H.
Proof. exact (@lem354347 A B H lt2 h2 (@lem354348 A B lt2 H h1)). Qed.
Lemma lem354350 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) (h1 : term13 A B lt2 H) : term15 A B lt2 H.
Proof. exact (fun h0 : term10 A B lt2 => @lem354349 A B H lt2 h1 h0). Qed.
Lemma lem354351 {A B : Type'} (lt2 : type1402 A) (h1 : term10 A B lt2) : term10 A B lt2.
Proof. exact (h1). Qed.
Lemma lem354352 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (h1 : term13 A B lt2 H) (h2 : term10 A B lt2) : term14 A B H.
Proof. exact (@lem354350 A B lt2 H h1 (@lem354351 A B lt2 h2)). Qed.
Lemma lem354353 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (h1 : term10 A B lt2) : term12 A B lt2 H.
Proof. exact (fun h0 : term13 A B lt2 H => @lem354352 A B H lt2 h0 h1). Qed.
Lemma lem354354 {A B : Type'} (lt2 : type1402 A) (h1 : term10 A B lt2) : term10 A B lt2.
Proof. exact (fun H : type549 A B => @lem354353 A B H lt2 h1). Qed.
Lemma lem354355 {A B : Type'} (lt2 : type1402 A) : term16 A B lt2.
Proof. exact (fun h0 : term10 A B lt2 => @lem354354 A B lt2 h0). Qed.
Lemma lem354356 {A B : Type'} (lt2 : type1402 A) (h1 : @WF A lt2) : term10 A B lt2.
Proof. exact (@lem354355 A B lt2 (@lem354343 A B lt2 h1)). Qed.
Lemma lem354357 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (h1 : @WF A lt2) : term11 A B lt2 H.
Proof. exact (@lem354356 A B lt2 h1 H). Qed.
Lemma lem354358 {A B : Type'} (lt2 : type1402 A) (H : type549 A B) : (term11 A B lt2 H) = (term12 A B lt2 H).
Proof. exact (eq_refl (term11 A B lt2 H)). Qed.
Lemma lem354361 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (h1 : @WF A lt2) : term12 A B lt2 H.
Proof. exact (EQ_MP (@lem354358 A B lt2 H) (@lem354357 A B H lt2 h1)). Qed.
Lemma lem354362 {A B : Type'} (H : type549 A B) (lt2 : type1402 A) (h1 : @WF A lt2) : term12 A B lt2 H.
Proof. exact (@lem354361 A B H lt2 h1). Qed.
Lemma lem354363 {A B : Type'} (P : type547 A B) (lt2 : type1402 A) (h1 : @WF A lt2) : term17 A B lt2 P.
Proof. exact (@lem354362 A B (term18 A B P) lt2 h1). Qed.
Lemma lem354364 {A B : Type'} (P : type547 A B) (f : A -> B) : (term19 A B P f) = (term20 A B P f).
Proof. exact (eq_refl (term19 A B P f)). Qed.
Lemma lem354365 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem354366 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term21 A B P f x) = (term22 A B P f x).
Proof. exact (MK_COMB (@lem354364 A B P f) (@lem354365 A x)). Qed.
Lemma lem354367 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term22 A B P f x) = (term23 A B P f x).
Proof. exact (eq_refl (term22 A B P f x)). Qed.
Lemma lem354368 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term21 A B P f x) = (term23 A B P f x).
Proof. exact (TRANS (@lem354366 A B P f x) (@lem354367 A B P f x)). Qed.
Lemma lem354369 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem354370 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term24 A B P f x) = (term25 A B P f x).
Proof. exact (MK_COMB (@lem354369 B) (@lem354368 A B P f x)). Qed.
Lemma lem354371 {A B : Type'} (P : type547 A B) (g : A -> B) : (term19 A B P g) = (term20 A B P g).
Proof. exact (eq_refl (term19 A B P g)). Qed.
Lemma lem354372 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem354373 {A B : Type'} (P : type547 A B) (g : A -> B) (x : A) : (term21 A B P g x) = (term22 A B P g x).
Proof. exact (MK_COMB (@lem354371 A B P g) (@lem354372 A x)). Qed.
Lemma lem354374 {A B : Type'} (P : type547 A B) (g : A -> B) (x : A) : (term22 A B P g x) = (term23 A B P g x).
Proof. exact (eq_refl (term22 A B P g x)). Qed.
Lemma lem354375 {A B : Type'} (P : type547 A B) (g : A -> B) (x : A) : (term21 A B P g x) = (term23 A B P g x).
Proof. exact (TRANS (@lem354373 A B P g x) (@lem354374 A B P g x)). Qed.
Lemma lem354376 {A B : Type'} (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : ((term21 A B P f x) = (term21 A B P g x)) = ((term23 A B P f x) = (term23 A B P g x)).
Proof. exact (MK_COMB (@lem354370 A B P f x) (@lem354375 A B P g x)). Qed.
Lemma lem354377 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) : (term26 A B lt2 x f g) = (term26 A B lt2 x f g).
Proof. exact (eq_refl (term26 A B lt2 x f g)). Qed.
Lemma lem354378 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : (term27 A B lt2 f P g x) = (term28 A B lt2 f P g x).
Proof. exact (MK_COMB (@lem354377 A B lt2 x f g) (@lem354376 A B f P g x)). Qed.
Lemma lem354379 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) : (term29 A B lt2 f P g) = (term30 A B lt2 f P g).
Proof. exact (fun_ext (fun x : A => @lem354378 A B lt2 f P g x)). Qed.
Lemma lem354380 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem354381 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) : (term31 A B lt2 f P g) = (term32 A B lt2 f P g).
Proof. exact (MK_COMB (@lem354380 A) (@lem354379 A B lt2 f P g)). Qed.
Lemma lem354382 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) : (term33 A B lt2 f P) = (term34 A B lt2 f P).
Proof. exact (fun_ext (fun g : A -> B => @lem354381 A B lt2 f P g)). Qed.
Lemma lem354383 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem354384 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) : (term35 A B lt2 f P) = (term36 A B lt2 f P).
Proof. exact (MK_COMB (@lem354383 A B) (@lem354382 A B lt2 f P)). Qed.
Lemma lem354385 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : (term37 A B lt2 P) = (term38 A B lt2 P).
Proof. exact (fun_ext (fun f : A -> B => @lem354384 A B lt2 f P)). Qed.
Lemma lem354386 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem354387 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : (term39 A B lt2 P) = (term40 A B lt2 P).
Proof. exact (MK_COMB (@lem354386 A B) (@lem354385 A B lt2 P)). Qed.
Lemma lem354388 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem354389 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : (term41 A B lt2 P) = (term42 A B lt2 P).
Proof. exact (MK_COMB (@lem354388) (@lem354387 A B lt2 P)). Qed.
Lemma lem354390 {A B : Type'} (P : type547 A B) (f : A -> B) : (term19 A B P f) = (term20 A B P f).
Proof. exact (eq_refl (term19 A B P f)). Qed.
Lemma lem354391 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem354392 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term21 A B P f x) = (term22 A B P f x).
Proof. exact (MK_COMB (@lem354390 A B P f) (@lem354391 A x)). Qed.
Lemma lem354393 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term22 A B P f x) = (term23 A B P f x).
Proof. exact (eq_refl (term22 A B P f x)). Qed.
Lemma lem354394 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term21 A B P f x) = (term23 A B P f x).
Proof. exact (TRANS (@lem354392 A B P f x) (@lem354393 A B P f x)). Qed.
Lemma lem354395 {A B : Type'} (f : A -> B) (x : A) : (term43 A B f x) = (term43 A B f x).
Proof. exact (eq_refl (term43 A B f x)). Qed.
Lemma lem354396 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : ((f x) = (term21 A B P f x)) = ((f x) = (term23 A B P f x)).
Proof. exact (MK_COMB (@lem354395 A B f x) (@lem354394 A B P f x)). Qed.
Lemma lem354397 {A B : Type'} (P : type547 A B) (f : A -> B) : (term44 A B P f) = (term45 A B P f).
Proof. exact (fun_ext (fun x : A => @lem354396 A B P f x)). Qed.
Lemma lem354398 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem354399 {A B : Type'} (P : type547 A B) (f : A -> B) : (term46 A B P f) = (term47 A B P f).
Proof. exact (MK_COMB (@lem354398 A) (@lem354397 A B P f)). Qed.
Lemma lem354400 {A B : Type'} (P : type547 A B) : (term48 A B P) = (term49 A B P).
Proof. exact (fun_ext (fun f : A -> B => @lem354399 A B P f)). Qed.
Lemma lem354401 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem354402 {A B : Type'} (P : type547 A B) : (term50 A B P) = (term8 A B P).
Proof. exact (MK_COMB (@lem354401 A B) (@lem354400 A B P)). Qed.
Lemma lem354403 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : (term17 A B lt2 P) = (term51 A B lt2 P).
Proof. exact (MK_COMB (@lem354389 A B lt2 P) (@lem354402 A B P)). Qed.
Lemma lem354404 {A B : Type'} (P : type547 A B) (lt2 : type1402 A) (h1 : @WF A lt2) : term51 A B lt2 P.
Proof. exact (EQ_MP (@lem354403 A B lt2 P) (@lem354363 A B P lt2 h1)). Qed.
Lemma lem354405 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) (h1 : term52 A B lt2 x f g) : term52 A B lt2 x f g.
Proof. exact (h1). Qed.
Lemma lem354406 {B : Type'} : (@ε B) = (@ε B).
Proof. exact (eq_refl (@ε B)). Qed.
Lemma lem354450 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (h1 : term7 A B lt2 P) : term7 A B lt2 P.
Proof. exact (h1). Qed.
Lemma lem354451 {A B : Type'} (f : A -> B) (lt2 : type1402 A) (P : type547 A B) (h1 : term7 A B lt2 P) : term53 A B lt2 P f.
Proof. exact (@lem354450 A B lt2 P h1 f). Qed.
Lemma lem354452 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) : (term53 A B lt2 P f) = (term54 A B lt2 f P).
Proof. exact (eq_refl (term53 A B lt2 P f)). Qed.
Lemma lem354453 {A B : Type'} (f : A -> B) (lt2 : type1402 A) (P : type547 A B) (h1 : term7 A B lt2 P) : term54 A B lt2 f P.
Proof. exact (EQ_MP (@lem354452 A B lt2 f P) (@lem354451 A B f lt2 P h1)). Qed.
Lemma lem354454 {A B : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (P : type547 A B) (h1 : term7 A B lt2 P) : term55 A B lt2 f P g.
Proof. exact (@lem354453 A B f lt2 P h1 g). Qed.
Lemma lem354455 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) : (term55 A B lt2 f P g) = (term56 A B lt2 f P g).
Proof. exact (eq_refl (term55 A B lt2 f P g)). Qed.
Lemma lem354456 {A B : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (P : type547 A B) (h1 : term7 A B lt2 P) : term56 A B lt2 f P g.
Proof. exact (EQ_MP (@lem354455 A B lt2 f P g) (@lem354454 A B f g lt2 P h1)). Qed.
Lemma lem354457 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (lt2 : type1402 A) (P : type547 A B) (h1 : term7 A B lt2 P) : term57 A B lt2 f P g x.
Proof. exact (@lem354456 A B f g lt2 P h1 x). Qed.
Lemma lem354458 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : (term57 A B lt2 f P g x) = (term58 A B lt2 f P g x).
Proof. exact (eq_refl (term57 A B lt2 f P g x)). Qed.
Lemma lem354459 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (lt2 : type1402 A) (P : type547 A B) (h1 : term7 A B lt2 P) : term58 A B lt2 f P g x.
Proof. exact (EQ_MP (@lem354458 A B lt2 f P g x) (@lem354457 A B f g x lt2 P h1)). Qed.
Lemma lem354460 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (y : B) (lt2 : type1402 A) (P : type547 A B) (h1 : term7 A B lt2 P) : term59 A B lt2 f P g x y.
Proof. exact (@lem354459 A B f g x lt2 P h1 y). Qed.
Lemma lem354461 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) (y : B) : (term59 A B lt2 f P g x y) = (term60 A B lt2 f P g x y).
Proof. exact (eq_refl (term59 A B lt2 f P g x y)). Qed.
Lemma lem354462 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (y : B) (lt2 : type1402 A) (P : type547 A B) (h1 : term7 A B lt2 P) : term60 A B lt2 f P g x y.
Proof. exact (EQ_MP (@lem354461 A B lt2 f P g x y) (@lem354460 A B f g x y lt2 P h1)). Qed.
Lemma lem354463 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) (h1 : term52 A B lt2 x f g) : term52 A B lt2 x f g.
Proof. exact (h1). Qed.
Lemma lem354464 {A B : Type'} (y : B) (x : A) (f : A -> B) (g : A -> B) (lt2 : type1402 A) (P : type547 A B) (h1 : term52 A B lt2 x f g) (h2 : term7 A B lt2 P) : (P f x y) = (P g x y).
Proof. exact (@lem354462 A B f g x y lt2 P h2 (@lem354463 A B lt2 x f g h1)). Qed.
Lemma lem354465 {A B : Type'} (P : type547 A B) (y : B) (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) (h1 : term52 A B lt2 x f g) : term61 A B lt2 f P g x y.
Proof. exact (fun h0 : term7 A B lt2 P => @lem354464 A B y x f g lt2 P h1 h0). Qed.
Lemma lem354466 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (h1 : term7 A B lt2 P) : term7 A B lt2 P.
Proof. exact (h1). Qed.
Lemma lem354467 {A B : Type'} (y : B) (x : A) (f : A -> B) (g : A -> B) (lt2 : type1402 A) (P : type547 A B) (h1 : term52 A B lt2 x f g) (h2 : term7 A B lt2 P) : (P f x y) = (P g x y).
Proof. exact (@lem354465 A B P y lt2 x f g h1 (@lem354466 A B lt2 P h2)). Qed.
Lemma lem354468 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (y : B) (lt2 : type1402 A) (P : type547 A B) (h1 : term7 A B lt2 P) : term60 A B lt2 f P g x y.
Proof. exact (fun h0 : term52 A B lt2 x f g => @lem354467 A B y x f g lt2 P h0 h1). Qed.
Lemma lem354469 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (lt2 : type1402 A) (P : type547 A B) (h1 : term7 A B lt2 P) : term58 A B lt2 f P g x.
Proof. exact (fun y : B => @lem354468 A B f g x y lt2 P h1). Qed.
Lemma lem354470 {A B : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (P : type547 A B) (h1 : term7 A B lt2 P) : term56 A B lt2 f P g.
Proof. exact (fun x : A => @lem354469 A B f g x lt2 P h1). Qed.
Lemma lem354471 {A B : Type'} (f : A -> B) (lt2 : type1402 A) (P : type547 A B) (h1 : term7 A B lt2 P) : term54 A B lt2 f P.
Proof. exact (fun g : A -> B => @lem354470 A B f g lt2 P h1). Qed.
Lemma lem354472 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (h1 : term7 A B lt2 P) : term7 A B lt2 P.
Proof. exact (fun f : A -> B => @lem354471 A B f lt2 P h1). Qed.
Lemma lem354473 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : term62 A B lt2 P.
Proof. exact (fun h0 : term7 A B lt2 P => @lem354472 A B lt2 P h0). Qed.
Lemma lem354474 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (h1 : term7 A B lt2 P) : term7 A B lt2 P.
Proof. exact (@lem354473 A B lt2 P (@lem354334 A B lt2 P h1)). Qed.
Lemma lem354475 {A B : Type'} (f : A -> B) (lt2 : type1402 A) (P : type547 A B) (h1 : term7 A B lt2 P) : term53 A B lt2 P f.
Proof. exact (@lem354474 A B lt2 P h1 f). Qed.
Lemma lem354476 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) : (term53 A B lt2 P f) = (term54 A B lt2 f P).
Proof. exact (eq_refl (term53 A B lt2 P f)). Qed.
Lemma lem354477 {A B : Type'} (f : A -> B) (lt2 : type1402 A) (P : type547 A B) (h1 : term7 A B lt2 P) : term54 A B lt2 f P.
Proof. exact (EQ_MP (@lem354476 A B lt2 f P) (@lem354475 A B f lt2 P h1)). Qed.
Lemma lem354478 {A B : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (P : type547 A B) (h1 : term7 A B lt2 P) : term55 A B lt2 f P g.
Proof. exact (@lem354477 A B f lt2 P h1 g). Qed.
Lemma lem354479 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) : (term55 A B lt2 f P g) = (term56 A B lt2 f P g).
Proof. exact (eq_refl (term55 A B lt2 f P g)). Qed.
Lemma lem354480 {A B : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (P : type547 A B) (h1 : term7 A B lt2 P) : term56 A B lt2 f P g.
Proof. exact (EQ_MP (@lem354479 A B lt2 f P g) (@lem354478 A B f g lt2 P h1)). Qed.
Lemma lem354481 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (lt2 : type1402 A) (P : type547 A B) (h1 : term7 A B lt2 P) : term57 A B lt2 f P g x.
Proof. exact (@lem354480 A B f g lt2 P h1 x). Qed.
Lemma lem354482 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : (term57 A B lt2 f P g x) = (term58 A B lt2 f P g x).
Proof. exact (eq_refl (term57 A B lt2 f P g x)). Qed.
Lemma lem354483 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (lt2 : type1402 A) (P : type547 A B) (h1 : term7 A B lt2 P) : term58 A B lt2 f P g x.
Proof. exact (EQ_MP (@lem354482 A B lt2 f P g x) (@lem354481 A B f g x lt2 P h1)). Qed.
Lemma lem354484 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (y : B) (lt2 : type1402 A) (P : type547 A B) (h1 : term7 A B lt2 P) : term59 A B lt2 f P g x y.
Proof. exact (@lem354483 A B f g x lt2 P h1 y). Qed.
Lemma lem354485 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) (y : B) : (term59 A B lt2 f P g x y) = (term60 A B lt2 f P g x y).
Proof. exact (eq_refl (term59 A B lt2 f P g x y)). Qed.
Lemma lem354488 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (y : B) (lt2 : type1402 A) (P : type547 A B) (h1 : term7 A B lt2 P) : term60 A B lt2 f P g x y.
Proof. exact (EQ_MP (@lem354485 A B lt2 f P g x y) (@lem354484 A B f g x y lt2 P h1)). Qed.
Lemma lem354489 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (y : B) (lt2 : type1402 A) (P : type547 A B) (h1 : term7 A B lt2 P) : term60 A B lt2 f P g x y.
Proof. exact (@lem354488 A B f g x y lt2 P h1). Qed.
Lemma lem354500 {A B : Type'} (z : A) (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) (h1 : term52 A B lt2 x f g) : term63 A B lt2 x f g z.
Proof. exact (@lem354405 A B lt2 x f g h1 z). Qed.
Lemma lem354501 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) (z : A) : (term63 A B lt2 x f g z) = (term64 A B lt2 x f g z).
Proof. exact (eq_refl (term63 A B lt2 x f g z)). Qed.
Lemma lem354502 {A B : Type'} (z : A) (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) (h1 : term52 A B lt2 x f g) : term64 A B lt2 x f g z.
Proof. exact (EQ_MP (@lem354501 A B lt2 x f g z) (@lem354500 A B z lt2 x f g h1)). Qed.
Lemma lem354503 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) (z : A) : (term64 A B lt2 x f g z) = ((term64 A B lt2 x f g z) = True).
Proof. exact (@lem7 (term64 A B lt2 x f g z)). Qed.
Lemma lem354510 {A B : Type'} (z : A) (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) (h1 : term52 A B lt2 x f g) : (term64 A B lt2 x f g z) = True.
Proof. exact (EQ_MP (@lem354503 A B lt2 x f g z) (@lem354502 A B z lt2 x f g h1)). Qed.
Lemma lem354511 {A B : Type'} (z : A) (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) (h1 : term52 A B lt2 x f g) : (term64 A B lt2 x f g z) = True.
Proof. exact (@lem354510 A B z lt2 x f g h1). Qed.
Lemma lem354512 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) (h1 : term52 A B lt2 x f g) : (term65 A B lt2 x f g) = (term66 A).
Proof. exact (fun_ext (fun z : A => @lem354511 A B z lt2 x f g h1)). Qed.
Lemma lem354513 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem354514 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) (h1 : term52 A B lt2 x f g) : (term52 A B lt2 x f g) = (term67 A).
Proof. exact (MK_COMB (@lem354513 A) (@lem354512 A B lt2 x f g h1)). Qed.
Lemma lem354516 {A : Type'} (t : Prop) : (term68 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem354517 {A : Type'} (t : Prop) : (term68 A t) = t.
Proof. exact (@lem354516 A t). Qed.
Lemma lem354518 {A : Type'} : (term67 A) = True.
Proof. exact (@lem354517 A True). Qed.
Lemma lem354519 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) (h1 : term52 A B lt2 x f g) : (term52 A B lt2 x f g) = True.
Proof. exact (TRANS (@lem354514 A B lt2 x f g h1) (@lem354518 A)). Qed.
Lemma lem354520 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) (h1 : term52 A B lt2 x f g) : True = (term52 A B lt2 x f g).
Proof. exact (SYM (@lem354519 A B lt2 x f g h1)). Qed.
Lemma lem354521 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) (h1 : term52 A B lt2 x f g) : term52 A B lt2 x f g.
Proof. exact (EQ_MP (@lem354520 A B lt2 x f g h1) (@lem0)). Qed.
Lemma lem354522 {A B : Type'} (y : B) (x : A) (f : A -> B) (g : A -> B) (lt2 : type1402 A) (P : type547 A B) (h1 : term52 A B lt2 x f g) (h2 : term7 A B lt2 P) : (P f x y) = (P g x y).
Proof. exact (@lem354489 A B f g x y lt2 P h2 (@lem354521 A B lt2 x f g h1)). Qed.
Lemma lem354525 {A B : Type'} (x : A) (f : A -> B) (g : A -> B) (lt2 : type1402 A) (P : type547 A B) (h1 : term52 A B lt2 x f g) (h2 : term7 A B lt2 P) : (term69 A B P f x) = (term69 A B P g x).
Proof. exact (fun_ext (fun y : B => @lem354522 A B y x f g lt2 P h1 h2)). Qed.
Lemma lem354526 {A B : Type'} (x : A) (f : A -> B) (g : A -> B) (lt2 : type1402 A) (P : type547 A B) (h1 : term52 A B lt2 x f g) (h2 : term7 A B lt2 P) : (term23 A B P f x) = (term23 A B P g x).
Proof. exact (MK_COMB (@lem354406 B) (@lem354525 A B x f g lt2 P h1 h2)). Qed.
Lemma lem354527 {A B : Type'} (x : A) (f : A -> B) (g : A -> B) (lt2 : type1402 A) (P : type547 A B) (h1 : term52 A B lt2 x f g) (h2 : term7 A B lt2 P) : (term52 A B lt2 x f g) = ((term23 A B P f x) = (term23 A B P g x)).
Proof. exact (prop_ext (fun h3 : term52 A B lt2 x f g => @lem354526 A B x f g lt2 P h1 h2) (fun h3 : (term23 A B P f x) = (term23 A B P g x) => @lem354405 A B lt2 x f g h1)). Qed.
Lemma lem354528 {A B : Type'} (x : A) (f : A -> B) (g : A -> B) (lt2 : type1402 A) (P : type547 A B) (h1 : term52 A B lt2 x f g) (h2 : term7 A B lt2 P) : (term23 A B P f x) = (term23 A B P g x).
Proof. exact (EQ_MP (@lem354527 A B x f g lt2 P h1 h2) (@lem354405 A B lt2 x f g h1)). Qed.
Lemma lem354529 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (lt2 : type1402 A) (P : type547 A B) (h1 : term7 A B lt2 P) : term28 A B lt2 f P g x.
Proof. exact (fun h0 : term52 A B lt2 x f g => @lem354528 A B x f g lt2 P h0 h1). Qed.
Lemma lem354534 {A B : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (P : type547 A B) (h1 : term7 A B lt2 P) : term32 A B lt2 f P g.
Proof. exact (fun x : A => @lem354529 A B f g x lt2 P h1). Qed.
Lemma lem354539 {A B : Type'} (f : A -> B) (lt2 : type1402 A) (P : type547 A B) (h1 : term7 A B lt2 P) : term36 A B lt2 f P.
Proof. exact (fun g : A -> B => @lem354534 A B f g lt2 P h1). Qed.
Lemma lem354544 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (h1 : term7 A B lt2 P) : term40 A B lt2 P.
Proof. exact (fun f : A -> B => @lem354539 A B f lt2 P h1). Qed.
Lemma lem354545 {A B : Type'} (P : type547 A B) (lt2 : type1402 A) (h1 : term7 A B lt2 P) (h2 : @WF A lt2) : term8 A B P.
Proof. exact (@lem354404 A B P lt2 h2 (@lem354544 A B lt2 P h1)). Qed.
Lemma lem354547 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term0 A P Q.
Proof. exact (@lem354329 A P Q (@lem7401 A P Q)). Qed.
Lemma lem354548 {A B : Type'} (P : type572 A B) (Q : type572 A B) : term70 A B P Q.
Proof. exact (@lem354547 (A -> B) P Q). Qed.
Lemma lem354549 {A B : Type'} (P : type547 A B) : term71 A B P.
Proof. exact (@lem354548 A B (term49 A B P) (term72 A B P)). Qed.
Lemma lem354550 {A B : Type'} (P : type547 A B) (f : A -> B) : (term73 A B P f) = (term47 A B P f).
Proof. exact (eq_refl (term73 A B P f)). Qed.
Lemma lem354551 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem354552 {A B : Type'} (P : type547 A B) (f : A -> B) : (term74 A B P f) = (term75 A B P f).
Proof. exact (MK_COMB (@lem354551) (@lem354550 A B P f)). Qed.
Lemma lem354553 {A B : Type'} (P : type547 A B) (f : A -> B) : (term76 A B P f) = (term77 A B P f).
Proof. exact (eq_refl (term76 A B P f)). Qed.
Lemma lem354554 {A B : Type'} (P : type547 A B) (f : A -> B) : (term78 A B P f) = (term79 A B P f).
Proof. exact (MK_COMB (@lem354552 A B P f) (@lem354553 A B P f)). Qed.
Lemma lem354555 {A B : Type'} (P : type547 A B) : (term80 A B P) = (term81 A B P).
Proof. exact (fun_ext (fun f : A -> B => @lem354554 A B P f)). Qed.
Lemma lem354556 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem354557 {A B : Type'} (P : type547 A B) : (term82 A B P) = (term83 A B P).
Proof. exact (MK_COMB (@lem354556 A B) (@lem354555 A B P)). Qed.
Lemma lem354558 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem354559 {A B : Type'} (P : type547 A B) : (term84 A B P) = (term85 A B P).
Proof. exact (MK_COMB (@lem354558) (@lem354557 A B P)). Qed.
Lemma lem354560 {A B : Type'} (P : type547 A B) (f : A -> B) : (term73 A B P f) = (term47 A B P f).
Proof. exact (eq_refl (term73 A B P f)). Qed.
Lemma lem354561 {A B : Type'} (P : type547 A B) : (term86 A B P) = (term49 A B P).
Proof. exact (fun_ext (fun f : A -> B => @lem354560 A B P f)). Qed.
Lemma lem354562 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem354563 {A B : Type'} (P : type547 A B) : (term87 A B P) = (term8 A B P).
Proof. exact (MK_COMB (@lem354562 A B) (@lem354561 A B P)). Qed.
Lemma lem354564 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem354565 {A B : Type'} (P : type547 A B) : (term88 A B P) = (term89 A B P).
Proof. exact (MK_COMB (@lem354564) (@lem354563 A B P)). Qed.
Lemma lem354566 {A B : Type'} (P : type547 A B) (f : A -> B) : (term76 A B P f) = (term77 A B P f).
Proof. exact (eq_refl (term76 A B P f)). Qed.
Lemma lem354567 {A B : Type'} (P : type547 A B) : (term90 A B P) = (term72 A B P).
Proof. exact (fun_ext (fun f : A -> B => @lem354566 A B P f)). Qed.
Lemma lem354568 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem354569 {A B : Type'} (P : type547 A B) : (term91 A B P) = (term92 A B P).
Proof. exact (MK_COMB (@lem354568 A B) (@lem354567 A B P)). Qed.
Lemma lem354570 {A B : Type'} (P : type547 A B) : (term93 A B P) = (term94 A B P).
Proof. exact (MK_COMB (@lem354565 A B P) (@lem354569 A B P)). Qed.
Lemma lem354571 {A B : Type'} (P : type547 A B) : (term71 A B P) = (term95 A B P).
Proof. exact (MK_COMB (@lem354559 A B P) (@lem354570 A B P)). Qed.
Lemma lem354572 {A B : Type'} (P : type547 A B) : term95 A B P.
Proof. exact (EQ_MP (@lem354571 A B P) (@lem354549 A B P)). Qed.
Lemma lem354573 {A B : Type'} (P : type547 A B) (f : A -> B) (h1 : term47 A B P f) : term47 A B P f.
Proof. exact (h1). Qed.
Lemma lem354575 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (h1 : (f x) = (term23 A B P f x)) : (f x) = (term23 A B P f x).
Proof. exact (h1). Qed.
Lemma lem354576 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (h1 : (f x) = (term23 A B P f x)) : (term23 A B P f x) = (f x).
Proof. exact (SYM (@lem354575 A B P f x h1)). Qed.
Lemma lem354577 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (h1 : (term23 A B P f x) = (f x)) : (term23 A B P f x) = (f x).
Proof. exact (h1). Qed.
Lemma lem354578 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (h1 : (term23 A B P f x) = (f x)) : (f x) = (term23 A B P f x).
Proof. exact (SYM (@lem354577 A B P f x h1)). Qed.
Lemma lem354579 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : ((f x) = (term23 A B P f x)) = ((term23 A B P f x) = (f x)).
Proof. exact (prop_ext (fun h1 : (f x) = (term23 A B P f x) => @lem354576 A B P f x h1) (fun h1 : (term23 A B P f x) = (f x) => @lem354578 A B P f x h1)). Qed.
Lemma lem354580 {A B : Type'} (P : type547 A B) (f : A -> B) : (term45 A B P f) = (term96 A B P f).
Proof. exact (fun_ext (fun x : A => @lem354579 A B P f x)). Qed.
Lemma lem354581 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem354582 {A B : Type'} (P : type547 A B) (f : A -> B) : (term47 A B P f) = (term97 A B P f).
Proof. exact (MK_COMB (@lem354581 A) (@lem354580 A B P f)). Qed.
Lemma lem354583 {A B : Type'} (P : type547 A B) (f : A -> B) (h1 : term47 A B P f) : term97 A B P f.
Proof. exact (EQ_MP (@lem354582 A B P f) (@lem354573 A B P f h1)). Qed.
Lemma lem354584 {A B : Type'} (x : A) (P : type547 A B) (f : A -> B) (h1 : term47 A B P f) : term98 A B P f x.
Proof. exact (@lem354573 A B P f h1 x). Qed.
Lemma lem354585 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term98 A B P f x) = ((f x) = (term23 A B P f x)).
Proof. exact (eq_refl (term98 A B P f x)). Qed.
Lemma lem354592 {A B : Type'} (x : A) (P : type547 A B) (f : A -> B) (h1 : term47 A B P f) : (f x) = (term23 A B P f x).
Proof. exact (EQ_MP (@lem354585 A B P f x) (@lem354584 A B x P f h1)). Qed.
Lemma lem354593 {A B : Type'} (x : A) (P : type547 A B) (f : A -> B) (h1 : term47 A B P f) : (f x) = (term23 A B P f x).
Proof. exact (@lem354592 A B x P f h1). Qed.
Lemma lem354594 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (P f x) = (P f x).
Proof. exact (eq_refl (P f x)). Qed.
Lemma lem354595 {A B : Type'} (x : A) (P : type547 A B) (f : A -> B) (h1 : term47 A B P f) : (term99 A B P f x) = (term100 A B P f x).
Proof. exact (MK_COMB (@lem354594 A B P f x) (@lem354593 A B x P f h1)). Qed.
Lemma lem354596 {A B : Type'} (P : type547 A B) (f : A -> B) (h1 : term47 A B P f) : (term101 A B P f) = (term102 A B P f).
Proof. exact (fun_ext (fun x : A => @lem354595 A B x P f h1)). Qed.
Lemma lem354597 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem354598 {A B : Type'} (P : type547 A B) (f : A -> B) (h1 : term47 A B P f) : (term77 A B P f) = (term103 A B P f).
Proof. exact (MK_COMB (@lem354597 A) (@lem354596 A B P f h1)). Qed.
Lemma lem354599 {A B : Type'} (P : type547 A B) (f : A -> B) (h1 : term47 A B P f) : (term103 A B P f) = (term77 A B P f).
Proof. exact (SYM (@lem354598 A B P f h1)). Qed.
Lemma lem354600 {B : Type'} (P : B -> Prop) : (term104 B P) = (ex P).
Proof. exact (@lem9425 B P). Qed.
Lemma lem354601 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term105 A B P f x) = (term106 A B P f x).
Proof. exact (@lem354600 B (term69 A B P f x)). Qed.
Lemma lem354602 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term105 A B P f x) = (term100 A B P f x).
Proof. exact (eq_refl (term105 A B P f x)). Qed.
Lemma lem354603 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem354604 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term107 A B P f x) = (term108 A B P f x).
Proof. exact (MK_COMB (@lem354603) (@lem354602 A B P f x)). Qed.
Lemma lem354605 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term106 A B P f x) = (term106 A B P f x).
Proof. exact (eq_refl (term106 A B P f x)). Qed.
Lemma lem354606 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : ((term105 A B P f x) = (term106 A B P f x)) = ((term100 A B P f x) = (term106 A B P f x)).
Proof. exact (MK_COMB (@lem354604 A B P f x) (@lem354605 A B P f x)). Qed.
Lemma lem354607 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term100 A B P f x) = (term106 A B P f x).
Proof. exact (EQ_MP (@lem354606 A B P f x) (@lem354601 A B P f x)). Qed.
Lemma lem354608 {A B : Type'} (P : type547 A B) (f : A -> B) : (term102 A B P f) = (term109 A B P f).
Proof. exact (fun_ext (fun x : A => @lem354607 A B P f x)). Qed.
Lemma lem354609 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem354610 {A B : Type'} (P : type547 A B) (f : A -> B) : (term103 A B P f) = (term110 A B P f).
Proof. exact (MK_COMB (@lem354609 A) (@lem354608 A B P f)). Qed.
Lemma lem354611 {A B : Type'} (P : type547 A B) (f : A -> B) : (term110 A B P f) = (term103 A B P f).
Proof. exact (SYM (@lem354610 A B P f)). Qed.
Lemma lem354613 {A : Type'} (lt2 : type1402 A) : (@WF A lt2) = (term111 A lt2).
Proof. exact (EQ_MP (@lem307612 A lt2) (@lem309905 A lt2)). Qed.
Lemma lem354614 {A : Type'} (lt2 : type1402 A) : (@WF A lt2) = (term111 A lt2).
Proof. exact (@lem354613 A lt2). Qed.
Lemma lem354615 {A : Type'} (lt2 : type1402 A) (h1 : @WF A lt2) : term111 A lt2.
Proof. exact (EQ_MP (@lem354614 A lt2) (@lem354331 A lt2 h1)). Qed.
Lemma lem354616 {A : Type'} (lt2 : type1402 A) (h1 : term111 A lt2) : term111 A lt2.
Proof. exact (h1). Qed.
Lemma lem354617 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term111 A lt2) : term112 A lt2 P.
Proof. exact (@lem354616 A lt2 h1 P). Qed.
Lemma lem354618 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term112 A lt2 P) = (term113 A lt2 P).
Proof. exact (eq_refl (term112 A lt2 P)). Qed.
Lemma lem354619 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term111 A lt2) : term113 A lt2 P.
Proof. exact (EQ_MP (@lem354618 A lt2 P) (@lem354617 A P lt2 h1)). Qed.
Lemma lem354620 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term114 A lt2 P) : term114 A lt2 P.
Proof. exact (h1). Qed.
Lemma lem354621 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term114 A lt2 P) (h2 : term111 A lt2) : term115 A P.
Proof. exact (@lem354619 A P lt2 h2 (@lem354620 A lt2 P h1)). Qed.
Lemma lem354622 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) (h1 : term114 A lt2 P) : term116 A lt2 P.
Proof. exact (fun h0 : term111 A lt2 => @lem354621 A P lt2 h1 h0). Qed.
Lemma lem354623 {A : Type'} (lt2 : type1402 A) (h1 : term111 A lt2) : term111 A lt2.
Proof. exact (h1). Qed.
Lemma lem354624 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term114 A lt2 P) (h2 : term111 A lt2) : term115 A P.
Proof. exact (@lem354622 A lt2 P h1 (@lem354623 A lt2 h2)). Qed.
Lemma lem354625 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : term111 A lt2) : term113 A lt2 P.
Proof. exact (fun h0 : term114 A lt2 P => @lem354624 A P lt2 h0 h1). Qed.
Lemma lem354626 {A : Type'} (lt2 : type1402 A) (h1 : term111 A lt2) : term111 A lt2.
Proof. exact (fun P : A -> Prop => @lem354625 A P lt2 h1). Qed.
Lemma lem354627 {A : Type'} (lt2 : type1402 A) : term117 A lt2.
Proof. exact (fun h0 : term111 A lt2 => @lem354626 A lt2 h0). Qed.
Lemma lem354628 {A : Type'} (lt2 : type1402 A) (h1 : @WF A lt2) : term111 A lt2.
Proof. exact (@lem354627 A lt2 (@lem354615 A lt2 h1)). Qed.
Lemma lem354629 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : @WF A lt2) : term112 A lt2 P.
Proof. exact (@lem354628 A lt2 h1 P). Qed.
Lemma lem354630 {A : Type'} (lt2 : type1402 A) (P : A -> Prop) : (term112 A lt2 P) = (term113 A lt2 P).
Proof. exact (eq_refl (term112 A lt2 P)). Qed.
Lemma lem354633 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : @WF A lt2) : term113 A lt2 P.
Proof. exact (EQ_MP (@lem354630 A lt2 P) (@lem354629 A P lt2 h1)). Qed.
Lemma lem354634 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (h1 : @WF A lt2) : term113 A lt2 P.
Proof. exact (@lem354633 A P lt2 h1). Qed.
Lemma lem354635 {A B : Type'} (P : type547 A B) (f : A -> B) (lt2 : type1402 A) (h1 : @WF A lt2) : term118 A B lt2 P f.
Proof. exact (@lem354634 A (term109 A B P f) lt2 h1). Qed.
Lemma lem354636 {A B : Type'} (P : type547 A B) (f : A -> B) (y : A) : (term119 A B P f y) = (term106 A B P f y).
Proof. exact (eq_refl (term119 A B P f y)). Qed.
Lemma lem354637 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (term120 A lt2 y x) = (term120 A lt2 y x).
Proof. exact (eq_refl (term120 A lt2 y x)). Qed.
Lemma lem354638 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (y : A) : (term121 A B lt2 x P f y) = (term122 A B lt2 x P f y).
Proof. exact (MK_COMB (@lem354637 A lt2 y x) (@lem354636 A B P f y)). Qed.
Lemma lem354639 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) : (term123 A B lt2 x P f) = (term124 A B lt2 x P f).
Proof. exact (fun_ext (fun y : A => @lem354638 A B lt2 x P f y)). Qed.
Lemma lem354640 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem354641 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) : (term125 A B lt2 x P f) = (term126 A B lt2 x P f).
Proof. exact (MK_COMB (@lem354640 A) (@lem354639 A B lt2 x P f)). Qed.
Lemma lem354642 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem354643 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) : (term127 A B lt2 x P f) = (term128 A B lt2 x P f).
Proof. exact (MK_COMB (@lem354642) (@lem354641 A B lt2 x P f)). Qed.
Lemma lem354644 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term119 A B P f x) = (term106 A B P f x).
Proof. exact (eq_refl (term119 A B P f x)). Qed.
Lemma lem354645 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (x : A) : (term129 A B lt2 P f x) = (term130 A B lt2 P f x).
Proof. exact (MK_COMB (@lem354643 A B lt2 x P f) (@lem354644 A B P f x)). Qed.
Lemma lem354646 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term131 A B lt2 P f) = (term132 A B lt2 P f).
Proof. exact (fun_ext (fun x : A => @lem354645 A B lt2 P f x)). Qed.
Lemma lem354647 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem354648 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term133 A B lt2 P f) = (term134 A B lt2 P f).
Proof. exact (MK_COMB (@lem354647 A) (@lem354646 A B lt2 P f)). Qed.
Lemma lem354649 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem354650 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term135 A B lt2 P f) = (term136 A B lt2 P f).
Proof. exact (MK_COMB (@lem354649) (@lem354648 A B lt2 P f)). Qed.
Lemma lem354651 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term119 A B P f x) = (term106 A B P f x).
Proof. exact (eq_refl (term119 A B P f x)). Qed.
Lemma lem354652 {A B : Type'} (P : type547 A B) (f : A -> B) : (term137 A B P f) = (term109 A B P f).
Proof. exact (fun_ext (fun x : A => @lem354651 A B P f x)). Qed.
Lemma lem354653 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem354654 {A B : Type'} (P : type547 A B) (f : A -> B) : (term138 A B P f) = (term110 A B P f).
Proof. exact (MK_COMB (@lem354653 A) (@lem354652 A B P f)). Qed.
Lemma lem354655 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term118 A B lt2 P f) = (term139 A B lt2 P f).
Proof. exact (MK_COMB (@lem354650 A B lt2 P f) (@lem354654 A B P f)). Qed.
Lemma lem354656 {A B : Type'} (P : type547 A B) (f : A -> B) (lt2 : type1402 A) (h1 : @WF A lt2) : term139 A B lt2 P f.
Proof. exact (EQ_MP (@lem354655 A B lt2 P f) (@lem354635 A B P f lt2 h1)). Qed.
Lemma lem354658 (p : Prop) : p = (term140 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem354659 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term134 A B lt2 P f) = (term141 A B lt2 P f).
Proof. exact (@lem354658 (term134 A B lt2 P f)). Qed.
Lemma lem354660 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term141 A B lt2 P f) = (term134 A B lt2 P f).
Proof. exact (SYM (@lem354659 A B lt2 P f)). Qed.
Lemma lem354661 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (h1 : term142 A B lt2 P f) : term142 A B lt2 P f.
Proof. exact (h1). Qed.
Lemma lem355008 {B : Type'} (P : B -> Prop) : term143 B P.
Proof. exact (@lem19732 B P). Qed.
Lemma lem355009 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : term144 A B P f x.
Proof. exact (@lem355008 B (term69 A B P f x)). Qed.
Lemma lem355010 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term105 A B P f x) = (term100 A B P f x).
Proof. exact (eq_refl (term105 A B P f x)). Qed.
Lemma lem355011 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (x' : B) : (term145 A B P f x x') = (P f x x').
Proof. exact (eq_refl (term145 A B P f x x')). Qed.
Lemma lem355012 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem355013 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (x' : B) : (term146 A B P f x x') = (term147 A B P f x x').
Proof. exact (MK_COMB (@lem355012) (@lem355011 A B P f x x')). Qed.
Lemma lem355014 {A B : Type'} (x : B) (P : type547 A B) (f : A -> B) (x' : A) : (term148 A B x P f x') = (term149 A B x P f x').
Proof. exact (MK_COMB (@lem355013 A B P f x' x) (@lem355010 A B P f x')). Qed.
Lemma lem355015 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term150 A B P f x) = (term151 A B P f x).
Proof. exact (fun_ext (fun x' : B => @lem355014 A B x' P f x)). Qed.
Lemma lem355016 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem355017 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term144 A B P f x) = (term152 A B P f x).
Proof. exact (MK_COMB (@lem355016 B) (@lem355015 A B P f x)). Qed.
Lemma lem355018 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : term152 A B P f x.
Proof. exact (EQ_MP (@lem355017 A B P f x) (@lem355009 A B P f x)). Qed.
Lemma lem355019 {A B : Type'} (P : type547 A B) (f : A -> B) : term153 A B P f.
Proof. exact (fun x : A => @lem355018 A B P f x). Qed.
Lemma lem355020 {A B : Type'} (P : type547 A B) : term154 A B P.
Proof. exact (fun f : A -> B => @lem355019 A B P f). Qed.
Lemma lem355021 {A B : Type'} : term155 A B.
Proof. exact (fun P : type547 A B => @lem355020 A B P). Qed.
Lemma lem355022 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (h1 : term156 A B lt2 P f) : term156 A B lt2 P f.
Proof. exact (h1). Qed.
Lemma lem355023 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (h1 : term156 A B lt2 P f) : term157 A B lt2 P f.
Proof. exact (@lem355022 A B lt2 P f h1 (@lem355021 A B)). Qed.
Lemma lem355024 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : term158 A B lt2 P f.
Proof. exact (fun h0 : term156 A B lt2 P f => @lem355023 A B lt2 P f h0). Qed.
Lemma lem355025 {A B : Type'} (_7729 : type103 A B) (h1 : _7729 = (term159 A B)) : _7729 = (term159 A B).
Proof. exact (h1). Qed.
Lemma lem355026 {A B : Type'} (P : type547 A B) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem355027 {A B : Type'} (P : type547 A B) (_7729 : type103 A B) (h1 : _7729 = (term159 A B)) : (_7729 P) = (term160 A B P).
Proof. exact (MK_COMB (@lem355025 A B _7729 h1) (@lem355026 A B P)). Qed.
Lemma lem355028 {A B : Type'} (P : type547 A B) : (term160 A B P) = (term18 A B P).
Proof. exact (eq_refl (term160 A B P)). Qed.
Lemma lem355029 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) : (term161 A B _7729 P) = (term161 A B _7729 P).
Proof. exact (eq_refl (term161 A B _7729 P)). Qed.
Lemma lem355030 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) : ((_7729 P) = (term160 A B P)) = ((_7729 P) = (term18 A B P)).
Proof. exact (MK_COMB (@lem355029 A B _7729 P) (@lem355028 A B P)). Qed.
Lemma lem355031 {A B : Type'} (P : type547 A B) (_7729 : type103 A B) (h1 : _7729 = (term159 A B)) : (_7729 P) = (term18 A B P).
Proof. exact (EQ_MP (@lem355030 A B _7729 P) (@lem355027 A B P _7729 h1)). Qed.
Lemma lem355032 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem355033 {A B : Type'} (P : type547 A B) (f : A -> B) (_7729 : type103 A B) (h1 : _7729 = (term159 A B)) : (_7729 P f) = (term19 A B P f).
Proof. exact (MK_COMB (@lem355031 A B P _7729 h1) (@lem355032 A B f)). Qed.
Lemma lem355034 {A B : Type'} (P : type547 A B) (f : A -> B) : (term19 A B P f) = (term20 A B P f).
Proof. exact (eq_refl (term19 A B P f)). Qed.
Lemma lem355035 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) : (term162 A B _7729 P f) = (term162 A B _7729 P f).
Proof. exact (eq_refl (term162 A B _7729 P f)). Qed.
Lemma lem355036 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) : ((_7729 P f) = (term19 A B P f)) = ((_7729 P f) = (term20 A B P f)).
Proof. exact (MK_COMB (@lem355035 A B _7729 P f) (@lem355034 A B P f)). Qed.
Lemma lem355037 {A B : Type'} (P : type547 A B) (f : A -> B) (_7729 : type103 A B) (h1 : _7729 = (term159 A B)) : (_7729 P f) = (term20 A B P f).
Proof. exact (EQ_MP (@lem355036 A B _7729 P f) (@lem355033 A B P f _7729 h1)). Qed.
Lemma lem355038 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem355039 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (_7729 : type103 A B) (h1 : _7729 = (term159 A B)) : (_7729 P f x) = (term22 A B P f x).
Proof. exact (MK_COMB (@lem355037 A B P f _7729 h1) (@lem355038 A x)). Qed.
Lemma lem355040 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term22 A B P f x) = (term23 A B P f x).
Proof. exact (eq_refl (term22 A B P f x)). Qed.
Lemma lem355041 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) : (term163 A B _7729 P f x) = (term163 A B _7729 P f x).
Proof. exact (eq_refl (term163 A B _7729 P f x)). Qed.
Lemma lem355042 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) : ((_7729 P f x) = (term22 A B P f x)) = ((_7729 P f x) = (term23 A B P f x)).
Proof. exact (MK_COMB (@lem355041 A B _7729 P f x) (@lem355040 A B P f x)). Qed.
Lemma lem355043 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (_7729 : type103 A B) (h1 : _7729 = (term159 A B)) : (_7729 P f x) = (term23 A B P f x).
Proof. exact (EQ_MP (@lem355042 A B _7729 P f x) (@lem355039 A B P f x _7729 h1)). Qed.
Lemma lem355044 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (_7729 : type103 A B) (h1 : _7729 = (term159 A B)) : (term23 A B P f x) = (_7729 P f x).
Proof. exact (SYM (@lem355043 A B P f x _7729 h1)). Qed.
Lemma lem355045 {A B : Type'} (P : type547 A B) (f : A -> B) (_7729 : type103 A B) (h1 : _7729 = (term159 A B)) : term164 A B _7729 P f.
Proof. exact (fun x : A => @lem355044 A B P f x _7729 h1). Qed.
Lemma lem355046 {A B : Type'} (P : type547 A B) (_7729 : type103 A B) (h1 : _7729 = (term159 A B)) : term165 A B _7729 P.
Proof. exact (fun f : A -> B => @lem355045 A B P f _7729 h1). Qed.
Lemma lem355047 {A B : Type'} (_7729 : type103 A B) (h1 : _7729 = (term159 A B)) : term166 A B _7729.
Proof. exact (fun P : type547 A B => @lem355046 A B P _7729 h1). Qed.
Lemma lem355048 {A B : Type'} (P : type547 A B) (_7729 : type103 A B) (h1 : _7729 = (term159 A B)) : term167 A B _7729 P.
Proof. exact (@lem355047 A B _7729 h1 P). Qed.
Lemma lem355049 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) : (term167 A B _7729 P) = (term165 A B _7729 P).
Proof. exact (eq_refl (term167 A B _7729 P)). Qed.
Lemma lem355050 {A B : Type'} (P : type547 A B) (_7729 : type103 A B) (h1 : _7729 = (term159 A B)) : term165 A B _7729 P.
Proof. exact (EQ_MP (@lem355049 A B _7729 P) (@lem355048 A B P _7729 h1)). Qed.
Lemma lem355051 {A B : Type'} (P : type547 A B) (f : A -> B) (_7729 : type103 A B) (h1 : _7729 = (term159 A B)) : term168 A B _7729 P f.
Proof. exact (@lem355050 A B P _7729 h1 f). Qed.
Lemma lem355052 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) : (term168 A B _7729 P f) = (term164 A B _7729 P f).
Proof. exact (eq_refl (term168 A B _7729 P f)). Qed.
Lemma lem355053 {A B : Type'} (P : type547 A B) (f : A -> B) (_7729 : type103 A B) (h1 : _7729 = (term159 A B)) : term164 A B _7729 P f.
Proof. exact (EQ_MP (@lem355052 A B _7729 P f) (@lem355051 A B P f _7729 h1)). Qed.
Lemma lem355054 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (_7729 : type103 A B) (h1 : _7729 = (term159 A B)) : term169 A B _7729 P f x.
Proof. exact (@lem355053 A B P f _7729 h1 x). Qed.
Lemma lem355055 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) : (term169 A B _7729 P f x) = ((term23 A B P f x) = (_7729 P f x)).
Proof. exact (eq_refl (term169 A B _7729 P f x)). Qed.
Lemma lem355058 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (_7729 : type103 A B) (h1 : _7729 = (term159 A B)) : (term23 A B P f x) = (_7729 P f x).
Proof. exact (EQ_MP (@lem355055 A B _7729 P f x) (@lem355054 A B P f x _7729 h1)). Qed.
Lemma lem355059 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (_7729 : type103 A B) (h1 : _7729 = (term159 A B)) : (term23 A B P f x) = (_7729 P f x).
Proof. exact (@lem355058 A B P f x _7729 h1). Qed.
Lemma lem355060 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (P f x) = (P f x).
Proof. exact (eq_refl (P f x)). Qed.
Lemma lem355061 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (_7729 : type103 A B) (h1 : _7729 = (term159 A B)) : (term100 A B P f x) = (term170 A B _7729 P f x).
Proof. exact (MK_COMB (@lem355060 A B P f x) (@lem355059 A B P f x _7729 h1)). Qed.
Lemma lem355062 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (x' : B) : (term147 A B P f x x') = (term147 A B P f x x').
Proof. exact (eq_refl (term147 A B P f x x')). Qed.
Lemma lem355063 {A B : Type'} (x : B) (P : type547 A B) (f : A -> B) (x' : A) (_7729 : type103 A B) (h1 : _7729 = (term159 A B)) : (term149 A B x P f x') = (term171 A B x _7729 P f x').
Proof. exact (MK_COMB (@lem355062 A B P f x' x) (@lem355061 A B P f x' _7729 h1)). Qed.
Lemma lem355064 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (_7729 : type103 A B) (h1 : _7729 = (term159 A B)) : (term151 A B P f x) = (term172 A B _7729 P f x).
Proof. exact (fun_ext (fun x' : B => @lem355063 A B x' P f x _7729 h1)). Qed.
Lemma lem355065 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem355066 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (_7729 : type103 A B) (h1 : _7729 = (term159 A B)) : (term152 A B P f x) = (term173 A B _7729 P f x).
Proof. exact (MK_COMB (@lem355065 B) (@lem355064 A B P f x _7729 h1)). Qed.
Lemma lem355067 {A B : Type'} (P : type547 A B) (f : A -> B) (_7729 : type103 A B) (h1 : _7729 = (term159 A B)) : (term174 A B P f) = (term175 A B _7729 P f).
Proof. exact (fun_ext (fun x : A => @lem355066 A B P f x _7729 h1)). Qed.
Lemma lem355068 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem355069 {A B : Type'} (P : type547 A B) (f : A -> B) (_7729 : type103 A B) (h1 : _7729 = (term159 A B)) : (term153 A B P f) = (term176 A B _7729 P f).
Proof. exact (MK_COMB (@lem355068 A) (@lem355067 A B P f _7729 h1)). Qed.
Lemma lem355070 {A B : Type'} (P : type547 A B) (_7729 : type103 A B) (h1 : _7729 = (term159 A B)) : (term177 A B P) = (term178 A B _7729 P).
Proof. exact (fun_ext (fun f : A -> B => @lem355069 A B P f _7729 h1)). Qed.
Lemma lem355071 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem355072 {A B : Type'} (P : type547 A B) (_7729 : type103 A B) (h1 : _7729 = (term159 A B)) : (term154 A B P) = (term179 A B _7729 P).
Proof. exact (MK_COMB (@lem355071 A B) (@lem355070 A B P _7729 h1)). Qed.
Lemma lem355073 {A B : Type'} (_7729 : type103 A B) (h1 : _7729 = (term159 A B)) : (term180 A B) = (term181 A B _7729).
Proof. exact (fun_ext (fun P : type547 A B => @lem355072 A B P _7729 h1)). Qed.
Lemma lem355074 {A B : Type'} : (@all ((A -> B) -> A -> B -> Prop)) = (@all ((A -> B) -> A -> B -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> A -> B -> Prop))). Qed.
Lemma lem355075 {A B : Type'} (_7729 : type103 A B) (h1 : _7729 = (term159 A B)) : (term155 A B) = (term182 A B _7729).
Proof. exact (MK_COMB (@lem355074 A B) (@lem355073 A B _7729 h1)). Qed.
Lemma lem355076 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem355077 {A B : Type'} (_7729 : type103 A B) (h1 : _7729 = (term159 A B)) : (term183 A B) = (term184 A B _7729).
Proof. exact (MK_COMB (@lem355076) (@lem355075 A B _7729 h1)). Qed.
Lemma lem355079 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (_7729 : type103 A B) (h1 : _7729 = (term159 A B)) : (term23 A B P f x) = (_7729 P f x).
Proof. exact (EQ_MP (@lem355055 A B _7729 P f x) (@lem355054 A B P f x _7729 h1)). Qed.
Lemma lem355080 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (_7729 : type103 A B) (h1 : _7729 = (term159 A B)) : (term23 A B P f x) = (_7729 P f x).
Proof. exact (@lem355079 A B P f x _7729 h1). Qed.
Lemma lem355081 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem355082 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (_7729 : type103 A B) (h1 : _7729 = (term159 A B)) : (term25 A B P f x) = (term163 A B _7729 P f x).
Proof. exact (MK_COMB (@lem355081 B) (@lem355080 A B P f x _7729 h1)). Qed.
Lemma lem355083 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem355084 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (_7729 : type103 A B) (h1 : _7729 = (term159 A B)) : ((term23 A B P f x) = (f x)) = ((_7729 P f x) = (f x)).
Proof. exact (MK_COMB (@lem355082 A B P f x _7729 h1) (@lem355083 A B f x)). Qed.
Lemma lem355085 {A B : Type'} (P : type547 A B) (f : A -> B) (_7729 : type103 A B) (h1 : _7729 = (term159 A B)) : (term96 A B P f) = (term185 A B _7729 P f).
Proof. exact (fun_ext (fun x : A => @lem355084 A B P f x _7729 h1)). Qed.
Lemma lem355086 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem355087 {A B : Type'} (P : type547 A B) (f : A -> B) (_7729 : type103 A B) (h1 : _7729 = (term159 A B)) : (term97 A B P f) = (term186 A B _7729 P f).
Proof. exact (MK_COMB (@lem355086 A) (@lem355085 A B P f _7729 h1)). Qed.
Lemma lem355088 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem355089 {A B : Type'} (P : type547 A B) (f : A -> B) (_7729 : type103 A B) (h1 : _7729 = (term159 A B)) : (term187 A B P f) = (term188 A B _7729 P f).
Proof. exact (MK_COMB (@lem355088) (@lem355087 A B P f _7729 h1)). Qed.
Lemma lem355090 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term141 A B lt2 P f) = (term141 A B lt2 P f).
Proof. exact (eq_refl (term141 A B lt2 P f)). Qed.
Lemma lem355091 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (_7729 : type103 A B) (h1 : _7729 = (term159 A B)) : (term189 A B lt2 P f) = (term190 A B _7729 lt2 P f).
Proof. exact (MK_COMB (@lem355089 A B P f _7729 h1) (@lem355090 A B lt2 P f)). Qed.
Lemma lem355092 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : (term191 A B lt2 P) = (term191 A B lt2 P).
Proof. exact (eq_refl (term191 A B lt2 P)). Qed.
Lemma lem355093 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (_7729 : type103 A B) (h1 : _7729 = (term159 A B)) : (term192 A B lt2 P f) = (term193 A B _7729 lt2 P f).
Proof. exact (MK_COMB (@lem355092 A B lt2 P) (@lem355091 A B lt2 P f _7729 h1)). Qed.
Lemma lem355094 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : (term194 A B lt2 P) = (term194 A B lt2 P).
Proof. exact (eq_refl (term194 A B lt2 P)). Qed.
Lemma lem355095 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (_7729 : type103 A B) (h1 : _7729 = (term159 A B)) : (term195 A B lt2 P f) = (term196 A B _7729 lt2 P f).
Proof. exact (MK_COMB (@lem355094 A B lt2 P) (@lem355093 A B lt2 P f _7729 h1)). Qed.
Lemma lem355096 {A : Type'} (lt2 : type1402 A) : (term197 A lt2) = (term197 A lt2).
Proof. exact (eq_refl (term197 A lt2)). Qed.
Lemma lem355097 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (_7729 : type103 A B) (h1 : _7729 = (term159 A B)) : (term157 A B lt2 P f) = (term198 A B _7729 lt2 P f).
Proof. exact (MK_COMB (@lem355096 A lt2) (@lem355095 A B lt2 P f _7729 h1)). Qed.
Lemma lem355098 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (_7729 : type103 A B) (h1 : _7729 = (term159 A B)) : (term156 A B lt2 P f) = (term199 A B _7729 lt2 P f).
Proof. exact (MK_COMB (@lem355077 A B _7729 h1) (@lem355097 A B lt2 P f _7729 h1)). Qed.
Lemma lem355099 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (h1 : term200 A B lt2 P f) : term200 A B lt2 P f.
Proof. exact (h1). Qed.
Lemma lem355100 {A B : Type'} (_7729 : type103 A B) (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (h1 : term200 A B lt2 P f) : term201 A B lt2 P f _7729.
Proof. exact (@lem355099 A B lt2 P f h1 _7729). Qed.
Lemma lem355101 {A B : Type'} (_7729 : type103 A B) (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term201 A B lt2 P f _7729) = (term199 A B _7729 lt2 P f).
Proof. exact (eq_refl (term201 A B lt2 P f _7729)). Qed.
Lemma lem355102 {A B : Type'} (_7729 : type103 A B) (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (h1 : term200 A B lt2 P f) : term199 A B _7729 lt2 P f.
Proof. exact (EQ_MP (@lem355101 A B _7729 lt2 P f) (@lem355100 A B _7729 lt2 P f h1)). Qed.
Lemma lem355103 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (_7729 : type103 A B) (h1 : _7729 = (term159 A B)) : (term199 A B _7729 lt2 P f) = (term156 A B lt2 P f).
Proof. exact (SYM (@lem355098 A B lt2 P f _7729 h1)). Qed.
Lemma lem355104 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (_7729 : type103 A B) (h1 : term200 A B lt2 P f) (h2 : _7729 = (term159 A B)) : term156 A B lt2 P f.
Proof. exact (EQ_MP (@lem355103 A B lt2 P f _7729 h2) (@lem355102 A B _7729 lt2 P f h1)). Qed.
Lemma lem355105 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (_7729 : type103 A B) (h1 : _7729 = (term159 A B)) : term202 A B lt2 P f.
Proof. exact (fun h0 : term200 A B lt2 P f => @lem355104 A B lt2 P f _7729 h0 h1). Qed.
Lemma lem355106 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : term203 A B lt2 P f.
Proof. exact (@lem51 (term156 A B lt2 P f) (term200 A B lt2 P f) (term157 A B lt2 P f)). Qed.
Lemma lem355107 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (_7729 : type103 A B) (h1 : _7729 = (term159 A B)) : term204 A B lt2 P f.
Proof. exact (@lem355106 A B lt2 P f (@lem355105 A B lt2 P f _7729 h1)). Qed.
Lemma lem355108 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (_7729 : type103 A B) (h1 : _7729 = (term159 A B)) : term205 A B lt2 P f.
Proof. exact (@lem355107 A B lt2 P f _7729 h1 (@lem355024 A B lt2 P f)). Qed.
Lemma lem355109 {A B : Type'} : (term159 A B) = (term159 A B).
Proof. exact (eq_refl (term159 A B)). Qed.
Lemma lem355110 {A B : Type'} (_7729 : type103 A B) (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : term206 A B _7729 lt2 P f.
Proof. exact (fun h0 : _7729 = (term159 A B) => @lem355108 A B lt2 P f _7729 h0). Qed.
Lemma lem355111 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : term207 A B lt2 P f.
Proof. exact (@lem355110 A B (term159 A B) lt2 P f). Qed.
Lemma lem355112 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : term205 A B lt2 P f.
Proof. exact (@lem355111 A B lt2 P f (@lem355109 A B)). Qed.
Lemma lem355113 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (h1 : term200 A B lt2 P f) : term200 A B lt2 P f.
Proof. exact (h1). Qed.
Lemma lem355114 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : term208 A B lt2 P f.
Proof. exact (fun h0 : term200 A B lt2 P f => @lem355113 A B lt2 P f h0). Qed.
Lemma lem355115 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : term209 A B lt2 P f.
Proof. exact (@lem51 (term200 A B lt2 P f) (term200 A B lt2 P f) (term157 A B lt2 P f)). Qed.
Lemma lem355116 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : term210 A B lt2 P f.
Proof. exact (@lem355115 A B lt2 P f (@lem355114 A B lt2 P f)). Qed.
Lemma lem355117 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : term205 A B lt2 P f.
Proof. exact (@lem355116 A B lt2 P f (@lem355112 A B lt2 P f)). Qed.
Lemma lem355118 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (h1 : term205 A B lt2 P f) : term205 A B lt2 P f.
Proof. exact (h1). Qed.
Lemma lem355119 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (h1 : term200 A B lt2 P f) : term200 A B lt2 P f.
Proof. exact (h1). Qed.
Lemma lem355120 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (h1 : term200 A B lt2 P f) (h2 : term205 A B lt2 P f) : term157 A B lt2 P f.
Proof. exact (@lem355118 A B lt2 P f h2 (@lem355119 A B lt2 P f h1)). Qed.
Lemma lem355121 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (h1 : term200 A B lt2 P f) : term211 A B lt2 P f.
Proof. exact (fun h0 : term205 A B lt2 P f => @lem355120 A B lt2 P f h1 h0). Qed.
Lemma lem355122 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (h1 : term205 A B lt2 P f) : term205 A B lt2 P f.
Proof. exact (h1). Qed.
Lemma lem355123 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (h1 : term200 A B lt2 P f) (h2 : term205 A B lt2 P f) : term157 A B lt2 P f.
Proof. exact (@lem355121 A B lt2 P f h1 (@lem355122 A B lt2 P f h2)). Qed.
Lemma lem355124 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (h1 : term205 A B lt2 P f) : term205 A B lt2 P f.
Proof. exact (fun h0 : term200 A B lt2 P f => @lem355123 A B lt2 P f h0 h1). Qed.
Lemma lem355125 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : term210 A B lt2 P f.
Proof. exact (fun h0 : term205 A B lt2 P f => @lem355124 A B lt2 P f h0). Qed.
Lemma lem355128 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : term205 A B lt2 P f.
Proof. exact (@lem355125 A B lt2 P f (@lem355117 A B lt2 P f)). Qed.
Lemma lem355129 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : term205 A B lt2 P f.
Proof. exact (@lem355128 A B lt2 P f). Qed.
Lemma lem355223 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem355224 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term141 A B lt2 P f) = (term212 A B lt2 P f).
Proof. exact (@lem355223 (term142 A B lt2 P f)). Qed.
Lemma lem355226 (t : Prop) : (term213 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem355227 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term212 A B lt2 P f) = (term134 A B lt2 P f).
Proof. exact (@lem355226 (term134 A B lt2 P f)). Qed.
Lemma lem355232 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term141 A B lt2 P f) = (term134 A B lt2 P f).
Proof. exact (TRANS (@lem355224 A B lt2 P f) (@lem355227 A B lt2 P f)). Qed.
Lemma lem355249 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) : (term188 A B _7729 P f) = (term188 A B _7729 P f).
Proof. exact (eq_refl (term188 A B _7729 P f)). Qed.
Lemma lem355250 {A B : Type'} (_7729 : type103 A B) (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term190 A B _7729 lt2 P f) = (term214 A B _7729 lt2 P f).
Proof. exact (MK_COMB (@lem355249 A B _7729 P f) (@lem355232 A B lt2 P f)). Qed.
Lemma lem355253 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : (term191 A B lt2 P) = (term191 A B lt2 P).
Proof. exact (eq_refl (term191 A B lt2 P)). Qed.
Lemma lem355254 {A B : Type'} (_7729 : type103 A B) (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term193 A B _7729 lt2 P f) = (term215 A B _7729 lt2 P f).
Proof. exact (MK_COMB (@lem355253 A B lt2 P) (@lem355250 A B _7729 lt2 P f)). Qed.
Lemma lem355257 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : (term194 A B lt2 P) = (term194 A B lt2 P).
Proof. exact (eq_refl (term194 A B lt2 P)). Qed.
Lemma lem355258 {A B : Type'} (_7729 : type103 A B) (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term196 A B _7729 lt2 P f) = (term216 A B _7729 lt2 P f).
Proof. exact (MK_COMB (@lem355257 A B lt2 P) (@lem355254 A B _7729 lt2 P f)). Qed.
Lemma lem355261 {A : Type'} (lt2 : type1402 A) : (term197 A lt2) = (term197 A lt2).
Proof. exact (eq_refl (term197 A lt2)). Qed.
Lemma lem355262 {A B : Type'} (_7729 : type103 A B) (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term198 A B _7729 lt2 P f) = (term217 A B _7729 lt2 P f).
Proof. exact (MK_COMB (@lem355261 A lt2) (@lem355258 A B _7729 lt2 P f)). Qed.
Lemma lem355265 {A B : Type'} (_7729 : type103 A B) : (term184 A B _7729) = (term184 A B _7729).
Proof. exact (eq_refl (term184 A B _7729)). Qed.
Lemma lem355266 {A B : Type'} (_7729 : type103 A B) (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term199 A B _7729 lt2 P f) = (term218 A B _7729 lt2 P f).
Proof. exact (MK_COMB (@lem355265 A B _7729) (@lem355262 A B _7729 lt2 P f)). Qed.
Lemma lem355269 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term219 A B lt2 P f) = (term220 A B lt2 P f).
Proof. exact (fun_ext (fun _7729 : type103 A B => @lem355266 A B _7729 lt2 P f)). Qed.
Lemma lem355270 {A B : Type'} : (@all (((A -> B) -> A -> B -> Prop) -> (A -> B) -> A -> B)) = (@all (((A -> B) -> A -> B -> Prop) -> (A -> B) -> A -> B)).
Proof. exact (eq_refl (@all (((A -> B) -> A -> B -> Prop) -> (A -> B) -> A -> B))). Qed.
Lemma lem355271 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term200 A B lt2 P f) = (term221 A B lt2 P f).
Proof. exact (MK_COMB (@lem355270 A B) (@lem355269 A B lt2 P f)). Qed.
Lemma lem355276 {A B : Type'} (P : type547 A B) (f : A -> B) : (term222 A B P f) = (term223 A B P f).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem355271 A B lt2 P f)). Qed.
Lemma lem355277 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem355278 {A B : Type'} (P : type547 A B) (f : A -> B) : (term224 A B P f) = (term225 A B P f).
Proof. exact (MK_COMB (@lem355277 A) (@lem355276 A B P f)). Qed.
Lemma lem355283 {A B : Type'} (f : A -> B) : (term226 A B f) = (term227 A B f).
Proof. exact (fun_ext (fun P : type547 A B => @lem355278 A B P f)). Qed.
Lemma lem355284 {A B : Type'} : (@all ((A -> B) -> A -> B -> Prop)) = (@all ((A -> B) -> A -> B -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> A -> B -> Prop))). Qed.
Lemma lem355285 {A B : Type'} (f : A -> B) : (term228 A B f) = (term229 A B f).
Proof. exact (MK_COMB (@lem355284 A B) (@lem355283 A B f)). Qed.
Lemma lem355290 {A B : Type'} : (term230 A B) = (term231 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem355285 A B f)). Qed.
Lemma lem355291 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem355300 {A B : Type'} : (term232 A B) = (term233 A B).
Proof. exact (MK_COMB (@lem355291 A B) (@lem355290 A B)). Qed.
Lemma lem355301 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (y : B) : (P f x y) = (P f x y).
Proof. exact (eq_refl (P f x y)). Qed.
Lemma lem355302 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term69 A B P f x) = (term69 A B P f x).
Proof. exact (fun_ext (fun y : B => @lem355301 A B P f x y)). Qed.
Lemma lem355303 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem355304 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term106 A B P f x) = (term106 A B P f x).
Proof. exact (MK_COMB (@lem355303 B) (@lem355302 A B P f x)). Qed.
Lemma lem355305 {A B : Type'} (P : type547 A B) (f : A -> B) (y : A) (y' : B) : (P f y y') = (P f y y').
Proof. exact (eq_refl (P f y y')). Qed.
Lemma lem355306 {A B : Type'} (P : type547 A B) (f : A -> B) (y : A) : (term69 A B P f y) = (term69 A B P f y).
Proof. exact (fun_ext (fun y' : B => @lem355305 A B P f y y')). Qed.
Lemma lem355307 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem355308 {A B : Type'} (P : type547 A B) (f : A -> B) (y : A) : (term106 A B P f y) = (term106 A B P f y).
Proof. exact (MK_COMB (@lem355307 B) (@lem355306 A B P f y)). Qed.
Lemma lem355311 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (term120 A lt2 y x) = (term120 A lt2 y x).
Proof. exact (eq_refl (term120 A lt2 y x)). Qed.
Lemma lem355312 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (y : A) : (term122 A B lt2 x P f y) = (term122 A B lt2 x P f y).
Proof. exact (MK_COMB (@lem355311 A lt2 y x) (@lem355308 A B P f y)). Qed.
Lemma lem355313 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) : (term124 A B lt2 x P f) = (term124 A B lt2 x P f).
Proof. exact (fun_ext (fun y : A => @lem355312 A B lt2 x P f y)). Qed.
Lemma lem355314 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem355315 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) : (term126 A B lt2 x P f) = (term126 A B lt2 x P f).
Proof. exact (MK_COMB (@lem355314 A) (@lem355313 A B lt2 x P f)). Qed.
Lemma lem355316 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem355317 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) : (term128 A B lt2 x P f) = (term128 A B lt2 x P f).
Proof. exact (MK_COMB (@lem355316) (@lem355315 A B lt2 x P f)). Qed.
Lemma lem355318 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (x : A) : (term130 A B lt2 P f x) = (term130 A B lt2 P f x).
Proof. exact (MK_COMB (@lem355317 A B lt2 x P f) (@lem355304 A B P f x)). Qed.
Lemma lem355319 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term132 A B lt2 P f) = (term132 A B lt2 P f).
Proof. exact (fun_ext (fun x : A => @lem355318 A B lt2 P f x)). Qed.
Lemma lem355320 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem355321 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term134 A B lt2 P f) = (term134 A B lt2 P f).
Proof. exact (MK_COMB (@lem355320 A) (@lem355319 A B lt2 P f)). Qed.
Lemma lem355322 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) : ((_7729 P f x) = (f x)) = ((_7729 P f x) = (f x)).
Proof. exact (eq_refl ((_7729 P f x) = (f x))). Qed.
Lemma lem355323 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) : (term185 A B _7729 P f) = (term185 A B _7729 P f).
Proof. exact (fun_ext (fun x : A => @lem355322 A B _7729 P f x)). Qed.
Lemma lem355324 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem355325 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) : (term186 A B _7729 P f) = (term186 A B _7729 P f).
Proof. exact (MK_COMB (@lem355324 A) (@lem355323 A B _7729 P f)). Qed.
Lemma lem355326 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem355327 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) : (term188 A B _7729 P f) = (term188 A B _7729 P f).
Proof. exact (MK_COMB (@lem355326) (@lem355325 A B _7729 P f)). Qed.
Lemma lem355328 {A B : Type'} (_7729 : type103 A B) (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term214 A B _7729 lt2 P f) = (term214 A B _7729 lt2 P f).
Proof. exact (MK_COMB (@lem355327 A B _7729 P f) (@lem355321 A B lt2 P f)). Qed.
Lemma lem355329 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (y : B) : (P f x y) = (P f x y).
Proof. exact (eq_refl (P f x y)). Qed.
Lemma lem355330 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term69 A B P f x) = (term69 A B P f x).
Proof. exact (fun_ext (fun y : B => @lem355329 A B P f x y)). Qed.
Lemma lem355331 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem355332 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term106 A B P f x) = (term106 A B P f x).
Proof. exact (MK_COMB (@lem355331 B) (@lem355330 A B P f x)). Qed.
Lemma lem355337 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (z : A) : (term234 A B lt2 x P f z) = (term234 A B lt2 x P f z).
Proof. exact (eq_refl (term234 A B lt2 x P f z)). Qed.
Lemma lem355338 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) : (term235 A B lt2 x P f) = (term235 A B lt2 x P f).
Proof. exact (fun_ext (fun z : A => @lem355337 A B lt2 x P f z)). Qed.
Lemma lem355339 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem355340 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) : (term236 A B lt2 x P f) = (term236 A B lt2 x P f).
Proof. exact (MK_COMB (@lem355339 A) (@lem355338 A B lt2 x P f)). Qed.
Lemma lem355341 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem355342 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) : (term237 A B lt2 x P f) = (term237 A B lt2 x P f).
Proof. exact (MK_COMB (@lem355341) (@lem355340 A B lt2 x P f)). Qed.
Lemma lem355343 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (x : A) : (term238 A B lt2 P f x) = (term238 A B lt2 P f x).
Proof. exact (MK_COMB (@lem355342 A B lt2 x P f) (@lem355332 A B P f x)). Qed.
Lemma lem355344 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term239 A B lt2 P f) = (term239 A B lt2 P f).
Proof. exact (fun_ext (fun x : A => @lem355343 A B lt2 P f x)). Qed.
Lemma lem355345 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem355346 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term240 A B lt2 P f) = (term240 A B lt2 P f).
Proof. exact (MK_COMB (@lem355345 A) (@lem355344 A B lt2 P f)). Qed.
Lemma lem355347 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : (term241 A B lt2 P) = (term241 A B lt2 P).
Proof. exact (fun_ext (fun f : A -> B => @lem355346 A B lt2 P f)). Qed.
Lemma lem355348 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem355349 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : (term6 A B lt2 P) = (term6 A B lt2 P).
Proof. exact (MK_COMB (@lem355348 A B) (@lem355347 A B lt2 P)). Qed.
Lemma lem355350 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem355351 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : (term191 A B lt2 P) = (term191 A B lt2 P).
Proof. exact (MK_COMB (@lem355350) (@lem355349 A B lt2 P)). Qed.
Lemma lem355352 {A B : Type'} (_7729 : type103 A B) (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term215 A B _7729 lt2 P f) = (term215 A B _7729 lt2 P f).
Proof. exact (MK_COMB (@lem355351 A B lt2 P) (@lem355328 A B _7729 lt2 P f)). Qed.
Lemma lem355357 {A B : Type'} (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) (y : B) : ((P f x y) = (P g x y)) = ((P f x y) = (P g x y)).
Proof. exact (eq_refl ((P f x y) = (P g x y))). Qed.
Lemma lem355362 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) (z : A) : (term64 A B lt2 x f g z) = (term64 A B lt2 x f g z).
Proof. exact (eq_refl (term64 A B lt2 x f g z)). Qed.
Lemma lem355363 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) : (term65 A B lt2 x f g) = (term65 A B lt2 x f g).
Proof. exact (fun_ext (fun z : A => @lem355362 A B lt2 x f g z)). Qed.
Lemma lem355364 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem355365 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) : (term52 A B lt2 x f g) = (term52 A B lt2 x f g).
Proof. exact (MK_COMB (@lem355364 A) (@lem355363 A B lt2 x f g)). Qed.
Lemma lem355366 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem355367 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) : (term26 A B lt2 x f g) = (term26 A B lt2 x f g).
Proof. exact (MK_COMB (@lem355366) (@lem355365 A B lt2 x f g)). Qed.
Lemma lem355368 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) (y : B) : (term60 A B lt2 f P g x y) = (term60 A B lt2 f P g x y).
Proof. exact (MK_COMB (@lem355367 A B lt2 x f g) (@lem355357 A B f P g x y)). Qed.
Lemma lem355369 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : (term242 A B lt2 f P g x) = (term242 A B lt2 f P g x).
Proof. exact (fun_ext (fun y : B => @lem355368 A B lt2 f P g x y)). Qed.
Lemma lem355370 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem355371 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : (term58 A B lt2 f P g x) = (term58 A B lt2 f P g x).
Proof. exact (MK_COMB (@lem355370 B) (@lem355369 A B lt2 f P g x)). Qed.
Lemma lem355372 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) : (term243 A B lt2 f P g) = (term243 A B lt2 f P g).
Proof. exact (fun_ext (fun x : A => @lem355371 A B lt2 f P g x)). Qed.
Lemma lem355373 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem355374 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) : (term56 A B lt2 f P g) = (term56 A B lt2 f P g).
Proof. exact (MK_COMB (@lem355373 A) (@lem355372 A B lt2 f P g)). Qed.
Lemma lem355375 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) : (term244 A B lt2 f P) = (term244 A B lt2 f P).
Proof. exact (fun_ext (fun g : A -> B => @lem355374 A B lt2 f P g)). Qed.
Lemma lem355376 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem355377 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) : (term54 A B lt2 f P) = (term54 A B lt2 f P).
Proof. exact (MK_COMB (@lem355376 A B) (@lem355375 A B lt2 f P)). Qed.
Lemma lem355378 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : (term245 A B lt2 P) = (term245 A B lt2 P).
Proof. exact (fun_ext (fun f : A -> B => @lem355377 A B lt2 f P)). Qed.
Lemma lem355379 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem355380 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : (term7 A B lt2 P) = (term7 A B lt2 P).
Proof. exact (MK_COMB (@lem355379 A B) (@lem355378 A B lt2 P)). Qed.
Lemma lem355381 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem355382 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : (term194 A B lt2 P) = (term194 A B lt2 P).
Proof. exact (MK_COMB (@lem355381) (@lem355380 A B lt2 P)). Qed.
Lemma lem355383 {A B : Type'} (_7729 : type103 A B) (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term216 A B _7729 lt2 P f) = (term216 A B _7729 lt2 P f).
Proof. exact (MK_COMB (@lem355382 A B lt2 P) (@lem355352 A B _7729 lt2 P f)). Qed.
Lemma lem355386 {A : Type'} (lt2 : type1402 A) : (term197 A lt2) = (term197 A lt2).
Proof. exact (eq_refl (term197 A lt2)). Qed.
Lemma lem355387 {A B : Type'} (_7729 : type103 A B) (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term217 A B _7729 lt2 P f) = (term217 A B _7729 lt2 P f).
Proof. exact (MK_COMB (@lem355386 A lt2) (@lem355383 A B _7729 lt2 P f)). Qed.
Lemma lem355392 {A B : Type'} (x : B) (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x' : A) : (term171 A B x _7729 P f x') = (term171 A B x _7729 P f x').
Proof. exact (eq_refl (term171 A B x _7729 P f x')). Qed.
Lemma lem355393 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) : (term172 A B _7729 P f x) = (term172 A B _7729 P f x).
Proof. exact (fun_ext (fun x' : B => @lem355392 A B x' _7729 P f x)). Qed.
Lemma lem355394 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem355395 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) : (term173 A B _7729 P f x) = (term173 A B _7729 P f x).
Proof. exact (MK_COMB (@lem355394 B) (@lem355393 A B _7729 P f x)). Qed.
Lemma lem355396 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) : (term175 A B _7729 P f) = (term175 A B _7729 P f).
Proof. exact (fun_ext (fun x : A => @lem355395 A B _7729 P f x)). Qed.
Lemma lem355397 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem355398 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) : (term176 A B _7729 P f) = (term176 A B _7729 P f).
Proof. exact (MK_COMB (@lem355397 A) (@lem355396 A B _7729 P f)). Qed.
Lemma lem355399 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) : (term178 A B _7729 P) = (term178 A B _7729 P).
Proof. exact (fun_ext (fun f : A -> B => @lem355398 A B _7729 P f)). Qed.
Lemma lem355400 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem355401 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) : (term179 A B _7729 P) = (term179 A B _7729 P).
Proof. exact (MK_COMB (@lem355400 A B) (@lem355399 A B _7729 P)). Qed.
Lemma lem355402 {A B : Type'} (_7729 : type103 A B) : (term181 A B _7729) = (term181 A B _7729).
Proof. exact (fun_ext (fun P : type547 A B => @lem355401 A B _7729 P)). Qed.
Lemma lem355403 {A B : Type'} : (@all ((A -> B) -> A -> B -> Prop)) = (@all ((A -> B) -> A -> B -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> A -> B -> Prop))). Qed.
Lemma lem355404 {A B : Type'} (_7729 : type103 A B) : (term182 A B _7729) = (term182 A B _7729).
Proof. exact (MK_COMB (@lem355403 A B) (@lem355402 A B _7729)). Qed.
Lemma lem355405 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem355406 {A B : Type'} (_7729 : type103 A B) : (term184 A B _7729) = (term184 A B _7729).
Proof. exact (MK_COMB (@lem355405) (@lem355404 A B _7729)). Qed.
Lemma lem355407 {A B : Type'} (_7729 : type103 A B) (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term218 A B _7729 lt2 P f) = (term218 A B _7729 lt2 P f).
Proof. exact (MK_COMB (@lem355406 A B _7729) (@lem355387 A B _7729 lt2 P f)). Qed.
Lemma lem355408 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term220 A B lt2 P f) = (term220 A B lt2 P f).
Proof. exact (fun_ext (fun _7729 : type103 A B => @lem355407 A B _7729 lt2 P f)). Qed.
Lemma lem355409 {A B : Type'} : (@all (((A -> B) -> A -> B -> Prop) -> (A -> B) -> A -> B)) = (@all (((A -> B) -> A -> B -> Prop) -> (A -> B) -> A -> B)).
Proof. exact (eq_refl (@all (((A -> B) -> A -> B -> Prop) -> (A -> B) -> A -> B))). Qed.
Lemma lem355410 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term221 A B lt2 P f) = (term221 A B lt2 P f).
Proof. exact (MK_COMB (@lem355409 A B) (@lem355408 A B lt2 P f)). Qed.
Lemma lem355411 {A B : Type'} (P : type547 A B) (f : A -> B) : (term223 A B P f) = (term223 A B P f).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem355410 A B lt2 P f)). Qed.
Lemma lem355412 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem355413 {A B : Type'} (P : type547 A B) (f : A -> B) : (term225 A B P f) = (term225 A B P f).
Proof. exact (MK_COMB (@lem355412 A) (@lem355411 A B P f)). Qed.
Lemma lem355414 {A B : Type'} (f : A -> B) : (term227 A B f) = (term227 A B f).
Proof. exact (fun_ext (fun P : type547 A B => @lem355413 A B P f)). Qed.
Lemma lem355415 {A B : Type'} : (@all ((A -> B) -> A -> B -> Prop)) = (@all ((A -> B) -> A -> B -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> A -> B -> Prop))). Qed.
Lemma lem355416 {A B : Type'} (f : A -> B) : (term229 A B f) = (term229 A B f).
Proof. exact (MK_COMB (@lem355415 A B) (@lem355414 A B f)). Qed.
Lemma lem355417 {A B : Type'} : (term231 A B) = (term231 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem355416 A B f)). Qed.
Lemma lem355418 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem355419 {A B : Type'} : (term233 A B) = (term233 A B).
Proof. exact (MK_COMB (@lem355418 A B) (@lem355417 A B)). Qed.
Lemma lem355578 {A B : Type'} : (term232 A B) = (term233 A B).
Proof. exact (TRANS (@lem355300 A B) (@lem355419 A B)). Qed.
Lemma lem355579 {A B : Type'} : (term233 A B) = (term232 A B).
Proof. exact (SYM (@lem355578 A B)). Qed.
Lemma lem355580 {A B : Type'} (_7729 : type103 A B) (h1 : term182 A B _7729) : term182 A B _7729.
Proof. exact (h1). Qed.
Lemma lem355582 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (h1 : term7 A B lt2 P) : term7 A B lt2 P.
Proof. exact (h1). Qed.
Lemma lem355583 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (h1 : term6 A B lt2 P) : term6 A B lt2 P.
Proof. exact (h1). Qed.
Lemma lem355584 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (h1 : term186 A B _7729 P f) : term186 A B _7729 P f.
Proof. exact (h1). Qed.
Lemma lem355585 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (h1 : term126 A B lt2 x P f) : term126 A B lt2 x P f.
Proof. exact (h1). Qed.
Lemma lem355587 (p : Prop) : p = (term140 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem355588 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term106 A B P f x) = (term246 A B P f x).
Proof. exact (@lem355587 (term106 A B P f x)). Qed.
Lemma lem355589 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term246 A B P f x) = (term106 A B P f x).
Proof. exact (SYM (@lem355588 A B P f x)). Qed.
Lemma lem355590 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (h1 : term247 A B P f x) : term247 A B P f x.
Proof. exact (h1). Qed.
Lemma lem355597 {A B : Type'} (x : B) (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x' : A) : (term171 A B x _7729 P f x') = (term248 A B x _7729 P f x').
Proof. exact (@lem17265 (P f x' x) (term170 A B _7729 P f x')). Qed.
Lemma lem355598 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) : (term172 A B _7729 P f x) = (term249 A B _7729 P f x).
Proof. exact (fun_ext (fun x' : B => @lem355597 A B x' _7729 P f x)). Qed.
Lemma lem355599 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem355600 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) : (term173 A B _7729 P f x) = (term250 A B _7729 P f x).
Proof. exact (MK_COMB (@lem355599 B) (@lem355598 A B _7729 P f x)). Qed.
Lemma lem355601 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) : (term175 A B _7729 P f) = (term251 A B _7729 P f).
Proof. exact (fun_ext (fun x : A => @lem355600 A B _7729 P f x)). Qed.
Lemma lem355602 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem355603 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) : (term176 A B _7729 P f) = (term252 A B _7729 P f).
Proof. exact (MK_COMB (@lem355602 A) (@lem355601 A B _7729 P f)). Qed.
Lemma lem355604 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) : (term178 A B _7729 P) = (term253 A B _7729 P).
Proof. exact (fun_ext (fun f : A -> B => @lem355603 A B _7729 P f)). Qed.
Lemma lem355605 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem355606 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) : (term179 A B _7729 P) = (term254 A B _7729 P).
Proof. exact (MK_COMB (@lem355605 A B) (@lem355604 A B _7729 P)). Qed.
Lemma lem355607 {A B : Type'} (_7729 : type103 A B) : (term181 A B _7729) = (term255 A B _7729).
Proof. exact (fun_ext (fun P : type547 A B => @lem355606 A B _7729 P)). Qed.
Lemma lem355608 {A B : Type'} : (@all ((A -> B) -> A -> B -> Prop)) = (@all ((A -> B) -> A -> B -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> A -> B -> Prop))). Qed.
Lemma lem355609 {A B : Type'} (_7729 : type103 A B) : (term182 A B _7729) = (term256 A B _7729).
Proof. exact (MK_COMB (@lem355608 A B) (@lem355607 A B _7729)). Qed.
Lemma lem355643 {A : Type'} (P : A -> Prop) (Q : Prop) : (term257 A P Q) = (term258 A P Q).
Proof. exact (EQ_MP (@lem18947 A P Q) (@lem18946 A P Q)). Qed.
Lemma lem355644 {B : Type'} (P : B -> Prop) (Q : Prop) : (term257 B P Q) = (term258 B P Q).
Proof. exact (@lem355643 B P Q). Qed.
Lemma lem355645 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) : (term259 A B _7729 P f x) = (term260 A B _7729 P f x).
Proof. exact (@lem355644 B (term261 A B P f x) (term170 A B _7729 P f x)). Qed.
Lemma lem355646 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (x' : B) : (term262 A B P f x x') = (term263 A B P f x x').
Proof. exact (eq_refl (term262 A B P f x x')). Qed.
Lemma lem355647 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem355648 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (x' : B) : (term264 A B P f x x') = (term265 A B P f x x').
Proof. exact (MK_COMB (@lem355647) (@lem355646 A B P f x x')). Qed.
Lemma lem355649 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) : (term170 A B _7729 P f x) = (term170 A B _7729 P f x).
Proof. exact (eq_refl (term170 A B _7729 P f x)). Qed.
Lemma lem355650 {A B : Type'} (x : B) (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x' : A) : (term266 A B x _7729 P f x') = (term248 A B x _7729 P f x').
Proof. exact (MK_COMB (@lem355648 A B P f x' x) (@lem355649 A B _7729 P f x')). Qed.
Lemma lem355651 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) : (term267 A B _7729 P f x) = (term249 A B _7729 P f x).
Proof. exact (fun_ext (fun x' : B => @lem355650 A B x' _7729 P f x)). Qed.
Lemma lem355652 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem355653 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) : (term259 A B _7729 P f x) = (term250 A B _7729 P f x).
Proof. exact (MK_COMB (@lem355652 B) (@lem355651 A B _7729 P f x)). Qed.
Lemma lem355654 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem355655 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) : (term268 A B _7729 P f x) = (term269 A B _7729 P f x).
Proof. exact (MK_COMB (@lem355654) (@lem355653 A B _7729 P f x)). Qed.
Lemma lem355656 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (x' : B) : (term262 A B P f x x') = (term263 A B P f x x').
Proof. exact (eq_refl (term262 A B P f x x')). Qed.
Lemma lem355657 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term270 A B P f x) = (term261 A B P f x).
Proof. exact (fun_ext (fun x' : B => @lem355656 A B P f x x')). Qed.
Lemma lem355658 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem355659 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term271 A B P f x) = (term272 A B P f x).
Proof. exact (MK_COMB (@lem355658 B) (@lem355657 A B P f x)). Qed.
Lemma lem355660 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem355661 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term273 A B P f x) = (term274 A B P f x).
Proof. exact (MK_COMB (@lem355660) (@lem355659 A B P f x)). Qed.
Lemma lem355662 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) : (term170 A B _7729 P f x) = (term170 A B _7729 P f x).
Proof. exact (eq_refl (term170 A B _7729 P f x)). Qed.
Lemma lem355663 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) : (term260 A B _7729 P f x) = (term275 A B _7729 P f x).
Proof. exact (MK_COMB (@lem355661 A B P f x) (@lem355662 A B _7729 P f x)). Qed.
Lemma lem355664 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) : ((term259 A B _7729 P f x) = (term260 A B _7729 P f x)) = ((term250 A B _7729 P f x) = (term275 A B _7729 P f x)).
Proof. exact (MK_COMB (@lem355655 A B _7729 P f x) (@lem355663 A B _7729 P f x)). Qed.
Lemma lem355665 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) : (term250 A B _7729 P f x) = (term275 A B _7729 P f x).
Proof. exact (EQ_MP (@lem355664 A B _7729 P f x) (@lem355645 A B _7729 P f x)). Qed.
Lemma lem355670 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) : (term251 A B _7729 P f) = (term276 A B _7729 P f).
Proof. exact (fun_ext (fun x : A => @lem355665 A B _7729 P f x)). Qed.
Lemma lem355671 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem355672 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) : (term252 A B _7729 P f) = (term277 A B _7729 P f).
Proof. exact (MK_COMB (@lem355671 A) (@lem355670 A B _7729 P f)). Qed.
Lemma lem355721 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) : (term253 A B _7729 P) = (term278 A B _7729 P).
Proof. exact (fun_ext (fun f : A -> B => @lem355672 A B _7729 P f)). Qed.
Lemma lem355722 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem355723 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) : (term254 A B _7729 P) = (term279 A B _7729 P).
Proof. exact (MK_COMB (@lem355722 A B) (@lem355721 A B _7729 P)). Qed.
Lemma lem355728 {A B : Type'} (_7729 : type103 A B) : (term255 A B _7729) = (term280 A B _7729).
Proof. exact (fun_ext (fun P : type547 A B => @lem355723 A B _7729 P)). Qed.
Lemma lem355729 {A B : Type'} : (@all ((A -> B) -> A -> B -> Prop)) = (@all ((A -> B) -> A -> B -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> A -> B -> Prop))). Qed.
Lemma lem355736 {A B : Type'} (_7729 : type103 A B) : (term256 A B _7729) = (term281 A B _7729).
Proof. exact (MK_COMB (@lem355729 A B) (@lem355728 A B _7729)). Qed.
Lemma lem355737 {A B : Type'} (_7729 : type103 A B) : (term182 A B _7729) = (term281 A B _7729).
Proof. exact (TRANS (@lem355609 A B _7729) (@lem355736 A B _7729)). Qed.
Lemma lem355738 {A B : Type'} (_7729 : type103 A B) (h1 : term182 A B _7729) : term281 A B _7729.
Proof. exact (EQ_MP (@lem355737 A B _7729) (@lem355580 A B _7729 h1)). Qed.
Lemma lem355751 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) (z : A) : (term282 A B lt2 x f g z) = (term283 A B lt2 x f g z).
Proof. exact (@lem17362 (lt2 z x) ((f z) = (g z))). Qed.
Lemma lem355752 {A : Type'} (P : A -> Prop) : (term284 A P) = (term285 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem355753 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) : (term286 A B lt2 x f g) = (term287 A B lt2 x f g).
Proof. exact (@lem355752 A (term65 A B lt2 x f g)). Qed.
Lemma lem355754 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) (z : A) : (term63 A B lt2 x f g z) = (term64 A B lt2 x f g z).
Proof. exact (eq_refl (term63 A B lt2 x f g z)). Qed.
Lemma lem355755 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem355756 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) (z : A) : (term288 A B lt2 x f g z) = (term282 A B lt2 x f g z).
Proof. exact (MK_COMB (@lem355755) (@lem355754 A B lt2 x f g z)). Qed.
Lemma lem355757 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) (z : A) : (term288 A B lt2 x f g z) = (term283 A B lt2 x f g z).
Proof. exact (TRANS (@lem355756 A B lt2 x f g z) (@lem355751 A B lt2 x f g z)). Qed.
Lemma lem355758 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) : (term289 A B lt2 x f g) = (term290 A B lt2 x f g).
Proof. exact (fun_ext (fun z : A => @lem355757 A B lt2 x f g z)). Qed.
Lemma lem355759 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem355760 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) : (term287 A B lt2 x f g) = (term291 A B lt2 x f g).
Proof. exact (MK_COMB (@lem355759 A) (@lem355758 A B lt2 x f g)). Qed.
Lemma lem355761 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) : (term286 A B lt2 x f g) = (term291 A B lt2 x f g).
Proof. exact (TRANS (@lem355753 A B lt2 x f g) (@lem355760 A B lt2 x f g)). Qed.
Lemma lem355776 {A B : Type'} (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) (y : B) : ((P f x y) = (P g x y)) = (term292 A B f P g x y).
Proof. exact (@lem17784 (P f x y) (P g x y)). Qed.
Lemma lem355777 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem355778 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) : (term293 A B lt2 x f g) = (term294 A B lt2 x f g).
Proof. exact (MK_COMB (@lem355777) (@lem355761 A B lt2 x f g)). Qed.
Lemma lem355779 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) (y : B) : (term295 A B lt2 f P g x y) = (term296 A B lt2 f P g x y).
Proof. exact (MK_COMB (@lem355778 A B lt2 x f g) (@lem355776 A B f P g x y)). Qed.
Lemma lem355780 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) (y : B) : (term60 A B lt2 f P g x y) = (term295 A B lt2 f P g x y).
Proof. exact (@lem17265 (term52 A B lt2 x f g) ((P f x y) = (P g x y))). Qed.
Lemma lem355781 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) (y : B) : (term60 A B lt2 f P g x y) = (term296 A B lt2 f P g x y).
Proof. exact (TRANS (@lem355780 A B lt2 f P g x y) (@lem355779 A B lt2 f P g x y)). Qed.
Lemma lem355782 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : (term242 A B lt2 f P g x) = (term297 A B lt2 f P g x).
Proof. exact (fun_ext (fun y : B => @lem355781 A B lt2 f P g x y)). Qed.
Lemma lem355783 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem355784 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : (term58 A B lt2 f P g x) = (term298 A B lt2 f P g x).
Proof. exact (MK_COMB (@lem355783 B) (@lem355782 A B lt2 f P g x)). Qed.
Lemma lem355785 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) : (term243 A B lt2 f P g) = (term299 A B lt2 f P g).
Proof. exact (fun_ext (fun x : A => @lem355784 A B lt2 f P g x)). Qed.
Lemma lem355786 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem355787 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) : (term56 A B lt2 f P g) = (term300 A B lt2 f P g).
Proof. exact (MK_COMB (@lem355786 A) (@lem355785 A B lt2 f P g)). Qed.
Lemma lem355788 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) : (term244 A B lt2 f P) = (term301 A B lt2 f P).
Proof. exact (fun_ext (fun g : A -> B => @lem355787 A B lt2 f P g)). Qed.
Lemma lem355789 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem355790 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) : (term54 A B lt2 f P) = (term302 A B lt2 f P).
Proof. exact (MK_COMB (@lem355789 A B) (@lem355788 A B lt2 f P)). Qed.
Lemma lem355791 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : (term245 A B lt2 P) = (term303 A B lt2 P).
Proof. exact (fun_ext (fun f : A -> B => @lem355790 A B lt2 f P)). Qed.
Lemma lem355792 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem355793 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : (term7 A B lt2 P) = (term304 A B lt2 P).
Proof. exact (MK_COMB (@lem355792 A B) (@lem355791 A B lt2 P)). Qed.
Lemma lem355807 {A : Type'} (P : Prop) (Q : A -> Prop) : (term305 A P Q) = (term306 A P Q).
Proof. exact (EQ_MP (@lem18941 A P Q) (@lem18940 A P Q)). Qed.
Lemma lem355808 {B : Type'} (P : Prop) (Q : B -> Prop) : (term305 B P Q) = (term306 B P Q).
Proof. exact (@lem355807 B P Q). Qed.
Lemma lem355809 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : (term307 A B lt2 f P g x) = (term308 A B lt2 f P g x).
Proof. exact (@lem355808 B (term291 A B lt2 x f g) (term309 A B f P g x)). Qed.
Lemma lem355810 {A B : Type'} (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) (y : B) : (term310 A B f P g x y) = (term292 A B f P g x y).
Proof. exact (eq_refl (term310 A B f P g x y)). Qed.
Lemma lem355811 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) : (term294 A B lt2 x f g) = (term294 A B lt2 x f g).
Proof. exact (eq_refl (term294 A B lt2 x f g)). Qed.
Lemma lem355812 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) (y : B) : (term311 A B lt2 f P g x y) = (term296 A B lt2 f P g x y).
Proof. exact (MK_COMB (@lem355811 A B lt2 x f g) (@lem355810 A B f P g x y)). Qed.
Lemma lem355813 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : (term312 A B lt2 f P g x) = (term297 A B lt2 f P g x).
Proof. exact (fun_ext (fun y : B => @lem355812 A B lt2 f P g x y)). Qed.
Lemma lem355814 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem355815 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : (term307 A B lt2 f P g x) = (term298 A B lt2 f P g x).
Proof. exact (MK_COMB (@lem355814 B) (@lem355813 A B lt2 f P g x)). Qed.
Lemma lem355816 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem355817 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : (term313 A B lt2 f P g x) = (term314 A B lt2 f P g x).
Proof. exact (MK_COMB (@lem355816) (@lem355815 A B lt2 f P g x)). Qed.
Lemma lem355818 {A B : Type'} (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) (y : B) : (term310 A B f P g x y) = (term292 A B f P g x y).
Proof. exact (eq_refl (term310 A B f P g x y)). Qed.
Lemma lem355819 {A B : Type'} (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : (term315 A B f P g x) = (term309 A B f P g x).
Proof. exact (fun_ext (fun y : B => @lem355818 A B f P g x y)). Qed.
Lemma lem355820 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem355821 {A B : Type'} (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : (term316 A B f P g x) = (term317 A B f P g x).
Proof. exact (MK_COMB (@lem355820 B) (@lem355819 A B f P g x)). Qed.
Lemma lem355822 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) : (term294 A B lt2 x f g) = (term294 A B lt2 x f g).
Proof. exact (eq_refl (term294 A B lt2 x f g)). Qed.
Lemma lem355823 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : (term308 A B lt2 f P g x) = (term318 A B lt2 f P g x).
Proof. exact (MK_COMB (@lem355822 A B lt2 x f g) (@lem355821 A B f P g x)). Qed.
Lemma lem355824 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : ((term307 A B lt2 f P g x) = (term308 A B lt2 f P g x)) = ((term298 A B lt2 f P g x) = (term318 A B lt2 f P g x)).
Proof. exact (MK_COMB (@lem355817 A B lt2 f P g x) (@lem355823 A B lt2 f P g x)). Qed.
Lemma lem355825 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : (term298 A B lt2 f P g x) = (term318 A B lt2 f P g x).
Proof. exact (EQ_MP (@lem355824 A B lt2 f P g x) (@lem355809 A B lt2 f P g x)). Qed.
Lemma lem355875 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term319 A P Q) = (term320 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem355876 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term319 B P Q) = (term320 B P Q).
Proof. exact (@lem355875 B P Q). Qed.
Lemma lem355877 {A B : Type'} (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : (term321 A B f P g x) = (term322 A B f P g x).
Proof. exact (@lem355876 B (term323 A B f P g x) (term324 A B f P g x)). Qed.
Lemma lem355878 {A B : Type'} (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) (y : B) : (term325 A B f P g x y) = (term326 A B f P g x y).
Proof. exact (eq_refl (term325 A B f P g x y)). Qed.
Lemma lem355879 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem355880 {A B : Type'} (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) (y : B) : (term327 A B f P g x y) = (term328 A B f P g x y).
Proof. exact (MK_COMB (@lem355879) (@lem355878 A B f P g x y)). Qed.
Lemma lem355881 {A B : Type'} (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) (y : B) : (term329 A B f P g x y) = (term330 A B f P g x y).
Proof. exact (eq_refl (term329 A B f P g x y)). Qed.
Lemma lem355882 {A B : Type'} (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) (y : B) : (term331 A B f P g x y) = (term292 A B f P g x y).
Proof. exact (MK_COMB (@lem355880 A B f P g x y) (@lem355881 A B f P g x y)). Qed.
Lemma lem355883 {A B : Type'} (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : (term332 A B f P g x) = (term309 A B f P g x).
Proof. exact (fun_ext (fun y : B => @lem355882 A B f P g x y)). Qed.
Lemma lem355884 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem355885 {A B : Type'} (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : (term321 A B f P g x) = (term317 A B f P g x).
Proof. exact (MK_COMB (@lem355884 B) (@lem355883 A B f P g x)). Qed.
Lemma lem355886 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem355887 {A B : Type'} (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : (term333 A B f P g x) = (term334 A B f P g x).
Proof. exact (MK_COMB (@lem355886) (@lem355885 A B f P g x)). Qed.
Lemma lem355888 {A B : Type'} (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) (y : B) : (term325 A B f P g x y) = (term326 A B f P g x y).
Proof. exact (eq_refl (term325 A B f P g x y)). Qed.
Lemma lem355889 {A B : Type'} (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : (term335 A B f P g x) = (term323 A B f P g x).
Proof. exact (fun_ext (fun y : B => @lem355888 A B f P g x y)). Qed.
Lemma lem355890 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem355891 {A B : Type'} (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : (term336 A B f P g x) = (term337 A B f P g x).
Proof. exact (MK_COMB (@lem355890 B) (@lem355889 A B f P g x)). Qed.
Lemma lem355892 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem355893 {A B : Type'} (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : (term338 A B f P g x) = (term339 A B f P g x).
Proof. exact (MK_COMB (@lem355892) (@lem355891 A B f P g x)). Qed.
Lemma lem355894 {A B : Type'} (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) (y : B) : (term329 A B f P g x y) = (term330 A B f P g x y).
Proof. exact (eq_refl (term329 A B f P g x y)). Qed.
Lemma lem355895 {A B : Type'} (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : (term340 A B f P g x) = (term324 A B f P g x).
Proof. exact (fun_ext (fun y : B => @lem355894 A B f P g x y)). Qed.
Lemma lem355896 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem355897 {A B : Type'} (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : (term341 A B f P g x) = (term342 A B f P g x).
Proof. exact (MK_COMB (@lem355896 B) (@lem355895 A B f P g x)). Qed.
Lemma lem355898 {A B : Type'} (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : (term322 A B f P g x) = (term343 A B f P g x).
Proof. exact (MK_COMB (@lem355893 A B f P g x) (@lem355897 A B f P g x)). Qed.
Lemma lem355899 {A B : Type'} (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : ((term321 A B f P g x) = (term322 A B f P g x)) = ((term317 A B f P g x) = (term343 A B f P g x)).
Proof. exact (MK_COMB (@lem355887 A B f P g x) (@lem355898 A B f P g x)). Qed.
Lemma lem355900 {A B : Type'} (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : (term317 A B f P g x) = (term343 A B f P g x).
Proof. exact (EQ_MP (@lem355899 A B f P g x) (@lem355877 A B f P g x)). Qed.
Lemma lem355997 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) : (term294 A B lt2 x f g) = (term294 A B lt2 x f g).
Proof. exact (eq_refl (term294 A B lt2 x f g)). Qed.
Lemma lem355998 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : (term318 A B lt2 f P g x) = (term344 A B lt2 f P g x).
Proof. exact (MK_COMB (@lem355997 A B lt2 x f g) (@lem355900 A B f P g x)). Qed.
Lemma lem355999 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : (term298 A B lt2 f P g x) = (term344 A B lt2 f P g x).
Proof. exact (TRANS (@lem355825 A B lt2 f P g x) (@lem355998 A B lt2 f P g x)). Qed.
Lemma lem356000 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) : (term299 A B lt2 f P g) = (term345 A B lt2 f P g).
Proof. exact (fun_ext (fun x : A => @lem355999 A B lt2 f P g x)). Qed.
Lemma lem356001 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem356002 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) : (term300 A B lt2 f P g) = (term346 A B lt2 f P g).
Proof. exact (MK_COMB (@lem356001 A) (@lem356000 A B lt2 f P g)). Qed.
Lemma lem356051 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) : (term301 A B lt2 f P) = (term347 A B lt2 f P).
Proof. exact (fun_ext (fun g : A -> B => @lem356002 A B lt2 f P g)). Qed.
Lemma lem356052 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem356053 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) : (term302 A B lt2 f P) = (term348 A B lt2 f P).
Proof. exact (MK_COMB (@lem356052 A B) (@lem356051 A B lt2 f P)). Qed.
Lemma lem356058 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : (term303 A B lt2 P) = (term349 A B lt2 P).
Proof. exact (fun_ext (fun f : A -> B => @lem356053 A B lt2 f P)). Qed.
Lemma lem356059 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem356060 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : (term304 A B lt2 P) = (term350 A B lt2 P).
Proof. exact (MK_COMB (@lem356059 A B) (@lem356058 A B lt2 P)). Qed.
Lemma lem356066 {A : Type'} (P : A -> Prop) (Q : Prop) : (term351 A P Q) = (term352 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem356067 {A : Type'} (P : A -> Prop) (Q : Prop) : (term351 A P Q) = (term352 A P Q).
Proof. exact (@lem356066 A P Q). Qed.
Lemma lem356068 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : (term353 A B lt2 f P g x) = (term354 A B lt2 f P g x).
Proof. exact (@lem356067 A (term290 A B lt2 x f g) (term343 A B f P g x)). Qed.
Lemma lem356069 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) (z : A) : (term355 A B lt2 x f g z) = (term283 A B lt2 x f g z).
Proof. exact (eq_refl (term355 A B lt2 x f g z)). Qed.
Lemma lem356070 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) : (term356 A B lt2 x f g) = (term290 A B lt2 x f g).
Proof. exact (fun_ext (fun z : A => @lem356069 A B lt2 x f g z)). Qed.
Lemma lem356071 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem356072 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) : (term357 A B lt2 x f g) = (term291 A B lt2 x f g).
Proof. exact (MK_COMB (@lem356071 A) (@lem356070 A B lt2 x f g)). Qed.
Lemma lem356073 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem356074 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) : (term358 A B lt2 x f g) = (term294 A B lt2 x f g).
Proof. exact (MK_COMB (@lem356073) (@lem356072 A B lt2 x f g)). Qed.
Lemma lem356075 {A B : Type'} (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : (term343 A B f P g x) = (term343 A B f P g x).
Proof. exact (eq_refl (term343 A B f P g x)). Qed.
Lemma lem356076 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : (term353 A B lt2 f P g x) = (term344 A B lt2 f P g x).
Proof. exact (MK_COMB (@lem356074 A B lt2 x f g) (@lem356075 A B f P g x)). Qed.
Lemma lem356077 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem356078 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : (term359 A B lt2 f P g x) = (term360 A B lt2 f P g x).
Proof. exact (MK_COMB (@lem356077) (@lem356076 A B lt2 f P g x)). Qed.
Lemma lem356079 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) (z : A) : (term355 A B lt2 x f g z) = (term283 A B lt2 x f g z).
Proof. exact (eq_refl (term355 A B lt2 x f g z)). Qed.
Lemma lem356080 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem356081 {A B : Type'} (lt2 : type1402 A) (x : A) (f : A -> B) (g : A -> B) (z : A) : (term361 A B lt2 x f g z) = (term362 A B lt2 x f g z).
Proof. exact (MK_COMB (@lem356080) (@lem356079 A B lt2 x f g z)). Qed.
Lemma lem356082 {A B : Type'} (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : (term343 A B f P g x) = (term343 A B f P g x).
Proof. exact (eq_refl (term343 A B f P g x)). Qed.
Lemma lem356083 {A B : Type'} (lt2 : type1402 A) (z : A) (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : (term363 A B lt2 z f P g x) = (term364 A B lt2 z f P g x).
Proof. exact (MK_COMB (@lem356081 A B lt2 x f g z) (@lem356082 A B f P g x)). Qed.
Lemma lem356084 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : (term365 A B lt2 f P g x) = (term366 A B lt2 f P g x).
Proof. exact (fun_ext (fun z : A => @lem356083 A B lt2 z f P g x)). Qed.
Lemma lem356085 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem356086 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : (term354 A B lt2 f P g x) = (term367 A B lt2 f P g x).
Proof. exact (MK_COMB (@lem356085 A) (@lem356084 A B lt2 f P g x)). Qed.
Lemma lem356087 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : ((term353 A B lt2 f P g x) = (term354 A B lt2 f P g x)) = ((term344 A B lt2 f P g x) = (term367 A B lt2 f P g x)).
Proof. exact (MK_COMB (@lem356078 A B lt2 f P g x) (@lem356086 A B lt2 f P g x)). Qed.
Lemma lem356088 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : (term344 A B lt2 f P g x) = (term367 A B lt2 f P g x).
Proof. exact (EQ_MP (@lem356087 A B lt2 f P g x) (@lem356068 A B lt2 f P g x)). Qed.
Lemma lem356089 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) : (term345 A B lt2 f P g) = (term368 A B lt2 f P g).
Proof. exact (fun_ext (fun x : A => @lem356088 A B lt2 f P g x)). Qed.
Lemma lem356090 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem356091 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) : (term346 A B lt2 f P g) = (term369 A B lt2 f P g).
Proof. exact (MK_COMB (@lem356090 A) (@lem356089 A B lt2 f P g)). Qed.
Lemma lem356093 {A B : Type'} (P : type1413 A B) : (term370 A B P) = (term371 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem356094 {A : Type'} (P : type1402 A) : (term372 A P) = (term373 A P).
Proof. exact (@lem356093 A A P). Qed.
Lemma lem356095 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) : (term374 A B lt2 f P g) = (term375 A B lt2 f P g).
Proof. exact (@lem356094 A (term376 A B lt2 f P g)). Qed.
Lemma lem356096 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : (term377 A B lt2 f P g x) = (term366 A B lt2 f P g x).
Proof. exact (eq_refl (term377 A B lt2 f P g x)). Qed.
Lemma lem356097 {A : Type'} (z : A) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem356098 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) (z : A) : (term378 A B lt2 f P g x z) = (term379 A B lt2 f P g x z).
Proof. exact (MK_COMB (@lem356096 A B lt2 f P g x) (@lem356097 A z)). Qed.
Lemma lem356099 {A B : Type'} (lt2 : type1402 A) (z : A) (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : (term379 A B lt2 f P g x z) = (term364 A B lt2 z f P g x).
Proof. exact (eq_refl (term379 A B lt2 f P g x z)). Qed.
Lemma lem356100 {A B : Type'} (lt2 : type1402 A) (z : A) (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : (term378 A B lt2 f P g x z) = (term364 A B lt2 z f P g x).
Proof. exact (TRANS (@lem356098 A B lt2 f P g x z) (@lem356099 A B lt2 z f P g x)). Qed.
Lemma lem356101 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : (term380 A B lt2 f P g x) = (term366 A B lt2 f P g x).
Proof. exact (fun_ext (fun z : A => @lem356100 A B lt2 z f P g x)). Qed.
Lemma lem356102 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem356103 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : (term381 A B lt2 f P g x) = (term367 A B lt2 f P g x).
Proof. exact (MK_COMB (@lem356102 A) (@lem356101 A B lt2 f P g x)). Qed.
Lemma lem356104 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) : (term382 A B lt2 f P g) = (term368 A B lt2 f P g).
Proof. exact (fun_ext (fun x : A => @lem356103 A B lt2 f P g x)). Qed.
Lemma lem356105 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem356106 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) : (term374 A B lt2 f P g) = (term369 A B lt2 f P g).
Proof. exact (MK_COMB (@lem356105 A) (@lem356104 A B lt2 f P g)). Qed.
Lemma lem356107 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem356108 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) : (term383 A B lt2 f P g) = (term384 A B lt2 f P g).
Proof. exact (MK_COMB (@lem356107) (@lem356106 A B lt2 f P g)). Qed.
Lemma lem356109 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : (term377 A B lt2 f P g x) = (term366 A B lt2 f P g x).
Proof. exact (eq_refl (term377 A B lt2 f P g x)). Qed.
Lemma lem356110 {A : Type'} (z : A -> A) (x : A) : (z x) = (z x).
Proof. exact (eq_refl (z x)). Qed.
Lemma lem356111 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) (z : A -> A) (x : A) : (term385 A B lt2 f P g z x) = (term386 A B lt2 f P g z x).
Proof. exact (MK_COMB (@lem356109 A B lt2 f P g x) (@lem356110 A z x)). Qed.
Lemma lem356112 {A B : Type'} (lt2 : type1402 A) (z : A -> A) (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : (term386 A B lt2 f P g z x) = (term387 A B lt2 z f P g x).
Proof. exact (eq_refl (term386 A B lt2 f P g z x)). Qed.
Lemma lem356113 {A B : Type'} (lt2 : type1402 A) (z : A -> A) (f : A -> B) (P : type547 A B) (g : A -> B) (x : A) : (term385 A B lt2 f P g z x) = (term387 A B lt2 z f P g x).
Proof. exact (TRANS (@lem356111 A B lt2 f P g z x) (@lem356112 A B lt2 z f P g x)). Qed.
Lemma lem356114 {A B : Type'} (lt2 : type1402 A) (z : A -> A) (f : A -> B) (P : type547 A B) (g : A -> B) : (term388 A B lt2 f P g z) = (term389 A B lt2 z f P g).
Proof. exact (fun_ext (fun x : A => @lem356113 A B lt2 z f P g x)). Qed.
Lemma lem356115 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem356116 {A B : Type'} (lt2 : type1402 A) (z : A -> A) (f : A -> B) (P : type547 A B) (g : A -> B) : (term390 A B lt2 f P g z) = (term391 A B lt2 z f P g).
Proof. exact (MK_COMB (@lem356115 A) (@lem356114 A B lt2 z f P g)). Qed.
Lemma lem356117 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) : (term392 A B lt2 f P g) = (term393 A B lt2 f P g).
Proof. exact (fun_ext (fun z : A -> A => @lem356116 A B lt2 z f P g)). Qed.
Lemma lem356118 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem356119 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) : (term375 A B lt2 f P g) = (term394 A B lt2 f P g).
Proof. exact (MK_COMB (@lem356118 A) (@lem356117 A B lt2 f P g)). Qed.
Lemma lem356120 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) : ((term374 A B lt2 f P g) = (term375 A B lt2 f P g)) = ((term369 A B lt2 f P g) = (term394 A B lt2 f P g)).
Proof. exact (MK_COMB (@lem356108 A B lt2 f P g) (@lem356119 A B lt2 f P g)). Qed.
Lemma lem356121 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) : (term369 A B lt2 f P g) = (term394 A B lt2 f P g).
Proof. exact (EQ_MP (@lem356120 A B lt2 f P g) (@lem356095 A B lt2 f P g)). Qed.
Lemma lem356122 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) : (term346 A B lt2 f P g) = (term394 A B lt2 f P g).
Proof. exact (TRANS (@lem356091 A B lt2 f P g) (@lem356121 A B lt2 f P g)). Qed.
Lemma lem356123 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) : (term347 A B lt2 f P) = (term395 A B lt2 f P).
Proof. exact (fun_ext (fun g : A -> B => @lem356122 A B lt2 f P g)). Qed.
Lemma lem356124 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem356125 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) : (term348 A B lt2 f P) = (term396 A B lt2 f P).
Proof. exact (MK_COMB (@lem356124 A B) (@lem356123 A B lt2 f P)). Qed.
Lemma lem356127 {A B : Type'} (P : type1413 A B) : (term370 A B P) = (term371 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem356128 {A B : Type'} (P : type513 A B) : (term397 A B P) = (term398 A B P).
Proof. exact (@lem356127 (A -> B) (A -> A) P). Qed.
Lemma lem356129 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) : (term399 A B lt2 f P) = (term400 A B lt2 f P).
Proof. exact (@lem356128 A B (term401 A B lt2 f P)). Qed.
Lemma lem356130 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) : (term402 A B lt2 f P g) = (term393 A B lt2 f P g).
Proof. exact (eq_refl (term402 A B lt2 f P g)). Qed.
Lemma lem356131 {A : Type'} (z : A -> A) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem356132 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) (z : A -> A) : (term403 A B lt2 f P g z) = (term404 A B lt2 f P g z).
Proof. exact (MK_COMB (@lem356130 A B lt2 f P g) (@lem356131 A z)). Qed.
Lemma lem356133 {A B : Type'} (lt2 : type1402 A) (z : A -> A) (f : A -> B) (P : type547 A B) (g : A -> B) : (term404 A B lt2 f P g z) = (term391 A B lt2 z f P g).
Proof. exact (eq_refl (term404 A B lt2 f P g z)). Qed.
Lemma lem356134 {A B : Type'} (lt2 : type1402 A) (z : A -> A) (f : A -> B) (P : type547 A B) (g : A -> B) : (term403 A B lt2 f P g z) = (term391 A B lt2 z f P g).
Proof. exact (TRANS (@lem356132 A B lt2 f P g z) (@lem356133 A B lt2 z f P g)). Qed.
Lemma lem356135 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) : (term405 A B lt2 f P g) = (term393 A B lt2 f P g).
Proof. exact (fun_ext (fun z : A -> A => @lem356134 A B lt2 z f P g)). Qed.
Lemma lem356136 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem356137 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) : (term406 A B lt2 f P g) = (term394 A B lt2 f P g).
Proof. exact (MK_COMB (@lem356136 A) (@lem356135 A B lt2 f P g)). Qed.
Lemma lem356138 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) : (term407 A B lt2 f P) = (term395 A B lt2 f P).
Proof. exact (fun_ext (fun g : A -> B => @lem356137 A B lt2 f P g)). Qed.
Lemma lem356139 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem356140 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) : (term399 A B lt2 f P) = (term396 A B lt2 f P).
Proof. exact (MK_COMB (@lem356139 A B) (@lem356138 A B lt2 f P)). Qed.
Lemma lem356141 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem356142 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) : (term408 A B lt2 f P) = (term409 A B lt2 f P).
Proof. exact (MK_COMB (@lem356141) (@lem356140 A B lt2 f P)). Qed.
Lemma lem356143 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (g : A -> B) : (term402 A B lt2 f P g) = (term393 A B lt2 f P g).
Proof. exact (eq_refl (term402 A B lt2 f P g)). Qed.
Lemma lem356144 {A B : Type'} (z : type548 A B) (g : A -> B) : (z g) = (z g).
Proof. exact (eq_refl (z g)). Qed.
Lemma lem356145 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (z : type548 A B) (g : A -> B) : (term410 A B lt2 f P z g) = (term411 A B lt2 f P z g).
Proof. exact (MK_COMB (@lem356143 A B lt2 f P g) (@lem356144 A B z g)). Qed.
Lemma lem356146 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (f : A -> B) (P : type547 A B) (g : A -> B) : (term411 A B lt2 f P z g) = (term412 A B lt2 z f P g).
Proof. exact (eq_refl (term411 A B lt2 f P z g)). Qed.
Lemma lem356147 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (f : A -> B) (P : type547 A B) (g : A -> B) : (term410 A B lt2 f P z g) = (term412 A B lt2 z f P g).
Proof. exact (TRANS (@lem356145 A B lt2 f P z g) (@lem356146 A B lt2 z f P g)). Qed.
Lemma lem356148 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (f : A -> B) (P : type547 A B) : (term413 A B lt2 f P z) = (term414 A B lt2 z f P).
Proof. exact (fun_ext (fun g : A -> B => @lem356147 A B lt2 z f P g)). Qed.
Lemma lem356149 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem356150 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (f : A -> B) (P : type547 A B) : (term415 A B lt2 f P z) = (term416 A B lt2 z f P).
Proof. exact (MK_COMB (@lem356149 A B) (@lem356148 A B lt2 z f P)). Qed.
Lemma lem356151 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) : (term417 A B lt2 f P) = (term418 A B lt2 f P).
Proof. exact (fun_ext (fun z : type548 A B => @lem356150 A B lt2 z f P)). Qed.
Lemma lem356152 {A B : Type'} : (@ex ((A -> B) -> A -> A)) = (@ex ((A -> B) -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> A -> A))). Qed.
Lemma lem356153 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) : (term400 A B lt2 f P) = (term419 A B lt2 f P).
Proof. exact (MK_COMB (@lem356152 A B) (@lem356151 A B lt2 f P)). Qed.
Lemma lem356154 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) : ((term399 A B lt2 f P) = (term400 A B lt2 f P)) = ((term396 A B lt2 f P) = (term419 A B lt2 f P)).
Proof. exact (MK_COMB (@lem356142 A B lt2 f P) (@lem356153 A B lt2 f P)). Qed.
Lemma lem356155 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) : (term396 A B lt2 f P) = (term419 A B lt2 f P).
Proof. exact (EQ_MP (@lem356154 A B lt2 f P) (@lem356129 A B lt2 f P)). Qed.
Lemma lem356156 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) : (term348 A B lt2 f P) = (term419 A B lt2 f P).
Proof. exact (TRANS (@lem356125 A B lt2 f P) (@lem356155 A B lt2 f P)). Qed.
Lemma lem356157 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : (term349 A B lt2 P) = (term420 A B lt2 P).
Proof. exact (fun_ext (fun f : A -> B => @lem356156 A B lt2 f P)). Qed.
Lemma lem356158 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem356159 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : (term350 A B lt2 P) = (term421 A B lt2 P).
Proof. exact (MK_COMB (@lem356158 A B) (@lem356157 A B lt2 P)). Qed.
Lemma lem356161 {A B : Type'} (P : type1413 A B) : (term370 A B P) = (term371 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem356162 {A B : Type'} (P : type493 A B) : (term422 A B P) = (term423 A B P).
Proof. exact (@lem356161 (A -> B) (type548 A B) P). Qed.
Lemma lem356163 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : (term424 A B lt2 P) = (term425 A B lt2 P).
Proof. exact (@lem356162 A B (term426 A B lt2 P)). Qed.
Lemma lem356164 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) : (term427 A B lt2 P f) = (term418 A B lt2 f P).
Proof. exact (eq_refl (term427 A B lt2 P f)). Qed.
Lemma lem356165 {A B : Type'} (z : type548 A B) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem356166 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) (z : type548 A B) : (term428 A B lt2 P f z) = (term429 A B lt2 f P z).
Proof. exact (MK_COMB (@lem356164 A B lt2 f P) (@lem356165 A B z)). Qed.
Lemma lem356167 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (f : A -> B) (P : type547 A B) : (term429 A B lt2 f P z) = (term416 A B lt2 z f P).
Proof. exact (eq_refl (term429 A B lt2 f P z)). Qed.
Lemma lem356168 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (f : A -> B) (P : type547 A B) : (term428 A B lt2 P f z) = (term416 A B lt2 z f P).
Proof. exact (TRANS (@lem356166 A B lt2 f P z) (@lem356167 A B lt2 z f P)). Qed.
Lemma lem356169 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) : (term430 A B lt2 P f) = (term418 A B lt2 f P).
Proof. exact (fun_ext (fun z : type548 A B => @lem356168 A B lt2 z f P)). Qed.
Lemma lem356170 {A B : Type'} : (@ex ((A -> B) -> A -> A)) = (@ex ((A -> B) -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> A -> A))). Qed.
Lemma lem356171 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) : (term431 A B lt2 P f) = (term419 A B lt2 f P).
Proof. exact (MK_COMB (@lem356170 A B) (@lem356169 A B lt2 f P)). Qed.
Lemma lem356172 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : (term432 A B lt2 P) = (term420 A B lt2 P).
Proof. exact (fun_ext (fun f : A -> B => @lem356171 A B lt2 f P)). Qed.
Lemma lem356173 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem356174 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : (term424 A B lt2 P) = (term421 A B lt2 P).
Proof. exact (MK_COMB (@lem356173 A B) (@lem356172 A B lt2 P)). Qed.
Lemma lem356175 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem356176 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : (term433 A B lt2 P) = (term434 A B lt2 P).
Proof. exact (MK_COMB (@lem356175) (@lem356174 A B lt2 P)). Qed.
Lemma lem356177 {A B : Type'} (lt2 : type1402 A) (f : A -> B) (P : type547 A B) : (term427 A B lt2 P f) = (term418 A B lt2 f P).
Proof. exact (eq_refl (term427 A B lt2 P f)). Qed.
Lemma lem356178 {A B : Type'} (z : type515 A B) (f : A -> B) : (z f) = (z f).
Proof. exact (eq_refl (z f)). Qed.
Lemma lem356179 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (z : type515 A B) (f : A -> B) : (term435 A B lt2 P z f) = (term436 A B lt2 P z f).
Proof. exact (MK_COMB (@lem356177 A B lt2 f P) (@lem356178 A B z f)). Qed.
Lemma lem356180 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (f : A -> B) (P : type547 A B) : (term436 A B lt2 P z f) = (term437 A B lt2 z f P).
Proof. exact (eq_refl (term436 A B lt2 P z f)). Qed.
Lemma lem356181 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (f : A -> B) (P : type547 A B) : (term435 A B lt2 P z f) = (term437 A B lt2 z f P).
Proof. exact (TRANS (@lem356179 A B lt2 P z f) (@lem356180 A B lt2 z f P)). Qed.
Lemma lem356182 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (P : type547 A B) : (term438 A B lt2 P z) = (term439 A B lt2 z P).
Proof. exact (fun_ext (fun f : A -> B => @lem356181 A B lt2 z f P)). Qed.
Lemma lem356183 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem356184 {A B : Type'} (lt2 : type1402 A) (z : type515 A B) (P : type547 A B) : (term440 A B lt2 P z) = (term441 A B lt2 z P).
Proof. exact (MK_COMB (@lem356183 A B) (@lem356182 A B lt2 z P)). Qed.
Lemma lem356185 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : (term442 A B lt2 P) = (term443 A B lt2 P).
Proof. exact (fun_ext (fun z : type515 A B => @lem356184 A B lt2 z P)). Qed.
Lemma lem356186 {A B : Type'} : (@ex ((A -> B) -> (A -> B) -> A -> A)) = (@ex ((A -> B) -> (A -> B) -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> B) -> A -> A))). Qed.
Lemma lem356187 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : (term425 A B lt2 P) = (term444 A B lt2 P).
Proof. exact (MK_COMB (@lem356186 A B) (@lem356185 A B lt2 P)). Qed.
Lemma lem356188 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : ((term424 A B lt2 P) = (term425 A B lt2 P)) = ((term421 A B lt2 P) = (term444 A B lt2 P)).
Proof. exact (MK_COMB (@lem356176 A B lt2 P) (@lem356187 A B lt2 P)). Qed.
Lemma lem356189 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : (term421 A B lt2 P) = (term444 A B lt2 P).
Proof. exact (EQ_MP (@lem356188 A B lt2 P) (@lem356163 A B lt2 P)). Qed.
Lemma lem356190 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : (term350 A B lt2 P) = (term444 A B lt2 P).
Proof. exact (TRANS (@lem356159 A B lt2 P) (@lem356189 A B lt2 P)). Qed.
Lemma lem356191 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : (term304 A B lt2 P) = (term444 A B lt2 P).
Proof. exact (TRANS (@lem356060 A B lt2 P) (@lem356190 A B lt2 P)). Qed.
Lemma lem356192 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : (term7 A B lt2 P) = (term444 A B lt2 P).
Proof. exact (TRANS (@lem355793 A B lt2 P) (@lem356191 A B lt2 P)). Qed.
Lemma lem356193 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (h1 : term7 A B lt2 P) : term444 A B lt2 P.
Proof. exact (EQ_MP (@lem356192 A B lt2 P) (@lem355582 A B lt2 P h1)). Qed.
Lemma lem356200 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (z : A) : (term445 A B lt2 x P f z) = (term446 A B lt2 x P f z).
Proof. exact (@lem17362 (lt2 z x) (term99 A B P f z)). Qed.
Lemma lem356201 {A : Type'} (P : A -> Prop) : (term284 A P) = (term285 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem356202 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) : (term447 A B lt2 x P f) = (term448 A B lt2 x P f).
Proof. exact (@lem356201 A (term235 A B lt2 x P f)). Qed.
Lemma lem356203 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (z : A) : (term449 A B lt2 x P f z) = (term234 A B lt2 x P f z).
Proof. exact (eq_refl (term449 A B lt2 x P f z)). Qed.
Lemma lem356204 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem356205 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (z : A) : (term450 A B lt2 x P f z) = (term445 A B lt2 x P f z).
Proof. exact (MK_COMB (@lem356204) (@lem356203 A B lt2 x P f z)). Qed.
Lemma lem356206 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (z : A) : (term450 A B lt2 x P f z) = (term446 A B lt2 x P f z).
Proof. exact (TRANS (@lem356205 A B lt2 x P f z) (@lem356200 A B lt2 x P f z)). Qed.
Lemma lem356207 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) : (term451 A B lt2 x P f) = (term452 A B lt2 x P f).
Proof. exact (fun_ext (fun z : A => @lem356206 A B lt2 x P f z)). Qed.
Lemma lem356208 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem356209 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) : (term448 A B lt2 x P f) = (term453 A B lt2 x P f).
Proof. exact (MK_COMB (@lem356208 A) (@lem356207 A B lt2 x P f)). Qed.
Lemma lem356210 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) : (term447 A B lt2 x P f) = (term453 A B lt2 x P f).
Proof. exact (TRANS (@lem356202 A B lt2 x P f) (@lem356209 A B lt2 x P f)). Qed.
Lemma lem356211 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (y : B) : (P f x y) = (P f x y).
Proof. exact (eq_refl (P f x y)). Qed.
Lemma lem356212 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term69 A B P f x) = (term69 A B P f x).
Proof. exact (fun_ext (fun y : B => @lem356211 A B P f x y)). Qed.
Lemma lem356213 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem356214 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term106 A B P f x) = (term106 A B P f x).
Proof. exact (MK_COMB (@lem356213 B) (@lem356212 A B P f x)). Qed.
Lemma lem356215 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem356216 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) : (term454 A B lt2 x P f) = (term455 A B lt2 x P f).
Proof. exact (MK_COMB (@lem356215) (@lem356210 A B lt2 x P f)). Qed.
Lemma lem356217 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (x : A) : (term456 A B lt2 P f x) = (term457 A B lt2 P f x).
Proof. exact (MK_COMB (@lem356216 A B lt2 x P f) (@lem356214 A B P f x)). Qed.
Lemma lem356218 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (x : A) : (term238 A B lt2 P f x) = (term456 A B lt2 P f x).
Proof. exact (@lem17265 (term236 A B lt2 x P f) (term106 A B P f x)). Qed.
Lemma lem356219 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (x : A) : (term238 A B lt2 P f x) = (term457 A B lt2 P f x).
Proof. exact (TRANS (@lem356218 A B lt2 P f x) (@lem356217 A B lt2 P f x)). Qed.
Lemma lem356220 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term239 A B lt2 P f) = (term458 A B lt2 P f).
Proof. exact (fun_ext (fun x : A => @lem356219 A B lt2 P f x)). Qed.
Lemma lem356221 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem356222 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term240 A B lt2 P f) = (term459 A B lt2 P f).
Proof. exact (MK_COMB (@lem356221 A) (@lem356220 A B lt2 P f)). Qed.
Lemma lem356223 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : (term241 A B lt2 P) = (term460 A B lt2 P).
Proof. exact (fun_ext (fun f : A -> B => @lem356222 A B lt2 P f)). Qed.
Lemma lem356224 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem356225 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : (term6 A B lt2 P) = (term461 A B lt2 P).
Proof. exact (MK_COMB (@lem356224 A B) (@lem356223 A B lt2 P)). Qed.
Lemma lem356334 {A : Type'} (P : A -> Prop) (Q : Prop) : (term351 A P Q) = (term352 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem356335 {A : Type'} (P : A -> Prop) (Q : Prop) : (term351 A P Q) = (term352 A P Q).
Proof. exact (@lem356334 A P Q). Qed.
Lemma lem356336 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (x : A) : (term462 A B lt2 P f x) = (term463 A B lt2 P f x).
Proof. exact (@lem356335 A (term452 A B lt2 x P f) (term106 A B P f x)). Qed.
Lemma lem356337 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (z : A) : (term464 A B lt2 x P f z) = (term446 A B lt2 x P f z).
Proof. exact (eq_refl (term464 A B lt2 x P f z)). Qed.
Lemma lem356338 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) : (term465 A B lt2 x P f) = (term452 A B lt2 x P f).
Proof. exact (fun_ext (fun z : A => @lem356337 A B lt2 x P f z)). Qed.
Lemma lem356339 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem356340 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) : (term466 A B lt2 x P f) = (term453 A B lt2 x P f).
Proof. exact (MK_COMB (@lem356339 A) (@lem356338 A B lt2 x P f)). Qed.
Lemma lem356341 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem356342 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) : (term467 A B lt2 x P f) = (term455 A B lt2 x P f).
Proof. exact (MK_COMB (@lem356341) (@lem356340 A B lt2 x P f)). Qed.
Lemma lem356343 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term106 A B P f x) = (term106 A B P f x).
Proof. exact (eq_refl (term106 A B P f x)). Qed.
Lemma lem356344 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (x : A) : (term462 A B lt2 P f x) = (term457 A B lt2 P f x).
Proof. exact (MK_COMB (@lem356342 A B lt2 x P f) (@lem356343 A B P f x)). Qed.
Lemma lem356345 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem356346 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (x : A) : (term468 A B lt2 P f x) = (term469 A B lt2 P f x).
Proof. exact (MK_COMB (@lem356345) (@lem356344 A B lt2 P f x)). Qed.
Lemma lem356347 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (z : A) : (term464 A B lt2 x P f z) = (term446 A B lt2 x P f z).
Proof. exact (eq_refl (term464 A B lt2 x P f z)). Qed.
Lemma lem356348 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem356349 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (z : A) : (term470 A B lt2 x P f z) = (term471 A B lt2 x P f z).
Proof. exact (MK_COMB (@lem356348) (@lem356347 A B lt2 x P f z)). Qed.
Lemma lem356350 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term106 A B P f x) = (term106 A B P f x).
Proof. exact (eq_refl (term106 A B P f x)). Qed.
Lemma lem356351 {A B : Type'} (lt2 : type1402 A) (z : A) (P : type547 A B) (f : A -> B) (x : A) : (term472 A B lt2 z P f x) = (term473 A B lt2 z P f x).
Proof. exact (MK_COMB (@lem356349 A B lt2 x P f z) (@lem356350 A B P f x)). Qed.
Lemma lem356352 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (x : A) : (term474 A B lt2 P f x) = (term475 A B lt2 P f x).
Proof. exact (fun_ext (fun z : A => @lem356351 A B lt2 z P f x)). Qed.
Lemma lem356353 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem356354 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (x : A) : (term463 A B lt2 P f x) = (term476 A B lt2 P f x).
Proof. exact (MK_COMB (@lem356353 A) (@lem356352 A B lt2 P f x)). Qed.
Lemma lem356355 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (x : A) : ((term462 A B lt2 P f x) = (term463 A B lt2 P f x)) = ((term457 A B lt2 P f x) = (term476 A B lt2 P f x)).
Proof. exact (MK_COMB (@lem356346 A B lt2 P f x) (@lem356354 A B lt2 P f x)). Qed.
Lemma lem356356 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (x : A) : (term457 A B lt2 P f x) = (term476 A B lt2 P f x).
Proof. exact (EQ_MP (@lem356355 A B lt2 P f x) (@lem356336 A B lt2 P f x)). Qed.
Lemma lem356358 {A : Type'} (P : Prop) (Q : A -> Prop) : (term477 A P Q) = (term478 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem356359 {B : Type'} (P : Prop) (Q : B -> Prop) : (term477 B P Q) = (term478 B P Q).
Proof. exact (@lem356358 B P Q). Qed.
Lemma lem356360 {A B : Type'} (lt2 : type1402 A) (z : A) (P : type547 A B) (f : A -> B) (x : A) : (term479 A B lt2 z P f x) = (term480 A B lt2 z P f x).
Proof. exact (@lem356359 B (term446 A B lt2 x P f z) (term69 A B P f x)). Qed.
Lemma lem356361 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (y : B) : (term145 A B P f x y) = (P f x y).
Proof. exact (eq_refl (term145 A B P f x y)). Qed.
Lemma lem356362 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term481 A B P f x) = (term69 A B P f x).
Proof. exact (fun_ext (fun y : B => @lem356361 A B P f x y)). Qed.
Lemma lem356363 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem356364 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term482 A B P f x) = (term106 A B P f x).
Proof. exact (MK_COMB (@lem356363 B) (@lem356362 A B P f x)). Qed.
Lemma lem356365 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (z : A) : (term471 A B lt2 x P f z) = (term471 A B lt2 x P f z).
Proof. exact (eq_refl (term471 A B lt2 x P f z)). Qed.
Lemma lem356366 {A B : Type'} (lt2 : type1402 A) (z : A) (P : type547 A B) (f : A -> B) (x : A) : (term479 A B lt2 z P f x) = (term473 A B lt2 z P f x).
Proof. exact (MK_COMB (@lem356365 A B lt2 x P f z) (@lem356364 A B P f x)). Qed.
Lemma lem356367 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem356368 {A B : Type'} (lt2 : type1402 A) (z : A) (P : type547 A B) (f : A -> B) (x : A) : (term483 A B lt2 z P f x) = (term484 A B lt2 z P f x).
Proof. exact (MK_COMB (@lem356367) (@lem356366 A B lt2 z P f x)). Qed.
Lemma lem356369 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (y : B) : (term145 A B P f x y) = (P f x y).
Proof. exact (eq_refl (term145 A B P f x y)). Qed.
Lemma lem356370 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (z : A) : (term471 A B lt2 x P f z) = (term471 A B lt2 x P f z).
Proof. exact (eq_refl (term471 A B lt2 x P f z)). Qed.
Lemma lem356371 {A B : Type'} (lt2 : type1402 A) (z : A) (P : type547 A B) (f : A -> B) (x : A) (y : B) : (term485 A B lt2 z P f x y) = (term486 A B lt2 z P f x y).
Proof. exact (MK_COMB (@lem356370 A B lt2 x P f z) (@lem356369 A B P f x y)). Qed.
Lemma lem356372 {A B : Type'} (lt2 : type1402 A) (z : A) (P : type547 A B) (f : A -> B) (x : A) : (term487 A B lt2 z P f x) = (term488 A B lt2 z P f x).
Proof. exact (fun_ext (fun y : B => @lem356371 A B lt2 z P f x y)). Qed.
Lemma lem356373 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem356374 {A B : Type'} (lt2 : type1402 A) (z : A) (P : type547 A B) (f : A -> B) (x : A) : (term480 A B lt2 z P f x) = (term489 A B lt2 z P f x).
Proof. exact (MK_COMB (@lem356373 B) (@lem356372 A B lt2 z P f x)). Qed.
Lemma lem356375 {A B : Type'} (lt2 : type1402 A) (z : A) (P : type547 A B) (f : A -> B) (x : A) : ((term479 A B lt2 z P f x) = (term480 A B lt2 z P f x)) = ((term473 A B lt2 z P f x) = (term489 A B lt2 z P f x)).
Proof. exact (MK_COMB (@lem356368 A B lt2 z P f x) (@lem356374 A B lt2 z P f x)). Qed.
Lemma lem356376 {A B : Type'} (lt2 : type1402 A) (z : A) (P : type547 A B) (f : A -> B) (x : A) : (term473 A B lt2 z P f x) = (term489 A B lt2 z P f x).
Proof. exact (EQ_MP (@lem356375 A B lt2 z P f x) (@lem356360 A B lt2 z P f x)). Qed.
Lemma lem356377 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (x : A) : (term475 A B lt2 P f x) = (term490 A B lt2 P f x).
Proof. exact (fun_ext (fun z : A => @lem356376 A B lt2 z P f x)). Qed.
Lemma lem356378 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem356379 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (x : A) : (term476 A B lt2 P f x) = (term491 A B lt2 P f x).
Proof. exact (MK_COMB (@lem356378 A) (@lem356377 A B lt2 P f x)). Qed.
Lemma lem356380 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (x : A) : (term457 A B lt2 P f x) = (term491 A B lt2 P f x).
Proof. exact (TRANS (@lem356356 A B lt2 P f x) (@lem356379 A B lt2 P f x)). Qed.
Lemma lem356381 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term458 A B lt2 P f) = (term492 A B lt2 P f).
Proof. exact (fun_ext (fun x : A => @lem356380 A B lt2 P f x)). Qed.
Lemma lem356382 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem356383 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term459 A B lt2 P f) = (term493 A B lt2 P f).
Proof. exact (MK_COMB (@lem356382 A) (@lem356381 A B lt2 P f)). Qed.
Lemma lem356385 {A B : Type'} (P : type1413 A B) : (term370 A B P) = (term371 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem356386 {A : Type'} (P : type1402 A) : (term372 A P) = (term373 A P).
Proof. exact (@lem356385 A A P). Qed.
Lemma lem356387 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term494 A B lt2 P f) = (term495 A B lt2 P f).
Proof. exact (@lem356386 A (term496 A B lt2 P f)). Qed.
Lemma lem356388 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (x : A) : (term497 A B lt2 P f x) = (term490 A B lt2 P f x).
Proof. exact (eq_refl (term497 A B lt2 P f x)). Qed.
Lemma lem356389 {A : Type'} (z : A) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem356390 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (x : A) (z : A) : (term498 A B lt2 P f x z) = (term499 A B lt2 P f x z).
Proof. exact (MK_COMB (@lem356388 A B lt2 P f x) (@lem356389 A z)). Qed.
Lemma lem356391 {A B : Type'} (lt2 : type1402 A) (z : A) (P : type547 A B) (f : A -> B) (x : A) : (term499 A B lt2 P f x z) = (term489 A B lt2 z P f x).
Proof. exact (eq_refl (term499 A B lt2 P f x z)). Qed.
Lemma lem356392 {A B : Type'} (lt2 : type1402 A) (z : A) (P : type547 A B) (f : A -> B) (x : A) : (term498 A B lt2 P f x z) = (term489 A B lt2 z P f x).
Proof. exact (TRANS (@lem356390 A B lt2 P f x z) (@lem356391 A B lt2 z P f x)). Qed.
Lemma lem356393 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (x : A) : (term500 A B lt2 P f x) = (term490 A B lt2 P f x).
Proof. exact (fun_ext (fun z : A => @lem356392 A B lt2 z P f x)). Qed.
Lemma lem356394 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem356395 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (x : A) : (term501 A B lt2 P f x) = (term491 A B lt2 P f x).
Proof. exact (MK_COMB (@lem356394 A) (@lem356393 A B lt2 P f x)). Qed.
Lemma lem356396 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term502 A B lt2 P f) = (term492 A B lt2 P f).
Proof. exact (fun_ext (fun x : A => @lem356395 A B lt2 P f x)). Qed.
Lemma lem356397 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem356398 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term494 A B lt2 P f) = (term493 A B lt2 P f).
Proof. exact (MK_COMB (@lem356397 A) (@lem356396 A B lt2 P f)). Qed.
Lemma lem356399 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem356400 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term503 A B lt2 P f) = (term504 A B lt2 P f).
Proof. exact (MK_COMB (@lem356399) (@lem356398 A B lt2 P f)). Qed.
Lemma lem356401 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (x : A) : (term497 A B lt2 P f x) = (term490 A B lt2 P f x).
Proof. exact (eq_refl (term497 A B lt2 P f x)). Qed.
Lemma lem356402 {A : Type'} (z : A -> A) (x : A) : (z x) = (z x).
Proof. exact (eq_refl (z x)). Qed.
Lemma lem356403 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (z : A -> A) (x : A) : (term505 A B lt2 P f z x) = (term506 A B lt2 P f z x).
Proof. exact (MK_COMB (@lem356401 A B lt2 P f x) (@lem356402 A z x)). Qed.
Lemma lem356404 {A B : Type'} (lt2 : type1402 A) (z : A -> A) (P : type547 A B) (f : A -> B) (x : A) : (term506 A B lt2 P f z x) = (term507 A B lt2 z P f x).
Proof. exact (eq_refl (term506 A B lt2 P f z x)). Qed.
Lemma lem356405 {A B : Type'} (lt2 : type1402 A) (z : A -> A) (P : type547 A B) (f : A -> B) (x : A) : (term505 A B lt2 P f z x) = (term507 A B lt2 z P f x).
Proof. exact (TRANS (@lem356403 A B lt2 P f z x) (@lem356404 A B lt2 z P f x)). Qed.
Lemma lem356406 {A B : Type'} (lt2 : type1402 A) (z : A -> A) (P : type547 A B) (f : A -> B) : (term508 A B lt2 P f z) = (term509 A B lt2 z P f).
Proof. exact (fun_ext (fun x : A => @lem356405 A B lt2 z P f x)). Qed.
Lemma lem356407 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem356408 {A B : Type'} (lt2 : type1402 A) (z : A -> A) (P : type547 A B) (f : A -> B) : (term510 A B lt2 P f z) = (term511 A B lt2 z P f).
Proof. exact (MK_COMB (@lem356407 A) (@lem356406 A B lt2 z P f)). Qed.
Lemma lem356409 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term512 A B lt2 P f) = (term513 A B lt2 P f).
Proof. exact (fun_ext (fun z : A -> A => @lem356408 A B lt2 z P f)). Qed.
Lemma lem356410 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem356411 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term495 A B lt2 P f) = (term514 A B lt2 P f).
Proof. exact (MK_COMB (@lem356410 A) (@lem356409 A B lt2 P f)). Qed.
Lemma lem356412 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : ((term494 A B lt2 P f) = (term495 A B lt2 P f)) = ((term493 A B lt2 P f) = (term514 A B lt2 P f)).
Proof. exact (MK_COMB (@lem356400 A B lt2 P f) (@lem356411 A B lt2 P f)). Qed.
Lemma lem356413 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term493 A B lt2 P f) = (term514 A B lt2 P f).
Proof. exact (EQ_MP (@lem356412 A B lt2 P f) (@lem356387 A B lt2 P f)). Qed.
Lemma lem356415 {A B : Type'} (P : type1413 A B) : (term370 A B P) = (term371 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem356416 {A B : Type'} (P : type1413 A B) : (term370 A B P) = (term371 A B P).
Proof. exact (@lem356415 A B P). Qed.
Lemma lem356417 {A B : Type'} (lt2 : type1402 A) (z : A -> A) (P : type547 A B) (f : A -> B) : (term515 A B lt2 z P f) = (term516 A B lt2 z P f).
Proof. exact (@lem356416 A B (term517 A B lt2 z P f)). Qed.
Lemma lem356418 {A B : Type'} (lt2 : type1402 A) (z : A -> A) (P : type547 A B) (f : A -> B) (x : A) : (term518 A B lt2 z P f x) = (term519 A B lt2 z P f x).
Proof. exact (eq_refl (term518 A B lt2 z P f x)). Qed.
Lemma lem356419 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem356420 {A B : Type'} (lt2 : type1402 A) (z : A -> A) (P : type547 A B) (f : A -> B) (x : A) (y : B) : (term520 A B lt2 z P f x y) = (term521 A B lt2 z P f x y).
Proof. exact (MK_COMB (@lem356418 A B lt2 z P f x) (@lem356419 B y)). Qed.
Lemma lem356421 {A B : Type'} (lt2 : type1402 A) (z : A -> A) (P : type547 A B) (f : A -> B) (x : A) (y : B) : (term521 A B lt2 z P f x y) = (term522 A B lt2 z P f x y).
Proof. exact (eq_refl (term521 A B lt2 z P f x y)). Qed.
Lemma lem356422 {A B : Type'} (lt2 : type1402 A) (z : A -> A) (P : type547 A B) (f : A -> B) (x : A) (y : B) : (term520 A B lt2 z P f x y) = (term522 A B lt2 z P f x y).
Proof. exact (TRANS (@lem356420 A B lt2 z P f x y) (@lem356421 A B lt2 z P f x y)). Qed.
Lemma lem356423 {A B : Type'} (lt2 : type1402 A) (z : A -> A) (P : type547 A B) (f : A -> B) (x : A) : (term523 A B lt2 z P f x) = (term519 A B lt2 z P f x).
Proof. exact (fun_ext (fun y : B => @lem356422 A B lt2 z P f x y)). Qed.
Lemma lem356424 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem356425 {A B : Type'} (lt2 : type1402 A) (z : A -> A) (P : type547 A B) (f : A -> B) (x : A) : (term524 A B lt2 z P f x) = (term507 A B lt2 z P f x).
Proof. exact (MK_COMB (@lem356424 B) (@lem356423 A B lt2 z P f x)). Qed.
Lemma lem356426 {A B : Type'} (lt2 : type1402 A) (z : A -> A) (P : type547 A B) (f : A -> B) : (term525 A B lt2 z P f) = (term509 A B lt2 z P f).
Proof. exact (fun_ext (fun x : A => @lem356425 A B lt2 z P f x)). Qed.
Lemma lem356427 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem356428 {A B : Type'} (lt2 : type1402 A) (z : A -> A) (P : type547 A B) (f : A -> B) : (term515 A B lt2 z P f) = (term511 A B lt2 z P f).
Proof. exact (MK_COMB (@lem356427 A) (@lem356426 A B lt2 z P f)). Qed.
Lemma lem356429 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem356430 {A B : Type'} (lt2 : type1402 A) (z : A -> A) (P : type547 A B) (f : A -> B) : (term526 A B lt2 z P f) = (term527 A B lt2 z P f).
Proof. exact (MK_COMB (@lem356429) (@lem356428 A B lt2 z P f)). Qed.
Lemma lem356431 {A B : Type'} (lt2 : type1402 A) (z : A -> A) (P : type547 A B) (f : A -> B) (x : A) : (term518 A B lt2 z P f x) = (term519 A B lt2 z P f x).
Proof. exact (eq_refl (term518 A B lt2 z P f x)). Qed.
Lemma lem356432 {A B : Type'} (y : A -> B) (x : A) : (y x) = (y x).
Proof. exact (eq_refl (y x)). Qed.
Lemma lem356433 {A B : Type'} (lt2 : type1402 A) (z : A -> A) (P : type547 A B) (f : A -> B) (y : A -> B) (x : A) : (term528 A B lt2 z P f y x) = (term529 A B lt2 z P f y x).
Proof. exact (MK_COMB (@lem356431 A B lt2 z P f x) (@lem356432 A B y x)). Qed.
Lemma lem356434 {A B : Type'} (lt2 : type1402 A) (z : A -> A) (P : type547 A B) (f : A -> B) (y : A -> B) (x : A) : (term529 A B lt2 z P f y x) = (term530 A B lt2 z P f y x).
Proof. exact (eq_refl (term529 A B lt2 z P f y x)). Qed.
Lemma lem356435 {A B : Type'} (lt2 : type1402 A) (z : A -> A) (P : type547 A B) (f : A -> B) (y : A -> B) (x : A) : (term528 A B lt2 z P f y x) = (term530 A B lt2 z P f y x).
Proof. exact (TRANS (@lem356433 A B lt2 z P f y x) (@lem356434 A B lt2 z P f y x)). Qed.
Lemma lem356436 {A B : Type'} (lt2 : type1402 A) (z : A -> A) (P : type547 A B) (f : A -> B) (y : A -> B) : (term531 A B lt2 z P f y) = (term532 A B lt2 z P f y).
Proof. exact (fun_ext (fun x : A => @lem356435 A B lt2 z P f y x)). Qed.
Lemma lem356437 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem356438 {A B : Type'} (lt2 : type1402 A) (z : A -> A) (P : type547 A B) (f : A -> B) (y : A -> B) : (term533 A B lt2 z P f y) = (term534 A B lt2 z P f y).
Proof. exact (MK_COMB (@lem356437 A) (@lem356436 A B lt2 z P f y)). Qed.
Lemma lem356439 {A B : Type'} (lt2 : type1402 A) (z : A -> A) (P : type547 A B) (f : A -> B) : (term535 A B lt2 z P f) = (term536 A B lt2 z P f).
Proof. exact (fun_ext (fun y : A -> B => @lem356438 A B lt2 z P f y)). Qed.
Lemma lem356440 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem356441 {A B : Type'} (lt2 : type1402 A) (z : A -> A) (P : type547 A B) (f : A -> B) : (term516 A B lt2 z P f) = (term537 A B lt2 z P f).
Proof. exact (MK_COMB (@lem356440 A B) (@lem356439 A B lt2 z P f)). Qed.
Lemma lem356442 {A B : Type'} (lt2 : type1402 A) (z : A -> A) (P : type547 A B) (f : A -> B) : ((term515 A B lt2 z P f) = (term516 A B lt2 z P f)) = ((term511 A B lt2 z P f) = (term537 A B lt2 z P f)).
Proof. exact (MK_COMB (@lem356430 A B lt2 z P f) (@lem356441 A B lt2 z P f)). Qed.
Lemma lem356443 {A B : Type'} (lt2 : type1402 A) (z : A -> A) (P : type547 A B) (f : A -> B) : (term511 A B lt2 z P f) = (term537 A B lt2 z P f).
Proof. exact (EQ_MP (@lem356442 A B lt2 z P f) (@lem356417 A B lt2 z P f)). Qed.
Lemma lem356444 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term513 A B lt2 P f) = (term538 A B lt2 P f).
Proof. exact (fun_ext (fun z : A -> A => @lem356443 A B lt2 z P f)). Qed.
Lemma lem356445 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem356446 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term514 A B lt2 P f) = (term539 A B lt2 P f).
Proof. exact (MK_COMB (@lem356445 A) (@lem356444 A B lt2 P f)). Qed.
Lemma lem356447 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term493 A B lt2 P f) = (term539 A B lt2 P f).
Proof. exact (TRANS (@lem356413 A B lt2 P f) (@lem356446 A B lt2 P f)). Qed.
Lemma lem356448 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term459 A B lt2 P f) = (term539 A B lt2 P f).
Proof. exact (TRANS (@lem356383 A B lt2 P f) (@lem356447 A B lt2 P f)). Qed.
Lemma lem356449 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : (term460 A B lt2 P) = (term540 A B lt2 P).
Proof. exact (fun_ext (fun f : A -> B => @lem356448 A B lt2 P f)). Qed.
Lemma lem356450 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem356451 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : (term461 A B lt2 P) = (term541 A B lt2 P).
Proof. exact (MK_COMB (@lem356450 A B) (@lem356449 A B lt2 P)). Qed.
Lemma lem356453 {A B : Type'} (P : type1413 A B) : (term370 A B P) = (term371 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem356454 {A B : Type'} (P : type513 A B) : (term397 A B P) = (term398 A B P).
Proof. exact (@lem356453 (A -> B) (A -> A) P). Qed.
Lemma lem356455 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : (term542 A B lt2 P) = (term543 A B lt2 P).
Proof. exact (@lem356454 A B (term544 A B lt2 P)). Qed.
Lemma lem356456 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term545 A B lt2 P f) = (term538 A B lt2 P f).
Proof. exact (eq_refl (term545 A B lt2 P f)). Qed.
Lemma lem356457 {A : Type'} (z : A -> A) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem356458 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (z : A -> A) : (term546 A B lt2 P f z) = (term547 A B lt2 P f z).
Proof. exact (MK_COMB (@lem356456 A B lt2 P f) (@lem356457 A z)). Qed.
Lemma lem356459 {A B : Type'} (lt2 : type1402 A) (z : A -> A) (P : type547 A B) (f : A -> B) : (term547 A B lt2 P f z) = (term537 A B lt2 z P f).
Proof. exact (eq_refl (term547 A B lt2 P f z)). Qed.
Lemma lem356460 {A B : Type'} (lt2 : type1402 A) (z : A -> A) (P : type547 A B) (f : A -> B) : (term546 A B lt2 P f z) = (term537 A B lt2 z P f).
Proof. exact (TRANS (@lem356458 A B lt2 P f z) (@lem356459 A B lt2 z P f)). Qed.
Lemma lem356461 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term548 A B lt2 P f) = (term538 A B lt2 P f).
Proof. exact (fun_ext (fun z : A -> A => @lem356460 A B lt2 z P f)). Qed.
Lemma lem356462 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem356463 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term549 A B lt2 P f) = (term539 A B lt2 P f).
Proof. exact (MK_COMB (@lem356462 A) (@lem356461 A B lt2 P f)). Qed.
Lemma lem356464 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : (term550 A B lt2 P) = (term540 A B lt2 P).
Proof. exact (fun_ext (fun f : A -> B => @lem356463 A B lt2 P f)). Qed.
Lemma lem356465 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem356466 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : (term542 A B lt2 P) = (term541 A B lt2 P).
Proof. exact (MK_COMB (@lem356465 A B) (@lem356464 A B lt2 P)). Qed.
Lemma lem356467 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem356468 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : (term551 A B lt2 P) = (term552 A B lt2 P).
Proof. exact (MK_COMB (@lem356467) (@lem356466 A B lt2 P)). Qed.
Lemma lem356469 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term545 A B lt2 P f) = (term538 A B lt2 P f).
Proof. exact (eq_refl (term545 A B lt2 P f)). Qed.
Lemma lem356470 {A B : Type'} (z : type548 A B) (f : A -> B) : (z f) = (z f).
Proof. exact (eq_refl (z f)). Qed.
Lemma lem356471 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (z : type548 A B) (f : A -> B) : (term553 A B lt2 P z f) = (term554 A B lt2 P z f).
Proof. exact (MK_COMB (@lem356469 A B lt2 P f) (@lem356470 A B z f)). Qed.
Lemma lem356472 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (f : A -> B) : (term554 A B lt2 P z f) = (term555 A B lt2 z P f).
Proof. exact (eq_refl (term554 A B lt2 P z f)). Qed.
Lemma lem356473 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (f : A -> B) : (term553 A B lt2 P z f) = (term555 A B lt2 z P f).
Proof. exact (TRANS (@lem356471 A B lt2 P z f) (@lem356472 A B lt2 z P f)). Qed.
Lemma lem356474 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) : (term556 A B lt2 P z) = (term557 A B lt2 z P).
Proof. exact (fun_ext (fun f : A -> B => @lem356473 A B lt2 z P f)). Qed.
Lemma lem356475 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem356476 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) : (term558 A B lt2 P z) = (term559 A B lt2 z P).
Proof. exact (MK_COMB (@lem356475 A B) (@lem356474 A B lt2 z P)). Qed.
Lemma lem356477 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : (term560 A B lt2 P) = (term561 A B lt2 P).
Proof. exact (fun_ext (fun z : type548 A B => @lem356476 A B lt2 z P)). Qed.
Lemma lem356478 {A B : Type'} : (@ex ((A -> B) -> A -> A)) = (@ex ((A -> B) -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> A -> A))). Qed.
Lemma lem356479 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : (term543 A B lt2 P) = (term562 A B lt2 P).
Proof. exact (MK_COMB (@lem356478 A B) (@lem356477 A B lt2 P)). Qed.
Lemma lem356480 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : ((term542 A B lt2 P) = (term543 A B lt2 P)) = ((term541 A B lt2 P) = (term562 A B lt2 P)).
Proof. exact (MK_COMB (@lem356468 A B lt2 P) (@lem356479 A B lt2 P)). Qed.
Lemma lem356481 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : (term541 A B lt2 P) = (term562 A B lt2 P).
Proof. exact (EQ_MP (@lem356480 A B lt2 P) (@lem356455 A B lt2 P)). Qed.
Lemma lem356483 {A B : Type'} (P : type1413 A B) : (term370 A B P) = (term371 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem356484 {A B : Type'} (P : type523 A B) : (term563 A B P) = (term564 A B P).
Proof. exact (@lem356483 (A -> B) (A -> B) P). Qed.
Lemma lem356485 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) : (term565 A B lt2 z P) = (term566 A B lt2 z P).
Proof. exact (@lem356484 A B (term567 A B lt2 z P)). Qed.
Lemma lem356486 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (f : A -> B) : (term568 A B lt2 z P f) = (term569 A B lt2 z P f).
Proof. exact (eq_refl (term568 A B lt2 z P f)). Qed.
Lemma lem356487 {A B : Type'} (y : A -> B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem356488 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (f : A -> B) (y : A -> B) : (term570 A B lt2 z P f y) = (term571 A B lt2 z P f y).
Proof. exact (MK_COMB (@lem356486 A B lt2 z P f) (@lem356487 A B y)). Qed.
Lemma lem356489 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (f : A -> B) (y : A -> B) : (term571 A B lt2 z P f y) = (term572 A B lt2 z P f y).
Proof. exact (eq_refl (term571 A B lt2 z P f y)). Qed.
Lemma lem356490 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (f : A -> B) (y : A -> B) : (term570 A B lt2 z P f y) = (term572 A B lt2 z P f y).
Proof. exact (TRANS (@lem356488 A B lt2 z P f y) (@lem356489 A B lt2 z P f y)). Qed.
Lemma lem356491 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (f : A -> B) : (term573 A B lt2 z P f) = (term569 A B lt2 z P f).
Proof. exact (fun_ext (fun y : A -> B => @lem356490 A B lt2 z P f y)). Qed.
Lemma lem356492 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem356493 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (f : A -> B) : (term574 A B lt2 z P f) = (term555 A B lt2 z P f).
Proof. exact (MK_COMB (@lem356492 A B) (@lem356491 A B lt2 z P f)). Qed.
Lemma lem356494 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) : (term575 A B lt2 z P) = (term557 A B lt2 z P).
Proof. exact (fun_ext (fun f : A -> B => @lem356493 A B lt2 z P f)). Qed.
Lemma lem356495 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem356496 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) : (term565 A B lt2 z P) = (term559 A B lt2 z P).
Proof. exact (MK_COMB (@lem356495 A B) (@lem356494 A B lt2 z P)). Qed.
Lemma lem356497 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem356498 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) : (term576 A B lt2 z P) = (term577 A B lt2 z P).
Proof. exact (MK_COMB (@lem356497) (@lem356496 A B lt2 z P)). Qed.
Lemma lem356499 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (f : A -> B) : (term568 A B lt2 z P f) = (term569 A B lt2 z P f).
Proof. exact (eq_refl (term568 A B lt2 z P f)). Qed.
Lemma lem356500 {A B : Type'} (y : type549 A B) (f : A -> B) : (y f) = (y f).
Proof. exact (eq_refl (y f)). Qed.
Lemma lem356501 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (y : type549 A B) (f : A -> B) : (term578 A B lt2 z P y f) = (term579 A B lt2 z P y f).
Proof. exact (MK_COMB (@lem356499 A B lt2 z P f) (@lem356500 A B y f)). Qed.
Lemma lem356502 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (y : type549 A B) (f : A -> B) : (term579 A B lt2 z P y f) = (term580 A B lt2 z P y f).
Proof. exact (eq_refl (term579 A B lt2 z P y f)). Qed.
Lemma lem356503 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (y : type549 A B) (f : A -> B) : (term578 A B lt2 z P y f) = (term580 A B lt2 z P y f).
Proof. exact (TRANS (@lem356501 A B lt2 z P y f) (@lem356502 A B lt2 z P y f)). Qed.
Lemma lem356504 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (y : type549 A B) : (term581 A B lt2 z P y) = (term582 A B lt2 z P y).
Proof. exact (fun_ext (fun f : A -> B => @lem356503 A B lt2 z P y f)). Qed.
Lemma lem356505 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem356506 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (y : type549 A B) : (term583 A B lt2 z P y) = (term584 A B lt2 z P y).
Proof. exact (MK_COMB (@lem356505 A B) (@lem356504 A B lt2 z P y)). Qed.
Lemma lem356507 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) : (term585 A B lt2 z P) = (term586 A B lt2 z P).
Proof. exact (fun_ext (fun y : type549 A B => @lem356506 A B lt2 z P y)). Qed.
Lemma lem356508 {A B : Type'} : (@ex ((A -> B) -> A -> B)) = (@ex ((A -> B) -> A -> B)).
Proof. exact (eq_refl (@ex ((A -> B) -> A -> B))). Qed.
Lemma lem356509 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) : (term566 A B lt2 z P) = (term587 A B lt2 z P).
Proof. exact (MK_COMB (@lem356508 A B) (@lem356507 A B lt2 z P)). Qed.
Lemma lem356510 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) : ((term565 A B lt2 z P) = (term566 A B lt2 z P)) = ((term559 A B lt2 z P) = (term587 A B lt2 z P)).
Proof. exact (MK_COMB (@lem356498 A B lt2 z P) (@lem356509 A B lt2 z P)). Qed.
Lemma lem356511 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) : (term559 A B lt2 z P) = (term587 A B lt2 z P).
Proof. exact (EQ_MP (@lem356510 A B lt2 z P) (@lem356485 A B lt2 z P)). Qed.
Lemma lem356512 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : (term561 A B lt2 P) = (term588 A B lt2 P).
Proof. exact (fun_ext (fun z : type548 A B => @lem356511 A B lt2 z P)). Qed.
Lemma lem356513 {A B : Type'} : (@ex ((A -> B) -> A -> A)) = (@ex ((A -> B) -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> A -> A))). Qed.
Lemma lem356514 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : (term562 A B lt2 P) = (term589 A B lt2 P).
Proof. exact (MK_COMB (@lem356513 A B) (@lem356512 A B lt2 P)). Qed.
Lemma lem356515 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : (term541 A B lt2 P) = (term589 A B lt2 P).
Proof. exact (TRANS (@lem356481 A B lt2 P) (@lem356514 A B lt2 P)). Qed.
Lemma lem356517 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : (term461 A B lt2 P) = (term589 A B lt2 P).
Proof. exact (TRANS (@lem356451 A B lt2 P) (@lem356515 A B lt2 P)). Qed.
Lemma lem356518 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) : (term6 A B lt2 P) = (term589 A B lt2 P).
Proof. exact (TRANS (@lem356225 A B lt2 P) (@lem356517 A B lt2 P)). Qed.
Lemma lem356519 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (h1 : term6 A B lt2 P) : term589 A B lt2 P.
Proof. exact (EQ_MP (@lem356518 A B lt2 P) (@lem355583 A B lt2 P h1)). Qed.
Lemma lem356520 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) : ((_7729 P f x) = (f x)) = ((_7729 P f x) = (f x)).
Proof. exact (eq_refl ((_7729 P f x) = (f x))). Qed.
Lemma lem356521 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) : (term185 A B _7729 P f) = (term185 A B _7729 P f).
Proof. exact (fun_ext (fun x : A => @lem356520 A B _7729 P f x)). Qed.
Lemma lem356522 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem356531 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) : (term186 A B _7729 P f) = (term186 A B _7729 P f).
Proof. exact (MK_COMB (@lem356522 A) (@lem356521 A B _7729 P f)). Qed.
Lemma lem356532 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (h1 : term186 A B _7729 P f) : term186 A B _7729 P f.
Proof. exact (EQ_MP (@lem356531 A B _7729 P f) (@lem355584 A B _7729 P f h1)). Qed.
Lemma lem356534 {A B : Type'} (P : type547 A B) (f : A -> B) (y : A) (y' : B) : (P f y y') = (P f y y').
Proof. exact (eq_refl (P f y y')). Qed.
Lemma lem356535 {A B : Type'} (P : type547 A B) (f : A -> B) (y : A) : (term69 A B P f y) = (term69 A B P f y).
Proof. exact (fun_ext (fun y' : B => @lem356534 A B P f y y')). Qed.
Lemma lem356536 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem356537 {A B : Type'} (P : type547 A B) (f : A -> B) (y : A) : (term106 A B P f y) = (term106 A B P f y).
Proof. exact (MK_COMB (@lem356536 B) (@lem356535 A B P f y)). Qed.
Lemma lem356539 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (term590 A lt2 y x) = (term590 A lt2 y x).
Proof. exact (eq_refl (term590 A lt2 y x)). Qed.
Lemma lem356540 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (y : A) : (term591 A B lt2 x P f y) = (term591 A B lt2 x P f y).
Proof. exact (MK_COMB (@lem356539 A lt2 y x) (@lem356537 A B P f y)). Qed.
Lemma lem356541 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (y : A) : (term122 A B lt2 x P f y) = (term591 A B lt2 x P f y).
Proof. exact (@lem17265 (lt2 y x) (term106 A B P f y)). Qed.
Lemma lem356542 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (y : A) : (term122 A B lt2 x P f y) = (term591 A B lt2 x P f y).
Proof. exact (TRANS (@lem356541 A B lt2 x P f y) (@lem356540 A B lt2 x P f y)). Qed.
Lemma lem356543 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) : (term124 A B lt2 x P f) = (term592 A B lt2 x P f).
Proof. exact (fun_ext (fun y : A => @lem356542 A B lt2 x P f y)). Qed.
Lemma lem356544 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem356545 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) : (term126 A B lt2 x P f) = (term593 A B lt2 x P f).
Proof. exact (MK_COMB (@lem356544 A) (@lem356543 A B lt2 x P f)). Qed.
Lemma lem356600 {A : Type'} (P : Prop) (Q : A -> Prop) : (term477 A P Q) = (term478 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem356601 {B : Type'} (P : Prop) (Q : B -> Prop) : (term477 B P Q) = (term478 B P Q).
Proof. exact (@lem356600 B P Q). Qed.
Lemma lem356602 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (y : A) : (term594 A B lt2 x P f y) = (term595 A B lt2 x P f y).
Proof. exact (@lem356601 B (term596 A lt2 y x) (term69 A B P f y)). Qed.
Lemma lem356603 {A B : Type'} (P : type547 A B) (f : A -> B) (y : A) (y' : B) : (term145 A B P f y y') = (P f y y').
Proof. exact (eq_refl (term145 A B P f y y')). Qed.
Lemma lem356604 {A B : Type'} (P : type547 A B) (f : A -> B) (y : A) : (term481 A B P f y) = (term69 A B P f y).
Proof. exact (fun_ext (fun y' : B => @lem356603 A B P f y y')). Qed.
Lemma lem356605 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem356606 {A B : Type'} (P : type547 A B) (f : A -> B) (y : A) : (term482 A B P f y) = (term106 A B P f y).
Proof. exact (MK_COMB (@lem356605 B) (@lem356604 A B P f y)). Qed.
Lemma lem356607 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (term590 A lt2 y x) = (term590 A lt2 y x).
Proof. exact (eq_refl (term590 A lt2 y x)). Qed.
Lemma lem356608 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (y : A) : (term594 A B lt2 x P f y) = (term591 A B lt2 x P f y).
Proof. exact (MK_COMB (@lem356607 A lt2 y x) (@lem356606 A B P f y)). Qed.
Lemma lem356609 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem356610 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (y : A) : (term597 A B lt2 x P f y) = (term598 A B lt2 x P f y).
Proof. exact (MK_COMB (@lem356609) (@lem356608 A B lt2 x P f y)). Qed.
Lemma lem356611 {A B : Type'} (P : type547 A B) (f : A -> B) (y : A) (y' : B) : (term145 A B P f y y') = (P f y y').
Proof. exact (eq_refl (term145 A B P f y y')). Qed.
Lemma lem356612 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (term590 A lt2 y x) = (term590 A lt2 y x).
Proof. exact (eq_refl (term590 A lt2 y x)). Qed.
Lemma lem356613 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (y : A) (y' : B) : (term599 A B lt2 x P f y y') = (term600 A B lt2 x P f y y').
Proof. exact (MK_COMB (@lem356612 A lt2 y x) (@lem356611 A B P f y y')). Qed.
Lemma lem356614 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (y : A) : (term601 A B lt2 x P f y) = (term602 A B lt2 x P f y).
Proof. exact (fun_ext (fun y' : B => @lem356613 A B lt2 x P f y y')). Qed.
Lemma lem356615 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem356616 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (y : A) : (term595 A B lt2 x P f y) = (term603 A B lt2 x P f y).
Proof. exact (MK_COMB (@lem356615 B) (@lem356614 A B lt2 x P f y)). Qed.
Lemma lem356617 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (y : A) : ((term594 A B lt2 x P f y) = (term595 A B lt2 x P f y)) = ((term591 A B lt2 x P f y) = (term603 A B lt2 x P f y)).
Proof. exact (MK_COMB (@lem356610 A B lt2 x P f y) (@lem356616 A B lt2 x P f y)). Qed.
Lemma lem356618 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (y : A) : (term591 A B lt2 x P f y) = (term603 A B lt2 x P f y).
Proof. exact (EQ_MP (@lem356617 A B lt2 x P f y) (@lem356602 A B lt2 x P f y)). Qed.
Lemma lem356619 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) : (term592 A B lt2 x P f) = (term604 A B lt2 x P f).
Proof. exact (fun_ext (fun y : A => @lem356618 A B lt2 x P f y)). Qed.
Lemma lem356620 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem356621 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) : (term593 A B lt2 x P f) = (term605 A B lt2 x P f).
Proof. exact (MK_COMB (@lem356620 A) (@lem356619 A B lt2 x P f)). Qed.
Lemma lem356623 {A B : Type'} (P : type1413 A B) : (term370 A B P) = (term371 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem356624 {A B : Type'} (P : type1413 A B) : (term370 A B P) = (term371 A B P).
Proof. exact (@lem356623 A B P). Qed.
Lemma lem356625 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) : (term606 A B lt2 x P f) = (term607 A B lt2 x P f).
Proof. exact (@lem356624 A B (term608 A B lt2 x P f)). Qed.
Lemma lem356626 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (y : A) : (term609 A B lt2 x P f y) = (term602 A B lt2 x P f y).
Proof. exact (eq_refl (term609 A B lt2 x P f y)). Qed.
Lemma lem356627 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem356628 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (y : A) (y' : B) : (term610 A B lt2 x P f y y') = (term611 A B lt2 x P f y y').
Proof. exact (MK_COMB (@lem356626 A B lt2 x P f y) (@lem356627 B y')). Qed.
Lemma lem356629 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (y : A) (y' : B) : (term611 A B lt2 x P f y y') = (term600 A B lt2 x P f y y').
Proof. exact (eq_refl (term611 A B lt2 x P f y y')). Qed.
Lemma lem356630 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (y : A) (y' : B) : (term610 A B lt2 x P f y y') = (term600 A B lt2 x P f y y').
Proof. exact (TRANS (@lem356628 A B lt2 x P f y y') (@lem356629 A B lt2 x P f y y')). Qed.
Lemma lem356631 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (y : A) : (term612 A B lt2 x P f y) = (term602 A B lt2 x P f y).
Proof. exact (fun_ext (fun y' : B => @lem356630 A B lt2 x P f y y')). Qed.
Lemma lem356632 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem356633 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (y : A) : (term613 A B lt2 x P f y) = (term603 A B lt2 x P f y).
Proof. exact (MK_COMB (@lem356632 B) (@lem356631 A B lt2 x P f y)). Qed.
Lemma lem356634 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) : (term614 A B lt2 x P f) = (term604 A B lt2 x P f).
Proof. exact (fun_ext (fun y : A => @lem356633 A B lt2 x P f y)). Qed.
Lemma lem356635 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem356636 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) : (term606 A B lt2 x P f) = (term605 A B lt2 x P f).
Proof. exact (MK_COMB (@lem356635 A) (@lem356634 A B lt2 x P f)). Qed.
Lemma lem356637 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem356638 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) : (term615 A B lt2 x P f) = (term616 A B lt2 x P f).
Proof. exact (MK_COMB (@lem356637) (@lem356636 A B lt2 x P f)). Qed.
Lemma lem356639 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (y : A) : (term609 A B lt2 x P f y) = (term602 A B lt2 x P f y).
Proof. exact (eq_refl (term609 A B lt2 x P f y)). Qed.
Lemma lem356640 {A B : Type'} (y : A -> B) (y' : A) : (y y') = (y y').
Proof. exact (eq_refl (y y')). Qed.
Lemma lem356641 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (y : A -> B) (y' : A) : (term617 A B lt2 x P f y y') = (term618 A B lt2 x P f y y').
Proof. exact (MK_COMB (@lem356639 A B lt2 x P f y') (@lem356640 A B y y')). Qed.
Lemma lem356642 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (y : A -> B) (y' : A) : (term618 A B lt2 x P f y y') = (term619 A B lt2 x P f y y').
Proof. exact (eq_refl (term618 A B lt2 x P f y y')). Qed.
Lemma lem356643 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (y : A -> B) (y' : A) : (term617 A B lt2 x P f y y') = (term619 A B lt2 x P f y y').
Proof. exact (TRANS (@lem356641 A B lt2 x P f y y') (@lem356642 A B lt2 x P f y y')). Qed.
Lemma lem356644 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (y : A -> B) : (term620 A B lt2 x P f y) = (term621 A B lt2 x P f y).
Proof. exact (fun_ext (fun y' : A => @lem356643 A B lt2 x P f y y')). Qed.
Lemma lem356645 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem356646 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (y : A -> B) : (term622 A B lt2 x P f y) = (term623 A B lt2 x P f y).
Proof. exact (MK_COMB (@lem356645 A) (@lem356644 A B lt2 x P f y)). Qed.
Lemma lem356647 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) : (term624 A B lt2 x P f) = (term625 A B lt2 x P f).
Proof. exact (fun_ext (fun y : A -> B => @lem356646 A B lt2 x P f y)). Qed.
Lemma lem356648 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem356649 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) : (term607 A B lt2 x P f) = (term626 A B lt2 x P f).
Proof. exact (MK_COMB (@lem356648 A B) (@lem356647 A B lt2 x P f)). Qed.
Lemma lem356650 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) : ((term606 A B lt2 x P f) = (term607 A B lt2 x P f)) = ((term605 A B lt2 x P f) = (term626 A B lt2 x P f)).
Proof. exact (MK_COMB (@lem356638 A B lt2 x P f) (@lem356649 A B lt2 x P f)). Qed.
Lemma lem356651 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) : (term605 A B lt2 x P f) = (term626 A B lt2 x P f).
Proof. exact (EQ_MP (@lem356650 A B lt2 x P f) (@lem356625 A B lt2 x P f)). Qed.
Lemma lem356653 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) : (term593 A B lt2 x P f) = (term626 A B lt2 x P f).
Proof. exact (TRANS (@lem356621 A B lt2 x P f) (@lem356651 A B lt2 x P f)). Qed.
Lemma lem356654 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) : (term126 A B lt2 x P f) = (term626 A B lt2 x P f).
Proof. exact (TRANS (@lem356545 A B lt2 x P f) (@lem356653 A B lt2 x P f)). Qed.
Lemma lem356655 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (h1 : term126 A B lt2 x P f) : term626 A B lt2 x P f.
Proof. exact (EQ_MP (@lem356654 A B lt2 x P f) (@lem355585 A B lt2 x P f h1)). Qed.
Lemma lem356657 {B : Type'} (P : B -> Prop) : (term627 B P) = (term628 B P).
Proof. exact (@lem18394 B P). Qed.
Lemma lem356658 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term247 A B P f x) = (term629 A B P f x).
Proof. exact (@lem356657 B (term69 A B P f x)). Qed.
Lemma lem356659 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (y : B) : (term145 A B P f x y) = (P f x y).
Proof. exact (eq_refl (term145 A B P f x y)). Qed.
Lemma lem356660 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem356662 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (y : B) : (term630 A B P f x y) = (term263 A B P f x y).
Proof. exact (MK_COMB (@lem356660) (@lem356659 A B P f x y)). Qed.
Lemma lem356663 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term631 A B P f x) = (term261 A B P f x).
Proof. exact (fun_ext (fun y : B => @lem356662 A B P f x y)). Qed.
Lemma lem356664 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem356665 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term629 A B P f x) = (term272 A B P f x).
Proof. exact (MK_COMB (@lem356664 B) (@lem356663 A B P f x)). Qed.
Lemma lem356674 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term247 A B P f x) = (term272 A B P f x).
Proof. exact (TRANS (@lem356658 A B P f x) (@lem356665 A B P f x)). Qed.
Lemma lem356675 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (h1 : term247 A B P f x) : term272 A B P f x.
Proof. exact (EQ_MP (@lem356674 A B P f x) (@lem355590 A B P f x h1)). Qed.
Lemma lem356676 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (y : A -> B) (h1 : term623 A B lt2 x P f y) : term623 A B lt2 x P f y.
Proof. exact (h1). Qed.
Lemma lem356677 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (h1 : term587 A B lt2 z P) : term587 A B lt2 z P.
Proof. exact (h1). Qed.
Lemma lem356678 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (y' : type549 A B) (h1 : term584 A B lt2 z P y') : term584 A B lt2 z P y'.
Proof. exact (h1). Qed.
Lemma lem356691 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem356692 {A B : Type'} (f : type103 A B) (x : type547 A B) : (f x) = (@I (((A -> B) -> A -> B -> Prop) -> (A -> B) -> A -> B) f x).
Proof. exact (@lem356691 (type547 A B) (type549 A B) f x). Qed.
Lemma lem356693 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) : (_7729 P) = (@I (((A -> B) -> A -> B -> Prop) -> (A -> B) -> A -> B) _7729 P).
Proof. exact (@lem356692 A B _7729 P). Qed.
Lemma lem356694 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem356695 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) : (_7729 P f) = (@I (((A -> B) -> A -> B -> Prop) -> (A -> B) -> A -> B) _7729 P f).
Proof. exact (MK_COMB (@lem356693 A B _7729 P) (@lem356694 A B f)). Qed.
Lemma lem356697 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem356698 {A B : Type'} (f : type549 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> A -> B) f x).
Proof. exact (@lem356697 (A -> B) (A -> B) f x). Qed.
Lemma lem356699 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) : (@I (((A -> B) -> A -> B -> Prop) -> (A -> B) -> A -> B) _7729 P f) = (term632 A B _7729 P f).
Proof. exact (@lem356698 A B (@I (((A -> B) -> A -> B -> Prop) -> (A -> B) -> A -> B) _7729 P) f). Qed.
Lemma lem356700 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) : (_7729 P f) = (term632 A B _7729 P f).
Proof. exact (TRANS (@lem356695 A B _7729 P f) (@lem356699 A B _7729 P f)). Qed.
Lemma lem356701 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem356702 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) : (_7729 P f x) = (term633 A B _7729 P f x).
Proof. exact (MK_COMB (@lem356700 A B _7729 P f) (@lem356701 A x)). Qed.
Lemma lem356704 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem356705 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem356704 A B f x). Qed.
Lemma lem356706 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) : (term633 A B _7729 P f x) = (term634 A B _7729 P f x).
Proof. exact (@lem356705 A B (term632 A B _7729 P f) x). Qed.
Lemma lem356708 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) : (_7729 P f x) = (term634 A B _7729 P f x).
Proof. exact (TRANS (@lem356702 A B _7729 P f x) (@lem356706 A B _7729 P f x)). Qed.
Lemma lem356710 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (P f x) = (P f x).
Proof. exact (eq_refl (P f x)). Qed.
Lemma lem356711 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) : (term170 A B _7729 P f x) = (term635 A B _7729 P f x).
Proof. exact (MK_COMB (@lem356710 A B P f x) (@lem356708 A B _7729 P f x)). Qed.
Lemma lem356713 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem356714 {A B : Type'} (f : type547 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> A -> B -> Prop) f x).
Proof. exact (@lem356713 (A -> B) (type1413 A B) f x). Qed.
Lemma lem356715 {A B : Type'} (P : type547 A B) (f : A -> B) : (P f) = (@I ((A -> B) -> A -> B -> Prop) P f).
Proof. exact (@lem356714 A B P f). Qed.
Lemma lem356716 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem356717 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (P f x) = (@I ((A -> B) -> A -> B -> Prop) P f x).
Proof. exact (MK_COMB (@lem356715 A B P f) (@lem356716 A x)). Qed.
Lemma lem356719 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem356720 {A B : Type'} (f : type1413 A B) (x : A) : (f x) = (@I (A -> B -> Prop) f x).
Proof. exact (@lem356719 A (B -> Prop) f x). Qed.
Lemma lem356721 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (@I ((A -> B) -> A -> B -> Prop) P f x) = (term636 A B P f x).
Proof. exact (@lem356720 A B (@I ((A -> B) -> A -> B -> Prop) P f) x). Qed.
Lemma lem356722 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (P f x) = (term636 A B P f x).
Proof. exact (TRANS (@lem356717 A B P f x) (@lem356721 A B P f x)). Qed.
Lemma lem356723 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) : (term634 A B _7729 P f x) = (term634 A B _7729 P f x).
Proof. exact (eq_refl (term634 A B _7729 P f x)). Qed.
Lemma lem356724 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) : (term635 A B _7729 P f x) = (term637 A B _7729 P f x).
Proof. exact (MK_COMB (@lem356722 A B P f x) (@lem356723 A B _7729 P f x)). Qed.
Lemma lem356726 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem356727 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem356726 B Prop f x). Qed.
Lemma lem356728 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) : (term637 A B _7729 P f x) = (term638 A B _7729 P f x).
Proof. exact (@lem356727 B (term636 A B P f x) (term634 A B _7729 P f x)). Qed.
Lemma lem356729 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) : (term635 A B _7729 P f x) = (term638 A B _7729 P f x).
Proof. exact (TRANS (@lem356724 A B _7729 P f x) (@lem356728 A B _7729 P f x)). Qed.
Lemma lem356730 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) : (term170 A B _7729 P f x) = (term638 A B _7729 P f x).
Proof. exact (TRANS (@lem356711 A B _7729 P f x) (@lem356729 A B _7729 P f x)). Qed.
Lemma lem356731 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem356740 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem356741 {A B : Type'} (f : type547 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> A -> B -> Prop) f x).
Proof. exact (@lem356740 (A -> B) (type1413 A B) f x). Qed.
Lemma lem356742 {A B : Type'} (P : type547 A B) (f : A -> B) : (P f) = (@I ((A -> B) -> A -> B -> Prop) P f).
Proof. exact (@lem356741 A B P f). Qed.
Lemma lem356743 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem356744 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (P f x) = (@I ((A -> B) -> A -> B -> Prop) P f x).
Proof. exact (MK_COMB (@lem356742 A B P f) (@lem356743 A x)). Qed.
Lemma lem356746 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem356747 {A B : Type'} (f : type1413 A B) (x : A) : (f x) = (@I (A -> B -> Prop) f x).
Proof. exact (@lem356746 A (B -> Prop) f x). Qed.
Lemma lem356748 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (@I ((A -> B) -> A -> B -> Prop) P f x) = (term636 A B P f x).
Proof. exact (@lem356747 A B (@I ((A -> B) -> A -> B -> Prop) P f) x). Qed.
Lemma lem356749 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (P f x) = (term636 A B P f x).
Proof. exact (TRANS (@lem356744 A B P f x) (@lem356748 A B P f x)). Qed.
Lemma lem356750 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem356751 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (x' : B) : (P f x x') = (term639 A B P f x x').
Proof. exact (MK_COMB (@lem356749 A B P f x) (@lem356750 B x')). Qed.
Lemma lem356753 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem356754 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem356753 B Prop f x). Qed.
Lemma lem356755 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (x' : B) : (term639 A B P f x x') = (term640 A B P f x x').
Proof. exact (@lem356754 B (term636 A B P f x) x'). Qed.
Lemma lem356757 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (x' : B) : (P f x x') = (term640 A B P f x x').
Proof. exact (TRANS (@lem356751 A B P f x x') (@lem356755 A B P f x x')). Qed.
Lemma lem356758 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (x' : B) : (term263 A B P f x x') = (term641 A B P f x x').
Proof. exact (MK_COMB (@lem356731) (@lem356757 A B P f x x')). Qed.
Lemma lem356759 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term261 A B P f x) = (term642 A B P f x).
Proof. exact (fun_ext (fun x' : B => @lem356758 A B P f x x')). Qed.
Lemma lem356760 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem356761 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term272 A B P f x) = (term643 A B P f x).
Proof. exact (MK_COMB (@lem356760 B) (@lem356759 A B P f x)). Qed.
Lemma lem356762 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem356763 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term274 A B P f x) = (term644 A B P f x).
Proof. exact (MK_COMB (@lem356762) (@lem356761 A B P f x)). Qed.
Lemma lem356764 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) : (term275 A B _7729 P f x) = (term645 A B _7729 P f x).
Proof. exact (MK_COMB (@lem356763 A B P f x) (@lem356730 A B _7729 P f x)). Qed.
Lemma lem356765 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) : (term276 A B _7729 P f) = (term646 A B _7729 P f).
Proof. exact (fun_ext (fun x : A => @lem356764 A B _7729 P f x)). Qed.
Lemma lem356766 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem356767 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) : (term277 A B _7729 P f) = (term647 A B _7729 P f).
Proof. exact (MK_COMB (@lem356766 A) (@lem356765 A B _7729 P f)). Qed.
Lemma lem356768 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) : (term278 A B _7729 P) = (term648 A B _7729 P).
Proof. exact (fun_ext (fun f : A -> B => @lem356767 A B _7729 P f)). Qed.
Lemma lem356769 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem356770 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) : (term279 A B _7729 P) = (term649 A B _7729 P).
Proof. exact (MK_COMB (@lem356769 A B) (@lem356768 A B _7729 P)). Qed.
Lemma lem356771 {A B : Type'} (_7729 : type103 A B) : (term280 A B _7729) = (term650 A B _7729).
Proof. exact (fun_ext (fun P : type547 A B => @lem356770 A B _7729 P)). Qed.
Lemma lem356772 {A B : Type'} : (@all ((A -> B) -> A -> B -> Prop)) = (@all ((A -> B) -> A -> B -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> A -> B -> Prop))). Qed.
Lemma lem356773 {A B : Type'} (_7729 : type103 A B) : (term281 A B _7729) = (term651 A B _7729).
Proof. exact (MK_COMB (@lem356772 A B) (@lem356771 A B _7729)). Qed.
Lemma lem356774 {A B : Type'} (_7729 : type103 A B) (h1 : term182 A B _7729) : term651 A B _7729.
Proof. exact (EQ_MP (@lem356773 A B _7729) (@lem355738 A B _7729 h1)). Qed.
Lemma lem356784 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem356793 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem356794 {A B : Type'} (f : type103 A B) (x : type547 A B) : (f x) = (@I (((A -> B) -> A -> B -> Prop) -> (A -> B) -> A -> B) f x).
Proof. exact (@lem356793 (type547 A B) (type549 A B) f x). Qed.
Lemma lem356795 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) : (_7729 P) = (@I (((A -> B) -> A -> B -> Prop) -> (A -> B) -> A -> B) _7729 P).
Proof. exact (@lem356794 A B _7729 P). Qed.
Lemma lem356796 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem356797 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) : (_7729 P f) = (@I (((A -> B) -> A -> B -> Prop) -> (A -> B) -> A -> B) _7729 P f).
Proof. exact (MK_COMB (@lem356795 A B _7729 P) (@lem356796 A B f)). Qed.
Lemma lem356799 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem356800 {A B : Type'} (f : type549 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> A -> B) f x).
Proof. exact (@lem356799 (A -> B) (A -> B) f x). Qed.
Lemma lem356801 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) : (@I (((A -> B) -> A -> B -> Prop) -> (A -> B) -> A -> B) _7729 P f) = (term632 A B _7729 P f).
Proof. exact (@lem356800 A B (@I (((A -> B) -> A -> B -> Prop) -> (A -> B) -> A -> B) _7729 P) f). Qed.
Lemma lem356802 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) : (_7729 P f) = (term632 A B _7729 P f).
Proof. exact (TRANS (@lem356797 A B _7729 P f) (@lem356801 A B _7729 P f)). Qed.
Lemma lem356803 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem356804 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) : (_7729 P f x) = (term633 A B _7729 P f x).
Proof. exact (MK_COMB (@lem356802 A B _7729 P f) (@lem356803 A x)). Qed.
Lemma lem356806 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem356807 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem356806 A B f x). Qed.
Lemma lem356808 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) : (term633 A B _7729 P f x) = (term634 A B _7729 P f x).
Proof. exact (@lem356807 A B (term632 A B _7729 P f) x). Qed.
Lemma lem356810 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) : (_7729 P f x) = (term634 A B _7729 P f x).
Proof. exact (TRANS (@lem356804 A B _7729 P f x) (@lem356808 A B _7729 P f x)). Qed.
Lemma lem356815 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem356817 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem356815 A B f x). Qed.
Lemma lem356818 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) : (term163 A B _7729 P f x) = (term652 A B _7729 P f x).
Proof. exact (MK_COMB (@lem356784 B) (@lem356810 A B _7729 P f x)). Qed.
Lemma lem356819 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) : ((_7729 P f x) = (f x)) = ((term634 A B _7729 P f x) = (@I (A -> B) f x)).
Proof. exact (MK_COMB (@lem356818 A B _7729 P f x) (@lem356817 A B f x)). Qed.
Lemma lem356820 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) : (term185 A B _7729 P f) = (term653 A B _7729 P f).
Proof. exact (fun_ext (fun x : A => @lem356819 A B _7729 P f x)). Qed.
Lemma lem356821 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem356822 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) : (term186 A B _7729 P f) = (term654 A B _7729 P f).
Proof. exact (MK_COMB (@lem356821 A) (@lem356820 A B _7729 P f)). Qed.
Lemma lem356823 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (h1 : term186 A B _7729 P f) : term654 A B _7729 P f.
Proof. exact (EQ_MP (@lem356822 A B _7729 P f) (@lem356532 A B _7729 P f h1)). Qed.
Lemma lem356824 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem356833 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem356834 {A B : Type'} (f : type547 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> A -> B -> Prop) f x).
Proof. exact (@lem356833 (A -> B) (type1413 A B) f x). Qed.
Lemma lem356835 {A B : Type'} (P : type547 A B) (f : A -> B) : (P f) = (@I ((A -> B) -> A -> B -> Prop) P f).
Proof. exact (@lem356834 A B P f). Qed.
Lemma lem356836 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem356837 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (P f x) = (@I ((A -> B) -> A -> B -> Prop) P f x).
Proof. exact (MK_COMB (@lem356835 A B P f) (@lem356836 A x)). Qed.
Lemma lem356839 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem356840 {A B : Type'} (f : type1413 A B) (x : A) : (f x) = (@I (A -> B -> Prop) f x).
Proof. exact (@lem356839 A (B -> Prop) f x). Qed.
Lemma lem356841 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (@I ((A -> B) -> A -> B -> Prop) P f x) = (term636 A B P f x).
Proof. exact (@lem356840 A B (@I ((A -> B) -> A -> B -> Prop) P f) x). Qed.
Lemma lem356842 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (P f x) = (term636 A B P f x).
Proof. exact (TRANS (@lem356837 A B P f x) (@lem356841 A B P f x)). Qed.
Lemma lem356843 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem356844 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (y : B) : (P f x y) = (term639 A B P f x y).
Proof. exact (MK_COMB (@lem356842 A B P f x) (@lem356843 B y)). Qed.
Lemma lem356846 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem356847 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem356846 B Prop f x). Qed.
Lemma lem356848 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (y : B) : (term639 A B P f x y) = (term640 A B P f x y).
Proof. exact (@lem356847 B (term636 A B P f x) y). Qed.
Lemma lem356850 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (y : B) : (P f x y) = (term640 A B P f x y).
Proof. exact (TRANS (@lem356844 A B P f x y) (@lem356848 A B P f x y)). Qed.
Lemma lem356851 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (y : B) : (term263 A B P f x y) = (term641 A B P f x y).
Proof. exact (MK_COMB (@lem356824) (@lem356850 A B P f x y)). Qed.
Lemma lem356852 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term261 A B P f x) = (term642 A B P f x).
Proof. exact (fun_ext (fun y : B => @lem356851 A B P f x y)). Qed.
Lemma lem356853 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem356854 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term272 A B P f x) = (term643 A B P f x).
Proof. exact (MK_COMB (@lem356853 B) (@lem356852 A B P f x)). Qed.
Lemma lem356855 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (h1 : term247 A B P f x) : term643 A B P f x.
Proof. exact (EQ_MP (@lem356854 A B P f x) (@lem356675 A B P f x h1)). Qed.
Lemma lem356863 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem356864 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem356863 A B f x). Qed.
Lemma lem356866 {A B : Type'} (y : A -> B) (y' : A) : (y y') = (@I (A -> B) y y').
Proof. exact (@lem356864 A B y y'). Qed.
Lemma lem356868 {A B : Type'} (P : type547 A B) (f : A -> B) (y : A) : (P f y) = (P f y).
Proof. exact (eq_refl (P f y)). Qed.
Lemma lem356869 {A B : Type'} (P : type547 A B) (f : A -> B) (y : A -> B) (y' : A) : (term655 A B P f y y') = (term656 A B P f y y').
Proof. exact (MK_COMB (@lem356868 A B P f y') (@lem356866 A B y y')). Qed.
Lemma lem356871 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem356872 {A B : Type'} (f : type547 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> A -> B -> Prop) f x).
Proof. exact (@lem356871 (A -> B) (type1413 A B) f x). Qed.
Lemma lem356873 {A B : Type'} (P : type547 A B) (f : A -> B) : (P f) = (@I ((A -> B) -> A -> B -> Prop) P f).
Proof. exact (@lem356872 A B P f). Qed.
Lemma lem356874 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem356875 {A B : Type'} (P : type547 A B) (f : A -> B) (y : A) : (P f y) = (@I ((A -> B) -> A -> B -> Prop) P f y).
Proof. exact (MK_COMB (@lem356873 A B P f) (@lem356874 A y)). Qed.
Lemma lem356877 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem356878 {A B : Type'} (f : type1413 A B) (x : A) : (f x) = (@I (A -> B -> Prop) f x).
Proof. exact (@lem356877 A (B -> Prop) f x). Qed.
Lemma lem356879 {A B : Type'} (P : type547 A B) (f : A -> B) (y : A) : (@I ((A -> B) -> A -> B -> Prop) P f y) = (term636 A B P f y).
Proof. exact (@lem356878 A B (@I ((A -> B) -> A -> B -> Prop) P f) y). Qed.
Lemma lem356880 {A B : Type'} (P : type547 A B) (f : A -> B) (y : A) : (P f y) = (term636 A B P f y).
Proof. exact (TRANS (@lem356875 A B P f y) (@lem356879 A B P f y)). Qed.
Lemma lem356881 {A B : Type'} (y : A -> B) (y' : A) : (@I (A -> B) y y') = (@I (A -> B) y y').
Proof. exact (eq_refl (@I (A -> B) y y')). Qed.
Lemma lem356882 {A B : Type'} (P : type547 A B) (f : A -> B) (y : A -> B) (y' : A) : (term656 A B P f y y') = (term657 A B P f y y').
Proof. exact (MK_COMB (@lem356880 A B P f y') (@lem356881 A B y y')). Qed.
Lemma lem356884 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem356885 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem356884 B Prop f x). Qed.
Lemma lem356886 {A B : Type'} (P : type547 A B) (f : A -> B) (y : A -> B) (y' : A) : (term657 A B P f y y') = (term658 A B P f y y').
Proof. exact (@lem356885 B (term636 A B P f y') (@I (A -> B) y y')). Qed.
Lemma lem356887 {A B : Type'} (P : type547 A B) (f : A -> B) (y : A -> B) (y' : A) : (term656 A B P f y y') = (term658 A B P f y y').
Proof. exact (TRANS (@lem356882 A B P f y y') (@lem356886 A B P f y y')). Qed.
Lemma lem356888 {A B : Type'} (P : type547 A B) (f : A -> B) (y : A -> B) (y' : A) : (term655 A B P f y y') = (term658 A B P f y y').
Proof. exact (TRANS (@lem356869 A B P f y y') (@lem356887 A B P f y y')). Qed.
Lemma lem356889 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem356896 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem356897 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem356896 A (A -> Prop) f x). Qed.
Lemma lem356898 {A : Type'} (lt2 : type1402 A) (y : A) : (lt2 y) = (@I (A -> A -> Prop) lt2 y).
Proof. exact (@lem356897 A lt2 y). Qed.
Lemma lem356899 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem356900 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (lt2 y x) = (@I (A -> A -> Prop) lt2 y x).
Proof. exact (MK_COMB (@lem356898 A lt2 y) (@lem356899 A x)). Qed.
Lemma lem356902 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem356903 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem356902 A Prop f x). Qed.
Lemma lem356904 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (@I (A -> A -> Prop) lt2 y x) = (term659 A lt2 y x).
Proof. exact (@lem356903 A (@I (A -> A -> Prop) lt2 y) x). Qed.
Lemma lem356906 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (lt2 y x) = (term659 A lt2 y x).
Proof. exact (TRANS (@lem356900 A lt2 y x) (@lem356904 A lt2 y x)). Qed.
Lemma lem356907 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (term596 A lt2 y x) = (term660 A lt2 y x).
Proof. exact (MK_COMB (@lem356889) (@lem356906 A lt2 y x)). Qed.
Lemma lem356908 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem356909 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (term590 A lt2 y x) = (term661 A lt2 y x).
Proof. exact (MK_COMB (@lem356908) (@lem356907 A lt2 y x)). Qed.
Lemma lem356910 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (y : A -> B) (y' : A) : (term619 A B lt2 x P f y y') = (term662 A B lt2 x P f y y').
Proof. exact (MK_COMB (@lem356909 A lt2 y' x) (@lem356888 A B P f y y')). Qed.
Lemma lem356911 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (y : A -> B) : (term621 A B lt2 x P f y) = (term663 A B lt2 x P f y).
Proof. exact (fun_ext (fun y' : A => @lem356910 A B lt2 x P f y y')). Qed.
Lemma lem356912 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem356913 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (y : A -> B) : (term623 A B lt2 x P f y) = (term664 A B lt2 x P f y).
Proof. exact (MK_COMB (@lem356912 A) (@lem356911 A B lt2 x P f y)). Qed.
Lemma lem356914 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (y : A -> B) (h1 : term623 A B lt2 x P f y) : term664 A B lt2 x P f y.
Proof. exact (EQ_MP (@lem356913 A B lt2 x P f y) (@lem356676 A B lt2 x P f y h1)). Qed.
Lemma lem356924 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem356925 {A B : Type'} (f : type549 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> A -> B) f x).
Proof. exact (@lem356924 (A -> B) (A -> B) f x). Qed.
Lemma lem356926 {A B : Type'} (y' : type549 A B) (f : A -> B) : (y' f) = (@I ((A -> B) -> A -> B) y' f).
Proof. exact (@lem356925 A B y' f). Qed.
Lemma lem356927 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem356928 {A B : Type'} (y' : type549 A B) (f : A -> B) (x : A) : (y' f x) = (@I ((A -> B) -> A -> B) y' f x).
Proof. exact (MK_COMB (@lem356926 A B y' f) (@lem356927 A x)). Qed.
Lemma lem356930 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem356931 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem356930 A B f x). Qed.
Lemma lem356932 {A B : Type'} (y' : type549 A B) (f : A -> B) (x : A) : (@I ((A -> B) -> A -> B) y' f x) = (term665 A B y' f x).
Proof. exact (@lem356931 A B (@I ((A -> B) -> A -> B) y' f) x). Qed.
Lemma lem356934 {A B : Type'} (y' : type549 A B) (f : A -> B) (x : A) : (y' f x) = (term665 A B y' f x).
Proof. exact (TRANS (@lem356928 A B y' f x) (@lem356932 A B y' f x)). Qed.
Lemma lem356936 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (P f x) = (P f x).
Proof. exact (eq_refl (P f x)). Qed.
Lemma lem356937 {A B : Type'} (P : type547 A B) (y' : type549 A B) (f : A -> B) (x : A) : (term666 A B P y' f x) = (term667 A B P y' f x).
Proof. exact (MK_COMB (@lem356936 A B P f x) (@lem356934 A B y' f x)). Qed.
Lemma lem356939 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem356940 {A B : Type'} (f : type547 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> A -> B -> Prop) f x).
Proof. exact (@lem356939 (A -> B) (type1413 A B) f x). Qed.
Lemma lem356941 {A B : Type'} (P : type547 A B) (f : A -> B) : (P f) = (@I ((A -> B) -> A -> B -> Prop) P f).
Proof. exact (@lem356940 A B P f). Qed.
Lemma lem356942 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem356943 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (P f x) = (@I ((A -> B) -> A -> B -> Prop) P f x).
Proof. exact (MK_COMB (@lem356941 A B P f) (@lem356942 A x)). Qed.
Lemma lem356945 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem356946 {A B : Type'} (f : type1413 A B) (x : A) : (f x) = (@I (A -> B -> Prop) f x).
Proof. exact (@lem356945 A (B -> Prop) f x). Qed.
Lemma lem356947 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (@I ((A -> B) -> A -> B -> Prop) P f x) = (term636 A B P f x).
Proof. exact (@lem356946 A B (@I ((A -> B) -> A -> B -> Prop) P f) x). Qed.
Lemma lem356948 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (P f x) = (term636 A B P f x).
Proof. exact (TRANS (@lem356943 A B P f x) (@lem356947 A B P f x)). Qed.
Lemma lem356949 {A B : Type'} (y' : type549 A B) (f : A -> B) (x : A) : (term665 A B y' f x) = (term665 A B y' f x).
Proof. exact (eq_refl (term665 A B y' f x)). Qed.
Lemma lem356950 {A B : Type'} (P : type547 A B) (y' : type549 A B) (f : A -> B) (x : A) : (term667 A B P y' f x) = (term668 A B P y' f x).
Proof. exact (MK_COMB (@lem356948 A B P f x) (@lem356949 A B y' f x)). Qed.
Lemma lem356952 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem356953 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem356952 B Prop f x). Qed.
Lemma lem356954 {A B : Type'} (P : type547 A B) (y' : type549 A B) (f : A -> B) (x : A) : (term668 A B P y' f x) = (term669 A B P y' f x).
Proof. exact (@lem356953 B (term636 A B P f x) (term665 A B y' f x)). Qed.
Lemma lem356955 {A B : Type'} (P : type547 A B) (y' : type549 A B) (f : A -> B) (x : A) : (term667 A B P y' f x) = (term669 A B P y' f x).
Proof. exact (TRANS (@lem356950 A B P y' f x) (@lem356954 A B P y' f x)). Qed.
Lemma lem356956 {A B : Type'} (P : type547 A B) (y' : type549 A B) (f : A -> B) (x : A) : (term666 A B P y' f x) = (term669 A B P y' f x).
Proof. exact (TRANS (@lem356937 A B P y' f x) (@lem356955 A B P y' f x)). Qed.
Lemma lem356957 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem356966 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem356967 {A B : Type'} (f : type548 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> A -> A) f x).
Proof. exact (@lem356966 (A -> B) (A -> A) f x). Qed.
Lemma lem356968 {A B : Type'} (z : type548 A B) (f : A -> B) : (z f) = (@I ((A -> B) -> A -> A) z f).
Proof. exact (@lem356967 A B z f). Qed.
Lemma lem356969 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem356970 {A B : Type'} (z : type548 A B) (f : A -> B) (x : A) : (z f x) = (@I ((A -> B) -> A -> A) z f x).
Proof. exact (MK_COMB (@lem356968 A B z f) (@lem356969 A x)). Qed.
Lemma lem356972 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem356973 {A : Type'} (f : A -> A) (x : A) : (f x) = (@I (A -> A) f x).
Proof. exact (@lem356972 A A f x). Qed.
Lemma lem356974 {A B : Type'} (z : type548 A B) (f : A -> B) (x : A) : (@I ((A -> B) -> A -> A) z f x) = (term670 A B z f x).
Proof. exact (@lem356973 A (@I ((A -> B) -> A -> A) z f) x). Qed.
Lemma lem356976 {A B : Type'} (z : type548 A B) (f : A -> B) (x : A) : (z f x) = (term670 A B z f x).
Proof. exact (TRANS (@lem356970 A B z f x) (@lem356974 A B z f x)). Qed.
Lemma lem356977 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem356984 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem356985 {A B : Type'} (f : type548 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> A -> A) f x).
Proof. exact (@lem356984 (A -> B) (A -> A) f x). Qed.
Lemma lem356986 {A B : Type'} (z : type548 A B) (f : A -> B) : (z f) = (@I ((A -> B) -> A -> A) z f).
Proof. exact (@lem356985 A B z f). Qed.
Lemma lem356987 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem356988 {A B : Type'} (z : type548 A B) (f : A -> B) (x : A) : (z f x) = (@I ((A -> B) -> A -> A) z f x).
Proof. exact (MK_COMB (@lem356986 A B z f) (@lem356987 A x)). Qed.
Lemma lem356990 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem356991 {A : Type'} (f : A -> A) (x : A) : (f x) = (@I (A -> A) f x).
Proof. exact (@lem356990 A A f x). Qed.
Lemma lem356992 {A B : Type'} (z : type548 A B) (f : A -> B) (x : A) : (@I ((A -> B) -> A -> A) z f x) = (term670 A B z f x).
Proof. exact (@lem356991 A (@I ((A -> B) -> A -> A) z f) x). Qed.
Lemma lem356994 {A B : Type'} (z : type548 A B) (f : A -> B) (x : A) : (z f x) = (term670 A B z f x).
Proof. exact (TRANS (@lem356988 A B z f x) (@lem356992 A B z f x)). Qed.
Lemma lem356995 {A B : Type'} (z : type548 A B) (f : A -> B) (x : A) : (term671 A B z f x) = (term672 A B z f x).
Proof. exact (MK_COMB (@lem356977 A B f) (@lem356994 A B z f x)). Qed.
Lemma lem356997 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem356998 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem356997 A B f x). Qed.
Lemma lem356999 {A B : Type'} (z : type548 A B) (f : A -> B) (x : A) : (term672 A B z f x) = (term673 A B z f x).
Proof. exact (@lem356998 A B f (term670 A B z f x)). Qed.
Lemma lem357000 {A B : Type'} (z : type548 A B) (f : A -> B) (x : A) : (term671 A B z f x) = (term673 A B z f x).
Proof. exact (TRANS (@lem356995 A B z f x) (@lem356999 A B z f x)). Qed.
Lemma lem357001 {A B : Type'} (P : type547 A B) (f : A -> B) : (P f) = (P f).
Proof. exact (eq_refl (P f)). Qed.
Lemma lem357002 {A B : Type'} (P : type547 A B) (z : type548 A B) (f : A -> B) (x : A) : (term674 A B P z f x) = (term675 A B P z f x).
Proof. exact (MK_COMB (@lem357001 A B P f) (@lem356976 A B z f x)). Qed.
Lemma lem357003 {A B : Type'} (P : type547 A B) (z : type548 A B) (f : A -> B) (x : A) : (term676 A B P z f x) = (term677 A B P z f x).
Proof. exact (MK_COMB (@lem357002 A B P z f x) (@lem357000 A B z f x)). Qed.
Lemma lem357005 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem357006 {A B : Type'} (f : type547 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> A -> B -> Prop) f x).
Proof. exact (@lem357005 (A -> B) (type1413 A B) f x). Qed.
Lemma lem357007 {A B : Type'} (P : type547 A B) (f : A -> B) : (P f) = (@I ((A -> B) -> A -> B -> Prop) P f).
Proof. exact (@lem357006 A B P f). Qed.
Lemma lem357008 {A B : Type'} (z : type548 A B) (f : A -> B) (x : A) : (term670 A B z f x) = (term670 A B z f x).
Proof. exact (eq_refl (term670 A B z f x)). Qed.
Lemma lem357009 {A B : Type'} (P : type547 A B) (z : type548 A B) (f : A -> B) (x : A) : (term675 A B P z f x) = (term678 A B P z f x).
Proof. exact (MK_COMB (@lem357007 A B P f) (@lem357008 A B z f x)). Qed.
Lemma lem357011 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem357012 {A B : Type'} (f : type1413 A B) (x : A) : (f x) = (@I (A -> B -> Prop) f x).
Proof. exact (@lem357011 A (B -> Prop) f x). Qed.
Lemma lem357013 {A B : Type'} (P : type547 A B) (z : type548 A B) (f : A -> B) (x : A) : (term678 A B P z f x) = (term679 A B P z f x).
Proof. exact (@lem357012 A B (@I ((A -> B) -> A -> B -> Prop) P f) (term670 A B z f x)). Qed.
Lemma lem357014 {A B : Type'} (P : type547 A B) (z : type548 A B) (f : A -> B) (x : A) : (term675 A B P z f x) = (term679 A B P z f x).
Proof. exact (TRANS (@lem357009 A B P z f x) (@lem357013 A B P z f x)). Qed.
Lemma lem357015 {A B : Type'} (z : type548 A B) (f : A -> B) (x : A) : (term673 A B z f x) = (term673 A B z f x).
Proof. exact (eq_refl (term673 A B z f x)). Qed.
Lemma lem357016 {A B : Type'} (P : type547 A B) (z : type548 A B) (f : A -> B) (x : A) : (term677 A B P z f x) = (term680 A B P z f x).
Proof. exact (MK_COMB (@lem357014 A B P z f x) (@lem357015 A B z f x)). Qed.
Lemma lem357018 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem357019 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem357018 B Prop f x). Qed.
Lemma lem357020 {A B : Type'} (P : type547 A B) (z : type548 A B) (f : A -> B) (x : A) : (term680 A B P z f x) = (term681 A B P z f x).
Proof. exact (@lem357019 B (term679 A B P z f x) (term673 A B z f x)). Qed.
Lemma lem357021 {A B : Type'} (P : type547 A B) (z : type548 A B) (f : A -> B) (x : A) : (term677 A B P z f x) = (term681 A B P z f x).
Proof. exact (TRANS (@lem357016 A B P z f x) (@lem357020 A B P z f x)). Qed.
Lemma lem357022 {A B : Type'} (P : type547 A B) (z : type548 A B) (f : A -> B) (x : A) : (term676 A B P z f x) = (term681 A B P z f x).
Proof. exact (TRANS (@lem357003 A B P z f x) (@lem357021 A B P z f x)). Qed.
Lemma lem357023 {A B : Type'} (P : type547 A B) (z : type548 A B) (f : A -> B) (x : A) : (term682 A B P z f x) = (term683 A B P z f x).
Proof. exact (MK_COMB (@lem356957) (@lem357022 A B P z f x)). Qed.
Lemma lem357024 {A : Type'} (lt2 : type1402 A) : lt2 = lt2.
Proof. exact (eq_refl lt2). Qed.
Lemma lem357031 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem357032 {A B : Type'} (f : type548 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> A -> A) f x).
Proof. exact (@lem357031 (A -> B) (A -> A) f x). Qed.
Lemma lem357033 {A B : Type'} (z : type548 A B) (f : A -> B) : (z f) = (@I ((A -> B) -> A -> A) z f).
Proof. exact (@lem357032 A B z f). Qed.
Lemma lem357034 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem357035 {A B : Type'} (z : type548 A B) (f : A -> B) (x : A) : (z f x) = (@I ((A -> B) -> A -> A) z f x).
Proof. exact (MK_COMB (@lem357033 A B z f) (@lem357034 A x)). Qed.
Lemma lem357037 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem357038 {A : Type'} (f : A -> A) (x : A) : (f x) = (@I (A -> A) f x).
Proof. exact (@lem357037 A A f x). Qed.
Lemma lem357039 {A B : Type'} (z : type548 A B) (f : A -> B) (x : A) : (@I ((A -> B) -> A -> A) z f x) = (term670 A B z f x).
Proof. exact (@lem357038 A (@I ((A -> B) -> A -> A) z f) x). Qed.
Lemma lem357041 {A B : Type'} (z : type548 A B) (f : A -> B) (x : A) : (z f x) = (term670 A B z f x).
Proof. exact (TRANS (@lem357035 A B z f x) (@lem357039 A B z f x)). Qed.
Lemma lem357042 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem357043 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (f : A -> B) (x : A) : (term684 A B lt2 z f x) = (term685 A B lt2 z f x).
Proof. exact (MK_COMB (@lem357024 A lt2) (@lem357041 A B z f x)). Qed.
Lemma lem357044 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (f : A -> B) (x : A) : (term686 A B lt2 z f x) = (term687 A B lt2 z f x).
Proof. exact (MK_COMB (@lem357043 A B lt2 z f x) (@lem357042 A x)). Qed.
Lemma lem357046 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem357047 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem357046 A (A -> Prop) f x). Qed.
Lemma lem357048 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (f : A -> B) (x : A) : (term685 A B lt2 z f x) = (term688 A B lt2 z f x).
Proof. exact (@lem357047 A lt2 (term670 A B z f x)). Qed.
Lemma lem357049 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem357050 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (f : A -> B) (x : A) : (term687 A B lt2 z f x) = (term689 A B lt2 z f x).
Proof. exact (MK_COMB (@lem357048 A B lt2 z f x) (@lem357049 A x)). Qed.
Lemma lem357052 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem357053 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem357052 A Prop f x). Qed.
Lemma lem357054 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (f : A -> B) (x : A) : (term689 A B lt2 z f x) = (term690 A B lt2 z f x).
Proof. exact (@lem357053 A (term688 A B lt2 z f x) x). Qed.
Lemma lem357055 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (f : A -> B) (x : A) : (term687 A B lt2 z f x) = (term690 A B lt2 z f x).
Proof. exact (TRANS (@lem357050 A B lt2 z f x) (@lem357054 A B lt2 z f x)). Qed.
Lemma lem357056 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (f : A -> B) (x : A) : (term686 A B lt2 z f x) = (term690 A B lt2 z f x).
Proof. exact (TRANS (@lem357044 A B lt2 z f x) (@lem357055 A B lt2 z f x)). Qed.
Lemma lem357057 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem357058 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (f : A -> B) (x : A) : (term691 A B lt2 z f x) = (term692 A B lt2 z f x).
Proof. exact (MK_COMB (@lem357057) (@lem357056 A B lt2 z f x)). Qed.
Lemma lem357059 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (z : type548 A B) (f : A -> B) (x : A) : (term693 A B lt2 P z f x) = (term694 A B lt2 P z f x).
Proof. exact (MK_COMB (@lem357058 A B lt2 z f x) (@lem357023 A B P z f x)). Qed.
Lemma lem357060 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem357061 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (z : type548 A B) (f : A -> B) (x : A) : (term695 A B lt2 P z f x) = (term696 A B lt2 P z f x).
Proof. exact (MK_COMB (@lem357060) (@lem357059 A B lt2 P z f x)). Qed.
Lemma lem357062 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (y' : type549 A B) (f : A -> B) (x : A) : (term697 A B lt2 z P y' f x) = (term698 A B lt2 z P y' f x).
Proof. exact (MK_COMB (@lem357061 A B lt2 P z f x) (@lem356956 A B P y' f x)). Qed.
Lemma lem357063 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (y' : type549 A B) (f : A -> B) : (term699 A B lt2 z P y' f) = (term700 A B lt2 z P y' f).
Proof. exact (fun_ext (fun x : A => @lem357062 A B lt2 z P y' f x)). Qed.
Lemma lem357064 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem357065 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (y' : type549 A B) (f : A -> B) : (term580 A B lt2 z P y' f) = (term701 A B lt2 z P y' f).
Proof. exact (MK_COMB (@lem357064 A) (@lem357063 A B lt2 z P y' f)). Qed.
Lemma lem357066 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (y' : type549 A B) : (term582 A B lt2 z P y') = (term702 A B lt2 z P y').
Proof. exact (fun_ext (fun f : A -> B => @lem357065 A B lt2 z P y' f)). Qed.
Lemma lem357067 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem357068 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (y' : type549 A B) : (term584 A B lt2 z P y') = (term703 A B lt2 z P y').
Proof. exact (MK_COMB (@lem357067 A B) (@lem357066 A B lt2 z P y')). Qed.
Lemma lem357069 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (y' : type549 A B) (h1 : term584 A B lt2 z P y') : term703 A B lt2 z P y'.
Proof. exact (EQ_MP (@lem357068 A B lt2 z P y') (@lem356678 A B lt2 z P y' h1)). Qed.
Lemma lem357323 {A : Type'} (P : A -> Prop) (Q : Prop) : (term258 A P Q) = (term257 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem357324 {B : Type'} (P : B -> Prop) (Q : Prop) : (term258 B P Q) = (term257 B P Q).
Proof. exact (@lem357323 B P Q). Qed.
Lemma lem357325 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) : (term704 A B _7729 P f x) = (term705 A B _7729 P f x).
Proof. exact (@lem357324 B (term642 A B P f x) (term638 A B _7729 P f x)). Qed.
Lemma lem357326 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (x' : B) : (term706 A B P f x x') = (term641 A B P f x x').
Proof. exact (eq_refl (term706 A B P f x x')). Qed.
Lemma lem357327 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term707 A B P f x) = (term642 A B P f x).
Proof. exact (fun_ext (fun x' : B => @lem357326 A B P f x x')). Qed.
Lemma lem357328 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem357329 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term708 A B P f x) = (term643 A B P f x).
Proof. exact (MK_COMB (@lem357328 B) (@lem357327 A B P f x)). Qed.
Lemma lem357330 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem357331 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term709 A B P f x) = (term644 A B P f x).
Proof. exact (MK_COMB (@lem357330) (@lem357329 A B P f x)). Qed.
Lemma lem357332 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) : (term638 A B _7729 P f x) = (term638 A B _7729 P f x).
Proof. exact (eq_refl (term638 A B _7729 P f x)). Qed.
Lemma lem357333 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) : (term704 A B _7729 P f x) = (term645 A B _7729 P f x).
Proof. exact (MK_COMB (@lem357331 A B P f x) (@lem357332 A B _7729 P f x)). Qed.
Lemma lem357334 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem357335 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) : (term710 A B _7729 P f x) = (term711 A B _7729 P f x).
Proof. exact (MK_COMB (@lem357334) (@lem357333 A B _7729 P f x)). Qed.
Lemma lem357336 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (x' : B) : (term706 A B P f x x') = (term641 A B P f x x').
Proof. exact (eq_refl (term706 A B P f x x')). Qed.
Lemma lem357337 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem357338 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (x' : B) : (term712 A B P f x x') = (term713 A B P f x x').
Proof. exact (MK_COMB (@lem357337) (@lem357336 A B P f x x')). Qed.
Lemma lem357339 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) : (term638 A B _7729 P f x) = (term638 A B _7729 P f x).
Proof. exact (eq_refl (term638 A B _7729 P f x)). Qed.
Lemma lem357340 {A B : Type'} (x : B) (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x' : A) : (term714 A B x _7729 P f x') = (term715 A B x _7729 P f x').
Proof. exact (MK_COMB (@lem357338 A B P f x' x) (@lem357339 A B _7729 P f x')). Qed.
Lemma lem357341 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) : (term716 A B _7729 P f x) = (term717 A B _7729 P f x).
Proof. exact (fun_ext (fun x' : B => @lem357340 A B x' _7729 P f x)). Qed.
Lemma lem357342 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem357343 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) : (term705 A B _7729 P f x) = (term718 A B _7729 P f x).
Proof. exact (MK_COMB (@lem357342 B) (@lem357341 A B _7729 P f x)). Qed.
Lemma lem357344 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) : ((term704 A B _7729 P f x) = (term705 A B _7729 P f x)) = ((term645 A B _7729 P f x) = (term718 A B _7729 P f x)).
Proof. exact (MK_COMB (@lem357335 A B _7729 P f x) (@lem357343 A B _7729 P f x)). Qed.
Lemma lem357345 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) : (term645 A B _7729 P f x) = (term718 A B _7729 P f x).
Proof. exact (EQ_MP (@lem357344 A B _7729 P f x) (@lem357325 A B _7729 P f x)). Qed.
Lemma lem357346 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) : (term646 A B _7729 P f) = (term719 A B _7729 P f).
Proof. exact (fun_ext (fun x : A => @lem357345 A B _7729 P f x)). Qed.
Lemma lem357347 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem357348 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) : (term647 A B _7729 P f) = (term720 A B _7729 P f).
Proof. exact (MK_COMB (@lem357347 A) (@lem357346 A B _7729 P f)). Qed.
Lemma lem357349 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) : (term648 A B _7729 P) = (term721 A B _7729 P).
Proof. exact (fun_ext (fun f : A -> B => @lem357348 A B _7729 P f)). Qed.
Lemma lem357350 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem357351 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) : (term649 A B _7729 P) = (term722 A B _7729 P).
Proof. exact (MK_COMB (@lem357350 A B) (@lem357349 A B _7729 P)). Qed.
Lemma lem357352 {A B : Type'} (_7729 : type103 A B) : (term650 A B _7729) = (term723 A B _7729).
Proof. exact (fun_ext (fun P : type547 A B => @lem357351 A B _7729 P)). Qed.
Lemma lem357353 {A B : Type'} : (@all ((A -> B) -> A -> B -> Prop)) = (@all ((A -> B) -> A -> B -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> A -> B -> Prop))). Qed.
Lemma lem357354 {A B : Type'} (_7729 : type103 A B) : (term651 A B _7729) = (term724 A B _7729).
Proof. exact (MK_COMB (@lem357353 A B) (@lem357352 A B _7729)). Qed.
Lemma lem357361 {A B : Type'} (x : B) (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x' : A) : (term715 A B x _7729 P f x') = (term715 A B x _7729 P f x').
Proof. exact (eq_refl (term715 A B x _7729 P f x')). Qed.
Lemma lem357362 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) : (term717 A B _7729 P f x) = (term717 A B _7729 P f x).
Proof. exact (fun_ext (fun x' : B => @lem357361 A B x' _7729 P f x)). Qed.
Lemma lem357363 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem357364 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) : (term718 A B _7729 P f x) = (term718 A B _7729 P f x).
Proof. exact (MK_COMB (@lem357363 B) (@lem357362 A B _7729 P f x)). Qed.
Lemma lem357365 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) : (term719 A B _7729 P f) = (term719 A B _7729 P f).
Proof. exact (fun_ext (fun x : A => @lem357364 A B _7729 P f x)). Qed.
Lemma lem357366 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem357367 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) : (term720 A B _7729 P f) = (term720 A B _7729 P f).
Proof. exact (MK_COMB (@lem357366 A) (@lem357365 A B _7729 P f)). Qed.
Lemma lem357368 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) : (term721 A B _7729 P) = (term721 A B _7729 P).
Proof. exact (fun_ext (fun f : A -> B => @lem357367 A B _7729 P f)). Qed.
Lemma lem357369 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem357370 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) : (term722 A B _7729 P) = (term722 A B _7729 P).
Proof. exact (MK_COMB (@lem357369 A B) (@lem357368 A B _7729 P)). Qed.
Lemma lem357371 {A B : Type'} (_7729 : type103 A B) : (term723 A B _7729) = (term723 A B _7729).
Proof. exact (fun_ext (fun P : type547 A B => @lem357370 A B _7729 P)). Qed.
Lemma lem357372 {A B : Type'} : (@all ((A -> B) -> A -> B -> Prop)) = (@all ((A -> B) -> A -> B -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> A -> B -> Prop))). Qed.
Lemma lem357373 {A B : Type'} (_7729 : type103 A B) : (term724 A B _7729) = (term724 A B _7729).
Proof. exact (MK_COMB (@lem357372 A B) (@lem357371 A B _7729)). Qed.
Lemma lem357374 {A B : Type'} (_7729 : type103 A B) : (term651 A B _7729) = (term724 A B _7729).
Proof. exact (TRANS (@lem357354 A B _7729) (@lem357373 A B _7729)). Qed.
Lemma lem357375 {A B : Type'} (_7729 : type103 A B) (h1 : term182 A B _7729) : term724 A B _7729.
Proof. exact (EQ_MP (@lem357374 A B _7729) (@lem356774 A B _7729 h1)). Qed.
Lemma lem357381 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) : ((term634 A B _7729 P f x) = (@I (A -> B) f x)) = ((term634 A B _7729 P f x) = (@I (A -> B) f x)).
Proof. exact (eq_refl ((term634 A B _7729 P f x) = (@I (A -> B) f x))). Qed.
Lemma lem357382 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) : (term653 A B _7729 P f) = (term653 A B _7729 P f).
Proof. exact (fun_ext (fun x : A => @lem357381 A B _7729 P f x)). Qed.
Lemma lem357383 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem357385 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) : (term654 A B _7729 P f) = (term654 A B _7729 P f).
Proof. exact (MK_COMB (@lem357383 A) (@lem357382 A B _7729 P f)). Qed.
Lemma lem357386 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (h1 : term186 A B _7729 P f) : term654 A B _7729 P f.
Proof. exact (EQ_MP (@lem357385 A B _7729 P f) (@lem356823 A B _7729 P f h1)). Qed.
Lemma lem357388 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (y : B) : (term641 A B P f x y) = (term641 A B P f x y).
Proof. exact (eq_refl (term641 A B P f x y)). Qed.
Lemma lem357389 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term642 A B P f x) = (term642 A B P f x).
Proof. exact (fun_ext (fun y : B => @lem357388 A B P f x y)). Qed.
Lemma lem357390 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem357392 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) : (term643 A B P f x) = (term643 A B P f x).
Proof. exact (MK_COMB (@lem357390 B) (@lem357389 A B P f x)). Qed.
Lemma lem357393 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (h1 : term247 A B P f x) : term643 A B P f x.
Proof. exact (EQ_MP (@lem357392 A B P f x) (@lem356855 A B P f x h1)). Qed.
Lemma lem357401 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (y : A -> B) (y' : A) : (term662 A B lt2 x P f y y') = (term662 A B lt2 x P f y y').
Proof. exact (eq_refl (term662 A B lt2 x P f y y')). Qed.
Lemma lem357402 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (y : A -> B) : (term663 A B lt2 x P f y) = (term663 A B lt2 x P f y).
Proof. exact (fun_ext (fun y' : A => @lem357401 A B lt2 x P f y y')). Qed.
Lemma lem357403 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem357405 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (y : A -> B) : (term664 A B lt2 x P f y) = (term664 A B lt2 x P f y).
Proof. exact (MK_COMB (@lem357403 A) (@lem357402 A B lt2 x P f y)). Qed.
Lemma lem357406 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (y : A -> B) (h1 : term623 A B lt2 x P f y) : term664 A B lt2 x P f y.
Proof. exact (EQ_MP (@lem357405 A B lt2 x P f y) (@lem356914 A B lt2 x P f y h1)). Qed.
Lemma lem357424 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (y' : type549 A B) (f : A -> B) (x : A) : (term698 A B lt2 z P y' f x) = (term725 A B lt2 z P y' f x).
Proof. exact (@lem19699 (term690 A B lt2 z f x) (term683 A B P z f x) (term669 A B P y' f x)). Qed.
Lemma lem357425 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (y' : type549 A B) (f : A -> B) : (term700 A B lt2 z P y' f) = (term726 A B lt2 z P y' f).
Proof. exact (fun_ext (fun x : A => @lem357424 A B lt2 z P y' f x)). Qed.
Lemma lem357426 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem357427 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (y' : type549 A B) (f : A -> B) : (term701 A B lt2 z P y' f) = (term727 A B lt2 z P y' f).
Proof. exact (MK_COMB (@lem357426 A) (@lem357425 A B lt2 z P y' f)). Qed.
Lemma lem357428 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (y' : type549 A B) : (term702 A B lt2 z P y') = (term728 A B lt2 z P y').
Proof. exact (fun_ext (fun f : A -> B => @lem357427 A B lt2 z P y' f)). Qed.
Lemma lem357429 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem357431 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (y' : type549 A B) : (term703 A B lt2 z P y') = (term729 A B lt2 z P y').
Proof. exact (MK_COMB (@lem357429 A B) (@lem357428 A B lt2 z P y')). Qed.
Lemma lem357432 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (y' : type549 A B) (h1 : term584 A B lt2 z P y') : term729 A B lt2 z P y'.
Proof. exact (EQ_MP (@lem357431 A B lt2 z P y') (@lem357069 A B lt2 z P y' h1)). Qed.
Lemma lem357551 {A B : Type'} (_7730 : type547 A B) (_7729 : type103 A B) (h1 : term182 A B _7729) : term730 A B _7729 _7730.
Proof. exact (@lem357375 A B _7729 h1 _7730). Qed.
Lemma lem357552 {A B : Type'} (_7729 : type103 A B) (_7730 : type547 A B) : (term730 A B _7729 _7730) = (term722 A B _7729 _7730).
Proof. exact (eq_refl (term730 A B _7729 _7730)). Qed.
Lemma lem357553 {A B : Type'} (_7730 : type547 A B) (_7729 : type103 A B) (h1 : term182 A B _7729) : term722 A B _7729 _7730.
Proof. exact (EQ_MP (@lem357552 A B _7729 _7730) (@lem357551 A B _7730 _7729 h1)). Qed.
Lemma lem357554 {A B : Type'} (_7730 : type547 A B) (_7731 : A -> B) (_7729 : type103 A B) (h1 : term182 A B _7729) : term731 A B _7729 _7730 _7731.
Proof. exact (@lem357553 A B _7730 _7729 h1 _7731). Qed.
Lemma lem357555 {A B : Type'} (_7729 : type103 A B) (_7730 : type547 A B) (_7731 : A -> B) : (term731 A B _7729 _7730 _7731) = (term720 A B _7729 _7730 _7731).
Proof. exact (eq_refl (term731 A B _7729 _7730 _7731)). Qed.
Lemma lem357556 {A B : Type'} (_7730 : type547 A B) (_7731 : A -> B) (_7729 : type103 A B) (h1 : term182 A B _7729) : term720 A B _7729 _7730 _7731.
Proof. exact (EQ_MP (@lem357555 A B _7729 _7730 _7731) (@lem357554 A B _7730 _7731 _7729 h1)). Qed.
Lemma lem357557 {A B : Type'} (_7730 : type547 A B) (_7731 : A -> B) (_7732 : A) (_7729 : type103 A B) (h1 : term182 A B _7729) : term732 A B _7729 _7730 _7731 _7732.
Proof. exact (@lem357556 A B _7730 _7731 _7729 h1 _7732). Qed.
Lemma lem357558 {A B : Type'} (_7729 : type103 A B) (_7730 : type547 A B) (_7731 : A -> B) (_7732 : A) : (term732 A B _7729 _7730 _7731 _7732) = (term718 A B _7729 _7730 _7731 _7732).
Proof. exact (eq_refl (term732 A B _7729 _7730 _7731 _7732)). Qed.
Lemma lem357559 {A B : Type'} (_7730 : type547 A B) (_7731 : A -> B) (_7732 : A) (_7729 : type103 A B) (h1 : term182 A B _7729) : term718 A B _7729 _7730 _7731 _7732.
Proof. exact (EQ_MP (@lem357558 A B _7729 _7730 _7731 _7732) (@lem357557 A B _7730 _7731 _7732 _7729 h1)). Qed.
Lemma lem357560 {A B : Type'} (_7730 : type547 A B) (_7731 : A -> B) (_7732 : A) (_7733 : B) (_7729 : type103 A B) (h1 : term182 A B _7729) : term733 A B _7729 _7730 _7731 _7732 _7733.
Proof. exact (@lem357559 A B _7730 _7731 _7732 _7729 h1 _7733). Qed.
Lemma lem357561 {A B : Type'} (_7733 : B) (_7729 : type103 A B) (_7730 : type547 A B) (_7731 : A -> B) (_7732 : A) : (term733 A B _7729 _7730 _7731 _7732 _7733) = (term715 A B _7733 _7729 _7730 _7731 _7732).
Proof. exact (eq_refl (term733 A B _7729 _7730 _7731 _7732 _7733)). Qed.
Lemma lem357563 {A B : Type'} (_7734 : A) (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (h1 : term186 A B _7729 P f) : term734 A B _7729 P f _7734.
Proof. exact (@lem357386 A B _7729 P f h1 _7734). Qed.
Lemma lem357564 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (_7734 : A) : (term734 A B _7729 P f _7734) = ((term634 A B _7729 P f _7734) = (@I (A -> B) f _7734)).
Proof. exact (eq_refl (term734 A B _7729 P f _7734)). Qed.
Lemma lem357566 {A B : Type'} (_7735 : B) (P : type547 A B) (f : A -> B) (x : A) (h1 : term247 A B P f x) : term706 A B P f x _7735.
Proof. exact (@lem357393 A B P f x h1 _7735). Qed.
Lemma lem357567 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (_7735 : B) : (term706 A B P f x _7735) = (term641 A B P f x _7735).
Proof. exact (eq_refl (term706 A B P f x _7735)). Qed.
Lemma lem357569 {A B : Type'} (_7736 : A) (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (y : A -> B) (h1 : term623 A B lt2 x P f y) : term735 A B lt2 x P f y _7736.
Proof. exact (@lem357406 A B lt2 x P f y h1 _7736). Qed.
Lemma lem357570 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (y : A -> B) (_7736 : A) : (term735 A B lt2 x P f y _7736) = (term662 A B lt2 x P f y _7736).
Proof. exact (eq_refl (term735 A B lt2 x P f y _7736)). Qed.
Lemma lem357572 {A B : Type'} (_7737 : A -> B) (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (y' : type549 A B) (h1 : term584 A B lt2 z P y') : term736 A B lt2 z P y' _7737.
Proof. exact (@lem357432 A B lt2 z P y' h1 _7737). Qed.
Lemma lem357573 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (y' : type549 A B) (_7737 : A -> B) : (term736 A B lt2 z P y' _7737) = (term727 A B lt2 z P y' _7737).
Proof. exact (eq_refl (term736 A B lt2 z P y' _7737)). Qed.
Lemma lem357574 {A B : Type'} (_7737 : A -> B) (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (y' : type549 A B) (h1 : term584 A B lt2 z P y') : term727 A B lt2 z P y' _7737.
Proof. exact (EQ_MP (@lem357573 A B lt2 z P y' _7737) (@lem357572 A B _7737 lt2 z P y' h1)). Qed.
Lemma lem357575 {A B : Type'} (_7737 : A -> B) (_7738 : A) (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (y' : type549 A B) (h1 : term584 A B lt2 z P y') : term737 A B lt2 z P y' _7737 _7738.
Proof. exact (@lem357574 A B _7737 lt2 z P y' h1 _7738). Qed.
Lemma lem357576 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (y' : type549 A B) (_7737 : A -> B) (_7738 : A) : (term737 A B lt2 z P y' _7737 _7738) = (term725 A B lt2 z P y' _7737 _7738).
Proof. exact (eq_refl (term737 A B lt2 z P y' _7737 _7738)). Qed.
Lemma lem357577 {A B : Type'} (_7737 : A -> B) (_7738 : A) (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (y' : type549 A B) (h1 : term584 A B lt2 z P y') : term725 A B lt2 z P y' _7737 _7738.
Proof. exact (EQ_MP (@lem357576 A B lt2 z P y' _7737 _7738) (@lem357575 A B _7737 _7738 lt2 z P y' h1)). Qed.
Lemma lem357603 {A B : Type'} (_7733 : B) (_7730 : type547 A B) (_7731 : A -> B) (_7732 : A) (_7729 : type103 A B) (h1 : term182 A B _7729) : term715 A B _7733 _7729 _7730 _7731 _7732.
Proof. exact (EQ_MP (@lem357561 A B _7733 _7729 _7730 _7731 _7732) (@lem357560 A B _7730 _7731 _7732 _7733 _7729 h1)). Qed.
Lemma lem357609 {A B : Type'} (_7735 : B) (P : type547 A B) (f : A -> B) (x : A) (h1 : term247 A B P f x) : term641 A B P f x _7735.
Proof. exact (EQ_MP (@lem357567 A B P f x _7735) (@lem357566 A B _7735 P f x h1)). Qed.
Lemma lem357615 {A B : Type'} (_7736 : A) (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (y : A -> B) (h1 : term623 A B lt2 x P f y) : term662 A B lt2 x P f y _7736.
Proof. exact (EQ_MP (@lem357570 A B lt2 x P f y _7736) (@lem357569 A B _7736 lt2 x P f y h1)). Qed.
Lemma lem357661 {A B : Type'} (_7737 : A -> B) (_7738 : A) (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (y' : type549 A B) (h1 : term584 A B lt2 z P y') : term738 A B lt2 z P y' _7737 _7738.
Proof. exact (proj1 (@lem357577 A B _7737 _7738 lt2 z P y' h1)). Qed.
Lemma lem357667 {A B : Type'} (_7737 : A -> B) (_7738 : A) (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (y' : type549 A B) (h1 : term584 A B lt2 z P y') : term739 A B z P y' _7737 _7738.
Proof. exact (proj2 (@lem357577 A B _7737 _7738 lt2 z P y' h1)). Qed.
Lemma lem357706 {B : Type'} : (@I (B -> Prop)) = (@I (B -> Prop)).
Proof. exact (eq_refl (@I (B -> Prop))). Qed.
Lemma lem357707 {B : Type'} (_7751 : B -> Prop) (_7753 : B -> Prop) (h1 : _7751 = _7753) : _7751 = _7753.
Proof. exact (h1). Qed.
Lemma lem357708 {B : Type'} (_7752 : B) (_7754 : B) (h1 : _7752 = _7754) : _7752 = _7754.
Proof. exact (h1). Qed.
Lemma lem357709 {B : Type'} (_7751 : B -> Prop) (_7753 : B -> Prop) (h1 : _7751 = _7753) : (@I (B -> Prop) _7751) = (@I (B -> Prop) _7753).
Proof. exact (MK_COMB (@lem357706 B) (@lem357707 B _7751 _7753 h1)). Qed.
Lemma lem357710 {B : Type'} (_7752 : B) (_7754 : B) (_7751 : B -> Prop) (_7753 : B -> Prop) (h1 : _7752 = _7754) (h2 : _7751 = _7753) : (@I (B -> Prop) _7751 _7752) = (@I (B -> Prop) _7753 _7754).
Proof. exact (MK_COMB (@lem357709 B _7751 _7753 h2) (@lem357708 B _7752 _7754 h1)). Qed.
Lemma lem357712 (b : Prop) (a : Prop) : term740 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem357713 {B : Type'} (_7753 : B -> Prop) (_7754 : B) (_7751 : B -> Prop) (_7752 : B) : term741 B _7753 _7754 _7751 _7752.
Proof. exact (@lem357712 (@I (B -> Prop) _7753 _7754) (@I (B -> Prop) _7751 _7752)). Qed.
Lemma lem357714 {B : Type'} (_7752 : B) (_7754 : B) (_7751 : B -> Prop) (_7753 : B -> Prop) (h1 : _7752 = _7754) (h2 : _7751 = _7753) : term742 B _7753 _7754 _7751 _7752.
Proof. exact (@lem357713 B _7753 _7754 _7751 _7752 (@lem357710 B _7752 _7754 _7751 _7753 h1 h2)). Qed.
Lemma lem357715 {B : Type'} (_7753 : B -> Prop) (_7751 : B -> Prop) (_7752 : B) (_7754 : B) (h1 : _7752 = _7754) : term743 B _7753 _7754 _7751 _7752.
Proof. exact (fun h0 : _7751 = _7753 => @lem357714 B _7752 _7754 _7751 _7753 h1 h0). Qed.
Lemma lem357717 (a : Prop) (b : Prop) : (a -> b) = (term744 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem357718 {B : Type'} (_7753 : B -> Prop) (_7754 : B) (_7751 : B -> Prop) (_7752 : B) : (term743 B _7753 _7754 _7751 _7752) = (term745 B _7753 _7754 _7751 _7752).
Proof. exact (@lem357717 (_7751 = _7753) (term742 B _7753 _7754 _7751 _7752)). Qed.
Lemma lem357719 {B : Type'} (_7753 : B -> Prop) (_7751 : B -> Prop) (_7752 : B) (_7754 : B) (h1 : _7752 = _7754) : term745 B _7753 _7754 _7751 _7752.
Proof. exact (EQ_MP (@lem357718 B _7753 _7754 _7751 _7752) (@lem357715 B _7753 _7751 _7752 _7754 h1)). Qed.
Lemma lem357720 {B : Type'} (_7753 : B -> Prop) (_7754 : B) (_7751 : B -> Prop) (_7752 : B) : term746 B _7753 _7754 _7751 _7752.
Proof. exact (fun h0 : _7752 = _7754 => @lem357719 B _7753 _7751 _7752 _7754 h0). Qed.
Lemma lem357722 (a : Prop) (b : Prop) : (a -> b) = (term744 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem357723 {B : Type'} (_7753 : B -> Prop) (_7754 : B) (_7751 : B -> Prop) (_7752 : B) : (term746 B _7753 _7754 _7751 _7752) = (term747 B _7753 _7754 _7751 _7752).
Proof. exact (@lem357722 (_7752 = _7754) (term745 B _7753 _7754 _7751 _7752)). Qed.
Lemma lem357724 {B : Type'} (_7753 : B -> Prop) (_7754 : B) (_7751 : B -> Prop) (_7752 : B) : term747 B _7753 _7754 _7751 _7752.
Proof. exact (EQ_MP (@lem357723 B _7753 _7754 _7751 _7752) (@lem357720 B _7753 _7754 _7751 _7752)). Qed.
Lemma lem357889 {A B : Type'} (_7734 : A) (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (h1 : term186 A B _7729 P f) : (term634 A B _7729 P f _7734) = (@I (A -> B) f _7734).
Proof. exact (EQ_MP (@lem357564 A B _7729 P f _7734) (@lem357563 A B _7734 _7729 P f h1)). Qed.
Lemma lem357890 {A B : Type'} (_7734 : A) (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (h1 : term186 A B _7729 P f) : (term634 A B _7729 P f _7734) = (@I (A -> B) f _7734).
Proof. exact (@lem357889 A B _7734 _7729 P f h1). Qed.
Lemma lem357891 {A B : Type'} (z : type548 A B) (x : A) (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (h1 : term186 A B _7729 P f) : (term748 A B _7729 P z f x) = (term673 A B z f x).
Proof. exact (@lem357890 A B (term670 A B z f x) _7729 P f h1). Qed.
Lemma lem357892 {A B : Type'} (z : type548 A B) (x : A) (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (h1 : term186 A B _7729 P f) : term749 A B _7729 P z f x.
Proof. exact (fun h0 : term750 A B _7729 P z f x => @lem357891 A B z x _7729 P f h1). Qed.
Lemma lem357894 (p : Prop) : (term751 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem357895 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (z : type548 A B) (f : A -> B) (x : A) : (term749 A B _7729 P z f x) = ((term748 A B _7729 P z f x) = (term673 A B z f x)).
Proof. exact (@lem357894 ((term748 A B _7729 P z f x) = (term673 A B z f x))). Qed.
Lemma lem357896 {A B : Type'} (z : type548 A B) (x : A) (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (h1 : term186 A B _7729 P f) : (term748 A B _7729 P z f x) = (term673 A B z f x).
Proof. exact (EQ_MP (@lem357895 A B _7729 P z f x) (@lem357892 A B z x _7729 P f h1)). Qed.
Lemma lem357898 {B : Type'} (x : B -> Prop) : x = x.
Proof. exact (@lem21386 (B -> Prop) x). Qed.
Lemma lem357899 {B : Type'} (x : B -> Prop) : x = x.
Proof. exact (@lem357898 B x). Qed.
Lemma lem357900 {A B : Type'} (P : type547 A B) (z : type548 A B) (f : A -> B) (x : A) : (term679 A B P z f x) = (term679 A B P z f x).
Proof. exact (@lem357899 B (term679 A B P z f x)). Qed.
Lemma lem357901 {A B : Type'} (P : type547 A B) (z : type548 A B) (f : A -> B) (x : A) : term752 A B P z f x.
Proof. exact (fun h0 : term753 A B P z f x => @lem357900 A B P z f x). Qed.
Lemma lem357903 (p : Prop) : (term751 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem357904 {A B : Type'} (P : type547 A B) (z : type548 A B) (f : A -> B) (x : A) : (term752 A B P z f x) = ((term679 A B P z f x) = (term679 A B P z f x)).
Proof. exact (@lem357903 ((term679 A B P z f x) = (term679 A B P z f x))). Qed.
Lemma lem357905 {A B : Type'} (P : type547 A B) (z : type548 A B) (f : A -> B) (x : A) : (term679 A B P z f x) = (term679 A B P z f x).
Proof. exact (EQ_MP (@lem357904 A B P z f x) (@lem357901 A B P z f x)). Qed.
Lemma lem357908 {A B : Type'} (P : type547 A B) (y' : type549 A B) (f : A -> B) (x : A) (h1 : term754 A B P y' f x) : term754 A B P y' f x.
Proof. exact (h1). Qed.
Lemma lem357909 {A B : Type'} (P : type547 A B) (y' : type549 A B) (f : A -> B) (x : A) (h1 : term754 A B P y' f x) : term755 A B P y' f x.
Proof. exact (fun h0 : term669 A B P y' f x => @lem357908 A B P y' f x h1). Qed.
Lemma lem357911 (p : Prop) : (term756 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem357912 {A B : Type'} (P : type547 A B) (y' : type549 A B) (f : A -> B) (x : A) : (term755 A B P y' f x) = (term754 A B P y' f x).
Proof. exact (@lem357911 (term669 A B P y' f x)). Qed.
Lemma lem357913 {A B : Type'} (P : type547 A B) (y' : type549 A B) (f : A -> B) (x : A) (h1 : term754 A B P y' f x) : term754 A B P y' f x.
Proof. exact (EQ_MP (@lem357912 A B P y' f x) (@lem357909 A B P y' f x h1)). Qed.
Lemma lem357915 (b : Prop) (a : Prop) : (a \/ b) = (term757 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem357918 {A B : Type'} (P : type547 A B) (y' : type549 A B) (lt2 : type1402 A) (z : type548 A B) (_7737 : A -> B) (_7738 : A) : (term738 A B lt2 z P y' _7737 _7738) = (term758 A B P y' lt2 z _7737 _7738).
Proof. exact (@lem357915 (term669 A B P y' _7737 _7738) (term690 A B lt2 z _7737 _7738)). Qed.
Lemma lem357921 {A B : Type'} (_7737 : A -> B) (_7738 : A) (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (y' : type549 A B) (h1 : term584 A B lt2 z P y') : term758 A B P y' lt2 z _7737 _7738.
Proof. exact (EQ_MP (@lem357918 A B P y' lt2 z _7737 _7738) (@lem357661 A B _7737 _7738 lt2 z P y' h1)). Qed.
Lemma lem357922 {A B : Type'} (_7737 : A -> B) (_7738 : A) (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (y' : type549 A B) (h1 : term584 A B lt2 z P y') : term758 A B P y' lt2 z _7737 _7738.
Proof. exact (@lem357921 A B _7737 _7738 lt2 z P y' h1). Qed.
Lemma lem357923 {A B : Type'} (f : A -> B) (x : A) (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (y' : type549 A B) (h1 : term584 A B lt2 z P y') : term758 A B P y' lt2 z f x.
Proof. exact (@lem357922 A B f x lt2 z P y' h1). Qed.
Lemma lem357926 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (y' : type549 A B) (f : A -> B) (x : A) (h1 : term584 A B lt2 z P y') (h2 : term754 A B P y' f x) : term690 A B lt2 z f x.
Proof. exact (@lem357923 A B f x lt2 z P y' h1 (@lem357913 A B P y' f x h2)). Qed.
Lemma lem357927 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (y' : type549 A B) (f : A -> B) (x : A) (h1 : term584 A B lt2 z P y') (h2 : term754 A B P y' f x) : term759 A B lt2 z f x.
Proof. exact (fun h0 : term760 A B lt2 z f x => @lem357926 A B lt2 z P y' f x h1 h2). Qed.
Lemma lem357929 (p : Prop) : (term751 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem357930 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (f : A -> B) (x : A) : (term759 A B lt2 z f x) = (term690 A B lt2 z f x).
Proof. exact (@lem357929 (term690 A B lt2 z f x)). Qed.
Lemma lem357931 {A B : Type'} (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (y' : type549 A B) (f : A -> B) (x : A) (h1 : term584 A B lt2 z P y') (h2 : term754 A B P y' f x) : term690 A B lt2 z f x.
Proof. exact (EQ_MP (@lem357930 A B lt2 z f x) (@lem357927 A B lt2 z P y' f x h1 h2)). Qed.
Lemma lem357937 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem357938 {A B : Type'} (P : type547 A B) (f : A -> B) (y : A -> B) (lt2 : type1402 A) (_7736 : A) (x : A) : (term662 A B lt2 x P f y _7736) = (term761 A B P f y lt2 _7736 x).
Proof. exact (@lem357937 (term658 A B P f y _7736) (term660 A lt2 _7736 x)). Qed.
Lemma lem357944 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem357945 {A B : Type'} (P : type547 A B) (f : A -> B) (y : A -> B) (lt2 : type1402 A) (_7736 : A) (x : A) : (term762 A B lt2 x P f y _7736) = (term763 A B P f y lt2 _7736 x).
Proof. exact (MK_COMB (@lem357944) (@lem357938 A B P f y lt2 _7736 x)). Qed.
Lemma lem357951 {A B : Type'} (P : type547 A B) (f : A -> B) (y : A -> B) (lt2 : type1402 A) (_7736 : A) (x : A) : (term761 A B P f y lt2 _7736 x) = (term761 A B P f y lt2 _7736 x).
Proof. exact (eq_refl (term761 A B P f y lt2 _7736 x)). Qed.
Lemma lem357952 {A B : Type'} (P : type547 A B) (f : A -> B) (y : A -> B) (lt2 : type1402 A) (_7736 : A) (x : A) : ((term662 A B lt2 x P f y _7736) = (term761 A B P f y lt2 _7736 x)) = ((term761 A B P f y lt2 _7736 x) = (term761 A B P f y lt2 _7736 x)).
Proof. exact (MK_COMB (@lem357945 A B P f y lt2 _7736 x) (@lem357951 A B P f y lt2 _7736 x)). Qed.
Lemma lem357954 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem357955 (x : Prop) : (x = x) = True.
Proof. exact (@lem357954 Prop x). Qed.
Lemma lem357956 {A B : Type'} (P : type547 A B) (f : A -> B) (y : A -> B) (lt2 : type1402 A) (_7736 : A) (x : A) : ((term761 A B P f y lt2 _7736 x) = (term761 A B P f y lt2 _7736 x)) = True.
Proof. exact (@lem357955 (term761 A B P f y lt2 _7736 x)). Qed.
Lemma lem357957 {A B : Type'} (P : type547 A B) (f : A -> B) (y : A -> B) (lt2 : type1402 A) (_7736 : A) (x : A) : ((term662 A B lt2 x P f y _7736) = (term761 A B P f y lt2 _7736 x)) = True.
Proof. exact (TRANS (@lem357952 A B P f y lt2 _7736 x) (@lem357956 A B P f y lt2 _7736 x)). Qed.
Lemma lem357958 {A B : Type'} (P : type547 A B) (f : A -> B) (y : A -> B) (lt2 : type1402 A) (_7736 : A) (x : A) : True = ((term662 A B lt2 x P f y _7736) = (term761 A B P f y lt2 _7736 x)).
Proof. exact (SYM (@lem357957 A B P f y lt2 _7736 x)). Qed.
Lemma lem357959 {A B : Type'} (P : type547 A B) (f : A -> B) (y : A -> B) (lt2 : type1402 A) (_7736 : A) (x : A) : (term662 A B lt2 x P f y _7736) = (term761 A B P f y lt2 _7736 x).
Proof. exact (EQ_MP (@lem357958 A B P f y lt2 _7736 x) (@lem0)). Qed.
Lemma lem357960 {A B : Type'} (_7736 : A) (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (y : A -> B) (h1 : term623 A B lt2 x P f y) : term761 A B P f y lt2 _7736 x.
Proof. exact (EQ_MP (@lem357959 A B P f y lt2 _7736 x) (@lem357615 A B _7736 lt2 x P f y h1)). Qed.
Lemma lem357962 (b : Prop) (a : Prop) : (a \/ b) = (term757 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem357963 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (y : A -> B) (_7736 : A) : (term761 A B P f y lt2 _7736 x) = (term764 A B lt2 x P f y _7736).
Proof. exact (@lem357962 (term660 A lt2 _7736 x) (term658 A B P f y _7736)). Qed.
Lemma lem357965 (a : Prop) : (term213 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem357966 {A : Type'} (lt2 : type1402 A) (_7736 : A) (x : A) : (term765 A lt2 _7736 x) = (term659 A lt2 _7736 x).
Proof. exact (@lem357965 (term659 A lt2 _7736 x)). Qed.
Lemma lem357967 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem357968 {A : Type'} (lt2 : type1402 A) (_7736 : A) (x : A) : (term766 A lt2 _7736 x) = (term767 A lt2 _7736 x).
Proof. exact (MK_COMB (@lem357967) (@lem357966 A lt2 _7736 x)). Qed.
Lemma lem357969 {A B : Type'} (P : type547 A B) (f : A -> B) (y : A -> B) (_7736 : A) : (term658 A B P f y _7736) = (term658 A B P f y _7736).
Proof. exact (eq_refl (term658 A B P f y _7736)). Qed.
Lemma lem357970 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (y : A -> B) (_7736 : A) : (term764 A B lt2 x P f y _7736) = (term768 A B lt2 x P f y _7736).
Proof. exact (MK_COMB (@lem357968 A lt2 _7736 x) (@lem357969 A B P f y _7736)). Qed.
Lemma lem357971 {A B : Type'} (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (y : A -> B) (_7736 : A) : (term761 A B P f y lt2 _7736 x) = (term768 A B lt2 x P f y _7736).
Proof. exact (TRANS (@lem357963 A B lt2 x P f y _7736) (@lem357970 A B lt2 x P f y _7736)). Qed.
Lemma lem357974 {A B : Type'} (_7736 : A) (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (y : A -> B) (h1 : term623 A B lt2 x P f y) : term768 A B lt2 x P f y _7736.
Proof. exact (EQ_MP (@lem357971 A B lt2 x P f y _7736) (@lem357960 A B _7736 lt2 x P f y h1)). Qed.
Lemma lem357975 {A B : Type'} (_7736 : A) (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (y : A -> B) (h1 : term623 A B lt2 x P f y) : term768 A B lt2 x P f y _7736.
Proof. exact (@lem357974 A B _7736 lt2 x P f y h1). Qed.
Lemma lem357976 {A B : Type'} (z : type548 A B) (lt2 : type1402 A) (x : A) (P : type547 A B) (f : A -> B) (y : A -> B) (h1 : term623 A B lt2 x P f y) : term769 A B lt2 P y z f x.
Proof. exact (@lem357975 A B (term670 A B z f x) lt2 x P f y h1). Qed.
Lemma lem357979 {A B : Type'} (y : A -> B) (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (y' : type549 A B) (f : A -> B) (x : A) (h1 : term623 A B lt2 x P f y) (h2 : term584 A B lt2 z P y') (h3 : term754 A B P y' f x) : term770 A B P y z f x.
Proof. exact (@lem357976 A B z lt2 x P f y h1 (@lem357931 A B lt2 z P y' f x h2 h3)). Qed.
Lemma lem357980 {A B : Type'} (y : A -> B) (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (y' : type549 A B) (f : A -> B) (x : A) (h1 : term623 A B lt2 x P f y) (h2 : term584 A B lt2 z P y') (h3 : term754 A B P y' f x) : term771 A B P y z f x.
Proof. exact (fun h0 : term772 A B P y z f x => @lem357979 A B y lt2 z P y' f x h1 h2 h3). Qed.
Lemma lem357982 (p : Prop) : (term751 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem357983 {A B : Type'} (P : type547 A B) (y : A -> B) (z : type548 A B) (f : A -> B) (x : A) : (term771 A B P y z f x) = (term770 A B P y z f x).
Proof. exact (@lem357982 (term770 A B P y z f x)). Qed.
Lemma lem357984 {A B : Type'} (y : A -> B) (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (y' : type549 A B) (f : A -> B) (x : A) (h1 : term623 A B lt2 x P f y) (h2 : term584 A B lt2 z P y') (h3 : term754 A B P y' f x) : term770 A B P y z f x.
Proof. exact (EQ_MP (@lem357983 A B P y z f x) (@lem357980 A B y lt2 z P y' f x h1 h2 h3)). Qed.
Lemma lem357990 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem357991 {A B : Type'} (_7729 : type103 A B) (_7730 : type547 A B) (_7731 : A -> B) (_7732 : A) (_7733 : B) : (term715 A B _7733 _7729 _7730 _7731 _7732) = (term773 A B _7729 _7730 _7731 _7732 _7733).
Proof. exact (@lem357990 (term638 A B _7729 _7730 _7731 _7732) (term641 A B _7730 _7731 _7732 _7733)). Qed.
Lemma lem357997 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem357998 {A B : Type'} (_7729 : type103 A B) (_7730 : type547 A B) (_7731 : A -> B) (_7732 : A) (_7733 : B) : (term774 A B _7733 _7729 _7730 _7731 _7732) = (term775 A B _7729 _7730 _7731 _7732 _7733).
Proof. exact (MK_COMB (@lem357997) (@lem357991 A B _7729 _7730 _7731 _7732 _7733)). Qed.
Lemma lem358004 {A B : Type'} (_7729 : type103 A B) (_7730 : type547 A B) (_7731 : A -> B) (_7732 : A) (_7733 : B) : (term773 A B _7729 _7730 _7731 _7732 _7733) = (term773 A B _7729 _7730 _7731 _7732 _7733).
Proof. exact (eq_refl (term773 A B _7729 _7730 _7731 _7732 _7733)). Qed.
Lemma lem358005 {A B : Type'} (_7729 : type103 A B) (_7730 : type547 A B) (_7731 : A -> B) (_7732 : A) (_7733 : B) : ((term715 A B _7733 _7729 _7730 _7731 _7732) = (term773 A B _7729 _7730 _7731 _7732 _7733)) = ((term773 A B _7729 _7730 _7731 _7732 _7733) = (term773 A B _7729 _7730 _7731 _7732 _7733)).
Proof. exact (MK_COMB (@lem357998 A B _7729 _7730 _7731 _7732 _7733) (@lem358004 A B _7729 _7730 _7731 _7732 _7733)). Qed.
Lemma lem358007 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem358008 (x : Prop) : (x = x) = True.
Proof. exact (@lem358007 Prop x). Qed.
Lemma lem358009 {A B : Type'} (_7729 : type103 A B) (_7730 : type547 A B) (_7731 : A -> B) (_7732 : A) (_7733 : B) : ((term773 A B _7729 _7730 _7731 _7732 _7733) = (term773 A B _7729 _7730 _7731 _7732 _7733)) = True.
Proof. exact (@lem358008 (term773 A B _7729 _7730 _7731 _7732 _7733)). Qed.
Lemma lem358010 {A B : Type'} (_7729 : type103 A B) (_7730 : type547 A B) (_7731 : A -> B) (_7732 : A) (_7733 : B) : ((term715 A B _7733 _7729 _7730 _7731 _7732) = (term773 A B _7729 _7730 _7731 _7732 _7733)) = True.
Proof. exact (TRANS (@lem358005 A B _7729 _7730 _7731 _7732 _7733) (@lem358009 A B _7729 _7730 _7731 _7732 _7733)). Qed.
Lemma lem358011 {A B : Type'} (_7729 : type103 A B) (_7730 : type547 A B) (_7731 : A -> B) (_7732 : A) (_7733 : B) : True = ((term715 A B _7733 _7729 _7730 _7731 _7732) = (term773 A B _7729 _7730 _7731 _7732 _7733)).
Proof. exact (SYM (@lem358010 A B _7729 _7730 _7731 _7732 _7733)). Qed.
Lemma lem358012 {A B : Type'} (_7729 : type103 A B) (_7730 : type547 A B) (_7731 : A -> B) (_7732 : A) (_7733 : B) : (term715 A B _7733 _7729 _7730 _7731 _7732) = (term773 A B _7729 _7730 _7731 _7732 _7733).
Proof. exact (EQ_MP (@lem358011 A B _7729 _7730 _7731 _7732 _7733) (@lem0)). Qed.
Lemma lem358013 {A B : Type'} (_7730 : type547 A B) (_7731 : A -> B) (_7732 : A) (_7733 : B) (_7729 : type103 A B) (h1 : term182 A B _7729) : term773 A B _7729 _7730 _7731 _7732 _7733.
Proof. exact (EQ_MP (@lem358012 A B _7729 _7730 _7731 _7732 _7733) (@lem357603 A B _7733 _7730 _7731 _7732 _7729 h1)). Qed.
Lemma lem358015 (b : Prop) (a : Prop) : (a \/ b) = (term757 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem358016 {A B : Type'} (_7733 : B) (_7729 : type103 A B) (_7730 : type547 A B) (_7731 : A -> B) (_7732 : A) : (term773 A B _7729 _7730 _7731 _7732 _7733) = (term776 A B _7733 _7729 _7730 _7731 _7732).
Proof. exact (@lem358015 (term641 A B _7730 _7731 _7732 _7733) (term638 A B _7729 _7730 _7731 _7732)). Qed.
Lemma lem358018 (a : Prop) : (term213 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem358019 {A B : Type'} (_7730 : type547 A B) (_7731 : A -> B) (_7732 : A) (_7733 : B) : (term777 A B _7730 _7731 _7732 _7733) = (term640 A B _7730 _7731 _7732 _7733).
Proof. exact (@lem358018 (term640 A B _7730 _7731 _7732 _7733)). Qed.
Lemma lem358020 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem358021 {A B : Type'} (_7730 : type547 A B) (_7731 : A -> B) (_7732 : A) (_7733 : B) : (term778 A B _7730 _7731 _7732 _7733) = (term779 A B _7730 _7731 _7732 _7733).
Proof. exact (MK_COMB (@lem358020) (@lem358019 A B _7730 _7731 _7732 _7733)). Qed.
Lemma lem358022 {A B : Type'} (_7729 : type103 A B) (_7730 : type547 A B) (_7731 : A -> B) (_7732 : A) : (term638 A B _7729 _7730 _7731 _7732) = (term638 A B _7729 _7730 _7731 _7732).
Proof. exact (eq_refl (term638 A B _7729 _7730 _7731 _7732)). Qed.
Lemma lem358023 {A B : Type'} (_7733 : B) (_7729 : type103 A B) (_7730 : type547 A B) (_7731 : A -> B) (_7732 : A) : (term776 A B _7733 _7729 _7730 _7731 _7732) = (term780 A B _7733 _7729 _7730 _7731 _7732).
Proof. exact (MK_COMB (@lem358021 A B _7730 _7731 _7732 _7733) (@lem358022 A B _7729 _7730 _7731 _7732)). Qed.
Lemma lem358024 {A B : Type'} (_7733 : B) (_7729 : type103 A B) (_7730 : type547 A B) (_7731 : A -> B) (_7732 : A) : (term773 A B _7729 _7730 _7731 _7732 _7733) = (term780 A B _7733 _7729 _7730 _7731 _7732).
Proof. exact (TRANS (@lem358016 A B _7733 _7729 _7730 _7731 _7732) (@lem358023 A B _7733 _7729 _7730 _7731 _7732)). Qed.
Lemma lem358027 {A B : Type'} (_7733 : B) (_7730 : type547 A B) (_7731 : A -> B) (_7732 : A) (_7729 : type103 A B) (h1 : term182 A B _7729) : term780 A B _7733 _7729 _7730 _7731 _7732.
Proof. exact (EQ_MP (@lem358024 A B _7733 _7729 _7730 _7731 _7732) (@lem358013 A B _7730 _7731 _7732 _7733 _7729 h1)). Qed.
Lemma lem358028 {A B : Type'} (_7733 : B) (_7730 : type547 A B) (_7731 : A -> B) (_7732 : A) (_7729 : type103 A B) (h1 : term182 A B _7729) : term780 A B _7733 _7729 _7730 _7731 _7732.
Proof. exact (@lem358027 A B _7733 _7730 _7731 _7732 _7729 h1). Qed.
Lemma lem358029 {A B : Type'} (y : A -> B) (P : type547 A B) (z : type548 A B) (f : A -> B) (x : A) (_7729 : type103 A B) (h1 : term182 A B _7729) : term781 A B y _7729 P z f x.
Proof. exact (@lem358028 A B (term782 A B y z f x) P f (term670 A B z f x) _7729 h1). Qed.
Lemma lem358032 {A B : Type'} (y : A -> B) (lt2 : type1402 A) (z : type548 A B) (_7729 : type103 A B) (P : type547 A B) (y' : type549 A B) (f : A -> B) (x : A) (h1 : term623 A B lt2 x P f y) (h2 : term584 A B lt2 z P y') (h3 : term182 A B _7729) (h4 : term754 A B P y' f x) : term783 A B _7729 P z f x.
Proof. exact (@lem358029 A B y P z f x _7729 h3 (@lem357984 A B y lt2 z P y' f x h1 h2 h4)). Qed.
Lemma lem358033 {A B : Type'} (y : A -> B) (lt2 : type1402 A) (z : type548 A B) (_7729 : type103 A B) (P : type547 A B) (y' : type549 A B) (f : A -> B) (x : A) (h1 : term623 A B lt2 x P f y) (h2 : term584 A B lt2 z P y') (h3 : term182 A B _7729) (h4 : term754 A B P y' f x) : term784 A B _7729 P z f x.
Proof. exact (fun h0 : term785 A B _7729 P z f x => @lem358032 A B y lt2 z _7729 P y' f x h1 h2 h3 h4). Qed.
Lemma lem358035 (p : Prop) : (term751 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem358036 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (z : type548 A B) (f : A -> B) (x : A) : (term784 A B _7729 P z f x) = (term783 A B _7729 P z f x).
Proof. exact (@lem358035 (term783 A B _7729 P z f x)). Qed.
Lemma lem358037 {A B : Type'} (y : A -> B) (lt2 : type1402 A) (z : type548 A B) (_7729 : type103 A B) (P : type547 A B) (y' : type549 A B) (f : A -> B) (x : A) (h1 : term623 A B lt2 x P f y) (h2 : term584 A B lt2 z P y') (h3 : term182 A B _7729) (h4 : term754 A B P y' f x) : term783 A B _7729 P z f x.
Proof. exact (EQ_MP (@lem358036 A B _7729 P z f x) (@lem358033 A B y lt2 z _7729 P y' f x h1 h2 h3 h4)). Qed.
Lemma lem358055 (q : Prop) (p : Prop) (r : Prop) : (term786 p q r) = (term786 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem358056 {B : Type'} (_7754 : B) (_7753 : B -> Prop) (_7751 : B -> Prop) (_7752 : B) : (term745 B _7753 _7754 _7751 _7752) = (term787 B _7754 _7753 _7751 _7752).
Proof. exact (@lem358055 (@I (B -> Prop) _7753 _7754) (term788 B _7751 _7753) (term789 B _7751 _7752)). Qed.
Lemma lem358074 {B : Type'} (_7752 : B) (_7754 : B) : (term790 B _7752 _7754) = (term790 B _7752 _7754).
Proof. exact (eq_refl (term790 B _7752 _7754)). Qed.
Lemma lem358075 {B : Type'} (_7754 : B) (_7753 : B -> Prop) (_7751 : B -> Prop) (_7752 : B) : (term747 B _7753 _7754 _7751 _7752) = (term791 B _7754 _7753 _7751 _7752).
Proof. exact (MK_COMB (@lem358074 B _7752 _7754) (@lem358056 B _7754 _7753 _7751 _7752)). Qed.
Lemma lem358079 (q : Prop) (p : Prop) (r : Prop) : (term786 p q r) = (term786 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem358080 {B : Type'} (_7754 : B) (_7753 : B -> Prop) (_7751 : B -> Prop) (_7752 : B) : (term791 B _7754 _7753 _7751 _7752) = (term792 B _7754 _7753 _7751 _7752).
Proof. exact (@lem358079 (@I (B -> Prop) _7753 _7754) (term793 B _7752 _7754) (term794 B _7753 _7751 _7752)). Qed.
Lemma lem358110 {B : Type'} (_7754 : B) (_7753 : B -> Prop) (_7751 : B -> Prop) (_7752 : B) : (term747 B _7753 _7754 _7751 _7752) = (term792 B _7754 _7753 _7751 _7752).
Proof. exact (TRANS (@lem358075 B _7754 _7753 _7751 _7752) (@lem358080 B _7754 _7753 _7751 _7752)). Qed.
Lemma lem358111 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem358112 {B : Type'} (_7754 : B) (_7753 : B -> Prop) (_7751 : B -> Prop) (_7752 : B) : (term795 B _7753 _7754 _7751 _7752) = (term796 B _7754 _7753 _7751 _7752).
Proof. exact (MK_COMB (@lem358111) (@lem358110 B _7754 _7753 _7751 _7752)). Qed.
Lemma lem358142 {B : Type'} (_7754 : B) (_7753 : B -> Prop) (_7751 : B -> Prop) (_7752 : B) : (term792 B _7754 _7753 _7751 _7752) = (term792 B _7754 _7753 _7751 _7752).
Proof. exact (eq_refl (term792 B _7754 _7753 _7751 _7752)). Qed.
Lemma lem358143 {B : Type'} (_7754 : B) (_7753 : B -> Prop) (_7751 : B -> Prop) (_7752 : B) : ((term747 B _7753 _7754 _7751 _7752) = (term792 B _7754 _7753 _7751 _7752)) = ((term792 B _7754 _7753 _7751 _7752) = (term792 B _7754 _7753 _7751 _7752)).
Proof. exact (MK_COMB (@lem358112 B _7754 _7753 _7751 _7752) (@lem358142 B _7754 _7753 _7751 _7752)). Qed.
Lemma lem358145 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem358146 (x : Prop) : (x = x) = True.
Proof. exact (@lem358145 Prop x). Qed.
Lemma lem358147 {B : Type'} (_7754 : B) (_7753 : B -> Prop) (_7751 : B -> Prop) (_7752 : B) : ((term792 B _7754 _7753 _7751 _7752) = (term792 B _7754 _7753 _7751 _7752)) = True.
Proof. exact (@lem358146 (term792 B _7754 _7753 _7751 _7752)). Qed.
Lemma lem358148 {B : Type'} (_7754 : B) (_7753 : B -> Prop) (_7751 : B -> Prop) (_7752 : B) : ((term747 B _7753 _7754 _7751 _7752) = (term792 B _7754 _7753 _7751 _7752)) = True.
Proof. exact (TRANS (@lem358143 B _7754 _7753 _7751 _7752) (@lem358147 B _7754 _7753 _7751 _7752)). Qed.
Lemma lem358149 {B : Type'} (_7754 : B) (_7753 : B -> Prop) (_7751 : B -> Prop) (_7752 : B) : True = ((term747 B _7753 _7754 _7751 _7752) = (term792 B _7754 _7753 _7751 _7752)).
Proof. exact (SYM (@lem358148 B _7754 _7753 _7751 _7752)). Qed.
Lemma lem358150 {B : Type'} (_7754 : B) (_7753 : B -> Prop) (_7751 : B -> Prop) (_7752 : B) : (term747 B _7753 _7754 _7751 _7752) = (term792 B _7754 _7753 _7751 _7752).
Proof. exact (EQ_MP (@lem358149 B _7754 _7753 _7751 _7752) (@lem0)). Qed.
Lemma lem358151 {B : Type'} (_7754 : B) (_7753 : B -> Prop) (_7751 : B -> Prop) (_7752 : B) : term792 B _7754 _7753 _7751 _7752.
Proof. exact (EQ_MP (@lem358150 B _7754 _7753 _7751 _7752) (@lem357724 B _7753 _7754 _7751 _7752)). Qed.
Lemma lem358153 (b : Prop) (a : Prop) : (a \/ b) = (term757 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem358154 {B : Type'} (_7751 : B -> Prop) (_7752 : B) (_7753 : B -> Prop) (_7754 : B) : (term792 B _7754 _7753 _7751 _7752) = (term797 B _7751 _7752 _7753 _7754).
Proof. exact (@lem358153 (term798 B _7754 _7753 _7751 _7752) (@I (B -> Prop) _7753 _7754)). Qed.
Lemma lem358156 (a : Prop) (b : Prop) : (term799 a b) = (term800 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem358157 {B : Type'} (_7754 : B) (_7753 : B -> Prop) (_7751 : B -> Prop) (_7752 : B) : (term801 B _7754 _7753 _7751 _7752) = (term802 B _7754 _7753 _7751 _7752).
Proof. exact (@lem358156 (term793 B _7752 _7754) (term794 B _7753 _7751 _7752)). Qed.
Lemma lem358159 (a : Prop) : (term213 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem358160 {B : Type'} (_7752 : B) (_7754 : B) : (term803 B _7752 _7754) = (_7752 = _7754).
Proof. exact (@lem358159 (_7752 = _7754)). Qed.
Lemma lem358161 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem358162 {B : Type'} (_7752 : B) (_7754 : B) : (term804 B _7752 _7754) = (term805 B _7752 _7754).
Proof. exact (MK_COMB (@lem358161) (@lem358160 B _7752 _7754)). Qed.
Lemma lem358164 (a : Prop) (b : Prop) : (term799 a b) = (term800 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem358165 {B : Type'} (_7753 : B -> Prop) (_7751 : B -> Prop) (_7752 : B) : (term806 B _7753 _7751 _7752) = (term807 B _7753 _7751 _7752).
Proof. exact (@lem358164 (term788 B _7751 _7753) (term789 B _7751 _7752)). Qed.
Lemma lem358167 (a : Prop) : (term213 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem358168 {B : Type'} (_7751 : B -> Prop) (_7753 : B -> Prop) : (term808 B _7751 _7753) = (_7751 = _7753).
Proof. exact (@lem358167 (_7751 = _7753)). Qed.
Lemma lem358169 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem358170 {B : Type'} (_7751 : B -> Prop) (_7753 : B -> Prop) : (term809 B _7751 _7753) = (term810 B _7751 _7753).
Proof. exact (MK_COMB (@lem358169) (@lem358168 B _7751 _7753)). Qed.
Lemma lem358172 (a : Prop) : (term213 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem358173 {B : Type'} (_7751 : B -> Prop) (_7752 : B) : (term811 B _7751 _7752) = (@I (B -> Prop) _7751 _7752).
Proof. exact (@lem358172 (@I (B -> Prop) _7751 _7752)). Qed.
Lemma lem358174 {B : Type'} (_7753 : B -> Prop) (_7751 : B -> Prop) (_7752 : B) : (term807 B _7753 _7751 _7752) = (term812 B _7753 _7751 _7752).
Proof. exact (MK_COMB (@lem358170 B _7751 _7753) (@lem358173 B _7751 _7752)). Qed.
Lemma lem358175 {B : Type'} (_7753 : B -> Prop) (_7751 : B -> Prop) (_7752 : B) : (term806 B _7753 _7751 _7752) = (term812 B _7753 _7751 _7752).
Proof. exact (TRANS (@lem358165 B _7753 _7751 _7752) (@lem358174 B _7753 _7751 _7752)). Qed.
Lemma lem358176 {B : Type'} (_7754 : B) (_7753 : B -> Prop) (_7751 : B -> Prop) (_7752 : B) : (term802 B _7754 _7753 _7751 _7752) = (term813 B _7754 _7753 _7751 _7752).
Proof. exact (MK_COMB (@lem358162 B _7752 _7754) (@lem358175 B _7753 _7751 _7752)). Qed.
Lemma lem358177 {B : Type'} (_7754 : B) (_7753 : B -> Prop) (_7751 : B -> Prop) (_7752 : B) : (term801 B _7754 _7753 _7751 _7752) = (term813 B _7754 _7753 _7751 _7752).
Proof. exact (TRANS (@lem358157 B _7754 _7753 _7751 _7752) (@lem358176 B _7754 _7753 _7751 _7752)). Qed.
Lemma lem358178 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem358179 {B : Type'} (_7754 : B) (_7753 : B -> Prop) (_7751 : B -> Prop) (_7752 : B) : (term814 B _7754 _7753 _7751 _7752) = (term815 B _7754 _7753 _7751 _7752).
Proof. exact (MK_COMB (@lem358178) (@lem358177 B _7754 _7753 _7751 _7752)). Qed.
Lemma lem358180 {B : Type'} (_7753 : B -> Prop) (_7754 : B) : (@I (B -> Prop) _7753 _7754) = (@I (B -> Prop) _7753 _7754).
Proof. exact (eq_refl (@I (B -> Prop) _7753 _7754)). Qed.
Lemma lem358181 {B : Type'} (_7751 : B -> Prop) (_7752 : B) (_7753 : B -> Prop) (_7754 : B) : (term797 B _7751 _7752 _7753 _7754) = (term816 B _7751 _7752 _7753 _7754).
Proof. exact (MK_COMB (@lem358179 B _7754 _7753 _7751 _7752) (@lem358180 B _7753 _7754)). Qed.
Lemma lem358182 {B : Type'} (_7751 : B -> Prop) (_7752 : B) (_7753 : B -> Prop) (_7754 : B) : (term792 B _7754 _7753 _7751 _7752) = (term816 B _7751 _7752 _7753 _7754).
Proof. exact (TRANS (@lem358154 B _7751 _7752 _7753 _7754) (@lem358181 B _7751 _7752 _7753 _7754)). Qed.
Lemma lem358184 {A B : Type'} (y : A -> B) (lt2 : type1402 A) (z : type548 A B) (_7729 : type103 A B) (P : type547 A B) (y' : type549 A B) (f : A -> B) (x : A) (h1 : term623 A B lt2 x P f y) (h2 : term584 A B lt2 z P y') (h3 : term182 A B _7729) (h4 : term754 A B P y' f x) : term817 A B _7729 P z f x.
Proof. exact (conj (@lem357905 A B P z f x) (@lem358037 A B y lt2 z _7729 P y' f x h1 h2 h3 h4)). Qed.
Lemma lem358185 {A B : Type'} (y : A -> B) (lt2 : type1402 A) (z : type548 A B) (_7729 : type103 A B) (P : type547 A B) (y' : type549 A B) (f : A -> B) (x : A) (h1 : term186 A B _7729 P f) (h2 : term623 A B lt2 x P f y) (h3 : term584 A B lt2 z P y') (h4 : term182 A B _7729) (h5 : term754 A B P y' f x) : term818 A B _7729 P z f x.
Proof. exact (conj (@lem357896 A B z x _7729 P f h1) (@lem358184 A B y lt2 z _7729 P y' f x h2 h3 h4 h5)). Qed.
Lemma lem358187 {B : Type'} (_7751 : B -> Prop) (_7752 : B) (_7753 : B -> Prop) (_7754 : B) : term816 B _7751 _7752 _7753 _7754.
Proof. exact (EQ_MP (@lem358182 B _7751 _7752 _7753 _7754) (@lem358151 B _7754 _7753 _7751 _7752)). Qed.
Lemma lem358188 {B : Type'} (_7751 : B -> Prop) (_7752 : B) (_7753 : B -> Prop) (_7754 : B) : term816 B _7751 _7752 _7753 _7754.
Proof. exact (@lem358187 B _7751 _7752 _7753 _7754). Qed.
Lemma lem358189 {A B : Type'} (_7729 : type103 A B) (P : type547 A B) (z : type548 A B) (f : A -> B) (x : A) : term819 A B _7729 P z f x.
Proof. exact (@lem358188 B (term679 A B P z f x) (term748 A B _7729 P z f x) (term679 A B P z f x) (term673 A B z f x)). Qed.
Lemma lem358192 {A B : Type'} (y : A -> B) (lt2 : type1402 A) (z : type548 A B) (_7729 : type103 A B) (P : type547 A B) (y' : type549 A B) (f : A -> B) (x : A) (h1 : term186 A B _7729 P f) (h2 : term623 A B lt2 x P f y) (h3 : term584 A B lt2 z P y') (h4 : term182 A B _7729) (h5 : term754 A B P y' f x) : term681 A B P z f x.
Proof. exact (@lem358189 A B _7729 P z f x (@lem358185 A B y lt2 z _7729 P y' f x h1 h2 h3 h4 h5)). Qed.
Lemma lem358193 {A B : Type'} (y : A -> B) (lt2 : type1402 A) (z : type548 A B) (_7729 : type103 A B) (P : type547 A B) (y' : type549 A B) (f : A -> B) (x : A) (h1 : term186 A B _7729 P f) (h2 : term623 A B lt2 x P f y) (h3 : term584 A B lt2 z P y') (h4 : term182 A B _7729) (h5 : term754 A B P y' f x) : term820 A B P z f x.
Proof. exact (fun h0 : term683 A B P z f x => @lem358192 A B y lt2 z _7729 P y' f x h1 h2 h3 h4 h5). Qed.
Lemma lem358195 (p : Prop) : (term751 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem358196 {A B : Type'} (P : type547 A B) (z : type548 A B) (f : A -> B) (x : A) : (term820 A B P z f x) = (term681 A B P z f x).
Proof. exact (@lem358195 (term681 A B P z f x)). Qed.
Lemma lem358197 {A B : Type'} (y : A -> B) (lt2 : type1402 A) (z : type548 A B) (_7729 : type103 A B) (P : type547 A B) (y' : type549 A B) (f : A -> B) (x : A) (h1 : term186 A B _7729 P f) (h2 : term623 A B lt2 x P f y) (h3 : term584 A B lt2 z P y') (h4 : term182 A B _7729) (h5 : term754 A B P y' f x) : term681 A B P z f x.
Proof. exact (EQ_MP (@lem358196 A B P z f x) (@lem358193 A B y lt2 z _7729 P y' f x h1 h2 h3 h4 h5)). Qed.
Lemma lem358203 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem358204 {A B : Type'} (y' : type549 A B) (P : type547 A B) (z : type548 A B) (_7737 : A -> B) (_7738 : A) : (term739 A B z P y' _7737 _7738) = (term821 A B y' P z _7737 _7738).
Proof. exact (@lem358203 (term669 A B P y' _7737 _7738) (term683 A B P z _7737 _7738)). Qed.
Lemma lem358210 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem358211 {A B : Type'} (y' : type549 A B) (P : type547 A B) (z : type548 A B) (_7737 : A -> B) (_7738 : A) : (term822 A B z P y' _7737 _7738) = (term823 A B y' P z _7737 _7738).
Proof. exact (MK_COMB (@lem358210) (@lem358204 A B y' P z _7737 _7738)). Qed.
Lemma lem358217 {A B : Type'} (y' : type549 A B) (P : type547 A B) (z : type548 A B) (_7737 : A -> B) (_7738 : A) : (term821 A B y' P z _7737 _7738) = (term821 A B y' P z _7737 _7738).
Proof. exact (eq_refl (term821 A B y' P z _7737 _7738)). Qed.
Lemma lem358218 {A B : Type'} (y' : type549 A B) (P : type547 A B) (z : type548 A B) (_7737 : A -> B) (_7738 : A) : ((term739 A B z P y' _7737 _7738) = (term821 A B y' P z _7737 _7738)) = ((term821 A B y' P z _7737 _7738) = (term821 A B y' P z _7737 _7738)).
Proof. exact (MK_COMB (@lem358211 A B y' P z _7737 _7738) (@lem358217 A B y' P z _7737 _7738)). Qed.
Lemma lem358220 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem358221 (x : Prop) : (x = x) = True.
Proof. exact (@lem358220 Prop x). Qed.
Lemma lem358222 {A B : Type'} (y' : type549 A B) (P : type547 A B) (z : type548 A B) (_7737 : A -> B) (_7738 : A) : ((term821 A B y' P z _7737 _7738) = (term821 A B y' P z _7737 _7738)) = True.
Proof. exact (@lem358221 (term821 A B y' P z _7737 _7738)). Qed.
Lemma lem358223 {A B : Type'} (y' : type549 A B) (P : type547 A B) (z : type548 A B) (_7737 : A -> B) (_7738 : A) : ((term739 A B z P y' _7737 _7738) = (term821 A B y' P z _7737 _7738)) = True.
Proof. exact (TRANS (@lem358218 A B y' P z _7737 _7738) (@lem358222 A B y' P z _7737 _7738)). Qed.
Lemma lem358224 {A B : Type'} (y' : type549 A B) (P : type547 A B) (z : type548 A B) (_7737 : A -> B) (_7738 : A) : True = ((term739 A B z P y' _7737 _7738) = (term821 A B y' P z _7737 _7738)).
Proof. exact (SYM (@lem358223 A B y' P z _7737 _7738)). Qed.
Lemma lem358225 {A B : Type'} (y' : type549 A B) (P : type547 A B) (z : type548 A B) (_7737 : A -> B) (_7738 : A) : (term739 A B z P y' _7737 _7738) = (term821 A B y' P z _7737 _7738).
Proof. exact (EQ_MP (@lem358224 A B y' P z _7737 _7738) (@lem0)). Qed.
Lemma lem358226 {A B : Type'} (_7737 : A -> B) (_7738 : A) (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (y' : type549 A B) (h1 : term584 A B lt2 z P y') : term821 A B y' P z _7737 _7738.
Proof. exact (EQ_MP (@lem358225 A B y' P z _7737 _7738) (@lem357667 A B _7737 _7738 lt2 z P y' h1)). Qed.
Lemma lem358228 (b : Prop) (a : Prop) : (a \/ b) = (term757 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem358229 {A B : Type'} (z : type548 A B) (P : type547 A B) (y' : type549 A B) (_7737 : A -> B) (_7738 : A) : (term821 A B y' P z _7737 _7738) = (term824 A B z P y' _7737 _7738).
Proof. exact (@lem358228 (term683 A B P z _7737 _7738) (term669 A B P y' _7737 _7738)). Qed.
Lemma lem358231 (a : Prop) : (term213 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem358232 {A B : Type'} (P : type547 A B) (z : type548 A B) (_7737 : A -> B) (_7738 : A) : (term825 A B P z _7737 _7738) = (term681 A B P z _7737 _7738).
Proof. exact (@lem358231 (term681 A B P z _7737 _7738)). Qed.
Lemma lem358233 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem358234 {A B : Type'} (P : type547 A B) (z : type548 A B) (_7737 : A -> B) (_7738 : A) : (term826 A B P z _7737 _7738) = (term827 A B P z _7737 _7738).
Proof. exact (MK_COMB (@lem358233) (@lem358232 A B P z _7737 _7738)). Qed.
Lemma lem358235 {A B : Type'} (P : type547 A B) (y' : type549 A B) (_7737 : A -> B) (_7738 : A) : (term669 A B P y' _7737 _7738) = (term669 A B P y' _7737 _7738).
Proof. exact (eq_refl (term669 A B P y' _7737 _7738)). Qed.
Lemma lem358236 {A B : Type'} (z : type548 A B) (P : type547 A B) (y' : type549 A B) (_7737 : A -> B) (_7738 : A) : (term824 A B z P y' _7737 _7738) = (term828 A B z P y' _7737 _7738).
Proof. exact (MK_COMB (@lem358234 A B P z _7737 _7738) (@lem358235 A B P y' _7737 _7738)). Qed.
Lemma lem358237 {A B : Type'} (z : type548 A B) (P : type547 A B) (y' : type549 A B) (_7737 : A -> B) (_7738 : A) : (term821 A B y' P z _7737 _7738) = (term828 A B z P y' _7737 _7738).
Proof. exact (TRANS (@lem358229 A B z P y' _7737 _7738) (@lem358236 A B z P y' _7737 _7738)). Qed.
Lemma lem358240 {A B : Type'} (_7737 : A -> B) (_7738 : A) (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (y' : type549 A B) (h1 : term584 A B lt2 z P y') : term828 A B z P y' _7737 _7738.
Proof. exact (EQ_MP (@lem358237 A B z P y' _7737 _7738) (@lem358226 A B _7737 _7738 lt2 z P y' h1)). Qed.
Lemma lem358241 {A B : Type'} (_7737 : A -> B) (_7738 : A) (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (y' : type549 A B) (h1 : term584 A B lt2 z P y') : term828 A B z P y' _7737 _7738.
Proof. exact (@lem358240 A B _7737 _7738 lt2 z P y' h1). Qed.
Lemma lem358242 {A B : Type'} (f : A -> B) (x : A) (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (y' : type549 A B) (h1 : term584 A B lt2 z P y') : term828 A B z P y' f x.
Proof. exact (@lem358241 A B f x lt2 z P y' h1). Qed.
Lemma lem358245 {A B : Type'} (y : A -> B) (lt2 : type1402 A) (z : type548 A B) (_7729 : type103 A B) (P : type547 A B) (y' : type549 A B) (f : A -> B) (x : A) (h1 : term186 A B _7729 P f) (h2 : term623 A B lt2 x P f y) (h3 : term584 A B lt2 z P y') (h4 : term182 A B _7729) (h5 : term754 A B P y' f x) : term669 A B P y' f x.
Proof. exact (@lem358242 A B f x lt2 z P y' h3 (@lem358197 A B y lt2 z _7729 P y' f x h1 h2 h3 h4 h5)). Qed.
Lemma lem358246 {A B : Type'} (x : A) (f : A -> B) (y : A -> B) (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (y' : type549 A B) (_7729 : type103 A B) (h1 : term186 A B _7729 P f) (h2 : term623 A B lt2 x P f y) (h3 : term584 A B lt2 z P y') (h4 : term182 A B _7729) : term829 A B P y' f x.
Proof. exact (fun h0 : term754 A B P y' f x => @lem358245 A B y lt2 z _7729 P y' f x h1 h2 h3 h4 h0). Qed.
Lemma lem358248 (p : Prop) : (term751 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem358249 {A B : Type'} (P : type547 A B) (y' : type549 A B) (f : A -> B) (x : A) : (term829 A B P y' f x) = (term669 A B P y' f x).
Proof. exact (@lem358248 (term669 A B P y' f x)). Qed.
Lemma lem358250 {A B : Type'} (x : A) (f : A -> B) (y : A -> B) (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (y' : type549 A B) (_7729 : type103 A B) (h1 : term186 A B _7729 P f) (h2 : term623 A B lt2 x P f y) (h3 : term584 A B lt2 z P y') (h4 : term182 A B _7729) : term669 A B P y' f x.
Proof. exact (EQ_MP (@lem358249 A B P y' f x) (@lem358246 A B x f y lt2 z P y' _7729 h1 h2 h3 h4)). Qed.
Lemma lem358253 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem358255 {A B : Type'} (P : type547 A B) (f : A -> B) (x : A) (_7735 : B) : (term641 A B P f x _7735) = (term830 A B P f x _7735).
Proof. exact (@lem358253 (term640 A B P f x _7735)). Qed.
Lemma lem358258 {A B : Type'} (_7735 : B) (P : type547 A B) (f : A -> B) (x : A) (h1 : term247 A B P f x) : term830 A B P f x _7735.
Proof. exact (EQ_MP (@lem358255 A B P f x _7735) (@lem357609 A B _7735 P f x h1)). Qed.
Lemma lem358259 {A B : Type'} (_7735 : B) (P : type547 A B) (f : A -> B) (x : A) (h1 : term247 A B P f x) : term830 A B P f x _7735.
Proof. exact (@lem358258 A B _7735 P f x h1). Qed.
Lemma lem358260 {A B : Type'} (y' : type549 A B) (P : type547 A B) (f : A -> B) (x : A) (h1 : term247 A B P f x) : term831 A B P y' f x.
Proof. exact (@lem358259 A B (term665 A B y' f x) P f x h1). Qed.
Lemma lem358263 {A B : Type'} (y : A -> B) (lt2 : type1402 A) (z : type548 A B) (y' : type549 A B) (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) (h1 : term186 A B _7729 P f) (h2 : term623 A B lt2 x P f y) (h3 : term584 A B lt2 z P y') (h4 : term182 A B _7729) (h5 : term247 A B P f x) : False.
Proof. exact (@lem358260 A B y' P f x h5 (@lem358250 A B x f y lt2 z P y' _7729 h1 h2 h3 h4)). Qed.
Lemma lem358264 {A B : Type'} (y : A -> B) (lt2 : type1402 A) (z : type548 A B) (y' : type549 A B) (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) (h1 : term186 A B _7729 P f) (h2 : term623 A B lt2 x P f y) (h3 : term584 A B lt2 z P y') (h4 : term182 A B _7729) (h5 : term247 A B P f x) : term832.
Proof. exact (fun h0 : ~ False => @lem358263 A B y lt2 z y' _7729 P f x h1 h2 h3 h4 h5). Qed.
Lemma lem358266 (p : Prop) : (term751 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem358267 : term832 = False.
Proof. exact (@lem358266 False). Qed.
Lemma lem358268 {A B : Type'} (y : A -> B) (lt2 : type1402 A) (z : type548 A B) (y' : type549 A B) (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) (h1 : term186 A B _7729 P f) (h2 : term623 A B lt2 x P f y) (h3 : term584 A B lt2 z P y') (h4 : term182 A B _7729) (h5 : term247 A B P f x) : False.
Proof. exact (EQ_MP (@lem358267) (@lem358264 A B y lt2 z y' _7729 P f x h1 h2 h3 h4 h5)). Qed.
Lemma lem358269 {A B : Type'} (y : A -> B) (z : type548 A B) (y' : type549 A B) (lt2 : type1402 A) (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) (h1 : term186 A B _7729 P f) (h2 : term623 A B lt2 x P f y) (h3 : term584 A B lt2 z P y') (h4 : term7 A B lt2 P) (h5 : term182 A B _7729) (h6 : term247 A B P f x) : False.
Proof. exact (ex_elim (@lem356193 A B lt2 P h4) (fun z' : type515 A B => fun h0 : term443 A B lt2 P z' => @lem358268 A B y lt2 z y' _7729 P f x h1 h2 h3 h5 h6)). Qed.
Lemma lem358270 {A B : Type'} (y : A -> B) (_7729 : type103 A B) (lt2 : type1402 A) (z : type548 A B) (P : type547 A B) (f : A -> B) (x : A) (h1 : term186 A B _7729 P f) (h2 : term623 A B lt2 x P f y) (h3 : term7 A B lt2 P) (h4 : term182 A B _7729) (h5 : term587 A B lt2 z P) (h6 : term247 A B P f x) : False.
Proof. exact (ex_elim (@lem356677 A B lt2 z P h5) (fun y' : type549 A B => fun h0 : term586 A B lt2 z P y' => @lem358269 A B y z y' lt2 _7729 P f x h1 h2 h0 h3 h4 h6)). Qed.
Lemma lem358271 {A B : Type'} (y : A -> B) (lt2 : type1402 A) (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) (h1 : term186 A B _7729 P f) (h2 : term623 A B lt2 x P f y) (h3 : term6 A B lt2 P) (h4 : term7 A B lt2 P) (h5 : term182 A B _7729) (h6 : term247 A B P f x) : False.
Proof. exact (ex_elim (@lem356519 A B lt2 P h3) (fun z : type548 A B => fun h0 : term588 A B lt2 P z => @lem358270 A B y _7729 lt2 z P f x h1 h2 h4 h5 h0 h6)). Qed.
Lemma lem358272 {A B : Type'} (lt2 : type1402 A) (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) (h1 : term186 A B _7729 P f) (h2 : term126 A B lt2 x P f) (h3 : term6 A B lt2 P) (h4 : term7 A B lt2 P) (h5 : term182 A B _7729) (h6 : term247 A B P f x) : False.
Proof. exact (ex_elim (@lem356655 A B lt2 x P f h2) (fun y : A -> B => fun h0 : term625 A B lt2 x P f y => @lem358271 A B y lt2 _7729 P f x h1 h0 h3 h4 h5 h6)). Qed.
Lemma lem358273 {A B : Type'} (lt2 : type1402 A) (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) (h1 : term186 A B _7729 P f) (h2 : term126 A B lt2 x P f) (h3 : term6 A B lt2 P) (h4 : term7 A B lt2 P) (h5 : term182 A B _7729) (h6 : term247 A B P f x) : (term186 A B _7729 P f) = False.
Proof. exact (prop_ext (fun h7 : term186 A B _7729 P f => @lem358272 A B lt2 _7729 P f x h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem356532 A B _7729 P f h1)). Qed.
Lemma lem358274 {A B : Type'} (lt2 : type1402 A) (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) (h1 : term186 A B _7729 P f) (h2 : term126 A B lt2 x P f) (h3 : term6 A B lt2 P) (h4 : term7 A B lt2 P) (h5 : term182 A B _7729) (h6 : term247 A B P f x) : False.
Proof. exact (EQ_MP (@lem358273 A B lt2 _7729 P f x h1 h2 h3 h4 h5 h6) (@lem356532 A B _7729 P f h1)). Qed.
Lemma lem358275 {A B : Type'} (lt2 : type1402 A) (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) (h1 : term186 A B _7729 P f) (h2 : term126 A B lt2 x P f) (h3 : term6 A B lt2 P) (h4 : term7 A B lt2 P) (h5 : term182 A B _7729) (h6 : term247 A B P f x) : (term247 A B P f x) = False.
Proof. exact (prop_ext (fun h7 : term247 A B P f x => @lem358274 A B lt2 _7729 P f x h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem355590 A B P f x h6)). Qed.
Lemma lem358276 {A B : Type'} (lt2 : type1402 A) (_7729 : type103 A B) (P : type547 A B) (f : A -> B) (x : A) (h1 : term186 A B _7729 P f) (h2 : term126 A B lt2 x P f) (h3 : term6 A B lt2 P) (h4 : term7 A B lt2 P) (h5 : term182 A B _7729) (h6 : term247 A B P f x) : False.
Proof. exact (EQ_MP (@lem358275 A B lt2 _7729 P f x h1 h2 h3 h4 h5 h6) (@lem355590 A B P f x h6)). Qed.
Lemma lem358277 {A B : Type'} (x : A) (f : A -> B) (lt2 : type1402 A) (P : type547 A B) (_7729 : type103 A B) (h1 : term186 A B _7729 P f) (h2 : term126 A B lt2 x P f) (h3 : term6 A B lt2 P) (h4 : term7 A B lt2 P) (h5 : term182 A B _7729) : term246 A B P f x.
Proof. exact (fun h0 : term247 A B P f x => @lem358276 A B lt2 _7729 P f x h1 h2 h3 h4 h5 h0). Qed.
Lemma lem358278 {A B : Type'} (x : A) (f : A -> B) (lt2 : type1402 A) (P : type547 A B) (_7729 : type103 A B) (h1 : term186 A B _7729 P f) (h2 : term126 A B lt2 x P f) (h3 : term6 A B lt2 P) (h4 : term7 A B lt2 P) (h5 : term182 A B _7729) : term106 A B P f x.
Proof. exact (EQ_MP (@lem355589 A B P f x) (@lem358277 A B x f lt2 P _7729 h1 h2 h3 h4 h5)). Qed.
Lemma lem358279 {A B : Type'} (x : A) (f : A -> B) (lt2 : type1402 A) (P : type547 A B) (_7729 : type103 A B) (h1 : term186 A B _7729 P f) (h2 : term6 A B lt2 P) (h3 : term7 A B lt2 P) (h4 : term182 A B _7729) : term130 A B lt2 P f x.
Proof. exact (fun h0 : term126 A B lt2 x P f => @lem358278 A B x f lt2 P _7729 h1 h0 h2 h3 h4). Qed.
Lemma lem358284 {A B : Type'} (f : A -> B) (lt2 : type1402 A) (P : type547 A B) (_7729 : type103 A B) (h1 : term186 A B _7729 P f) (h2 : term6 A B lt2 P) (h3 : term7 A B lt2 P) (h4 : term182 A B _7729) : term134 A B lt2 P f.
Proof. exact (fun x : A => @lem358279 A B x f lt2 P _7729 h1 h2 h3 h4). Qed.
Lemma lem358285 {A B : Type'} (f : A -> B) (lt2 : type1402 A) (P : type547 A B) (_7729 : type103 A B) (h1 : term6 A B lt2 P) (h2 : term7 A B lt2 P) (h3 : term182 A B _7729) : term214 A B _7729 lt2 P f.
Proof. exact (fun h0 : term186 A B _7729 P f => @lem358284 A B f lt2 P _7729 h0 h1 h2 h3). Qed.
Lemma lem358286 {A B : Type'} (f : A -> B) (lt2 : type1402 A) (P : type547 A B) (_7729 : type103 A B) (h1 : term7 A B lt2 P) (h2 : term182 A B _7729) : term215 A B _7729 lt2 P f.
Proof. exact (fun h0 : term6 A B lt2 P => @lem358285 A B f lt2 P _7729 h0 h1 h2). Qed.
Lemma lem358287 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (_7729 : type103 A B) (h1 : term182 A B _7729) : term216 A B _7729 lt2 P f.
Proof. exact (fun h0 : term7 A B lt2 P => @lem358286 A B f lt2 P _7729 h0 h1). Qed.
Lemma lem358288 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (_7729 : type103 A B) (h1 : term182 A B _7729) : term217 A B _7729 lt2 P f.
Proof. exact (fun h0 : @WF A lt2 => @lem358287 A B lt2 P f _7729 h1). Qed.
Lemma lem358289 {A B : Type'} (_7729 : type103 A B) (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : term218 A B _7729 lt2 P f.
Proof. exact (fun h0 : term182 A B _7729 => @lem358288 A B lt2 P f _7729 h0). Qed.
Lemma lem358294 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : term221 A B lt2 P f.
Proof. exact (fun _7729 : type103 A B => @lem358289 A B _7729 lt2 P f). Qed.
Lemma lem358299 {A B : Type'} (P : type547 A B) (f : A -> B) : term225 A B P f.
Proof. exact (fun lt2 : type1402 A => @lem358294 A B lt2 P f). Qed.
Lemma lem358304 {A B : Type'} (f : A -> B) : term229 A B f.
Proof. exact (fun P : type547 A B => @lem358299 A B P f). Qed.
Lemma lem358309 {A B : Type'} : term233 A B.
Proof. exact (fun f : A -> B => @lem358304 A B f). Qed.
Lemma lem358310 {A B : Type'} : term232 A B.
Proof. exact (EQ_MP (@lem355579 A B) (@lem358309 A B)). Qed.
Lemma lem358311 {A B : Type'} (f : A -> B) : term833 A B f.
Proof. exact (@lem358310 A B f). Qed.
Lemma lem358312 {A B : Type'} (f : A -> B) : (term833 A B f) = (term228 A B f).
Proof. exact (eq_refl (term833 A B f)). Qed.
Lemma lem358313 {A B : Type'} (f : A -> B) : term228 A B f.
Proof. exact (EQ_MP (@lem358312 A B f) (@lem358311 A B f)). Qed.
Lemma lem358314 {A B : Type'} (f : A -> B) (P : type547 A B) : term834 A B f P.
Proof. exact (@lem358313 A B f P). Qed.
Lemma lem358315 {A B : Type'} (P : type547 A B) (f : A -> B) : (term834 A B f P) = (term224 A B P f).
Proof. exact (eq_refl (term834 A B f P)). Qed.
Lemma lem358316 {A B : Type'} (P : type547 A B) (f : A -> B) : term224 A B P f.
Proof. exact (EQ_MP (@lem358315 A B P f) (@lem358314 A B f P)). Qed.
Lemma lem358317 {A B : Type'} (P : type547 A B) (f : A -> B) (lt2 : type1402 A) : term835 A B P f lt2.
Proof. exact (@lem358316 A B P f lt2). Qed.
Lemma lem358318 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : (term835 A B P f lt2) = (term200 A B lt2 P f).
Proof. exact (eq_refl (term835 A B P f lt2)). Qed.
Lemma lem358319 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : term200 A B lt2 P f.
Proof. exact (EQ_MP (@lem358318 A B lt2 P f) (@lem358317 A B P f lt2)). Qed.
Lemma lem358321 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) : term157 A B lt2 P f.
Proof. exact (@lem355129 A B lt2 P f (@lem358319 A B lt2 P f)). Qed.
Lemma lem358322 {A B : Type'} (P : type547 A B) (f : A -> B) (lt2 : type1402 A) (h1 : @WF A lt2) : term195 A B lt2 P f.
Proof. exact (@lem358321 A B lt2 P f (@lem354331 A lt2 h1)). Qed.
Lemma lem358323 {A B : Type'} (f : A -> B) (P : type547 A B) (lt2 : type1402 A) (h1 : term7 A B lt2 P) (h2 : @WF A lt2) : term192 A B lt2 P f.
Proof. exact (@lem358322 A B P f lt2 h2 (@lem354334 A B lt2 P h1)). Qed.
Lemma lem358324 {A B : Type'} (f : A -> B) (P : type547 A B) (lt2 : type1402 A) (h1 : term6 A B lt2 P) (h2 : term7 A B lt2 P) (h3 : @WF A lt2) : term189 A B lt2 P f.
Proof. exact (@lem358323 A B f P lt2 h2 h3 (@lem354333 A B lt2 P h1)). Qed.
Lemma lem358325 {A B : Type'} (f : A -> B) (P : type547 A B) (lt2 : type1402 A) (h1 : term47 A B P f) (h2 : term6 A B lt2 P) (h3 : term7 A B lt2 P) (h4 : @WF A lt2) : term141 A B lt2 P f.
Proof. exact (@lem358324 A B f P lt2 h2 h3 h4 (@lem354583 A B P f h1)). Qed.
Lemma lem358326 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (h1 : term47 A B P f) (h2 : term6 A B lt2 P) (h3 : term7 A B lt2 P) (h4 : @WF A lt2) (h5 : term142 A B lt2 P f) : False.
Proof. exact (@lem358325 A B f P lt2 h1 h2 h3 h4 (@lem354661 A B lt2 P f h5)). Qed.
Lemma lem358327 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (h1 : term47 A B P f) (h2 : term6 A B lt2 P) (h3 : term7 A B lt2 P) (h4 : @WF A lt2) (h5 : term142 A B lt2 P f) : (term142 A B lt2 P f) = False.
Proof. exact (prop_ext (fun h6 : term142 A B lt2 P f => @lem358326 A B lt2 P f h1 h2 h3 h4 h5) (fun h6 : False => @lem354661 A B lt2 P f h5)). Qed.
Lemma lem358328 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (f : A -> B) (h1 : term47 A B P f) (h2 : term6 A B lt2 P) (h3 : term7 A B lt2 P) (h4 : @WF A lt2) (h5 : term142 A B lt2 P f) : False.
Proof. exact (EQ_MP (@lem358327 A B lt2 P f h1 h2 h3 h4 h5) (@lem354661 A B lt2 P f h5)). Qed.
Lemma lem358329 {A B : Type'} (f : A -> B) (P : type547 A B) (lt2 : type1402 A) (h1 : term47 A B P f) (h2 : term6 A B lt2 P) (h3 : term7 A B lt2 P) (h4 : @WF A lt2) : term141 A B lt2 P f.
Proof. exact (fun h0 : term142 A B lt2 P f => @lem358328 A B lt2 P f h1 h2 h3 h4 h0). Qed.
Lemma lem358330 {A B : Type'} (f : A -> B) (P : type547 A B) (lt2 : type1402 A) (h1 : term47 A B P f) (h2 : term6 A B lt2 P) (h3 : term7 A B lt2 P) (h4 : @WF A lt2) : term134 A B lt2 P f.
Proof. exact (EQ_MP (@lem354660 A B lt2 P f) (@lem358329 A B f P lt2 h1 h2 h3 h4)). Qed.
Lemma lem358331 {A B : Type'} (f : A -> B) (P : type547 A B) (lt2 : type1402 A) (h1 : term47 A B P f) (h2 : term6 A B lt2 P) (h3 : term7 A B lt2 P) (h4 : @WF A lt2) : term110 A B P f.
Proof. exact (@lem354656 A B P f lt2 h4 (@lem358330 A B f P lt2 h1 h2 h3 h4)). Qed.
Lemma lem358332 {A B : Type'} (f : A -> B) (P : type547 A B) (lt2 : type1402 A) (h1 : term47 A B P f) (h2 : term6 A B lt2 P) (h3 : term7 A B lt2 P) (h4 : @WF A lt2) : term103 A B P f.
Proof. exact (EQ_MP (@lem354611 A B P f) (@lem358331 A B f P lt2 h1 h2 h3 h4)). Qed.
Lemma lem358333 {A B : Type'} (f : A -> B) (P : type547 A B) (lt2 : type1402 A) (h1 : term47 A B P f) (h2 : term6 A B lt2 P) (h3 : term7 A B lt2 P) (h4 : @WF A lt2) : term77 A B P f.
Proof. exact (EQ_MP (@lem354599 A B P f h1) (@lem358332 A B f P lt2 h1 h2 h3 h4)). Qed.
Lemma lem358334 {A B : Type'} (f : A -> B) (P : type547 A B) (lt2 : type1402 A) (h1 : term6 A B lt2 P) (h2 : term7 A B lt2 P) (h3 : @WF A lt2) : term79 A B P f.
Proof. exact (fun h0 : term47 A B P f => @lem358333 A B f P lt2 h0 h1 h2 h3). Qed.
Lemma lem358339 {A B : Type'} (P : type547 A B) (lt2 : type1402 A) (h1 : term6 A B lt2 P) (h2 : term7 A B lt2 P) (h3 : @WF A lt2) : term83 A B P.
Proof. exact (fun f : A -> B => @lem358334 A B f P lt2 h1 h2 h3). Qed.
Lemma lem358340 {A B : Type'} (P : type547 A B) (lt2 : type1402 A) (h1 : term6 A B lt2 P) (h2 : term7 A B lt2 P) (h3 : @WF A lt2) : term94 A B P.
Proof. exact (@lem354572 A B P (@lem358339 A B P lt2 h1 h2 h3)). Qed.
Lemma lem358341 {A B : Type'} (P : type547 A B) (lt2 : type1402 A) (h1 : term6 A B lt2 P) (h2 : term7 A B lt2 P) (h3 : term8 A B P) (h4 : @WF A lt2) : term92 A B P.
Proof. exact (@lem358340 A B P lt2 h1 h2 h4 (@lem354335 A B P h3)). Qed.
Lemma lem358342 {A B : Type'} (P : type547 A B) (lt2 : type1402 A) (h1 : term6 A B lt2 P) (h2 : term7 A B lt2 P) (h3 : @WF A lt2) : (term8 A B P) = (term92 A B P).
Proof. exact (prop_ext (fun h4 : term8 A B P => @lem358341 A B P lt2 h1 h2 h4 h3) (fun h4 : term92 A B P => @lem354545 A B P lt2 h2 h3)). Qed.
Lemma lem358343 {A B : Type'} (P : type547 A B) (lt2 : type1402 A) (h1 : term6 A B lt2 P) (h2 : term7 A B lt2 P) (h3 : @WF A lt2) : term92 A B P.
Proof. exact (EQ_MP (@lem358342 A B P lt2 h1 h2 h3) (@lem354545 A B P lt2 h2 h3)). Qed.
Lemma lem358344 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (h1 : term5 A B lt2 P) : term6 A B lt2 P.
Proof. exact (proj2 (@lem354332 A B lt2 P h1)). Qed.
Lemma lem358345 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (h1 : term5 A B lt2 P) : term7 A B lt2 P.
Proof. exact (proj1 (@lem354332 A B lt2 P h1)). Qed.
Lemma lem358346 {A B : Type'} (P : type547 A B) (lt2 : type1402 A) (h1 : term6 A B lt2 P) (h2 : term7 A B lt2 P) (h3 : @WF A lt2) : (term6 A B lt2 P) = (term92 A B P).
Proof. exact (prop_ext (fun h4 : term6 A B lt2 P => @lem358343 A B P lt2 h1 h2 h3) (fun h4 : term92 A B P => @lem354333 A B lt2 P h1)). Qed.
Lemma lem358347 {A B : Type'} (P : type547 A B) (lt2 : type1402 A) (h1 : term6 A B lt2 P) (h2 : term7 A B lt2 P) (h3 : @WF A lt2) : term92 A B P.
Proof. exact (EQ_MP (@lem358346 A B P lt2 h1 h2 h3) (@lem354333 A B lt2 P h1)). Qed.
Lemma lem358348 {A B : Type'} (P : type547 A B) (lt2 : type1402 A) (h1 : term6 A B lt2 P) (h2 : term7 A B lt2 P) (h3 : @WF A lt2) : (term7 A B lt2 P) = (term92 A B P).
Proof. exact (prop_ext (fun h4 : term7 A B lt2 P => @lem358347 A B P lt2 h1 h2 h3) (fun h4 : term92 A B P => @lem354334 A B lt2 P h2)). Qed.
Lemma lem358349 {A B : Type'} (P : type547 A B) (lt2 : type1402 A) (h1 : term6 A B lt2 P) (h2 : term7 A B lt2 P) (h3 : @WF A lt2) : term92 A B P.
Proof. exact (EQ_MP (@lem358348 A B P lt2 h1 h2 h3) (@lem354334 A B lt2 P h2)). Qed.
Lemma lem358350 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (h1 : term7 A B lt2 P) (h2 : @WF A lt2) (h3 : term5 A B lt2 P) : (term6 A B lt2 P) = (term92 A B P).
Proof. exact (prop_ext (fun h4 : term6 A B lt2 P => @lem358349 A B P lt2 h4 h1 h2) (fun h4 : term92 A B P => @lem358344 A B lt2 P h3)). Qed.
Lemma lem358351 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (h1 : term7 A B lt2 P) (h2 : @WF A lt2) (h3 : term5 A B lt2 P) : term92 A B P.
Proof. exact (EQ_MP (@lem358350 A B lt2 P h1 h2 h3) (@lem358344 A B lt2 P h3)). Qed.
Lemma lem358352 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (h1 : @WF A lt2) (h2 : term5 A B lt2 P) : (term7 A B lt2 P) = (term92 A B P).
Proof. exact (prop_ext (fun h3 : term7 A B lt2 P => @lem358351 A B lt2 P h3 h1 h2) (fun h3 : term92 A B P => @lem358345 A B lt2 P h2)). Qed.
Lemma lem358353 {A B : Type'} (lt2 : type1402 A) (P : type547 A B) (h1 : @WF A lt2) (h2 : term5 A B lt2 P) : term92 A B P.
Proof. exact (EQ_MP (@lem358352 A B lt2 P h1 h2) (@lem358345 A B lt2 P h2)). Qed.
Lemma lem358354 {A B : Type'} (P : type547 A B) (lt2 : type1402 A) (h1 : @WF A lt2) : term836 A B lt2 P.
Proof. exact (fun h0 : term5 A B lt2 P => @lem358353 A B lt2 P h1 h0). Qed.
Lemma lem358359 {A B : Type'} (lt2 : type1402 A) (h1 : @WF A lt2) : term837 A B lt2.
Proof. exact (fun P : type547 A B => @lem358354 A B P lt2 h1). Qed.
Lemma lem358360 {A B : Type'} (lt2 : type1402 A) (h1 : @WF A lt2) : (@WF A lt2) = (term837 A B lt2).
Proof. exact (prop_ext (fun h2 : @WF A lt2 => @lem358359 A B lt2 h1) (fun h2 : term837 A B lt2 => @lem354331 A lt2 h1)). Qed.
Lemma lem358361 {A B : Type'} (lt2 : type1402 A) (h1 : @WF A lt2) : term837 A B lt2.
Proof. exact (EQ_MP (@lem358360 A B lt2 h1) (@lem354331 A lt2 h1)). Qed.
