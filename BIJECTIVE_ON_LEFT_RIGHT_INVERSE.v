Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import BIJECTIVE_ON_LEFT_RIGHT_INVERSE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import INJECTIVE_ON_LEFT_INVERSE_spec.
Require Import RIGHT_AND_EXISTS_THM_spec.
Require Import SURJECTIVE_ON_RIGHT_INVERSE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm19490_spec.
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
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm32_spec.
Lemma lem3566193 {A : Type'} (P : Prop) : term0 A P.
Proof. exact (@lem5950 A P). Qed.
Lemma lem3566194 {A : Type'} (P : Prop) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem3566195 {A : Type'} (P : Prop) : term1 A P.
Proof. exact (EQ_MP (@lem3566194 A P) (@lem3566193 A P)). Qed.
Lemma lem3566196 {A : Type'} (P : Prop) (Q : A -> Prop) : term2 A P Q.
Proof. exact (@lem3566195 A P Q). Qed.
Lemma lem3566197 {A : Type'} (P : Prop) (Q : A -> Prop) : (term2 A P Q) = ((term3 A P Q) = (term4 A P Q)).
Proof. exact (eq_refl (term2 A P Q)). Qed.
Lemma lem3566199 {_91307 _91308 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91308) : term5 _91307 _91308 s f.
Proof. exact (@lem3562737 _91307 _91308 s f). Qed.
Lemma lem3566200 {_91307 _91308 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91308) : (term5 _91307 _91308 s f) = (term6 _91307 _91308 s f).
Proof. exact (eq_refl (term5 _91307 _91308 s f)). Qed.
Lemma lem3566201 {_91307 _91308 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91308) : term6 _91307 _91308 s f.
Proof. exact (EQ_MP (@lem3566200 _91307 _91308 s f) (@lem3566199 _91307 _91308 s f)). Qed.
Lemma lem3566202 {_91307 _91308 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91308) (t : _91308 -> Prop) : term7 _91307 _91308 s f t.
Proof. exact (@lem3566201 _91307 _91308 s f t). Qed.
Lemma lem3566203 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) : (term7 _91307 _91308 s f t) = ((term8 _91307 _91308 t s f) = (term9 _91307 _91308 t s f)).
Proof. exact (eq_refl (term7 _91307 _91308 s f t)). Qed.
Lemma lem3566205 {_91401 _91404 : Type'} (f : _91401 -> _91404) : term10 _91401 _91404 f.
Proof. exact (@lem3566182 _91401 _91404 f). Qed.
Lemma lem3566206 {_91401 _91404 : Type'} (f : _91401 -> _91404) : (term10 _91401 _91404 f) = (term11 _91401 _91404 f).
Proof. exact (eq_refl (term10 _91401 _91404 f)). Qed.
Lemma lem3566207 {_91401 _91404 : Type'} (f : _91401 -> _91404) : term11 _91401 _91404 f.
Proof. exact (EQ_MP (@lem3566206 _91401 _91404 f) (@lem3566205 _91401 _91404 f)). Qed.
Lemma lem3566208 {_91401 _91404 : Type'} (f : _91401 -> _91404) (s : _91401 -> Prop) : term12 _91401 _91404 f s.
Proof. exact (@lem3566207 _91401 _91404 f s). Qed.
Lemma lem3566209 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term12 _91401 _91404 f s) = ((term13 _91401 _91404 s f) = (term14 _91401 _91404 s f)).
Proof. exact (eq_refl (term12 _91401 _91404 f s)). Qed.
Lemma lem3566211 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (t : _91535 -> Prop) (h1 : term15 _91535 _91536 s f t) : term15 _91535 _91536 s f t.
Proof. exact (h1). Qed.
Lemma lem3566217 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term13 _91401 _91404 s f) = (term14 _91401 _91404 s f).
Proof. exact (EQ_MP (@lem3566209 _91401 _91404 s f) (@lem3566208 _91401 _91404 f s)). Qed.
Lemma lem3566218 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) : (term16 _91535 _91536 s f) = (term17 _91535 _91536 s f).
Proof. exact (@lem3566217 _91536 _91535 s f). Qed.
Lemma lem3566231 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3566232 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) : (term18 _91535 _91536 s f) = (term19 _91535 _91536 s f).
Proof. exact (MK_COMB (@lem3566231) (@lem3566218 _91535 _91536 s f)). Qed.
Lemma lem3566234 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) : (term8 _91307 _91308 t s f) = (term9 _91307 _91308 t s f).
Proof. exact (EQ_MP (@lem3566203 _91307 _91308 t s f) (@lem3566202 _91307 _91308 s f t)). Qed.
Lemma lem3566235 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) : (term20 _91535 _91536 t s f) = (term21 _91535 _91536 t s f).
Proof. exact (@lem3566234 _91536 _91535 t s f). Qed.
Lemma lem3566250 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) : (term22 _91535 _91536 t s f) = (term23 _91535 _91536 t s f).
Proof. exact (MK_COMB (@lem3566232 _91535 _91536 s f) (@lem3566235 _91535 _91536 t s f)). Qed.
Lemma lem3566253 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3566254 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) : (term24 _91535 _91536 t s f) = (term25 _91535 _91536 t s f).
Proof. exact (MK_COMB (@lem3566253) (@lem3566250 _91535 _91536 t s f)). Qed.
Lemma lem3566285 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) : (term26 _91535 _91536 t s f) = (term26 _91535 _91536 t s f).
Proof. exact (eq_refl (term26 _91535 _91536 t s f)). Qed.
Lemma lem3566286 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) : ((term22 _91535 _91536 t s f) = (term26 _91535 _91536 t s f)) = ((term23 _91535 _91536 t s f) = (term26 _91535 _91536 t s f)).
Proof. exact (MK_COMB (@lem3566254 _91535 _91536 t s f) (@lem3566285 _91535 _91536 t s f)). Qed.
Lemma lem3566289 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) : ((term23 _91535 _91536 t s f) = (term26 _91535 _91536 t s f)) = ((term22 _91535 _91536 t s f) = (term26 _91535 _91536 t s f)).
Proof. exact (SYM (@lem3566286 _91535 _91536 t s f)). Qed.
Lemma lem3566293 {A : Type'} (P : Prop) (Q : A -> Prop) : (term3 A P Q) = (term4 A P Q).
Proof. exact (EQ_MP (@lem3566197 A P Q) (@lem3566196 A P Q)). Qed.
Lemma lem3566294 {_91535 _91536 : Type'} (P : Prop) (Q : type572 _91535 _91536) : (term27 _91535 _91536 P Q) = (term28 _91535 _91536 P Q).
Proof. exact (@lem3566293 (_91535 -> _91536) P Q). Qed.
Lemma lem3566295 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) : (term29 _91535 _91536 t s f) = (term30 _91535 _91536 t s f).
Proof. exact (@lem3566294 _91535 _91536 (term17 _91535 _91536 s f) (term31 _91535 _91536 t s f)). Qed.
Lemma lem3566296 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term32 _91535 _91536 t s f g) = (term33 _91535 _91536 t s f g).
Proof. exact (eq_refl (term32 _91535 _91536 t s f g)). Qed.
Lemma lem3566297 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) : (term34 _91535 _91536 t s f) = (term31 _91535 _91536 t s f).
Proof. exact (fun_ext (fun g : _91535 -> _91536 => @lem3566296 _91535 _91536 t s f g)). Qed.
Lemma lem3566298 {_91535 _91536 : Type'} : (@ex (_91535 -> _91536)) = (@ex (_91535 -> _91536)).
Proof. exact (eq_refl (@ex (_91535 -> _91536))). Qed.
Lemma lem3566299 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) : (term35 _91535 _91536 t s f) = (term21 _91535 _91536 t s f).
Proof. exact (MK_COMB (@lem3566298 _91535 _91536) (@lem3566297 _91535 _91536 t s f)). Qed.
Lemma lem3566300 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) : (term19 _91535 _91536 s f) = (term19 _91535 _91536 s f).
Proof. exact (eq_refl (term19 _91535 _91536 s f)). Qed.
Lemma lem3566301 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) : (term29 _91535 _91536 t s f) = (term23 _91535 _91536 t s f).
Proof. exact (MK_COMB (@lem3566300 _91535 _91536 s f) (@lem3566299 _91535 _91536 t s f)). Qed.
Lemma lem3566302 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3566303 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) : (term36 _91535 _91536 t s f) = (term25 _91535 _91536 t s f).
Proof. exact (MK_COMB (@lem3566302) (@lem3566301 _91535 _91536 t s f)). Qed.
Lemma lem3566304 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term32 _91535 _91536 t s f g) = (term33 _91535 _91536 t s f g).
Proof. exact (eq_refl (term32 _91535 _91536 t s f g)). Qed.
Lemma lem3566305 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) : (term19 _91535 _91536 s f) = (term19 _91535 _91536 s f).
Proof. exact (eq_refl (term19 _91535 _91536 s f)). Qed.
Lemma lem3566306 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term37 _91535 _91536 t s f g) = (term38 _91535 _91536 t s f g).
Proof. exact (MK_COMB (@lem3566305 _91535 _91536 s f) (@lem3566304 _91535 _91536 t s f g)). Qed.
Lemma lem3566307 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) : (term39 _91535 _91536 t s f) = (term40 _91535 _91536 t s f).
Proof. exact (fun_ext (fun g : _91535 -> _91536 => @lem3566306 _91535 _91536 t s f g)). Qed.
Lemma lem3566308 {_91535 _91536 : Type'} : (@ex (_91535 -> _91536)) = (@ex (_91535 -> _91536)).
Proof. exact (eq_refl (@ex (_91535 -> _91536))). Qed.
Lemma lem3566309 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) : (term30 _91535 _91536 t s f) = (term41 _91535 _91536 t s f).
Proof. exact (MK_COMB (@lem3566308 _91535 _91536) (@lem3566307 _91535 _91536 t s f)). Qed.
Lemma lem3566310 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) : ((term29 _91535 _91536 t s f) = (term30 _91535 _91536 t s f)) = ((term23 _91535 _91536 t s f) = (term41 _91535 _91536 t s f)).
Proof. exact (MK_COMB (@lem3566303 _91535 _91536 t s f) (@lem3566309 _91535 _91536 t s f)). Qed.
Lemma lem3566311 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) : (term23 _91535 _91536 t s f) = (term41 _91535 _91536 t s f).
Proof. exact (EQ_MP (@lem3566310 _91535 _91536 t s f) (@lem3566295 _91535 _91536 t s f)). Qed.
Lemma lem3566340 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3566341 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) : (term25 _91535 _91536 t s f) = (term42 _91535 _91536 t s f).
Proof. exact (MK_COMB (@lem3566340) (@lem3566311 _91535 _91536 t s f)). Qed.
Lemma lem3566372 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) : (term26 _91535 _91536 t s f) = (term26 _91535 _91536 t s f).
Proof. exact (eq_refl (term26 _91535 _91536 t s f)). Qed.
Lemma lem3566373 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) : ((term23 _91535 _91536 t s f) = (term26 _91535 _91536 t s f)) = ((term41 _91535 _91536 t s f) = (term26 _91535 _91536 t s f)).
Proof. exact (MK_COMB (@lem3566341 _91535 _91536 t s f) (@lem3566372 _91535 _91536 t s f)). Qed.
Lemma lem3566376 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) : ((term41 _91535 _91536 t s f) = (term26 _91535 _91536 t s f)) = ((term23 _91535 _91536 t s f) = (term26 _91535 _91536 t s f)).
Proof. exact (SYM (@lem3566373 _91535 _91536 t s f)). Qed.
Lemma lem3566377 {_91535 _91536 : Type'} : (@ex (_91535 -> _91536)) = (@ex (_91535 -> _91536)).
Proof. exact (eq_refl (@ex (_91535 -> _91536))). Qed.
Lemma lem3566379 (p : Prop) : p = (term43 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3566380 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term44 _91535 _91536 t s g f) = (term45 _91535 _91536 t s g f).
Proof. exact (@lem3566379 (term44 _91535 _91536 t s g f)). Qed.
Lemma lem3566381 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term45 _91535 _91536 t s g f) = (term44 _91535 _91536 t s g f).
Proof. exact (SYM (@lem3566380 _91535 _91536 t s g f)). Qed.
Lemma lem3566382 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term46 _91535 _91536 t s g f) : term46 _91535 _91536 t s g f.
Proof. exact (h1). Qed.
Lemma lem3566385 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term47 _91535 _91536 t s g f) : term47 _91535 _91536 t s g f.
Proof. exact (h1). Qed.
Lemma lem3566386 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : term48 _91535 _91536 t s g f.
Proof. exact (fun h0 : term47 _91535 _91536 t s g f => @lem3566385 _91535 _91536 t s g f h0). Qed.
Lemma lem3566387 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term48 _91535 _91536 t s g f) : term48 _91535 _91536 t s g f.
Proof. exact (h1). Qed.
Lemma lem3566388 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term47 _91535 _91536 t s g f) : term47 _91535 _91536 t s g f.
Proof. exact (h1). Qed.
Lemma lem3566389 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term47 _91535 _91536 t s g f) (h2 : term48 _91535 _91536 t s g f) : term47 _91535 _91536 t s g f.
Proof. exact (@lem3566387 _91535 _91536 t s g f h2 (@lem3566388 _91535 _91536 t s g f h1)). Qed.
Lemma lem3566390 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term47 _91535 _91536 t s g f) : term49 _91535 _91536 t s g f.
Proof. exact (fun h0 : term48 _91535 _91536 t s g f => @lem3566389 _91535 _91536 t s g f h1 h0). Qed.
Lemma lem3566391 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term48 _91535 _91536 t s g f) : term48 _91535 _91536 t s g f.
Proof. exact (h1). Qed.
Lemma lem3566392 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term47 _91535 _91536 t s g f) (h2 : term48 _91535 _91536 t s g f) : term47 _91535 _91536 t s g f.
Proof. exact (@lem3566390 _91535 _91536 t s g f h1 (@lem3566391 _91535 _91536 t s g f h2)). Qed.
Lemma lem3566393 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term48 _91535 _91536 t s g f) : term48 _91535 _91536 t s g f.
Proof. exact (fun h0 : term47 _91535 _91536 t s g f => @lem3566392 _91535 _91536 t s g f h0 h1). Qed.
Lemma lem3566394 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : term50 _91535 _91536 t s g f.
Proof. exact (fun h0 : term48 _91535 _91536 t s g f => @lem3566393 _91535 _91536 t s g f h0). Qed.
Lemma lem3566397 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : term48 _91535 _91536 t s g f.
Proof. exact (@lem3566394 _91535 _91536 t s g f (@lem3566386 _91535 _91536 t s g f)). Qed.
Lemma lem3566398 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : term48 _91535 _91536 t s g f.
Proof. exact (@lem3566397 _91535 _91536 t s g f). Qed.
Lemma lem3566424 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3566425 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term45 _91535 _91536 t s g f) = (term51 _91535 _91536 t s g f).
Proof. exact (@lem3566424 (term46 _91535 _91536 t s g f)). Qed.
Lemma lem3566427 (t : Prop) : (term52 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3566428 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term51 _91535 _91536 t s g f) = (term44 _91535 _91536 t s g f).
Proof. exact (@lem3566427 (term44 _91535 _91536 t s g f)). Qed.
Lemma lem3566431 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term45 _91535 _91536 t s g f) = (term44 _91535 _91536 t s g f).
Proof. exact (TRANS (@lem3566425 _91535 _91536 t s g f) (@lem3566428 _91535 _91536 t s g f)). Qed.
Lemma lem3566474 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (t : _91535 -> Prop) : (term53 _91535 _91536 s f t) = (term53 _91535 _91536 s f t).
Proof. exact (eq_refl (term53 _91535 _91536 s f t)). Qed.
Lemma lem3566475 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term47 _91535 _91536 t s g f) = (term54 _91535 _91536 t s g f).
Proof. exact (MK_COMB (@lem3566474 _91535 _91536 s f t) (@lem3566431 _91535 _91536 t s g f)). Qed.
Lemma lem3566478 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term55 _91535 _91536 s g f) = (term56 _91535 _91536 s g f).
Proof. exact (fun_ext (fun t : _91535 -> Prop => @lem3566475 _91535 _91536 t s g f)). Qed.
Lemma lem3566479 {_91535 : Type'} : (@all (_91535 -> Prop)) = (@all (_91535 -> Prop)).
Proof. exact (eq_refl (@all (_91535 -> Prop))). Qed.
Lemma lem3566480 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term57 _91535 _91536 s g f) = (term58 _91535 _91536 s g f).
Proof. exact (MK_COMB (@lem3566479 _91535) (@lem3566478 _91535 _91536 s g f)). Qed.
Lemma lem3566485 {_91535 _91536 : Type'} (g : _91535 -> _91536) (f : _91536 -> _91535) : (term59 _91535 _91536 g f) = (term60 _91535 _91536 g f).
Proof. exact (fun_ext (fun s : _91536 -> Prop => @lem3566480 _91535 _91536 s g f)). Qed.
Lemma lem3566486 {_91536 : Type'} : (@all (_91536 -> Prop)) = (@all (_91536 -> Prop)).
Proof. exact (eq_refl (@all (_91536 -> Prop))). Qed.
Lemma lem3566487 {_91535 _91536 : Type'} (g : _91535 -> _91536) (f : _91536 -> _91535) : (term61 _91535 _91536 g f) = (term62 _91535 _91536 g f).
Proof. exact (MK_COMB (@lem3566486 _91536) (@lem3566485 _91535 _91536 g f)). Qed.
Lemma lem3566492 {_91535 _91536 : Type'} (f : _91536 -> _91535) : (term63 _91535 _91536 f) = (term64 _91535 _91536 f).
Proof. exact (fun_ext (fun g : _91535 -> _91536 => @lem3566487 _91535 _91536 g f)). Qed.
Lemma lem3566493 {_91535 _91536 : Type'} : (@all (_91535 -> _91536)) = (@all (_91535 -> _91536)).
Proof. exact (eq_refl (@all (_91535 -> _91536))). Qed.
Lemma lem3566494 {_91535 _91536 : Type'} (f : _91536 -> _91535) : (term65 _91535 _91536 f) = (term66 _91535 _91536 f).
Proof. exact (MK_COMB (@lem3566493 _91535 _91536) (@lem3566492 _91535 _91536 f)). Qed.
Lemma lem3566499 {_91535 _91536 : Type'} : (term67 _91535 _91536) = (term68 _91535 _91536).
Proof. exact (fun_ext (fun f : _91536 -> _91535 => @lem3566494 _91535 _91536 f)). Qed.
Lemma lem3566500 {_91535 _91536 : Type'} : (@all (_91536 -> _91535)) = (@all (_91536 -> _91535)).
Proof. exact (eq_refl (@all (_91536 -> _91535))). Qed.
Lemma lem3566509 {_91535 _91536 : Type'} : (term69 _91535 _91536) = (term70 _91535 _91536).
Proof. exact (MK_COMB (@lem3566500 _91535 _91536) (@lem3566499 _91535 _91536)). Qed.
Lemma lem3566514 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : (term71 _91535 _91536 s g f x) = (term71 _91535 _91536 s g f x).
Proof. exact (eq_refl (term71 _91535 _91536 s g f x)). Qed.
Lemma lem3566515 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term72 _91535 _91536 s g f) = (term72 _91535 _91536 s g f).
Proof. exact (fun_ext (fun x : _91536 => @lem3566514 _91535 _91536 s g f x)). Qed.
Lemma lem3566516 {_91536 : Type'} : (@all _91536) = (@all _91536).
Proof. exact (eq_refl (@all _91536)). Qed.
Lemma lem3566517 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term73 _91535 _91536 s g f) = (term73 _91535 _91536 s g f).
Proof. exact (MK_COMB (@lem3566516 _91536) (@lem3566515 _91535 _91536 s g f)). Qed.
Lemma lem3566522 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : (term74 _91535 _91536 t f g y) = (term74 _91535 _91536 t f g y).
Proof. exact (eq_refl (term74 _91535 _91536 t f g y)). Qed.
Lemma lem3566523 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term75 _91535 _91536 t f g) = (term75 _91535 _91536 t f g).
Proof. exact (fun_ext (fun y : _91535 => @lem3566522 _91535 _91536 t f g y)). Qed.
Lemma lem3566524 {_91535 : Type'} : (@all _91535) = (@all _91535).
Proof. exact (eq_refl (@all _91535)). Qed.
Lemma lem3566525 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term76 _91535 _91536 t f g) = (term76 _91535 _91536 t f g).
Proof. exact (MK_COMB (@lem3566524 _91535) (@lem3566523 _91535 _91536 t f g)). Qed.
Lemma lem3566526 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3566527 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term77 _91535 _91536 t f g) = (term77 _91535 _91536 t f g).
Proof. exact (MK_COMB (@lem3566526) (@lem3566525 _91535 _91536 t f g)). Qed.
Lemma lem3566528 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term78 _91535 _91536 t s g f) = (term78 _91535 _91536 t s g f).
Proof. exact (MK_COMB (@lem3566527 _91535 _91536 t f g) (@lem3566517 _91535 _91536 s g f)). Qed.
Lemma lem3566533 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (y : _91535) (s : _91536 -> Prop) : (term79 _91535 _91536 t g y s) = (term79 _91535 _91536 t g y s).
Proof. exact (eq_refl (term79 _91535 _91536 t g y s)). Qed.
Lemma lem3566534 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (s : _91536 -> Prop) : (term80 _91535 _91536 t g s) = (term80 _91535 _91536 t g s).
Proof. exact (fun_ext (fun y : _91535 => @lem3566533 _91535 _91536 t g y s)). Qed.
Lemma lem3566535 {_91535 : Type'} : (@all _91535) = (@all _91535).
Proof. exact (eq_refl (@all _91535)). Qed.
Lemma lem3566536 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (s : _91536 -> Prop) : (term81 _91535 _91536 t g s) = (term81 _91535 _91536 t g s).
Proof. exact (MK_COMB (@lem3566535 _91535) (@lem3566534 _91535 _91536 t g s)). Qed.
Lemma lem3566537 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3566538 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (s : _91536 -> Prop) : (term82 _91535 _91536 t g s) = (term82 _91535 _91536 t g s).
Proof. exact (MK_COMB (@lem3566537) (@lem3566536 _91535 _91536 t g s)). Qed.
Lemma lem3566539 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term83 _91535 _91536 t s g f) = (term83 _91535 _91536 t s g f).
Proof. exact (MK_COMB (@lem3566538 _91535 _91536 t g s) (@lem3566528 _91535 _91536 t s g f)). Qed.
Lemma lem3566548 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : (term84 _91535 _91536 t s f g y) = (term84 _91535 _91536 t s f g y).
Proof. exact (eq_refl (term84 _91535 _91536 t s f g y)). Qed.
Lemma lem3566549 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term85 _91535 _91536 t s f g) = (term85 _91535 _91536 t s f g).
Proof. exact (fun_ext (fun y : _91535 => @lem3566548 _91535 _91536 t s f g y)). Qed.
Lemma lem3566550 {_91535 : Type'} : (@all _91535) = (@all _91535).
Proof. exact (eq_refl (@all _91535)). Qed.
Lemma lem3566551 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term33 _91535 _91536 t s f g) = (term33 _91535 _91536 t s f g).
Proof. exact (MK_COMB (@lem3566550 _91535) (@lem3566549 _91535 _91536 t s f g)). Qed.
Lemma lem3566556 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : (term71 _91535 _91536 s g f x) = (term71 _91535 _91536 s g f x).
Proof. exact (eq_refl (term71 _91535 _91536 s g f x)). Qed.
Lemma lem3566557 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term72 _91535 _91536 s g f) = (term72 _91535 _91536 s g f).
Proof. exact (fun_ext (fun x : _91536 => @lem3566556 _91535 _91536 s g f x)). Qed.
Lemma lem3566558 {_91536 : Type'} : (@all _91536) = (@all _91536).
Proof. exact (eq_refl (@all _91536)). Qed.
Lemma lem3566559 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term73 _91535 _91536 s g f) = (term73 _91535 _91536 s g f).
Proof. exact (MK_COMB (@lem3566558 _91536) (@lem3566557 _91535 _91536 s g f)). Qed.
Lemma lem3566560 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) : (term86 _91535 _91536 s f) = (term86 _91535 _91536 s f).
Proof. exact (fun_ext (fun g : _91535 -> _91536 => @lem3566559 _91535 _91536 s g f)). Qed.
Lemma lem3566561 {_91535 _91536 : Type'} : (@ex (_91535 -> _91536)) = (@ex (_91535 -> _91536)).
Proof. exact (eq_refl (@ex (_91535 -> _91536))). Qed.
Lemma lem3566562 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) : (term17 _91535 _91536 s f) = (term17 _91535 _91536 s f).
Proof. exact (MK_COMB (@lem3566561 _91535 _91536) (@lem3566560 _91535 _91536 s f)). Qed.
Lemma lem3566563 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3566564 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) : (term19 _91535 _91536 s f) = (term19 _91535 _91536 s f).
Proof. exact (MK_COMB (@lem3566563) (@lem3566562 _91535 _91536 s f)). Qed.
Lemma lem3566565 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term38 _91535 _91536 t s f g) = (term38 _91535 _91536 t s f g).
Proof. exact (MK_COMB (@lem3566564 _91535 _91536 s f) (@lem3566551 _91535 _91536 t s f g)). Qed.
Lemma lem3566566 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3566567 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term87 _91535 _91536 t s f g) = (term87 _91535 _91536 t s f g).
Proof. exact (MK_COMB (@lem3566566) (@lem3566565 _91535 _91536 t s f g)). Qed.
Lemma lem3566568 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term44 _91535 _91536 t s g f) = (term44 _91535 _91536 t s g f).
Proof. exact (MK_COMB (@lem3566567 _91535 _91536 t s f g) (@lem3566539 _91535 _91536 t s g f)). Qed.
Lemma lem3566573 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (x : _91536) (t : _91535 -> Prop) : (term88 _91535 _91536 s f x t) = (term88 _91535 _91536 s f x t).
Proof. exact (eq_refl (term88 _91535 _91536 s f x t)). Qed.
Lemma lem3566574 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (t : _91535 -> Prop) : (term89 _91535 _91536 s f t) = (term89 _91535 _91536 s f t).
Proof. exact (fun_ext (fun x : _91536 => @lem3566573 _91535 _91536 s f x t)). Qed.
Lemma lem3566575 {_91536 : Type'} : (@all _91536) = (@all _91536).
Proof. exact (eq_refl (@all _91536)). Qed.
Lemma lem3566576 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (t : _91535 -> Prop) : (term15 _91535 _91536 s f t) = (term15 _91535 _91536 s f t).
Proof. exact (MK_COMB (@lem3566575 _91536) (@lem3566574 _91535 _91536 s f t)). Qed.
Lemma lem3566577 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3566578 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (t : _91535 -> Prop) : (term53 _91535 _91536 s f t) = (term53 _91535 _91536 s f t).
Proof. exact (MK_COMB (@lem3566577) (@lem3566576 _91535 _91536 s f t)). Qed.
Lemma lem3566579 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term54 _91535 _91536 t s g f) = (term54 _91535 _91536 t s g f).
Proof. exact (MK_COMB (@lem3566578 _91535 _91536 s f t) (@lem3566568 _91535 _91536 t s g f)). Qed.
Lemma lem3566580 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term56 _91535 _91536 s g f) = (term56 _91535 _91536 s g f).
Proof. exact (fun_ext (fun t : _91535 -> Prop => @lem3566579 _91535 _91536 t s g f)). Qed.
Lemma lem3566581 {_91535 : Type'} : (@all (_91535 -> Prop)) = (@all (_91535 -> Prop)).
Proof. exact (eq_refl (@all (_91535 -> Prop))). Qed.
Lemma lem3566582 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term58 _91535 _91536 s g f) = (term58 _91535 _91536 s g f).
Proof. exact (MK_COMB (@lem3566581 _91535) (@lem3566580 _91535 _91536 s g f)). Qed.
Lemma lem3566583 {_91535 _91536 : Type'} (g : _91535 -> _91536) (f : _91536 -> _91535) : (term60 _91535 _91536 g f) = (term60 _91535 _91536 g f).
Proof. exact (fun_ext (fun s : _91536 -> Prop => @lem3566582 _91535 _91536 s g f)). Qed.
Lemma lem3566584 {_91536 : Type'} : (@all (_91536 -> Prop)) = (@all (_91536 -> Prop)).
Proof. exact (eq_refl (@all (_91536 -> Prop))). Qed.
Lemma lem3566585 {_91535 _91536 : Type'} (g : _91535 -> _91536) (f : _91536 -> _91535) : (term62 _91535 _91536 g f) = (term62 _91535 _91536 g f).
Proof. exact (MK_COMB (@lem3566584 _91536) (@lem3566583 _91535 _91536 g f)). Qed.
Lemma lem3566586 {_91535 _91536 : Type'} (f : _91536 -> _91535) : (term64 _91535 _91536 f) = (term64 _91535 _91536 f).
Proof. exact (fun_ext (fun g : _91535 -> _91536 => @lem3566585 _91535 _91536 g f)). Qed.
Lemma lem3566587 {_91535 _91536 : Type'} : (@all (_91535 -> _91536)) = (@all (_91535 -> _91536)).
Proof. exact (eq_refl (@all (_91535 -> _91536))). Qed.
Lemma lem3566588 {_91535 _91536 : Type'} (f : _91536 -> _91535) : (term66 _91535 _91536 f) = (term66 _91535 _91536 f).
Proof. exact (MK_COMB (@lem3566587 _91535 _91536) (@lem3566586 _91535 _91536 f)). Qed.
Lemma lem3566589 {_91535 _91536 : Type'} : (term68 _91535 _91536) = (term68 _91535 _91536).
Proof. exact (fun_ext (fun f : _91536 -> _91535 => @lem3566588 _91535 _91536 f)). Qed.
Lemma lem3566590 {_91535 _91536 : Type'} : (@all (_91536 -> _91535)) = (@all (_91536 -> _91535)).
Proof. exact (eq_refl (@all (_91536 -> _91535))). Qed.
Lemma lem3566591 {_91535 _91536 : Type'} : (term70 _91535 _91536) = (term70 _91535 _91536).
Proof. exact (MK_COMB (@lem3566590 _91535 _91536) (@lem3566589 _91535 _91536)). Qed.
Lemma lem3566684 {_91535 _91536 : Type'} : (term69 _91535 _91536) = (term70 _91535 _91536).
Proof. exact (TRANS (@lem3566509 _91535 _91536) (@lem3566591 _91535 _91536)). Qed.
Lemma lem3566685 {_91535 _91536 : Type'} : (term70 _91535 _91536) = (term69 _91535 _91536).
Proof. exact (SYM (@lem3566684 _91535 _91536)). Qed.
Lemma lem3566686 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (t : _91535 -> Prop) (h1 : term15 _91535 _91536 s f t) : term15 _91535 _91536 s f t.
Proof. exact (h1). Qed.
Lemma lem3566687 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term38 _91535 _91536 t s f g) : term38 _91535 _91536 t s f g.
Proof. exact (h1). Qed.
Lemma lem3566689 (p : Prop) : p = (term43 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3566690 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term83 _91535 _91536 t s g f) = (term90 _91535 _91536 t s g f).
Proof. exact (@lem3566689 (term83 _91535 _91536 t s g f)). Qed.
Lemma lem3566691 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term90 _91535 _91536 t s g f) = (term83 _91535 _91536 t s g f).
Proof. exact (SYM (@lem3566690 _91535 _91536 t s g f)). Qed.
Lemma lem3566692 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term91 _91535 _91536 t s g f) : term91 _91535 _91536 t s g f.
Proof. exact (h1). Qed.
Lemma lem3566699 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (x : _91536) (t : _91535 -> Prop) : (term88 _91535 _91536 s f x t) = (term92 _91535 _91536 s f x t).
Proof. exact (@lem17265 (@IN _91536 x s) (term93 _91535 _91536 f x t)). Qed.
Lemma lem3566700 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (t : _91535 -> Prop) : (term89 _91535 _91536 s f t) = (term94 _91535 _91536 s f t).
Proof. exact (fun_ext (fun x : _91536 => @lem3566699 _91535 _91536 s f x t)). Qed.
Lemma lem3566701 {_91536 : Type'} : (@all _91536) = (@all _91536).
Proof. exact (eq_refl (@all _91536)). Qed.
Lemma lem3566754 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (t : _91535 -> Prop) : (term15 _91535 _91536 s f t) = (term95 _91535 _91536 s f t).
Proof. exact (MK_COMB (@lem3566701 _91536) (@lem3566700 _91535 _91536 s f t)). Qed.
Lemma lem3566755 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (t : _91535 -> Prop) (h1 : term15 _91535 _91536 s f t) : term95 _91535 _91536 s f t.
Proof. exact (EQ_MP (@lem3566754 _91535 _91536 s f t) (@lem3566686 _91535 _91536 s f t h1)). Qed.
Lemma lem3566762 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : (term71 _91535 _91536 s g f x) = (term96 _91535 _91536 s g f x).
Proof. exact (@lem17265 (@IN _91536 x s) ((term97 _91535 _91536 g f x) = x)). Qed.
Lemma lem3566763 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term72 _91535 _91536 s g f) = (term98 _91535 _91536 s g f).
Proof. exact (fun_ext (fun x : _91536 => @lem3566762 _91535 _91536 s g f x)). Qed.
Lemma lem3566764 {_91536 : Type'} : (@all _91536) = (@all _91536).
Proof. exact (eq_refl (@all _91536)). Qed.
Lemma lem3566765 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term73 _91535 _91536 s g f) = (term99 _91535 _91536 s g f).
Proof. exact (MK_COMB (@lem3566764 _91536) (@lem3566763 _91535 _91536 s g f)). Qed.
Lemma lem3566766 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) : (term86 _91535 _91536 s f) = (term100 _91535 _91536 s f).
Proof. exact (fun_ext (fun g : _91535 -> _91536 => @lem3566765 _91535 _91536 s g f)). Qed.
Lemma lem3566767 {_91535 _91536 : Type'} : (@ex (_91535 -> _91536)) = (@ex (_91535 -> _91536)).
Proof. exact (eq_refl (@ex (_91535 -> _91536))). Qed.
Lemma lem3566768 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) : (term17 _91535 _91536 s f) = (term101 _91535 _91536 s f).
Proof. exact (MK_COMB (@lem3566767 _91535 _91536) (@lem3566766 _91535 _91536 s f)). Qed.
Lemma lem3566779 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : (term84 _91535 _91536 t s f g y) = (term102 _91535 _91536 t s f g y).
Proof. exact (@lem17265 (@IN _91535 y t) (term103 _91535 _91536 s f g y)). Qed.
Lemma lem3566780 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term85 _91535 _91536 t s f g) = (term104 _91535 _91536 t s f g).
Proof. exact (fun_ext (fun y : _91535 => @lem3566779 _91535 _91536 t s f g y)). Qed.
Lemma lem3566781 {_91535 : Type'} : (@all _91535) = (@all _91535).
Proof. exact (eq_refl (@all _91535)). Qed.
Lemma lem3566782 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term33 _91535 _91536 t s f g) = (term105 _91535 _91536 t s f g).
Proof. exact (MK_COMB (@lem3566781 _91535) (@lem3566780 _91535 _91536 t s f g)). Qed.
Lemma lem3566783 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3566784 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) : (term19 _91535 _91536 s f) = (term106 _91535 _91536 s f).
Proof. exact (MK_COMB (@lem3566783) (@lem3566768 _91535 _91536 s f)). Qed.
Lemma lem3566785 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term38 _91535 _91536 t s f g) = (term107 _91535 _91536 t s f g).
Proof. exact (MK_COMB (@lem3566784 _91535 _91536 s f) (@lem3566782 _91535 _91536 t s f g)). Qed.
Lemma lem3566888 {A : Type'} (P : A -> Prop) (Q : Prop) : (term108 A P Q) = (term109 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3566889 {_91535 _91536 : Type'} (P : type572 _91535 _91536) (Q : Prop) : (term110 _91535 _91536 P Q) = (term111 _91535 _91536 P Q).
Proof. exact (@lem3566888 (_91535 -> _91536) P Q). Qed.
Lemma lem3566890 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term112 _91535 _91536 t s f g) = (term113 _91535 _91536 t s f g).
Proof. exact (@lem3566889 _91535 _91536 (term100 _91535 _91536 s f) (term105 _91535 _91536 t s f g)). Qed.
Lemma lem3566891 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term114 _91535 _91536 s f g) = (term99 _91535 _91536 s g f).
Proof. exact (eq_refl (term114 _91535 _91536 s f g)). Qed.
Lemma lem3566892 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) : (term115 _91535 _91536 s f) = (term100 _91535 _91536 s f).
Proof. exact (fun_ext (fun g : _91535 -> _91536 => @lem3566891 _91535 _91536 s g f)). Qed.
Lemma lem3566893 {_91535 _91536 : Type'} : (@ex (_91535 -> _91536)) = (@ex (_91535 -> _91536)).
Proof. exact (eq_refl (@ex (_91535 -> _91536))). Qed.
Lemma lem3566894 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) : (term116 _91535 _91536 s f) = (term101 _91535 _91536 s f).
Proof. exact (MK_COMB (@lem3566893 _91535 _91536) (@lem3566892 _91535 _91536 s f)). Qed.
Lemma lem3566895 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3566896 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) : (term117 _91535 _91536 s f) = (term106 _91535 _91536 s f).
Proof. exact (MK_COMB (@lem3566895) (@lem3566894 _91535 _91536 s f)). Qed.
Lemma lem3566897 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term105 _91535 _91536 t s f g) = (term105 _91535 _91536 t s f g).
Proof. exact (eq_refl (term105 _91535 _91536 t s f g)). Qed.
Lemma lem3566898 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term112 _91535 _91536 t s f g) = (term107 _91535 _91536 t s f g).
Proof. exact (MK_COMB (@lem3566896 _91535 _91536 s f) (@lem3566897 _91535 _91536 t s f g)). Qed.
Lemma lem3566899 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3566900 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term118 _91535 _91536 t s f g) = (term119 _91535 _91536 t s f g).
Proof. exact (MK_COMB (@lem3566899) (@lem3566898 _91535 _91536 t s f g)). Qed.
Lemma lem3566901 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g' : _91535 -> _91536) (f : _91536 -> _91535) : (term114 _91535 _91536 s f g') = (term99 _91535 _91536 s g' f).
Proof. exact (eq_refl (term114 _91535 _91536 s f g')). Qed.
Lemma lem3566902 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3566903 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g' : _91535 -> _91536) (f : _91536 -> _91535) : (term120 _91535 _91536 s f g') = (term121 _91535 _91536 s g' f).
Proof. exact (MK_COMB (@lem3566902) (@lem3566901 _91535 _91536 s g' f)). Qed.
Lemma lem3566904 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term105 _91535 _91536 t s f g) = (term105 _91535 _91536 t s f g).
Proof. exact (eq_refl (term105 _91535 _91536 t s f g)). Qed.
Lemma lem3566905 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term122 _91535 _91536 g' t s f g) = (term123 _91535 _91536 g' t s f g).
Proof. exact (MK_COMB (@lem3566903 _91535 _91536 s g' f) (@lem3566904 _91535 _91536 t s f g)). Qed.
Lemma lem3566906 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term124 _91535 _91536 t s f g) = (term125 _91535 _91536 t s f g).
Proof. exact (fun_ext (fun g' : _91535 -> _91536 => @lem3566905 _91535 _91536 g' t s f g)). Qed.
Lemma lem3566907 {_91535 _91536 : Type'} : (@ex (_91535 -> _91536)) = (@ex (_91535 -> _91536)).
Proof. exact (eq_refl (@ex (_91535 -> _91536))). Qed.
Lemma lem3566908 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term113 _91535 _91536 t s f g) = (term126 _91535 _91536 t s f g).
Proof. exact (MK_COMB (@lem3566907 _91535 _91536) (@lem3566906 _91535 _91536 t s f g)). Qed.
Lemma lem3566909 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : ((term112 _91535 _91536 t s f g) = (term113 _91535 _91536 t s f g)) = ((term107 _91535 _91536 t s f g) = (term126 _91535 _91536 t s f g)).
Proof. exact (MK_COMB (@lem3566900 _91535 _91536 t s f g) (@lem3566908 _91535 _91536 t s f g)). Qed.
Lemma lem3566911 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term107 _91535 _91536 t s f g) = (term126 _91535 _91536 t s f g).
Proof. exact (EQ_MP (@lem3566909 _91535 _91536 t s f g) (@lem3566890 _91535 _91536 t s f g)). Qed.
Lemma lem3566912 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term38 _91535 _91536 t s f g) = (term126 _91535 _91536 t s f g).
Proof. exact (TRANS (@lem3566785 _91535 _91536 t s f g) (@lem3566911 _91535 _91536 t s f g)). Qed.
Lemma lem3566913 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term38 _91535 _91536 t s f g) : term126 _91535 _91536 t s f g.
Proof. exact (EQ_MP (@lem3566912 _91535 _91536 t s f g) (@lem3566687 _91535 _91536 t s f g h1)). Qed.
Lemma lem3566920 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (y : _91535) (s : _91536 -> Prop) : (term127 _91535 _91536 t g y s) = (term128 _91535 _91536 t g y s).
Proof. exact (@lem17362 (@IN _91535 y t) (term129 _91535 _91536 g y s)). Qed.
Lemma lem3566921 {_91535 : Type'} (P : _91535 -> Prop) : (term130 _91535 P) = (term131 _91535 P).
Proof. exact (@lem18392 _91535 P). Qed.
Lemma lem3566922 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (s : _91536 -> Prop) : (term132 _91535 _91536 t g s) = (term133 _91535 _91536 t g s).
Proof. exact (@lem3566921 _91535 (term80 _91535 _91536 t g s)). Qed.
Lemma lem3566923 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (y : _91535) (s : _91536 -> Prop) : (term134 _91535 _91536 t g s y) = (term79 _91535 _91536 t g y s).
Proof. exact (eq_refl (term134 _91535 _91536 t g s y)). Qed.
Lemma lem3566924 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3566925 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (y : _91535) (s : _91536 -> Prop) : (term135 _91535 _91536 t g s y) = (term127 _91535 _91536 t g y s).
Proof. exact (MK_COMB (@lem3566924) (@lem3566923 _91535 _91536 t g y s)). Qed.
Lemma lem3566926 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (y : _91535) (s : _91536 -> Prop) : (term135 _91535 _91536 t g s y) = (term128 _91535 _91536 t g y s).
Proof. exact (TRANS (@lem3566925 _91535 _91536 t g y s) (@lem3566920 _91535 _91536 t g y s)). Qed.
Lemma lem3566927 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (s : _91536 -> Prop) : (term136 _91535 _91536 t g s) = (term137 _91535 _91536 t g s).
Proof. exact (fun_ext (fun y : _91535 => @lem3566926 _91535 _91536 t g y s)). Qed.
Lemma lem3566928 {_91535 : Type'} : (@ex _91535) = (@ex _91535).
Proof. exact (eq_refl (@ex _91535)). Qed.
Lemma lem3566929 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (s : _91536 -> Prop) : (term133 _91535 _91536 t g s) = (term138 _91535 _91536 t g s).
Proof. exact (MK_COMB (@lem3566928 _91535) (@lem3566927 _91535 _91536 t g s)). Qed.
Lemma lem3566930 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (s : _91536 -> Prop) : (term132 _91535 _91536 t g s) = (term138 _91535 _91536 t g s).
Proof. exact (TRANS (@lem3566922 _91535 _91536 t g s) (@lem3566929 _91535 _91536 t g s)). Qed.
Lemma lem3566937 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : (term139 _91535 _91536 t f g y) = (term140 _91535 _91536 t f g y).
Proof. exact (@lem17362 (@IN _91535 y t) ((term141 _91535 _91536 f g y) = y)). Qed.
Lemma lem3566938 {_91535 : Type'} (P : _91535 -> Prop) : (term130 _91535 P) = (term131 _91535 P).
Proof. exact (@lem18392 _91535 P). Qed.
Lemma lem3566939 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term142 _91535 _91536 t f g) = (term143 _91535 _91536 t f g).
Proof. exact (@lem3566938 _91535 (term75 _91535 _91536 t f g)). Qed.
Lemma lem3566940 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : (term144 _91535 _91536 t f g y) = (term74 _91535 _91536 t f g y).
Proof. exact (eq_refl (term144 _91535 _91536 t f g y)). Qed.
Lemma lem3566941 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3566942 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : (term145 _91535 _91536 t f g y) = (term139 _91535 _91536 t f g y).
Proof. exact (MK_COMB (@lem3566941) (@lem3566940 _91535 _91536 t f g y)). Qed.
Lemma lem3566943 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : (term145 _91535 _91536 t f g y) = (term140 _91535 _91536 t f g y).
Proof. exact (TRANS (@lem3566942 _91535 _91536 t f g y) (@lem3566937 _91535 _91536 t f g y)). Qed.
Lemma lem3566944 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term146 _91535 _91536 t f g) = (term147 _91535 _91536 t f g).
Proof. exact (fun_ext (fun y : _91535 => @lem3566943 _91535 _91536 t f g y)). Qed.
Lemma lem3566945 {_91535 : Type'} : (@ex _91535) = (@ex _91535).
Proof. exact (eq_refl (@ex _91535)). Qed.
Lemma lem3566946 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term143 _91535 _91536 t f g) = (term148 _91535 _91536 t f g).
Proof. exact (MK_COMB (@lem3566945 _91535) (@lem3566944 _91535 _91536 t f g)). Qed.
Lemma lem3566947 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term142 _91535 _91536 t f g) = (term148 _91535 _91536 t f g).
Proof. exact (TRANS (@lem3566939 _91535 _91536 t f g) (@lem3566946 _91535 _91536 t f g)). Qed.
Lemma lem3566954 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : (term149 _91535 _91536 s g f x) = (term150 _91535 _91536 s g f x).
Proof. exact (@lem17362 (@IN _91536 x s) ((term97 _91535 _91536 g f x) = x)). Qed.
Lemma lem3566955 {_91536 : Type'} (P : _91536 -> Prop) : (term130 _91536 P) = (term131 _91536 P).
Proof. exact (@lem18392 _91536 P). Qed.
Lemma lem3566956 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term151 _91535 _91536 s g f) = (term152 _91535 _91536 s g f).
Proof. exact (@lem3566955 _91536 (term72 _91535 _91536 s g f)). Qed.
Lemma lem3566957 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : (term153 _91535 _91536 s g f x) = (term71 _91535 _91536 s g f x).
Proof. exact (eq_refl (term153 _91535 _91536 s g f x)). Qed.
Lemma lem3566958 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3566959 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : (term154 _91535 _91536 s g f x) = (term149 _91535 _91536 s g f x).
Proof. exact (MK_COMB (@lem3566958) (@lem3566957 _91535 _91536 s g f x)). Qed.
Lemma lem3566960 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : (term154 _91535 _91536 s g f x) = (term150 _91535 _91536 s g f x).
Proof. exact (TRANS (@lem3566959 _91535 _91536 s g f x) (@lem3566954 _91535 _91536 s g f x)). Qed.
Lemma lem3566961 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term155 _91535 _91536 s g f) = (term156 _91535 _91536 s g f).
Proof. exact (fun_ext (fun x : _91536 => @lem3566960 _91535 _91536 s g f x)). Qed.
Lemma lem3566962 {_91536 : Type'} : (@ex _91536) = (@ex _91536).
Proof. exact (eq_refl (@ex _91536)). Qed.
Lemma lem3566963 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term152 _91535 _91536 s g f) = (term157 _91535 _91536 s g f).
Proof. exact (MK_COMB (@lem3566962 _91536) (@lem3566961 _91535 _91536 s g f)). Qed.
Lemma lem3566964 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term151 _91535 _91536 s g f) = (term157 _91535 _91536 s g f).
Proof. exact (TRANS (@lem3566956 _91535 _91536 s g f) (@lem3566963 _91535 _91536 s g f)). Qed.
Lemma lem3566965 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3566966 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term158 _91535 _91536 t f g) = (term159 _91535 _91536 t f g).
Proof. exact (MK_COMB (@lem3566965) (@lem3566947 _91535 _91536 t f g)). Qed.
Lemma lem3566967 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term160 _91535 _91536 t s g f) = (term161 _91535 _91536 t s g f).
Proof. exact (MK_COMB (@lem3566966 _91535 _91536 t f g) (@lem3566964 _91535 _91536 s g f)). Qed.
Lemma lem3566968 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term162 _91535 _91536 t s g f) = (term160 _91535 _91536 t s g f).
Proof. exact (@lem17045 (term76 _91535 _91536 t f g) (term73 _91535 _91536 s g f)). Qed.
Lemma lem3566969 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term162 _91535 _91536 t s g f) = (term161 _91535 _91536 t s g f).
Proof. exact (TRANS (@lem3566968 _91535 _91536 t s g f) (@lem3566967 _91535 _91536 t s g f)). Qed.
Lemma lem3566970 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3566971 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (s : _91536 -> Prop) : (term163 _91535 _91536 t g s) = (term164 _91535 _91536 t g s).
Proof. exact (MK_COMB (@lem3566970) (@lem3566930 _91535 _91536 t g s)). Qed.
Lemma lem3566972 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term165 _91535 _91536 t s g f) = (term166 _91535 _91536 t s g f).
Proof. exact (MK_COMB (@lem3566971 _91535 _91536 t g s) (@lem3566969 _91535 _91536 t s g f)). Qed.
Lemma lem3566973 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term91 _91535 _91536 t s g f) = (term165 _91535 _91536 t s g f).
Proof. exact (@lem17045 (term81 _91535 _91536 t g s) (term78 _91535 _91536 t s g f)). Qed.
Lemma lem3566974 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term91 _91535 _91536 t s g f) = (term166 _91535 _91536 t s g f).
Proof. exact (TRANS (@lem3566973 _91535 _91536 t s g f) (@lem3566972 _91535 _91536 t s g f)). Qed.
Lemma lem3567123 {A : Type'} (P : A -> Prop) (Q : Prop) : (term167 A P Q) = (term168 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3567124 {_91535 : Type'} (P : _91535 -> Prop) (Q : Prop) : (term167 _91535 P Q) = (term168 _91535 P Q).
Proof. exact (@lem3567123 _91535 P Q). Qed.
Lemma lem3567125 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term169 _91535 _91536 t s g f) = (term170 _91535 _91536 t s g f).
Proof. exact (@lem3567124 _91535 (term147 _91535 _91536 t f g) (term157 _91535 _91536 s g f)). Qed.
Lemma lem3567126 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : (term171 _91535 _91536 t f g y) = (term140 _91535 _91536 t f g y).
Proof. exact (eq_refl (term171 _91535 _91536 t f g y)). Qed.
Lemma lem3567127 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term172 _91535 _91536 t f g) = (term147 _91535 _91536 t f g).
Proof. exact (fun_ext (fun y : _91535 => @lem3567126 _91535 _91536 t f g y)). Qed.
Lemma lem3567128 {_91535 : Type'} : (@ex _91535) = (@ex _91535).
Proof. exact (eq_refl (@ex _91535)). Qed.
Lemma lem3567129 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term173 _91535 _91536 t f g) = (term148 _91535 _91536 t f g).
Proof. exact (MK_COMB (@lem3567128 _91535) (@lem3567127 _91535 _91536 t f g)). Qed.
Lemma lem3567130 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3567131 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term174 _91535 _91536 t f g) = (term159 _91535 _91536 t f g).
Proof. exact (MK_COMB (@lem3567130) (@lem3567129 _91535 _91536 t f g)). Qed.
Lemma lem3567132 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term157 _91535 _91536 s g f) = (term157 _91535 _91536 s g f).
Proof. exact (eq_refl (term157 _91535 _91536 s g f)). Qed.
Lemma lem3567133 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term169 _91535 _91536 t s g f) = (term161 _91535 _91536 t s g f).
Proof. exact (MK_COMB (@lem3567131 _91535 _91536 t f g) (@lem3567132 _91535 _91536 s g f)). Qed.
Lemma lem3567134 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3567135 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term175 _91535 _91536 t s g f) = (term176 _91535 _91536 t s g f).
Proof. exact (MK_COMB (@lem3567134) (@lem3567133 _91535 _91536 t s g f)). Qed.
Lemma lem3567136 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : (term171 _91535 _91536 t f g y) = (term140 _91535 _91536 t f g y).
Proof. exact (eq_refl (term171 _91535 _91536 t f g y)). Qed.
Lemma lem3567137 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3567138 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : (term177 _91535 _91536 t f g y) = (term178 _91535 _91536 t f g y).
Proof. exact (MK_COMB (@lem3567137) (@lem3567136 _91535 _91536 t f g y)). Qed.
Lemma lem3567139 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term157 _91535 _91536 s g f) = (term157 _91535 _91536 s g f).
Proof. exact (eq_refl (term157 _91535 _91536 s g f)). Qed.
Lemma lem3567140 {_91535 _91536 : Type'} (t : _91535 -> Prop) (y : _91535) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term179 _91535 _91536 t y s g f) = (term180 _91535 _91536 t y s g f).
Proof. exact (MK_COMB (@lem3567138 _91535 _91536 t f g y) (@lem3567139 _91535 _91536 s g f)). Qed.
Lemma lem3567141 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term181 _91535 _91536 t s g f) = (term182 _91535 _91536 t s g f).
Proof. exact (fun_ext (fun y : _91535 => @lem3567140 _91535 _91536 t y s g f)). Qed.
Lemma lem3567142 {_91535 : Type'} : (@ex _91535) = (@ex _91535).
Proof. exact (eq_refl (@ex _91535)). Qed.
Lemma lem3567143 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term170 _91535 _91536 t s g f) = (term183 _91535 _91536 t s g f).
Proof. exact (MK_COMB (@lem3567142 _91535) (@lem3567141 _91535 _91536 t s g f)). Qed.
Lemma lem3567144 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : ((term169 _91535 _91536 t s g f) = (term170 _91535 _91536 t s g f)) = ((term161 _91535 _91536 t s g f) = (term183 _91535 _91536 t s g f)).
Proof. exact (MK_COMB (@lem3567135 _91535 _91536 t s g f) (@lem3567143 _91535 _91536 t s g f)). Qed.
Lemma lem3567145 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term161 _91535 _91536 t s g f) = (term183 _91535 _91536 t s g f).
Proof. exact (EQ_MP (@lem3567144 _91535 _91536 t s g f) (@lem3567125 _91535 _91536 t s g f)). Qed.
Lemma lem3567147 {A : Type'} (P : Prop) (Q : A -> Prop) : (term184 A P Q) = (term185 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3567148 {_91536 : Type'} (P : Prop) (Q : _91536 -> Prop) : (term184 _91536 P Q) = (term185 _91536 P Q).
Proof. exact (@lem3567147 _91536 P Q). Qed.
Lemma lem3567149 {_91535 _91536 : Type'} (t : _91535 -> Prop) (y : _91535) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term186 _91535 _91536 t y s g f) = (term187 _91535 _91536 t y s g f).
Proof. exact (@lem3567148 _91536 (term140 _91535 _91536 t f g y) (term156 _91535 _91536 s g f)). Qed.
Lemma lem3567150 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : (term188 _91535 _91536 s g f x) = (term150 _91535 _91536 s g f x).
Proof. exact (eq_refl (term188 _91535 _91536 s g f x)). Qed.
Lemma lem3567151 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term189 _91535 _91536 s g f) = (term156 _91535 _91536 s g f).
Proof. exact (fun_ext (fun x : _91536 => @lem3567150 _91535 _91536 s g f x)). Qed.
Lemma lem3567152 {_91536 : Type'} : (@ex _91536) = (@ex _91536).
Proof. exact (eq_refl (@ex _91536)). Qed.
Lemma lem3567153 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term190 _91535 _91536 s g f) = (term157 _91535 _91536 s g f).
Proof. exact (MK_COMB (@lem3567152 _91536) (@lem3567151 _91535 _91536 s g f)). Qed.
Lemma lem3567154 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : (term178 _91535 _91536 t f g y) = (term178 _91535 _91536 t f g y).
Proof. exact (eq_refl (term178 _91535 _91536 t f g y)). Qed.
Lemma lem3567155 {_91535 _91536 : Type'} (t : _91535 -> Prop) (y : _91535) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term186 _91535 _91536 t y s g f) = (term180 _91535 _91536 t y s g f).
Proof. exact (MK_COMB (@lem3567154 _91535 _91536 t f g y) (@lem3567153 _91535 _91536 s g f)). Qed.
Lemma lem3567156 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3567157 {_91535 _91536 : Type'} (t : _91535 -> Prop) (y : _91535) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term191 _91535 _91536 t y s g f) = (term192 _91535 _91536 t y s g f).
Proof. exact (MK_COMB (@lem3567156) (@lem3567155 _91535 _91536 t y s g f)). Qed.
Lemma lem3567158 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : (term188 _91535 _91536 s g f x) = (term150 _91535 _91536 s g f x).
Proof. exact (eq_refl (term188 _91535 _91536 s g f x)). Qed.
Lemma lem3567159 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : (term178 _91535 _91536 t f g y) = (term178 _91535 _91536 t f g y).
Proof. exact (eq_refl (term178 _91535 _91536 t f g y)). Qed.
Lemma lem3567160 {_91535 _91536 : Type'} (t : _91535 -> Prop) (y : _91535) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : (term193 _91535 _91536 t y s g f x) = (term194 _91535 _91536 t y s g f x).
Proof. exact (MK_COMB (@lem3567159 _91535 _91536 t f g y) (@lem3567158 _91535 _91536 s g f x)). Qed.
Lemma lem3567161 {_91535 _91536 : Type'} (t : _91535 -> Prop) (y : _91535) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term195 _91535 _91536 t y s g f) = (term196 _91535 _91536 t y s g f).
Proof. exact (fun_ext (fun x : _91536 => @lem3567160 _91535 _91536 t y s g f x)). Qed.
Lemma lem3567162 {_91536 : Type'} : (@ex _91536) = (@ex _91536).
Proof. exact (eq_refl (@ex _91536)). Qed.
Lemma lem3567163 {_91535 _91536 : Type'} (t : _91535 -> Prop) (y : _91535) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term187 _91535 _91536 t y s g f) = (term197 _91535 _91536 t y s g f).
Proof. exact (MK_COMB (@lem3567162 _91536) (@lem3567161 _91535 _91536 t y s g f)). Qed.
Lemma lem3567164 {_91535 _91536 : Type'} (t : _91535 -> Prop) (y : _91535) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : ((term186 _91535 _91536 t y s g f) = (term187 _91535 _91536 t y s g f)) = ((term180 _91535 _91536 t y s g f) = (term197 _91535 _91536 t y s g f)).
Proof. exact (MK_COMB (@lem3567157 _91535 _91536 t y s g f) (@lem3567163 _91535 _91536 t y s g f)). Qed.
Lemma lem3567165 {_91535 _91536 : Type'} (t : _91535 -> Prop) (y : _91535) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term180 _91535 _91536 t y s g f) = (term197 _91535 _91536 t y s g f).
Proof. exact (EQ_MP (@lem3567164 _91535 _91536 t y s g f) (@lem3567149 _91535 _91536 t y s g f)). Qed.
Lemma lem3567166 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term182 _91535 _91536 t s g f) = (term198 _91535 _91536 t s g f).
Proof. exact (fun_ext (fun y : _91535 => @lem3567165 _91535 _91536 t y s g f)). Qed.
Lemma lem3567167 {_91535 : Type'} : (@ex _91535) = (@ex _91535).
Proof. exact (eq_refl (@ex _91535)). Qed.
Lemma lem3567168 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term183 _91535 _91536 t s g f) = (term199 _91535 _91536 t s g f).
Proof. exact (MK_COMB (@lem3567167 _91535) (@lem3567166 _91535 _91536 t s g f)). Qed.
Lemma lem3567169 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term161 _91535 _91536 t s g f) = (term199 _91535 _91536 t s g f).
Proof. exact (TRANS (@lem3567145 _91535 _91536 t s g f) (@lem3567168 _91535 _91536 t s g f)). Qed.
Lemma lem3567170 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (s : _91536 -> Prop) : (term164 _91535 _91536 t g s) = (term164 _91535 _91536 t g s).
Proof. exact (eq_refl (term164 _91535 _91536 t g s)). Qed.
Lemma lem3567171 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term166 _91535 _91536 t s g f) = (term200 _91535 _91536 t s g f).
Proof. exact (MK_COMB (@lem3567170 _91535 _91536 t g s) (@lem3567169 _91535 _91536 t s g f)). Qed.
Lemma lem3567173 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term201 A P Q) = (term202 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3567174 {_91535 : Type'} (P : _91535 -> Prop) (Q : _91535 -> Prop) : (term201 _91535 P Q) = (term202 _91535 P Q).
Proof. exact (@lem3567173 _91535 P Q). Qed.
Lemma lem3567175 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term203 _91535 _91536 t s g f) = (term204 _91535 _91536 t s g f).
Proof. exact (@lem3567174 _91535 (term137 _91535 _91536 t g s) (term198 _91535 _91536 t s g f)). Qed.
Lemma lem3567176 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (y : _91535) (s : _91536 -> Prop) : (term205 _91535 _91536 t g s y) = (term128 _91535 _91536 t g y s).
Proof. exact (eq_refl (term205 _91535 _91536 t g s y)). Qed.
Lemma lem3567177 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (s : _91536 -> Prop) : (term206 _91535 _91536 t g s) = (term137 _91535 _91536 t g s).
Proof. exact (fun_ext (fun y : _91535 => @lem3567176 _91535 _91536 t g y s)). Qed.
Lemma lem3567178 {_91535 : Type'} : (@ex _91535) = (@ex _91535).
Proof. exact (eq_refl (@ex _91535)). Qed.
Lemma lem3567179 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (s : _91536 -> Prop) : (term207 _91535 _91536 t g s) = (term138 _91535 _91536 t g s).
Proof. exact (MK_COMB (@lem3567178 _91535) (@lem3567177 _91535 _91536 t g s)). Qed.
Lemma lem3567180 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3567181 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (s : _91536 -> Prop) : (term208 _91535 _91536 t g s) = (term164 _91535 _91536 t g s).
Proof. exact (MK_COMB (@lem3567180) (@lem3567179 _91535 _91536 t g s)). Qed.
Lemma lem3567182 {_91535 _91536 : Type'} (t : _91535 -> Prop) (y : _91535) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term209 _91535 _91536 t s g f y) = (term197 _91535 _91536 t y s g f).
Proof. exact (eq_refl (term209 _91535 _91536 t s g f y)). Qed.
Lemma lem3567183 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term210 _91535 _91536 t s g f) = (term198 _91535 _91536 t s g f).
Proof. exact (fun_ext (fun y : _91535 => @lem3567182 _91535 _91536 t y s g f)). Qed.
Lemma lem3567184 {_91535 : Type'} : (@ex _91535) = (@ex _91535).
Proof. exact (eq_refl (@ex _91535)). Qed.
Lemma lem3567185 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term211 _91535 _91536 t s g f) = (term199 _91535 _91536 t s g f).
Proof. exact (MK_COMB (@lem3567184 _91535) (@lem3567183 _91535 _91536 t s g f)). Qed.
Lemma lem3567186 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term203 _91535 _91536 t s g f) = (term200 _91535 _91536 t s g f).
Proof. exact (MK_COMB (@lem3567181 _91535 _91536 t g s) (@lem3567185 _91535 _91536 t s g f)). Qed.
Lemma lem3567187 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3567188 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term212 _91535 _91536 t s g f) = (term213 _91535 _91536 t s g f).
Proof. exact (MK_COMB (@lem3567187) (@lem3567186 _91535 _91536 t s g f)). Qed.
Lemma lem3567189 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (y : _91535) (s : _91536 -> Prop) : (term205 _91535 _91536 t g s y) = (term128 _91535 _91536 t g y s).
Proof. exact (eq_refl (term205 _91535 _91536 t g s y)). Qed.
Lemma lem3567190 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3567191 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (y : _91535) (s : _91536 -> Prop) : (term214 _91535 _91536 t g s y) = (term215 _91535 _91536 t g y s).
Proof. exact (MK_COMB (@lem3567190) (@lem3567189 _91535 _91536 t g y s)). Qed.
Lemma lem3567192 {_91535 _91536 : Type'} (t : _91535 -> Prop) (y : _91535) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term209 _91535 _91536 t s g f y) = (term197 _91535 _91536 t y s g f).
Proof. exact (eq_refl (term209 _91535 _91536 t s g f y)). Qed.
Lemma lem3567193 {_91535 _91536 : Type'} (t : _91535 -> Prop) (y : _91535) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term216 _91535 _91536 t s g f y) = (term217 _91535 _91536 t y s g f).
Proof. exact (MK_COMB (@lem3567191 _91535 _91536 t g y s) (@lem3567192 _91535 _91536 t y s g f)). Qed.
Lemma lem3567194 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term218 _91535 _91536 t s g f) = (term219 _91535 _91536 t s g f).
Proof. exact (fun_ext (fun y : _91535 => @lem3567193 _91535 _91536 t y s g f)). Qed.
Lemma lem3567195 {_91535 : Type'} : (@ex _91535) = (@ex _91535).
Proof. exact (eq_refl (@ex _91535)). Qed.
Lemma lem3567196 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term204 _91535 _91536 t s g f) = (term220 _91535 _91536 t s g f).
Proof. exact (MK_COMB (@lem3567195 _91535) (@lem3567194 _91535 _91536 t s g f)). Qed.
Lemma lem3567197 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : ((term203 _91535 _91536 t s g f) = (term204 _91535 _91536 t s g f)) = ((term200 _91535 _91536 t s g f) = (term220 _91535 _91536 t s g f)).
Proof. exact (MK_COMB (@lem3567188 _91535 _91536 t s g f) (@lem3567196 _91535 _91536 t s g f)). Qed.
Lemma lem3567198 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term200 _91535 _91536 t s g f) = (term220 _91535 _91536 t s g f).
Proof. exact (EQ_MP (@lem3567197 _91535 _91536 t s g f) (@lem3567175 _91535 _91536 t s g f)). Qed.
Lemma lem3567200 {A : Type'} (P : Prop) (Q : A -> Prop) : (term184 A P Q) = (term185 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3567201 {_91536 : Type'} (P : Prop) (Q : _91536 -> Prop) : (term184 _91536 P Q) = (term185 _91536 P Q).
Proof. exact (@lem3567200 _91536 P Q). Qed.
Lemma lem3567202 {_91535 _91536 : Type'} (t : _91535 -> Prop) (y : _91535) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term221 _91535 _91536 t y s g f) = (term222 _91535 _91536 t y s g f).
Proof. exact (@lem3567201 _91536 (term128 _91535 _91536 t g y s) (term196 _91535 _91536 t y s g f)). Qed.
Lemma lem3567203 {_91535 _91536 : Type'} (t : _91535 -> Prop) (y : _91535) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : (term223 _91535 _91536 t y s g f x) = (term194 _91535 _91536 t y s g f x).
Proof. exact (eq_refl (term223 _91535 _91536 t y s g f x)). Qed.
Lemma lem3567204 {_91535 _91536 : Type'} (t : _91535 -> Prop) (y : _91535) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term224 _91535 _91536 t y s g f) = (term196 _91535 _91536 t y s g f).
Proof. exact (fun_ext (fun x : _91536 => @lem3567203 _91535 _91536 t y s g f x)). Qed.
Lemma lem3567205 {_91536 : Type'} : (@ex _91536) = (@ex _91536).
Proof. exact (eq_refl (@ex _91536)). Qed.
Lemma lem3567206 {_91535 _91536 : Type'} (t : _91535 -> Prop) (y : _91535) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term225 _91535 _91536 t y s g f) = (term197 _91535 _91536 t y s g f).
Proof. exact (MK_COMB (@lem3567205 _91536) (@lem3567204 _91535 _91536 t y s g f)). Qed.
Lemma lem3567207 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (y : _91535) (s : _91536 -> Prop) : (term215 _91535 _91536 t g y s) = (term215 _91535 _91536 t g y s).
Proof. exact (eq_refl (term215 _91535 _91536 t g y s)). Qed.
Lemma lem3567208 {_91535 _91536 : Type'} (t : _91535 -> Prop) (y : _91535) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term221 _91535 _91536 t y s g f) = (term217 _91535 _91536 t y s g f).
Proof. exact (MK_COMB (@lem3567207 _91535 _91536 t g y s) (@lem3567206 _91535 _91536 t y s g f)). Qed.
Lemma lem3567209 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3567210 {_91535 _91536 : Type'} (t : _91535 -> Prop) (y : _91535) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term226 _91535 _91536 t y s g f) = (term227 _91535 _91536 t y s g f).
Proof. exact (MK_COMB (@lem3567209) (@lem3567208 _91535 _91536 t y s g f)). Qed.
Lemma lem3567211 {_91535 _91536 : Type'} (t : _91535 -> Prop) (y : _91535) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : (term223 _91535 _91536 t y s g f x) = (term194 _91535 _91536 t y s g f x).
Proof. exact (eq_refl (term223 _91535 _91536 t y s g f x)). Qed.
Lemma lem3567212 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (y : _91535) (s : _91536 -> Prop) : (term215 _91535 _91536 t g y s) = (term215 _91535 _91536 t g y s).
Proof. exact (eq_refl (term215 _91535 _91536 t g y s)). Qed.
Lemma lem3567213 {_91535 _91536 : Type'} (t : _91535 -> Prop) (y : _91535) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : (term228 _91535 _91536 t y s g f x) = (term229 _91535 _91536 t y s g f x).
Proof. exact (MK_COMB (@lem3567212 _91535 _91536 t g y s) (@lem3567211 _91535 _91536 t y s g f x)). Qed.
Lemma lem3567214 {_91535 _91536 : Type'} (t : _91535 -> Prop) (y : _91535) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term230 _91535 _91536 t y s g f) = (term231 _91535 _91536 t y s g f).
Proof. exact (fun_ext (fun x : _91536 => @lem3567213 _91535 _91536 t y s g f x)). Qed.
Lemma lem3567215 {_91536 : Type'} : (@ex _91536) = (@ex _91536).
Proof. exact (eq_refl (@ex _91536)). Qed.
Lemma lem3567216 {_91535 _91536 : Type'} (t : _91535 -> Prop) (y : _91535) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term222 _91535 _91536 t y s g f) = (term232 _91535 _91536 t y s g f).
Proof. exact (MK_COMB (@lem3567215 _91536) (@lem3567214 _91535 _91536 t y s g f)). Qed.
Lemma lem3567217 {_91535 _91536 : Type'} (t : _91535 -> Prop) (y : _91535) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : ((term221 _91535 _91536 t y s g f) = (term222 _91535 _91536 t y s g f)) = ((term217 _91535 _91536 t y s g f) = (term232 _91535 _91536 t y s g f)).
Proof. exact (MK_COMB (@lem3567210 _91535 _91536 t y s g f) (@lem3567216 _91535 _91536 t y s g f)). Qed.
Lemma lem3567218 {_91535 _91536 : Type'} (t : _91535 -> Prop) (y : _91535) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term217 _91535 _91536 t y s g f) = (term232 _91535 _91536 t y s g f).
Proof. exact (EQ_MP (@lem3567217 _91535 _91536 t y s g f) (@lem3567202 _91535 _91536 t y s g f)). Qed.
Lemma lem3567219 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term219 _91535 _91536 t s g f) = (term233 _91535 _91536 t s g f).
Proof. exact (fun_ext (fun y : _91535 => @lem3567218 _91535 _91536 t y s g f)). Qed.
Lemma lem3567220 {_91535 : Type'} : (@ex _91535) = (@ex _91535).
Proof. exact (eq_refl (@ex _91535)). Qed.
Lemma lem3567221 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term220 _91535 _91536 t s g f) = (term234 _91535 _91536 t s g f).
Proof. exact (MK_COMB (@lem3567220 _91535) (@lem3567219 _91535 _91536 t s g f)). Qed.
Lemma lem3567222 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term200 _91535 _91536 t s g f) = (term234 _91535 _91536 t s g f).
Proof. exact (TRANS (@lem3567198 _91535 _91536 t s g f) (@lem3567221 _91535 _91536 t s g f)). Qed.
Lemma lem3567224 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term166 _91535 _91536 t s g f) = (term234 _91535 _91536 t s g f).
Proof. exact (TRANS (@lem3567171 _91535 _91536 t s g f) (@lem3567222 _91535 _91536 t s g f)). Qed.
Lemma lem3567225 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term91 _91535 _91536 t s g f) = (term234 _91535 _91536 t s g f).
Proof. exact (TRANS (@lem3566974 _91535 _91536 t s g f) (@lem3567224 _91535 _91536 t s g f)). Qed.
Lemma lem3567226 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term91 _91535 _91536 t s g f) : term234 _91535 _91536 t s g f.
Proof. exact (EQ_MP (@lem3567225 _91535 _91536 t s g f) (@lem3566692 _91535 _91536 t s g f h1)). Qed.
Lemma lem3567227 {_91535 _91536 : Type'} (t : _91535 -> Prop) (y : _91535) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term232 _91535 _91536 t y s g f) : term232 _91535 _91536 t y s g f.
Proof. exact (h1). Qed.
Lemma lem3567229 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term123 _91535 _91536 g' t s f g) : term123 _91535 _91536 g' t s f g.
Proof. exact (h1). Qed.
Lemma lem3567246 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (x : _91536) (t : _91535 -> Prop) : (term92 _91535 _91536 s f x t) = (term92 _91535 _91536 s f x t).
Proof. exact (eq_refl (term92 _91535 _91536 s f x t)). Qed.
Lemma lem3567247 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (t : _91535 -> Prop) : (term94 _91535 _91536 s f t) = (term94 _91535 _91536 s f t).
Proof. exact (fun_ext (fun x : _91536 => @lem3567246 _91535 _91536 s f x t)). Qed.
Lemma lem3567248 {_91536 : Type'} : (@all _91536) = (@all _91536).
Proof. exact (eq_refl (@all _91536)). Qed.
Lemma lem3567249 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (t : _91535 -> Prop) : (term95 _91535 _91536 s f t) = (term95 _91535 _91536 s f t).
Proof. exact (MK_COMB (@lem3567248 _91536) (@lem3567247 _91535 _91536 s f t)). Qed.
Lemma lem3567250 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (t : _91535 -> Prop) (h1 : term15 _91535 _91536 s f t) : term95 _91535 _91536 s f t.
Proof. exact (EQ_MP (@lem3567249 _91535 _91536 s f t) (@lem3566755 _91535 _91536 s f t h1)). Qed.
Lemma lem3567312 {_91535 _91536 : Type'} (t : _91535 -> Prop) (y : _91535) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term229 _91535 _91536 t y s g f x) : term229 _91535 _91536 t y s g f x.
Proof. exact (h1). Qed.
Lemma lem3567341 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : (term102 _91535 _91536 t s f g y) = (term102 _91535 _91536 t s f g y).
Proof. exact (eq_refl (term102 _91535 _91536 t s f g y)). Qed.
Lemma lem3567342 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term104 _91535 _91536 t s f g) = (term104 _91535 _91536 t s f g).
Proof. exact (fun_ext (fun y : _91535 => @lem3567341 _91535 _91536 t s f g y)). Qed.
Lemma lem3567343 {_91535 : Type'} : (@all _91535) = (@all _91535).
Proof. exact (eq_refl (@all _91535)). Qed.
Lemma lem3567344 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term105 _91535 _91536 t s f g) = (term105 _91535 _91536 t s f g).
Proof. exact (MK_COMB (@lem3567343 _91535) (@lem3567342 _91535 _91536 t s f g)). Qed.
Lemma lem3567363 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g' : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : (term96 _91535 _91536 s g' f x) = (term96 _91535 _91536 s g' f x).
Proof. exact (eq_refl (term96 _91535 _91536 s g' f x)). Qed.
Lemma lem3567364 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g' : _91535 -> _91536) (f : _91536 -> _91535) : (term98 _91535 _91536 s g' f) = (term98 _91535 _91536 s g' f).
Proof. exact (fun_ext (fun x : _91536 => @lem3567363 _91535 _91536 s g' f x)). Qed.
Lemma lem3567365 {_91536 : Type'} : (@all _91536) = (@all _91536).
Proof. exact (eq_refl (@all _91536)). Qed.
Lemma lem3567366 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g' : _91535 -> _91536) (f : _91536 -> _91535) : (term99 _91535 _91536 s g' f) = (term99 _91535 _91536 s g' f).
Proof. exact (MK_COMB (@lem3567365 _91536) (@lem3567364 _91535 _91536 s g' f)). Qed.
Lemma lem3567367 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3567368 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g' : _91535 -> _91536) (f : _91536 -> _91535) : (term121 _91535 _91536 s g' f) = (term121 _91535 _91536 s g' f).
Proof. exact (MK_COMB (@lem3567367) (@lem3567366 _91535 _91536 s g' f)). Qed.
Lemma lem3567369 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term123 _91535 _91536 g' t s f g) = (term123 _91535 _91536 g' t s f g).
Proof. exact (MK_COMB (@lem3567368 _91535 _91536 s g' f) (@lem3567344 _91535 _91536 t s f g)). Qed.
Lemma lem3567370 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term123 _91535 _91536 g' t s f g) : term123 _91535 _91536 g' t s f g.
Proof. exact (EQ_MP (@lem3567369 _91535 _91536 g' t s f g) (@lem3567229 _91535 _91536 g' t s f g h1)). Qed.
Lemma lem3567371 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term123 _91535 _91536 g' t s f g) : term105 _91535 _91536 t s f g.
Proof. exact (proj2 (@lem3567370 _91535 _91536 g' t s f g h1)). Qed.
Lemma lem3567372 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term123 _91535 _91536 g' t s f g) : term99 _91535 _91536 s g' f.
Proof. exact (proj1 (@lem3567370 _91535 _91536 g' t s f g h1)). Qed.
Lemma lem3567373 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (y : _91535) (s : _91536 -> Prop) (h1 : term128 _91535 _91536 t g y s) : term128 _91535 _91536 t g y s.
Proof. exact (h1). Qed.
Lemma lem3567374 {_91535 _91536 : Type'} (t : _91535 -> Prop) (y : _91535) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term194 _91535 _91536 t y s g f x) : term194 _91535 _91536 t y s g f x.
Proof. exact (h1). Qed.
Lemma lem3567377 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term140 _91535 _91536 t f g y) : term140 _91535 _91536 t f g y.
Proof. exact (h1). Qed.
Lemma lem3567378 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term150 _91535 _91536 s g f x) : term150 _91535 _91536 s g f x.
Proof. exact (h1). Qed.
Lemma lem3567426 {_91535 _91536 : Type'} (s : _91536 -> Prop) (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : (term102 _91535 _91536 t s f g y) = (term235 _91535 _91536 s t f g y).
Proof. exact (@lem19490 (term129 _91535 _91536 g y s) (term236 _91535 y t) ((term141 _91535 _91536 f g y) = y)). Qed.
Lemma lem3567427 {_91535 _91536 : Type'} (s : _91536 -> Prop) (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term104 _91535 _91536 t s f g) = (term237 _91535 _91536 s t f g).
Proof. exact (fun_ext (fun y : _91535 => @lem3567426 _91535 _91536 s t f g y)). Qed.
Lemma lem3567428 {_91535 : Type'} : (@all _91535) = (@all _91535).
Proof. exact (eq_refl (@all _91535)). Qed.
Lemma lem3567430 {_91535 _91536 : Type'} (s : _91536 -> Prop) (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term105 _91535 _91536 t s f g) = (term238 _91535 _91536 s t f g).
Proof. exact (MK_COMB (@lem3567428 _91535) (@lem3567427 _91535 _91536 s t f g)). Qed.
Lemma lem3567431 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term123 _91535 _91536 g' t s f g) : term238 _91535 _91536 s t f g.
Proof. exact (EQ_MP (@lem3567430 _91535 _91536 s t f g) (@lem3567371 _91535 _91536 g' t s f g h1)). Qed.
Lemma lem3567483 {_91535 _91536 : Type'} (s : _91536 -> Prop) (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : (term102 _91535 _91536 t s f g y) = (term235 _91535 _91536 s t f g y).
Proof. exact (@lem19490 (term129 _91535 _91536 g y s) (term236 _91535 y t) ((term141 _91535 _91536 f g y) = y)). Qed.
Lemma lem3567484 {_91535 _91536 : Type'} (s : _91536 -> Prop) (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term104 _91535 _91536 t s f g) = (term237 _91535 _91536 s t f g).
Proof. exact (fun_ext (fun y : _91535 => @lem3567483 _91535 _91536 s t f g y)). Qed.
Lemma lem3567485 {_91535 : Type'} : (@all _91535) = (@all _91535).
Proof. exact (eq_refl (@all _91535)). Qed.
Lemma lem3567487 {_91535 _91536 : Type'} (s : _91536 -> Prop) (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term105 _91535 _91536 t s f g) = (term238 _91535 _91536 s t f g).
Proof. exact (MK_COMB (@lem3567485 _91535) (@lem3567484 _91535 _91536 s t f g)). Qed.
Lemma lem3567488 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term123 _91535 _91536 g' t s f g) : term238 _91535 _91536 s t f g.
Proof. exact (EQ_MP (@lem3567487 _91535 _91536 s t f g) (@lem3567371 _91535 _91536 g' t s f g h1)). Qed.
Lemma lem3567504 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (x : _91536) (t : _91535 -> Prop) : (term92 _91535 _91536 s f x t) = (term92 _91535 _91536 s f x t).
Proof. exact (eq_refl (term92 _91535 _91536 s f x t)). Qed.
Lemma lem3567505 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (t : _91535 -> Prop) : (term94 _91535 _91536 s f t) = (term94 _91535 _91536 s f t).
Proof. exact (fun_ext (fun x : _91536 => @lem3567504 _91535 _91536 s f x t)). Qed.
Lemma lem3567506 {_91536 : Type'} : (@all _91536) = (@all _91536).
Proof. exact (eq_refl (@all _91536)). Qed.
Lemma lem3567508 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (t : _91535 -> Prop) : (term95 _91535 _91536 s f t) = (term95 _91535 _91536 s f t).
Proof. exact (MK_COMB (@lem3567506 _91536) (@lem3567505 _91535 _91536 s f t)). Qed.
Lemma lem3567509 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (t : _91535 -> Prop) (h1 : term15 _91535 _91536 s f t) : term95 _91535 _91536 s f t.
Proof. exact (EQ_MP (@lem3567508 _91535 _91536 s f t) (@lem3567250 _91535 _91536 s f t h1)). Qed.
Lemma lem3567517 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g' : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : (term96 _91535 _91536 s g' f x) = (term96 _91535 _91536 s g' f x).
Proof. exact (eq_refl (term96 _91535 _91536 s g' f x)). Qed.
Lemma lem3567518 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g' : _91535 -> _91536) (f : _91536 -> _91535) : (term98 _91535 _91536 s g' f) = (term98 _91535 _91536 s g' f).
Proof. exact (fun_ext (fun x : _91536 => @lem3567517 _91535 _91536 s g' f x)). Qed.
Lemma lem3567519 {_91536 : Type'} : (@all _91536) = (@all _91536).
Proof. exact (eq_refl (@all _91536)). Qed.
Lemma lem3567521 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g' : _91535 -> _91536) (f : _91536 -> _91535) : (term99 _91535 _91536 s g' f) = (term99 _91535 _91536 s g' f).
Proof. exact (MK_COMB (@lem3567519 _91536) (@lem3567518 _91535 _91536 s g' f)). Qed.
Lemma lem3567522 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term123 _91535 _91536 g' t s f g) : term99 _91535 _91536 s g' f.
Proof. exact (EQ_MP (@lem3567521 _91535 _91536 s g' f) (@lem3567372 _91535 _91536 g' t s f g h1)). Qed.
Lemma lem3567540 {_91535 _91536 : Type'} (s : _91536 -> Prop) (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : (term102 _91535 _91536 t s f g y) = (term235 _91535 _91536 s t f g y).
Proof. exact (@lem19490 (term129 _91535 _91536 g y s) (term236 _91535 y t) ((term141 _91535 _91536 f g y) = y)). Qed.
Lemma lem3567541 {_91535 _91536 : Type'} (s : _91536 -> Prop) (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term104 _91535 _91536 t s f g) = (term237 _91535 _91536 s t f g).
Proof. exact (fun_ext (fun y : _91535 => @lem3567540 _91535 _91536 s t f g y)). Qed.
Lemma lem3567542 {_91535 : Type'} : (@all _91535) = (@all _91535).
Proof. exact (eq_refl (@all _91535)). Qed.
Lemma lem3567544 {_91535 _91536 : Type'} (s : _91536 -> Prop) (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term105 _91535 _91536 t s f g) = (term238 _91535 _91536 s t f g).
Proof. exact (MK_COMB (@lem3567542 _91535) (@lem3567541 _91535 _91536 s t f g)). Qed.
Lemma lem3567545 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term123 _91535 _91536 g' t s f g) : term238 _91535 _91536 s t f g.
Proof. exact (EQ_MP (@lem3567544 _91535 _91536 s t f g) (@lem3567371 _91535 _91536 g' t s f g h1)). Qed.
Lemma lem3567560 {_91535 _91536 : Type'} (_38281 : _91535) (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term123 _91535 _91536 g' t s f g) : term239 _91535 _91536 s t f g _38281.
Proof. exact (@lem3567431 _91535 _91536 g' t s f g h1 _38281). Qed.
Lemma lem3567561 {_91535 _91536 : Type'} (s : _91536 -> Prop) (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (_38281 : _91535) : (term239 _91535 _91536 s t f g _38281) = (term235 _91535 _91536 s t f g _38281).
Proof. exact (eq_refl (term239 _91535 _91536 s t f g _38281)). Qed.
Lemma lem3567562 {_91535 _91536 : Type'} (_38281 : _91535) (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term123 _91535 _91536 g' t s f g) : term235 _91535 _91536 s t f g _38281.
Proof. exact (EQ_MP (@lem3567561 _91535 _91536 s t f g _38281) (@lem3567560 _91535 _91536 _38281 g' t s f g h1)). Qed.
Lemma lem3567569 {_91535 _91536 : Type'} (_38284 : _91535) (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term123 _91535 _91536 g' t s f g) : term239 _91535 _91536 s t f g _38284.
Proof. exact (@lem3567488 _91535 _91536 g' t s f g h1 _38284). Qed.
Lemma lem3567570 {_91535 _91536 : Type'} (s : _91536 -> Prop) (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (_38284 : _91535) : (term239 _91535 _91536 s t f g _38284) = (term235 _91535 _91536 s t f g _38284).
Proof. exact (eq_refl (term239 _91535 _91536 s t f g _38284)). Qed.
Lemma lem3567571 {_91535 _91536 : Type'} (_38284 : _91535) (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term123 _91535 _91536 g' t s f g) : term235 _91535 _91536 s t f g _38284.
Proof. exact (EQ_MP (@lem3567570 _91535 _91536 s t f g _38284) (@lem3567569 _91535 _91536 _38284 g' t s f g h1)). Qed.
Lemma lem3567572 {_91535 _91536 : Type'} (_38285 : _91536) (s : _91536 -> Prop) (f : _91536 -> _91535) (t : _91535 -> Prop) (h1 : term15 _91535 _91536 s f t) : term240 _91535 _91536 s f t _38285.
Proof. exact (@lem3567509 _91535 _91536 s f t h1 _38285). Qed.
Lemma lem3567573 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (_38285 : _91536) (t : _91535 -> Prop) : (term240 _91535 _91536 s f t _38285) = (term92 _91535 _91536 s f _38285 t).
Proof. exact (eq_refl (term240 _91535 _91536 s f t _38285)). Qed.
Lemma lem3567575 {_91535 _91536 : Type'} (_38286 : _91536) (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term123 _91535 _91536 g' t s f g) : term241 _91535 _91536 s g' f _38286.
Proof. exact (@lem3567522 _91535 _91536 g' t s f g h1 _38286). Qed.
Lemma lem3567576 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g' : _91535 -> _91536) (f : _91536 -> _91535) (_38286 : _91536) : (term241 _91535 _91536 s g' f _38286) = (term96 _91535 _91536 s g' f _38286).
Proof. exact (eq_refl (term241 _91535 _91536 s g' f _38286)). Qed.
Lemma lem3567578 {_91535 _91536 : Type'} (_38287 : _91535) (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term123 _91535 _91536 g' t s f g) : term239 _91535 _91536 s t f g _38287.
Proof. exact (@lem3567545 _91535 _91536 g' t s f g h1 _38287). Qed.
Lemma lem3567579 {_91535 _91536 : Type'} (s : _91536 -> Prop) (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (_38287 : _91535) : (term239 _91535 _91536 s t f g _38287) = (term235 _91535 _91536 s t f g _38287).
Proof. exact (eq_refl (term239 _91535 _91536 s t f g _38287)). Qed.
Lemma lem3567580 {_91535 _91536 : Type'} (_38287 : _91535) (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term123 _91535 _91536 g' t s f g) : term235 _91535 _91536 s t f g _38287.
Proof. exact (EQ_MP (@lem3567579 _91535 _91536 s t f g _38287) (@lem3567578 _91535 _91536 _38287 g' t s f g h1)). Qed.
Lemma lem3567602 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (y : _91535) (s : _91536 -> Prop) (h1 : term128 _91535 _91536 t g y s) : term242 _91535 _91536 g y s.
Proof. exact (proj2 (@lem3567373 _91535 _91536 t g y s h1)). Qed.
Lemma lem3567608 {_91535 _91536 : Type'} (_38281 : _91535) (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term123 _91535 _91536 g' t s f g) : term243 _91535 _91536 t g _38281 s.
Proof. exact (proj1 (@lem3567562 _91535 _91536 _38281 g' t s f g h1)). Qed.
Lemma lem3567630 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term140 _91535 _91536 t f g y) : term244 _91535 _91536 f g y.
Proof. exact (proj2 (@lem3567377 _91535 _91536 t f g y h1)). Qed.
Lemma lem3567642 {_91535 _91536 : Type'} (_38284 : _91535) (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term123 _91535 _91536 g' t s f g) : term245 _91535 _91536 t f g _38284.
Proof. exact (proj2 (@lem3567571 _91535 _91536 _38284 g' t s f g h1)). Qed.
Lemma lem3567648 {_91535 _91536 : Type'} (_38285 : _91536) (s : _91536 -> Prop) (f : _91536 -> _91535) (t : _91535 -> Prop) (h1 : term15 _91535 _91536 s f t) : term92 _91535 _91536 s f _38285 t.
Proof. exact (EQ_MP (@lem3567573 _91535 _91536 s f _38285 t) (@lem3567572 _91535 _91536 _38285 s f t h1)). Qed.
Lemma lem3567654 {_91535 _91536 : Type'} (_38286 : _91536) (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term123 _91535 _91536 g' t s f g) : term96 _91535 _91536 s g' f _38286.
Proof. exact (EQ_MP (@lem3567576 _91535 _91536 s g' f _38286) (@lem3567575 _91535 _91536 _38286 g' t s f g h1)). Qed.
Lemma lem3567658 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term150 _91535 _91536 s g f x) : term246 _91535 _91536 g f x.
Proof. exact (proj2 (@lem3567378 _91535 _91536 s g f x h1)). Qed.
Lemma lem3567664 {_91535 _91536 : Type'} (_38287 : _91535) (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term123 _91535 _91536 g' t s f g) : term243 _91535 _91536 t g _38287 s.
Proof. exact (proj1 (@lem3567580 _91535 _91536 _38287 g' t s f g h1)). Qed.
Lemma lem3567670 {_91535 _91536 : Type'} (_38287 : _91535) (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term123 _91535 _91536 g' t s f g) : term245 _91535 _91536 t f g _38287.
Proof. exact (proj2 (@lem3567580 _91535 _91536 _38287 g' t s f g h1)). Qed.
Lemma lem3567742 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (y : _91535) (s : _91536 -> Prop) (h1 : term128 _91535 _91536 t g y s) : @IN _91535 y t.
Proof. exact (proj1 (@lem3567373 _91535 _91536 t g y s h1)). Qed.
Lemma lem3567743 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (y : _91535) (s : _91536 -> Prop) (h1 : term128 _91535 _91536 t g y s) : term247 _91535 y t.
Proof. exact (fun h0 : term236 _91535 y t => @lem3567742 _91535 _91536 t g y s h1). Qed.
Lemma lem3567745 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3567746 {_91535 : Type'} (y : _91535) (t : _91535 -> Prop) : (term247 _91535 y t) = (@IN _91535 y t).
Proof. exact (@lem3567745 (@IN _91535 y t)). Qed.
Lemma lem3567747 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (y : _91535) (s : _91536 -> Prop) (h1 : term128 _91535 _91536 t g y s) : @IN _91535 y t.
Proof. exact (EQ_MP (@lem3567746 _91535 y t) (@lem3567743 _91535 _91536 t g y s h1)). Qed.
Lemma lem3567753 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3567754 {_91535 _91536 : Type'} (g : _91535 -> _91536) (s : _91536 -> Prop) (_38281 : _91535) (t : _91535 -> Prop) : (term243 _91535 _91536 t g _38281 s) = (term249 _91535 _91536 g s _38281 t).
Proof. exact (@lem3567753 (term129 _91535 _91536 g _38281 s) (term236 _91535 _38281 t)). Qed.
Lemma lem3567760 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3567761 {_91535 _91536 : Type'} (g : _91535 -> _91536) (s : _91536 -> Prop) (_38281 : _91535) (t : _91535 -> Prop) : (term250 _91535 _91536 t g _38281 s) = (term251 _91535 _91536 g s _38281 t).
Proof. exact (MK_COMB (@lem3567760) (@lem3567754 _91535 _91536 g s _38281 t)). Qed.
Lemma lem3567767 {_91535 _91536 : Type'} (g : _91535 -> _91536) (s : _91536 -> Prop) (_38281 : _91535) (t : _91535 -> Prop) : (term249 _91535 _91536 g s _38281 t) = (term249 _91535 _91536 g s _38281 t).
Proof. exact (eq_refl (term249 _91535 _91536 g s _38281 t)). Qed.
Lemma lem3567768 {_91535 _91536 : Type'} (g : _91535 -> _91536) (s : _91536 -> Prop) (_38281 : _91535) (t : _91535 -> Prop) : ((term243 _91535 _91536 t g _38281 s) = (term249 _91535 _91536 g s _38281 t)) = ((term249 _91535 _91536 g s _38281 t) = (term249 _91535 _91536 g s _38281 t)).
Proof. exact (MK_COMB (@lem3567761 _91535 _91536 g s _38281 t) (@lem3567767 _91535 _91536 g s _38281 t)). Qed.
Lemma lem3567770 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3567771 (x : Prop) : (x = x) = True.
Proof. exact (@lem3567770 Prop x). Qed.
Lemma lem3567772 {_91535 _91536 : Type'} (g : _91535 -> _91536) (s : _91536 -> Prop) (_38281 : _91535) (t : _91535 -> Prop) : ((term249 _91535 _91536 g s _38281 t) = (term249 _91535 _91536 g s _38281 t)) = True.
Proof. exact (@lem3567771 (term249 _91535 _91536 g s _38281 t)). Qed.
Lemma lem3567773 {_91535 _91536 : Type'} (g : _91535 -> _91536) (s : _91536 -> Prop) (_38281 : _91535) (t : _91535 -> Prop) : ((term243 _91535 _91536 t g _38281 s) = (term249 _91535 _91536 g s _38281 t)) = True.
Proof. exact (TRANS (@lem3567768 _91535 _91536 g s _38281 t) (@lem3567772 _91535 _91536 g s _38281 t)). Qed.
Lemma lem3567774 {_91535 _91536 : Type'} (g : _91535 -> _91536) (s : _91536 -> Prop) (_38281 : _91535) (t : _91535 -> Prop) : True = ((term243 _91535 _91536 t g _38281 s) = (term249 _91535 _91536 g s _38281 t)).
Proof. exact (SYM (@lem3567773 _91535 _91536 g s _38281 t)). Qed.
Lemma lem3567775 {_91535 _91536 : Type'} (g : _91535 -> _91536) (s : _91536 -> Prop) (_38281 : _91535) (t : _91535 -> Prop) : (term243 _91535 _91536 t g _38281 s) = (term249 _91535 _91536 g s _38281 t).
Proof. exact (EQ_MP (@lem3567774 _91535 _91536 g s _38281 t) (@lem0)). Qed.
Lemma lem3567776 {_91535 _91536 : Type'} (_38281 : _91535) (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term123 _91535 _91536 g' t s f g) : term249 _91535 _91536 g s _38281 t.
Proof. exact (EQ_MP (@lem3567775 _91535 _91536 g s _38281 t) (@lem3567608 _91535 _91536 _38281 g' t s f g h1)). Qed.
Lemma lem3567778 (b : Prop) (a : Prop) : (a \/ b) = (term252 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3567779 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (_38281 : _91535) (s : _91536 -> Prop) : (term249 _91535 _91536 g s _38281 t) = (term253 _91535 _91536 t g _38281 s).
Proof. exact (@lem3567778 (term236 _91535 _38281 t) (term129 _91535 _91536 g _38281 s)). Qed.
Lemma lem3567781 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3567782 {_91535 : Type'} (_38281 : _91535) (t : _91535 -> Prop) : (term254 _91535 _38281 t) = (@IN _91535 _38281 t).
Proof. exact (@lem3567781 (@IN _91535 _38281 t)). Qed.
Lemma lem3567783 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3567784 {_91535 : Type'} (_38281 : _91535) (t : _91535 -> Prop) : (term255 _91535 _38281 t) = (term256 _91535 _38281 t).
Proof. exact (MK_COMB (@lem3567783) (@lem3567782 _91535 _38281 t)). Qed.
Lemma lem3567785 {_91535 _91536 : Type'} (g : _91535 -> _91536) (_38281 : _91535) (s : _91536 -> Prop) : (term129 _91535 _91536 g _38281 s) = (term129 _91535 _91536 g _38281 s).
Proof. exact (eq_refl (term129 _91535 _91536 g _38281 s)). Qed.
Lemma lem3567786 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (_38281 : _91535) (s : _91536 -> Prop) : (term253 _91535 _91536 t g _38281 s) = (term79 _91535 _91536 t g _38281 s).
Proof. exact (MK_COMB (@lem3567784 _91535 _38281 t) (@lem3567785 _91535 _91536 g _38281 s)). Qed.
Lemma lem3567787 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (_38281 : _91535) (s : _91536 -> Prop) : (term249 _91535 _91536 g s _38281 t) = (term79 _91535 _91536 t g _38281 s).
Proof. exact (TRANS (@lem3567779 _91535 _91536 t g _38281 s) (@lem3567786 _91535 _91536 t g _38281 s)). Qed.
Lemma lem3567790 {_91535 _91536 : Type'} (_38281 : _91535) (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term123 _91535 _91536 g' t s f g) : term79 _91535 _91536 t g _38281 s.
Proof. exact (EQ_MP (@lem3567787 _91535 _91536 t g _38281 s) (@lem3567776 _91535 _91536 _38281 g' t s f g h1)). Qed.
Lemma lem3567791 {_91535 _91536 : Type'} (_38281 : _91535) (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term123 _91535 _91536 g' t s f g) : term79 _91535 _91536 t g _38281 s.
Proof. exact (@lem3567790 _91535 _91536 _38281 g' t s f g h1). Qed.
Lemma lem3567792 {_91535 _91536 : Type'} (y : _91535) (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term123 _91535 _91536 g' t s f g) : term79 _91535 _91536 t g y s.
Proof. exact (@lem3567791 _91535 _91536 y g' t s f g h1). Qed.
Lemma lem3567795 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (f : _91536 -> _91535) (t : _91535 -> Prop) (g : _91535 -> _91536) (y : _91535) (s : _91536 -> Prop) (h1 : term123 _91535 _91536 g' t s f g) (h2 : term128 _91535 _91536 t g y s) : term129 _91535 _91536 g y s.
Proof. exact (@lem3567792 _91535 _91536 y g' t s f g h1 (@lem3567747 _91535 _91536 t g y s h2)). Qed.
Lemma lem3567796 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (f : _91536 -> _91535) (t : _91535 -> Prop) (g : _91535 -> _91536) (y : _91535) (s : _91536 -> Prop) (h1 : term123 _91535 _91536 g' t s f g) (h2 : term128 _91535 _91536 t g y s) : term257 _91535 _91536 g y s.
Proof. exact (fun h0 : term242 _91535 _91536 g y s => @lem3567795 _91535 _91536 g' f t g y s h1 h2). Qed.
Lemma lem3567798 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3567799 {_91535 _91536 : Type'} (g : _91535 -> _91536) (y : _91535) (s : _91536 -> Prop) : (term257 _91535 _91536 g y s) = (term129 _91535 _91536 g y s).
Proof. exact (@lem3567798 (term129 _91535 _91536 g y s)). Qed.
Lemma lem3567800 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (f : _91536 -> _91535) (t : _91535 -> Prop) (g : _91535 -> _91536) (y : _91535) (s : _91536 -> Prop) (h1 : term123 _91535 _91536 g' t s f g) (h2 : term128 _91535 _91536 t g y s) : term129 _91535 _91536 g y s.
Proof. exact (EQ_MP (@lem3567799 _91535 _91536 g y s) (@lem3567796 _91535 _91536 g' f t g y s h1 h2)). Qed.
Lemma lem3567803 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3567805 {_91535 _91536 : Type'} (g : _91535 -> _91536) (y : _91535) (s : _91536 -> Prop) : (term242 _91535 _91536 g y s) = (term258 _91535 _91536 g y s).
Proof. exact (@lem3567803 (term129 _91535 _91536 g y s)). Qed.
Lemma lem3567808 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (y : _91535) (s : _91536 -> Prop) (h1 : term128 _91535 _91536 t g y s) : term258 _91535 _91536 g y s.
Proof. exact (EQ_MP (@lem3567805 _91535 _91536 g y s) (@lem3567602 _91535 _91536 t g y s h1)). Qed.
Lemma lem3567811 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (f : _91536 -> _91535) (t : _91535 -> Prop) (g : _91535 -> _91536) (y : _91535) (s : _91536 -> Prop) (h1 : term123 _91535 _91536 g' t s f g) (h2 : term128 _91535 _91536 t g y s) : False.
Proof. exact (@lem3567808 _91535 _91536 t g y s h2 (@lem3567800 _91535 _91536 g' f t g y s h1 h2)). Qed.
Lemma lem3567812 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (f : _91536 -> _91535) (t : _91535 -> Prop) (g : _91535 -> _91536) (y : _91535) (s : _91536 -> Prop) (h1 : term123 _91535 _91536 g' t s f g) (h2 : term128 _91535 _91536 t g y s) : term259.
Proof. exact (fun h0 : ~ False => @lem3567811 _91535 _91536 g' f t g y s h1 h2). Qed.
Lemma lem3567814 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3567815 : term259 = False.
Proof. exact (@lem3567814 False). Qed.
Lemma lem3567816 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (f : _91536 -> _91535) (t : _91535 -> Prop) (g : _91535 -> _91536) (y : _91535) (s : _91536 -> Prop) (h1 : term123 _91535 _91536 g' t s f g) (h2 : term128 _91535 _91536 t g y s) : False.
Proof. exact (EQ_MP (@lem3567815) (@lem3567812 _91535 _91536 g' f t g y s h1 h2)). Qed.
Lemma lem3567888 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term140 _91535 _91536 t f g y) : @IN _91535 y t.
Proof. exact (proj1 (@lem3567377 _91535 _91536 t f g y h1)). Qed.
Lemma lem3567889 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term140 _91535 _91536 t f g y) : term247 _91535 y t.
Proof. exact (fun h0 : term236 _91535 y t => @lem3567888 _91535 _91536 t f g y h1). Qed.
Lemma lem3567891 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3567892 {_91535 : Type'} (y : _91535) (t : _91535 -> Prop) : (term247 _91535 y t) = (@IN _91535 y t).
Proof. exact (@lem3567891 (@IN _91535 y t)). Qed.
Lemma lem3567893 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term140 _91535 _91536 t f g y) : @IN _91535 y t.
Proof. exact (EQ_MP (@lem3567892 _91535 y t) (@lem3567889 _91535 _91536 t f g y h1)). Qed.
Lemma lem3567899 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3567900 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) (_38284 : _91535) (t : _91535 -> Prop) : (term245 _91535 _91536 t f g _38284) = (term260 _91535 _91536 f g _38284 t).
Proof. exact (@lem3567899 ((term141 _91535 _91536 f g _38284) = _38284) (term236 _91535 _38284 t)). Qed.
Lemma lem3567908 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3567909 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) (_38284 : _91535) (t : _91535 -> Prop) : (term261 _91535 _91536 t f g _38284) = (term262 _91535 _91536 f g _38284 t).
Proof. exact (MK_COMB (@lem3567908) (@lem3567900 _91535 _91536 f g _38284 t)). Qed.
Lemma lem3567917 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) (_38284 : _91535) (t : _91535 -> Prop) : (term260 _91535 _91536 f g _38284 t) = (term260 _91535 _91536 f g _38284 t).
Proof. exact (eq_refl (term260 _91535 _91536 f g _38284 t)). Qed.
Lemma lem3567918 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) (_38284 : _91535) (t : _91535 -> Prop) : ((term245 _91535 _91536 t f g _38284) = (term260 _91535 _91536 f g _38284 t)) = ((term260 _91535 _91536 f g _38284 t) = (term260 _91535 _91536 f g _38284 t)).
Proof. exact (MK_COMB (@lem3567909 _91535 _91536 f g _38284 t) (@lem3567917 _91535 _91536 f g _38284 t)). Qed.
Lemma lem3567920 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3567921 (x : Prop) : (x = x) = True.
Proof. exact (@lem3567920 Prop x). Qed.
Lemma lem3567922 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) (_38284 : _91535) (t : _91535 -> Prop) : ((term260 _91535 _91536 f g _38284 t) = (term260 _91535 _91536 f g _38284 t)) = True.
Proof. exact (@lem3567921 (term260 _91535 _91536 f g _38284 t)). Qed.
Lemma lem3567923 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) (_38284 : _91535) (t : _91535 -> Prop) : ((term245 _91535 _91536 t f g _38284) = (term260 _91535 _91536 f g _38284 t)) = True.
Proof. exact (TRANS (@lem3567918 _91535 _91536 f g _38284 t) (@lem3567922 _91535 _91536 f g _38284 t)). Qed.
Lemma lem3567924 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) (_38284 : _91535) (t : _91535 -> Prop) : True = ((term245 _91535 _91536 t f g _38284) = (term260 _91535 _91536 f g _38284 t)).
Proof. exact (SYM (@lem3567923 _91535 _91536 f g _38284 t)). Qed.
Lemma lem3567925 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) (_38284 : _91535) (t : _91535 -> Prop) : (term245 _91535 _91536 t f g _38284) = (term260 _91535 _91536 f g _38284 t).
Proof. exact (EQ_MP (@lem3567924 _91535 _91536 f g _38284 t) (@lem0)). Qed.
Lemma lem3567926 {_91535 _91536 : Type'} (_38284 : _91535) (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term123 _91535 _91536 g' t s f g) : term260 _91535 _91536 f g _38284 t.
Proof. exact (EQ_MP (@lem3567925 _91535 _91536 f g _38284 t) (@lem3567642 _91535 _91536 _38284 g' t s f g h1)). Qed.
Lemma lem3567928 (b : Prop) (a : Prop) : (a \/ b) = (term252 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3567929 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (_38284 : _91535) : (term260 _91535 _91536 f g _38284 t) = (term263 _91535 _91536 t f g _38284).
Proof. exact (@lem3567928 (term236 _91535 _38284 t) ((term141 _91535 _91536 f g _38284) = _38284)). Qed.
Lemma lem3567931 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3567932 {_91535 : Type'} (_38284 : _91535) (t : _91535 -> Prop) : (term254 _91535 _38284 t) = (@IN _91535 _38284 t).
Proof. exact (@lem3567931 (@IN _91535 _38284 t)). Qed.
Lemma lem3567933 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3567934 {_91535 : Type'} (_38284 : _91535) (t : _91535 -> Prop) : (term255 _91535 _38284 t) = (term256 _91535 _38284 t).
Proof. exact (MK_COMB (@lem3567933) (@lem3567932 _91535 _38284 t)). Qed.
Lemma lem3567935 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) (_38284 : _91535) : ((term141 _91535 _91536 f g _38284) = _38284) = ((term141 _91535 _91536 f g _38284) = _38284).
Proof. exact (eq_refl ((term141 _91535 _91536 f g _38284) = _38284)). Qed.
Lemma lem3567936 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (_38284 : _91535) : (term263 _91535 _91536 t f g _38284) = (term74 _91535 _91536 t f g _38284).
Proof. exact (MK_COMB (@lem3567934 _91535 _38284 t) (@lem3567935 _91535 _91536 f g _38284)). Qed.
Lemma lem3567937 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (_38284 : _91535) : (term260 _91535 _91536 f g _38284 t) = (term74 _91535 _91536 t f g _38284).
Proof. exact (TRANS (@lem3567929 _91535 _91536 t f g _38284) (@lem3567936 _91535 _91536 t f g _38284)). Qed.
Lemma lem3567940 {_91535 _91536 : Type'} (_38284 : _91535) (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term123 _91535 _91536 g' t s f g) : term74 _91535 _91536 t f g _38284.
Proof. exact (EQ_MP (@lem3567937 _91535 _91536 t f g _38284) (@lem3567926 _91535 _91536 _38284 g' t s f g h1)). Qed.
Lemma lem3567941 {_91535 _91536 : Type'} (_38284 : _91535) (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term123 _91535 _91536 g' t s f g) : term74 _91535 _91536 t f g _38284.
Proof. exact (@lem3567940 _91535 _91536 _38284 g' t s f g h1). Qed.
Lemma lem3567942 {_91535 _91536 : Type'} (y : _91535) (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term123 _91535 _91536 g' t s f g) : term74 _91535 _91536 t f g y.
Proof. exact (@lem3567941 _91535 _91536 y g' t s f g h1). Qed.
Lemma lem3567945 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (s : _91536 -> Prop) (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term123 _91535 _91536 g' t s f g) (h2 : term140 _91535 _91536 t f g y) : (term141 _91535 _91536 f g y) = y.
Proof. exact (@lem3567942 _91535 _91536 y g' t s f g h1 (@lem3567893 _91535 _91536 t f g y h2)). Qed.
Lemma lem3567946 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (s : _91536 -> Prop) (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term123 _91535 _91536 g' t s f g) (h2 : term140 _91535 _91536 t f g y) : term264 _91535 _91536 f g y.
Proof. exact (fun h0 : term244 _91535 _91536 f g y => @lem3567945 _91535 _91536 g' s t f g y h1 h2). Qed.
Lemma lem3567948 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3567949 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : (term264 _91535 _91536 f g y) = ((term141 _91535 _91536 f g y) = y).
Proof. exact (@lem3567948 ((term141 _91535 _91536 f g y) = y)). Qed.
Lemma lem3567950 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (s : _91536 -> Prop) (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term123 _91535 _91536 g' t s f g) (h2 : term140 _91535 _91536 t f g y) : (term141 _91535 _91536 f g y) = y.
Proof. exact (EQ_MP (@lem3567949 _91535 _91536 f g y) (@lem3567946 _91535 _91536 g' s t f g y h1 h2)). Qed.
Lemma lem3567953 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3567955 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : (term244 _91535 _91536 f g y) = (term265 _91535 _91536 f g y).
Proof. exact (@lem3567953 ((term141 _91535 _91536 f g y) = y)). Qed.
Lemma lem3567958 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term140 _91535 _91536 t f g y) : term265 _91535 _91536 f g y.
Proof. exact (EQ_MP (@lem3567955 _91535 _91536 f g y) (@lem3567630 _91535 _91536 t f g y h1)). Qed.
Lemma lem3567961 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (s : _91536 -> Prop) (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term123 _91535 _91536 g' t s f g) (h2 : term140 _91535 _91536 t f g y) : False.
Proof. exact (@lem3567958 _91535 _91536 t f g y h2 (@lem3567950 _91535 _91536 g' s t f g y h1 h2)). Qed.
Lemma lem3567962 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (s : _91536 -> Prop) (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term123 _91535 _91536 g' t s f g) (h2 : term140 _91535 _91536 t f g y) : term259.
Proof. exact (fun h0 : ~ False => @lem3567961 _91535 _91536 g' s t f g y h1 h2). Qed.
Lemma lem3567964 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3567965 : term259 = False.
Proof. exact (@lem3567964 False). Qed.
Lemma lem3567966 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (s : _91536 -> Prop) (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term123 _91535 _91536 g' t s f g) (h2 : term140 _91535 _91536 t f g y) : False.
Proof. exact (EQ_MP (@lem3567965) (@lem3567962 _91535 _91536 g' s t f g y h1 h2)). Qed.
Lemma lem3568013 {_91535 _91536 : Type'} (g' : _91535 -> _91536) : g' = g'.
Proof. exact (eq_refl g'). Qed.
Lemma lem3568014 {_91535 : Type'} (_38326 : _91535) (_38327 : _91535) (h1 : _38326 = _38327) : _38326 = _38327.
Proof. exact (h1). Qed.
Lemma lem3568015 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (_38326 : _91535) (_38327 : _91535) (h1 : _38326 = _38327) : (g' _38326) = (g' _38327).
Proof. exact (MK_COMB (@lem3568013 _91535 _91536 g') (@lem3568014 _91535 _38326 _38327 h1)). Qed.
Lemma lem3568016 {_91535 _91536 : Type'} (_38326 : _91535) (g' : _91535 -> _91536) (_38327 : _91535) : term266 _91535 _91536 _38326 g' _38327.
Proof. exact (fun h0 : _38326 = _38327 => @lem3568015 _91535 _91536 g' _38326 _38327 h0). Qed.
Lemma lem3568018 (a : Prop) (b : Prop) : (a -> b) = (term267 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3568019 {_91535 _91536 : Type'} (_38326 : _91535) (g' : _91535 -> _91536) (_38327 : _91535) : (term266 _91535 _91536 _38326 g' _38327) = (term268 _91535 _91536 _38326 g' _38327).
Proof. exact (@lem3568018 (_38326 = _38327) ((g' _38326) = (g' _38327))). Qed.
Lemma lem3568020 {_91535 _91536 : Type'} (_38326 : _91535) (g' : _91535 -> _91536) (_38327 : _91535) : term268 _91535 _91536 _38326 g' _38327.
Proof. exact (EQ_MP (@lem3568019 _91535 _91536 _38326 g' _38327) (@lem3568016 _91535 _91536 _38326 g' _38327)). Qed.
Lemma lem3568030 {_91535 : Type'} (x : _91535) (y : _91535) (z : _91535) : term269 _91535 x y z.
Proof. exact (@lem21385 _91535 x y z). Qed.
Lemma lem3568032 {_91536 : Type'} (x : _91536) (y : _91536) (z : _91536) : term269 _91536 x y z.
Proof. exact (@lem21385 _91536 x y z). Qed.
Lemma lem3568038 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term150 _91535 _91536 s g f x) : @IN _91536 x s.
Proof. exact (proj1 (@lem3567378 _91535 _91536 s g f x h1)). Qed.
Lemma lem3568039 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term150 _91535 _91536 s g f x) : term247 _91536 x s.
Proof. exact (fun h0 : term236 _91536 x s => @lem3568038 _91535 _91536 s g f x h1). Qed.
Lemma lem3568041 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3568042 {_91536 : Type'} (x : _91536) (s : _91536 -> Prop) : (term247 _91536 x s) = (@IN _91536 x s).
Proof. exact (@lem3568041 (@IN _91536 x s)). Qed.
Lemma lem3568043 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term150 _91535 _91536 s g f x) : @IN _91536 x s.
Proof. exact (EQ_MP (@lem3568042 _91536 x s) (@lem3568039 _91535 _91536 s g f x h1)). Qed.
Lemma lem3568049 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3568050 {_91535 _91536 : Type'} (f : _91536 -> _91535) (t : _91535 -> Prop) (_38285 : _91536) (s : _91536 -> Prop) : (term92 _91535 _91536 s f _38285 t) = (term270 _91535 _91536 f t _38285 s).
Proof. exact (@lem3568049 (term93 _91535 _91536 f _38285 t) (term236 _91536 _38285 s)). Qed.
Lemma lem3568056 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3568057 {_91535 _91536 : Type'} (f : _91536 -> _91535) (t : _91535 -> Prop) (_38285 : _91536) (s : _91536 -> Prop) : (term271 _91535 _91536 s f _38285 t) = (term272 _91535 _91536 f t _38285 s).
Proof. exact (MK_COMB (@lem3568056) (@lem3568050 _91535 _91536 f t _38285 s)). Qed.
Lemma lem3568063 {_91535 _91536 : Type'} (f : _91536 -> _91535) (t : _91535 -> Prop) (_38285 : _91536) (s : _91536 -> Prop) : (term270 _91535 _91536 f t _38285 s) = (term270 _91535 _91536 f t _38285 s).
Proof. exact (eq_refl (term270 _91535 _91536 f t _38285 s)). Qed.
Lemma lem3568064 {_91535 _91536 : Type'} (f : _91536 -> _91535) (t : _91535 -> Prop) (_38285 : _91536) (s : _91536 -> Prop) : ((term92 _91535 _91536 s f _38285 t) = (term270 _91535 _91536 f t _38285 s)) = ((term270 _91535 _91536 f t _38285 s) = (term270 _91535 _91536 f t _38285 s)).
Proof. exact (MK_COMB (@lem3568057 _91535 _91536 f t _38285 s) (@lem3568063 _91535 _91536 f t _38285 s)). Qed.
Lemma lem3568066 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3568067 (x : Prop) : (x = x) = True.
Proof. exact (@lem3568066 Prop x). Qed.
Lemma lem3568068 {_91535 _91536 : Type'} (f : _91536 -> _91535) (t : _91535 -> Prop) (_38285 : _91536) (s : _91536 -> Prop) : ((term270 _91535 _91536 f t _38285 s) = (term270 _91535 _91536 f t _38285 s)) = True.
Proof. exact (@lem3568067 (term270 _91535 _91536 f t _38285 s)). Qed.
Lemma lem3568069 {_91535 _91536 : Type'} (f : _91536 -> _91535) (t : _91535 -> Prop) (_38285 : _91536) (s : _91536 -> Prop) : ((term92 _91535 _91536 s f _38285 t) = (term270 _91535 _91536 f t _38285 s)) = True.
Proof. exact (TRANS (@lem3568064 _91535 _91536 f t _38285 s) (@lem3568068 _91535 _91536 f t _38285 s)). Qed.
Lemma lem3568070 {_91535 _91536 : Type'} (f : _91536 -> _91535) (t : _91535 -> Prop) (_38285 : _91536) (s : _91536 -> Prop) : True = ((term92 _91535 _91536 s f _38285 t) = (term270 _91535 _91536 f t _38285 s)).
Proof. exact (SYM (@lem3568069 _91535 _91536 f t _38285 s)). Qed.
Lemma lem3568071 {_91535 _91536 : Type'} (f : _91536 -> _91535) (t : _91535 -> Prop) (_38285 : _91536) (s : _91536 -> Prop) : (term92 _91535 _91536 s f _38285 t) = (term270 _91535 _91536 f t _38285 s).
Proof. exact (EQ_MP (@lem3568070 _91535 _91536 f t _38285 s) (@lem0)). Qed.
Lemma lem3568072 {_91535 _91536 : Type'} (_38285 : _91536) (s : _91536 -> Prop) (f : _91536 -> _91535) (t : _91535 -> Prop) (h1 : term15 _91535 _91536 s f t) : term270 _91535 _91536 f t _38285 s.
Proof. exact (EQ_MP (@lem3568071 _91535 _91536 f t _38285 s) (@lem3567648 _91535 _91536 _38285 s f t h1)). Qed.
Lemma lem3568074 (b : Prop) (a : Prop) : (a \/ b) = (term252 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3568075 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (_38285 : _91536) (t : _91535 -> Prop) : (term270 _91535 _91536 f t _38285 s) = (term273 _91535 _91536 s f _38285 t).
Proof. exact (@lem3568074 (term236 _91536 _38285 s) (term93 _91535 _91536 f _38285 t)). Qed.
Lemma lem3568077 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3568078 {_91536 : Type'} (_38285 : _91536) (s : _91536 -> Prop) : (term254 _91536 _38285 s) = (@IN _91536 _38285 s).
Proof. exact (@lem3568077 (@IN _91536 _38285 s)). Qed.
Lemma lem3568079 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3568080 {_91536 : Type'} (_38285 : _91536) (s : _91536 -> Prop) : (term255 _91536 _38285 s) = (term256 _91536 _38285 s).
Proof. exact (MK_COMB (@lem3568079) (@lem3568078 _91536 _38285 s)). Qed.
Lemma lem3568081 {_91535 _91536 : Type'} (f : _91536 -> _91535) (_38285 : _91536) (t : _91535 -> Prop) : (term93 _91535 _91536 f _38285 t) = (term93 _91535 _91536 f _38285 t).
Proof. exact (eq_refl (term93 _91535 _91536 f _38285 t)). Qed.
Lemma lem3568082 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (_38285 : _91536) (t : _91535 -> Prop) : (term273 _91535 _91536 s f _38285 t) = (term88 _91535 _91536 s f _38285 t).
Proof. exact (MK_COMB (@lem3568080 _91536 _38285 s) (@lem3568081 _91535 _91536 f _38285 t)). Qed.
Lemma lem3568083 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (_38285 : _91536) (t : _91535 -> Prop) : (term270 _91535 _91536 f t _38285 s) = (term88 _91535 _91536 s f _38285 t).
Proof. exact (TRANS (@lem3568075 _91535 _91536 s f _38285 t) (@lem3568082 _91535 _91536 s f _38285 t)). Qed.
Lemma lem3568086 {_91535 _91536 : Type'} (_38285 : _91536) (s : _91536 -> Prop) (f : _91536 -> _91535) (t : _91535 -> Prop) (h1 : term15 _91535 _91536 s f t) : term88 _91535 _91536 s f _38285 t.
Proof. exact (EQ_MP (@lem3568083 _91535 _91536 s f _38285 t) (@lem3568072 _91535 _91536 _38285 s f t h1)). Qed.
Lemma lem3568087 {_91535 _91536 : Type'} (_38285 : _91536) (s : _91536 -> Prop) (f : _91536 -> _91535) (t : _91535 -> Prop) (h1 : term15 _91535 _91536 s f t) : term88 _91535 _91536 s f _38285 t.
Proof. exact (@lem3568086 _91535 _91536 _38285 s f t h1). Qed.
Lemma lem3568088 {_91535 _91536 : Type'} (x : _91536) (s : _91536 -> Prop) (f : _91536 -> _91535) (t : _91535 -> Prop) (h1 : term15 _91535 _91536 s f t) : term88 _91535 _91536 s f x t.
Proof. exact (@lem3568087 _91535 _91536 x s f t h1). Qed.
Lemma lem3568091 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term150 _91535 _91536 s g f x) : term93 _91535 _91536 f x t.
Proof. exact (@lem3568088 _91535 _91536 x s f t h1 (@lem3568043 _91535 _91536 s g f x h2)). Qed.
Lemma lem3568092 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term150 _91535 _91536 s g f x) : term274 _91535 _91536 f x t.
Proof. exact (fun h0 : term275 _91535 _91536 f x t => @lem3568091 _91535 _91536 t s g f x h1 h2). Qed.
Lemma lem3568094 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3568095 {_91535 _91536 : Type'} (f : _91536 -> _91535) (x : _91536) (t : _91535 -> Prop) : (term274 _91535 _91536 f x t) = (term93 _91535 _91536 f x t).
Proof. exact (@lem3568094 (term93 _91535 _91536 f x t)). Qed.
Lemma lem3568096 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term150 _91535 _91536 s g f x) : term93 _91535 _91536 f x t.
Proof. exact (EQ_MP (@lem3568095 _91535 _91536 f x t) (@lem3568092 _91535 _91536 t s g f x h1 h2)). Qed.
Lemma lem3568102 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3568103 {_91535 _91536 : Type'} (g : _91535 -> _91536) (s : _91536 -> Prop) (_38287 : _91535) (t : _91535 -> Prop) : (term243 _91535 _91536 t g _38287 s) = (term249 _91535 _91536 g s _38287 t).
Proof. exact (@lem3568102 (term129 _91535 _91536 g _38287 s) (term236 _91535 _38287 t)). Qed.
Lemma lem3568109 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3568110 {_91535 _91536 : Type'} (g : _91535 -> _91536) (s : _91536 -> Prop) (_38287 : _91535) (t : _91535 -> Prop) : (term250 _91535 _91536 t g _38287 s) = (term251 _91535 _91536 g s _38287 t).
Proof. exact (MK_COMB (@lem3568109) (@lem3568103 _91535 _91536 g s _38287 t)). Qed.
Lemma lem3568116 {_91535 _91536 : Type'} (g : _91535 -> _91536) (s : _91536 -> Prop) (_38287 : _91535) (t : _91535 -> Prop) : (term249 _91535 _91536 g s _38287 t) = (term249 _91535 _91536 g s _38287 t).
Proof. exact (eq_refl (term249 _91535 _91536 g s _38287 t)). Qed.
Lemma lem3568117 {_91535 _91536 : Type'} (g : _91535 -> _91536) (s : _91536 -> Prop) (_38287 : _91535) (t : _91535 -> Prop) : ((term243 _91535 _91536 t g _38287 s) = (term249 _91535 _91536 g s _38287 t)) = ((term249 _91535 _91536 g s _38287 t) = (term249 _91535 _91536 g s _38287 t)).
Proof. exact (MK_COMB (@lem3568110 _91535 _91536 g s _38287 t) (@lem3568116 _91535 _91536 g s _38287 t)). Qed.
Lemma lem3568119 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3568120 (x : Prop) : (x = x) = True.
Proof. exact (@lem3568119 Prop x). Qed.
Lemma lem3568121 {_91535 _91536 : Type'} (g : _91535 -> _91536) (s : _91536 -> Prop) (_38287 : _91535) (t : _91535 -> Prop) : ((term249 _91535 _91536 g s _38287 t) = (term249 _91535 _91536 g s _38287 t)) = True.
Proof. exact (@lem3568120 (term249 _91535 _91536 g s _38287 t)). Qed.
Lemma lem3568122 {_91535 _91536 : Type'} (g : _91535 -> _91536) (s : _91536 -> Prop) (_38287 : _91535) (t : _91535 -> Prop) : ((term243 _91535 _91536 t g _38287 s) = (term249 _91535 _91536 g s _38287 t)) = True.
Proof. exact (TRANS (@lem3568117 _91535 _91536 g s _38287 t) (@lem3568121 _91535 _91536 g s _38287 t)). Qed.
Lemma lem3568123 {_91535 _91536 : Type'} (g : _91535 -> _91536) (s : _91536 -> Prop) (_38287 : _91535) (t : _91535 -> Prop) : True = ((term243 _91535 _91536 t g _38287 s) = (term249 _91535 _91536 g s _38287 t)).
Proof. exact (SYM (@lem3568122 _91535 _91536 g s _38287 t)). Qed.
Lemma lem3568124 {_91535 _91536 : Type'} (g : _91535 -> _91536) (s : _91536 -> Prop) (_38287 : _91535) (t : _91535 -> Prop) : (term243 _91535 _91536 t g _38287 s) = (term249 _91535 _91536 g s _38287 t).
Proof. exact (EQ_MP (@lem3568123 _91535 _91536 g s _38287 t) (@lem0)). Qed.
Lemma lem3568125 {_91535 _91536 : Type'} (_38287 : _91535) (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term123 _91535 _91536 g' t s f g) : term249 _91535 _91536 g s _38287 t.
Proof. exact (EQ_MP (@lem3568124 _91535 _91536 g s _38287 t) (@lem3567664 _91535 _91536 _38287 g' t s f g h1)). Qed.
Lemma lem3568127 (b : Prop) (a : Prop) : (a \/ b) = (term252 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3568128 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (_38287 : _91535) (s : _91536 -> Prop) : (term249 _91535 _91536 g s _38287 t) = (term253 _91535 _91536 t g _38287 s).
Proof. exact (@lem3568127 (term236 _91535 _38287 t) (term129 _91535 _91536 g _38287 s)). Qed.
Lemma lem3568130 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3568131 {_91535 : Type'} (_38287 : _91535) (t : _91535 -> Prop) : (term254 _91535 _38287 t) = (@IN _91535 _38287 t).
Proof. exact (@lem3568130 (@IN _91535 _38287 t)). Qed.
Lemma lem3568132 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3568133 {_91535 : Type'} (_38287 : _91535) (t : _91535 -> Prop) : (term255 _91535 _38287 t) = (term256 _91535 _38287 t).
Proof. exact (MK_COMB (@lem3568132) (@lem3568131 _91535 _38287 t)). Qed.
Lemma lem3568134 {_91535 _91536 : Type'} (g : _91535 -> _91536) (_38287 : _91535) (s : _91536 -> Prop) : (term129 _91535 _91536 g _38287 s) = (term129 _91535 _91536 g _38287 s).
Proof. exact (eq_refl (term129 _91535 _91536 g _38287 s)). Qed.
Lemma lem3568135 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (_38287 : _91535) (s : _91536 -> Prop) : (term253 _91535 _91536 t g _38287 s) = (term79 _91535 _91536 t g _38287 s).
Proof. exact (MK_COMB (@lem3568133 _91535 _38287 t) (@lem3568134 _91535 _91536 g _38287 s)). Qed.
Lemma lem3568136 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (_38287 : _91535) (s : _91536 -> Prop) : (term249 _91535 _91536 g s _38287 t) = (term79 _91535 _91536 t g _38287 s).
Proof. exact (TRANS (@lem3568128 _91535 _91536 t g _38287 s) (@lem3568135 _91535 _91536 t g _38287 s)). Qed.
Lemma lem3568139 {_91535 _91536 : Type'} (_38287 : _91535) (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term123 _91535 _91536 g' t s f g) : term79 _91535 _91536 t g _38287 s.
Proof. exact (EQ_MP (@lem3568136 _91535 _91536 t g _38287 s) (@lem3568125 _91535 _91536 _38287 g' t s f g h1)). Qed.
Lemma lem3568140 {_91535 _91536 : Type'} (_38287 : _91535) (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term123 _91535 _91536 g' t s f g) : term79 _91535 _91536 t g _38287 s.
Proof. exact (@lem3568139 _91535 _91536 _38287 g' t s f g h1). Qed.
Lemma lem3568141 {_91535 _91536 : Type'} (x : _91536) (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term123 _91535 _91536 g' t s f g) : term276 _91535 _91536 t g f x s.
Proof. exact (@lem3568140 _91535 _91536 (f x) g' t s f g h1). Qed.
Lemma lem3568144 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term123 _91535 _91536 g' t s f g) (h3 : term150 _91535 _91536 s g f x) : term277 _91535 _91536 g f x s.
Proof. exact (@lem3568141 _91535 _91536 x g' t s f g h2 (@lem3568096 _91535 _91536 t s g f x h1 h3)). Qed.
Lemma lem3568145 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term123 _91535 _91536 g' t s f g) (h3 : term150 _91535 _91536 s g f x) : term278 _91535 _91536 g f x s.
Proof. exact (fun h0 : term279 _91535 _91536 g f x s => @lem3568144 _91535 _91536 g' t s g f x h1 h2 h3). Qed.
Lemma lem3568147 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3568148 {_91535 _91536 : Type'} (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (s : _91536 -> Prop) : (term278 _91535 _91536 g f x s) = (term277 _91535 _91536 g f x s).
Proof. exact (@lem3568147 (term277 _91535 _91536 g f x s)). Qed.
Lemma lem3568149 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term123 _91535 _91536 g' t s f g) (h3 : term150 _91535 _91536 s g f x) : term277 _91535 _91536 g f x s.
Proof. exact (EQ_MP (@lem3568148 _91535 _91536 g f x s) (@lem3568145 _91535 _91536 g' t s g f x h1 h2 h3)). Qed.
Lemma lem3568155 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3568156 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (f : _91536 -> _91535) (_38286 : _91536) (s : _91536 -> Prop) : (term96 _91535 _91536 s g' f _38286) = (term280 _91535 _91536 g' f _38286 s).
Proof. exact (@lem3568155 ((term97 _91535 _91536 g' f _38286) = _38286) (term236 _91536 _38286 s)). Qed.
Lemma lem3568164 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3568165 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (f : _91536 -> _91535) (_38286 : _91536) (s : _91536 -> Prop) : (term281 _91535 _91536 s g' f _38286) = (term282 _91535 _91536 g' f _38286 s).
Proof. exact (MK_COMB (@lem3568164) (@lem3568156 _91535 _91536 g' f _38286 s)). Qed.
Lemma lem3568173 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (f : _91536 -> _91535) (_38286 : _91536) (s : _91536 -> Prop) : (term280 _91535 _91536 g' f _38286 s) = (term280 _91535 _91536 g' f _38286 s).
Proof. exact (eq_refl (term280 _91535 _91536 g' f _38286 s)). Qed.
Lemma lem3568174 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (f : _91536 -> _91535) (_38286 : _91536) (s : _91536 -> Prop) : ((term96 _91535 _91536 s g' f _38286) = (term280 _91535 _91536 g' f _38286 s)) = ((term280 _91535 _91536 g' f _38286 s) = (term280 _91535 _91536 g' f _38286 s)).
Proof. exact (MK_COMB (@lem3568165 _91535 _91536 g' f _38286 s) (@lem3568173 _91535 _91536 g' f _38286 s)). Qed.
Lemma lem3568176 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3568177 (x : Prop) : (x = x) = True.
Proof. exact (@lem3568176 Prop x). Qed.
Lemma lem3568178 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (f : _91536 -> _91535) (_38286 : _91536) (s : _91536 -> Prop) : ((term280 _91535 _91536 g' f _38286 s) = (term280 _91535 _91536 g' f _38286 s)) = True.
Proof. exact (@lem3568177 (term280 _91535 _91536 g' f _38286 s)). Qed.
Lemma lem3568179 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (f : _91536 -> _91535) (_38286 : _91536) (s : _91536 -> Prop) : ((term96 _91535 _91536 s g' f _38286) = (term280 _91535 _91536 g' f _38286 s)) = True.
Proof. exact (TRANS (@lem3568174 _91535 _91536 g' f _38286 s) (@lem3568178 _91535 _91536 g' f _38286 s)). Qed.
Lemma lem3568180 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (f : _91536 -> _91535) (_38286 : _91536) (s : _91536 -> Prop) : True = ((term96 _91535 _91536 s g' f _38286) = (term280 _91535 _91536 g' f _38286 s)).
Proof. exact (SYM (@lem3568179 _91535 _91536 g' f _38286 s)). Qed.
Lemma lem3568181 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (f : _91536 -> _91535) (_38286 : _91536) (s : _91536 -> Prop) : (term96 _91535 _91536 s g' f _38286) = (term280 _91535 _91536 g' f _38286 s).
Proof. exact (EQ_MP (@lem3568180 _91535 _91536 g' f _38286 s) (@lem0)). Qed.
Lemma lem3568182 {_91535 _91536 : Type'} (_38286 : _91536) (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term123 _91535 _91536 g' t s f g) : term280 _91535 _91536 g' f _38286 s.
Proof. exact (EQ_MP (@lem3568181 _91535 _91536 g' f _38286 s) (@lem3567654 _91535 _91536 _38286 g' t s f g h1)). Qed.
Lemma lem3568184 (b : Prop) (a : Prop) : (a \/ b) = (term252 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3568185 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g' : _91535 -> _91536) (f : _91536 -> _91535) (_38286 : _91536) : (term280 _91535 _91536 g' f _38286 s) = (term283 _91535 _91536 s g' f _38286).
Proof. exact (@lem3568184 (term236 _91536 _38286 s) ((term97 _91535 _91536 g' f _38286) = _38286)). Qed.
Lemma lem3568187 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3568188 {_91536 : Type'} (_38286 : _91536) (s : _91536 -> Prop) : (term254 _91536 _38286 s) = (@IN _91536 _38286 s).
Proof. exact (@lem3568187 (@IN _91536 _38286 s)). Qed.
Lemma lem3568189 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3568190 {_91536 : Type'} (_38286 : _91536) (s : _91536 -> Prop) : (term255 _91536 _38286 s) = (term256 _91536 _38286 s).
Proof. exact (MK_COMB (@lem3568189) (@lem3568188 _91536 _38286 s)). Qed.
Lemma lem3568191 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (f : _91536 -> _91535) (_38286 : _91536) : ((term97 _91535 _91536 g' f _38286) = _38286) = ((term97 _91535 _91536 g' f _38286) = _38286).
Proof. exact (eq_refl ((term97 _91535 _91536 g' f _38286) = _38286)). Qed.
Lemma lem3568192 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g' : _91535 -> _91536) (f : _91536 -> _91535) (_38286 : _91536) : (term283 _91535 _91536 s g' f _38286) = (term71 _91535 _91536 s g' f _38286).
Proof. exact (MK_COMB (@lem3568190 _91536 _38286 s) (@lem3568191 _91535 _91536 g' f _38286)). Qed.
Lemma lem3568193 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g' : _91535 -> _91536) (f : _91536 -> _91535) (_38286 : _91536) : (term280 _91535 _91536 g' f _38286 s) = (term71 _91535 _91536 s g' f _38286).
Proof. exact (TRANS (@lem3568185 _91535 _91536 s g' f _38286) (@lem3568192 _91535 _91536 s g' f _38286)). Qed.
Lemma lem3568196 {_91535 _91536 : Type'} (_38286 : _91536) (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term123 _91535 _91536 g' t s f g) : term71 _91535 _91536 s g' f _38286.
Proof. exact (EQ_MP (@lem3568193 _91535 _91536 s g' f _38286) (@lem3568182 _91535 _91536 _38286 g' t s f g h1)). Qed.
Lemma lem3568197 {_91535 _91536 : Type'} (_38286 : _91536) (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term123 _91535 _91536 g' t s f g) : term71 _91535 _91536 s g' f _38286.
Proof. exact (@lem3568196 _91535 _91536 _38286 g' t s f g h1). Qed.
Lemma lem3568198 {_91535 _91536 : Type'} (x : _91536) (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term123 _91535 _91536 g' t s f g) : term284 _91535 _91536 s g' g f x.
Proof. exact (@lem3568197 _91535 _91536 (term97 _91535 _91536 g f x) g' t s f g h1). Qed.
Lemma lem3568201 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term123 _91535 _91536 g' t s f g) (h3 : term150 _91535 _91536 s g f x) : (term285 _91535 _91536 g' g f x) = (term97 _91535 _91536 g f x).
Proof. exact (@lem3568198 _91535 _91536 x g' t s f g h2 (@lem3568149 _91535 _91536 g' t s g f x h1 h2 h3)). Qed.
Lemma lem3568202 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term123 _91535 _91536 g' t s f g) (h3 : term150 _91535 _91536 s g f x) : term286 _91535 _91536 g' g f x.
Proof. exact (fun h0 : term287 _91535 _91536 g' g f x => @lem3568201 _91535 _91536 g' t s g f x h1 h2 h3). Qed.
Lemma lem3568204 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3568205 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : (term286 _91535 _91536 g' g f x) = ((term285 _91535 _91536 g' g f x) = (term97 _91535 _91536 g f x)).
Proof. exact (@lem3568204 ((term285 _91535 _91536 g' g f x) = (term97 _91535 _91536 g f x))). Qed.
Lemma lem3568206 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term123 _91535 _91536 g' t s f g) (h3 : term150 _91535 _91536 s g f x) : (term285 _91535 _91536 g' g f x) = (term97 _91535 _91536 g f x).
Proof. exact (EQ_MP (@lem3568205 _91535 _91536 g' g f x) (@lem3568202 _91535 _91536 g' t s g f x h1 h2 h3)). Qed.
Lemma lem3568208 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term150 _91535 _91536 s g f x) : @IN _91536 x s.
Proof. exact (proj1 (@lem3567378 _91535 _91536 s g f x h1)). Qed.
Lemma lem3568209 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term150 _91535 _91536 s g f x) : term247 _91536 x s.
Proof. exact (fun h0 : term236 _91536 x s => @lem3568208 _91535 _91536 s g f x h1). Qed.
Lemma lem3568211 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3568212 {_91536 : Type'} (x : _91536) (s : _91536 -> Prop) : (term247 _91536 x s) = (@IN _91536 x s).
Proof. exact (@lem3568211 (@IN _91536 x s)). Qed.
Lemma lem3568213 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term150 _91535 _91536 s g f x) : @IN _91536 x s.
Proof. exact (EQ_MP (@lem3568212 _91536 x s) (@lem3568209 _91535 _91536 s g f x h1)). Qed.
Lemma lem3568215 {_91535 _91536 : Type'} (_38285 : _91536) (s : _91536 -> Prop) (f : _91536 -> _91535) (t : _91535 -> Prop) (h1 : term15 _91535 _91536 s f t) : term88 _91535 _91536 s f _38285 t.
Proof. exact (EQ_MP (@lem3568083 _91535 _91536 s f _38285 t) (@lem3568072 _91535 _91536 _38285 s f t h1)). Qed.
Lemma lem3568216 {_91535 _91536 : Type'} (_38285 : _91536) (s : _91536 -> Prop) (f : _91536 -> _91535) (t : _91535 -> Prop) (h1 : term15 _91535 _91536 s f t) : term88 _91535 _91536 s f _38285 t.
Proof. exact (@lem3568215 _91535 _91536 _38285 s f t h1). Qed.
Lemma lem3568217 {_91535 _91536 : Type'} (x : _91536) (s : _91536 -> Prop) (f : _91536 -> _91535) (t : _91535 -> Prop) (h1 : term15 _91535 _91536 s f t) : term88 _91535 _91536 s f x t.
Proof. exact (@lem3568216 _91535 _91536 x s f t h1). Qed.
Lemma lem3568220 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term150 _91535 _91536 s g f x) : term93 _91535 _91536 f x t.
Proof. exact (@lem3568217 _91535 _91536 x s f t h1 (@lem3568213 _91535 _91536 s g f x h2)). Qed.
Lemma lem3568221 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term150 _91535 _91536 s g f x) : term274 _91535 _91536 f x t.
Proof. exact (fun h0 : term275 _91535 _91536 f x t => @lem3568220 _91535 _91536 t s g f x h1 h2). Qed.
Lemma lem3568223 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3568224 {_91535 _91536 : Type'} (f : _91536 -> _91535) (x : _91536) (t : _91535 -> Prop) : (term274 _91535 _91536 f x t) = (term93 _91535 _91536 f x t).
Proof. exact (@lem3568223 (term93 _91535 _91536 f x t)). Qed.
Lemma lem3568225 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term150 _91535 _91536 s g f x) : term93 _91535 _91536 f x t.
Proof. exact (EQ_MP (@lem3568224 _91535 _91536 f x t) (@lem3568221 _91535 _91536 t s g f x h1 h2)). Qed.
Lemma lem3568231 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3568232 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) (_38287 : _91535) (t : _91535 -> Prop) : (term245 _91535 _91536 t f g _38287) = (term260 _91535 _91536 f g _38287 t).
Proof. exact (@lem3568231 ((term141 _91535 _91536 f g _38287) = _38287) (term236 _91535 _38287 t)). Qed.
Lemma lem3568240 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3568241 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) (_38287 : _91535) (t : _91535 -> Prop) : (term261 _91535 _91536 t f g _38287) = (term262 _91535 _91536 f g _38287 t).
Proof. exact (MK_COMB (@lem3568240) (@lem3568232 _91535 _91536 f g _38287 t)). Qed.
Lemma lem3568249 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) (_38287 : _91535) (t : _91535 -> Prop) : (term260 _91535 _91536 f g _38287 t) = (term260 _91535 _91536 f g _38287 t).
Proof. exact (eq_refl (term260 _91535 _91536 f g _38287 t)). Qed.
Lemma lem3568250 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) (_38287 : _91535) (t : _91535 -> Prop) : ((term245 _91535 _91536 t f g _38287) = (term260 _91535 _91536 f g _38287 t)) = ((term260 _91535 _91536 f g _38287 t) = (term260 _91535 _91536 f g _38287 t)).
Proof. exact (MK_COMB (@lem3568241 _91535 _91536 f g _38287 t) (@lem3568249 _91535 _91536 f g _38287 t)). Qed.
Lemma lem3568252 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3568253 (x : Prop) : (x = x) = True.
Proof. exact (@lem3568252 Prop x). Qed.
Lemma lem3568254 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) (_38287 : _91535) (t : _91535 -> Prop) : ((term260 _91535 _91536 f g _38287 t) = (term260 _91535 _91536 f g _38287 t)) = True.
Proof. exact (@lem3568253 (term260 _91535 _91536 f g _38287 t)). Qed.
Lemma lem3568255 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) (_38287 : _91535) (t : _91535 -> Prop) : ((term245 _91535 _91536 t f g _38287) = (term260 _91535 _91536 f g _38287 t)) = True.
Proof. exact (TRANS (@lem3568250 _91535 _91536 f g _38287 t) (@lem3568254 _91535 _91536 f g _38287 t)). Qed.
Lemma lem3568256 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) (_38287 : _91535) (t : _91535 -> Prop) : True = ((term245 _91535 _91536 t f g _38287) = (term260 _91535 _91536 f g _38287 t)).
Proof. exact (SYM (@lem3568255 _91535 _91536 f g _38287 t)). Qed.
Lemma lem3568257 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) (_38287 : _91535) (t : _91535 -> Prop) : (term245 _91535 _91536 t f g _38287) = (term260 _91535 _91536 f g _38287 t).
Proof. exact (EQ_MP (@lem3568256 _91535 _91536 f g _38287 t) (@lem0)). Qed.
Lemma lem3568258 {_91535 _91536 : Type'} (_38287 : _91535) (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term123 _91535 _91536 g' t s f g) : term260 _91535 _91536 f g _38287 t.
Proof. exact (EQ_MP (@lem3568257 _91535 _91536 f g _38287 t) (@lem3567670 _91535 _91536 _38287 g' t s f g h1)). Qed.
Lemma lem3568260 (b : Prop) (a : Prop) : (a \/ b) = (term252 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3568261 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (_38287 : _91535) : (term260 _91535 _91536 f g _38287 t) = (term263 _91535 _91536 t f g _38287).
Proof. exact (@lem3568260 (term236 _91535 _38287 t) ((term141 _91535 _91536 f g _38287) = _38287)). Qed.
Lemma lem3568263 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3568264 {_91535 : Type'} (_38287 : _91535) (t : _91535 -> Prop) : (term254 _91535 _38287 t) = (@IN _91535 _38287 t).
Proof. exact (@lem3568263 (@IN _91535 _38287 t)). Qed.
Lemma lem3568265 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3568266 {_91535 : Type'} (_38287 : _91535) (t : _91535 -> Prop) : (term255 _91535 _38287 t) = (term256 _91535 _38287 t).
Proof. exact (MK_COMB (@lem3568265) (@lem3568264 _91535 _38287 t)). Qed.
Lemma lem3568267 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) (_38287 : _91535) : ((term141 _91535 _91536 f g _38287) = _38287) = ((term141 _91535 _91536 f g _38287) = _38287).
Proof. exact (eq_refl ((term141 _91535 _91536 f g _38287) = _38287)). Qed.
Lemma lem3568268 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (_38287 : _91535) : (term263 _91535 _91536 t f g _38287) = (term74 _91535 _91536 t f g _38287).
Proof. exact (MK_COMB (@lem3568266 _91535 _38287 t) (@lem3568267 _91535 _91536 f g _38287)). Qed.
Lemma lem3568269 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (_38287 : _91535) : (term260 _91535 _91536 f g _38287 t) = (term74 _91535 _91536 t f g _38287).
Proof. exact (TRANS (@lem3568261 _91535 _91536 t f g _38287) (@lem3568268 _91535 _91536 t f g _38287)). Qed.
Lemma lem3568272 {_91535 _91536 : Type'} (_38287 : _91535) (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term123 _91535 _91536 g' t s f g) : term74 _91535 _91536 t f g _38287.
Proof. exact (EQ_MP (@lem3568269 _91535 _91536 t f g _38287) (@lem3568258 _91535 _91536 _38287 g' t s f g h1)). Qed.
Lemma lem3568273 {_91535 _91536 : Type'} (_38287 : _91535) (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term123 _91535 _91536 g' t s f g) : term74 _91535 _91536 t f g _38287.
Proof. exact (@lem3568272 _91535 _91536 _38287 g' t s f g h1). Qed.
Lemma lem3568274 {_91535 _91536 : Type'} (x : _91536) (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term123 _91535 _91536 g' t s f g) : term288 _91535 _91536 t g f x.
Proof. exact (@lem3568273 _91535 _91536 (f x) g' t s f g h1). Qed.
Lemma lem3568277 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term123 _91535 _91536 g' t s f g) (h3 : term150 _91535 _91536 s g f x) : (term289 _91535 _91536 g f x) = (f x).
Proof. exact (@lem3568274 _91535 _91536 x g' t s f g h2 (@lem3568225 _91535 _91536 t s g f x h1 h3)). Qed.
Lemma lem3568278 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term123 _91535 _91536 g' t s f g) (h3 : term150 _91535 _91536 s g f x) : term290 _91535 _91536 g f x.
Proof. exact (fun h0 : term291 _91535 _91536 g f x => @lem3568277 _91535 _91536 g' t s g f x h1 h2 h3). Qed.
Lemma lem3568280 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3568281 {_91535 _91536 : Type'} (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : (term290 _91535 _91536 g f x) = ((term289 _91535 _91536 g f x) = (f x)).
Proof. exact (@lem3568280 ((term289 _91535 _91536 g f x) = (f x))). Qed.
Lemma lem3568282 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term123 _91535 _91536 g' t s f g) (h3 : term150 _91535 _91536 s g f x) : (term289 _91535 _91536 g f x) = (f x).
Proof. exact (EQ_MP (@lem3568281 _91535 _91536 g f x) (@lem3568278 _91535 _91536 g' t s g f x h1 h2 h3)). Qed.
Lemma lem3568284 {_91535 : Type'} (x : _91535) : x = x.
Proof. exact (@lem21386 _91535 x). Qed.
Lemma lem3568285 {_91535 : Type'} (x : _91535) : x = x.
Proof. exact (@lem3568284 _91535 x). Qed.
Lemma lem3568286 {_91535 _91536 : Type'} (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : (term289 _91535 _91536 g f x) = (term289 _91535 _91536 g f x).
Proof. exact (@lem3568285 _91535 (term289 _91535 _91536 g f x)). Qed.
Lemma lem3568287 {_91535 _91536 : Type'} (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : term292 _91535 _91536 g f x.
Proof. exact (fun h0 : term293 _91535 _91536 g f x => @lem3568286 _91535 _91536 g f x). Qed.
Lemma lem3568289 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3568290 {_91535 _91536 : Type'} (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : (term292 _91535 _91536 g f x) = ((term289 _91535 _91536 g f x) = (term289 _91535 _91536 g f x)).
Proof. exact (@lem3568289 ((term289 _91535 _91536 g f x) = (term289 _91535 _91536 g f x))). Qed.
Lemma lem3568291 {_91535 _91536 : Type'} (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : (term289 _91535 _91536 g f x) = (term289 _91535 _91536 g f x).
Proof. exact (EQ_MP (@lem3568290 _91535 _91536 g f x) (@lem3568287 _91535 _91536 g f x)). Qed.
Lemma lem3568309 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3568310 {_91535 : Type'} (y : _91535) (x : _91535) (z : _91535) : (term294 _91535 x y z) = (term295 _91535 y x z).
Proof. exact (@lem3568309 (y = z) (term296 _91535 x z)). Qed.
Lemma lem3568320 {_91535 : Type'} (x : _91535) (y : _91535) : (term297 _91535 x y) = (term297 _91535 x y).
Proof. exact (eq_refl (term297 _91535 x y)). Qed.
Lemma lem3568321 {_91535 : Type'} (y : _91535) (x : _91535) (z : _91535) : (term269 _91535 x y z) = (term298 _91535 y x z).
Proof. exact (MK_COMB (@lem3568320 _91535 x y) (@lem3568310 _91535 y x z)). Qed.
Lemma lem3568325 (q : Prop) (p : Prop) (r : Prop) : (term299 p q r) = (term299 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3568326 {_91535 : Type'} (y : _91535) (x : _91535) (z : _91535) : (term298 _91535 y x z) = (term300 _91535 y x z).
Proof. exact (@lem3568325 (y = z) (term296 _91535 x y) (term296 _91535 x z)). Qed.
Lemma lem3568348 {_91535 : Type'} (y : _91535) (x : _91535) (z : _91535) : (term269 _91535 x y z) = (term300 _91535 y x z).
Proof. exact (TRANS (@lem3568321 _91535 y x z) (@lem3568326 _91535 y x z)). Qed.
Lemma lem3568349 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3568350 {_91535 : Type'} (y : _91535) (x : _91535) (z : _91535) : (term301 _91535 x y z) = (term302 _91535 y x z).
Proof. exact (MK_COMB (@lem3568349) (@lem3568348 _91535 y x z)). Qed.
Lemma lem3568372 {_91535 : Type'} (y : _91535) (x : _91535) (z : _91535) : (term300 _91535 y x z) = (term300 _91535 y x z).
Proof. exact (eq_refl (term300 _91535 y x z)). Qed.
Lemma lem3568373 {_91535 : Type'} (y : _91535) (x : _91535) (z : _91535) : ((term269 _91535 x y z) = (term300 _91535 y x z)) = ((term300 _91535 y x z) = (term300 _91535 y x z)).
Proof. exact (MK_COMB (@lem3568350 _91535 y x z) (@lem3568372 _91535 y x z)). Qed.
Lemma lem3568375 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3568376 (x : Prop) : (x = x) = True.
Proof. exact (@lem3568375 Prop x). Qed.
Lemma lem3568377 {_91535 : Type'} (y : _91535) (x : _91535) (z : _91535) : ((term300 _91535 y x z) = (term300 _91535 y x z)) = True.
Proof. exact (@lem3568376 (term300 _91535 y x z)). Qed.
Lemma lem3568378 {_91535 : Type'} (y : _91535) (x : _91535) (z : _91535) : ((term269 _91535 x y z) = (term300 _91535 y x z)) = True.
Proof. exact (TRANS (@lem3568373 _91535 y x z) (@lem3568377 _91535 y x z)). Qed.
Lemma lem3568379 {_91535 : Type'} (y : _91535) (x : _91535) (z : _91535) : True = ((term269 _91535 x y z) = (term300 _91535 y x z)).
Proof. exact (SYM (@lem3568378 _91535 y x z)). Qed.
Lemma lem3568380 {_91535 : Type'} (y : _91535) (x : _91535) (z : _91535) : (term269 _91535 x y z) = (term300 _91535 y x z).
Proof. exact (EQ_MP (@lem3568379 _91535 y x z) (@lem0)). Qed.
Lemma lem3568381 {_91535 : Type'} (y : _91535) (x : _91535) (z : _91535) : term300 _91535 y x z.
Proof. exact (EQ_MP (@lem3568380 _91535 y x z) (@lem3568030 _91535 x y z)). Qed.
Lemma lem3568383 (b : Prop) (a : Prop) : (a \/ b) = (term252 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3568384 {_91535 : Type'} (x : _91535) (y : _91535) (z : _91535) : (term300 _91535 y x z) = (term303 _91535 x y z).
Proof. exact (@lem3568383 (term304 _91535 y x z) (y = z)). Qed.
Lemma lem3568386 (a : Prop) (b : Prop) : (term305 a b) = (term306 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3568387 {_91535 : Type'} (y : _91535) (x : _91535) (z : _91535) : (term307 _91535 y x z) = (term308 _91535 y x z).
Proof. exact (@lem3568386 (term296 _91535 x y) (term296 _91535 x z)). Qed.
Lemma lem3568389 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3568390 {_91535 : Type'} (x : _91535) (y : _91535) : (term309 _91535 x y) = (x = y).
Proof. exact (@lem3568389 (x = y)). Qed.
Lemma lem3568391 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3568392 {_91535 : Type'} (x : _91535) (y : _91535) : (term310 _91535 x y) = (term311 _91535 x y).
Proof. exact (MK_COMB (@lem3568391) (@lem3568390 _91535 x y)). Qed.
Lemma lem3568394 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3568395 {_91535 : Type'} (x : _91535) (z : _91535) : (term309 _91535 x z) = (x = z).
Proof. exact (@lem3568394 (x = z)). Qed.
Lemma lem3568396 {_91535 : Type'} (y : _91535) (x : _91535) (z : _91535) : (term308 _91535 y x z) = (term312 _91535 y x z).
Proof. exact (MK_COMB (@lem3568392 _91535 x y) (@lem3568395 _91535 x z)). Qed.
Lemma lem3568397 {_91535 : Type'} (y : _91535) (x : _91535) (z : _91535) : (term307 _91535 y x z) = (term312 _91535 y x z).
Proof. exact (TRANS (@lem3568387 _91535 y x z) (@lem3568396 _91535 y x z)). Qed.
Lemma lem3568398 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3568399 {_91535 : Type'} (y : _91535) (x : _91535) (z : _91535) : (term313 _91535 y x z) = (term314 _91535 y x z).
Proof. exact (MK_COMB (@lem3568398) (@lem3568397 _91535 y x z)). Qed.
Lemma lem3568400 {_91535 : Type'} (y : _91535) (z : _91535) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem3568401 {_91535 : Type'} (x : _91535) (y : _91535) (z : _91535) : (term303 _91535 x y z) = (term315 _91535 x y z).
Proof. exact (MK_COMB (@lem3568399 _91535 y x z) (@lem3568400 _91535 y z)). Qed.
Lemma lem3568402 {_91535 : Type'} (x : _91535) (y : _91535) (z : _91535) : (term300 _91535 y x z) = (term315 _91535 x y z).
Proof. exact (TRANS (@lem3568384 _91535 x y z) (@lem3568401 _91535 x y z)). Qed.
Lemma lem3568404 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term123 _91535 _91536 g' t s f g) (h3 : term150 _91535 _91536 s g f x) : term316 _91535 _91536 g f x.
Proof. exact (conj (@lem3568282 _91535 _91536 g' t s g f x h1 h2 h3) (@lem3568291 _91535 _91536 g f x)). Qed.
Lemma lem3568406 {_91535 : Type'} (x : _91535) (y : _91535) (z : _91535) : term315 _91535 x y z.
Proof. exact (EQ_MP (@lem3568402 _91535 x y z) (@lem3568381 _91535 y x z)). Qed.
Lemma lem3568407 {_91535 : Type'} (x : _91535) (y : _91535) (z : _91535) : term315 _91535 x y z.
Proof. exact (@lem3568406 _91535 x y z). Qed.
Lemma lem3568408 {_91535 _91536 : Type'} (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : term317 _91535 _91536 g f x.
Proof. exact (@lem3568407 _91535 (term289 _91535 _91536 g f x) (f x) (term289 _91535 _91536 g f x)). Qed.
Lemma lem3568411 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term123 _91535 _91536 g' t s f g) (h3 : term150 _91535 _91536 s g f x) : (f x) = (term289 _91535 _91536 g f x).
Proof. exact (@lem3568408 _91535 _91536 g f x (@lem3568404 _91535 _91536 g' t s g f x h1 h2 h3)). Qed.
Lemma lem3568412 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term123 _91535 _91536 g' t s f g) (h3 : term150 _91535 _91536 s g f x) : term318 _91535 _91536 g f x.
Proof. exact (fun h0 : term319 _91535 _91536 g f x => @lem3568411 _91535 _91536 g' t s g f x h1 h2 h3). Qed.
Lemma lem3568414 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3568415 {_91535 _91536 : Type'} (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : (term318 _91535 _91536 g f x) = ((f x) = (term289 _91535 _91536 g f x)).
Proof. exact (@lem3568414 ((f x) = (term289 _91535 _91536 g f x))). Qed.
Lemma lem3568416 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term123 _91535 _91536 g' t s f g) (h3 : term150 _91535 _91536 s g f x) : (f x) = (term289 _91535 _91536 g f x).
Proof. exact (EQ_MP (@lem3568415 _91535 _91536 g f x) (@lem3568412 _91535 _91536 g' t s g f x h1 h2 h3)). Qed.
Lemma lem3568422 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3568423 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (_38326 : _91535) (_38327 : _91535) : (term268 _91535 _91536 _38326 g' _38327) = (term320 _91535 _91536 g' _38326 _38327).
Proof. exact (@lem3568422 ((g' _38326) = (g' _38327)) (term296 _91535 _38326 _38327)). Qed.
Lemma lem3568433 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3568434 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (_38326 : _91535) (_38327 : _91535) : (term321 _91535 _91536 _38326 g' _38327) = (term322 _91535 _91536 g' _38326 _38327).
Proof. exact (MK_COMB (@lem3568433) (@lem3568423 _91535 _91536 g' _38326 _38327)). Qed.
Lemma lem3568444 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (_38326 : _91535) (_38327 : _91535) : (term320 _91535 _91536 g' _38326 _38327) = (term320 _91535 _91536 g' _38326 _38327).
Proof. exact (eq_refl (term320 _91535 _91536 g' _38326 _38327)). Qed.
Lemma lem3568445 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (_38326 : _91535) (_38327 : _91535) : ((term268 _91535 _91536 _38326 g' _38327) = (term320 _91535 _91536 g' _38326 _38327)) = ((term320 _91535 _91536 g' _38326 _38327) = (term320 _91535 _91536 g' _38326 _38327)).
Proof. exact (MK_COMB (@lem3568434 _91535 _91536 g' _38326 _38327) (@lem3568444 _91535 _91536 g' _38326 _38327)). Qed.
Lemma lem3568447 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3568448 (x : Prop) : (x = x) = True.
Proof. exact (@lem3568447 Prop x). Qed.
Lemma lem3568449 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (_38326 : _91535) (_38327 : _91535) : ((term320 _91535 _91536 g' _38326 _38327) = (term320 _91535 _91536 g' _38326 _38327)) = True.
Proof. exact (@lem3568448 (term320 _91535 _91536 g' _38326 _38327)). Qed.
Lemma lem3568450 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (_38326 : _91535) (_38327 : _91535) : ((term268 _91535 _91536 _38326 g' _38327) = (term320 _91535 _91536 g' _38326 _38327)) = True.
Proof. exact (TRANS (@lem3568445 _91535 _91536 g' _38326 _38327) (@lem3568449 _91535 _91536 g' _38326 _38327)). Qed.
Lemma lem3568451 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (_38326 : _91535) (_38327 : _91535) : True = ((term268 _91535 _91536 _38326 g' _38327) = (term320 _91535 _91536 g' _38326 _38327)).
Proof. exact (SYM (@lem3568450 _91535 _91536 g' _38326 _38327)). Qed.
Lemma lem3568452 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (_38326 : _91535) (_38327 : _91535) : (term268 _91535 _91536 _38326 g' _38327) = (term320 _91535 _91536 g' _38326 _38327).
Proof. exact (EQ_MP (@lem3568451 _91535 _91536 g' _38326 _38327) (@lem0)). Qed.
Lemma lem3568453 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (_38326 : _91535) (_38327 : _91535) : term320 _91535 _91536 g' _38326 _38327.
Proof. exact (EQ_MP (@lem3568452 _91535 _91536 g' _38326 _38327) (@lem3568020 _91535 _91536 _38326 g' _38327)). Qed.
Lemma lem3568455 (b : Prop) (a : Prop) : (a \/ b) = (term252 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3568456 {_91535 _91536 : Type'} (_38326 : _91535) (g' : _91535 -> _91536) (_38327 : _91535) : (term320 _91535 _91536 g' _38326 _38327) = (term323 _91535 _91536 _38326 g' _38327).
Proof. exact (@lem3568455 (term296 _91535 _38326 _38327) ((g' _38326) = (g' _38327))). Qed.
Lemma lem3568458 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3568459 {_91535 : Type'} (_38326 : _91535) (_38327 : _91535) : (term309 _91535 _38326 _38327) = (_38326 = _38327).
Proof. exact (@lem3568458 (_38326 = _38327)). Qed.
Lemma lem3568460 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3568461 {_91535 : Type'} (_38326 : _91535) (_38327 : _91535) : (term324 _91535 _38326 _38327) = (term325 _91535 _38326 _38327).
Proof. exact (MK_COMB (@lem3568460) (@lem3568459 _91535 _38326 _38327)). Qed.
Lemma lem3568462 {_91535 _91536 : Type'} (_38326 : _91535) (g' : _91535 -> _91536) (_38327 : _91535) : ((g' _38326) = (g' _38327)) = ((g' _38326) = (g' _38327)).
Proof. exact (eq_refl ((g' _38326) = (g' _38327))). Qed.
Lemma lem3568463 {_91535 _91536 : Type'} (_38326 : _91535) (g' : _91535 -> _91536) (_38327 : _91535) : (term323 _91535 _91536 _38326 g' _38327) = (term266 _91535 _91536 _38326 g' _38327).
Proof. exact (MK_COMB (@lem3568461 _91535 _38326 _38327) (@lem3568462 _91535 _91536 _38326 g' _38327)). Qed.
Lemma lem3568464 {_91535 _91536 : Type'} (_38326 : _91535) (g' : _91535 -> _91536) (_38327 : _91535) : (term320 _91535 _91536 g' _38326 _38327) = (term266 _91535 _91536 _38326 g' _38327).
Proof. exact (TRANS (@lem3568456 _91535 _91536 _38326 g' _38327) (@lem3568463 _91535 _91536 _38326 g' _38327)). Qed.
Lemma lem3568467 {_91535 _91536 : Type'} (_38326 : _91535) (g' : _91535 -> _91536) (_38327 : _91535) : term266 _91535 _91536 _38326 g' _38327.
Proof. exact (EQ_MP (@lem3568464 _91535 _91536 _38326 g' _38327) (@lem3568453 _91535 _91536 g' _38326 _38327)). Qed.
Lemma lem3568468 {_91535 _91536 : Type'} (_38326 : _91535) (g' : _91535 -> _91536) (_38327 : _91535) : term266 _91535 _91536 _38326 g' _38327.
Proof. exact (@lem3568467 _91535 _91536 _38326 g' _38327). Qed.
Lemma lem3568469 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : term326 _91535 _91536 g' g f x.
Proof. exact (@lem3568468 _91535 _91536 (f x) g' (term289 _91535 _91536 g f x)). Qed.
Lemma lem3568472 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term123 _91535 _91536 g' t s f g) (h3 : term150 _91535 _91536 s g f x) : (term97 _91535 _91536 g' f x) = (term285 _91535 _91536 g' g f x).
Proof. exact (@lem3568469 _91535 _91536 g' g f x (@lem3568416 _91535 _91536 g' t s g f x h1 h2 h3)). Qed.
Lemma lem3568473 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term123 _91535 _91536 g' t s f g) (h3 : term150 _91535 _91536 s g f x) : term327 _91535 _91536 g' g f x.
Proof. exact (fun h0 : term328 _91535 _91536 g' g f x => @lem3568472 _91535 _91536 g' t s g f x h1 h2 h3). Qed.
Lemma lem3568475 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3568476 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : (term327 _91535 _91536 g' g f x) = ((term97 _91535 _91536 g' f x) = (term285 _91535 _91536 g' g f x)).
Proof. exact (@lem3568475 ((term97 _91535 _91536 g' f x) = (term285 _91535 _91536 g' g f x))). Qed.
Lemma lem3568477 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term123 _91535 _91536 g' t s f g) (h3 : term150 _91535 _91536 s g f x) : (term97 _91535 _91536 g' f x) = (term285 _91535 _91536 g' g f x).
Proof. exact (EQ_MP (@lem3568476 _91535 _91536 g' g f x) (@lem3568473 _91535 _91536 g' t s g f x h1 h2 h3)). Qed.
Lemma lem3568479 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term150 _91535 _91536 s g f x) : @IN _91536 x s.
Proof. exact (proj1 (@lem3567378 _91535 _91536 s g f x h1)). Qed.
Lemma lem3568480 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term150 _91535 _91536 s g f x) : term247 _91536 x s.
Proof. exact (fun h0 : term236 _91536 x s => @lem3568479 _91535 _91536 s g f x h1). Qed.
Lemma lem3568482 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3568483 {_91536 : Type'} (x : _91536) (s : _91536 -> Prop) : (term247 _91536 x s) = (@IN _91536 x s).
Proof. exact (@lem3568482 (@IN _91536 x s)). Qed.
Lemma lem3568484 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term150 _91535 _91536 s g f x) : @IN _91536 x s.
Proof. exact (EQ_MP (@lem3568483 _91536 x s) (@lem3568480 _91535 _91536 s g f x h1)). Qed.
Lemma lem3568486 {_91535 _91536 : Type'} (_38286 : _91536) (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term123 _91535 _91536 g' t s f g) : term71 _91535 _91536 s g' f _38286.
Proof. exact (EQ_MP (@lem3568193 _91535 _91536 s g' f _38286) (@lem3568182 _91535 _91536 _38286 g' t s f g h1)). Qed.
Lemma lem3568487 {_91535 _91536 : Type'} (_38286 : _91536) (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term123 _91535 _91536 g' t s f g) : term71 _91535 _91536 s g' f _38286.
Proof. exact (@lem3568486 _91535 _91536 _38286 g' t s f g h1). Qed.
Lemma lem3568488 {_91535 _91536 : Type'} (x : _91536) (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term123 _91535 _91536 g' t s f g) : term71 _91535 _91536 s g' f x.
Proof. exact (@lem3568487 _91535 _91536 x g' t s f g h1). Qed.
Lemma lem3568491 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term123 _91535 _91536 g' t s f g) (h2 : term150 _91535 _91536 s g f x) : (term97 _91535 _91536 g' f x) = x.
Proof. exact (@lem3568488 _91535 _91536 x g' t s f g h1 (@lem3568484 _91535 _91536 s g f x h2)). Qed.
Lemma lem3568492 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term123 _91535 _91536 g' t s f g) (h2 : term150 _91535 _91536 s g f x) : term329 _91535 _91536 g' f x.
Proof. exact (fun h0 : term246 _91535 _91536 g' f x => @lem3568491 _91535 _91536 g' t s g f x h1 h2). Qed.
Lemma lem3568494 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3568495 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : (term329 _91535 _91536 g' f x) = ((term97 _91535 _91536 g' f x) = x).
Proof. exact (@lem3568494 ((term97 _91535 _91536 g' f x) = x)). Qed.
Lemma lem3568496 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term123 _91535 _91536 g' t s f g) (h2 : term150 _91535 _91536 s g f x) : (term97 _91535 _91536 g' f x) = x.
Proof. exact (EQ_MP (@lem3568495 _91535 _91536 g' f x) (@lem3568492 _91535 _91536 g' t s g f x h1 h2)). Qed.
Lemma lem3568514 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3568515 {_91536 : Type'} (y : _91536) (x : _91536) (z : _91536) : (term294 _91536 x y z) = (term295 _91536 y x z).
Proof. exact (@lem3568514 (y = z) (term296 _91536 x z)). Qed.
Lemma lem3568525 {_91536 : Type'} (x : _91536) (y : _91536) : (term297 _91536 x y) = (term297 _91536 x y).
Proof. exact (eq_refl (term297 _91536 x y)). Qed.
Lemma lem3568526 {_91536 : Type'} (y : _91536) (x : _91536) (z : _91536) : (term269 _91536 x y z) = (term298 _91536 y x z).
Proof. exact (MK_COMB (@lem3568525 _91536 x y) (@lem3568515 _91536 y x z)). Qed.
Lemma lem3568530 (q : Prop) (p : Prop) (r : Prop) : (term299 p q r) = (term299 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3568531 {_91536 : Type'} (y : _91536) (x : _91536) (z : _91536) : (term298 _91536 y x z) = (term300 _91536 y x z).
Proof. exact (@lem3568530 (y = z) (term296 _91536 x y) (term296 _91536 x z)). Qed.
Lemma lem3568553 {_91536 : Type'} (y : _91536) (x : _91536) (z : _91536) : (term269 _91536 x y z) = (term300 _91536 y x z).
Proof. exact (TRANS (@lem3568526 _91536 y x z) (@lem3568531 _91536 y x z)). Qed.
Lemma lem3568554 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3568555 {_91536 : Type'} (y : _91536) (x : _91536) (z : _91536) : (term301 _91536 x y z) = (term302 _91536 y x z).
Proof. exact (MK_COMB (@lem3568554) (@lem3568553 _91536 y x z)). Qed.
Lemma lem3568577 {_91536 : Type'} (y : _91536) (x : _91536) (z : _91536) : (term300 _91536 y x z) = (term300 _91536 y x z).
Proof. exact (eq_refl (term300 _91536 y x z)). Qed.
Lemma lem3568578 {_91536 : Type'} (y : _91536) (x : _91536) (z : _91536) : ((term269 _91536 x y z) = (term300 _91536 y x z)) = ((term300 _91536 y x z) = (term300 _91536 y x z)).
Proof. exact (MK_COMB (@lem3568555 _91536 y x z) (@lem3568577 _91536 y x z)). Qed.
Lemma lem3568580 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3568581 (x : Prop) : (x = x) = True.
Proof. exact (@lem3568580 Prop x). Qed.
Lemma lem3568582 {_91536 : Type'} (y : _91536) (x : _91536) (z : _91536) : ((term300 _91536 y x z) = (term300 _91536 y x z)) = True.
Proof. exact (@lem3568581 (term300 _91536 y x z)). Qed.
Lemma lem3568583 {_91536 : Type'} (y : _91536) (x : _91536) (z : _91536) : ((term269 _91536 x y z) = (term300 _91536 y x z)) = True.
Proof. exact (TRANS (@lem3568578 _91536 y x z) (@lem3568582 _91536 y x z)). Qed.
Lemma lem3568584 {_91536 : Type'} (y : _91536) (x : _91536) (z : _91536) : True = ((term269 _91536 x y z) = (term300 _91536 y x z)).
Proof. exact (SYM (@lem3568583 _91536 y x z)). Qed.
Lemma lem3568585 {_91536 : Type'} (y : _91536) (x : _91536) (z : _91536) : (term269 _91536 x y z) = (term300 _91536 y x z).
Proof. exact (EQ_MP (@lem3568584 _91536 y x z) (@lem0)). Qed.
Lemma lem3568586 {_91536 : Type'} (y : _91536) (x : _91536) (z : _91536) : term300 _91536 y x z.
Proof. exact (EQ_MP (@lem3568585 _91536 y x z) (@lem3568032 _91536 x y z)). Qed.
Lemma lem3568588 (b : Prop) (a : Prop) : (a \/ b) = (term252 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3568589 {_91536 : Type'} (x : _91536) (y : _91536) (z : _91536) : (term300 _91536 y x z) = (term303 _91536 x y z).
Proof. exact (@lem3568588 (term304 _91536 y x z) (y = z)). Qed.
Lemma lem3568591 (a : Prop) (b : Prop) : (term305 a b) = (term306 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3568592 {_91536 : Type'} (y : _91536) (x : _91536) (z : _91536) : (term307 _91536 y x z) = (term308 _91536 y x z).
Proof. exact (@lem3568591 (term296 _91536 x y) (term296 _91536 x z)). Qed.
Lemma lem3568594 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3568595 {_91536 : Type'} (x : _91536) (y : _91536) : (term309 _91536 x y) = (x = y).
Proof. exact (@lem3568594 (x = y)). Qed.
Lemma lem3568596 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3568597 {_91536 : Type'} (x : _91536) (y : _91536) : (term310 _91536 x y) = (term311 _91536 x y).
Proof. exact (MK_COMB (@lem3568596) (@lem3568595 _91536 x y)). Qed.
Lemma lem3568599 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3568600 {_91536 : Type'} (x : _91536) (z : _91536) : (term309 _91536 x z) = (x = z).
Proof. exact (@lem3568599 (x = z)). Qed.
Lemma lem3568601 {_91536 : Type'} (y : _91536) (x : _91536) (z : _91536) : (term308 _91536 y x z) = (term312 _91536 y x z).
Proof. exact (MK_COMB (@lem3568597 _91536 x y) (@lem3568600 _91536 x z)). Qed.
Lemma lem3568602 {_91536 : Type'} (y : _91536) (x : _91536) (z : _91536) : (term307 _91536 y x z) = (term312 _91536 y x z).
Proof. exact (TRANS (@lem3568592 _91536 y x z) (@lem3568601 _91536 y x z)). Qed.
Lemma lem3568603 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3568604 {_91536 : Type'} (y : _91536) (x : _91536) (z : _91536) : (term313 _91536 y x z) = (term314 _91536 y x z).
Proof. exact (MK_COMB (@lem3568603) (@lem3568602 _91536 y x z)). Qed.
Lemma lem3568605 {_91536 : Type'} (y : _91536) (z : _91536) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem3568606 {_91536 : Type'} (x : _91536) (y : _91536) (z : _91536) : (term303 _91536 x y z) = (term315 _91536 x y z).
Proof. exact (MK_COMB (@lem3568604 _91536 y x z) (@lem3568605 _91536 y z)). Qed.
Lemma lem3568607 {_91536 : Type'} (x : _91536) (y : _91536) (z : _91536) : (term300 _91536 y x z) = (term315 _91536 x y z).
Proof. exact (TRANS (@lem3568589 _91536 x y z) (@lem3568606 _91536 x y z)). Qed.
Lemma lem3568609 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term123 _91535 _91536 g' t s f g) (h3 : term150 _91535 _91536 s g f x) : term330 _91535 _91536 g g' f x.
Proof. exact (conj (@lem3568477 _91535 _91536 g' t s g f x h1 h2 h3) (@lem3568496 _91535 _91536 g' t s g f x h2 h3)). Qed.
Lemma lem3568611 {_91536 : Type'} (x : _91536) (y : _91536) (z : _91536) : term315 _91536 x y z.
Proof. exact (EQ_MP (@lem3568607 _91536 x y z) (@lem3568586 _91536 y x z)). Qed.
Lemma lem3568612 {_91536 : Type'} (x : _91536) (y : _91536) (z : _91536) : term315 _91536 x y z.
Proof. exact (@lem3568611 _91536 x y z). Qed.
Lemma lem3568613 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : term331 _91535 _91536 g' g f x.
Proof. exact (@lem3568612 _91536 (term97 _91535 _91536 g' f x) (term285 _91535 _91536 g' g f x) x). Qed.
Lemma lem3568616 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term123 _91535 _91536 g' t s f g) (h3 : term150 _91535 _91536 s g f x) : (term285 _91535 _91536 g' g f x) = x.
Proof. exact (@lem3568613 _91535 _91536 g' g f x (@lem3568609 _91535 _91536 g' t s g f x h1 h2 h3)). Qed.
Lemma lem3568617 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term123 _91535 _91536 g' t s f g) (h3 : term150 _91535 _91536 s g f x) : term332 _91535 _91536 g' g f x.
Proof. exact (fun h0 : term333 _91535 _91536 g' g f x => @lem3568616 _91535 _91536 g' t s g f x h1 h2 h3). Qed.
Lemma lem3568619 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3568620 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : (term332 _91535 _91536 g' g f x) = ((term285 _91535 _91536 g' g f x) = x).
Proof. exact (@lem3568619 ((term285 _91535 _91536 g' g f x) = x)). Qed.
Lemma lem3568621 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term123 _91535 _91536 g' t s f g) (h3 : term150 _91535 _91536 s g f x) : (term285 _91535 _91536 g' g f x) = x.
Proof. exact (EQ_MP (@lem3568620 _91535 _91536 g' g f x) (@lem3568617 _91535 _91536 g' t s g f x h1 h2 h3)). Qed.
Lemma lem3568622 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term123 _91535 _91536 g' t s f g) (h3 : term150 _91535 _91536 s g f x) : term334 _91535 _91536 g' g f x.
Proof. exact (conj (@lem3568206 _91535 _91536 g' t s g f x h1 h2 h3) (@lem3568621 _91535 _91536 g' t s g f x h1 h2 h3)). Qed.
Lemma lem3568624 {_91536 : Type'} (x : _91536) (y : _91536) (z : _91536) : term315 _91536 x y z.
Proof. exact (EQ_MP (@lem3568607 _91536 x y z) (@lem3568586 _91536 y x z)). Qed.
Lemma lem3568625 {_91536 : Type'} (x : _91536) (y : _91536) (z : _91536) : term315 _91536 x y z.
Proof. exact (@lem3568624 _91536 x y z). Qed.
Lemma lem3568626 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : term335 _91535 _91536 g' g f x.
Proof. exact (@lem3568625 _91536 (term285 _91535 _91536 g' g f x) (term97 _91535 _91536 g f x) x). Qed.
Lemma lem3568629 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term123 _91535 _91536 g' t s f g) (h3 : term150 _91535 _91536 s g f x) : (term97 _91535 _91536 g f x) = x.
Proof. exact (@lem3568626 _91535 _91536 g' g f x (@lem3568622 _91535 _91536 g' t s g f x h1 h2 h3)). Qed.
Lemma lem3568630 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term123 _91535 _91536 g' t s f g) (h3 : term150 _91535 _91536 s g f x) : term329 _91535 _91536 g f x.
Proof. exact (fun h0 : term246 _91535 _91536 g f x => @lem3568629 _91535 _91536 g' t s g f x h1 h2 h3). Qed.
Lemma lem3568632 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3568633 {_91535 _91536 : Type'} (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : (term329 _91535 _91536 g f x) = ((term97 _91535 _91536 g f x) = x).
Proof. exact (@lem3568632 ((term97 _91535 _91536 g f x) = x)). Qed.
Lemma lem3568634 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term123 _91535 _91536 g' t s f g) (h3 : term150 _91535 _91536 s g f x) : (term97 _91535 _91536 g f x) = x.
Proof. exact (EQ_MP (@lem3568633 _91535 _91536 g f x) (@lem3568630 _91535 _91536 g' t s g f x h1 h2 h3)). Qed.
Lemma lem3568637 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3568639 {_91535 _91536 : Type'} (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : (term246 _91535 _91536 g f x) = (term336 _91535 _91536 g f x).
Proof. exact (@lem3568637 ((term97 _91535 _91536 g f x) = x)). Qed.
Lemma lem3568642 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term150 _91535 _91536 s g f x) : term336 _91535 _91536 g f x.
Proof. exact (EQ_MP (@lem3568639 _91535 _91536 g f x) (@lem3567658 _91535 _91536 s g f x h1)). Qed.
Lemma lem3568645 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term123 _91535 _91536 g' t s f g) (h3 : term150 _91535 _91536 s g f x) : False.
Proof. exact (@lem3568642 _91535 _91536 s g f x h3 (@lem3568634 _91535 _91536 g' t s g f x h1 h2 h3)). Qed.
Lemma lem3568646 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term123 _91535 _91536 g' t s f g) (h3 : term150 _91535 _91536 s g f x) : term259.
Proof. exact (fun h0 : ~ False => @lem3568645 _91535 _91536 g' t s g f x h1 h2 h3). Qed.
Lemma lem3568648 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3568649 : term259 = False.
Proof. exact (@lem3568648 False). Qed.
Lemma lem3568650 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term123 _91535 _91536 g' t s f g) (h3 : term150 _91535 _91536 s g f x) : False.
Proof. exact (EQ_MP (@lem3568649) (@lem3568646 _91535 _91536 g' t s g f x h1 h2 h3)). Qed.
Lemma lem3568651 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (t : _91535 -> Prop) (y : _91535) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term123 _91535 _91536 g' t s f g) (h3 : term194 _91535 _91536 t y s g f x) : False.
Proof. exact (or_elim (@lem3567374 _91535 _91536 t y s g f x h3) (fun h0 : term140 _91535 _91536 t f g y => @lem3567966 _91535 _91536 g' s t f g y h2 h0) (fun h0 : term150 _91535 _91536 s g f x => @lem3568650 _91535 _91536 g' t s g f x h1 h2 h0)). Qed.
Lemma lem3568652 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (t : _91535 -> Prop) (y : _91535) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term123 _91535 _91536 g' t s f g) (h3 : term229 _91535 _91536 t y s g f x) : False.
Proof. exact (or_elim (@lem3567312 _91535 _91536 t y s g f x h3) (fun h0 : term128 _91535 _91536 t g y s => @lem3567816 _91535 _91536 g' f t g y s h2 h0) (fun h0 : term194 _91535 _91536 t y s g f x => @lem3568651 _91535 _91536 g' t y s g f x h1 h2 h0)). Qed.
Lemma lem3568653 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (t : _91535 -> Prop) (y : _91535) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term123 _91535 _91536 g' t s f g) (h3 : term229 _91535 _91536 t y s g f x) : (term123 _91535 _91536 g' t s f g) = False.
Proof. exact (prop_ext (fun h4 : term123 _91535 _91536 g' t s f g => @lem3568652 _91535 _91536 g' t y s g f x h1 h2 h3) (fun h4 : False => @lem3567370 _91535 _91536 g' t s f g h2)). Qed.
Lemma lem3568654 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (t : _91535 -> Prop) (y : _91535) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term123 _91535 _91536 g' t s f g) (h3 : term229 _91535 _91536 t y s g f x) : False.
Proof. exact (EQ_MP (@lem3568653 _91535 _91536 g' t y s g f x h1 h2 h3) (@lem3567370 _91535 _91536 g' t s f g h2)). Qed.
Lemma lem3568655 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (t : _91535 -> Prop) (y : _91535) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term123 _91535 _91536 g' t s f g) (h3 : term229 _91535 _91536 t y s g f x) : (term229 _91535 _91536 t y s g f x) = False.
Proof. exact (prop_ext (fun h4 : term229 _91535 _91536 t y s g f x => @lem3568654 _91535 _91536 g' t y s g f x h1 h2 h3) (fun h4 : False => @lem3567312 _91535 _91536 t y s g f x h3)). Qed.
Lemma lem3568656 {_91535 _91536 : Type'} (g' : _91535 -> _91536) (t : _91535 -> Prop) (y : _91535) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term123 _91535 _91536 g' t s f g) (h3 : term229 _91535 _91536 t y s g f x) : False.
Proof. exact (EQ_MP (@lem3568655 _91535 _91536 g' t y s g f x h1 h2 h3) (@lem3567312 _91535 _91536 t y s g f x h3)). Qed.
Lemma lem3568657 {_91535 _91536 : Type'} (t : _91535 -> Prop) (y : _91535) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term38 _91535 _91536 t s f g) (h3 : term229 _91535 _91536 t y s g f x) : False.
Proof. exact (ex_elim (@lem3566913 _91535 _91536 t s f g h2) (fun g' : _91535 -> _91536 => fun h0 : term125 _91535 _91536 t s f g g' => @lem3568656 _91535 _91536 g' t y s g f x h1 h0 h3)). Qed.
Lemma lem3568658 {_91535 _91536 : Type'} (y : _91535) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term232 _91535 _91536 t y s g f) (h3 : term38 _91535 _91536 t s f g) : False.
Proof. exact (ex_elim (@lem3567227 _91535 _91536 t y s g f h2) (fun x : _91536 => fun h0 : term231 _91535 _91536 t y s g f x => @lem3568657 _91535 _91536 t y s g f x h1 h3 h0)). Qed.
Lemma lem3568659 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term91 _91535 _91536 t s g f) (h3 : term38 _91535 _91536 t s f g) : False.
Proof. exact (ex_elim (@lem3567226 _91535 _91536 t s g f h2) (fun y : _91535 => fun h0 : term233 _91535 _91536 t s g f y => @lem3568658 _91535 _91536 y t s f g h1 h0 h3)). Qed.
Lemma lem3568660 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term91 _91535 _91536 t s g f) (h3 : term38 _91535 _91536 t s f g) : (term91 _91535 _91536 t s g f) = False.
Proof. exact (prop_ext (fun h4 : term91 _91535 _91536 t s g f => @lem3568659 _91535 _91536 t s f g h1 h2 h3) (fun h4 : False => @lem3566692 _91535 _91536 t s g f h2)). Qed.
Lemma lem3568661 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term91 _91535 _91536 t s g f) (h3 : term38 _91535 _91536 t s f g) : False.
Proof. exact (EQ_MP (@lem3568660 _91535 _91536 t s f g h1 h2 h3) (@lem3566692 _91535 _91536 t s g f h2)). Qed.
Lemma lem3568662 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term38 _91535 _91536 t s f g) : term90 _91535 _91536 t s g f.
Proof. exact (fun h0 : term91 _91535 _91536 t s g f => @lem3568661 _91535 _91536 t s f g h1 h0 h2). Qed.
Lemma lem3568663 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term38 _91535 _91536 t s f g) : term83 _91535 _91536 t s g f.
Proof. exact (EQ_MP (@lem3566691 _91535 _91536 t s g f) (@lem3568662 _91535 _91536 t s f g h1 h2)). Qed.
Lemma lem3568664 {_91535 _91536 : Type'} (g : _91535 -> _91536) (s : _91536 -> Prop) (f : _91536 -> _91535) (t : _91535 -> Prop) (h1 : term15 _91535 _91536 s f t) : term44 _91535 _91536 t s g f.
Proof. exact (fun h0 : term38 _91535 _91536 t s f g => @lem3568663 _91535 _91536 t s f g h1 h0). Qed.
Lemma lem3568665 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : term54 _91535 _91536 t s g f.
Proof. exact (fun h0 : term15 _91535 _91536 s f t => @lem3568664 _91535 _91536 g s f t h0). Qed.
Lemma lem3568670 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : term58 _91535 _91536 s g f.
Proof. exact (fun t : _91535 -> Prop => @lem3568665 _91535 _91536 t s g f). Qed.
Lemma lem3568675 {_91535 _91536 : Type'} (g : _91535 -> _91536) (f : _91536 -> _91535) : term62 _91535 _91536 g f.
Proof. exact (fun s : _91536 -> Prop => @lem3568670 _91535 _91536 s g f). Qed.
Lemma lem3568680 {_91535 _91536 : Type'} (f : _91536 -> _91535) : term66 _91535 _91536 f.
Proof. exact (fun g : _91535 -> _91536 => @lem3568675 _91535 _91536 g f). Qed.
Lemma lem3568685 {_91535 _91536 : Type'} : term70 _91535 _91536.
Proof. exact (fun f : _91536 -> _91535 => @lem3568680 _91535 _91536 f). Qed.
Lemma lem3568686 {_91535 _91536 : Type'} : term69 _91535 _91536.
Proof. exact (EQ_MP (@lem3566685 _91535 _91536) (@lem3568685 _91535 _91536)). Qed.
Lemma lem3568687 {_91535 _91536 : Type'} (f : _91536 -> _91535) : term337 _91535 _91536 f.
Proof. exact (@lem3568686 _91535 _91536 f). Qed.
Lemma lem3568688 {_91535 _91536 : Type'} (f : _91536 -> _91535) : (term337 _91535 _91536 f) = (term65 _91535 _91536 f).
Proof. exact (eq_refl (term337 _91535 _91536 f)). Qed.
Lemma lem3568689 {_91535 _91536 : Type'} (f : _91536 -> _91535) : term65 _91535 _91536 f.
Proof. exact (EQ_MP (@lem3568688 _91535 _91536 f) (@lem3568687 _91535 _91536 f)). Qed.
Lemma lem3568690 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) : term338 _91535 _91536 f g.
Proof. exact (@lem3568689 _91535 _91536 f g). Qed.
Lemma lem3568691 {_91535 _91536 : Type'} (g : _91535 -> _91536) (f : _91536 -> _91535) : (term338 _91535 _91536 f g) = (term61 _91535 _91536 g f).
Proof. exact (eq_refl (term338 _91535 _91536 f g)). Qed.
Lemma lem3568692 {_91535 _91536 : Type'} (g : _91535 -> _91536) (f : _91536 -> _91535) : term61 _91535 _91536 g f.
Proof. exact (EQ_MP (@lem3568691 _91535 _91536 g f) (@lem3568690 _91535 _91536 f g)). Qed.
Lemma lem3568693 {_91535 _91536 : Type'} (g : _91535 -> _91536) (f : _91536 -> _91535) (s : _91536 -> Prop) : term339 _91535 _91536 g f s.
Proof. exact (@lem3568692 _91535 _91536 g f s). Qed.
Lemma lem3568694 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term339 _91535 _91536 g f s) = (term57 _91535 _91536 s g f).
Proof. exact (eq_refl (term339 _91535 _91536 g f s)). Qed.
Lemma lem3568695 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : term57 _91535 _91536 s g f.
Proof. exact (EQ_MP (@lem3568694 _91535 _91536 s g f) (@lem3568693 _91535 _91536 g f s)). Qed.
Lemma lem3568696 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (t : _91535 -> Prop) : term340 _91535 _91536 s g f t.
Proof. exact (@lem3568695 _91535 _91536 s g f t). Qed.
Lemma lem3568697 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term340 _91535 _91536 s g f t) = (term47 _91535 _91536 t s g f).
Proof. exact (eq_refl (term340 _91535 _91536 s g f t)). Qed.
Lemma lem3568698 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : term47 _91535 _91536 t s g f.
Proof. exact (EQ_MP (@lem3568697 _91535 _91536 t s g f) (@lem3568696 _91535 _91536 s g f t)). Qed.
Lemma lem3568700 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : term47 _91535 _91536 t s g f.
Proof. exact (@lem3566398 _91535 _91536 t s g f (@lem3568698 _91535 _91536 t s g f)). Qed.
Lemma lem3568701 {_91535 _91536 : Type'} (g : _91535 -> _91536) (s : _91536 -> Prop) (f : _91536 -> _91535) (t : _91535 -> Prop) (h1 : term15 _91535 _91536 s f t) : term45 _91535 _91536 t s g f.
Proof. exact (@lem3568700 _91535 _91536 t s g f (@lem3566211 _91535 _91536 s f t h1)). Qed.
Lemma lem3568702 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term15 _91535 _91536 s f t) (h2 : term46 _91535 _91536 t s g f) : False.
Proof. exact (@lem3568701 _91535 _91536 g s f t h1 (@lem3566382 _91535 _91536 t s g f h2)). Qed.
Lemma lem3568703 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term15 _91535 _91536 s f t) (h2 : term46 _91535 _91536 t s g f) : (term46 _91535 _91536 t s g f) = False.
Proof. exact (prop_ext (fun h3 : term46 _91535 _91536 t s g f => @lem3568702 _91535 _91536 t s g f h1 h2) (fun h3 : False => @lem3566382 _91535 _91536 t s g f h2)). Qed.
Lemma lem3568704 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term15 _91535 _91536 s f t) (h2 : term46 _91535 _91536 t s g f) : False.
Proof. exact (EQ_MP (@lem3568703 _91535 _91536 t s g f h1 h2) (@lem3566382 _91535 _91536 t s g f h2)). Qed.
Lemma lem3568705 {_91535 _91536 : Type'} (g : _91535 -> _91536) (s : _91536 -> Prop) (f : _91536 -> _91535) (t : _91535 -> Prop) (h1 : term15 _91535 _91536 s f t) : term45 _91535 _91536 t s g f.
Proof. exact (fun h0 : term46 _91535 _91536 t s g f => @lem3568704 _91535 _91536 t s g f h1 h0). Qed.
Lemma lem3568706 {_91535 _91536 : Type'} (g : _91535 -> _91536) (s : _91536 -> Prop) (f : _91536 -> _91535) (t : _91535 -> Prop) (h1 : term15 _91535 _91536 s f t) : term44 _91535 _91536 t s g f.
Proof. exact (EQ_MP (@lem3566381 _91535 _91536 t s g f) (@lem3568705 _91535 _91536 g s f t h1)). Qed.
Lemma lem3568708 (p : Prop) : p = (term43 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3568709 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term341 _91535 _91536 t s f g) = (term342 _91535 _91536 t s f g).
Proof. exact (@lem3568708 (term341 _91535 _91536 t s f g)). Qed.
Lemma lem3568710 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term342 _91535 _91536 t s f g) = (term341 _91535 _91536 t s f g).
Proof. exact (SYM (@lem3568709 _91535 _91536 t s f g)). Qed.
Lemma lem3568711 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term343 _91535 _91536 t s f g) : term343 _91535 _91536 t s f g.
Proof. exact (h1). Qed.
Lemma lem3568714 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term344 _91535 _91536 t s f g) : term344 _91535 _91536 t s f g.
Proof. exact (h1). Qed.
Lemma lem3568715 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : term345 _91535 _91536 t s f g.
Proof. exact (fun h0 : term344 _91535 _91536 t s f g => @lem3568714 _91535 _91536 t s f g h0). Qed.
Lemma lem3568716 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term345 _91535 _91536 t s f g) : term345 _91535 _91536 t s f g.
Proof. exact (h1). Qed.
Lemma lem3568717 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term344 _91535 _91536 t s f g) : term344 _91535 _91536 t s f g.
Proof. exact (h1). Qed.
Lemma lem3568718 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term344 _91535 _91536 t s f g) (h2 : term345 _91535 _91536 t s f g) : term344 _91535 _91536 t s f g.
Proof. exact (@lem3568716 _91535 _91536 t s f g h2 (@lem3568717 _91535 _91536 t s f g h1)). Qed.
Lemma lem3568719 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term344 _91535 _91536 t s f g) : term346 _91535 _91536 t s f g.
Proof. exact (fun h0 : term345 _91535 _91536 t s f g => @lem3568718 _91535 _91536 t s f g h1 h0). Qed.
Lemma lem3568720 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term345 _91535 _91536 t s f g) : term345 _91535 _91536 t s f g.
Proof. exact (h1). Qed.
Lemma lem3568721 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term344 _91535 _91536 t s f g) (h2 : term345 _91535 _91536 t s f g) : term344 _91535 _91536 t s f g.
Proof. exact (@lem3568719 _91535 _91536 t s f g h1 (@lem3568720 _91535 _91536 t s f g h2)). Qed.
Lemma lem3568722 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term345 _91535 _91536 t s f g) : term345 _91535 _91536 t s f g.
Proof. exact (fun h0 : term344 _91535 _91536 t s f g => @lem3568721 _91535 _91536 t s f g h0 h1). Qed.
Lemma lem3568723 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : term347 _91535 _91536 t s f g.
Proof. exact (fun h0 : term345 _91535 _91536 t s f g => @lem3568722 _91535 _91536 t s f g h0). Qed.
Lemma lem3568726 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : term345 _91535 _91536 t s f g.
Proof. exact (@lem3568723 _91535 _91536 t s f g (@lem3568715 _91535 _91536 t s f g)). Qed.
Lemma lem3568727 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : term345 _91535 _91536 t s f g.
Proof. exact (@lem3568726 _91535 _91536 t s f g). Qed.
Lemma lem3568753 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3568754 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term342 _91535 _91536 t s f g) = (term348 _91535 _91536 t s f g).
Proof. exact (@lem3568753 (term343 _91535 _91536 t s f g)). Qed.
Lemma lem3568756 (t : Prop) : (term52 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3568757 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term348 _91535 _91536 t s f g) = (term341 _91535 _91536 t s f g).
Proof. exact (@lem3568756 (term341 _91535 _91536 t s f g)). Qed.
Lemma lem3568760 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term342 _91535 _91536 t s f g) = (term341 _91535 _91536 t s f g).
Proof. exact (TRANS (@lem3568754 _91535 _91536 t s f g) (@lem3568757 _91535 _91536 t s f g)). Qed.
Lemma lem3568803 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (t : _91535 -> Prop) : (term53 _91535 _91536 s f t) = (term53 _91535 _91536 s f t).
Proof. exact (eq_refl (term53 _91535 _91536 s f t)). Qed.
Lemma lem3568804 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term344 _91535 _91536 t s f g) = (term349 _91535 _91536 t s f g).
Proof. exact (MK_COMB (@lem3568803 _91535 _91536 s f t) (@lem3568760 _91535 _91536 t s f g)). Qed.
Lemma lem3568807 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term350 _91535 _91536 s f g) = (term351 _91535 _91536 s f g).
Proof. exact (fun_ext (fun t : _91535 -> Prop => @lem3568804 _91535 _91536 t s f g)). Qed.
Lemma lem3568808 {_91535 : Type'} : (@all (_91535 -> Prop)) = (@all (_91535 -> Prop)).
Proof. exact (eq_refl (@all (_91535 -> Prop))). Qed.
Lemma lem3568809 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term352 _91535 _91536 s f g) = (term353 _91535 _91536 s f g).
Proof. exact (MK_COMB (@lem3568808 _91535) (@lem3568807 _91535 _91536 s f g)). Qed.
Lemma lem3568814 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) : (term354 _91535 _91536 f g) = (term355 _91535 _91536 f g).
Proof. exact (fun_ext (fun s : _91536 -> Prop => @lem3568809 _91535 _91536 s f g)). Qed.
Lemma lem3568815 {_91536 : Type'} : (@all (_91536 -> Prop)) = (@all (_91536 -> Prop)).
Proof. exact (eq_refl (@all (_91536 -> Prop))). Qed.
Lemma lem3568816 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) : (term356 _91535 _91536 f g) = (term357 _91535 _91536 f g).
Proof. exact (MK_COMB (@lem3568815 _91536) (@lem3568814 _91535 _91536 f g)). Qed.
Lemma lem3568821 {_91535 _91536 : Type'} (g : _91535 -> _91536) : (term358 _91535 _91536 g) = (term359 _91535 _91536 g).
Proof. exact (fun_ext (fun f : _91536 -> _91535 => @lem3568816 _91535 _91536 f g)). Qed.
Lemma lem3568822 {_91535 _91536 : Type'} : (@all (_91536 -> _91535)) = (@all (_91536 -> _91535)).
Proof. exact (eq_refl (@all (_91536 -> _91535))). Qed.
Lemma lem3568823 {_91535 _91536 : Type'} (g : _91535 -> _91536) : (term360 _91535 _91536 g) = (term361 _91535 _91536 g).
Proof. exact (MK_COMB (@lem3568822 _91535 _91536) (@lem3568821 _91535 _91536 g)). Qed.
Lemma lem3568828 {_91535 _91536 : Type'} : (term362 _91535 _91536) = (term363 _91535 _91536).
Proof. exact (fun_ext (fun g : _91535 -> _91536 => @lem3568823 _91535 _91536 g)). Qed.
Lemma lem3568829 {_91535 _91536 : Type'} : (@all (_91535 -> _91536)) = (@all (_91535 -> _91536)).
Proof. exact (eq_refl (@all (_91535 -> _91536))). Qed.
Lemma lem3568838 {_91535 _91536 : Type'} : (term364 _91535 _91536) = (term365 _91535 _91536).
Proof. exact (MK_COMB (@lem3568829 _91535 _91536) (@lem3568828 _91535 _91536)). Qed.
Lemma lem3568847 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : (term84 _91535 _91536 t s f g y) = (term84 _91535 _91536 t s f g y).
Proof. exact (eq_refl (term84 _91535 _91536 t s f g y)). Qed.
Lemma lem3568848 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term85 _91535 _91536 t s f g) = (term85 _91535 _91536 t s f g).
Proof. exact (fun_ext (fun y : _91535 => @lem3568847 _91535 _91536 t s f g y)). Qed.
Lemma lem3568849 {_91535 : Type'} : (@all _91535) = (@all _91535).
Proof. exact (eq_refl (@all _91535)). Qed.
Lemma lem3568850 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term33 _91535 _91536 t s f g) = (term33 _91535 _91536 t s f g).
Proof. exact (MK_COMB (@lem3568849 _91535) (@lem3568848 _91535 _91536 t s f g)). Qed.
Lemma lem3568855 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : (term71 _91535 _91536 s g f x) = (term71 _91535 _91536 s g f x).
Proof. exact (eq_refl (term71 _91535 _91536 s g f x)). Qed.
Lemma lem3568856 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term72 _91535 _91536 s g f) = (term72 _91535 _91536 s g f).
Proof. exact (fun_ext (fun x : _91536 => @lem3568855 _91535 _91536 s g f x)). Qed.
Lemma lem3568857 {_91536 : Type'} : (@all _91536) = (@all _91536).
Proof. exact (eq_refl (@all _91536)). Qed.
Lemma lem3568858 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term73 _91535 _91536 s g f) = (term73 _91535 _91536 s g f).
Proof. exact (MK_COMB (@lem3568857 _91536) (@lem3568856 _91535 _91536 s g f)). Qed.
Lemma lem3568859 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) : (term86 _91535 _91536 s f) = (term86 _91535 _91536 s f).
Proof. exact (fun_ext (fun g : _91535 -> _91536 => @lem3568858 _91535 _91536 s g f)). Qed.
Lemma lem3568860 {_91535 _91536 : Type'} : (@ex (_91535 -> _91536)) = (@ex (_91535 -> _91536)).
Proof. exact (eq_refl (@ex (_91535 -> _91536))). Qed.
Lemma lem3568861 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) : (term17 _91535 _91536 s f) = (term17 _91535 _91536 s f).
Proof. exact (MK_COMB (@lem3568860 _91535 _91536) (@lem3568859 _91535 _91536 s f)). Qed.
Lemma lem3568862 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3568863 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) : (term19 _91535 _91536 s f) = (term19 _91535 _91536 s f).
Proof. exact (MK_COMB (@lem3568862) (@lem3568861 _91535 _91536 s f)). Qed.
Lemma lem3568864 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term38 _91535 _91536 t s f g) = (term38 _91535 _91536 t s f g).
Proof. exact (MK_COMB (@lem3568863 _91535 _91536 s f) (@lem3568850 _91535 _91536 t s f g)). Qed.
Lemma lem3568869 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : (term71 _91535 _91536 s g f x) = (term71 _91535 _91536 s g f x).
Proof. exact (eq_refl (term71 _91535 _91536 s g f x)). Qed.
Lemma lem3568870 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term72 _91535 _91536 s g f) = (term72 _91535 _91536 s g f).
Proof. exact (fun_ext (fun x : _91536 => @lem3568869 _91535 _91536 s g f x)). Qed.
Lemma lem3568871 {_91536 : Type'} : (@all _91536) = (@all _91536).
Proof. exact (eq_refl (@all _91536)). Qed.
Lemma lem3568872 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term73 _91535 _91536 s g f) = (term73 _91535 _91536 s g f).
Proof. exact (MK_COMB (@lem3568871 _91536) (@lem3568870 _91535 _91536 s g f)). Qed.
Lemma lem3568877 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : (term74 _91535 _91536 t f g y) = (term74 _91535 _91536 t f g y).
Proof. exact (eq_refl (term74 _91535 _91536 t f g y)). Qed.
Lemma lem3568878 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term75 _91535 _91536 t f g) = (term75 _91535 _91536 t f g).
Proof. exact (fun_ext (fun y : _91535 => @lem3568877 _91535 _91536 t f g y)). Qed.
Lemma lem3568879 {_91535 : Type'} : (@all _91535) = (@all _91535).
Proof. exact (eq_refl (@all _91535)). Qed.
Lemma lem3568880 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term76 _91535 _91536 t f g) = (term76 _91535 _91536 t f g).
Proof. exact (MK_COMB (@lem3568879 _91535) (@lem3568878 _91535 _91536 t f g)). Qed.
Lemma lem3568881 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3568882 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term77 _91535 _91536 t f g) = (term77 _91535 _91536 t f g).
Proof. exact (MK_COMB (@lem3568881) (@lem3568880 _91535 _91536 t f g)). Qed.
Lemma lem3568883 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term78 _91535 _91536 t s g f) = (term78 _91535 _91536 t s g f).
Proof. exact (MK_COMB (@lem3568882 _91535 _91536 t f g) (@lem3568872 _91535 _91536 s g f)). Qed.
Lemma lem3568888 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (y : _91535) (s : _91536 -> Prop) : (term79 _91535 _91536 t g y s) = (term79 _91535 _91536 t g y s).
Proof. exact (eq_refl (term79 _91535 _91536 t g y s)). Qed.
Lemma lem3568889 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (s : _91536 -> Prop) : (term80 _91535 _91536 t g s) = (term80 _91535 _91536 t g s).
Proof. exact (fun_ext (fun y : _91535 => @lem3568888 _91535 _91536 t g y s)). Qed.
Lemma lem3568890 {_91535 : Type'} : (@all _91535) = (@all _91535).
Proof. exact (eq_refl (@all _91535)). Qed.
Lemma lem3568891 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (s : _91536 -> Prop) : (term81 _91535 _91536 t g s) = (term81 _91535 _91536 t g s).
Proof. exact (MK_COMB (@lem3568890 _91535) (@lem3568889 _91535 _91536 t g s)). Qed.
Lemma lem3568892 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3568893 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (s : _91536 -> Prop) : (term82 _91535 _91536 t g s) = (term82 _91535 _91536 t g s).
Proof. exact (MK_COMB (@lem3568892) (@lem3568891 _91535 _91536 t g s)). Qed.
Lemma lem3568894 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term83 _91535 _91536 t s g f) = (term83 _91535 _91536 t s g f).
Proof. exact (MK_COMB (@lem3568893 _91535 _91536 t g s) (@lem3568883 _91535 _91536 t s g f)). Qed.
Lemma lem3568895 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3568896 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term366 _91535 _91536 t s g f) = (term366 _91535 _91536 t s g f).
Proof. exact (MK_COMB (@lem3568895) (@lem3568894 _91535 _91536 t s g f)). Qed.
Lemma lem3568897 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term341 _91535 _91536 t s f g) = (term341 _91535 _91536 t s f g).
Proof. exact (MK_COMB (@lem3568896 _91535 _91536 t s g f) (@lem3568864 _91535 _91536 t s f g)). Qed.
Lemma lem3568902 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (x : _91536) (t : _91535 -> Prop) : (term88 _91535 _91536 s f x t) = (term88 _91535 _91536 s f x t).
Proof. exact (eq_refl (term88 _91535 _91536 s f x t)). Qed.
Lemma lem3568903 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (t : _91535 -> Prop) : (term89 _91535 _91536 s f t) = (term89 _91535 _91536 s f t).
Proof. exact (fun_ext (fun x : _91536 => @lem3568902 _91535 _91536 s f x t)). Qed.
Lemma lem3568904 {_91536 : Type'} : (@all _91536) = (@all _91536).
Proof. exact (eq_refl (@all _91536)). Qed.
Lemma lem3568905 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (t : _91535 -> Prop) : (term15 _91535 _91536 s f t) = (term15 _91535 _91536 s f t).
Proof. exact (MK_COMB (@lem3568904 _91536) (@lem3568903 _91535 _91536 s f t)). Qed.
Lemma lem3568906 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3568907 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (t : _91535 -> Prop) : (term53 _91535 _91536 s f t) = (term53 _91535 _91536 s f t).
Proof. exact (MK_COMB (@lem3568906) (@lem3568905 _91535 _91536 s f t)). Qed.
Lemma lem3568908 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term349 _91535 _91536 t s f g) = (term349 _91535 _91536 t s f g).
Proof. exact (MK_COMB (@lem3568907 _91535 _91536 s f t) (@lem3568897 _91535 _91536 t s f g)). Qed.
Lemma lem3568909 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term351 _91535 _91536 s f g) = (term351 _91535 _91536 s f g).
Proof. exact (fun_ext (fun t : _91535 -> Prop => @lem3568908 _91535 _91536 t s f g)). Qed.
Lemma lem3568910 {_91535 : Type'} : (@all (_91535 -> Prop)) = (@all (_91535 -> Prop)).
Proof. exact (eq_refl (@all (_91535 -> Prop))). Qed.
Lemma lem3568911 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term353 _91535 _91536 s f g) = (term353 _91535 _91536 s f g).
Proof. exact (MK_COMB (@lem3568910 _91535) (@lem3568909 _91535 _91536 s f g)). Qed.
Lemma lem3568912 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) : (term355 _91535 _91536 f g) = (term355 _91535 _91536 f g).
Proof. exact (fun_ext (fun s : _91536 -> Prop => @lem3568911 _91535 _91536 s f g)). Qed.
Lemma lem3568913 {_91536 : Type'} : (@all (_91536 -> Prop)) = (@all (_91536 -> Prop)).
Proof. exact (eq_refl (@all (_91536 -> Prop))). Qed.
Lemma lem3568914 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) : (term357 _91535 _91536 f g) = (term357 _91535 _91536 f g).
Proof. exact (MK_COMB (@lem3568913 _91536) (@lem3568912 _91535 _91536 f g)). Qed.
Lemma lem3568915 {_91535 _91536 : Type'} (g : _91535 -> _91536) : (term359 _91535 _91536 g) = (term359 _91535 _91536 g).
Proof. exact (fun_ext (fun f : _91536 -> _91535 => @lem3568914 _91535 _91536 f g)). Qed.
Lemma lem3568916 {_91535 _91536 : Type'} : (@all (_91536 -> _91535)) = (@all (_91536 -> _91535)).
Proof. exact (eq_refl (@all (_91536 -> _91535))). Qed.
Lemma lem3568917 {_91535 _91536 : Type'} (g : _91535 -> _91536) : (term361 _91535 _91536 g) = (term361 _91535 _91536 g).
Proof. exact (MK_COMB (@lem3568916 _91535 _91536) (@lem3568915 _91535 _91536 g)). Qed.
Lemma lem3568918 {_91535 _91536 : Type'} : (term363 _91535 _91536) = (term363 _91535 _91536).
Proof. exact (fun_ext (fun g : _91535 -> _91536 => @lem3568917 _91535 _91536 g)). Qed.
Lemma lem3568919 {_91535 _91536 : Type'} : (@all (_91535 -> _91536)) = (@all (_91535 -> _91536)).
Proof. exact (eq_refl (@all (_91535 -> _91536))). Qed.
Lemma lem3568920 {_91535 _91536 : Type'} : (term365 _91535 _91536) = (term365 _91535 _91536).
Proof. exact (MK_COMB (@lem3568919 _91535 _91536) (@lem3568918 _91535 _91536)). Qed.
Lemma lem3569013 {_91535 _91536 : Type'} : (term364 _91535 _91536) = (term365 _91535 _91536).
Proof. exact (TRANS (@lem3568838 _91535 _91536) (@lem3568920 _91535 _91536)). Qed.
Lemma lem3569014 {_91535 _91536 : Type'} : (term365 _91535 _91536) = (term364 _91535 _91536).
Proof. exact (SYM (@lem3569013 _91535 _91536)). Qed.
Lemma lem3569016 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term83 _91535 _91536 t s g f) : term83 _91535 _91536 t s g f.
Proof. exact (h1). Qed.
Lemma lem3569018 (p : Prop) : p = (term43 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3569019 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term38 _91535 _91536 t s f g) = (term367 _91535 _91536 t s f g).
Proof. exact (@lem3569018 (term38 _91535 _91536 t s f g)). Qed.
Lemma lem3569020 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term367 _91535 _91536 t s f g) = (term38 _91535 _91536 t s f g).
Proof. exact (SYM (@lem3569019 _91535 _91536 t s f g)). Qed.
Lemma lem3569021 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term368 _91535 _91536 t s f g) : term368 _91535 _91536 t s f g.
Proof. exact (h1). Qed.
Lemma lem3569091 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (y : _91535) (s : _91536 -> Prop) : (term79 _91535 _91536 t g y s) = (term243 _91535 _91536 t g y s).
Proof. exact (@lem17265 (@IN _91535 y t) (term129 _91535 _91536 g y s)). Qed.
Lemma lem3569092 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (s : _91536 -> Prop) : (term80 _91535 _91536 t g s) = (term369 _91535 _91536 t g s).
Proof. exact (fun_ext (fun y : _91535 => @lem3569091 _91535 _91536 t g y s)). Qed.
Lemma lem3569093 {_91535 : Type'} : (@all _91535) = (@all _91535).
Proof. exact (eq_refl (@all _91535)). Qed.
Lemma lem3569094 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (s : _91536 -> Prop) : (term81 _91535 _91536 t g s) = (term370 _91535 _91536 t g s).
Proof. exact (MK_COMB (@lem3569093 _91535) (@lem3569092 _91535 _91536 t g s)). Qed.
Lemma lem3569101 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : (term74 _91535 _91536 t f g y) = (term245 _91535 _91536 t f g y).
Proof. exact (@lem17265 (@IN _91535 y t) ((term141 _91535 _91536 f g y) = y)). Qed.
Lemma lem3569102 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term75 _91535 _91536 t f g) = (term371 _91535 _91536 t f g).
Proof. exact (fun_ext (fun y : _91535 => @lem3569101 _91535 _91536 t f g y)). Qed.
Lemma lem3569103 {_91535 : Type'} : (@all _91535) = (@all _91535).
Proof. exact (eq_refl (@all _91535)). Qed.
Lemma lem3569104 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term76 _91535 _91536 t f g) = (term372 _91535 _91536 t f g).
Proof. exact (MK_COMB (@lem3569103 _91535) (@lem3569102 _91535 _91536 t f g)). Qed.
Lemma lem3569111 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : (term71 _91535 _91536 s g f x) = (term96 _91535 _91536 s g f x).
Proof. exact (@lem17265 (@IN _91536 x s) ((term97 _91535 _91536 g f x) = x)). Qed.
Lemma lem3569112 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term72 _91535 _91536 s g f) = (term98 _91535 _91536 s g f).
Proof. exact (fun_ext (fun x : _91536 => @lem3569111 _91535 _91536 s g f x)). Qed.
Lemma lem3569113 {_91536 : Type'} : (@all _91536) = (@all _91536).
Proof. exact (eq_refl (@all _91536)). Qed.
Lemma lem3569114 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term73 _91535 _91536 s g f) = (term99 _91535 _91536 s g f).
Proof. exact (MK_COMB (@lem3569113 _91536) (@lem3569112 _91535 _91536 s g f)). Qed.
Lemma lem3569115 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3569116 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term77 _91535 _91536 t f g) = (term373 _91535 _91536 t f g).
Proof. exact (MK_COMB (@lem3569115) (@lem3569104 _91535 _91536 t f g)). Qed.
Lemma lem3569117 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term78 _91535 _91536 t s g f) = (term374 _91535 _91536 t s g f).
Proof. exact (MK_COMB (@lem3569116 _91535 _91536 t f g) (@lem3569114 _91535 _91536 s g f)). Qed.
Lemma lem3569118 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3569119 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (s : _91536 -> Prop) : (term82 _91535 _91536 t g s) = (term375 _91535 _91536 t g s).
Proof. exact (MK_COMB (@lem3569118) (@lem3569094 _91535 _91536 t g s)). Qed.
Lemma lem3569268 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term83 _91535 _91536 t s g f) = (term376 _91535 _91536 t s g f).
Proof. exact (MK_COMB (@lem3569119 _91535 _91536 t g s) (@lem3569117 _91535 _91536 t s g f)). Qed.
Lemma lem3569269 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term83 _91535 _91536 t s g f) : term376 _91535 _91536 t s g f.
Proof. exact (EQ_MP (@lem3569268 _91535 _91536 t s g f) (@lem3569016 _91535 _91536 t s g f h1)). Qed.
Lemma lem3569276 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : (term149 _91535 _91536 s g f x) = (term150 _91535 _91536 s g f x).
Proof. exact (@lem17362 (@IN _91536 x s) ((term97 _91535 _91536 g f x) = x)). Qed.
Lemma lem3569277 {_91536 : Type'} (P : _91536 -> Prop) : (term130 _91536 P) = (term131 _91536 P).
Proof. exact (@lem18392 _91536 P). Qed.
Lemma lem3569278 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term151 _91535 _91536 s g f) = (term152 _91535 _91536 s g f).
Proof. exact (@lem3569277 _91536 (term72 _91535 _91536 s g f)). Qed.
Lemma lem3569279 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : (term153 _91535 _91536 s g f x) = (term71 _91535 _91536 s g f x).
Proof. exact (eq_refl (term153 _91535 _91536 s g f x)). Qed.
Lemma lem3569280 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3569281 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : (term154 _91535 _91536 s g f x) = (term149 _91535 _91536 s g f x).
Proof. exact (MK_COMB (@lem3569280) (@lem3569279 _91535 _91536 s g f x)). Qed.
Lemma lem3569282 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : (term154 _91535 _91536 s g f x) = (term150 _91535 _91536 s g f x).
Proof. exact (TRANS (@lem3569281 _91535 _91536 s g f x) (@lem3569276 _91535 _91536 s g f x)). Qed.
Lemma lem3569283 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term155 _91535 _91536 s g f) = (term156 _91535 _91536 s g f).
Proof. exact (fun_ext (fun x : _91536 => @lem3569282 _91535 _91536 s g f x)). Qed.
Lemma lem3569284 {_91536 : Type'} : (@ex _91536) = (@ex _91536).
Proof. exact (eq_refl (@ex _91536)). Qed.
Lemma lem3569285 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term152 _91535 _91536 s g f) = (term157 _91535 _91536 s g f).
Proof. exact (MK_COMB (@lem3569284 _91536) (@lem3569283 _91535 _91536 s g f)). Qed.
Lemma lem3569286 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term151 _91535 _91536 s g f) = (term157 _91535 _91536 s g f).
Proof. exact (TRANS (@lem3569278 _91535 _91536 s g f) (@lem3569285 _91535 _91536 s g f)). Qed.
Lemma lem3569287 {_91535 _91536 : Type'} (P : type572 _91535 _91536) : (term377 _91535 _91536 P) = (term378 _91535 _91536 P).
Proof. exact (@lem18394 (_91535 -> _91536) P). Qed.
Lemma lem3569288 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) : (term379 _91535 _91536 s f) = (term380 _91535 _91536 s f).
Proof. exact (@lem3569287 _91535 _91536 (term86 _91535 _91536 s f)). Qed.
Lemma lem3569289 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term381 _91535 _91536 s f g) = (term73 _91535 _91536 s g f).
Proof. exact (eq_refl (term381 _91535 _91536 s f g)). Qed.
Lemma lem3569290 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3569291 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term382 _91535 _91536 s f g) = (term151 _91535 _91536 s g f).
Proof. exact (MK_COMB (@lem3569290) (@lem3569289 _91535 _91536 s g f)). Qed.
Lemma lem3569292 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term382 _91535 _91536 s f g) = (term157 _91535 _91536 s g f).
Proof. exact (TRANS (@lem3569291 _91535 _91536 s g f) (@lem3569286 _91535 _91536 s g f)). Qed.
Lemma lem3569293 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) : (term383 _91535 _91536 s f) = (term384 _91535 _91536 s f).
Proof. exact (fun_ext (fun g : _91535 -> _91536 => @lem3569292 _91535 _91536 s g f)). Qed.
Lemma lem3569294 {_91535 _91536 : Type'} : (@all (_91535 -> _91536)) = (@all (_91535 -> _91536)).
Proof. exact (eq_refl (@all (_91535 -> _91536))). Qed.
Lemma lem3569295 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) : (term380 _91535 _91536 s f) = (term385 _91535 _91536 s f).
Proof. exact (MK_COMB (@lem3569294 _91535 _91536) (@lem3569293 _91535 _91536 s f)). Qed.
Lemma lem3569296 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) : (term379 _91535 _91536 s f) = (term385 _91535 _91536 s f).
Proof. exact (TRANS (@lem3569288 _91535 _91536 s f) (@lem3569295 _91535 _91536 s f)). Qed.
Lemma lem3569304 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : (term386 _91535 _91536 s f g y) = (term387 _91535 _91536 s f g y).
Proof. exact (@lem17045 (term129 _91535 _91536 g y s) ((term141 _91535 _91536 f g y) = y)). Qed.
Lemma lem3569306 {_91535 : Type'} (y : _91535) (t : _91535 -> Prop) : (term388 _91535 y t) = (term388 _91535 y t).
Proof. exact (eq_refl (term388 _91535 y t)). Qed.
Lemma lem3569307 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : (term389 _91535 _91536 t s f g y) = (term390 _91535 _91536 t s f g y).
Proof. exact (MK_COMB (@lem3569306 _91535 y t) (@lem3569304 _91535 _91536 s f g y)). Qed.
Lemma lem3569308 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : (term391 _91535 _91536 t s f g y) = (term389 _91535 _91536 t s f g y).
Proof. exact (@lem17362 (@IN _91535 y t) (term103 _91535 _91536 s f g y)). Qed.
Lemma lem3569309 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : (term391 _91535 _91536 t s f g y) = (term390 _91535 _91536 t s f g y).
Proof. exact (TRANS (@lem3569308 _91535 _91536 t s f g y) (@lem3569307 _91535 _91536 t s f g y)). Qed.
Lemma lem3569310 {_91535 : Type'} (P : _91535 -> Prop) : (term130 _91535 P) = (term131 _91535 P).
Proof. exact (@lem18392 _91535 P). Qed.
Lemma lem3569311 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term392 _91535 _91536 t s f g) = (term393 _91535 _91536 t s f g).
Proof. exact (@lem3569310 _91535 (term85 _91535 _91536 t s f g)). Qed.
Lemma lem3569312 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : (term394 _91535 _91536 t s f g y) = (term84 _91535 _91536 t s f g y).
Proof. exact (eq_refl (term394 _91535 _91536 t s f g y)). Qed.
Lemma lem3569313 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3569314 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : (term395 _91535 _91536 t s f g y) = (term391 _91535 _91536 t s f g y).
Proof. exact (MK_COMB (@lem3569313) (@lem3569312 _91535 _91536 t s f g y)). Qed.
Lemma lem3569315 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : (term395 _91535 _91536 t s f g y) = (term390 _91535 _91536 t s f g y).
Proof. exact (TRANS (@lem3569314 _91535 _91536 t s f g y) (@lem3569309 _91535 _91536 t s f g y)). Qed.
Lemma lem3569316 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term396 _91535 _91536 t s f g) = (term397 _91535 _91536 t s f g).
Proof. exact (fun_ext (fun y : _91535 => @lem3569315 _91535 _91536 t s f g y)). Qed.
Lemma lem3569317 {_91535 : Type'} : (@ex _91535) = (@ex _91535).
Proof. exact (eq_refl (@ex _91535)). Qed.
Lemma lem3569318 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term393 _91535 _91536 t s f g) = (term398 _91535 _91536 t s f g).
Proof. exact (MK_COMB (@lem3569317 _91535) (@lem3569316 _91535 _91536 t s f g)). Qed.
Lemma lem3569319 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term392 _91535 _91536 t s f g) = (term398 _91535 _91536 t s f g).
Proof. exact (TRANS (@lem3569311 _91535 _91536 t s f g) (@lem3569318 _91535 _91536 t s f g)). Qed.
Lemma lem3569320 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3569321 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) : (term399 _91535 _91536 s f) = (term400 _91535 _91536 s f).
Proof. exact (MK_COMB (@lem3569320) (@lem3569296 _91535 _91536 s f)). Qed.
Lemma lem3569322 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term401 _91535 _91536 t s f g) = (term402 _91535 _91536 t s f g).
Proof. exact (MK_COMB (@lem3569321 _91535 _91536 s f) (@lem3569319 _91535 _91536 t s f g)). Qed.
Lemma lem3569323 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term368 _91535 _91536 t s f g) = (term401 _91535 _91536 t s f g).
Proof. exact (@lem17045 (term17 _91535 _91536 s f) (term33 _91535 _91536 t s f g)). Qed.
Lemma lem3569324 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term368 _91535 _91536 t s f g) = (term402 _91535 _91536 t s f g).
Proof. exact (TRANS (@lem3569323 _91535 _91536 t s f g) (@lem3569322 _91535 _91536 t s f g)). Qed.
Lemma lem3569427 {A B : Type'} (P : type1413 A B) : (term403 A B P) = (term404 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3569428 {_91535 _91536 : Type'} (P : type552 _91535 _91536) : (term405 _91535 _91536 P) = (term406 _91535 _91536 P).
Proof. exact (@lem3569427 (_91535 -> _91536) _91536 P). Qed.
Lemma lem3569429 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) : (term407 _91535 _91536 s f) = (term408 _91535 _91536 s f).
Proof. exact (@lem3569428 _91535 _91536 (term409 _91535 _91536 s f)). Qed.
Lemma lem3569430 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term410 _91535 _91536 s f g) = (term156 _91535 _91536 s g f).
Proof. exact (eq_refl (term410 _91535 _91536 s f g)). Qed.
Lemma lem3569431 {_91536 : Type'} (x : _91536) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3569432 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : (term411 _91535 _91536 s f g x) = (term188 _91535 _91536 s g f x).
Proof. exact (MK_COMB (@lem3569430 _91535 _91536 s g f) (@lem3569431 _91536 x)). Qed.
Lemma lem3569433 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : (term188 _91535 _91536 s g f x) = (term150 _91535 _91536 s g f x).
Proof. exact (eq_refl (term188 _91535 _91536 s g f x)). Qed.
Lemma lem3569434 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : (term411 _91535 _91536 s f g x) = (term150 _91535 _91536 s g f x).
Proof. exact (TRANS (@lem3569432 _91535 _91536 s g f x) (@lem3569433 _91535 _91536 s g f x)). Qed.
Lemma lem3569435 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term412 _91535 _91536 s f g) = (term156 _91535 _91536 s g f).
Proof. exact (fun_ext (fun x : _91536 => @lem3569434 _91535 _91536 s g f x)). Qed.
Lemma lem3569436 {_91536 : Type'} : (@ex _91536) = (@ex _91536).
Proof. exact (eq_refl (@ex _91536)). Qed.
Lemma lem3569437 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term413 _91535 _91536 s f g) = (term157 _91535 _91536 s g f).
Proof. exact (MK_COMB (@lem3569436 _91536) (@lem3569435 _91535 _91536 s g f)). Qed.
Lemma lem3569438 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) : (term414 _91535 _91536 s f) = (term384 _91535 _91536 s f).
Proof. exact (fun_ext (fun g : _91535 -> _91536 => @lem3569437 _91535 _91536 s g f)). Qed.
Lemma lem3569439 {_91535 _91536 : Type'} : (@all (_91535 -> _91536)) = (@all (_91535 -> _91536)).
Proof. exact (eq_refl (@all (_91535 -> _91536))). Qed.
Lemma lem3569440 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) : (term407 _91535 _91536 s f) = (term385 _91535 _91536 s f).
Proof. exact (MK_COMB (@lem3569439 _91535 _91536) (@lem3569438 _91535 _91536 s f)). Qed.
Lemma lem3569441 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3569442 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) : (term415 _91535 _91536 s f) = (term416 _91535 _91536 s f).
Proof. exact (MK_COMB (@lem3569441) (@lem3569440 _91535 _91536 s f)). Qed.
Lemma lem3569443 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term410 _91535 _91536 s f g) = (term156 _91535 _91536 s g f).
Proof. exact (eq_refl (term410 _91535 _91536 s f g)). Qed.
Lemma lem3569444 {_91535 _91536 : Type'} (x : type570 _91535 _91536) (g : _91535 -> _91536) : (x g) = (x g).
Proof. exact (eq_refl (x g)). Qed.
Lemma lem3569445 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (x : type570 _91535 _91536) (g : _91535 -> _91536) : (term417 _91535 _91536 s f x g) = (term418 _91535 _91536 s f x g).
Proof. exact (MK_COMB (@lem3569443 _91535 _91536 s g f) (@lem3569444 _91535 _91536 x g)). Qed.
Lemma lem3569446 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (x : type570 _91535 _91536) (g : _91535 -> _91536) : (term418 _91535 _91536 s f x g) = (term419 _91535 _91536 s f x g).
Proof. exact (eq_refl (term418 _91535 _91536 s f x g)). Qed.
Lemma lem3569447 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (x : type570 _91535 _91536) (g : _91535 -> _91536) : (term417 _91535 _91536 s f x g) = (term419 _91535 _91536 s f x g).
Proof. exact (TRANS (@lem3569445 _91535 _91536 s f x g) (@lem3569446 _91535 _91536 s f x g)). Qed.
Lemma lem3569448 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (x : type570 _91535 _91536) : (term420 _91535 _91536 s f x) = (term421 _91535 _91536 s f x).
Proof. exact (fun_ext (fun g : _91535 -> _91536 => @lem3569447 _91535 _91536 s f x g)). Qed.
Lemma lem3569449 {_91535 _91536 : Type'} : (@all (_91535 -> _91536)) = (@all (_91535 -> _91536)).
Proof. exact (eq_refl (@all (_91535 -> _91536))). Qed.
Lemma lem3569450 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (x : type570 _91535 _91536) : (term422 _91535 _91536 s f x) = (term423 _91535 _91536 s f x).
Proof. exact (MK_COMB (@lem3569449 _91535 _91536) (@lem3569448 _91535 _91536 s f x)). Qed.
Lemma lem3569451 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) : (term424 _91535 _91536 s f) = (term425 _91535 _91536 s f).
Proof. exact (fun_ext (fun x : type570 _91535 _91536 => @lem3569450 _91535 _91536 s f x)). Qed.
Lemma lem3569452 {_91535 _91536 : Type'} : (@ex ((_91535 -> _91536) -> _91536)) = (@ex ((_91535 -> _91536) -> _91536)).
Proof. exact (eq_refl (@ex ((_91535 -> _91536) -> _91536))). Qed.
Lemma lem3569453 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) : (term408 _91535 _91536 s f) = (term426 _91535 _91536 s f).
Proof. exact (MK_COMB (@lem3569452 _91535 _91536) (@lem3569451 _91535 _91536 s f)). Qed.
Lemma lem3569454 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) : ((term407 _91535 _91536 s f) = (term408 _91535 _91536 s f)) = ((term385 _91535 _91536 s f) = (term426 _91535 _91536 s f)).
Proof. exact (MK_COMB (@lem3569442 _91535 _91536 s f) (@lem3569453 _91535 _91536 s f)). Qed.
Lemma lem3569455 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) : (term385 _91535 _91536 s f) = (term426 _91535 _91536 s f).
Proof. exact (EQ_MP (@lem3569454 _91535 _91536 s f) (@lem3569429 _91535 _91536 s f)). Qed.
Lemma lem3569456 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3569457 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) : (term400 _91535 _91536 s f) = (term427 _91535 _91536 s f).
Proof. exact (MK_COMB (@lem3569456) (@lem3569455 _91535 _91536 s f)). Qed.
Lemma lem3569458 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term398 _91535 _91536 t s f g) = (term398 _91535 _91536 t s f g).
Proof. exact (eq_refl (term398 _91535 _91536 t s f g)). Qed.
Lemma lem3569459 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term402 _91535 _91536 t s f g) = (term428 _91535 _91536 t s f g).
Proof. exact (MK_COMB (@lem3569457 _91535 _91536 s f) (@lem3569458 _91535 _91536 t s f g)). Qed.
Lemma lem3569463 {A : Type'} (P : A -> Prop) (Q : Prop) : (term167 A P Q) = (term168 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3569464 {_91535 _91536 : Type'} (P : type119 _91535 _91536) (Q : Prop) : (term429 _91535 _91536 P Q) = (term430 _91535 _91536 P Q).
Proof. exact (@lem3569463 (type570 _91535 _91536) P Q). Qed.
Lemma lem3569465 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term431 _91535 _91536 t s f g) = (term432 _91535 _91536 t s f g).
Proof. exact (@lem3569464 _91535 _91536 (term425 _91535 _91536 s f) (term398 _91535 _91536 t s f g)). Qed.
Lemma lem3569466 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (x : type570 _91535 _91536) : (term433 _91535 _91536 s f x) = (term423 _91535 _91536 s f x).
Proof. exact (eq_refl (term433 _91535 _91536 s f x)). Qed.
Lemma lem3569467 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) : (term434 _91535 _91536 s f) = (term425 _91535 _91536 s f).
Proof. exact (fun_ext (fun x : type570 _91535 _91536 => @lem3569466 _91535 _91536 s f x)). Qed.
Lemma lem3569468 {_91535 _91536 : Type'} : (@ex ((_91535 -> _91536) -> _91536)) = (@ex ((_91535 -> _91536) -> _91536)).
Proof. exact (eq_refl (@ex ((_91535 -> _91536) -> _91536))). Qed.
Lemma lem3569469 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) : (term435 _91535 _91536 s f) = (term426 _91535 _91536 s f).
Proof. exact (MK_COMB (@lem3569468 _91535 _91536) (@lem3569467 _91535 _91536 s f)). Qed.
Lemma lem3569470 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3569471 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) : (term436 _91535 _91536 s f) = (term427 _91535 _91536 s f).
Proof. exact (MK_COMB (@lem3569470) (@lem3569469 _91535 _91536 s f)). Qed.
Lemma lem3569472 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term398 _91535 _91536 t s f g) = (term398 _91535 _91536 t s f g).
Proof. exact (eq_refl (term398 _91535 _91536 t s f g)). Qed.
Lemma lem3569473 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term431 _91535 _91536 t s f g) = (term428 _91535 _91536 t s f g).
Proof. exact (MK_COMB (@lem3569471 _91535 _91536 s f) (@lem3569472 _91535 _91536 t s f g)). Qed.
Lemma lem3569474 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3569475 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term437 _91535 _91536 t s f g) = (term438 _91535 _91536 t s f g).
Proof. exact (MK_COMB (@lem3569474) (@lem3569473 _91535 _91536 t s f g)). Qed.
Lemma lem3569476 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (x : type570 _91535 _91536) : (term433 _91535 _91536 s f x) = (term423 _91535 _91536 s f x).
Proof. exact (eq_refl (term433 _91535 _91536 s f x)). Qed.
Lemma lem3569477 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3569478 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (x : type570 _91535 _91536) : (term439 _91535 _91536 s f x) = (term440 _91535 _91536 s f x).
Proof. exact (MK_COMB (@lem3569477) (@lem3569476 _91535 _91536 s f x)). Qed.
Lemma lem3569479 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term398 _91535 _91536 t s f g) = (term398 _91535 _91536 t s f g).
Proof. exact (eq_refl (term398 _91535 _91536 t s f g)). Qed.
Lemma lem3569480 {_91535 _91536 : Type'} (x : type570 _91535 _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term441 _91535 _91536 x t s f g) = (term442 _91535 _91536 x t s f g).
Proof. exact (MK_COMB (@lem3569478 _91535 _91536 s f x) (@lem3569479 _91535 _91536 t s f g)). Qed.
Lemma lem3569481 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term443 _91535 _91536 t s f g) = (term444 _91535 _91536 t s f g).
Proof. exact (fun_ext (fun x : type570 _91535 _91536 => @lem3569480 _91535 _91536 x t s f g)). Qed.
Lemma lem3569482 {_91535 _91536 : Type'} : (@ex ((_91535 -> _91536) -> _91536)) = (@ex ((_91535 -> _91536) -> _91536)).
Proof. exact (eq_refl (@ex ((_91535 -> _91536) -> _91536))). Qed.
Lemma lem3569483 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term432 _91535 _91536 t s f g) = (term445 _91535 _91536 t s f g).
Proof. exact (MK_COMB (@lem3569482 _91535 _91536) (@lem3569481 _91535 _91536 t s f g)). Qed.
Lemma lem3569484 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : ((term431 _91535 _91536 t s f g) = (term432 _91535 _91536 t s f g)) = ((term428 _91535 _91536 t s f g) = (term445 _91535 _91536 t s f g)).
Proof. exact (MK_COMB (@lem3569475 _91535 _91536 t s f g) (@lem3569483 _91535 _91536 t s f g)). Qed.
Lemma lem3569485 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term428 _91535 _91536 t s f g) = (term445 _91535 _91536 t s f g).
Proof. exact (EQ_MP (@lem3569484 _91535 _91536 t s f g) (@lem3569465 _91535 _91536 t s f g)). Qed.
Lemma lem3569487 {A : Type'} (P : Prop) (Q : A -> Prop) : (term184 A P Q) = (term185 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3569488 {_91535 : Type'} (P : Prop) (Q : _91535 -> Prop) : (term184 _91535 P Q) = (term185 _91535 P Q).
Proof. exact (@lem3569487 _91535 P Q). Qed.
Lemma lem3569489 {_91535 _91536 : Type'} (x : type570 _91535 _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term446 _91535 _91536 x t s f g) = (term447 _91535 _91536 x t s f g).
Proof. exact (@lem3569488 _91535 (term423 _91535 _91536 s f x) (term397 _91535 _91536 t s f g)). Qed.
Lemma lem3569490 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : (term448 _91535 _91536 t s f g y) = (term390 _91535 _91536 t s f g y).
Proof. exact (eq_refl (term448 _91535 _91536 t s f g y)). Qed.
Lemma lem3569491 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term449 _91535 _91536 t s f g) = (term397 _91535 _91536 t s f g).
Proof. exact (fun_ext (fun y : _91535 => @lem3569490 _91535 _91536 t s f g y)). Qed.
Lemma lem3569492 {_91535 : Type'} : (@ex _91535) = (@ex _91535).
Proof. exact (eq_refl (@ex _91535)). Qed.
Lemma lem3569493 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term450 _91535 _91536 t s f g) = (term398 _91535 _91536 t s f g).
Proof. exact (MK_COMB (@lem3569492 _91535) (@lem3569491 _91535 _91536 t s f g)). Qed.
Lemma lem3569494 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (x : type570 _91535 _91536) : (term440 _91535 _91536 s f x) = (term440 _91535 _91536 s f x).
Proof. exact (eq_refl (term440 _91535 _91536 s f x)). Qed.
Lemma lem3569495 {_91535 _91536 : Type'} (x : type570 _91535 _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term446 _91535 _91536 x t s f g) = (term442 _91535 _91536 x t s f g).
Proof. exact (MK_COMB (@lem3569494 _91535 _91536 s f x) (@lem3569493 _91535 _91536 t s f g)). Qed.
Lemma lem3569496 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3569497 {_91535 _91536 : Type'} (x : type570 _91535 _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term451 _91535 _91536 x t s f g) = (term452 _91535 _91536 x t s f g).
Proof. exact (MK_COMB (@lem3569496) (@lem3569495 _91535 _91536 x t s f g)). Qed.
Lemma lem3569498 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : (term448 _91535 _91536 t s f g y) = (term390 _91535 _91536 t s f g y).
Proof. exact (eq_refl (term448 _91535 _91536 t s f g y)). Qed.
Lemma lem3569499 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (x : type570 _91535 _91536) : (term440 _91535 _91536 s f x) = (term440 _91535 _91536 s f x).
Proof. exact (eq_refl (term440 _91535 _91536 s f x)). Qed.
Lemma lem3569500 {_91535 _91536 : Type'} (x : type570 _91535 _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : (term453 _91535 _91536 x t s f g y) = (term454 _91535 _91536 x t s f g y).
Proof. exact (MK_COMB (@lem3569499 _91535 _91536 s f x) (@lem3569498 _91535 _91536 t s f g y)). Qed.
Lemma lem3569501 {_91535 _91536 : Type'} (x : type570 _91535 _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term455 _91535 _91536 x t s f g) = (term456 _91535 _91536 x t s f g).
Proof. exact (fun_ext (fun y : _91535 => @lem3569500 _91535 _91536 x t s f g y)). Qed.
Lemma lem3569502 {_91535 : Type'} : (@ex _91535) = (@ex _91535).
Proof. exact (eq_refl (@ex _91535)). Qed.
Lemma lem3569503 {_91535 _91536 : Type'} (x : type570 _91535 _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term447 _91535 _91536 x t s f g) = (term457 _91535 _91536 x t s f g).
Proof. exact (MK_COMB (@lem3569502 _91535) (@lem3569501 _91535 _91536 x t s f g)). Qed.
Lemma lem3569504 {_91535 _91536 : Type'} (x : type570 _91535 _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : ((term446 _91535 _91536 x t s f g) = (term447 _91535 _91536 x t s f g)) = ((term442 _91535 _91536 x t s f g) = (term457 _91535 _91536 x t s f g)).
Proof. exact (MK_COMB (@lem3569497 _91535 _91536 x t s f g) (@lem3569503 _91535 _91536 x t s f g)). Qed.
Lemma lem3569505 {_91535 _91536 : Type'} (x : type570 _91535 _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term442 _91535 _91536 x t s f g) = (term457 _91535 _91536 x t s f g).
Proof. exact (EQ_MP (@lem3569504 _91535 _91536 x t s f g) (@lem3569489 _91535 _91536 x t s f g)). Qed.
Lemma lem3569506 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term444 _91535 _91536 t s f g) = (term458 _91535 _91536 t s f g).
Proof. exact (fun_ext (fun x : type570 _91535 _91536 => @lem3569505 _91535 _91536 x t s f g)). Qed.
Lemma lem3569507 {_91535 _91536 : Type'} : (@ex ((_91535 -> _91536) -> _91536)) = (@ex ((_91535 -> _91536) -> _91536)).
Proof. exact (eq_refl (@ex ((_91535 -> _91536) -> _91536))). Qed.
Lemma lem3569508 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term445 _91535 _91536 t s f g) = (term459 _91535 _91536 t s f g).
Proof. exact (MK_COMB (@lem3569507 _91535 _91536) (@lem3569506 _91535 _91536 t s f g)). Qed.
Lemma lem3569509 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term428 _91535 _91536 t s f g) = (term459 _91535 _91536 t s f g).
Proof. exact (TRANS (@lem3569485 _91535 _91536 t s f g) (@lem3569508 _91535 _91536 t s f g)). Qed.
Lemma lem3569511 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term402 _91535 _91536 t s f g) = (term459 _91535 _91536 t s f g).
Proof. exact (TRANS (@lem3569459 _91535 _91536 t s f g) (@lem3569509 _91535 _91536 t s f g)). Qed.
Lemma lem3569512 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term368 _91535 _91536 t s f g) = (term459 _91535 _91536 t s f g).
Proof. exact (TRANS (@lem3569324 _91535 _91536 t s f g) (@lem3569511 _91535 _91536 t s f g)). Qed.
Lemma lem3569513 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term368 _91535 _91536 t s f g) : term459 _91535 _91536 t s f g.
Proof. exact (EQ_MP (@lem3569512 _91535 _91536 t s f g) (@lem3569021 _91535 _91536 t s f g h1)). Qed.
Lemma lem3569514 {_91535 _91536 : Type'} (x : type570 _91535 _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term457 _91535 _91536 x t s f g) : term457 _91535 _91536 x t s f g.
Proof. exact (h1). Qed.
Lemma lem3569515 {_91535 _91536 : Type'} (x : type570 _91535 _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term454 _91535 _91536 x t s f g y) : term454 _91535 _91536 x t s f g y.
Proof. exact (h1). Qed.
Lemma lem3569565 {_91536 : Type'} : (@eq _91536) = (@eq _91536).
Proof. exact (eq_refl (@eq _91536)). Qed.
Lemma lem3569566 {_91535 _91536 : Type'} (g : _91535 -> _91536) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem3569571 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3569573 {_91535 _91536 : Type'} (f : _91536 -> _91535) (x : _91536) : (f x) = (@I (_91536 -> _91535) f x).
Proof. exact (@lem3569571 _91536 _91535 f x). Qed.
Lemma lem3569574 {_91535 _91536 : Type'} (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : (term97 _91535 _91536 g f x) = (term460 _91535 _91536 g f x).
Proof. exact (MK_COMB (@lem3569566 _91535 _91536 g) (@lem3569573 _91535 _91536 f x)). Qed.
Lemma lem3569576 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3569577 {_91535 _91536 : Type'} (f : _91535 -> _91536) (x : _91535) : (f x) = (@I (_91535 -> _91536) f x).
Proof. exact (@lem3569576 _91535 _91536 f x). Qed.
Lemma lem3569578 {_91535 _91536 : Type'} (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : (term460 _91535 _91536 g f x) = (term461 _91535 _91536 g f x).
Proof. exact (@lem3569577 _91535 _91536 g (@I (_91536 -> _91535) f x)). Qed.
Lemma lem3569579 {_91535 _91536 : Type'} (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : (term97 _91535 _91536 g f x) = (term461 _91535 _91536 g f x).
Proof. exact (TRANS (@lem3569574 _91535 _91536 g f x) (@lem3569578 _91535 _91536 g f x)). Qed.
Lemma lem3569580 {_91536 : Type'} (x : _91536) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3569581 {_91535 _91536 : Type'} (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : (term462 _91535 _91536 g f x) = (term463 _91535 _91536 g f x).
Proof. exact (MK_COMB (@lem3569565 _91536) (@lem3569579 _91535 _91536 g f x)). Qed.
Lemma lem3569582 {_91535 _91536 : Type'} (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : ((term97 _91535 _91536 g f x) = x) = ((term461 _91535 _91536 g f x) = x).
Proof. exact (MK_COMB (@lem3569581 _91535 _91536 g f x) (@lem3569580 _91536 x)). Qed.
Lemma lem3569583 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3569590 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3569591 {_91536 : Type'} (f : type1364 _91536) (x : _91536) : (f x) = (@I (_91536 -> (_91536 -> Prop) -> Prop) f x).
Proof. exact (@lem3569590 _91536 (type686 _91536) f x). Qed.
Lemma lem3569592 {_91536 : Type'} (x : _91536) : (@IN _91536 x) = (@I (_91536 -> (_91536 -> Prop) -> Prop) (@IN _91536) x).
Proof. exact (@lem3569591 _91536 (@IN _91536) x). Qed.
Lemma lem3569593 {_91536 : Type'} (s : _91536 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3569594 {_91536 : Type'} (x : _91536) (s : _91536 -> Prop) : (@IN _91536 x s) = (@I (_91536 -> (_91536 -> Prop) -> Prop) (@IN _91536) x s).
Proof. exact (MK_COMB (@lem3569592 _91536 x) (@lem3569593 _91536 s)). Qed.
Lemma lem3569596 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3569597 {_91536 : Type'} (f : type686 _91536) (x : _91536 -> Prop) : (f x) = (@I ((_91536 -> Prop) -> Prop) f x).
Proof. exact (@lem3569596 (_91536 -> Prop) Prop f x). Qed.
Lemma lem3569598 {_91536 : Type'} (x : _91536) (s : _91536 -> Prop) : (@I (_91536 -> (_91536 -> Prop) -> Prop) (@IN _91536) x s) = (term464 _91536 x s).
Proof. exact (@lem3569597 _91536 (@I (_91536 -> (_91536 -> Prop) -> Prop) (@IN _91536) x) s). Qed.
Lemma lem3569600 {_91536 : Type'} (x : _91536) (s : _91536 -> Prop) : (@IN _91536 x s) = (term464 _91536 x s).
Proof. exact (TRANS (@lem3569594 _91536 x s) (@lem3569598 _91536 x s)). Qed.
Lemma lem3569601 {_91536 : Type'} (x : _91536) (s : _91536 -> Prop) : (term236 _91536 x s) = (term465 _91536 x s).
Proof. exact (MK_COMB (@lem3569583) (@lem3569600 _91536 x s)). Qed.
Lemma lem3569602 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3569603 {_91536 : Type'} (x : _91536) (s : _91536 -> Prop) : (term466 _91536 x s) = (term467 _91536 x s).
Proof. exact (MK_COMB (@lem3569602) (@lem3569601 _91536 x s)). Qed.
Lemma lem3569604 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : (term96 _91535 _91536 s g f x) = (term468 _91535 _91536 s g f x).
Proof. exact (MK_COMB (@lem3569603 _91536 x s) (@lem3569582 _91535 _91536 g f x)). Qed.
Lemma lem3569605 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term98 _91535 _91536 s g f) = (term469 _91535 _91536 s g f).
Proof. exact (fun_ext (fun x : _91536 => @lem3569604 _91535 _91536 s g f x)). Qed.
Lemma lem3569606 {_91536 : Type'} : (@all _91536) = (@all _91536).
Proof. exact (eq_refl (@all _91536)). Qed.
Lemma lem3569607 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term99 _91535 _91536 s g f) = (term470 _91535 _91536 s g f).
Proof. exact (MK_COMB (@lem3569606 _91536) (@lem3569605 _91535 _91536 s g f)). Qed.
Lemma lem3569608 {_91535 : Type'} : (@eq _91535) = (@eq _91535).
Proof. exact (eq_refl (@eq _91535)). Qed.
Lemma lem3569609 {_91535 _91536 : Type'} (f : _91536 -> _91535) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem3569614 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3569615 {_91535 _91536 : Type'} (f : _91535 -> _91536) (x : _91535) : (f x) = (@I (_91535 -> _91536) f x).
Proof. exact (@lem3569614 _91535 _91536 f x). Qed.
Lemma lem3569617 {_91535 _91536 : Type'} (g : _91535 -> _91536) (y : _91535) : (g y) = (@I (_91535 -> _91536) g y).
Proof. exact (@lem3569615 _91535 _91536 g y). Qed.
Lemma lem3569618 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : (term141 _91535 _91536 f g y) = (term471 _91535 _91536 f g y).
Proof. exact (MK_COMB (@lem3569609 _91535 _91536 f) (@lem3569617 _91535 _91536 g y)). Qed.
Lemma lem3569620 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3569621 {_91535 _91536 : Type'} (f : _91536 -> _91535) (x : _91536) : (f x) = (@I (_91536 -> _91535) f x).
Proof. exact (@lem3569620 _91536 _91535 f x). Qed.
Lemma lem3569622 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : (term471 _91535 _91536 f g y) = (term472 _91535 _91536 f g y).
Proof. exact (@lem3569621 _91535 _91536 f (@I (_91535 -> _91536) g y)). Qed.
Lemma lem3569623 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : (term141 _91535 _91536 f g y) = (term472 _91535 _91536 f g y).
Proof. exact (TRANS (@lem3569618 _91535 _91536 f g y) (@lem3569622 _91535 _91536 f g y)). Qed.
Lemma lem3569624 {_91535 : Type'} (y : _91535) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3569625 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : (term473 _91535 _91536 f g y) = (term474 _91535 _91536 f g y).
Proof. exact (MK_COMB (@lem3569608 _91535) (@lem3569623 _91535 _91536 f g y)). Qed.
Lemma lem3569626 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : ((term141 _91535 _91536 f g y) = y) = ((term472 _91535 _91536 f g y) = y).
Proof. exact (MK_COMB (@lem3569625 _91535 _91536 f g y) (@lem3569624 _91535 y)). Qed.
Lemma lem3569627 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3569634 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3569635 {_91535 : Type'} (f : type1364 _91535) (x : _91535) : (f x) = (@I (_91535 -> (_91535 -> Prop) -> Prop) f x).
Proof. exact (@lem3569634 _91535 (type686 _91535) f x). Qed.
Lemma lem3569636 {_91535 : Type'} (y : _91535) : (@IN _91535 y) = (@I (_91535 -> (_91535 -> Prop) -> Prop) (@IN _91535) y).
Proof. exact (@lem3569635 _91535 (@IN _91535) y). Qed.
Lemma lem3569637 {_91535 : Type'} (t : _91535 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3569638 {_91535 : Type'} (y : _91535) (t : _91535 -> Prop) : (@IN _91535 y t) = (@I (_91535 -> (_91535 -> Prop) -> Prop) (@IN _91535) y t).
Proof. exact (MK_COMB (@lem3569636 _91535 y) (@lem3569637 _91535 t)). Qed.
Lemma lem3569640 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3569641 {_91535 : Type'} (f : type686 _91535) (x : _91535 -> Prop) : (f x) = (@I ((_91535 -> Prop) -> Prop) f x).
Proof. exact (@lem3569640 (_91535 -> Prop) Prop f x). Qed.
Lemma lem3569642 {_91535 : Type'} (y : _91535) (t : _91535 -> Prop) : (@I (_91535 -> (_91535 -> Prop) -> Prop) (@IN _91535) y t) = (term464 _91535 y t).
Proof. exact (@lem3569641 _91535 (@I (_91535 -> (_91535 -> Prop) -> Prop) (@IN _91535) y) t). Qed.
Lemma lem3569644 {_91535 : Type'} (y : _91535) (t : _91535 -> Prop) : (@IN _91535 y t) = (term464 _91535 y t).
Proof. exact (TRANS (@lem3569638 _91535 y t) (@lem3569642 _91535 y t)). Qed.
Lemma lem3569645 {_91535 : Type'} (y : _91535) (t : _91535 -> Prop) : (term236 _91535 y t) = (term465 _91535 y t).
Proof. exact (MK_COMB (@lem3569627) (@lem3569644 _91535 y t)). Qed.
Lemma lem3569646 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3569647 {_91535 : Type'} (y : _91535) (t : _91535 -> Prop) : (term466 _91535 y t) = (term467 _91535 y t).
Proof. exact (MK_COMB (@lem3569646) (@lem3569645 _91535 y t)). Qed.
Lemma lem3569648 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : (term245 _91535 _91536 t f g y) = (term475 _91535 _91536 t f g y).
Proof. exact (MK_COMB (@lem3569647 _91535 y t) (@lem3569626 _91535 _91536 f g y)). Qed.
Lemma lem3569649 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term371 _91535 _91536 t f g) = (term476 _91535 _91536 t f g).
Proof. exact (fun_ext (fun y : _91535 => @lem3569648 _91535 _91536 t f g y)). Qed.
Lemma lem3569650 {_91535 : Type'} : (@all _91535) = (@all _91535).
Proof. exact (eq_refl (@all _91535)). Qed.
Lemma lem3569651 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term372 _91535 _91536 t f g) = (term477 _91535 _91536 t f g).
Proof. exact (MK_COMB (@lem3569650 _91535) (@lem3569649 _91535 _91536 t f g)). Qed.
Lemma lem3569652 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3569653 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term373 _91535 _91536 t f g) = (term478 _91535 _91536 t f g).
Proof. exact (MK_COMB (@lem3569652) (@lem3569651 _91535 _91536 t f g)). Qed.
Lemma lem3569654 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term374 _91535 _91536 t s g f) = (term479 _91535 _91536 t s g f).
Proof. exact (MK_COMB (@lem3569653 _91535 _91536 t f g) (@lem3569607 _91535 _91536 s g f)). Qed.
Lemma lem3569655 {_91536 : Type'} : (@IN _91536) = (@IN _91536).
Proof. exact (eq_refl (@IN _91536)). Qed.
Lemma lem3569660 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3569661 {_91535 _91536 : Type'} (f : _91535 -> _91536) (x : _91535) : (f x) = (@I (_91535 -> _91536) f x).
Proof. exact (@lem3569660 _91535 _91536 f x). Qed.
Lemma lem3569663 {_91535 _91536 : Type'} (g : _91535 -> _91536) (y : _91535) : (g y) = (@I (_91535 -> _91536) g y).
Proof. exact (@lem3569661 _91535 _91536 g y). Qed.
Lemma lem3569664 {_91536 : Type'} (s : _91536 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3569665 {_91535 _91536 : Type'} (g : _91535 -> _91536) (y : _91535) : (term480 _91535 _91536 g y) = (term481 _91535 _91536 g y).
Proof. exact (MK_COMB (@lem3569655 _91536) (@lem3569663 _91535 _91536 g y)). Qed.
Lemma lem3569666 {_91535 _91536 : Type'} (g : _91535 -> _91536) (y : _91535) (s : _91536 -> Prop) : (term129 _91535 _91536 g y s) = (term482 _91535 _91536 g y s).
Proof. exact (MK_COMB (@lem3569665 _91535 _91536 g y) (@lem3569664 _91536 s)). Qed.
Lemma lem3569668 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3569669 {_91536 : Type'} (f : type1364 _91536) (x : _91536) : (f x) = (@I (_91536 -> (_91536 -> Prop) -> Prop) f x).
Proof. exact (@lem3569668 _91536 (type686 _91536) f x). Qed.
Lemma lem3569670 {_91535 _91536 : Type'} (g : _91535 -> _91536) (y : _91535) : (term481 _91535 _91536 g y) = (term483 _91535 _91536 g y).
Proof. exact (@lem3569669 _91536 (@IN _91536) (@I (_91535 -> _91536) g y)). Qed.
Lemma lem3569671 {_91536 : Type'} (s : _91536 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3569672 {_91535 _91536 : Type'} (g : _91535 -> _91536) (y : _91535) (s : _91536 -> Prop) : (term482 _91535 _91536 g y s) = (term484 _91535 _91536 g y s).
Proof. exact (MK_COMB (@lem3569670 _91535 _91536 g y) (@lem3569671 _91536 s)). Qed.
Lemma lem3569674 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3569675 {_91536 : Type'} (f : type686 _91536) (x : _91536 -> Prop) : (f x) = (@I ((_91536 -> Prop) -> Prop) f x).
Proof. exact (@lem3569674 (_91536 -> Prop) Prop f x). Qed.
Lemma lem3569676 {_91535 _91536 : Type'} (g : _91535 -> _91536) (y : _91535) (s : _91536 -> Prop) : (term484 _91535 _91536 g y s) = (term485 _91535 _91536 g y s).
Proof. exact (@lem3569675 _91536 (term483 _91535 _91536 g y) s). Qed.
Lemma lem3569677 {_91535 _91536 : Type'} (g : _91535 -> _91536) (y : _91535) (s : _91536 -> Prop) : (term482 _91535 _91536 g y s) = (term485 _91535 _91536 g y s).
Proof. exact (TRANS (@lem3569672 _91535 _91536 g y s) (@lem3569676 _91535 _91536 g y s)). Qed.
Lemma lem3569678 {_91535 _91536 : Type'} (g : _91535 -> _91536) (y : _91535) (s : _91536 -> Prop) : (term129 _91535 _91536 g y s) = (term485 _91535 _91536 g y s).
Proof. exact (TRANS (@lem3569666 _91535 _91536 g y s) (@lem3569677 _91535 _91536 g y s)). Qed.
Lemma lem3569679 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3569686 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3569687 {_91535 : Type'} (f : type1364 _91535) (x : _91535) : (f x) = (@I (_91535 -> (_91535 -> Prop) -> Prop) f x).
Proof. exact (@lem3569686 _91535 (type686 _91535) f x). Qed.
Lemma lem3569688 {_91535 : Type'} (y : _91535) : (@IN _91535 y) = (@I (_91535 -> (_91535 -> Prop) -> Prop) (@IN _91535) y).
Proof. exact (@lem3569687 _91535 (@IN _91535) y). Qed.
Lemma lem3569689 {_91535 : Type'} (t : _91535 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3569690 {_91535 : Type'} (y : _91535) (t : _91535 -> Prop) : (@IN _91535 y t) = (@I (_91535 -> (_91535 -> Prop) -> Prop) (@IN _91535) y t).
Proof. exact (MK_COMB (@lem3569688 _91535 y) (@lem3569689 _91535 t)). Qed.
Lemma lem3569692 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3569693 {_91535 : Type'} (f : type686 _91535) (x : _91535 -> Prop) : (f x) = (@I ((_91535 -> Prop) -> Prop) f x).
Proof. exact (@lem3569692 (_91535 -> Prop) Prop f x). Qed.
Lemma lem3569694 {_91535 : Type'} (y : _91535) (t : _91535 -> Prop) : (@I (_91535 -> (_91535 -> Prop) -> Prop) (@IN _91535) y t) = (term464 _91535 y t).
Proof. exact (@lem3569693 _91535 (@I (_91535 -> (_91535 -> Prop) -> Prop) (@IN _91535) y) t). Qed.
Lemma lem3569696 {_91535 : Type'} (y : _91535) (t : _91535 -> Prop) : (@IN _91535 y t) = (term464 _91535 y t).
Proof. exact (TRANS (@lem3569690 _91535 y t) (@lem3569694 _91535 y t)). Qed.
Lemma lem3569697 {_91535 : Type'} (y : _91535) (t : _91535 -> Prop) : (term236 _91535 y t) = (term465 _91535 y t).
Proof. exact (MK_COMB (@lem3569679) (@lem3569696 _91535 y t)). Qed.
Lemma lem3569698 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3569699 {_91535 : Type'} (y : _91535) (t : _91535 -> Prop) : (term466 _91535 y t) = (term467 _91535 y t).
Proof. exact (MK_COMB (@lem3569698) (@lem3569697 _91535 y t)). Qed.
Lemma lem3569700 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (y : _91535) (s : _91536 -> Prop) : (term243 _91535 _91536 t g y s) = (term486 _91535 _91536 t g y s).
Proof. exact (MK_COMB (@lem3569699 _91535 y t) (@lem3569678 _91535 _91536 g y s)). Qed.
Lemma lem3569701 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (s : _91536 -> Prop) : (term369 _91535 _91536 t g s) = (term487 _91535 _91536 t g s).
Proof. exact (fun_ext (fun y : _91535 => @lem3569700 _91535 _91536 t g y s)). Qed.
Lemma lem3569702 {_91535 : Type'} : (@all _91535) = (@all _91535).
Proof. exact (eq_refl (@all _91535)). Qed.
Lemma lem3569703 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (s : _91536 -> Prop) : (term370 _91535 _91536 t g s) = (term488 _91535 _91536 t g s).
Proof. exact (MK_COMB (@lem3569702 _91535) (@lem3569701 _91535 _91536 t g s)). Qed.
Lemma lem3569704 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3569705 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (s : _91536 -> Prop) : (term375 _91535 _91536 t g s) = (term489 _91535 _91536 t g s).
Proof. exact (MK_COMB (@lem3569704) (@lem3569703 _91535 _91536 t g s)). Qed.
Lemma lem3569706 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term376 _91535 _91536 t s g f) = (term490 _91535 _91536 t s g f).
Proof. exact (MK_COMB (@lem3569705 _91535 _91536 t g s) (@lem3569654 _91535 _91536 t s g f)). Qed.
Lemma lem3569707 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term83 _91535 _91536 t s g f) : term490 _91535 _91536 t s g f.
Proof. exact (EQ_MP (@lem3569706 _91535 _91536 t s g f) (@lem3569269 _91535 _91536 t s g f h1)). Qed.
Lemma lem3569708 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3569709 {_91535 : Type'} : (@eq _91535) = (@eq _91535).
Proof. exact (eq_refl (@eq _91535)). Qed.
Lemma lem3569710 {_91535 _91536 : Type'} (f : _91536 -> _91535) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem3569715 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3569716 {_91535 _91536 : Type'} (f : _91535 -> _91536) (x : _91535) : (f x) = (@I (_91535 -> _91536) f x).
Proof. exact (@lem3569715 _91535 _91536 f x). Qed.
Lemma lem3569718 {_91535 _91536 : Type'} (g : _91535 -> _91536) (y : _91535) : (g y) = (@I (_91535 -> _91536) g y).
Proof. exact (@lem3569716 _91535 _91536 g y). Qed.
Lemma lem3569719 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : (term141 _91535 _91536 f g y) = (term471 _91535 _91536 f g y).
Proof. exact (MK_COMB (@lem3569710 _91535 _91536 f) (@lem3569718 _91535 _91536 g y)). Qed.
Lemma lem3569721 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3569722 {_91535 _91536 : Type'} (f : _91536 -> _91535) (x : _91536) : (f x) = (@I (_91536 -> _91535) f x).
Proof. exact (@lem3569721 _91536 _91535 f x). Qed.
Lemma lem3569723 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : (term471 _91535 _91536 f g y) = (term472 _91535 _91536 f g y).
Proof. exact (@lem3569722 _91535 _91536 f (@I (_91535 -> _91536) g y)). Qed.
Lemma lem3569724 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : (term141 _91535 _91536 f g y) = (term472 _91535 _91536 f g y).
Proof. exact (TRANS (@lem3569719 _91535 _91536 f g y) (@lem3569723 _91535 _91536 f g y)). Qed.
Lemma lem3569725 {_91535 : Type'} (y : _91535) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3569726 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : (term473 _91535 _91536 f g y) = (term474 _91535 _91536 f g y).
Proof. exact (MK_COMB (@lem3569709 _91535) (@lem3569724 _91535 _91536 f g y)). Qed.
Lemma lem3569727 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : ((term141 _91535 _91536 f g y) = y) = ((term472 _91535 _91536 f g y) = y).
Proof. exact (MK_COMB (@lem3569726 _91535 _91536 f g y) (@lem3569725 _91535 y)). Qed.
Lemma lem3569728 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : (term244 _91535 _91536 f g y) = (term491 _91535 _91536 f g y).
Proof. exact (MK_COMB (@lem3569708) (@lem3569727 _91535 _91536 f g y)). Qed.
Lemma lem3569729 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3569730 {_91536 : Type'} : (@IN _91536) = (@IN _91536).
Proof. exact (eq_refl (@IN _91536)). Qed.
Lemma lem3569735 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3569736 {_91535 _91536 : Type'} (f : _91535 -> _91536) (x : _91535) : (f x) = (@I (_91535 -> _91536) f x).
Proof. exact (@lem3569735 _91535 _91536 f x). Qed.
Lemma lem3569738 {_91535 _91536 : Type'} (g : _91535 -> _91536) (y : _91535) : (g y) = (@I (_91535 -> _91536) g y).
Proof. exact (@lem3569736 _91535 _91536 g y). Qed.
Lemma lem3569739 {_91536 : Type'} (s : _91536 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3569740 {_91535 _91536 : Type'} (g : _91535 -> _91536) (y : _91535) : (term480 _91535 _91536 g y) = (term481 _91535 _91536 g y).
Proof. exact (MK_COMB (@lem3569730 _91536) (@lem3569738 _91535 _91536 g y)). Qed.
Lemma lem3569741 {_91535 _91536 : Type'} (g : _91535 -> _91536) (y : _91535) (s : _91536 -> Prop) : (term129 _91535 _91536 g y s) = (term482 _91535 _91536 g y s).
Proof. exact (MK_COMB (@lem3569740 _91535 _91536 g y) (@lem3569739 _91536 s)). Qed.
Lemma lem3569743 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3569744 {_91536 : Type'} (f : type1364 _91536) (x : _91536) : (f x) = (@I (_91536 -> (_91536 -> Prop) -> Prop) f x).
Proof. exact (@lem3569743 _91536 (type686 _91536) f x). Qed.
Lemma lem3569745 {_91535 _91536 : Type'} (g : _91535 -> _91536) (y : _91535) : (term481 _91535 _91536 g y) = (term483 _91535 _91536 g y).
Proof. exact (@lem3569744 _91536 (@IN _91536) (@I (_91535 -> _91536) g y)). Qed.
Lemma lem3569746 {_91536 : Type'} (s : _91536 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3569747 {_91535 _91536 : Type'} (g : _91535 -> _91536) (y : _91535) (s : _91536 -> Prop) : (term482 _91535 _91536 g y s) = (term484 _91535 _91536 g y s).
Proof. exact (MK_COMB (@lem3569745 _91535 _91536 g y) (@lem3569746 _91536 s)). Qed.
Lemma lem3569749 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3569750 {_91536 : Type'} (f : type686 _91536) (x : _91536 -> Prop) : (f x) = (@I ((_91536 -> Prop) -> Prop) f x).
Proof. exact (@lem3569749 (_91536 -> Prop) Prop f x). Qed.
Lemma lem3569751 {_91535 _91536 : Type'} (g : _91535 -> _91536) (y : _91535) (s : _91536 -> Prop) : (term484 _91535 _91536 g y s) = (term485 _91535 _91536 g y s).
Proof. exact (@lem3569750 _91536 (term483 _91535 _91536 g y) s). Qed.
Lemma lem3569752 {_91535 _91536 : Type'} (g : _91535 -> _91536) (y : _91535) (s : _91536 -> Prop) : (term482 _91535 _91536 g y s) = (term485 _91535 _91536 g y s).
Proof. exact (TRANS (@lem3569747 _91535 _91536 g y s) (@lem3569751 _91535 _91536 g y s)). Qed.
Lemma lem3569753 {_91535 _91536 : Type'} (g : _91535 -> _91536) (y : _91535) (s : _91536 -> Prop) : (term129 _91535 _91536 g y s) = (term485 _91535 _91536 g y s).
Proof. exact (TRANS (@lem3569741 _91535 _91536 g y s) (@lem3569752 _91535 _91536 g y s)). Qed.
Lemma lem3569754 {_91535 _91536 : Type'} (g : _91535 -> _91536) (y : _91535) (s : _91536 -> Prop) : (term242 _91535 _91536 g y s) = (term492 _91535 _91536 g y s).
Proof. exact (MK_COMB (@lem3569729) (@lem3569753 _91535 _91536 g y s)). Qed.
Lemma lem3569755 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3569756 {_91535 _91536 : Type'} (g : _91535 -> _91536) (y : _91535) (s : _91536 -> Prop) : (term493 _91535 _91536 g y s) = (term494 _91535 _91536 g y s).
Proof. exact (MK_COMB (@lem3569755) (@lem3569754 _91535 _91536 g y s)). Qed.
Lemma lem3569757 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : (term387 _91535 _91536 s f g y) = (term495 _91535 _91536 s f g y).
Proof. exact (MK_COMB (@lem3569756 _91535 _91536 g y s) (@lem3569728 _91535 _91536 f g y)). Qed.
Lemma lem3569764 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3569765 {_91535 : Type'} (f : type1364 _91535) (x : _91535) : (f x) = (@I (_91535 -> (_91535 -> Prop) -> Prop) f x).
Proof. exact (@lem3569764 _91535 (type686 _91535) f x). Qed.
Lemma lem3569766 {_91535 : Type'} (y : _91535) : (@IN _91535 y) = (@I (_91535 -> (_91535 -> Prop) -> Prop) (@IN _91535) y).
Proof. exact (@lem3569765 _91535 (@IN _91535) y). Qed.
Lemma lem3569767 {_91535 : Type'} (t : _91535 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3569768 {_91535 : Type'} (y : _91535) (t : _91535 -> Prop) : (@IN _91535 y t) = (@I (_91535 -> (_91535 -> Prop) -> Prop) (@IN _91535) y t).
Proof. exact (MK_COMB (@lem3569766 _91535 y) (@lem3569767 _91535 t)). Qed.
Lemma lem3569770 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3569771 {_91535 : Type'} (f : type686 _91535) (x : _91535 -> Prop) : (f x) = (@I ((_91535 -> Prop) -> Prop) f x).
Proof. exact (@lem3569770 (_91535 -> Prop) Prop f x). Qed.
Lemma lem3569772 {_91535 : Type'} (y : _91535) (t : _91535 -> Prop) : (@I (_91535 -> (_91535 -> Prop) -> Prop) (@IN _91535) y t) = (term464 _91535 y t).
Proof. exact (@lem3569771 _91535 (@I (_91535 -> (_91535 -> Prop) -> Prop) (@IN _91535) y) t). Qed.
Lemma lem3569774 {_91535 : Type'} (y : _91535) (t : _91535 -> Prop) : (@IN _91535 y t) = (term464 _91535 y t).
Proof. exact (TRANS (@lem3569768 _91535 y t) (@lem3569772 _91535 y t)). Qed.
Lemma lem3569775 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3569776 {_91535 : Type'} (y : _91535) (t : _91535 -> Prop) : (term388 _91535 y t) = (term496 _91535 y t).
Proof. exact (MK_COMB (@lem3569775) (@lem3569774 _91535 y t)). Qed.
Lemma lem3569777 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : (term390 _91535 _91536 t s f g y) = (term497 _91535 _91536 t s f g y).
Proof. exact (MK_COMB (@lem3569776 _91535 y t) (@lem3569757 _91535 _91536 s f g y)). Qed.
Lemma lem3569778 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3569779 {_91536 : Type'} : (@eq _91536) = (@eq _91536).
Proof. exact (eq_refl (@eq _91536)). Qed.
Lemma lem3569780 {_91535 _91536 : Type'} (g : _91535 -> _91536) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem3569781 {_91535 _91536 : Type'} (f : _91536 -> _91535) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem3569786 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3569787 {_91535 _91536 : Type'} (f : type570 _91535 _91536) (x : _91535 -> _91536) : (f x) = (@I ((_91535 -> _91536) -> _91536) f x).
Proof. exact (@lem3569786 (_91535 -> _91536) _91536 f x). Qed.
Lemma lem3569789 {_91535 _91536 : Type'} (x : type570 _91535 _91536) (g : _91535 -> _91536) : (x g) = (@I ((_91535 -> _91536) -> _91536) x g).
Proof. exact (@lem3569787 _91535 _91536 x g). Qed.
Lemma lem3569790 {_91535 _91536 : Type'} (f : _91536 -> _91535) (x : type570 _91535 _91536) (g : _91535 -> _91536) : (term498 _91535 _91536 f x g) = (term499 _91535 _91536 f x g).
Proof. exact (MK_COMB (@lem3569781 _91535 _91536 f) (@lem3569789 _91535 _91536 x g)). Qed.
Lemma lem3569792 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3569793 {_91535 _91536 : Type'} (f : _91536 -> _91535) (x : _91536) : (f x) = (@I (_91536 -> _91535) f x).
Proof. exact (@lem3569792 _91536 _91535 f x). Qed.
Lemma lem3569794 {_91535 _91536 : Type'} (f : _91536 -> _91535) (x : type570 _91535 _91536) (g : _91535 -> _91536) : (term499 _91535 _91536 f x g) = (term500 _91535 _91536 f x g).
Proof. exact (@lem3569793 _91535 _91536 f (@I ((_91535 -> _91536) -> _91536) x g)). Qed.
Lemma lem3569795 {_91535 _91536 : Type'} (f : _91536 -> _91535) (x : type570 _91535 _91536) (g : _91535 -> _91536) : (term498 _91535 _91536 f x g) = (term500 _91535 _91536 f x g).
Proof. exact (TRANS (@lem3569790 _91535 _91536 f x g) (@lem3569794 _91535 _91536 f x g)). Qed.
Lemma lem3569796 {_91535 _91536 : Type'} (f : _91536 -> _91535) (x : type570 _91535 _91536) (g : _91535 -> _91536) : (term501 _91535 _91536 f x g) = (term502 _91535 _91536 f x g).
Proof. exact (MK_COMB (@lem3569780 _91535 _91536 g) (@lem3569795 _91535 _91536 f x g)). Qed.
Lemma lem3569798 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3569799 {_91535 _91536 : Type'} (f : _91535 -> _91536) (x : _91535) : (f x) = (@I (_91535 -> _91536) f x).
Proof. exact (@lem3569798 _91535 _91536 f x). Qed.
Lemma lem3569800 {_91535 _91536 : Type'} (f : _91536 -> _91535) (x : type570 _91535 _91536) (g : _91535 -> _91536) : (term502 _91535 _91536 f x g) = (term503 _91535 _91536 f x g).
Proof. exact (@lem3569799 _91535 _91536 g (term500 _91535 _91536 f x g)). Qed.
Lemma lem3569801 {_91535 _91536 : Type'} (f : _91536 -> _91535) (x : type570 _91535 _91536) (g : _91535 -> _91536) : (term501 _91535 _91536 f x g) = (term503 _91535 _91536 f x g).
Proof. exact (TRANS (@lem3569796 _91535 _91536 f x g) (@lem3569800 _91535 _91536 f x g)). Qed.
Lemma lem3569806 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3569807 {_91535 _91536 : Type'} (f : type570 _91535 _91536) (x : _91535 -> _91536) : (f x) = (@I ((_91535 -> _91536) -> _91536) f x).
Proof. exact (@lem3569806 (_91535 -> _91536) _91536 f x). Qed.
Lemma lem3569809 {_91535 _91536 : Type'} (x : type570 _91535 _91536) (g : _91535 -> _91536) : (x g) = (@I ((_91535 -> _91536) -> _91536) x g).
Proof. exact (@lem3569807 _91535 _91536 x g). Qed.
Lemma lem3569810 {_91535 _91536 : Type'} (f : _91536 -> _91535) (x : type570 _91535 _91536) (g : _91535 -> _91536) : (term504 _91535 _91536 f x g) = (term505 _91535 _91536 f x g).
Proof. exact (MK_COMB (@lem3569779 _91536) (@lem3569801 _91535 _91536 f x g)). Qed.
Lemma lem3569811 {_91535 _91536 : Type'} (f : _91536 -> _91535) (x : type570 _91535 _91536) (g : _91535 -> _91536) : ((term501 _91535 _91536 f x g) = (x g)) = ((term503 _91535 _91536 f x g) = (@I ((_91535 -> _91536) -> _91536) x g)).
Proof. exact (MK_COMB (@lem3569810 _91535 _91536 f x g) (@lem3569809 _91535 _91536 x g)). Qed.
Lemma lem3569812 {_91535 _91536 : Type'} (f : _91536 -> _91535) (x : type570 _91535 _91536) (g : _91535 -> _91536) : (term506 _91535 _91536 f x g) = (term507 _91535 _91536 f x g).
Proof. exact (MK_COMB (@lem3569778) (@lem3569811 _91535 _91536 f x g)). Qed.
Lemma lem3569813 {_91536 : Type'} : (@IN _91536) = (@IN _91536).
Proof. exact (eq_refl (@IN _91536)). Qed.
Lemma lem3569818 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3569819 {_91535 _91536 : Type'} (f : type570 _91535 _91536) (x : _91535 -> _91536) : (f x) = (@I ((_91535 -> _91536) -> _91536) f x).
Proof. exact (@lem3569818 (_91535 -> _91536) _91536 f x). Qed.
Lemma lem3569821 {_91535 _91536 : Type'} (x : type570 _91535 _91536) (g : _91535 -> _91536) : (x g) = (@I ((_91535 -> _91536) -> _91536) x g).
Proof. exact (@lem3569819 _91535 _91536 x g). Qed.
Lemma lem3569822 {_91536 : Type'} (s : _91536 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3569823 {_91535 _91536 : Type'} (x : type570 _91535 _91536) (g : _91535 -> _91536) : (term508 _91535 _91536 x g) = (term509 _91535 _91536 x g).
Proof. exact (MK_COMB (@lem3569813 _91536) (@lem3569821 _91535 _91536 x g)). Qed.
Lemma lem3569824 {_91535 _91536 : Type'} (x : type570 _91535 _91536) (g : _91535 -> _91536) (s : _91536 -> Prop) : (term510 _91535 _91536 x g s) = (term511 _91535 _91536 x g s).
Proof. exact (MK_COMB (@lem3569823 _91535 _91536 x g) (@lem3569822 _91536 s)). Qed.
Lemma lem3569826 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3569827 {_91536 : Type'} (f : type1364 _91536) (x : _91536) : (f x) = (@I (_91536 -> (_91536 -> Prop) -> Prop) f x).
Proof. exact (@lem3569826 _91536 (type686 _91536) f x). Qed.
Lemma lem3569828 {_91535 _91536 : Type'} (x : type570 _91535 _91536) (g : _91535 -> _91536) : (term509 _91535 _91536 x g) = (term512 _91535 _91536 x g).
Proof. exact (@lem3569827 _91536 (@IN _91536) (@I ((_91535 -> _91536) -> _91536) x g)). Qed.
Lemma lem3569829 {_91536 : Type'} (s : _91536 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3569830 {_91535 _91536 : Type'} (x : type570 _91535 _91536) (g : _91535 -> _91536) (s : _91536 -> Prop) : (term511 _91535 _91536 x g s) = (term513 _91535 _91536 x g s).
Proof. exact (MK_COMB (@lem3569828 _91535 _91536 x g) (@lem3569829 _91536 s)). Qed.
Lemma lem3569832 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3569833 {_91536 : Type'} (f : type686 _91536) (x : _91536 -> Prop) : (f x) = (@I ((_91536 -> Prop) -> Prop) f x).
Proof. exact (@lem3569832 (_91536 -> Prop) Prop f x). Qed.
Lemma lem3569834 {_91535 _91536 : Type'} (x : type570 _91535 _91536) (g : _91535 -> _91536) (s : _91536 -> Prop) : (term513 _91535 _91536 x g s) = (term514 _91535 _91536 x g s).
Proof. exact (@lem3569833 _91536 (term512 _91535 _91536 x g) s). Qed.
Lemma lem3569835 {_91535 _91536 : Type'} (x : type570 _91535 _91536) (g : _91535 -> _91536) (s : _91536 -> Prop) : (term511 _91535 _91536 x g s) = (term514 _91535 _91536 x g s).
Proof. exact (TRANS (@lem3569830 _91535 _91536 x g s) (@lem3569834 _91535 _91536 x g s)). Qed.
Lemma lem3569836 {_91535 _91536 : Type'} (x : type570 _91535 _91536) (g : _91535 -> _91536) (s : _91536 -> Prop) : (term510 _91535 _91536 x g s) = (term514 _91535 _91536 x g s).
Proof. exact (TRANS (@lem3569824 _91535 _91536 x g s) (@lem3569835 _91535 _91536 x g s)). Qed.
Lemma lem3569837 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3569838 {_91535 _91536 : Type'} (x : type570 _91535 _91536) (g : _91535 -> _91536) (s : _91536 -> Prop) : (term515 _91535 _91536 x g s) = (term516 _91535 _91536 x g s).
Proof. exact (MK_COMB (@lem3569837) (@lem3569836 _91535 _91536 x g s)). Qed.
Lemma lem3569839 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (x : type570 _91535 _91536) (g : _91535 -> _91536) : (term419 _91535 _91536 s f x g) = (term517 _91535 _91536 s f x g).
Proof. exact (MK_COMB (@lem3569838 _91535 _91536 x g s) (@lem3569812 _91535 _91536 f x g)). Qed.
Lemma lem3569840 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (x : type570 _91535 _91536) : (term421 _91535 _91536 s f x) = (term518 _91535 _91536 s f x).
Proof. exact (fun_ext (fun g : _91535 -> _91536 => @lem3569839 _91535 _91536 s f x g)). Qed.
Lemma lem3569841 {_91535 _91536 : Type'} : (@all (_91535 -> _91536)) = (@all (_91535 -> _91536)).
Proof. exact (eq_refl (@all (_91535 -> _91536))). Qed.
Lemma lem3569842 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (x : type570 _91535 _91536) : (term423 _91535 _91536 s f x) = (term519 _91535 _91536 s f x).
Proof. exact (MK_COMB (@lem3569841 _91535 _91536) (@lem3569840 _91535 _91536 s f x)). Qed.
Lemma lem3569843 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3569844 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (x : type570 _91535 _91536) : (term440 _91535 _91536 s f x) = (term520 _91535 _91536 s f x).
Proof. exact (MK_COMB (@lem3569843) (@lem3569842 _91535 _91536 s f x)). Qed.
Lemma lem3569845 {_91535 _91536 : Type'} (x : type570 _91535 _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : (term454 _91535 _91536 x t s f g y) = (term521 _91535 _91536 x t s f g y).
Proof. exact (MK_COMB (@lem3569844 _91535 _91536 s f x) (@lem3569777 _91535 _91536 t s f g y)). Qed.
Lemma lem3569846 {_91535 _91536 : Type'} (x : type570 _91535 _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term454 _91535 _91536 x t s f g y) : term521 _91535 _91536 x t s f g y.
Proof. exact (EQ_MP (@lem3569845 _91535 _91536 x t s f g y) (@lem3569515 _91535 _91536 x t s f g y h1)). Qed.
Lemma lem3569847 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term83 _91535 _91536 t s g f) : term479 _91535 _91536 t s g f.
Proof. exact (proj2 (@lem3569707 _91535 _91536 t s g f h1)). Qed.
Lemma lem3569848 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term83 _91535 _91536 t s g f) : term488 _91535 _91536 t g s.
Proof. exact (proj1 (@lem3569707 _91535 _91536 t s g f h1)). Qed.
Lemma lem3569849 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term83 _91535 _91536 t s g f) : term470 _91535 _91536 s g f.
Proof. exact (proj2 (@lem3569847 _91535 _91536 t s g f h1)). Qed.
Lemma lem3569850 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term83 _91535 _91536 t s g f) : term477 _91535 _91536 t f g.
Proof. exact (proj1 (@lem3569847 _91535 _91536 t s g f h1)). Qed.
Lemma lem3569851 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (x : type570 _91535 _91536) (h1 : term519 _91535 _91536 s f x) : term519 _91535 _91536 s f x.
Proof. exact (h1). Qed.
Lemma lem3569852 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term497 _91535 _91536 t s f g y) : term497 _91535 _91536 t s f g y.
Proof. exact (h1). Qed.
Lemma lem3569853 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term497 _91535 _91536 t s f g y) : term495 _91535 _91536 s f g y.
Proof. exact (proj2 (@lem3569852 _91535 _91536 t s f g y h1)). Qed.
Lemma lem3569903 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (x : _91536) : (term468 _91535 _91536 s g f x) = (term468 _91535 _91536 s g f x).
Proof. exact (eq_refl (term468 _91535 _91536 s g f x)). Qed.
Lemma lem3569904 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term469 _91535 _91536 s g f) = (term469 _91535 _91536 s g f).
Proof. exact (fun_ext (fun x : _91536 => @lem3569903 _91535 _91536 s g f x)). Qed.
Lemma lem3569905 {_91536 : Type'} : (@all _91536) = (@all _91536).
Proof. exact (eq_refl (@all _91536)). Qed.
Lemma lem3569907 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term470 _91535 _91536 s g f) = (term470 _91535 _91536 s g f).
Proof. exact (MK_COMB (@lem3569905 _91536) (@lem3569904 _91535 _91536 s g f)). Qed.
Lemma lem3569908 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term83 _91535 _91536 t s g f) : term470 _91535 _91536 s g f.
Proof. exact (EQ_MP (@lem3569907 _91535 _91536 s g f) (@lem3569849 _91535 _91536 t s g f h1)). Qed.
Lemma lem3569914 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (x : type570 _91535 _91536) (g : _91535 -> _91536) : (term517 _91535 _91536 s f x g) = (term517 _91535 _91536 s f x g).
Proof. exact (eq_refl (term517 _91535 _91536 s f x g)). Qed.
Lemma lem3569915 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (x : type570 _91535 _91536) : (term518 _91535 _91536 s f x) = (term518 _91535 _91536 s f x).
Proof. exact (fun_ext (fun g : _91535 -> _91536 => @lem3569914 _91535 _91536 s f x g)). Qed.
Lemma lem3569916 {_91535 _91536 : Type'} : (@all (_91535 -> _91536)) = (@all (_91535 -> _91536)).
Proof. exact (eq_refl (@all (_91535 -> _91536))). Qed.
Lemma lem3569918 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (x : type570 _91535 _91536) : (term519 _91535 _91536 s f x) = (term519 _91535 _91536 s f x).
Proof. exact (MK_COMB (@lem3569916 _91535 _91536) (@lem3569915 _91535 _91536 s f x)). Qed.
Lemma lem3569919 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (x : type570 _91535 _91536) (h1 : term519 _91535 _91536 s f x) : term519 _91535 _91536 s f x.
Proof. exact (EQ_MP (@lem3569918 _91535 _91536 s f x) (@lem3569851 _91535 _91536 s f x h1)). Qed.
Lemma lem3569940 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (y : _91535) (s : _91536 -> Prop) : (term486 _91535 _91536 t g y s) = (term486 _91535 _91536 t g y s).
Proof. exact (eq_refl (term486 _91535 _91536 t g y s)). Qed.
Lemma lem3569941 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (s : _91536 -> Prop) : (term487 _91535 _91536 t g s) = (term487 _91535 _91536 t g s).
Proof. exact (fun_ext (fun y : _91535 => @lem3569940 _91535 _91536 t g y s)). Qed.
Lemma lem3569942 {_91535 : Type'} : (@all _91535) = (@all _91535).
Proof. exact (eq_refl (@all _91535)). Qed.
Lemma lem3569944 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (s : _91536 -> Prop) : (term488 _91535 _91536 t g s) = (term488 _91535 _91536 t g s).
Proof. exact (MK_COMB (@lem3569942 _91535) (@lem3569941 _91535 _91536 t g s)). Qed.
Lemma lem3569945 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term83 _91535 _91536 t s g f) : term488 _91535 _91536 t g s.
Proof. exact (EQ_MP (@lem3569944 _91535 _91536 t g s) (@lem3569848 _91535 _91536 t s g f h1)). Qed.
Lemma lem3569979 {_91535 _91536 : Type'} (g : _91535 -> _91536) (y : _91535) (s : _91536 -> Prop) (h1 : term492 _91535 _91536 g y s) : term492 _91535 _91536 g y s.
Proof. exact (h1). Qed.
Lemma lem3570013 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : (term475 _91535 _91536 t f g y) = (term475 _91535 _91536 t f g y).
Proof. exact (eq_refl (term475 _91535 _91536 t f g y)). Qed.
Lemma lem3570014 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term476 _91535 _91536 t f g) = (term476 _91535 _91536 t f g).
Proof. exact (fun_ext (fun y : _91535 => @lem3570013 _91535 _91536 t f g y)). Qed.
Lemma lem3570015 {_91535 : Type'} : (@all _91535) = (@all _91535).
Proof. exact (eq_refl (@all _91535)). Qed.
Lemma lem3570017 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term477 _91535 _91536 t f g) = (term477 _91535 _91536 t f g).
Proof. exact (MK_COMB (@lem3570015 _91535) (@lem3570014 _91535 _91536 t f g)). Qed.
Lemma lem3570018 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term83 _91535 _91536 t s g f) : term477 _91535 _91536 t f g.
Proof. exact (EQ_MP (@lem3570017 _91535 _91536 t f g) (@lem3569850 _91535 _91536 t s g f h1)). Qed.
Lemma lem3570039 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term491 _91535 _91536 f g y) : term491 _91535 _91536 f g y.
Proof. exact (h1). Qed.
Lemma lem3570049 {_91535 _91536 : Type'} (_38333 : _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term83 _91535 _91536 t s g f) : term522 _91535 _91536 s g f _38333.
Proof. exact (@lem3569908 _91535 _91536 t s g f h1 _38333). Qed.
Lemma lem3570050 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (_38333 : _91536) : (term522 _91535 _91536 s g f _38333) = (term468 _91535 _91536 s g f _38333).
Proof. exact (eq_refl (term522 _91535 _91536 s g f _38333)). Qed.
Lemma lem3570052 {_91535 _91536 : Type'} (_38334 : _91535 -> _91536) (s : _91536 -> Prop) (f : _91536 -> _91535) (x : type570 _91535 _91536) (h1 : term519 _91535 _91536 s f x) : term523 _91535 _91536 s f x _38334.
Proof. exact (@lem3569919 _91535 _91536 s f x h1 _38334). Qed.
Lemma lem3570053 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (x : type570 _91535 _91536) (_38334 : _91535 -> _91536) : (term523 _91535 _91536 s f x _38334) = (term517 _91535 _91536 s f x _38334).
Proof. exact (eq_refl (term523 _91535 _91536 s f x _38334)). Qed.
Lemma lem3570054 {_91535 _91536 : Type'} (_38334 : _91535 -> _91536) (s : _91536 -> Prop) (f : _91536 -> _91535) (x : type570 _91535 _91536) (h1 : term519 _91535 _91536 s f x) : term517 _91535 _91536 s f x _38334.
Proof. exact (EQ_MP (@lem3570053 _91535 _91536 s f x _38334) (@lem3570052 _91535 _91536 _38334 s f x h1)). Qed.
Lemma lem3570058 {_91535 _91536 : Type'} (_38336 : _91535) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term83 _91535 _91536 t s g f) : term524 _91535 _91536 t g s _38336.
Proof. exact (@lem3569945 _91535 _91536 t s g f h1 _38336). Qed.
Lemma lem3570059 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (_38336 : _91535) (s : _91536 -> Prop) : (term524 _91535 _91536 t g s _38336) = (term486 _91535 _91536 t g _38336 s).
Proof. exact (eq_refl (term524 _91535 _91536 t g s _38336)). Qed.
Lemma lem3570073 {_91535 _91536 : Type'} (_38341 : _91535) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term83 _91535 _91536 t s g f) : term525 _91535 _91536 t f g _38341.
Proof. exact (@lem3570018 _91535 _91536 t s g f h1 _38341). Qed.
Lemma lem3570074 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (_38341 : _91535) : (term525 _91535 _91536 t f g _38341) = (term475 _91535 _91536 t f g _38341).
Proof. exact (eq_refl (term525 _91535 _91536 t f g _38341)). Qed.
Lemma lem3570104 {_91535 _91536 : Type'} (_38333 : _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term83 _91535 _91536 t s g f) : term468 _91535 _91536 s g f _38333.
Proof. exact (EQ_MP (@lem3570050 _91535 _91536 s g f _38333) (@lem3570049 _91535 _91536 _38333 t s g f h1)). Qed.
Lemma lem3570108 {_91535 _91536 : Type'} (_38334 : _91535 -> _91536) (s : _91536 -> Prop) (f : _91536 -> _91535) (x : type570 _91535 _91536) (h1 : term519 _91535 _91536 s f x) : term507 _91535 _91536 f x _38334.
Proof. exact (proj2 (@lem3570054 _91535 _91536 _38334 s f x h1)). Qed.
Lemma lem3570120 {_91535 _91536 : Type'} (_38336 : _91535) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term83 _91535 _91536 t s g f) : term486 _91535 _91536 t g _38336 s.
Proof. exact (EQ_MP (@lem3570059 _91535 _91536 t g _38336 s) (@lem3570058 _91535 _91536 _38336 t s g f h1)). Qed.
Lemma lem3570136 {_91535 _91536 : Type'} (g : _91535 -> _91536) (y : _91535) (s : _91536 -> Prop) (h1 : term492 _91535 _91536 g y s) : term492 _91535 _91536 g y s.
Proof. exact (h1). Qed.
Lemma lem3570154 {_91535 _91536 : Type'} (_38341 : _91535) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term83 _91535 _91536 t s g f) : term475 _91535 _91536 t f g _38341.
Proof. exact (EQ_MP (@lem3570074 _91535 _91536 t f g _38341) (@lem3570073 _91535 _91536 _38341 t s g f h1)). Qed.
Lemma lem3570164 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term491 _91535 _91536 f g y) : term491 _91535 _91536 f g y.
Proof. exact (h1). Qed.
Lemma lem3570301 {_91535 _91536 : Type'} (_38334 : _91535 -> _91536) (s : _91536 -> Prop) (f : _91536 -> _91535) (x : type570 _91535 _91536) (h1 : term519 _91535 _91536 s f x) : term514 _91535 _91536 x _38334 s.
Proof. exact (proj1 (@lem3570054 _91535 _91536 _38334 s f x h1)). Qed.
Lemma lem3570302 {_91535 _91536 : Type'} (_38334 : _91535 -> _91536) (s : _91536 -> Prop) (f : _91536 -> _91535) (x : type570 _91535 _91536) (h1 : term519 _91535 _91536 s f x) : term514 _91535 _91536 x _38334 s.
Proof. exact (@lem3570301 _91535 _91536 _38334 s f x h1). Qed.
Lemma lem3570303 {_91535 _91536 : Type'} (g : _91535 -> _91536) (s : _91536 -> Prop) (f : _91536 -> _91535) (x : type570 _91535 _91536) (h1 : term519 _91535 _91536 s f x) : term514 _91535 _91536 x g s.
Proof. exact (@lem3570302 _91535 _91536 g s f x h1). Qed.
Lemma lem3570304 {_91535 _91536 : Type'} (g : _91535 -> _91536) (s : _91536 -> Prop) (f : _91536 -> _91535) (x : type570 _91535 _91536) (h1 : term519 _91535 _91536 s f x) : term526 _91535 _91536 x g s.
Proof. exact (fun h0 : term527 _91535 _91536 x g s => @lem3570303 _91535 _91536 g s f x h1). Qed.
Lemma lem3570306 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3570307 {_91535 _91536 : Type'} (x : type570 _91535 _91536) (g : _91535 -> _91536) (s : _91536 -> Prop) : (term526 _91535 _91536 x g s) = (term514 _91535 _91536 x g s).
Proof. exact (@lem3570306 (term514 _91535 _91536 x g s)). Qed.
Lemma lem3570308 {_91535 _91536 : Type'} (g : _91535 -> _91536) (s : _91536 -> Prop) (f : _91536 -> _91535) (x : type570 _91535 _91536) (h1 : term519 _91535 _91536 s f x) : term514 _91535 _91536 x g s.
Proof. exact (EQ_MP (@lem3570307 _91535 _91536 x g s) (@lem3570304 _91535 _91536 g s f x h1)). Qed.
Lemma lem3570314 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3570315 {_91535 _91536 : Type'} (g : _91535 -> _91536) (f : _91536 -> _91535) (_38333 : _91536) (s : _91536 -> Prop) : (term468 _91535 _91536 s g f _38333) = (term528 _91535 _91536 g f _38333 s).
Proof. exact (@lem3570314 ((term461 _91535 _91536 g f _38333) = _38333) (term465 _91536 _38333 s)). Qed.
Lemma lem3570323 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3570324 {_91535 _91536 : Type'} (g : _91535 -> _91536) (f : _91536 -> _91535) (_38333 : _91536) (s : _91536 -> Prop) : (term529 _91535 _91536 s g f _38333) = (term530 _91535 _91536 g f _38333 s).
Proof. exact (MK_COMB (@lem3570323) (@lem3570315 _91535 _91536 g f _38333 s)). Qed.
Lemma lem3570332 {_91535 _91536 : Type'} (g : _91535 -> _91536) (f : _91536 -> _91535) (_38333 : _91536) (s : _91536 -> Prop) : (term528 _91535 _91536 g f _38333 s) = (term528 _91535 _91536 g f _38333 s).
Proof. exact (eq_refl (term528 _91535 _91536 g f _38333 s)). Qed.
Lemma lem3570333 {_91535 _91536 : Type'} (g : _91535 -> _91536) (f : _91536 -> _91535) (_38333 : _91536) (s : _91536 -> Prop) : ((term468 _91535 _91536 s g f _38333) = (term528 _91535 _91536 g f _38333 s)) = ((term528 _91535 _91536 g f _38333 s) = (term528 _91535 _91536 g f _38333 s)).
Proof. exact (MK_COMB (@lem3570324 _91535 _91536 g f _38333 s) (@lem3570332 _91535 _91536 g f _38333 s)). Qed.
Lemma lem3570335 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3570336 (x : Prop) : (x = x) = True.
Proof. exact (@lem3570335 Prop x). Qed.
Lemma lem3570337 {_91535 _91536 : Type'} (g : _91535 -> _91536) (f : _91536 -> _91535) (_38333 : _91536) (s : _91536 -> Prop) : ((term528 _91535 _91536 g f _38333 s) = (term528 _91535 _91536 g f _38333 s)) = True.
Proof. exact (@lem3570336 (term528 _91535 _91536 g f _38333 s)). Qed.
Lemma lem3570338 {_91535 _91536 : Type'} (g : _91535 -> _91536) (f : _91536 -> _91535) (_38333 : _91536) (s : _91536 -> Prop) : ((term468 _91535 _91536 s g f _38333) = (term528 _91535 _91536 g f _38333 s)) = True.
Proof. exact (TRANS (@lem3570333 _91535 _91536 g f _38333 s) (@lem3570337 _91535 _91536 g f _38333 s)). Qed.
Lemma lem3570339 {_91535 _91536 : Type'} (g : _91535 -> _91536) (f : _91536 -> _91535) (_38333 : _91536) (s : _91536 -> Prop) : True = ((term468 _91535 _91536 s g f _38333) = (term528 _91535 _91536 g f _38333 s)).
Proof. exact (SYM (@lem3570338 _91535 _91536 g f _38333 s)). Qed.
Lemma lem3570340 {_91535 _91536 : Type'} (g : _91535 -> _91536) (f : _91536 -> _91535) (_38333 : _91536) (s : _91536 -> Prop) : (term468 _91535 _91536 s g f _38333) = (term528 _91535 _91536 g f _38333 s).
Proof. exact (EQ_MP (@lem3570339 _91535 _91536 g f _38333 s) (@lem0)). Qed.
Lemma lem3570341 {_91535 _91536 : Type'} (_38333 : _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term83 _91535 _91536 t s g f) : term528 _91535 _91536 g f _38333 s.
Proof. exact (EQ_MP (@lem3570340 _91535 _91536 g f _38333 s) (@lem3570104 _91535 _91536 _38333 t s g f h1)). Qed.
Lemma lem3570343 (b : Prop) (a : Prop) : (a \/ b) = (term252 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3570344 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (_38333 : _91536) : (term528 _91535 _91536 g f _38333 s) = (term531 _91535 _91536 s g f _38333).
Proof. exact (@lem3570343 (term465 _91536 _38333 s) ((term461 _91535 _91536 g f _38333) = _38333)). Qed.
Lemma lem3570346 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3570347 {_91536 : Type'} (_38333 : _91536) (s : _91536 -> Prop) : (term532 _91536 _38333 s) = (term464 _91536 _38333 s).
Proof. exact (@lem3570346 (term464 _91536 _38333 s)). Qed.
Lemma lem3570348 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3570349 {_91536 : Type'} (_38333 : _91536) (s : _91536 -> Prop) : (term533 _91536 _38333 s) = (term534 _91536 _38333 s).
Proof. exact (MK_COMB (@lem3570348) (@lem3570347 _91536 _38333 s)). Qed.
Lemma lem3570350 {_91535 _91536 : Type'} (g : _91535 -> _91536) (f : _91536 -> _91535) (_38333 : _91536) : ((term461 _91535 _91536 g f _38333) = _38333) = ((term461 _91535 _91536 g f _38333) = _38333).
Proof. exact (eq_refl ((term461 _91535 _91536 g f _38333) = _38333)). Qed.
Lemma lem3570351 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (_38333 : _91536) : (term531 _91535 _91536 s g f _38333) = (term535 _91535 _91536 s g f _38333).
Proof. exact (MK_COMB (@lem3570349 _91536 _38333 s) (@lem3570350 _91535 _91536 g f _38333)). Qed.
Lemma lem3570352 {_91535 _91536 : Type'} (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (_38333 : _91536) : (term528 _91535 _91536 g f _38333 s) = (term535 _91535 _91536 s g f _38333).
Proof. exact (TRANS (@lem3570344 _91535 _91536 s g f _38333) (@lem3570351 _91535 _91536 s g f _38333)). Qed.
Lemma lem3570355 {_91535 _91536 : Type'} (_38333 : _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term83 _91535 _91536 t s g f) : term535 _91535 _91536 s g f _38333.
Proof. exact (EQ_MP (@lem3570352 _91535 _91536 s g f _38333) (@lem3570341 _91535 _91536 _38333 t s g f h1)). Qed.
Lemma lem3570356 {_91535 _91536 : Type'} (_38333 : _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term83 _91535 _91536 t s g f) : term535 _91535 _91536 s g f _38333.
Proof. exact (@lem3570355 _91535 _91536 _38333 t s g f h1). Qed.
Lemma lem3570357 {_91535 _91536 : Type'} (x : type570 _91535 _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term83 _91535 _91536 t s g f) : term536 _91535 _91536 s f x g.
Proof. exact (@lem3570356 _91535 _91536 (@I ((_91535 -> _91536) -> _91536) x g) t s g f h1). Qed.
Lemma lem3570360 {_91535 _91536 : Type'} (x : type570 _91535 _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term519 _91535 _91536 s f x) (h2 : term83 _91535 _91536 t s g f) : (term503 _91535 _91536 f x g) = (@I ((_91535 -> _91536) -> _91536) x g).
Proof. exact (@lem3570357 _91535 _91536 x t s g f h2 (@lem3570308 _91535 _91536 g s f x h1)). Qed.
Lemma lem3570361 {_91535 _91536 : Type'} (x : type570 _91535 _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term519 _91535 _91536 s f x) (h2 : term83 _91535 _91536 t s g f) : term537 _91535 _91536 f x g.
Proof. exact (fun h0 : term507 _91535 _91536 f x g => @lem3570360 _91535 _91536 x t s g f h1 h2). Qed.
Lemma lem3570363 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3570364 {_91535 _91536 : Type'} (f : _91536 -> _91535) (x : type570 _91535 _91536) (g : _91535 -> _91536) : (term537 _91535 _91536 f x g) = ((term503 _91535 _91536 f x g) = (@I ((_91535 -> _91536) -> _91536) x g)).
Proof. exact (@lem3570363 ((term503 _91535 _91536 f x g) = (@I ((_91535 -> _91536) -> _91536) x g))). Qed.
Lemma lem3570365 {_91535 _91536 : Type'} (x : type570 _91535 _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term519 _91535 _91536 s f x) (h2 : term83 _91535 _91536 t s g f) : (term503 _91535 _91536 f x g) = (@I ((_91535 -> _91536) -> _91536) x g).
Proof. exact (EQ_MP (@lem3570364 _91535 _91536 f x g) (@lem3570361 _91535 _91536 x t s g f h1 h2)). Qed.
Lemma lem3570368 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3570370 {_91535 _91536 : Type'} (f : _91536 -> _91535) (x : type570 _91535 _91536) (_38334 : _91535 -> _91536) : (term507 _91535 _91536 f x _38334) = (term538 _91535 _91536 f x _38334).
Proof. exact (@lem3570368 ((term503 _91535 _91536 f x _38334) = (@I ((_91535 -> _91536) -> _91536) x _38334))). Qed.
Lemma lem3570373 {_91535 _91536 : Type'} (_38334 : _91535 -> _91536) (s : _91536 -> Prop) (f : _91536 -> _91535) (x : type570 _91535 _91536) (h1 : term519 _91535 _91536 s f x) : term538 _91535 _91536 f x _38334.
Proof. exact (EQ_MP (@lem3570370 _91535 _91536 f x _38334) (@lem3570108 _91535 _91536 _38334 s f x h1)). Qed.
Lemma lem3570374 {_91535 _91536 : Type'} (_38334 : _91535 -> _91536) (s : _91536 -> Prop) (f : _91536 -> _91535) (x : type570 _91535 _91536) (h1 : term519 _91535 _91536 s f x) : term538 _91535 _91536 f x _38334.
Proof. exact (@lem3570373 _91535 _91536 _38334 s f x h1). Qed.
Lemma lem3570375 {_91535 _91536 : Type'} (g : _91535 -> _91536) (s : _91536 -> Prop) (f : _91536 -> _91535) (x : type570 _91535 _91536) (h1 : term519 _91535 _91536 s f x) : term538 _91535 _91536 f x g.
Proof. exact (@lem3570374 _91535 _91536 g s f x h1). Qed.
Lemma lem3570378 {_91535 _91536 : Type'} (x : type570 _91535 _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term519 _91535 _91536 s f x) (h2 : term83 _91535 _91536 t s g f) : False.
Proof. exact (@lem3570375 _91535 _91536 g s f x h1 (@lem3570365 _91535 _91536 x t s g f h1 h2)). Qed.
Lemma lem3570379 {_91535 _91536 : Type'} (x : type570 _91535 _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term519 _91535 _91536 s f x) (h2 : term83 _91535 _91536 t s g f) : term259.
Proof. exact (fun h0 : ~ False => @lem3570378 _91535 _91536 x t s g f h1 h2). Qed.
Lemma lem3570381 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3570382 : term259 = False.
Proof. exact (@lem3570381 False). Qed.
Lemma lem3570383 {_91535 _91536 : Type'} (x : type570 _91535 _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term519 _91535 _91536 s f x) (h2 : term83 _91535 _91536 t s g f) : False.
Proof. exact (EQ_MP (@lem3570382) (@lem3570379 _91535 _91536 x t s g f h1 h2)). Qed.
Lemma lem3570503 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term497 _91535 _91536 t s f g y) : term464 _91535 y t.
Proof. exact (proj1 (@lem3569852 _91535 _91536 t s f g y h1)). Qed.
Lemma lem3570504 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term497 _91535 _91536 t s f g y) : term539 _91535 y t.
Proof. exact (fun h0 : term465 _91535 y t => @lem3570503 _91535 _91536 t s f g y h1). Qed.
Lemma lem3570506 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3570507 {_91535 : Type'} (y : _91535) (t : _91535 -> Prop) : (term539 _91535 y t) = (term464 _91535 y t).
Proof. exact (@lem3570506 (term464 _91535 y t)). Qed.
Lemma lem3570508 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term497 _91535 _91536 t s f g y) : term464 _91535 y t.
Proof. exact (EQ_MP (@lem3570507 _91535 y t) (@lem3570504 _91535 _91536 t s f g y h1)). Qed.
Lemma lem3570514 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3570515 {_91535 _91536 : Type'} (g : _91535 -> _91536) (s : _91536 -> Prop) (_38336 : _91535) (t : _91535 -> Prop) : (term486 _91535 _91536 t g _38336 s) = (term540 _91535 _91536 g s _38336 t).
Proof. exact (@lem3570514 (term485 _91535 _91536 g _38336 s) (term465 _91535 _38336 t)). Qed.
Lemma lem3570521 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3570522 {_91535 _91536 : Type'} (g : _91535 -> _91536) (s : _91536 -> Prop) (_38336 : _91535) (t : _91535 -> Prop) : (term541 _91535 _91536 t g _38336 s) = (term542 _91535 _91536 g s _38336 t).
Proof. exact (MK_COMB (@lem3570521) (@lem3570515 _91535 _91536 g s _38336 t)). Qed.
Lemma lem3570528 {_91535 _91536 : Type'} (g : _91535 -> _91536) (s : _91536 -> Prop) (_38336 : _91535) (t : _91535 -> Prop) : (term540 _91535 _91536 g s _38336 t) = (term540 _91535 _91536 g s _38336 t).
Proof. exact (eq_refl (term540 _91535 _91536 g s _38336 t)). Qed.
Lemma lem3570529 {_91535 _91536 : Type'} (g : _91535 -> _91536) (s : _91536 -> Prop) (_38336 : _91535) (t : _91535 -> Prop) : ((term486 _91535 _91536 t g _38336 s) = (term540 _91535 _91536 g s _38336 t)) = ((term540 _91535 _91536 g s _38336 t) = (term540 _91535 _91536 g s _38336 t)).
Proof. exact (MK_COMB (@lem3570522 _91535 _91536 g s _38336 t) (@lem3570528 _91535 _91536 g s _38336 t)). Qed.
Lemma lem3570531 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3570532 (x : Prop) : (x = x) = True.
Proof. exact (@lem3570531 Prop x). Qed.
Lemma lem3570533 {_91535 _91536 : Type'} (g : _91535 -> _91536) (s : _91536 -> Prop) (_38336 : _91535) (t : _91535 -> Prop) : ((term540 _91535 _91536 g s _38336 t) = (term540 _91535 _91536 g s _38336 t)) = True.
Proof. exact (@lem3570532 (term540 _91535 _91536 g s _38336 t)). Qed.
Lemma lem3570534 {_91535 _91536 : Type'} (g : _91535 -> _91536) (s : _91536 -> Prop) (_38336 : _91535) (t : _91535 -> Prop) : ((term486 _91535 _91536 t g _38336 s) = (term540 _91535 _91536 g s _38336 t)) = True.
Proof. exact (TRANS (@lem3570529 _91535 _91536 g s _38336 t) (@lem3570533 _91535 _91536 g s _38336 t)). Qed.
Lemma lem3570535 {_91535 _91536 : Type'} (g : _91535 -> _91536) (s : _91536 -> Prop) (_38336 : _91535) (t : _91535 -> Prop) : True = ((term486 _91535 _91536 t g _38336 s) = (term540 _91535 _91536 g s _38336 t)).
Proof. exact (SYM (@lem3570534 _91535 _91536 g s _38336 t)). Qed.
Lemma lem3570536 {_91535 _91536 : Type'} (g : _91535 -> _91536) (s : _91536 -> Prop) (_38336 : _91535) (t : _91535 -> Prop) : (term486 _91535 _91536 t g _38336 s) = (term540 _91535 _91536 g s _38336 t).
Proof. exact (EQ_MP (@lem3570535 _91535 _91536 g s _38336 t) (@lem0)). Qed.
Lemma lem3570537 {_91535 _91536 : Type'} (_38336 : _91535) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term83 _91535 _91536 t s g f) : term540 _91535 _91536 g s _38336 t.
Proof. exact (EQ_MP (@lem3570536 _91535 _91536 g s _38336 t) (@lem3570120 _91535 _91536 _38336 t s g f h1)). Qed.
Lemma lem3570539 (b : Prop) (a : Prop) : (a \/ b) = (term252 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3570540 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (_38336 : _91535) (s : _91536 -> Prop) : (term540 _91535 _91536 g s _38336 t) = (term543 _91535 _91536 t g _38336 s).
Proof. exact (@lem3570539 (term465 _91535 _38336 t) (term485 _91535 _91536 g _38336 s)). Qed.
Lemma lem3570542 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3570543 {_91535 : Type'} (_38336 : _91535) (t : _91535 -> Prop) : (term532 _91535 _38336 t) = (term464 _91535 _38336 t).
Proof. exact (@lem3570542 (term464 _91535 _38336 t)). Qed.
Lemma lem3570544 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3570545 {_91535 : Type'} (_38336 : _91535) (t : _91535 -> Prop) : (term533 _91535 _38336 t) = (term534 _91535 _38336 t).
Proof. exact (MK_COMB (@lem3570544) (@lem3570543 _91535 _38336 t)). Qed.
Lemma lem3570546 {_91535 _91536 : Type'} (g : _91535 -> _91536) (_38336 : _91535) (s : _91536 -> Prop) : (term485 _91535 _91536 g _38336 s) = (term485 _91535 _91536 g _38336 s).
Proof. exact (eq_refl (term485 _91535 _91536 g _38336 s)). Qed.
Lemma lem3570547 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (_38336 : _91535) (s : _91536 -> Prop) : (term543 _91535 _91536 t g _38336 s) = (term544 _91535 _91536 t g _38336 s).
Proof. exact (MK_COMB (@lem3570545 _91535 _38336 t) (@lem3570546 _91535 _91536 g _38336 s)). Qed.
Lemma lem3570548 {_91535 _91536 : Type'} (t : _91535 -> Prop) (g : _91535 -> _91536) (_38336 : _91535) (s : _91536 -> Prop) : (term540 _91535 _91536 g s _38336 t) = (term544 _91535 _91536 t g _38336 s).
Proof. exact (TRANS (@lem3570540 _91535 _91536 t g _38336 s) (@lem3570547 _91535 _91536 t g _38336 s)). Qed.
Lemma lem3570551 {_91535 _91536 : Type'} (_38336 : _91535) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term83 _91535 _91536 t s g f) : term544 _91535 _91536 t g _38336 s.
Proof. exact (EQ_MP (@lem3570548 _91535 _91536 t g _38336 s) (@lem3570537 _91535 _91536 _38336 t s g f h1)). Qed.
Lemma lem3570552 {_91535 _91536 : Type'} (_38336 : _91535) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term83 _91535 _91536 t s g f) : term544 _91535 _91536 t g _38336 s.
Proof. exact (@lem3570551 _91535 _91536 _38336 t s g f h1). Qed.
Lemma lem3570553 {_91535 _91536 : Type'} (y : _91535) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term83 _91535 _91536 t s g f) : term544 _91535 _91536 t g y s.
Proof. exact (@lem3570552 _91535 _91536 y t s g f h1). Qed.
Lemma lem3570556 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term83 _91535 _91536 t s g f) (h2 : term497 _91535 _91536 t s f g y) : term485 _91535 _91536 g y s.
Proof. exact (@lem3570553 _91535 _91536 y t s g f h1 (@lem3570508 _91535 _91536 t s f g y h2)). Qed.
Lemma lem3570557 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term83 _91535 _91536 t s g f) (h2 : term497 _91535 _91536 t s f g y) : term545 _91535 _91536 g y s.
Proof. exact (fun h0 : term492 _91535 _91536 g y s => @lem3570556 _91535 _91536 t s f g y h1 h2). Qed.
Lemma lem3570559 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3570560 {_91535 _91536 : Type'} (g : _91535 -> _91536) (y : _91535) (s : _91536 -> Prop) : (term545 _91535 _91536 g y s) = (term485 _91535 _91536 g y s).
Proof. exact (@lem3570559 (term485 _91535 _91536 g y s)). Qed.
Lemma lem3570561 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term83 _91535 _91536 t s g f) (h2 : term497 _91535 _91536 t s f g y) : term485 _91535 _91536 g y s.
Proof. exact (EQ_MP (@lem3570560 _91535 _91536 g y s) (@lem3570557 _91535 _91536 t s f g y h1 h2)). Qed.
Lemma lem3570564 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3570566 {_91535 _91536 : Type'} (g : _91535 -> _91536) (y : _91535) (s : _91536 -> Prop) : (term492 _91535 _91536 g y s) = (term546 _91535 _91536 g y s).
Proof. exact (@lem3570564 (term485 _91535 _91536 g y s)). Qed.
Lemma lem3570569 {_91535 _91536 : Type'} (g : _91535 -> _91536) (y : _91535) (s : _91536 -> Prop) (h1 : term492 _91535 _91536 g y s) : term546 _91535 _91536 g y s.
Proof. exact (EQ_MP (@lem3570566 _91535 _91536 g y s) (@lem3570136 _91535 _91536 g y s h1)). Qed.
Lemma lem3570572 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term492 _91535 _91536 g y s) (h2 : term83 _91535 _91536 t s g f) (h3 : term497 _91535 _91536 t s f g y) : False.
Proof. exact (@lem3570569 _91535 _91536 g y s h1 (@lem3570561 _91535 _91536 t s f g y h2 h3)). Qed.
Lemma lem3570573 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term492 _91535 _91536 g y s) (h2 : term83 _91535 _91536 t s g f) (h3 : term497 _91535 _91536 t s f g y) : term259.
Proof. exact (fun h0 : ~ False => @lem3570572 _91535 _91536 t s f g y h1 h2 h3). Qed.
Lemma lem3570575 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3570576 : term259 = False.
Proof. exact (@lem3570575 False). Qed.
Lemma lem3570577 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term492 _91535 _91536 g y s) (h2 : term83 _91535 _91536 t s g f) (h3 : term497 _91535 _91536 t s f g y) : False.
Proof. exact (EQ_MP (@lem3570576) (@lem3570573 _91535 _91536 t s f g y h1 h2 h3)). Qed.
Lemma lem3570697 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term497 _91535 _91536 t s f g y) : term464 _91535 y t.
Proof. exact (proj1 (@lem3569852 _91535 _91536 t s f g y h1)). Qed.
Lemma lem3570698 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term497 _91535 _91536 t s f g y) : term539 _91535 y t.
Proof. exact (fun h0 : term465 _91535 y t => @lem3570697 _91535 _91536 t s f g y h1). Qed.
Lemma lem3570700 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3570701 {_91535 : Type'} (y : _91535) (t : _91535 -> Prop) : (term539 _91535 y t) = (term464 _91535 y t).
Proof. exact (@lem3570700 (term464 _91535 y t)). Qed.
Lemma lem3570702 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term497 _91535 _91536 t s f g y) : term464 _91535 y t.
Proof. exact (EQ_MP (@lem3570701 _91535 y t) (@lem3570698 _91535 _91536 t s f g y h1)). Qed.
Lemma lem3570708 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3570709 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) (_38341 : _91535) (t : _91535 -> Prop) : (term475 _91535 _91536 t f g _38341) = (term547 _91535 _91536 f g _38341 t).
Proof. exact (@lem3570708 ((term472 _91535 _91536 f g _38341) = _38341) (term465 _91535 _38341 t)). Qed.
Lemma lem3570717 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3570718 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) (_38341 : _91535) (t : _91535 -> Prop) : (term548 _91535 _91536 t f g _38341) = (term549 _91535 _91536 f g _38341 t).
Proof. exact (MK_COMB (@lem3570717) (@lem3570709 _91535 _91536 f g _38341 t)). Qed.
Lemma lem3570726 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) (_38341 : _91535) (t : _91535 -> Prop) : (term547 _91535 _91536 f g _38341 t) = (term547 _91535 _91536 f g _38341 t).
Proof. exact (eq_refl (term547 _91535 _91536 f g _38341 t)). Qed.
Lemma lem3570727 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) (_38341 : _91535) (t : _91535 -> Prop) : ((term475 _91535 _91536 t f g _38341) = (term547 _91535 _91536 f g _38341 t)) = ((term547 _91535 _91536 f g _38341 t) = (term547 _91535 _91536 f g _38341 t)).
Proof. exact (MK_COMB (@lem3570718 _91535 _91536 f g _38341 t) (@lem3570726 _91535 _91536 f g _38341 t)). Qed.
Lemma lem3570729 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3570730 (x : Prop) : (x = x) = True.
Proof. exact (@lem3570729 Prop x). Qed.
Lemma lem3570731 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) (_38341 : _91535) (t : _91535 -> Prop) : ((term547 _91535 _91536 f g _38341 t) = (term547 _91535 _91536 f g _38341 t)) = True.
Proof. exact (@lem3570730 (term547 _91535 _91536 f g _38341 t)). Qed.
Lemma lem3570732 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) (_38341 : _91535) (t : _91535 -> Prop) : ((term475 _91535 _91536 t f g _38341) = (term547 _91535 _91536 f g _38341 t)) = True.
Proof. exact (TRANS (@lem3570727 _91535 _91536 f g _38341 t) (@lem3570731 _91535 _91536 f g _38341 t)). Qed.
Lemma lem3570733 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) (_38341 : _91535) (t : _91535 -> Prop) : True = ((term475 _91535 _91536 t f g _38341) = (term547 _91535 _91536 f g _38341 t)).
Proof. exact (SYM (@lem3570732 _91535 _91536 f g _38341 t)). Qed.
Lemma lem3570734 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) (_38341 : _91535) (t : _91535 -> Prop) : (term475 _91535 _91536 t f g _38341) = (term547 _91535 _91536 f g _38341 t).
Proof. exact (EQ_MP (@lem3570733 _91535 _91536 f g _38341 t) (@lem0)). Qed.
Lemma lem3570735 {_91535 _91536 : Type'} (_38341 : _91535) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term83 _91535 _91536 t s g f) : term547 _91535 _91536 f g _38341 t.
Proof. exact (EQ_MP (@lem3570734 _91535 _91536 f g _38341 t) (@lem3570154 _91535 _91536 _38341 t s g f h1)). Qed.
Lemma lem3570737 (b : Prop) (a : Prop) : (a \/ b) = (term252 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3570738 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (_38341 : _91535) : (term547 _91535 _91536 f g _38341 t) = (term550 _91535 _91536 t f g _38341).
Proof. exact (@lem3570737 (term465 _91535 _38341 t) ((term472 _91535 _91536 f g _38341) = _38341)). Qed.
Lemma lem3570740 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3570741 {_91535 : Type'} (_38341 : _91535) (t : _91535 -> Prop) : (term532 _91535 _38341 t) = (term464 _91535 _38341 t).
Proof. exact (@lem3570740 (term464 _91535 _38341 t)). Qed.
Lemma lem3570742 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3570743 {_91535 : Type'} (_38341 : _91535) (t : _91535 -> Prop) : (term533 _91535 _38341 t) = (term534 _91535 _38341 t).
Proof. exact (MK_COMB (@lem3570742) (@lem3570741 _91535 _38341 t)). Qed.
Lemma lem3570744 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) (_38341 : _91535) : ((term472 _91535 _91536 f g _38341) = _38341) = ((term472 _91535 _91536 f g _38341) = _38341).
Proof. exact (eq_refl ((term472 _91535 _91536 f g _38341) = _38341)). Qed.
Lemma lem3570745 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (_38341 : _91535) : (term550 _91535 _91536 t f g _38341) = (term551 _91535 _91536 t f g _38341).
Proof. exact (MK_COMB (@lem3570743 _91535 _38341 t) (@lem3570744 _91535 _91536 f g _38341)). Qed.
Lemma lem3570746 {_91535 _91536 : Type'} (t : _91535 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (_38341 : _91535) : (term547 _91535 _91536 f g _38341 t) = (term551 _91535 _91536 t f g _38341).
Proof. exact (TRANS (@lem3570738 _91535 _91536 t f g _38341) (@lem3570745 _91535 _91536 t f g _38341)). Qed.
Lemma lem3570749 {_91535 _91536 : Type'} (_38341 : _91535) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term83 _91535 _91536 t s g f) : term551 _91535 _91536 t f g _38341.
Proof. exact (EQ_MP (@lem3570746 _91535 _91536 t f g _38341) (@lem3570735 _91535 _91536 _38341 t s g f h1)). Qed.
Lemma lem3570750 {_91535 _91536 : Type'} (_38341 : _91535) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term83 _91535 _91536 t s g f) : term551 _91535 _91536 t f g _38341.
Proof. exact (@lem3570749 _91535 _91536 _38341 t s g f h1). Qed.
Lemma lem3570751 {_91535 _91536 : Type'} (y : _91535) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term83 _91535 _91536 t s g f) : term551 _91535 _91536 t f g y.
Proof. exact (@lem3570750 _91535 _91536 y t s g f h1). Qed.
Lemma lem3570754 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term83 _91535 _91536 t s g f) (h2 : term497 _91535 _91536 t s f g y) : (term472 _91535 _91536 f g y) = y.
Proof. exact (@lem3570751 _91535 _91536 y t s g f h1 (@lem3570702 _91535 _91536 t s f g y h2)). Qed.
Lemma lem3570755 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term83 _91535 _91536 t s g f) (h2 : term497 _91535 _91536 t s f g y) : term552 _91535 _91536 f g y.
Proof. exact (fun h0 : term491 _91535 _91536 f g y => @lem3570754 _91535 _91536 t s f g y h1 h2). Qed.
Lemma lem3570757 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3570758 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : (term552 _91535 _91536 f g y) = ((term472 _91535 _91536 f g y) = y).
Proof. exact (@lem3570757 ((term472 _91535 _91536 f g y) = y)). Qed.
Lemma lem3570759 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term83 _91535 _91536 t s g f) (h2 : term497 _91535 _91536 t s f g y) : (term472 _91535 _91536 f g y) = y.
Proof. exact (EQ_MP (@lem3570758 _91535 _91536 f g y) (@lem3570755 _91535 _91536 t s f g y h1 h2)). Qed.
Lemma lem3570762 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3570764 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) : (term491 _91535 _91536 f g y) = (term553 _91535 _91536 f g y).
Proof. exact (@lem3570762 ((term472 _91535 _91536 f g y) = y)). Qed.
Lemma lem3570767 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term491 _91535 _91536 f g y) : term553 _91535 _91536 f g y.
Proof. exact (EQ_MP (@lem3570764 _91535 _91536 f g y) (@lem3570164 _91535 _91536 f g y h1)). Qed.
Lemma lem3570770 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term491 _91535 _91536 f g y) (h2 : term83 _91535 _91536 t s g f) (h3 : term497 _91535 _91536 t s f g y) : False.
Proof. exact (@lem3570767 _91535 _91536 f g y h1 (@lem3570759 _91535 _91536 t s f g y h2 h3)). Qed.
Lemma lem3570771 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term491 _91535 _91536 f g y) (h2 : term83 _91535 _91536 t s g f) (h3 : term497 _91535 _91536 t s f g y) : term259.
Proof. exact (fun h0 : ~ False => @lem3570770 _91535 _91536 t s f g y h1 h2 h3). Qed.
Lemma lem3570773 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3570774 : term259 = False.
Proof. exact (@lem3570773 False). Qed.
Lemma lem3570775 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term491 _91535 _91536 f g y) (h2 : term83 _91535 _91536 t s g f) (h3 : term497 _91535 _91536 t s f g y) : False.
Proof. exact (EQ_MP (@lem3570774) (@lem3570771 _91535 _91536 t s f g y h1 h2 h3)). Qed.
Lemma lem3570776 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term491 _91535 _91536 f g y) (h2 : term83 _91535 _91536 t s g f) (h3 : term497 _91535 _91536 t s f g y) : (term491 _91535 _91536 f g y) = False.
Proof. exact (prop_ext (fun h4 : term491 _91535 _91536 f g y => @lem3570775 _91535 _91536 t s f g y h1 h2 h3) (fun h4 : False => @lem3570164 _91535 _91536 f g y h1)). Qed.
Lemma lem3570777 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term491 _91535 _91536 f g y) (h2 : term83 _91535 _91536 t s g f) (h3 : term497 _91535 _91536 t s f g y) : False.
Proof. exact (EQ_MP (@lem3570776 _91535 _91536 t s f g y h1 h2 h3) (@lem3570164 _91535 _91536 f g y h1)). Qed.
Lemma lem3570778 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term492 _91535 _91536 g y s) (h2 : term83 _91535 _91536 t s g f) (h3 : term497 _91535 _91536 t s f g y) : (term492 _91535 _91536 g y s) = False.
Proof. exact (prop_ext (fun h4 : term492 _91535 _91536 g y s => @lem3570577 _91535 _91536 t s f g y h1 h2 h3) (fun h4 : False => @lem3570136 _91535 _91536 g y s h1)). Qed.
Lemma lem3570779 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term492 _91535 _91536 g y s) (h2 : term83 _91535 _91536 t s g f) (h3 : term497 _91535 _91536 t s f g y) : False.
Proof. exact (EQ_MP (@lem3570778 _91535 _91536 t s f g y h1 h2 h3) (@lem3570136 _91535 _91536 g y s h1)). Qed.
Lemma lem3570780 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term491 _91535 _91536 f g y) (h2 : term83 _91535 _91536 t s g f) (h3 : term497 _91535 _91536 t s f g y) : (term491 _91535 _91536 f g y) = False.
Proof. exact (prop_ext (fun h4 : term491 _91535 _91536 f g y => @lem3570777 _91535 _91536 t s f g y h1 h2 h3) (fun h4 : False => @lem3570039 _91535 _91536 f g y h1)). Qed.
Lemma lem3570781 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term491 _91535 _91536 f g y) (h2 : term83 _91535 _91536 t s g f) (h3 : term497 _91535 _91536 t s f g y) : False.
Proof. exact (EQ_MP (@lem3570780 _91535 _91536 t s f g y h1 h2 h3) (@lem3570039 _91535 _91536 f g y h1)). Qed.
Lemma lem3570782 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term492 _91535 _91536 g y s) (h2 : term83 _91535 _91536 t s g f) (h3 : term497 _91535 _91536 t s f g y) : (term492 _91535 _91536 g y s) = False.
Proof. exact (prop_ext (fun h4 : term492 _91535 _91536 g y s => @lem3570779 _91535 _91536 t s f g y h1 h2 h3) (fun h4 : False => @lem3569979 _91535 _91536 g y s h1)). Qed.
Lemma lem3570783 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term492 _91535 _91536 g y s) (h2 : term83 _91535 _91536 t s g f) (h3 : term497 _91535 _91536 t s f g y) : False.
Proof. exact (EQ_MP (@lem3570782 _91535 _91536 t s f g y h1 h2 h3) (@lem3569979 _91535 _91536 g y s h1)). Qed.
Lemma lem3570784 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term491 _91535 _91536 f g y) (h2 : term83 _91535 _91536 t s g f) (h3 : term497 _91535 _91536 t s f g y) : (term491 _91535 _91536 f g y) = False.
Proof. exact (prop_ext (fun h4 : term491 _91535 _91536 f g y => @lem3570781 _91535 _91536 t s f g y h1 h2 h3) (fun h4 : False => @lem3570039 _91535 _91536 f g y h1)). Qed.
Lemma lem3570785 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term491 _91535 _91536 f g y) (h2 : term83 _91535 _91536 t s g f) (h3 : term497 _91535 _91536 t s f g y) : False.
Proof. exact (EQ_MP (@lem3570784 _91535 _91536 t s f g y h1 h2 h3) (@lem3570039 _91535 _91536 f g y h1)). Qed.
Lemma lem3570786 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term492 _91535 _91536 g y s) (h2 : term83 _91535 _91536 t s g f) (h3 : term497 _91535 _91536 t s f g y) : (term492 _91535 _91536 g y s) = False.
Proof. exact (prop_ext (fun h4 : term492 _91535 _91536 g y s => @lem3570783 _91535 _91536 t s f g y h1 h2 h3) (fun h4 : False => @lem3569979 _91535 _91536 g y s h1)). Qed.
Lemma lem3570787 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term492 _91535 _91536 g y s) (h2 : term83 _91535 _91536 t s g f) (h3 : term497 _91535 _91536 t s f g y) : False.
Proof. exact (EQ_MP (@lem3570786 _91535 _91536 t s f g y h1 h2 h3) (@lem3569979 _91535 _91536 g y s h1)). Qed.
Lemma lem3570788 {_91535 _91536 : Type'} (x : type570 _91535 _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term519 _91535 _91536 s f x) (h2 : term83 _91535 _91536 t s g f) : (term519 _91535 _91536 s f x) = False.
Proof. exact (prop_ext (fun h3 : term519 _91535 _91536 s f x => @lem3570383 _91535 _91536 x t s g f h1 h2) (fun h3 : False => @lem3569919 _91535 _91536 s f x h1)). Qed.
Lemma lem3570789 {_91535 _91536 : Type'} (x : type570 _91535 _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term519 _91535 _91536 s f x) (h2 : term83 _91535 _91536 t s g f) : False.
Proof. exact (EQ_MP (@lem3570788 _91535 _91536 x t s g f h1 h2) (@lem3569919 _91535 _91536 s f x h1)). Qed.
Lemma lem3570790 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term83 _91535 _91536 t s g f) (h2 : term497 _91535 _91536 t s f g y) : False.
Proof. exact (or_elim (@lem3569853 _91535 _91536 t s f g y h2) (fun h0 : term492 _91535 _91536 g y s => @lem3570787 _91535 _91536 t s f g y h0 h1 h2) (fun h0 : term491 _91535 _91536 f g y => @lem3570785 _91535 _91536 t s f g y h0 h1 h2)). Qed.
Lemma lem3570791 {_91535 _91536 : Type'} (x : type570 _91535 _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (y : _91535) (h1 : term83 _91535 _91536 t s g f) (h2 : term454 _91535 _91536 x t s f g y) : False.
Proof. exact (or_elim (@lem3569846 _91535 _91536 x t s f g y h2) (fun h0 : term519 _91535 _91536 s f x => @lem3570789 _91535 _91536 x t s g f h0 h1) (fun h0 : term497 _91535 _91536 t s f g y => @lem3570790 _91535 _91536 t s f g y h1 h0)). Qed.
Lemma lem3570792 {_91535 _91536 : Type'} (x : type570 _91535 _91536) (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term457 _91535 _91536 x t s f g) (h2 : term83 _91535 _91536 t s g f) : False.
Proof. exact (ex_elim (@lem3569514 _91535 _91536 x t s f g h1) (fun y : _91535 => fun h0 : term456 _91535 _91536 x t s f g y => @lem3570791 _91535 _91536 x t s f g y h2 h0)). Qed.
Lemma lem3570793 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term368 _91535 _91536 t s f g) (h2 : term83 _91535 _91536 t s g f) : False.
Proof. exact (ex_elim (@lem3569513 _91535 _91536 t s f g h1) (fun x : type570 _91535 _91536 => fun h0 : term458 _91535 _91536 t s f g x => @lem3570792 _91535 _91536 x t s g f h0 h2)). Qed.
Lemma lem3570794 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term368 _91535 _91536 t s f g) (h2 : term83 _91535 _91536 t s g f) : (term368 _91535 _91536 t s f g) = False.
Proof. exact (prop_ext (fun h3 : term368 _91535 _91536 t s f g => @lem3570793 _91535 _91536 t s g f h1 h2) (fun h3 : False => @lem3569021 _91535 _91536 t s f g h1)). Qed.
Lemma lem3570795 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term368 _91535 _91536 t s f g) (h2 : term83 _91535 _91536 t s g f) : False.
Proof. exact (EQ_MP (@lem3570794 _91535 _91536 t s g f h1 h2) (@lem3569021 _91535 _91536 t s f g h1)). Qed.
Lemma lem3570796 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term83 _91535 _91536 t s g f) : term367 _91535 _91536 t s f g.
Proof. exact (fun h0 : term368 _91535 _91536 t s f g => @lem3570795 _91535 _91536 t s g f h0 h1). Qed.
Lemma lem3570797 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) (h1 : term83 _91535 _91536 t s g f) : term38 _91535 _91536 t s f g.
Proof. exact (EQ_MP (@lem3569020 _91535 _91536 t s f g) (@lem3570796 _91535 _91536 t s g f h1)). Qed.
Lemma lem3570798 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : term341 _91535 _91536 t s f g.
Proof. exact (fun h0 : term83 _91535 _91536 t s g f => @lem3570797 _91535 _91536 t s g f h0). Qed.
Lemma lem3570799 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : term349 _91535 _91536 t s f g.
Proof. exact (fun h0 : term15 _91535 _91536 s f t => @lem3570798 _91535 _91536 t s f g). Qed.
Lemma lem3570804 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : term353 _91535 _91536 s f g.
Proof. exact (fun t : _91535 -> Prop => @lem3570799 _91535 _91536 t s f g). Qed.
Lemma lem3570809 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) : term357 _91535 _91536 f g.
Proof. exact (fun s : _91536 -> Prop => @lem3570804 _91535 _91536 s f g). Qed.
Lemma lem3570814 {_91535 _91536 : Type'} (g : _91535 -> _91536) : term361 _91535 _91536 g.
Proof. exact (fun f : _91536 -> _91535 => @lem3570809 _91535 _91536 f g). Qed.
Lemma lem3570819 {_91535 _91536 : Type'} : term365 _91535 _91536.
Proof. exact (fun g : _91535 -> _91536 => @lem3570814 _91535 _91536 g). Qed.
Lemma lem3570820 {_91535 _91536 : Type'} : term364 _91535 _91536.
Proof. exact (EQ_MP (@lem3569014 _91535 _91536) (@lem3570819 _91535 _91536)). Qed.
Lemma lem3570821 {_91535 _91536 : Type'} (g : _91535 -> _91536) : term554 _91535 _91536 g.
Proof. exact (@lem3570820 _91535 _91536 g). Qed.
Lemma lem3570822 {_91535 _91536 : Type'} (g : _91535 -> _91536) : (term554 _91535 _91536 g) = (term360 _91535 _91536 g).
Proof. exact (eq_refl (term554 _91535 _91536 g)). Qed.
Lemma lem3570823 {_91535 _91536 : Type'} (g : _91535 -> _91536) : term360 _91535 _91536 g.
Proof. exact (EQ_MP (@lem3570822 _91535 _91536 g) (@lem3570821 _91535 _91536 g)). Qed.
Lemma lem3570824 {_91535 _91536 : Type'} (g : _91535 -> _91536) (f : _91536 -> _91535) : term555 _91535 _91536 g f.
Proof. exact (@lem3570823 _91535 _91536 g f). Qed.
Lemma lem3570825 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) : (term555 _91535 _91536 g f) = (term356 _91535 _91536 f g).
Proof. exact (eq_refl (term555 _91535 _91536 g f)). Qed.
Lemma lem3570826 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) : term356 _91535 _91536 f g.
Proof. exact (EQ_MP (@lem3570825 _91535 _91536 f g) (@lem3570824 _91535 _91536 g f)). Qed.
Lemma lem3570827 {_91535 _91536 : Type'} (f : _91536 -> _91535) (g : _91535 -> _91536) (s : _91536 -> Prop) : term556 _91535 _91536 f g s.
Proof. exact (@lem3570826 _91535 _91536 f g s). Qed.
Lemma lem3570828 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term556 _91535 _91536 f g s) = (term352 _91535 _91536 s f g).
Proof. exact (eq_refl (term556 _91535 _91536 f g s)). Qed.
Lemma lem3570829 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : term352 _91535 _91536 s f g.
Proof. exact (EQ_MP (@lem3570828 _91535 _91536 s f g) (@lem3570827 _91535 _91536 f g s)). Qed.
Lemma lem3570830 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (t : _91535 -> Prop) : term557 _91535 _91536 s f g t.
Proof. exact (@lem3570829 _91535 _91536 s f g t). Qed.
Lemma lem3570831 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : (term557 _91535 _91536 s f g t) = (term344 _91535 _91536 t s f g).
Proof. exact (eq_refl (term557 _91535 _91536 s f g t)). Qed.
Lemma lem3570832 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : term344 _91535 _91536 t s f g.
Proof. exact (EQ_MP (@lem3570831 _91535 _91536 t s f g) (@lem3570830 _91535 _91536 s f g t)). Qed.
Lemma lem3570834 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) : term344 _91535 _91536 t s f g.
Proof. exact (@lem3568727 _91535 _91536 t s f g (@lem3570832 _91535 _91536 t s f g)). Qed.
Lemma lem3570835 {_91535 _91536 : Type'} (g : _91535 -> _91536) (s : _91536 -> Prop) (f : _91536 -> _91535) (t : _91535 -> Prop) (h1 : term15 _91535 _91536 s f t) : term342 _91535 _91536 t s f g.
Proof. exact (@lem3570834 _91535 _91536 t s f g (@lem3566211 _91535 _91536 s f t h1)). Qed.
Lemma lem3570836 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term343 _91535 _91536 t s f g) : False.
Proof. exact (@lem3570835 _91535 _91536 g s f t h1 (@lem3568711 _91535 _91536 t s f g h2)). Qed.
Lemma lem3570837 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term343 _91535 _91536 t s f g) : (term343 _91535 _91536 t s f g) = False.
Proof. exact (prop_ext (fun h3 : term343 _91535 _91536 t s f g => @lem3570836 _91535 _91536 t s f g h1 h2) (fun h3 : False => @lem3568711 _91535 _91536 t s f g h2)). Qed.
Lemma lem3570838 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) (g : _91535 -> _91536) (h1 : term15 _91535 _91536 s f t) (h2 : term343 _91535 _91536 t s f g) : False.
Proof. exact (EQ_MP (@lem3570837 _91535 _91536 t s f g h1 h2) (@lem3568711 _91535 _91536 t s f g h2)). Qed.
Lemma lem3570839 {_91535 _91536 : Type'} (g : _91535 -> _91536) (s : _91536 -> Prop) (f : _91536 -> _91535) (t : _91535 -> Prop) (h1 : term15 _91535 _91536 s f t) : term342 _91535 _91536 t s f g.
Proof. exact (fun h0 : term343 _91535 _91536 t s f g => @lem3570838 _91535 _91536 t s f g h1 h0). Qed.
Lemma lem3570840 {_91535 _91536 : Type'} (g : _91535 -> _91536) (s : _91536 -> Prop) (f : _91536 -> _91535) (t : _91535 -> Prop) (h1 : term15 _91535 _91536 s f t) : term341 _91535 _91536 t s f g.
Proof. exact (EQ_MP (@lem3568710 _91535 _91536 t s f g) (@lem3570839 _91535 _91536 g s f t h1)). Qed.
Lemma lem3570841 {_91535 _91536 : Type'} (g : _91535 -> _91536) (s : _91536 -> Prop) (f : _91536 -> _91535) (t : _91535 -> Prop) (h1 : term15 _91535 _91536 s f t) : term558 _91535 _91536 t s f g.
Proof. exact (conj (@lem3568706 _91535 _91536 g s f t h1) (@lem3570840 _91535 _91536 g s f t h1)). Qed.
Lemma lem3570842 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (g : _91535 -> _91536) (f : _91536 -> _91535) : (term558 _91535 _91536 t s f g) = ((term38 _91535 _91536 t s f g) = (term83 _91535 _91536 t s g f)).
Proof. exact (@lem32 (term38 _91535 _91536 t s f g) (term83 _91535 _91536 t s g f)). Qed.
Lemma lem3570843 {_91535 _91536 : Type'} (g : _91535 -> _91536) (s : _91536 -> Prop) (f : _91536 -> _91535) (t : _91535 -> Prop) (h1 : term15 _91535 _91536 s f t) : (term38 _91535 _91536 t s f g) = (term83 _91535 _91536 t s g f).
Proof. exact (EQ_MP (@lem3570842 _91535 _91536 t s g f) (@lem3570841 _91535 _91536 g s f t h1)). Qed.
Lemma lem3570846 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (t : _91535 -> Prop) (h1 : term15 _91535 _91536 s f t) : (term40 _91535 _91536 t s f) = (term559 _91535 _91536 t s f).
Proof. exact (fun_ext (fun g : _91535 -> _91536 => @lem3570843 _91535 _91536 g s f t h1)). Qed.
Lemma lem3570847 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (t : _91535 -> Prop) (h1 : term15 _91535 _91536 s f t) : (term41 _91535 _91536 t s f) = (term26 _91535 _91536 t s f).
Proof. exact (MK_COMB (@lem3566377 _91535 _91536) (@lem3570846 _91535 _91536 s f t h1)). Qed.
Lemma lem3570848 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (t : _91535 -> Prop) (h1 : term15 _91535 _91536 s f t) : (term23 _91535 _91536 t s f) = (term26 _91535 _91536 t s f).
Proof. exact (EQ_MP (@lem3566376 _91535 _91536 t s f) (@lem3570847 _91535 _91536 s f t h1)). Qed.
Lemma lem3570849 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) (t : _91535 -> Prop) (h1 : term15 _91535 _91536 s f t) : (term22 _91535 _91536 t s f) = (term26 _91535 _91536 t s f).
Proof. exact (EQ_MP (@lem3566289 _91535 _91536 t s f) (@lem3570848 _91535 _91536 s f t h1)). Qed.
Lemma lem3570850 {_91535 _91536 : Type'} (t : _91535 -> Prop) (s : _91536 -> Prop) (f : _91536 -> _91535) : term560 _91535 _91536 t s f.
Proof. exact (fun h0 : term15 _91535 _91536 s f t => @lem3570849 _91535 _91536 s f t h0). Qed.
Lemma lem3570855 {_91535 _91536 : Type'} (s : _91536 -> Prop) (f : _91536 -> _91535) : term561 _91535 _91536 s f.
Proof. exact (fun t : _91535 -> Prop => @lem3570850 _91535 _91536 t s f). Qed.
Lemma lem3570860 {_91535 _91536 : Type'} (f : _91536 -> _91535) : term562 _91535 _91536 f.
Proof. exact (fun s : _91536 -> Prop => @lem3570855 _91535 _91536 s f). Qed.
Lemma lem3570865 {_91535 _91536 : Type'} : term563 _91535 _91536.
Proof. exact (fun f : _91536 -> _91535 => @lem3570860 _91535 _91536 f). Qed.
