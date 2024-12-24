Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3322871_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm1834_spec.
Require Import thm18394_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211662_spec.
Require Import thm3211663_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Lemma lem3322198 {A : Type'} (s : type686 A) (x : A) : (term0 A x s) = (term1 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem3322199 {_86807 : Type'} (s : type686 _86807) (x : _86807) : (term0 _86807 x s) = (term1 _86807 s x).
Proof. exact (@lem3322198 _86807 s x). Qed.
Lemma lem3322200 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term2 _86807 x s) = (term3 _86807 s x).
Proof. exact (@lem3322199 _86807 (@INSERT (_86807 -> Prop) s (@EMPTY (_86807 -> Prop))) x). Qed.
Lemma lem3322208 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term4 A x y s) = (term5 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3322209 {_86807 : Type'} (y : _86807 -> Prop) (x : _86807 -> Prop) (s : type686 _86807) : (term6 _86807 x y s) = (term7 _86807 y x s).
Proof. exact (@lem3322208 (_86807 -> Prop) y x s). Qed.
Lemma lem3322210 {_86807 : Type'} (s : _86807 -> Prop) (t : _86807 -> Prop) : (term8 _86807 t s) = (term9 _86807 s t).
Proof. exact (@lem3322209 _86807 s t (@EMPTY (_86807 -> Prop))). Qed.
Lemma lem3322216 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3322217 {_86807 : Type'} (x : _86807 -> Prop) : (@IN (_86807 -> Prop) x (@EMPTY (_86807 -> Prop))) = False.
Proof. exact (@lem3322216 (_86807 -> Prop) x). Qed.
Lemma lem3322218 {_86807 : Type'} (t : _86807 -> Prop) : (@IN (_86807 -> Prop) t (@EMPTY (_86807 -> Prop))) = False.
Proof. exact (@lem3322217 _86807 t). Qed.
Lemma lem3322219 {_86807 : Type'} (t : _86807 -> Prop) (s : _86807 -> Prop) : (term10 _86807 t s) = (term10 _86807 t s).
Proof. exact (eq_refl (term10 _86807 t s)). Qed.
Lemma lem3322220 {_86807 : Type'} (t : _86807 -> Prop) (s : _86807 -> Prop) : (term9 _86807 s t) = (term11 _86807 t s).
Proof. exact (MK_COMB (@lem3322219 _86807 t s) (@lem3322218 _86807 t)). Qed.
Lemma lem3322222 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem3322223 {_86807 : Type'} (t : _86807 -> Prop) (s : _86807 -> Prop) : (term11 _86807 t s) = (t = s).
Proof. exact (@lem3322222 (t = s)). Qed.
Lemma lem3322226 {_86807 : Type'} (t : _86807 -> Prop) (s : _86807 -> Prop) : (term9 _86807 s t) = (t = s).
Proof. exact (TRANS (@lem3322220 _86807 t s) (@lem3322223 _86807 t s)). Qed.
Lemma lem3322227 {_86807 : Type'} (t : _86807 -> Prop) (s : _86807 -> Prop) : (term8 _86807 t s) = (t = s).
Proof. exact (TRANS (@lem3322210 _86807 s t) (@lem3322226 _86807 t s)). Qed.
Lemma lem3322228 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3322229 {_86807 : Type'} (t : _86807 -> Prop) (s : _86807 -> Prop) : (term12 _86807 t s) = (term13 _86807 t s).
Proof. exact (MK_COMB (@lem3322228) (@lem3322227 _86807 t s)). Qed.
Lemma lem3322231 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3322232 {_86807 : Type'} (P : _86807 -> Prop) (x : _86807) : (@IN _86807 x P) = (P x).
Proof. exact (@lem3322231 _86807 P x). Qed.
Lemma lem3322233 {_86807 : Type'} (t : _86807 -> Prop) (x : _86807) : (@IN _86807 x t) = (t x).
Proof. exact (@lem3322232 _86807 t x). Qed.
Lemma lem3322234 {_86807 : Type'} (s : _86807 -> Prop) (t : _86807 -> Prop) (x : _86807) : (term14 _86807 s x t) = (term15 _86807 s t x).
Proof. exact (MK_COMB (@lem3322229 _86807 t s) (@lem3322233 _86807 t x)). Qed.
Lemma lem3322237 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term16 _86807 s x) = (term17 _86807 s x).
Proof. exact (fun_ext (fun t : _86807 -> Prop => @lem3322234 _86807 s t x)). Qed.
Lemma lem3322238 {_86807 : Type'} : (@ex (_86807 -> Prop)) = (@ex (_86807 -> Prop)).
Proof. exact (eq_refl (@ex (_86807 -> Prop))). Qed.
Lemma lem3322239 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term3 _86807 s x) = (term18 _86807 s x).
Proof. exact (MK_COMB (@lem3322238 _86807) (@lem3322237 _86807 s x)). Qed.
Lemma lem3322244 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term2 _86807 x s) = (term18 _86807 s x).
Proof. exact (TRANS (@lem3322200 _86807 s x) (@lem3322239 _86807 s x)). Qed.
Lemma lem3322245 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3322246 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term19 _86807 x s) = (term20 _86807 s x).
Proof. exact (MK_COMB (@lem3322245) (@lem3322244 _86807 s x)). Qed.
Lemma lem3322248 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3322249 {_86807 : Type'} (P : _86807 -> Prop) (x : _86807) : (@IN _86807 x P) = (P x).
Proof. exact (@lem3322248 _86807 P x). Qed.
Lemma lem3322250 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (@IN _86807 x s) = (s x).
Proof. exact (@lem3322249 _86807 s x). Qed.
Lemma lem3322251 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : ((term2 _86807 x s) = (@IN _86807 x s)) = ((term18 _86807 s x) = (s x)).
Proof. exact (MK_COMB (@lem3322246 _86807 s x) (@lem3322250 _86807 s x)). Qed.
Lemma lem3322254 {_86807 : Type'} (s : _86807 -> Prop) : (term21 _86807 s) = (term22 _86807 s).
Proof. exact (fun_ext (fun x : _86807 => @lem3322251 _86807 s x)). Qed.
Lemma lem3322255 {_86807 : Type'} : (@all _86807) = (@all _86807).
Proof. exact (eq_refl (@all _86807)). Qed.
Lemma lem3322256 {_86807 : Type'} (s : _86807 -> Prop) : (term23 _86807 s) = (term24 _86807 s).
Proof. exact (MK_COMB (@lem3322255 _86807) (@lem3322254 _86807 s)). Qed.
Lemma lem3322261 {_86807 : Type'} (s : _86807 -> Prop) : (term24 _86807 s) = (term23 _86807 s).
Proof. exact (SYM (@lem3322256 _86807 s)). Qed.
Lemma lem3322263 (p : Prop) : p = (term25 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3322264 {_86807 : Type'} (s : _86807 -> Prop) : (term24 _86807 s) = (term26 _86807 s).
Proof. exact (@lem3322263 (term24 _86807 s)). Qed.
Lemma lem3322265 {_86807 : Type'} (s : _86807 -> Prop) : (term26 _86807 s) = (term24 _86807 s).
Proof. exact (SYM (@lem3322264 _86807 s)). Qed.
Lemma lem3322266 {_86807 : Type'} (s : _86807 -> Prop) (h1 : term27 _86807 s) : term27 _86807 s.
Proof. exact (h1). Qed.
Lemma lem3322269 {_86807 : Type'} (s : _86807 -> Prop) (h1 : term26 _86807 s) : term26 _86807 s.
Proof. exact (h1). Qed.
Lemma lem3322270 {_86807 : Type'} (s : _86807 -> Prop) : term28 _86807 s.
Proof. exact (fun h0 : term26 _86807 s => @lem3322269 _86807 s h0). Qed.
Lemma lem3322271 {_86807 : Type'} (s : _86807 -> Prop) (h1 : term28 _86807 s) : term28 _86807 s.
Proof. exact (h1). Qed.
Lemma lem3322272 {_86807 : Type'} (s : _86807 -> Prop) (h1 : term26 _86807 s) : term26 _86807 s.
Proof. exact (h1). Qed.
Lemma lem3322273 {_86807 : Type'} (s : _86807 -> Prop) (h1 : term26 _86807 s) (h2 : term28 _86807 s) : term26 _86807 s.
Proof. exact (@lem3322271 _86807 s h2 (@lem3322272 _86807 s h1)). Qed.
Lemma lem3322274 {_86807 : Type'} (s : _86807 -> Prop) (h1 : term26 _86807 s) : term29 _86807 s.
Proof. exact (fun h0 : term28 _86807 s => @lem3322273 _86807 s h1 h0). Qed.
Lemma lem3322275 {_86807 : Type'} (s : _86807 -> Prop) (h1 : term28 _86807 s) : term28 _86807 s.
Proof. exact (h1). Qed.
Lemma lem3322276 {_86807 : Type'} (s : _86807 -> Prop) (h1 : term26 _86807 s) (h2 : term28 _86807 s) : term26 _86807 s.
Proof. exact (@lem3322274 _86807 s h1 (@lem3322275 _86807 s h2)). Qed.
Lemma lem3322277 {_86807 : Type'} (s : _86807 -> Prop) (h1 : term28 _86807 s) : term28 _86807 s.
Proof. exact (fun h0 : term26 _86807 s => @lem3322276 _86807 s h0 h1). Qed.
Lemma lem3322278 {_86807 : Type'} (s : _86807 -> Prop) : term30 _86807 s.
Proof. exact (fun h0 : term28 _86807 s => @lem3322277 _86807 s h0). Qed.
Lemma lem3322281 {_86807 : Type'} (s : _86807 -> Prop) : term28 _86807 s.
Proof. exact (@lem3322278 _86807 s (@lem3322270 _86807 s)). Qed.
Lemma lem3322282 {_86807 : Type'} (s : _86807 -> Prop) : term28 _86807 s.
Proof. exact (@lem3322281 _86807 s). Qed.
Lemma lem3322288 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3322289 {_86807 : Type'} (s : _86807 -> Prop) : (term26 _86807 s) = (term31 _86807 s).
Proof. exact (@lem3322288 (term27 _86807 s)). Qed.
Lemma lem3322291 (t : Prop) : (term32 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3322292 {_86807 : Type'} (s : _86807 -> Prop) : (term31 _86807 s) = (term24 _86807 s).
Proof. exact (@lem3322291 (term24 _86807 s)). Qed.
Lemma lem3322297 {_86807 : Type'} (s : _86807 -> Prop) : (term26 _86807 s) = (term24 _86807 s).
Proof. exact (TRANS (@lem3322289 _86807 s) (@lem3322292 _86807 s)). Qed.
Lemma lem3322348 {_86807 : Type'} : (term33 _86807) = (term34 _86807).
Proof. exact (fun_ext (fun s : _86807 -> Prop => @lem3322297 _86807 s)). Qed.
Lemma lem3322349 {_86807 : Type'} : (@all (_86807 -> Prop)) = (@all (_86807 -> Prop)).
Proof. exact (eq_refl (@all (_86807 -> Prop))). Qed.
Lemma lem3322358 {_86807 : Type'} : (term35 _86807) = (term36 _86807).
Proof. exact (MK_COMB (@lem3322349 _86807) (@lem3322348 _86807)). Qed.
Lemma lem3322359 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3322364 {_86807 : Type'} (s : _86807 -> Prop) (t : _86807 -> Prop) (x : _86807) : (term15 _86807 s t x) = (term15 _86807 s t x).
Proof. exact (eq_refl (term15 _86807 s t x)). Qed.
Lemma lem3322365 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term17 _86807 s x) = (term17 _86807 s x).
Proof. exact (fun_ext (fun t : _86807 -> Prop => @lem3322364 _86807 s t x)). Qed.
Lemma lem3322366 {_86807 : Type'} : (@ex (_86807 -> Prop)) = (@ex (_86807 -> Prop)).
Proof. exact (eq_refl (@ex (_86807 -> Prop))). Qed.
Lemma lem3322367 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term18 _86807 s x) = (term18 _86807 s x).
Proof. exact (MK_COMB (@lem3322366 _86807) (@lem3322365 _86807 s x)). Qed.
Lemma lem3322368 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3322369 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term20 _86807 s x) = (term20 _86807 s x).
Proof. exact (MK_COMB (@lem3322368) (@lem3322367 _86807 s x)). Qed.
Lemma lem3322370 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : ((term18 _86807 s x) = (s x)) = ((term18 _86807 s x) = (s x)).
Proof. exact (MK_COMB (@lem3322369 _86807 s x) (@lem3322359 _86807 s x)). Qed.
Lemma lem3322371 {_86807 : Type'} (s : _86807 -> Prop) : (term22 _86807 s) = (term22 _86807 s).
Proof. exact (fun_ext (fun x : _86807 => @lem3322370 _86807 s x)). Qed.
Lemma lem3322372 {_86807 : Type'} : (@all _86807) = (@all _86807).
Proof. exact (eq_refl (@all _86807)). Qed.
Lemma lem3322373 {_86807 : Type'} (s : _86807 -> Prop) : (term24 _86807 s) = (term24 _86807 s).
Proof. exact (MK_COMB (@lem3322372 _86807) (@lem3322371 _86807 s)). Qed.
Lemma lem3322374 {_86807 : Type'} : (term34 _86807) = (term34 _86807).
Proof. exact (fun_ext (fun s : _86807 -> Prop => @lem3322373 _86807 s)). Qed.
Lemma lem3322375 {_86807 : Type'} : (@all (_86807 -> Prop)) = (@all (_86807 -> Prop)).
Proof. exact (eq_refl (@all (_86807 -> Prop))). Qed.
Lemma lem3322376 {_86807 : Type'} : (term36 _86807) = (term36 _86807).
Proof. exact (MK_COMB (@lem3322375 _86807) (@lem3322374 _86807)). Qed.
Lemma lem3322399 {_86807 : Type'} : (term35 _86807) = (term36 _86807).
Proof. exact (TRANS (@lem3322358 _86807) (@lem3322376 _86807)). Qed.
Lemma lem3322400 {_86807 : Type'} : (term36 _86807) = (term35 _86807).
Proof. exact (SYM (@lem3322399 _86807)). Qed.
Lemma lem3322402 (p : Prop) : p = (term25 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3322403 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : ((term18 _86807 s x) = (s x)) = (term37 _86807 s x).
Proof. exact (@lem3322402 ((term18 _86807 s x) = (s x))). Qed.
Lemma lem3322404 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term37 _86807 s x) = ((term18 _86807 s x) = (s x)).
Proof. exact (SYM (@lem3322403 _86807 s x)). Qed.
Lemma lem3322405 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) (h1 : term38 _86807 s x) : term38 _86807 s x.
Proof. exact (h1). Qed.
Lemma lem3322414 {_86807 : Type'} (s : _86807 -> Prop) (t : _86807 -> Prop) (x : _86807) : (term39 _86807 s t x) = (term40 _86807 s t x).
Proof. exact (@lem17045 (t = s) (t x)). Qed.
Lemma lem3322417 {_86807 : Type'} (s : _86807 -> Prop) (t : _86807 -> Prop) (x : _86807) : (term15 _86807 s t x) = (term15 _86807 s t x).
Proof. exact (eq_refl (term15 _86807 s t x)). Qed.
Lemma lem3322418 {_86807 : Type'} (P : type686 _86807) : (term41 _86807 P) = (term42 _86807 P).
Proof. exact (@lem18394 (_86807 -> Prop) P). Qed.
Lemma lem3322419 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term43 _86807 s x) = (term44 _86807 s x).
Proof. exact (@lem3322418 _86807 (term17 _86807 s x)). Qed.
Lemma lem3322420 {_86807 : Type'} (s : _86807 -> Prop) (t : _86807 -> Prop) (x : _86807) : (term45 _86807 s x t) = (term15 _86807 s t x).
Proof. exact (eq_refl (term45 _86807 s x t)). Qed.
Lemma lem3322421 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3322422 {_86807 : Type'} (s : _86807 -> Prop) (t : _86807 -> Prop) (x : _86807) : (term46 _86807 s x t) = (term39 _86807 s t x).
Proof. exact (MK_COMB (@lem3322421) (@lem3322420 _86807 s t x)). Qed.
Lemma lem3322423 {_86807 : Type'} (s : _86807 -> Prop) (t : _86807 -> Prop) (x : _86807) : (term46 _86807 s x t) = (term40 _86807 s t x).
Proof. exact (TRANS (@lem3322422 _86807 s t x) (@lem3322414 _86807 s t x)). Qed.
Lemma lem3322424 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term47 _86807 s x) = (term48 _86807 s x).
Proof. exact (fun_ext (fun t : _86807 -> Prop => @lem3322423 _86807 s t x)). Qed.
Lemma lem3322425 {_86807 : Type'} : (@all (_86807 -> Prop)) = (@all (_86807 -> Prop)).
Proof. exact (eq_refl (@all (_86807 -> Prop))). Qed.
Lemma lem3322426 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term44 _86807 s x) = (term49 _86807 s x).
Proof. exact (MK_COMB (@lem3322425 _86807) (@lem3322424 _86807 s x)). Qed.
Lemma lem3322427 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term43 _86807 s x) = (term49 _86807 s x).
Proof. exact (TRANS (@lem3322419 _86807 s x) (@lem3322426 _86807 s x)). Qed.
Lemma lem3322428 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term17 _86807 s x) = (term17 _86807 s x).
Proof. exact (fun_ext (fun t : _86807 -> Prop => @lem3322417 _86807 s t x)). Qed.
Lemma lem3322429 {_86807 : Type'} : (@ex (_86807 -> Prop)) = (@ex (_86807 -> Prop)).
Proof. exact (eq_refl (@ex (_86807 -> Prop))). Qed.
Lemma lem3322430 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term18 _86807 s x) = (term18 _86807 s x).
Proof. exact (MK_COMB (@lem3322429 _86807) (@lem3322428 _86807 s x)). Qed.
Lemma lem3322431 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term50 _86807 s x) = (term50 _86807 s x).
Proof. exact (eq_refl (term50 _86807 s x)). Qed.
Lemma lem3322432 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3322433 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3322434 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term51 _86807 s x) = (term52 _86807 s x).
Proof. exact (MK_COMB (@lem3322433) (@lem3322427 _86807 s x)). Qed.
Lemma lem3322435 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term53 _86807 s x) = (term54 _86807 s x).
Proof. exact (MK_COMB (@lem3322434 _86807 s x) (@lem3322432 _86807 s x)). Qed.
Lemma lem3322436 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3322437 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term55 _86807 s x) = (term55 _86807 s x).
Proof. exact (MK_COMB (@lem3322436) (@lem3322430 _86807 s x)). Qed.
Lemma lem3322438 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term56 _86807 s x) = (term56 _86807 s x).
Proof. exact (MK_COMB (@lem3322437 _86807 s x) (@lem3322431 _86807 s x)). Qed.
Lemma lem3322439 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3322440 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term57 _86807 s x) = (term57 _86807 s x).
Proof. exact (MK_COMB (@lem3322439) (@lem3322438 _86807 s x)). Qed.
Lemma lem3322441 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term58 _86807 s x) = (term59 _86807 s x).
Proof. exact (MK_COMB (@lem3322440 _86807 s x) (@lem3322435 _86807 s x)). Qed.
Lemma lem3322442 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term38 _86807 s x) = (term58 _86807 s x).
Proof. exact (@lem17646 (term18 _86807 s x) (s x)). Qed.
Lemma lem3322443 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term38 _86807 s x) = (term59 _86807 s x).
Proof. exact (TRANS (@lem3322442 _86807 s x) (@lem3322441 _86807 s x)). Qed.
Lemma lem3322542 {A : Type'} (P : A -> Prop) (Q : Prop) : (term60 A P Q) = (term61 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3322543 {_86807 : Type'} (P : type686 _86807) (Q : Prop) : (term62 _86807 P Q) = (term63 _86807 P Q).
Proof. exact (@lem3322542 (_86807 -> Prop) P Q). Qed.
Lemma lem3322544 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term64 _86807 s x) = (term65 _86807 s x).
Proof. exact (@lem3322543 _86807 (term17 _86807 s x) (term50 _86807 s x)). Qed.
Lemma lem3322545 {_86807 : Type'} (s : _86807 -> Prop) (t : _86807 -> Prop) (x : _86807) : (term45 _86807 s x t) = (term15 _86807 s t x).
Proof. exact (eq_refl (term45 _86807 s x t)). Qed.
Lemma lem3322546 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term66 _86807 s x) = (term17 _86807 s x).
Proof. exact (fun_ext (fun t : _86807 -> Prop => @lem3322545 _86807 s t x)). Qed.
Lemma lem3322547 {_86807 : Type'} : (@ex (_86807 -> Prop)) = (@ex (_86807 -> Prop)).
Proof. exact (eq_refl (@ex (_86807 -> Prop))). Qed.
Lemma lem3322548 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term67 _86807 s x) = (term18 _86807 s x).
Proof. exact (MK_COMB (@lem3322547 _86807) (@lem3322546 _86807 s x)). Qed.
Lemma lem3322549 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3322550 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term68 _86807 s x) = (term55 _86807 s x).
Proof. exact (MK_COMB (@lem3322549) (@lem3322548 _86807 s x)). Qed.
Lemma lem3322551 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term50 _86807 s x) = (term50 _86807 s x).
Proof. exact (eq_refl (term50 _86807 s x)). Qed.
Lemma lem3322552 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term64 _86807 s x) = (term56 _86807 s x).
Proof. exact (MK_COMB (@lem3322550 _86807 s x) (@lem3322551 _86807 s x)). Qed.
Lemma lem3322553 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3322554 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term69 _86807 s x) = (term70 _86807 s x).
Proof. exact (MK_COMB (@lem3322553) (@lem3322552 _86807 s x)). Qed.
Lemma lem3322555 {_86807 : Type'} (s : _86807 -> Prop) (t : _86807 -> Prop) (x : _86807) : (term45 _86807 s x t) = (term15 _86807 s t x).
Proof. exact (eq_refl (term45 _86807 s x t)). Qed.
Lemma lem3322556 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3322557 {_86807 : Type'} (s : _86807 -> Prop) (t : _86807 -> Prop) (x : _86807) : (term71 _86807 s x t) = (term72 _86807 s t x).
Proof. exact (MK_COMB (@lem3322556) (@lem3322555 _86807 s t x)). Qed.
Lemma lem3322558 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term50 _86807 s x) = (term50 _86807 s x).
Proof. exact (eq_refl (term50 _86807 s x)). Qed.
Lemma lem3322559 {_86807 : Type'} (t : _86807 -> Prop) (s : _86807 -> Prop) (x : _86807) : (term73 _86807 t s x) = (term74 _86807 t s x).
Proof. exact (MK_COMB (@lem3322557 _86807 s t x) (@lem3322558 _86807 s x)). Qed.
Lemma lem3322560 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term75 _86807 s x) = (term76 _86807 s x).
Proof. exact (fun_ext (fun t : _86807 -> Prop => @lem3322559 _86807 t s x)). Qed.
Lemma lem3322561 {_86807 : Type'} : (@ex (_86807 -> Prop)) = (@ex (_86807 -> Prop)).
Proof. exact (eq_refl (@ex (_86807 -> Prop))). Qed.
Lemma lem3322562 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term65 _86807 s x) = (term77 _86807 s x).
Proof. exact (MK_COMB (@lem3322561 _86807) (@lem3322560 _86807 s x)). Qed.
Lemma lem3322563 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : ((term64 _86807 s x) = (term65 _86807 s x)) = ((term56 _86807 s x) = (term77 _86807 s x)).
Proof. exact (MK_COMB (@lem3322554 _86807 s x) (@lem3322562 _86807 s x)). Qed.
Lemma lem3322564 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term56 _86807 s x) = (term77 _86807 s x).
Proof. exact (EQ_MP (@lem3322563 _86807 s x) (@lem3322544 _86807 s x)). Qed.
Lemma lem3322565 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3322566 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term57 _86807 s x) = (term78 _86807 s x).
Proof. exact (MK_COMB (@lem3322565) (@lem3322564 _86807 s x)). Qed.
Lemma lem3322567 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term54 _86807 s x) = (term54 _86807 s x).
Proof. exact (eq_refl (term54 _86807 s x)). Qed.
Lemma lem3322568 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term59 _86807 s x) = (term79 _86807 s x).
Proof. exact (MK_COMB (@lem3322566 _86807 s x) (@lem3322567 _86807 s x)). Qed.
Lemma lem3322570 {A : Type'} (P : A -> Prop) (Q : Prop) : (term80 A P Q) = (term81 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3322571 {_86807 : Type'} (P : type686 _86807) (Q : Prop) : (term82 _86807 P Q) = (term83 _86807 P Q).
Proof. exact (@lem3322570 (_86807 -> Prop) P Q). Qed.
Lemma lem3322572 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term84 _86807 s x) = (term85 _86807 s x).
Proof. exact (@lem3322571 _86807 (term76 _86807 s x) (term54 _86807 s x)). Qed.
Lemma lem3322573 {_86807 : Type'} (t : _86807 -> Prop) (s : _86807 -> Prop) (x : _86807) : (term86 _86807 s x t) = (term74 _86807 t s x).
Proof. exact (eq_refl (term86 _86807 s x t)). Qed.
Lemma lem3322574 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term87 _86807 s x) = (term76 _86807 s x).
Proof. exact (fun_ext (fun t : _86807 -> Prop => @lem3322573 _86807 t s x)). Qed.
Lemma lem3322575 {_86807 : Type'} : (@ex (_86807 -> Prop)) = (@ex (_86807 -> Prop)).
Proof. exact (eq_refl (@ex (_86807 -> Prop))). Qed.
Lemma lem3322576 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term88 _86807 s x) = (term77 _86807 s x).
Proof. exact (MK_COMB (@lem3322575 _86807) (@lem3322574 _86807 s x)). Qed.
Lemma lem3322577 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3322578 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term89 _86807 s x) = (term78 _86807 s x).
Proof. exact (MK_COMB (@lem3322577) (@lem3322576 _86807 s x)). Qed.
Lemma lem3322579 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term54 _86807 s x) = (term54 _86807 s x).
Proof. exact (eq_refl (term54 _86807 s x)). Qed.
Lemma lem3322580 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term84 _86807 s x) = (term79 _86807 s x).
Proof. exact (MK_COMB (@lem3322578 _86807 s x) (@lem3322579 _86807 s x)). Qed.
Lemma lem3322581 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3322582 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term90 _86807 s x) = (term91 _86807 s x).
Proof. exact (MK_COMB (@lem3322581) (@lem3322580 _86807 s x)). Qed.
Lemma lem3322583 {_86807 : Type'} (t : _86807 -> Prop) (s : _86807 -> Prop) (x : _86807) : (term86 _86807 s x t) = (term74 _86807 t s x).
Proof. exact (eq_refl (term86 _86807 s x t)). Qed.
Lemma lem3322584 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3322585 {_86807 : Type'} (t : _86807 -> Prop) (s : _86807 -> Prop) (x : _86807) : (term92 _86807 s x t) = (term93 _86807 t s x).
Proof. exact (MK_COMB (@lem3322584) (@lem3322583 _86807 t s x)). Qed.
Lemma lem3322586 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term54 _86807 s x) = (term54 _86807 s x).
Proof. exact (eq_refl (term54 _86807 s x)). Qed.
Lemma lem3322587 {_86807 : Type'} (t : _86807 -> Prop) (s : _86807 -> Prop) (x : _86807) : (term94 _86807 t s x) = (term95 _86807 t s x).
Proof. exact (MK_COMB (@lem3322585 _86807 t s x) (@lem3322586 _86807 s x)). Qed.
Lemma lem3322588 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term96 _86807 s x) = (term97 _86807 s x).
Proof. exact (fun_ext (fun t : _86807 -> Prop => @lem3322587 _86807 t s x)). Qed.
Lemma lem3322589 {_86807 : Type'} : (@ex (_86807 -> Prop)) = (@ex (_86807 -> Prop)).
Proof. exact (eq_refl (@ex (_86807 -> Prop))). Qed.
Lemma lem3322590 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term85 _86807 s x) = (term98 _86807 s x).
Proof. exact (MK_COMB (@lem3322589 _86807) (@lem3322588 _86807 s x)). Qed.
Lemma lem3322591 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : ((term84 _86807 s x) = (term85 _86807 s x)) = ((term79 _86807 s x) = (term98 _86807 s x)).
Proof. exact (MK_COMB (@lem3322582 _86807 s x) (@lem3322590 _86807 s x)). Qed.
Lemma lem3322592 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term79 _86807 s x) = (term98 _86807 s x).
Proof. exact (EQ_MP (@lem3322591 _86807 s x) (@lem3322572 _86807 s x)). Qed.
Lemma lem3322594 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term59 _86807 s x) = (term98 _86807 s x).
Proof. exact (TRANS (@lem3322568 _86807 s x) (@lem3322592 _86807 s x)). Qed.
Lemma lem3322595 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term38 _86807 s x) = (term98 _86807 s x).
Proof. exact (TRANS (@lem3322443 _86807 s x) (@lem3322594 _86807 s x)). Qed.
Lemma lem3322596 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) (h1 : term38 _86807 s x) : term98 _86807 s x.
Proof. exact (EQ_MP (@lem3322595 _86807 s x) (@lem3322405 _86807 s x h1)). Qed.
Lemma lem3322597 {_86807 : Type'} (t : _86807 -> Prop) (s : _86807 -> Prop) (x : _86807) (h1 : term95 _86807 t s x) : term95 _86807 t s x.
Proof. exact (h1). Qed.
Lemma lem3322602 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3322603 {_86807 : Type'} (f : _86807 -> Prop) (x : _86807) : (f x) = (@I (_86807 -> Prop) f x).
Proof. exact (@lem3322602 _86807 Prop f x). Qed.
Lemma lem3322605 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (s x) = (@I (_86807 -> Prop) s x).
Proof. exact (@lem3322603 _86807 s x). Qed.
Lemma lem3322606 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3322611 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3322612 {_86807 : Type'} (f : _86807 -> Prop) (x : _86807) : (f x) = (@I (_86807 -> Prop) f x).
Proof. exact (@lem3322611 _86807 Prop f x). Qed.
Lemma lem3322614 {_86807 : Type'} (t : _86807 -> Prop) (x : _86807) : (t x) = (@I (_86807 -> Prop) t x).
Proof. exact (@lem3322612 _86807 t x). Qed.
Lemma lem3322615 {_86807 : Type'} (t : _86807 -> Prop) (x : _86807) : (term50 _86807 t x) = (term99 _86807 t x).
Proof. exact (MK_COMB (@lem3322606) (@lem3322614 _86807 t x)). Qed.
Lemma lem3322624 {_86807 : Type'} (t : _86807 -> Prop) (s : _86807 -> Prop) : (term100 _86807 t s) = (term100 _86807 t s).
Proof. exact (eq_refl (term100 _86807 t s)). Qed.
Lemma lem3322625 {_86807 : Type'} (s : _86807 -> Prop) (t : _86807 -> Prop) (x : _86807) : (term40 _86807 s t x) = (term101 _86807 s t x).
Proof. exact (MK_COMB (@lem3322624 _86807 t s) (@lem3322615 _86807 t x)). Qed.
Lemma lem3322626 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term48 _86807 s x) = (term102 _86807 s x).
Proof. exact (fun_ext (fun t : _86807 -> Prop => @lem3322625 _86807 s t x)). Qed.
Lemma lem3322627 {_86807 : Type'} : (@all (_86807 -> Prop)) = (@all (_86807 -> Prop)).
Proof. exact (eq_refl (@all (_86807 -> Prop))). Qed.
Lemma lem3322628 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term49 _86807 s x) = (term103 _86807 s x).
Proof. exact (MK_COMB (@lem3322627 _86807) (@lem3322626 _86807 s x)). Qed.
Lemma lem3322629 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3322630 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term52 _86807 s x) = (term104 _86807 s x).
Proof. exact (MK_COMB (@lem3322629) (@lem3322628 _86807 s x)). Qed.
Lemma lem3322631 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term54 _86807 s x) = (term105 _86807 s x).
Proof. exact (MK_COMB (@lem3322630 _86807 s x) (@lem3322605 _86807 s x)). Qed.
Lemma lem3322632 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3322637 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3322638 {_86807 : Type'} (f : _86807 -> Prop) (x : _86807) : (f x) = (@I (_86807 -> Prop) f x).
Proof. exact (@lem3322637 _86807 Prop f x). Qed.
Lemma lem3322640 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (s x) = (@I (_86807 -> Prop) s x).
Proof. exact (@lem3322638 _86807 s x). Qed.
Lemma lem3322641 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term50 _86807 s x) = (term99 _86807 s x).
Proof. exact (MK_COMB (@lem3322632) (@lem3322640 _86807 s x)). Qed.
Lemma lem3322646 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3322647 {_86807 : Type'} (f : _86807 -> Prop) (x : _86807) : (f x) = (@I (_86807 -> Prop) f x).
Proof. exact (@lem3322646 _86807 Prop f x). Qed.
Lemma lem3322649 {_86807 : Type'} (t : _86807 -> Prop) (x : _86807) : (t x) = (@I (_86807 -> Prop) t x).
Proof. exact (@lem3322647 _86807 t x). Qed.
Lemma lem3322656 {_86807 : Type'} (t : _86807 -> Prop) (s : _86807 -> Prop) : (term13 _86807 t s) = (term13 _86807 t s).
Proof. exact (eq_refl (term13 _86807 t s)). Qed.
Lemma lem3322657 {_86807 : Type'} (s : _86807 -> Prop) (t : _86807 -> Prop) (x : _86807) : (term15 _86807 s t x) = (term106 _86807 s t x).
Proof. exact (MK_COMB (@lem3322656 _86807 t s) (@lem3322649 _86807 t x)). Qed.
Lemma lem3322658 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3322659 {_86807 : Type'} (s : _86807 -> Prop) (t : _86807 -> Prop) (x : _86807) : (term72 _86807 s t x) = (term107 _86807 s t x).
Proof. exact (MK_COMB (@lem3322658) (@lem3322657 _86807 s t x)). Qed.
Lemma lem3322660 {_86807 : Type'} (t : _86807 -> Prop) (s : _86807 -> Prop) (x : _86807) : (term74 _86807 t s x) = (term108 _86807 t s x).
Proof. exact (MK_COMB (@lem3322659 _86807 s t x) (@lem3322641 _86807 s x)). Qed.
Lemma lem3322661 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3322662 {_86807 : Type'} (t : _86807 -> Prop) (s : _86807 -> Prop) (x : _86807) : (term93 _86807 t s x) = (term109 _86807 t s x).
Proof. exact (MK_COMB (@lem3322661) (@lem3322660 _86807 t s x)). Qed.
Lemma lem3322663 {_86807 : Type'} (t : _86807 -> Prop) (s : _86807 -> Prop) (x : _86807) : (term95 _86807 t s x) = (term110 _86807 t s x).
Proof. exact (MK_COMB (@lem3322662 _86807 t s x) (@lem3322631 _86807 s x)). Qed.
Lemma lem3322664 {_86807 : Type'} (t : _86807 -> Prop) (s : _86807 -> Prop) (x : _86807) (h1 : term95 _86807 t s x) : term110 _86807 t s x.
Proof. exact (EQ_MP (@lem3322663 _86807 t s x) (@lem3322597 _86807 t s x h1)). Qed.
Lemma lem3322665 {_86807 : Type'} (t : _86807 -> Prop) (s : _86807 -> Prop) (x : _86807) (h1 : term108 _86807 t s x) : term108 _86807 t s x.
Proof. exact (h1). Qed.
Lemma lem3322666 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) (h1 : term105 _86807 s x) : term105 _86807 s x.
Proof. exact (h1). Qed.
Lemma lem3322668 {_86807 : Type'} (t : _86807 -> Prop) (s : _86807 -> Prop) (x : _86807) (h1 : term108 _86807 t s x) : term106 _86807 s t x.
Proof. exact (proj1 (@lem3322665 _86807 t s x h1)). Qed.
Lemma lem3322672 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) (h1 : term105 _86807 s x) : term103 _86807 s x.
Proof. exact (proj1 (@lem3322666 _86807 s x h1)). Qed.
Lemma lem3322692 {_86807 : Type'} (s : _86807 -> Prop) (t : _86807 -> Prop) (x : _86807) : (term101 _86807 s t x) = (term101 _86807 s t x).
Proof. exact (eq_refl (term101 _86807 s t x)). Qed.
Lemma lem3322693 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term102 _86807 s x) = (term102 _86807 s x).
Proof. exact (fun_ext (fun t : _86807 -> Prop => @lem3322692 _86807 s t x)). Qed.
Lemma lem3322694 {_86807 : Type'} : (@all (_86807 -> Prop)) = (@all (_86807 -> Prop)).
Proof. exact (eq_refl (@all (_86807 -> Prop))). Qed.
Lemma lem3322696 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term103 _86807 s x) = (term103 _86807 s x).
Proof. exact (MK_COMB (@lem3322694 _86807) (@lem3322693 _86807 s x)). Qed.
Lemma lem3322697 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) (h1 : term105 _86807 s x) : term103 _86807 s x.
Proof. exact (EQ_MP (@lem3322696 _86807 s x) (@lem3322672 _86807 s x h1)). Qed.
Lemma lem3322702 {_86807 : Type'} (_34464 : _86807 -> Prop) (s : _86807 -> Prop) (x : _86807) (h1 : term105 _86807 s x) : term111 _86807 s x _34464.
Proof. exact (@lem3322697 _86807 s x h1 _34464). Qed.
Lemma lem3322703 {_86807 : Type'} (s : _86807 -> Prop) (_34464 : _86807 -> Prop) (x : _86807) : (term111 _86807 s x _34464) = (term101 _86807 s _34464 x).
Proof. exact (eq_refl (term111 _86807 s x _34464)). Qed.
Lemma lem3322708 {_86807 : Type'} (t : _86807 -> Prop) (s : _86807 -> Prop) (x : _86807) (h1 : term108 _86807 t s x) : t = s.
Proof. exact (proj1 (@lem3322668 _86807 t s x h1)). Qed.
Lemma lem3322710 {_86807 : Type'} (t : _86807 -> Prop) (s : _86807 -> Prop) (x : _86807) (h1 : term108 _86807 t s x) : @I (_86807 -> Prop) t x.
Proof. exact (proj2 (@lem3322668 _86807 t s x h1)). Qed.
Lemma lem3322716 {_86807 : Type'} (_34464 : _86807 -> Prop) (s : _86807 -> Prop) (x : _86807) (h1 : term105 _86807 s x) : term101 _86807 s _34464 x.
Proof. exact (EQ_MP (@lem3322703 _86807 s _34464 x) (@lem3322702 _86807 _34464 s x h1)). Qed.
Lemma lem3322746 {_86807 : Type'} (t : _86807 -> Prop) (s : _86807 -> Prop) (x : _86807) (h1 : term108 _86807 t s x) : term99 _86807 s x.
Proof. exact (proj2 (@lem3322665 _86807 t s x h1)). Qed.
Lemma lem3322747 {_86807 : Type'} (x : _86807) : (term112 _86807 x) = (term112 _86807 x).
Proof. exact (eq_refl (term112 _86807 x)). Qed.
Lemma lem3322748 {_86807 : Type'} (t : _86807 -> Prop) (s : _86807 -> Prop) (x : _86807) (h1 : term108 _86807 t s x) : (term113 _86807 x t) = (term113 _86807 x s).
Proof. exact (MK_COMB (@lem3322747 _86807 x) (@lem3322708 _86807 t s x h1)). Qed.
Lemma lem3322749 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term113 _86807 x s) = (@I (_86807 -> Prop) s x).
Proof. exact (eq_refl (term113 _86807 x s)). Qed.
Lemma lem3322750 {_86807 : Type'} (x : _86807) (t : _86807 -> Prop) : (term114 _86807 x t) = (term114 _86807 x t).
Proof. exact (eq_refl (term114 _86807 x t)). Qed.
Lemma lem3322751 {_86807 : Type'} (t : _86807 -> Prop) (s : _86807 -> Prop) (x : _86807) : ((term113 _86807 x t) = (term113 _86807 x s)) = ((term113 _86807 x t) = (@I (_86807 -> Prop) s x)).
Proof. exact (MK_COMB (@lem3322750 _86807 x t) (@lem3322749 _86807 s x)). Qed.
Lemma lem3322752 {_86807 : Type'} (t : _86807 -> Prop) (x : _86807) : (term113 _86807 x t) = (@I (_86807 -> Prop) t x).
Proof. exact (eq_refl (term113 _86807 x t)). Qed.
Lemma lem3322753 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3322754 {_86807 : Type'} (t : _86807 -> Prop) (x : _86807) : (term114 _86807 x t) = (term115 _86807 t x).
Proof. exact (MK_COMB (@lem3322753) (@lem3322752 _86807 t x)). Qed.
Lemma lem3322755 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (@I (_86807 -> Prop) s x) = (@I (_86807 -> Prop) s x).
Proof. exact (eq_refl (@I (_86807 -> Prop) s x)). Qed.
Lemma lem3322756 {_86807 : Type'} (t : _86807 -> Prop) (s : _86807 -> Prop) (x : _86807) : ((term113 _86807 x t) = (@I (_86807 -> Prop) s x)) = ((@I (_86807 -> Prop) t x) = (@I (_86807 -> Prop) s x)).
Proof. exact (MK_COMB (@lem3322754 _86807 t x) (@lem3322755 _86807 s x)). Qed.
Lemma lem3322757 {_86807 : Type'} (t : _86807 -> Prop) (s : _86807 -> Prop) (x : _86807) : ((term113 _86807 x t) = (term113 _86807 x s)) = ((@I (_86807 -> Prop) t x) = (@I (_86807 -> Prop) s x)).
Proof. exact (TRANS (@lem3322751 _86807 t s x) (@lem3322756 _86807 t s x)). Qed.
Lemma lem3322758 {_86807 : Type'} (t : _86807 -> Prop) (s : _86807 -> Prop) (x : _86807) (h1 : term108 _86807 t s x) : (@I (_86807 -> Prop) t x) = (@I (_86807 -> Prop) s x).
Proof. exact (EQ_MP (@lem3322757 _86807 t s x) (@lem3322748 _86807 t s x h1)). Qed.
Lemma lem3322761 {_86807 : Type'} (t : _86807 -> Prop) (s : _86807 -> Prop) (x : _86807) (h1 : term108 _86807 t s x) : @I (_86807 -> Prop) s x.
Proof. exact (EQ_MP (@lem3322758 _86807 t s x h1) (@lem3322710 _86807 t s x h1)). Qed.
Lemma lem3322762 {_86807 : Type'} (t : _86807 -> Prop) (s : _86807 -> Prop) (x : _86807) (h1 : term108 _86807 t s x) : term116 _86807 s x.
Proof. exact (fun h0 : term99 _86807 s x => @lem3322761 _86807 t s x h1). Qed.
Lemma lem3322764 (p : Prop) : (term117 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3322765 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term116 _86807 s x) = (@I (_86807 -> Prop) s x).
Proof. exact (@lem3322764 (@I (_86807 -> Prop) s x)). Qed.
Lemma lem3322766 {_86807 : Type'} (t : _86807 -> Prop) (s : _86807 -> Prop) (x : _86807) (h1 : term108 _86807 t s x) : @I (_86807 -> Prop) s x.
Proof. exact (EQ_MP (@lem3322765 _86807 s x) (@lem3322762 _86807 t s x h1)). Qed.
Lemma lem3322769 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3322771 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term99 _86807 s x) = (term118 _86807 s x).
Proof. exact (@lem3322769 (@I (_86807 -> Prop) s x)). Qed.
Lemma lem3322774 {_86807 : Type'} (t : _86807 -> Prop) (s : _86807 -> Prop) (x : _86807) (h1 : term108 _86807 t s x) : term118 _86807 s x.
Proof. exact (EQ_MP (@lem3322771 _86807 s x) (@lem3322746 _86807 t s x h1)). Qed.
Lemma lem3322777 {_86807 : Type'} (t : _86807 -> Prop) (s : _86807 -> Prop) (x : _86807) (h1 : term108 _86807 t s x) : False.
Proof. exact (@lem3322774 _86807 t s x h1 (@lem3322766 _86807 t s x h1)). Qed.
Lemma lem3322778 {_86807 : Type'} (t : _86807 -> Prop) (s : _86807 -> Prop) (x : _86807) (h1 : term108 _86807 t s x) : term119.
Proof. exact (fun h0 : ~ False => @lem3322777 _86807 t s x h1). Qed.
Lemma lem3322780 (p : Prop) : (term117 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3322781 : term119 = False.
Proof. exact (@lem3322780 False). Qed.
Lemma lem3322807 {_86807 : Type'} (x : _86807 -> Prop) : x = x.
Proof. exact (@lem21386 (_86807 -> Prop) x). Qed.
Lemma lem3322808 {_86807 : Type'} (x : _86807 -> Prop) : x = x.
Proof. exact (@lem3322807 _86807 x). Qed.
Lemma lem3322809 {_86807 : Type'} (s : _86807 -> Prop) : s = s.
Proof. exact (@lem3322808 _86807 s). Qed.
Lemma lem3322810 {_86807 : Type'} (s : _86807 -> Prop) : term120 _86807 s.
Proof. exact (fun h0 : term121 _86807 s => @lem3322809 _86807 s). Qed.
Lemma lem3322812 (p : Prop) : (term117 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3322813 {_86807 : Type'} (s : _86807 -> Prop) : (term120 _86807 s) = (s = s).
Proof. exact (@lem3322812 (s = s)). Qed.
Lemma lem3322814 {_86807 : Type'} (s : _86807 -> Prop) : s = s.
Proof. exact (EQ_MP (@lem3322813 _86807 s) (@lem3322810 _86807 s)). Qed.
Lemma lem3322816 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) (h1 : term105 _86807 s x) : @I (_86807 -> Prop) s x.
Proof. exact (proj2 (@lem3322666 _86807 s x h1)). Qed.
Lemma lem3322817 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) (h1 : term105 _86807 s x) : term116 _86807 s x.
Proof. exact (fun h0 : term99 _86807 s x => @lem3322816 _86807 s x h1). Qed.
Lemma lem3322819 (p : Prop) : (term117 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3322820 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term116 _86807 s x) = (@I (_86807 -> Prop) s x).
Proof. exact (@lem3322819 (@I (_86807 -> Prop) s x)). Qed.
Lemma lem3322821 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) (h1 : term105 _86807 s x) : @I (_86807 -> Prop) s x.
Proof. exact (EQ_MP (@lem3322820 _86807 s x) (@lem3322817 _86807 s x h1)). Qed.
Lemma lem3322823 (a : Prop) (b : Prop) : (term122 a b) = (term123 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3322824 {_86807 : Type'} (s : _86807 -> Prop) (_34464 : _86807 -> Prop) (x : _86807) : (term101 _86807 s _34464 x) = (term124 _86807 s _34464 x).
Proof. exact (@lem3322823 (_34464 = s) (@I (_86807 -> Prop) _34464 x)). Qed.
Lemma lem3322826 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3322827 {_86807 : Type'} (s : _86807 -> Prop) (_34464 : _86807 -> Prop) (x : _86807) : (term124 _86807 s _34464 x) = (term125 _86807 s _34464 x).
Proof. exact (@lem3322826 (term106 _86807 s _34464 x)). Qed.
Lemma lem3322828 {_86807 : Type'} (s : _86807 -> Prop) (_34464 : _86807 -> Prop) (x : _86807) : (term101 _86807 s _34464 x) = (term125 _86807 s _34464 x).
Proof. exact (TRANS (@lem3322824 _86807 s _34464 x) (@lem3322827 _86807 s _34464 x)). Qed.
Lemma lem3322830 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) (h1 : term105 _86807 s x) : term126 _86807 s x.
Proof. exact (conj (@lem3322814 _86807 s) (@lem3322821 _86807 s x h1)). Qed.
Lemma lem3322832 {_86807 : Type'} (_34464 : _86807 -> Prop) (s : _86807 -> Prop) (x : _86807) (h1 : term105 _86807 s x) : term125 _86807 s _34464 x.
Proof. exact (EQ_MP (@lem3322828 _86807 s _34464 x) (@lem3322716 _86807 _34464 s x h1)). Qed.
Lemma lem3322833 {_86807 : Type'} (_34464 : _86807 -> Prop) (s : _86807 -> Prop) (x : _86807) (h1 : term105 _86807 s x) : term125 _86807 s _34464 x.
Proof. exact (@lem3322832 _86807 _34464 s x h1). Qed.
Lemma lem3322834 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) (h1 : term105 _86807 s x) : term127 _86807 s x.
Proof. exact (@lem3322833 _86807 s s x h1). Qed.
Lemma lem3322837 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) (h1 : term105 _86807 s x) : False.
Proof. exact (@lem3322834 _86807 s x h1 (@lem3322830 _86807 s x h1)). Qed.
Lemma lem3322838 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) (h1 : term105 _86807 s x) : term119.
Proof. exact (fun h0 : ~ False => @lem3322837 _86807 s x h1). Qed.
Lemma lem3322840 (p : Prop) : (term117 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3322841 : term119 = False.
Proof. exact (@lem3322840 False). Qed.
Lemma lem3322842 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) (h1 : term105 _86807 s x) : False.
Proof. exact (EQ_MP (@lem3322841) (@lem3322838 _86807 s x h1)). Qed.
Lemma lem3322843 {_86807 : Type'} (t : _86807 -> Prop) (s : _86807 -> Prop) (x : _86807) (h1 : term108 _86807 t s x) : False.
Proof. exact (EQ_MP (@lem3322781) (@lem3322778 _86807 t s x h1)). Qed.
Lemma lem3322844 {_86807 : Type'} (t : _86807 -> Prop) (s : _86807 -> Prop) (x : _86807) (h1 : term95 _86807 t s x) : False.
Proof. exact (or_elim (@lem3322664 _86807 t s x h1) (fun h0 : term108 _86807 t s x => @lem3322843 _86807 t s x h0) (fun h0 : term105 _86807 s x => @lem3322842 _86807 s x h0)). Qed.
Lemma lem3322845 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) (h1 : term38 _86807 s x) : False.
Proof. exact (ex_elim (@lem3322596 _86807 s x h1) (fun t : _86807 -> Prop => fun h0 : term97 _86807 s x t => @lem3322844 _86807 t s x h0)). Qed.
Lemma lem3322846 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) (h1 : term38 _86807 s x) : (term38 _86807 s x) = False.
Proof. exact (prop_ext (fun h2 : term38 _86807 s x => @lem3322845 _86807 s x h1) (fun h2 : False => @lem3322405 _86807 s x h1)). Qed.
Lemma lem3322847 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) (h1 : term38 _86807 s x) : False.
Proof. exact (EQ_MP (@lem3322846 _86807 s x h1) (@lem3322405 _86807 s x h1)). Qed.
Lemma lem3322848 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : term37 _86807 s x.
Proof. exact (fun h0 : term38 _86807 s x => @lem3322847 _86807 s x h0). Qed.
Lemma lem3322849 {_86807 : Type'} (s : _86807 -> Prop) (x : _86807) : (term18 _86807 s x) = (s x).
Proof. exact (EQ_MP (@lem3322404 _86807 s x) (@lem3322848 _86807 s x)). Qed.
Lemma lem3322854 {_86807 : Type'} (s : _86807 -> Prop) : term24 _86807 s.
Proof. exact (fun x : _86807 => @lem3322849 _86807 s x). Qed.
Lemma lem3322859 {_86807 : Type'} : term36 _86807.
Proof. exact (fun s : _86807 -> Prop => @lem3322854 _86807 s). Qed.
Lemma lem3322860 {_86807 : Type'} : term35 _86807.
Proof. exact (EQ_MP (@lem3322400 _86807) (@lem3322859 _86807)). Qed.
Lemma lem3322861 {_86807 : Type'} (s : _86807 -> Prop) : term128 _86807 s.
Proof. exact (@lem3322860 _86807 s). Qed.
Lemma lem3322862 {_86807 : Type'} (s : _86807 -> Prop) : (term128 _86807 s) = (term26 _86807 s).
Proof. exact (eq_refl (term128 _86807 s)). Qed.
Lemma lem3322863 {_86807 : Type'} (s : _86807 -> Prop) : term26 _86807 s.
Proof. exact (EQ_MP (@lem3322862 _86807 s) (@lem3322861 _86807 s)). Qed.
Lemma lem3322865 {_86807 : Type'} (s : _86807 -> Prop) : term26 _86807 s.
Proof. exact (@lem3322282 _86807 s (@lem3322863 _86807 s)). Qed.
Lemma lem3322866 {_86807 : Type'} (s : _86807 -> Prop) (h1 : term27 _86807 s) : False.
Proof. exact (@lem3322865 _86807 s (@lem3322266 _86807 s h1)). Qed.
Lemma lem3322867 {_86807 : Type'} (s : _86807 -> Prop) (h1 : term27 _86807 s) : (term27 _86807 s) = False.
Proof. exact (prop_ext (fun h2 : term27 _86807 s => @lem3322866 _86807 s h1) (fun h2 : False => @lem3322266 _86807 s h1)). Qed.
Lemma lem3322868 {_86807 : Type'} (s : _86807 -> Prop) (h1 : term27 _86807 s) : False.
Proof. exact (EQ_MP (@lem3322867 _86807 s h1) (@lem3322266 _86807 s h1)). Qed.
Lemma lem3322869 {_86807 : Type'} (s : _86807 -> Prop) : term26 _86807 s.
Proof. exact (fun h0 : term27 _86807 s => @lem3322868 _86807 s h0). Qed.
Lemma lem3322870 {_86807 : Type'} (s : _86807 -> Prop) : term24 _86807 s.
Proof. exact (EQ_MP (@lem3322265 _86807 s) (@lem3322869 _86807 s)). Qed.
Lemma lem3322871 {_86807 : Type'} (s : _86807 -> Prop) : term23 _86807 s.
Proof. exact (EQ_MP (@lem3322261 _86807 s) (@lem3322870 _86807 s)). Qed.
