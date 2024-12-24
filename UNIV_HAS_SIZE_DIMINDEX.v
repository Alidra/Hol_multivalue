Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import UNIV_HAS_SIZE_DIMINDEX_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import HAS_SIZE_spec.
Require Import dimindex_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm1856_spec.
Require Import thm1857_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19490_spec.
Require Import thm20425_spec.
Require Import thm20611_spec.
Require Import thm20612_spec.
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
Lemma lem7598132 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7598133 {N : Type'} : ((term1 N) = (@FINITE N (@UNIV N))) = (term2 N).
Proof. exact (@lem7598132 ((term1 N) = (@FINITE N (@UNIV N)))). Qed.
Lemma lem7598134 {N : Type'} : (term2 N) = ((term1 N) = (@FINITE N (@UNIV N))).
Proof. exact (SYM (@lem7598133 N)). Qed.
Lemma lem7598135 {N : Type'} (h1 : term3 N) : term3 N.
Proof. exact (h1). Qed.
Lemma lem7598136 {N : Type'} : term4 N.
Proof. exact (@lem3863773 N). Qed.
Lemma lem7598138 {N : Type'} : term5 N.
Proof. exact (@lem7590231 N). Qed.
Lemma lem7598144 {A N : Type'} (h1 : term6 A N) : term6 A N.
Proof. exact (h1). Qed.
Lemma lem7598145 {A N : Type'} : term7 A N.
Proof. exact (fun h0 : term6 A N => @lem7598144 A N h0). Qed.
Lemma lem7598146 {A N : Type'} (h1 : term7 A N) : term7 A N.
Proof. exact (h1). Qed.
Lemma lem7598147 {A N : Type'} (h1 : term6 A N) : term6 A N.
Proof. exact (h1). Qed.
Lemma lem7598148 {A N : Type'} (h1 : term6 A N) (h2 : term7 A N) : term6 A N.
Proof. exact (@lem7598146 A N h2 (@lem7598147 A N h1)). Qed.
Lemma lem7598149 {A N : Type'} (h1 : term6 A N) : term8 A N.
Proof. exact (fun h0 : term7 A N => @lem7598148 A N h1 h0). Qed.
Lemma lem7598150 {A N : Type'} (h1 : term7 A N) : term7 A N.
Proof. exact (h1). Qed.
Lemma lem7598151 {A N : Type'} (h1 : term6 A N) (h2 : term7 A N) : term6 A N.
Proof. exact (@lem7598149 A N h1 (@lem7598150 A N h2)). Qed.
Lemma lem7598152 {A N : Type'} (h1 : term7 A N) : term7 A N.
Proof. exact (fun h0 : term6 A N => @lem7598151 A N h0 h1). Qed.
Lemma lem7598153 {A N : Type'} : term9 A N.
Proof. exact (fun h0 : term7 A N => @lem7598152 A N h0). Qed.
Lemma lem7598156 {A N : Type'} : term7 A N.
Proof. exact (@lem7598153 A N (@lem7598145 A N)). Qed.
Lemma lem7598157 {A N : Type'} : term7 A N.
Proof. exact (@lem7598156 A N). Qed.
Lemma lem7598173 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7598174 {N : Type'} : (term10 N) = (term11 N).
Proof. exact (@lem7598173 (term4 N)). Qed.
Lemma lem7598185 {N : Type'} : (term12 N) = (term12 N).
Proof. exact (eq_refl (term12 N)). Qed.
Lemma lem7598186 {N : Type'} : (term13 N) = (term14 N).
Proof. exact (MK_COMB (@lem7598185 N) (@lem7598174 N)). Qed.
Lemma lem7598189 {A : Type'} : (term12 A) = (term12 A).
Proof. exact (eq_refl (term12 A)). Qed.
Lemma lem7598190 {A N : Type'} : (term15 A N) = (term16 A N).
Proof. exact (MK_COMB (@lem7598189 A) (@lem7598186 N)). Qed.
Lemma lem7598193 {N : Type'} : (term17 N) = (term17 N).
Proof. exact (eq_refl (term17 N)). Qed.
Lemma lem7598200 {A N : Type'} : (term6 A N) = (term18 A N).
Proof. exact (MK_COMB (@lem7598193 N) (@lem7598190 A N)). Qed.
Lemma lem7598209 {A : Type'} (h1 : (@FINITE A (@UNIV A)) = False) : (@FINITE A (@UNIV A)) = False.
Proof. exact (h1). Qed.
Lemma lem7598210 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem7598211 {A : Type'} (h1 : (@FINITE A (@UNIV A)) = False) : (term19 A) = (@COND nat False).
Proof. exact (MK_COMB (@lem7598210) (@lem7598209 A h1)). Qed.
Lemma lem7598212 {A : Type'} : (@CARD A (@UNIV A)) = (@CARD A (@UNIV A)).
Proof. exact (eq_refl (@CARD A (@UNIV A))). Qed.
Lemma lem7598213 {A : Type'} (h1 : (@FINITE A (@UNIV A)) = False) : (term20 A) = (term21 A).
Proof. exact (MK_COMB (@lem7598211 A h1) (@lem7598212 A)). Qed.
Lemma lem7598214 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem7598215 {A : Type'} (h1 : (@FINITE A (@UNIV A)) = False) : (term23 A) = (term24 A).
Proof. exact (MK_COMB (@lem7598213 A h1) (@lem7598214)). Qed.
Lemma lem7598217 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7598218 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem7598217 nat t1 t2). Qed.
Lemma lem7598219 {A : Type'} : (term24 A) = term22.
Proof. exact (@lem7598218 (@CARD A (@UNIV A)) term22). Qed.
Lemma lem7598220 {A : Type'} (h1 : (@FINITE A (@UNIV A)) = False) : (term23 A) = term22.
Proof. exact (TRANS (@lem7598215 A h1) (@lem7598219 A)). Qed.
Lemma lem7598221 {A : Type'} (s : A -> Prop) : (term25 A s) = (term25 A s).
Proof. exact (eq_refl (term25 A s)). Qed.
Lemma lem7598222 {A : Type'} (s : A -> Prop) (h1 : (@FINITE A (@UNIV A)) = False) : ((@dimindex A s) = (term23 A)) = ((@dimindex A s) = term22).
Proof. exact (MK_COMB (@lem7598221 A s) (@lem7598220 A h1)). Qed.
Lemma lem7598225 {A : Type'} (h1 : (@FINITE A (@UNIV A)) = False) : (term26 A) = (term27 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7598222 A s h1)). Qed.
Lemma lem7598226 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7598227 {A : Type'} (h1 : (@FINITE A (@UNIV A)) = False) : (term5 A) = (term28 A).
Proof. exact (MK_COMB (@lem7598226 A) (@lem7598225 A h1)). Qed.
Lemma lem7598232 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7598233 {A : Type'} (h1 : (@FINITE A (@UNIV A)) = False) : (term12 A) = (term29 A).
Proof. exact (MK_COMB (@lem7598232) (@lem7598227 A h1)). Qed.
Lemma lem7598259 {N : Type'} : (term14 N) = (term14 N).
Proof. exact (eq_refl (term14 N)). Qed.
Lemma lem7598260 {A N : Type'} (h1 : (@FINITE A (@UNIV A)) = False) : (term16 A N) = (term30 A N).
Proof. exact (MK_COMB (@lem7598233 A h1) (@lem7598259 N)). Qed.
Lemma lem7598263 {N : Type'} : (term17 N) = (term17 N).
Proof. exact (eq_refl (term17 N)). Qed.
Lemma lem7598264 {A N : Type'} (h1 : (@FINITE A (@UNIV A)) = False) : (term18 A N) = (term31 A N).
Proof. exact (MK_COMB (@lem7598263 N) (@lem7598260 A N h1)). Qed.
Lemma lem7598267 {A N : Type'} : term32 A N.
Proof. exact (fun h0 : (@FINITE A (@UNIV A)) = False => @lem7598264 A N h0). Qed.
Lemma lem7598274 {A : Type'} (h1 : (@FINITE A (@UNIV A)) = True) : (@FINITE A (@UNIV A)) = True.
Proof. exact (h1). Qed.
Lemma lem7598275 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem7598276 {A : Type'} (h1 : (@FINITE A (@UNIV A)) = True) : (term19 A) = (@COND nat True).
Proof. exact (MK_COMB (@lem7598275) (@lem7598274 A h1)). Qed.
Lemma lem7598277 {A : Type'} : (@CARD A (@UNIV A)) = (@CARD A (@UNIV A)).
Proof. exact (eq_refl (@CARD A (@UNIV A))). Qed.
Lemma lem7598278 {A : Type'} (h1 : (@FINITE A (@UNIV A)) = True) : (term20 A) = (term33 A).
Proof. exact (MK_COMB (@lem7598276 A h1) (@lem7598277 A)). Qed.
Lemma lem7598279 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem7598280 {A : Type'} (h1 : (@FINITE A (@UNIV A)) = True) : (term23 A) = (term34 A).
Proof. exact (MK_COMB (@lem7598278 A h1) (@lem7598279)). Qed.
Lemma lem7598282 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem7598283 (t2 : nat) (t1 : nat) : (@COND nat True t1 t2) = t1.
Proof. exact (@lem7598282 nat t2 t1). Qed.
Lemma lem7598284 {A : Type'} : (term34 A) = (@CARD A (@UNIV A)).
Proof. exact (@lem7598283 term22 (@CARD A (@UNIV A))). Qed.
Lemma lem7598285 {A : Type'} (h1 : (@FINITE A (@UNIV A)) = True) : (term23 A) = (@CARD A (@UNIV A)).
Proof. exact (TRANS (@lem7598280 A h1) (@lem7598284 A)). Qed.
Lemma lem7598286 {A : Type'} (s : A -> Prop) : (term25 A s) = (term25 A s).
Proof. exact (eq_refl (term25 A s)). Qed.
Lemma lem7598287 {A : Type'} (s : A -> Prop) (h1 : (@FINITE A (@UNIV A)) = True) : ((@dimindex A s) = (term23 A)) = ((@dimindex A s) = (@CARD A (@UNIV A))).
Proof. exact (MK_COMB (@lem7598286 A s) (@lem7598285 A h1)). Qed.
Lemma lem7598290 {A : Type'} (h1 : (@FINITE A (@UNIV A)) = True) : (term26 A) = (term35 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7598287 A s h1)). Qed.
Lemma lem7598291 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7598292 {A : Type'} (h1 : (@FINITE A (@UNIV A)) = True) : (term5 A) = (term36 A).
Proof. exact (MK_COMB (@lem7598291 A) (@lem7598290 A h1)). Qed.
Lemma lem7598297 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7598298 {A : Type'} (h1 : (@FINITE A (@UNIV A)) = True) : (term12 A) = (term37 A).
Proof. exact (MK_COMB (@lem7598297) (@lem7598292 A h1)). Qed.
Lemma lem7598324 {N : Type'} : (term14 N) = (term14 N).
Proof. exact (eq_refl (term14 N)). Qed.
Lemma lem7598325 {A N : Type'} (h1 : (@FINITE A (@UNIV A)) = True) : (term16 A N) = (term38 A N).
Proof. exact (MK_COMB (@lem7598298 A h1) (@lem7598324 N)). Qed.
Lemma lem7598328 {N : Type'} : (term17 N) = (term17 N).
Proof. exact (eq_refl (term17 N)). Qed.
Lemma lem7598329 {A N : Type'} (h1 : (@FINITE A (@UNIV A)) = True) : (term18 A N) = (term39 A N).
Proof. exact (MK_COMB (@lem7598328 N) (@lem7598325 A N h1)). Qed.
Lemma lem7598332 {A N : Type'} : term40 A N.
Proof. exact (fun h0 : (@FINITE A (@UNIV A)) = True => @lem7598329 A N h0). Qed.
Lemma lem7598333 {A N : Type'} : term41 A N.
Proof. exact (conj (@lem7598267 A N) (@lem7598332 A N)). Qed.
Lemma lem7598335 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term42 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem7598336 {A N : Type'} : term43 A N.
Proof. exact (@lem7598335 (term18 A N) (term39 A N) (@FINITE A (@UNIV A)) (term31 A N)). Qed.
Lemma lem7598351 {A N : Type'} : (term18 A N) = (term44 A N).
Proof. exact (@lem7598336 A N (@lem7598333 A N)). Qed.
Lemma lem7598358 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = False) : (@FINITE N (@UNIV N)) = False.
Proof. exact (h1). Qed.
Lemma lem7598359 {N : Type'} : (term45 N) = (term45 N).
Proof. exact (eq_refl (term45 N)). Qed.
Lemma lem7598360 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = False) : ((term1 N) = (@FINITE N (@UNIV N))) = ((term1 N) = False).
Proof. exact (MK_COMB (@lem7598359 N) (@lem7598358 N h1)). Qed.
Lemma lem7598362 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem7598363 {N : Type'} : ((term1 N) = False) = (term46 N).
Proof. exact (@lem7598362 (term1 N)). Qed.
Lemma lem7598364 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = False) : ((term1 N) = (@FINITE N (@UNIV N))) = (term46 N).
Proof. exact (TRANS (@lem7598360 N h1) (@lem7598363 N)). Qed.
Lemma lem7598365 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7598366 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = False) : (term3 N) = (term47 N).
Proof. exact (MK_COMB (@lem7598365) (@lem7598364 N h1)). Qed.
Lemma lem7598368 (t : Prop) : (term48 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem7598369 {N : Type'} : (term47 N) = (term1 N).
Proof. exact (@lem7598368 (term1 N)). Qed.
Lemma lem7598370 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = False) : (term3 N) = (term1 N).
Proof. exact (TRANS (@lem7598366 N h1) (@lem7598369 N)). Qed.
Lemma lem7598371 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7598372 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = False) : (term17 N) = (term49 N).
Proof. exact (MK_COMB (@lem7598371) (@lem7598370 N h1)). Qed.
Lemma lem7598380 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = False) : (@FINITE N (@UNIV N)) = False.
Proof. exact (h1). Qed.
Lemma lem7598381 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem7598382 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = False) : (term19 N) = (@COND nat False).
Proof. exact (MK_COMB (@lem7598381) (@lem7598380 N h1)). Qed.
Lemma lem7598383 {N : Type'} : (@CARD N (@UNIV N)) = (@CARD N (@UNIV N)).
Proof. exact (eq_refl (@CARD N (@UNIV N))). Qed.
Lemma lem7598384 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = False) : (term20 N) = (term21 N).
Proof. exact (MK_COMB (@lem7598382 N h1) (@lem7598383 N)). Qed.
Lemma lem7598385 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem7598386 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = False) : (term23 N) = (term24 N).
Proof. exact (MK_COMB (@lem7598384 N h1) (@lem7598385)). Qed.
Lemma lem7598388 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7598389 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem7598388 nat t1 t2). Qed.
Lemma lem7598390 {N : Type'} : (term24 N) = term22.
Proof. exact (@lem7598389 (@CARD N (@UNIV N)) term22). Qed.
Lemma lem7598391 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = False) : (term23 N) = term22.
Proof. exact (TRANS (@lem7598386 N h1) (@lem7598390 N)). Qed.
Lemma lem7598392 {N : Type'} (s : N -> Prop) : (term25 N s) = (term25 N s).
Proof. exact (eq_refl (term25 N s)). Qed.
Lemma lem7598393 {N : Type'} (s : N -> Prop) (h1 : (@FINITE N (@UNIV N)) = False) : ((@dimindex N s) = (term23 N)) = ((@dimindex N s) = term22).
Proof. exact (MK_COMB (@lem7598392 N s) (@lem7598391 N h1)). Qed.
Lemma lem7598396 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = False) : (term26 N) = (term27 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7598393 N s h1)). Qed.
Lemma lem7598397 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7598398 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = False) : (term5 N) = (term28 N).
Proof. exact (MK_COMB (@lem7598397 N) (@lem7598396 N h1)). Qed.
Lemma lem7598403 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7598404 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = False) : (term12 N) = (term29 N).
Proof. exact (MK_COMB (@lem7598403) (@lem7598398 N h1)). Qed.
Lemma lem7598419 {N : Type'} : (term11 N) = (term11 N).
Proof. exact (eq_refl (term11 N)). Qed.
Lemma lem7598420 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = False) : (term14 N) = (term50 N).
Proof. exact (MK_COMB (@lem7598404 N h1) (@lem7598419 N)). Qed.
Lemma lem7598423 {A : Type'} : (term37 A) = (term37 A).
Proof. exact (eq_refl (term37 A)). Qed.
Lemma lem7598424 {A N : Type'} (h1 : (@FINITE N (@UNIV N)) = False) : (term38 A N) = (term51 A N).
Proof. exact (MK_COMB (@lem7598423 A) (@lem7598420 N h1)). Qed.
Lemma lem7598427 {A N : Type'} (h1 : (@FINITE N (@UNIV N)) = False) : (term39 A N) = (term52 A N).
Proof. exact (MK_COMB (@lem7598372 N h1) (@lem7598424 A N h1)). Qed.
Lemma lem7598430 {A : Type'} : (term53 A) = (term53 A).
Proof. exact (eq_refl (term53 A)). Qed.
Lemma lem7598431 {A N : Type'} (h1 : (@FINITE N (@UNIV N)) = False) : (term54 A N) = (term55 A N).
Proof. exact (MK_COMB (@lem7598430 A) (@lem7598427 A N h1)). Qed.
Lemma lem7598434 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7598435 {A N : Type'} (h1 : (@FINITE N (@UNIV N)) = False) : (term56 A N) = (term57 A N).
Proof. exact (MK_COMB (@lem7598434) (@lem7598431 A N h1)). Qed.
Lemma lem7598440 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = False) : (@FINITE N (@UNIV N)) = False.
Proof. exact (h1). Qed.
Lemma lem7598441 {N : Type'} : (term45 N) = (term45 N).
Proof. exact (eq_refl (term45 N)). Qed.
Lemma lem7598442 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = False) : ((term1 N) = (@FINITE N (@UNIV N))) = ((term1 N) = False).
Proof. exact (MK_COMB (@lem7598441 N) (@lem7598440 N h1)). Qed.
Lemma lem7598444 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem7598445 {N : Type'} : ((term1 N) = False) = (term46 N).
Proof. exact (@lem7598444 (term1 N)). Qed.
Lemma lem7598446 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = False) : ((term1 N) = (@FINITE N (@UNIV N))) = (term46 N).
Proof. exact (TRANS (@lem7598442 N h1) (@lem7598445 N)). Qed.
Lemma lem7598447 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7598448 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = False) : (term3 N) = (term47 N).
Proof. exact (MK_COMB (@lem7598447) (@lem7598446 N h1)). Qed.
Lemma lem7598450 (t : Prop) : (term48 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem7598451 {N : Type'} : (term47 N) = (term1 N).
Proof. exact (@lem7598450 (term1 N)). Qed.
Lemma lem7598452 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = False) : (term3 N) = (term1 N).
Proof. exact (TRANS (@lem7598448 N h1) (@lem7598451 N)). Qed.
Lemma lem7598453 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7598454 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = False) : (term17 N) = (term49 N).
Proof. exact (MK_COMB (@lem7598453) (@lem7598452 N h1)). Qed.
Lemma lem7598462 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = False) : (@FINITE N (@UNIV N)) = False.
Proof. exact (h1). Qed.
Lemma lem7598463 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem7598464 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = False) : (term19 N) = (@COND nat False).
Proof. exact (MK_COMB (@lem7598463) (@lem7598462 N h1)). Qed.
Lemma lem7598465 {N : Type'} : (@CARD N (@UNIV N)) = (@CARD N (@UNIV N)).
Proof. exact (eq_refl (@CARD N (@UNIV N))). Qed.
Lemma lem7598466 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = False) : (term20 N) = (term21 N).
Proof. exact (MK_COMB (@lem7598464 N h1) (@lem7598465 N)). Qed.
Lemma lem7598467 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem7598468 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = False) : (term23 N) = (term24 N).
Proof. exact (MK_COMB (@lem7598466 N h1) (@lem7598467)). Qed.
Lemma lem7598470 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7598471 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem7598470 nat t1 t2). Qed.
Lemma lem7598472 {N : Type'} : (term24 N) = term22.
Proof. exact (@lem7598471 (@CARD N (@UNIV N)) term22). Qed.
Lemma lem7598473 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = False) : (term23 N) = term22.
Proof. exact (TRANS (@lem7598468 N h1) (@lem7598472 N)). Qed.
Lemma lem7598474 {N : Type'} (s : N -> Prop) : (term25 N s) = (term25 N s).
Proof. exact (eq_refl (term25 N s)). Qed.
Lemma lem7598475 {N : Type'} (s : N -> Prop) (h1 : (@FINITE N (@UNIV N)) = False) : ((@dimindex N s) = (term23 N)) = ((@dimindex N s) = term22).
Proof. exact (MK_COMB (@lem7598474 N s) (@lem7598473 N h1)). Qed.
Lemma lem7598478 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = False) : (term26 N) = (term27 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7598475 N s h1)). Qed.
Lemma lem7598479 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7598480 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = False) : (term5 N) = (term28 N).
Proof. exact (MK_COMB (@lem7598479 N) (@lem7598478 N h1)). Qed.
Lemma lem7598485 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7598486 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = False) : (term12 N) = (term29 N).
Proof. exact (MK_COMB (@lem7598485) (@lem7598480 N h1)). Qed.
Lemma lem7598501 {N : Type'} : (term11 N) = (term11 N).
Proof. exact (eq_refl (term11 N)). Qed.
Lemma lem7598502 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = False) : (term14 N) = (term50 N).
Proof. exact (MK_COMB (@lem7598486 N h1) (@lem7598501 N)). Qed.
Lemma lem7598505 {A : Type'} : (term29 A) = (term29 A).
Proof. exact (eq_refl (term29 A)). Qed.
Lemma lem7598506 {A N : Type'} (h1 : (@FINITE N (@UNIV N)) = False) : (term30 A N) = (term58 A N).
Proof. exact (MK_COMB (@lem7598505 A) (@lem7598502 N h1)). Qed.
Lemma lem7598509 {A N : Type'} (h1 : (@FINITE N (@UNIV N)) = False) : (term31 A N) = (term59 A N).
Proof. exact (MK_COMB (@lem7598454 N h1) (@lem7598506 A N h1)). Qed.
Lemma lem7598512 {A : Type'} : (term60 A) = (term60 A).
Proof. exact (eq_refl (term60 A)). Qed.
Lemma lem7598513 {A N : Type'} (h1 : (@FINITE N (@UNIV N)) = False) : (term61 A N) = (term62 A N).
Proof. exact (MK_COMB (@lem7598512 A) (@lem7598509 A N h1)). Qed.
Lemma lem7598516 {A N : Type'} (h1 : (@FINITE N (@UNIV N)) = False) : (term44 A N) = (term63 A N).
Proof. exact (MK_COMB (@lem7598435 A N h1) (@lem7598513 A N h1)). Qed.
Lemma lem7598519 {A N : Type'} : term64 A N.
Proof. exact (fun h0 : (@FINITE N (@UNIV N)) = False => @lem7598516 A N h0). Qed.
Lemma lem7598524 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = True) : (@FINITE N (@UNIV N)) = True.
Proof. exact (h1). Qed.
Lemma lem7598525 {N : Type'} : (term45 N) = (term45 N).
Proof. exact (eq_refl (term45 N)). Qed.
Lemma lem7598526 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = True) : ((term1 N) = (@FINITE N (@UNIV N))) = ((term1 N) = True).
Proof. exact (MK_COMB (@lem7598525 N) (@lem7598524 N h1)). Qed.
Lemma lem7598528 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem7598529 {N : Type'} : ((term1 N) = True) = (term1 N).
Proof. exact (@lem7598528 (term1 N)). Qed.
Lemma lem7598530 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = True) : ((term1 N) = (@FINITE N (@UNIV N))) = (term1 N).
Proof. exact (TRANS (@lem7598526 N h1) (@lem7598529 N)). Qed.
Lemma lem7598531 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7598532 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = True) : (term3 N) = (term46 N).
Proof. exact (MK_COMB (@lem7598531) (@lem7598530 N h1)). Qed.
Lemma lem7598533 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7598534 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = True) : (term17 N) = (term65 N).
Proof. exact (MK_COMB (@lem7598533) (@lem7598532 N h1)). Qed.
Lemma lem7598542 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = True) : (@FINITE N (@UNIV N)) = True.
Proof. exact (h1). Qed.
Lemma lem7598543 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem7598544 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = True) : (term19 N) = (@COND nat True).
Proof. exact (MK_COMB (@lem7598543) (@lem7598542 N h1)). Qed.
Lemma lem7598545 {N : Type'} : (@CARD N (@UNIV N)) = (@CARD N (@UNIV N)).
Proof. exact (eq_refl (@CARD N (@UNIV N))). Qed.
Lemma lem7598546 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = True) : (term20 N) = (term33 N).
Proof. exact (MK_COMB (@lem7598544 N h1) (@lem7598545 N)). Qed.
Lemma lem7598547 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem7598548 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = True) : (term23 N) = (term34 N).
Proof. exact (MK_COMB (@lem7598546 N h1) (@lem7598547)). Qed.
Lemma lem7598550 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem7598551 (t2 : nat) (t1 : nat) : (@COND nat True t1 t2) = t1.
Proof. exact (@lem7598550 nat t2 t1). Qed.
Lemma lem7598552 {N : Type'} : (term34 N) = (@CARD N (@UNIV N)).
Proof. exact (@lem7598551 term22 (@CARD N (@UNIV N))). Qed.
Lemma lem7598553 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = True) : (term23 N) = (@CARD N (@UNIV N)).
Proof. exact (TRANS (@lem7598548 N h1) (@lem7598552 N)). Qed.
Lemma lem7598554 {N : Type'} (s : N -> Prop) : (term25 N s) = (term25 N s).
Proof. exact (eq_refl (term25 N s)). Qed.
Lemma lem7598555 {N : Type'} (s : N -> Prop) (h1 : (@FINITE N (@UNIV N)) = True) : ((@dimindex N s) = (term23 N)) = ((@dimindex N s) = (@CARD N (@UNIV N))).
Proof. exact (MK_COMB (@lem7598554 N s) (@lem7598553 N h1)). Qed.
Lemma lem7598558 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = True) : (term26 N) = (term35 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7598555 N s h1)). Qed.
Lemma lem7598559 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7598560 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = True) : (term5 N) = (term36 N).
Proof. exact (MK_COMB (@lem7598559 N) (@lem7598558 N h1)). Qed.
Lemma lem7598565 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7598566 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = True) : (term12 N) = (term37 N).
Proof. exact (MK_COMB (@lem7598565) (@lem7598560 N h1)). Qed.
Lemma lem7598581 {N : Type'} : (term11 N) = (term11 N).
Proof. exact (eq_refl (term11 N)). Qed.
Lemma lem7598582 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = True) : (term14 N) = (term66 N).
Proof. exact (MK_COMB (@lem7598566 N h1) (@lem7598581 N)). Qed.
Lemma lem7598585 {A : Type'} : (term37 A) = (term37 A).
Proof. exact (eq_refl (term37 A)). Qed.
Lemma lem7598586 {A N : Type'} (h1 : (@FINITE N (@UNIV N)) = True) : (term38 A N) = (term67 A N).
Proof. exact (MK_COMB (@lem7598585 A) (@lem7598582 N h1)). Qed.
Lemma lem7598589 {A N : Type'} (h1 : (@FINITE N (@UNIV N)) = True) : (term39 A N) = (term68 A N).
Proof. exact (MK_COMB (@lem7598534 N h1) (@lem7598586 A N h1)). Qed.
Lemma lem7598592 {A : Type'} : (term53 A) = (term53 A).
Proof. exact (eq_refl (term53 A)). Qed.
Lemma lem7598593 {A N : Type'} (h1 : (@FINITE N (@UNIV N)) = True) : (term54 A N) = (term69 A N).
Proof. exact (MK_COMB (@lem7598592 A) (@lem7598589 A N h1)). Qed.
Lemma lem7598596 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7598597 {A N : Type'} (h1 : (@FINITE N (@UNIV N)) = True) : (term56 A N) = (term70 A N).
Proof. exact (MK_COMB (@lem7598596) (@lem7598593 A N h1)). Qed.
Lemma lem7598602 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = True) : (@FINITE N (@UNIV N)) = True.
Proof. exact (h1). Qed.
Lemma lem7598603 {N : Type'} : (term45 N) = (term45 N).
Proof. exact (eq_refl (term45 N)). Qed.
Lemma lem7598604 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = True) : ((term1 N) = (@FINITE N (@UNIV N))) = ((term1 N) = True).
Proof. exact (MK_COMB (@lem7598603 N) (@lem7598602 N h1)). Qed.
Lemma lem7598606 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem7598607 {N : Type'} : ((term1 N) = True) = (term1 N).
Proof. exact (@lem7598606 (term1 N)). Qed.
Lemma lem7598608 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = True) : ((term1 N) = (@FINITE N (@UNIV N))) = (term1 N).
Proof. exact (TRANS (@lem7598604 N h1) (@lem7598607 N)). Qed.
Lemma lem7598609 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7598610 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = True) : (term3 N) = (term46 N).
Proof. exact (MK_COMB (@lem7598609) (@lem7598608 N h1)). Qed.
Lemma lem7598611 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7598612 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = True) : (term17 N) = (term65 N).
Proof. exact (MK_COMB (@lem7598611) (@lem7598610 N h1)). Qed.
Lemma lem7598620 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = True) : (@FINITE N (@UNIV N)) = True.
Proof. exact (h1). Qed.
Lemma lem7598621 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem7598622 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = True) : (term19 N) = (@COND nat True).
Proof. exact (MK_COMB (@lem7598621) (@lem7598620 N h1)). Qed.
Lemma lem7598623 {N : Type'} : (@CARD N (@UNIV N)) = (@CARD N (@UNIV N)).
Proof. exact (eq_refl (@CARD N (@UNIV N))). Qed.
Lemma lem7598624 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = True) : (term20 N) = (term33 N).
Proof. exact (MK_COMB (@lem7598622 N h1) (@lem7598623 N)). Qed.
Lemma lem7598625 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem7598626 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = True) : (term23 N) = (term34 N).
Proof. exact (MK_COMB (@lem7598624 N h1) (@lem7598625)). Qed.
Lemma lem7598628 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem7598629 (t2 : nat) (t1 : nat) : (@COND nat True t1 t2) = t1.
Proof. exact (@lem7598628 nat t2 t1). Qed.
Lemma lem7598630 {N : Type'} : (term34 N) = (@CARD N (@UNIV N)).
Proof. exact (@lem7598629 term22 (@CARD N (@UNIV N))). Qed.
Lemma lem7598631 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = True) : (term23 N) = (@CARD N (@UNIV N)).
Proof. exact (TRANS (@lem7598626 N h1) (@lem7598630 N)). Qed.
Lemma lem7598632 {N : Type'} (s : N -> Prop) : (term25 N s) = (term25 N s).
Proof. exact (eq_refl (term25 N s)). Qed.
Lemma lem7598633 {N : Type'} (s : N -> Prop) (h1 : (@FINITE N (@UNIV N)) = True) : ((@dimindex N s) = (term23 N)) = ((@dimindex N s) = (@CARD N (@UNIV N))).
Proof. exact (MK_COMB (@lem7598632 N s) (@lem7598631 N h1)). Qed.
Lemma lem7598636 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = True) : (term26 N) = (term35 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7598633 N s h1)). Qed.
Lemma lem7598637 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7598638 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = True) : (term5 N) = (term36 N).
Proof. exact (MK_COMB (@lem7598637 N) (@lem7598636 N h1)). Qed.
Lemma lem7598643 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7598644 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = True) : (term12 N) = (term37 N).
Proof. exact (MK_COMB (@lem7598643) (@lem7598638 N h1)). Qed.
Lemma lem7598659 {N : Type'} : (term11 N) = (term11 N).
Proof. exact (eq_refl (term11 N)). Qed.
Lemma lem7598660 {N : Type'} (h1 : (@FINITE N (@UNIV N)) = True) : (term14 N) = (term66 N).
Proof. exact (MK_COMB (@lem7598644 N h1) (@lem7598659 N)). Qed.
Lemma lem7598663 {A : Type'} : (term29 A) = (term29 A).
Proof. exact (eq_refl (term29 A)). Qed.
Lemma lem7598664 {A N : Type'} (h1 : (@FINITE N (@UNIV N)) = True) : (term30 A N) = (term71 A N).
Proof. exact (MK_COMB (@lem7598663 A) (@lem7598660 N h1)). Qed.
Lemma lem7598667 {A N : Type'} (h1 : (@FINITE N (@UNIV N)) = True) : (term31 A N) = (term72 A N).
Proof. exact (MK_COMB (@lem7598612 N h1) (@lem7598664 A N h1)). Qed.
Lemma lem7598670 {A : Type'} : (term60 A) = (term60 A).
Proof. exact (eq_refl (term60 A)). Qed.
Lemma lem7598671 {A N : Type'} (h1 : (@FINITE N (@UNIV N)) = True) : (term61 A N) = (term73 A N).
Proof. exact (MK_COMB (@lem7598670 A) (@lem7598667 A N h1)). Qed.
Lemma lem7598674 {A N : Type'} (h1 : (@FINITE N (@UNIV N)) = True) : (term44 A N) = (term74 A N).
Proof. exact (MK_COMB (@lem7598597 A N h1) (@lem7598671 A N h1)). Qed.
Lemma lem7598677 {A N : Type'} : term75 A N.
Proof. exact (fun h0 : (@FINITE N (@UNIV N)) = True => @lem7598674 A N h0). Qed.
Lemma lem7598678 {A N : Type'} : term76 A N.
Proof. exact (conj (@lem7598519 A N) (@lem7598677 A N)). Qed.
Lemma lem7598680 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term42 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem7598681 {A N : Type'} : term77 A N.
Proof. exact (@lem7598680 (term44 A N) (term74 A N) (@FINITE N (@UNIV N)) (term63 A N)). Qed.
Lemma lem7598696 {A N : Type'} : (term44 A N) = (term78 A N).
Proof. exact (@lem7598681 A N (@lem7598678 A N)). Qed.
Lemma lem7598705 {N : Type'} (s : N -> Prop) (n : nat) : ((@HAS_SIZE N s n) = (term79 N s n)) = ((@HAS_SIZE N s n) = (term79 N s n)).
Proof. exact (eq_refl ((@HAS_SIZE N s n) = (term79 N s n))). Qed.
Lemma lem7598706 {N : Type'} (s : N -> Prop) : (term80 N s) = (term80 N s).
Proof. exact (fun_ext (fun n : nat => @lem7598705 N s n)). Qed.
Lemma lem7598707 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7598708 {N : Type'} (s : N -> Prop) : (term81 N s) = (term81 N s).
Proof. exact (MK_COMB (@lem7598707) (@lem7598706 N s)). Qed.
Lemma lem7598709 {N : Type'} : (term82 N) = (term82 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7598708 N s)). Qed.
Lemma lem7598710 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7598711 {N : Type'} : (term4 N) = (term4 N).
Proof. exact (MK_COMB (@lem7598710 N) (@lem7598709 N)). Qed.
Lemma lem7598712 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7598713 {N : Type'} : (term11 N) = (term11 N).
Proof. exact (MK_COMB (@lem7598712) (@lem7598711 N)). Qed.
Lemma lem7598714 {N : Type'} (s : N -> Prop) : ((@dimindex N s) = term22) = ((@dimindex N s) = term22).
Proof. exact (eq_refl ((@dimindex N s) = term22)). Qed.
Lemma lem7598715 {N : Type'} : (term27 N) = (term27 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7598714 N s)). Qed.
Lemma lem7598716 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7598717 {N : Type'} : (term28 N) = (term28 N).
Proof. exact (MK_COMB (@lem7598716 N) (@lem7598715 N)). Qed.
Lemma lem7598718 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7598719 {N : Type'} : (term29 N) = (term29 N).
Proof. exact (MK_COMB (@lem7598718) (@lem7598717 N)). Qed.
Lemma lem7598720 {N : Type'} : (term50 N) = (term50 N).
Proof. exact (MK_COMB (@lem7598719 N) (@lem7598713 N)). Qed.
Lemma lem7598721 {A : Type'} (s : A -> Prop) : ((@dimindex A s) = term22) = ((@dimindex A s) = term22).
Proof. exact (eq_refl ((@dimindex A s) = term22)). Qed.
Lemma lem7598722 {A : Type'} : (term27 A) = (term27 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7598721 A s)). Qed.
Lemma lem7598723 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7598724 {A : Type'} : (term28 A) = (term28 A).
Proof. exact (MK_COMB (@lem7598723 A) (@lem7598722 A)). Qed.
Lemma lem7598725 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7598726 {A : Type'} : (term29 A) = (term29 A).
Proof. exact (MK_COMB (@lem7598725) (@lem7598724 A)). Qed.
Lemma lem7598727 {A N : Type'} : (term58 A N) = (term58 A N).
Proof. exact (MK_COMB (@lem7598726 A) (@lem7598720 N)). Qed.
Lemma lem7598730 {N : Type'} : (term49 N) = (term49 N).
Proof. exact (eq_refl (term49 N)). Qed.
Lemma lem7598731 {A N : Type'} : (term59 A N) = (term59 A N).
Proof. exact (MK_COMB (@lem7598730 N) (@lem7598727 A N)). Qed.
Lemma lem7598734 {A : Type'} : (term60 A) = (term60 A).
Proof. exact (eq_refl (term60 A)). Qed.
Lemma lem7598735 {A N : Type'} : (term62 A N) = (term62 A N).
Proof. exact (MK_COMB (@lem7598734 A) (@lem7598731 A N)). Qed.
Lemma lem7598744 {N : Type'} (s : N -> Prop) (n : nat) : ((@HAS_SIZE N s n) = (term79 N s n)) = ((@HAS_SIZE N s n) = (term79 N s n)).
Proof. exact (eq_refl ((@HAS_SIZE N s n) = (term79 N s n))). Qed.
Lemma lem7598745 {N : Type'} (s : N -> Prop) : (term80 N s) = (term80 N s).
Proof. exact (fun_ext (fun n : nat => @lem7598744 N s n)). Qed.
Lemma lem7598746 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7598747 {N : Type'} (s : N -> Prop) : (term81 N s) = (term81 N s).
Proof. exact (MK_COMB (@lem7598746) (@lem7598745 N s)). Qed.
Lemma lem7598748 {N : Type'} : (term82 N) = (term82 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7598747 N s)). Qed.
Lemma lem7598749 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7598750 {N : Type'} : (term4 N) = (term4 N).
Proof. exact (MK_COMB (@lem7598749 N) (@lem7598748 N)). Qed.
Lemma lem7598751 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7598752 {N : Type'} : (term11 N) = (term11 N).
Proof. exact (MK_COMB (@lem7598751) (@lem7598750 N)). Qed.
Lemma lem7598753 {N : Type'} (s : N -> Prop) : ((@dimindex N s) = term22) = ((@dimindex N s) = term22).
Proof. exact (eq_refl ((@dimindex N s) = term22)). Qed.
Lemma lem7598754 {N : Type'} : (term27 N) = (term27 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7598753 N s)). Qed.
Lemma lem7598755 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7598756 {N : Type'} : (term28 N) = (term28 N).
Proof. exact (MK_COMB (@lem7598755 N) (@lem7598754 N)). Qed.
Lemma lem7598757 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7598758 {N : Type'} : (term29 N) = (term29 N).
Proof. exact (MK_COMB (@lem7598757) (@lem7598756 N)). Qed.
Lemma lem7598759 {N : Type'} : (term50 N) = (term50 N).
Proof. exact (MK_COMB (@lem7598758 N) (@lem7598752 N)). Qed.
Lemma lem7598760 {A : Type'} (s : A -> Prop) : ((@dimindex A s) = (@CARD A (@UNIV A))) = ((@dimindex A s) = (@CARD A (@UNIV A))).
Proof. exact (eq_refl ((@dimindex A s) = (@CARD A (@UNIV A)))). Qed.
Lemma lem7598761 {A : Type'} : (term35 A) = (term35 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7598760 A s)). Qed.
Lemma lem7598762 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7598763 {A : Type'} : (term36 A) = (term36 A).
Proof. exact (MK_COMB (@lem7598762 A) (@lem7598761 A)). Qed.
Lemma lem7598764 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7598765 {A : Type'} : (term37 A) = (term37 A).
Proof. exact (MK_COMB (@lem7598764) (@lem7598763 A)). Qed.
Lemma lem7598766 {A N : Type'} : (term51 A N) = (term51 A N).
Proof. exact (MK_COMB (@lem7598765 A) (@lem7598759 N)). Qed.
Lemma lem7598769 {N : Type'} : (term49 N) = (term49 N).
Proof. exact (eq_refl (term49 N)). Qed.
Lemma lem7598770 {A N : Type'} : (term52 A N) = (term52 A N).
Proof. exact (MK_COMB (@lem7598769 N) (@lem7598766 A N)). Qed.
Lemma lem7598775 {A : Type'} : (term53 A) = (term53 A).
Proof. exact (eq_refl (term53 A)). Qed.
Lemma lem7598776 {A N : Type'} : (term55 A N) = (term55 A N).
Proof. exact (MK_COMB (@lem7598775 A) (@lem7598770 A N)). Qed.
Lemma lem7598777 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7598778 {A N : Type'} : (term57 A N) = (term57 A N).
Proof. exact (MK_COMB (@lem7598777) (@lem7598776 A N)). Qed.
Lemma lem7598779 {A N : Type'} : (term63 A N) = (term63 A N).
Proof. exact (MK_COMB (@lem7598778 A N) (@lem7598735 A N)). Qed.
Lemma lem7598782 {N : Type'} : (term60 N) = (term60 N).
Proof. exact (eq_refl (term60 N)). Qed.
Lemma lem7598783 {A N : Type'} : (term83 A N) = (term83 A N).
Proof. exact (MK_COMB (@lem7598782 N) (@lem7598779 A N)). Qed.
Lemma lem7598792 {N : Type'} (s : N -> Prop) (n : nat) : ((@HAS_SIZE N s n) = (term79 N s n)) = ((@HAS_SIZE N s n) = (term79 N s n)).
Proof. exact (eq_refl ((@HAS_SIZE N s n) = (term79 N s n))). Qed.
Lemma lem7598793 {N : Type'} (s : N -> Prop) : (term80 N s) = (term80 N s).
Proof. exact (fun_ext (fun n : nat => @lem7598792 N s n)). Qed.
Lemma lem7598794 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7598795 {N : Type'} (s : N -> Prop) : (term81 N s) = (term81 N s).
Proof. exact (MK_COMB (@lem7598794) (@lem7598793 N s)). Qed.
Lemma lem7598796 {N : Type'} : (term82 N) = (term82 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7598795 N s)). Qed.
Lemma lem7598797 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7598798 {N : Type'} : (term4 N) = (term4 N).
Proof. exact (MK_COMB (@lem7598797 N) (@lem7598796 N)). Qed.
Lemma lem7598799 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7598800 {N : Type'} : (term11 N) = (term11 N).
Proof. exact (MK_COMB (@lem7598799) (@lem7598798 N)). Qed.
Lemma lem7598801 {N : Type'} (s : N -> Prop) : ((@dimindex N s) = (@CARD N (@UNIV N))) = ((@dimindex N s) = (@CARD N (@UNIV N))).
Proof. exact (eq_refl ((@dimindex N s) = (@CARD N (@UNIV N)))). Qed.
Lemma lem7598802 {N : Type'} : (term35 N) = (term35 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7598801 N s)). Qed.
Lemma lem7598803 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7598804 {N : Type'} : (term36 N) = (term36 N).
Proof. exact (MK_COMB (@lem7598803 N) (@lem7598802 N)). Qed.
Lemma lem7598805 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7598806 {N : Type'} : (term37 N) = (term37 N).
Proof. exact (MK_COMB (@lem7598805) (@lem7598804 N)). Qed.
Lemma lem7598807 {N : Type'} : (term66 N) = (term66 N).
Proof. exact (MK_COMB (@lem7598806 N) (@lem7598800 N)). Qed.
Lemma lem7598808 {A : Type'} (s : A -> Prop) : ((@dimindex A s) = term22) = ((@dimindex A s) = term22).
Proof. exact (eq_refl ((@dimindex A s) = term22)). Qed.
Lemma lem7598809 {A : Type'} : (term27 A) = (term27 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7598808 A s)). Qed.
Lemma lem7598810 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7598811 {A : Type'} : (term28 A) = (term28 A).
Proof. exact (MK_COMB (@lem7598810 A) (@lem7598809 A)). Qed.
Lemma lem7598812 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7598813 {A : Type'} : (term29 A) = (term29 A).
Proof. exact (MK_COMB (@lem7598812) (@lem7598811 A)). Qed.
Lemma lem7598814 {A N : Type'} : (term71 A N) = (term71 A N).
Proof. exact (MK_COMB (@lem7598813 A) (@lem7598807 N)). Qed.
Lemma lem7598819 {N : Type'} : (term65 N) = (term65 N).
Proof. exact (eq_refl (term65 N)). Qed.
Lemma lem7598820 {A N : Type'} : (term72 A N) = (term72 A N).
Proof. exact (MK_COMB (@lem7598819 N) (@lem7598814 A N)). Qed.
Lemma lem7598823 {A : Type'} : (term60 A) = (term60 A).
Proof. exact (eq_refl (term60 A)). Qed.
Lemma lem7598824 {A N : Type'} : (term73 A N) = (term73 A N).
Proof. exact (MK_COMB (@lem7598823 A) (@lem7598820 A N)). Qed.
Lemma lem7598833 {N : Type'} (s : N -> Prop) (n : nat) : ((@HAS_SIZE N s n) = (term79 N s n)) = ((@HAS_SIZE N s n) = (term79 N s n)).
Proof. exact (eq_refl ((@HAS_SIZE N s n) = (term79 N s n))). Qed.
Lemma lem7598834 {N : Type'} (s : N -> Prop) : (term80 N s) = (term80 N s).
Proof. exact (fun_ext (fun n : nat => @lem7598833 N s n)). Qed.
Lemma lem7598835 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7598836 {N : Type'} (s : N -> Prop) : (term81 N s) = (term81 N s).
Proof. exact (MK_COMB (@lem7598835) (@lem7598834 N s)). Qed.
Lemma lem7598837 {N : Type'} : (term82 N) = (term82 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7598836 N s)). Qed.
Lemma lem7598838 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7598839 {N : Type'} : (term4 N) = (term4 N).
Proof. exact (MK_COMB (@lem7598838 N) (@lem7598837 N)). Qed.
Lemma lem7598840 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7598841 {N : Type'} : (term11 N) = (term11 N).
Proof. exact (MK_COMB (@lem7598840) (@lem7598839 N)). Qed.
Lemma lem7598842 {N : Type'} (s : N -> Prop) : ((@dimindex N s) = (@CARD N (@UNIV N))) = ((@dimindex N s) = (@CARD N (@UNIV N))).
Proof. exact (eq_refl ((@dimindex N s) = (@CARD N (@UNIV N)))). Qed.
Lemma lem7598843 {N : Type'} : (term35 N) = (term35 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7598842 N s)). Qed.
Lemma lem7598844 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7598845 {N : Type'} : (term36 N) = (term36 N).
Proof. exact (MK_COMB (@lem7598844 N) (@lem7598843 N)). Qed.
Lemma lem7598846 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7598847 {N : Type'} : (term37 N) = (term37 N).
Proof. exact (MK_COMB (@lem7598846) (@lem7598845 N)). Qed.
Lemma lem7598848 {N : Type'} : (term66 N) = (term66 N).
Proof. exact (MK_COMB (@lem7598847 N) (@lem7598841 N)). Qed.
Lemma lem7598849 {A : Type'} (s : A -> Prop) : ((@dimindex A s) = (@CARD A (@UNIV A))) = ((@dimindex A s) = (@CARD A (@UNIV A))).
Proof. exact (eq_refl ((@dimindex A s) = (@CARD A (@UNIV A)))). Qed.
Lemma lem7598850 {A : Type'} : (term35 A) = (term35 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7598849 A s)). Qed.
Lemma lem7598851 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7598852 {A : Type'} : (term36 A) = (term36 A).
Proof. exact (MK_COMB (@lem7598851 A) (@lem7598850 A)). Qed.
Lemma lem7598853 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7598854 {A : Type'} : (term37 A) = (term37 A).
Proof. exact (MK_COMB (@lem7598853) (@lem7598852 A)). Qed.
Lemma lem7598855 {A N : Type'} : (term67 A N) = (term67 A N).
Proof. exact (MK_COMB (@lem7598854 A) (@lem7598848 N)). Qed.
Lemma lem7598860 {N : Type'} : (term65 N) = (term65 N).
Proof. exact (eq_refl (term65 N)). Qed.
Lemma lem7598861 {A N : Type'} : (term68 A N) = (term68 A N).
Proof. exact (MK_COMB (@lem7598860 N) (@lem7598855 A N)). Qed.
Lemma lem7598866 {A : Type'} : (term53 A) = (term53 A).
Proof. exact (eq_refl (term53 A)). Qed.
Lemma lem7598867 {A N : Type'} : (term69 A N) = (term69 A N).
Proof. exact (MK_COMB (@lem7598866 A) (@lem7598861 A N)). Qed.
Lemma lem7598868 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7598869 {A N : Type'} : (term70 A N) = (term70 A N).
Proof. exact (MK_COMB (@lem7598868) (@lem7598867 A N)). Qed.
Lemma lem7598870 {A N : Type'} : (term74 A N) = (term74 A N).
Proof. exact (MK_COMB (@lem7598869 A N) (@lem7598824 A N)). Qed.
Lemma lem7598875 {N : Type'} : (term53 N) = (term53 N).
Proof. exact (eq_refl (term53 N)). Qed.
Lemma lem7598876 {A N : Type'} : (term84 A N) = (term84 A N).
Proof. exact (MK_COMB (@lem7598875 N) (@lem7598870 A N)). Qed.
Lemma lem7598877 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7598878 {A N : Type'} : (term85 A N) = (term85 A N).
Proof. exact (MK_COMB (@lem7598877) (@lem7598876 A N)). Qed.
Lemma lem7598879 {A N : Type'} : (term78 A N) = (term78 A N).
Proof. exact (MK_COMB (@lem7598878 A N) (@lem7598783 A N)). Qed.
Lemma lem7598880 {A N : Type'} : (term86 A N) = (term86 A N).
Proof. exact (eq_refl (term86 A N)). Qed.
Lemma lem7598881 {A N : Type'} : ((term44 A N) = (term78 A N)) = ((term44 A N) = (term78 A N)).
Proof. exact (MK_COMB (@lem7598880 A N) (@lem7598879 A N)). Qed.
Lemma lem7598882 {A N : Type'} : (term44 A N) = (term78 A N).
Proof. exact (EQ_MP (@lem7598881 A N) (@lem7598696 A N)). Qed.
Lemma lem7598883 {A N : Type'} : (term87 A N) = (term87 A N).
Proof. exact (eq_refl (term87 A N)). Qed.
Lemma lem7598884 {A N : Type'} : ((term18 A N) = (term44 A N)) = ((term18 A N) = (term78 A N)).
Proof. exact (MK_COMB (@lem7598883 A N) (@lem7598882 A N)). Qed.
Lemma lem7598885 {A N : Type'} : (term18 A N) = (term78 A N).
Proof. exact (EQ_MP (@lem7598884 A N) (@lem7598351 A N)). Qed.
Lemma lem7599034 {A N : Type'} : (term6 A N) = (term78 A N).
Proof. exact (TRANS (@lem7598200 A N) (@lem7598885 A N)). Qed.
Lemma lem7599035 {A N : Type'} : (term78 A N) = (term6 A N).
Proof. exact (SYM (@lem7599034 A N)). Qed.
Lemma lem7599037 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7599038 {A N : Type'} : (term78 A N) = (term88 A N).
Proof. exact (@lem7599037 (term78 A N)). Qed.
Lemma lem7599039 {A N : Type'} : (term88 A N) = (term78 A N).
Proof. exact (SYM (@lem7599038 A N)). Qed.
Lemma lem7599040 {A N : Type'} (h1 : term89 A N) : term89 A N.
Proof. exact (h1). Qed.
Lemma lem7599043 {N : Type'} : (term90 N) = (@FINITE N (@UNIV N)).
Proof. exact (@lem16933 (@FINITE N (@UNIV N))). Qed.
Lemma lem7599046 {A : Type'} : (term90 A) = (@FINITE A (@UNIV A)).
Proof. exact (@lem16933 (@FINITE A (@UNIV A))). Qed.
Lemma lem7599048 {A : Type'} (s : A -> Prop) : ((@dimindex A s) = (@CARD A (@UNIV A))) = ((@dimindex A s) = (@CARD A (@UNIV A))).
Proof. exact (eq_refl ((@dimindex A s) = (@CARD A (@UNIV A)))). Qed.
Lemma lem7599049 {A : Type'} : (term35 A) = (term35 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7599048 A s)). Qed.
Lemma lem7599050 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7599051 {A : Type'} : (term36 A) = (term36 A).
Proof. exact (MK_COMB (@lem7599050 A) (@lem7599049 A)). Qed.
Lemma lem7599052 {N : Type'} (s : N -> Prop) : ((@dimindex N s) = (@CARD N (@UNIV N))) = ((@dimindex N s) = (@CARD N (@UNIV N))).
Proof. exact (eq_refl ((@dimindex N s) = (@CARD N (@UNIV N)))). Qed.
Lemma lem7599053 {N : Type'} : (term35 N) = (term35 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7599052 N s)). Qed.
Lemma lem7599054 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7599055 {N : Type'} : (term36 N) = (term36 N).
Proof. exact (MK_COMB (@lem7599054 N) (@lem7599053 N)). Qed.
Lemma lem7599066 {N : Type'} (s : N -> Prop) (n : nat) : (term91 N s n) = (term92 N s n).
Proof. exact (@lem17045 (@FINITE N s) ((@CARD N s) = n)). Qed.
Lemma lem7599072 {N : Type'} (s : N -> Prop) (n : nat) : (term93 N s n) = (term93 N s n).
Proof. exact (eq_refl (term93 N s n)). Qed.
Lemma lem7599074 {N : Type'} (s : N -> Prop) (n : nat) : (term94 N s n) = (term94 N s n).
Proof. exact (eq_refl (term94 N s n)). Qed.
Lemma lem7599075 {N : Type'} (s : N -> Prop) (n : nat) : (term95 N s n) = (term96 N s n).
Proof. exact (MK_COMB (@lem7599074 N s n) (@lem7599066 N s n)). Qed.
Lemma lem7599076 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7599077 {N : Type'} (s : N -> Prop) (n : nat) : (term97 N s n) = (term98 N s n).
Proof. exact (MK_COMB (@lem7599076) (@lem7599075 N s n)). Qed.
Lemma lem7599078 {N : Type'} (s : N -> Prop) (n : nat) : (term99 N s n) = (term100 N s n).
Proof. exact (MK_COMB (@lem7599077 N s n) (@lem7599072 N s n)). Qed.
Lemma lem7599079 {N : Type'} (s : N -> Prop) (n : nat) : ((@HAS_SIZE N s n) = (term79 N s n)) = (term99 N s n).
Proof. exact (@lem17784 (@HAS_SIZE N s n) (term79 N s n)). Qed.
Lemma lem7599080 {N : Type'} (s : N -> Prop) (n : nat) : ((@HAS_SIZE N s n) = (term79 N s n)) = (term100 N s n).
Proof. exact (TRANS (@lem7599079 N s n) (@lem7599078 N s n)). Qed.
Lemma lem7599081 {N : Type'} (s : N -> Prop) : (term80 N s) = (term101 N s).
Proof. exact (fun_ext (fun n : nat => @lem7599080 N s n)). Qed.
Lemma lem7599082 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7599083 {N : Type'} (s : N -> Prop) : (term81 N s) = (term102 N s).
Proof. exact (MK_COMB (@lem7599082) (@lem7599081 N s)). Qed.
Lemma lem7599084 {N : Type'} : (term82 N) = (term103 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7599083 N s)). Qed.
Lemma lem7599085 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7599086 {N : Type'} : (term4 N) = (term104 N).
Proof. exact (MK_COMB (@lem7599085 N) (@lem7599084 N)). Qed.
Lemma lem7599087 {N : Type'} : (term105 N) = (term4 N).
Proof. exact (@lem16933 (term4 N)). Qed.
Lemma lem7599088 {N : Type'} : (term105 N) = (term104 N).
Proof. exact (TRANS (@lem7599087 N) (@lem7599086 N)). Qed.
Lemma lem7599089 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7599090 {N : Type'} : (term106 N) = (term106 N).
Proof. exact (MK_COMB (@lem7599089) (@lem7599055 N)). Qed.
Lemma lem7599091 {N : Type'} : (term107 N) = (term108 N).
Proof. exact (MK_COMB (@lem7599090 N) (@lem7599088 N)). Qed.
Lemma lem7599092 {N : Type'} : (term109 N) = (term107 N).
Proof. exact (@lem17362 (term36 N) (term11 N)). Qed.
Lemma lem7599093 {N : Type'} : (term109 N) = (term108 N).
Proof. exact (TRANS (@lem7599092 N) (@lem7599091 N)). Qed.
Lemma lem7599094 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7599095 {A : Type'} : (term106 A) = (term106 A).
Proof. exact (MK_COMB (@lem7599094) (@lem7599051 A)). Qed.
Lemma lem7599096 {A N : Type'} : (term110 A N) = (term111 A N).
Proof. exact (MK_COMB (@lem7599095 A) (@lem7599093 N)). Qed.
Lemma lem7599097 {A N : Type'} : (term112 A N) = (term110 A N).
Proof. exact (@lem17362 (term36 A) (term66 N)). Qed.
Lemma lem7599098 {A N : Type'} : (term112 A N) = (term111 A N).
Proof. exact (TRANS (@lem7599097 A N) (@lem7599096 A N)). Qed.
Lemma lem7599100 {N : Type'} : (term113 N) = (term113 N).
Proof. exact (eq_refl (term113 N)). Qed.
Lemma lem7599101 {A N : Type'} : (term114 A N) = (term115 A N).
Proof. exact (MK_COMB (@lem7599100 N) (@lem7599098 A N)). Qed.
Lemma lem7599102 {A N : Type'} : (term116 A N) = (term114 A N).
Proof. exact (@lem17362 (term46 N) (term67 A N)). Qed.
Lemma lem7599103 {A N : Type'} : (term116 A N) = (term115 A N).
Proof. exact (TRANS (@lem7599102 A N) (@lem7599101 A N)). Qed.
Lemma lem7599104 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7599105 {A : Type'} : (term117 A) = (term118 A).
Proof. exact (MK_COMB (@lem7599104) (@lem7599046 A)). Qed.
Lemma lem7599106 {A N : Type'} : (term119 A N) = (term120 A N).
Proof. exact (MK_COMB (@lem7599105 A) (@lem7599103 A N)). Qed.
Lemma lem7599107 {A N : Type'} : (term121 A N) = (term119 A N).
Proof. exact (@lem17160 (term122 A) (term68 A N)). Qed.
Lemma lem7599108 {A N : Type'} : (term121 A N) = (term120 A N).
Proof. exact (TRANS (@lem7599107 A N) (@lem7599106 A N)). Qed.
Lemma lem7599111 {A : Type'} (s : A -> Prop) : ((@dimindex A s) = term22) = ((@dimindex A s) = term22).
Proof. exact (eq_refl ((@dimindex A s) = term22)). Qed.
Lemma lem7599112 {A : Type'} : (term27 A) = (term27 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7599111 A s)). Qed.
Lemma lem7599113 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7599114 {A : Type'} : (term28 A) = (term28 A).
Proof. exact (MK_COMB (@lem7599113 A) (@lem7599112 A)). Qed.
Lemma lem7599115 {N : Type'} (s : N -> Prop) : ((@dimindex N s) = (@CARD N (@UNIV N))) = ((@dimindex N s) = (@CARD N (@UNIV N))).
Proof. exact (eq_refl ((@dimindex N s) = (@CARD N (@UNIV N)))). Qed.
Lemma lem7599116 {N : Type'} : (term35 N) = (term35 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7599115 N s)). Qed.
Lemma lem7599117 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7599118 {N : Type'} : (term36 N) = (term36 N).
Proof. exact (MK_COMB (@lem7599117 N) (@lem7599116 N)). Qed.
Lemma lem7599129 {N : Type'} (s : N -> Prop) (n : nat) : (term91 N s n) = (term92 N s n).
Proof. exact (@lem17045 (@FINITE N s) ((@CARD N s) = n)). Qed.
Lemma lem7599135 {N : Type'} (s : N -> Prop) (n : nat) : (term93 N s n) = (term93 N s n).
Proof. exact (eq_refl (term93 N s n)). Qed.
Lemma lem7599137 {N : Type'} (s : N -> Prop) (n : nat) : (term94 N s n) = (term94 N s n).
Proof. exact (eq_refl (term94 N s n)). Qed.
Lemma lem7599138 {N : Type'} (s : N -> Prop) (n : nat) : (term95 N s n) = (term96 N s n).
Proof. exact (MK_COMB (@lem7599137 N s n) (@lem7599129 N s n)). Qed.
Lemma lem7599139 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7599140 {N : Type'} (s : N -> Prop) (n : nat) : (term97 N s n) = (term98 N s n).
Proof. exact (MK_COMB (@lem7599139) (@lem7599138 N s n)). Qed.
Lemma lem7599141 {N : Type'} (s : N -> Prop) (n : nat) : (term99 N s n) = (term100 N s n).
Proof. exact (MK_COMB (@lem7599140 N s n) (@lem7599135 N s n)). Qed.
Lemma lem7599142 {N : Type'} (s : N -> Prop) (n : nat) : ((@HAS_SIZE N s n) = (term79 N s n)) = (term99 N s n).
Proof. exact (@lem17784 (@HAS_SIZE N s n) (term79 N s n)). Qed.
Lemma lem7599143 {N : Type'} (s : N -> Prop) (n : nat) : ((@HAS_SIZE N s n) = (term79 N s n)) = (term100 N s n).
Proof. exact (TRANS (@lem7599142 N s n) (@lem7599141 N s n)). Qed.
Lemma lem7599144 {N : Type'} (s : N -> Prop) : (term80 N s) = (term101 N s).
Proof. exact (fun_ext (fun n : nat => @lem7599143 N s n)). Qed.
Lemma lem7599145 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7599146 {N : Type'} (s : N -> Prop) : (term81 N s) = (term102 N s).
Proof. exact (MK_COMB (@lem7599145) (@lem7599144 N s)). Qed.
Lemma lem7599147 {N : Type'} : (term82 N) = (term103 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7599146 N s)). Qed.
Lemma lem7599148 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7599149 {N : Type'} : (term4 N) = (term104 N).
Proof. exact (MK_COMB (@lem7599148 N) (@lem7599147 N)). Qed.
Lemma lem7599150 {N : Type'} : (term105 N) = (term4 N).
Proof. exact (@lem16933 (term4 N)). Qed.
Lemma lem7599151 {N : Type'} : (term105 N) = (term104 N).
Proof. exact (TRANS (@lem7599150 N) (@lem7599149 N)). Qed.
Lemma lem7599152 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7599153 {N : Type'} : (term106 N) = (term106 N).
Proof. exact (MK_COMB (@lem7599152) (@lem7599118 N)). Qed.
Lemma lem7599154 {N : Type'} : (term107 N) = (term108 N).
Proof. exact (MK_COMB (@lem7599153 N) (@lem7599151 N)). Qed.
Lemma lem7599155 {N : Type'} : (term109 N) = (term107 N).
Proof. exact (@lem17362 (term36 N) (term11 N)). Qed.
Lemma lem7599156 {N : Type'} : (term109 N) = (term108 N).
Proof. exact (TRANS (@lem7599155 N) (@lem7599154 N)). Qed.
Lemma lem7599157 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7599158 {A : Type'} : (term123 A) = (term123 A).
Proof. exact (MK_COMB (@lem7599157) (@lem7599114 A)). Qed.
Lemma lem7599159 {A N : Type'} : (term124 A N) = (term125 A N).
Proof. exact (MK_COMB (@lem7599158 A) (@lem7599156 N)). Qed.
Lemma lem7599160 {A N : Type'} : (term126 A N) = (term124 A N).
Proof. exact (@lem17362 (term28 A) (term66 N)). Qed.
Lemma lem7599161 {A N : Type'} : (term126 A N) = (term125 A N).
Proof. exact (TRANS (@lem7599160 A N) (@lem7599159 A N)). Qed.
Lemma lem7599163 {N : Type'} : (term113 N) = (term113 N).
Proof. exact (eq_refl (term113 N)). Qed.
Lemma lem7599164 {A N : Type'} : (term127 A N) = (term128 A N).
Proof. exact (MK_COMB (@lem7599163 N) (@lem7599161 A N)). Qed.
Lemma lem7599165 {A N : Type'} : (term129 A N) = (term127 A N).
Proof. exact (@lem17362 (term46 N) (term71 A N)). Qed.
Lemma lem7599166 {A N : Type'} : (term129 A N) = (term128 A N).
Proof. exact (TRANS (@lem7599165 A N) (@lem7599164 A N)). Qed.
Lemma lem7599168 {A : Type'} : (term130 A) = (term130 A).
Proof. exact (eq_refl (term130 A)). Qed.
Lemma lem7599169 {A N : Type'} : (term131 A N) = (term132 A N).
Proof. exact (MK_COMB (@lem7599168 A) (@lem7599166 A N)). Qed.
Lemma lem7599170 {A N : Type'} : (term133 A N) = (term131 A N).
Proof. exact (@lem17160 (@FINITE A (@UNIV A)) (term72 A N)). Qed.
Lemma lem7599171 {A N : Type'} : (term133 A N) = (term132 A N).
Proof. exact (TRANS (@lem7599170 A N) (@lem7599169 A N)). Qed.
Lemma lem7599172 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7599173 {A N : Type'} : (term134 A N) = (term135 A N).
Proof. exact (MK_COMB (@lem7599172) (@lem7599108 A N)). Qed.
Lemma lem7599174 {A N : Type'} : (term136 A N) = (term137 A N).
Proof. exact (MK_COMB (@lem7599173 A N) (@lem7599171 A N)). Qed.
Lemma lem7599175 {A N : Type'} : (term138 A N) = (term136 A N).
Proof. exact (@lem17045 (term69 A N) (term73 A N)). Qed.
Lemma lem7599176 {A N : Type'} : (term138 A N) = (term137 A N).
Proof. exact (TRANS (@lem7599175 A N) (@lem7599174 A N)). Qed.
Lemma lem7599177 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7599178 {N : Type'} : (term117 N) = (term118 N).
Proof. exact (MK_COMB (@lem7599177) (@lem7599043 N)). Qed.
Lemma lem7599179 {A N : Type'} : (term139 A N) = (term140 A N).
Proof. exact (MK_COMB (@lem7599178 N) (@lem7599176 A N)). Qed.
Lemma lem7599180 {A N : Type'} : (term141 A N) = (term139 A N).
Proof. exact (@lem17160 (term122 N) (term74 A N)). Qed.
Lemma lem7599181 {A N : Type'} : (term141 A N) = (term140 A N).
Proof. exact (TRANS (@lem7599180 A N) (@lem7599179 A N)). Qed.
Lemma lem7599185 {A : Type'} : (term90 A) = (@FINITE A (@UNIV A)).
Proof. exact (@lem16933 (@FINITE A (@UNIV A))). Qed.
Lemma lem7599187 {A : Type'} (s : A -> Prop) : ((@dimindex A s) = (@CARD A (@UNIV A))) = ((@dimindex A s) = (@CARD A (@UNIV A))).
Proof. exact (eq_refl ((@dimindex A s) = (@CARD A (@UNIV A)))). Qed.
Lemma lem7599188 {A : Type'} : (term35 A) = (term35 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7599187 A s)). Qed.
Lemma lem7599189 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7599190 {A : Type'} : (term36 A) = (term36 A).
Proof. exact (MK_COMB (@lem7599189 A) (@lem7599188 A)). Qed.
Lemma lem7599191 {N : Type'} (s : N -> Prop) : ((@dimindex N s) = term22) = ((@dimindex N s) = term22).
Proof. exact (eq_refl ((@dimindex N s) = term22)). Qed.
Lemma lem7599192 {N : Type'} : (term27 N) = (term27 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7599191 N s)). Qed.
Lemma lem7599193 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7599194 {N : Type'} : (term28 N) = (term28 N).
Proof. exact (MK_COMB (@lem7599193 N) (@lem7599192 N)). Qed.
Lemma lem7599205 {N : Type'} (s : N -> Prop) (n : nat) : (term91 N s n) = (term92 N s n).
Proof. exact (@lem17045 (@FINITE N s) ((@CARD N s) = n)). Qed.
Lemma lem7599211 {N : Type'} (s : N -> Prop) (n : nat) : (term93 N s n) = (term93 N s n).
Proof. exact (eq_refl (term93 N s n)). Qed.
Lemma lem7599213 {N : Type'} (s : N -> Prop) (n : nat) : (term94 N s n) = (term94 N s n).
Proof. exact (eq_refl (term94 N s n)). Qed.
Lemma lem7599214 {N : Type'} (s : N -> Prop) (n : nat) : (term95 N s n) = (term96 N s n).
Proof. exact (MK_COMB (@lem7599213 N s n) (@lem7599205 N s n)). Qed.
Lemma lem7599215 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7599216 {N : Type'} (s : N -> Prop) (n : nat) : (term97 N s n) = (term98 N s n).
Proof. exact (MK_COMB (@lem7599215) (@lem7599214 N s n)). Qed.
Lemma lem7599217 {N : Type'} (s : N -> Prop) (n : nat) : (term99 N s n) = (term100 N s n).
Proof. exact (MK_COMB (@lem7599216 N s n) (@lem7599211 N s n)). Qed.
Lemma lem7599218 {N : Type'} (s : N -> Prop) (n : nat) : ((@HAS_SIZE N s n) = (term79 N s n)) = (term99 N s n).
Proof. exact (@lem17784 (@HAS_SIZE N s n) (term79 N s n)). Qed.
Lemma lem7599219 {N : Type'} (s : N -> Prop) (n : nat) : ((@HAS_SIZE N s n) = (term79 N s n)) = (term100 N s n).
Proof. exact (TRANS (@lem7599218 N s n) (@lem7599217 N s n)). Qed.
Lemma lem7599220 {N : Type'} (s : N -> Prop) : (term80 N s) = (term101 N s).
Proof. exact (fun_ext (fun n : nat => @lem7599219 N s n)). Qed.
Lemma lem7599221 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7599222 {N : Type'} (s : N -> Prop) : (term81 N s) = (term102 N s).
Proof. exact (MK_COMB (@lem7599221) (@lem7599220 N s)). Qed.
Lemma lem7599223 {N : Type'} : (term82 N) = (term103 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7599222 N s)). Qed.
Lemma lem7599224 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7599225 {N : Type'} : (term4 N) = (term104 N).
Proof. exact (MK_COMB (@lem7599224 N) (@lem7599223 N)). Qed.
Lemma lem7599226 {N : Type'} : (term105 N) = (term4 N).
Proof. exact (@lem16933 (term4 N)). Qed.
Lemma lem7599227 {N : Type'} : (term105 N) = (term104 N).
Proof. exact (TRANS (@lem7599226 N) (@lem7599225 N)). Qed.
Lemma lem7599228 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7599229 {N : Type'} : (term123 N) = (term123 N).
Proof. exact (MK_COMB (@lem7599228) (@lem7599194 N)). Qed.
Lemma lem7599230 {N : Type'} : (term142 N) = (term143 N).
Proof. exact (MK_COMB (@lem7599229 N) (@lem7599227 N)). Qed.
Lemma lem7599231 {N : Type'} : (term144 N) = (term142 N).
Proof. exact (@lem17362 (term28 N) (term11 N)). Qed.
Lemma lem7599232 {N : Type'} : (term144 N) = (term143 N).
Proof. exact (TRANS (@lem7599231 N) (@lem7599230 N)). Qed.
Lemma lem7599233 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7599234 {A : Type'} : (term106 A) = (term106 A).
Proof. exact (MK_COMB (@lem7599233) (@lem7599190 A)). Qed.
Lemma lem7599235 {A N : Type'} : (term145 A N) = (term146 A N).
Proof. exact (MK_COMB (@lem7599234 A) (@lem7599232 N)). Qed.
Lemma lem7599236 {A N : Type'} : (term147 A N) = (term145 A N).
Proof. exact (@lem17362 (term36 A) (term50 N)). Qed.
Lemma lem7599237 {A N : Type'} : (term147 A N) = (term146 A N).
Proof. exact (TRANS (@lem7599236 A N) (@lem7599235 A N)). Qed.
Lemma lem7599239 {N : Type'} : (term148 N) = (term148 N).
Proof. exact (eq_refl (term148 N)). Qed.
Lemma lem7599240 {A N : Type'} : (term149 A N) = (term150 A N).
Proof. exact (MK_COMB (@lem7599239 N) (@lem7599237 A N)). Qed.
Lemma lem7599241 {A N : Type'} : (term151 A N) = (term149 A N).
Proof. exact (@lem17362 (term1 N) (term51 A N)). Qed.
Lemma lem7599242 {A N : Type'} : (term151 A N) = (term150 A N).
Proof. exact (TRANS (@lem7599241 A N) (@lem7599240 A N)). Qed.
Lemma lem7599243 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7599244 {A : Type'} : (term117 A) = (term118 A).
Proof. exact (MK_COMB (@lem7599243) (@lem7599185 A)). Qed.
Lemma lem7599245 {A N : Type'} : (term152 A N) = (term153 A N).
Proof. exact (MK_COMB (@lem7599244 A) (@lem7599242 A N)). Qed.
Lemma lem7599246 {A N : Type'} : (term154 A N) = (term152 A N).
Proof. exact (@lem17160 (term122 A) (term52 A N)). Qed.
Lemma lem7599247 {A N : Type'} : (term154 A N) = (term153 A N).
Proof. exact (TRANS (@lem7599246 A N) (@lem7599245 A N)). Qed.
Lemma lem7599250 {A : Type'} (s : A -> Prop) : ((@dimindex A s) = term22) = ((@dimindex A s) = term22).
Proof. exact (eq_refl ((@dimindex A s) = term22)). Qed.
Lemma lem7599251 {A : Type'} : (term27 A) = (term27 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7599250 A s)). Qed.
Lemma lem7599252 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7599253 {A : Type'} : (term28 A) = (term28 A).
Proof. exact (MK_COMB (@lem7599252 A) (@lem7599251 A)). Qed.
Lemma lem7599254 {N : Type'} (s : N -> Prop) : ((@dimindex N s) = term22) = ((@dimindex N s) = term22).
Proof. exact (eq_refl ((@dimindex N s) = term22)). Qed.
Lemma lem7599255 {N : Type'} : (term27 N) = (term27 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7599254 N s)). Qed.
Lemma lem7599256 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7599257 {N : Type'} : (term28 N) = (term28 N).
Proof. exact (MK_COMB (@lem7599256 N) (@lem7599255 N)). Qed.
Lemma lem7599268 {N : Type'} (s : N -> Prop) (n : nat) : (term91 N s n) = (term92 N s n).
Proof. exact (@lem17045 (@FINITE N s) ((@CARD N s) = n)). Qed.
Lemma lem7599274 {N : Type'} (s : N -> Prop) (n : nat) : (term93 N s n) = (term93 N s n).
Proof. exact (eq_refl (term93 N s n)). Qed.
Lemma lem7599276 {N : Type'} (s : N -> Prop) (n : nat) : (term94 N s n) = (term94 N s n).
Proof. exact (eq_refl (term94 N s n)). Qed.
Lemma lem7599277 {N : Type'} (s : N -> Prop) (n : nat) : (term95 N s n) = (term96 N s n).
Proof. exact (MK_COMB (@lem7599276 N s n) (@lem7599268 N s n)). Qed.
Lemma lem7599278 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7599279 {N : Type'} (s : N -> Prop) (n : nat) : (term97 N s n) = (term98 N s n).
Proof. exact (MK_COMB (@lem7599278) (@lem7599277 N s n)). Qed.
Lemma lem7599280 {N : Type'} (s : N -> Prop) (n : nat) : (term99 N s n) = (term100 N s n).
Proof. exact (MK_COMB (@lem7599279 N s n) (@lem7599274 N s n)). Qed.
Lemma lem7599281 {N : Type'} (s : N -> Prop) (n : nat) : ((@HAS_SIZE N s n) = (term79 N s n)) = (term99 N s n).
Proof. exact (@lem17784 (@HAS_SIZE N s n) (term79 N s n)). Qed.
Lemma lem7599282 {N : Type'} (s : N -> Prop) (n : nat) : ((@HAS_SIZE N s n) = (term79 N s n)) = (term100 N s n).
Proof. exact (TRANS (@lem7599281 N s n) (@lem7599280 N s n)). Qed.
Lemma lem7599283 {N : Type'} (s : N -> Prop) : (term80 N s) = (term101 N s).
Proof. exact (fun_ext (fun n : nat => @lem7599282 N s n)). Qed.
Lemma lem7599284 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7599285 {N : Type'} (s : N -> Prop) : (term81 N s) = (term102 N s).
Proof. exact (MK_COMB (@lem7599284) (@lem7599283 N s)). Qed.
Lemma lem7599286 {N : Type'} : (term82 N) = (term103 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7599285 N s)). Qed.
Lemma lem7599287 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7599288 {N : Type'} : (term4 N) = (term104 N).
Proof. exact (MK_COMB (@lem7599287 N) (@lem7599286 N)). Qed.
Lemma lem7599289 {N : Type'} : (term105 N) = (term4 N).
Proof. exact (@lem16933 (term4 N)). Qed.
Lemma lem7599290 {N : Type'} : (term105 N) = (term104 N).
Proof. exact (TRANS (@lem7599289 N) (@lem7599288 N)). Qed.
Lemma lem7599291 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7599292 {N : Type'} : (term123 N) = (term123 N).
Proof. exact (MK_COMB (@lem7599291) (@lem7599257 N)). Qed.
Lemma lem7599293 {N : Type'} : (term142 N) = (term143 N).
Proof. exact (MK_COMB (@lem7599292 N) (@lem7599290 N)). Qed.
Lemma lem7599294 {N : Type'} : (term144 N) = (term142 N).
Proof. exact (@lem17362 (term28 N) (term11 N)). Qed.
Lemma lem7599295 {N : Type'} : (term144 N) = (term143 N).
Proof. exact (TRANS (@lem7599294 N) (@lem7599293 N)). Qed.
Lemma lem7599296 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7599297 {A : Type'} : (term123 A) = (term123 A).
Proof. exact (MK_COMB (@lem7599296) (@lem7599253 A)). Qed.
Lemma lem7599298 {A N : Type'} : (term155 A N) = (term156 A N).
Proof. exact (MK_COMB (@lem7599297 A) (@lem7599295 N)). Qed.
Lemma lem7599299 {A N : Type'} : (term157 A N) = (term155 A N).
Proof. exact (@lem17362 (term28 A) (term50 N)). Qed.
Lemma lem7599300 {A N : Type'} : (term157 A N) = (term156 A N).
Proof. exact (TRANS (@lem7599299 A N) (@lem7599298 A N)). Qed.
Lemma lem7599302 {N : Type'} : (term148 N) = (term148 N).
Proof. exact (eq_refl (term148 N)). Qed.
Lemma lem7599303 {A N : Type'} : (term158 A N) = (term159 A N).
Proof. exact (MK_COMB (@lem7599302 N) (@lem7599300 A N)). Qed.
Lemma lem7599304 {A N : Type'} : (term160 A N) = (term158 A N).
Proof. exact (@lem17362 (term1 N) (term58 A N)). Qed.
Lemma lem7599305 {A N : Type'} : (term160 A N) = (term159 A N).
Proof. exact (TRANS (@lem7599304 A N) (@lem7599303 A N)). Qed.
Lemma lem7599307 {A : Type'} : (term130 A) = (term130 A).
Proof. exact (eq_refl (term130 A)). Qed.
Lemma lem7599308 {A N : Type'} : (term161 A N) = (term162 A N).
Proof. exact (MK_COMB (@lem7599307 A) (@lem7599305 A N)). Qed.
Lemma lem7599309 {A N : Type'} : (term163 A N) = (term161 A N).
Proof. exact (@lem17160 (@FINITE A (@UNIV A)) (term59 A N)). Qed.
Lemma lem7599310 {A N : Type'} : (term163 A N) = (term162 A N).
Proof. exact (TRANS (@lem7599309 A N) (@lem7599308 A N)). Qed.
Lemma lem7599311 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7599312 {A N : Type'} : (term164 A N) = (term165 A N).
Proof. exact (MK_COMB (@lem7599311) (@lem7599247 A N)). Qed.
Lemma lem7599313 {A N : Type'} : (term166 A N) = (term167 A N).
Proof. exact (MK_COMB (@lem7599312 A N) (@lem7599310 A N)). Qed.
Lemma lem7599314 {A N : Type'} : (term168 A N) = (term166 A N).
Proof. exact (@lem17045 (term55 A N) (term62 A N)). Qed.
Lemma lem7599315 {A N : Type'} : (term168 A N) = (term167 A N).
Proof. exact (TRANS (@lem7599314 A N) (@lem7599313 A N)). Qed.
Lemma lem7599317 {N : Type'} : (term130 N) = (term130 N).
Proof. exact (eq_refl (term130 N)). Qed.
Lemma lem7599318 {A N : Type'} : (term169 A N) = (term170 A N).
Proof. exact (MK_COMB (@lem7599317 N) (@lem7599315 A N)). Qed.
Lemma lem7599319 {A N : Type'} : (term171 A N) = (term169 A N).
Proof. exact (@lem17160 (@FINITE N (@UNIV N)) (term63 A N)). Qed.
Lemma lem7599320 {A N : Type'} : (term171 A N) = (term170 A N).
Proof. exact (TRANS (@lem7599319 A N) (@lem7599318 A N)). Qed.
Lemma lem7599321 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7599322 {A N : Type'} : (term172 A N) = (term173 A N).
Proof. exact (MK_COMB (@lem7599321) (@lem7599181 A N)). Qed.
Lemma lem7599323 {A N : Type'} : (term174 A N) = (term175 A N).
Proof. exact (MK_COMB (@lem7599322 A N) (@lem7599320 A N)). Qed.
Lemma lem7599324 {A N : Type'} : (term89 A N) = (term174 A N).
Proof. exact (@lem17045 (term84 A N) (term83 A N)). Qed.
Lemma lem7599325 {A N : Type'} : (term89 A N) = (term175 A N).
Proof. exact (TRANS (@lem7599324 A N) (@lem7599323 A N)). Qed.
Lemma lem7599339 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term176 A P Q) = (term177 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7599340 (P : nat -> Prop) (Q : nat -> Prop) : (term178 P Q) = (term179 P Q).
Proof. exact (@lem7599339 nat P Q). Qed.
Lemma lem7599341 {N : Type'} (s : N -> Prop) : (term180 N s) = (term181 N s).
Proof. exact (@lem7599340 (term182 N s) (term183 N s)). Qed.
Lemma lem7599342 {N : Type'} (s : N -> Prop) (n : nat) : (term184 N s n) = (term96 N s n).
Proof. exact (eq_refl (term184 N s n)). Qed.
Lemma lem7599343 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7599344 {N : Type'} (s : N -> Prop) (n : nat) : (term185 N s n) = (term98 N s n).
Proof. exact (MK_COMB (@lem7599343) (@lem7599342 N s n)). Qed.
Lemma lem7599345 {N : Type'} (s : N -> Prop) (n : nat) : (term186 N s n) = (term93 N s n).
Proof. exact (eq_refl (term186 N s n)). Qed.
Lemma lem7599346 {N : Type'} (s : N -> Prop) (n : nat) : (term187 N s n) = (term100 N s n).
Proof. exact (MK_COMB (@lem7599344 N s n) (@lem7599345 N s n)). Qed.
Lemma lem7599347 {N : Type'} (s : N -> Prop) : (term188 N s) = (term101 N s).
Proof. exact (fun_ext (fun n : nat => @lem7599346 N s n)). Qed.
Lemma lem7599348 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7599349 {N : Type'} (s : N -> Prop) : (term180 N s) = (term102 N s).
Proof. exact (MK_COMB (@lem7599348) (@lem7599347 N s)). Qed.
Lemma lem7599350 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7599351 {N : Type'} (s : N -> Prop) : (term189 N s) = (term190 N s).
Proof. exact (MK_COMB (@lem7599350) (@lem7599349 N s)). Qed.
Lemma lem7599352 {N : Type'} (s : N -> Prop) (n : nat) : (term184 N s n) = (term96 N s n).
Proof. exact (eq_refl (term184 N s n)). Qed.
Lemma lem7599353 {N : Type'} (s : N -> Prop) : (term191 N s) = (term182 N s).
Proof. exact (fun_ext (fun n : nat => @lem7599352 N s n)). Qed.
Lemma lem7599354 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7599355 {N : Type'} (s : N -> Prop) : (term192 N s) = (term193 N s).
Proof. exact (MK_COMB (@lem7599354) (@lem7599353 N s)). Qed.
Lemma lem7599356 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7599357 {N : Type'} (s : N -> Prop) : (term194 N s) = (term195 N s).
Proof. exact (MK_COMB (@lem7599356) (@lem7599355 N s)). Qed.
Lemma lem7599358 {N : Type'} (s : N -> Prop) (n : nat) : (term186 N s n) = (term93 N s n).
Proof. exact (eq_refl (term186 N s n)). Qed.
Lemma lem7599359 {N : Type'} (s : N -> Prop) : (term196 N s) = (term183 N s).
Proof. exact (fun_ext (fun n : nat => @lem7599358 N s n)). Qed.
Lemma lem7599360 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7599361 {N : Type'} (s : N -> Prop) : (term197 N s) = (term198 N s).
Proof. exact (MK_COMB (@lem7599360) (@lem7599359 N s)). Qed.
Lemma lem7599362 {N : Type'} (s : N -> Prop) : (term181 N s) = (term199 N s).
Proof. exact (MK_COMB (@lem7599357 N s) (@lem7599361 N s)). Qed.
Lemma lem7599363 {N : Type'} (s : N -> Prop) : ((term180 N s) = (term181 N s)) = ((term102 N s) = (term199 N s)).
Proof. exact (MK_COMB (@lem7599351 N s) (@lem7599362 N s)). Qed.
Lemma lem7599364 {N : Type'} (s : N -> Prop) : (term102 N s) = (term199 N s).
Proof. exact (EQ_MP (@lem7599363 N s) (@lem7599341 N s)). Qed.
Lemma lem7599461 {N : Type'} : (term103 N) = (term200 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7599364 N s)). Qed.
Lemma lem7599462 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7599463 {N : Type'} : (term104 N) = (term201 N).
Proof. exact (MK_COMB (@lem7599462 N) (@lem7599461 N)). Qed.
Lemma lem7599465 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term176 A P Q) = (term177 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7599466 {N : Type'} (P : type686 N) (Q : type686 N) : (term202 N P Q) = (term203 N P Q).
Proof. exact (@lem7599465 (N -> Prop) P Q). Qed.
Lemma lem7599467 {N : Type'} : (term204 N) = (term205 N).
Proof. exact (@lem7599466 N (term206 N) (term207 N)). Qed.
Lemma lem7599468 {N : Type'} (s : N -> Prop) : (term208 N s) = (term193 N s).
Proof. exact (eq_refl (term208 N s)). Qed.
Lemma lem7599469 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7599470 {N : Type'} (s : N -> Prop) : (term209 N s) = (term195 N s).
Proof. exact (MK_COMB (@lem7599469) (@lem7599468 N s)). Qed.
Lemma lem7599471 {N : Type'} (s : N -> Prop) : (term210 N s) = (term198 N s).
Proof. exact (eq_refl (term210 N s)). Qed.
Lemma lem7599472 {N : Type'} (s : N -> Prop) : (term211 N s) = (term199 N s).
Proof. exact (MK_COMB (@lem7599470 N s) (@lem7599471 N s)). Qed.
Lemma lem7599473 {N : Type'} : (term212 N) = (term200 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7599472 N s)). Qed.
Lemma lem7599474 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7599475 {N : Type'} : (term204 N) = (term201 N).
Proof. exact (MK_COMB (@lem7599474 N) (@lem7599473 N)). Qed.
Lemma lem7599476 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7599477 {N : Type'} : (term213 N) = (term214 N).
Proof. exact (MK_COMB (@lem7599476) (@lem7599475 N)). Qed.
Lemma lem7599478 {N : Type'} (s : N -> Prop) : (term208 N s) = (term193 N s).
Proof. exact (eq_refl (term208 N s)). Qed.
Lemma lem7599479 {N : Type'} : (term215 N) = (term206 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7599478 N s)). Qed.
Lemma lem7599480 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7599481 {N : Type'} : (term216 N) = (term217 N).
Proof. exact (MK_COMB (@lem7599480 N) (@lem7599479 N)). Qed.
Lemma lem7599482 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7599483 {N : Type'} : (term218 N) = (term219 N).
Proof. exact (MK_COMB (@lem7599482) (@lem7599481 N)). Qed.
Lemma lem7599484 {N : Type'} (s : N -> Prop) : (term210 N s) = (term198 N s).
Proof. exact (eq_refl (term210 N s)). Qed.
Lemma lem7599485 {N : Type'} : (term220 N) = (term207 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7599484 N s)). Qed.
Lemma lem7599486 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7599487 {N : Type'} : (term221 N) = (term222 N).
Proof. exact (MK_COMB (@lem7599486 N) (@lem7599485 N)). Qed.
Lemma lem7599488 {N : Type'} : (term205 N) = (term223 N).
Proof. exact (MK_COMB (@lem7599483 N) (@lem7599487 N)). Qed.
Lemma lem7599489 {N : Type'} : ((term204 N) = (term205 N)) = ((term201 N) = (term223 N)).
Proof. exact (MK_COMB (@lem7599477 N) (@lem7599488 N)). Qed.
Lemma lem7599490 {N : Type'} : (term201 N) = (term223 N).
Proof. exact (EQ_MP (@lem7599489 N) (@lem7599467 N)). Qed.
Lemma lem7599595 {N : Type'} : (term104 N) = (term223 N).
Proof. exact (TRANS (@lem7599463 N) (@lem7599490 N)). Qed.
Lemma lem7599596 {N : Type'} : (term106 N) = (term106 N).
Proof. exact (eq_refl (term106 N)). Qed.
Lemma lem7599597 {N : Type'} : (term108 N) = (term224 N).
Proof. exact (MK_COMB (@lem7599596 N) (@lem7599595 N)). Qed.
Lemma lem7599598 {A : Type'} : (term106 A) = (term106 A).
Proof. exact (eq_refl (term106 A)). Qed.
Lemma lem7599599 {A N : Type'} : (term111 A N) = (term225 A N).
Proof. exact (MK_COMB (@lem7599598 A) (@lem7599597 N)). Qed.
Lemma lem7599600 {N : Type'} : (term113 N) = (term113 N).
Proof. exact (eq_refl (term113 N)). Qed.
Lemma lem7599601 {A N : Type'} : (term115 A N) = (term226 A N).
Proof. exact (MK_COMB (@lem7599600 N) (@lem7599599 A N)). Qed.
Lemma lem7599602 {A : Type'} : (term118 A) = (term118 A).
Proof. exact (eq_refl (term118 A)). Qed.
Lemma lem7599603 {A N : Type'} : (term120 A N) = (term227 A N).
Proof. exact (MK_COMB (@lem7599602 A) (@lem7599601 A N)). Qed.
Lemma lem7599604 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7599605 {A N : Type'} : (term135 A N) = (term228 A N).
Proof. exact (MK_COMB (@lem7599604) (@lem7599603 A N)). Qed.
Lemma lem7599619 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term176 A P Q) = (term177 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7599620 (P : nat -> Prop) (Q : nat -> Prop) : (term178 P Q) = (term179 P Q).
Proof. exact (@lem7599619 nat P Q). Qed.
Lemma lem7599621 {N : Type'} (s : N -> Prop) : (term180 N s) = (term181 N s).
Proof. exact (@lem7599620 (term182 N s) (term183 N s)). Qed.
Lemma lem7599622 {N : Type'} (s : N -> Prop) (n : nat) : (term184 N s n) = (term96 N s n).
Proof. exact (eq_refl (term184 N s n)). Qed.
Lemma lem7599623 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7599624 {N : Type'} (s : N -> Prop) (n : nat) : (term185 N s n) = (term98 N s n).
Proof. exact (MK_COMB (@lem7599623) (@lem7599622 N s n)). Qed.
Lemma lem7599625 {N : Type'} (s : N -> Prop) (n : nat) : (term186 N s n) = (term93 N s n).
Proof. exact (eq_refl (term186 N s n)). Qed.
Lemma lem7599626 {N : Type'} (s : N -> Prop) (n : nat) : (term187 N s n) = (term100 N s n).
Proof. exact (MK_COMB (@lem7599624 N s n) (@lem7599625 N s n)). Qed.
Lemma lem7599627 {N : Type'} (s : N -> Prop) : (term188 N s) = (term101 N s).
Proof. exact (fun_ext (fun n : nat => @lem7599626 N s n)). Qed.
Lemma lem7599628 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7599629 {N : Type'} (s : N -> Prop) : (term180 N s) = (term102 N s).
Proof. exact (MK_COMB (@lem7599628) (@lem7599627 N s)). Qed.
Lemma lem7599630 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7599631 {N : Type'} (s : N -> Prop) : (term189 N s) = (term190 N s).
Proof. exact (MK_COMB (@lem7599630) (@lem7599629 N s)). Qed.
Lemma lem7599632 {N : Type'} (s : N -> Prop) (n : nat) : (term184 N s n) = (term96 N s n).
Proof. exact (eq_refl (term184 N s n)). Qed.
Lemma lem7599633 {N : Type'} (s : N -> Prop) : (term191 N s) = (term182 N s).
Proof. exact (fun_ext (fun n : nat => @lem7599632 N s n)). Qed.
Lemma lem7599634 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7599635 {N : Type'} (s : N -> Prop) : (term192 N s) = (term193 N s).
Proof. exact (MK_COMB (@lem7599634) (@lem7599633 N s)). Qed.
Lemma lem7599636 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7599637 {N : Type'} (s : N -> Prop) : (term194 N s) = (term195 N s).
Proof. exact (MK_COMB (@lem7599636) (@lem7599635 N s)). Qed.
Lemma lem7599638 {N : Type'} (s : N -> Prop) (n : nat) : (term186 N s n) = (term93 N s n).
Proof. exact (eq_refl (term186 N s n)). Qed.
Lemma lem7599639 {N : Type'} (s : N -> Prop) : (term196 N s) = (term183 N s).
Proof. exact (fun_ext (fun n : nat => @lem7599638 N s n)). Qed.
Lemma lem7599640 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7599641 {N : Type'} (s : N -> Prop) : (term197 N s) = (term198 N s).
Proof. exact (MK_COMB (@lem7599640) (@lem7599639 N s)). Qed.
Lemma lem7599642 {N : Type'} (s : N -> Prop) : (term181 N s) = (term199 N s).
Proof. exact (MK_COMB (@lem7599637 N s) (@lem7599641 N s)). Qed.
Lemma lem7599643 {N : Type'} (s : N -> Prop) : ((term180 N s) = (term181 N s)) = ((term102 N s) = (term199 N s)).
Proof. exact (MK_COMB (@lem7599631 N s) (@lem7599642 N s)). Qed.
Lemma lem7599644 {N : Type'} (s : N -> Prop) : (term102 N s) = (term199 N s).
Proof. exact (EQ_MP (@lem7599643 N s) (@lem7599621 N s)). Qed.
Lemma lem7599741 {N : Type'} : (term103 N) = (term200 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7599644 N s)). Qed.
Lemma lem7599742 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7599743 {N : Type'} : (term104 N) = (term201 N).
Proof. exact (MK_COMB (@lem7599742 N) (@lem7599741 N)). Qed.
Lemma lem7599745 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term176 A P Q) = (term177 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7599746 {N : Type'} (P : type686 N) (Q : type686 N) : (term202 N P Q) = (term203 N P Q).
Proof. exact (@lem7599745 (N -> Prop) P Q). Qed.
Lemma lem7599747 {N : Type'} : (term204 N) = (term205 N).
Proof. exact (@lem7599746 N (term206 N) (term207 N)). Qed.
Lemma lem7599748 {N : Type'} (s : N -> Prop) : (term208 N s) = (term193 N s).
Proof. exact (eq_refl (term208 N s)). Qed.
Lemma lem7599749 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7599750 {N : Type'} (s : N -> Prop) : (term209 N s) = (term195 N s).
Proof. exact (MK_COMB (@lem7599749) (@lem7599748 N s)). Qed.
Lemma lem7599751 {N : Type'} (s : N -> Prop) : (term210 N s) = (term198 N s).
Proof. exact (eq_refl (term210 N s)). Qed.
Lemma lem7599752 {N : Type'} (s : N -> Prop) : (term211 N s) = (term199 N s).
Proof. exact (MK_COMB (@lem7599750 N s) (@lem7599751 N s)). Qed.
Lemma lem7599753 {N : Type'} : (term212 N) = (term200 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7599752 N s)). Qed.
Lemma lem7599754 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7599755 {N : Type'} : (term204 N) = (term201 N).
Proof. exact (MK_COMB (@lem7599754 N) (@lem7599753 N)). Qed.
Lemma lem7599756 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7599757 {N : Type'} : (term213 N) = (term214 N).
Proof. exact (MK_COMB (@lem7599756) (@lem7599755 N)). Qed.
Lemma lem7599758 {N : Type'} (s : N -> Prop) : (term208 N s) = (term193 N s).
Proof. exact (eq_refl (term208 N s)). Qed.
Lemma lem7599759 {N : Type'} : (term215 N) = (term206 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7599758 N s)). Qed.
Lemma lem7599760 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7599761 {N : Type'} : (term216 N) = (term217 N).
Proof. exact (MK_COMB (@lem7599760 N) (@lem7599759 N)). Qed.
Lemma lem7599762 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7599763 {N : Type'} : (term218 N) = (term219 N).
Proof. exact (MK_COMB (@lem7599762) (@lem7599761 N)). Qed.
Lemma lem7599764 {N : Type'} (s : N -> Prop) : (term210 N s) = (term198 N s).
Proof. exact (eq_refl (term210 N s)). Qed.
Lemma lem7599765 {N : Type'} : (term220 N) = (term207 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7599764 N s)). Qed.
Lemma lem7599766 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7599767 {N : Type'} : (term221 N) = (term222 N).
Proof. exact (MK_COMB (@lem7599766 N) (@lem7599765 N)). Qed.
Lemma lem7599768 {N : Type'} : (term205 N) = (term223 N).
Proof. exact (MK_COMB (@lem7599763 N) (@lem7599767 N)). Qed.
Lemma lem7599769 {N : Type'} : ((term204 N) = (term205 N)) = ((term201 N) = (term223 N)).
Proof. exact (MK_COMB (@lem7599757 N) (@lem7599768 N)). Qed.
Lemma lem7599770 {N : Type'} : (term201 N) = (term223 N).
Proof. exact (EQ_MP (@lem7599769 N) (@lem7599747 N)). Qed.
Lemma lem7599875 {N : Type'} : (term104 N) = (term223 N).
Proof. exact (TRANS (@lem7599743 N) (@lem7599770 N)). Qed.
Lemma lem7599876 {N : Type'} : (term106 N) = (term106 N).
Proof. exact (eq_refl (term106 N)). Qed.
Lemma lem7599877 {N : Type'} : (term108 N) = (term224 N).
Proof. exact (MK_COMB (@lem7599876 N) (@lem7599875 N)). Qed.
Lemma lem7599878 {A : Type'} : (term123 A) = (term123 A).
Proof. exact (eq_refl (term123 A)). Qed.
Lemma lem7599879 {A N : Type'} : (term125 A N) = (term229 A N).
Proof. exact (MK_COMB (@lem7599878 A) (@lem7599877 N)). Qed.
Lemma lem7599880 {N : Type'} : (term113 N) = (term113 N).
Proof. exact (eq_refl (term113 N)). Qed.
Lemma lem7599881 {A N : Type'} : (term128 A N) = (term230 A N).
Proof. exact (MK_COMB (@lem7599880 N) (@lem7599879 A N)). Qed.
Lemma lem7599882 {A : Type'} : (term130 A) = (term130 A).
Proof. exact (eq_refl (term130 A)). Qed.
Lemma lem7599883 {A N : Type'} : (term132 A N) = (term231 A N).
Proof. exact (MK_COMB (@lem7599882 A) (@lem7599881 A N)). Qed.
Lemma lem7599884 {A N : Type'} : (term137 A N) = (term232 A N).
Proof. exact (MK_COMB (@lem7599605 A N) (@lem7599883 A N)). Qed.
Lemma lem7599885 {N : Type'} : (term118 N) = (term118 N).
Proof. exact (eq_refl (term118 N)). Qed.
Lemma lem7599886 {A N : Type'} : (term140 A N) = (term233 A N).
Proof. exact (MK_COMB (@lem7599885 N) (@lem7599884 A N)). Qed.
Lemma lem7599887 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7599888 {A N : Type'} : (term173 A N) = (term234 A N).
Proof. exact (MK_COMB (@lem7599887) (@lem7599886 A N)). Qed.
Lemma lem7599902 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term176 A P Q) = (term177 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7599903 (P : nat -> Prop) (Q : nat -> Prop) : (term178 P Q) = (term179 P Q).
Proof. exact (@lem7599902 nat P Q). Qed.
Lemma lem7599904 {N : Type'} (s : N -> Prop) : (term180 N s) = (term181 N s).
Proof. exact (@lem7599903 (term182 N s) (term183 N s)). Qed.
Lemma lem7599905 {N : Type'} (s : N -> Prop) (n : nat) : (term184 N s n) = (term96 N s n).
Proof. exact (eq_refl (term184 N s n)). Qed.
Lemma lem7599906 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7599907 {N : Type'} (s : N -> Prop) (n : nat) : (term185 N s n) = (term98 N s n).
Proof. exact (MK_COMB (@lem7599906) (@lem7599905 N s n)). Qed.
Lemma lem7599908 {N : Type'} (s : N -> Prop) (n : nat) : (term186 N s n) = (term93 N s n).
Proof. exact (eq_refl (term186 N s n)). Qed.
Lemma lem7599909 {N : Type'} (s : N -> Prop) (n : nat) : (term187 N s n) = (term100 N s n).
Proof. exact (MK_COMB (@lem7599907 N s n) (@lem7599908 N s n)). Qed.
Lemma lem7599910 {N : Type'} (s : N -> Prop) : (term188 N s) = (term101 N s).
Proof. exact (fun_ext (fun n : nat => @lem7599909 N s n)). Qed.
Lemma lem7599911 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7599912 {N : Type'} (s : N -> Prop) : (term180 N s) = (term102 N s).
Proof. exact (MK_COMB (@lem7599911) (@lem7599910 N s)). Qed.
Lemma lem7599913 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7599914 {N : Type'} (s : N -> Prop) : (term189 N s) = (term190 N s).
Proof. exact (MK_COMB (@lem7599913) (@lem7599912 N s)). Qed.
Lemma lem7599915 {N : Type'} (s : N -> Prop) (n : nat) : (term184 N s n) = (term96 N s n).
Proof. exact (eq_refl (term184 N s n)). Qed.
Lemma lem7599916 {N : Type'} (s : N -> Prop) : (term191 N s) = (term182 N s).
Proof. exact (fun_ext (fun n : nat => @lem7599915 N s n)). Qed.
Lemma lem7599917 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7599918 {N : Type'} (s : N -> Prop) : (term192 N s) = (term193 N s).
Proof. exact (MK_COMB (@lem7599917) (@lem7599916 N s)). Qed.
Lemma lem7599919 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7599920 {N : Type'} (s : N -> Prop) : (term194 N s) = (term195 N s).
Proof. exact (MK_COMB (@lem7599919) (@lem7599918 N s)). Qed.
Lemma lem7599921 {N : Type'} (s : N -> Prop) (n : nat) : (term186 N s n) = (term93 N s n).
Proof. exact (eq_refl (term186 N s n)). Qed.
Lemma lem7599922 {N : Type'} (s : N -> Prop) : (term196 N s) = (term183 N s).
Proof. exact (fun_ext (fun n : nat => @lem7599921 N s n)). Qed.
Lemma lem7599923 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7599924 {N : Type'} (s : N -> Prop) : (term197 N s) = (term198 N s).
Proof. exact (MK_COMB (@lem7599923) (@lem7599922 N s)). Qed.
Lemma lem7599925 {N : Type'} (s : N -> Prop) : (term181 N s) = (term199 N s).
Proof. exact (MK_COMB (@lem7599920 N s) (@lem7599924 N s)). Qed.
Lemma lem7599926 {N : Type'} (s : N -> Prop) : ((term180 N s) = (term181 N s)) = ((term102 N s) = (term199 N s)).
Proof. exact (MK_COMB (@lem7599914 N s) (@lem7599925 N s)). Qed.
Lemma lem7599927 {N : Type'} (s : N -> Prop) : (term102 N s) = (term199 N s).
Proof. exact (EQ_MP (@lem7599926 N s) (@lem7599904 N s)). Qed.
Lemma lem7600024 {N : Type'} : (term103 N) = (term200 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7599927 N s)). Qed.
Lemma lem7600025 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7600026 {N : Type'} : (term104 N) = (term201 N).
Proof. exact (MK_COMB (@lem7600025 N) (@lem7600024 N)). Qed.
Lemma lem7600028 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term176 A P Q) = (term177 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7600029 {N : Type'} (P : type686 N) (Q : type686 N) : (term202 N P Q) = (term203 N P Q).
Proof. exact (@lem7600028 (N -> Prop) P Q). Qed.
Lemma lem7600030 {N : Type'} : (term204 N) = (term205 N).
Proof. exact (@lem7600029 N (term206 N) (term207 N)). Qed.
Lemma lem7600031 {N : Type'} (s : N -> Prop) : (term208 N s) = (term193 N s).
Proof. exact (eq_refl (term208 N s)). Qed.
Lemma lem7600032 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7600033 {N : Type'} (s : N -> Prop) : (term209 N s) = (term195 N s).
Proof. exact (MK_COMB (@lem7600032) (@lem7600031 N s)). Qed.
Lemma lem7600034 {N : Type'} (s : N -> Prop) : (term210 N s) = (term198 N s).
Proof. exact (eq_refl (term210 N s)). Qed.
Lemma lem7600035 {N : Type'} (s : N -> Prop) : (term211 N s) = (term199 N s).
Proof. exact (MK_COMB (@lem7600033 N s) (@lem7600034 N s)). Qed.
Lemma lem7600036 {N : Type'} : (term212 N) = (term200 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7600035 N s)). Qed.
Lemma lem7600037 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7600038 {N : Type'} : (term204 N) = (term201 N).
Proof. exact (MK_COMB (@lem7600037 N) (@lem7600036 N)). Qed.
Lemma lem7600039 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7600040 {N : Type'} : (term213 N) = (term214 N).
Proof. exact (MK_COMB (@lem7600039) (@lem7600038 N)). Qed.
Lemma lem7600041 {N : Type'} (s : N -> Prop) : (term208 N s) = (term193 N s).
Proof. exact (eq_refl (term208 N s)). Qed.
Lemma lem7600042 {N : Type'} : (term215 N) = (term206 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7600041 N s)). Qed.
Lemma lem7600043 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7600044 {N : Type'} : (term216 N) = (term217 N).
Proof. exact (MK_COMB (@lem7600043 N) (@lem7600042 N)). Qed.
Lemma lem7600045 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7600046 {N : Type'} : (term218 N) = (term219 N).
Proof. exact (MK_COMB (@lem7600045) (@lem7600044 N)). Qed.
Lemma lem7600047 {N : Type'} (s : N -> Prop) : (term210 N s) = (term198 N s).
Proof. exact (eq_refl (term210 N s)). Qed.
Lemma lem7600048 {N : Type'} : (term220 N) = (term207 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7600047 N s)). Qed.
Lemma lem7600049 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7600050 {N : Type'} : (term221 N) = (term222 N).
Proof. exact (MK_COMB (@lem7600049 N) (@lem7600048 N)). Qed.
Lemma lem7600051 {N : Type'} : (term205 N) = (term223 N).
Proof. exact (MK_COMB (@lem7600046 N) (@lem7600050 N)). Qed.
Lemma lem7600052 {N : Type'} : ((term204 N) = (term205 N)) = ((term201 N) = (term223 N)).
Proof. exact (MK_COMB (@lem7600040 N) (@lem7600051 N)). Qed.
Lemma lem7600053 {N : Type'} : (term201 N) = (term223 N).
Proof. exact (EQ_MP (@lem7600052 N) (@lem7600030 N)). Qed.
Lemma lem7600158 {N : Type'} : (term104 N) = (term223 N).
Proof. exact (TRANS (@lem7600026 N) (@lem7600053 N)). Qed.
Lemma lem7600159 {N : Type'} : (term123 N) = (term123 N).
Proof. exact (eq_refl (term123 N)). Qed.
Lemma lem7600160 {N : Type'} : (term143 N) = (term235 N).
Proof. exact (MK_COMB (@lem7600159 N) (@lem7600158 N)). Qed.
Lemma lem7600161 {A : Type'} : (term106 A) = (term106 A).
Proof. exact (eq_refl (term106 A)). Qed.
Lemma lem7600162 {A N : Type'} : (term146 A N) = (term236 A N).
Proof. exact (MK_COMB (@lem7600161 A) (@lem7600160 N)). Qed.
Lemma lem7600163 {N : Type'} : (term148 N) = (term148 N).
Proof. exact (eq_refl (term148 N)). Qed.
Lemma lem7600164 {A N : Type'} : (term150 A N) = (term237 A N).
Proof. exact (MK_COMB (@lem7600163 N) (@lem7600162 A N)). Qed.
Lemma lem7600165 {A : Type'} : (term118 A) = (term118 A).
Proof. exact (eq_refl (term118 A)). Qed.
Lemma lem7600166 {A N : Type'} : (term153 A N) = (term238 A N).
Proof. exact (MK_COMB (@lem7600165 A) (@lem7600164 A N)). Qed.
Lemma lem7600167 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7600168 {A N : Type'} : (term165 A N) = (term239 A N).
Proof. exact (MK_COMB (@lem7600167) (@lem7600166 A N)). Qed.
Lemma lem7600182 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term176 A P Q) = (term177 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7600183 (P : nat -> Prop) (Q : nat -> Prop) : (term178 P Q) = (term179 P Q).
Proof. exact (@lem7600182 nat P Q). Qed.
Lemma lem7600184 {N : Type'} (s : N -> Prop) : (term180 N s) = (term181 N s).
Proof. exact (@lem7600183 (term182 N s) (term183 N s)). Qed.
Lemma lem7600185 {N : Type'} (s : N -> Prop) (n : nat) : (term184 N s n) = (term96 N s n).
Proof. exact (eq_refl (term184 N s n)). Qed.
Lemma lem7600186 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7600187 {N : Type'} (s : N -> Prop) (n : nat) : (term185 N s n) = (term98 N s n).
Proof. exact (MK_COMB (@lem7600186) (@lem7600185 N s n)). Qed.
Lemma lem7600188 {N : Type'} (s : N -> Prop) (n : nat) : (term186 N s n) = (term93 N s n).
Proof. exact (eq_refl (term186 N s n)). Qed.
Lemma lem7600189 {N : Type'} (s : N -> Prop) (n : nat) : (term187 N s n) = (term100 N s n).
Proof. exact (MK_COMB (@lem7600187 N s n) (@lem7600188 N s n)). Qed.
Lemma lem7600190 {N : Type'} (s : N -> Prop) : (term188 N s) = (term101 N s).
Proof. exact (fun_ext (fun n : nat => @lem7600189 N s n)). Qed.
Lemma lem7600191 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7600192 {N : Type'} (s : N -> Prop) : (term180 N s) = (term102 N s).
Proof. exact (MK_COMB (@lem7600191) (@lem7600190 N s)). Qed.
Lemma lem7600193 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7600194 {N : Type'} (s : N -> Prop) : (term189 N s) = (term190 N s).
Proof. exact (MK_COMB (@lem7600193) (@lem7600192 N s)). Qed.
Lemma lem7600195 {N : Type'} (s : N -> Prop) (n : nat) : (term184 N s n) = (term96 N s n).
Proof. exact (eq_refl (term184 N s n)). Qed.
Lemma lem7600196 {N : Type'} (s : N -> Prop) : (term191 N s) = (term182 N s).
Proof. exact (fun_ext (fun n : nat => @lem7600195 N s n)). Qed.
Lemma lem7600197 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7600198 {N : Type'} (s : N -> Prop) : (term192 N s) = (term193 N s).
Proof. exact (MK_COMB (@lem7600197) (@lem7600196 N s)). Qed.
Lemma lem7600199 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7600200 {N : Type'} (s : N -> Prop) : (term194 N s) = (term195 N s).
Proof. exact (MK_COMB (@lem7600199) (@lem7600198 N s)). Qed.
Lemma lem7600201 {N : Type'} (s : N -> Prop) (n : nat) : (term186 N s n) = (term93 N s n).
Proof. exact (eq_refl (term186 N s n)). Qed.
Lemma lem7600202 {N : Type'} (s : N -> Prop) : (term196 N s) = (term183 N s).
Proof. exact (fun_ext (fun n : nat => @lem7600201 N s n)). Qed.
Lemma lem7600203 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7600204 {N : Type'} (s : N -> Prop) : (term197 N s) = (term198 N s).
Proof. exact (MK_COMB (@lem7600203) (@lem7600202 N s)). Qed.
Lemma lem7600205 {N : Type'} (s : N -> Prop) : (term181 N s) = (term199 N s).
Proof. exact (MK_COMB (@lem7600200 N s) (@lem7600204 N s)). Qed.
Lemma lem7600206 {N : Type'} (s : N -> Prop) : ((term180 N s) = (term181 N s)) = ((term102 N s) = (term199 N s)).
Proof. exact (MK_COMB (@lem7600194 N s) (@lem7600205 N s)). Qed.
Lemma lem7600207 {N : Type'} (s : N -> Prop) : (term102 N s) = (term199 N s).
Proof. exact (EQ_MP (@lem7600206 N s) (@lem7600184 N s)). Qed.
Lemma lem7600304 {N : Type'} : (term103 N) = (term200 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7600207 N s)). Qed.
Lemma lem7600305 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7600306 {N : Type'} : (term104 N) = (term201 N).
Proof. exact (MK_COMB (@lem7600305 N) (@lem7600304 N)). Qed.
Lemma lem7600308 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term176 A P Q) = (term177 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7600309 {N : Type'} (P : type686 N) (Q : type686 N) : (term202 N P Q) = (term203 N P Q).
Proof. exact (@lem7600308 (N -> Prop) P Q). Qed.
Lemma lem7600310 {N : Type'} : (term204 N) = (term205 N).
Proof. exact (@lem7600309 N (term206 N) (term207 N)). Qed.
Lemma lem7600311 {N : Type'} (s : N -> Prop) : (term208 N s) = (term193 N s).
Proof. exact (eq_refl (term208 N s)). Qed.
Lemma lem7600312 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7600313 {N : Type'} (s : N -> Prop) : (term209 N s) = (term195 N s).
Proof. exact (MK_COMB (@lem7600312) (@lem7600311 N s)). Qed.
Lemma lem7600314 {N : Type'} (s : N -> Prop) : (term210 N s) = (term198 N s).
Proof. exact (eq_refl (term210 N s)). Qed.
Lemma lem7600315 {N : Type'} (s : N -> Prop) : (term211 N s) = (term199 N s).
Proof. exact (MK_COMB (@lem7600313 N s) (@lem7600314 N s)). Qed.
Lemma lem7600316 {N : Type'} : (term212 N) = (term200 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7600315 N s)). Qed.
Lemma lem7600317 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7600318 {N : Type'} : (term204 N) = (term201 N).
Proof. exact (MK_COMB (@lem7600317 N) (@lem7600316 N)). Qed.
Lemma lem7600319 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7600320 {N : Type'} : (term213 N) = (term214 N).
Proof. exact (MK_COMB (@lem7600319) (@lem7600318 N)). Qed.
Lemma lem7600321 {N : Type'} (s : N -> Prop) : (term208 N s) = (term193 N s).
Proof. exact (eq_refl (term208 N s)). Qed.
Lemma lem7600322 {N : Type'} : (term215 N) = (term206 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7600321 N s)). Qed.
Lemma lem7600323 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7600324 {N : Type'} : (term216 N) = (term217 N).
Proof. exact (MK_COMB (@lem7600323 N) (@lem7600322 N)). Qed.
Lemma lem7600325 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7600326 {N : Type'} : (term218 N) = (term219 N).
Proof. exact (MK_COMB (@lem7600325) (@lem7600324 N)). Qed.
Lemma lem7600327 {N : Type'} (s : N -> Prop) : (term210 N s) = (term198 N s).
Proof. exact (eq_refl (term210 N s)). Qed.
Lemma lem7600328 {N : Type'} : (term220 N) = (term207 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7600327 N s)). Qed.
Lemma lem7600329 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7600330 {N : Type'} : (term221 N) = (term222 N).
Proof. exact (MK_COMB (@lem7600329 N) (@lem7600328 N)). Qed.
Lemma lem7600331 {N : Type'} : (term205 N) = (term223 N).
Proof. exact (MK_COMB (@lem7600326 N) (@lem7600330 N)). Qed.
Lemma lem7600332 {N : Type'} : ((term204 N) = (term205 N)) = ((term201 N) = (term223 N)).
Proof. exact (MK_COMB (@lem7600320 N) (@lem7600331 N)). Qed.
Lemma lem7600333 {N : Type'} : (term201 N) = (term223 N).
Proof. exact (EQ_MP (@lem7600332 N) (@lem7600310 N)). Qed.
Lemma lem7600438 {N : Type'} : (term104 N) = (term223 N).
Proof. exact (TRANS (@lem7600306 N) (@lem7600333 N)). Qed.
Lemma lem7600439 {N : Type'} : (term123 N) = (term123 N).
Proof. exact (eq_refl (term123 N)). Qed.
Lemma lem7600440 {N : Type'} : (term143 N) = (term235 N).
Proof. exact (MK_COMB (@lem7600439 N) (@lem7600438 N)). Qed.
Lemma lem7600441 {A : Type'} : (term123 A) = (term123 A).
Proof. exact (eq_refl (term123 A)). Qed.
Lemma lem7600442 {A N : Type'} : (term156 A N) = (term240 A N).
Proof. exact (MK_COMB (@lem7600441 A) (@lem7600440 N)). Qed.
Lemma lem7600443 {N : Type'} : (term148 N) = (term148 N).
Proof. exact (eq_refl (term148 N)). Qed.
Lemma lem7600444 {A N : Type'} : (term159 A N) = (term241 A N).
Proof. exact (MK_COMB (@lem7600443 N) (@lem7600442 A N)). Qed.
Lemma lem7600445 {A : Type'} : (term130 A) = (term130 A).
Proof. exact (eq_refl (term130 A)). Qed.
Lemma lem7600446 {A N : Type'} : (term162 A N) = (term242 A N).
Proof. exact (MK_COMB (@lem7600445 A) (@lem7600444 A N)). Qed.
Lemma lem7600447 {A N : Type'} : (term167 A N) = (term243 A N).
Proof. exact (MK_COMB (@lem7600168 A N) (@lem7600446 A N)). Qed.
Lemma lem7600448 {N : Type'} : (term130 N) = (term130 N).
Proof. exact (eq_refl (term130 N)). Qed.
Lemma lem7600449 {A N : Type'} : (term170 A N) = (term244 A N).
Proof. exact (MK_COMB (@lem7600448 N) (@lem7600447 A N)). Qed.
Lemma lem7600452 {A N : Type'} : (term175 A N) = (term245 A N).
Proof. exact (MK_COMB (@lem7599888 A N) (@lem7600449 A N)). Qed.
Lemma lem7600453 {A N : Type'} : (term89 A N) = (term245 A N).
Proof. exact (TRANS (@lem7599325 A N) (@lem7600452 A N)). Qed.
Lemma lem7600454 {A N : Type'} (h1 : term89 A N) : term245 A N.
Proof. exact (EQ_MP (@lem7600453 A N) (@lem7599040 A N h1)). Qed.
Lemma lem7600477 {N : Type'} (s : N -> Prop) (n : nat) : (term93 N s n) = (term93 N s n).
Proof. exact (eq_refl (term93 N s n)). Qed.
Lemma lem7600478 {N : Type'} (s : N -> Prop) : (term183 N s) = (term183 N s).
Proof. exact (fun_ext (fun n : nat => @lem7600477 N s n)). Qed.
Lemma lem7600479 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7600480 {N : Type'} (s : N -> Prop) : (term198 N s) = (term198 N s).
Proof. exact (MK_COMB (@lem7600479) (@lem7600478 N s)). Qed.
Lemma lem7600481 {N : Type'} : (term207 N) = (term207 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7600480 N s)). Qed.
Lemma lem7600482 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7600483 {N : Type'} : (term222 N) = (term222 N).
Proof. exact (MK_COMB (@lem7600482 N) (@lem7600481 N)). Qed.
Lemma lem7600508 {N : Type'} (s : N -> Prop) (n : nat) : (term96 N s n) = (term96 N s n).
Proof. exact (eq_refl (term96 N s n)). Qed.
Lemma lem7600509 {N : Type'} (s : N -> Prop) : (term182 N s) = (term182 N s).
Proof. exact (fun_ext (fun n : nat => @lem7600508 N s n)). Qed.
Lemma lem7600510 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7600511 {N : Type'} (s : N -> Prop) : (term193 N s) = (term193 N s).
Proof. exact (MK_COMB (@lem7600510) (@lem7600509 N s)). Qed.
Lemma lem7600512 {N : Type'} : (term206 N) = (term206 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7600511 N s)). Qed.
Lemma lem7600513 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7600514 {N : Type'} : (term217 N) = (term217 N).
Proof. exact (MK_COMB (@lem7600513 N) (@lem7600512 N)). Qed.
Lemma lem7600515 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7600516 {N : Type'} : (term219 N) = (term219 N).
Proof. exact (MK_COMB (@lem7600515) (@lem7600514 N)). Qed.
Lemma lem7600517 {N : Type'} : (term223 N) = (term223 N).
Proof. exact (MK_COMB (@lem7600516 N) (@lem7600483 N)). Qed.
Lemma lem7600528 {N : Type'} (s : N -> Prop) : ((@dimindex N s) = term22) = ((@dimindex N s) = term22).
Proof. exact (eq_refl ((@dimindex N s) = term22)). Qed.
Lemma lem7600529 {N : Type'} : (term27 N) = (term27 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7600528 N s)). Qed.
Lemma lem7600530 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7600531 {N : Type'} : (term28 N) = (term28 N).
Proof. exact (MK_COMB (@lem7600530 N) (@lem7600529 N)). Qed.
Lemma lem7600532 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7600533 {N : Type'} : (term123 N) = (term123 N).
Proof. exact (MK_COMB (@lem7600532) (@lem7600531 N)). Qed.
Lemma lem7600534 {N : Type'} : (term235 N) = (term235 N).
Proof. exact (MK_COMB (@lem7600533 N) (@lem7600517 N)). Qed.
Lemma lem7600545 {A : Type'} (s : A -> Prop) : ((@dimindex A s) = term22) = ((@dimindex A s) = term22).
Proof. exact (eq_refl ((@dimindex A s) = term22)). Qed.
Lemma lem7600546 {A : Type'} : (term27 A) = (term27 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7600545 A s)). Qed.
Lemma lem7600547 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7600548 {A : Type'} : (term28 A) = (term28 A).
Proof. exact (MK_COMB (@lem7600547 A) (@lem7600546 A)). Qed.
Lemma lem7600549 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7600550 {A : Type'} : (term123 A) = (term123 A).
Proof. exact (MK_COMB (@lem7600549) (@lem7600548 A)). Qed.
Lemma lem7600551 {A N : Type'} : (term240 A N) = (term240 A N).
Proof. exact (MK_COMB (@lem7600550 A) (@lem7600534 N)). Qed.
Lemma lem7600560 {N : Type'} : (term148 N) = (term148 N).
Proof. exact (eq_refl (term148 N)). Qed.
Lemma lem7600561 {A N : Type'} : (term241 A N) = (term241 A N).
Proof. exact (MK_COMB (@lem7600560 N) (@lem7600551 A N)). Qed.
Lemma lem7600568 {A : Type'} : (term130 A) = (term130 A).
Proof. exact (eq_refl (term130 A)). Qed.
Lemma lem7600569 {A N : Type'} : (term242 A N) = (term242 A N).
Proof. exact (MK_COMB (@lem7600568 A) (@lem7600561 A N)). Qed.
Lemma lem7600592 {N : Type'} (s : N -> Prop) (n : nat) : (term93 N s n) = (term93 N s n).
Proof. exact (eq_refl (term93 N s n)). Qed.
Lemma lem7600593 {N : Type'} (s : N -> Prop) : (term183 N s) = (term183 N s).
Proof. exact (fun_ext (fun n : nat => @lem7600592 N s n)). Qed.
Lemma lem7600594 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7600595 {N : Type'} (s : N -> Prop) : (term198 N s) = (term198 N s).
Proof. exact (MK_COMB (@lem7600594) (@lem7600593 N s)). Qed.
Lemma lem7600596 {N : Type'} : (term207 N) = (term207 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7600595 N s)). Qed.
Lemma lem7600597 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7600598 {N : Type'} : (term222 N) = (term222 N).
Proof. exact (MK_COMB (@lem7600597 N) (@lem7600596 N)). Qed.
Lemma lem7600623 {N : Type'} (s : N -> Prop) (n : nat) : (term96 N s n) = (term96 N s n).
Proof. exact (eq_refl (term96 N s n)). Qed.
Lemma lem7600624 {N : Type'} (s : N -> Prop) : (term182 N s) = (term182 N s).
Proof. exact (fun_ext (fun n : nat => @lem7600623 N s n)). Qed.
Lemma lem7600625 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7600626 {N : Type'} (s : N -> Prop) : (term193 N s) = (term193 N s).
Proof. exact (MK_COMB (@lem7600625) (@lem7600624 N s)). Qed.
Lemma lem7600627 {N : Type'} : (term206 N) = (term206 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7600626 N s)). Qed.
Lemma lem7600628 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7600629 {N : Type'} : (term217 N) = (term217 N).
Proof. exact (MK_COMB (@lem7600628 N) (@lem7600627 N)). Qed.
Lemma lem7600630 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7600631 {N : Type'} : (term219 N) = (term219 N).
Proof. exact (MK_COMB (@lem7600630) (@lem7600629 N)). Qed.
Lemma lem7600632 {N : Type'} : (term223 N) = (term223 N).
Proof. exact (MK_COMB (@lem7600631 N) (@lem7600598 N)). Qed.
Lemma lem7600643 {N : Type'} (s : N -> Prop) : ((@dimindex N s) = term22) = ((@dimindex N s) = term22).
Proof. exact (eq_refl ((@dimindex N s) = term22)). Qed.
Lemma lem7600644 {N : Type'} : (term27 N) = (term27 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7600643 N s)). Qed.
Lemma lem7600645 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7600646 {N : Type'} : (term28 N) = (term28 N).
Proof. exact (MK_COMB (@lem7600645 N) (@lem7600644 N)). Qed.
Lemma lem7600647 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7600648 {N : Type'} : (term123 N) = (term123 N).
Proof. exact (MK_COMB (@lem7600647) (@lem7600646 N)). Qed.
Lemma lem7600649 {N : Type'} : (term235 N) = (term235 N).
Proof. exact (MK_COMB (@lem7600648 N) (@lem7600632 N)). Qed.
Lemma lem7600658 {A : Type'} (s : A -> Prop) : ((@dimindex A s) = (@CARD A (@UNIV A))) = ((@dimindex A s) = (@CARD A (@UNIV A))).
Proof. exact (eq_refl ((@dimindex A s) = (@CARD A (@UNIV A)))). Qed.
Lemma lem7600659 {A : Type'} : (term35 A) = (term35 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7600658 A s)). Qed.
Lemma lem7600660 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7600661 {A : Type'} : (term36 A) = (term36 A).
Proof. exact (MK_COMB (@lem7600660 A) (@lem7600659 A)). Qed.
Lemma lem7600662 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7600663 {A : Type'} : (term106 A) = (term106 A).
Proof. exact (MK_COMB (@lem7600662) (@lem7600661 A)). Qed.
Lemma lem7600664 {A N : Type'} : (term236 A N) = (term236 A N).
Proof. exact (MK_COMB (@lem7600663 A) (@lem7600649 N)). Qed.
Lemma lem7600673 {N : Type'} : (term148 N) = (term148 N).
Proof. exact (eq_refl (term148 N)). Qed.
Lemma lem7600674 {A N : Type'} : (term237 A N) = (term237 A N).
Proof. exact (MK_COMB (@lem7600673 N) (@lem7600664 A N)). Qed.
Lemma lem7600679 {A : Type'} : (term118 A) = (term118 A).
Proof. exact (eq_refl (term118 A)). Qed.
Lemma lem7600680 {A N : Type'} : (term238 A N) = (term238 A N).
Proof. exact (MK_COMB (@lem7600679 A) (@lem7600674 A N)). Qed.
Lemma lem7600681 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7600682 {A N : Type'} : (term239 A N) = (term239 A N).
Proof. exact (MK_COMB (@lem7600681) (@lem7600680 A N)). Qed.
Lemma lem7600683 {A N : Type'} : (term243 A N) = (term243 A N).
Proof. exact (MK_COMB (@lem7600682 A N) (@lem7600569 A N)). Qed.
Lemma lem7600690 {N : Type'} : (term130 N) = (term130 N).
Proof. exact (eq_refl (term130 N)). Qed.
Lemma lem7600691 {A N : Type'} : (term244 A N) = (term244 A N).
Proof. exact (MK_COMB (@lem7600690 N) (@lem7600683 A N)). Qed.
Lemma lem7600714 {N : Type'} (s : N -> Prop) (n : nat) : (term93 N s n) = (term93 N s n).
Proof. exact (eq_refl (term93 N s n)). Qed.
Lemma lem7600715 {N : Type'} (s : N -> Prop) : (term183 N s) = (term183 N s).
Proof. exact (fun_ext (fun n : nat => @lem7600714 N s n)). Qed.
Lemma lem7600716 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7600717 {N : Type'} (s : N -> Prop) : (term198 N s) = (term198 N s).
Proof. exact (MK_COMB (@lem7600716) (@lem7600715 N s)). Qed.
Lemma lem7600718 {N : Type'} : (term207 N) = (term207 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7600717 N s)). Qed.
Lemma lem7600719 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7600720 {N : Type'} : (term222 N) = (term222 N).
Proof. exact (MK_COMB (@lem7600719 N) (@lem7600718 N)). Qed.
Lemma lem7600745 {N : Type'} (s : N -> Prop) (n : nat) : (term96 N s n) = (term96 N s n).
Proof. exact (eq_refl (term96 N s n)). Qed.
Lemma lem7600746 {N : Type'} (s : N -> Prop) : (term182 N s) = (term182 N s).
Proof. exact (fun_ext (fun n : nat => @lem7600745 N s n)). Qed.
Lemma lem7600747 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7600748 {N : Type'} (s : N -> Prop) : (term193 N s) = (term193 N s).
Proof. exact (MK_COMB (@lem7600747) (@lem7600746 N s)). Qed.
Lemma lem7600749 {N : Type'} : (term206 N) = (term206 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7600748 N s)). Qed.
Lemma lem7600750 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7600751 {N : Type'} : (term217 N) = (term217 N).
Proof. exact (MK_COMB (@lem7600750 N) (@lem7600749 N)). Qed.
Lemma lem7600752 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7600753 {N : Type'} : (term219 N) = (term219 N).
Proof. exact (MK_COMB (@lem7600752) (@lem7600751 N)). Qed.
Lemma lem7600754 {N : Type'} : (term223 N) = (term223 N).
Proof. exact (MK_COMB (@lem7600753 N) (@lem7600720 N)). Qed.
Lemma lem7600763 {N : Type'} (s : N -> Prop) : ((@dimindex N s) = (@CARD N (@UNIV N))) = ((@dimindex N s) = (@CARD N (@UNIV N))).
Proof. exact (eq_refl ((@dimindex N s) = (@CARD N (@UNIV N)))). Qed.
Lemma lem7600764 {N : Type'} : (term35 N) = (term35 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7600763 N s)). Qed.
Lemma lem7600765 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7600766 {N : Type'} : (term36 N) = (term36 N).
Proof. exact (MK_COMB (@lem7600765 N) (@lem7600764 N)). Qed.
Lemma lem7600767 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7600768 {N : Type'} : (term106 N) = (term106 N).
Proof. exact (MK_COMB (@lem7600767) (@lem7600766 N)). Qed.
Lemma lem7600769 {N : Type'} : (term224 N) = (term224 N).
Proof. exact (MK_COMB (@lem7600768 N) (@lem7600754 N)). Qed.
Lemma lem7600780 {A : Type'} (s : A -> Prop) : ((@dimindex A s) = term22) = ((@dimindex A s) = term22).
Proof. exact (eq_refl ((@dimindex A s) = term22)). Qed.
Lemma lem7600781 {A : Type'} : (term27 A) = (term27 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7600780 A s)). Qed.
Lemma lem7600782 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7600783 {A : Type'} : (term28 A) = (term28 A).
Proof. exact (MK_COMB (@lem7600782 A) (@lem7600781 A)). Qed.
Lemma lem7600784 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7600785 {A : Type'} : (term123 A) = (term123 A).
Proof. exact (MK_COMB (@lem7600784) (@lem7600783 A)). Qed.
Lemma lem7600786 {A N : Type'} : (term229 A N) = (term229 A N).
Proof. exact (MK_COMB (@lem7600785 A) (@lem7600769 N)). Qed.
Lemma lem7600797 {N : Type'} : (term113 N) = (term113 N).
Proof. exact (eq_refl (term113 N)). Qed.
Lemma lem7600798 {A N : Type'} : (term230 A N) = (term230 A N).
Proof. exact (MK_COMB (@lem7600797 N) (@lem7600786 A N)). Qed.
Lemma lem7600805 {A : Type'} : (term130 A) = (term130 A).
Proof. exact (eq_refl (term130 A)). Qed.
Lemma lem7600806 {A N : Type'} : (term231 A N) = (term231 A N).
Proof. exact (MK_COMB (@lem7600805 A) (@lem7600798 A N)). Qed.
Lemma lem7600829 {N : Type'} (s : N -> Prop) (n : nat) : (term93 N s n) = (term93 N s n).
Proof. exact (eq_refl (term93 N s n)). Qed.
Lemma lem7600830 {N : Type'} (s : N -> Prop) : (term183 N s) = (term183 N s).
Proof. exact (fun_ext (fun n : nat => @lem7600829 N s n)). Qed.
Lemma lem7600831 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7600832 {N : Type'} (s : N -> Prop) : (term198 N s) = (term198 N s).
Proof. exact (MK_COMB (@lem7600831) (@lem7600830 N s)). Qed.
Lemma lem7600833 {N : Type'} : (term207 N) = (term207 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7600832 N s)). Qed.
Lemma lem7600834 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7600835 {N : Type'} : (term222 N) = (term222 N).
Proof. exact (MK_COMB (@lem7600834 N) (@lem7600833 N)). Qed.
Lemma lem7600860 {N : Type'} (s : N -> Prop) (n : nat) : (term96 N s n) = (term96 N s n).
Proof. exact (eq_refl (term96 N s n)). Qed.
Lemma lem7600861 {N : Type'} (s : N -> Prop) : (term182 N s) = (term182 N s).
Proof. exact (fun_ext (fun n : nat => @lem7600860 N s n)). Qed.
Lemma lem7600862 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7600863 {N : Type'} (s : N -> Prop) : (term193 N s) = (term193 N s).
Proof. exact (MK_COMB (@lem7600862) (@lem7600861 N s)). Qed.
Lemma lem7600864 {N : Type'} : (term206 N) = (term206 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7600863 N s)). Qed.
Lemma lem7600865 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7600866 {N : Type'} : (term217 N) = (term217 N).
Proof. exact (MK_COMB (@lem7600865 N) (@lem7600864 N)). Qed.
Lemma lem7600867 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7600868 {N : Type'} : (term219 N) = (term219 N).
Proof. exact (MK_COMB (@lem7600867) (@lem7600866 N)). Qed.
Lemma lem7600869 {N : Type'} : (term223 N) = (term223 N).
Proof. exact (MK_COMB (@lem7600868 N) (@lem7600835 N)). Qed.
Lemma lem7600878 {N : Type'} (s : N -> Prop) : ((@dimindex N s) = (@CARD N (@UNIV N))) = ((@dimindex N s) = (@CARD N (@UNIV N))).
Proof. exact (eq_refl ((@dimindex N s) = (@CARD N (@UNIV N)))). Qed.
Lemma lem7600879 {N : Type'} : (term35 N) = (term35 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7600878 N s)). Qed.
Lemma lem7600880 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7600881 {N : Type'} : (term36 N) = (term36 N).
Proof. exact (MK_COMB (@lem7600880 N) (@lem7600879 N)). Qed.
Lemma lem7600882 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7600883 {N : Type'} : (term106 N) = (term106 N).
Proof. exact (MK_COMB (@lem7600882) (@lem7600881 N)). Qed.
Lemma lem7600884 {N : Type'} : (term224 N) = (term224 N).
Proof. exact (MK_COMB (@lem7600883 N) (@lem7600869 N)). Qed.
Lemma lem7600893 {A : Type'} (s : A -> Prop) : ((@dimindex A s) = (@CARD A (@UNIV A))) = ((@dimindex A s) = (@CARD A (@UNIV A))).
Proof. exact (eq_refl ((@dimindex A s) = (@CARD A (@UNIV A)))). Qed.
Lemma lem7600894 {A : Type'} : (term35 A) = (term35 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7600893 A s)). Qed.
Lemma lem7600895 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7600896 {A : Type'} : (term36 A) = (term36 A).
Proof. exact (MK_COMB (@lem7600895 A) (@lem7600894 A)). Qed.
Lemma lem7600897 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7600898 {A : Type'} : (term106 A) = (term106 A).
Proof. exact (MK_COMB (@lem7600897) (@lem7600896 A)). Qed.
Lemma lem7600899 {A N : Type'} : (term225 A N) = (term225 A N).
Proof. exact (MK_COMB (@lem7600898 A) (@lem7600884 N)). Qed.
Lemma lem7600910 {N : Type'} : (term113 N) = (term113 N).
Proof. exact (eq_refl (term113 N)). Qed.
Lemma lem7600911 {A N : Type'} : (term226 A N) = (term226 A N).
Proof. exact (MK_COMB (@lem7600910 N) (@lem7600899 A N)). Qed.
Lemma lem7600916 {A : Type'} : (term118 A) = (term118 A).
Proof. exact (eq_refl (term118 A)). Qed.
Lemma lem7600917 {A N : Type'} : (term227 A N) = (term227 A N).
Proof. exact (MK_COMB (@lem7600916 A) (@lem7600911 A N)). Qed.
Lemma lem7600918 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7600919 {A N : Type'} : (term228 A N) = (term228 A N).
Proof. exact (MK_COMB (@lem7600918) (@lem7600917 A N)). Qed.
Lemma lem7600920 {A N : Type'} : (term232 A N) = (term232 A N).
Proof. exact (MK_COMB (@lem7600919 A N) (@lem7600806 A N)). Qed.
Lemma lem7600925 {N : Type'} : (term118 N) = (term118 N).
Proof. exact (eq_refl (term118 N)). Qed.
Lemma lem7600926 {A N : Type'} : (term233 A N) = (term233 A N).
Proof. exact (MK_COMB (@lem7600925 N) (@lem7600920 A N)). Qed.
Lemma lem7600927 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7600928 {A N : Type'} : (term234 A N) = (term234 A N).
Proof. exact (MK_COMB (@lem7600927) (@lem7600926 A N)). Qed.
Lemma lem7600929 {A N : Type'} : (term245 A N) = (term245 A N).
Proof. exact (MK_COMB (@lem7600928 A N) (@lem7600691 A N)). Qed.
Lemma lem7600930 {A N : Type'} (h1 : term89 A N) : term245 A N.
Proof. exact (EQ_MP (@lem7600929 A N) (@lem7600454 A N h1)). Qed.
Lemma lem7600931 {A N : Type'} (h1 : term233 A N) : term233 A N.
Proof. exact (h1). Qed.
Lemma lem7600932 {A N : Type'} (h1 : term244 A N) : term244 A N.
Proof. exact (h1). Qed.
Lemma lem7600933 {A N : Type'} (h1 : term233 A N) : term232 A N.
Proof. exact (proj2 (@lem7600931 A N h1)). Qed.
Lemma lem7600935 {A N : Type'} (h1 : term227 A N) : term227 A N.
Proof. exact (h1). Qed.
Lemma lem7600936 {A N : Type'} (h1 : term231 A N) : term231 A N.
Proof. exact (h1). Qed.
Lemma lem7600937 {A N : Type'} (h1 : term227 A N) : term226 A N.
Proof. exact (proj2 (@lem7600935 A N h1)). Qed.
Lemma lem7600939 {A N : Type'} (h1 : term227 A N) : term225 A N.
Proof. exact (proj2 (@lem7600937 A N h1)). Qed.
Lemma lem7600941 {A N : Type'} (h1 : term227 A N) : term224 N.
Proof. exact (proj2 (@lem7600939 A N h1)). Qed.
Lemma lem7600943 {A N : Type'} (h1 : term227 A N) : term223 N.
Proof. exact (proj2 (@lem7600941 A N h1)). Qed.
Lemma lem7600944 {A N : Type'} (h1 : term227 A N) : term36 N.
Proof. exact (proj1 (@lem7600941 A N h1)). Qed.
Lemma lem7600946 {A N : Type'} (h1 : term227 A N) : term217 N.
Proof. exact (proj1 (@lem7600943 A N h1)). Qed.
Lemma lem7600947 {A N : Type'} (h1 : term231 A N) : term230 A N.
Proof. exact (proj2 (@lem7600936 A N h1)). Qed.
Lemma lem7600949 {A N : Type'} (h1 : term231 A N) : term229 A N.
Proof. exact (proj2 (@lem7600947 A N h1)). Qed.
Lemma lem7600951 {A N : Type'} (h1 : term231 A N) : term224 N.
Proof. exact (proj2 (@lem7600949 A N h1)). Qed.
Lemma lem7600953 {A N : Type'} (h1 : term231 A N) : term223 N.
Proof. exact (proj2 (@lem7600951 A N h1)). Qed.
Lemma lem7600954 {A N : Type'} (h1 : term231 A N) : term36 N.
Proof. exact (proj1 (@lem7600951 A N h1)). Qed.
Lemma lem7600956 {A N : Type'} (h1 : term231 A N) : term217 N.
Proof. exact (proj1 (@lem7600953 A N h1)). Qed.
Lemma lem7600957 {A N : Type'} (h1 : term244 A N) : term243 A N.
Proof. exact (proj2 (@lem7600932 A N h1)). Qed.
Lemma lem7600959 {A N : Type'} (h1 : term238 A N) : term238 A N.
Proof. exact (h1). Qed.
Lemma lem7600960 {A N : Type'} (h1 : term242 A N) : term242 A N.
Proof. exact (h1). Qed.
Lemma lem7600961 {A N : Type'} (h1 : term238 A N) : term237 A N.
Proof. exact (proj2 (@lem7600959 A N h1)). Qed.
Lemma lem7600963 {A N : Type'} (h1 : term238 A N) : term236 A N.
Proof. exact (proj2 (@lem7600961 A N h1)). Qed.
Lemma lem7600965 {A N : Type'} (h1 : term238 A N) : term235 N.
Proof. exact (proj2 (@lem7600963 A N h1)). Qed.
Lemma lem7600967 {A N : Type'} (h1 : term238 A N) : term223 N.
Proof. exact (proj2 (@lem7600965 A N h1)). Qed.
Lemma lem7600969 {A N : Type'} (h1 : term238 A N) : term222 N.
Proof. exact (proj2 (@lem7600967 A N h1)). Qed.
Lemma lem7600971 {A N : Type'} (h1 : term242 A N) : term241 A N.
Proof. exact (proj2 (@lem7600960 A N h1)). Qed.
Lemma lem7600973 {A N : Type'} (h1 : term242 A N) : term240 A N.
Proof. exact (proj2 (@lem7600971 A N h1)). Qed.
Lemma lem7600975 {A N : Type'} (h1 : term242 A N) : term235 N.
Proof. exact (proj2 (@lem7600973 A N h1)). Qed.
Lemma lem7600977 {A N : Type'} (h1 : term242 A N) : term223 N.
Proof. exact (proj2 (@lem7600975 A N h1)). Qed.
Lemma lem7600979 {A N : Type'} (h1 : term242 A N) : term222 N.
Proof. exact (proj2 (@lem7600977 A N h1)). Qed.
Lemma lem7601001 {N : Type'} (s : N -> Prop) : ((@dimindex N s) = (@CARD N (@UNIV N))) = ((@dimindex N s) = (@CARD N (@UNIV N))).
Proof. exact (eq_refl ((@dimindex N s) = (@CARD N (@UNIV N)))). Qed.
Lemma lem7601002 {N : Type'} : (term35 N) = (term35 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7601001 N s)). Qed.
Lemma lem7601003 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7601005 {N : Type'} : (term36 N) = (term36 N).
Proof. exact (MK_COMB (@lem7601003 N) (@lem7601002 N)). Qed.
Lemma lem7601006 {A N : Type'} (h1 : term227 A N) : term36 N.
Proof. exact (EQ_MP (@lem7601005 N) (@lem7600944 A N h1)). Qed.
Lemma lem7601020 {N : Type'} (s : N -> Prop) (n : nat) : (term96 N s n) = (term96 N s n).
Proof. exact (eq_refl (term96 N s n)). Qed.
Lemma lem7601021 {N : Type'} (s : N -> Prop) : (term182 N s) = (term182 N s).
Proof. exact (fun_ext (fun n : nat => @lem7601020 N s n)). Qed.
Lemma lem7601022 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7601023 {N : Type'} (s : N -> Prop) : (term193 N s) = (term193 N s).
Proof. exact (MK_COMB (@lem7601022) (@lem7601021 N s)). Qed.
Lemma lem7601024 {N : Type'} : (term206 N) = (term206 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7601023 N s)). Qed.
Lemma lem7601025 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7601027 {N : Type'} : (term217 N) = (term217 N).
Proof. exact (MK_COMB (@lem7601025 N) (@lem7601024 N)). Qed.
Lemma lem7601028 {A N : Type'} (h1 : term227 A N) : term217 N.
Proof. exact (EQ_MP (@lem7601027 N) (@lem7600946 A N h1)). Qed.
Lemma lem7601075 {N : Type'} (s : N -> Prop) : ((@dimindex N s) = (@CARD N (@UNIV N))) = ((@dimindex N s) = (@CARD N (@UNIV N))).
Proof. exact (eq_refl ((@dimindex N s) = (@CARD N (@UNIV N)))). Qed.
Lemma lem7601076 {N : Type'} : (term35 N) = (term35 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7601075 N s)). Qed.
Lemma lem7601077 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7601079 {N : Type'} : (term36 N) = (term36 N).
Proof. exact (MK_COMB (@lem7601077 N) (@lem7601076 N)). Qed.
Lemma lem7601080 {A N : Type'} (h1 : term231 A N) : term36 N.
Proof. exact (EQ_MP (@lem7601079 N) (@lem7600954 A N h1)). Qed.
Lemma lem7601094 {N : Type'} (s : N -> Prop) (n : nat) : (term96 N s n) = (term96 N s n).
Proof. exact (eq_refl (term96 N s n)). Qed.
Lemma lem7601095 {N : Type'} (s : N -> Prop) : (term182 N s) = (term182 N s).
Proof. exact (fun_ext (fun n : nat => @lem7601094 N s n)). Qed.
Lemma lem7601096 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7601097 {N : Type'} (s : N -> Prop) : (term193 N s) = (term193 N s).
Proof. exact (MK_COMB (@lem7601096) (@lem7601095 N s)). Qed.
Lemma lem7601098 {N : Type'} : (term206 N) = (term206 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7601097 N s)). Qed.
Lemma lem7601099 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7601101 {N : Type'} : (term217 N) = (term217 N).
Proof. exact (MK_COMB (@lem7601099 N) (@lem7601098 N)). Qed.
Lemma lem7601102 {A N : Type'} (h1 : term231 A N) : term217 N.
Proof. exact (EQ_MP (@lem7601101 N) (@lem7600956 A N h1)). Qed.
Lemma lem7601194 {N : Type'} (s : N -> Prop) (n : nat) : (term93 N s n) = (term246 N s n).
Proof. exact (@lem19490 (@FINITE N s) (term247 N s n) ((@CARD N s) = n)). Qed.
Lemma lem7601195 {N : Type'} (s : N -> Prop) : (term183 N s) = (term248 N s).
Proof. exact (fun_ext (fun n : nat => @lem7601194 N s n)). Qed.
Lemma lem7601196 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7601197 {N : Type'} (s : N -> Prop) : (term198 N s) = (term249 N s).
Proof. exact (MK_COMB (@lem7601196) (@lem7601195 N s)). Qed.
Lemma lem7601198 {N : Type'} : (term207 N) = (term250 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7601197 N s)). Qed.
Lemma lem7601199 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7601201 {N : Type'} : (term222 N) = (term251 N).
Proof. exact (MK_COMB (@lem7601199 N) (@lem7601198 N)). Qed.
Lemma lem7601202 {A N : Type'} (h1 : term238 A N) : term251 N.
Proof. exact (EQ_MP (@lem7601201 N) (@lem7600969 A N h1)). Qed.
Lemma lem7601268 {N : Type'} (s : N -> Prop) (n : nat) : (term93 N s n) = (term246 N s n).
Proof. exact (@lem19490 (@FINITE N s) (term247 N s n) ((@CARD N s) = n)). Qed.
Lemma lem7601269 {N : Type'} (s : N -> Prop) : (term183 N s) = (term248 N s).
Proof. exact (fun_ext (fun n : nat => @lem7601268 N s n)). Qed.
Lemma lem7601270 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7601271 {N : Type'} (s : N -> Prop) : (term198 N s) = (term249 N s).
Proof. exact (MK_COMB (@lem7601270) (@lem7601269 N s)). Qed.
Lemma lem7601272 {N : Type'} : (term207 N) = (term250 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7601271 N s)). Qed.
Lemma lem7601273 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7601275 {N : Type'} : (term222 N) = (term251 N).
Proof. exact (MK_COMB (@lem7601273 N) (@lem7601272 N)). Qed.
Lemma lem7601276 {A N : Type'} (h1 : term242 A N) : term251 N.
Proof. exact (EQ_MP (@lem7601275 N) (@lem7600979 A N h1)). Qed.
Lemma lem7601280 {A N : Type'} (_97667 : N -> Prop) (h1 : term227 A N) : term252 N _97667.
Proof. exact (@lem7601006 A N h1 _97667). Qed.
Lemma lem7601281 {N : Type'} (_97667 : N -> Prop) : (term252 N _97667) = ((@dimindex N _97667) = (@CARD N (@UNIV N))).
Proof. exact (eq_refl (term252 N _97667)). Qed.
Lemma lem7601283 {A N : Type'} (_97668 : N -> Prop) (h1 : term227 A N) : term208 N _97668.
Proof. exact (@lem7601028 A N h1 _97668). Qed.
Lemma lem7601284 {N : Type'} (_97668 : N -> Prop) : (term208 N _97668) = (term193 N _97668).
Proof. exact (eq_refl (term208 N _97668)). Qed.
Lemma lem7601285 {A N : Type'} (_97668 : N -> Prop) (h1 : term227 A N) : term193 N _97668.
Proof. exact (EQ_MP (@lem7601284 N _97668) (@lem7601283 A N _97668 h1)). Qed.
Lemma lem7601286 {A N : Type'} (_97668 : N -> Prop) (_97669 : nat) (h1 : term227 A N) : term184 N _97668 _97669.
Proof. exact (@lem7601285 A N _97668 h1 _97669). Qed.
Lemma lem7601287 {N : Type'} (_97668 : N -> Prop) (_97669 : nat) : (term184 N _97668 _97669) = (term96 N _97668 _97669).
Proof. exact (eq_refl (term184 N _97668 _97669)). Qed.
Lemma lem7601298 {A N : Type'} (_97673 : N -> Prop) (h1 : term231 A N) : term252 N _97673.
Proof. exact (@lem7601080 A N h1 _97673). Qed.
Lemma lem7601299 {N : Type'} (_97673 : N -> Prop) : (term252 N _97673) = ((@dimindex N _97673) = (@CARD N (@UNIV N))).
Proof. exact (eq_refl (term252 N _97673)). Qed.
Lemma lem7601301 {A N : Type'} (_97674 : N -> Prop) (h1 : term231 A N) : term208 N _97674.
Proof. exact (@lem7601102 A N h1 _97674). Qed.
Lemma lem7601302 {N : Type'} (_97674 : N -> Prop) : (term208 N _97674) = (term193 N _97674).
Proof. exact (eq_refl (term208 N _97674)). Qed.
Lemma lem7601303 {A N : Type'} (_97674 : N -> Prop) (h1 : term231 A N) : term193 N _97674.
Proof. exact (EQ_MP (@lem7601302 N _97674) (@lem7601301 A N _97674 h1)). Qed.
Lemma lem7601304 {A N : Type'} (_97674 : N -> Prop) (_97675 : nat) (h1 : term231 A N) : term184 N _97674 _97675.
Proof. exact (@lem7601303 A N _97674 h1 _97675). Qed.
Lemma lem7601305 {N : Type'} (_97674 : N -> Prop) (_97675 : nat) : (term184 N _97674 _97675) = (term96 N _97674 _97675).
Proof. exact (eq_refl (term184 N _97674 _97675)). Qed.
Lemma lem7601325 {A N : Type'} (_97682 : N -> Prop) (h1 : term238 A N) : term253 N _97682.
Proof. exact (@lem7601202 A N h1 _97682). Qed.
Lemma lem7601326 {N : Type'} (_97682 : N -> Prop) : (term253 N _97682) = (term249 N _97682).
Proof. exact (eq_refl (term253 N _97682)). Qed.
Lemma lem7601327 {A N : Type'} (_97682 : N -> Prop) (h1 : term238 A N) : term249 N _97682.
Proof. exact (EQ_MP (@lem7601326 N _97682) (@lem7601325 A N _97682 h1)). Qed.
Lemma lem7601328 {A N : Type'} (_97682 : N -> Prop) (_97683 : nat) (h1 : term238 A N) : term254 N _97682 _97683.
Proof. exact (@lem7601327 A N _97682 h1 _97683). Qed.
Lemma lem7601329 {N : Type'} (_97682 : N -> Prop) (_97683 : nat) : (term254 N _97682 _97683) = (term246 N _97682 _97683).
Proof. exact (eq_refl (term254 N _97682 _97683)). Qed.
Lemma lem7601330 {A N : Type'} (_97682 : N -> Prop) (_97683 : nat) (h1 : term238 A N) : term246 N _97682 _97683.
Proof. exact (EQ_MP (@lem7601329 N _97682 _97683) (@lem7601328 A N _97682 _97683 h1)). Qed.
Lemma lem7601343 {A N : Type'} (_97688 : N -> Prop) (h1 : term242 A N) : term253 N _97688.
Proof. exact (@lem7601276 A N h1 _97688). Qed.
Lemma lem7601344 {N : Type'} (_97688 : N -> Prop) : (term253 N _97688) = (term249 N _97688).
Proof. exact (eq_refl (term253 N _97688)). Qed.
Lemma lem7601345 {A N : Type'} (_97688 : N -> Prop) (h1 : term242 A N) : term249 N _97688.
Proof. exact (EQ_MP (@lem7601344 N _97688) (@lem7601343 A N _97688 h1)). Qed.
Lemma lem7601346 {A N : Type'} (_97688 : N -> Prop) (_97689 : nat) (h1 : term242 A N) : term254 N _97688 _97689.
Proof. exact (@lem7601345 A N _97688 h1 _97689). Qed.
Lemma lem7601347 {N : Type'} (_97688 : N -> Prop) (_97689 : nat) : (term254 N _97688 _97689) = (term246 N _97688 _97689).
Proof. exact (eq_refl (term254 N _97688 _97689)). Qed.
Lemma lem7601348 {A N : Type'} (_97688 : N -> Prop) (_97689 : nat) (h1 : term242 A N) : term246 N _97688 _97689.
Proof. exact (EQ_MP (@lem7601347 N _97688 _97689) (@lem7601346 A N _97688 _97689 h1)). Qed.
Lemma lem7601362 {A N : Type'} (h1 : term227 A N) : term46 N.
Proof. exact (proj1 (@lem7600937 A N h1)). Qed.
Lemma lem7601376 {A N : Type'} (_97668 : N -> Prop) (_97669 : nat) (h1 : term227 A N) : term96 N _97668 _97669.
Proof. exact (EQ_MP (@lem7601287 N _97668 _97669) (@lem7601286 A N _97668 _97669 h1)). Qed.
Lemma lem7601394 {A N : Type'} (h1 : term231 A N) : term46 N.
Proof. exact (proj1 (@lem7600947 A N h1)). Qed.
Lemma lem7601408 {A N : Type'} (_97674 : N -> Prop) (_97675 : nat) (h1 : term231 A N) : term96 N _97674 _97675.
Proof. exact (EQ_MP (@lem7601305 N _97674 _97675) (@lem7601304 A N _97674 _97675 h1)). Qed.
Lemma lem7601422 {A N : Type'} (h1 : term244 A N) : term122 N.
Proof. exact (proj1 (@lem7600932 A N h1)). Qed.
Lemma lem7601446 {A N : Type'} (_97683 : nat) (_97682 : N -> Prop) (h1 : term238 A N) : term255 N _97683 _97682.
Proof. exact (proj1 (@lem7601330 A N _97682 _97683 h1)). Qed.
Lemma lem7601454 {A N : Type'} (h1 : term244 A N) : term122 N.
Proof. exact (proj1 (@lem7600932 A N h1)). Qed.
Lemma lem7601478 {A N : Type'} (_97689 : nat) (_97688 : N -> Prop) (h1 : term242 A N) : term255 N _97689 _97688.
Proof. exact (proj1 (@lem7601348 A N _97688 _97689 h1)). Qed.
Lemma lem7601561 (x : nat) (y : nat) (z : nat) : term256 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem7601567 {A N : Type'} (h1 : term233 A N) : @FINITE N (@UNIV N).
Proof. exact (proj1 (@lem7600931 A N h1)). Qed.
Lemma lem7601568 {A N : Type'} (h1 : term233 A N) : term257 N.
Proof. exact (fun h0 : term122 N => @lem7601567 A N h1). Qed.
Lemma lem7601570 (p : Prop) : (term258 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7601571 {N : Type'} : (term257 N) = (@FINITE N (@UNIV N)).
Proof. exact (@lem7601570 (@FINITE N (@UNIV N))). Qed.
Lemma lem7601572 {A N : Type'} (h1 : term233 A N) : @FINITE N (@UNIV N).
Proof. exact (EQ_MP (@lem7601571 N) (@lem7601568 A N h1)). Qed.
Lemma lem7601574 {A N : Type'} (_97667 : N -> Prop) (h1 : term227 A N) : (@dimindex N _97667) = (@CARD N (@UNIV N)).
Proof. exact (EQ_MP (@lem7601281 N _97667) (@lem7601280 A N _97667 h1)). Qed.
Lemma lem7601575 {A N : Type'} (_97667 : N -> Prop) (h1 : term227 A N) : (@dimindex N _97667) = (@CARD N (@UNIV N)).
Proof. exact (@lem7601574 A N _97667 h1). Qed.
Lemma lem7601576 {A N : Type'} (h1 : term227 A N) : (@dimindex N (@UNIV N)) = (@CARD N (@UNIV N)).
Proof. exact (@lem7601575 A N (@UNIV N) h1). Qed.
Lemma lem7601577 {A N : Type'} (h1 : term227 A N) : term259 N.
Proof. exact (fun h0 : term260 N => @lem7601576 A N h1). Qed.
Lemma lem7601579 (p : Prop) : (term258 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7601580 {N : Type'} : (term259 N) = ((@dimindex N (@UNIV N)) = (@CARD N (@UNIV N))).
Proof. exact (@lem7601579 ((@dimindex N (@UNIV N)) = (@CARD N (@UNIV N)))). Qed.
Lemma lem7601581 {A N : Type'} (h1 : term227 A N) : (@dimindex N (@UNIV N)) = (@CARD N (@UNIV N)).
Proof. exact (EQ_MP (@lem7601580 N) (@lem7601577 A N h1)). Qed.
Lemma lem7601583 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem7601584 {N : Type'} : (@dimindex N (@UNIV N)) = (@dimindex N (@UNIV N)).
Proof. exact (@lem7601583 (@dimindex N (@UNIV N))). Qed.
Lemma lem7601585 {N : Type'} : term261 N.
Proof. exact (fun h0 : term262 N => @lem7601584 N). Qed.
Lemma lem7601587 (p : Prop) : (term258 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7601588 {N : Type'} : (term261 N) = ((@dimindex N (@UNIV N)) = (@dimindex N (@UNIV N))).
Proof. exact (@lem7601587 ((@dimindex N (@UNIV N)) = (@dimindex N (@UNIV N)))). Qed.
Lemma lem7601589 {N : Type'} : (@dimindex N (@UNIV N)) = (@dimindex N (@UNIV N)).
Proof. exact (EQ_MP (@lem7601588 N) (@lem7601585 N)). Qed.
Lemma lem7601607 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7601608 (y : nat) (x : nat) (z : nat) : (term263 x y z) = (term264 y x z).
Proof. exact (@lem7601607 (y = z) (term265 x z)). Qed.
Lemma lem7601618 (x : nat) (y : nat) : (term266 x y) = (term266 x y).
Proof. exact (eq_refl (term266 x y)). Qed.
Lemma lem7601619 (y : nat) (x : nat) (z : nat) : (term256 x y z) = (term267 y x z).
Proof. exact (MK_COMB (@lem7601618 x y) (@lem7601608 y x z)). Qed.
Lemma lem7601623 (q : Prop) (p : Prop) (r : Prop) : (term268 p q r) = (term268 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7601624 (y : nat) (x : nat) (z : nat) : (term267 y x z) = (term269 y x z).
Proof. exact (@lem7601623 (y = z) (term265 x y) (term265 x z)). Qed.
Lemma lem7601646 (y : nat) (x : nat) (z : nat) : (term256 x y z) = (term269 y x z).
Proof. exact (TRANS (@lem7601619 y x z) (@lem7601624 y x z)). Qed.
Lemma lem7601647 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7601648 (y : nat) (x : nat) (z : nat) : (term270 x y z) = (term271 y x z).
Proof. exact (MK_COMB (@lem7601647) (@lem7601646 y x z)). Qed.
Lemma lem7601670 (y : nat) (x : nat) (z : nat) : (term269 y x z) = (term269 y x z).
Proof. exact (eq_refl (term269 y x z)). Qed.
Lemma lem7601671 (y : nat) (x : nat) (z : nat) : ((term256 x y z) = (term269 y x z)) = ((term269 y x z) = (term269 y x z)).
Proof. exact (MK_COMB (@lem7601648 y x z) (@lem7601670 y x z)). Qed.
Lemma lem7601673 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7601674 (x : Prop) : (x = x) = True.
Proof. exact (@lem7601673 Prop x). Qed.
Lemma lem7601675 (y : nat) (x : nat) (z : nat) : ((term269 y x z) = (term269 y x z)) = True.
Proof. exact (@lem7601674 (term269 y x z)). Qed.
Lemma lem7601676 (y : nat) (x : nat) (z : nat) : ((term256 x y z) = (term269 y x z)) = True.
Proof. exact (TRANS (@lem7601671 y x z) (@lem7601675 y x z)). Qed.
Lemma lem7601677 (y : nat) (x : nat) (z : nat) : True = ((term256 x y z) = (term269 y x z)).
Proof. exact (SYM (@lem7601676 y x z)). Qed.
Lemma lem7601678 (y : nat) (x : nat) (z : nat) : (term256 x y z) = (term269 y x z).
Proof. exact (EQ_MP (@lem7601677 y x z) (@lem0)). Qed.
Lemma lem7601679 (y : nat) (x : nat) (z : nat) : term269 y x z.
Proof. exact (EQ_MP (@lem7601678 y x z) (@lem7601561 x y z)). Qed.
Lemma lem7601681 (b : Prop) (a : Prop) : (a \/ b) = (term272 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7601682 (x : nat) (y : nat) (z : nat) : (term269 y x z) = (term273 x y z).
Proof. exact (@lem7601681 (term274 y x z) (y = z)). Qed.
Lemma lem7601684 (a : Prop) (b : Prop) : (term275 a b) = (term276 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7601685 (y : nat) (x : nat) (z : nat) : (term277 y x z) = (term278 y x z).
Proof. exact (@lem7601684 (term265 x y) (term265 x z)). Qed.
Lemma lem7601687 (a : Prop) : (term48 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7601688 (x : nat) (y : nat) : (term279 x y) = (x = y).
Proof. exact (@lem7601687 (x = y)). Qed.
Lemma lem7601689 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7601690 (x : nat) (y : nat) : (term280 x y) = (term281 x y).
Proof. exact (MK_COMB (@lem7601689) (@lem7601688 x y)). Qed.
Lemma lem7601692 (a : Prop) : (term48 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7601693 (x : nat) (z : nat) : (term279 x z) = (x = z).
Proof. exact (@lem7601692 (x = z)). Qed.
Lemma lem7601694 (y : nat) (x : nat) (z : nat) : (term278 y x z) = (term282 y x z).
Proof. exact (MK_COMB (@lem7601690 x y) (@lem7601693 x z)). Qed.
Lemma lem7601695 (y : nat) (x : nat) (z : nat) : (term277 y x z) = (term282 y x z).
Proof. exact (TRANS (@lem7601685 y x z) (@lem7601694 y x z)). Qed.
Lemma lem7601696 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7601697 (y : nat) (x : nat) (z : nat) : (term283 y x z) = (term284 y x z).
Proof. exact (MK_COMB (@lem7601696) (@lem7601695 y x z)). Qed.
Lemma lem7601698 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem7601699 (x : nat) (y : nat) (z : nat) : (term273 x y z) = (term285 x y z).
Proof. exact (MK_COMB (@lem7601697 y x z) (@lem7601698 y z)). Qed.
Lemma lem7601700 (x : nat) (y : nat) (z : nat) : (term269 y x z) = (term285 x y z).
Proof. exact (TRANS (@lem7601682 x y z) (@lem7601699 x y z)). Qed.
Lemma lem7601702 {A N : Type'} (h1 : term227 A N) : term286 N.
Proof. exact (conj (@lem7601581 A N h1) (@lem7601589 N)). Qed.
Lemma lem7601704 (x : nat) (y : nat) (z : nat) : term285 x y z.
Proof. exact (EQ_MP (@lem7601700 x y z) (@lem7601679 y x z)). Qed.
Lemma lem7601705 {N : Type'} : term287 N.
Proof. exact (@lem7601704 (@dimindex N (@UNIV N)) (@CARD N (@UNIV N)) (@dimindex N (@UNIV N))). Qed.
Lemma lem7601708 {A N : Type'} (h1 : term227 A N) : (@CARD N (@UNIV N)) = (@dimindex N (@UNIV N)).
Proof. exact (@lem7601705 N (@lem7601702 A N h1)). Qed.
Lemma lem7601709 {A N : Type'} (h1 : term227 A N) : term288 N.
Proof. exact (fun h0 : term289 N => @lem7601708 A N h1). Qed.
Lemma lem7601711 (p : Prop) : (term258 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7601712 {N : Type'} : (term288 N) = ((@CARD N (@UNIV N)) = (@dimindex N (@UNIV N))).
Proof. exact (@lem7601711 ((@CARD N (@UNIV N)) = (@dimindex N (@UNIV N)))). Qed.
Lemma lem7601713 {A N : Type'} (h1 : term227 A N) : (@CARD N (@UNIV N)) = (@dimindex N (@UNIV N)).
Proof. exact (EQ_MP (@lem7601712 N) (@lem7601709 A N h1)). Qed.
Lemma lem7601715 (b : Prop) (a : Prop) : (a \/ b) = (term272 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7601716 {N : Type'} (_97668 : N -> Prop) (_97669 : nat) : (term96 N _97668 _97669) = (term290 N _97668 _97669).
Proof. exact (@lem7601715 (term92 N _97668 _97669) (@HAS_SIZE N _97668 _97669)). Qed.
Lemma lem7601718 (a : Prop) (b : Prop) : (term275 a b) = (term276 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7601719 {N : Type'} (_97668 : N -> Prop) (_97669 : nat) : (term291 N _97668 _97669) = (term292 N _97668 _97669).
Proof. exact (@lem7601718 (term293 N _97668) (term294 N _97668 _97669)). Qed.
Lemma lem7601721 (a : Prop) : (term48 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7601722 {N : Type'} (_97668 : N -> Prop) : (term295 N _97668) = (@FINITE N _97668).
Proof. exact (@lem7601721 (@FINITE N _97668)). Qed.
Lemma lem7601723 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7601724 {N : Type'} (_97668 : N -> Prop) : (term296 N _97668) = (term297 N _97668).
Proof. exact (MK_COMB (@lem7601723) (@lem7601722 N _97668)). Qed.
Lemma lem7601726 (a : Prop) : (term48 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7601727 {N : Type'} (_97668 : N -> Prop) (_97669 : nat) : (term298 N _97668 _97669) = ((@CARD N _97668) = _97669).
Proof. exact (@lem7601726 ((@CARD N _97668) = _97669)). Qed.
Lemma lem7601728 {N : Type'} (_97668 : N -> Prop) (_97669 : nat) : (term292 N _97668 _97669) = (term79 N _97668 _97669).
Proof. exact (MK_COMB (@lem7601724 N _97668) (@lem7601727 N _97668 _97669)). Qed.
Lemma lem7601729 {N : Type'} (_97668 : N -> Prop) (_97669 : nat) : (term291 N _97668 _97669) = (term79 N _97668 _97669).
Proof. exact (TRANS (@lem7601719 N _97668 _97669) (@lem7601728 N _97668 _97669)). Qed.
Lemma lem7601730 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7601731 {N : Type'} (_97668 : N -> Prop) (_97669 : nat) : (term299 N _97668 _97669) = (term300 N _97668 _97669).
Proof. exact (MK_COMB (@lem7601730) (@lem7601729 N _97668 _97669)). Qed.
Lemma lem7601732 {N : Type'} (_97668 : N -> Prop) (_97669 : nat) : (@HAS_SIZE N _97668 _97669) = (@HAS_SIZE N _97668 _97669).
Proof. exact (eq_refl (@HAS_SIZE N _97668 _97669)). Qed.
Lemma lem7601733 {N : Type'} (_97668 : N -> Prop) (_97669 : nat) : (term290 N _97668 _97669) = (term301 N _97668 _97669).
Proof. exact (MK_COMB (@lem7601731 N _97668 _97669) (@lem7601732 N _97668 _97669)). Qed.
Lemma lem7601734 {N : Type'} (_97668 : N -> Prop) (_97669 : nat) : (term96 N _97668 _97669) = (term301 N _97668 _97669).
Proof. exact (TRANS (@lem7601716 N _97668 _97669) (@lem7601733 N _97668 _97669)). Qed.
Lemma lem7601736 {A N : Type'} (h1 : term227 A N) (h2 : term233 A N) : term302 N.
Proof. exact (conj (@lem7601572 A N h2) (@lem7601713 A N h1)). Qed.
Lemma lem7601738 {A N : Type'} (_97668 : N -> Prop) (_97669 : nat) (h1 : term227 A N) : term301 N _97668 _97669.
Proof. exact (EQ_MP (@lem7601734 N _97668 _97669) (@lem7601376 A N _97668 _97669 h1)). Qed.
Lemma lem7601739 {A N : Type'} (_97668 : N -> Prop) (_97669 : nat) (h1 : term227 A N) : term301 N _97668 _97669.
Proof. exact (@lem7601738 A N _97668 _97669 h1). Qed.
Lemma lem7601740 {A N : Type'} (h1 : term227 A N) : term303 N.
Proof. exact (@lem7601739 A N (@UNIV N) (@dimindex N (@UNIV N)) h1). Qed.
Lemma lem7601743 {A N : Type'} (h1 : term227 A N) (h2 : term233 A N) : term1 N.
Proof. exact (@lem7601740 A N h1 (@lem7601736 A N h1 h2)). Qed.
Lemma lem7601744 {A N : Type'} (h1 : term227 A N) (h2 : term233 A N) : term304 N.
Proof. exact (fun h0 : term46 N => @lem7601743 A N h1 h2). Qed.
Lemma lem7601746 (p : Prop) : (term258 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7601747 {N : Type'} : (term304 N) = (term1 N).
Proof. exact (@lem7601746 (term1 N)). Qed.
Lemma lem7601748 {A N : Type'} (h1 : term227 A N) (h2 : term233 A N) : term1 N.
Proof. exact (EQ_MP (@lem7601747 N) (@lem7601744 A N h1 h2)). Qed.
Lemma lem7601751 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7601753 {N : Type'} : (term46 N) = (term305 N).
Proof. exact (@lem7601751 (term1 N)). Qed.
Lemma lem7601756 {A N : Type'} (h1 : term227 A N) : term305 N.
Proof. exact (EQ_MP (@lem7601753 N) (@lem7601362 A N h1)). Qed.
Lemma lem7601759 {A N : Type'} (h1 : term227 A N) (h2 : term233 A N) : False.
Proof. exact (@lem7601756 A N h1 (@lem7601748 A N h1 h2)). Qed.
Lemma lem7601760 {A N : Type'} (h1 : term227 A N) (h2 : term233 A N) : term306.
Proof. exact (fun h0 : ~ False => @lem7601759 A N h1 h2). Qed.
Lemma lem7601762 (p : Prop) : (term258 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7601763 : term306 = False.
Proof. exact (@lem7601762 False). Qed.
Lemma lem7601764 {A N : Type'} (h1 : term227 A N) (h2 : term233 A N) : False.
Proof. exact (EQ_MP (@lem7601763) (@lem7601760 A N h1 h2)). Qed.
Lemma lem7601849 (x : nat) (y : nat) (z : nat) : term256 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem7601855 {A N : Type'} (h1 : term233 A N) : @FINITE N (@UNIV N).
Proof. exact (proj1 (@lem7600931 A N h1)). Qed.
Lemma lem7601856 {A N : Type'} (h1 : term233 A N) : term257 N.
Proof. exact (fun h0 : term122 N => @lem7601855 A N h1). Qed.
Lemma lem7601858 (p : Prop) : (term258 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7601859 {N : Type'} : (term257 N) = (@FINITE N (@UNIV N)).
Proof. exact (@lem7601858 (@FINITE N (@UNIV N))). Qed.
Lemma lem7601860 {A N : Type'} (h1 : term233 A N) : @FINITE N (@UNIV N).
Proof. exact (EQ_MP (@lem7601859 N) (@lem7601856 A N h1)). Qed.
Lemma lem7601862 {A N : Type'} (_97673 : N -> Prop) (h1 : term231 A N) : (@dimindex N _97673) = (@CARD N (@UNIV N)).
Proof. exact (EQ_MP (@lem7601299 N _97673) (@lem7601298 A N _97673 h1)). Qed.
Lemma lem7601863 {A N : Type'} (_97673 : N -> Prop) (h1 : term231 A N) : (@dimindex N _97673) = (@CARD N (@UNIV N)).
Proof. exact (@lem7601862 A N _97673 h1). Qed.
Lemma lem7601864 {A N : Type'} (h1 : term231 A N) : (@dimindex N (@UNIV N)) = (@CARD N (@UNIV N)).
Proof. exact (@lem7601863 A N (@UNIV N) h1). Qed.
Lemma lem7601865 {A N : Type'} (h1 : term231 A N) : term259 N.
Proof. exact (fun h0 : term260 N => @lem7601864 A N h1). Qed.
Lemma lem7601867 (p : Prop) : (term258 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7601868 {N : Type'} : (term259 N) = ((@dimindex N (@UNIV N)) = (@CARD N (@UNIV N))).
Proof. exact (@lem7601867 ((@dimindex N (@UNIV N)) = (@CARD N (@UNIV N)))). Qed.
Lemma lem7601869 {A N : Type'} (h1 : term231 A N) : (@dimindex N (@UNIV N)) = (@CARD N (@UNIV N)).
Proof. exact (EQ_MP (@lem7601868 N) (@lem7601865 A N h1)). Qed.
Lemma lem7601871 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem7601872 {N : Type'} : (@dimindex N (@UNIV N)) = (@dimindex N (@UNIV N)).
Proof. exact (@lem7601871 (@dimindex N (@UNIV N))). Qed.
Lemma lem7601873 {N : Type'} : term261 N.
Proof. exact (fun h0 : term262 N => @lem7601872 N). Qed.
Lemma lem7601875 (p : Prop) : (term258 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7601876 {N : Type'} : (term261 N) = ((@dimindex N (@UNIV N)) = (@dimindex N (@UNIV N))).
Proof. exact (@lem7601875 ((@dimindex N (@UNIV N)) = (@dimindex N (@UNIV N)))). Qed.
Lemma lem7601877 {N : Type'} : (@dimindex N (@UNIV N)) = (@dimindex N (@UNIV N)).
Proof. exact (EQ_MP (@lem7601876 N) (@lem7601873 N)). Qed.
Lemma lem7601895 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7601896 (y : nat) (x : nat) (z : nat) : (term263 x y z) = (term264 y x z).
Proof. exact (@lem7601895 (y = z) (term265 x z)). Qed.
Lemma lem7601906 (x : nat) (y : nat) : (term266 x y) = (term266 x y).
Proof. exact (eq_refl (term266 x y)). Qed.
Lemma lem7601907 (y : nat) (x : nat) (z : nat) : (term256 x y z) = (term267 y x z).
Proof. exact (MK_COMB (@lem7601906 x y) (@lem7601896 y x z)). Qed.
Lemma lem7601911 (q : Prop) (p : Prop) (r : Prop) : (term268 p q r) = (term268 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7601912 (y : nat) (x : nat) (z : nat) : (term267 y x z) = (term269 y x z).
Proof. exact (@lem7601911 (y = z) (term265 x y) (term265 x z)). Qed.
Lemma lem7601934 (y : nat) (x : nat) (z : nat) : (term256 x y z) = (term269 y x z).
Proof. exact (TRANS (@lem7601907 y x z) (@lem7601912 y x z)). Qed.
Lemma lem7601935 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7601936 (y : nat) (x : nat) (z : nat) : (term270 x y z) = (term271 y x z).
Proof. exact (MK_COMB (@lem7601935) (@lem7601934 y x z)). Qed.
Lemma lem7601958 (y : nat) (x : nat) (z : nat) : (term269 y x z) = (term269 y x z).
Proof. exact (eq_refl (term269 y x z)). Qed.
Lemma lem7601959 (y : nat) (x : nat) (z : nat) : ((term256 x y z) = (term269 y x z)) = ((term269 y x z) = (term269 y x z)).
Proof. exact (MK_COMB (@lem7601936 y x z) (@lem7601958 y x z)). Qed.
Lemma lem7601961 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7601962 (x : Prop) : (x = x) = True.
Proof. exact (@lem7601961 Prop x). Qed.
Lemma lem7601963 (y : nat) (x : nat) (z : nat) : ((term269 y x z) = (term269 y x z)) = True.
Proof. exact (@lem7601962 (term269 y x z)). Qed.
Lemma lem7601964 (y : nat) (x : nat) (z : nat) : ((term256 x y z) = (term269 y x z)) = True.
Proof. exact (TRANS (@lem7601959 y x z) (@lem7601963 y x z)). Qed.
Lemma lem7601965 (y : nat) (x : nat) (z : nat) : True = ((term256 x y z) = (term269 y x z)).
Proof. exact (SYM (@lem7601964 y x z)). Qed.
Lemma lem7601966 (y : nat) (x : nat) (z : nat) : (term256 x y z) = (term269 y x z).
Proof. exact (EQ_MP (@lem7601965 y x z) (@lem0)). Qed.
Lemma lem7601967 (y : nat) (x : nat) (z : nat) : term269 y x z.
Proof. exact (EQ_MP (@lem7601966 y x z) (@lem7601849 x y z)). Qed.
Lemma lem7601969 (b : Prop) (a : Prop) : (a \/ b) = (term272 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7601970 (x : nat) (y : nat) (z : nat) : (term269 y x z) = (term273 x y z).
Proof. exact (@lem7601969 (term274 y x z) (y = z)). Qed.
Lemma lem7601972 (a : Prop) (b : Prop) : (term275 a b) = (term276 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7601973 (y : nat) (x : nat) (z : nat) : (term277 y x z) = (term278 y x z).
Proof. exact (@lem7601972 (term265 x y) (term265 x z)). Qed.
Lemma lem7601975 (a : Prop) : (term48 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7601976 (x : nat) (y : nat) : (term279 x y) = (x = y).
Proof. exact (@lem7601975 (x = y)). Qed.
Lemma lem7601977 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7601978 (x : nat) (y : nat) : (term280 x y) = (term281 x y).
Proof. exact (MK_COMB (@lem7601977) (@lem7601976 x y)). Qed.
Lemma lem7601980 (a : Prop) : (term48 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7601981 (x : nat) (z : nat) : (term279 x z) = (x = z).
Proof. exact (@lem7601980 (x = z)). Qed.
Lemma lem7601982 (y : nat) (x : nat) (z : nat) : (term278 y x z) = (term282 y x z).
Proof. exact (MK_COMB (@lem7601978 x y) (@lem7601981 x z)). Qed.
Lemma lem7601983 (y : nat) (x : nat) (z : nat) : (term277 y x z) = (term282 y x z).
Proof. exact (TRANS (@lem7601973 y x z) (@lem7601982 y x z)). Qed.
Lemma lem7601984 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7601985 (y : nat) (x : nat) (z : nat) : (term283 y x z) = (term284 y x z).
Proof. exact (MK_COMB (@lem7601984) (@lem7601983 y x z)). Qed.
Lemma lem7601986 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem7601987 (x : nat) (y : nat) (z : nat) : (term273 x y z) = (term285 x y z).
Proof. exact (MK_COMB (@lem7601985 y x z) (@lem7601986 y z)). Qed.
Lemma lem7601988 (x : nat) (y : nat) (z : nat) : (term269 y x z) = (term285 x y z).
Proof. exact (TRANS (@lem7601970 x y z) (@lem7601987 x y z)). Qed.
Lemma lem7601990 {A N : Type'} (h1 : term231 A N) : term286 N.
Proof. exact (conj (@lem7601869 A N h1) (@lem7601877 N)). Qed.
Lemma lem7601992 (x : nat) (y : nat) (z : nat) : term285 x y z.
Proof. exact (EQ_MP (@lem7601988 x y z) (@lem7601967 y x z)). Qed.
Lemma lem7601993 {N : Type'} : term287 N.
Proof. exact (@lem7601992 (@dimindex N (@UNIV N)) (@CARD N (@UNIV N)) (@dimindex N (@UNIV N))). Qed.
Lemma lem7601996 {A N : Type'} (h1 : term231 A N) : (@CARD N (@UNIV N)) = (@dimindex N (@UNIV N)).
Proof. exact (@lem7601993 N (@lem7601990 A N h1)). Qed.
Lemma lem7601997 {A N : Type'} (h1 : term231 A N) : term288 N.
Proof. exact (fun h0 : term289 N => @lem7601996 A N h1). Qed.
Lemma lem7601999 (p : Prop) : (term258 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7602000 {N : Type'} : (term288 N) = ((@CARD N (@UNIV N)) = (@dimindex N (@UNIV N))).
Proof. exact (@lem7601999 ((@CARD N (@UNIV N)) = (@dimindex N (@UNIV N)))). Qed.
Lemma lem7602001 {A N : Type'} (h1 : term231 A N) : (@CARD N (@UNIV N)) = (@dimindex N (@UNIV N)).
Proof. exact (EQ_MP (@lem7602000 N) (@lem7601997 A N h1)). Qed.
Lemma lem7602003 (b : Prop) (a : Prop) : (a \/ b) = (term272 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7602004 {N : Type'} (_97674 : N -> Prop) (_97675 : nat) : (term96 N _97674 _97675) = (term290 N _97674 _97675).
Proof. exact (@lem7602003 (term92 N _97674 _97675) (@HAS_SIZE N _97674 _97675)). Qed.
Lemma lem7602006 (a : Prop) (b : Prop) : (term275 a b) = (term276 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7602007 {N : Type'} (_97674 : N -> Prop) (_97675 : nat) : (term291 N _97674 _97675) = (term292 N _97674 _97675).
Proof. exact (@lem7602006 (term293 N _97674) (term294 N _97674 _97675)). Qed.
Lemma lem7602009 (a : Prop) : (term48 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7602010 {N : Type'} (_97674 : N -> Prop) : (term295 N _97674) = (@FINITE N _97674).
Proof. exact (@lem7602009 (@FINITE N _97674)). Qed.
Lemma lem7602011 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7602012 {N : Type'} (_97674 : N -> Prop) : (term296 N _97674) = (term297 N _97674).
Proof. exact (MK_COMB (@lem7602011) (@lem7602010 N _97674)). Qed.
Lemma lem7602014 (a : Prop) : (term48 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7602015 {N : Type'} (_97674 : N -> Prop) (_97675 : nat) : (term298 N _97674 _97675) = ((@CARD N _97674) = _97675).
Proof. exact (@lem7602014 ((@CARD N _97674) = _97675)). Qed.
Lemma lem7602016 {N : Type'} (_97674 : N -> Prop) (_97675 : nat) : (term292 N _97674 _97675) = (term79 N _97674 _97675).
Proof. exact (MK_COMB (@lem7602012 N _97674) (@lem7602015 N _97674 _97675)). Qed.
Lemma lem7602017 {N : Type'} (_97674 : N -> Prop) (_97675 : nat) : (term291 N _97674 _97675) = (term79 N _97674 _97675).
Proof. exact (TRANS (@lem7602007 N _97674 _97675) (@lem7602016 N _97674 _97675)). Qed.
Lemma lem7602018 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7602019 {N : Type'} (_97674 : N -> Prop) (_97675 : nat) : (term299 N _97674 _97675) = (term300 N _97674 _97675).
Proof. exact (MK_COMB (@lem7602018) (@lem7602017 N _97674 _97675)). Qed.
Lemma lem7602020 {N : Type'} (_97674 : N -> Prop) (_97675 : nat) : (@HAS_SIZE N _97674 _97675) = (@HAS_SIZE N _97674 _97675).
Proof. exact (eq_refl (@HAS_SIZE N _97674 _97675)). Qed.
Lemma lem7602021 {N : Type'} (_97674 : N -> Prop) (_97675 : nat) : (term290 N _97674 _97675) = (term301 N _97674 _97675).
Proof. exact (MK_COMB (@lem7602019 N _97674 _97675) (@lem7602020 N _97674 _97675)). Qed.
Lemma lem7602022 {N : Type'} (_97674 : N -> Prop) (_97675 : nat) : (term96 N _97674 _97675) = (term301 N _97674 _97675).
Proof. exact (TRANS (@lem7602004 N _97674 _97675) (@lem7602021 N _97674 _97675)). Qed.
Lemma lem7602024 {A N : Type'} (h1 : term233 A N) (h2 : term231 A N) : term302 N.
Proof. exact (conj (@lem7601860 A N h1) (@lem7602001 A N h2)). Qed.
Lemma lem7602026 {A N : Type'} (_97674 : N -> Prop) (_97675 : nat) (h1 : term231 A N) : term301 N _97674 _97675.
Proof. exact (EQ_MP (@lem7602022 N _97674 _97675) (@lem7601408 A N _97674 _97675 h1)). Qed.
Lemma lem7602027 {A N : Type'} (_97674 : N -> Prop) (_97675 : nat) (h1 : term231 A N) : term301 N _97674 _97675.
Proof. exact (@lem7602026 A N _97674 _97675 h1). Qed.
Lemma lem7602028 {A N : Type'} (h1 : term231 A N) : term303 N.
Proof. exact (@lem7602027 A N (@UNIV N) (@dimindex N (@UNIV N)) h1). Qed.
Lemma lem7602031 {A N : Type'} (h1 : term233 A N) (h2 : term231 A N) : term1 N.
Proof. exact (@lem7602028 A N h2 (@lem7602024 A N h1 h2)). Qed.
Lemma lem7602032 {A N : Type'} (h1 : term233 A N) (h2 : term231 A N) : term304 N.
Proof. exact (fun h0 : term46 N => @lem7602031 A N h1 h2). Qed.
Lemma lem7602034 (p : Prop) : (term258 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7602035 {N : Type'} : (term304 N) = (term1 N).
Proof. exact (@lem7602034 (term1 N)). Qed.
Lemma lem7602036 {A N : Type'} (h1 : term233 A N) (h2 : term231 A N) : term1 N.
Proof. exact (EQ_MP (@lem7602035 N) (@lem7602032 A N h1 h2)). Qed.
Lemma lem7602039 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7602041 {N : Type'} : (term46 N) = (term305 N).
Proof. exact (@lem7602039 (term1 N)). Qed.
Lemma lem7602044 {A N : Type'} (h1 : term231 A N) : term305 N.
Proof. exact (EQ_MP (@lem7602041 N) (@lem7601394 A N h1)). Qed.
Lemma lem7602047 {A N : Type'} (h1 : term233 A N) (h2 : term231 A N) : False.
Proof. exact (@lem7602044 A N h2 (@lem7602036 A N h1 h2)). Qed.
Lemma lem7602048 {A N : Type'} (h1 : term233 A N) (h2 : term231 A N) : term306.
Proof. exact (fun h0 : ~ False => @lem7602047 A N h1 h2). Qed.
Lemma lem7602050 (p : Prop) : (term258 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7602051 : term306 = False.
Proof. exact (@lem7602050 False). Qed.
Lemma lem7602052 {A N : Type'} (h1 : term233 A N) (h2 : term231 A N) : False.
Proof. exact (EQ_MP (@lem7602051) (@lem7602048 A N h1 h2)). Qed.
Lemma lem7602151 {A N : Type'} (h1 : term238 A N) : term1 N.
Proof. exact (proj1 (@lem7600961 A N h1)). Qed.
Lemma lem7602152 {A N : Type'} (h1 : term238 A N) : term304 N.
Proof. exact (fun h0 : term46 N => @lem7602151 A N h1). Qed.
Lemma lem7602154 (p : Prop) : (term258 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7602155 {N : Type'} : (term304 N) = (term1 N).
Proof. exact (@lem7602154 (term1 N)). Qed.
Lemma lem7602156 {A N : Type'} (h1 : term238 A N) : term1 N.
Proof. exact (EQ_MP (@lem7602155 N) (@lem7602152 A N h1)). Qed.
Lemma lem7602162 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7602163 {N : Type'} (_97682 : N -> Prop) (_97683 : nat) : (term255 N _97683 _97682) = (term307 N _97682 _97683).
Proof. exact (@lem7602162 (@FINITE N _97682) (term247 N _97682 _97683)). Qed.
Lemma lem7602169 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7602170 {N : Type'} (_97682 : N -> Prop) (_97683 : nat) : (term308 N _97683 _97682) = (term309 N _97682 _97683).
Proof. exact (MK_COMB (@lem7602169) (@lem7602163 N _97682 _97683)). Qed.
Lemma lem7602176 {N : Type'} (_97682 : N -> Prop) (_97683 : nat) : (term307 N _97682 _97683) = (term307 N _97682 _97683).
Proof. exact (eq_refl (term307 N _97682 _97683)). Qed.
Lemma lem7602177 {N : Type'} (_97682 : N -> Prop) (_97683 : nat) : ((term255 N _97683 _97682) = (term307 N _97682 _97683)) = ((term307 N _97682 _97683) = (term307 N _97682 _97683)).
Proof. exact (MK_COMB (@lem7602170 N _97682 _97683) (@lem7602176 N _97682 _97683)). Qed.
Lemma lem7602179 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7602180 (x : Prop) : (x = x) = True.
Proof. exact (@lem7602179 Prop x). Qed.
Lemma lem7602181 {N : Type'} (_97682 : N -> Prop) (_97683 : nat) : ((term307 N _97682 _97683) = (term307 N _97682 _97683)) = True.
Proof. exact (@lem7602180 (term307 N _97682 _97683)). Qed.
Lemma lem7602182 {N : Type'} (_97682 : N -> Prop) (_97683 : nat) : ((term255 N _97683 _97682) = (term307 N _97682 _97683)) = True.
Proof. exact (TRANS (@lem7602177 N _97682 _97683) (@lem7602181 N _97682 _97683)). Qed.
Lemma lem7602183 {N : Type'} (_97682 : N -> Prop) (_97683 : nat) : True = ((term255 N _97683 _97682) = (term307 N _97682 _97683)).
Proof. exact (SYM (@lem7602182 N _97682 _97683)). Qed.
Lemma lem7602184 {N : Type'} (_97682 : N -> Prop) (_97683 : nat) : (term255 N _97683 _97682) = (term307 N _97682 _97683).
Proof. exact (EQ_MP (@lem7602183 N _97682 _97683) (@lem0)). Qed.
Lemma lem7602185 {A N : Type'} (_97682 : N -> Prop) (_97683 : nat) (h1 : term238 A N) : term307 N _97682 _97683.
Proof. exact (EQ_MP (@lem7602184 N _97682 _97683) (@lem7601446 A N _97683 _97682 h1)). Qed.
Lemma lem7602187 (b : Prop) (a : Prop) : (a \/ b) = (term272 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7602188 {N : Type'} (_97683 : nat) (_97682 : N -> Prop) : (term307 N _97682 _97683) = (term310 N _97683 _97682).
Proof. exact (@lem7602187 (term247 N _97682 _97683) (@FINITE N _97682)). Qed.
Lemma lem7602190 (a : Prop) : (term48 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7602191 {N : Type'} (_97682 : N -> Prop) (_97683 : nat) : (term311 N _97682 _97683) = (@HAS_SIZE N _97682 _97683).
Proof. exact (@lem7602190 (@HAS_SIZE N _97682 _97683)). Qed.
Lemma lem7602192 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7602193 {N : Type'} (_97682 : N -> Prop) (_97683 : nat) : (term312 N _97682 _97683) = (term313 N _97682 _97683).
Proof. exact (MK_COMB (@lem7602192) (@lem7602191 N _97682 _97683)). Qed.
Lemma lem7602194 {N : Type'} (_97682 : N -> Prop) : (@FINITE N _97682) = (@FINITE N _97682).
Proof. exact (eq_refl (@FINITE N _97682)). Qed.
Lemma lem7602195 {N : Type'} (_97683 : nat) (_97682 : N -> Prop) : (term310 N _97683 _97682) = (term314 N _97683 _97682).
Proof. exact (MK_COMB (@lem7602193 N _97682 _97683) (@lem7602194 N _97682)). Qed.
Lemma lem7602196 {N : Type'} (_97683 : nat) (_97682 : N -> Prop) : (term307 N _97682 _97683) = (term314 N _97683 _97682).
Proof. exact (TRANS (@lem7602188 N _97683 _97682) (@lem7602195 N _97683 _97682)). Qed.
Lemma lem7602199 {A N : Type'} (_97683 : nat) (_97682 : N -> Prop) (h1 : term238 A N) : term314 N _97683 _97682.
Proof. exact (EQ_MP (@lem7602196 N _97683 _97682) (@lem7602185 A N _97682 _97683 h1)). Qed.
Lemma lem7602200 {A N : Type'} (_97683 : nat) (_97682 : N -> Prop) (h1 : term238 A N) : term314 N _97683 _97682.
Proof. exact (@lem7602199 A N _97683 _97682 h1). Qed.
Lemma lem7602201 {A N : Type'} (h1 : term238 A N) : term315 N.
Proof. exact (@lem7602200 A N (@dimindex N (@UNIV N)) (@UNIV N) h1). Qed.
Lemma lem7602204 {A N : Type'} (h1 : term238 A N) : @FINITE N (@UNIV N).
Proof. exact (@lem7602201 A N h1 (@lem7602156 A N h1)). Qed.
Lemma lem7602205 {A N : Type'} (h1 : term238 A N) : term257 N.
Proof. exact (fun h0 : term122 N => @lem7602204 A N h1). Qed.
Lemma lem7602207 (p : Prop) : (term258 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7602208 {N : Type'} : (term257 N) = (@FINITE N (@UNIV N)).
Proof. exact (@lem7602207 (@FINITE N (@UNIV N))). Qed.
Lemma lem7602209 {A N : Type'} (h1 : term238 A N) : @FINITE N (@UNIV N).
Proof. exact (EQ_MP (@lem7602208 N) (@lem7602205 A N h1)). Qed.
Lemma lem7602212 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7602214 {N : Type'} : (term122 N) = (term316 N).
Proof. exact (@lem7602212 (@FINITE N (@UNIV N))). Qed.
Lemma lem7602217 {A N : Type'} (h1 : term244 A N) : term316 N.
Proof. exact (EQ_MP (@lem7602214 N) (@lem7601422 A N h1)). Qed.
Lemma lem7602220 {A N : Type'} (h1 : term238 A N) (h2 : term244 A N) : False.
Proof. exact (@lem7602217 A N h2 (@lem7602209 A N h1)). Qed.
Lemma lem7602221 {A N : Type'} (h1 : term238 A N) (h2 : term244 A N) : term306.
Proof. exact (fun h0 : ~ False => @lem7602220 A N h1 h2). Qed.
Lemma lem7602223 (p : Prop) : (term258 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7602224 : term306 = False.
Proof. exact (@lem7602223 False). Qed.
Lemma lem7602225 {A N : Type'} (h1 : term238 A N) (h2 : term244 A N) : False.
Proof. exact (EQ_MP (@lem7602224) (@lem7602221 A N h1 h2)). Qed.
Lemma lem7602316 {A N : Type'} (h1 : term242 A N) : term1 N.
Proof. exact (proj1 (@lem7600971 A N h1)). Qed.
Lemma lem7602317 {A N : Type'} (h1 : term242 A N) : term304 N.
Proof. exact (fun h0 : term46 N => @lem7602316 A N h1). Qed.
Lemma lem7602319 (p : Prop) : (term258 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7602320 {N : Type'} : (term304 N) = (term1 N).
Proof. exact (@lem7602319 (term1 N)). Qed.
Lemma lem7602321 {A N : Type'} (h1 : term242 A N) : term1 N.
Proof. exact (EQ_MP (@lem7602320 N) (@lem7602317 A N h1)). Qed.
Lemma lem7602327 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7602328 {N : Type'} (_97688 : N -> Prop) (_97689 : nat) : (term255 N _97689 _97688) = (term307 N _97688 _97689).
Proof. exact (@lem7602327 (@FINITE N _97688) (term247 N _97688 _97689)). Qed.
Lemma lem7602334 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7602335 {N : Type'} (_97688 : N -> Prop) (_97689 : nat) : (term308 N _97689 _97688) = (term309 N _97688 _97689).
Proof. exact (MK_COMB (@lem7602334) (@lem7602328 N _97688 _97689)). Qed.
Lemma lem7602341 {N : Type'} (_97688 : N -> Prop) (_97689 : nat) : (term307 N _97688 _97689) = (term307 N _97688 _97689).
Proof. exact (eq_refl (term307 N _97688 _97689)). Qed.
Lemma lem7602342 {N : Type'} (_97688 : N -> Prop) (_97689 : nat) : ((term255 N _97689 _97688) = (term307 N _97688 _97689)) = ((term307 N _97688 _97689) = (term307 N _97688 _97689)).
Proof. exact (MK_COMB (@lem7602335 N _97688 _97689) (@lem7602341 N _97688 _97689)). Qed.
Lemma lem7602344 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7602345 (x : Prop) : (x = x) = True.
Proof. exact (@lem7602344 Prop x). Qed.
Lemma lem7602346 {N : Type'} (_97688 : N -> Prop) (_97689 : nat) : ((term307 N _97688 _97689) = (term307 N _97688 _97689)) = True.
Proof. exact (@lem7602345 (term307 N _97688 _97689)). Qed.
Lemma lem7602347 {N : Type'} (_97688 : N -> Prop) (_97689 : nat) : ((term255 N _97689 _97688) = (term307 N _97688 _97689)) = True.
Proof. exact (TRANS (@lem7602342 N _97688 _97689) (@lem7602346 N _97688 _97689)). Qed.
Lemma lem7602348 {N : Type'} (_97688 : N -> Prop) (_97689 : nat) : True = ((term255 N _97689 _97688) = (term307 N _97688 _97689)).
Proof. exact (SYM (@lem7602347 N _97688 _97689)). Qed.
Lemma lem7602349 {N : Type'} (_97688 : N -> Prop) (_97689 : nat) : (term255 N _97689 _97688) = (term307 N _97688 _97689).
Proof. exact (EQ_MP (@lem7602348 N _97688 _97689) (@lem0)). Qed.
Lemma lem7602350 {A N : Type'} (_97688 : N -> Prop) (_97689 : nat) (h1 : term242 A N) : term307 N _97688 _97689.
Proof. exact (EQ_MP (@lem7602349 N _97688 _97689) (@lem7601478 A N _97689 _97688 h1)). Qed.
Lemma lem7602352 (b : Prop) (a : Prop) : (a \/ b) = (term272 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7602353 {N : Type'} (_97689 : nat) (_97688 : N -> Prop) : (term307 N _97688 _97689) = (term310 N _97689 _97688).
Proof. exact (@lem7602352 (term247 N _97688 _97689) (@FINITE N _97688)). Qed.
Lemma lem7602355 (a : Prop) : (term48 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7602356 {N : Type'} (_97688 : N -> Prop) (_97689 : nat) : (term311 N _97688 _97689) = (@HAS_SIZE N _97688 _97689).
Proof. exact (@lem7602355 (@HAS_SIZE N _97688 _97689)). Qed.
Lemma lem7602357 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7602358 {N : Type'} (_97688 : N -> Prop) (_97689 : nat) : (term312 N _97688 _97689) = (term313 N _97688 _97689).
Proof. exact (MK_COMB (@lem7602357) (@lem7602356 N _97688 _97689)). Qed.
Lemma lem7602359 {N : Type'} (_97688 : N -> Prop) : (@FINITE N _97688) = (@FINITE N _97688).
Proof. exact (eq_refl (@FINITE N _97688)). Qed.
Lemma lem7602360 {N : Type'} (_97689 : nat) (_97688 : N -> Prop) : (term310 N _97689 _97688) = (term314 N _97689 _97688).
Proof. exact (MK_COMB (@lem7602358 N _97688 _97689) (@lem7602359 N _97688)). Qed.
Lemma lem7602361 {N : Type'} (_97689 : nat) (_97688 : N -> Prop) : (term307 N _97688 _97689) = (term314 N _97689 _97688).
Proof. exact (TRANS (@lem7602353 N _97689 _97688) (@lem7602360 N _97689 _97688)). Qed.
Lemma lem7602364 {A N : Type'} (_97689 : nat) (_97688 : N -> Prop) (h1 : term242 A N) : term314 N _97689 _97688.
Proof. exact (EQ_MP (@lem7602361 N _97689 _97688) (@lem7602350 A N _97688 _97689 h1)). Qed.
Lemma lem7602365 {A N : Type'} (_97689 : nat) (_97688 : N -> Prop) (h1 : term242 A N) : term314 N _97689 _97688.
Proof. exact (@lem7602364 A N _97689 _97688 h1). Qed.
Lemma lem7602366 {A N : Type'} (h1 : term242 A N) : term315 N.
Proof. exact (@lem7602365 A N (@dimindex N (@UNIV N)) (@UNIV N) h1). Qed.
Lemma lem7602369 {A N : Type'} (h1 : term242 A N) : @FINITE N (@UNIV N).
Proof. exact (@lem7602366 A N h1 (@lem7602321 A N h1)). Qed.
Lemma lem7602370 {A N : Type'} (h1 : term242 A N) : term257 N.
Proof. exact (fun h0 : term122 N => @lem7602369 A N h1). Qed.
Lemma lem7602372 (p : Prop) : (term258 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7602373 {N : Type'} : (term257 N) = (@FINITE N (@UNIV N)).
Proof. exact (@lem7602372 (@FINITE N (@UNIV N))). Qed.
Lemma lem7602374 {A N : Type'} (h1 : term242 A N) : @FINITE N (@UNIV N).
Proof. exact (EQ_MP (@lem7602373 N) (@lem7602370 A N h1)). Qed.
Lemma lem7602377 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7602379 {N : Type'} : (term122 N) = (term316 N).
Proof. exact (@lem7602377 (@FINITE N (@UNIV N))). Qed.
Lemma lem7602382 {A N : Type'} (h1 : term244 A N) : term316 N.
Proof. exact (EQ_MP (@lem7602379 N) (@lem7601454 A N h1)). Qed.
Lemma lem7602385 {A N : Type'} (h1 : term242 A N) (h2 : term244 A N) : False.
Proof. exact (@lem7602382 A N h2 (@lem7602374 A N h1)). Qed.
Lemma lem7602386 {A N : Type'} (h1 : term242 A N) (h2 : term244 A N) : term306.
Proof. exact (fun h0 : ~ False => @lem7602385 A N h1 h2). Qed.
Lemma lem7602388 (p : Prop) : (term258 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7602389 : term306 = False.
Proof. exact (@lem7602388 False). Qed.
Lemma lem7602390 {A N : Type'} (h1 : term242 A N) (h2 : term244 A N) : False.
Proof. exact (EQ_MP (@lem7602389) (@lem7602386 A N h1 h2)). Qed.
Lemma lem7602391 {A N : Type'} (h1 : term244 A N) : False.
Proof. exact (or_elim (@lem7600957 A N h1) (fun h0 : term238 A N => @lem7602225 A N h0 h1) (fun h0 : term242 A N => @lem7602390 A N h0 h1)). Qed.
Lemma lem7602392 {A N : Type'} (h1 : term233 A N) : False.
Proof. exact (or_elim (@lem7600933 A N h1) (fun h0 : term227 A N => @lem7601764 A N h0 h1) (fun h0 : term231 A N => @lem7602052 A N h1 h0)). Qed.
Lemma lem7602393 {A N : Type'} (h1 : term89 A N) : False.
Proof. exact (or_elim (@lem7600930 A N h1) (fun h0 : term233 A N => @lem7602392 A N h0) (fun h0 : term244 A N => @lem7602391 A N h0)). Qed.
Lemma lem7602394 {A N : Type'} (h1 : term89 A N) : (term89 A N) = False.
Proof. exact (prop_ext (fun h2 : term89 A N => @lem7602393 A N h1) (fun h2 : False => @lem7599040 A N h1)). Qed.
Lemma lem7602395 {A N : Type'} (h1 : term89 A N) : False.
Proof. exact (EQ_MP (@lem7602394 A N h1) (@lem7599040 A N h1)). Qed.
Lemma lem7602396 {A N : Type'} : term88 A N.
Proof. exact (fun h0 : term89 A N => @lem7602395 A N h0). Qed.
Lemma lem7602397 {A N : Type'} : term78 A N.
Proof. exact (EQ_MP (@lem7599039 A N) (@lem7602396 A N)). Qed.
Lemma lem7602398 {A N : Type'} : term6 A N.
Proof. exact (EQ_MP (@lem7599035 A N) (@lem7602397 A N)). Qed.
Lemma lem7602400 {A N : Type'} : term6 A N.
Proof. exact (@lem7598157 A N (@lem7602398 A N)). Qed.
Lemma lem7602401 {A N : Type'} (h1 : term3 N) : term15 A N.
Proof. exact (@lem7602400 A N (@lem7598135 N h1)). Qed.
Lemma lem7602402 {N : Type'} (h1 : term3 N) : term13 N.
Proof. exact (@lem7602401 Prop N h1 (@lem7590231 Prop)). Qed.
Lemma lem7602403 {N : Type'} (h1 : term3 N) : term10 N.
Proof. exact (@lem7602402 N h1 (@lem7598138 N)). Qed.
Lemma lem7602404 {N : Type'} (h1 : term3 N) : False.
Proof. exact (@lem7602403 N h1 (@lem7598136 N)). Qed.
Lemma lem7602405 {N : Type'} (h1 : term3 N) : (term3 N) = False.
Proof. exact (prop_ext (fun h2 : term3 N => @lem7602404 N h1) (fun h2 : False => @lem7598135 N h1)). Qed.
Lemma lem7602406 {N : Type'} (h1 : term3 N) : False.
Proof. exact (EQ_MP (@lem7602405 N h1) (@lem7598135 N h1)). Qed.
Lemma lem7602407 {N : Type'} : term2 N.
Proof. exact (fun h0 : term3 N => @lem7602406 N h0). Qed.
Lemma lem7602408 {N : Type'} : (term1 N) = (@FINITE N (@UNIV N)).
Proof. exact (EQ_MP (@lem7598134 N) (@lem7602407 N)). Qed.
