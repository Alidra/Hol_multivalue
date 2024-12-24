Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXISTS_PAIR_FUN_THM_term_abbrevs.
Require Import FORALL_PAIR_FUN_THM_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17646_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Lemma lem54242 {A B C : Type'} (P : type478 A B C) : term0 A B C P.
Proof. exact (@lem54241 A B C P). Qed.
Lemma lem54243 {A B C : Type'} (P : type478 A B C) : (term0 A B C P) = ((term1 A B C P) = (term2 A B C P)).
Proof. exact (eq_refl (term0 A B C P)). Qed.
Lemma lem54256 (p : Prop) : p = (term3 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem54257 {_5565 : Type'} (P : _5565 -> Prop) : ((term4 _5565 P) = (term5 _5565 P)) = (term6 _5565 P).
Proof. exact (@lem54256 ((term4 _5565 P) = (term5 _5565 P))). Qed.
Lemma lem54258 {_5565 : Type'} (P : _5565 -> Prop) : (term6 _5565 P) = ((term4 _5565 P) = (term5 _5565 P)).
Proof. exact (SYM (@lem54257 _5565 P)). Qed.
Lemma lem54259 {_5565 : Type'} (P : _5565 -> Prop) (h1 : term7 _5565 P) : term7 _5565 P.
Proof. exact (h1). Qed.
Lemma lem54262 {_5565 : Type'} (P : _5565 -> Prop) (h1 : term6 _5565 P) : term6 _5565 P.
Proof. exact (h1). Qed.
Lemma lem54263 {_5565 : Type'} (P : _5565 -> Prop) : term8 _5565 P.
Proof. exact (fun h0 : term6 _5565 P => @lem54262 _5565 P h0). Qed.
Lemma lem54264 {_5565 : Type'} (P : _5565 -> Prop) (h1 : term8 _5565 P) : term8 _5565 P.
Proof. exact (h1). Qed.
Lemma lem54265 {_5565 : Type'} (P : _5565 -> Prop) (h1 : term6 _5565 P) : term6 _5565 P.
Proof. exact (h1). Qed.
Lemma lem54266 {_5565 : Type'} (P : _5565 -> Prop) (h1 : term6 _5565 P) (h2 : term8 _5565 P) : term6 _5565 P.
Proof. exact (@lem54264 _5565 P h2 (@lem54265 _5565 P h1)). Qed.
Lemma lem54267 {_5565 : Type'} (P : _5565 -> Prop) (h1 : term6 _5565 P) : term9 _5565 P.
Proof. exact (fun h0 : term8 _5565 P => @lem54266 _5565 P h1 h0). Qed.
Lemma lem54268 {_5565 : Type'} (P : _5565 -> Prop) (h1 : term8 _5565 P) : term8 _5565 P.
Proof. exact (h1). Qed.
Lemma lem54269 {_5565 : Type'} (P : _5565 -> Prop) (h1 : term6 _5565 P) (h2 : term8 _5565 P) : term6 _5565 P.
Proof. exact (@lem54267 _5565 P h1 (@lem54268 _5565 P h2)). Qed.
Lemma lem54270 {_5565 : Type'} (P : _5565 -> Prop) (h1 : term8 _5565 P) : term8 _5565 P.
Proof. exact (fun h0 : term6 _5565 P => @lem54269 _5565 P h0 h1). Qed.
Lemma lem54271 {_5565 : Type'} (P : _5565 -> Prop) : term10 _5565 P.
Proof. exact (fun h0 : term8 _5565 P => @lem54270 _5565 P h0). Qed.
Lemma lem54274 {_5565 : Type'} (P : _5565 -> Prop) : term8 _5565 P.
Proof. exact (@lem54271 _5565 P (@lem54263 _5565 P)). Qed.
Lemma lem54275 {_5565 : Type'} (P : _5565 -> Prop) : term8 _5565 P.
Proof. exact (@lem54274 _5565 P). Qed.
Lemma lem54281 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem54282 {_5565 : Type'} (P : _5565 -> Prop) : (term6 _5565 P) = (term11 _5565 P).
Proof. exact (@lem54281 (term7 _5565 P)). Qed.
Lemma lem54284 (t : Prop) : (term12 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem54285 {_5565 : Type'} (P : _5565 -> Prop) : (term11 _5565 P) = ((term4 _5565 P) = (term5 _5565 P)).
Proof. exact (@lem54284 ((term4 _5565 P) = (term5 _5565 P))). Qed.
Lemma lem54286 {_5565 : Type'} (P : _5565 -> Prop) : (term6 _5565 P) = ((term4 _5565 P) = (term5 _5565 P)).
Proof. exact (TRANS (@lem54282 _5565 P) (@lem54285 _5565 P)). Qed.
Lemma lem54295 {_5565 : Type'} : (term13 _5565) = (term14 _5565).
Proof. exact (fun_ext (fun P : _5565 -> Prop => @lem54286 _5565 P)). Qed.
Lemma lem54296 {_5565 : Type'} : (@all (_5565 -> Prop)) = (@all (_5565 -> Prop)).
Proof. exact (eq_refl (@all (_5565 -> Prop))). Qed.
Lemma lem54305 {_5565 : Type'} : (term15 _5565) = (term16 _5565).
Proof. exact (MK_COMB (@lem54296 _5565) (@lem54295 _5565)). Qed.
Lemma lem54308 {_5565 : Type'} (P : _5565 -> Prop) (x : _5565) : (term17 _5565 P x) = (term17 _5565 P x).
Proof. exact (eq_refl (term17 _5565 P x)). Qed.
Lemma lem54309 {_5565 : Type'} (P : _5565 -> Prop) : (term18 _5565 P) = (term18 _5565 P).
Proof. exact (fun_ext (fun x : _5565 => @lem54308 _5565 P x)). Qed.
Lemma lem54310 {_5565 : Type'} : (@all _5565) = (@all _5565).
Proof. exact (eq_refl (@all _5565)). Qed.
Lemma lem54311 {_5565 : Type'} (P : _5565 -> Prop) : (term19 _5565 P) = (term19 _5565 P).
Proof. exact (MK_COMB (@lem54310 _5565) (@lem54309 _5565 P)). Qed.
Lemma lem54312 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem54313 {_5565 : Type'} (P : _5565 -> Prop) : (term5 _5565 P) = (term5 _5565 P).
Proof. exact (MK_COMB (@lem54312) (@lem54311 _5565 P)). Qed.
Lemma lem54314 {_5565 : Type'} (P : _5565 -> Prop) (x : _5565) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem54315 {_5565 : Type'} (P : _5565 -> Prop) : (term20 _5565 P) = (term20 _5565 P).
Proof. exact (fun_ext (fun x : _5565 => @lem54314 _5565 P x)). Qed.
Lemma lem54316 {_5565 : Type'} : (@ex _5565) = (@ex _5565).
Proof. exact (eq_refl (@ex _5565)). Qed.
Lemma lem54317 {_5565 : Type'} (P : _5565 -> Prop) : (term4 _5565 P) = (term4 _5565 P).
Proof. exact (MK_COMB (@lem54316 _5565) (@lem54315 _5565 P)). Qed.
Lemma lem54318 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem54319 {_5565 : Type'} (P : _5565 -> Prop) : (term21 _5565 P) = (term21 _5565 P).
Proof. exact (MK_COMB (@lem54318) (@lem54317 _5565 P)). Qed.
Lemma lem54320 {_5565 : Type'} (P : _5565 -> Prop) : ((term4 _5565 P) = (term5 _5565 P)) = ((term4 _5565 P) = (term5 _5565 P)).
Proof. exact (MK_COMB (@lem54319 _5565 P) (@lem54313 _5565 P)). Qed.
Lemma lem54321 {_5565 : Type'} : (term14 _5565) = (term14 _5565).
Proof. exact (fun_ext (fun P : _5565 -> Prop => @lem54320 _5565 P)). Qed.
Lemma lem54322 {_5565 : Type'} : (@all (_5565 -> Prop)) = (@all (_5565 -> Prop)).
Proof. exact (eq_refl (@all (_5565 -> Prop))). Qed.
Lemma lem54323 {_5565 : Type'} : (term16 _5565) = (term16 _5565).
Proof. exact (MK_COMB (@lem54322 _5565) (@lem54321 _5565)). Qed.
Lemma lem54344 {_5565 : Type'} : (term15 _5565) = (term16 _5565).
Proof. exact (TRANS (@lem54305 _5565) (@lem54323 _5565)). Qed.
Lemma lem54345 {_5565 : Type'} : (term16 _5565) = (term15 _5565).
Proof. exact (SYM (@lem54344 _5565)). Qed.
Lemma lem54347 (p : Prop) : p = (term3 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem54348 {_5565 : Type'} (P : _5565 -> Prop) : ((term4 _5565 P) = (term5 _5565 P)) = (term6 _5565 P).
Proof. exact (@lem54347 ((term4 _5565 P) = (term5 _5565 P))). Qed.
Lemma lem54349 {_5565 : Type'} (P : _5565 -> Prop) : (term6 _5565 P) = ((term4 _5565 P) = (term5 _5565 P)).
Proof. exact (SYM (@lem54348 _5565 P)). Qed.
Lemma lem54350 {_5565 : Type'} (P : _5565 -> Prop) (h1 : term7 _5565 P) : term7 _5565 P.
Proof. exact (h1). Qed.
Lemma lem54352 {_5565 : Type'} (P : _5565 -> Prop) (x : _5565) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem54353 {_5565 : Type'} (P : _5565 -> Prop) : (term22 _5565 P) = (term19 _5565 P).
Proof. exact (@lem18394 _5565 P). Qed.
Lemma lem54354 {_5565 : Type'} (P : _5565 -> Prop) : (term23 _5565 P) = (term24 _5565 P).
Proof. exact (@lem54353 _5565 (term20 _5565 P)). Qed.
Lemma lem54355 {_5565 : Type'} (P : _5565 -> Prop) (x : _5565) : (term25 _5565 P x) = (P x).
Proof. exact (eq_refl (term25 _5565 P x)). Qed.
Lemma lem54356 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem54358 {_5565 : Type'} (P : _5565 -> Prop) (x : _5565) : (term26 _5565 P x) = (term17 _5565 P x).
Proof. exact (MK_COMB (@lem54356) (@lem54355 _5565 P x)). Qed.
Lemma lem54359 {_5565 : Type'} (P : _5565 -> Prop) : (term27 _5565 P) = (term18 _5565 P).
Proof. exact (fun_ext (fun x : _5565 => @lem54358 _5565 P x)). Qed.
Lemma lem54360 {_5565 : Type'} : (@all _5565) = (@all _5565).
Proof. exact (eq_refl (@all _5565)). Qed.
Lemma lem54361 {_5565 : Type'} (P : _5565 -> Prop) : (term24 _5565 P) = (term19 _5565 P).
Proof. exact (MK_COMB (@lem54360 _5565) (@lem54359 _5565 P)). Qed.
Lemma lem54362 {_5565 : Type'} (P : _5565 -> Prop) : (term23 _5565 P) = (term19 _5565 P).
Proof. exact (TRANS (@lem54354 _5565 P) (@lem54361 _5565 P)). Qed.
Lemma lem54363 {_5565 : Type'} (P : _5565 -> Prop) : (term20 _5565 P) = (term20 _5565 P).
Proof. exact (fun_ext (fun x : _5565 => @lem54352 _5565 P x)). Qed.
Lemma lem54364 {_5565 : Type'} : (@ex _5565) = (@ex _5565).
Proof. exact (eq_refl (@ex _5565)). Qed.
Lemma lem54365 {_5565 : Type'} (P : _5565 -> Prop) : (term4 _5565 P) = (term4 _5565 P).
Proof. exact (MK_COMB (@lem54364 _5565) (@lem54363 _5565 P)). Qed.
Lemma lem54366 {_5565 : Type'} (P : _5565 -> Prop) (x : _5565) : (term17 _5565 P x) = (term17 _5565 P x).
Proof. exact (eq_refl (term17 _5565 P x)). Qed.
Lemma lem54369 {_5565 : Type'} (P : _5565 -> Prop) (x : _5565) : (term28 _5565 P x) = (P x).
Proof. exact (@lem16933 (P x)). Qed.
Lemma lem54370 {_5565 : Type'} (P : _5565 -> Prop) : (term29 _5565 P) = (term30 _5565 P).
Proof. exact (@lem18392 _5565 P). Qed.
Lemma lem54371 {_5565 : Type'} (P : _5565 -> Prop) : (term5 _5565 P) = (term31 _5565 P).
Proof. exact (@lem54370 _5565 (term18 _5565 P)). Qed.
Lemma lem54372 {_5565 : Type'} (P : _5565 -> Prop) (x : _5565) : (term32 _5565 P x) = (term17 _5565 P x).
Proof. exact (eq_refl (term32 _5565 P x)). Qed.
Lemma lem54373 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem54374 {_5565 : Type'} (P : _5565 -> Prop) (x : _5565) : (term33 _5565 P x) = (term28 _5565 P x).
Proof. exact (MK_COMB (@lem54373) (@lem54372 _5565 P x)). Qed.
Lemma lem54375 {_5565 : Type'} (P : _5565 -> Prop) (x : _5565) : (term33 _5565 P x) = (P x).
Proof. exact (TRANS (@lem54374 _5565 P x) (@lem54369 _5565 P x)). Qed.
Lemma lem54376 {_5565 : Type'} (P : _5565 -> Prop) : (term34 _5565 P) = (term20 _5565 P).
Proof. exact (fun_ext (fun x : _5565 => @lem54375 _5565 P x)). Qed.
Lemma lem54377 {_5565 : Type'} : (@ex _5565) = (@ex _5565).
Proof. exact (eq_refl (@ex _5565)). Qed.
Lemma lem54378 {_5565 : Type'} (P : _5565 -> Prop) : (term31 _5565 P) = (term4 _5565 P).
Proof. exact (MK_COMB (@lem54377 _5565) (@lem54376 _5565 P)). Qed.
Lemma lem54379 {_5565 : Type'} (P : _5565 -> Prop) : (term5 _5565 P) = (term4 _5565 P).
Proof. exact (TRANS (@lem54371 _5565 P) (@lem54378 _5565 P)). Qed.
Lemma lem54380 {_5565 : Type'} (P : _5565 -> Prop) : (term18 _5565 P) = (term18 _5565 P).
Proof. exact (fun_ext (fun x : _5565 => @lem54366 _5565 P x)). Qed.
Lemma lem54381 {_5565 : Type'} : (@all _5565) = (@all _5565).
Proof. exact (eq_refl (@all _5565)). Qed.
Lemma lem54382 {_5565 : Type'} (P : _5565 -> Prop) : (term19 _5565 P) = (term19 _5565 P).
Proof. exact (MK_COMB (@lem54381 _5565) (@lem54380 _5565 P)). Qed.
Lemma lem54383 {_5565 : Type'} (P : _5565 -> Prop) : (term35 _5565 P) = (term19 _5565 P).
Proof. exact (@lem16933 (term19 _5565 P)). Qed.
Lemma lem54384 {_5565 : Type'} (P : _5565 -> Prop) : (term35 _5565 P) = (term19 _5565 P).
Proof. exact (TRANS (@lem54383 _5565 P) (@lem54382 _5565 P)). Qed.
Lemma lem54385 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem54386 {_5565 : Type'} (P : _5565 -> Prop) : (term36 _5565 P) = (term37 _5565 P).
Proof. exact (MK_COMB (@lem54385) (@lem54362 _5565 P)). Qed.
Lemma lem54387 {_5565 : Type'} (P : _5565 -> Prop) : (term38 _5565 P) = (term39 _5565 P).
Proof. exact (MK_COMB (@lem54386 _5565 P) (@lem54379 _5565 P)). Qed.
Lemma lem54388 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem54389 {_5565 : Type'} (P : _5565 -> Prop) : (term40 _5565 P) = (term40 _5565 P).
Proof. exact (MK_COMB (@lem54388) (@lem54365 _5565 P)). Qed.
Lemma lem54390 {_5565 : Type'} (P : _5565 -> Prop) : (term41 _5565 P) = (term42 _5565 P).
Proof. exact (MK_COMB (@lem54389 _5565 P) (@lem54384 _5565 P)). Qed.
Lemma lem54391 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem54392 {_5565 : Type'} (P : _5565 -> Prop) : (term43 _5565 P) = (term44 _5565 P).
Proof. exact (MK_COMB (@lem54391) (@lem54390 _5565 P)). Qed.
Lemma lem54393 {_5565 : Type'} (P : _5565 -> Prop) : (term45 _5565 P) = (term46 _5565 P).
Proof. exact (MK_COMB (@lem54392 _5565 P) (@lem54387 _5565 P)). Qed.
Lemma lem54394 {_5565 : Type'} (P : _5565 -> Prop) : (term7 _5565 P) = (term45 _5565 P).
Proof. exact (@lem17646 (term4 _5565 P) (term5 _5565 P)). Qed.
Lemma lem54395 {_5565 : Type'} (P : _5565 -> Prop) : (term7 _5565 P) = (term46 _5565 P).
Proof. exact (TRANS (@lem54394 _5565 P) (@lem54393 _5565 P)). Qed.
Lemma lem54414 {A : Type'} (P : A -> Prop) (Q : Prop) : (term47 A P Q) = (term48 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem54415 {_5565 : Type'} (P : _5565 -> Prop) (Q : Prop) : (term47 _5565 P Q) = (term48 _5565 P Q).
Proof. exact (@lem54414 _5565 P Q). Qed.
Lemma lem54416 {_5565 : Type'} (P : _5565 -> Prop) : (term42 _5565 P) = (term49 _5565 P).
Proof. exact (@lem54415 _5565 P (term19 _5565 P)). Qed.
Lemma lem54417 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem54418 {_5565 : Type'} (P : _5565 -> Prop) : (term44 _5565 P) = (term50 _5565 P).
Proof. exact (MK_COMB (@lem54417) (@lem54416 _5565 P)). Qed.
Lemma lem54420 {A : Type'} (P : Prop) (Q : A -> Prop) : (term51 A P Q) = (term52 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem54421 {_5565 : Type'} (P : Prop) (Q : _5565 -> Prop) : (term51 _5565 P Q) = (term52 _5565 P Q).
Proof. exact (@lem54420 _5565 P Q). Qed.
Lemma lem54422 {_5565 : Type'} (P : _5565 -> Prop) : (term39 _5565 P) = (term53 _5565 P).
Proof. exact (@lem54421 _5565 (term19 _5565 P) P). Qed.
Lemma lem54423 {_5565 : Type'} (P : _5565 -> Prop) : (term46 _5565 P) = (term54 _5565 P).
Proof. exact (MK_COMB (@lem54418 _5565 P) (@lem54422 _5565 P)). Qed.
Lemma lem54425 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term55 A P Q) = (term56 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem54426 {_5565 : Type'} (P : _5565 -> Prop) (Q : _5565 -> Prop) : (term55 _5565 P Q) = (term56 _5565 P Q).
Proof. exact (@lem54425 _5565 P Q). Qed.
Lemma lem54427 {_5565 : Type'} (P : _5565 -> Prop) : (term57 _5565 P) = (term58 _5565 P).
Proof. exact (@lem54426 _5565 (term59 _5565 P) (term60 _5565 P)). Qed.
Lemma lem54428 {_5565 : Type'} (x : _5565) (P : _5565 -> Prop) : (term61 _5565 P x) = (term62 _5565 x P).
Proof. exact (eq_refl (term61 _5565 P x)). Qed.
Lemma lem54429 {_5565 : Type'} (P : _5565 -> Prop) : (term63 _5565 P) = (term59 _5565 P).
Proof. exact (fun_ext (fun x : _5565 => @lem54428 _5565 x P)). Qed.
Lemma lem54430 {_5565 : Type'} : (@ex _5565) = (@ex _5565).
Proof. exact (eq_refl (@ex _5565)). Qed.
Lemma lem54431 {_5565 : Type'} (P : _5565 -> Prop) : (term64 _5565 P) = (term49 _5565 P).
Proof. exact (MK_COMB (@lem54430 _5565) (@lem54429 _5565 P)). Qed.
Lemma lem54432 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem54433 {_5565 : Type'} (P : _5565 -> Prop) : (term65 _5565 P) = (term50 _5565 P).
Proof. exact (MK_COMB (@lem54432) (@lem54431 _5565 P)). Qed.
Lemma lem54434 {_5565 : Type'} (P : _5565 -> Prop) (x : _5565) : (term66 _5565 P x) = (term67 _5565 P x).
Proof. exact (eq_refl (term66 _5565 P x)). Qed.
Lemma lem54435 {_5565 : Type'} (P : _5565 -> Prop) : (term68 _5565 P) = (term60 _5565 P).
Proof. exact (fun_ext (fun x : _5565 => @lem54434 _5565 P x)). Qed.
Lemma lem54436 {_5565 : Type'} : (@ex _5565) = (@ex _5565).
Proof. exact (eq_refl (@ex _5565)). Qed.
Lemma lem54437 {_5565 : Type'} (P : _5565 -> Prop) : (term69 _5565 P) = (term53 _5565 P).
Proof. exact (MK_COMB (@lem54436 _5565) (@lem54435 _5565 P)). Qed.
Lemma lem54438 {_5565 : Type'} (P : _5565 -> Prop) : (term57 _5565 P) = (term54 _5565 P).
Proof. exact (MK_COMB (@lem54433 _5565 P) (@lem54437 _5565 P)). Qed.
Lemma lem54439 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem54440 {_5565 : Type'} (P : _5565 -> Prop) : (term70 _5565 P) = (term71 _5565 P).
Proof. exact (MK_COMB (@lem54439) (@lem54438 _5565 P)). Qed.
Lemma lem54441 {_5565 : Type'} (x : _5565) (P : _5565 -> Prop) : (term61 _5565 P x) = (term62 _5565 x P).
Proof. exact (eq_refl (term61 _5565 P x)). Qed.
Lemma lem54442 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem54443 {_5565 : Type'} (x : _5565) (P : _5565 -> Prop) : (term72 _5565 P x) = (term73 _5565 x P).
Proof. exact (MK_COMB (@lem54442) (@lem54441 _5565 x P)). Qed.
Lemma lem54444 {_5565 : Type'} (P : _5565 -> Prop) (x : _5565) : (term66 _5565 P x) = (term67 _5565 P x).
Proof. exact (eq_refl (term66 _5565 P x)). Qed.
Lemma lem54445 {_5565 : Type'} (P : _5565 -> Prop) (x : _5565) : (term74 _5565 P x) = (term75 _5565 P x).
Proof. exact (MK_COMB (@lem54443 _5565 x P) (@lem54444 _5565 P x)). Qed.
Lemma lem54446 {_5565 : Type'} (P : _5565 -> Prop) : (term76 _5565 P) = (term77 _5565 P).
Proof. exact (fun_ext (fun x : _5565 => @lem54445 _5565 P x)). Qed.
Lemma lem54447 {_5565 : Type'} : (@ex _5565) = (@ex _5565).
Proof. exact (eq_refl (@ex _5565)). Qed.
Lemma lem54448 {_5565 : Type'} (P : _5565 -> Prop) : (term58 _5565 P) = (term78 _5565 P).
Proof. exact (MK_COMB (@lem54447 _5565) (@lem54446 _5565 P)). Qed.
Lemma lem54449 {_5565 : Type'} (P : _5565 -> Prop) : ((term57 _5565 P) = (term58 _5565 P)) = ((term54 _5565 P) = (term78 _5565 P)).
Proof. exact (MK_COMB (@lem54440 _5565 P) (@lem54448 _5565 P)). Qed.
Lemma lem54450 {_5565 : Type'} (P : _5565 -> Prop) : (term54 _5565 P) = (term78 _5565 P).
Proof. exact (EQ_MP (@lem54449 _5565 P) (@lem54427 _5565 P)). Qed.
Lemma lem54452 {_5565 : Type'} (P : _5565 -> Prop) : (term46 _5565 P) = (term78 _5565 P).
Proof. exact (TRANS (@lem54423 _5565 P) (@lem54450 _5565 P)). Qed.
Lemma lem54453 {_5565 : Type'} (P : _5565 -> Prop) : (term7 _5565 P) = (term78 _5565 P).
Proof. exact (TRANS (@lem54395 _5565 P) (@lem54452 _5565 P)). Qed.
Lemma lem54454 {_5565 : Type'} (P : _5565 -> Prop) (h1 : term7 _5565 P) : term78 _5565 P.
Proof. exact (EQ_MP (@lem54453 _5565 P) (@lem54350 _5565 P h1)). Qed.
Lemma lem54455 {_5565 : Type'} (P : _5565 -> Prop) (x : _5565) (h1 : term75 _5565 P x) : term75 _5565 P x.
Proof. exact (h1). Qed.
Lemma lem54458 {_5565 : Type'} (P : _5565 -> Prop) (x : _5565) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem54463 {_5565 : Type'} (P : _5565 -> Prop) (x : _5565) : (term17 _5565 P x) = (term17 _5565 P x).
Proof. exact (eq_refl (term17 _5565 P x)). Qed.
Lemma lem54464 {_5565 : Type'} (P : _5565 -> Prop) : (term18 _5565 P) = (term18 _5565 P).
Proof. exact (fun_ext (fun x : _5565 => @lem54463 _5565 P x)). Qed.
Lemma lem54465 {_5565 : Type'} : (@all _5565) = (@all _5565).
Proof. exact (eq_refl (@all _5565)). Qed.
Lemma lem54466 {_5565 : Type'} (P : _5565 -> Prop) : (term19 _5565 P) = (term19 _5565 P).
Proof. exact (MK_COMB (@lem54465 _5565) (@lem54464 _5565 P)). Qed.
Lemma lem54467 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem54468 {_5565 : Type'} (P : _5565 -> Prop) : (term37 _5565 P) = (term37 _5565 P).
Proof. exact (MK_COMB (@lem54467) (@lem54466 _5565 P)). Qed.
Lemma lem54469 {_5565 : Type'} (P : _5565 -> Prop) (x : _5565) : (term67 _5565 P x) = (term67 _5565 P x).
Proof. exact (MK_COMB (@lem54468 _5565 P) (@lem54458 _5565 P x)). Qed.
Lemma lem54474 {_5565 : Type'} (P : _5565 -> Prop) (x : _5565) : (term17 _5565 P x) = (term17 _5565 P x).
Proof. exact (eq_refl (term17 _5565 P x)). Qed.
Lemma lem54475 {_5565 : Type'} (P : _5565 -> Prop) : (term18 _5565 P) = (term18 _5565 P).
Proof. exact (fun_ext (fun x : _5565 => @lem54474 _5565 P x)). Qed.
Lemma lem54476 {_5565 : Type'} : (@all _5565) = (@all _5565).
Proof. exact (eq_refl (@all _5565)). Qed.
Lemma lem54477 {_5565 : Type'} (P : _5565 -> Prop) : (term19 _5565 P) = (term19 _5565 P).
Proof. exact (MK_COMB (@lem54476 _5565) (@lem54475 _5565 P)). Qed.
Lemma lem54482 {_5565 : Type'} (P : _5565 -> Prop) (x : _5565) : (term79 _5565 P x) = (term79 _5565 P x).
Proof. exact (eq_refl (term79 _5565 P x)). Qed.
Lemma lem54483 {_5565 : Type'} (x : _5565) (P : _5565 -> Prop) : (term62 _5565 x P) = (term62 _5565 x P).
Proof. exact (MK_COMB (@lem54482 _5565 P x) (@lem54477 _5565 P)). Qed.
Lemma lem54484 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem54485 {_5565 : Type'} (x : _5565) (P : _5565 -> Prop) : (term73 _5565 x P) = (term73 _5565 x P).
Proof. exact (MK_COMB (@lem54484) (@lem54483 _5565 x P)). Qed.
Lemma lem54486 {_5565 : Type'} (P : _5565 -> Prop) (x : _5565) : (term75 _5565 P x) = (term75 _5565 P x).
Proof. exact (MK_COMB (@lem54485 _5565 x P) (@lem54469 _5565 P x)). Qed.
Lemma lem54487 {_5565 : Type'} (P : _5565 -> Prop) (x : _5565) (h1 : term75 _5565 P x) : term75 _5565 P x.
Proof. exact (EQ_MP (@lem54486 _5565 P x) (@lem54455 _5565 P x h1)). Qed.
Lemma lem54488 {_5565 : Type'} (x : _5565) (P : _5565 -> Prop) (h1 : term62 _5565 x P) : term62 _5565 x P.
Proof. exact (h1). Qed.
Lemma lem54489 {_5565 : Type'} (P : _5565 -> Prop) (x : _5565) (h1 : term67 _5565 P x) : term67 _5565 P x.
Proof. exact (h1). Qed.
Lemma lem54490 {_5565 : Type'} (x : _5565) (P : _5565 -> Prop) (h1 : term62 _5565 x P) : term19 _5565 P.
Proof. exact (proj2 (@lem54488 _5565 x P h1)). Qed.
Lemma lem54493 {_5565 : Type'} (P : _5565 -> Prop) (x : _5565) (h1 : term67 _5565 P x) : term19 _5565 P.
Proof. exact (proj1 (@lem54489 _5565 P x h1)). Qed.
Lemma lem54499 {_5565 : Type'} (P : _5565 -> Prop) (x : _5565) : (term17 _5565 P x) = (term17 _5565 P x).
Proof. exact (eq_refl (term17 _5565 P x)). Qed.
Lemma lem54500 {_5565 : Type'} (P : _5565 -> Prop) : (term18 _5565 P) = (term18 _5565 P).
Proof. exact (fun_ext (fun x : _5565 => @lem54499 _5565 P x)). Qed.
Lemma lem54501 {_5565 : Type'} : (@all _5565) = (@all _5565).
Proof. exact (eq_refl (@all _5565)). Qed.
Lemma lem54503 {_5565 : Type'} (P : _5565 -> Prop) : (term19 _5565 P) = (term19 _5565 P).
Proof. exact (MK_COMB (@lem54501 _5565) (@lem54500 _5565 P)). Qed.
Lemma lem54504 {_5565 : Type'} (x : _5565) (P : _5565 -> Prop) (h1 : term62 _5565 x P) : term19 _5565 P.
Proof. exact (EQ_MP (@lem54503 _5565 P) (@lem54490 _5565 x P h1)). Qed.
Lemma lem54506 {_5565 : Type'} (P : _5565 -> Prop) (x : _5565) : (term17 _5565 P x) = (term17 _5565 P x).
Proof. exact (eq_refl (term17 _5565 P x)). Qed.
Lemma lem54507 {_5565 : Type'} (P : _5565 -> Prop) : (term18 _5565 P) = (term18 _5565 P).
Proof. exact (fun_ext (fun x : _5565 => @lem54506 _5565 P x)). Qed.
Lemma lem54508 {_5565 : Type'} : (@all _5565) = (@all _5565).
Proof. exact (eq_refl (@all _5565)). Qed.
Lemma lem54510 {_5565 : Type'} (P : _5565 -> Prop) : (term19 _5565 P) = (term19 _5565 P).
Proof. exact (MK_COMB (@lem54508 _5565) (@lem54507 _5565 P)). Qed.
Lemma lem54511 {_5565 : Type'} (P : _5565 -> Prop) (x : _5565) (h1 : term67 _5565 P x) : term19 _5565 P.
Proof. exact (EQ_MP (@lem54510 _5565 P) (@lem54493 _5565 P x h1)). Qed.
Lemma lem54516 {_5565 : Type'} (_1512 : _5565) (x : _5565) (P : _5565 -> Prop) (h1 : term62 _5565 x P) : term32 _5565 P _1512.
Proof. exact (@lem54504 _5565 x P h1 _1512). Qed.
Lemma lem54517 {_5565 : Type'} (P : _5565 -> Prop) (_1512 : _5565) : (term32 _5565 P _1512) = (term17 _5565 P _1512).
Proof. exact (eq_refl (term32 _5565 P _1512)). Qed.
Lemma lem54519 {_5565 : Type'} (_1513 : _5565) (P : _5565 -> Prop) (x : _5565) (h1 : term67 _5565 P x) : term32 _5565 P _1513.
Proof. exact (@lem54511 _5565 P x h1 _1513). Qed.
Lemma lem54520 {_5565 : Type'} (P : _5565 -> Prop) (_1513 : _5565) : (term32 _5565 P _1513) = (term17 _5565 P _1513).
Proof. exact (eq_refl (term32 _5565 P _1513)). Qed.
Lemma lem54525 {_5565 : Type'} (_1512 : _5565) (x : _5565) (P : _5565 -> Prop) (h1 : term62 _5565 x P) : term17 _5565 P _1512.
Proof. exact (EQ_MP (@lem54517 _5565 P _1512) (@lem54516 _5565 _1512 x P h1)). Qed.
Lemma lem54527 {_5565 : Type'} (_1513 : _5565) (P : _5565 -> Prop) (x : _5565) (h1 : term67 _5565 P x) : term17 _5565 P _1513.
Proof. exact (EQ_MP (@lem54520 _5565 P _1513) (@lem54519 _5565 _1513 P x h1)). Qed.
Lemma lem54531 {_5565 : Type'} (x : _5565) (P : _5565 -> Prop) (h1 : term62 _5565 x P) : P x.
Proof. exact (proj1 (@lem54488 _5565 x P h1)). Qed.
Lemma lem54532 {_5565 : Type'} (x : _5565) (P : _5565 -> Prop) (h1 : term62 _5565 x P) : term80 _5565 P x.
Proof. exact (fun h0 : term17 _5565 P x => @lem54531 _5565 x P h1). Qed.
Lemma lem54534 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem54535 {_5565 : Type'} (P : _5565 -> Prop) (x : _5565) : (term80 _5565 P x) = (P x).
Proof. exact (@lem54534 (P x)). Qed.
Lemma lem54536 {_5565 : Type'} (x : _5565) (P : _5565 -> Prop) (h1 : term62 _5565 x P) : P x.
Proof. exact (EQ_MP (@lem54535 _5565 P x) (@lem54532 _5565 x P h1)). Qed.
Lemma lem54539 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem54541 {_5565 : Type'} (P : _5565 -> Prop) (_1512 : _5565) : (term17 _5565 P _1512) = (term82 _5565 P _1512).
Proof. exact (@lem54539 (P _1512)). Qed.
Lemma lem54544 {_5565 : Type'} (_1512 : _5565) (x : _5565) (P : _5565 -> Prop) (h1 : term62 _5565 x P) : term82 _5565 P _1512.
Proof. exact (EQ_MP (@lem54541 _5565 P _1512) (@lem54525 _5565 _1512 x P h1)). Qed.
Lemma lem54545 {_5565 : Type'} (_1512 : _5565) (x : _5565) (P : _5565 -> Prop) (h1 : term62 _5565 x P) : term82 _5565 P _1512.
Proof. exact (@lem54544 _5565 _1512 x P h1). Qed.
Lemma lem54546 {_5565 : Type'} (x : _5565) (P : _5565 -> Prop) (h1 : term62 _5565 x P) : term82 _5565 P x.
Proof. exact (@lem54545 _5565 x x P h1). Qed.
Lemma lem54549 {_5565 : Type'} (x : _5565) (P : _5565 -> Prop) (h1 : term62 _5565 x P) : False.
Proof. exact (@lem54546 _5565 x P h1 (@lem54536 _5565 x P h1)). Qed.
Lemma lem54550 {_5565 : Type'} (x : _5565) (P : _5565 -> Prop) (h1 : term62 _5565 x P) : term83.
Proof. exact (fun h0 : ~ False => @lem54549 _5565 x P h1). Qed.
Lemma lem54552 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem54553 : term83 = False.
Proof. exact (@lem54552 False). Qed.
Lemma lem54554 {_5565 : Type'} (x : _5565) (P : _5565 -> Prop) (h1 : term62 _5565 x P) : False.
Proof. exact (EQ_MP (@lem54553) (@lem54550 _5565 x P h1)). Qed.
Lemma lem54556 {_5565 : Type'} (P : _5565 -> Prop) (x : _5565) (h1 : term67 _5565 P x) : P x.
Proof. exact (proj2 (@lem54489 _5565 P x h1)). Qed.
Lemma lem54557 {_5565 : Type'} (P : _5565 -> Prop) (x : _5565) (h1 : term67 _5565 P x) : term80 _5565 P x.
Proof. exact (fun h0 : term17 _5565 P x => @lem54556 _5565 P x h1). Qed.
Lemma lem54559 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem54560 {_5565 : Type'} (P : _5565 -> Prop) (x : _5565) : (term80 _5565 P x) = (P x).
Proof. exact (@lem54559 (P x)). Qed.
Lemma lem54561 {_5565 : Type'} (P : _5565 -> Prop) (x : _5565) (h1 : term67 _5565 P x) : P x.
Proof. exact (EQ_MP (@lem54560 _5565 P x) (@lem54557 _5565 P x h1)). Qed.
Lemma lem54564 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem54566 {_5565 : Type'} (P : _5565 -> Prop) (_1513 : _5565) : (term17 _5565 P _1513) = (term82 _5565 P _1513).
Proof. exact (@lem54564 (P _1513)). Qed.
Lemma lem54569 {_5565 : Type'} (_1513 : _5565) (P : _5565 -> Prop) (x : _5565) (h1 : term67 _5565 P x) : term82 _5565 P _1513.
Proof. exact (EQ_MP (@lem54566 _5565 P _1513) (@lem54527 _5565 _1513 P x h1)). Qed.
Lemma lem54570 {_5565 : Type'} (_1513 : _5565) (P : _5565 -> Prop) (x : _5565) (h1 : term67 _5565 P x) : term82 _5565 P _1513.
Proof. exact (@lem54569 _5565 _1513 P x h1). Qed.
Lemma lem54571 {_5565 : Type'} (P : _5565 -> Prop) (x : _5565) (h1 : term67 _5565 P x) : term82 _5565 P x.
Proof. exact (@lem54570 _5565 x P x h1). Qed.
Lemma lem54574 {_5565 : Type'} (P : _5565 -> Prop) (x : _5565) (h1 : term67 _5565 P x) : False.
Proof. exact (@lem54571 _5565 P x h1 (@lem54561 _5565 P x h1)). Qed.
Lemma lem54575 {_5565 : Type'} (P : _5565 -> Prop) (x : _5565) (h1 : term67 _5565 P x) : term83.
Proof. exact (fun h0 : ~ False => @lem54574 _5565 P x h1). Qed.
Lemma lem54577 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem54578 : term83 = False.
Proof. exact (@lem54577 False). Qed.
Lemma lem54579 {_5565 : Type'} (P : _5565 -> Prop) (x : _5565) (h1 : term67 _5565 P x) : False.
Proof. exact (EQ_MP (@lem54578) (@lem54575 _5565 P x h1)). Qed.
Lemma lem54580 {_5565 : Type'} (P : _5565 -> Prop) (x : _5565) (h1 : term75 _5565 P x) : False.
Proof. exact (or_elim (@lem54487 _5565 P x h1) (fun h0 : term62 _5565 x P => @lem54554 _5565 x P h0) (fun h0 : term67 _5565 P x => @lem54579 _5565 P x h0)). Qed.
Lemma lem54581 {_5565 : Type'} (P : _5565 -> Prop) (x : _5565) (h1 : term75 _5565 P x) : (term75 _5565 P x) = False.
Proof. exact (prop_ext (fun h2 : term75 _5565 P x => @lem54580 _5565 P x h1) (fun h2 : False => @lem54487 _5565 P x h1)). Qed.
Lemma lem54582 {_5565 : Type'} (P : _5565 -> Prop) (x : _5565) (h1 : term75 _5565 P x) : False.
Proof. exact (EQ_MP (@lem54581 _5565 P x h1) (@lem54487 _5565 P x h1)). Qed.
Lemma lem54583 {_5565 : Type'} (P : _5565 -> Prop) (h1 : term7 _5565 P) : False.
Proof. exact (ex_elim (@lem54454 _5565 P h1) (fun x : _5565 => fun h0 : term77 _5565 P x => @lem54582 _5565 P x h0)). Qed.
Lemma lem54584 {_5565 : Type'} (P : _5565 -> Prop) (h1 : term7 _5565 P) : (term7 _5565 P) = False.
Proof. exact (prop_ext (fun h2 : term7 _5565 P => @lem54583 _5565 P h1) (fun h2 : False => @lem54350 _5565 P h1)). Qed.
Lemma lem54585 {_5565 : Type'} (P : _5565 -> Prop) (h1 : term7 _5565 P) : False.
Proof. exact (EQ_MP (@lem54584 _5565 P h1) (@lem54350 _5565 P h1)). Qed.
Lemma lem54586 {_5565 : Type'} (P : _5565 -> Prop) : term6 _5565 P.
Proof. exact (fun h0 : term7 _5565 P => @lem54585 _5565 P h0). Qed.
Lemma lem54587 {_5565 : Type'} (P : _5565 -> Prop) : (term4 _5565 P) = (term5 _5565 P).
Proof. exact (EQ_MP (@lem54349 _5565 P) (@lem54586 _5565 P)). Qed.
Lemma lem54592 {_5565 : Type'} : term16 _5565.
Proof. exact (fun P : _5565 -> Prop => @lem54587 _5565 P). Qed.
Lemma lem54593 {_5565 : Type'} : term15 _5565.
Proof. exact (EQ_MP (@lem54345 _5565) (@lem54592 _5565)). Qed.
Lemma lem54594 {_5565 : Type'} (P : _5565 -> Prop) : term84 _5565 P.
Proof. exact (@lem54593 _5565 P). Qed.
Lemma lem54595 {_5565 : Type'} (P : _5565 -> Prop) : (term84 _5565 P) = (term6 _5565 P).
Proof. exact (eq_refl (term84 _5565 P)). Qed.
Lemma lem54596 {_5565 : Type'} (P : _5565 -> Prop) : term6 _5565 P.
Proof. exact (EQ_MP (@lem54595 _5565 P) (@lem54594 _5565 P)). Qed.
Lemma lem54598 {_5565 : Type'} (P : _5565 -> Prop) : term6 _5565 P.
Proof. exact (@lem54275 _5565 P (@lem54596 _5565 P)). Qed.
Lemma lem54599 {_5565 : Type'} (P : _5565 -> Prop) (h1 : term7 _5565 P) : False.
Proof. exact (@lem54598 _5565 P (@lem54259 _5565 P h1)). Qed.
Lemma lem54600 {_5565 : Type'} (P : _5565 -> Prop) (h1 : term7 _5565 P) : (term7 _5565 P) = False.
Proof. exact (prop_ext (fun h2 : term7 _5565 P => @lem54599 _5565 P h1) (fun h2 : False => @lem54259 _5565 P h1)). Qed.
Lemma lem54601 {_5565 : Type'} (P : _5565 -> Prop) (h1 : term7 _5565 P) : False.
Proof. exact (EQ_MP (@lem54600 _5565 P h1) (@lem54259 _5565 P h1)). Qed.
Lemma lem54602 {_5565 : Type'} (P : _5565 -> Prop) : term6 _5565 P.
Proof. exact (fun h0 : term7 _5565 P => @lem54601 _5565 P h0). Qed.
Lemma lem54615 {_5565 : Type'} (P : _5565 -> Prop) : (term4 _5565 P) = (term5 _5565 P).
Proof. exact (EQ_MP (@lem54258 _5565 P) (@lem54602 _5565 P)). Qed.
Lemma lem54616 {A B C : Type'} (P : type478 A B C) : (term85 A B C P) = (term86 A B C P).
Proof. exact (@lem54615 (type1430 A B C) P). Qed.
Lemma lem54621 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem54622 {A B C : Type'} (P : type478 A B C) : (term87 A B C P) = (term88 A B C P).
Proof. exact (MK_COMB (@lem54621) (@lem54616 A B C P)). Qed.
Lemma lem54628 {_5565 : Type'} (P : _5565 -> Prop) : (term4 _5565 P) = (term5 _5565 P).
Proof. exact (EQ_MP (@lem54258 _5565 P) (@lem54602 _5565 P)). Qed.
Lemma lem54629 {A B : Type'} (P : type572 A B) : (term89 A B P) = (term90 A B P).
Proof. exact (@lem54628 (A -> B) P). Qed.
Lemma lem54630 {A B C : Type'} (P : type478 A B C) : (term91 A B C P) = (term92 A B C P).
Proof. exact (@lem54629 A B (term93 A B C P)). Qed.
Lemma lem54631 {A B C : Type'} (P : type478 A B C) (g : A -> B) : (term94 A B C P g) = (term95 A B C P g).
Proof. exact (eq_refl (term94 A B C P g)). Qed.
Lemma lem54632 {A B C : Type'} (P : type478 A B C) : (term96 A B C P) = (term93 A B C P).
Proof. exact (fun_ext (fun g : A -> B => @lem54631 A B C P g)). Qed.
Lemma lem54633 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem54634 {A B C : Type'} (P : type478 A B C) : (term91 A B C P) = (term97 A B C P).
Proof. exact (MK_COMB (@lem54633 A B) (@lem54632 A B C P)). Qed.
Lemma lem54635 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem54636 {A B C : Type'} (P : type478 A B C) : (term98 A B C P) = (term99 A B C P).
Proof. exact (MK_COMB (@lem54635) (@lem54634 A B C P)). Qed.
Lemma lem54637 {A B C : Type'} (P : type478 A B C) (g : A -> B) : (term94 A B C P g) = (term95 A B C P g).
Proof. exact (eq_refl (term94 A B C P g)). Qed.
Lemma lem54638 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem54639 {A B C : Type'} (P : type478 A B C) (g : A -> B) : (term100 A B C P g) = (term101 A B C P g).
Proof. exact (MK_COMB (@lem54638) (@lem54637 A B C P g)). Qed.
Lemma lem54640 {A B C : Type'} (P : type478 A B C) : (term102 A B C P) = (term103 A B C P).
Proof. exact (fun_ext (fun g : A -> B => @lem54639 A B C P g)). Qed.
Lemma lem54641 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem54642 {A B C : Type'} (P : type478 A B C) : (term104 A B C P) = (term105 A B C P).
Proof. exact (MK_COMB (@lem54641 A B) (@lem54640 A B C P)). Qed.
Lemma lem54643 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem54644 {A B C : Type'} (P : type478 A B C) : (term92 A B C P) = (term106 A B C P).
Proof. exact (MK_COMB (@lem54643) (@lem54642 A B C P)). Qed.
Lemma lem54645 {A B C : Type'} (P : type478 A B C) : ((term91 A B C P) = (term92 A B C P)) = ((term97 A B C P) = (term106 A B C P)).
Proof. exact (MK_COMB (@lem54636 A B C P) (@lem54644 A B C P)). Qed.
Lemma lem54646 {A B C : Type'} (P : type478 A B C) : (term97 A B C P) = (term106 A B C P).
Proof. exact (EQ_MP (@lem54645 A B C P) (@lem54630 A B C P)). Qed.
Lemma lem54656 {_5565 : Type'} (P : _5565 -> Prop) : (term4 _5565 P) = (term5 _5565 P).
Proof. exact (EQ_MP (@lem54258 _5565 P) (@lem54602 _5565 P)). Qed.
Lemma lem54657 {A C : Type'} (P : type572 A C) : (term89 A C P) = (term90 A C P).
Proof. exact (@lem54656 (A -> C) P). Qed.
Lemma lem54658 {A B C : Type'} (P : type478 A B C) (g : A -> B) : (term107 A B C P g) = (term108 A B C P g).
Proof. exact (@lem54657 A C (term109 A B C P g)). Qed.
Lemma lem54659 {A B C : Type'} (P : type478 A B C) (g : A -> B) (h : A -> C) : (term110 A B C P g h) = (term111 A B C P g h).
Proof. exact (eq_refl (term110 A B C P g h)). Qed.
Lemma lem54660 {A B C : Type'} (P : type478 A B C) (g : A -> B) : (term112 A B C P g) = (term109 A B C P g).
Proof. exact (fun_ext (fun h : A -> C => @lem54659 A B C P g h)). Qed.
Lemma lem54661 {A C : Type'} : (@ex (A -> C)) = (@ex (A -> C)).
Proof. exact (eq_refl (@ex (A -> C))). Qed.
Lemma lem54662 {A B C : Type'} (P : type478 A B C) (g : A -> B) : (term107 A B C P g) = (term95 A B C P g).
Proof. exact (MK_COMB (@lem54661 A C) (@lem54660 A B C P g)). Qed.
Lemma lem54663 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem54664 {A B C : Type'} (P : type478 A B C) (g : A -> B) : (term113 A B C P g) = (term114 A B C P g).
Proof. exact (MK_COMB (@lem54663) (@lem54662 A B C P g)). Qed.
Lemma lem54665 {A B C : Type'} (P : type478 A B C) (g : A -> B) (h : A -> C) : (term110 A B C P g h) = (term111 A B C P g h).
Proof. exact (eq_refl (term110 A B C P g h)). Qed.
Lemma lem54666 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem54667 {A B C : Type'} (P : type478 A B C) (g : A -> B) (h : A -> C) : (term115 A B C P g h) = (term116 A B C P g h).
Proof. exact (MK_COMB (@lem54666) (@lem54665 A B C P g h)). Qed.
Lemma lem54668 {A B C : Type'} (P : type478 A B C) (g : A -> B) : (term117 A B C P g) = (term118 A B C P g).
Proof. exact (fun_ext (fun h : A -> C => @lem54667 A B C P g h)). Qed.
Lemma lem54669 {A C : Type'} : (@all (A -> C)) = (@all (A -> C)).
Proof. exact (eq_refl (@all (A -> C))). Qed.
Lemma lem54670 {A B C : Type'} (P : type478 A B C) (g : A -> B) : (term119 A B C P g) = (term120 A B C P g).
Proof. exact (MK_COMB (@lem54669 A C) (@lem54668 A B C P g)). Qed.
Lemma lem54671 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem54672 {A B C : Type'} (P : type478 A B C) (g : A -> B) : (term108 A B C P g) = (term121 A B C P g).
Proof. exact (MK_COMB (@lem54671) (@lem54670 A B C P g)). Qed.
Lemma lem54673 {A B C : Type'} (P : type478 A B C) (g : A -> B) : ((term107 A B C P g) = (term108 A B C P g)) = ((term95 A B C P g) = (term121 A B C P g)).
Proof. exact (MK_COMB (@lem54664 A B C P g) (@lem54672 A B C P g)). Qed.
Lemma lem54674 {A B C : Type'} (P : type478 A B C) (g : A -> B) : (term95 A B C P g) = (term121 A B C P g).
Proof. exact (EQ_MP (@lem54673 A B C P g) (@lem54658 A B C P g)). Qed.
Lemma lem54679 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem54680 {A B C : Type'} (P : type478 A B C) (g : A -> B) : (term101 A B C P g) = (term122 A B C P g).
Proof. exact (MK_COMB (@lem54679) (@lem54674 A B C P g)). Qed.
Lemma lem54682 (t : Prop) : (term12 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem54683 {A B C : Type'} (P : type478 A B C) (g : A -> B) : (term122 A B C P g) = (term120 A B C P g).
Proof. exact (@lem54682 (term120 A B C P g)). Qed.
Lemma lem54688 {A B C : Type'} (P : type478 A B C) (g : A -> B) : (term101 A B C P g) = (term120 A B C P g).
Proof. exact (TRANS (@lem54680 A B C P g) (@lem54683 A B C P g)). Qed.
Lemma lem54689 {A B C : Type'} (P : type478 A B C) : (term103 A B C P) = (term123 A B C P).
Proof. exact (fun_ext (fun g : A -> B => @lem54688 A B C P g)). Qed.
Lemma lem54690 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem54691 {A B C : Type'} (P : type478 A B C) : (term105 A B C P) = (term124 A B C P).
Proof. exact (MK_COMB (@lem54690 A B) (@lem54689 A B C P)). Qed.
Lemma lem54696 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem54697 {A B C : Type'} (P : type478 A B C) : (term106 A B C P) = (term125 A B C P).
Proof. exact (MK_COMB (@lem54696) (@lem54691 A B C P)). Qed.
Lemma lem54698 {A B C : Type'} (P : type478 A B C) : (term97 A B C P) = (term125 A B C P).
Proof. exact (TRANS (@lem54646 A B C P) (@lem54697 A B C P)). Qed.
Lemma lem54699 {A B C : Type'} (P : type478 A B C) : ((term85 A B C P) = (term97 A B C P)) = ((term86 A B C P) = (term125 A B C P)).
Proof. exact (MK_COMB (@lem54622 A B C P) (@lem54698 A B C P)). Qed.
Lemma lem54702 {A B C : Type'} : (term126 A B C) = (term127 A B C).
Proof. exact (fun_ext (fun P : type478 A B C => @lem54699 A B C P)). Qed.
Lemma lem54703 {A B C : Type'} : (@all ((A -> prod B C) -> Prop)) = (@all ((A -> prod B C) -> Prop)).
Proof. exact (eq_refl (@all ((A -> prod B C) -> Prop))). Qed.
Lemma lem54704 {A B C : Type'} : (term128 A B C) = (term129 A B C).
Proof. exact (MK_COMB (@lem54703 A B C) (@lem54702 A B C)). Qed.
Lemma lem54709 {A B C : Type'} : (term129 A B C) = (term128 A B C).
Proof. exact (SYM (@lem54704 A B C)). Qed.
Lemma lem54723 {A B C : Type'} (P : type478 A B C) : (term1 A B C P) = (term2 A B C P).
Proof. exact (EQ_MP (@lem54243 A B C P) (@lem54242 A B C P)). Qed.
Lemma lem54724 {A B C : Type'} (P : type478 A B C) : (term1 A B C P) = (term2 A B C P).
Proof. exact (@lem54723 A B C P). Qed.
Lemma lem54725 {A B C : Type'} (P : type478 A B C) : (term130 A B C P) = (term131 A B C P).
Proof. exact (@lem54724 A B C (term132 A B C P)). Qed.
Lemma lem54726 {A B C : Type'} (P : type478 A B C) (f : type1430 A B C) : (term133 A B C P f) = (term134 A B C P f).
Proof. exact (eq_refl (term133 A B C P f)). Qed.
Lemma lem54727 {A B C : Type'} (P : type478 A B C) : (term135 A B C P) = (term132 A B C P).
Proof. exact (fun_ext (fun f : type1430 A B C => @lem54726 A B C P f)). Qed.
Lemma lem54728 {A B C : Type'} : (@all (A -> prod B C)) = (@all (A -> prod B C)).
Proof. exact (eq_refl (@all (A -> prod B C))). Qed.
Lemma lem54729 {A B C : Type'} (P : type478 A B C) : (term130 A B C P) = (term136 A B C P).
Proof. exact (MK_COMB (@lem54728 A B C) (@lem54727 A B C P)). Qed.
Lemma lem54730 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem54731 {A B C : Type'} (P : type478 A B C) : (term137 A B C P) = (term138 A B C P).
Proof. exact (MK_COMB (@lem54730) (@lem54729 A B C P)). Qed.
Lemma lem54732 {A B C : Type'} (P : type478 A B C) (g : A -> B) (h : A -> C) : (term139 A B C P g h) = (term116 A B C P g h).
Proof. exact (eq_refl (term139 A B C P g h)). Qed.
Lemma lem54733 {A B C : Type'} (P : type478 A B C) (g : A -> B) : (term140 A B C P g) = (term118 A B C P g).
Proof. exact (fun_ext (fun h : A -> C => @lem54732 A B C P g h)). Qed.
Lemma lem54734 {A C : Type'} : (@all (A -> C)) = (@all (A -> C)).
Proof. exact (eq_refl (@all (A -> C))). Qed.
Lemma lem54735 {A B C : Type'} (P : type478 A B C) (g : A -> B) : (term141 A B C P g) = (term120 A B C P g).
Proof. exact (MK_COMB (@lem54734 A C) (@lem54733 A B C P g)). Qed.
Lemma lem54736 {A B C : Type'} (P : type478 A B C) : (term142 A B C P) = (term123 A B C P).
Proof. exact (fun_ext (fun g : A -> B => @lem54735 A B C P g)). Qed.
Lemma lem54737 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem54738 {A B C : Type'} (P : type478 A B C) : (term131 A B C P) = (term124 A B C P).
Proof. exact (MK_COMB (@lem54737 A B) (@lem54736 A B C P)). Qed.
Lemma lem54739 {A B C : Type'} (P : type478 A B C) : ((term130 A B C P) = (term131 A B C P)) = ((term136 A B C P) = (term124 A B C P)).
Proof. exact (MK_COMB (@lem54731 A B C P) (@lem54738 A B C P)). Qed.
Lemma lem54740 {A B C : Type'} (P : type478 A B C) : (term136 A B C P) = (term124 A B C P).
Proof. exact (EQ_MP (@lem54739 A B C P) (@lem54725 A B C P)). Qed.
Lemma lem54753 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem54754 {A B C : Type'} (P : type478 A B C) : (term86 A B C P) = (term125 A B C P).
Proof. exact (MK_COMB (@lem54753) (@lem54740 A B C P)). Qed.
Lemma lem54755 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem54756 {A B C : Type'} (P : type478 A B C) : (term88 A B C P) = (term143 A B C P).
Proof. exact (MK_COMB (@lem54755) (@lem54754 A B C P)). Qed.
Lemma lem54769 {A B C : Type'} (P : type478 A B C) : (term125 A B C P) = (term125 A B C P).
Proof. exact (eq_refl (term125 A B C P)). Qed.
Lemma lem54770 {A B C : Type'} (P : type478 A B C) : ((term86 A B C P) = (term125 A B C P)) = ((term125 A B C P) = (term125 A B C P)).
Proof. exact (MK_COMB (@lem54756 A B C P) (@lem54769 A B C P)). Qed.
Lemma lem54772 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem54773 (x : Prop) : (x = x) = True.
Proof. exact (@lem54772 Prop x). Qed.
Lemma lem54774 {A B C : Type'} (P : type478 A B C) : ((term125 A B C P) = (term125 A B C P)) = True.
Proof. exact (@lem54773 (term125 A B C P)). Qed.
Lemma lem54775 {A B C : Type'} (P : type478 A B C) : ((term86 A B C P) = (term125 A B C P)) = True.
Proof. exact (TRANS (@lem54770 A B C P) (@lem54774 A B C P)). Qed.
Lemma lem54776 {A B C : Type'} : (term127 A B C) = (term144 A B C).
Proof. exact (fun_ext (fun P : type478 A B C => @lem54775 A B C P)). Qed.
Lemma lem54777 {A B C : Type'} : (@all ((A -> prod B C) -> Prop)) = (@all ((A -> prod B C) -> Prop)).
Proof. exact (eq_refl (@all ((A -> prod B C) -> Prop))). Qed.
Lemma lem54778 {A B C : Type'} : (term129 A B C) = (term145 A B C).
Proof. exact (MK_COMB (@lem54777 A B C) (@lem54776 A B C)). Qed.
Lemma lem54780 {A : Type'} (t : Prop) : (term146 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem54781 {A B C : Type'} (t : Prop) : (term147 A B C t) = t.
Proof. exact (@lem54780 (type478 A B C) t). Qed.
Lemma lem54782 {A B C : Type'} : (term145 A B C) = True.
Proof. exact (@lem54781 A B C True). Qed.
Lemma lem54783 {A B C : Type'} : (term129 A B C) = True.
Proof. exact (TRANS (@lem54778 A B C) (@lem54782 A B C)). Qed.
Lemma lem54784 {A B C : Type'} : True = (term129 A B C).
Proof. exact (SYM (@lem54783 A B C)). Qed.
Lemma lem54785 {A B C : Type'} : term129 A B C.
Proof. exact (EQ_MP (@lem54784 A B C) (@lem0)). Qed.
Lemma lem54786 {A B C : Type'} : term128 A B C.
Proof. exact (EQ_MP (@lem54709 A B C) (@lem54785 A B C)). Qed.
