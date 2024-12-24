Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2338993_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Lemma lem2338288 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem2338289 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : ((term1 _58314 P Q) = (term2 _58314 P Q)) = (term3 _58314 P Q).
Proof. exact (@lem2338288 ((term1 _58314 P Q) = (term2 _58314 P Q))). Qed.
Lemma lem2338290 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term3 _58314 P Q) = ((term1 _58314 P Q) = (term2 _58314 P Q)).
Proof. exact (SYM (@lem2338289 _58314 P Q)). Qed.
Lemma lem2338291 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (h1 : term4 _58314 P Q) : term4 _58314 P Q.
Proof. exact (h1). Qed.
Lemma lem2338294 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (h1 : term3 _58314 P Q) : term3 _58314 P Q.
Proof. exact (h1). Qed.
Lemma lem2338295 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : term5 _58314 P Q.
Proof. exact (fun h0 : term3 _58314 P Q => @lem2338294 _58314 P Q h0). Qed.
Lemma lem2338296 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (h1 : term5 _58314 P Q) : term5 _58314 P Q.
Proof. exact (h1). Qed.
Lemma lem2338297 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (h1 : term3 _58314 P Q) : term3 _58314 P Q.
Proof. exact (h1). Qed.
Lemma lem2338298 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (h1 : term3 _58314 P Q) (h2 : term5 _58314 P Q) : term3 _58314 P Q.
Proof. exact (@lem2338296 _58314 P Q h2 (@lem2338297 _58314 P Q h1)). Qed.
Lemma lem2338299 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (h1 : term3 _58314 P Q) : term6 _58314 P Q.
Proof. exact (fun h0 : term5 _58314 P Q => @lem2338298 _58314 P Q h1 h0). Qed.
Lemma lem2338300 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (h1 : term5 _58314 P Q) : term5 _58314 P Q.
Proof. exact (h1). Qed.
Lemma lem2338301 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (h1 : term3 _58314 P Q) (h2 : term5 _58314 P Q) : term3 _58314 P Q.
Proof. exact (@lem2338299 _58314 P Q h1 (@lem2338300 _58314 P Q h2)). Qed.
Lemma lem2338302 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (h1 : term5 _58314 P Q) : term5 _58314 P Q.
Proof. exact (fun h0 : term3 _58314 P Q => @lem2338301 _58314 P Q h0 h1). Qed.
Lemma lem2338303 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : term7 _58314 P Q.
Proof. exact (fun h0 : term5 _58314 P Q => @lem2338302 _58314 P Q h0). Qed.
Lemma lem2338306 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : term5 _58314 P Q.
Proof. exact (@lem2338303 _58314 P Q (@lem2338295 _58314 P Q)). Qed.
Lemma lem2338307 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : term5 _58314 P Q.
Proof. exact (@lem2338306 _58314 P Q). Qed.
Lemma lem2338317 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem2338318 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term3 _58314 P Q) = (term8 _58314 P Q).
Proof. exact (@lem2338317 (term4 _58314 P Q)). Qed.
Lemma lem2338320 (t : Prop) : (term9 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem2338321 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term8 _58314 P Q) = ((term1 _58314 P Q) = (term2 _58314 P Q)).
Proof. exact (@lem2338320 ((term1 _58314 P Q) = (term2 _58314 P Q))). Qed.
Lemma lem2338322 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term3 _58314 P Q) = ((term1 _58314 P Q) = (term2 _58314 P Q)).
Proof. exact (TRANS (@lem2338318 _58314 P Q) (@lem2338321 _58314 P Q)). Qed.
Lemma lem2338343 {_58314 : Type'} (Q : _58314 -> Prop) : (term10 _58314 Q) = (term11 _58314 Q).
Proof. exact (fun_ext (fun P : _58314 -> Prop => @lem2338322 _58314 P Q)). Qed.
Lemma lem2338344 {_58314 : Type'} : (@all (_58314 -> Prop)) = (@all (_58314 -> Prop)).
Proof. exact (eq_refl (@all (_58314 -> Prop))). Qed.
Lemma lem2338345 {_58314 : Type'} (Q : _58314 -> Prop) : (term12 _58314 Q) = (term13 _58314 Q).
Proof. exact (MK_COMB (@lem2338344 _58314) (@lem2338343 _58314 Q)). Qed.
Lemma lem2338350 {_58314 : Type'} : (term14 _58314) = (term15 _58314).
Proof. exact (fun_ext (fun Q : _58314 -> Prop => @lem2338345 _58314 Q)). Qed.
Lemma lem2338351 {_58314 : Type'} : (@all (_58314 -> Prop)) = (@all (_58314 -> Prop)).
Proof. exact (eq_refl (@all (_58314 -> Prop))). Qed.
Lemma lem2338360 {_58314 : Type'} : (term16 _58314) = (term17 _58314).
Proof. exact (MK_COMB (@lem2338351 _58314) (@lem2338350 _58314)). Qed.
Lemma lem2338367 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) : (term18 _58314 P Q x) = (term18 _58314 P Q x).
Proof. exact (eq_refl (term18 _58314 P Q x)). Qed.
Lemma lem2338368 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term19 _58314 P Q) = (term19 _58314 P Q).
Proof. exact (fun_ext (fun x : _58314 => @lem2338367 _58314 P Q x)). Qed.
Lemma lem2338369 {_58314 : Type'} : (@all _58314) = (@all _58314).
Proof. exact (eq_refl (@all _58314)). Qed.
Lemma lem2338370 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term20 _58314 P Q) = (term20 _58314 P Q).
Proof. exact (MK_COMB (@lem2338369 _58314) (@lem2338368 _58314 P Q)). Qed.
Lemma lem2338371 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2338372 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term2 _58314 P Q) = (term2 _58314 P Q).
Proof. exact (MK_COMB (@lem2338371) (@lem2338370 _58314 P Q)). Qed.
Lemma lem2338377 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) : (term21 _58314 P Q x) = (term21 _58314 P Q x).
Proof. exact (eq_refl (term21 _58314 P Q x)). Qed.
Lemma lem2338378 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term22 _58314 P Q) = (term22 _58314 P Q).
Proof. exact (fun_ext (fun x : _58314 => @lem2338377 _58314 P Q x)). Qed.
Lemma lem2338379 {_58314 : Type'} : (@ex _58314) = (@ex _58314).
Proof. exact (eq_refl (@ex _58314)). Qed.
Lemma lem2338380 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term1 _58314 P Q) = (term1 _58314 P Q).
Proof. exact (MK_COMB (@lem2338379 _58314) (@lem2338378 _58314 P Q)). Qed.
Lemma lem2338381 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2338382 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term23 _58314 P Q) = (term23 _58314 P Q).
Proof. exact (MK_COMB (@lem2338381) (@lem2338380 _58314 P Q)). Qed.
Lemma lem2338383 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : ((term1 _58314 P Q) = (term2 _58314 P Q)) = ((term1 _58314 P Q) = (term2 _58314 P Q)).
Proof. exact (MK_COMB (@lem2338382 _58314 P Q) (@lem2338372 _58314 P Q)). Qed.
Lemma lem2338384 {_58314 : Type'} (Q : _58314 -> Prop) : (term11 _58314 Q) = (term11 _58314 Q).
Proof. exact (fun_ext (fun P : _58314 -> Prop => @lem2338383 _58314 P Q)). Qed.
Lemma lem2338385 {_58314 : Type'} : (@all (_58314 -> Prop)) = (@all (_58314 -> Prop)).
Proof. exact (eq_refl (@all (_58314 -> Prop))). Qed.
Lemma lem2338386 {_58314 : Type'} (Q : _58314 -> Prop) : (term13 _58314 Q) = (term13 _58314 Q).
Proof. exact (MK_COMB (@lem2338385 _58314) (@lem2338384 _58314 Q)). Qed.
Lemma lem2338387 {_58314 : Type'} : (term15 _58314) = (term15 _58314).
Proof. exact (fun_ext (fun Q : _58314 -> Prop => @lem2338386 _58314 Q)). Qed.
Lemma lem2338388 {_58314 : Type'} : (@all (_58314 -> Prop)) = (@all (_58314 -> Prop)).
Proof. exact (eq_refl (@all (_58314 -> Prop))). Qed.
Lemma lem2338389 {_58314 : Type'} : (term17 _58314) = (term17 _58314).
Proof. exact (MK_COMB (@lem2338388 _58314) (@lem2338387 _58314)). Qed.
Lemma lem2338420 {_58314 : Type'} : (term16 _58314) = (term17 _58314).
Proof. exact (TRANS (@lem2338360 _58314) (@lem2338389 _58314)). Qed.
Lemma lem2338421 {_58314 : Type'} : (term17 _58314) = (term16 _58314).
Proof. exact (SYM (@lem2338420 _58314)). Qed.
Lemma lem2338423 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem2338424 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : ((term1 _58314 P Q) = (term2 _58314 P Q)) = (term3 _58314 P Q).
Proof. exact (@lem2338423 ((term1 _58314 P Q) = (term2 _58314 P Q))). Qed.
Lemma lem2338425 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term3 _58314 P Q) = ((term1 _58314 P Q) = (term2 _58314 P Q)).
Proof. exact (SYM (@lem2338424 _58314 P Q)). Qed.
Lemma lem2338426 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (h1 : term4 _58314 P Q) : term4 _58314 P Q.
Proof. exact (h1). Qed.
Lemma lem2338435 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) : (term24 _58314 P Q x) = (term25 _58314 P Q x).
Proof. exact (@lem17045 (P x) (Q x)). Qed.
Lemma lem2338438 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) : (term21 _58314 P Q x) = (term21 _58314 P Q x).
Proof. exact (eq_refl (term21 _58314 P Q x)). Qed.
Lemma lem2338439 {_58314 : Type'} (P : _58314 -> Prop) : (term26 _58314 P) = (term27 _58314 P).
Proof. exact (@lem18394 _58314 P). Qed.
Lemma lem2338440 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term28 _58314 P Q) = (term29 _58314 P Q).
Proof. exact (@lem2338439 _58314 (term22 _58314 P Q)). Qed.
Lemma lem2338441 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) : (term30 _58314 P Q x) = (term21 _58314 P Q x).
Proof. exact (eq_refl (term30 _58314 P Q x)). Qed.
Lemma lem2338442 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2338443 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) : (term31 _58314 P Q x) = (term24 _58314 P Q x).
Proof. exact (MK_COMB (@lem2338442) (@lem2338441 _58314 P Q x)). Qed.
Lemma lem2338444 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) : (term31 _58314 P Q x) = (term25 _58314 P Q x).
Proof. exact (TRANS (@lem2338443 _58314 P Q x) (@lem2338435 _58314 P Q x)). Qed.
Lemma lem2338445 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term32 _58314 P Q) = (term33 _58314 P Q).
Proof. exact (fun_ext (fun x : _58314 => @lem2338444 _58314 P Q x)). Qed.
Lemma lem2338446 {_58314 : Type'} : (@all _58314) = (@all _58314).
Proof. exact (eq_refl (@all _58314)). Qed.
Lemma lem2338447 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term29 _58314 P Q) = (term34 _58314 P Q).
Proof. exact (MK_COMB (@lem2338446 _58314) (@lem2338445 _58314 P Q)). Qed.
Lemma lem2338448 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term28 _58314 P Q) = (term34 _58314 P Q).
Proof. exact (TRANS (@lem2338440 _58314 P Q) (@lem2338447 _58314 P Q)). Qed.
Lemma lem2338449 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term22 _58314 P Q) = (term22 _58314 P Q).
Proof. exact (fun_ext (fun x : _58314 => @lem2338438 _58314 P Q x)). Qed.
Lemma lem2338450 {_58314 : Type'} : (@ex _58314) = (@ex _58314).
Proof. exact (eq_refl (@ex _58314)). Qed.
Lemma lem2338451 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term1 _58314 P Q) = (term1 _58314 P Q).
Proof. exact (MK_COMB (@lem2338450 _58314) (@lem2338449 _58314 P Q)). Qed.
Lemma lem2338457 {_58314 : Type'} (Q : _58314 -> Prop) (x : _58314) : (term35 _58314 Q x) = (Q x).
Proof. exact (@lem16933 (Q x)). Qed.
Lemma lem2338459 {_58314 : Type'} (P : _58314 -> Prop) (x : _58314) : (term36 _58314 P x) = (term36 _58314 P x).
Proof. exact (eq_refl (term36 _58314 P x)). Qed.
Lemma lem2338460 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) : (term37 _58314 P Q x) = (term21 _58314 P Q x).
Proof. exact (MK_COMB (@lem2338459 _58314 P x) (@lem2338457 _58314 Q x)). Qed.
Lemma lem2338461 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) : (term38 _58314 P Q x) = (term37 _58314 P Q x).
Proof. exact (@lem17362 (P x) (term39 _58314 Q x)). Qed.
Lemma lem2338462 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) : (term38 _58314 P Q x) = (term21 _58314 P Q x).
Proof. exact (TRANS (@lem2338461 _58314 P Q x) (@lem2338460 _58314 P Q x)). Qed.
Lemma lem2338467 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) : (term18 _58314 P Q x) = (term25 _58314 P Q x).
Proof. exact (@lem17265 (P x) (term39 _58314 Q x)). Qed.
Lemma lem2338468 {_58314 : Type'} (P : _58314 -> Prop) : (term40 _58314 P) = (term41 _58314 P).
Proof. exact (@lem18392 _58314 P). Qed.
Lemma lem2338469 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term2 _58314 P Q) = (term42 _58314 P Q).
Proof. exact (@lem2338468 _58314 (term19 _58314 P Q)). Qed.
Lemma lem2338470 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) : (term43 _58314 P Q x) = (term18 _58314 P Q x).
Proof. exact (eq_refl (term43 _58314 P Q x)). Qed.
Lemma lem2338471 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2338472 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) : (term44 _58314 P Q x) = (term38 _58314 P Q x).
Proof. exact (MK_COMB (@lem2338471) (@lem2338470 _58314 P Q x)). Qed.
Lemma lem2338473 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) : (term44 _58314 P Q x) = (term21 _58314 P Q x).
Proof. exact (TRANS (@lem2338472 _58314 P Q x) (@lem2338462 _58314 P Q x)). Qed.
Lemma lem2338474 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term45 _58314 P Q) = (term22 _58314 P Q).
Proof. exact (fun_ext (fun x : _58314 => @lem2338473 _58314 P Q x)). Qed.
Lemma lem2338475 {_58314 : Type'} : (@ex _58314) = (@ex _58314).
Proof. exact (eq_refl (@ex _58314)). Qed.
Lemma lem2338476 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term42 _58314 P Q) = (term1 _58314 P Q).
Proof. exact (MK_COMB (@lem2338475 _58314) (@lem2338474 _58314 P Q)). Qed.
Lemma lem2338477 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term2 _58314 P Q) = (term1 _58314 P Q).
Proof. exact (TRANS (@lem2338469 _58314 P Q) (@lem2338476 _58314 P Q)). Qed.
Lemma lem2338478 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term19 _58314 P Q) = (term33 _58314 P Q).
Proof. exact (fun_ext (fun x : _58314 => @lem2338467 _58314 P Q x)). Qed.
Lemma lem2338479 {_58314 : Type'} : (@all _58314) = (@all _58314).
Proof. exact (eq_refl (@all _58314)). Qed.
Lemma lem2338480 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term20 _58314 P Q) = (term34 _58314 P Q).
Proof. exact (MK_COMB (@lem2338479 _58314) (@lem2338478 _58314 P Q)). Qed.
Lemma lem2338481 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term46 _58314 P Q) = (term20 _58314 P Q).
Proof. exact (@lem16933 (term20 _58314 P Q)). Qed.
Lemma lem2338482 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term46 _58314 P Q) = (term34 _58314 P Q).
Proof. exact (TRANS (@lem2338481 _58314 P Q) (@lem2338480 _58314 P Q)). Qed.
Lemma lem2338483 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2338484 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term47 _58314 P Q) = (term48 _58314 P Q).
Proof. exact (MK_COMB (@lem2338483) (@lem2338448 _58314 P Q)). Qed.
Lemma lem2338485 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term49 _58314 P Q) = (term50 _58314 P Q).
Proof. exact (MK_COMB (@lem2338484 _58314 P Q) (@lem2338477 _58314 P Q)). Qed.
Lemma lem2338486 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2338487 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term51 _58314 P Q) = (term51 _58314 P Q).
Proof. exact (MK_COMB (@lem2338486) (@lem2338451 _58314 P Q)). Qed.
Lemma lem2338488 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term52 _58314 P Q) = (term53 _58314 P Q).
Proof. exact (MK_COMB (@lem2338487 _58314 P Q) (@lem2338482 _58314 P Q)). Qed.
Lemma lem2338489 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2338490 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term54 _58314 P Q) = (term55 _58314 P Q).
Proof. exact (MK_COMB (@lem2338489) (@lem2338488 _58314 P Q)). Qed.
Lemma lem2338491 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term56 _58314 P Q) = (term57 _58314 P Q).
Proof. exact (MK_COMB (@lem2338490 _58314 P Q) (@lem2338485 _58314 P Q)). Qed.
Lemma lem2338492 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term4 _58314 P Q) = (term56 _58314 P Q).
Proof. exact (@lem17646 (term1 _58314 P Q) (term2 _58314 P Q)). Qed.
Lemma lem2338493 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term4 _58314 P Q) = (term57 _58314 P Q).
Proof. exact (TRANS (@lem2338492 _58314 P Q) (@lem2338491 _58314 P Q)). Qed.
Lemma lem2338616 {A : Type'} (P : A -> Prop) (Q : Prop) : (term58 A P Q) = (term59 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem2338617 {_58314 : Type'} (P : _58314 -> Prop) (Q : Prop) : (term58 _58314 P Q) = (term59 _58314 P Q).
Proof. exact (@lem2338616 _58314 P Q). Qed.
Lemma lem2338618 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term60 _58314 P Q) = (term61 _58314 P Q).
Proof. exact (@lem2338617 _58314 (term22 _58314 P Q) (term34 _58314 P Q)). Qed.
Lemma lem2338619 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) : (term30 _58314 P Q x) = (term21 _58314 P Q x).
Proof. exact (eq_refl (term30 _58314 P Q x)). Qed.
Lemma lem2338620 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term62 _58314 P Q) = (term22 _58314 P Q).
Proof. exact (fun_ext (fun x : _58314 => @lem2338619 _58314 P Q x)). Qed.
Lemma lem2338621 {_58314 : Type'} : (@ex _58314) = (@ex _58314).
Proof. exact (eq_refl (@ex _58314)). Qed.
Lemma lem2338622 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term63 _58314 P Q) = (term1 _58314 P Q).
Proof. exact (MK_COMB (@lem2338621 _58314) (@lem2338620 _58314 P Q)). Qed.
Lemma lem2338623 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2338624 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term64 _58314 P Q) = (term51 _58314 P Q).
Proof. exact (MK_COMB (@lem2338623) (@lem2338622 _58314 P Q)). Qed.
Lemma lem2338625 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term34 _58314 P Q) = (term34 _58314 P Q).
Proof. exact (eq_refl (term34 _58314 P Q)). Qed.
Lemma lem2338626 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term60 _58314 P Q) = (term53 _58314 P Q).
Proof. exact (MK_COMB (@lem2338624 _58314 P Q) (@lem2338625 _58314 P Q)). Qed.
Lemma lem2338627 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2338628 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term65 _58314 P Q) = (term66 _58314 P Q).
Proof. exact (MK_COMB (@lem2338627) (@lem2338626 _58314 P Q)). Qed.
Lemma lem2338629 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) : (term30 _58314 P Q x) = (term21 _58314 P Q x).
Proof. exact (eq_refl (term30 _58314 P Q x)). Qed.
Lemma lem2338630 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2338631 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) : (term67 _58314 P Q x) = (term68 _58314 P Q x).
Proof. exact (MK_COMB (@lem2338630) (@lem2338629 _58314 P Q x)). Qed.
Lemma lem2338632 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term34 _58314 P Q) = (term34 _58314 P Q).
Proof. exact (eq_refl (term34 _58314 P Q)). Qed.
Lemma lem2338633 {_58314 : Type'} (x : _58314) (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term69 _58314 x P Q) = (term70 _58314 x P Q).
Proof. exact (MK_COMB (@lem2338631 _58314 P Q x) (@lem2338632 _58314 P Q)). Qed.
Lemma lem2338634 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term71 _58314 P Q) = (term72 _58314 P Q).
Proof. exact (fun_ext (fun x : _58314 => @lem2338633 _58314 x P Q)). Qed.
Lemma lem2338635 {_58314 : Type'} : (@ex _58314) = (@ex _58314).
Proof. exact (eq_refl (@ex _58314)). Qed.
Lemma lem2338636 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term61 _58314 P Q) = (term73 _58314 P Q).
Proof. exact (MK_COMB (@lem2338635 _58314) (@lem2338634 _58314 P Q)). Qed.
Lemma lem2338637 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : ((term60 _58314 P Q) = (term61 _58314 P Q)) = ((term53 _58314 P Q) = (term73 _58314 P Q)).
Proof. exact (MK_COMB (@lem2338628 _58314 P Q) (@lem2338636 _58314 P Q)). Qed.
Lemma lem2338638 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term53 _58314 P Q) = (term73 _58314 P Q).
Proof. exact (EQ_MP (@lem2338637 _58314 P Q) (@lem2338618 _58314 P Q)). Qed.
Lemma lem2338639 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2338640 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term55 _58314 P Q) = (term74 _58314 P Q).
Proof. exact (MK_COMB (@lem2338639) (@lem2338638 _58314 P Q)). Qed.
Lemma lem2338642 {A : Type'} (P : Prop) (Q : A -> Prop) : (term75 A P Q) = (term76 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem2338643 {_58314 : Type'} (P : Prop) (Q : _58314 -> Prop) : (term75 _58314 P Q) = (term76 _58314 P Q).
Proof. exact (@lem2338642 _58314 P Q). Qed.
Lemma lem2338644 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term77 _58314 P Q) = (term78 _58314 P Q).
Proof. exact (@lem2338643 _58314 (term34 _58314 P Q) (term22 _58314 P Q)). Qed.
Lemma lem2338645 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) : (term30 _58314 P Q x) = (term21 _58314 P Q x).
Proof. exact (eq_refl (term30 _58314 P Q x)). Qed.
Lemma lem2338646 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term62 _58314 P Q) = (term22 _58314 P Q).
Proof. exact (fun_ext (fun x : _58314 => @lem2338645 _58314 P Q x)). Qed.
Lemma lem2338647 {_58314 : Type'} : (@ex _58314) = (@ex _58314).
Proof. exact (eq_refl (@ex _58314)). Qed.
Lemma lem2338648 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term63 _58314 P Q) = (term1 _58314 P Q).
Proof. exact (MK_COMB (@lem2338647 _58314) (@lem2338646 _58314 P Q)). Qed.
Lemma lem2338649 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term48 _58314 P Q) = (term48 _58314 P Q).
Proof. exact (eq_refl (term48 _58314 P Q)). Qed.
Lemma lem2338650 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term77 _58314 P Q) = (term50 _58314 P Q).
Proof. exact (MK_COMB (@lem2338649 _58314 P Q) (@lem2338648 _58314 P Q)). Qed.
Lemma lem2338651 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2338652 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term79 _58314 P Q) = (term80 _58314 P Q).
Proof. exact (MK_COMB (@lem2338651) (@lem2338650 _58314 P Q)). Qed.
Lemma lem2338653 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) : (term30 _58314 P Q x) = (term21 _58314 P Q x).
Proof. exact (eq_refl (term30 _58314 P Q x)). Qed.
Lemma lem2338654 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term48 _58314 P Q) = (term48 _58314 P Q).
Proof. exact (eq_refl (term48 _58314 P Q)). Qed.
Lemma lem2338655 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) : (term81 _58314 P Q x) = (term82 _58314 P Q x).
Proof. exact (MK_COMB (@lem2338654 _58314 P Q) (@lem2338653 _58314 P Q x)). Qed.
Lemma lem2338656 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term83 _58314 P Q) = (term84 _58314 P Q).
Proof. exact (fun_ext (fun x : _58314 => @lem2338655 _58314 P Q x)). Qed.
Lemma lem2338657 {_58314 : Type'} : (@ex _58314) = (@ex _58314).
Proof. exact (eq_refl (@ex _58314)). Qed.
Lemma lem2338658 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term78 _58314 P Q) = (term85 _58314 P Q).
Proof. exact (MK_COMB (@lem2338657 _58314) (@lem2338656 _58314 P Q)). Qed.
Lemma lem2338659 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : ((term77 _58314 P Q) = (term78 _58314 P Q)) = ((term50 _58314 P Q) = (term85 _58314 P Q)).
Proof. exact (MK_COMB (@lem2338652 _58314 P Q) (@lem2338658 _58314 P Q)). Qed.
Lemma lem2338660 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term50 _58314 P Q) = (term85 _58314 P Q).
Proof. exact (EQ_MP (@lem2338659 _58314 P Q) (@lem2338644 _58314 P Q)). Qed.
Lemma lem2338661 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term57 _58314 P Q) = (term86 _58314 P Q).
Proof. exact (MK_COMB (@lem2338640 _58314 P Q) (@lem2338660 _58314 P Q)). Qed.
Lemma lem2338663 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term87 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem2338664 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term87 _58314 P Q) = (term88 _58314 P Q).
Proof. exact (@lem2338663 _58314 P Q). Qed.
Lemma lem2338665 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term89 _58314 P Q) = (term90 _58314 P Q).
Proof. exact (@lem2338664 _58314 (term72 _58314 P Q) (term84 _58314 P Q)). Qed.
Lemma lem2338666 {_58314 : Type'} (x : _58314) (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term91 _58314 P Q x) = (term70 _58314 x P Q).
Proof. exact (eq_refl (term91 _58314 P Q x)). Qed.
Lemma lem2338667 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term92 _58314 P Q) = (term72 _58314 P Q).
Proof. exact (fun_ext (fun x : _58314 => @lem2338666 _58314 x P Q)). Qed.
Lemma lem2338668 {_58314 : Type'} : (@ex _58314) = (@ex _58314).
Proof. exact (eq_refl (@ex _58314)). Qed.
Lemma lem2338669 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term93 _58314 P Q) = (term73 _58314 P Q).
Proof. exact (MK_COMB (@lem2338668 _58314) (@lem2338667 _58314 P Q)). Qed.
Lemma lem2338670 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2338671 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term94 _58314 P Q) = (term74 _58314 P Q).
Proof. exact (MK_COMB (@lem2338670) (@lem2338669 _58314 P Q)). Qed.
Lemma lem2338672 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) : (term95 _58314 P Q x) = (term82 _58314 P Q x).
Proof. exact (eq_refl (term95 _58314 P Q x)). Qed.
Lemma lem2338673 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term96 _58314 P Q) = (term84 _58314 P Q).
Proof. exact (fun_ext (fun x : _58314 => @lem2338672 _58314 P Q x)). Qed.
Lemma lem2338674 {_58314 : Type'} : (@ex _58314) = (@ex _58314).
Proof. exact (eq_refl (@ex _58314)). Qed.
Lemma lem2338675 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term97 _58314 P Q) = (term85 _58314 P Q).
Proof. exact (MK_COMB (@lem2338674 _58314) (@lem2338673 _58314 P Q)). Qed.
Lemma lem2338676 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term89 _58314 P Q) = (term86 _58314 P Q).
Proof. exact (MK_COMB (@lem2338671 _58314 P Q) (@lem2338675 _58314 P Q)). Qed.
Lemma lem2338677 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2338678 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term98 _58314 P Q) = (term99 _58314 P Q).
Proof. exact (MK_COMB (@lem2338677) (@lem2338676 _58314 P Q)). Qed.
Lemma lem2338679 {_58314 : Type'} (x : _58314) (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term91 _58314 P Q x) = (term70 _58314 x P Q).
Proof. exact (eq_refl (term91 _58314 P Q x)). Qed.
Lemma lem2338680 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2338681 {_58314 : Type'} (x : _58314) (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term100 _58314 P Q x) = (term101 _58314 x P Q).
Proof. exact (MK_COMB (@lem2338680) (@lem2338679 _58314 x P Q)). Qed.
Lemma lem2338682 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) : (term95 _58314 P Q x) = (term82 _58314 P Q x).
Proof. exact (eq_refl (term95 _58314 P Q x)). Qed.
Lemma lem2338683 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) : (term102 _58314 P Q x) = (term103 _58314 P Q x).
Proof. exact (MK_COMB (@lem2338681 _58314 x P Q) (@lem2338682 _58314 P Q x)). Qed.
Lemma lem2338684 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term104 _58314 P Q) = (term105 _58314 P Q).
Proof. exact (fun_ext (fun x : _58314 => @lem2338683 _58314 P Q x)). Qed.
Lemma lem2338685 {_58314 : Type'} : (@ex _58314) = (@ex _58314).
Proof. exact (eq_refl (@ex _58314)). Qed.
Lemma lem2338686 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term90 _58314 P Q) = (term106 _58314 P Q).
Proof. exact (MK_COMB (@lem2338685 _58314) (@lem2338684 _58314 P Q)). Qed.
Lemma lem2338687 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : ((term89 _58314 P Q) = (term90 _58314 P Q)) = ((term86 _58314 P Q) = (term106 _58314 P Q)).
Proof. exact (MK_COMB (@lem2338678 _58314 P Q) (@lem2338686 _58314 P Q)). Qed.
Lemma lem2338688 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term86 _58314 P Q) = (term106 _58314 P Q).
Proof. exact (EQ_MP (@lem2338687 _58314 P Q) (@lem2338665 _58314 P Q)). Qed.
Lemma lem2338690 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term57 _58314 P Q) = (term106 _58314 P Q).
Proof. exact (TRANS (@lem2338661 _58314 P Q) (@lem2338688 _58314 P Q)). Qed.
Lemma lem2338691 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term4 _58314 P Q) = (term106 _58314 P Q).
Proof. exact (TRANS (@lem2338493 _58314 P Q) (@lem2338690 _58314 P Q)). Qed.
Lemma lem2338692 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (h1 : term4 _58314 P Q) : term106 _58314 P Q.
Proof. exact (EQ_MP (@lem2338691 _58314 P Q) (@lem2338426 _58314 P Q h1)). Qed.
Lemma lem2338693 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) (h1 : term103 _58314 P Q x) : term103 _58314 P Q x.
Proof. exact (h1). Qed.
Lemma lem2338702 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) : (term21 _58314 P Q x) = (term21 _58314 P Q x).
Proof. exact (eq_refl (term21 _58314 P Q x)). Qed.
Lemma lem2338715 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) : (term25 _58314 P Q x) = (term25 _58314 P Q x).
Proof. exact (eq_refl (term25 _58314 P Q x)). Qed.
Lemma lem2338716 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term33 _58314 P Q) = (term33 _58314 P Q).
Proof. exact (fun_ext (fun x : _58314 => @lem2338715 _58314 P Q x)). Qed.
Lemma lem2338717 {_58314 : Type'} : (@all _58314) = (@all _58314).
Proof. exact (eq_refl (@all _58314)). Qed.
Lemma lem2338718 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term34 _58314 P Q) = (term34 _58314 P Q).
Proof. exact (MK_COMB (@lem2338717 _58314) (@lem2338716 _58314 P Q)). Qed.
Lemma lem2338719 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2338720 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term48 _58314 P Q) = (term48 _58314 P Q).
Proof. exact (MK_COMB (@lem2338719) (@lem2338718 _58314 P Q)). Qed.
Lemma lem2338721 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) : (term82 _58314 P Q x) = (term82 _58314 P Q x).
Proof. exact (MK_COMB (@lem2338720 _58314 P Q) (@lem2338702 _58314 P Q x)). Qed.
Lemma lem2338734 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) : (term25 _58314 P Q x) = (term25 _58314 P Q x).
Proof. exact (eq_refl (term25 _58314 P Q x)). Qed.
Lemma lem2338735 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term33 _58314 P Q) = (term33 _58314 P Q).
Proof. exact (fun_ext (fun x : _58314 => @lem2338734 _58314 P Q x)). Qed.
Lemma lem2338736 {_58314 : Type'} : (@all _58314) = (@all _58314).
Proof. exact (eq_refl (@all _58314)). Qed.
Lemma lem2338737 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term34 _58314 P Q) = (term34 _58314 P Q).
Proof. exact (MK_COMB (@lem2338736 _58314) (@lem2338735 _58314 P Q)). Qed.
Lemma lem2338748 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) : (term68 _58314 P Q x) = (term68 _58314 P Q x).
Proof. exact (eq_refl (term68 _58314 P Q x)). Qed.
Lemma lem2338749 {_58314 : Type'} (x : _58314) (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term70 _58314 x P Q) = (term70 _58314 x P Q).
Proof. exact (MK_COMB (@lem2338748 _58314 P Q x) (@lem2338737 _58314 P Q)). Qed.
Lemma lem2338750 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2338751 {_58314 : Type'} (x : _58314) (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term101 _58314 x P Q) = (term101 _58314 x P Q).
Proof. exact (MK_COMB (@lem2338750) (@lem2338749 _58314 x P Q)). Qed.
Lemma lem2338752 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) : (term103 _58314 P Q x) = (term103 _58314 P Q x).
Proof. exact (MK_COMB (@lem2338751 _58314 x P Q) (@lem2338721 _58314 P Q x)). Qed.
Lemma lem2338753 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) (h1 : term103 _58314 P Q x) : term103 _58314 P Q x.
Proof. exact (EQ_MP (@lem2338752 _58314 P Q x) (@lem2338693 _58314 P Q x h1)). Qed.
Lemma lem2338754 {_58314 : Type'} (x : _58314) (P : _58314 -> Prop) (Q : _58314 -> Prop) (h1 : term70 _58314 x P Q) : term70 _58314 x P Q.
Proof. exact (h1). Qed.
Lemma lem2338755 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) (h1 : term82 _58314 P Q x) : term82 _58314 P Q x.
Proof. exact (h1). Qed.
Lemma lem2338756 {_58314 : Type'} (x : _58314) (P : _58314 -> Prop) (Q : _58314 -> Prop) (h1 : term70 _58314 x P Q) : term34 _58314 P Q.
Proof. exact (proj2 (@lem2338754 _58314 x P Q h1)). Qed.
Lemma lem2338757 {_58314 : Type'} (x : _58314) (P : _58314 -> Prop) (Q : _58314 -> Prop) (h1 : term70 _58314 x P Q) : term21 _58314 P Q x.
Proof. exact (proj1 (@lem2338754 _58314 x P Q h1)). Qed.
Lemma lem2338760 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) (h1 : term82 _58314 P Q x) : term21 _58314 P Q x.
Proof. exact (proj2 (@lem2338755 _58314 P Q x h1)). Qed.
Lemma lem2338761 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) (h1 : term82 _58314 P Q x) : term34 _58314 P Q.
Proof. exact (proj1 (@lem2338755 _58314 P Q x h1)). Qed.
Lemma lem2338771 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) : (term25 _58314 P Q x) = (term25 _58314 P Q x).
Proof. exact (eq_refl (term25 _58314 P Q x)). Qed.
Lemma lem2338772 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term33 _58314 P Q) = (term33 _58314 P Q).
Proof. exact (fun_ext (fun x : _58314 => @lem2338771 _58314 P Q x)). Qed.
Lemma lem2338773 {_58314 : Type'} : (@all _58314) = (@all _58314).
Proof. exact (eq_refl (@all _58314)). Qed.
Lemma lem2338775 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term34 _58314 P Q) = (term34 _58314 P Q).
Proof. exact (MK_COMB (@lem2338773 _58314) (@lem2338772 _58314 P Q)). Qed.
Lemma lem2338776 {_58314 : Type'} (x : _58314) (P : _58314 -> Prop) (Q : _58314 -> Prop) (h1 : term70 _58314 x P Q) : term34 _58314 P Q.
Proof. exact (EQ_MP (@lem2338775 _58314 P Q) (@lem2338756 _58314 x P Q h1)). Qed.
Lemma lem2338792 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) : (term25 _58314 P Q x) = (term25 _58314 P Q x).
Proof. exact (eq_refl (term25 _58314 P Q x)). Qed.
Lemma lem2338793 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term33 _58314 P Q) = (term33 _58314 P Q).
Proof. exact (fun_ext (fun x : _58314 => @lem2338792 _58314 P Q x)). Qed.
Lemma lem2338794 {_58314 : Type'} : (@all _58314) = (@all _58314).
Proof. exact (eq_refl (@all _58314)). Qed.
Lemma lem2338796 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term34 _58314 P Q) = (term34 _58314 P Q).
Proof. exact (MK_COMB (@lem2338794 _58314) (@lem2338793 _58314 P Q)). Qed.
Lemma lem2338797 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) (h1 : term82 _58314 P Q x) : term34 _58314 P Q.
Proof. exact (EQ_MP (@lem2338796 _58314 P Q) (@lem2338761 _58314 P Q x h1)). Qed.
Lemma lem2338806 {_58314 : Type'} (_29057 : _58314) (x : _58314) (P : _58314 -> Prop) (Q : _58314 -> Prop) (h1 : term70 _58314 x P Q) : term107 _58314 P Q _29057.
Proof. exact (@lem2338776 _58314 x P Q h1 _29057). Qed.
Lemma lem2338807 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (_29057 : _58314) : (term107 _58314 P Q _29057) = (term25 _58314 P Q _29057).
Proof. exact (eq_refl (term107 _58314 P Q _29057)). Qed.
Lemma lem2338809 {_58314 : Type'} (_29058 : _58314) (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) (h1 : term82 _58314 P Q x) : term107 _58314 P Q _29058.
Proof. exact (@lem2338797 _58314 P Q x h1 _29058). Qed.
Lemma lem2338810 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (_29058 : _58314) : (term107 _58314 P Q _29058) = (term25 _58314 P Q _29058).
Proof. exact (eq_refl (term107 _58314 P Q _29058)). Qed.
Lemma lem2338817 {_58314 : Type'} (_29057 : _58314) (x : _58314) (P : _58314 -> Prop) (Q : _58314 -> Prop) (h1 : term70 _58314 x P Q) : term25 _58314 P Q _29057.
Proof. exact (EQ_MP (@lem2338807 _58314 P Q _29057) (@lem2338806 _58314 _29057 x P Q h1)). Qed.
Lemma lem2338827 {_58314 : Type'} (_29058 : _58314) (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) (h1 : term82 _58314 P Q x) : term25 _58314 P Q _29058.
Proof. exact (EQ_MP (@lem2338810 _58314 P Q _29058) (@lem2338809 _58314 _29058 P Q x h1)). Qed.
Lemma lem2338833 {_58314 : Type'} (x : _58314) (P : _58314 -> Prop) (Q : _58314 -> Prop) (h1 : term70 _58314 x P Q) : P x.
Proof. exact (proj1 (@lem2338757 _58314 x P Q h1)). Qed.
Lemma lem2338834 {_58314 : Type'} (x : _58314) (P : _58314 -> Prop) (Q : _58314 -> Prop) (h1 : term70 _58314 x P Q) : term108 _58314 P x.
Proof. exact (fun h0 : term39 _58314 P x => @lem2338833 _58314 x P Q h1). Qed.
Lemma lem2338836 (p : Prop) : (term109 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2338837 {_58314 : Type'} (P : _58314 -> Prop) (x : _58314) : (term108 _58314 P x) = (P x).
Proof. exact (@lem2338836 (P x)). Qed.
Lemma lem2338838 {_58314 : Type'} (x : _58314) (P : _58314 -> Prop) (Q : _58314 -> Prop) (h1 : term70 _58314 x P Q) : P x.
Proof. exact (EQ_MP (@lem2338837 _58314 P x) (@lem2338834 _58314 x P Q h1)). Qed.
Lemma lem2338840 {_58314 : Type'} (x : _58314) (P : _58314 -> Prop) (Q : _58314 -> Prop) (h1 : term70 _58314 x P Q) : Q x.
Proof. exact (proj2 (@lem2338757 _58314 x P Q h1)). Qed.
Lemma lem2338841 {_58314 : Type'} (x : _58314) (P : _58314 -> Prop) (Q : _58314 -> Prop) (h1 : term70 _58314 x P Q) : term108 _58314 Q x.
Proof. exact (fun h0 : term39 _58314 Q x => @lem2338840 _58314 x P Q h1). Qed.
Lemma lem2338843 (p : Prop) : (term109 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2338844 {_58314 : Type'} (Q : _58314 -> Prop) (x : _58314) : (term108 _58314 Q x) = (Q x).
Proof. exact (@lem2338843 (Q x)). Qed.
Lemma lem2338845 {_58314 : Type'} (x : _58314) (P : _58314 -> Prop) (Q : _58314 -> Prop) (h1 : term70 _58314 x P Q) : Q x.
Proof. exact (EQ_MP (@lem2338844 _58314 Q x) (@lem2338841 _58314 x P Q h1)). Qed.
Lemma lem2338847 (a : Prop) (b : Prop) : (term110 a b) = (term111 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem2338848 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (_29057 : _58314) : (term25 _58314 P Q _29057) = (term24 _58314 P Q _29057).
Proof. exact (@lem2338847 (P _29057) (Q _29057)). Qed.
Lemma lem2338850 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem2338851 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (_29057 : _58314) : (term24 _58314 P Q _29057) = (term112 _58314 P Q _29057).
Proof. exact (@lem2338850 (term21 _58314 P Q _29057)). Qed.
Lemma lem2338852 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (_29057 : _58314) : (term25 _58314 P Q _29057) = (term112 _58314 P Q _29057).
Proof. exact (TRANS (@lem2338848 _58314 P Q _29057) (@lem2338851 _58314 P Q _29057)). Qed.
Lemma lem2338854 {_58314 : Type'} (x : _58314) (P : _58314 -> Prop) (Q : _58314 -> Prop) (h1 : term70 _58314 x P Q) : term21 _58314 P Q x.
Proof. exact (conj (@lem2338838 _58314 x P Q h1) (@lem2338845 _58314 x P Q h1)). Qed.
Lemma lem2338856 {_58314 : Type'} (_29057 : _58314) (x : _58314) (P : _58314 -> Prop) (Q : _58314 -> Prop) (h1 : term70 _58314 x P Q) : term112 _58314 P Q _29057.
Proof. exact (EQ_MP (@lem2338852 _58314 P Q _29057) (@lem2338817 _58314 _29057 x P Q h1)). Qed.
Lemma lem2338857 {_58314 : Type'} (_29057 : _58314) (x : _58314) (P : _58314 -> Prop) (Q : _58314 -> Prop) (h1 : term70 _58314 x P Q) : term112 _58314 P Q _29057.
Proof. exact (@lem2338856 _58314 _29057 x P Q h1). Qed.
Lemma lem2338858 {_58314 : Type'} (x : _58314) (P : _58314 -> Prop) (Q : _58314 -> Prop) (h1 : term70 _58314 x P Q) : term112 _58314 P Q x.
Proof. exact (@lem2338857 _58314 x x P Q h1). Qed.
Lemma lem2338861 {_58314 : Type'} (x : _58314) (P : _58314 -> Prop) (Q : _58314 -> Prop) (h1 : term70 _58314 x P Q) : False.
Proof. exact (@lem2338858 _58314 x P Q h1 (@lem2338854 _58314 x P Q h1)). Qed.
Lemma lem2338862 {_58314 : Type'} (x : _58314) (P : _58314 -> Prop) (Q : _58314 -> Prop) (h1 : term70 _58314 x P Q) : term113.
Proof. exact (fun h0 : ~ False => @lem2338861 _58314 x P Q h1). Qed.
Lemma lem2338864 (p : Prop) : (term109 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2338865 : term113 = False.
Proof. exact (@lem2338864 False). Qed.
Lemma lem2338866 {_58314 : Type'} (x : _58314) (P : _58314 -> Prop) (Q : _58314 -> Prop) (h1 : term70 _58314 x P Q) : False.
Proof. exact (EQ_MP (@lem2338865) (@lem2338862 _58314 x P Q h1)). Qed.
Lemma lem2338868 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) (h1 : term82 _58314 P Q x) : P x.
Proof. exact (proj1 (@lem2338760 _58314 P Q x h1)). Qed.
Lemma lem2338869 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) (h1 : term82 _58314 P Q x) : term108 _58314 P x.
Proof. exact (fun h0 : term39 _58314 P x => @lem2338868 _58314 P Q x h1). Qed.
Lemma lem2338871 (p : Prop) : (term109 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2338872 {_58314 : Type'} (P : _58314 -> Prop) (x : _58314) : (term108 _58314 P x) = (P x).
Proof. exact (@lem2338871 (P x)). Qed.
Lemma lem2338873 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) (h1 : term82 _58314 P Q x) : P x.
Proof. exact (EQ_MP (@lem2338872 _58314 P x) (@lem2338869 _58314 P Q x h1)). Qed.
Lemma lem2338875 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) (h1 : term82 _58314 P Q x) : Q x.
Proof. exact (proj2 (@lem2338760 _58314 P Q x h1)). Qed.
Lemma lem2338876 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) (h1 : term82 _58314 P Q x) : term108 _58314 Q x.
Proof. exact (fun h0 : term39 _58314 Q x => @lem2338875 _58314 P Q x h1). Qed.
Lemma lem2338878 (p : Prop) : (term109 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2338879 {_58314 : Type'} (Q : _58314 -> Prop) (x : _58314) : (term108 _58314 Q x) = (Q x).
Proof. exact (@lem2338878 (Q x)). Qed.
Lemma lem2338880 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) (h1 : term82 _58314 P Q x) : Q x.
Proof. exact (EQ_MP (@lem2338879 _58314 Q x) (@lem2338876 _58314 P Q x h1)). Qed.
Lemma lem2338882 (a : Prop) (b : Prop) : (term110 a b) = (term111 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem2338883 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (_29058 : _58314) : (term25 _58314 P Q _29058) = (term24 _58314 P Q _29058).
Proof. exact (@lem2338882 (P _29058) (Q _29058)). Qed.
Lemma lem2338885 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem2338886 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (_29058 : _58314) : (term24 _58314 P Q _29058) = (term112 _58314 P Q _29058).
Proof. exact (@lem2338885 (term21 _58314 P Q _29058)). Qed.
Lemma lem2338887 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (_29058 : _58314) : (term25 _58314 P Q _29058) = (term112 _58314 P Q _29058).
Proof. exact (TRANS (@lem2338883 _58314 P Q _29058) (@lem2338886 _58314 P Q _29058)). Qed.
Lemma lem2338889 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) (h1 : term82 _58314 P Q x) : term21 _58314 P Q x.
Proof. exact (conj (@lem2338873 _58314 P Q x h1) (@lem2338880 _58314 P Q x h1)). Qed.
Lemma lem2338891 {_58314 : Type'} (_29058 : _58314) (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) (h1 : term82 _58314 P Q x) : term112 _58314 P Q _29058.
Proof. exact (EQ_MP (@lem2338887 _58314 P Q _29058) (@lem2338827 _58314 _29058 P Q x h1)). Qed.
Lemma lem2338892 {_58314 : Type'} (_29058 : _58314) (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) (h1 : term82 _58314 P Q x) : term112 _58314 P Q _29058.
Proof. exact (@lem2338891 _58314 _29058 P Q x h1). Qed.
Lemma lem2338893 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) (h1 : term82 _58314 P Q x) : term112 _58314 P Q x.
Proof. exact (@lem2338892 _58314 x P Q x h1). Qed.
Lemma lem2338896 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) (h1 : term82 _58314 P Q x) : False.
Proof. exact (@lem2338893 _58314 P Q x h1 (@lem2338889 _58314 P Q x h1)). Qed.
Lemma lem2338897 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) (h1 : term82 _58314 P Q x) : term113.
Proof. exact (fun h0 : ~ False => @lem2338896 _58314 P Q x h1). Qed.
Lemma lem2338899 (p : Prop) : (term109 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2338900 : term113 = False.
Proof. exact (@lem2338899 False). Qed.
Lemma lem2338901 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) (h1 : term82 _58314 P Q x) : False.
Proof. exact (EQ_MP (@lem2338900) (@lem2338897 _58314 P Q x h1)). Qed.
Lemma lem2338902 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) (h1 : term103 _58314 P Q x) : False.
Proof. exact (or_elim (@lem2338753 _58314 P Q x h1) (fun h0 : term70 _58314 x P Q => @lem2338866 _58314 x P Q h0) (fun h0 : term82 _58314 P Q x => @lem2338901 _58314 P Q x h0)). Qed.
Lemma lem2338903 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) (h1 : term103 _58314 P Q x) : (term103 _58314 P Q x) = False.
Proof. exact (prop_ext (fun h2 : term103 _58314 P Q x => @lem2338902 _58314 P Q x h1) (fun h2 : False => @lem2338753 _58314 P Q x h1)). Qed.
Lemma lem2338904 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (x : _58314) (h1 : term103 _58314 P Q x) : False.
Proof. exact (EQ_MP (@lem2338903 _58314 P Q x h1) (@lem2338753 _58314 P Q x h1)). Qed.
Lemma lem2338905 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (h1 : term4 _58314 P Q) : False.
Proof. exact (ex_elim (@lem2338692 _58314 P Q h1) (fun x : _58314 => fun h0 : term105 _58314 P Q x => @lem2338904 _58314 P Q x h0)). Qed.
Lemma lem2338906 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (h1 : term4 _58314 P Q) : (term4 _58314 P Q) = False.
Proof. exact (prop_ext (fun h2 : term4 _58314 P Q => @lem2338905 _58314 P Q h1) (fun h2 : False => @lem2338426 _58314 P Q h1)). Qed.
Lemma lem2338907 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (h1 : term4 _58314 P Q) : False.
Proof. exact (EQ_MP (@lem2338906 _58314 P Q h1) (@lem2338426 _58314 P Q h1)). Qed.
Lemma lem2338908 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : term3 _58314 P Q.
Proof. exact (fun h0 : term4 _58314 P Q => @lem2338907 _58314 P Q h0). Qed.
Lemma lem2338909 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term1 _58314 P Q) = (term2 _58314 P Q).
Proof. exact (EQ_MP (@lem2338425 _58314 P Q) (@lem2338908 _58314 P Q)). Qed.
Lemma lem2338914 {_58314 : Type'} (Q : _58314 -> Prop) : term13 _58314 Q.
Proof. exact (fun P : _58314 -> Prop => @lem2338909 _58314 P Q). Qed.
Lemma lem2338919 {_58314 : Type'} : term17 _58314.
Proof. exact (fun Q : _58314 -> Prop => @lem2338914 _58314 Q). Qed.
Lemma lem2338920 {_58314 : Type'} : term16 _58314.
Proof. exact (EQ_MP (@lem2338421 _58314) (@lem2338919 _58314)). Qed.
Lemma lem2338921 {_58314 : Type'} (Q : _58314 -> Prop) : term114 _58314 Q.
Proof. exact (@lem2338920 _58314 Q). Qed.
Lemma lem2338922 {_58314 : Type'} (Q : _58314 -> Prop) : (term114 _58314 Q) = (term12 _58314 Q).
Proof. exact (eq_refl (term114 _58314 Q)). Qed.
Lemma lem2338923 {_58314 : Type'} (Q : _58314 -> Prop) : term12 _58314 Q.
Proof. exact (EQ_MP (@lem2338922 _58314 Q) (@lem2338921 _58314 Q)). Qed.
Lemma lem2338924 {_58314 : Type'} (Q : _58314 -> Prop) (P : _58314 -> Prop) : term115 _58314 Q P.
Proof. exact (@lem2338923 _58314 Q P). Qed.
Lemma lem2338925 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term115 _58314 Q P) = (term3 _58314 P Q).
Proof. exact (eq_refl (term115 _58314 Q P)). Qed.
Lemma lem2338926 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : term3 _58314 P Q.
Proof. exact (EQ_MP (@lem2338925 _58314 P Q) (@lem2338924 _58314 Q P)). Qed.
Lemma lem2338928 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : term3 _58314 P Q.
Proof. exact (@lem2338307 _58314 P Q (@lem2338926 _58314 P Q)). Qed.
Lemma lem2338929 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (h1 : term4 _58314 P Q) : False.
Proof. exact (@lem2338928 _58314 P Q (@lem2338291 _58314 P Q h1)). Qed.
Lemma lem2338930 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (h1 : term4 _58314 P Q) : (term4 _58314 P Q) = False.
Proof. exact (prop_ext (fun h2 : term4 _58314 P Q => @lem2338929 _58314 P Q h1) (fun h2 : False => @lem2338291 _58314 P Q h1)). Qed.
Lemma lem2338931 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) (h1 : term4 _58314 P Q) : False.
Proof. exact (EQ_MP (@lem2338930 _58314 P Q h1) (@lem2338291 _58314 P Q h1)). Qed.
Lemma lem2338932 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : term3 _58314 P Q.
Proof. exact (fun h0 : term4 _58314 P Q => @lem2338931 _58314 P Q h0). Qed.
Lemma lem2338937 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term1 _58314 P Q) = (term2 _58314 P Q).
Proof. exact (EQ_MP (@lem2338290 _58314 P Q) (@lem2338932 _58314 P Q)). Qed.
Lemma lem2338938 (P : int -> Prop) (Q : int -> Prop) : (term116 P Q) = (term117 P Q).
Proof. exact (@lem2338937 int P Q). Qed.
Lemma lem2338939 (P : int -> Prop) : (term118 P) = (term119 P).
Proof. exact (@lem2338938 term120 P). Qed.
Lemma lem2338940 (x : int) : (term121 x) = (term122 x).
Proof. exact (eq_refl (term121 x)). Qed.
Lemma lem2338941 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2338942 (x : int) : (term123 x) = (term124 x).
Proof. exact (MK_COMB (@lem2338941) (@lem2338940 x)). Qed.
Lemma lem2338943 (P : int -> Prop) (x : int) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem2338944 (P : int -> Prop) (x : int) : (term125 P x) = (term126 P x).
Proof. exact (MK_COMB (@lem2338942 x) (@lem2338943 P x)). Qed.
Lemma lem2338945 (P : int -> Prop) : (term127 P) = (term128 P).
Proof. exact (fun_ext (fun x : int => @lem2338944 P x)). Qed.
Lemma lem2338946 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2338947 (P : int -> Prop) : (term118 P) = (term129 P).
Proof. exact (MK_COMB (@lem2338946) (@lem2338945 P)). Qed.
Lemma lem2338948 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2338949 (P : int -> Prop) : (term130 P) = (term131 P).
Proof. exact (MK_COMB (@lem2338948) (@lem2338947 P)). Qed.
Lemma lem2338950 (x : int) : (term121 x) = (term122 x).
Proof. exact (eq_refl (term121 x)). Qed.
Lemma lem2338951 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2338952 (x : int) : (term132 x) = (term133 x).
Proof. exact (MK_COMB (@lem2338951) (@lem2338950 x)). Qed.
Lemma lem2338953 (P : int -> Prop) (x : int) : (term134 P x) = (term134 P x).
Proof. exact (eq_refl (term134 P x)). Qed.
Lemma lem2338954 (P : int -> Prop) (x : int) : (term135 P x) = (term136 P x).
Proof. exact (MK_COMB (@lem2338952 x) (@lem2338953 P x)). Qed.
Lemma lem2338955 (P : int -> Prop) : (term137 P) = (term138 P).
Proof. exact (fun_ext (fun x : int => @lem2338954 P x)). Qed.
Lemma lem2338956 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2338957 (P : int -> Prop) : (term139 P) = (term140 P).
Proof. exact (MK_COMB (@lem2338956) (@lem2338955 P)). Qed.
Lemma lem2338958 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2338959 (P : int -> Prop) : (term119 P) = (term141 P).
Proof. exact (MK_COMB (@lem2338958) (@lem2338957 P)). Qed.
Lemma lem2338960 (P : int -> Prop) : ((term118 P) = (term119 P)) = ((term129 P) = (term141 P)).
Proof. exact (MK_COMB (@lem2338949 P) (@lem2338959 P)). Qed.
Lemma lem2338961 (P : int -> Prop) : (term129 P) = (term141 P).
Proof. exact (EQ_MP (@lem2338960 P) (@lem2338939 P)). Qed.
Lemma lem2338962 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2338963 (P : int -> Prop) : (term131 P) = (term142 P).
Proof. exact (MK_COMB (@lem2338962) (@lem2338961 P)). Qed.
Lemma lem2338965 {_58314 : Type'} (P : _58314 -> Prop) (Q : _58314 -> Prop) : (term1 _58314 P Q) = (term2 _58314 P Q).
Proof. exact (EQ_MP (@lem2338290 _58314 P Q) (@lem2338932 _58314 P Q)). Qed.
Lemma lem2338966 (P : int -> Prop) (Q : int -> Prop) : (term116 P Q) = (term117 P Q).
Proof. exact (@lem2338965 int P Q). Qed.
Lemma lem2338967 (P : int -> Prop) : (term143 P) = (term144 P).
Proof. exact (@lem2338966 term120 (term145 P)). Qed.
Lemma lem2338968 (x : int) : (term121 x) = (term122 x).
Proof. exact (eq_refl (term121 x)). Qed.
Lemma lem2338969 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2338970 (x : int) : (term123 x) = (term124 x).
Proof. exact (MK_COMB (@lem2338969) (@lem2338968 x)). Qed.
Lemma lem2338971 (P : int -> Prop) (x : int) : (term146 P x) = (term147 P x).
Proof. exact (eq_refl (term146 P x)). Qed.
Lemma lem2338972 (P : int -> Prop) (x : int) : (term148 P x) = (term149 P x).
Proof. exact (MK_COMB (@lem2338970 x) (@lem2338971 P x)). Qed.
Lemma lem2338973 (P : int -> Prop) : (term150 P) = (term151 P).
Proof. exact (fun_ext (fun x : int => @lem2338972 P x)). Qed.
Lemma lem2338974 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2338975 (P : int -> Prop) : (term143 P) = (term152 P).
Proof. exact (MK_COMB (@lem2338974) (@lem2338973 P)). Qed.
Lemma lem2338976 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2338977 (P : int -> Prop) : (term153 P) = (term154 P).
Proof. exact (MK_COMB (@lem2338976) (@lem2338975 P)). Qed.
Lemma lem2338978 (x : int) : (term121 x) = (term122 x).
Proof. exact (eq_refl (term121 x)). Qed.
Lemma lem2338979 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2338980 (x : int) : (term132 x) = (term133 x).
Proof. exact (MK_COMB (@lem2338979) (@lem2338978 x)). Qed.
Lemma lem2338981 (P : int -> Prop) (x : int) : (term146 P x) = (term147 P x).
Proof. exact (eq_refl (term146 P x)). Qed.
Lemma lem2338982 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2338983 (P : int -> Prop) (x : int) : (term155 P x) = (term156 P x).
Proof. exact (MK_COMB (@lem2338982) (@lem2338981 P x)). Qed.
Lemma lem2338984 (P : int -> Prop) (x : int) : (term157 P x) = (term158 P x).
Proof. exact (MK_COMB (@lem2338980 x) (@lem2338983 P x)). Qed.
Lemma lem2338985 (P : int -> Prop) : (term159 P) = (term160 P).
Proof. exact (fun_ext (fun x : int => @lem2338984 P x)). Qed.
Lemma lem2338986 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2338987 (P : int -> Prop) : (term161 P) = (term162 P).
Proof. exact (MK_COMB (@lem2338986) (@lem2338985 P)). Qed.
Lemma lem2338988 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2338989 (P : int -> Prop) : (term144 P) = (term163 P).
Proof. exact (MK_COMB (@lem2338988) (@lem2338987 P)). Qed.
Lemma lem2338990 (P : int -> Prop) : ((term143 P) = (term144 P)) = ((term152 P) = (term163 P)).
Proof. exact (MK_COMB (@lem2338977 P) (@lem2338989 P)). Qed.
Lemma lem2338991 (P : int -> Prop) : (term152 P) = (term163 P).
Proof. exact (EQ_MP (@lem2338990 P) (@lem2338967 P)). Qed.
Lemma lem2338992 (P : int -> Prop) : ((term129 P) = (term152 P)) = ((term141 P) = (term163 P)).
Proof. exact (MK_COMB (@lem2338963 P) (@lem2338991 P)). Qed.
Lemma lem2338993 (P : int -> Prop) : ((term141 P) = (term163 P)) = ((term129 P) = (term152 P)).
Proof. exact (SYM (@lem2338992 P)). Qed.
