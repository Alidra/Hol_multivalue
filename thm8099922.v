Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm8099922_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm16457_spec.
Require Import thm16458_spec.
Require Import thm16471_spec.
Require Import thm16473_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1831_spec.
Require Import thm1832_spec.
Require Import thm1833_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19732_spec.
Require Import thm20425_spec.
Require Import thm20611_spec.
Require Import thm20612_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm51_spec.
Lemma lem8096296 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8096297 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : ((term1 _143642 _143649 r s x) = (term2 _143642 _143649 r s x)) = (term3 _143642 _143649 r s x).
Proof. exact (@lem8096296 ((term1 _143642 _143649 r s x) = (term2 _143642 _143649 r s x))). Qed.
Lemma lem8096298 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term3 _143642 _143649 r s x) = ((term1 _143642 _143649 r s x) = (term2 _143642 _143649 r s x)).
Proof. exact (SYM (@lem8096297 _143642 _143649 r s x)). Qed.
Lemma lem8096299 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : term4 _143642 _143649 r s x) : term4 _143642 _143649 r s x.
Proof. exact (h1). Qed.
Lemma lem8096320 {_143642 : Type'} (P : _143642 -> Prop) : term5 _143642 P.
Proof. exact (@lem19732 _143642 P). Qed.
Lemma lem8096321 {_143642 : Type'} : term6 _143642.
Proof. exact (@lem8096320 _143642 (term7 _143642)). Qed.
Lemma lem8096322 {_143642 : Type'} : (term8 _143642) = False.
Proof. exact (eq_refl (term8 _143642)). Qed.
Lemma lem8096323 {_143642 : Type'} (x : _143642) : (term9 _143642 x) = False.
Proof. exact (eq_refl (term9 _143642 x)). Qed.
Lemma lem8096324 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8096325 {_143642 : Type'} (x : _143642) : (term10 _143642 x) = (imp False).
Proof. exact (MK_COMB (@lem8096324) (@lem8096323 _143642 x)). Qed.
Lemma lem8096326 {_143642 : Type'} (x : _143642) : (term11 _143642 x) = (False -> False).
Proof. exact (MK_COMB (@lem8096325 _143642 x) (@lem8096322 _143642)). Qed.
Lemma lem8096327 {_143642 : Type'} : (term12 _143642) = (term13 _143642).
Proof. exact (fun_ext (fun x : _143642 => @lem8096326 _143642 x)). Qed.
Lemma lem8096328 {_143642 : Type'} : (@all _143642) = (@all _143642).
Proof. exact (eq_refl (@all _143642)). Qed.
Lemma lem8096329 {_143642 : Type'} : (term6 _143642) = (term14 _143642).
Proof. exact (MK_COMB (@lem8096328 _143642) (@lem8096327 _143642)). Qed.
Lemma lem8096330 {_143642 : Type'} : term14 _143642.
Proof. exact (EQ_MP (@lem8096329 _143642) (@lem8096321 _143642)). Qed.
Lemma lem8096331 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : term15 _143642 _143649 r s x) : term15 _143642 _143649 r s x.
Proof. exact (h1). Qed.
Lemma lem8096332 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : term15 _143642 _143649 r s x) : term3 _143642 _143649 r s x.
Proof. exact (@lem8096331 _143642 _143649 r s x h1 (@lem8096330 _143642)). Qed.
Lemma lem8096333 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : term16 _143642 _143649 r s x.
Proof. exact (fun h0 : term15 _143642 _143649 r s x => @lem8096332 _143642 _143649 r s x h0). Qed.
Lemma lem8096334 {_143642 : Type'} (_107385 : _143642) (h1 : _107385 = (term17 _143642)) : _107385 = (term17 _143642).
Proof. exact (h1). Qed.
Lemma lem8096337 {_143642 : Type'} (_107385 : _143642) (h1 : _107385 = (term17 _143642)) : (term17 _143642) = _107385.
Proof. exact (SYM (@lem8096334 _143642 _107385 h1)). Qed.
Lemma lem8096338 {_143642 : Type'} (_107385 : _143642) (h1 : _107385 = (term17 _143642)) : (term17 _143642) = _107385.
Proof. exact (@lem8096337 _143642 _107385 h1). Qed.
Lemma lem8096339 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term18 _143642 _143649 r s x) = (term18 _143642 _143649 r s x).
Proof. exact (eq_refl (term18 _143642 _143649 r s x)). Qed.
Lemma lem8096340 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) (h1 : _107385 = (term17 _143642)) : (term1 _143642 _143649 r s x) = (term19 _143642 _143649 r s x _107385).
Proof. exact (MK_COMB (@lem8096339 _143642 _143649 r s x) (@lem8096338 _143642 _107385 h1)). Qed.
Lemma lem8096341 {_143642 : Type'} : (@eq _143642) = (@eq _143642).
Proof. exact (eq_refl (@eq _143642)). Qed.
Lemma lem8096342 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) (h1 : _107385 = (term17 _143642)) : (term20 _143642 _143649 r s x) = (term21 _143642 _143649 r s x _107385).
Proof. exact (MK_COMB (@lem8096341 _143642) (@lem8096340 _143642 _143649 r s x _107385 h1)). Qed.
Lemma lem8096344 {_143642 : Type'} (_107385 : _143642) (h1 : _107385 = (term17 _143642)) : (term17 _143642) = _107385.
Proof. exact (SYM (@lem8096334 _143642 _107385 h1)). Qed.
Lemma lem8096345 {_143642 : Type'} (_107385 : _143642) (h1 : _107385 = (term17 _143642)) : (term17 _143642) = _107385.
Proof. exact (@lem8096344 _143642 _107385 h1). Qed.
Lemma lem8096346 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term22 _143642 _143649 r x) = (term22 _143642 _143649 r x).
Proof. exact (eq_refl (term22 _143642 _143649 r x)). Qed.
Lemma lem8096347 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) (h1 : _107385 = (term17 _143642)) : (term23 _143642 _143649 r x) = (term24 _143642 _143649 r x _107385).
Proof. exact (MK_COMB (@lem8096346 _143642 _143649 r x) (@lem8096345 _143642 _107385 h1)). Qed.
Lemma lem8096348 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term25 _143642 _143649 r x) = (term25 _143642 _143649 r x).
Proof. exact (eq_refl (term25 _143642 _143649 r x)). Qed.
Lemma lem8096349 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) (h1 : _107385 = (term17 _143642)) : (term26 _143642 _143649 r x) = (term27 _143642 _143649 r x _107385).
Proof. exact (MK_COMB (@lem8096348 _143642 _143649 r x) (@lem8096347 _143642 _143649 r x _107385 h1)). Qed.
Lemma lem8096351 {_143642 : Type'} (_107385 : _143642) (h1 : _107385 = (term17 _143642)) : (term17 _143642) = _107385.
Proof. exact (SYM (@lem8096334 _143642 _107385 h1)). Qed.
Lemma lem8096352 {_143642 : Type'} (_107385 : _143642) (h1 : _107385 = (term17 _143642)) : (term17 _143642) = _107385.
Proof. exact (@lem8096351 _143642 _107385 h1). Qed.
Lemma lem8096353 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term22 _143642 _143649 s x) = (term22 _143642 _143649 s x).
Proof. exact (eq_refl (term22 _143642 _143649 s x)). Qed.
Lemma lem8096354 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) (h1 : _107385 = (term17 _143642)) : (term23 _143642 _143649 s x) = (term24 _143642 _143649 s x _107385).
Proof. exact (MK_COMB (@lem8096353 _143642 _143649 s x) (@lem8096352 _143642 _107385 h1)). Qed.
Lemma lem8096355 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) (h1 : _107385 = (term17 _143642)) : (term2 _143642 _143649 r s x) = (term28 _143642 _143649 r s x _107385).
Proof. exact (MK_COMB (@lem8096349 _143642 _143649 r x _107385 h1) (@lem8096354 _143642 _143649 s x _107385 h1)). Qed.
Lemma lem8096356 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) (h1 : _107385 = (term17 _143642)) : ((term1 _143642 _143649 r s x) = (term2 _143642 _143649 r s x)) = ((term19 _143642 _143649 r s x _107385) = (term28 _143642 _143649 r s x _107385)).
Proof. exact (MK_COMB (@lem8096342 _143642 _143649 r s x _107385 h1) (@lem8096355 _143642 _143649 r s x _107385 h1)). Qed.
Lemma lem8096357 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8096358 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) (h1 : _107385 = (term17 _143642)) : (term4 _143642 _143649 r s x) = (term29 _143642 _143649 r s x _107385).
Proof. exact (MK_COMB (@lem8096357) (@lem8096356 _143642 _143649 r s x _107385 h1)). Qed.
Lemma lem8096359 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8096360 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) (h1 : _107385 = (term17 _143642)) : (term30 _143642 _143649 r s x) = (term31 _143642 _143649 r s x _107385).
Proof. exact (MK_COMB (@lem8096359) (@lem8096358 _143642 _143649 r s x _107385 h1)). Qed.
Lemma lem8096361 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem8096362 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) (h1 : _107385 = (term17 _143642)) : (term3 _143642 _143649 r s x) = (term32 _143642 _143649 r s x _107385).
Proof. exact (MK_COMB (@lem8096360 _143642 _143649 r s x _107385 h1) (@lem8096361)). Qed.
Lemma lem8096363 {_143642 : Type'} : (term33 _143642) = (term33 _143642).
Proof. exact (eq_refl (term33 _143642)). Qed.
Lemma lem8096364 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) (h1 : _107385 = (term17 _143642)) : (term15 _143642 _143649 r s x) = (term34 _143642 _143649 r s x _107385).
Proof. exact (MK_COMB (@lem8096363 _143642) (@lem8096362 _143642 _143649 r s x _107385 h1)). Qed.
Lemma lem8096365 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : term35 _143642 _143649 r s x) : term35 _143642 _143649 r s x.
Proof. exact (h1). Qed.
Lemma lem8096366 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : term35 _143642 _143649 r s x) : term36 _143642 _143649 r s x _107385.
Proof. exact (@lem8096365 _143642 _143649 r s x h1 _107385). Qed.
Lemma lem8096367 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term36 _143642 _143649 r s x _107385) = (term34 _143642 _143649 r s x _107385).
Proof. exact (eq_refl (term36 _143642 _143649 r s x _107385)). Qed.
Lemma lem8096368 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : term35 _143642 _143649 r s x) : term34 _143642 _143649 r s x _107385.
Proof. exact (EQ_MP (@lem8096367 _143642 _143649 r s x _107385) (@lem8096366 _143642 _143649 _107385 r s x h1)). Qed.
Lemma lem8096369 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) (h1 : _107385 = (term17 _143642)) : (term34 _143642 _143649 r s x _107385) = (term15 _143642 _143649 r s x).
Proof. exact (SYM (@lem8096364 _143642 _143649 r s x _107385 h1)). Qed.
Lemma lem8096370 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) (h1 : term35 _143642 _143649 r s x) (h2 : _107385 = (term17 _143642)) : term15 _143642 _143649 r s x.
Proof. exact (EQ_MP (@lem8096369 _143642 _143649 r s x _107385 h2) (@lem8096368 _143642 _143649 _107385 r s x h1)). Qed.
Lemma lem8096371 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) (h1 : _107385 = (term17 _143642)) : term37 _143642 _143649 r s x.
Proof. exact (fun h0 : term35 _143642 _143649 r s x => @lem8096370 _143642 _143649 r s x _107385 h0 h1). Qed.
Lemma lem8096372 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : term38 _143642 _143649 r s x.
Proof. exact (@lem51 (term15 _143642 _143649 r s x) (term35 _143642 _143649 r s x) (term3 _143642 _143649 r s x)). Qed.
Lemma lem8096373 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) (h1 : _107385 = (term17 _143642)) : term39 _143642 _143649 r s x.
Proof. exact (@lem8096372 _143642 _143649 r s x (@lem8096371 _143642 _143649 r s x _107385 h1)). Qed.
Lemma lem8096374 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) (h1 : _107385 = (term17 _143642)) : term40 _143642 _143649 r s x.
Proof. exact (@lem8096373 _143642 _143649 r s x _107385 h1 (@lem8096333 _143642 _143649 r s x)). Qed.
Lemma lem8096375 {_143642 : Type'} : (term17 _143642) = (term17 _143642).
Proof. exact (eq_refl (term17 _143642)). Qed.
Lemma lem8096376 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : term41 _143642 _143649 _107385 r s x.
Proof. exact (fun h0 : _107385 = (term17 _143642) => @lem8096374 _143642 _143649 r s x _107385 h0). Qed.
Lemma lem8096377 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : term42 _143642 _143649 r s x.
Proof. exact (@lem8096376 _143642 _143649 (term17 _143642) r s x). Qed.
Lemma lem8096378 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : term40 _143642 _143649 r s x.
Proof. exact (@lem8096377 _143642 _143649 r s x (@lem8096375 _143642)). Qed.
Lemma lem8096379 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : term35 _143642 _143649 r s x) : term35 _143642 _143649 r s x.
Proof. exact (h1). Qed.
Lemma lem8096380 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : term43 _143642 _143649 r s x.
Proof. exact (fun h0 : term35 _143642 _143649 r s x => @lem8096379 _143642 _143649 r s x h0). Qed.
Lemma lem8096381 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : term44 _143642 _143649 r s x.
Proof. exact (@lem51 (term35 _143642 _143649 r s x) (term35 _143642 _143649 r s x) (term3 _143642 _143649 r s x)). Qed.
Lemma lem8096382 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : term45 _143642 _143649 r s x.
Proof. exact (@lem8096381 _143642 _143649 r s x (@lem8096380 _143642 _143649 r s x)). Qed.
Lemma lem8096383 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : term40 _143642 _143649 r s x.
Proof. exact (@lem8096382 _143642 _143649 r s x (@lem8096378 _143642 _143649 r s x)). Qed.
Lemma lem8096384 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : term40 _143642 _143649 r s x) : term40 _143642 _143649 r s x.
Proof. exact (h1). Qed.
Lemma lem8096385 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : term35 _143642 _143649 r s x) : term35 _143642 _143649 r s x.
Proof. exact (h1). Qed.
Lemma lem8096386 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : term35 _143642 _143649 r s x) (h2 : term40 _143642 _143649 r s x) : term3 _143642 _143649 r s x.
Proof. exact (@lem8096384 _143642 _143649 r s x h2 (@lem8096385 _143642 _143649 r s x h1)). Qed.
Lemma lem8096387 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : term35 _143642 _143649 r s x) : term46 _143642 _143649 r s x.
Proof. exact (fun h0 : term40 _143642 _143649 r s x => @lem8096386 _143642 _143649 r s x h1 h0). Qed.
Lemma lem8096388 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : term40 _143642 _143649 r s x) : term40 _143642 _143649 r s x.
Proof. exact (h1). Qed.
Lemma lem8096389 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : term35 _143642 _143649 r s x) (h2 : term40 _143642 _143649 r s x) : term3 _143642 _143649 r s x.
Proof. exact (@lem8096387 _143642 _143649 r s x h1 (@lem8096388 _143642 _143649 r s x h2)). Qed.
Lemma lem8096390 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : term40 _143642 _143649 r s x) : term40 _143642 _143649 r s x.
Proof. exact (fun h0 : term35 _143642 _143649 r s x => @lem8096389 _143642 _143649 r s x h0 h1). Qed.
Lemma lem8096391 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : term45 _143642 _143649 r s x.
Proof. exact (fun h0 : term40 _143642 _143649 r s x => @lem8096390 _143642 _143649 r s x h0). Qed.
Lemma lem8096394 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : term40 _143642 _143649 r s x.
Proof. exact (@lem8096391 _143642 _143649 r s x (@lem8096383 _143642 _143649 r s x)). Qed.
Lemma lem8096395 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : term40 _143642 _143649 r s x.
Proof. exact (@lem8096394 _143642 _143649 r s x). Qed.
Lemma lem8096415 {A : Type'} (t : Prop) : (term47 A t) = t.
Proof. exact (EQ_MP (@lem16458 A t) (@lem16457 A t)). Qed.
Lemma lem8096416 {_143642 : Type'} (t : Prop) : (term47 _143642 t) = t.
Proof. exact (@lem8096415 _143642 t). Qed.
Lemma lem8096417 {_143642 : Type'} : (term14 _143642) = (False -> False).
Proof. exact (@lem8096416 _143642 (False -> False)). Qed.
Lemma lem8096419 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem16473 t)). Qed.
Lemma lem8096420 : (False -> False) = True.
Proof. exact (@lem8096419 False). Qed.
Lemma lem8096421 {_143642 : Type'} : (term14 _143642) = True.
Proof. exact (TRANS (@lem8096417 _143642) (@lem8096420)). Qed.
Lemma lem8096422 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8096423 {_143642 : Type'} : (term33 _143642) = (imp True).
Proof. exact (MK_COMB (@lem8096422) (@lem8096421 _143642)). Qed.
Lemma lem8096425 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem8096426 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term32 _143642 _143649 r s x _107385) = (term48 _143642 _143649 r s x _107385).
Proof. exact (@lem8096425 (term29 _143642 _143649 r s x _107385)). Qed.
Lemma lem8096428 (t : Prop) : (term49 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem8096429 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term48 _143642 _143649 r s x _107385) = ((term19 _143642 _143649 r s x _107385) = (term28 _143642 _143649 r s x _107385)).
Proof. exact (@lem8096428 ((term19 _143642 _143649 r s x _107385) = (term28 _143642 _143649 r s x _107385))). Qed.
Lemma lem8096430 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term32 _143642 _143649 r s x _107385) = ((term19 _143642 _143649 r s x _107385) = (term28 _143642 _143649 r s x _107385)).
Proof. exact (TRANS (@lem8096426 _143642 _143649 r s x _107385) (@lem8096429 _143642 _143649 r s x _107385)). Qed.
Lemma lem8096443 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term34 _143642 _143649 r s x _107385) = (term50 _143642 _143649 r s x _107385).
Proof. exact (MK_COMB (@lem8096423 _143642) (@lem8096430 _143642 _143649 r s x _107385)). Qed.
Lemma lem8096445 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem16471 t)). Qed.
Lemma lem8096446 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term50 _143642 _143649 r s x _107385) = ((term19 _143642 _143649 r s x _107385) = (term28 _143642 _143649 r s x _107385)).
Proof. exact (@lem8096445 ((term19 _143642 _143649 r s x _107385) = (term28 _143642 _143649 r s x _107385))). Qed.
Lemma lem8096459 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term34 _143642 _143649 r s x _107385) = ((term19 _143642 _143649 r s x _107385) = (term28 _143642 _143649 r s x _107385)).
Proof. exact (TRANS (@lem8096443 _143642 _143649 r s x _107385) (@lem8096446 _143642 _143649 r s x _107385)). Qed.
Lemma lem8096460 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term51 _143642 _143649 r s x) = (term52 _143642 _143649 r s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8096459 _143642 _143649 r s x _107385)). Qed.
Lemma lem8096461 {_143642 : Type'} : (@all _143642) = (@all _143642).
Proof. exact (eq_refl (@all _143642)). Qed.
Lemma lem8096462 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term35 _143642 _143649 r s x) = (term53 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8096461 _143642) (@lem8096460 _143642 _143649 r s x)). Qed.
Lemma lem8096467 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term54 _143642 _143649 s x) = (term55 _143642 _143649 s x).
Proof. exact (fun_ext (fun r : type1470 _143642 _143649 => @lem8096462 _143642 _143649 r s x)). Qed.
Lemma lem8096468 {_143642 _143649 : Type'} : (@all (_143649 -> _143642 -> Prop)) = (@all (_143649 -> _143642 -> Prop)).
Proof. exact (eq_refl (@all (_143649 -> _143642 -> Prop))). Qed.
Lemma lem8096469 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term56 _143642 _143649 s x) = (term57 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8096468 _143642 _143649) (@lem8096467 _143642 _143649 s x)). Qed.
Lemma lem8096474 {_143642 _143649 : Type'} (x : _143649) : (term58 _143642 _143649 x) = (term59 _143642 _143649 x).
Proof. exact (fun_ext (fun s : type1470 _143642 _143649 => @lem8096469 _143642 _143649 s x)). Qed.
Lemma lem8096475 {_143642 _143649 : Type'} : (@all (_143649 -> _143642 -> Prop)) = (@all (_143649 -> _143642 -> Prop)).
Proof. exact (eq_refl (@all (_143649 -> _143642 -> Prop))). Qed.
Lemma lem8096476 {_143642 _143649 : Type'} (x : _143649) : (term60 _143642 _143649 x) = (term61 _143642 _143649 x).
Proof. exact (MK_COMB (@lem8096475 _143642 _143649) (@lem8096474 _143642 _143649 x)). Qed.
Lemma lem8096481 {_143642 _143649 : Type'} : (term62 _143642 _143649) = (term63 _143642 _143649).
Proof. exact (fun_ext (fun x : _143649 => @lem8096476 _143642 _143649 x)). Qed.
Lemma lem8096482 {_143649 : Type'} : (@all _143649) = (@all _143649).
Proof. exact (eq_refl (@all _143649)). Qed.
Lemma lem8096491 {_143642 _143649 : Type'} : (term64 _143642 _143649) = (term65 _143642 _143649).
Proof. exact (MK_COMB (@lem8096482 _143649) (@lem8096481 _143642 _143649)). Qed.
Lemma lem8096507 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 s x) = False) : (term66 _143642 _143649 s x) = False.
Proof. exact (h1). Qed.
Lemma lem8096508 {_143642 : Type'} : (@COND _143642) = (@COND _143642).
Proof. exact (eq_refl (@COND _143642)). Qed.
Lemma lem8096509 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 s x) = False) : (term67 _143642 _143649 s x) = (@COND _143642 False).
Proof. exact (MK_COMB (@lem8096508 _143642) (@lem8096507 _143642 _143649 s x h1)). Qed.
Lemma lem8096510 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term68 _143642 _143649 s x) = (term68 _143642 _143649 s x).
Proof. exact (eq_refl (term68 _143642 _143649 s x)). Qed.
Lemma lem8096511 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 s x) = False) : (term22 _143642 _143649 s x) = (term69 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8096509 _143642 _143649 s x h1) (@lem8096510 _143642 _143649 s x)). Qed.
Lemma lem8096512 {_143642 : Type'} (_107385 : _143642) : _107385 = _107385.
Proof. exact (eq_refl _107385). Qed.
Lemma lem8096513 {_143642 _143649 : Type'} (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 s x) = False) : (term24 _143642 _143649 s x _107385) = (term70 _143642 _143649 s x _107385).
Proof. exact (MK_COMB (@lem8096511 _143642 _143649 s x h1) (@lem8096512 _143642 _107385)). Qed.
Lemma lem8096515 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem8096516 {_143642 : Type'} (t1 : _143642) (t2 : _143642) : (@COND _143642 False t1 t2) = t2.
Proof. exact (@lem8096515 _143642 t1 t2). Qed.
Lemma lem8096517 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term70 _143642 _143649 s x _107385) = _107385.
Proof. exact (@lem8096516 _143642 (term68 _143642 _143649 s x) _107385). Qed.
Lemma lem8096518 {_143642 _143649 : Type'} (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 s x) = False) : (term24 _143642 _143649 s x _107385) = _107385.
Proof. exact (TRANS (@lem8096513 _143642 _143649 _107385 s x h1) (@lem8096517 _143642 _143649 s x _107385)). Qed.
Lemma lem8096519 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term27 _143642 _143649 r x _107385) = (term27 _143642 _143649 r x _107385).
Proof. exact (eq_refl (term27 _143642 _143649 r x _107385)). Qed.
Lemma lem8096520 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 s x) = False) : (term28 _143642 _143649 r s x _107385) = (term71 _143642 _143649 r x _107385).
Proof. exact (MK_COMB (@lem8096519 _143642 _143649 r x _107385) (@lem8096518 _143642 _143649 _107385 s x h1)). Qed.
Lemma lem8096521 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term21 _143642 _143649 r s x _107385) = (term21 _143642 _143649 r s x _107385).
Proof. exact (eq_refl (term21 _143642 _143649 r s x _107385)). Qed.
Lemma lem8096522 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 s x) = False) : ((term19 _143642 _143649 r s x _107385) = (term28 _143642 _143649 r s x _107385)) = ((term19 _143642 _143649 r s x _107385) = (term71 _143642 _143649 r x _107385)).
Proof. exact (MK_COMB (@lem8096521 _143642 _143649 r s x _107385) (@lem8096520 _143642 _143649 r _107385 s x h1)). Qed.
Lemma lem8096525 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 s x) = False) : (term52 _143642 _143649 r s x) = (term72 _143642 _143649 s r x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8096522 _143642 _143649 r _107385 s x h1)). Qed.
Lemma lem8096526 {_143642 : Type'} : (@all _143642) = (@all _143642).
Proof. exact (eq_refl (@all _143642)). Qed.
Lemma lem8096527 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 s x) = False) : (term53 _143642 _143649 r s x) = (term73 _143642 _143649 s r x).
Proof. exact (MK_COMB (@lem8096526 _143642) (@lem8096525 _143642 _143649 r s x h1)). Qed.
Lemma lem8096532 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 s x) = False) : (term55 _143642 _143649 s x) = (term74 _143642 _143649 s x).
Proof. exact (fun_ext (fun r : type1470 _143642 _143649 => @lem8096527 _143642 _143649 r s x h1)). Qed.
Lemma lem8096533 {_143642 _143649 : Type'} : (@all (_143649 -> _143642 -> Prop)) = (@all (_143649 -> _143642 -> Prop)).
Proof. exact (eq_refl (@all (_143649 -> _143642 -> Prop))). Qed.
Lemma lem8096534 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 s x) = False) : (term57 _143642 _143649 s x) = (term75 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8096533 _143642 _143649) (@lem8096532 _143642 _143649 s x h1)). Qed.
Lemma lem8096539 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : term76 _143642 _143649 s x.
Proof. exact (fun h0 : (term66 _143642 _143649 s x) = False => @lem8096534 _143642 _143649 s x h0). Qed.
Lemma lem8096553 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 s x) = True) : (term66 _143642 _143649 s x) = True.
Proof. exact (h1). Qed.
Lemma lem8096554 {_143642 : Type'} : (@COND _143642) = (@COND _143642).
Proof. exact (eq_refl (@COND _143642)). Qed.
Lemma lem8096555 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 s x) = True) : (term67 _143642 _143649 s x) = (@COND _143642 True).
Proof. exact (MK_COMB (@lem8096554 _143642) (@lem8096553 _143642 _143649 s x h1)). Qed.
Lemma lem8096556 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term68 _143642 _143649 s x) = (term68 _143642 _143649 s x).
Proof. exact (eq_refl (term68 _143642 _143649 s x)). Qed.
Lemma lem8096557 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 s x) = True) : (term22 _143642 _143649 s x) = (term77 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8096555 _143642 _143649 s x h1) (@lem8096556 _143642 _143649 s x)). Qed.
Lemma lem8096558 {_143642 : Type'} (_107385 : _143642) : _107385 = _107385.
Proof. exact (eq_refl _107385). Qed.
Lemma lem8096559 {_143642 _143649 : Type'} (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 s x) = True) : (term24 _143642 _143649 s x _107385) = (term78 _143642 _143649 s x _107385).
Proof. exact (MK_COMB (@lem8096557 _143642 _143649 s x h1) (@lem8096558 _143642 _107385)). Qed.
Lemma lem8096561 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem8096562 {_143642 : Type'} (t2 : _143642) (t1 : _143642) : (@COND _143642 True t1 t2) = t1.
Proof. exact (@lem8096561 _143642 t2 t1). Qed.
Lemma lem8096563 {_143642 _143649 : Type'} (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term78 _143642 _143649 s x _107385) = (term68 _143642 _143649 s x).
Proof. exact (@lem8096562 _143642 _107385 (term68 _143642 _143649 s x)). Qed.
Lemma lem8096564 {_143642 _143649 : Type'} (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 s x) = True) : (term24 _143642 _143649 s x _107385) = (term68 _143642 _143649 s x).
Proof. exact (TRANS (@lem8096559 _143642 _143649 _107385 s x h1) (@lem8096563 _143642 _143649 _107385 s x)). Qed.
Lemma lem8096565 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term27 _143642 _143649 r x _107385) = (term27 _143642 _143649 r x _107385).
Proof. exact (eq_refl (term27 _143642 _143649 r x _107385)). Qed.
Lemma lem8096566 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 s x) = True) : (term28 _143642 _143649 r s x _107385) = (term79 _143642 _143649 r _107385 s x).
Proof. exact (MK_COMB (@lem8096565 _143642 _143649 r x _107385) (@lem8096564 _143642 _143649 _107385 s x h1)). Qed.
Lemma lem8096567 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term21 _143642 _143649 r s x _107385) = (term21 _143642 _143649 r s x _107385).
Proof. exact (eq_refl (term21 _143642 _143649 r s x _107385)). Qed.
Lemma lem8096568 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 s x) = True) : ((term19 _143642 _143649 r s x _107385) = (term28 _143642 _143649 r s x _107385)) = ((term19 _143642 _143649 r s x _107385) = (term79 _143642 _143649 r _107385 s x)).
Proof. exact (MK_COMB (@lem8096567 _143642 _143649 r s x _107385) (@lem8096566 _143642 _143649 r _107385 s x h1)). Qed.
Lemma lem8096571 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 s x) = True) : (term52 _143642 _143649 r s x) = (term80 _143642 _143649 r s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8096568 _143642 _143649 r _107385 s x h1)). Qed.
Lemma lem8096572 {_143642 : Type'} : (@all _143642) = (@all _143642).
Proof. exact (eq_refl (@all _143642)). Qed.
Lemma lem8096573 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 s x) = True) : (term53 _143642 _143649 r s x) = (term81 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8096572 _143642) (@lem8096571 _143642 _143649 r s x h1)). Qed.
Lemma lem8096578 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 s x) = True) : (term55 _143642 _143649 s x) = (term82 _143642 _143649 s x).
Proof. exact (fun_ext (fun r : type1470 _143642 _143649 => @lem8096573 _143642 _143649 r s x h1)). Qed.
Lemma lem8096579 {_143642 _143649 : Type'} : (@all (_143649 -> _143642 -> Prop)) = (@all (_143649 -> _143642 -> Prop)).
Proof. exact (eq_refl (@all (_143649 -> _143642 -> Prop))). Qed.
Lemma lem8096580 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 s x) = True) : (term57 _143642 _143649 s x) = (term83 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8096579 _143642 _143649) (@lem8096578 _143642 _143649 s x h1)). Qed.
Lemma lem8096585 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : term84 _143642 _143649 s x.
Proof. exact (fun h0 : (term66 _143642 _143649 s x) = True => @lem8096580 _143642 _143649 s x h0). Qed.
Lemma lem8096586 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : term85 _143642 _143649 s x.
Proof. exact (conj (@lem8096539 _143642 _143649 s x) (@lem8096585 _143642 _143649 s x)). Qed.
Lemma lem8096588 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term86 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem8096589 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : term87 _143642 _143649 s x.
Proof. exact (@lem8096588 (term57 _143642 _143649 s x) (term83 _143642 _143649 s x) (term66 _143642 _143649 s x) (term75 _143642 _143649 s x)). Qed.
Lemma lem8096604 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term57 _143642 _143649 s x) = (term88 _143642 _143649 s x).
Proof. exact (@lem8096589 _143642 _143649 s x (@lem8096586 _143642 _143649 s x)). Qed.
Lemma lem8096612 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term89 _143642 _143649 r s x) = False) : (term89 _143642 _143649 r s x) = False.
Proof. exact (h1). Qed.
Lemma lem8096613 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term89 _143642 _143649 r s x) = False) : (term89 _143642 _143649 r s x) = False.
Proof. exact (@lem8096612 _143642 _143649 r s x h1). Qed.
Lemma lem8096614 {_143642 : Type'} : (@COND _143642) = (@COND _143642).
Proof. exact (eq_refl (@COND _143642)). Qed.
Lemma lem8096615 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term89 _143642 _143649 r s x) = False) : (term90 _143642 _143649 r s x) = (@COND _143642 False).
Proof. exact (MK_COMB (@lem8096614 _143642) (@lem8096613 _143642 _143649 r s x h1)). Qed.
Lemma lem8096620 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term91 _143642 _143649 r s x) = (term91 _143642 _143649 r s x).
Proof. exact (eq_refl (term91 _143642 _143649 r s x)). Qed.
Lemma lem8096621 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term89 _143642 _143649 r s x) = False) : (term18 _143642 _143649 r s x) = (term92 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8096615 _143642 _143649 r s x h1) (@lem8096620 _143642 _143649 r s x)). Qed.
Lemma lem8096622 {_143642 : Type'} (_107385 : _143642) : _107385 = _107385.
Proof. exact (eq_refl _107385). Qed.
Lemma lem8096623 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term89 _143642 _143649 r s x) = False) : (term19 _143642 _143649 r s x _107385) = (term93 _143642 _143649 r s x _107385).
Proof. exact (MK_COMB (@lem8096621 _143642 _143649 r s x h1) (@lem8096622 _143642 _107385)). Qed.
Lemma lem8096625 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem8096626 {_143642 : Type'} (t1 : _143642) (t2 : _143642) : (@COND _143642 False t1 t2) = t2.
Proof. exact (@lem8096625 _143642 t1 t2). Qed.
Lemma lem8096627 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term93 _143642 _143649 r s x _107385) = _107385.
Proof. exact (@lem8096626 _143642 (term91 _143642 _143649 r s x) _107385). Qed.
Lemma lem8096628 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term89 _143642 _143649 r s x) = False) : (term19 _143642 _143649 r s x _107385) = _107385.
Proof. exact (TRANS (@lem8096623 _143642 _143649 _107385 r s x h1) (@lem8096627 _143642 _143649 r s x _107385)). Qed.
Lemma lem8096629 {_143642 : Type'} : (@eq _143642) = (@eq _143642).
Proof. exact (eq_refl (@eq _143642)). Qed.
Lemma lem8096630 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term89 _143642 _143649 r s x) = False) : (term21 _143642 _143649 r s x _107385) = (@eq _143642 _107385).
Proof. exact (MK_COMB (@lem8096629 _143642) (@lem8096628 _143642 _143649 _107385 r s x h1)). Qed.
Lemma lem8096635 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term71 _143642 _143649 r x _107385) = (term71 _143642 _143649 r x _107385).
Proof. exact (eq_refl (term71 _143642 _143649 r x _107385)). Qed.
Lemma lem8096636 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term89 _143642 _143649 r s x) = False) : ((term19 _143642 _143649 r s x _107385) = (term71 _143642 _143649 r x _107385)) = (_107385 = (term71 _143642 _143649 r x _107385)).
Proof. exact (MK_COMB (@lem8096630 _143642 _143649 _107385 r s x h1) (@lem8096635 _143642 _143649 r x _107385)). Qed.
Lemma lem8096639 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term89 _143642 _143649 r s x) = False) : (term72 _143642 _143649 s r x) = (term94 _143642 _143649 r x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8096636 _143642 _143649 _107385 r s x h1)). Qed.
Lemma lem8096640 {_143642 : Type'} : (@all _143642) = (@all _143642).
Proof. exact (eq_refl (@all _143642)). Qed.
Lemma lem8096641 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term89 _143642 _143649 r s x) = False) : (term73 _143642 _143649 s r x) = (term95 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8096640 _143642) (@lem8096639 _143642 _143649 r s x h1)). Qed.
Lemma lem8096646 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) : term96 _143642 _143649 s r x.
Proof. exact (fun h0 : (term89 _143642 _143649 r s x) = False => @lem8096641 _143642 _143649 r s x h0). Qed.
Lemma lem8096652 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term89 _143642 _143649 r s x) = True) : (term89 _143642 _143649 r s x) = True.
Proof. exact (h1). Qed.
Lemma lem8096653 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term89 _143642 _143649 r s x) = True) : (term89 _143642 _143649 r s x) = True.
Proof. exact (@lem8096652 _143642 _143649 r s x h1). Qed.
Lemma lem8096654 {_143642 : Type'} : (@COND _143642) = (@COND _143642).
Proof. exact (eq_refl (@COND _143642)). Qed.
Lemma lem8096655 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term89 _143642 _143649 r s x) = True) : (term90 _143642 _143649 r s x) = (@COND _143642 True).
Proof. exact (MK_COMB (@lem8096654 _143642) (@lem8096653 _143642 _143649 r s x h1)). Qed.
Lemma lem8096660 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term91 _143642 _143649 r s x) = (term91 _143642 _143649 r s x).
Proof. exact (eq_refl (term91 _143642 _143649 r s x)). Qed.
Lemma lem8096661 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term89 _143642 _143649 r s x) = True) : (term18 _143642 _143649 r s x) = (term97 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8096655 _143642 _143649 r s x h1) (@lem8096660 _143642 _143649 r s x)). Qed.
Lemma lem8096662 {_143642 : Type'} (_107385 : _143642) : _107385 = _107385.
Proof. exact (eq_refl _107385). Qed.
Lemma lem8096663 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term89 _143642 _143649 r s x) = True) : (term19 _143642 _143649 r s x _107385) = (term98 _143642 _143649 r s x _107385).
Proof. exact (MK_COMB (@lem8096661 _143642 _143649 r s x h1) (@lem8096662 _143642 _107385)). Qed.
Lemma lem8096665 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem8096666 {_143642 : Type'} (t2 : _143642) (t1 : _143642) : (@COND _143642 True t1 t2) = t1.
Proof. exact (@lem8096665 _143642 t2 t1). Qed.
Lemma lem8096667 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term98 _143642 _143649 r s x _107385) = (term91 _143642 _143649 r s x).
Proof. exact (@lem8096666 _143642 _107385 (term91 _143642 _143649 r s x)). Qed.
Lemma lem8096668 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term89 _143642 _143649 r s x) = True) : (term19 _143642 _143649 r s x _107385) = (term91 _143642 _143649 r s x).
Proof. exact (TRANS (@lem8096663 _143642 _143649 _107385 r s x h1) (@lem8096667 _143642 _143649 _107385 r s x)). Qed.
Lemma lem8096669 {_143642 : Type'} : (@eq _143642) = (@eq _143642).
Proof. exact (eq_refl (@eq _143642)). Qed.
Lemma lem8096670 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term89 _143642 _143649 r s x) = True) : (term21 _143642 _143649 r s x _107385) = (term99 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8096669 _143642) (@lem8096668 _143642 _143649 _107385 r s x h1)). Qed.
Lemma lem8096675 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term71 _143642 _143649 r x _107385) = (term71 _143642 _143649 r x _107385).
Proof. exact (eq_refl (term71 _143642 _143649 r x _107385)). Qed.
Lemma lem8096676 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term89 _143642 _143649 r s x) = True) : ((term19 _143642 _143649 r s x _107385) = (term71 _143642 _143649 r x _107385)) = ((term91 _143642 _143649 r s x) = (term71 _143642 _143649 r x _107385)).
Proof. exact (MK_COMB (@lem8096670 _143642 _143649 _107385 r s x h1) (@lem8096675 _143642 _143649 r x _107385)). Qed.
Lemma lem8096679 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term89 _143642 _143649 r s x) = True) : (term72 _143642 _143649 s r x) = (term100 _143642 _143649 s r x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8096676 _143642 _143649 _107385 r s x h1)). Qed.
Lemma lem8096680 {_143642 : Type'} : (@all _143642) = (@all _143642).
Proof. exact (eq_refl (@all _143642)). Qed.
Lemma lem8096681 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term89 _143642 _143649 r s x) = True) : (term73 _143642 _143649 s r x) = (term101 _143642 _143649 s r x).
Proof. exact (MK_COMB (@lem8096680 _143642) (@lem8096679 _143642 _143649 r s x h1)). Qed.
Lemma lem8096686 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) : term102 _143642 _143649 s r x.
Proof. exact (fun h0 : (term89 _143642 _143649 r s x) = True => @lem8096681 _143642 _143649 r s x h0). Qed.
Lemma lem8096687 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) : term103 _143642 _143649 s r x.
Proof. exact (conj (@lem8096646 _143642 _143649 s r x) (@lem8096686 _143642 _143649 s r x)). Qed.
Lemma lem8096689 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term86 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem8096690 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) : term104 _143642 _143649 s r x.
Proof. exact (@lem8096689 (term73 _143642 _143649 s r x) (term101 _143642 _143649 s r x) (term89 _143642 _143649 r s x) (term95 _143642 _143649 r x)). Qed.
Lemma lem8096705 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) : (term73 _143642 _143649 s r x) = (term105 _143642 _143649 s r x).
Proof. exact (@lem8096690 _143642 _143649 s r x (@lem8096687 _143642 _143649 s r x)). Qed.
Lemma lem8096709 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term106 _143642 _143649 r x) = False.
Proof. exact (h1). Qed.
Lemma lem8096710 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term106 _143642 _143649 r x) = False.
Proof. exact (@lem8096709 _143642 _143649 r x h1). Qed.
Lemma lem8096711 {_143642 : Type'} : (@COND (_143642 -> Prop)) = (@COND (_143642 -> Prop)).
Proof. exact (eq_refl (@COND (_143642 -> Prop))). Qed.
Lemma lem8096712 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term107 _143642 _143649 r x) = (@COND (_143642 -> Prop) False).
Proof. exact (MK_COMB (@lem8096711 _143642) (@lem8096710 _143642 _143649 r x h1)). Qed.
Lemma lem8096713 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (r x) = (r x).
Proof. exact (eq_refl (r x)). Qed.
Lemma lem8096714 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term108 _143642 _143649 r x) = (term109 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8096712 _143642 _143649 r x h1) (@lem8096713 _143642 _143649 r x)). Qed.
Lemma lem8096715 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem8096716 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term110 _143642 _143649 r s x) = (term111 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8096714 _143642 _143649 r x h1) (@lem8096715 _143642 _143649 s x)). Qed.
Lemma lem8096718 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem8096719 {_143642 : Type'} (t1 : _143642 -> Prop) (t2 : _143642 -> Prop) : (@COND (_143642 -> Prop) False t1 t2) = t2.
Proof. exact (@lem8096718 (_143642 -> Prop) t1 t2). Qed.
Lemma lem8096720 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term111 _143642 _143649 r s x) = (s x).
Proof. exact (@lem8096719 _143642 (r x) (s x)). Qed.
Lemma lem8096721 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term110 _143642 _143649 r s x) = (s x).
Proof. exact (TRANS (@lem8096716 _143642 _143649 s r x h1) (@lem8096720 _143642 _143649 r s x)). Qed.
Lemma lem8096722 {_143642 : Type'} : (@ex1 _143642) = (@ex1 _143642).
Proof. exact (eq_refl (@ex1 _143642)). Qed.
Lemma lem8096723 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term89 _143642 _143649 r s x) = (term66 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8096722 _143642) (@lem8096721 _143642 _143649 s r x h1)). Qed.
Lemma lem8096724 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8096725 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term112 _143642 _143649 r s x) = (term113 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8096724) (@lem8096723 _143642 _143649 s r x h1)). Qed.
Lemma lem8096726 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8096727 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term114 _143642 _143649 r s x) = (term115 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8096726) (@lem8096725 _143642 _143649 s r x h1)). Qed.
Lemma lem8096729 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term106 _143642 _143649 r x) = False.
Proof. exact (h1). Qed.
Lemma lem8096730 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term106 _143642 _143649 r x) = False.
Proof. exact (@lem8096729 _143642 _143649 r x h1). Qed.
Lemma lem8096731 {_143642 : Type'} : (@COND (_143642 -> Prop)) = (@COND (_143642 -> Prop)).
Proof. exact (eq_refl (@COND (_143642 -> Prop))). Qed.
Lemma lem8096732 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term107 _143642 _143649 r x) = (@COND (_143642 -> Prop) False).
Proof. exact (MK_COMB (@lem8096731 _143642) (@lem8096730 _143642 _143649 r x h1)). Qed.
Lemma lem8096733 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (r x) = (r x).
Proof. exact (eq_refl (r x)). Qed.
Lemma lem8096734 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term108 _143642 _143649 r x) = (term109 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8096732 _143642 _143649 r x h1) (@lem8096733 _143642 _143649 r x)). Qed.
Lemma lem8096735 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem8096736 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term110 _143642 _143649 r s x) = (term111 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8096734 _143642 _143649 r x h1) (@lem8096735 _143642 _143649 s x)). Qed.
Lemma lem8096738 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem8096739 {_143642 : Type'} (t1 : _143642 -> Prop) (t2 : _143642 -> Prop) : (@COND (_143642 -> Prop) False t1 t2) = t2.
Proof. exact (@lem8096738 (_143642 -> Prop) t1 t2). Qed.
Lemma lem8096740 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term111 _143642 _143649 r s x) = (s x).
Proof. exact (@lem8096739 _143642 (r x) (s x)). Qed.
Lemma lem8096741 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term110 _143642 _143649 r s x) = (s x).
Proof. exact (TRANS (@lem8096736 _143642 _143649 s r x h1) (@lem8096740 _143642 _143649 r s x)). Qed.
Lemma lem8096742 {_143642 : Type'} : (@ε _143642) = (@ε _143642).
Proof. exact (eq_refl (@ε _143642)). Qed.
Lemma lem8096743 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term91 _143642 _143649 r s x) = (term68 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8096742 _143642) (@lem8096741 _143642 _143649 s r x h1)). Qed.
Lemma lem8096744 {_143642 : Type'} : (@eq _143642) = (@eq _143642).
Proof. exact (eq_refl (@eq _143642)). Qed.
Lemma lem8096745 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term99 _143642 _143649 r s x) = (term116 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8096744 _143642) (@lem8096743 _143642 _143649 s r x h1)). Qed.
Lemma lem8096747 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term106 _143642 _143649 r x) = False.
Proof. exact (h1). Qed.
Lemma lem8096748 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term106 _143642 _143649 r x) = False.
Proof. exact (@lem8096747 _143642 _143649 r x h1). Qed.
Lemma lem8096749 {_143642 : Type'} : (@COND _143642) = (@COND _143642).
Proof. exact (eq_refl (@COND _143642)). Qed.
Lemma lem8096750 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term25 _143642 _143649 r x) = (@COND _143642 False).
Proof. exact (MK_COMB (@lem8096749 _143642) (@lem8096748 _143642 _143649 r x h1)). Qed.
Lemma lem8096751 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term24 _143642 _143649 r x _107385) = (term24 _143642 _143649 r x _107385).
Proof. exact (eq_refl (term24 _143642 _143649 r x _107385)). Qed.
Lemma lem8096752 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term27 _143642 _143649 r x _107385) = (term117 _143642 _143649 r x _107385).
Proof. exact (MK_COMB (@lem8096750 _143642 _143649 r x h1) (@lem8096751 _143642 _143649 r x _107385)). Qed.
Lemma lem8096753 {_143642 : Type'} (_107385 : _143642) : _107385 = _107385.
Proof. exact (eq_refl _107385). Qed.
Lemma lem8096754 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term71 _143642 _143649 r x _107385) = (term118 _143642 _143649 r x _107385).
Proof. exact (MK_COMB (@lem8096752 _143642 _143649 _107385 r x h1) (@lem8096753 _143642 _107385)). Qed.
Lemma lem8096756 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem8096757 {_143642 : Type'} (t1 : _143642) (t2 : _143642) : (@COND _143642 False t1 t2) = t2.
Proof. exact (@lem8096756 _143642 t1 t2). Qed.
Lemma lem8096758 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term118 _143642 _143649 r x _107385) = _107385.
Proof. exact (@lem8096757 _143642 (term24 _143642 _143649 r x _107385) _107385). Qed.
Lemma lem8096759 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term71 _143642 _143649 r x _107385) = _107385.
Proof. exact (TRANS (@lem8096754 _143642 _143649 _107385 r x h1) (@lem8096758 _143642 _143649 r x _107385)). Qed.
Lemma lem8096760 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : ((term91 _143642 _143649 r s x) = (term71 _143642 _143649 r x _107385)) = ((term68 _143642 _143649 s x) = _107385).
Proof. exact (MK_COMB (@lem8096745 _143642 _143649 s r x h1) (@lem8096759 _143642 _143649 _107385 r x h1)). Qed.
Lemma lem8096763 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term100 _143642 _143649 s r x) = (term119 _143642 _143649 s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8096760 _143642 _143649 s _107385 r x h1)). Qed.
Lemma lem8096764 {_143642 : Type'} : (@all _143642) = (@all _143642).
Proof. exact (eq_refl (@all _143642)). Qed.
Lemma lem8096765 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term101 _143642 _143649 s r x) = (term120 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8096764 _143642) (@lem8096763 _143642 _143649 s r x h1)). Qed.
Lemma lem8096770 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term121 _143642 _143649 s r x) = (term122 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8096727 _143642 _143649 s r x h1) (@lem8096765 _143642 _143649 s r x h1)). Qed.
Lemma lem8096773 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8096774 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term123 _143642 _143649 s r x) = (term124 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8096773) (@lem8096770 _143642 _143649 s r x h1)). Qed.
Lemma lem8096776 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term106 _143642 _143649 r x) = False.
Proof. exact (h1). Qed.
Lemma lem8096777 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term106 _143642 _143649 r x) = False.
Proof. exact (@lem8096776 _143642 _143649 r x h1). Qed.
Lemma lem8096778 {_143642 : Type'} : (@COND (_143642 -> Prop)) = (@COND (_143642 -> Prop)).
Proof. exact (eq_refl (@COND (_143642 -> Prop))). Qed.
Lemma lem8096779 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term107 _143642 _143649 r x) = (@COND (_143642 -> Prop) False).
Proof. exact (MK_COMB (@lem8096778 _143642) (@lem8096777 _143642 _143649 r x h1)). Qed.
Lemma lem8096780 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (r x) = (r x).
Proof. exact (eq_refl (r x)). Qed.
Lemma lem8096781 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term108 _143642 _143649 r x) = (term109 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8096779 _143642 _143649 r x h1) (@lem8096780 _143642 _143649 r x)). Qed.
Lemma lem8096782 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem8096783 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term110 _143642 _143649 r s x) = (term111 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8096781 _143642 _143649 r x h1) (@lem8096782 _143642 _143649 s x)). Qed.
Lemma lem8096785 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem8096786 {_143642 : Type'} (t1 : _143642 -> Prop) (t2 : _143642 -> Prop) : (@COND (_143642 -> Prop) False t1 t2) = t2.
Proof. exact (@lem8096785 (_143642 -> Prop) t1 t2). Qed.
Lemma lem8096787 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term111 _143642 _143649 r s x) = (s x).
Proof. exact (@lem8096786 _143642 (r x) (s x)). Qed.
Lemma lem8096788 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term110 _143642 _143649 r s x) = (s x).
Proof. exact (TRANS (@lem8096783 _143642 _143649 s r x h1) (@lem8096787 _143642 _143649 r s x)). Qed.
Lemma lem8096789 {_143642 : Type'} : (@ex1 _143642) = (@ex1 _143642).
Proof. exact (eq_refl (@ex1 _143642)). Qed.
Lemma lem8096790 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term89 _143642 _143649 r s x) = (term66 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8096789 _143642) (@lem8096788 _143642 _143649 s r x h1)). Qed.
Lemma lem8096791 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8096792 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term125 _143642 _143649 r s x) = (term126 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8096791) (@lem8096790 _143642 _143649 s r x h1)). Qed.
Lemma lem8096794 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term106 _143642 _143649 r x) = False.
Proof. exact (h1). Qed.
Lemma lem8096795 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term106 _143642 _143649 r x) = False.
Proof. exact (@lem8096794 _143642 _143649 r x h1). Qed.
Lemma lem8096796 {_143642 : Type'} : (@COND _143642) = (@COND _143642).
Proof. exact (eq_refl (@COND _143642)). Qed.
Lemma lem8096797 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term25 _143642 _143649 r x) = (@COND _143642 False).
Proof. exact (MK_COMB (@lem8096796 _143642) (@lem8096795 _143642 _143649 r x h1)). Qed.
Lemma lem8096798 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term24 _143642 _143649 r x _107385) = (term24 _143642 _143649 r x _107385).
Proof. exact (eq_refl (term24 _143642 _143649 r x _107385)). Qed.
Lemma lem8096799 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term27 _143642 _143649 r x _107385) = (term117 _143642 _143649 r x _107385).
Proof. exact (MK_COMB (@lem8096797 _143642 _143649 r x h1) (@lem8096798 _143642 _143649 r x _107385)). Qed.
Lemma lem8096800 {_143642 : Type'} (_107385 : _143642) : _107385 = _107385.
Proof. exact (eq_refl _107385). Qed.
Lemma lem8096801 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term71 _143642 _143649 r x _107385) = (term118 _143642 _143649 r x _107385).
Proof. exact (MK_COMB (@lem8096799 _143642 _143649 _107385 r x h1) (@lem8096800 _143642 _107385)). Qed.
Lemma lem8096803 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem8096804 {_143642 : Type'} (t1 : _143642) (t2 : _143642) : (@COND _143642 False t1 t2) = t2.
Proof. exact (@lem8096803 _143642 t1 t2). Qed.
Lemma lem8096805 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term118 _143642 _143649 r x _107385) = _107385.
Proof. exact (@lem8096804 _143642 (term24 _143642 _143649 r x _107385) _107385). Qed.
Lemma lem8096806 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term71 _143642 _143649 r x _107385) = _107385.
Proof. exact (TRANS (@lem8096801 _143642 _143649 _107385 r x h1) (@lem8096805 _143642 _143649 r x _107385)). Qed.
Lemma lem8096807 {_143642 : Type'} (_107385 : _143642) : (@eq _143642 _107385) = (@eq _143642 _107385).
Proof. exact (eq_refl (@eq _143642 _107385)). Qed.
Lemma lem8096808 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (_107385 = (term71 _143642 _143649 r x _107385)) = (_107385 = _107385).
Proof. exact (MK_COMB (@lem8096807 _143642 _107385) (@lem8096806 _143642 _143649 _107385 r x h1)). Qed.
Lemma lem8096810 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem8096811 {_143642 : Type'} (x : _143642) : (x = x) = True.
Proof. exact (@lem8096810 _143642 x). Qed.
Lemma lem8096812 {_143642 : Type'} (_107385 : _143642) : (_107385 = _107385) = True.
Proof. exact (@lem8096811 _143642 _107385). Qed.
Lemma lem8096813 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (_107385 = (term71 _143642 _143649 r x _107385)) = True.
Proof. exact (TRANS (@lem8096808 _143642 _143649 _107385 r x h1) (@lem8096812 _143642 _107385)). Qed.
Lemma lem8096814 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term94 _143642 _143649 r x) = (term127 _143642).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8096813 _143642 _143649 _107385 r x h1)). Qed.
Lemma lem8096815 {_143642 : Type'} : (@all _143642) = (@all _143642).
Proof. exact (eq_refl (@all _143642)). Qed.
Lemma lem8096816 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term95 _143642 _143649 r x) = (term128 _143642).
Proof. exact (MK_COMB (@lem8096815 _143642) (@lem8096814 _143642 _143649 r x h1)). Qed.
Lemma lem8096818 {A : Type'} (t : Prop) : (term47 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8096819 {_143642 : Type'} (t : Prop) : (term47 _143642 t) = t.
Proof. exact (@lem8096818 _143642 t). Qed.
Lemma lem8096820 {_143642 : Type'} : (term128 _143642) = True.
Proof. exact (@lem8096819 _143642 True). Qed.
Lemma lem8096821 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term95 _143642 _143649 r x) = True.
Proof. exact (TRANS (@lem8096816 _143642 _143649 r x h1) (@lem8096820 _143642)). Qed.
Lemma lem8096822 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term129 _143642 _143649 s r x) = (term130 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8096792 _143642 _143649 s r x h1) (@lem8096821 _143642 _143649 r x h1)). Qed.
Lemma lem8096824 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem8096825 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term130 _143642 _143649 s x) = True.
Proof. exact (@lem8096824 (term66 _143642 _143649 s x)). Qed.
Lemma lem8096826 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term129 _143642 _143649 s r x) = True.
Proof. exact (TRANS (@lem8096822 _143642 _143649 s r x h1) (@lem8096825 _143642 _143649 s x)). Qed.
Lemma lem8096827 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term105 _143642 _143649 s r x) = (term131 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8096774 _143642 _143649 s r x h1) (@lem8096826 _143642 _143649 s r x h1)). Qed.
Lemma lem8096829 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem8096830 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term131 _143642 _143649 s x) = (term122 _143642 _143649 s x).
Proof. exact (@lem8096829 (term122 _143642 _143649 s x)). Qed.
Lemma lem8096833 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term105 _143642 _143649 s r x) = (term122 _143642 _143649 s x).
Proof. exact (TRANS (@lem8096827 _143642 _143649 s r x h1) (@lem8096830 _143642 _143649 s x)). Qed.
Lemma lem8096834 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : term132 _143642 _143649 r s x.
Proof. exact (fun h0 : (term106 _143642 _143649 r x) = False => @lem8096833 _143642 _143649 s r x h0). Qed.
Lemma lem8096836 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term106 _143642 _143649 r x) = True.
Proof. exact (h1). Qed.
Lemma lem8096837 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term106 _143642 _143649 r x) = True.
Proof. exact (@lem8096836 _143642 _143649 r x h1). Qed.
Lemma lem8096838 {_143642 : Type'} : (@COND (_143642 -> Prop)) = (@COND (_143642 -> Prop)).
Proof. exact (eq_refl (@COND (_143642 -> Prop))). Qed.
Lemma lem8096839 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term107 _143642 _143649 r x) = (@COND (_143642 -> Prop) True).
Proof. exact (MK_COMB (@lem8096838 _143642) (@lem8096837 _143642 _143649 r x h1)). Qed.
Lemma lem8096840 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (r x) = (r x).
Proof. exact (eq_refl (r x)). Qed.
Lemma lem8096841 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term108 _143642 _143649 r x) = (term133 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8096839 _143642 _143649 r x h1) (@lem8096840 _143642 _143649 r x)). Qed.
Lemma lem8096842 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem8096843 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term110 _143642 _143649 r s x) = (term134 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8096841 _143642 _143649 r x h1) (@lem8096842 _143642 _143649 s x)). Qed.
Lemma lem8096845 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem8096846 {_143642 : Type'} (t2 : _143642 -> Prop) (t1 : _143642 -> Prop) : (@COND (_143642 -> Prop) True t1 t2) = t1.
Proof. exact (@lem8096845 (_143642 -> Prop) t2 t1). Qed.
Lemma lem8096847 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) : (term134 _143642 _143649 r s x) = (r x).
Proof. exact (@lem8096846 _143642 (s x) (r x)). Qed.
Lemma lem8096848 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term110 _143642 _143649 r s x) = (r x).
Proof. exact (TRANS (@lem8096843 _143642 _143649 s r x h1) (@lem8096847 _143642 _143649 s r x)). Qed.
Lemma lem8096849 {_143642 : Type'} : (@ex1 _143642) = (@ex1 _143642).
Proof. exact (eq_refl (@ex1 _143642)). Qed.
Lemma lem8096850 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term89 _143642 _143649 r s x) = (term66 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8096849 _143642) (@lem8096848 _143642 _143649 s r x h1)). Qed.
Lemma lem8096851 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8096852 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term112 _143642 _143649 r s x) = (term113 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8096851) (@lem8096850 _143642 _143649 s r x h1)). Qed.
Lemma lem8096853 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8096854 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term114 _143642 _143649 r s x) = (term115 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8096853) (@lem8096852 _143642 _143649 s r x h1)). Qed.
Lemma lem8096856 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term106 _143642 _143649 r x) = True.
Proof. exact (h1). Qed.
Lemma lem8096857 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term106 _143642 _143649 r x) = True.
Proof. exact (@lem8096856 _143642 _143649 r x h1). Qed.
Lemma lem8096858 {_143642 : Type'} : (@COND (_143642 -> Prop)) = (@COND (_143642 -> Prop)).
Proof. exact (eq_refl (@COND (_143642 -> Prop))). Qed.
Lemma lem8096859 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term107 _143642 _143649 r x) = (@COND (_143642 -> Prop) True).
Proof. exact (MK_COMB (@lem8096858 _143642) (@lem8096857 _143642 _143649 r x h1)). Qed.
Lemma lem8096860 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (r x) = (r x).
Proof. exact (eq_refl (r x)). Qed.
Lemma lem8096861 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term108 _143642 _143649 r x) = (term133 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8096859 _143642 _143649 r x h1) (@lem8096860 _143642 _143649 r x)). Qed.
Lemma lem8096862 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem8096863 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term110 _143642 _143649 r s x) = (term134 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8096861 _143642 _143649 r x h1) (@lem8096862 _143642 _143649 s x)). Qed.
Lemma lem8096865 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem8096866 {_143642 : Type'} (t2 : _143642 -> Prop) (t1 : _143642 -> Prop) : (@COND (_143642 -> Prop) True t1 t2) = t1.
Proof. exact (@lem8096865 (_143642 -> Prop) t2 t1). Qed.
Lemma lem8096867 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) : (term134 _143642 _143649 r s x) = (r x).
Proof. exact (@lem8096866 _143642 (s x) (r x)). Qed.
Lemma lem8096868 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term110 _143642 _143649 r s x) = (r x).
Proof. exact (TRANS (@lem8096863 _143642 _143649 s r x h1) (@lem8096867 _143642 _143649 s r x)). Qed.
Lemma lem8096869 {_143642 : Type'} : (@ε _143642) = (@ε _143642).
Proof. exact (eq_refl (@ε _143642)). Qed.
Lemma lem8096870 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term91 _143642 _143649 r s x) = (term68 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8096869 _143642) (@lem8096868 _143642 _143649 s r x h1)). Qed.
Lemma lem8096871 {_143642 : Type'} : (@eq _143642) = (@eq _143642).
Proof. exact (eq_refl (@eq _143642)). Qed.
Lemma lem8096872 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term99 _143642 _143649 r s x) = (term116 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8096871 _143642) (@lem8096870 _143642 _143649 s r x h1)). Qed.
Lemma lem8096874 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term106 _143642 _143649 r x) = True.
Proof. exact (h1). Qed.
Lemma lem8096875 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term106 _143642 _143649 r x) = True.
Proof. exact (@lem8096874 _143642 _143649 r x h1). Qed.
Lemma lem8096876 {_143642 : Type'} : (@COND _143642) = (@COND _143642).
Proof. exact (eq_refl (@COND _143642)). Qed.
Lemma lem8096877 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term25 _143642 _143649 r x) = (@COND _143642 True).
Proof. exact (MK_COMB (@lem8096876 _143642) (@lem8096875 _143642 _143649 r x h1)). Qed.
Lemma lem8096878 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term24 _143642 _143649 r x _107385) = (term24 _143642 _143649 r x _107385).
Proof. exact (eq_refl (term24 _143642 _143649 r x _107385)). Qed.
Lemma lem8096879 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term27 _143642 _143649 r x _107385) = (term135 _143642 _143649 r x _107385).
Proof. exact (MK_COMB (@lem8096877 _143642 _143649 r x h1) (@lem8096878 _143642 _143649 r x _107385)). Qed.
Lemma lem8096880 {_143642 : Type'} (_107385 : _143642) : _107385 = _107385.
Proof. exact (eq_refl _107385). Qed.
Lemma lem8096881 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term71 _143642 _143649 r x _107385) = (term136 _143642 _143649 r x _107385).
Proof. exact (MK_COMB (@lem8096879 _143642 _143649 _107385 r x h1) (@lem8096880 _143642 _107385)). Qed.
Lemma lem8096883 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem8096884 {_143642 : Type'} (t2 : _143642) (t1 : _143642) : (@COND _143642 True t1 t2) = t1.
Proof. exact (@lem8096883 _143642 t2 t1). Qed.
Lemma lem8096885 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term136 _143642 _143649 r x _107385) = (term24 _143642 _143649 r x _107385).
Proof. exact (@lem8096884 _143642 _107385 (term24 _143642 _143649 r x _107385)). Qed.
Lemma lem8096886 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term71 _143642 _143649 r x _107385) = (term24 _143642 _143649 r x _107385).
Proof. exact (TRANS (@lem8096881 _143642 _143649 _107385 r x h1) (@lem8096885 _143642 _143649 r x _107385)). Qed.
Lemma lem8096887 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : ((term91 _143642 _143649 r s x) = (term71 _143642 _143649 r x _107385)) = ((term68 _143642 _143649 r x) = (term24 _143642 _143649 r x _107385)).
Proof. exact (MK_COMB (@lem8096872 _143642 _143649 s r x h1) (@lem8096886 _143642 _143649 _107385 r x h1)). Qed.
Lemma lem8096890 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term100 _143642 _143649 s r x) = (term137 _143642 _143649 r x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8096887 _143642 _143649 s _107385 r x h1)). Qed.
Lemma lem8096891 {_143642 : Type'} : (@all _143642) = (@all _143642).
Proof. exact (eq_refl (@all _143642)). Qed.
Lemma lem8096892 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term101 _143642 _143649 s r x) = (term138 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8096891 _143642) (@lem8096890 _143642 _143649 s r x h1)). Qed.
Lemma lem8096897 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term121 _143642 _143649 s r x) = (term139 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8096854 _143642 _143649 s r x h1) (@lem8096892 _143642 _143649 s r x h1)). Qed.
Lemma lem8096900 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8096901 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term123 _143642 _143649 s r x) = (term140 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8096900) (@lem8096897 _143642 _143649 s r x h1)). Qed.
Lemma lem8096903 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term106 _143642 _143649 r x) = True.
Proof. exact (h1). Qed.
Lemma lem8096904 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term106 _143642 _143649 r x) = True.
Proof. exact (@lem8096903 _143642 _143649 r x h1). Qed.
Lemma lem8096905 {_143642 : Type'} : (@COND (_143642 -> Prop)) = (@COND (_143642 -> Prop)).
Proof. exact (eq_refl (@COND (_143642 -> Prop))). Qed.
Lemma lem8096906 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term107 _143642 _143649 r x) = (@COND (_143642 -> Prop) True).
Proof. exact (MK_COMB (@lem8096905 _143642) (@lem8096904 _143642 _143649 r x h1)). Qed.
Lemma lem8096907 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (r x) = (r x).
Proof. exact (eq_refl (r x)). Qed.
Lemma lem8096908 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term108 _143642 _143649 r x) = (term133 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8096906 _143642 _143649 r x h1) (@lem8096907 _143642 _143649 r x)). Qed.
Lemma lem8096909 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem8096910 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term110 _143642 _143649 r s x) = (term134 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8096908 _143642 _143649 r x h1) (@lem8096909 _143642 _143649 s x)). Qed.
Lemma lem8096912 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem8096913 {_143642 : Type'} (t2 : _143642 -> Prop) (t1 : _143642 -> Prop) : (@COND (_143642 -> Prop) True t1 t2) = t1.
Proof. exact (@lem8096912 (_143642 -> Prop) t2 t1). Qed.
Lemma lem8096914 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) : (term134 _143642 _143649 r s x) = (r x).
Proof. exact (@lem8096913 _143642 (s x) (r x)). Qed.
Lemma lem8096915 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term110 _143642 _143649 r s x) = (r x).
Proof. exact (TRANS (@lem8096910 _143642 _143649 s r x h1) (@lem8096914 _143642 _143649 s r x)). Qed.
Lemma lem8096916 {_143642 : Type'} : (@ex1 _143642) = (@ex1 _143642).
Proof. exact (eq_refl (@ex1 _143642)). Qed.
Lemma lem8096917 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term89 _143642 _143649 r s x) = (term66 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8096916 _143642) (@lem8096915 _143642 _143649 s r x h1)). Qed.
Lemma lem8096918 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8096919 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term125 _143642 _143649 r s x) = (term126 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8096918) (@lem8096917 _143642 _143649 s r x h1)). Qed.
Lemma lem8096921 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term106 _143642 _143649 r x) = True.
Proof. exact (h1). Qed.
Lemma lem8096922 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term106 _143642 _143649 r x) = True.
Proof. exact (@lem8096921 _143642 _143649 r x h1). Qed.
Lemma lem8096923 {_143642 : Type'} : (@COND _143642) = (@COND _143642).
Proof. exact (eq_refl (@COND _143642)). Qed.
Lemma lem8096924 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term25 _143642 _143649 r x) = (@COND _143642 True).
Proof. exact (MK_COMB (@lem8096923 _143642) (@lem8096922 _143642 _143649 r x h1)). Qed.
Lemma lem8096925 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term24 _143642 _143649 r x _107385) = (term24 _143642 _143649 r x _107385).
Proof. exact (eq_refl (term24 _143642 _143649 r x _107385)). Qed.
Lemma lem8096926 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term27 _143642 _143649 r x _107385) = (term135 _143642 _143649 r x _107385).
Proof. exact (MK_COMB (@lem8096924 _143642 _143649 r x h1) (@lem8096925 _143642 _143649 r x _107385)). Qed.
Lemma lem8096927 {_143642 : Type'} (_107385 : _143642) : _107385 = _107385.
Proof. exact (eq_refl _107385). Qed.
Lemma lem8096928 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term71 _143642 _143649 r x _107385) = (term136 _143642 _143649 r x _107385).
Proof. exact (MK_COMB (@lem8096926 _143642 _143649 _107385 r x h1) (@lem8096927 _143642 _107385)). Qed.
Lemma lem8096930 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem8096931 {_143642 : Type'} (t2 : _143642) (t1 : _143642) : (@COND _143642 True t1 t2) = t1.
Proof. exact (@lem8096930 _143642 t2 t1). Qed.
Lemma lem8096932 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term136 _143642 _143649 r x _107385) = (term24 _143642 _143649 r x _107385).
Proof. exact (@lem8096931 _143642 _107385 (term24 _143642 _143649 r x _107385)). Qed.
Lemma lem8096933 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term71 _143642 _143649 r x _107385) = (term24 _143642 _143649 r x _107385).
Proof. exact (TRANS (@lem8096928 _143642 _143649 _107385 r x h1) (@lem8096932 _143642 _143649 r x _107385)). Qed.
Lemma lem8096934 {_143642 : Type'} (_107385 : _143642) : (@eq _143642 _107385) = (@eq _143642 _107385).
Proof. exact (eq_refl (@eq _143642 _107385)). Qed.
Lemma lem8096935 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (_107385 = (term71 _143642 _143649 r x _107385)) = (_107385 = (term24 _143642 _143649 r x _107385)).
Proof. exact (MK_COMB (@lem8096934 _143642 _107385) (@lem8096933 _143642 _143649 _107385 r x h1)). Qed.
Lemma lem8096938 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term94 _143642 _143649 r x) = (term141 _143642 _143649 r x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8096935 _143642 _143649 _107385 r x h1)). Qed.
Lemma lem8096939 {_143642 : Type'} : (@all _143642) = (@all _143642).
Proof. exact (eq_refl (@all _143642)). Qed.
Lemma lem8096940 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term95 _143642 _143649 r x) = (term142 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8096939 _143642) (@lem8096938 _143642 _143649 r x h1)). Qed.
Lemma lem8096945 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term129 _143642 _143649 s r x) = (term143 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8096919 _143642 _143649 s r x h1) (@lem8096940 _143642 _143649 r x h1)). Qed.
Lemma lem8096948 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term105 _143642 _143649 s r x) = (term144 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8096901 _143642 _143649 s r x h1) (@lem8096945 _143642 _143649 s r x h1)). Qed.
Lemma lem8096951 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) : term145 _143642 _143649 s r x.
Proof. exact (fun h0 : (term106 _143642 _143649 r x) = True => @lem8096948 _143642 _143649 s r x h0). Qed.
Lemma lem8096952 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) : term146 _143642 _143649 s r x.
Proof. exact (conj (@lem8096834 _143642 _143649 r s x) (@lem8096951 _143642 _143649 s r x)). Qed.
Lemma lem8096954 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term86 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem8096955 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : term147 _143642 _143649 r s x.
Proof. exact (@lem8096954 (term105 _143642 _143649 s r x) (term144 _143642 _143649 r x) (term106 _143642 _143649 r x) (term122 _143642 _143649 s x)). Qed.
Lemma lem8096970 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term105 _143642 _143649 s r x) = (term148 _143642 _143649 r s x).
Proof. exact (@lem8096955 _143642 _143649 r s x (@lem8096952 _143642 _143649 s r x)). Qed.
Lemma lem8096978 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term66 _143642 _143649 r x) = False.
Proof. exact (h1). Qed.
Lemma lem8096979 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8096980 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term113 _143642 _143649 r x) = (~ False).
Proof. exact (MK_COMB (@lem8096979) (@lem8096978 _143642 _143649 r x h1)). Qed.
Lemma lem8096982 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem8096983 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term113 _143642 _143649 r x) = True.
Proof. exact (TRANS (@lem8096980 _143642 _143649 r x h1) (@lem8096982)). Qed.
Lemma lem8096984 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8096985 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term115 _143642 _143649 r x) = (or True).
Proof. exact (MK_COMB (@lem8096984) (@lem8096983 _143642 _143649 r x h1)). Qed.
Lemma lem8096987 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term66 _143642 _143649 r x) = False.
Proof. exact (h1). Qed.
Lemma lem8096988 {_143642 : Type'} : (@COND _143642) = (@COND _143642).
Proof. exact (eq_refl (@COND _143642)). Qed.
Lemma lem8096989 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term67 _143642 _143649 r x) = (@COND _143642 False).
Proof. exact (MK_COMB (@lem8096988 _143642) (@lem8096987 _143642 _143649 r x h1)). Qed.
Lemma lem8096990 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term68 _143642 _143649 r x) = (term68 _143642 _143649 r x).
Proof. exact (eq_refl (term68 _143642 _143649 r x)). Qed.
Lemma lem8096991 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term22 _143642 _143649 r x) = (term69 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8096989 _143642 _143649 r x h1) (@lem8096990 _143642 _143649 r x)). Qed.
Lemma lem8096992 {_143642 : Type'} (_107385 : _143642) : _107385 = _107385.
Proof. exact (eq_refl _107385). Qed.
Lemma lem8096993 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term24 _143642 _143649 r x _107385) = (term70 _143642 _143649 r x _107385).
Proof. exact (MK_COMB (@lem8096991 _143642 _143649 r x h1) (@lem8096992 _143642 _107385)). Qed.
Lemma lem8096995 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem8096996 {_143642 : Type'} (t1 : _143642) (t2 : _143642) : (@COND _143642 False t1 t2) = t2.
Proof. exact (@lem8096995 _143642 t1 t2). Qed.
Lemma lem8096997 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term70 _143642 _143649 r x _107385) = _107385.
Proof. exact (@lem8096996 _143642 (term68 _143642 _143649 r x) _107385). Qed.
Lemma lem8096998 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term24 _143642 _143649 r x _107385) = _107385.
Proof. exact (TRANS (@lem8096993 _143642 _143649 _107385 r x h1) (@lem8096997 _143642 _143649 r x _107385)). Qed.
Lemma lem8096999 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term116 _143642 _143649 r x) = (term116 _143642 _143649 r x).
Proof. exact (eq_refl (term116 _143642 _143649 r x)). Qed.
Lemma lem8097000 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : ((term68 _143642 _143649 r x) = (term24 _143642 _143649 r x _107385)) = ((term68 _143642 _143649 r x) = _107385).
Proof. exact (MK_COMB (@lem8096999 _143642 _143649 r x) (@lem8096998 _143642 _143649 _107385 r x h1)). Qed.
Lemma lem8097003 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term137 _143642 _143649 r x) = (term119 _143642 _143649 r x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8097000 _143642 _143649 _107385 r x h1)). Qed.
Lemma lem8097004 {_143642 : Type'} : (@all _143642) = (@all _143642).
Proof. exact (eq_refl (@all _143642)). Qed.
Lemma lem8097005 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term138 _143642 _143649 r x) = (term120 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8097004 _143642) (@lem8097003 _143642 _143649 r x h1)). Qed.
Lemma lem8097010 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term139 _143642 _143649 r x) = (term149 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8096985 _143642 _143649 r x h1) (@lem8097005 _143642 _143649 r x h1)). Qed.
Lemma lem8097012 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem8097013 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term149 _143642 _143649 r x) = True.
Proof. exact (@lem8097012 (term120 _143642 _143649 r x)). Qed.
Lemma lem8097014 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term139 _143642 _143649 r x) = True.
Proof. exact (TRANS (@lem8097010 _143642 _143649 r x h1) (@lem8097013 _143642 _143649 r x)). Qed.
Lemma lem8097015 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8097016 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term140 _143642 _143649 r x) = (and True).
Proof. exact (MK_COMB (@lem8097015) (@lem8097014 _143642 _143649 r x h1)). Qed.
Lemma lem8097018 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term66 _143642 _143649 r x) = False.
Proof. exact (h1). Qed.
Lemma lem8097019 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8097020 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term126 _143642 _143649 r x) = (or False).
Proof. exact (MK_COMB (@lem8097019) (@lem8097018 _143642 _143649 r x h1)). Qed.
Lemma lem8097022 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term66 _143642 _143649 r x) = False.
Proof. exact (h1). Qed.
Lemma lem8097023 {_143642 : Type'} : (@COND _143642) = (@COND _143642).
Proof. exact (eq_refl (@COND _143642)). Qed.
Lemma lem8097024 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term67 _143642 _143649 r x) = (@COND _143642 False).
Proof. exact (MK_COMB (@lem8097023 _143642) (@lem8097022 _143642 _143649 r x h1)). Qed.
Lemma lem8097025 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term68 _143642 _143649 r x) = (term68 _143642 _143649 r x).
Proof. exact (eq_refl (term68 _143642 _143649 r x)). Qed.
Lemma lem8097026 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term22 _143642 _143649 r x) = (term69 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8097024 _143642 _143649 r x h1) (@lem8097025 _143642 _143649 r x)). Qed.
Lemma lem8097027 {_143642 : Type'} (_107385 : _143642) : _107385 = _107385.
Proof. exact (eq_refl _107385). Qed.
Lemma lem8097028 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term24 _143642 _143649 r x _107385) = (term70 _143642 _143649 r x _107385).
Proof. exact (MK_COMB (@lem8097026 _143642 _143649 r x h1) (@lem8097027 _143642 _107385)). Qed.
Lemma lem8097030 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem8097031 {_143642 : Type'} (t1 : _143642) (t2 : _143642) : (@COND _143642 False t1 t2) = t2.
Proof. exact (@lem8097030 _143642 t1 t2). Qed.
Lemma lem8097032 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term70 _143642 _143649 r x _107385) = _107385.
Proof. exact (@lem8097031 _143642 (term68 _143642 _143649 r x) _107385). Qed.
Lemma lem8097033 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term24 _143642 _143649 r x _107385) = _107385.
Proof. exact (TRANS (@lem8097028 _143642 _143649 _107385 r x h1) (@lem8097032 _143642 _143649 r x _107385)). Qed.
Lemma lem8097034 {_143642 : Type'} (_107385 : _143642) : (@eq _143642 _107385) = (@eq _143642 _107385).
Proof. exact (eq_refl (@eq _143642 _107385)). Qed.
Lemma lem8097035 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (_107385 = (term24 _143642 _143649 r x _107385)) = (_107385 = _107385).
Proof. exact (MK_COMB (@lem8097034 _143642 _107385) (@lem8097033 _143642 _143649 _107385 r x h1)). Qed.
Lemma lem8097037 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem8097038 {_143642 : Type'} (x : _143642) : (x = x) = True.
Proof. exact (@lem8097037 _143642 x). Qed.
Lemma lem8097039 {_143642 : Type'} (_107385 : _143642) : (_107385 = _107385) = True.
Proof. exact (@lem8097038 _143642 _107385). Qed.
Lemma lem8097040 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (_107385 = (term24 _143642 _143649 r x _107385)) = True.
Proof. exact (TRANS (@lem8097035 _143642 _143649 _107385 r x h1) (@lem8097039 _143642 _107385)). Qed.
Lemma lem8097041 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term141 _143642 _143649 r x) = (term127 _143642).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8097040 _143642 _143649 _107385 r x h1)). Qed.
Lemma lem8097042 {_143642 : Type'} : (@all _143642) = (@all _143642).
Proof. exact (eq_refl (@all _143642)). Qed.
Lemma lem8097043 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term142 _143642 _143649 r x) = (term128 _143642).
Proof. exact (MK_COMB (@lem8097042 _143642) (@lem8097041 _143642 _143649 r x h1)). Qed.
Lemma lem8097045 {A : Type'} (t : Prop) : (term47 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8097046 {_143642 : Type'} (t : Prop) : (term47 _143642 t) = t.
Proof. exact (@lem8097045 _143642 t). Qed.
Lemma lem8097047 {_143642 : Type'} : (term128 _143642) = True.
Proof. exact (@lem8097046 _143642 True). Qed.
Lemma lem8097048 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term142 _143642 _143649 r x) = True.
Proof. exact (TRANS (@lem8097043 _143642 _143649 r x h1) (@lem8097047 _143642)). Qed.
Lemma lem8097049 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term143 _143642 _143649 r x) = (False \/ True).
Proof. exact (MK_COMB (@lem8097020 _143642 _143649 r x h1) (@lem8097048 _143642 _143649 r x h1)). Qed.
Lemma lem8097051 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem8097052 : (False \/ True) = True.
Proof. exact (@lem8097051 True). Qed.
Lemma lem8097053 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term143 _143642 _143649 r x) = True.
Proof. exact (TRANS (@lem8097049 _143642 _143649 r x h1) (@lem8097052)). Qed.
Lemma lem8097054 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term144 _143642 _143649 r x) = (True /\ True).
Proof. exact (MK_COMB (@lem8097016 _143642 _143649 r x h1) (@lem8097053 _143642 _143649 r x h1)). Qed.
Lemma lem8097056 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8097057 : (True /\ True) = True.
Proof. exact (@lem8097056 True). Qed.
Lemma lem8097058 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term144 _143642 _143649 r x) = True.
Proof. exact (TRANS (@lem8097054 _143642 _143649 r x h1) (@lem8097057)). Qed.
Lemma lem8097059 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term150 _143642 _143649 r x) = (term150 _143642 _143649 r x).
Proof. exact (eq_refl (term150 _143642 _143649 r x)). Qed.
Lemma lem8097060 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term151 _143642 _143649 r x) = (term152 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8097059 _143642 _143649 r x) (@lem8097058 _143642 _143649 r x h1)). Qed.
Lemma lem8097062 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem8097063 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term152 _143642 _143649 r x) = True.
Proof. exact (@lem8097062 (term153 _143642 _143649 r x)). Qed.
Lemma lem8097064 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term151 _143642 _143649 r x) = True.
Proof. exact (TRANS (@lem8097060 _143642 _143649 r x h1) (@lem8097063 _143642 _143649 r x)). Qed.
Lemma lem8097065 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8097066 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term154 _143642 _143649 r x) = (and True).
Proof. exact (MK_COMB (@lem8097065) (@lem8097064 _143642 _143649 r x h1)). Qed.
Lemma lem8097081 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term155 _143642 _143649 r s x) = (term155 _143642 _143649 r s x).
Proof. exact (eq_refl (term155 _143642 _143649 r s x)). Qed.
Lemma lem8097082 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term148 _143642 _143649 r s x) = (term156 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8097066 _143642 _143649 r x h1) (@lem8097081 _143642 _143649 r s x)). Qed.
Lemma lem8097084 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8097085 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term156 _143642 _143649 r s x) = (term155 _143642 _143649 r s x).
Proof. exact (@lem8097084 (term155 _143642 _143649 r s x)). Qed.
Lemma lem8097088 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term148 _143642 _143649 r s x) = (term155 _143642 _143649 r s x).
Proof. exact (TRANS (@lem8097082 _143642 _143649 s r x h1) (@lem8097085 _143642 _143649 r s x)). Qed.
Lemma lem8097089 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : term157 _143642 _143649 r s x.
Proof. exact (fun h0 : (term66 _143642 _143649 r x) = False => @lem8097088 _143642 _143649 s r x h0). Qed.
Lemma lem8097095 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term66 _143642 _143649 r x) = True.
Proof. exact (h1). Qed.
Lemma lem8097096 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8097097 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term113 _143642 _143649 r x) = (~ True).
Proof. exact (MK_COMB (@lem8097096) (@lem8097095 _143642 _143649 r x h1)). Qed.
Lemma lem8097099 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem8097100 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term113 _143642 _143649 r x) = False.
Proof. exact (TRANS (@lem8097097 _143642 _143649 r x h1) (@lem8097099)). Qed.
Lemma lem8097101 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8097102 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term115 _143642 _143649 r x) = (or False).
Proof. exact (MK_COMB (@lem8097101) (@lem8097100 _143642 _143649 r x h1)). Qed.
Lemma lem8097104 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term66 _143642 _143649 r x) = True.
Proof. exact (h1). Qed.
Lemma lem8097105 {_143642 : Type'} : (@COND _143642) = (@COND _143642).
Proof. exact (eq_refl (@COND _143642)). Qed.
Lemma lem8097106 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term67 _143642 _143649 r x) = (@COND _143642 True).
Proof. exact (MK_COMB (@lem8097105 _143642) (@lem8097104 _143642 _143649 r x h1)). Qed.
Lemma lem8097107 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term68 _143642 _143649 r x) = (term68 _143642 _143649 r x).
Proof. exact (eq_refl (term68 _143642 _143649 r x)). Qed.
Lemma lem8097108 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term22 _143642 _143649 r x) = (term77 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8097106 _143642 _143649 r x h1) (@lem8097107 _143642 _143649 r x)). Qed.
Lemma lem8097109 {_143642 : Type'} (_107385 : _143642) : _107385 = _107385.
Proof. exact (eq_refl _107385). Qed.
Lemma lem8097110 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term24 _143642 _143649 r x _107385) = (term78 _143642 _143649 r x _107385).
Proof. exact (MK_COMB (@lem8097108 _143642 _143649 r x h1) (@lem8097109 _143642 _107385)). Qed.
Lemma lem8097112 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem8097113 {_143642 : Type'} (t2 : _143642) (t1 : _143642) : (@COND _143642 True t1 t2) = t1.
Proof. exact (@lem8097112 _143642 t2 t1). Qed.
Lemma lem8097114 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) : (term78 _143642 _143649 r x _107385) = (term68 _143642 _143649 r x).
Proof. exact (@lem8097113 _143642 _107385 (term68 _143642 _143649 r x)). Qed.
Lemma lem8097115 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term24 _143642 _143649 r x _107385) = (term68 _143642 _143649 r x).
Proof. exact (TRANS (@lem8097110 _143642 _143649 _107385 r x h1) (@lem8097114 _143642 _143649 _107385 r x)). Qed.
Lemma lem8097116 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term116 _143642 _143649 r x) = (term116 _143642 _143649 r x).
Proof. exact (eq_refl (term116 _143642 _143649 r x)). Qed.
Lemma lem8097117 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : ((term68 _143642 _143649 r x) = (term24 _143642 _143649 r x _107385)) = ((term68 _143642 _143649 r x) = (term68 _143642 _143649 r x)).
Proof. exact (MK_COMB (@lem8097116 _143642 _143649 r x) (@lem8097115 _143642 _143649 _107385 r x h1)). Qed.
Lemma lem8097119 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem8097120 {_143642 : Type'} (x : _143642) : (x = x) = True.
Proof. exact (@lem8097119 _143642 x). Qed.
Lemma lem8097121 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : ((term68 _143642 _143649 r x) = (term68 _143642 _143649 r x)) = True.
Proof. exact (@lem8097120 _143642 (term68 _143642 _143649 r x)). Qed.
Lemma lem8097122 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : ((term68 _143642 _143649 r x) = (term24 _143642 _143649 r x _107385)) = True.
Proof. exact (TRANS (@lem8097117 _143642 _143649 _107385 r x h1) (@lem8097121 _143642 _143649 r x)). Qed.
Lemma lem8097123 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term137 _143642 _143649 r x) = (term127 _143642).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8097122 _143642 _143649 _107385 r x h1)). Qed.
Lemma lem8097124 {_143642 : Type'} : (@all _143642) = (@all _143642).
Proof. exact (eq_refl (@all _143642)). Qed.
Lemma lem8097125 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term138 _143642 _143649 r x) = (term128 _143642).
Proof. exact (MK_COMB (@lem8097124 _143642) (@lem8097123 _143642 _143649 r x h1)). Qed.
Lemma lem8097127 {A : Type'} (t : Prop) : (term47 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8097128 {_143642 : Type'} (t : Prop) : (term47 _143642 t) = t.
Proof. exact (@lem8097127 _143642 t). Qed.
Lemma lem8097129 {_143642 : Type'} : (term128 _143642) = True.
Proof. exact (@lem8097128 _143642 True). Qed.
Lemma lem8097130 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term138 _143642 _143649 r x) = True.
Proof. exact (TRANS (@lem8097125 _143642 _143649 r x h1) (@lem8097129 _143642)). Qed.
Lemma lem8097131 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term139 _143642 _143649 r x) = (False \/ True).
Proof. exact (MK_COMB (@lem8097102 _143642 _143649 r x h1) (@lem8097130 _143642 _143649 r x h1)). Qed.
Lemma lem8097133 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem8097134 : (False \/ True) = True.
Proof. exact (@lem8097133 True). Qed.
Lemma lem8097135 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term139 _143642 _143649 r x) = True.
Proof. exact (TRANS (@lem8097131 _143642 _143649 r x h1) (@lem8097134)). Qed.
Lemma lem8097136 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8097137 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term140 _143642 _143649 r x) = (and True).
Proof. exact (MK_COMB (@lem8097136) (@lem8097135 _143642 _143649 r x h1)). Qed.
Lemma lem8097139 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term66 _143642 _143649 r x) = True.
Proof. exact (h1). Qed.
Lemma lem8097140 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8097141 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term126 _143642 _143649 r x) = (or True).
Proof. exact (MK_COMB (@lem8097140) (@lem8097139 _143642 _143649 r x h1)). Qed.
Lemma lem8097143 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term66 _143642 _143649 r x) = True.
Proof. exact (h1). Qed.
Lemma lem8097144 {_143642 : Type'} : (@COND _143642) = (@COND _143642).
Proof. exact (eq_refl (@COND _143642)). Qed.
Lemma lem8097145 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term67 _143642 _143649 r x) = (@COND _143642 True).
Proof. exact (MK_COMB (@lem8097144 _143642) (@lem8097143 _143642 _143649 r x h1)). Qed.
Lemma lem8097146 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term68 _143642 _143649 r x) = (term68 _143642 _143649 r x).
Proof. exact (eq_refl (term68 _143642 _143649 r x)). Qed.
Lemma lem8097147 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term22 _143642 _143649 r x) = (term77 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8097145 _143642 _143649 r x h1) (@lem8097146 _143642 _143649 r x)). Qed.
Lemma lem8097148 {_143642 : Type'} (_107385 : _143642) : _107385 = _107385.
Proof. exact (eq_refl _107385). Qed.
Lemma lem8097149 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term24 _143642 _143649 r x _107385) = (term78 _143642 _143649 r x _107385).
Proof. exact (MK_COMB (@lem8097147 _143642 _143649 r x h1) (@lem8097148 _143642 _107385)). Qed.
Lemma lem8097151 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem8097152 {_143642 : Type'} (t2 : _143642) (t1 : _143642) : (@COND _143642 True t1 t2) = t1.
Proof. exact (@lem8097151 _143642 t2 t1). Qed.
Lemma lem8097153 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) : (term78 _143642 _143649 r x _107385) = (term68 _143642 _143649 r x).
Proof. exact (@lem8097152 _143642 _107385 (term68 _143642 _143649 r x)). Qed.
Lemma lem8097154 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term24 _143642 _143649 r x _107385) = (term68 _143642 _143649 r x).
Proof. exact (TRANS (@lem8097149 _143642 _143649 _107385 r x h1) (@lem8097153 _143642 _143649 _107385 r x)). Qed.
Lemma lem8097155 {_143642 : Type'} (_107385 : _143642) : (@eq _143642 _107385) = (@eq _143642 _107385).
Proof. exact (eq_refl (@eq _143642 _107385)). Qed.
Lemma lem8097156 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (_107385 = (term24 _143642 _143649 r x _107385)) = (_107385 = (term68 _143642 _143649 r x)).
Proof. exact (MK_COMB (@lem8097155 _143642 _107385) (@lem8097154 _143642 _143649 _107385 r x h1)). Qed.
Lemma lem8097159 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term141 _143642 _143649 r x) = (term158 _143642 _143649 r x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8097156 _143642 _143649 _107385 r x h1)). Qed.
Lemma lem8097160 {_143642 : Type'} : (@all _143642) = (@all _143642).
Proof. exact (eq_refl (@all _143642)). Qed.
Lemma lem8097161 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term142 _143642 _143649 r x) = (term159 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8097160 _143642) (@lem8097159 _143642 _143649 r x h1)). Qed.
Lemma lem8097166 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term143 _143642 _143649 r x) = (term160 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8097141 _143642 _143649 r x h1) (@lem8097161 _143642 _143649 r x h1)). Qed.
Lemma lem8097168 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem8097169 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term160 _143642 _143649 r x) = True.
Proof. exact (@lem8097168 (term159 _143642 _143649 r x)). Qed.
Lemma lem8097170 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term143 _143642 _143649 r x) = True.
Proof. exact (TRANS (@lem8097166 _143642 _143649 r x h1) (@lem8097169 _143642 _143649 r x)). Qed.
Lemma lem8097171 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term144 _143642 _143649 r x) = (True /\ True).
Proof. exact (MK_COMB (@lem8097137 _143642 _143649 r x h1) (@lem8097170 _143642 _143649 r x h1)). Qed.
Lemma lem8097173 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8097174 : (True /\ True) = True.
Proof. exact (@lem8097173 True). Qed.
Lemma lem8097175 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term144 _143642 _143649 r x) = True.
Proof. exact (TRANS (@lem8097171 _143642 _143649 r x h1) (@lem8097174)). Qed.
Lemma lem8097176 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term150 _143642 _143649 r x) = (term150 _143642 _143649 r x).
Proof. exact (eq_refl (term150 _143642 _143649 r x)). Qed.
Lemma lem8097177 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term151 _143642 _143649 r x) = (term152 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8097176 _143642 _143649 r x) (@lem8097175 _143642 _143649 r x h1)). Qed.
Lemma lem8097179 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem8097180 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term152 _143642 _143649 r x) = True.
Proof. exact (@lem8097179 (term153 _143642 _143649 r x)). Qed.
Lemma lem8097181 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term151 _143642 _143649 r x) = True.
Proof. exact (TRANS (@lem8097177 _143642 _143649 r x h1) (@lem8097180 _143642 _143649 r x)). Qed.
Lemma lem8097182 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8097183 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term154 _143642 _143649 r x) = (and True).
Proof. exact (MK_COMB (@lem8097182) (@lem8097181 _143642 _143649 r x h1)). Qed.
Lemma lem8097198 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term155 _143642 _143649 r s x) = (term155 _143642 _143649 r s x).
Proof. exact (eq_refl (term155 _143642 _143649 r s x)). Qed.
Lemma lem8097199 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term148 _143642 _143649 r s x) = (term156 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8097183 _143642 _143649 r x h1) (@lem8097198 _143642 _143649 r s x)). Qed.
Lemma lem8097201 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8097202 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term156 _143642 _143649 r s x) = (term155 _143642 _143649 r s x).
Proof. exact (@lem8097201 (term155 _143642 _143649 r s x)). Qed.
Lemma lem8097205 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term148 _143642 _143649 r s x) = (term155 _143642 _143649 r s x).
Proof. exact (TRANS (@lem8097199 _143642 _143649 s r x h1) (@lem8097202 _143642 _143649 r s x)). Qed.
Lemma lem8097206 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : term161 _143642 _143649 r s x.
Proof. exact (fun h0 : (term66 _143642 _143649 r x) = True => @lem8097205 _143642 _143649 s r x h0). Qed.
Lemma lem8097207 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : term162 _143642 _143649 r s x.
Proof. exact (conj (@lem8097089 _143642 _143649 r s x) (@lem8097206 _143642 _143649 r s x)). Qed.
Lemma lem8097209 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term86 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem8097210 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : term163 _143642 _143649 r s x.
Proof. exact (@lem8097209 (term148 _143642 _143649 r s x) (term155 _143642 _143649 r s x) (term66 _143642 _143649 r x) (term155 _143642 _143649 r s x)). Qed.
Lemma lem8097225 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term148 _143642 _143649 r s x) = (term164 _143642 _143649 r s x).
Proof. exact (@lem8097210 _143642 _143649 r s x (@lem8097207 _143642 _143649 r s x)). Qed.
Lemma lem8097226 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : ((term68 _143642 _143649 s x) = _107385) = ((term68 _143642 _143649 s x) = _107385).
Proof. exact (eq_refl ((term68 _143642 _143649 s x) = _107385)). Qed.
Lemma lem8097227 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term119 _143642 _143649 s x) = (term119 _143642 _143649 s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8097226 _143642 _143649 s x _107385)). Qed.
Lemma lem8097228 {_143642 : Type'} : (@all _143642) = (@all _143642).
Proof. exact (eq_refl (@all _143642)). Qed.
Lemma lem8097229 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term120 _143642 _143649 s x) = (term120 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8097228 _143642) (@lem8097227 _143642 _143649 s x)). Qed.
Lemma lem8097234 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term115 _143642 _143649 s x) = (term115 _143642 _143649 s x).
Proof. exact (eq_refl (term115 _143642 _143649 s x)). Qed.
Lemma lem8097235 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term122 _143642 _143649 s x) = (term122 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8097234 _143642 _143649 s x) (@lem8097229 _143642 _143649 s x)). Qed.
Lemma lem8097236 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (y : _143642) : (r x y) = (r x y).
Proof. exact (eq_refl (r x y)). Qed.
Lemma lem8097237 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term165 _143642 _143649 r x) = (term165 _143642 _143649 r x).
Proof. exact (fun_ext (fun y : _143642 => @lem8097236 _143642 _143649 r x y)). Qed.
Lemma lem8097238 {_143642 : Type'} : (@ex _143642) = (@ex _143642).
Proof. exact (eq_refl (@ex _143642)). Qed.
Lemma lem8097239 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term106 _143642 _143649 r x) = (term106 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8097238 _143642) (@lem8097237 _143642 _143649 r x)). Qed.
Lemma lem8097240 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8097241 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term166 _143642 _143649 r x) = (term166 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8097240) (@lem8097239 _143642 _143649 r x)). Qed.
Lemma lem8097242 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term155 _143642 _143649 r s x) = (term155 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8097241 _143642 _143649 r x) (@lem8097235 _143642 _143649 s x)). Qed.
Lemma lem8097245 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term126 _143642 _143649 r x) = (term126 _143642 _143649 r x).
Proof. exact (eq_refl (term126 _143642 _143649 r x)). Qed.
Lemma lem8097246 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term167 _143642 _143649 r s x) = (term167 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8097245 _143642 _143649 r x) (@lem8097242 _143642 _143649 r s x)). Qed.
Lemma lem8097247 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : ((term68 _143642 _143649 s x) = _107385) = ((term68 _143642 _143649 s x) = _107385).
Proof. exact (eq_refl ((term68 _143642 _143649 s x) = _107385)). Qed.
Lemma lem8097248 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term119 _143642 _143649 s x) = (term119 _143642 _143649 s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8097247 _143642 _143649 s x _107385)). Qed.
Lemma lem8097249 {_143642 : Type'} : (@all _143642) = (@all _143642).
Proof. exact (eq_refl (@all _143642)). Qed.
Lemma lem8097250 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term120 _143642 _143649 s x) = (term120 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8097249 _143642) (@lem8097248 _143642 _143649 s x)). Qed.
Lemma lem8097255 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term115 _143642 _143649 s x) = (term115 _143642 _143649 s x).
Proof. exact (eq_refl (term115 _143642 _143649 s x)). Qed.
Lemma lem8097256 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term122 _143642 _143649 s x) = (term122 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8097255 _143642 _143649 s x) (@lem8097250 _143642 _143649 s x)). Qed.
Lemma lem8097257 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (y : _143642) : (r x y) = (r x y).
Proof. exact (eq_refl (r x y)). Qed.
Lemma lem8097258 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term165 _143642 _143649 r x) = (term165 _143642 _143649 r x).
Proof. exact (fun_ext (fun y : _143642 => @lem8097257 _143642 _143649 r x y)). Qed.
Lemma lem8097259 {_143642 : Type'} : (@ex _143642) = (@ex _143642).
Proof. exact (eq_refl (@ex _143642)). Qed.
Lemma lem8097260 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term106 _143642 _143649 r x) = (term106 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8097259 _143642) (@lem8097258 _143642 _143649 r x)). Qed.
Lemma lem8097261 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8097262 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term166 _143642 _143649 r x) = (term166 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8097261) (@lem8097260 _143642 _143649 r x)). Qed.
Lemma lem8097263 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term155 _143642 _143649 r s x) = (term155 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8097262 _143642 _143649 r x) (@lem8097256 _143642 _143649 s x)). Qed.
Lemma lem8097268 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term115 _143642 _143649 r x) = (term115 _143642 _143649 r x).
Proof. exact (eq_refl (term115 _143642 _143649 r x)). Qed.
Lemma lem8097269 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term168 _143642 _143649 r s x) = (term168 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8097268 _143642 _143649 r x) (@lem8097263 _143642 _143649 r s x)). Qed.
Lemma lem8097270 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8097271 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term169 _143642 _143649 r s x) = (term169 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8097270) (@lem8097269 _143642 _143649 r s x)). Qed.
Lemma lem8097272 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term164 _143642 _143649 r s x) = (term164 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8097271 _143642 _143649 r s x) (@lem8097246 _143642 _143649 r s x)). Qed.
Lemma lem8097273 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term170 _143642 _143649 r s x) = (term170 _143642 _143649 r s x).
Proof. exact (eq_refl (term170 _143642 _143649 r s x)). Qed.
Lemma lem8097274 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : ((term148 _143642 _143649 r s x) = (term164 _143642 _143649 r s x)) = ((term148 _143642 _143649 r s x) = (term164 _143642 _143649 r s x)).
Proof. exact (MK_COMB (@lem8097273 _143642 _143649 r s x) (@lem8097272 _143642 _143649 r s x)). Qed.
Lemma lem8097275 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term148 _143642 _143649 r s x) = (term164 _143642 _143649 r s x).
Proof. exact (EQ_MP (@lem8097274 _143642 _143649 r s x) (@lem8097225 _143642 _143649 r s x)). Qed.
Lemma lem8097276 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) : (term171 _143642 _143649 s r x) = (term171 _143642 _143649 s r x).
Proof. exact (eq_refl (term171 _143642 _143649 s r x)). Qed.
Lemma lem8097277 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : ((term105 _143642 _143649 s r x) = (term148 _143642 _143649 r s x)) = ((term105 _143642 _143649 s r x) = (term164 _143642 _143649 r s x)).
Proof. exact (MK_COMB (@lem8097276 _143642 _143649 s r x) (@lem8097275 _143642 _143649 r s x)). Qed.
Lemma lem8097278 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term105 _143642 _143649 s r x) = (term164 _143642 _143649 r s x).
Proof. exact (EQ_MP (@lem8097277 _143642 _143649 r s x) (@lem8096970 _143642 _143649 r s x)). Qed.
Lemma lem8097279 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) : (term172 _143642 _143649 s r x) = (term172 _143642 _143649 s r x).
Proof. exact (eq_refl (term172 _143642 _143649 s r x)). Qed.
Lemma lem8097280 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : ((term73 _143642 _143649 s r x) = (term105 _143642 _143649 s r x)) = ((term73 _143642 _143649 s r x) = (term164 _143642 _143649 r s x)).
Proof. exact (MK_COMB (@lem8097279 _143642 _143649 s r x) (@lem8097278 _143642 _143649 r s x)). Qed.
Lemma lem8097281 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term73 _143642 _143649 s r x) = (term164 _143642 _143649 r s x).
Proof. exact (EQ_MP (@lem8097280 _143642 _143649 r s x) (@lem8096705 _143642 _143649 s r x)). Qed.
Lemma lem8097282 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term74 _143642 _143649 s x) = (term173 _143642 _143649 s x).
Proof. exact (fun_ext (fun r : type1470 _143642 _143649 => @lem8097281 _143642 _143649 r s x)). Qed.
Lemma lem8097283 {_143642 _143649 : Type'} : (@all (_143649 -> _143642 -> Prop)) = (@all (_143649 -> _143642 -> Prop)).
Proof. exact (eq_refl (@all (_143649 -> _143642 -> Prop))). Qed.
Lemma lem8097284 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term75 _143642 _143649 s x) = (term174 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8097283 _143642 _143649) (@lem8097282 _143642 _143649 s x)). Qed.
Lemma lem8097287 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term126 _143642 _143649 s x) = (term126 _143642 _143649 s x).
Proof. exact (eq_refl (term126 _143642 _143649 s x)). Qed.
Lemma lem8097288 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term175 _143642 _143649 s x) = (term176 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8097287 _143642 _143649 s x) (@lem8097284 _143642 _143649 s x)). Qed.
Lemma lem8097296 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term89 _143642 _143649 r s x) = False) : (term89 _143642 _143649 r s x) = False.
Proof. exact (h1). Qed.
Lemma lem8097297 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term89 _143642 _143649 r s x) = False) : (term89 _143642 _143649 r s x) = False.
Proof. exact (@lem8097296 _143642 _143649 r s x h1). Qed.
Lemma lem8097298 {_143642 : Type'} : (@COND _143642) = (@COND _143642).
Proof. exact (eq_refl (@COND _143642)). Qed.
Lemma lem8097299 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term89 _143642 _143649 r s x) = False) : (term90 _143642 _143649 r s x) = (@COND _143642 False).
Proof. exact (MK_COMB (@lem8097298 _143642) (@lem8097297 _143642 _143649 r s x h1)). Qed.
Lemma lem8097304 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term91 _143642 _143649 r s x) = (term91 _143642 _143649 r s x).
Proof. exact (eq_refl (term91 _143642 _143649 r s x)). Qed.
Lemma lem8097305 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term89 _143642 _143649 r s x) = False) : (term18 _143642 _143649 r s x) = (term92 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8097299 _143642 _143649 r s x h1) (@lem8097304 _143642 _143649 r s x)). Qed.
Lemma lem8097306 {_143642 : Type'} (_107385 : _143642) : _107385 = _107385.
Proof. exact (eq_refl _107385). Qed.
Lemma lem8097307 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term89 _143642 _143649 r s x) = False) : (term19 _143642 _143649 r s x _107385) = (term93 _143642 _143649 r s x _107385).
Proof. exact (MK_COMB (@lem8097305 _143642 _143649 r s x h1) (@lem8097306 _143642 _107385)). Qed.
Lemma lem8097309 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem8097310 {_143642 : Type'} (t1 : _143642) (t2 : _143642) : (@COND _143642 False t1 t2) = t2.
Proof. exact (@lem8097309 _143642 t1 t2). Qed.
Lemma lem8097311 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term93 _143642 _143649 r s x _107385) = _107385.
Proof. exact (@lem8097310 _143642 (term91 _143642 _143649 r s x) _107385). Qed.
Lemma lem8097312 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term89 _143642 _143649 r s x) = False) : (term19 _143642 _143649 r s x _107385) = _107385.
Proof. exact (TRANS (@lem8097307 _143642 _143649 _107385 r s x h1) (@lem8097311 _143642 _143649 r s x _107385)). Qed.
Lemma lem8097313 {_143642 : Type'} : (@eq _143642) = (@eq _143642).
Proof. exact (eq_refl (@eq _143642)). Qed.
Lemma lem8097314 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term89 _143642 _143649 r s x) = False) : (term21 _143642 _143649 r s x _107385) = (@eq _143642 _107385).
Proof. exact (MK_COMB (@lem8097313 _143642) (@lem8097312 _143642 _143649 _107385 r s x h1)). Qed.
Lemma lem8097319 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term79 _143642 _143649 r _107385 s x) = (term79 _143642 _143649 r _107385 s x).
Proof. exact (eq_refl (term79 _143642 _143649 r _107385 s x)). Qed.
Lemma lem8097320 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term89 _143642 _143649 r s x) = False) : ((term19 _143642 _143649 r s x _107385) = (term79 _143642 _143649 r _107385 s x)) = (_107385 = (term79 _143642 _143649 r _107385 s x)).
Proof. exact (MK_COMB (@lem8097314 _143642 _143649 _107385 r s x h1) (@lem8097319 _143642 _143649 r _107385 s x)). Qed.
Lemma lem8097323 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term89 _143642 _143649 r s x) = False) : (term80 _143642 _143649 r s x) = (term177 _143642 _143649 r s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8097320 _143642 _143649 _107385 r s x h1)). Qed.
Lemma lem8097324 {_143642 : Type'} : (@all _143642) = (@all _143642).
Proof. exact (eq_refl (@all _143642)). Qed.
Lemma lem8097325 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term89 _143642 _143649 r s x) = False) : (term81 _143642 _143649 r s x) = (term178 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8097324 _143642) (@lem8097323 _143642 _143649 r s x h1)). Qed.
Lemma lem8097330 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : term179 _143642 _143649 r s x.
Proof. exact (fun h0 : (term89 _143642 _143649 r s x) = False => @lem8097325 _143642 _143649 r s x h0). Qed.
Lemma lem8097336 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term89 _143642 _143649 r s x) = True) : (term89 _143642 _143649 r s x) = True.
Proof. exact (h1). Qed.
Lemma lem8097337 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term89 _143642 _143649 r s x) = True) : (term89 _143642 _143649 r s x) = True.
Proof. exact (@lem8097336 _143642 _143649 r s x h1). Qed.
Lemma lem8097338 {_143642 : Type'} : (@COND _143642) = (@COND _143642).
Proof. exact (eq_refl (@COND _143642)). Qed.
Lemma lem8097339 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term89 _143642 _143649 r s x) = True) : (term90 _143642 _143649 r s x) = (@COND _143642 True).
Proof. exact (MK_COMB (@lem8097338 _143642) (@lem8097337 _143642 _143649 r s x h1)). Qed.
Lemma lem8097344 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term91 _143642 _143649 r s x) = (term91 _143642 _143649 r s x).
Proof. exact (eq_refl (term91 _143642 _143649 r s x)). Qed.
Lemma lem8097345 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term89 _143642 _143649 r s x) = True) : (term18 _143642 _143649 r s x) = (term97 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8097339 _143642 _143649 r s x h1) (@lem8097344 _143642 _143649 r s x)). Qed.
Lemma lem8097346 {_143642 : Type'} (_107385 : _143642) : _107385 = _107385.
Proof. exact (eq_refl _107385). Qed.
Lemma lem8097347 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term89 _143642 _143649 r s x) = True) : (term19 _143642 _143649 r s x _107385) = (term98 _143642 _143649 r s x _107385).
Proof. exact (MK_COMB (@lem8097345 _143642 _143649 r s x h1) (@lem8097346 _143642 _107385)). Qed.
Lemma lem8097349 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem8097350 {_143642 : Type'} (t2 : _143642) (t1 : _143642) : (@COND _143642 True t1 t2) = t1.
Proof. exact (@lem8097349 _143642 t2 t1). Qed.
Lemma lem8097351 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term98 _143642 _143649 r s x _107385) = (term91 _143642 _143649 r s x).
Proof. exact (@lem8097350 _143642 _107385 (term91 _143642 _143649 r s x)). Qed.
Lemma lem8097352 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term89 _143642 _143649 r s x) = True) : (term19 _143642 _143649 r s x _107385) = (term91 _143642 _143649 r s x).
Proof. exact (TRANS (@lem8097347 _143642 _143649 _107385 r s x h1) (@lem8097351 _143642 _143649 _107385 r s x)). Qed.
Lemma lem8097353 {_143642 : Type'} : (@eq _143642) = (@eq _143642).
Proof. exact (eq_refl (@eq _143642)). Qed.
Lemma lem8097354 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term89 _143642 _143649 r s x) = True) : (term21 _143642 _143649 r s x _107385) = (term99 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8097353 _143642) (@lem8097352 _143642 _143649 _107385 r s x h1)). Qed.
Lemma lem8097359 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term79 _143642 _143649 r _107385 s x) = (term79 _143642 _143649 r _107385 s x).
Proof. exact (eq_refl (term79 _143642 _143649 r _107385 s x)). Qed.
Lemma lem8097360 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term89 _143642 _143649 r s x) = True) : ((term19 _143642 _143649 r s x _107385) = (term79 _143642 _143649 r _107385 s x)) = ((term91 _143642 _143649 r s x) = (term79 _143642 _143649 r _107385 s x)).
Proof. exact (MK_COMB (@lem8097354 _143642 _143649 _107385 r s x h1) (@lem8097359 _143642 _143649 r _107385 s x)). Qed.
Lemma lem8097363 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term89 _143642 _143649 r s x) = True) : (term80 _143642 _143649 r s x) = (term180 _143642 _143649 r s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8097360 _143642 _143649 _107385 r s x h1)). Qed.
Lemma lem8097364 {_143642 : Type'} : (@all _143642) = (@all _143642).
Proof. exact (eq_refl (@all _143642)). Qed.
Lemma lem8097365 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : (term89 _143642 _143649 r s x) = True) : (term81 _143642 _143649 r s x) = (term181 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8097364 _143642) (@lem8097363 _143642 _143649 r s x h1)). Qed.
Lemma lem8097370 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : term182 _143642 _143649 r s x.
Proof. exact (fun h0 : (term89 _143642 _143649 r s x) = True => @lem8097365 _143642 _143649 r s x h0). Qed.
Lemma lem8097371 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : term183 _143642 _143649 r s x.
Proof. exact (conj (@lem8097330 _143642 _143649 r s x) (@lem8097370 _143642 _143649 r s x)). Qed.
Lemma lem8097373 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term86 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem8097374 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : term184 _143642 _143649 r s x.
Proof. exact (@lem8097373 (term81 _143642 _143649 r s x) (term181 _143642 _143649 r s x) (term89 _143642 _143649 r s x) (term178 _143642 _143649 r s x)). Qed.
Lemma lem8097389 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term81 _143642 _143649 r s x) = (term185 _143642 _143649 r s x).
Proof. exact (@lem8097374 _143642 _143649 r s x (@lem8097371 _143642 _143649 r s x)). Qed.
Lemma lem8097393 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term106 _143642 _143649 r x) = False.
Proof. exact (h1). Qed.
Lemma lem8097394 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term106 _143642 _143649 r x) = False.
Proof. exact (@lem8097393 _143642 _143649 r x h1). Qed.
Lemma lem8097395 {_143642 : Type'} : (@COND (_143642 -> Prop)) = (@COND (_143642 -> Prop)).
Proof. exact (eq_refl (@COND (_143642 -> Prop))). Qed.
Lemma lem8097396 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term107 _143642 _143649 r x) = (@COND (_143642 -> Prop) False).
Proof. exact (MK_COMB (@lem8097395 _143642) (@lem8097394 _143642 _143649 r x h1)). Qed.
Lemma lem8097397 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (r x) = (r x).
Proof. exact (eq_refl (r x)). Qed.
Lemma lem8097398 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term108 _143642 _143649 r x) = (term109 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8097396 _143642 _143649 r x h1) (@lem8097397 _143642 _143649 r x)). Qed.
Lemma lem8097399 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem8097400 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term110 _143642 _143649 r s x) = (term111 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8097398 _143642 _143649 r x h1) (@lem8097399 _143642 _143649 s x)). Qed.
Lemma lem8097402 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem8097403 {_143642 : Type'} (t1 : _143642 -> Prop) (t2 : _143642 -> Prop) : (@COND (_143642 -> Prop) False t1 t2) = t2.
Proof. exact (@lem8097402 (_143642 -> Prop) t1 t2). Qed.
Lemma lem8097404 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term111 _143642 _143649 r s x) = (s x).
Proof. exact (@lem8097403 _143642 (r x) (s x)). Qed.
Lemma lem8097405 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term110 _143642 _143649 r s x) = (s x).
Proof. exact (TRANS (@lem8097400 _143642 _143649 s r x h1) (@lem8097404 _143642 _143649 r s x)). Qed.
Lemma lem8097406 {_143642 : Type'} : (@ex1 _143642) = (@ex1 _143642).
Proof. exact (eq_refl (@ex1 _143642)). Qed.
Lemma lem8097407 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term89 _143642 _143649 r s x) = (term66 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8097406 _143642) (@lem8097405 _143642 _143649 s r x h1)). Qed.
Lemma lem8097408 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8097409 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term112 _143642 _143649 r s x) = (term113 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8097408) (@lem8097407 _143642 _143649 s r x h1)). Qed.
Lemma lem8097410 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8097411 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term114 _143642 _143649 r s x) = (term115 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8097410) (@lem8097409 _143642 _143649 s r x h1)). Qed.
Lemma lem8097413 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term106 _143642 _143649 r x) = False.
Proof. exact (h1). Qed.
Lemma lem8097414 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term106 _143642 _143649 r x) = False.
Proof. exact (@lem8097413 _143642 _143649 r x h1). Qed.
Lemma lem8097415 {_143642 : Type'} : (@COND (_143642 -> Prop)) = (@COND (_143642 -> Prop)).
Proof. exact (eq_refl (@COND (_143642 -> Prop))). Qed.
Lemma lem8097416 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term107 _143642 _143649 r x) = (@COND (_143642 -> Prop) False).
Proof. exact (MK_COMB (@lem8097415 _143642) (@lem8097414 _143642 _143649 r x h1)). Qed.
Lemma lem8097417 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (r x) = (r x).
Proof. exact (eq_refl (r x)). Qed.
Lemma lem8097418 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term108 _143642 _143649 r x) = (term109 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8097416 _143642 _143649 r x h1) (@lem8097417 _143642 _143649 r x)). Qed.
Lemma lem8097419 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem8097420 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term110 _143642 _143649 r s x) = (term111 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8097418 _143642 _143649 r x h1) (@lem8097419 _143642 _143649 s x)). Qed.
Lemma lem8097422 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem8097423 {_143642 : Type'} (t1 : _143642 -> Prop) (t2 : _143642 -> Prop) : (@COND (_143642 -> Prop) False t1 t2) = t2.
Proof. exact (@lem8097422 (_143642 -> Prop) t1 t2). Qed.
Lemma lem8097424 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term111 _143642 _143649 r s x) = (s x).
Proof. exact (@lem8097423 _143642 (r x) (s x)). Qed.
Lemma lem8097425 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term110 _143642 _143649 r s x) = (s x).
Proof. exact (TRANS (@lem8097420 _143642 _143649 s r x h1) (@lem8097424 _143642 _143649 r s x)). Qed.
Lemma lem8097426 {_143642 : Type'} : (@ε _143642) = (@ε _143642).
Proof. exact (eq_refl (@ε _143642)). Qed.
Lemma lem8097427 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term91 _143642 _143649 r s x) = (term68 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8097426 _143642) (@lem8097425 _143642 _143649 s r x h1)). Qed.
Lemma lem8097428 {_143642 : Type'} : (@eq _143642) = (@eq _143642).
Proof. exact (eq_refl (@eq _143642)). Qed.
Lemma lem8097429 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term99 _143642 _143649 r s x) = (term116 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8097428 _143642) (@lem8097427 _143642 _143649 s r x h1)). Qed.
Lemma lem8097431 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term106 _143642 _143649 r x) = False.
Proof. exact (h1). Qed.
Lemma lem8097432 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term106 _143642 _143649 r x) = False.
Proof. exact (@lem8097431 _143642 _143649 r x h1). Qed.
Lemma lem8097433 {_143642 : Type'} : (@COND _143642) = (@COND _143642).
Proof. exact (eq_refl (@COND _143642)). Qed.
Lemma lem8097434 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term25 _143642 _143649 r x) = (@COND _143642 False).
Proof. exact (MK_COMB (@lem8097433 _143642) (@lem8097432 _143642 _143649 r x h1)). Qed.
Lemma lem8097435 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term24 _143642 _143649 r x _107385) = (term24 _143642 _143649 r x _107385).
Proof. exact (eq_refl (term24 _143642 _143649 r x _107385)). Qed.
Lemma lem8097436 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term27 _143642 _143649 r x _107385) = (term117 _143642 _143649 r x _107385).
Proof. exact (MK_COMB (@lem8097434 _143642 _143649 r x h1) (@lem8097435 _143642 _143649 r x _107385)). Qed.
Lemma lem8097437 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term68 _143642 _143649 s x) = (term68 _143642 _143649 s x).
Proof. exact (eq_refl (term68 _143642 _143649 s x)). Qed.
Lemma lem8097438 {_143642 _143649 : Type'} (_107385 : _143642) (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term79 _143642 _143649 r _107385 s x) = (term186 _143642 _143649 r _107385 s x).
Proof. exact (MK_COMB (@lem8097436 _143642 _143649 _107385 r x h1) (@lem8097437 _143642 _143649 s x)). Qed.
Lemma lem8097440 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem8097441 {_143642 : Type'} (t1 : _143642) (t2 : _143642) : (@COND _143642 False t1 t2) = t2.
Proof. exact (@lem8097440 _143642 t1 t2). Qed.
Lemma lem8097442 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term186 _143642 _143649 r _107385 s x) = (term68 _143642 _143649 s x).
Proof. exact (@lem8097441 _143642 (term24 _143642 _143649 r x _107385) (term68 _143642 _143649 s x)). Qed.
Lemma lem8097443 {_143642 _143649 : Type'} (_107385 : _143642) (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term79 _143642 _143649 r _107385 s x) = (term68 _143642 _143649 s x).
Proof. exact (TRANS (@lem8097438 _143642 _143649 _107385 s r x h1) (@lem8097442 _143642 _143649 r _107385 s x)). Qed.
Lemma lem8097444 {_143642 _143649 : Type'} (_107385 : _143642) (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : ((term91 _143642 _143649 r s x) = (term79 _143642 _143649 r _107385 s x)) = ((term68 _143642 _143649 s x) = (term68 _143642 _143649 s x)).
Proof. exact (MK_COMB (@lem8097429 _143642 _143649 s r x h1) (@lem8097443 _143642 _143649 _107385 s r x h1)). Qed.
Lemma lem8097446 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem8097447 {_143642 : Type'} (x : _143642) : (x = x) = True.
Proof. exact (@lem8097446 _143642 x). Qed.
Lemma lem8097448 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : ((term68 _143642 _143649 s x) = (term68 _143642 _143649 s x)) = True.
Proof. exact (@lem8097447 _143642 (term68 _143642 _143649 s x)). Qed.
Lemma lem8097449 {_143642 _143649 : Type'} (_107385 : _143642) (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : ((term91 _143642 _143649 r s x) = (term79 _143642 _143649 r _107385 s x)) = True.
Proof. exact (TRANS (@lem8097444 _143642 _143649 _107385 s r x h1) (@lem8097448 _143642 _143649 s x)). Qed.
Lemma lem8097450 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term180 _143642 _143649 r s x) = (term127 _143642).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8097449 _143642 _143649 _107385 s r x h1)). Qed.
Lemma lem8097451 {_143642 : Type'} : (@all _143642) = (@all _143642).
Proof. exact (eq_refl (@all _143642)). Qed.
Lemma lem8097452 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term181 _143642 _143649 r s x) = (term128 _143642).
Proof. exact (MK_COMB (@lem8097451 _143642) (@lem8097450 _143642 _143649 s r x h1)). Qed.
Lemma lem8097454 {A : Type'} (t : Prop) : (term47 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8097455 {_143642 : Type'} (t : Prop) : (term47 _143642 t) = t.
Proof. exact (@lem8097454 _143642 t). Qed.
Lemma lem8097456 {_143642 : Type'} : (term128 _143642) = True.
Proof. exact (@lem8097455 _143642 True). Qed.
Lemma lem8097457 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term181 _143642 _143649 r s x) = True.
Proof. exact (TRANS (@lem8097452 _143642 _143649 s r x h1) (@lem8097456 _143642)). Qed.
Lemma lem8097458 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term187 _143642 _143649 r s x) = (term188 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8097411 _143642 _143649 s r x h1) (@lem8097457 _143642 _143649 s r x h1)). Qed.
Lemma lem8097460 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem8097461 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term188 _143642 _143649 s x) = True.
Proof. exact (@lem8097460 (term113 _143642 _143649 s x)). Qed.
Lemma lem8097462 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term187 _143642 _143649 r s x) = True.
Proof. exact (TRANS (@lem8097458 _143642 _143649 s r x h1) (@lem8097461 _143642 _143649 s x)). Qed.
Lemma lem8097463 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8097464 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term189 _143642 _143649 r s x) = (and True).
Proof. exact (MK_COMB (@lem8097463) (@lem8097462 _143642 _143649 s r x h1)). Qed.
Lemma lem8097466 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term106 _143642 _143649 r x) = False.
Proof. exact (h1). Qed.
Lemma lem8097467 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term106 _143642 _143649 r x) = False.
Proof. exact (@lem8097466 _143642 _143649 r x h1). Qed.
Lemma lem8097468 {_143642 : Type'} : (@COND (_143642 -> Prop)) = (@COND (_143642 -> Prop)).
Proof. exact (eq_refl (@COND (_143642 -> Prop))). Qed.
Lemma lem8097469 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term107 _143642 _143649 r x) = (@COND (_143642 -> Prop) False).
Proof. exact (MK_COMB (@lem8097468 _143642) (@lem8097467 _143642 _143649 r x h1)). Qed.
Lemma lem8097470 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (r x) = (r x).
Proof. exact (eq_refl (r x)). Qed.
Lemma lem8097471 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term108 _143642 _143649 r x) = (term109 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8097469 _143642 _143649 r x h1) (@lem8097470 _143642 _143649 r x)). Qed.
Lemma lem8097472 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem8097473 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term110 _143642 _143649 r s x) = (term111 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8097471 _143642 _143649 r x h1) (@lem8097472 _143642 _143649 s x)). Qed.
Lemma lem8097475 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem8097476 {_143642 : Type'} (t1 : _143642 -> Prop) (t2 : _143642 -> Prop) : (@COND (_143642 -> Prop) False t1 t2) = t2.
Proof. exact (@lem8097475 (_143642 -> Prop) t1 t2). Qed.
Lemma lem8097477 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term111 _143642 _143649 r s x) = (s x).
Proof. exact (@lem8097476 _143642 (r x) (s x)). Qed.
Lemma lem8097478 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term110 _143642 _143649 r s x) = (s x).
Proof. exact (TRANS (@lem8097473 _143642 _143649 s r x h1) (@lem8097477 _143642 _143649 r s x)). Qed.
Lemma lem8097479 {_143642 : Type'} : (@ex1 _143642) = (@ex1 _143642).
Proof. exact (eq_refl (@ex1 _143642)). Qed.
Lemma lem8097480 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term89 _143642 _143649 r s x) = (term66 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8097479 _143642) (@lem8097478 _143642 _143649 s r x h1)). Qed.
Lemma lem8097481 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8097482 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term125 _143642 _143649 r s x) = (term126 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8097481) (@lem8097480 _143642 _143649 s r x h1)). Qed.
Lemma lem8097484 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term106 _143642 _143649 r x) = False.
Proof. exact (h1). Qed.
Lemma lem8097485 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term106 _143642 _143649 r x) = False.
Proof. exact (@lem8097484 _143642 _143649 r x h1). Qed.
Lemma lem8097486 {_143642 : Type'} : (@COND _143642) = (@COND _143642).
Proof. exact (eq_refl (@COND _143642)). Qed.
Lemma lem8097487 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term25 _143642 _143649 r x) = (@COND _143642 False).
Proof. exact (MK_COMB (@lem8097486 _143642) (@lem8097485 _143642 _143649 r x h1)). Qed.
Lemma lem8097488 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term24 _143642 _143649 r x _107385) = (term24 _143642 _143649 r x _107385).
Proof. exact (eq_refl (term24 _143642 _143649 r x _107385)). Qed.
Lemma lem8097489 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term27 _143642 _143649 r x _107385) = (term117 _143642 _143649 r x _107385).
Proof. exact (MK_COMB (@lem8097487 _143642 _143649 r x h1) (@lem8097488 _143642 _143649 r x _107385)). Qed.
Lemma lem8097490 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term68 _143642 _143649 s x) = (term68 _143642 _143649 s x).
Proof. exact (eq_refl (term68 _143642 _143649 s x)). Qed.
Lemma lem8097491 {_143642 _143649 : Type'} (_107385 : _143642) (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term79 _143642 _143649 r _107385 s x) = (term186 _143642 _143649 r _107385 s x).
Proof. exact (MK_COMB (@lem8097489 _143642 _143649 _107385 r x h1) (@lem8097490 _143642 _143649 s x)). Qed.
Lemma lem8097493 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem8097494 {_143642 : Type'} (t1 : _143642) (t2 : _143642) : (@COND _143642 False t1 t2) = t2.
Proof. exact (@lem8097493 _143642 t1 t2). Qed.
Lemma lem8097495 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term186 _143642 _143649 r _107385 s x) = (term68 _143642 _143649 s x).
Proof. exact (@lem8097494 _143642 (term24 _143642 _143649 r x _107385) (term68 _143642 _143649 s x)). Qed.
Lemma lem8097496 {_143642 _143649 : Type'} (_107385 : _143642) (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term79 _143642 _143649 r _107385 s x) = (term68 _143642 _143649 s x).
Proof. exact (TRANS (@lem8097491 _143642 _143649 _107385 s r x h1) (@lem8097495 _143642 _143649 r _107385 s x)). Qed.
Lemma lem8097497 {_143642 : Type'} (_107385 : _143642) : (@eq _143642 _107385) = (@eq _143642 _107385).
Proof. exact (eq_refl (@eq _143642 _107385)). Qed.
Lemma lem8097498 {_143642 _143649 : Type'} (_107385 : _143642) (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (_107385 = (term79 _143642 _143649 r _107385 s x)) = (_107385 = (term68 _143642 _143649 s x)).
Proof. exact (MK_COMB (@lem8097497 _143642 _107385) (@lem8097496 _143642 _143649 _107385 s r x h1)). Qed.
Lemma lem8097501 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term177 _143642 _143649 r s x) = (term158 _143642 _143649 s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8097498 _143642 _143649 _107385 s r x h1)). Qed.
Lemma lem8097502 {_143642 : Type'} : (@all _143642) = (@all _143642).
Proof. exact (eq_refl (@all _143642)). Qed.
Lemma lem8097503 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term178 _143642 _143649 r s x) = (term159 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8097502 _143642) (@lem8097501 _143642 _143649 s r x h1)). Qed.
Lemma lem8097508 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term190 _143642 _143649 r s x) = (term191 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8097482 _143642 _143649 s r x h1) (@lem8097503 _143642 _143649 s r x h1)). Qed.
Lemma lem8097511 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term185 _143642 _143649 r s x) = (term192 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8097464 _143642 _143649 s r x h1) (@lem8097508 _143642 _143649 s r x h1)). Qed.
Lemma lem8097513 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8097514 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term192 _143642 _143649 s x) = (term191 _143642 _143649 s x).
Proof. exact (@lem8097513 (term191 _143642 _143649 s x)). Qed.
Lemma lem8097517 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = False) : (term185 _143642 _143649 r s x) = (term191 _143642 _143649 s x).
Proof. exact (TRANS (@lem8097511 _143642 _143649 s r x h1) (@lem8097514 _143642 _143649 s x)). Qed.
Lemma lem8097518 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : term193 _143642 _143649 r s x.
Proof. exact (fun h0 : (term106 _143642 _143649 r x) = False => @lem8097517 _143642 _143649 s r x h0). Qed.
Lemma lem8097520 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term106 _143642 _143649 r x) = True.
Proof. exact (h1). Qed.
Lemma lem8097521 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term106 _143642 _143649 r x) = True.
Proof. exact (@lem8097520 _143642 _143649 r x h1). Qed.
Lemma lem8097522 {_143642 : Type'} : (@COND (_143642 -> Prop)) = (@COND (_143642 -> Prop)).
Proof. exact (eq_refl (@COND (_143642 -> Prop))). Qed.
Lemma lem8097523 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term107 _143642 _143649 r x) = (@COND (_143642 -> Prop) True).
Proof. exact (MK_COMB (@lem8097522 _143642) (@lem8097521 _143642 _143649 r x h1)). Qed.
Lemma lem8097524 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (r x) = (r x).
Proof. exact (eq_refl (r x)). Qed.
Lemma lem8097525 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term108 _143642 _143649 r x) = (term133 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8097523 _143642 _143649 r x h1) (@lem8097524 _143642 _143649 r x)). Qed.
Lemma lem8097526 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem8097527 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term110 _143642 _143649 r s x) = (term134 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8097525 _143642 _143649 r x h1) (@lem8097526 _143642 _143649 s x)). Qed.
Lemma lem8097529 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem8097530 {_143642 : Type'} (t2 : _143642 -> Prop) (t1 : _143642 -> Prop) : (@COND (_143642 -> Prop) True t1 t2) = t1.
Proof. exact (@lem8097529 (_143642 -> Prop) t2 t1). Qed.
Lemma lem8097531 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) : (term134 _143642 _143649 r s x) = (r x).
Proof. exact (@lem8097530 _143642 (s x) (r x)). Qed.
Lemma lem8097532 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term110 _143642 _143649 r s x) = (r x).
Proof. exact (TRANS (@lem8097527 _143642 _143649 s r x h1) (@lem8097531 _143642 _143649 s r x)). Qed.
Lemma lem8097533 {_143642 : Type'} : (@ex1 _143642) = (@ex1 _143642).
Proof. exact (eq_refl (@ex1 _143642)). Qed.
Lemma lem8097534 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term89 _143642 _143649 r s x) = (term66 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8097533 _143642) (@lem8097532 _143642 _143649 s r x h1)). Qed.
Lemma lem8097535 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8097536 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term112 _143642 _143649 r s x) = (term113 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8097535) (@lem8097534 _143642 _143649 s r x h1)). Qed.
Lemma lem8097537 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8097538 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term114 _143642 _143649 r s x) = (term115 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8097537) (@lem8097536 _143642 _143649 s r x h1)). Qed.
Lemma lem8097540 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term106 _143642 _143649 r x) = True.
Proof. exact (h1). Qed.
Lemma lem8097541 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term106 _143642 _143649 r x) = True.
Proof. exact (@lem8097540 _143642 _143649 r x h1). Qed.
Lemma lem8097542 {_143642 : Type'} : (@COND (_143642 -> Prop)) = (@COND (_143642 -> Prop)).
Proof. exact (eq_refl (@COND (_143642 -> Prop))). Qed.
Lemma lem8097543 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term107 _143642 _143649 r x) = (@COND (_143642 -> Prop) True).
Proof. exact (MK_COMB (@lem8097542 _143642) (@lem8097541 _143642 _143649 r x h1)). Qed.
Lemma lem8097544 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (r x) = (r x).
Proof. exact (eq_refl (r x)). Qed.
Lemma lem8097545 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term108 _143642 _143649 r x) = (term133 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8097543 _143642 _143649 r x h1) (@lem8097544 _143642 _143649 r x)). Qed.
Lemma lem8097546 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem8097547 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term110 _143642 _143649 r s x) = (term134 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8097545 _143642 _143649 r x h1) (@lem8097546 _143642 _143649 s x)). Qed.
Lemma lem8097549 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem8097550 {_143642 : Type'} (t2 : _143642 -> Prop) (t1 : _143642 -> Prop) : (@COND (_143642 -> Prop) True t1 t2) = t1.
Proof. exact (@lem8097549 (_143642 -> Prop) t2 t1). Qed.
Lemma lem8097551 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) : (term134 _143642 _143649 r s x) = (r x).
Proof. exact (@lem8097550 _143642 (s x) (r x)). Qed.
Lemma lem8097552 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term110 _143642 _143649 r s x) = (r x).
Proof. exact (TRANS (@lem8097547 _143642 _143649 s r x h1) (@lem8097551 _143642 _143649 s r x)). Qed.
Lemma lem8097553 {_143642 : Type'} : (@ε _143642) = (@ε _143642).
Proof. exact (eq_refl (@ε _143642)). Qed.
Lemma lem8097554 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term91 _143642 _143649 r s x) = (term68 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8097553 _143642) (@lem8097552 _143642 _143649 s r x h1)). Qed.
Lemma lem8097555 {_143642 : Type'} : (@eq _143642) = (@eq _143642).
Proof. exact (eq_refl (@eq _143642)). Qed.
Lemma lem8097556 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term99 _143642 _143649 r s x) = (term116 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8097555 _143642) (@lem8097554 _143642 _143649 s r x h1)). Qed.
Lemma lem8097558 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term106 _143642 _143649 r x) = True.
Proof. exact (h1). Qed.
Lemma lem8097559 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term106 _143642 _143649 r x) = True.
Proof. exact (@lem8097558 _143642 _143649 r x h1). Qed.
Lemma lem8097560 {_143642 : Type'} : (@COND _143642) = (@COND _143642).
Proof. exact (eq_refl (@COND _143642)). Qed.
Lemma lem8097561 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term25 _143642 _143649 r x) = (@COND _143642 True).
Proof. exact (MK_COMB (@lem8097560 _143642) (@lem8097559 _143642 _143649 r x h1)). Qed.
Lemma lem8097562 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term24 _143642 _143649 r x _107385) = (term24 _143642 _143649 r x _107385).
Proof. exact (eq_refl (term24 _143642 _143649 r x _107385)). Qed.
Lemma lem8097563 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term27 _143642 _143649 r x _107385) = (term135 _143642 _143649 r x _107385).
Proof. exact (MK_COMB (@lem8097561 _143642 _143649 r x h1) (@lem8097562 _143642 _143649 r x _107385)). Qed.
Lemma lem8097564 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term68 _143642 _143649 s x) = (term68 _143642 _143649 s x).
Proof. exact (eq_refl (term68 _143642 _143649 s x)). Qed.
Lemma lem8097565 {_143642 _143649 : Type'} (_107385 : _143642) (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term79 _143642 _143649 r _107385 s x) = (term194 _143642 _143649 r _107385 s x).
Proof. exact (MK_COMB (@lem8097563 _143642 _143649 _107385 r x h1) (@lem8097564 _143642 _143649 s x)). Qed.
Lemma lem8097567 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem8097568 {_143642 : Type'} (t2 : _143642) (t1 : _143642) : (@COND _143642 True t1 t2) = t1.
Proof. exact (@lem8097567 _143642 t2 t1). Qed.
Lemma lem8097569 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term194 _143642 _143649 r _107385 s x) = (term24 _143642 _143649 r x _107385).
Proof. exact (@lem8097568 _143642 (term68 _143642 _143649 s x) (term24 _143642 _143649 r x _107385)). Qed.
Lemma lem8097570 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term79 _143642 _143649 r _107385 s x) = (term24 _143642 _143649 r x _107385).
Proof. exact (TRANS (@lem8097565 _143642 _143649 _107385 s r x h1) (@lem8097569 _143642 _143649 s r x _107385)). Qed.
Lemma lem8097571 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : ((term91 _143642 _143649 r s x) = (term79 _143642 _143649 r _107385 s x)) = ((term68 _143642 _143649 r x) = (term24 _143642 _143649 r x _107385)).
Proof. exact (MK_COMB (@lem8097556 _143642 _143649 s r x h1) (@lem8097570 _143642 _143649 s _107385 r x h1)). Qed.
Lemma lem8097574 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term180 _143642 _143649 r s x) = (term137 _143642 _143649 r x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8097571 _143642 _143649 s _107385 r x h1)). Qed.
Lemma lem8097575 {_143642 : Type'} : (@all _143642) = (@all _143642).
Proof. exact (eq_refl (@all _143642)). Qed.
Lemma lem8097576 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term181 _143642 _143649 r s x) = (term138 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8097575 _143642) (@lem8097574 _143642 _143649 s r x h1)). Qed.
Lemma lem8097581 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term187 _143642 _143649 r s x) = (term139 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8097538 _143642 _143649 s r x h1) (@lem8097576 _143642 _143649 s r x h1)). Qed.
Lemma lem8097584 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8097585 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term189 _143642 _143649 r s x) = (term140 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8097584) (@lem8097581 _143642 _143649 s r x h1)). Qed.
Lemma lem8097587 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term106 _143642 _143649 r x) = True.
Proof. exact (h1). Qed.
Lemma lem8097588 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term106 _143642 _143649 r x) = True.
Proof. exact (@lem8097587 _143642 _143649 r x h1). Qed.
Lemma lem8097589 {_143642 : Type'} : (@COND (_143642 -> Prop)) = (@COND (_143642 -> Prop)).
Proof. exact (eq_refl (@COND (_143642 -> Prop))). Qed.
Lemma lem8097590 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term107 _143642 _143649 r x) = (@COND (_143642 -> Prop) True).
Proof. exact (MK_COMB (@lem8097589 _143642) (@lem8097588 _143642 _143649 r x h1)). Qed.
Lemma lem8097591 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (r x) = (r x).
Proof. exact (eq_refl (r x)). Qed.
Lemma lem8097592 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term108 _143642 _143649 r x) = (term133 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8097590 _143642 _143649 r x h1) (@lem8097591 _143642 _143649 r x)). Qed.
Lemma lem8097593 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem8097594 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term110 _143642 _143649 r s x) = (term134 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8097592 _143642 _143649 r x h1) (@lem8097593 _143642 _143649 s x)). Qed.
Lemma lem8097596 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem8097597 {_143642 : Type'} (t2 : _143642 -> Prop) (t1 : _143642 -> Prop) : (@COND (_143642 -> Prop) True t1 t2) = t1.
Proof. exact (@lem8097596 (_143642 -> Prop) t2 t1). Qed.
Lemma lem8097598 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) : (term134 _143642 _143649 r s x) = (r x).
Proof. exact (@lem8097597 _143642 (s x) (r x)). Qed.
Lemma lem8097599 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term110 _143642 _143649 r s x) = (r x).
Proof. exact (TRANS (@lem8097594 _143642 _143649 s r x h1) (@lem8097598 _143642 _143649 s r x)). Qed.
Lemma lem8097600 {_143642 : Type'} : (@ex1 _143642) = (@ex1 _143642).
Proof. exact (eq_refl (@ex1 _143642)). Qed.
Lemma lem8097601 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term89 _143642 _143649 r s x) = (term66 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8097600 _143642) (@lem8097599 _143642 _143649 s r x h1)). Qed.
Lemma lem8097602 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8097603 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term125 _143642 _143649 r s x) = (term126 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8097602) (@lem8097601 _143642 _143649 s r x h1)). Qed.
Lemma lem8097605 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term106 _143642 _143649 r x) = True.
Proof. exact (h1). Qed.
Lemma lem8097606 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term106 _143642 _143649 r x) = True.
Proof. exact (@lem8097605 _143642 _143649 r x h1). Qed.
Lemma lem8097607 {_143642 : Type'} : (@COND _143642) = (@COND _143642).
Proof. exact (eq_refl (@COND _143642)). Qed.
Lemma lem8097608 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term25 _143642 _143649 r x) = (@COND _143642 True).
Proof. exact (MK_COMB (@lem8097607 _143642) (@lem8097606 _143642 _143649 r x h1)). Qed.
Lemma lem8097609 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term24 _143642 _143649 r x _107385) = (term24 _143642 _143649 r x _107385).
Proof. exact (eq_refl (term24 _143642 _143649 r x _107385)). Qed.
Lemma lem8097610 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term27 _143642 _143649 r x _107385) = (term135 _143642 _143649 r x _107385).
Proof. exact (MK_COMB (@lem8097608 _143642 _143649 r x h1) (@lem8097609 _143642 _143649 r x _107385)). Qed.
Lemma lem8097611 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term68 _143642 _143649 s x) = (term68 _143642 _143649 s x).
Proof. exact (eq_refl (term68 _143642 _143649 s x)). Qed.
Lemma lem8097612 {_143642 _143649 : Type'} (_107385 : _143642) (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term79 _143642 _143649 r _107385 s x) = (term194 _143642 _143649 r _107385 s x).
Proof. exact (MK_COMB (@lem8097610 _143642 _143649 _107385 r x h1) (@lem8097611 _143642 _143649 s x)). Qed.
Lemma lem8097614 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem8097615 {_143642 : Type'} (t2 : _143642) (t1 : _143642) : (@COND _143642 True t1 t2) = t1.
Proof. exact (@lem8097614 _143642 t2 t1). Qed.
Lemma lem8097616 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term194 _143642 _143649 r _107385 s x) = (term24 _143642 _143649 r x _107385).
Proof. exact (@lem8097615 _143642 (term68 _143642 _143649 s x) (term24 _143642 _143649 r x _107385)). Qed.
Lemma lem8097617 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term79 _143642 _143649 r _107385 s x) = (term24 _143642 _143649 r x _107385).
Proof. exact (TRANS (@lem8097612 _143642 _143649 _107385 s r x h1) (@lem8097616 _143642 _143649 s r x _107385)). Qed.
Lemma lem8097618 {_143642 : Type'} (_107385 : _143642) : (@eq _143642 _107385) = (@eq _143642 _107385).
Proof. exact (eq_refl (@eq _143642 _107385)). Qed.
Lemma lem8097619 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (_107385 = (term79 _143642 _143649 r _107385 s x)) = (_107385 = (term24 _143642 _143649 r x _107385)).
Proof. exact (MK_COMB (@lem8097618 _143642 _107385) (@lem8097617 _143642 _143649 s _107385 r x h1)). Qed.
Lemma lem8097622 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term177 _143642 _143649 r s x) = (term141 _143642 _143649 r x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8097619 _143642 _143649 s _107385 r x h1)). Qed.
Lemma lem8097623 {_143642 : Type'} : (@all _143642) = (@all _143642).
Proof. exact (eq_refl (@all _143642)). Qed.
Lemma lem8097624 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term178 _143642 _143649 r s x) = (term142 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8097623 _143642) (@lem8097622 _143642 _143649 s r x h1)). Qed.
Lemma lem8097629 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term190 _143642 _143649 r s x) = (term143 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8097603 _143642 _143649 s r x h1) (@lem8097624 _143642 _143649 s r x h1)). Qed.
Lemma lem8097632 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term106 _143642 _143649 r x) = True) : (term185 _143642 _143649 r s x) = (term144 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8097585 _143642 _143649 s r x h1) (@lem8097629 _143642 _143649 s r x h1)). Qed.
Lemma lem8097635 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) : term195 _143642 _143649 s r x.
Proof. exact (fun h0 : (term106 _143642 _143649 r x) = True => @lem8097632 _143642 _143649 s r x h0). Qed.
Lemma lem8097636 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) : term196 _143642 _143649 s r x.
Proof. exact (conj (@lem8097518 _143642 _143649 r s x) (@lem8097635 _143642 _143649 s r x)). Qed.
Lemma lem8097638 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term86 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem8097639 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : term197 _143642 _143649 r s x.
Proof. exact (@lem8097638 (term185 _143642 _143649 r s x) (term144 _143642 _143649 r x) (term106 _143642 _143649 r x) (term191 _143642 _143649 s x)). Qed.
Lemma lem8097654 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term185 _143642 _143649 r s x) = (term198 _143642 _143649 r s x).
Proof. exact (@lem8097639 _143642 _143649 r s x (@lem8097636 _143642 _143649 s r x)). Qed.
Lemma lem8097662 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term66 _143642 _143649 r x) = False.
Proof. exact (h1). Qed.
Lemma lem8097663 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8097664 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term113 _143642 _143649 r x) = (~ False).
Proof. exact (MK_COMB (@lem8097663) (@lem8097662 _143642 _143649 r x h1)). Qed.
Lemma lem8097666 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem8097667 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term113 _143642 _143649 r x) = True.
Proof. exact (TRANS (@lem8097664 _143642 _143649 r x h1) (@lem8097666)). Qed.
Lemma lem8097668 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8097669 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term115 _143642 _143649 r x) = (or True).
Proof. exact (MK_COMB (@lem8097668) (@lem8097667 _143642 _143649 r x h1)). Qed.
Lemma lem8097671 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term66 _143642 _143649 r x) = False.
Proof. exact (h1). Qed.
Lemma lem8097672 {_143642 : Type'} : (@COND _143642) = (@COND _143642).
Proof. exact (eq_refl (@COND _143642)). Qed.
Lemma lem8097673 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term67 _143642 _143649 r x) = (@COND _143642 False).
Proof. exact (MK_COMB (@lem8097672 _143642) (@lem8097671 _143642 _143649 r x h1)). Qed.
Lemma lem8097674 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term68 _143642 _143649 r x) = (term68 _143642 _143649 r x).
Proof. exact (eq_refl (term68 _143642 _143649 r x)). Qed.
Lemma lem8097675 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term22 _143642 _143649 r x) = (term69 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8097673 _143642 _143649 r x h1) (@lem8097674 _143642 _143649 r x)). Qed.
Lemma lem8097676 {_143642 : Type'} (_107385 : _143642) : _107385 = _107385.
Proof. exact (eq_refl _107385). Qed.
Lemma lem8097677 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term24 _143642 _143649 r x _107385) = (term70 _143642 _143649 r x _107385).
Proof. exact (MK_COMB (@lem8097675 _143642 _143649 r x h1) (@lem8097676 _143642 _107385)). Qed.
Lemma lem8097679 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem8097680 {_143642 : Type'} (t1 : _143642) (t2 : _143642) : (@COND _143642 False t1 t2) = t2.
Proof. exact (@lem8097679 _143642 t1 t2). Qed.
Lemma lem8097681 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term70 _143642 _143649 r x _107385) = _107385.
Proof. exact (@lem8097680 _143642 (term68 _143642 _143649 r x) _107385). Qed.
Lemma lem8097682 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term24 _143642 _143649 r x _107385) = _107385.
Proof. exact (TRANS (@lem8097677 _143642 _143649 _107385 r x h1) (@lem8097681 _143642 _143649 r x _107385)). Qed.
Lemma lem8097683 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term116 _143642 _143649 r x) = (term116 _143642 _143649 r x).
Proof. exact (eq_refl (term116 _143642 _143649 r x)). Qed.
Lemma lem8097684 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : ((term68 _143642 _143649 r x) = (term24 _143642 _143649 r x _107385)) = ((term68 _143642 _143649 r x) = _107385).
Proof. exact (MK_COMB (@lem8097683 _143642 _143649 r x) (@lem8097682 _143642 _143649 _107385 r x h1)). Qed.
Lemma lem8097687 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term137 _143642 _143649 r x) = (term119 _143642 _143649 r x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8097684 _143642 _143649 _107385 r x h1)). Qed.
Lemma lem8097688 {_143642 : Type'} : (@all _143642) = (@all _143642).
Proof. exact (eq_refl (@all _143642)). Qed.
Lemma lem8097689 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term138 _143642 _143649 r x) = (term120 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8097688 _143642) (@lem8097687 _143642 _143649 r x h1)). Qed.
Lemma lem8097694 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term139 _143642 _143649 r x) = (term149 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8097669 _143642 _143649 r x h1) (@lem8097689 _143642 _143649 r x h1)). Qed.
Lemma lem8097696 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem8097697 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term149 _143642 _143649 r x) = True.
Proof. exact (@lem8097696 (term120 _143642 _143649 r x)). Qed.
Lemma lem8097698 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term139 _143642 _143649 r x) = True.
Proof. exact (TRANS (@lem8097694 _143642 _143649 r x h1) (@lem8097697 _143642 _143649 r x)). Qed.
Lemma lem8097699 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8097700 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term140 _143642 _143649 r x) = (and True).
Proof. exact (MK_COMB (@lem8097699) (@lem8097698 _143642 _143649 r x h1)). Qed.
Lemma lem8097702 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term66 _143642 _143649 r x) = False.
Proof. exact (h1). Qed.
Lemma lem8097703 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8097704 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term126 _143642 _143649 r x) = (or False).
Proof. exact (MK_COMB (@lem8097703) (@lem8097702 _143642 _143649 r x h1)). Qed.
Lemma lem8097706 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term66 _143642 _143649 r x) = False.
Proof. exact (h1). Qed.
Lemma lem8097707 {_143642 : Type'} : (@COND _143642) = (@COND _143642).
Proof. exact (eq_refl (@COND _143642)). Qed.
Lemma lem8097708 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term67 _143642 _143649 r x) = (@COND _143642 False).
Proof. exact (MK_COMB (@lem8097707 _143642) (@lem8097706 _143642 _143649 r x h1)). Qed.
Lemma lem8097709 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term68 _143642 _143649 r x) = (term68 _143642 _143649 r x).
Proof. exact (eq_refl (term68 _143642 _143649 r x)). Qed.
Lemma lem8097710 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term22 _143642 _143649 r x) = (term69 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8097708 _143642 _143649 r x h1) (@lem8097709 _143642 _143649 r x)). Qed.
Lemma lem8097711 {_143642 : Type'} (_107385 : _143642) : _107385 = _107385.
Proof. exact (eq_refl _107385). Qed.
Lemma lem8097712 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term24 _143642 _143649 r x _107385) = (term70 _143642 _143649 r x _107385).
Proof. exact (MK_COMB (@lem8097710 _143642 _143649 r x h1) (@lem8097711 _143642 _107385)). Qed.
Lemma lem8097714 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem8097715 {_143642 : Type'} (t1 : _143642) (t2 : _143642) : (@COND _143642 False t1 t2) = t2.
Proof. exact (@lem8097714 _143642 t1 t2). Qed.
Lemma lem8097716 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term70 _143642 _143649 r x _107385) = _107385.
Proof. exact (@lem8097715 _143642 (term68 _143642 _143649 r x) _107385). Qed.
Lemma lem8097717 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term24 _143642 _143649 r x _107385) = _107385.
Proof. exact (TRANS (@lem8097712 _143642 _143649 _107385 r x h1) (@lem8097716 _143642 _143649 r x _107385)). Qed.
Lemma lem8097718 {_143642 : Type'} (_107385 : _143642) : (@eq _143642 _107385) = (@eq _143642 _107385).
Proof. exact (eq_refl (@eq _143642 _107385)). Qed.
Lemma lem8097719 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (_107385 = (term24 _143642 _143649 r x _107385)) = (_107385 = _107385).
Proof. exact (MK_COMB (@lem8097718 _143642 _107385) (@lem8097717 _143642 _143649 _107385 r x h1)). Qed.
Lemma lem8097721 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem8097722 {_143642 : Type'} (x : _143642) : (x = x) = True.
Proof. exact (@lem8097721 _143642 x). Qed.
Lemma lem8097723 {_143642 : Type'} (_107385 : _143642) : (_107385 = _107385) = True.
Proof. exact (@lem8097722 _143642 _107385). Qed.
Lemma lem8097724 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (_107385 = (term24 _143642 _143649 r x _107385)) = True.
Proof. exact (TRANS (@lem8097719 _143642 _143649 _107385 r x h1) (@lem8097723 _143642 _107385)). Qed.
Lemma lem8097725 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term141 _143642 _143649 r x) = (term127 _143642).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8097724 _143642 _143649 _107385 r x h1)). Qed.
Lemma lem8097726 {_143642 : Type'} : (@all _143642) = (@all _143642).
Proof. exact (eq_refl (@all _143642)). Qed.
Lemma lem8097727 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term142 _143642 _143649 r x) = (term128 _143642).
Proof. exact (MK_COMB (@lem8097726 _143642) (@lem8097725 _143642 _143649 r x h1)). Qed.
Lemma lem8097729 {A : Type'} (t : Prop) : (term47 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8097730 {_143642 : Type'} (t : Prop) : (term47 _143642 t) = t.
Proof. exact (@lem8097729 _143642 t). Qed.
Lemma lem8097731 {_143642 : Type'} : (term128 _143642) = True.
Proof. exact (@lem8097730 _143642 True). Qed.
Lemma lem8097732 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term142 _143642 _143649 r x) = True.
Proof. exact (TRANS (@lem8097727 _143642 _143649 r x h1) (@lem8097731 _143642)). Qed.
Lemma lem8097733 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term143 _143642 _143649 r x) = (False \/ True).
Proof. exact (MK_COMB (@lem8097704 _143642 _143649 r x h1) (@lem8097732 _143642 _143649 r x h1)). Qed.
Lemma lem8097735 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem8097736 : (False \/ True) = True.
Proof. exact (@lem8097735 True). Qed.
Lemma lem8097737 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term143 _143642 _143649 r x) = True.
Proof. exact (TRANS (@lem8097733 _143642 _143649 r x h1) (@lem8097736)). Qed.
Lemma lem8097738 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term144 _143642 _143649 r x) = (True /\ True).
Proof. exact (MK_COMB (@lem8097700 _143642 _143649 r x h1) (@lem8097737 _143642 _143649 r x h1)). Qed.
Lemma lem8097740 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8097741 : (True /\ True) = True.
Proof. exact (@lem8097740 True). Qed.
Lemma lem8097742 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term144 _143642 _143649 r x) = True.
Proof. exact (TRANS (@lem8097738 _143642 _143649 r x h1) (@lem8097741)). Qed.
Lemma lem8097743 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term150 _143642 _143649 r x) = (term150 _143642 _143649 r x).
Proof. exact (eq_refl (term150 _143642 _143649 r x)). Qed.
Lemma lem8097744 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term151 _143642 _143649 r x) = (term152 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8097743 _143642 _143649 r x) (@lem8097742 _143642 _143649 r x h1)). Qed.
Lemma lem8097746 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem8097747 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term152 _143642 _143649 r x) = True.
Proof. exact (@lem8097746 (term153 _143642 _143649 r x)). Qed.
Lemma lem8097748 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term151 _143642 _143649 r x) = True.
Proof. exact (TRANS (@lem8097744 _143642 _143649 r x h1) (@lem8097747 _143642 _143649 r x)). Qed.
Lemma lem8097749 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8097750 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term154 _143642 _143649 r x) = (and True).
Proof. exact (MK_COMB (@lem8097749) (@lem8097748 _143642 _143649 r x h1)). Qed.
Lemma lem8097765 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term199 _143642 _143649 r s x) = (term199 _143642 _143649 r s x).
Proof. exact (eq_refl (term199 _143642 _143649 r s x)). Qed.
Lemma lem8097766 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term198 _143642 _143649 r s x) = (term200 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8097750 _143642 _143649 r x h1) (@lem8097765 _143642 _143649 r s x)). Qed.
Lemma lem8097768 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8097769 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term200 _143642 _143649 r s x) = (term199 _143642 _143649 r s x).
Proof. exact (@lem8097768 (term199 _143642 _143649 r s x)). Qed.
Lemma lem8097772 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = False) : (term198 _143642 _143649 r s x) = (term199 _143642 _143649 r s x).
Proof. exact (TRANS (@lem8097766 _143642 _143649 s r x h1) (@lem8097769 _143642 _143649 r s x)). Qed.
Lemma lem8097773 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : term201 _143642 _143649 r s x.
Proof. exact (fun h0 : (term66 _143642 _143649 r x) = False => @lem8097772 _143642 _143649 s r x h0). Qed.
Lemma lem8097779 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term66 _143642 _143649 r x) = True.
Proof. exact (h1). Qed.
Lemma lem8097780 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8097781 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term113 _143642 _143649 r x) = (~ True).
Proof. exact (MK_COMB (@lem8097780) (@lem8097779 _143642 _143649 r x h1)). Qed.
Lemma lem8097783 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem8097784 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term113 _143642 _143649 r x) = False.
Proof. exact (TRANS (@lem8097781 _143642 _143649 r x h1) (@lem8097783)). Qed.
Lemma lem8097785 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8097786 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term115 _143642 _143649 r x) = (or False).
Proof. exact (MK_COMB (@lem8097785) (@lem8097784 _143642 _143649 r x h1)). Qed.
Lemma lem8097788 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term66 _143642 _143649 r x) = True.
Proof. exact (h1). Qed.
Lemma lem8097789 {_143642 : Type'} : (@COND _143642) = (@COND _143642).
Proof. exact (eq_refl (@COND _143642)). Qed.
Lemma lem8097790 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term67 _143642 _143649 r x) = (@COND _143642 True).
Proof. exact (MK_COMB (@lem8097789 _143642) (@lem8097788 _143642 _143649 r x h1)). Qed.
Lemma lem8097791 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term68 _143642 _143649 r x) = (term68 _143642 _143649 r x).
Proof. exact (eq_refl (term68 _143642 _143649 r x)). Qed.
Lemma lem8097792 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term22 _143642 _143649 r x) = (term77 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8097790 _143642 _143649 r x h1) (@lem8097791 _143642 _143649 r x)). Qed.
Lemma lem8097793 {_143642 : Type'} (_107385 : _143642) : _107385 = _107385.
Proof. exact (eq_refl _107385). Qed.
Lemma lem8097794 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term24 _143642 _143649 r x _107385) = (term78 _143642 _143649 r x _107385).
Proof. exact (MK_COMB (@lem8097792 _143642 _143649 r x h1) (@lem8097793 _143642 _107385)). Qed.
Lemma lem8097796 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem8097797 {_143642 : Type'} (t2 : _143642) (t1 : _143642) : (@COND _143642 True t1 t2) = t1.
Proof. exact (@lem8097796 _143642 t2 t1). Qed.
Lemma lem8097798 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) : (term78 _143642 _143649 r x _107385) = (term68 _143642 _143649 r x).
Proof. exact (@lem8097797 _143642 _107385 (term68 _143642 _143649 r x)). Qed.
Lemma lem8097799 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term24 _143642 _143649 r x _107385) = (term68 _143642 _143649 r x).
Proof. exact (TRANS (@lem8097794 _143642 _143649 _107385 r x h1) (@lem8097798 _143642 _143649 _107385 r x)). Qed.
Lemma lem8097800 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term116 _143642 _143649 r x) = (term116 _143642 _143649 r x).
Proof. exact (eq_refl (term116 _143642 _143649 r x)). Qed.
Lemma lem8097801 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : ((term68 _143642 _143649 r x) = (term24 _143642 _143649 r x _107385)) = ((term68 _143642 _143649 r x) = (term68 _143642 _143649 r x)).
Proof. exact (MK_COMB (@lem8097800 _143642 _143649 r x) (@lem8097799 _143642 _143649 _107385 r x h1)). Qed.
Lemma lem8097803 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem8097804 {_143642 : Type'} (x : _143642) : (x = x) = True.
Proof. exact (@lem8097803 _143642 x). Qed.
Lemma lem8097805 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : ((term68 _143642 _143649 r x) = (term68 _143642 _143649 r x)) = True.
Proof. exact (@lem8097804 _143642 (term68 _143642 _143649 r x)). Qed.
Lemma lem8097806 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : ((term68 _143642 _143649 r x) = (term24 _143642 _143649 r x _107385)) = True.
Proof. exact (TRANS (@lem8097801 _143642 _143649 _107385 r x h1) (@lem8097805 _143642 _143649 r x)). Qed.
Lemma lem8097807 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term137 _143642 _143649 r x) = (term127 _143642).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8097806 _143642 _143649 _107385 r x h1)). Qed.
Lemma lem8097808 {_143642 : Type'} : (@all _143642) = (@all _143642).
Proof. exact (eq_refl (@all _143642)). Qed.
Lemma lem8097809 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term138 _143642 _143649 r x) = (term128 _143642).
Proof. exact (MK_COMB (@lem8097808 _143642) (@lem8097807 _143642 _143649 r x h1)). Qed.
Lemma lem8097811 {A : Type'} (t : Prop) : (term47 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8097812 {_143642 : Type'} (t : Prop) : (term47 _143642 t) = t.
Proof. exact (@lem8097811 _143642 t). Qed.
Lemma lem8097813 {_143642 : Type'} : (term128 _143642) = True.
Proof. exact (@lem8097812 _143642 True). Qed.
Lemma lem8097814 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term138 _143642 _143649 r x) = True.
Proof. exact (TRANS (@lem8097809 _143642 _143649 r x h1) (@lem8097813 _143642)). Qed.
Lemma lem8097815 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term139 _143642 _143649 r x) = (False \/ True).
Proof. exact (MK_COMB (@lem8097786 _143642 _143649 r x h1) (@lem8097814 _143642 _143649 r x h1)). Qed.
Lemma lem8097817 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem8097818 : (False \/ True) = True.
Proof. exact (@lem8097817 True). Qed.
Lemma lem8097819 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term139 _143642 _143649 r x) = True.
Proof. exact (TRANS (@lem8097815 _143642 _143649 r x h1) (@lem8097818)). Qed.
Lemma lem8097820 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8097821 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term140 _143642 _143649 r x) = (and True).
Proof. exact (MK_COMB (@lem8097820) (@lem8097819 _143642 _143649 r x h1)). Qed.
Lemma lem8097823 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term66 _143642 _143649 r x) = True.
Proof. exact (h1). Qed.
Lemma lem8097824 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8097825 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term126 _143642 _143649 r x) = (or True).
Proof. exact (MK_COMB (@lem8097824) (@lem8097823 _143642 _143649 r x h1)). Qed.
Lemma lem8097827 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term66 _143642 _143649 r x) = True.
Proof. exact (h1). Qed.
Lemma lem8097828 {_143642 : Type'} : (@COND _143642) = (@COND _143642).
Proof. exact (eq_refl (@COND _143642)). Qed.
Lemma lem8097829 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term67 _143642 _143649 r x) = (@COND _143642 True).
Proof. exact (MK_COMB (@lem8097828 _143642) (@lem8097827 _143642 _143649 r x h1)). Qed.
Lemma lem8097830 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term68 _143642 _143649 r x) = (term68 _143642 _143649 r x).
Proof. exact (eq_refl (term68 _143642 _143649 r x)). Qed.
Lemma lem8097831 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term22 _143642 _143649 r x) = (term77 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8097829 _143642 _143649 r x h1) (@lem8097830 _143642 _143649 r x)). Qed.
Lemma lem8097832 {_143642 : Type'} (_107385 : _143642) : _107385 = _107385.
Proof. exact (eq_refl _107385). Qed.
Lemma lem8097833 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term24 _143642 _143649 r x _107385) = (term78 _143642 _143649 r x _107385).
Proof. exact (MK_COMB (@lem8097831 _143642 _143649 r x h1) (@lem8097832 _143642 _107385)). Qed.
Lemma lem8097835 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem8097836 {_143642 : Type'} (t2 : _143642) (t1 : _143642) : (@COND _143642 True t1 t2) = t1.
Proof. exact (@lem8097835 _143642 t2 t1). Qed.
Lemma lem8097837 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) : (term78 _143642 _143649 r x _107385) = (term68 _143642 _143649 r x).
Proof. exact (@lem8097836 _143642 _107385 (term68 _143642 _143649 r x)). Qed.
Lemma lem8097838 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term24 _143642 _143649 r x _107385) = (term68 _143642 _143649 r x).
Proof. exact (TRANS (@lem8097833 _143642 _143649 _107385 r x h1) (@lem8097837 _143642 _143649 _107385 r x)). Qed.
Lemma lem8097839 {_143642 : Type'} (_107385 : _143642) : (@eq _143642 _107385) = (@eq _143642 _107385).
Proof. exact (eq_refl (@eq _143642 _107385)). Qed.
Lemma lem8097840 {_143642 _143649 : Type'} (_107385 : _143642) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (_107385 = (term24 _143642 _143649 r x _107385)) = (_107385 = (term68 _143642 _143649 r x)).
Proof. exact (MK_COMB (@lem8097839 _143642 _107385) (@lem8097838 _143642 _143649 _107385 r x h1)). Qed.
Lemma lem8097843 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term141 _143642 _143649 r x) = (term158 _143642 _143649 r x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8097840 _143642 _143649 _107385 r x h1)). Qed.
Lemma lem8097844 {_143642 : Type'} : (@all _143642) = (@all _143642).
Proof. exact (eq_refl (@all _143642)). Qed.
Lemma lem8097845 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term142 _143642 _143649 r x) = (term159 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8097844 _143642) (@lem8097843 _143642 _143649 r x h1)). Qed.
Lemma lem8097850 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term143 _143642 _143649 r x) = (term160 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8097825 _143642 _143649 r x h1) (@lem8097845 _143642 _143649 r x h1)). Qed.
Lemma lem8097852 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem8097853 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term160 _143642 _143649 r x) = True.
Proof. exact (@lem8097852 (term159 _143642 _143649 r x)). Qed.
Lemma lem8097854 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term143 _143642 _143649 r x) = True.
Proof. exact (TRANS (@lem8097850 _143642 _143649 r x h1) (@lem8097853 _143642 _143649 r x)). Qed.
Lemma lem8097855 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term144 _143642 _143649 r x) = (True /\ True).
Proof. exact (MK_COMB (@lem8097821 _143642 _143649 r x h1) (@lem8097854 _143642 _143649 r x h1)). Qed.
Lemma lem8097857 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8097858 : (True /\ True) = True.
Proof. exact (@lem8097857 True). Qed.
Lemma lem8097859 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term144 _143642 _143649 r x) = True.
Proof. exact (TRANS (@lem8097855 _143642 _143649 r x h1) (@lem8097858)). Qed.
Lemma lem8097860 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term150 _143642 _143649 r x) = (term150 _143642 _143649 r x).
Proof. exact (eq_refl (term150 _143642 _143649 r x)). Qed.
Lemma lem8097861 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term151 _143642 _143649 r x) = (term152 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8097860 _143642 _143649 r x) (@lem8097859 _143642 _143649 r x h1)). Qed.
Lemma lem8097863 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem8097864 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term152 _143642 _143649 r x) = True.
Proof. exact (@lem8097863 (term153 _143642 _143649 r x)). Qed.
Lemma lem8097865 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term151 _143642 _143649 r x) = True.
Proof. exact (TRANS (@lem8097861 _143642 _143649 r x h1) (@lem8097864 _143642 _143649 r x)). Qed.
Lemma lem8097866 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8097867 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term154 _143642 _143649 r x) = (and True).
Proof. exact (MK_COMB (@lem8097866) (@lem8097865 _143642 _143649 r x h1)). Qed.
Lemma lem8097882 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term199 _143642 _143649 r s x) = (term199 _143642 _143649 r s x).
Proof. exact (eq_refl (term199 _143642 _143649 r s x)). Qed.
Lemma lem8097883 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term198 _143642 _143649 r s x) = (term200 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8097867 _143642 _143649 r x h1) (@lem8097882 _143642 _143649 r s x)). Qed.
Lemma lem8097885 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8097886 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term200 _143642 _143649 r s x) = (term199 _143642 _143649 r s x).
Proof. exact (@lem8097885 (term199 _143642 _143649 r s x)). Qed.
Lemma lem8097889 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (r : type1470 _143642 _143649) (x : _143649) (h1 : (term66 _143642 _143649 r x) = True) : (term198 _143642 _143649 r s x) = (term199 _143642 _143649 r s x).
Proof. exact (TRANS (@lem8097883 _143642 _143649 s r x h1) (@lem8097886 _143642 _143649 r s x)). Qed.
Lemma lem8097890 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : term202 _143642 _143649 r s x.
Proof. exact (fun h0 : (term66 _143642 _143649 r x) = True => @lem8097889 _143642 _143649 s r x h0). Qed.
Lemma lem8097891 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : term203 _143642 _143649 r s x.
Proof. exact (conj (@lem8097773 _143642 _143649 r s x) (@lem8097890 _143642 _143649 r s x)). Qed.
Lemma lem8097893 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term86 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem8097894 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : term204 _143642 _143649 r s x.
Proof. exact (@lem8097893 (term198 _143642 _143649 r s x) (term199 _143642 _143649 r s x) (term66 _143642 _143649 r x) (term199 _143642 _143649 r s x)). Qed.
Lemma lem8097909 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term198 _143642 _143649 r s x) = (term205 _143642 _143649 r s x).
Proof. exact (@lem8097894 _143642 _143649 r s x (@lem8097891 _143642 _143649 r s x)). Qed.
Lemma lem8097910 {_143642 _143649 : Type'} (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (_107385 = (term68 _143642 _143649 s x)) = (_107385 = (term68 _143642 _143649 s x)).
Proof. exact (eq_refl (_107385 = (term68 _143642 _143649 s x))). Qed.
Lemma lem8097911 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term158 _143642 _143649 s x) = (term158 _143642 _143649 s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8097910 _143642 _143649 _107385 s x)). Qed.
Lemma lem8097912 {_143642 : Type'} : (@all _143642) = (@all _143642).
Proof. exact (eq_refl (@all _143642)). Qed.
Lemma lem8097913 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term159 _143642 _143649 s x) = (term159 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8097912 _143642) (@lem8097911 _143642 _143649 s x)). Qed.
Lemma lem8097916 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term126 _143642 _143649 s x) = (term126 _143642 _143649 s x).
Proof. exact (eq_refl (term126 _143642 _143649 s x)). Qed.
Lemma lem8097917 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term191 _143642 _143649 s x) = (term191 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8097916 _143642 _143649 s x) (@lem8097913 _143642 _143649 s x)). Qed.
Lemma lem8097918 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (y : _143642) : (r x y) = (r x y).
Proof. exact (eq_refl (r x y)). Qed.
Lemma lem8097919 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term165 _143642 _143649 r x) = (term165 _143642 _143649 r x).
Proof. exact (fun_ext (fun y : _143642 => @lem8097918 _143642 _143649 r x y)). Qed.
Lemma lem8097920 {_143642 : Type'} : (@ex _143642) = (@ex _143642).
Proof. exact (eq_refl (@ex _143642)). Qed.
Lemma lem8097921 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term106 _143642 _143649 r x) = (term106 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8097920 _143642) (@lem8097919 _143642 _143649 r x)). Qed.
Lemma lem8097922 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8097923 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term166 _143642 _143649 r x) = (term166 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8097922) (@lem8097921 _143642 _143649 r x)). Qed.
Lemma lem8097924 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term199 _143642 _143649 r s x) = (term199 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8097923 _143642 _143649 r x) (@lem8097917 _143642 _143649 s x)). Qed.
Lemma lem8097927 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term126 _143642 _143649 r x) = (term126 _143642 _143649 r x).
Proof. exact (eq_refl (term126 _143642 _143649 r x)). Qed.
Lemma lem8097928 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term206 _143642 _143649 r s x) = (term206 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8097927 _143642 _143649 r x) (@lem8097924 _143642 _143649 r s x)). Qed.
Lemma lem8097929 {_143642 _143649 : Type'} (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (_107385 = (term68 _143642 _143649 s x)) = (_107385 = (term68 _143642 _143649 s x)).
Proof. exact (eq_refl (_107385 = (term68 _143642 _143649 s x))). Qed.
Lemma lem8097930 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term158 _143642 _143649 s x) = (term158 _143642 _143649 s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8097929 _143642 _143649 _107385 s x)). Qed.
Lemma lem8097931 {_143642 : Type'} : (@all _143642) = (@all _143642).
Proof. exact (eq_refl (@all _143642)). Qed.
Lemma lem8097932 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term159 _143642 _143649 s x) = (term159 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8097931 _143642) (@lem8097930 _143642 _143649 s x)). Qed.
Lemma lem8097935 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term126 _143642 _143649 s x) = (term126 _143642 _143649 s x).
Proof. exact (eq_refl (term126 _143642 _143649 s x)). Qed.
Lemma lem8097936 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term191 _143642 _143649 s x) = (term191 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8097935 _143642 _143649 s x) (@lem8097932 _143642 _143649 s x)). Qed.
Lemma lem8097937 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (y : _143642) : (r x y) = (r x y).
Proof. exact (eq_refl (r x y)). Qed.
Lemma lem8097938 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term165 _143642 _143649 r x) = (term165 _143642 _143649 r x).
Proof. exact (fun_ext (fun y : _143642 => @lem8097937 _143642 _143649 r x y)). Qed.
Lemma lem8097939 {_143642 : Type'} : (@ex _143642) = (@ex _143642).
Proof. exact (eq_refl (@ex _143642)). Qed.
Lemma lem8097940 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term106 _143642 _143649 r x) = (term106 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8097939 _143642) (@lem8097938 _143642 _143649 r x)). Qed.
Lemma lem8097941 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8097942 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term166 _143642 _143649 r x) = (term166 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8097941) (@lem8097940 _143642 _143649 r x)). Qed.
Lemma lem8097943 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term199 _143642 _143649 r s x) = (term199 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8097942 _143642 _143649 r x) (@lem8097936 _143642 _143649 s x)). Qed.
Lemma lem8097948 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term115 _143642 _143649 r x) = (term115 _143642 _143649 r x).
Proof. exact (eq_refl (term115 _143642 _143649 r x)). Qed.
Lemma lem8097949 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term207 _143642 _143649 r s x) = (term207 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8097948 _143642 _143649 r x) (@lem8097943 _143642 _143649 r s x)). Qed.
Lemma lem8097950 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8097951 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term208 _143642 _143649 r s x) = (term208 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8097950) (@lem8097949 _143642 _143649 r s x)). Qed.
Lemma lem8097952 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term205 _143642 _143649 r s x) = (term205 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8097951 _143642 _143649 r s x) (@lem8097928 _143642 _143649 r s x)). Qed.
Lemma lem8097953 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term209 _143642 _143649 r s x) = (term209 _143642 _143649 r s x).
Proof. exact (eq_refl (term209 _143642 _143649 r s x)). Qed.
Lemma lem8097954 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : ((term198 _143642 _143649 r s x) = (term205 _143642 _143649 r s x)) = ((term198 _143642 _143649 r s x) = (term205 _143642 _143649 r s x)).
Proof. exact (MK_COMB (@lem8097953 _143642 _143649 r s x) (@lem8097952 _143642 _143649 r s x)). Qed.
Lemma lem8097955 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term198 _143642 _143649 r s x) = (term205 _143642 _143649 r s x).
Proof. exact (EQ_MP (@lem8097954 _143642 _143649 r s x) (@lem8097909 _143642 _143649 r s x)). Qed.
Lemma lem8097956 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term210 _143642 _143649 r s x) = (term210 _143642 _143649 r s x).
Proof. exact (eq_refl (term210 _143642 _143649 r s x)). Qed.
Lemma lem8097957 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : ((term185 _143642 _143649 r s x) = (term198 _143642 _143649 r s x)) = ((term185 _143642 _143649 r s x) = (term205 _143642 _143649 r s x)).
Proof. exact (MK_COMB (@lem8097956 _143642 _143649 r s x) (@lem8097955 _143642 _143649 r s x)). Qed.
Lemma lem8097958 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term185 _143642 _143649 r s x) = (term205 _143642 _143649 r s x).
Proof. exact (EQ_MP (@lem8097957 _143642 _143649 r s x) (@lem8097654 _143642 _143649 r s x)). Qed.
Lemma lem8097959 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term211 _143642 _143649 r s x) = (term211 _143642 _143649 r s x).
Proof. exact (eq_refl (term211 _143642 _143649 r s x)). Qed.
Lemma lem8097960 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : ((term81 _143642 _143649 r s x) = (term185 _143642 _143649 r s x)) = ((term81 _143642 _143649 r s x) = (term205 _143642 _143649 r s x)).
Proof. exact (MK_COMB (@lem8097959 _143642 _143649 r s x) (@lem8097958 _143642 _143649 r s x)). Qed.
Lemma lem8097961 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term81 _143642 _143649 r s x) = (term205 _143642 _143649 r s x).
Proof. exact (EQ_MP (@lem8097960 _143642 _143649 r s x) (@lem8097389 _143642 _143649 r s x)). Qed.
Lemma lem8097962 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term82 _143642 _143649 s x) = (term212 _143642 _143649 s x).
Proof. exact (fun_ext (fun r : type1470 _143642 _143649 => @lem8097961 _143642 _143649 r s x)). Qed.
Lemma lem8097963 {_143642 _143649 : Type'} : (@all (_143649 -> _143642 -> Prop)) = (@all (_143649 -> _143642 -> Prop)).
Proof. exact (eq_refl (@all (_143649 -> _143642 -> Prop))). Qed.
Lemma lem8097964 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term83 _143642 _143649 s x) = (term213 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8097963 _143642 _143649) (@lem8097962 _143642 _143649 s x)). Qed.
Lemma lem8097969 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term115 _143642 _143649 s x) = (term115 _143642 _143649 s x).
Proof. exact (eq_refl (term115 _143642 _143649 s x)). Qed.
Lemma lem8097970 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term214 _143642 _143649 s x) = (term215 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8097969 _143642 _143649 s x) (@lem8097964 _143642 _143649 s x)). Qed.
Lemma lem8097971 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8097972 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term216 _143642 _143649 s x) = (term217 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8097971) (@lem8097970 _143642 _143649 s x)). Qed.
Lemma lem8097973 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term88 _143642 _143649 s x) = (term218 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8097972 _143642 _143649 s x) (@lem8097288 _143642 _143649 s x)). Qed.
Lemma lem8097974 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term219 _143642 _143649 s x) = (term219 _143642 _143649 s x).
Proof. exact (eq_refl (term219 _143642 _143649 s x)). Qed.
Lemma lem8097975 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : ((term57 _143642 _143649 s x) = (term88 _143642 _143649 s x)) = ((term57 _143642 _143649 s x) = (term218 _143642 _143649 s x)).
Proof. exact (MK_COMB (@lem8097974 _143642 _143649 s x) (@lem8097973 _143642 _143649 s x)). Qed.
Lemma lem8097976 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term57 _143642 _143649 s x) = (term218 _143642 _143649 s x).
Proof. exact (EQ_MP (@lem8097975 _143642 _143649 s x) (@lem8096604 _143642 _143649 s x)). Qed.
Lemma lem8097977 {_143642 _143649 : Type'} (x : _143649) : (term59 _143642 _143649 x) = (term220 _143642 _143649 x).
Proof. exact (fun_ext (fun s : type1470 _143642 _143649 => @lem8097976 _143642 _143649 s x)). Qed.
Lemma lem8097978 {_143642 _143649 : Type'} : (@all (_143649 -> _143642 -> Prop)) = (@all (_143649 -> _143642 -> Prop)).
Proof. exact (eq_refl (@all (_143649 -> _143642 -> Prop))). Qed.
Lemma lem8097979 {_143642 _143649 : Type'} (x : _143649) : (term61 _143642 _143649 x) = (term221 _143642 _143649 x).
Proof. exact (MK_COMB (@lem8097978 _143642 _143649) (@lem8097977 _143642 _143649 x)). Qed.
Lemma lem8097980 {_143642 _143649 : Type'} : (term63 _143642 _143649) = (term222 _143642 _143649).
Proof. exact (fun_ext (fun x : _143649 => @lem8097979 _143642 _143649 x)). Qed.
Lemma lem8097981 {_143649 : Type'} : (@all _143649) = (@all _143649).
Proof. exact (eq_refl (@all _143649)). Qed.
Lemma lem8097982 {_143642 _143649 : Type'} : (term65 _143642 _143649) = (term223 _143642 _143649).
Proof. exact (MK_COMB (@lem8097981 _143649) (@lem8097980 _143642 _143649)). Qed.
Lemma lem8098091 {_143642 _143649 : Type'} : (term64 _143642 _143649) = (term223 _143642 _143649).
Proof. exact (TRANS (@lem8096491 _143642 _143649) (@lem8097982 _143642 _143649)). Qed.
Lemma lem8098092 {_143642 _143649 : Type'} : (term223 _143642 _143649) = (term64 _143642 _143649).
Proof. exact (SYM (@lem8098091 _143642 _143649)). Qed.
Lemma lem8098094 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8098095 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term218 _143642 _143649 s x) = (term224 _143642 _143649 s x).
Proof. exact (@lem8098094 (term218 _143642 _143649 s x)). Qed.
Lemma lem8098096 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term224 _143642 _143649 s x) = (term218 _143642 _143649 s x).
Proof. exact (SYM (@lem8098095 _143642 _143649 s x)). Qed.
Lemma lem8098097 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) (h1 : term225 _143642 _143649 s x) : term225 _143642 _143649 s x.
Proof. exact (h1). Qed.
Lemma lem8098100 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term226 _143642 _143649 s x) = (term66 _143642 _143649 s x).
Proof. exact (@lem16933 (term66 _143642 _143649 s x)). Qed.
Lemma lem8098103 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term226 _143642 _143649 r x) = (term66 _143642 _143649 r x).
Proof. exact (@lem16933 (term66 _143642 _143649 r x)). Qed.
Lemma lem8098105 {_143642 : Type'} (P : _143642 -> Prop) : (term227 _143642 P) = (term228 _143642 P).
Proof. exact (@lem18394 _143642 P). Qed.
Lemma lem8098106 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term153 _143642 _143649 r x) = (term229 _143642 _143649 r x).
Proof. exact (@lem8098105 _143642 (term165 _143642 _143649 r x)). Qed.
Lemma lem8098107 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (y : _143642) : (term230 _143642 _143649 r x y) = (r x y).
Proof. exact (eq_refl (term230 _143642 _143649 r x y)). Qed.
Lemma lem8098108 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8098110 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (y : _143642) : (term231 _143642 _143649 r x y) = (term232 _143642 _143649 r x y).
Proof. exact (MK_COMB (@lem8098108) (@lem8098107 _143642 _143649 r x y)). Qed.
Lemma lem8098111 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term233 _143642 _143649 r x) = (term234 _143642 _143649 r x).
Proof. exact (fun_ext (fun y : _143642 => @lem8098110 _143642 _143649 r x y)). Qed.
Lemma lem8098112 {_143642 : Type'} : (@all _143642) = (@all _143642).
Proof. exact (eq_refl (@all _143642)). Qed.
Lemma lem8098113 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term229 _143642 _143649 r x) = (term235 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8098112 _143642) (@lem8098111 _143642 _143649 r x)). Qed.
Lemma lem8098114 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term153 _143642 _143649 r x) = (term235 _143642 _143649 r x).
Proof. exact (TRANS (@lem8098106 _143642 _143649 r x) (@lem8098113 _143642 _143649 r x)). Qed.
Lemma lem8098117 {_143642 : Type'} (P : _143642 -> Prop) : (term236 _143642 P) = (term237 _143642 P).
Proof. exact (@lem18392 _143642 P). Qed.
Lemma lem8098118 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term238 _143642 _143649 s x) = (term239 _143642 _143649 s x).
Proof. exact (@lem8098117 _143642 (term158 _143642 _143649 s x)). Qed.
Lemma lem8098119 {_143642 _143649 : Type'} (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term240 _143642 _143649 s x _107385) = (_107385 = (term68 _143642 _143649 s x)).
Proof. exact (eq_refl (term240 _143642 _143649 s x _107385)). Qed.
Lemma lem8098120 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8098122 {_143642 _143649 : Type'} (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term241 _143642 _143649 s x _107385) = (term242 _143642 _143649 _107385 s x).
Proof. exact (MK_COMB (@lem8098120) (@lem8098119 _143642 _143649 _107385 s x)). Qed.
Lemma lem8098123 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term243 _143642 _143649 s x) = (term244 _143642 _143649 s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8098122 _143642 _143649 _107385 s x)). Qed.
Lemma lem8098124 {_143642 : Type'} : (@ex _143642) = (@ex _143642).
Proof. exact (eq_refl (@ex _143642)). Qed.
Lemma lem8098125 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term239 _143642 _143649 s x) = (term245 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098124 _143642) (@lem8098123 _143642 _143649 s x)). Qed.
Lemma lem8098126 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term238 _143642 _143649 s x) = (term245 _143642 _143649 s x).
Proof. exact (TRANS (@lem8098118 _143642 _143649 s x) (@lem8098125 _143642 _143649 s x)). Qed.
Lemma lem8098128 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term246 _143642 _143649 s x) = (term246 _143642 _143649 s x).
Proof. exact (eq_refl (term246 _143642 _143649 s x)). Qed.
Lemma lem8098129 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term247 _143642 _143649 s x) = (term248 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098128 _143642 _143649 s x) (@lem8098126 _143642 _143649 s x)). Qed.
Lemma lem8098130 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term249 _143642 _143649 s x) = (term247 _143642 _143649 s x).
Proof. exact (@lem17160 (term66 _143642 _143649 s x) (term159 _143642 _143649 s x)). Qed.
Lemma lem8098131 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term249 _143642 _143649 s x) = (term248 _143642 _143649 s x).
Proof. exact (TRANS (@lem8098130 _143642 _143649 s x) (@lem8098129 _143642 _143649 s x)). Qed.
Lemma lem8098132 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8098133 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term250 _143642 _143649 r x) = (term251 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8098132) (@lem8098114 _143642 _143649 r x)). Qed.
Lemma lem8098134 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term252 _143642 _143649 r s x) = (term253 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098133 _143642 _143649 r x) (@lem8098131 _143642 _143649 s x)). Qed.
Lemma lem8098135 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term254 _143642 _143649 r s x) = (term252 _143642 _143649 r s x).
Proof. exact (@lem17160 (term106 _143642 _143649 r x) (term191 _143642 _143649 s x)). Qed.
Lemma lem8098136 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term254 _143642 _143649 r s x) = (term253 _143642 _143649 r s x).
Proof. exact (TRANS (@lem8098135 _143642 _143649 r s x) (@lem8098134 _143642 _143649 r s x)). Qed.
Lemma lem8098137 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8098138 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term255 _143642 _143649 r x) = (term256 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8098137) (@lem8098103 _143642 _143649 r x)). Qed.
Lemma lem8098139 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term257 _143642 _143649 r s x) = (term258 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098138 _143642 _143649 r x) (@lem8098136 _143642 _143649 r s x)). Qed.
Lemma lem8098140 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term259 _143642 _143649 r s x) = (term257 _143642 _143649 r s x).
Proof. exact (@lem17160 (term113 _143642 _143649 r x) (term199 _143642 _143649 r s x)). Qed.
Lemma lem8098141 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term259 _143642 _143649 r s x) = (term258 _143642 _143649 r s x).
Proof. exact (TRANS (@lem8098140 _143642 _143649 r s x) (@lem8098139 _143642 _143649 r s x)). Qed.
Lemma lem8098144 {_143642 : Type'} (P : _143642 -> Prop) : (term227 _143642 P) = (term228 _143642 P).
Proof. exact (@lem18394 _143642 P). Qed.
Lemma lem8098145 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term153 _143642 _143649 r x) = (term229 _143642 _143649 r x).
Proof. exact (@lem8098144 _143642 (term165 _143642 _143649 r x)). Qed.
Lemma lem8098146 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (y : _143642) : (term230 _143642 _143649 r x y) = (r x y).
Proof. exact (eq_refl (term230 _143642 _143649 r x y)). Qed.
Lemma lem8098147 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8098149 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (y : _143642) : (term231 _143642 _143649 r x y) = (term232 _143642 _143649 r x y).
Proof. exact (MK_COMB (@lem8098147) (@lem8098146 _143642 _143649 r x y)). Qed.
Lemma lem8098150 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term233 _143642 _143649 r x) = (term234 _143642 _143649 r x).
Proof. exact (fun_ext (fun y : _143642 => @lem8098149 _143642 _143649 r x y)). Qed.
Lemma lem8098151 {_143642 : Type'} : (@all _143642) = (@all _143642).
Proof. exact (eq_refl (@all _143642)). Qed.
Lemma lem8098152 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term229 _143642 _143649 r x) = (term235 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8098151 _143642) (@lem8098150 _143642 _143649 r x)). Qed.
Lemma lem8098153 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term153 _143642 _143649 r x) = (term235 _143642 _143649 r x).
Proof. exact (TRANS (@lem8098145 _143642 _143649 r x) (@lem8098152 _143642 _143649 r x)). Qed.
Lemma lem8098156 {_143642 : Type'} (P : _143642 -> Prop) : (term236 _143642 P) = (term237 _143642 P).
Proof. exact (@lem18392 _143642 P). Qed.
Lemma lem8098157 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term238 _143642 _143649 s x) = (term239 _143642 _143649 s x).
Proof. exact (@lem8098156 _143642 (term158 _143642 _143649 s x)). Qed.
Lemma lem8098158 {_143642 _143649 : Type'} (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term240 _143642 _143649 s x _107385) = (_107385 = (term68 _143642 _143649 s x)).
Proof. exact (eq_refl (term240 _143642 _143649 s x _107385)). Qed.
Lemma lem8098159 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8098161 {_143642 _143649 : Type'} (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term241 _143642 _143649 s x _107385) = (term242 _143642 _143649 _107385 s x).
Proof. exact (MK_COMB (@lem8098159) (@lem8098158 _143642 _143649 _107385 s x)). Qed.
Lemma lem8098162 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term243 _143642 _143649 s x) = (term244 _143642 _143649 s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8098161 _143642 _143649 _107385 s x)). Qed.
Lemma lem8098163 {_143642 : Type'} : (@ex _143642) = (@ex _143642).
Proof. exact (eq_refl (@ex _143642)). Qed.
Lemma lem8098164 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term239 _143642 _143649 s x) = (term245 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098163 _143642) (@lem8098162 _143642 _143649 s x)). Qed.
Lemma lem8098165 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term238 _143642 _143649 s x) = (term245 _143642 _143649 s x).
Proof. exact (TRANS (@lem8098157 _143642 _143649 s x) (@lem8098164 _143642 _143649 s x)). Qed.
Lemma lem8098167 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term246 _143642 _143649 s x) = (term246 _143642 _143649 s x).
Proof. exact (eq_refl (term246 _143642 _143649 s x)). Qed.
Lemma lem8098168 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term247 _143642 _143649 s x) = (term248 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098167 _143642 _143649 s x) (@lem8098165 _143642 _143649 s x)). Qed.
Lemma lem8098169 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term249 _143642 _143649 s x) = (term247 _143642 _143649 s x).
Proof. exact (@lem17160 (term66 _143642 _143649 s x) (term159 _143642 _143649 s x)). Qed.
Lemma lem8098170 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term249 _143642 _143649 s x) = (term248 _143642 _143649 s x).
Proof. exact (TRANS (@lem8098169 _143642 _143649 s x) (@lem8098168 _143642 _143649 s x)). Qed.
Lemma lem8098171 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8098172 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term250 _143642 _143649 r x) = (term251 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8098171) (@lem8098153 _143642 _143649 r x)). Qed.
Lemma lem8098173 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term252 _143642 _143649 r s x) = (term253 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098172 _143642 _143649 r x) (@lem8098170 _143642 _143649 s x)). Qed.
Lemma lem8098174 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term254 _143642 _143649 r s x) = (term252 _143642 _143649 r s x).
Proof. exact (@lem17160 (term106 _143642 _143649 r x) (term191 _143642 _143649 s x)). Qed.
Lemma lem8098175 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term254 _143642 _143649 r s x) = (term253 _143642 _143649 r s x).
Proof. exact (TRANS (@lem8098174 _143642 _143649 r s x) (@lem8098173 _143642 _143649 r s x)). Qed.
Lemma lem8098177 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term246 _143642 _143649 r x) = (term246 _143642 _143649 r x).
Proof. exact (eq_refl (term246 _143642 _143649 r x)). Qed.
Lemma lem8098178 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term260 _143642 _143649 r s x) = (term261 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098177 _143642 _143649 r x) (@lem8098175 _143642 _143649 r s x)). Qed.
Lemma lem8098179 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term262 _143642 _143649 r s x) = (term260 _143642 _143649 r s x).
Proof. exact (@lem17160 (term66 _143642 _143649 r x) (term199 _143642 _143649 r s x)). Qed.
Lemma lem8098180 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term262 _143642 _143649 r s x) = (term261 _143642 _143649 r s x).
Proof. exact (TRANS (@lem8098179 _143642 _143649 r s x) (@lem8098178 _143642 _143649 r s x)). Qed.
Lemma lem8098181 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8098182 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term263 _143642 _143649 r s x) = (term264 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098181) (@lem8098141 _143642 _143649 r s x)). Qed.
Lemma lem8098183 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term265 _143642 _143649 r s x) = (term266 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098182 _143642 _143649 r s x) (@lem8098180 _143642 _143649 r s x)). Qed.
Lemma lem8098184 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term267 _143642 _143649 r s x) = (term265 _143642 _143649 r s x).
Proof. exact (@lem17045 (term207 _143642 _143649 r s x) (term206 _143642 _143649 r s x)). Qed.
Lemma lem8098185 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term267 _143642 _143649 r s x) = (term266 _143642 _143649 r s x).
Proof. exact (TRANS (@lem8098184 _143642 _143649 r s x) (@lem8098183 _143642 _143649 r s x)). Qed.
Lemma lem8098186 {_143642 _143649 : Type'} (P : type745 _143642 _143649) : (term268 _143642 _143649 P) = (term269 _143642 _143649 P).
Proof. exact (@lem18392 (type1470 _143642 _143649) P). Qed.
Lemma lem8098187 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term270 _143642 _143649 s x) = (term271 _143642 _143649 s x).
Proof. exact (@lem8098186 _143642 _143649 (term212 _143642 _143649 s x)). Qed.
Lemma lem8098188 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term272 _143642 _143649 s x r) = (term205 _143642 _143649 r s x).
Proof. exact (eq_refl (term272 _143642 _143649 s x r)). Qed.
Lemma lem8098189 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8098190 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term273 _143642 _143649 s x r) = (term267 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098189) (@lem8098188 _143642 _143649 r s x)). Qed.
Lemma lem8098191 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term273 _143642 _143649 s x r) = (term266 _143642 _143649 r s x).
Proof. exact (TRANS (@lem8098190 _143642 _143649 r s x) (@lem8098185 _143642 _143649 r s x)). Qed.
Lemma lem8098192 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term274 _143642 _143649 s x) = (term275 _143642 _143649 s x).
Proof. exact (fun_ext (fun r : type1470 _143642 _143649 => @lem8098191 _143642 _143649 r s x)). Qed.
Lemma lem8098193 {_143642 _143649 : Type'} : (@ex (_143649 -> _143642 -> Prop)) = (@ex (_143649 -> _143642 -> Prop)).
Proof. exact (eq_refl (@ex (_143649 -> _143642 -> Prop))). Qed.
Lemma lem8098194 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term271 _143642 _143649 s x) = (term276 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098193 _143642 _143649) (@lem8098192 _143642 _143649 s x)). Qed.
Lemma lem8098195 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term270 _143642 _143649 s x) = (term276 _143642 _143649 s x).
Proof. exact (TRANS (@lem8098187 _143642 _143649 s x) (@lem8098194 _143642 _143649 s x)). Qed.
Lemma lem8098196 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8098197 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term255 _143642 _143649 s x) = (term256 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098196) (@lem8098100 _143642 _143649 s x)). Qed.
Lemma lem8098198 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term277 _143642 _143649 s x) = (term278 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098197 _143642 _143649 s x) (@lem8098195 _143642 _143649 s x)). Qed.
Lemma lem8098199 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term279 _143642 _143649 s x) = (term277 _143642 _143649 s x).
Proof. exact (@lem17160 (term113 _143642 _143649 s x) (term213 _143642 _143649 s x)). Qed.
Lemma lem8098200 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term279 _143642 _143649 s x) = (term278 _143642 _143649 s x).
Proof. exact (TRANS (@lem8098199 _143642 _143649 s x) (@lem8098198 _143642 _143649 s x)). Qed.
Lemma lem8098204 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term226 _143642 _143649 r x) = (term66 _143642 _143649 r x).
Proof. exact (@lem16933 (term66 _143642 _143649 r x)). Qed.
Lemma lem8098206 {_143642 : Type'} (P : _143642 -> Prop) : (term227 _143642 P) = (term228 _143642 P).
Proof. exact (@lem18394 _143642 P). Qed.
Lemma lem8098207 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term153 _143642 _143649 r x) = (term229 _143642 _143649 r x).
Proof. exact (@lem8098206 _143642 (term165 _143642 _143649 r x)). Qed.
Lemma lem8098208 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (y : _143642) : (term230 _143642 _143649 r x y) = (r x y).
Proof. exact (eq_refl (term230 _143642 _143649 r x y)). Qed.
Lemma lem8098209 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8098211 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (y : _143642) : (term231 _143642 _143649 r x y) = (term232 _143642 _143649 r x y).
Proof. exact (MK_COMB (@lem8098209) (@lem8098208 _143642 _143649 r x y)). Qed.
Lemma lem8098212 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term233 _143642 _143649 r x) = (term234 _143642 _143649 r x).
Proof. exact (fun_ext (fun y : _143642 => @lem8098211 _143642 _143649 r x y)). Qed.
Lemma lem8098213 {_143642 : Type'} : (@all _143642) = (@all _143642).
Proof. exact (eq_refl (@all _143642)). Qed.
Lemma lem8098214 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term229 _143642 _143649 r x) = (term235 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8098213 _143642) (@lem8098212 _143642 _143649 r x)). Qed.
Lemma lem8098215 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term153 _143642 _143649 r x) = (term235 _143642 _143649 r x).
Proof. exact (TRANS (@lem8098207 _143642 _143649 r x) (@lem8098214 _143642 _143649 r x)). Qed.
Lemma lem8098218 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term226 _143642 _143649 s x) = (term66 _143642 _143649 s x).
Proof. exact (@lem16933 (term66 _143642 _143649 s x)). Qed.
Lemma lem8098220 {_143642 : Type'} (P : _143642 -> Prop) : (term236 _143642 P) = (term237 _143642 P).
Proof. exact (@lem18392 _143642 P). Qed.
Lemma lem8098221 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term280 _143642 _143649 s x) = (term281 _143642 _143649 s x).
Proof. exact (@lem8098220 _143642 (term119 _143642 _143649 s x)). Qed.
Lemma lem8098222 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term282 _143642 _143649 s x _107385) = ((term68 _143642 _143649 s x) = _107385).
Proof. exact (eq_refl (term282 _143642 _143649 s x _107385)). Qed.
Lemma lem8098223 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8098225 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term283 _143642 _143649 s x _107385) = (term284 _143642 _143649 s x _107385).
Proof. exact (MK_COMB (@lem8098223) (@lem8098222 _143642 _143649 s x _107385)). Qed.
Lemma lem8098226 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term285 _143642 _143649 s x) = (term286 _143642 _143649 s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8098225 _143642 _143649 s x _107385)). Qed.
Lemma lem8098227 {_143642 : Type'} : (@ex _143642) = (@ex _143642).
Proof. exact (eq_refl (@ex _143642)). Qed.
Lemma lem8098228 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term281 _143642 _143649 s x) = (term287 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098227 _143642) (@lem8098226 _143642 _143649 s x)). Qed.
Lemma lem8098229 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term280 _143642 _143649 s x) = (term287 _143642 _143649 s x).
Proof. exact (TRANS (@lem8098221 _143642 _143649 s x) (@lem8098228 _143642 _143649 s x)). Qed.
Lemma lem8098230 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8098231 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term255 _143642 _143649 s x) = (term256 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098230) (@lem8098218 _143642 _143649 s x)). Qed.
Lemma lem8098232 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term288 _143642 _143649 s x) = (term289 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098231 _143642 _143649 s x) (@lem8098229 _143642 _143649 s x)). Qed.
Lemma lem8098233 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term290 _143642 _143649 s x) = (term288 _143642 _143649 s x).
Proof. exact (@lem17160 (term113 _143642 _143649 s x) (term120 _143642 _143649 s x)). Qed.
Lemma lem8098234 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term290 _143642 _143649 s x) = (term289 _143642 _143649 s x).
Proof. exact (TRANS (@lem8098233 _143642 _143649 s x) (@lem8098232 _143642 _143649 s x)). Qed.
Lemma lem8098235 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8098236 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term250 _143642 _143649 r x) = (term251 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8098235) (@lem8098215 _143642 _143649 r x)). Qed.
Lemma lem8098237 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term291 _143642 _143649 r s x) = (term292 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098236 _143642 _143649 r x) (@lem8098234 _143642 _143649 s x)). Qed.
Lemma lem8098238 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term293 _143642 _143649 r s x) = (term291 _143642 _143649 r s x).
Proof. exact (@lem17160 (term106 _143642 _143649 r x) (term122 _143642 _143649 s x)). Qed.
Lemma lem8098239 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term293 _143642 _143649 r s x) = (term292 _143642 _143649 r s x).
Proof. exact (TRANS (@lem8098238 _143642 _143649 r s x) (@lem8098237 _143642 _143649 r s x)). Qed.
Lemma lem8098240 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8098241 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term255 _143642 _143649 r x) = (term256 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8098240) (@lem8098204 _143642 _143649 r x)). Qed.
Lemma lem8098242 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term294 _143642 _143649 r s x) = (term295 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098241 _143642 _143649 r x) (@lem8098239 _143642 _143649 r s x)). Qed.
Lemma lem8098243 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term296 _143642 _143649 r s x) = (term294 _143642 _143649 r s x).
Proof. exact (@lem17160 (term113 _143642 _143649 r x) (term155 _143642 _143649 r s x)). Qed.
Lemma lem8098244 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term296 _143642 _143649 r s x) = (term295 _143642 _143649 r s x).
Proof. exact (TRANS (@lem8098243 _143642 _143649 r s x) (@lem8098242 _143642 _143649 r s x)). Qed.
Lemma lem8098247 {_143642 : Type'} (P : _143642 -> Prop) : (term227 _143642 P) = (term228 _143642 P).
Proof. exact (@lem18394 _143642 P). Qed.
Lemma lem8098248 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term153 _143642 _143649 r x) = (term229 _143642 _143649 r x).
Proof. exact (@lem8098247 _143642 (term165 _143642 _143649 r x)). Qed.
Lemma lem8098249 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (y : _143642) : (term230 _143642 _143649 r x y) = (r x y).
Proof. exact (eq_refl (term230 _143642 _143649 r x y)). Qed.
Lemma lem8098250 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8098252 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (y : _143642) : (term231 _143642 _143649 r x y) = (term232 _143642 _143649 r x y).
Proof. exact (MK_COMB (@lem8098250) (@lem8098249 _143642 _143649 r x y)). Qed.
Lemma lem8098253 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term233 _143642 _143649 r x) = (term234 _143642 _143649 r x).
Proof. exact (fun_ext (fun y : _143642 => @lem8098252 _143642 _143649 r x y)). Qed.
Lemma lem8098254 {_143642 : Type'} : (@all _143642) = (@all _143642).
Proof. exact (eq_refl (@all _143642)). Qed.
Lemma lem8098255 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term229 _143642 _143649 r x) = (term235 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8098254 _143642) (@lem8098253 _143642 _143649 r x)). Qed.
Lemma lem8098256 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term153 _143642 _143649 r x) = (term235 _143642 _143649 r x).
Proof. exact (TRANS (@lem8098248 _143642 _143649 r x) (@lem8098255 _143642 _143649 r x)). Qed.
Lemma lem8098259 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term226 _143642 _143649 s x) = (term66 _143642 _143649 s x).
Proof. exact (@lem16933 (term66 _143642 _143649 s x)). Qed.
Lemma lem8098261 {_143642 : Type'} (P : _143642 -> Prop) : (term236 _143642 P) = (term237 _143642 P).
Proof. exact (@lem18392 _143642 P). Qed.
Lemma lem8098262 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term280 _143642 _143649 s x) = (term281 _143642 _143649 s x).
Proof. exact (@lem8098261 _143642 (term119 _143642 _143649 s x)). Qed.
Lemma lem8098263 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term282 _143642 _143649 s x _107385) = ((term68 _143642 _143649 s x) = _107385).
Proof. exact (eq_refl (term282 _143642 _143649 s x _107385)). Qed.
Lemma lem8098264 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8098266 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term283 _143642 _143649 s x _107385) = (term284 _143642 _143649 s x _107385).
Proof. exact (MK_COMB (@lem8098264) (@lem8098263 _143642 _143649 s x _107385)). Qed.
Lemma lem8098267 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term285 _143642 _143649 s x) = (term286 _143642 _143649 s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8098266 _143642 _143649 s x _107385)). Qed.
Lemma lem8098268 {_143642 : Type'} : (@ex _143642) = (@ex _143642).
Proof. exact (eq_refl (@ex _143642)). Qed.
Lemma lem8098269 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term281 _143642 _143649 s x) = (term287 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098268 _143642) (@lem8098267 _143642 _143649 s x)). Qed.
Lemma lem8098270 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term280 _143642 _143649 s x) = (term287 _143642 _143649 s x).
Proof. exact (TRANS (@lem8098262 _143642 _143649 s x) (@lem8098269 _143642 _143649 s x)). Qed.
Lemma lem8098271 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8098272 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term255 _143642 _143649 s x) = (term256 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098271) (@lem8098259 _143642 _143649 s x)). Qed.
Lemma lem8098273 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term288 _143642 _143649 s x) = (term289 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098272 _143642 _143649 s x) (@lem8098270 _143642 _143649 s x)). Qed.
Lemma lem8098274 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term290 _143642 _143649 s x) = (term288 _143642 _143649 s x).
Proof. exact (@lem17160 (term113 _143642 _143649 s x) (term120 _143642 _143649 s x)). Qed.
Lemma lem8098275 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term290 _143642 _143649 s x) = (term289 _143642 _143649 s x).
Proof. exact (TRANS (@lem8098274 _143642 _143649 s x) (@lem8098273 _143642 _143649 s x)). Qed.
Lemma lem8098276 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8098277 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term250 _143642 _143649 r x) = (term251 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8098276) (@lem8098256 _143642 _143649 r x)). Qed.
Lemma lem8098278 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term291 _143642 _143649 r s x) = (term292 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098277 _143642 _143649 r x) (@lem8098275 _143642 _143649 s x)). Qed.
Lemma lem8098279 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term293 _143642 _143649 r s x) = (term291 _143642 _143649 r s x).
Proof. exact (@lem17160 (term106 _143642 _143649 r x) (term122 _143642 _143649 s x)). Qed.
Lemma lem8098280 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term293 _143642 _143649 r s x) = (term292 _143642 _143649 r s x).
Proof. exact (TRANS (@lem8098279 _143642 _143649 r s x) (@lem8098278 _143642 _143649 r s x)). Qed.
Lemma lem8098282 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term246 _143642 _143649 r x) = (term246 _143642 _143649 r x).
Proof. exact (eq_refl (term246 _143642 _143649 r x)). Qed.
Lemma lem8098283 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term297 _143642 _143649 r s x) = (term298 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098282 _143642 _143649 r x) (@lem8098280 _143642 _143649 r s x)). Qed.
Lemma lem8098284 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term299 _143642 _143649 r s x) = (term297 _143642 _143649 r s x).
Proof. exact (@lem17160 (term66 _143642 _143649 r x) (term155 _143642 _143649 r s x)). Qed.
Lemma lem8098285 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term299 _143642 _143649 r s x) = (term298 _143642 _143649 r s x).
Proof. exact (TRANS (@lem8098284 _143642 _143649 r s x) (@lem8098283 _143642 _143649 r s x)). Qed.
Lemma lem8098286 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8098287 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term300 _143642 _143649 r s x) = (term301 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098286) (@lem8098244 _143642 _143649 r s x)). Qed.
Lemma lem8098288 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term302 _143642 _143649 r s x) = (term303 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098287 _143642 _143649 r s x) (@lem8098285 _143642 _143649 r s x)). Qed.
Lemma lem8098289 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term304 _143642 _143649 r s x) = (term302 _143642 _143649 r s x).
Proof. exact (@lem17045 (term168 _143642 _143649 r s x) (term167 _143642 _143649 r s x)). Qed.
Lemma lem8098290 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term304 _143642 _143649 r s x) = (term303 _143642 _143649 r s x).
Proof. exact (TRANS (@lem8098289 _143642 _143649 r s x) (@lem8098288 _143642 _143649 r s x)). Qed.
Lemma lem8098291 {_143642 _143649 : Type'} (P : type745 _143642 _143649) : (term268 _143642 _143649 P) = (term269 _143642 _143649 P).
Proof. exact (@lem18392 (type1470 _143642 _143649) P). Qed.
Lemma lem8098292 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term305 _143642 _143649 s x) = (term306 _143642 _143649 s x).
Proof. exact (@lem8098291 _143642 _143649 (term173 _143642 _143649 s x)). Qed.
Lemma lem8098293 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term307 _143642 _143649 s x r) = (term164 _143642 _143649 r s x).
Proof. exact (eq_refl (term307 _143642 _143649 s x r)). Qed.
Lemma lem8098294 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8098295 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term308 _143642 _143649 s x r) = (term304 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098294) (@lem8098293 _143642 _143649 r s x)). Qed.
Lemma lem8098296 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term308 _143642 _143649 s x r) = (term303 _143642 _143649 r s x).
Proof. exact (TRANS (@lem8098295 _143642 _143649 r s x) (@lem8098290 _143642 _143649 r s x)). Qed.
Lemma lem8098297 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term309 _143642 _143649 s x) = (term310 _143642 _143649 s x).
Proof. exact (fun_ext (fun r : type1470 _143642 _143649 => @lem8098296 _143642 _143649 r s x)). Qed.
Lemma lem8098298 {_143642 _143649 : Type'} : (@ex (_143649 -> _143642 -> Prop)) = (@ex (_143649 -> _143642 -> Prop)).
Proof. exact (eq_refl (@ex (_143649 -> _143642 -> Prop))). Qed.
Lemma lem8098299 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term306 _143642 _143649 s x) = (term311 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098298 _143642 _143649) (@lem8098297 _143642 _143649 s x)). Qed.
Lemma lem8098300 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term305 _143642 _143649 s x) = (term311 _143642 _143649 s x).
Proof. exact (TRANS (@lem8098292 _143642 _143649 s x) (@lem8098299 _143642 _143649 s x)). Qed.
Lemma lem8098302 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term246 _143642 _143649 s x) = (term246 _143642 _143649 s x).
Proof. exact (eq_refl (term246 _143642 _143649 s x)). Qed.
Lemma lem8098303 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term312 _143642 _143649 s x) = (term313 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098302 _143642 _143649 s x) (@lem8098300 _143642 _143649 s x)). Qed.
Lemma lem8098304 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term314 _143642 _143649 s x) = (term312 _143642 _143649 s x).
Proof. exact (@lem17160 (term66 _143642 _143649 s x) (term174 _143642 _143649 s x)). Qed.
Lemma lem8098305 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term314 _143642 _143649 s x) = (term313 _143642 _143649 s x).
Proof. exact (TRANS (@lem8098304 _143642 _143649 s x) (@lem8098303 _143642 _143649 s x)). Qed.
Lemma lem8098306 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8098307 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term315 _143642 _143649 s x) = (term316 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098306) (@lem8098200 _143642 _143649 s x)). Qed.
Lemma lem8098308 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term317 _143642 _143649 s x) = (term318 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098307 _143642 _143649 s x) (@lem8098305 _143642 _143649 s x)). Qed.
Lemma lem8098309 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term225 _143642 _143649 s x) = (term317 _143642 _143649 s x).
Proof. exact (@lem17045 (term215 _143642 _143649 s x) (term176 _143642 _143649 s x)). Qed.
Lemma lem8098310 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term225 _143642 _143649 s x) = (term318 _143642 _143649 s x).
Proof. exact (TRANS (@lem8098309 _143642 _143649 s x) (@lem8098308 _143642 _143649 s x)). Qed.
Lemma lem8098312 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term319 A P Q) = (term320 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem8098313 {_143642 _143649 : Type'} (P : type745 _143642 _143649) (Q : type745 _143642 _143649) : (term321 _143642 _143649 P Q) = (term322 _143642 _143649 P Q).
Proof. exact (@lem8098312 (type1470 _143642 _143649) P Q). Qed.
Lemma lem8098314 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term323 _143642 _143649 s x) = (term324 _143642 _143649 s x).
Proof. exact (@lem8098313 _143642 _143649 (term325 _143642 _143649 s x) (term326 _143642 _143649 s x)). Qed.
Lemma lem8098315 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term327 _143642 _143649 s x r) = (term258 _143642 _143649 r s x).
Proof. exact (eq_refl (term327 _143642 _143649 s x r)). Qed.
Lemma lem8098316 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8098317 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term328 _143642 _143649 s x r) = (term264 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098316) (@lem8098315 _143642 _143649 r s x)). Qed.
Lemma lem8098318 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term329 _143642 _143649 s x r) = (term261 _143642 _143649 r s x).
Proof. exact (eq_refl (term329 _143642 _143649 s x r)). Qed.
Lemma lem8098319 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term330 _143642 _143649 s x r) = (term266 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098317 _143642 _143649 r s x) (@lem8098318 _143642 _143649 r s x)). Qed.
Lemma lem8098320 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term331 _143642 _143649 s x) = (term275 _143642 _143649 s x).
Proof. exact (fun_ext (fun r : type1470 _143642 _143649 => @lem8098319 _143642 _143649 r s x)). Qed.
Lemma lem8098321 {_143642 _143649 : Type'} : (@ex (_143649 -> _143642 -> Prop)) = (@ex (_143649 -> _143642 -> Prop)).
Proof. exact (eq_refl (@ex (_143649 -> _143642 -> Prop))). Qed.
Lemma lem8098322 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term323 _143642 _143649 s x) = (term276 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098321 _143642 _143649) (@lem8098320 _143642 _143649 s x)). Qed.
Lemma lem8098323 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8098324 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term332 _143642 _143649 s x) = (term333 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098323) (@lem8098322 _143642 _143649 s x)). Qed.
Lemma lem8098325 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term327 _143642 _143649 s x r) = (term258 _143642 _143649 r s x).
Proof. exact (eq_refl (term327 _143642 _143649 s x r)). Qed.
Lemma lem8098326 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term334 _143642 _143649 s x) = (term325 _143642 _143649 s x).
Proof. exact (fun_ext (fun r : type1470 _143642 _143649 => @lem8098325 _143642 _143649 r s x)). Qed.
Lemma lem8098327 {_143642 _143649 : Type'} : (@ex (_143649 -> _143642 -> Prop)) = (@ex (_143649 -> _143642 -> Prop)).
Proof. exact (eq_refl (@ex (_143649 -> _143642 -> Prop))). Qed.
Lemma lem8098328 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term335 _143642 _143649 s x) = (term336 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098327 _143642 _143649) (@lem8098326 _143642 _143649 s x)). Qed.
Lemma lem8098329 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8098330 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term337 _143642 _143649 s x) = (term338 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098329) (@lem8098328 _143642 _143649 s x)). Qed.
Lemma lem8098331 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term329 _143642 _143649 s x r) = (term261 _143642 _143649 r s x).
Proof. exact (eq_refl (term329 _143642 _143649 s x r)). Qed.
Lemma lem8098332 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term339 _143642 _143649 s x) = (term326 _143642 _143649 s x).
Proof. exact (fun_ext (fun r : type1470 _143642 _143649 => @lem8098331 _143642 _143649 r s x)). Qed.
Lemma lem8098333 {_143642 _143649 : Type'} : (@ex (_143649 -> _143642 -> Prop)) = (@ex (_143649 -> _143642 -> Prop)).
Proof. exact (eq_refl (@ex (_143649 -> _143642 -> Prop))). Qed.
Lemma lem8098334 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term340 _143642 _143649 s x) = (term341 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098333 _143642 _143649) (@lem8098332 _143642 _143649 s x)). Qed.
Lemma lem8098335 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term324 _143642 _143649 s x) = (term342 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098330 _143642 _143649 s x) (@lem8098334 _143642 _143649 s x)). Qed.
Lemma lem8098336 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : ((term323 _143642 _143649 s x) = (term324 _143642 _143649 s x)) = ((term276 _143642 _143649 s x) = (term342 _143642 _143649 s x)).
Proof. exact (MK_COMB (@lem8098324 _143642 _143649 s x) (@lem8098335 _143642 _143649 s x)). Qed.
Lemma lem8098337 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term276 _143642 _143649 s x) = (term342 _143642 _143649 s x).
Proof. exact (EQ_MP (@lem8098336 _143642 _143649 s x) (@lem8098314 _143642 _143649 s x)). Qed.
Lemma lem8098450 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term256 _143642 _143649 s x) = (term256 _143642 _143649 s x).
Proof. exact (eq_refl (term256 _143642 _143649 s x)). Qed.
Lemma lem8098451 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term278 _143642 _143649 s x) = (term343 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098450 _143642 _143649 s x) (@lem8098337 _143642 _143649 s x)). Qed.
Lemma lem8098452 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8098453 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term316 _143642 _143649 s x) = (term344 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098452) (@lem8098451 _143642 _143649 s x)). Qed.
Lemma lem8098455 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term319 A P Q) = (term320 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem8098456 {_143642 _143649 : Type'} (P : type745 _143642 _143649) (Q : type745 _143642 _143649) : (term321 _143642 _143649 P Q) = (term322 _143642 _143649 P Q).
Proof. exact (@lem8098455 (type1470 _143642 _143649) P Q). Qed.
Lemma lem8098457 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term345 _143642 _143649 s x) = (term346 _143642 _143649 s x).
Proof. exact (@lem8098456 _143642 _143649 (term347 _143642 _143649 s x) (term348 _143642 _143649 s x)). Qed.
Lemma lem8098458 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term349 _143642 _143649 s x r) = (term295 _143642 _143649 r s x).
Proof. exact (eq_refl (term349 _143642 _143649 s x r)). Qed.
Lemma lem8098459 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8098460 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term350 _143642 _143649 s x r) = (term301 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098459) (@lem8098458 _143642 _143649 r s x)). Qed.
Lemma lem8098461 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term351 _143642 _143649 s x r) = (term298 _143642 _143649 r s x).
Proof. exact (eq_refl (term351 _143642 _143649 s x r)). Qed.
Lemma lem8098462 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term352 _143642 _143649 s x r) = (term303 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098460 _143642 _143649 r s x) (@lem8098461 _143642 _143649 r s x)). Qed.
Lemma lem8098463 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term353 _143642 _143649 s x) = (term310 _143642 _143649 s x).
Proof. exact (fun_ext (fun r : type1470 _143642 _143649 => @lem8098462 _143642 _143649 r s x)). Qed.
Lemma lem8098464 {_143642 _143649 : Type'} : (@ex (_143649 -> _143642 -> Prop)) = (@ex (_143649 -> _143642 -> Prop)).
Proof. exact (eq_refl (@ex (_143649 -> _143642 -> Prop))). Qed.
Lemma lem8098465 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term345 _143642 _143649 s x) = (term311 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098464 _143642 _143649) (@lem8098463 _143642 _143649 s x)). Qed.
Lemma lem8098466 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8098467 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term354 _143642 _143649 s x) = (term355 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098466) (@lem8098465 _143642 _143649 s x)). Qed.
Lemma lem8098468 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term349 _143642 _143649 s x r) = (term295 _143642 _143649 r s x).
Proof. exact (eq_refl (term349 _143642 _143649 s x r)). Qed.
Lemma lem8098469 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term356 _143642 _143649 s x) = (term347 _143642 _143649 s x).
Proof. exact (fun_ext (fun r : type1470 _143642 _143649 => @lem8098468 _143642 _143649 r s x)). Qed.
Lemma lem8098470 {_143642 _143649 : Type'} : (@ex (_143649 -> _143642 -> Prop)) = (@ex (_143649 -> _143642 -> Prop)).
Proof. exact (eq_refl (@ex (_143649 -> _143642 -> Prop))). Qed.
Lemma lem8098471 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term357 _143642 _143649 s x) = (term358 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098470 _143642 _143649) (@lem8098469 _143642 _143649 s x)). Qed.
Lemma lem8098472 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8098473 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term359 _143642 _143649 s x) = (term360 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098472) (@lem8098471 _143642 _143649 s x)). Qed.
Lemma lem8098474 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term351 _143642 _143649 s x r) = (term298 _143642 _143649 r s x).
Proof. exact (eq_refl (term351 _143642 _143649 s x r)). Qed.
Lemma lem8098475 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term361 _143642 _143649 s x) = (term348 _143642 _143649 s x).
Proof. exact (fun_ext (fun r : type1470 _143642 _143649 => @lem8098474 _143642 _143649 r s x)). Qed.
Lemma lem8098476 {_143642 _143649 : Type'} : (@ex (_143649 -> _143642 -> Prop)) = (@ex (_143649 -> _143642 -> Prop)).
Proof. exact (eq_refl (@ex (_143649 -> _143642 -> Prop))). Qed.
Lemma lem8098477 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term362 _143642 _143649 s x) = (term363 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098476 _143642 _143649) (@lem8098475 _143642 _143649 s x)). Qed.
Lemma lem8098478 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term346 _143642 _143649 s x) = (term364 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098473 _143642 _143649 s x) (@lem8098477 _143642 _143649 s x)). Qed.
Lemma lem8098479 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : ((term345 _143642 _143649 s x) = (term346 _143642 _143649 s x)) = ((term311 _143642 _143649 s x) = (term364 _143642 _143649 s x)).
Proof. exact (MK_COMB (@lem8098467 _143642 _143649 s x) (@lem8098478 _143642 _143649 s x)). Qed.
Lemma lem8098480 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term311 _143642 _143649 s x) = (term364 _143642 _143649 s x).
Proof. exact (EQ_MP (@lem8098479 _143642 _143649 s x) (@lem8098457 _143642 _143649 s x)). Qed.
Lemma lem8098593 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term246 _143642 _143649 s x) = (term246 _143642 _143649 s x).
Proof. exact (eq_refl (term246 _143642 _143649 s x)). Qed.
Lemma lem8098594 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term313 _143642 _143649 s x) = (term365 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098593 _143642 _143649 s x) (@lem8098480 _143642 _143649 s x)). Qed.
Lemma lem8098595 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term318 _143642 _143649 s x) = (term366 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098453 _143642 _143649 s x) (@lem8098594 _143642 _143649 s x)). Qed.
Lemma lem8098597 {A : Type'} (P : Prop) (Q : A -> Prop) : (term367 A P Q) = (term368 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem8098598 {_143642 : Type'} (P : Prop) (Q : _143642 -> Prop) : (term367 _143642 P Q) = (term368 _143642 P Q).
Proof. exact (@lem8098597 _143642 P Q). Qed.
Lemma lem8098599 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term369 _143642 _143649 s x) = (term370 _143642 _143649 s x).
Proof. exact (@lem8098598 _143642 (term113 _143642 _143649 s x) (term244 _143642 _143649 s x)). Qed.
Lemma lem8098600 {_143642 _143649 : Type'} (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term371 _143642 _143649 s x _107385) = (term242 _143642 _143649 _107385 s x).
Proof. exact (eq_refl (term371 _143642 _143649 s x _107385)). Qed.
Lemma lem8098601 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term372 _143642 _143649 s x) = (term244 _143642 _143649 s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8098600 _143642 _143649 _107385 s x)). Qed.
Lemma lem8098602 {_143642 : Type'} : (@ex _143642) = (@ex _143642).
Proof. exact (eq_refl (@ex _143642)). Qed.
Lemma lem8098603 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term373 _143642 _143649 s x) = (term245 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098602 _143642) (@lem8098601 _143642 _143649 s x)). Qed.
Lemma lem8098604 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term246 _143642 _143649 s x) = (term246 _143642 _143649 s x).
Proof. exact (eq_refl (term246 _143642 _143649 s x)). Qed.
Lemma lem8098605 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term369 _143642 _143649 s x) = (term248 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098604 _143642 _143649 s x) (@lem8098603 _143642 _143649 s x)). Qed.
Lemma lem8098606 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8098607 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term374 _143642 _143649 s x) = (term375 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098606) (@lem8098605 _143642 _143649 s x)). Qed.
Lemma lem8098608 {_143642 _143649 : Type'} (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term371 _143642 _143649 s x _107385) = (term242 _143642 _143649 _107385 s x).
Proof. exact (eq_refl (term371 _143642 _143649 s x _107385)). Qed.
Lemma lem8098609 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term246 _143642 _143649 s x) = (term246 _143642 _143649 s x).
Proof. exact (eq_refl (term246 _143642 _143649 s x)). Qed.
Lemma lem8098610 {_143642 _143649 : Type'} (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term376 _143642 _143649 s x _107385) = (term377 _143642 _143649 _107385 s x).
Proof. exact (MK_COMB (@lem8098609 _143642 _143649 s x) (@lem8098608 _143642 _143649 _107385 s x)). Qed.
Lemma lem8098611 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term378 _143642 _143649 s x) = (term379 _143642 _143649 s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8098610 _143642 _143649 _107385 s x)). Qed.
Lemma lem8098612 {_143642 : Type'} : (@ex _143642) = (@ex _143642).
Proof. exact (eq_refl (@ex _143642)). Qed.
Lemma lem8098613 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term370 _143642 _143649 s x) = (term380 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098612 _143642) (@lem8098611 _143642 _143649 s x)). Qed.
Lemma lem8098614 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : ((term369 _143642 _143649 s x) = (term370 _143642 _143649 s x)) = ((term248 _143642 _143649 s x) = (term380 _143642 _143649 s x)).
Proof. exact (MK_COMB (@lem8098607 _143642 _143649 s x) (@lem8098613 _143642 _143649 s x)). Qed.
Lemma lem8098615 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term248 _143642 _143649 s x) = (term380 _143642 _143649 s x).
Proof. exact (EQ_MP (@lem8098614 _143642 _143649 s x) (@lem8098599 _143642 _143649 s x)). Qed.
Lemma lem8098616 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term251 _143642 _143649 r x) = (term251 _143642 _143649 r x).
Proof. exact (eq_refl (term251 _143642 _143649 r x)). Qed.
Lemma lem8098617 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term253 _143642 _143649 r s x) = (term381 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098616 _143642 _143649 r x) (@lem8098615 _143642 _143649 s x)). Qed.
Lemma lem8098619 {A : Type'} (P : Prop) (Q : A -> Prop) : (term367 A P Q) = (term368 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem8098620 {_143642 : Type'} (P : Prop) (Q : _143642 -> Prop) : (term367 _143642 P Q) = (term368 _143642 P Q).
Proof. exact (@lem8098619 _143642 P Q). Qed.
Lemma lem8098621 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term382 _143642 _143649 r s x) = (term383 _143642 _143649 r s x).
Proof. exact (@lem8098620 _143642 (term235 _143642 _143649 r x) (term379 _143642 _143649 s x)). Qed.
Lemma lem8098622 {_143642 _143649 : Type'} (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term384 _143642 _143649 s x _107385) = (term377 _143642 _143649 _107385 s x).
Proof. exact (eq_refl (term384 _143642 _143649 s x _107385)). Qed.
Lemma lem8098623 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term385 _143642 _143649 s x) = (term379 _143642 _143649 s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8098622 _143642 _143649 _107385 s x)). Qed.
Lemma lem8098624 {_143642 : Type'} : (@ex _143642) = (@ex _143642).
Proof. exact (eq_refl (@ex _143642)). Qed.
Lemma lem8098625 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term386 _143642 _143649 s x) = (term380 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098624 _143642) (@lem8098623 _143642 _143649 s x)). Qed.
Lemma lem8098626 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term251 _143642 _143649 r x) = (term251 _143642 _143649 r x).
Proof. exact (eq_refl (term251 _143642 _143649 r x)). Qed.
Lemma lem8098627 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term382 _143642 _143649 r s x) = (term381 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098626 _143642 _143649 r x) (@lem8098625 _143642 _143649 s x)). Qed.
Lemma lem8098628 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8098629 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term387 _143642 _143649 r s x) = (term388 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098628) (@lem8098627 _143642 _143649 r s x)). Qed.
Lemma lem8098630 {_143642 _143649 : Type'} (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term384 _143642 _143649 s x _107385) = (term377 _143642 _143649 _107385 s x).
Proof. exact (eq_refl (term384 _143642 _143649 s x _107385)). Qed.
Lemma lem8098631 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term251 _143642 _143649 r x) = (term251 _143642 _143649 r x).
Proof. exact (eq_refl (term251 _143642 _143649 r x)). Qed.
Lemma lem8098632 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term389 _143642 _143649 r s x _107385) = (term390 _143642 _143649 r _107385 s x).
Proof. exact (MK_COMB (@lem8098631 _143642 _143649 r x) (@lem8098630 _143642 _143649 _107385 s x)). Qed.
Lemma lem8098633 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term391 _143642 _143649 r s x) = (term392 _143642 _143649 r s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8098632 _143642 _143649 r _107385 s x)). Qed.
Lemma lem8098634 {_143642 : Type'} : (@ex _143642) = (@ex _143642).
Proof. exact (eq_refl (@ex _143642)). Qed.
Lemma lem8098635 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term383 _143642 _143649 r s x) = (term393 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098634 _143642) (@lem8098633 _143642 _143649 r s x)). Qed.
Lemma lem8098636 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : ((term382 _143642 _143649 r s x) = (term383 _143642 _143649 r s x)) = ((term381 _143642 _143649 r s x) = (term393 _143642 _143649 r s x)).
Proof. exact (MK_COMB (@lem8098629 _143642 _143649 r s x) (@lem8098635 _143642 _143649 r s x)). Qed.
Lemma lem8098637 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term381 _143642 _143649 r s x) = (term393 _143642 _143649 r s x).
Proof. exact (EQ_MP (@lem8098636 _143642 _143649 r s x) (@lem8098621 _143642 _143649 r s x)). Qed.
Lemma lem8098638 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term253 _143642 _143649 r s x) = (term393 _143642 _143649 r s x).
Proof. exact (TRANS (@lem8098617 _143642 _143649 r s x) (@lem8098637 _143642 _143649 r s x)). Qed.
Lemma lem8098639 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term256 _143642 _143649 r x) = (term256 _143642 _143649 r x).
Proof. exact (eq_refl (term256 _143642 _143649 r x)). Qed.
Lemma lem8098640 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term258 _143642 _143649 r s x) = (term394 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098639 _143642 _143649 r x) (@lem8098638 _143642 _143649 r s x)). Qed.
Lemma lem8098642 {A : Type'} (P : Prop) (Q : A -> Prop) : (term367 A P Q) = (term368 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem8098643 {_143642 : Type'} (P : Prop) (Q : _143642 -> Prop) : (term367 _143642 P Q) = (term368 _143642 P Q).
Proof. exact (@lem8098642 _143642 P Q). Qed.
Lemma lem8098644 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term395 _143642 _143649 r s x) = (term396 _143642 _143649 r s x).
Proof. exact (@lem8098643 _143642 (term66 _143642 _143649 r x) (term392 _143642 _143649 r s x)). Qed.
Lemma lem8098645 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term397 _143642 _143649 r s x _107385) = (term390 _143642 _143649 r _107385 s x).
Proof. exact (eq_refl (term397 _143642 _143649 r s x _107385)). Qed.
Lemma lem8098646 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term398 _143642 _143649 r s x) = (term392 _143642 _143649 r s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8098645 _143642 _143649 r _107385 s x)). Qed.
Lemma lem8098647 {_143642 : Type'} : (@ex _143642) = (@ex _143642).
Proof. exact (eq_refl (@ex _143642)). Qed.
Lemma lem8098648 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term399 _143642 _143649 r s x) = (term393 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098647 _143642) (@lem8098646 _143642 _143649 r s x)). Qed.
Lemma lem8098649 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term256 _143642 _143649 r x) = (term256 _143642 _143649 r x).
Proof. exact (eq_refl (term256 _143642 _143649 r x)). Qed.
Lemma lem8098650 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term395 _143642 _143649 r s x) = (term394 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098649 _143642 _143649 r x) (@lem8098648 _143642 _143649 r s x)). Qed.
Lemma lem8098651 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8098652 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term400 _143642 _143649 r s x) = (term401 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098651) (@lem8098650 _143642 _143649 r s x)). Qed.
Lemma lem8098653 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term397 _143642 _143649 r s x _107385) = (term390 _143642 _143649 r _107385 s x).
Proof. exact (eq_refl (term397 _143642 _143649 r s x _107385)). Qed.
Lemma lem8098654 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term256 _143642 _143649 r x) = (term256 _143642 _143649 r x).
Proof. exact (eq_refl (term256 _143642 _143649 r x)). Qed.
Lemma lem8098655 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term402 _143642 _143649 r s x _107385) = (term403 _143642 _143649 r _107385 s x).
Proof. exact (MK_COMB (@lem8098654 _143642 _143649 r x) (@lem8098653 _143642 _143649 r _107385 s x)). Qed.
Lemma lem8098656 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term404 _143642 _143649 r s x) = (term405 _143642 _143649 r s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8098655 _143642 _143649 r _107385 s x)). Qed.
Lemma lem8098657 {_143642 : Type'} : (@ex _143642) = (@ex _143642).
Proof. exact (eq_refl (@ex _143642)). Qed.
Lemma lem8098658 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term396 _143642 _143649 r s x) = (term406 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098657 _143642) (@lem8098656 _143642 _143649 r s x)). Qed.
Lemma lem8098659 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : ((term395 _143642 _143649 r s x) = (term396 _143642 _143649 r s x)) = ((term394 _143642 _143649 r s x) = (term406 _143642 _143649 r s x)).
Proof. exact (MK_COMB (@lem8098652 _143642 _143649 r s x) (@lem8098658 _143642 _143649 r s x)). Qed.
Lemma lem8098660 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term394 _143642 _143649 r s x) = (term406 _143642 _143649 r s x).
Proof. exact (EQ_MP (@lem8098659 _143642 _143649 r s x) (@lem8098644 _143642 _143649 r s x)). Qed.
Lemma lem8098661 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term258 _143642 _143649 r s x) = (term406 _143642 _143649 r s x).
Proof. exact (TRANS (@lem8098640 _143642 _143649 r s x) (@lem8098660 _143642 _143649 r s x)). Qed.
Lemma lem8098662 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term325 _143642 _143649 s x) = (term407 _143642 _143649 s x).
Proof. exact (fun_ext (fun r : type1470 _143642 _143649 => @lem8098661 _143642 _143649 r s x)). Qed.
Lemma lem8098663 {_143642 _143649 : Type'} : (@ex (_143649 -> _143642 -> Prop)) = (@ex (_143649 -> _143642 -> Prop)).
Proof. exact (eq_refl (@ex (_143649 -> _143642 -> Prop))). Qed.
Lemma lem8098664 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term336 _143642 _143649 s x) = (term408 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098663 _143642 _143649) (@lem8098662 _143642 _143649 s x)). Qed.
Lemma lem8098665 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8098666 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term338 _143642 _143649 s x) = (term409 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098665) (@lem8098664 _143642 _143649 s x)). Qed.
Lemma lem8098668 {A : Type'} (P : Prop) (Q : A -> Prop) : (term367 A P Q) = (term368 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem8098669 {_143642 : Type'} (P : Prop) (Q : _143642 -> Prop) : (term367 _143642 P Q) = (term368 _143642 P Q).
Proof. exact (@lem8098668 _143642 P Q). Qed.
Lemma lem8098670 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term369 _143642 _143649 s x) = (term370 _143642 _143649 s x).
Proof. exact (@lem8098669 _143642 (term113 _143642 _143649 s x) (term244 _143642 _143649 s x)). Qed.
Lemma lem8098671 {_143642 _143649 : Type'} (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term371 _143642 _143649 s x _107385) = (term242 _143642 _143649 _107385 s x).
Proof. exact (eq_refl (term371 _143642 _143649 s x _107385)). Qed.
Lemma lem8098672 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term372 _143642 _143649 s x) = (term244 _143642 _143649 s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8098671 _143642 _143649 _107385 s x)). Qed.
Lemma lem8098673 {_143642 : Type'} : (@ex _143642) = (@ex _143642).
Proof. exact (eq_refl (@ex _143642)). Qed.
Lemma lem8098674 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term373 _143642 _143649 s x) = (term245 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098673 _143642) (@lem8098672 _143642 _143649 s x)). Qed.
Lemma lem8098675 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term246 _143642 _143649 s x) = (term246 _143642 _143649 s x).
Proof. exact (eq_refl (term246 _143642 _143649 s x)). Qed.
Lemma lem8098676 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term369 _143642 _143649 s x) = (term248 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098675 _143642 _143649 s x) (@lem8098674 _143642 _143649 s x)). Qed.
Lemma lem8098677 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8098678 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term374 _143642 _143649 s x) = (term375 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098677) (@lem8098676 _143642 _143649 s x)). Qed.
Lemma lem8098679 {_143642 _143649 : Type'} (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term371 _143642 _143649 s x _107385) = (term242 _143642 _143649 _107385 s x).
Proof. exact (eq_refl (term371 _143642 _143649 s x _107385)). Qed.
Lemma lem8098680 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term246 _143642 _143649 s x) = (term246 _143642 _143649 s x).
Proof. exact (eq_refl (term246 _143642 _143649 s x)). Qed.
Lemma lem8098681 {_143642 _143649 : Type'} (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term376 _143642 _143649 s x _107385) = (term377 _143642 _143649 _107385 s x).
Proof. exact (MK_COMB (@lem8098680 _143642 _143649 s x) (@lem8098679 _143642 _143649 _107385 s x)). Qed.
Lemma lem8098682 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term378 _143642 _143649 s x) = (term379 _143642 _143649 s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8098681 _143642 _143649 _107385 s x)). Qed.
Lemma lem8098683 {_143642 : Type'} : (@ex _143642) = (@ex _143642).
Proof. exact (eq_refl (@ex _143642)). Qed.
Lemma lem8098684 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term370 _143642 _143649 s x) = (term380 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098683 _143642) (@lem8098682 _143642 _143649 s x)). Qed.
Lemma lem8098685 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : ((term369 _143642 _143649 s x) = (term370 _143642 _143649 s x)) = ((term248 _143642 _143649 s x) = (term380 _143642 _143649 s x)).
Proof. exact (MK_COMB (@lem8098678 _143642 _143649 s x) (@lem8098684 _143642 _143649 s x)). Qed.
Lemma lem8098686 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term248 _143642 _143649 s x) = (term380 _143642 _143649 s x).
Proof. exact (EQ_MP (@lem8098685 _143642 _143649 s x) (@lem8098670 _143642 _143649 s x)). Qed.
Lemma lem8098687 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term251 _143642 _143649 r x) = (term251 _143642 _143649 r x).
Proof. exact (eq_refl (term251 _143642 _143649 r x)). Qed.
Lemma lem8098688 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term253 _143642 _143649 r s x) = (term381 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098687 _143642 _143649 r x) (@lem8098686 _143642 _143649 s x)). Qed.
Lemma lem8098690 {A : Type'} (P : Prop) (Q : A -> Prop) : (term367 A P Q) = (term368 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem8098691 {_143642 : Type'} (P : Prop) (Q : _143642 -> Prop) : (term367 _143642 P Q) = (term368 _143642 P Q).
Proof. exact (@lem8098690 _143642 P Q). Qed.
Lemma lem8098692 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term382 _143642 _143649 r s x) = (term383 _143642 _143649 r s x).
Proof. exact (@lem8098691 _143642 (term235 _143642 _143649 r x) (term379 _143642 _143649 s x)). Qed.
Lemma lem8098693 {_143642 _143649 : Type'} (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term384 _143642 _143649 s x _107385) = (term377 _143642 _143649 _107385 s x).
Proof. exact (eq_refl (term384 _143642 _143649 s x _107385)). Qed.
Lemma lem8098694 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term385 _143642 _143649 s x) = (term379 _143642 _143649 s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8098693 _143642 _143649 _107385 s x)). Qed.
Lemma lem8098695 {_143642 : Type'} : (@ex _143642) = (@ex _143642).
Proof. exact (eq_refl (@ex _143642)). Qed.
Lemma lem8098696 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term386 _143642 _143649 s x) = (term380 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098695 _143642) (@lem8098694 _143642 _143649 s x)). Qed.
Lemma lem8098697 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term251 _143642 _143649 r x) = (term251 _143642 _143649 r x).
Proof. exact (eq_refl (term251 _143642 _143649 r x)). Qed.
Lemma lem8098698 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term382 _143642 _143649 r s x) = (term381 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098697 _143642 _143649 r x) (@lem8098696 _143642 _143649 s x)). Qed.
Lemma lem8098699 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8098700 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term387 _143642 _143649 r s x) = (term388 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098699) (@lem8098698 _143642 _143649 r s x)). Qed.
Lemma lem8098701 {_143642 _143649 : Type'} (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term384 _143642 _143649 s x _107385) = (term377 _143642 _143649 _107385 s x).
Proof. exact (eq_refl (term384 _143642 _143649 s x _107385)). Qed.
Lemma lem8098702 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term251 _143642 _143649 r x) = (term251 _143642 _143649 r x).
Proof. exact (eq_refl (term251 _143642 _143649 r x)). Qed.
Lemma lem8098703 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term389 _143642 _143649 r s x _107385) = (term390 _143642 _143649 r _107385 s x).
Proof. exact (MK_COMB (@lem8098702 _143642 _143649 r x) (@lem8098701 _143642 _143649 _107385 s x)). Qed.
Lemma lem8098704 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term391 _143642 _143649 r s x) = (term392 _143642 _143649 r s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8098703 _143642 _143649 r _107385 s x)). Qed.
Lemma lem8098705 {_143642 : Type'} : (@ex _143642) = (@ex _143642).
Proof. exact (eq_refl (@ex _143642)). Qed.
Lemma lem8098706 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term383 _143642 _143649 r s x) = (term393 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098705 _143642) (@lem8098704 _143642 _143649 r s x)). Qed.
Lemma lem8098707 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : ((term382 _143642 _143649 r s x) = (term383 _143642 _143649 r s x)) = ((term381 _143642 _143649 r s x) = (term393 _143642 _143649 r s x)).
Proof. exact (MK_COMB (@lem8098700 _143642 _143649 r s x) (@lem8098706 _143642 _143649 r s x)). Qed.
Lemma lem8098708 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term381 _143642 _143649 r s x) = (term393 _143642 _143649 r s x).
Proof. exact (EQ_MP (@lem8098707 _143642 _143649 r s x) (@lem8098692 _143642 _143649 r s x)). Qed.
Lemma lem8098709 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term253 _143642 _143649 r s x) = (term393 _143642 _143649 r s x).
Proof. exact (TRANS (@lem8098688 _143642 _143649 r s x) (@lem8098708 _143642 _143649 r s x)). Qed.
Lemma lem8098710 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term246 _143642 _143649 r x) = (term246 _143642 _143649 r x).
Proof. exact (eq_refl (term246 _143642 _143649 r x)). Qed.
Lemma lem8098711 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term261 _143642 _143649 r s x) = (term410 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098710 _143642 _143649 r x) (@lem8098709 _143642 _143649 r s x)). Qed.
Lemma lem8098713 {A : Type'} (P : Prop) (Q : A -> Prop) : (term367 A P Q) = (term368 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem8098714 {_143642 : Type'} (P : Prop) (Q : _143642 -> Prop) : (term367 _143642 P Q) = (term368 _143642 P Q).
Proof. exact (@lem8098713 _143642 P Q). Qed.
Lemma lem8098715 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term411 _143642 _143649 r s x) = (term412 _143642 _143649 r s x).
Proof. exact (@lem8098714 _143642 (term113 _143642 _143649 r x) (term392 _143642 _143649 r s x)). Qed.
Lemma lem8098716 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term397 _143642 _143649 r s x _107385) = (term390 _143642 _143649 r _107385 s x).
Proof. exact (eq_refl (term397 _143642 _143649 r s x _107385)). Qed.
Lemma lem8098717 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term398 _143642 _143649 r s x) = (term392 _143642 _143649 r s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8098716 _143642 _143649 r _107385 s x)). Qed.
Lemma lem8098718 {_143642 : Type'} : (@ex _143642) = (@ex _143642).
Proof. exact (eq_refl (@ex _143642)). Qed.
Lemma lem8098719 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term399 _143642 _143649 r s x) = (term393 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098718 _143642) (@lem8098717 _143642 _143649 r s x)). Qed.
Lemma lem8098720 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term246 _143642 _143649 r x) = (term246 _143642 _143649 r x).
Proof. exact (eq_refl (term246 _143642 _143649 r x)). Qed.
Lemma lem8098721 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term411 _143642 _143649 r s x) = (term410 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098720 _143642 _143649 r x) (@lem8098719 _143642 _143649 r s x)). Qed.
Lemma lem8098722 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8098723 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term413 _143642 _143649 r s x) = (term414 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098722) (@lem8098721 _143642 _143649 r s x)). Qed.
Lemma lem8098724 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term397 _143642 _143649 r s x _107385) = (term390 _143642 _143649 r _107385 s x).
Proof. exact (eq_refl (term397 _143642 _143649 r s x _107385)). Qed.
Lemma lem8098725 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term246 _143642 _143649 r x) = (term246 _143642 _143649 r x).
Proof. exact (eq_refl (term246 _143642 _143649 r x)). Qed.
Lemma lem8098726 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term415 _143642 _143649 r s x _107385) = (term416 _143642 _143649 r _107385 s x).
Proof. exact (MK_COMB (@lem8098725 _143642 _143649 r x) (@lem8098724 _143642 _143649 r _107385 s x)). Qed.
Lemma lem8098727 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term417 _143642 _143649 r s x) = (term418 _143642 _143649 r s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8098726 _143642 _143649 r _107385 s x)). Qed.
Lemma lem8098728 {_143642 : Type'} : (@ex _143642) = (@ex _143642).
Proof. exact (eq_refl (@ex _143642)). Qed.
Lemma lem8098729 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term412 _143642 _143649 r s x) = (term419 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098728 _143642) (@lem8098727 _143642 _143649 r s x)). Qed.
Lemma lem8098730 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : ((term411 _143642 _143649 r s x) = (term412 _143642 _143649 r s x)) = ((term410 _143642 _143649 r s x) = (term419 _143642 _143649 r s x)).
Proof. exact (MK_COMB (@lem8098723 _143642 _143649 r s x) (@lem8098729 _143642 _143649 r s x)). Qed.
Lemma lem8098731 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term410 _143642 _143649 r s x) = (term419 _143642 _143649 r s x).
Proof. exact (EQ_MP (@lem8098730 _143642 _143649 r s x) (@lem8098715 _143642 _143649 r s x)). Qed.
Lemma lem8098732 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term261 _143642 _143649 r s x) = (term419 _143642 _143649 r s x).
Proof. exact (TRANS (@lem8098711 _143642 _143649 r s x) (@lem8098731 _143642 _143649 r s x)). Qed.
Lemma lem8098733 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term326 _143642 _143649 s x) = (term420 _143642 _143649 s x).
Proof. exact (fun_ext (fun r : type1470 _143642 _143649 => @lem8098732 _143642 _143649 r s x)). Qed.
Lemma lem8098734 {_143642 _143649 : Type'} : (@ex (_143649 -> _143642 -> Prop)) = (@ex (_143649 -> _143642 -> Prop)).
Proof. exact (eq_refl (@ex (_143649 -> _143642 -> Prop))). Qed.
Lemma lem8098735 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term341 _143642 _143649 s x) = (term421 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098734 _143642 _143649) (@lem8098733 _143642 _143649 s x)). Qed.
Lemma lem8098736 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term342 _143642 _143649 s x) = (term422 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098666 _143642 _143649 s x) (@lem8098735 _143642 _143649 s x)). Qed.
Lemma lem8098738 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term320 A P Q) = (term319 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem8098739 {_143642 _143649 : Type'} (P : type745 _143642 _143649) (Q : type745 _143642 _143649) : (term322 _143642 _143649 P Q) = (term321 _143642 _143649 P Q).
Proof. exact (@lem8098738 (type1470 _143642 _143649) P Q). Qed.
Lemma lem8098740 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term423 _143642 _143649 s x) = (term424 _143642 _143649 s x).
Proof. exact (@lem8098739 _143642 _143649 (term407 _143642 _143649 s x) (term420 _143642 _143649 s x)). Qed.
Lemma lem8098741 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term425 _143642 _143649 s x r) = (term406 _143642 _143649 r s x).
Proof. exact (eq_refl (term425 _143642 _143649 s x r)). Qed.
Lemma lem8098742 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term426 _143642 _143649 s x) = (term407 _143642 _143649 s x).
Proof. exact (fun_ext (fun r : type1470 _143642 _143649 => @lem8098741 _143642 _143649 r s x)). Qed.
Lemma lem8098743 {_143642 _143649 : Type'} : (@ex (_143649 -> _143642 -> Prop)) = (@ex (_143649 -> _143642 -> Prop)).
Proof. exact (eq_refl (@ex (_143649 -> _143642 -> Prop))). Qed.
Lemma lem8098744 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term427 _143642 _143649 s x) = (term408 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098743 _143642 _143649) (@lem8098742 _143642 _143649 s x)). Qed.
Lemma lem8098745 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8098746 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term428 _143642 _143649 s x) = (term409 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098745) (@lem8098744 _143642 _143649 s x)). Qed.
Lemma lem8098747 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term429 _143642 _143649 s x r) = (term419 _143642 _143649 r s x).
Proof. exact (eq_refl (term429 _143642 _143649 s x r)). Qed.
Lemma lem8098748 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term430 _143642 _143649 s x) = (term420 _143642 _143649 s x).
Proof. exact (fun_ext (fun r : type1470 _143642 _143649 => @lem8098747 _143642 _143649 r s x)). Qed.
Lemma lem8098749 {_143642 _143649 : Type'} : (@ex (_143649 -> _143642 -> Prop)) = (@ex (_143649 -> _143642 -> Prop)).
Proof. exact (eq_refl (@ex (_143649 -> _143642 -> Prop))). Qed.
Lemma lem8098750 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term431 _143642 _143649 s x) = (term421 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098749 _143642 _143649) (@lem8098748 _143642 _143649 s x)). Qed.
Lemma lem8098751 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term423 _143642 _143649 s x) = (term422 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098746 _143642 _143649 s x) (@lem8098750 _143642 _143649 s x)). Qed.
Lemma lem8098752 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8098753 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term432 _143642 _143649 s x) = (term433 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098752) (@lem8098751 _143642 _143649 s x)). Qed.
Lemma lem8098754 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term425 _143642 _143649 s x r) = (term406 _143642 _143649 r s x).
Proof. exact (eq_refl (term425 _143642 _143649 s x r)). Qed.
Lemma lem8098755 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8098756 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term434 _143642 _143649 s x r) = (term435 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098755) (@lem8098754 _143642 _143649 r s x)). Qed.
Lemma lem8098757 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term429 _143642 _143649 s x r) = (term419 _143642 _143649 r s x).
Proof. exact (eq_refl (term429 _143642 _143649 s x r)). Qed.
Lemma lem8098758 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term436 _143642 _143649 s x r) = (term437 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098756 _143642 _143649 r s x) (@lem8098757 _143642 _143649 r s x)). Qed.
Lemma lem8098759 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term438 _143642 _143649 s x) = (term439 _143642 _143649 s x).
Proof. exact (fun_ext (fun r : type1470 _143642 _143649 => @lem8098758 _143642 _143649 r s x)). Qed.
Lemma lem8098760 {_143642 _143649 : Type'} : (@ex (_143649 -> _143642 -> Prop)) = (@ex (_143649 -> _143642 -> Prop)).
Proof. exact (eq_refl (@ex (_143649 -> _143642 -> Prop))). Qed.
Lemma lem8098761 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term424 _143642 _143649 s x) = (term440 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098760 _143642 _143649) (@lem8098759 _143642 _143649 s x)). Qed.
Lemma lem8098762 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : ((term423 _143642 _143649 s x) = (term424 _143642 _143649 s x)) = ((term422 _143642 _143649 s x) = (term440 _143642 _143649 s x)).
Proof. exact (MK_COMB (@lem8098753 _143642 _143649 s x) (@lem8098761 _143642 _143649 s x)). Qed.
Lemma lem8098763 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term422 _143642 _143649 s x) = (term440 _143642 _143649 s x).
Proof. exact (EQ_MP (@lem8098762 _143642 _143649 s x) (@lem8098740 _143642 _143649 s x)). Qed.
Lemma lem8098765 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term320 A P Q) = (term319 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem8098766 {_143642 : Type'} (P : _143642 -> Prop) (Q : _143642 -> Prop) : (term320 _143642 P Q) = (term319 _143642 P Q).
Proof. exact (@lem8098765 _143642 P Q). Qed.
Lemma lem8098767 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term441 _143642 _143649 r s x) = (term442 _143642 _143649 r s x).
Proof. exact (@lem8098766 _143642 (term405 _143642 _143649 r s x) (term418 _143642 _143649 r s x)). Qed.
Lemma lem8098768 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term443 _143642 _143649 r s x _107385) = (term403 _143642 _143649 r _107385 s x).
Proof. exact (eq_refl (term443 _143642 _143649 r s x _107385)). Qed.
Lemma lem8098769 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term444 _143642 _143649 r s x) = (term405 _143642 _143649 r s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8098768 _143642 _143649 r _107385 s x)). Qed.
Lemma lem8098770 {_143642 : Type'} : (@ex _143642) = (@ex _143642).
Proof. exact (eq_refl (@ex _143642)). Qed.
Lemma lem8098771 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term445 _143642 _143649 r s x) = (term406 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098770 _143642) (@lem8098769 _143642 _143649 r s x)). Qed.
Lemma lem8098772 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8098773 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term446 _143642 _143649 r s x) = (term435 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098772) (@lem8098771 _143642 _143649 r s x)). Qed.
Lemma lem8098774 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term447 _143642 _143649 r s x _107385) = (term416 _143642 _143649 r _107385 s x).
Proof. exact (eq_refl (term447 _143642 _143649 r s x _107385)). Qed.
Lemma lem8098775 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term448 _143642 _143649 r s x) = (term418 _143642 _143649 r s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8098774 _143642 _143649 r _107385 s x)). Qed.
Lemma lem8098776 {_143642 : Type'} : (@ex _143642) = (@ex _143642).
Proof. exact (eq_refl (@ex _143642)). Qed.
Lemma lem8098777 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term449 _143642 _143649 r s x) = (term419 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098776 _143642) (@lem8098775 _143642 _143649 r s x)). Qed.
Lemma lem8098778 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term441 _143642 _143649 r s x) = (term437 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098773 _143642 _143649 r s x) (@lem8098777 _143642 _143649 r s x)). Qed.
Lemma lem8098779 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8098780 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term450 _143642 _143649 r s x) = (term451 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098779) (@lem8098778 _143642 _143649 r s x)). Qed.
Lemma lem8098781 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term443 _143642 _143649 r s x _107385) = (term403 _143642 _143649 r _107385 s x).
Proof. exact (eq_refl (term443 _143642 _143649 r s x _107385)). Qed.
Lemma lem8098782 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8098783 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term452 _143642 _143649 r s x _107385) = (term453 _143642 _143649 r _107385 s x).
Proof. exact (MK_COMB (@lem8098782) (@lem8098781 _143642 _143649 r _107385 s x)). Qed.
Lemma lem8098784 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term447 _143642 _143649 r s x _107385) = (term416 _143642 _143649 r _107385 s x).
Proof. exact (eq_refl (term447 _143642 _143649 r s x _107385)). Qed.
Lemma lem8098785 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term454 _143642 _143649 r s x _107385) = (term455 _143642 _143649 r _107385 s x).
Proof. exact (MK_COMB (@lem8098783 _143642 _143649 r _107385 s x) (@lem8098784 _143642 _143649 r _107385 s x)). Qed.
Lemma lem8098786 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term456 _143642 _143649 r s x) = (term457 _143642 _143649 r s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8098785 _143642 _143649 r _107385 s x)). Qed.
Lemma lem8098787 {_143642 : Type'} : (@ex _143642) = (@ex _143642).
Proof. exact (eq_refl (@ex _143642)). Qed.
Lemma lem8098788 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term442 _143642 _143649 r s x) = (term458 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098787 _143642) (@lem8098786 _143642 _143649 r s x)). Qed.
Lemma lem8098789 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : ((term441 _143642 _143649 r s x) = (term442 _143642 _143649 r s x)) = ((term437 _143642 _143649 r s x) = (term458 _143642 _143649 r s x)).
Proof. exact (MK_COMB (@lem8098780 _143642 _143649 r s x) (@lem8098788 _143642 _143649 r s x)). Qed.
Lemma lem8098790 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term437 _143642 _143649 r s x) = (term458 _143642 _143649 r s x).
Proof. exact (EQ_MP (@lem8098789 _143642 _143649 r s x) (@lem8098767 _143642 _143649 r s x)). Qed.
Lemma lem8098791 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term439 _143642 _143649 s x) = (term459 _143642 _143649 s x).
Proof. exact (fun_ext (fun r : type1470 _143642 _143649 => @lem8098790 _143642 _143649 r s x)). Qed.
Lemma lem8098792 {_143642 _143649 : Type'} : (@ex (_143649 -> _143642 -> Prop)) = (@ex (_143649 -> _143642 -> Prop)).
Proof. exact (eq_refl (@ex (_143649 -> _143642 -> Prop))). Qed.
Lemma lem8098793 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term440 _143642 _143649 s x) = (term460 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098792 _143642 _143649) (@lem8098791 _143642 _143649 s x)). Qed.
Lemma lem8098794 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term422 _143642 _143649 s x) = (term460 _143642 _143649 s x).
Proof. exact (TRANS (@lem8098763 _143642 _143649 s x) (@lem8098793 _143642 _143649 s x)). Qed.
Lemma lem8098795 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term342 _143642 _143649 s x) = (term460 _143642 _143649 s x).
Proof. exact (TRANS (@lem8098736 _143642 _143649 s x) (@lem8098794 _143642 _143649 s x)). Qed.
Lemma lem8098796 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term256 _143642 _143649 s x) = (term256 _143642 _143649 s x).
Proof. exact (eq_refl (term256 _143642 _143649 s x)). Qed.
Lemma lem8098797 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term343 _143642 _143649 s x) = (term461 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098796 _143642 _143649 s x) (@lem8098795 _143642 _143649 s x)). Qed.
Lemma lem8098799 {A : Type'} (P : Prop) (Q : A -> Prop) : (term367 A P Q) = (term368 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem8098800 {_143642 _143649 : Type'} (P : Prop) (Q : type745 _143642 _143649) : (term462 _143642 _143649 P Q) = (term463 _143642 _143649 P Q).
Proof. exact (@lem8098799 (type1470 _143642 _143649) P Q). Qed.
Lemma lem8098801 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term464 _143642 _143649 s x) = (term465 _143642 _143649 s x).
Proof. exact (@lem8098800 _143642 _143649 (term66 _143642 _143649 s x) (term459 _143642 _143649 s x)). Qed.
Lemma lem8098802 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term466 _143642 _143649 s x r) = (term458 _143642 _143649 r s x).
Proof. exact (eq_refl (term466 _143642 _143649 s x r)). Qed.
Lemma lem8098803 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term467 _143642 _143649 s x) = (term459 _143642 _143649 s x).
Proof. exact (fun_ext (fun r : type1470 _143642 _143649 => @lem8098802 _143642 _143649 r s x)). Qed.
Lemma lem8098804 {_143642 _143649 : Type'} : (@ex (_143649 -> _143642 -> Prop)) = (@ex (_143649 -> _143642 -> Prop)).
Proof. exact (eq_refl (@ex (_143649 -> _143642 -> Prop))). Qed.
Lemma lem8098805 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term468 _143642 _143649 s x) = (term460 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098804 _143642 _143649) (@lem8098803 _143642 _143649 s x)). Qed.
Lemma lem8098806 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term256 _143642 _143649 s x) = (term256 _143642 _143649 s x).
Proof. exact (eq_refl (term256 _143642 _143649 s x)). Qed.
Lemma lem8098807 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term464 _143642 _143649 s x) = (term461 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098806 _143642 _143649 s x) (@lem8098805 _143642 _143649 s x)). Qed.
Lemma lem8098808 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8098809 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term469 _143642 _143649 s x) = (term470 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098808) (@lem8098807 _143642 _143649 s x)). Qed.
Lemma lem8098810 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term466 _143642 _143649 s x r) = (term458 _143642 _143649 r s x).
Proof. exact (eq_refl (term466 _143642 _143649 s x r)). Qed.
Lemma lem8098811 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term256 _143642 _143649 s x) = (term256 _143642 _143649 s x).
Proof. exact (eq_refl (term256 _143642 _143649 s x)). Qed.
Lemma lem8098812 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term471 _143642 _143649 s x r) = (term472 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098811 _143642 _143649 s x) (@lem8098810 _143642 _143649 r s x)). Qed.
Lemma lem8098813 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term473 _143642 _143649 s x) = (term474 _143642 _143649 s x).
Proof. exact (fun_ext (fun r : type1470 _143642 _143649 => @lem8098812 _143642 _143649 r s x)). Qed.
Lemma lem8098814 {_143642 _143649 : Type'} : (@ex (_143649 -> _143642 -> Prop)) = (@ex (_143649 -> _143642 -> Prop)).
Proof. exact (eq_refl (@ex (_143649 -> _143642 -> Prop))). Qed.
Lemma lem8098815 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term465 _143642 _143649 s x) = (term475 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098814 _143642 _143649) (@lem8098813 _143642 _143649 s x)). Qed.
Lemma lem8098816 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : ((term464 _143642 _143649 s x) = (term465 _143642 _143649 s x)) = ((term461 _143642 _143649 s x) = (term475 _143642 _143649 s x)).
Proof. exact (MK_COMB (@lem8098809 _143642 _143649 s x) (@lem8098815 _143642 _143649 s x)). Qed.
Lemma lem8098817 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term461 _143642 _143649 s x) = (term475 _143642 _143649 s x).
Proof. exact (EQ_MP (@lem8098816 _143642 _143649 s x) (@lem8098801 _143642 _143649 s x)). Qed.
Lemma lem8098819 {A : Type'} (P : Prop) (Q : A -> Prop) : (term367 A P Q) = (term368 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem8098820 {_143642 : Type'} (P : Prop) (Q : _143642 -> Prop) : (term367 _143642 P Q) = (term368 _143642 P Q).
Proof. exact (@lem8098819 _143642 P Q). Qed.
Lemma lem8098821 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term476 _143642 _143649 r s x) = (term477 _143642 _143649 r s x).
Proof. exact (@lem8098820 _143642 (term66 _143642 _143649 s x) (term457 _143642 _143649 r s x)). Qed.
Lemma lem8098822 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term478 _143642 _143649 r s x _107385) = (term455 _143642 _143649 r _107385 s x).
Proof. exact (eq_refl (term478 _143642 _143649 r s x _107385)). Qed.
Lemma lem8098823 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term479 _143642 _143649 r s x) = (term457 _143642 _143649 r s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8098822 _143642 _143649 r _107385 s x)). Qed.
Lemma lem8098824 {_143642 : Type'} : (@ex _143642) = (@ex _143642).
Proof. exact (eq_refl (@ex _143642)). Qed.
Lemma lem8098825 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term480 _143642 _143649 r s x) = (term458 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098824 _143642) (@lem8098823 _143642 _143649 r s x)). Qed.
Lemma lem8098826 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term256 _143642 _143649 s x) = (term256 _143642 _143649 s x).
Proof. exact (eq_refl (term256 _143642 _143649 s x)). Qed.
Lemma lem8098827 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term476 _143642 _143649 r s x) = (term472 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098826 _143642 _143649 s x) (@lem8098825 _143642 _143649 r s x)). Qed.
Lemma lem8098828 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8098829 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term481 _143642 _143649 r s x) = (term482 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098828) (@lem8098827 _143642 _143649 r s x)). Qed.
Lemma lem8098830 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term478 _143642 _143649 r s x _107385) = (term455 _143642 _143649 r _107385 s x).
Proof. exact (eq_refl (term478 _143642 _143649 r s x _107385)). Qed.
Lemma lem8098831 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term256 _143642 _143649 s x) = (term256 _143642 _143649 s x).
Proof. exact (eq_refl (term256 _143642 _143649 s x)). Qed.
Lemma lem8098832 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term483 _143642 _143649 r s x _107385) = (term484 _143642 _143649 r _107385 s x).
Proof. exact (MK_COMB (@lem8098831 _143642 _143649 s x) (@lem8098830 _143642 _143649 r _107385 s x)). Qed.
Lemma lem8098833 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term485 _143642 _143649 r s x) = (term486 _143642 _143649 r s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8098832 _143642 _143649 r _107385 s x)). Qed.
Lemma lem8098834 {_143642 : Type'} : (@ex _143642) = (@ex _143642).
Proof. exact (eq_refl (@ex _143642)). Qed.
Lemma lem8098835 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term477 _143642 _143649 r s x) = (term487 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098834 _143642) (@lem8098833 _143642 _143649 r s x)). Qed.
Lemma lem8098836 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : ((term476 _143642 _143649 r s x) = (term477 _143642 _143649 r s x)) = ((term472 _143642 _143649 r s x) = (term487 _143642 _143649 r s x)).
Proof. exact (MK_COMB (@lem8098829 _143642 _143649 r s x) (@lem8098835 _143642 _143649 r s x)). Qed.
Lemma lem8098837 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term472 _143642 _143649 r s x) = (term487 _143642 _143649 r s x).
Proof. exact (EQ_MP (@lem8098836 _143642 _143649 r s x) (@lem8098821 _143642 _143649 r s x)). Qed.
Lemma lem8098838 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term474 _143642 _143649 s x) = (term488 _143642 _143649 s x).
Proof. exact (fun_ext (fun r : type1470 _143642 _143649 => @lem8098837 _143642 _143649 r s x)). Qed.
Lemma lem8098839 {_143642 _143649 : Type'} : (@ex (_143649 -> _143642 -> Prop)) = (@ex (_143649 -> _143642 -> Prop)).
Proof. exact (eq_refl (@ex (_143649 -> _143642 -> Prop))). Qed.
Lemma lem8098840 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term475 _143642 _143649 s x) = (term489 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098839 _143642 _143649) (@lem8098838 _143642 _143649 s x)). Qed.
Lemma lem8098841 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term461 _143642 _143649 s x) = (term489 _143642 _143649 s x).
Proof. exact (TRANS (@lem8098817 _143642 _143649 s x) (@lem8098840 _143642 _143649 s x)). Qed.
Lemma lem8098842 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term343 _143642 _143649 s x) = (term489 _143642 _143649 s x).
Proof. exact (TRANS (@lem8098797 _143642 _143649 s x) (@lem8098841 _143642 _143649 s x)). Qed.
Lemma lem8098843 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8098844 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term344 _143642 _143649 s x) = (term490 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098843) (@lem8098842 _143642 _143649 s x)). Qed.
Lemma lem8098846 {A : Type'} (P : Prop) (Q : A -> Prop) : (term367 A P Q) = (term368 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem8098847 {_143642 : Type'} (P : Prop) (Q : _143642 -> Prop) : (term367 _143642 P Q) = (term368 _143642 P Q).
Proof. exact (@lem8098846 _143642 P Q). Qed.
Lemma lem8098848 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term491 _143642 _143649 s x) = (term492 _143642 _143649 s x).
Proof. exact (@lem8098847 _143642 (term66 _143642 _143649 s x) (term286 _143642 _143649 s x)). Qed.
Lemma lem8098849 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term493 _143642 _143649 s x _107385) = (term284 _143642 _143649 s x _107385).
Proof. exact (eq_refl (term493 _143642 _143649 s x _107385)). Qed.
Lemma lem8098850 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term494 _143642 _143649 s x) = (term286 _143642 _143649 s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8098849 _143642 _143649 s x _107385)). Qed.
Lemma lem8098851 {_143642 : Type'} : (@ex _143642) = (@ex _143642).
Proof. exact (eq_refl (@ex _143642)). Qed.
Lemma lem8098852 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term495 _143642 _143649 s x) = (term287 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098851 _143642) (@lem8098850 _143642 _143649 s x)). Qed.
Lemma lem8098853 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term256 _143642 _143649 s x) = (term256 _143642 _143649 s x).
Proof. exact (eq_refl (term256 _143642 _143649 s x)). Qed.
Lemma lem8098854 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term491 _143642 _143649 s x) = (term289 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098853 _143642 _143649 s x) (@lem8098852 _143642 _143649 s x)). Qed.
Lemma lem8098855 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8098856 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term496 _143642 _143649 s x) = (term497 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098855) (@lem8098854 _143642 _143649 s x)). Qed.
Lemma lem8098857 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term493 _143642 _143649 s x _107385) = (term284 _143642 _143649 s x _107385).
Proof. exact (eq_refl (term493 _143642 _143649 s x _107385)). Qed.
Lemma lem8098858 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term256 _143642 _143649 s x) = (term256 _143642 _143649 s x).
Proof. exact (eq_refl (term256 _143642 _143649 s x)). Qed.
Lemma lem8098859 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term498 _143642 _143649 s x _107385) = (term499 _143642 _143649 s x _107385).
Proof. exact (MK_COMB (@lem8098858 _143642 _143649 s x) (@lem8098857 _143642 _143649 s x _107385)). Qed.
Lemma lem8098860 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term500 _143642 _143649 s x) = (term501 _143642 _143649 s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8098859 _143642 _143649 s x _107385)). Qed.
Lemma lem8098861 {_143642 : Type'} : (@ex _143642) = (@ex _143642).
Proof. exact (eq_refl (@ex _143642)). Qed.
Lemma lem8098862 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term492 _143642 _143649 s x) = (term502 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098861 _143642) (@lem8098860 _143642 _143649 s x)). Qed.
Lemma lem8098863 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : ((term491 _143642 _143649 s x) = (term492 _143642 _143649 s x)) = ((term289 _143642 _143649 s x) = (term502 _143642 _143649 s x)).
Proof. exact (MK_COMB (@lem8098856 _143642 _143649 s x) (@lem8098862 _143642 _143649 s x)). Qed.
Lemma lem8098864 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term289 _143642 _143649 s x) = (term502 _143642 _143649 s x).
Proof. exact (EQ_MP (@lem8098863 _143642 _143649 s x) (@lem8098848 _143642 _143649 s x)). Qed.
Lemma lem8098865 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term251 _143642 _143649 r x) = (term251 _143642 _143649 r x).
Proof. exact (eq_refl (term251 _143642 _143649 r x)). Qed.
Lemma lem8098866 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term292 _143642 _143649 r s x) = (term503 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098865 _143642 _143649 r x) (@lem8098864 _143642 _143649 s x)). Qed.
Lemma lem8098868 {A : Type'} (P : Prop) (Q : A -> Prop) : (term367 A P Q) = (term368 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem8098869 {_143642 : Type'} (P : Prop) (Q : _143642 -> Prop) : (term367 _143642 P Q) = (term368 _143642 P Q).
Proof. exact (@lem8098868 _143642 P Q). Qed.
Lemma lem8098870 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term504 _143642 _143649 r s x) = (term505 _143642 _143649 r s x).
Proof. exact (@lem8098869 _143642 (term235 _143642 _143649 r x) (term501 _143642 _143649 s x)). Qed.
Lemma lem8098871 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term506 _143642 _143649 s x _107385) = (term499 _143642 _143649 s x _107385).
Proof. exact (eq_refl (term506 _143642 _143649 s x _107385)). Qed.
Lemma lem8098872 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term507 _143642 _143649 s x) = (term501 _143642 _143649 s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8098871 _143642 _143649 s x _107385)). Qed.
Lemma lem8098873 {_143642 : Type'} : (@ex _143642) = (@ex _143642).
Proof. exact (eq_refl (@ex _143642)). Qed.
Lemma lem8098874 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term508 _143642 _143649 s x) = (term502 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098873 _143642) (@lem8098872 _143642 _143649 s x)). Qed.
Lemma lem8098875 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term251 _143642 _143649 r x) = (term251 _143642 _143649 r x).
Proof. exact (eq_refl (term251 _143642 _143649 r x)). Qed.
Lemma lem8098876 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term504 _143642 _143649 r s x) = (term503 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098875 _143642 _143649 r x) (@lem8098874 _143642 _143649 s x)). Qed.
Lemma lem8098877 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8098878 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term509 _143642 _143649 r s x) = (term510 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098877) (@lem8098876 _143642 _143649 r s x)). Qed.
Lemma lem8098879 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term506 _143642 _143649 s x _107385) = (term499 _143642 _143649 s x _107385).
Proof. exact (eq_refl (term506 _143642 _143649 s x _107385)). Qed.
Lemma lem8098880 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term251 _143642 _143649 r x) = (term251 _143642 _143649 r x).
Proof. exact (eq_refl (term251 _143642 _143649 r x)). Qed.
Lemma lem8098881 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term511 _143642 _143649 r s x _107385) = (term512 _143642 _143649 r s x _107385).
Proof. exact (MK_COMB (@lem8098880 _143642 _143649 r x) (@lem8098879 _143642 _143649 s x _107385)). Qed.
Lemma lem8098882 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term513 _143642 _143649 r s x) = (term514 _143642 _143649 r s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8098881 _143642 _143649 r s x _107385)). Qed.
Lemma lem8098883 {_143642 : Type'} : (@ex _143642) = (@ex _143642).
Proof. exact (eq_refl (@ex _143642)). Qed.
Lemma lem8098884 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term505 _143642 _143649 r s x) = (term515 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098883 _143642) (@lem8098882 _143642 _143649 r s x)). Qed.
Lemma lem8098885 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : ((term504 _143642 _143649 r s x) = (term505 _143642 _143649 r s x)) = ((term503 _143642 _143649 r s x) = (term515 _143642 _143649 r s x)).
Proof. exact (MK_COMB (@lem8098878 _143642 _143649 r s x) (@lem8098884 _143642 _143649 r s x)). Qed.
Lemma lem8098886 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term503 _143642 _143649 r s x) = (term515 _143642 _143649 r s x).
Proof. exact (EQ_MP (@lem8098885 _143642 _143649 r s x) (@lem8098870 _143642 _143649 r s x)). Qed.
Lemma lem8098887 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term292 _143642 _143649 r s x) = (term515 _143642 _143649 r s x).
Proof. exact (TRANS (@lem8098866 _143642 _143649 r s x) (@lem8098886 _143642 _143649 r s x)). Qed.
Lemma lem8098888 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term256 _143642 _143649 r x) = (term256 _143642 _143649 r x).
Proof. exact (eq_refl (term256 _143642 _143649 r x)). Qed.
Lemma lem8098889 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term295 _143642 _143649 r s x) = (term516 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098888 _143642 _143649 r x) (@lem8098887 _143642 _143649 r s x)). Qed.
Lemma lem8098891 {A : Type'} (P : Prop) (Q : A -> Prop) : (term367 A P Q) = (term368 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem8098892 {_143642 : Type'} (P : Prop) (Q : _143642 -> Prop) : (term367 _143642 P Q) = (term368 _143642 P Q).
Proof. exact (@lem8098891 _143642 P Q). Qed.
Lemma lem8098893 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term517 _143642 _143649 r s x) = (term518 _143642 _143649 r s x).
Proof. exact (@lem8098892 _143642 (term66 _143642 _143649 r x) (term514 _143642 _143649 r s x)). Qed.
Lemma lem8098894 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term519 _143642 _143649 r s x _107385) = (term512 _143642 _143649 r s x _107385).
Proof. exact (eq_refl (term519 _143642 _143649 r s x _107385)). Qed.
Lemma lem8098895 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term520 _143642 _143649 r s x) = (term514 _143642 _143649 r s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8098894 _143642 _143649 r s x _107385)). Qed.
Lemma lem8098896 {_143642 : Type'} : (@ex _143642) = (@ex _143642).
Proof. exact (eq_refl (@ex _143642)). Qed.
Lemma lem8098897 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term521 _143642 _143649 r s x) = (term515 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098896 _143642) (@lem8098895 _143642 _143649 r s x)). Qed.
Lemma lem8098898 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term256 _143642 _143649 r x) = (term256 _143642 _143649 r x).
Proof. exact (eq_refl (term256 _143642 _143649 r x)). Qed.
Lemma lem8098899 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term517 _143642 _143649 r s x) = (term516 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098898 _143642 _143649 r x) (@lem8098897 _143642 _143649 r s x)). Qed.
Lemma lem8098900 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8098901 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term522 _143642 _143649 r s x) = (term523 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098900) (@lem8098899 _143642 _143649 r s x)). Qed.
Lemma lem8098902 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term519 _143642 _143649 r s x _107385) = (term512 _143642 _143649 r s x _107385).
Proof. exact (eq_refl (term519 _143642 _143649 r s x _107385)). Qed.
Lemma lem8098903 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term256 _143642 _143649 r x) = (term256 _143642 _143649 r x).
Proof. exact (eq_refl (term256 _143642 _143649 r x)). Qed.
Lemma lem8098904 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term524 _143642 _143649 r s x _107385) = (term525 _143642 _143649 r s x _107385).
Proof. exact (MK_COMB (@lem8098903 _143642 _143649 r x) (@lem8098902 _143642 _143649 r s x _107385)). Qed.
Lemma lem8098905 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term526 _143642 _143649 r s x) = (term527 _143642 _143649 r s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8098904 _143642 _143649 r s x _107385)). Qed.
Lemma lem8098906 {_143642 : Type'} : (@ex _143642) = (@ex _143642).
Proof. exact (eq_refl (@ex _143642)). Qed.
Lemma lem8098907 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term518 _143642 _143649 r s x) = (term528 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098906 _143642) (@lem8098905 _143642 _143649 r s x)). Qed.
Lemma lem8098908 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : ((term517 _143642 _143649 r s x) = (term518 _143642 _143649 r s x)) = ((term516 _143642 _143649 r s x) = (term528 _143642 _143649 r s x)).
Proof. exact (MK_COMB (@lem8098901 _143642 _143649 r s x) (@lem8098907 _143642 _143649 r s x)). Qed.
Lemma lem8098909 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term516 _143642 _143649 r s x) = (term528 _143642 _143649 r s x).
Proof. exact (EQ_MP (@lem8098908 _143642 _143649 r s x) (@lem8098893 _143642 _143649 r s x)). Qed.
Lemma lem8098910 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term295 _143642 _143649 r s x) = (term528 _143642 _143649 r s x).
Proof. exact (TRANS (@lem8098889 _143642 _143649 r s x) (@lem8098909 _143642 _143649 r s x)). Qed.
Lemma lem8098911 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term347 _143642 _143649 s x) = (term529 _143642 _143649 s x).
Proof. exact (fun_ext (fun r : type1470 _143642 _143649 => @lem8098910 _143642 _143649 r s x)). Qed.
Lemma lem8098912 {_143642 _143649 : Type'} : (@ex (_143649 -> _143642 -> Prop)) = (@ex (_143649 -> _143642 -> Prop)).
Proof. exact (eq_refl (@ex (_143649 -> _143642 -> Prop))). Qed.
Lemma lem8098913 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term358 _143642 _143649 s x) = (term530 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098912 _143642 _143649) (@lem8098911 _143642 _143649 s x)). Qed.
Lemma lem8098914 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8098915 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term360 _143642 _143649 s x) = (term531 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098914) (@lem8098913 _143642 _143649 s x)). Qed.
Lemma lem8098917 {A : Type'} (P : Prop) (Q : A -> Prop) : (term367 A P Q) = (term368 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem8098918 {_143642 : Type'} (P : Prop) (Q : _143642 -> Prop) : (term367 _143642 P Q) = (term368 _143642 P Q).
Proof. exact (@lem8098917 _143642 P Q). Qed.
Lemma lem8098919 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term491 _143642 _143649 s x) = (term492 _143642 _143649 s x).
Proof. exact (@lem8098918 _143642 (term66 _143642 _143649 s x) (term286 _143642 _143649 s x)). Qed.
Lemma lem8098920 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term493 _143642 _143649 s x _107385) = (term284 _143642 _143649 s x _107385).
Proof. exact (eq_refl (term493 _143642 _143649 s x _107385)). Qed.
Lemma lem8098921 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term494 _143642 _143649 s x) = (term286 _143642 _143649 s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8098920 _143642 _143649 s x _107385)). Qed.
Lemma lem8098922 {_143642 : Type'} : (@ex _143642) = (@ex _143642).
Proof. exact (eq_refl (@ex _143642)). Qed.
Lemma lem8098923 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term495 _143642 _143649 s x) = (term287 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098922 _143642) (@lem8098921 _143642 _143649 s x)). Qed.
Lemma lem8098924 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term256 _143642 _143649 s x) = (term256 _143642 _143649 s x).
Proof. exact (eq_refl (term256 _143642 _143649 s x)). Qed.
Lemma lem8098925 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term491 _143642 _143649 s x) = (term289 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098924 _143642 _143649 s x) (@lem8098923 _143642 _143649 s x)). Qed.
Lemma lem8098926 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8098927 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term496 _143642 _143649 s x) = (term497 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098926) (@lem8098925 _143642 _143649 s x)). Qed.
Lemma lem8098928 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term493 _143642 _143649 s x _107385) = (term284 _143642 _143649 s x _107385).
Proof. exact (eq_refl (term493 _143642 _143649 s x _107385)). Qed.
Lemma lem8098929 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term256 _143642 _143649 s x) = (term256 _143642 _143649 s x).
Proof. exact (eq_refl (term256 _143642 _143649 s x)). Qed.
Lemma lem8098930 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term498 _143642 _143649 s x _107385) = (term499 _143642 _143649 s x _107385).
Proof. exact (MK_COMB (@lem8098929 _143642 _143649 s x) (@lem8098928 _143642 _143649 s x _107385)). Qed.
Lemma lem8098931 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term500 _143642 _143649 s x) = (term501 _143642 _143649 s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8098930 _143642 _143649 s x _107385)). Qed.
Lemma lem8098932 {_143642 : Type'} : (@ex _143642) = (@ex _143642).
Proof. exact (eq_refl (@ex _143642)). Qed.
Lemma lem8098933 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term492 _143642 _143649 s x) = (term502 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098932 _143642) (@lem8098931 _143642 _143649 s x)). Qed.
Lemma lem8098934 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : ((term491 _143642 _143649 s x) = (term492 _143642 _143649 s x)) = ((term289 _143642 _143649 s x) = (term502 _143642 _143649 s x)).
Proof. exact (MK_COMB (@lem8098927 _143642 _143649 s x) (@lem8098933 _143642 _143649 s x)). Qed.
Lemma lem8098935 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term289 _143642 _143649 s x) = (term502 _143642 _143649 s x).
Proof. exact (EQ_MP (@lem8098934 _143642 _143649 s x) (@lem8098919 _143642 _143649 s x)). Qed.
Lemma lem8098936 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term251 _143642 _143649 r x) = (term251 _143642 _143649 r x).
Proof. exact (eq_refl (term251 _143642 _143649 r x)). Qed.
Lemma lem8098937 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term292 _143642 _143649 r s x) = (term503 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098936 _143642 _143649 r x) (@lem8098935 _143642 _143649 s x)). Qed.
Lemma lem8098939 {A : Type'} (P : Prop) (Q : A -> Prop) : (term367 A P Q) = (term368 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem8098940 {_143642 : Type'} (P : Prop) (Q : _143642 -> Prop) : (term367 _143642 P Q) = (term368 _143642 P Q).
Proof. exact (@lem8098939 _143642 P Q). Qed.
Lemma lem8098941 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term504 _143642 _143649 r s x) = (term505 _143642 _143649 r s x).
Proof. exact (@lem8098940 _143642 (term235 _143642 _143649 r x) (term501 _143642 _143649 s x)). Qed.
Lemma lem8098942 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term506 _143642 _143649 s x _107385) = (term499 _143642 _143649 s x _107385).
Proof. exact (eq_refl (term506 _143642 _143649 s x _107385)). Qed.
Lemma lem8098943 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term507 _143642 _143649 s x) = (term501 _143642 _143649 s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8098942 _143642 _143649 s x _107385)). Qed.
Lemma lem8098944 {_143642 : Type'} : (@ex _143642) = (@ex _143642).
Proof. exact (eq_refl (@ex _143642)). Qed.
Lemma lem8098945 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term508 _143642 _143649 s x) = (term502 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098944 _143642) (@lem8098943 _143642 _143649 s x)). Qed.
Lemma lem8098946 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term251 _143642 _143649 r x) = (term251 _143642 _143649 r x).
Proof. exact (eq_refl (term251 _143642 _143649 r x)). Qed.
Lemma lem8098947 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term504 _143642 _143649 r s x) = (term503 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098946 _143642 _143649 r x) (@lem8098945 _143642 _143649 s x)). Qed.
Lemma lem8098948 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8098949 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term509 _143642 _143649 r s x) = (term510 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098948) (@lem8098947 _143642 _143649 r s x)). Qed.
Lemma lem8098950 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term506 _143642 _143649 s x _107385) = (term499 _143642 _143649 s x _107385).
Proof. exact (eq_refl (term506 _143642 _143649 s x _107385)). Qed.
Lemma lem8098951 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term251 _143642 _143649 r x) = (term251 _143642 _143649 r x).
Proof. exact (eq_refl (term251 _143642 _143649 r x)). Qed.
Lemma lem8098952 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term511 _143642 _143649 r s x _107385) = (term512 _143642 _143649 r s x _107385).
Proof. exact (MK_COMB (@lem8098951 _143642 _143649 r x) (@lem8098950 _143642 _143649 s x _107385)). Qed.
Lemma lem8098953 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term513 _143642 _143649 r s x) = (term514 _143642 _143649 r s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8098952 _143642 _143649 r s x _107385)). Qed.
Lemma lem8098954 {_143642 : Type'} : (@ex _143642) = (@ex _143642).
Proof. exact (eq_refl (@ex _143642)). Qed.
Lemma lem8098955 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term505 _143642 _143649 r s x) = (term515 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098954 _143642) (@lem8098953 _143642 _143649 r s x)). Qed.
Lemma lem8098956 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : ((term504 _143642 _143649 r s x) = (term505 _143642 _143649 r s x)) = ((term503 _143642 _143649 r s x) = (term515 _143642 _143649 r s x)).
Proof. exact (MK_COMB (@lem8098949 _143642 _143649 r s x) (@lem8098955 _143642 _143649 r s x)). Qed.
Lemma lem8098957 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term503 _143642 _143649 r s x) = (term515 _143642 _143649 r s x).
Proof. exact (EQ_MP (@lem8098956 _143642 _143649 r s x) (@lem8098941 _143642 _143649 r s x)). Qed.
Lemma lem8098958 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term292 _143642 _143649 r s x) = (term515 _143642 _143649 r s x).
Proof. exact (TRANS (@lem8098937 _143642 _143649 r s x) (@lem8098957 _143642 _143649 r s x)). Qed.
Lemma lem8098959 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term246 _143642 _143649 r x) = (term246 _143642 _143649 r x).
Proof. exact (eq_refl (term246 _143642 _143649 r x)). Qed.
Lemma lem8098960 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term298 _143642 _143649 r s x) = (term532 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098959 _143642 _143649 r x) (@lem8098958 _143642 _143649 r s x)). Qed.
Lemma lem8098962 {A : Type'} (P : Prop) (Q : A -> Prop) : (term367 A P Q) = (term368 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem8098963 {_143642 : Type'} (P : Prop) (Q : _143642 -> Prop) : (term367 _143642 P Q) = (term368 _143642 P Q).
Proof. exact (@lem8098962 _143642 P Q). Qed.
Lemma lem8098964 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term533 _143642 _143649 r s x) = (term534 _143642 _143649 r s x).
Proof. exact (@lem8098963 _143642 (term113 _143642 _143649 r x) (term514 _143642 _143649 r s x)). Qed.
Lemma lem8098965 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term519 _143642 _143649 r s x _107385) = (term512 _143642 _143649 r s x _107385).
Proof. exact (eq_refl (term519 _143642 _143649 r s x _107385)). Qed.
Lemma lem8098966 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term520 _143642 _143649 r s x) = (term514 _143642 _143649 r s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8098965 _143642 _143649 r s x _107385)). Qed.
Lemma lem8098967 {_143642 : Type'} : (@ex _143642) = (@ex _143642).
Proof. exact (eq_refl (@ex _143642)). Qed.
Lemma lem8098968 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term521 _143642 _143649 r s x) = (term515 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098967 _143642) (@lem8098966 _143642 _143649 r s x)). Qed.
Lemma lem8098969 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term246 _143642 _143649 r x) = (term246 _143642 _143649 r x).
Proof. exact (eq_refl (term246 _143642 _143649 r x)). Qed.
Lemma lem8098970 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term533 _143642 _143649 r s x) = (term532 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098969 _143642 _143649 r x) (@lem8098968 _143642 _143649 r s x)). Qed.
Lemma lem8098971 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8098972 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term535 _143642 _143649 r s x) = (term536 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098971) (@lem8098970 _143642 _143649 r s x)). Qed.
Lemma lem8098973 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term519 _143642 _143649 r s x _107385) = (term512 _143642 _143649 r s x _107385).
Proof. exact (eq_refl (term519 _143642 _143649 r s x _107385)). Qed.
Lemma lem8098974 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term246 _143642 _143649 r x) = (term246 _143642 _143649 r x).
Proof. exact (eq_refl (term246 _143642 _143649 r x)). Qed.
Lemma lem8098975 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term537 _143642 _143649 r s x _107385) = (term538 _143642 _143649 r s x _107385).
Proof. exact (MK_COMB (@lem8098974 _143642 _143649 r x) (@lem8098973 _143642 _143649 r s x _107385)). Qed.
Lemma lem8098976 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term539 _143642 _143649 r s x) = (term540 _143642 _143649 r s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8098975 _143642 _143649 r s x _107385)). Qed.
Lemma lem8098977 {_143642 : Type'} : (@ex _143642) = (@ex _143642).
Proof. exact (eq_refl (@ex _143642)). Qed.
Lemma lem8098978 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term534 _143642 _143649 r s x) = (term541 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8098977 _143642) (@lem8098976 _143642 _143649 r s x)). Qed.
Lemma lem8098979 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : ((term533 _143642 _143649 r s x) = (term534 _143642 _143649 r s x)) = ((term532 _143642 _143649 r s x) = (term541 _143642 _143649 r s x)).
Proof. exact (MK_COMB (@lem8098972 _143642 _143649 r s x) (@lem8098978 _143642 _143649 r s x)). Qed.
Lemma lem8098980 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term532 _143642 _143649 r s x) = (term541 _143642 _143649 r s x).
Proof. exact (EQ_MP (@lem8098979 _143642 _143649 r s x) (@lem8098964 _143642 _143649 r s x)). Qed.
Lemma lem8098981 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term298 _143642 _143649 r s x) = (term541 _143642 _143649 r s x).
Proof. exact (TRANS (@lem8098960 _143642 _143649 r s x) (@lem8098980 _143642 _143649 r s x)). Qed.
Lemma lem8098982 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term348 _143642 _143649 s x) = (term542 _143642 _143649 s x).
Proof. exact (fun_ext (fun r : type1470 _143642 _143649 => @lem8098981 _143642 _143649 r s x)). Qed.
Lemma lem8098983 {_143642 _143649 : Type'} : (@ex (_143649 -> _143642 -> Prop)) = (@ex (_143649 -> _143642 -> Prop)).
Proof. exact (eq_refl (@ex (_143649 -> _143642 -> Prop))). Qed.
Lemma lem8098984 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term363 _143642 _143649 s x) = (term543 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098983 _143642 _143649) (@lem8098982 _143642 _143649 s x)). Qed.
Lemma lem8098985 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term364 _143642 _143649 s x) = (term544 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098915 _143642 _143649 s x) (@lem8098984 _143642 _143649 s x)). Qed.
Lemma lem8098987 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term320 A P Q) = (term319 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem8098988 {_143642 _143649 : Type'} (P : type745 _143642 _143649) (Q : type745 _143642 _143649) : (term322 _143642 _143649 P Q) = (term321 _143642 _143649 P Q).
Proof. exact (@lem8098987 (type1470 _143642 _143649) P Q). Qed.
Lemma lem8098989 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term545 _143642 _143649 s x) = (term546 _143642 _143649 s x).
Proof. exact (@lem8098988 _143642 _143649 (term529 _143642 _143649 s x) (term542 _143642 _143649 s x)). Qed.
Lemma lem8098990 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term547 _143642 _143649 s x r) = (term528 _143642 _143649 r s x).
Proof. exact (eq_refl (term547 _143642 _143649 s x r)). Qed.
Lemma lem8098991 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term548 _143642 _143649 s x) = (term529 _143642 _143649 s x).
Proof. exact (fun_ext (fun r : type1470 _143642 _143649 => @lem8098990 _143642 _143649 r s x)). Qed.
Lemma lem8098992 {_143642 _143649 : Type'} : (@ex (_143649 -> _143642 -> Prop)) = (@ex (_143649 -> _143642 -> Prop)).
Proof. exact (eq_refl (@ex (_143649 -> _143642 -> Prop))). Qed.
Lemma lem8098993 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term549 _143642 _143649 s x) = (term530 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098992 _143642 _143649) (@lem8098991 _143642 _143649 s x)). Qed.
Lemma lem8098994 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8098995 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term550 _143642 _143649 s x) = (term531 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098994) (@lem8098993 _143642 _143649 s x)). Qed.
Lemma lem8098996 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term551 _143642 _143649 s x r) = (term541 _143642 _143649 r s x).
Proof. exact (eq_refl (term551 _143642 _143649 s x r)). Qed.
Lemma lem8098997 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term552 _143642 _143649 s x) = (term542 _143642 _143649 s x).
Proof. exact (fun_ext (fun r : type1470 _143642 _143649 => @lem8098996 _143642 _143649 r s x)). Qed.
Lemma lem8098998 {_143642 _143649 : Type'} : (@ex (_143649 -> _143642 -> Prop)) = (@ex (_143649 -> _143642 -> Prop)).
Proof. exact (eq_refl (@ex (_143649 -> _143642 -> Prop))). Qed.
Lemma lem8098999 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term553 _143642 _143649 s x) = (term543 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098998 _143642 _143649) (@lem8098997 _143642 _143649 s x)). Qed.
Lemma lem8099000 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term545 _143642 _143649 s x) = (term544 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098995 _143642 _143649 s x) (@lem8098999 _143642 _143649 s x)). Qed.
Lemma lem8099001 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8099002 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term554 _143642 _143649 s x) = (term555 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8099001) (@lem8099000 _143642 _143649 s x)). Qed.
Lemma lem8099003 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term547 _143642 _143649 s x r) = (term528 _143642 _143649 r s x).
Proof. exact (eq_refl (term547 _143642 _143649 s x r)). Qed.
Lemma lem8099004 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8099005 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term556 _143642 _143649 s x r) = (term557 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8099004) (@lem8099003 _143642 _143649 r s x)). Qed.
Lemma lem8099006 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term551 _143642 _143649 s x r) = (term541 _143642 _143649 r s x).
Proof. exact (eq_refl (term551 _143642 _143649 s x r)). Qed.
Lemma lem8099007 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term558 _143642 _143649 s x r) = (term559 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8099005 _143642 _143649 r s x) (@lem8099006 _143642 _143649 r s x)). Qed.
Lemma lem8099008 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term560 _143642 _143649 s x) = (term561 _143642 _143649 s x).
Proof. exact (fun_ext (fun r : type1470 _143642 _143649 => @lem8099007 _143642 _143649 r s x)). Qed.
Lemma lem8099009 {_143642 _143649 : Type'} : (@ex (_143649 -> _143642 -> Prop)) = (@ex (_143649 -> _143642 -> Prop)).
Proof. exact (eq_refl (@ex (_143649 -> _143642 -> Prop))). Qed.
Lemma lem8099010 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term546 _143642 _143649 s x) = (term562 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8099009 _143642 _143649) (@lem8099008 _143642 _143649 s x)). Qed.
Lemma lem8099011 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : ((term545 _143642 _143649 s x) = (term546 _143642 _143649 s x)) = ((term544 _143642 _143649 s x) = (term562 _143642 _143649 s x)).
Proof. exact (MK_COMB (@lem8099002 _143642 _143649 s x) (@lem8099010 _143642 _143649 s x)). Qed.
Lemma lem8099012 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term544 _143642 _143649 s x) = (term562 _143642 _143649 s x).
Proof. exact (EQ_MP (@lem8099011 _143642 _143649 s x) (@lem8098989 _143642 _143649 s x)). Qed.
Lemma lem8099014 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term320 A P Q) = (term319 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem8099015 {_143642 : Type'} (P : _143642 -> Prop) (Q : _143642 -> Prop) : (term320 _143642 P Q) = (term319 _143642 P Q).
Proof. exact (@lem8099014 _143642 P Q). Qed.
Lemma lem8099016 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term563 _143642 _143649 r s x) = (term564 _143642 _143649 r s x).
Proof. exact (@lem8099015 _143642 (term527 _143642 _143649 r s x) (term540 _143642 _143649 r s x)). Qed.
Lemma lem8099017 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term565 _143642 _143649 r s x _107385) = (term525 _143642 _143649 r s x _107385).
Proof. exact (eq_refl (term565 _143642 _143649 r s x _107385)). Qed.
Lemma lem8099018 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term566 _143642 _143649 r s x) = (term527 _143642 _143649 r s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8099017 _143642 _143649 r s x _107385)). Qed.
Lemma lem8099019 {_143642 : Type'} : (@ex _143642) = (@ex _143642).
Proof. exact (eq_refl (@ex _143642)). Qed.
Lemma lem8099020 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term567 _143642 _143649 r s x) = (term528 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8099019 _143642) (@lem8099018 _143642 _143649 r s x)). Qed.
Lemma lem8099021 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8099022 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term568 _143642 _143649 r s x) = (term557 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8099021) (@lem8099020 _143642 _143649 r s x)). Qed.
Lemma lem8099023 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term569 _143642 _143649 r s x _107385) = (term538 _143642 _143649 r s x _107385).
Proof. exact (eq_refl (term569 _143642 _143649 r s x _107385)). Qed.
Lemma lem8099024 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term570 _143642 _143649 r s x) = (term540 _143642 _143649 r s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8099023 _143642 _143649 r s x _107385)). Qed.
Lemma lem8099025 {_143642 : Type'} : (@ex _143642) = (@ex _143642).
Proof. exact (eq_refl (@ex _143642)). Qed.
Lemma lem8099026 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term571 _143642 _143649 r s x) = (term541 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8099025 _143642) (@lem8099024 _143642 _143649 r s x)). Qed.
Lemma lem8099027 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term563 _143642 _143649 r s x) = (term559 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8099022 _143642 _143649 r s x) (@lem8099026 _143642 _143649 r s x)). Qed.
Lemma lem8099028 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8099029 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term572 _143642 _143649 r s x) = (term573 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8099028) (@lem8099027 _143642 _143649 r s x)). Qed.
Lemma lem8099030 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term565 _143642 _143649 r s x _107385) = (term525 _143642 _143649 r s x _107385).
Proof. exact (eq_refl (term565 _143642 _143649 r s x _107385)). Qed.
Lemma lem8099031 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8099032 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term574 _143642 _143649 r s x _107385) = (term575 _143642 _143649 r s x _107385).
Proof. exact (MK_COMB (@lem8099031) (@lem8099030 _143642 _143649 r s x _107385)). Qed.
Lemma lem8099033 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term569 _143642 _143649 r s x _107385) = (term538 _143642 _143649 r s x _107385).
Proof. exact (eq_refl (term569 _143642 _143649 r s x _107385)). Qed.
Lemma lem8099034 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term576 _143642 _143649 r s x _107385) = (term577 _143642 _143649 r s x _107385).
Proof. exact (MK_COMB (@lem8099032 _143642 _143649 r s x _107385) (@lem8099033 _143642 _143649 r s x _107385)). Qed.
Lemma lem8099035 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term578 _143642 _143649 r s x) = (term579 _143642 _143649 r s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8099034 _143642 _143649 r s x _107385)). Qed.
Lemma lem8099036 {_143642 : Type'} : (@ex _143642) = (@ex _143642).
Proof. exact (eq_refl (@ex _143642)). Qed.
Lemma lem8099037 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term564 _143642 _143649 r s x) = (term580 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8099036 _143642) (@lem8099035 _143642 _143649 r s x)). Qed.
Lemma lem8099038 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : ((term563 _143642 _143649 r s x) = (term564 _143642 _143649 r s x)) = ((term559 _143642 _143649 r s x) = (term580 _143642 _143649 r s x)).
Proof. exact (MK_COMB (@lem8099029 _143642 _143649 r s x) (@lem8099037 _143642 _143649 r s x)). Qed.
Lemma lem8099039 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term559 _143642 _143649 r s x) = (term580 _143642 _143649 r s x).
Proof. exact (EQ_MP (@lem8099038 _143642 _143649 r s x) (@lem8099016 _143642 _143649 r s x)). Qed.
Lemma lem8099040 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term561 _143642 _143649 s x) = (term581 _143642 _143649 s x).
Proof. exact (fun_ext (fun r : type1470 _143642 _143649 => @lem8099039 _143642 _143649 r s x)). Qed.
Lemma lem8099041 {_143642 _143649 : Type'} : (@ex (_143649 -> _143642 -> Prop)) = (@ex (_143649 -> _143642 -> Prop)).
Proof. exact (eq_refl (@ex (_143649 -> _143642 -> Prop))). Qed.
Lemma lem8099042 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term562 _143642 _143649 s x) = (term582 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8099041 _143642 _143649) (@lem8099040 _143642 _143649 s x)). Qed.
Lemma lem8099043 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term544 _143642 _143649 s x) = (term582 _143642 _143649 s x).
Proof. exact (TRANS (@lem8099012 _143642 _143649 s x) (@lem8099042 _143642 _143649 s x)). Qed.
Lemma lem8099044 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term364 _143642 _143649 s x) = (term582 _143642 _143649 s x).
Proof. exact (TRANS (@lem8098985 _143642 _143649 s x) (@lem8099043 _143642 _143649 s x)). Qed.
Lemma lem8099045 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term246 _143642 _143649 s x) = (term246 _143642 _143649 s x).
Proof. exact (eq_refl (term246 _143642 _143649 s x)). Qed.
Lemma lem8099046 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term365 _143642 _143649 s x) = (term583 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8099045 _143642 _143649 s x) (@lem8099044 _143642 _143649 s x)). Qed.
Lemma lem8099048 {A : Type'} (P : Prop) (Q : A -> Prop) : (term367 A P Q) = (term368 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem8099049 {_143642 _143649 : Type'} (P : Prop) (Q : type745 _143642 _143649) : (term462 _143642 _143649 P Q) = (term463 _143642 _143649 P Q).
Proof. exact (@lem8099048 (type1470 _143642 _143649) P Q). Qed.
Lemma lem8099050 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term584 _143642 _143649 s x) = (term585 _143642 _143649 s x).
Proof. exact (@lem8099049 _143642 _143649 (term113 _143642 _143649 s x) (term581 _143642 _143649 s x)). Qed.
Lemma lem8099051 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term586 _143642 _143649 s x r) = (term580 _143642 _143649 r s x).
Proof. exact (eq_refl (term586 _143642 _143649 s x r)). Qed.
Lemma lem8099052 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term587 _143642 _143649 s x) = (term581 _143642 _143649 s x).
Proof. exact (fun_ext (fun r : type1470 _143642 _143649 => @lem8099051 _143642 _143649 r s x)). Qed.
Lemma lem8099053 {_143642 _143649 : Type'} : (@ex (_143649 -> _143642 -> Prop)) = (@ex (_143649 -> _143642 -> Prop)).
Proof. exact (eq_refl (@ex (_143649 -> _143642 -> Prop))). Qed.
Lemma lem8099054 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term588 _143642 _143649 s x) = (term582 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8099053 _143642 _143649) (@lem8099052 _143642 _143649 s x)). Qed.
Lemma lem8099055 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term246 _143642 _143649 s x) = (term246 _143642 _143649 s x).
Proof. exact (eq_refl (term246 _143642 _143649 s x)). Qed.
Lemma lem8099056 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term584 _143642 _143649 s x) = (term583 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8099055 _143642 _143649 s x) (@lem8099054 _143642 _143649 s x)). Qed.
Lemma lem8099057 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8099058 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term589 _143642 _143649 s x) = (term590 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8099057) (@lem8099056 _143642 _143649 s x)). Qed.
Lemma lem8099059 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term586 _143642 _143649 s x r) = (term580 _143642 _143649 r s x).
Proof. exact (eq_refl (term586 _143642 _143649 s x r)). Qed.
Lemma lem8099060 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term246 _143642 _143649 s x) = (term246 _143642 _143649 s x).
Proof. exact (eq_refl (term246 _143642 _143649 s x)). Qed.
Lemma lem8099061 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term591 _143642 _143649 s x r) = (term592 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8099060 _143642 _143649 s x) (@lem8099059 _143642 _143649 r s x)). Qed.
Lemma lem8099062 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term593 _143642 _143649 s x) = (term594 _143642 _143649 s x).
Proof. exact (fun_ext (fun r : type1470 _143642 _143649 => @lem8099061 _143642 _143649 r s x)). Qed.
Lemma lem8099063 {_143642 _143649 : Type'} : (@ex (_143649 -> _143642 -> Prop)) = (@ex (_143649 -> _143642 -> Prop)).
Proof. exact (eq_refl (@ex (_143649 -> _143642 -> Prop))). Qed.
Lemma lem8099064 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term585 _143642 _143649 s x) = (term595 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8099063 _143642 _143649) (@lem8099062 _143642 _143649 s x)). Qed.
Lemma lem8099065 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : ((term584 _143642 _143649 s x) = (term585 _143642 _143649 s x)) = ((term583 _143642 _143649 s x) = (term595 _143642 _143649 s x)).
Proof. exact (MK_COMB (@lem8099058 _143642 _143649 s x) (@lem8099064 _143642 _143649 s x)). Qed.
Lemma lem8099066 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term583 _143642 _143649 s x) = (term595 _143642 _143649 s x).
Proof. exact (EQ_MP (@lem8099065 _143642 _143649 s x) (@lem8099050 _143642 _143649 s x)). Qed.
Lemma lem8099068 {A : Type'} (P : Prop) (Q : A -> Prop) : (term367 A P Q) = (term368 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem8099069 {_143642 : Type'} (P : Prop) (Q : _143642 -> Prop) : (term367 _143642 P Q) = (term368 _143642 P Q).
Proof. exact (@lem8099068 _143642 P Q). Qed.
Lemma lem8099070 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term596 _143642 _143649 r s x) = (term597 _143642 _143649 r s x).
Proof. exact (@lem8099069 _143642 (term113 _143642 _143649 s x) (term579 _143642 _143649 r s x)). Qed.
Lemma lem8099071 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term598 _143642 _143649 r s x _107385) = (term577 _143642 _143649 r s x _107385).
Proof. exact (eq_refl (term598 _143642 _143649 r s x _107385)). Qed.
Lemma lem8099072 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term599 _143642 _143649 r s x) = (term579 _143642 _143649 r s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8099071 _143642 _143649 r s x _107385)). Qed.
Lemma lem8099073 {_143642 : Type'} : (@ex _143642) = (@ex _143642).
Proof. exact (eq_refl (@ex _143642)). Qed.
Lemma lem8099074 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term600 _143642 _143649 r s x) = (term580 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8099073 _143642) (@lem8099072 _143642 _143649 r s x)). Qed.
Lemma lem8099075 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term246 _143642 _143649 s x) = (term246 _143642 _143649 s x).
Proof. exact (eq_refl (term246 _143642 _143649 s x)). Qed.
Lemma lem8099076 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term596 _143642 _143649 r s x) = (term592 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8099075 _143642 _143649 s x) (@lem8099074 _143642 _143649 r s x)). Qed.
Lemma lem8099077 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8099078 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term601 _143642 _143649 r s x) = (term602 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8099077) (@lem8099076 _143642 _143649 r s x)). Qed.
Lemma lem8099079 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term598 _143642 _143649 r s x _107385) = (term577 _143642 _143649 r s x _107385).
Proof. exact (eq_refl (term598 _143642 _143649 r s x _107385)). Qed.
Lemma lem8099080 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term246 _143642 _143649 s x) = (term246 _143642 _143649 s x).
Proof. exact (eq_refl (term246 _143642 _143649 s x)). Qed.
Lemma lem8099081 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term603 _143642 _143649 r s x _107385) = (term604 _143642 _143649 r s x _107385).
Proof. exact (MK_COMB (@lem8099080 _143642 _143649 s x) (@lem8099079 _143642 _143649 r s x _107385)). Qed.
Lemma lem8099082 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term605 _143642 _143649 r s x) = (term606 _143642 _143649 r s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8099081 _143642 _143649 r s x _107385)). Qed.
Lemma lem8099083 {_143642 : Type'} : (@ex _143642) = (@ex _143642).
Proof. exact (eq_refl (@ex _143642)). Qed.
Lemma lem8099084 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term597 _143642 _143649 r s x) = (term607 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8099083 _143642) (@lem8099082 _143642 _143649 r s x)). Qed.
Lemma lem8099085 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : ((term596 _143642 _143649 r s x) = (term597 _143642 _143649 r s x)) = ((term592 _143642 _143649 r s x) = (term607 _143642 _143649 r s x)).
Proof. exact (MK_COMB (@lem8099078 _143642 _143649 r s x) (@lem8099084 _143642 _143649 r s x)). Qed.
Lemma lem8099086 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term592 _143642 _143649 r s x) = (term607 _143642 _143649 r s x).
Proof. exact (EQ_MP (@lem8099085 _143642 _143649 r s x) (@lem8099070 _143642 _143649 r s x)). Qed.
Lemma lem8099087 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term594 _143642 _143649 s x) = (term608 _143642 _143649 s x).
Proof. exact (fun_ext (fun r : type1470 _143642 _143649 => @lem8099086 _143642 _143649 r s x)). Qed.
Lemma lem8099088 {_143642 _143649 : Type'} : (@ex (_143649 -> _143642 -> Prop)) = (@ex (_143649 -> _143642 -> Prop)).
Proof. exact (eq_refl (@ex (_143649 -> _143642 -> Prop))). Qed.
Lemma lem8099089 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term595 _143642 _143649 s x) = (term609 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8099088 _143642 _143649) (@lem8099087 _143642 _143649 s x)). Qed.
Lemma lem8099090 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term583 _143642 _143649 s x) = (term609 _143642 _143649 s x).
Proof. exact (TRANS (@lem8099066 _143642 _143649 s x) (@lem8099089 _143642 _143649 s x)). Qed.
Lemma lem8099091 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term365 _143642 _143649 s x) = (term609 _143642 _143649 s x).
Proof. exact (TRANS (@lem8099046 _143642 _143649 s x) (@lem8099090 _143642 _143649 s x)). Qed.
Lemma lem8099092 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term366 _143642 _143649 s x) = (term610 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8098844 _143642 _143649 s x) (@lem8099091 _143642 _143649 s x)). Qed.
Lemma lem8099094 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term320 A P Q) = (term319 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem8099095 {_143642 _143649 : Type'} (P : type745 _143642 _143649) (Q : type745 _143642 _143649) : (term322 _143642 _143649 P Q) = (term321 _143642 _143649 P Q).
Proof. exact (@lem8099094 (type1470 _143642 _143649) P Q). Qed.
Lemma lem8099096 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term611 _143642 _143649 s x) = (term612 _143642 _143649 s x).
Proof. exact (@lem8099095 _143642 _143649 (term488 _143642 _143649 s x) (term608 _143642 _143649 s x)). Qed.
Lemma lem8099097 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term613 _143642 _143649 s x r) = (term487 _143642 _143649 r s x).
Proof. exact (eq_refl (term613 _143642 _143649 s x r)). Qed.
Lemma lem8099098 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term614 _143642 _143649 s x) = (term488 _143642 _143649 s x).
Proof. exact (fun_ext (fun r : type1470 _143642 _143649 => @lem8099097 _143642 _143649 r s x)). Qed.
Lemma lem8099099 {_143642 _143649 : Type'} : (@ex (_143649 -> _143642 -> Prop)) = (@ex (_143649 -> _143642 -> Prop)).
Proof. exact (eq_refl (@ex (_143649 -> _143642 -> Prop))). Qed.
Lemma lem8099100 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term615 _143642 _143649 s x) = (term489 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8099099 _143642 _143649) (@lem8099098 _143642 _143649 s x)). Qed.
Lemma lem8099101 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8099102 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term616 _143642 _143649 s x) = (term490 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8099101) (@lem8099100 _143642 _143649 s x)). Qed.
Lemma lem8099103 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term617 _143642 _143649 s x r) = (term607 _143642 _143649 r s x).
Proof. exact (eq_refl (term617 _143642 _143649 s x r)). Qed.
Lemma lem8099104 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term618 _143642 _143649 s x) = (term608 _143642 _143649 s x).
Proof. exact (fun_ext (fun r : type1470 _143642 _143649 => @lem8099103 _143642 _143649 r s x)). Qed.
Lemma lem8099105 {_143642 _143649 : Type'} : (@ex (_143649 -> _143642 -> Prop)) = (@ex (_143649 -> _143642 -> Prop)).
Proof. exact (eq_refl (@ex (_143649 -> _143642 -> Prop))). Qed.
Lemma lem8099106 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term619 _143642 _143649 s x) = (term609 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8099105 _143642 _143649) (@lem8099104 _143642 _143649 s x)). Qed.
Lemma lem8099107 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term611 _143642 _143649 s x) = (term610 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8099102 _143642 _143649 s x) (@lem8099106 _143642 _143649 s x)). Qed.
Lemma lem8099108 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8099109 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term620 _143642 _143649 s x) = (term621 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8099108) (@lem8099107 _143642 _143649 s x)). Qed.
Lemma lem8099110 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term613 _143642 _143649 s x r) = (term487 _143642 _143649 r s x).
Proof. exact (eq_refl (term613 _143642 _143649 s x r)). Qed.
Lemma lem8099111 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8099112 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term622 _143642 _143649 s x r) = (term623 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8099111) (@lem8099110 _143642 _143649 r s x)). Qed.
Lemma lem8099113 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term617 _143642 _143649 s x r) = (term607 _143642 _143649 r s x).
Proof. exact (eq_refl (term617 _143642 _143649 s x r)). Qed.
Lemma lem8099114 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term624 _143642 _143649 s x r) = (term625 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8099112 _143642 _143649 r s x) (@lem8099113 _143642 _143649 r s x)). Qed.
Lemma lem8099115 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term626 _143642 _143649 s x) = (term627 _143642 _143649 s x).
Proof. exact (fun_ext (fun r : type1470 _143642 _143649 => @lem8099114 _143642 _143649 r s x)). Qed.
Lemma lem8099116 {_143642 _143649 : Type'} : (@ex (_143649 -> _143642 -> Prop)) = (@ex (_143649 -> _143642 -> Prop)).
Proof. exact (eq_refl (@ex (_143649 -> _143642 -> Prop))). Qed.
Lemma lem8099117 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term612 _143642 _143649 s x) = (term628 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8099116 _143642 _143649) (@lem8099115 _143642 _143649 s x)). Qed.
Lemma lem8099118 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : ((term611 _143642 _143649 s x) = (term612 _143642 _143649 s x)) = ((term610 _143642 _143649 s x) = (term628 _143642 _143649 s x)).
Proof. exact (MK_COMB (@lem8099109 _143642 _143649 s x) (@lem8099117 _143642 _143649 s x)). Qed.
Lemma lem8099119 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term610 _143642 _143649 s x) = (term628 _143642 _143649 s x).
Proof. exact (EQ_MP (@lem8099118 _143642 _143649 s x) (@lem8099096 _143642 _143649 s x)). Qed.
Lemma lem8099121 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term320 A P Q) = (term319 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem8099122 {_143642 : Type'} (P : _143642 -> Prop) (Q : _143642 -> Prop) : (term320 _143642 P Q) = (term319 _143642 P Q).
Proof. exact (@lem8099121 _143642 P Q). Qed.
Lemma lem8099123 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term629 _143642 _143649 r s x) = (term630 _143642 _143649 r s x).
Proof. exact (@lem8099122 _143642 (term486 _143642 _143649 r s x) (term606 _143642 _143649 r s x)). Qed.
Lemma lem8099124 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term631 _143642 _143649 r s x _107385) = (term484 _143642 _143649 r _107385 s x).
Proof. exact (eq_refl (term631 _143642 _143649 r s x _107385)). Qed.
Lemma lem8099125 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term632 _143642 _143649 r s x) = (term486 _143642 _143649 r s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8099124 _143642 _143649 r _107385 s x)). Qed.
Lemma lem8099126 {_143642 : Type'} : (@ex _143642) = (@ex _143642).
Proof. exact (eq_refl (@ex _143642)). Qed.
Lemma lem8099127 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term633 _143642 _143649 r s x) = (term487 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8099126 _143642) (@lem8099125 _143642 _143649 r s x)). Qed.
Lemma lem8099128 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8099129 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term634 _143642 _143649 r s x) = (term623 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8099128) (@lem8099127 _143642 _143649 r s x)). Qed.
Lemma lem8099130 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term635 _143642 _143649 r s x _107385) = (term604 _143642 _143649 r s x _107385).
Proof. exact (eq_refl (term635 _143642 _143649 r s x _107385)). Qed.
Lemma lem8099131 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term636 _143642 _143649 r s x) = (term606 _143642 _143649 r s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8099130 _143642 _143649 r s x _107385)). Qed.
Lemma lem8099132 {_143642 : Type'} : (@ex _143642) = (@ex _143642).
Proof. exact (eq_refl (@ex _143642)). Qed.
Lemma lem8099133 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term637 _143642 _143649 r s x) = (term607 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8099132 _143642) (@lem8099131 _143642 _143649 r s x)). Qed.
Lemma lem8099134 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term629 _143642 _143649 r s x) = (term625 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8099129 _143642 _143649 r s x) (@lem8099133 _143642 _143649 r s x)). Qed.
Lemma lem8099135 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8099136 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term638 _143642 _143649 r s x) = (term639 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8099135) (@lem8099134 _143642 _143649 r s x)). Qed.
Lemma lem8099137 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term631 _143642 _143649 r s x _107385) = (term484 _143642 _143649 r _107385 s x).
Proof. exact (eq_refl (term631 _143642 _143649 r s x _107385)). Qed.
Lemma lem8099138 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8099139 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term640 _143642 _143649 r s x _107385) = (term641 _143642 _143649 r _107385 s x).
Proof. exact (MK_COMB (@lem8099138) (@lem8099137 _143642 _143649 r _107385 s x)). Qed.
Lemma lem8099140 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term635 _143642 _143649 r s x _107385) = (term604 _143642 _143649 r s x _107385).
Proof. exact (eq_refl (term635 _143642 _143649 r s x _107385)). Qed.
Lemma lem8099141 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term642 _143642 _143649 r s x _107385) = (term643 _143642 _143649 r s x _107385).
Proof. exact (MK_COMB (@lem8099139 _143642 _143649 r _107385 s x) (@lem8099140 _143642 _143649 r s x _107385)). Qed.
Lemma lem8099142 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term644 _143642 _143649 r s x) = (term645 _143642 _143649 r s x).
Proof. exact (fun_ext (fun _107385 : _143642 => @lem8099141 _143642 _143649 r s x _107385)). Qed.
Lemma lem8099143 {_143642 : Type'} : (@ex _143642) = (@ex _143642).
Proof. exact (eq_refl (@ex _143642)). Qed.
Lemma lem8099144 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term630 _143642 _143649 r s x) = (term646 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8099143 _143642) (@lem8099142 _143642 _143649 r s x)). Qed.
Lemma lem8099145 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : ((term629 _143642 _143649 r s x) = (term630 _143642 _143649 r s x)) = ((term625 _143642 _143649 r s x) = (term646 _143642 _143649 r s x)).
Proof. exact (MK_COMB (@lem8099136 _143642 _143649 r s x) (@lem8099144 _143642 _143649 r s x)). Qed.
Lemma lem8099146 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term625 _143642 _143649 r s x) = (term646 _143642 _143649 r s x).
Proof. exact (EQ_MP (@lem8099145 _143642 _143649 r s x) (@lem8099123 _143642 _143649 r s x)). Qed.
Lemma lem8099147 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term627 _143642 _143649 s x) = (term647 _143642 _143649 s x).
Proof. exact (fun_ext (fun r : type1470 _143642 _143649 => @lem8099146 _143642 _143649 r s x)). Qed.
Lemma lem8099148 {_143642 _143649 : Type'} : (@ex (_143649 -> _143642 -> Prop)) = (@ex (_143649 -> _143642 -> Prop)).
Proof. exact (eq_refl (@ex (_143649 -> _143642 -> Prop))). Qed.
Lemma lem8099149 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term628 _143642 _143649 s x) = (term648 _143642 _143649 s x).
Proof. exact (MK_COMB (@lem8099148 _143642 _143649) (@lem8099147 _143642 _143649 s x)). Qed.
Lemma lem8099150 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term610 _143642 _143649 s x) = (term648 _143642 _143649 s x).
Proof. exact (TRANS (@lem8099119 _143642 _143649 s x) (@lem8099149 _143642 _143649 s x)). Qed.
Lemma lem8099151 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term366 _143642 _143649 s x) = (term648 _143642 _143649 s x).
Proof. exact (TRANS (@lem8099092 _143642 _143649 s x) (@lem8099150 _143642 _143649 s x)). Qed.
Lemma lem8099152 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term318 _143642 _143649 s x) = (term648 _143642 _143649 s x).
Proof. exact (TRANS (@lem8098595 _143642 _143649 s x) (@lem8099151 _143642 _143649 s x)). Qed.
Lemma lem8099153 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term225 _143642 _143649 s x) = (term648 _143642 _143649 s x).
Proof. exact (TRANS (@lem8098310 _143642 _143649 s x) (@lem8099152 _143642 _143649 s x)). Qed.
Lemma lem8099154 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) (h1 : term225 _143642 _143649 s x) : term648 _143642 _143649 s x.
Proof. exact (EQ_MP (@lem8099153 _143642 _143649 s x) (@lem8098097 _143642 _143649 s x h1)). Qed.
Lemma lem8099155 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : term646 _143642 _143649 r s x) : term646 _143642 _143649 r s x.
Proof. exact (h1). Qed.
Lemma lem8099156 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) (h1 : term643 _143642 _143649 r s x _107385) : term643 _143642 _143649 r s x _107385.
Proof. exact (h1). Qed.
Lemma lem8099175 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term499 _143642 _143649 s x _107385) = (term499 _143642 _143649 s x _107385).
Proof. exact (eq_refl (term499 _143642 _143649 s x _107385)). Qed.
Lemma lem8099176 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8099183 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8099184 {_143642 : Type'} (f : _143642 -> Prop) (x : _143642) : (f x) = (@I (_143642 -> Prop) f x).
Proof. exact (@lem8099183 _143642 Prop f x). Qed.
Lemma lem8099186 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (y : _143642) : (r x y) = (term649 _143642 _143649 r x y).
Proof. exact (@lem8099184 _143642 (r x) y). Qed.
Lemma lem8099187 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (y : _143642) : (term232 _143642 _143649 r x y) = (term650 _143642 _143649 r x y).
Proof. exact (MK_COMB (@lem8099176) (@lem8099186 _143642 _143649 r x y)). Qed.
Lemma lem8099188 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term234 _143642 _143649 r x) = (term651 _143642 _143649 r x).
Proof. exact (fun_ext (fun y : _143642 => @lem8099187 _143642 _143649 r x y)). Qed.
Lemma lem8099189 {_143642 : Type'} : (@all _143642) = (@all _143642).
Proof. exact (eq_refl (@all _143642)). Qed.
Lemma lem8099190 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term235 _143642 _143649 r x) = (term652 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8099189 _143642) (@lem8099188 _143642 _143649 r x)). Qed.
Lemma lem8099191 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8099192 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term251 _143642 _143649 r x) = (term653 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8099191) (@lem8099190 _143642 _143649 r x)). Qed.
Lemma lem8099193 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term512 _143642 _143649 r s x _107385) = (term654 _143642 _143649 r s x _107385).
Proof. exact (MK_COMB (@lem8099192 _143642 _143649 r x) (@lem8099175 _143642 _143649 s x _107385)). Qed.
Lemma lem8099202 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term246 _143642 _143649 r x) = (term246 _143642 _143649 r x).
Proof. exact (eq_refl (term246 _143642 _143649 r x)). Qed.
Lemma lem8099203 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term538 _143642 _143649 r s x _107385) = (term655 _143642 _143649 r s x _107385).
Proof. exact (MK_COMB (@lem8099202 _143642 _143649 r x) (@lem8099193 _143642 _143649 r s x _107385)). Qed.
Lemma lem8099222 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term499 _143642 _143649 s x _107385) = (term499 _143642 _143649 s x _107385).
Proof. exact (eq_refl (term499 _143642 _143649 s x _107385)). Qed.
Lemma lem8099223 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8099230 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8099231 {_143642 : Type'} (f : _143642 -> Prop) (x : _143642) : (f x) = (@I (_143642 -> Prop) f x).
Proof. exact (@lem8099230 _143642 Prop f x). Qed.
Lemma lem8099233 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (y : _143642) : (r x y) = (term649 _143642 _143649 r x y).
Proof. exact (@lem8099231 _143642 (r x) y). Qed.
Lemma lem8099234 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (y : _143642) : (term232 _143642 _143649 r x y) = (term650 _143642 _143649 r x y).
Proof. exact (MK_COMB (@lem8099223) (@lem8099233 _143642 _143649 r x y)). Qed.
Lemma lem8099235 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term234 _143642 _143649 r x) = (term651 _143642 _143649 r x).
Proof. exact (fun_ext (fun y : _143642 => @lem8099234 _143642 _143649 r x y)). Qed.
Lemma lem8099236 {_143642 : Type'} : (@all _143642) = (@all _143642).
Proof. exact (eq_refl (@all _143642)). Qed.
Lemma lem8099237 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term235 _143642 _143649 r x) = (term652 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8099236 _143642) (@lem8099235 _143642 _143649 r x)). Qed.
Lemma lem8099238 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8099239 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term251 _143642 _143649 r x) = (term653 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8099238) (@lem8099237 _143642 _143649 r x)). Qed.
Lemma lem8099240 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term512 _143642 _143649 r s x _107385) = (term654 _143642 _143649 r s x _107385).
Proof. exact (MK_COMB (@lem8099239 _143642 _143649 r x) (@lem8099222 _143642 _143649 s x _107385)). Qed.
Lemma lem8099247 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term256 _143642 _143649 r x) = (term256 _143642 _143649 r x).
Proof. exact (eq_refl (term256 _143642 _143649 r x)). Qed.
Lemma lem8099248 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term525 _143642 _143649 r s x _107385) = (term656 _143642 _143649 r s x _107385).
Proof. exact (MK_COMB (@lem8099247 _143642 _143649 r x) (@lem8099240 _143642 _143649 r s x _107385)). Qed.
Lemma lem8099249 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8099250 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term575 _143642 _143649 r s x _107385) = (term657 _143642 _143649 r s x _107385).
Proof. exact (MK_COMB (@lem8099249) (@lem8099248 _143642 _143649 r s x _107385)). Qed.
Lemma lem8099251 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term577 _143642 _143649 r s x _107385) = (term658 _143642 _143649 r s x _107385).
Proof. exact (MK_COMB (@lem8099250 _143642 _143649 r s x _107385) (@lem8099203 _143642 _143649 r s x _107385)). Qed.
Lemma lem8099260 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term246 _143642 _143649 s x) = (term246 _143642 _143649 s x).
Proof. exact (eq_refl (term246 _143642 _143649 s x)). Qed.
Lemma lem8099261 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term604 _143642 _143649 r s x _107385) = (term659 _143642 _143649 r s x _107385).
Proof. exact (MK_COMB (@lem8099260 _143642 _143649 s x) (@lem8099251 _143642 _143649 r s x _107385)). Qed.
Lemma lem8099282 {_143642 _143649 : Type'} (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term377 _143642 _143649 _107385 s x) = (term377 _143642 _143649 _107385 s x).
Proof. exact (eq_refl (term377 _143642 _143649 _107385 s x)). Qed.
Lemma lem8099283 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8099290 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8099291 {_143642 : Type'} (f : _143642 -> Prop) (x : _143642) : (f x) = (@I (_143642 -> Prop) f x).
Proof. exact (@lem8099290 _143642 Prop f x). Qed.
Lemma lem8099293 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (y : _143642) : (r x y) = (term649 _143642 _143649 r x y).
Proof. exact (@lem8099291 _143642 (r x) y). Qed.
Lemma lem8099294 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (y : _143642) : (term232 _143642 _143649 r x y) = (term650 _143642 _143649 r x y).
Proof. exact (MK_COMB (@lem8099283) (@lem8099293 _143642 _143649 r x y)). Qed.
Lemma lem8099295 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term234 _143642 _143649 r x) = (term651 _143642 _143649 r x).
Proof. exact (fun_ext (fun y : _143642 => @lem8099294 _143642 _143649 r x y)). Qed.
Lemma lem8099296 {_143642 : Type'} : (@all _143642) = (@all _143642).
Proof. exact (eq_refl (@all _143642)). Qed.
Lemma lem8099297 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term235 _143642 _143649 r x) = (term652 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8099296 _143642) (@lem8099295 _143642 _143649 r x)). Qed.
Lemma lem8099298 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8099299 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term251 _143642 _143649 r x) = (term653 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8099298) (@lem8099297 _143642 _143649 r x)). Qed.
Lemma lem8099300 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term390 _143642 _143649 r _107385 s x) = (term660 _143642 _143649 r _107385 s x).
Proof. exact (MK_COMB (@lem8099299 _143642 _143649 r x) (@lem8099282 _143642 _143649 _107385 s x)). Qed.
Lemma lem8099309 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term246 _143642 _143649 r x) = (term246 _143642 _143649 r x).
Proof. exact (eq_refl (term246 _143642 _143649 r x)). Qed.
Lemma lem8099310 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term416 _143642 _143649 r _107385 s x) = (term661 _143642 _143649 r _107385 s x).
Proof. exact (MK_COMB (@lem8099309 _143642 _143649 r x) (@lem8099300 _143642 _143649 r _107385 s x)). Qed.
Lemma lem8099331 {_143642 _143649 : Type'} (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term377 _143642 _143649 _107385 s x) = (term377 _143642 _143649 _107385 s x).
Proof. exact (eq_refl (term377 _143642 _143649 _107385 s x)). Qed.
Lemma lem8099332 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8099339 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8099340 {_143642 : Type'} (f : _143642 -> Prop) (x : _143642) : (f x) = (@I (_143642 -> Prop) f x).
Proof. exact (@lem8099339 _143642 Prop f x). Qed.
Lemma lem8099342 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (y : _143642) : (r x y) = (term649 _143642 _143649 r x y).
Proof. exact (@lem8099340 _143642 (r x) y). Qed.
Lemma lem8099343 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (y : _143642) : (term232 _143642 _143649 r x y) = (term650 _143642 _143649 r x y).
Proof. exact (MK_COMB (@lem8099332) (@lem8099342 _143642 _143649 r x y)). Qed.
Lemma lem8099344 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term234 _143642 _143649 r x) = (term651 _143642 _143649 r x).
Proof. exact (fun_ext (fun y : _143642 => @lem8099343 _143642 _143649 r x y)). Qed.
Lemma lem8099345 {_143642 : Type'} : (@all _143642) = (@all _143642).
Proof. exact (eq_refl (@all _143642)). Qed.
Lemma lem8099346 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term235 _143642 _143649 r x) = (term652 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8099345 _143642) (@lem8099344 _143642 _143649 r x)). Qed.
Lemma lem8099347 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8099348 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term251 _143642 _143649 r x) = (term653 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8099347) (@lem8099346 _143642 _143649 r x)). Qed.
Lemma lem8099349 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term390 _143642 _143649 r _107385 s x) = (term660 _143642 _143649 r _107385 s x).
Proof. exact (MK_COMB (@lem8099348 _143642 _143649 r x) (@lem8099331 _143642 _143649 _107385 s x)). Qed.
Lemma lem8099356 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term256 _143642 _143649 r x) = (term256 _143642 _143649 r x).
Proof. exact (eq_refl (term256 _143642 _143649 r x)). Qed.
Lemma lem8099357 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term403 _143642 _143649 r _107385 s x) = (term662 _143642 _143649 r _107385 s x).
Proof. exact (MK_COMB (@lem8099356 _143642 _143649 r x) (@lem8099349 _143642 _143649 r _107385 s x)). Qed.
Lemma lem8099358 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8099359 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term453 _143642 _143649 r _107385 s x) = (term663 _143642 _143649 r _107385 s x).
Proof. exact (MK_COMB (@lem8099358) (@lem8099357 _143642 _143649 r _107385 s x)). Qed.
Lemma lem8099360 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term455 _143642 _143649 r _107385 s x) = (term664 _143642 _143649 r _107385 s x).
Proof. exact (MK_COMB (@lem8099359 _143642 _143649 r _107385 s x) (@lem8099310 _143642 _143649 r _107385 s x)). Qed.
Lemma lem8099367 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term256 _143642 _143649 s x) = (term256 _143642 _143649 s x).
Proof. exact (eq_refl (term256 _143642 _143649 s x)). Qed.
Lemma lem8099368 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term484 _143642 _143649 r _107385 s x) = (term665 _143642 _143649 r _107385 s x).
Proof. exact (MK_COMB (@lem8099367 _143642 _143649 s x) (@lem8099360 _143642 _143649 r _107385 s x)). Qed.
Lemma lem8099369 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8099370 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) : (term641 _143642 _143649 r _107385 s x) = (term666 _143642 _143649 r _107385 s x).
Proof. exact (MK_COMB (@lem8099369) (@lem8099368 _143642 _143649 r _107385 s x)). Qed.
Lemma lem8099371 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) : (term643 _143642 _143649 r s x _107385) = (term667 _143642 _143649 r s x _107385).
Proof. exact (MK_COMB (@lem8099370 _143642 _143649 r _107385 s x) (@lem8099261 _143642 _143649 r s x _107385)). Qed.
Lemma lem8099372 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) (h1 : term643 _143642 _143649 r s x _107385) : term667 _143642 _143649 r s x _107385.
Proof. exact (EQ_MP (@lem8099371 _143642 _143649 r s x _107385) (@lem8099156 _143642 _143649 r s x _107385 h1)). Qed.
Lemma lem8099373 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) (h1 : term665 _143642 _143649 r _107385 s x) : term665 _143642 _143649 r _107385 s x.
Proof. exact (h1). Qed.
Lemma lem8099374 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) (h1 : term659 _143642 _143649 r s x _107385) : term659 _143642 _143649 r s x _107385.
Proof. exact (h1). Qed.
Lemma lem8099375 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) (h1 : term665 _143642 _143649 r _107385 s x) : term664 _143642 _143649 r _107385 s x.
Proof. exact (proj2 (@lem8099373 _143642 _143649 r _107385 s x h1)). Qed.
Lemma lem8099377 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) (h1 : term662 _143642 _143649 r _107385 s x) : term662 _143642 _143649 r _107385 s x.
Proof. exact (h1). Qed.
Lemma lem8099378 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) (h1 : term661 _143642 _143649 r _107385 s x) : term661 _143642 _143649 r _107385 s x.
Proof. exact (h1). Qed.
Lemma lem8099379 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) (h1 : term662 _143642 _143649 r _107385 s x) : term660 _143642 _143649 r _107385 s x.
Proof. exact (proj2 (@lem8099377 _143642 _143649 r _107385 s x h1)). Qed.
Lemma lem8099381 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) (h1 : term662 _143642 _143649 r _107385 s x) : term377 _143642 _143649 _107385 s x.
Proof. exact (proj2 (@lem8099379 _143642 _143649 r _107385 s x h1)). Qed.
Lemma lem8099385 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) (h1 : term661 _143642 _143649 r _107385 s x) : term660 _143642 _143649 r _107385 s x.
Proof. exact (proj2 (@lem8099378 _143642 _143649 r _107385 s x h1)). Qed.
Lemma lem8099387 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) (h1 : term661 _143642 _143649 r _107385 s x) : term377 _143642 _143649 _107385 s x.
Proof. exact (proj2 (@lem8099385 _143642 _143649 r _107385 s x h1)). Qed.
Lemma lem8099391 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) (h1 : term659 _143642 _143649 r s x _107385) : term658 _143642 _143649 r s x _107385.
Proof. exact (proj2 (@lem8099374 _143642 _143649 r s x _107385 h1)). Qed.
Lemma lem8099393 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) (h1 : term656 _143642 _143649 r s x _107385) : term656 _143642 _143649 r s x _107385.
Proof. exact (h1). Qed.
Lemma lem8099394 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) (h1 : term655 _143642 _143649 r s x _107385) : term655 _143642 _143649 r s x _107385.
Proof. exact (h1). Qed.
Lemma lem8099395 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) (h1 : term656 _143642 _143649 r s x _107385) : term654 _143642 _143649 r s x _107385.
Proof. exact (proj2 (@lem8099393 _143642 _143649 r s x _107385 h1)). Qed.
Lemma lem8099397 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) (h1 : term656 _143642 _143649 r s x _107385) : term499 _143642 _143649 s x _107385.
Proof. exact (proj2 (@lem8099395 _143642 _143649 r s x _107385 h1)). Qed.
Lemma lem8099401 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) (h1 : term655 _143642 _143649 r s x _107385) : term654 _143642 _143649 r s x _107385.
Proof. exact (proj2 (@lem8099394 _143642 _143649 r s x _107385 h1)). Qed.
Lemma lem8099403 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) (h1 : term655 _143642 _143649 r s x _107385) : term499 _143642 _143649 s x _107385.
Proof. exact (proj2 (@lem8099401 _143642 _143649 r s x _107385 h1)). Qed.
Lemma lem8099518 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) (h1 : term662 _143642 _143649 r _107385 s x) : term113 _143642 _143649 s x.
Proof. exact (proj1 (@lem8099381 _143642 _143649 r _107385 s x h1)). Qed.
Lemma lem8099528 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) (h1 : term661 _143642 _143649 r _107385 s x) : term113 _143642 _143649 s x.
Proof. exact (proj1 (@lem8099387 _143642 _143649 r _107385 s x h1)). Qed.
Lemma lem8099532 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) (h1 : term659 _143642 _143649 r s x _107385) : term113 _143642 _143649 s x.
Proof. exact (proj1 (@lem8099374 _143642 _143649 r s x _107385 h1)). Qed.
Lemma lem8099542 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) (h1 : term659 _143642 _143649 r s x _107385) : term113 _143642 _143649 s x.
Proof. exact (proj1 (@lem8099374 _143642 _143649 r s x _107385 h1)). Qed.
Lemma lem8099613 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) (h1 : term665 _143642 _143649 r _107385 s x) : term66 _143642 _143649 s x.
Proof. exact (proj1 (@lem8099373 _143642 _143649 r _107385 s x h1)). Qed.
Lemma lem8099614 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) (h1 : term665 _143642 _143649 r _107385 s x) : term668 _143642 _143649 s x.
Proof. exact (fun h0 : term113 _143642 _143649 s x => @lem8099613 _143642 _143649 r _107385 s x h1). Qed.
Lemma lem8099616 (p : Prop) : (term669 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8099617 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term668 _143642 _143649 s x) = (term66 _143642 _143649 s x).
Proof. exact (@lem8099616 (term66 _143642 _143649 s x)). Qed.
Lemma lem8099618 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) (h1 : term665 _143642 _143649 r _107385 s x) : term66 _143642 _143649 s x.
Proof. exact (EQ_MP (@lem8099617 _143642 _143649 s x) (@lem8099614 _143642 _143649 r _107385 s x h1)). Qed.
Lemma lem8099621 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8099623 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term113 _143642 _143649 s x) = (term670 _143642 _143649 s x).
Proof. exact (@lem8099621 (term66 _143642 _143649 s x)). Qed.
Lemma lem8099626 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) (h1 : term662 _143642 _143649 r _107385 s x) : term670 _143642 _143649 s x.
Proof. exact (EQ_MP (@lem8099623 _143642 _143649 s x) (@lem8099518 _143642 _143649 r _107385 s x h1)). Qed.
Lemma lem8099629 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) (h1 : term662 _143642 _143649 r _107385 s x) (h2 : term665 _143642 _143649 r _107385 s x) : False.
Proof. exact (@lem8099626 _143642 _143649 r _107385 s x h1 (@lem8099618 _143642 _143649 r _107385 s x h2)). Qed.
Lemma lem8099630 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) (h1 : term662 _143642 _143649 r _107385 s x) (h2 : term665 _143642 _143649 r _107385 s x) : term671.
Proof. exact (fun h0 : ~ False => @lem8099629 _143642 _143649 r _107385 s x h1 h2). Qed.
Lemma lem8099632 (p : Prop) : (term669 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8099633 : term671 = False.
Proof. exact (@lem8099632 False). Qed.
Lemma lem8099634 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) (h1 : term662 _143642 _143649 r _107385 s x) (h2 : term665 _143642 _143649 r _107385 s x) : False.
Proof. exact (EQ_MP (@lem8099633) (@lem8099630 _143642 _143649 r _107385 s x h1 h2)). Qed.
Lemma lem8099697 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) (h1 : term665 _143642 _143649 r _107385 s x) : term66 _143642 _143649 s x.
Proof. exact (proj1 (@lem8099373 _143642 _143649 r _107385 s x h1)). Qed.
Lemma lem8099698 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) (h1 : term665 _143642 _143649 r _107385 s x) : term668 _143642 _143649 s x.
Proof. exact (fun h0 : term113 _143642 _143649 s x => @lem8099697 _143642 _143649 r _107385 s x h1). Qed.
Lemma lem8099700 (p : Prop) : (term669 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8099701 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term668 _143642 _143649 s x) = (term66 _143642 _143649 s x).
Proof. exact (@lem8099700 (term66 _143642 _143649 s x)). Qed.
Lemma lem8099702 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) (h1 : term665 _143642 _143649 r _107385 s x) : term66 _143642 _143649 s x.
Proof. exact (EQ_MP (@lem8099701 _143642 _143649 s x) (@lem8099698 _143642 _143649 r _107385 s x h1)). Qed.
Lemma lem8099705 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8099707 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term113 _143642 _143649 s x) = (term670 _143642 _143649 s x).
Proof. exact (@lem8099705 (term66 _143642 _143649 s x)). Qed.
Lemma lem8099710 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) (h1 : term661 _143642 _143649 r _107385 s x) : term670 _143642 _143649 s x.
Proof. exact (EQ_MP (@lem8099707 _143642 _143649 s x) (@lem8099528 _143642 _143649 r _107385 s x h1)). Qed.
Lemma lem8099713 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) (h1 : term665 _143642 _143649 r _107385 s x) (h2 : term661 _143642 _143649 r _107385 s x) : False.
Proof. exact (@lem8099710 _143642 _143649 r _107385 s x h2 (@lem8099702 _143642 _143649 r _107385 s x h1)). Qed.
Lemma lem8099714 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) (h1 : term665 _143642 _143649 r _107385 s x) (h2 : term661 _143642 _143649 r _107385 s x) : term671.
Proof. exact (fun h0 : ~ False => @lem8099713 _143642 _143649 r _107385 s x h1 h2). Qed.
Lemma lem8099716 (p : Prop) : (term669 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8099717 : term671 = False.
Proof. exact (@lem8099716 False). Qed.
Lemma lem8099718 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) (h1 : term665 _143642 _143649 r _107385 s x) (h2 : term661 _143642 _143649 r _107385 s x) : False.
Proof. exact (EQ_MP (@lem8099717) (@lem8099714 _143642 _143649 r _107385 s x h1 h2)). Qed.
Lemma lem8099781 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) (h1 : term656 _143642 _143649 r s x _107385) : term66 _143642 _143649 s x.
Proof. exact (proj1 (@lem8099397 _143642 _143649 r s x _107385 h1)). Qed.
Lemma lem8099782 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) (h1 : term656 _143642 _143649 r s x _107385) : term668 _143642 _143649 s x.
Proof. exact (fun h0 : term113 _143642 _143649 s x => @lem8099781 _143642 _143649 r s x _107385 h1). Qed.
Lemma lem8099784 (p : Prop) : (term669 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8099785 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term668 _143642 _143649 s x) = (term66 _143642 _143649 s x).
Proof. exact (@lem8099784 (term66 _143642 _143649 s x)). Qed.
Lemma lem8099786 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) (h1 : term656 _143642 _143649 r s x _107385) : term66 _143642 _143649 s x.
Proof. exact (EQ_MP (@lem8099785 _143642 _143649 s x) (@lem8099782 _143642 _143649 r s x _107385 h1)). Qed.
Lemma lem8099789 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8099791 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term113 _143642 _143649 s x) = (term670 _143642 _143649 s x).
Proof. exact (@lem8099789 (term66 _143642 _143649 s x)). Qed.
Lemma lem8099794 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) (h1 : term659 _143642 _143649 r s x _107385) : term670 _143642 _143649 s x.
Proof. exact (EQ_MP (@lem8099791 _143642 _143649 s x) (@lem8099532 _143642 _143649 r s x _107385 h1)). Qed.
Lemma lem8099797 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) (h1 : term656 _143642 _143649 r s x _107385) (h2 : term659 _143642 _143649 r s x _107385) : False.
Proof. exact (@lem8099794 _143642 _143649 r s x _107385 h2 (@lem8099786 _143642 _143649 r s x _107385 h1)). Qed.
Lemma lem8099798 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) (h1 : term656 _143642 _143649 r s x _107385) (h2 : term659 _143642 _143649 r s x _107385) : term671.
Proof. exact (fun h0 : ~ False => @lem8099797 _143642 _143649 r s x _107385 h1 h2). Qed.
Lemma lem8099800 (p : Prop) : (term669 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8099801 : term671 = False.
Proof. exact (@lem8099800 False). Qed.
Lemma lem8099802 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) (h1 : term656 _143642 _143649 r s x _107385) (h2 : term659 _143642 _143649 r s x _107385) : False.
Proof. exact (EQ_MP (@lem8099801) (@lem8099798 _143642 _143649 r s x _107385 h1 h2)). Qed.
Lemma lem8099865 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) (h1 : term655 _143642 _143649 r s x _107385) : term66 _143642 _143649 s x.
Proof. exact (proj1 (@lem8099403 _143642 _143649 r s x _107385 h1)). Qed.
Lemma lem8099866 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) (h1 : term655 _143642 _143649 r s x _107385) : term668 _143642 _143649 s x.
Proof. exact (fun h0 : term113 _143642 _143649 s x => @lem8099865 _143642 _143649 r s x _107385 h1). Qed.
Lemma lem8099868 (p : Prop) : (term669 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8099869 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term668 _143642 _143649 s x) = (term66 _143642 _143649 s x).
Proof. exact (@lem8099868 (term66 _143642 _143649 s x)). Qed.
Lemma lem8099870 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) (h1 : term655 _143642 _143649 r s x _107385) : term66 _143642 _143649 s x.
Proof. exact (EQ_MP (@lem8099869 _143642 _143649 s x) (@lem8099866 _143642 _143649 r s x _107385 h1)). Qed.
Lemma lem8099873 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8099875 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term113 _143642 _143649 s x) = (term670 _143642 _143649 s x).
Proof. exact (@lem8099873 (term66 _143642 _143649 s x)). Qed.
Lemma lem8099878 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) (h1 : term659 _143642 _143649 r s x _107385) : term670 _143642 _143649 s x.
Proof. exact (EQ_MP (@lem8099875 _143642 _143649 s x) (@lem8099542 _143642 _143649 r s x _107385 h1)). Qed.
Lemma lem8099881 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) (h1 : term655 _143642 _143649 r s x _107385) (h2 : term659 _143642 _143649 r s x _107385) : False.
Proof. exact (@lem8099878 _143642 _143649 r s x _107385 h2 (@lem8099870 _143642 _143649 r s x _107385 h1)). Qed.
Lemma lem8099882 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) (h1 : term655 _143642 _143649 r s x _107385) (h2 : term659 _143642 _143649 r s x _107385) : term671.
Proof. exact (fun h0 : ~ False => @lem8099881 _143642 _143649 r s x _107385 h1 h2). Qed.
Lemma lem8099884 (p : Prop) : (term669 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8099885 : term671 = False.
Proof. exact (@lem8099884 False). Qed.
Lemma lem8099886 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) (h1 : term655 _143642 _143649 r s x _107385) (h2 : term659 _143642 _143649 r s x _107385) : False.
Proof. exact (EQ_MP (@lem8099885) (@lem8099882 _143642 _143649 r s x _107385 h1 h2)). Qed.
Lemma lem8099887 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) (h1 : term659 _143642 _143649 r s x _107385) : False.
Proof. exact (or_elim (@lem8099391 _143642 _143649 r s x _107385 h1) (fun h0 : term656 _143642 _143649 r s x _107385 => @lem8099802 _143642 _143649 r s x _107385 h0 h1) (fun h0 : term655 _143642 _143649 r s x _107385 => @lem8099886 _143642 _143649 r s x _107385 h0 h1)). Qed.
Lemma lem8099888 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (_107385 : _143642) (s : type1470 _143642 _143649) (x : _143649) (h1 : term665 _143642 _143649 r _107385 s x) : False.
Proof. exact (or_elim (@lem8099375 _143642 _143649 r _107385 s x h1) (fun h0 : term662 _143642 _143649 r _107385 s x => @lem8099634 _143642 _143649 r _107385 s x h0 h1) (fun h0 : term661 _143642 _143649 r _107385 s x => @lem8099718 _143642 _143649 r _107385 s x h1 h0)). Qed.
Lemma lem8099889 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (_107385 : _143642) (h1 : term643 _143642 _143649 r s x _107385) : False.
Proof. exact (or_elim (@lem8099372 _143642 _143649 r s x _107385 h1) (fun h0 : term665 _143642 _143649 r _107385 s x => @lem8099888 _143642 _143649 r _107385 s x h0) (fun h0 : term659 _143642 _143649 r s x _107385 => @lem8099887 _143642 _143649 r s x _107385 h0)). Qed.
Lemma lem8099890 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : term646 _143642 _143649 r s x) : False.
Proof. exact (ex_elim (@lem8099155 _143642 _143649 r s x h1) (fun _107385 : _143642 => fun h0 : term645 _143642 _143649 r s x _107385 => @lem8099889 _143642 _143649 r s x _107385 h0)). Qed.
Lemma lem8099891 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) (h1 : term225 _143642 _143649 s x) : False.
Proof. exact (ex_elim (@lem8099154 _143642 _143649 s x h1) (fun r : type1470 _143642 _143649 => fun h0 : term647 _143642 _143649 s x r => @lem8099890 _143642 _143649 r s x h0)). Qed.
Lemma lem8099892 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) (h1 : term225 _143642 _143649 s x) : (term225 _143642 _143649 s x) = False.
Proof. exact (prop_ext (fun h2 : term225 _143642 _143649 s x => @lem8099891 _143642 _143649 s x h1) (fun h2 : False => @lem8098097 _143642 _143649 s x h1)). Qed.
Lemma lem8099893 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) (h1 : term225 _143642 _143649 s x) : False.
Proof. exact (EQ_MP (@lem8099892 _143642 _143649 s x h1) (@lem8098097 _143642 _143649 s x h1)). Qed.
Lemma lem8099894 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : term224 _143642 _143649 s x.
Proof. exact (fun h0 : term225 _143642 _143649 s x => @lem8099893 _143642 _143649 s x h0). Qed.
Lemma lem8099895 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : term218 _143642 _143649 s x.
Proof. exact (EQ_MP (@lem8098096 _143642 _143649 s x) (@lem8099894 _143642 _143649 s x)). Qed.
Lemma lem8099900 {_143642 _143649 : Type'} (x : _143649) : term221 _143642 _143649 x.
Proof. exact (fun s : type1470 _143642 _143649 => @lem8099895 _143642 _143649 s x). Qed.
Lemma lem8099905 {_143642 _143649 : Type'} : term223 _143642 _143649.
Proof. exact (fun x : _143649 => @lem8099900 _143642 _143649 x). Qed.
Lemma lem8099906 {_143642 _143649 : Type'} : term64 _143642 _143649.
Proof. exact (EQ_MP (@lem8098092 _143642 _143649) (@lem8099905 _143642 _143649)). Qed.
Lemma lem8099907 {_143642 _143649 : Type'} (x : _143649) : term672 _143642 _143649 x.
Proof. exact (@lem8099906 _143642 _143649 x). Qed.
Lemma lem8099908 {_143642 _143649 : Type'} (x : _143649) : (term672 _143642 _143649 x) = (term60 _143642 _143649 x).
Proof. exact (eq_refl (term672 _143642 _143649 x)). Qed.
Lemma lem8099909 {_143642 _143649 : Type'} (x : _143649) : term60 _143642 _143649 x.
Proof. exact (EQ_MP (@lem8099908 _143642 _143649 x) (@lem8099907 _143642 _143649 x)). Qed.
Lemma lem8099910 {_143642 _143649 : Type'} (x : _143649) (s : type1470 _143642 _143649) : term673 _143642 _143649 x s.
Proof. exact (@lem8099909 _143642 _143649 x s). Qed.
Lemma lem8099911 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term673 _143642 _143649 x s) = (term56 _143642 _143649 s x).
Proof. exact (eq_refl (term673 _143642 _143649 x s)). Qed.
Lemma lem8099912 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : term56 _143642 _143649 s x.
Proof. exact (EQ_MP (@lem8099911 _143642 _143649 s x) (@lem8099910 _143642 _143649 x s)). Qed.
Lemma lem8099913 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) (r : type1470 _143642 _143649) : term674 _143642 _143649 s x r.
Proof. exact (@lem8099912 _143642 _143649 s x r). Qed.
Lemma lem8099914 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term674 _143642 _143649 s x r) = (term35 _143642 _143649 r s x).
Proof. exact (eq_refl (term674 _143642 _143649 s x r)). Qed.
Lemma lem8099915 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : term35 _143642 _143649 r s x.
Proof. exact (EQ_MP (@lem8099914 _143642 _143649 r s x) (@lem8099913 _143642 _143649 s x r)). Qed.
Lemma lem8099917 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : term3 _143642 _143649 r s x.
Proof. exact (@lem8096395 _143642 _143649 r s x (@lem8099915 _143642 _143649 r s x)). Qed.
Lemma lem8099918 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : term4 _143642 _143649 r s x) : False.
Proof. exact (@lem8099917 _143642 _143649 r s x (@lem8096299 _143642 _143649 r s x h1)). Qed.
Lemma lem8099919 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : term4 _143642 _143649 r s x) : (term4 _143642 _143649 r s x) = False.
Proof. exact (prop_ext (fun h2 : term4 _143642 _143649 r s x => @lem8099918 _143642 _143649 r s x h1) (fun h2 : False => @lem8096299 _143642 _143649 r s x h1)). Qed.
Lemma lem8099920 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) (h1 : term4 _143642 _143649 r s x) : False.
Proof. exact (EQ_MP (@lem8099919 _143642 _143649 r s x h1) (@lem8096299 _143642 _143649 r s x h1)). Qed.
Lemma lem8099921 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : term3 _143642 _143649 r s x.
Proof. exact (fun h0 : term4 _143642 _143649 r s x => @lem8099920 _143642 _143649 r s x h0). Qed.
Lemma lem8099922 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term1 _143642 _143649 r s x) = (term2 _143642 _143649 r s x).
Proof. exact (EQ_MP (@lem8096298 _143642 _143649 r s x) (@lem8099921 _143642 _143649 r s x)). Qed.
