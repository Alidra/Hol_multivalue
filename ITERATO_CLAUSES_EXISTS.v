Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ITERATO_CLAUSES_EXISTS_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import ITERATO_SUPPORT_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm13473_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm1812_spec.
Require Import thm1813_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1834_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1844_spec.
Require Import thm1845_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18946_spec.
Require Import thm18947_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm19490_spec.
Require Import thm19732_spec.
Require Import thm19792_spec.
Require Import thm20230_spec.
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
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211701_spec.
Require Import thm3211702_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm3399706_spec.
Require Import thm3399757_spec.
Require Import thm4211_spec.
Require Import thm51_spec.
Require Import thm57691_spec.
Require Import thm57692_spec.
Require Import thm57694_spec.
Require Import thm57695_spec.
Require Import thm6401305_spec.
Require Import thm68127_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm9396_spec.
Lemma lem6779353 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6779354 {_125019 : Type'} (t : _125019) (i : _125019) (P : _125019 -> Prop) : (term1 _125019 t i P) = (term2 _125019 t i P).
Proof. exact (@lem6779353 (term1 _125019 t i P)). Qed.
Lemma lem6779355 {_125019 : Type'} (t : _125019) (i : _125019) (P : _125019 -> Prop) : (term2 _125019 t i P) = (term1 _125019 t i P).
Proof. exact (SYM (@lem6779354 _125019 t i P)). Qed.
Lemma lem6779356 {_125019 : Type'} (t : _125019) (i : _125019) (P : _125019 -> Prop) (h1 : term3 _125019 t i P) : term3 _125019 t i P.
Proof. exact (h1). Qed.
Lemma lem6779359 {_125019 : Type'} (t : _125019) (i : _125019) (P : _125019 -> Prop) (h1 : term2 _125019 t i P) : term2 _125019 t i P.
Proof. exact (h1). Qed.
Lemma lem6779360 {_125019 : Type'} (t : _125019) (i : _125019) (P : _125019 -> Prop) : term4 _125019 t i P.
Proof. exact (fun h0 : term2 _125019 t i P => @lem6779359 _125019 t i P h0). Qed.
Lemma lem6779361 {_125019 : Type'} (t : _125019) (i : _125019) (P : _125019 -> Prop) (h1 : term4 _125019 t i P) : term4 _125019 t i P.
Proof. exact (h1). Qed.
Lemma lem6779362 {_125019 : Type'} (t : _125019) (i : _125019) (P : _125019 -> Prop) (h1 : term2 _125019 t i P) : term2 _125019 t i P.
Proof. exact (h1). Qed.
Lemma lem6779363 {_125019 : Type'} (t : _125019) (i : _125019) (P : _125019 -> Prop) (h1 : term2 _125019 t i P) (h2 : term4 _125019 t i P) : term2 _125019 t i P.
Proof. exact (@lem6779361 _125019 t i P h2 (@lem6779362 _125019 t i P h1)). Qed.
Lemma lem6779364 {_125019 : Type'} (t : _125019) (i : _125019) (P : _125019 -> Prop) (h1 : term2 _125019 t i P) : term5 _125019 t i P.
Proof. exact (fun h0 : term4 _125019 t i P => @lem6779363 _125019 t i P h1 h0). Qed.
Lemma lem6779365 {_125019 : Type'} (t : _125019) (i : _125019) (P : _125019 -> Prop) (h1 : term4 _125019 t i P) : term4 _125019 t i P.
Proof. exact (h1). Qed.
Lemma lem6779366 {_125019 : Type'} (t : _125019) (i : _125019) (P : _125019 -> Prop) (h1 : term2 _125019 t i P) (h2 : term4 _125019 t i P) : term2 _125019 t i P.
Proof. exact (@lem6779364 _125019 t i P h1 (@lem6779365 _125019 t i P h2)). Qed.
Lemma lem6779367 {_125019 : Type'} (t : _125019) (i : _125019) (P : _125019 -> Prop) (h1 : term4 _125019 t i P) : term4 _125019 t i P.
Proof. exact (fun h0 : term2 _125019 t i P => @lem6779366 _125019 t i P h0 h1). Qed.
Lemma lem6779368 {_125019 : Type'} (t : _125019) (i : _125019) (P : _125019 -> Prop) : term6 _125019 t i P.
Proof. exact (fun h0 : term4 _125019 t i P => @lem6779367 _125019 t i P h0). Qed.
Lemma lem6779371 {_125019 : Type'} (t : _125019) (i : _125019) (P : _125019 -> Prop) : term4 _125019 t i P.
Proof. exact (@lem6779368 _125019 t i P (@lem6779360 _125019 t i P)). Qed.
Lemma lem6779372 {_125019 : Type'} (t : _125019) (i : _125019) (P : _125019 -> Prop) : term4 _125019 t i P.
Proof. exact (@lem6779371 _125019 t i P). Qed.
Lemma lem6779386 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem6779387 {_125019 : Type'} (t : _125019) (i : _125019) (P : _125019 -> Prop) : (term2 _125019 t i P) = (term7 _125019 t i P).
Proof. exact (@lem6779386 (term3 _125019 t i P)). Qed.
Lemma lem6779389 (t : Prop) : (term8 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem6779390 {_125019 : Type'} (t : _125019) (i : _125019) (P : _125019 -> Prop) : (term7 _125019 t i P) = (term1 _125019 t i P).
Proof. exact (@lem6779389 (term1 _125019 t i P)). Qed.
Lemma lem6779393 {_125019 : Type'} (t : _125019) (i : _125019) (P : _125019 -> Prop) : (term2 _125019 t i P) = (term1 _125019 t i P).
Proof. exact (TRANS (@lem6779387 _125019 t i P) (@lem6779390 _125019 t i P)). Qed.
Lemma lem6779402 {_125019 : Type'} (i : _125019) (P : _125019 -> Prop) : (term9 _125019 i P) = (term10 _125019 i P).
Proof. exact (fun_ext (fun t : _125019 => @lem6779393 _125019 t i P)). Qed.
Lemma lem6779403 {_125019 : Type'} : (@all _125019) = (@all _125019).
Proof. exact (eq_refl (@all _125019)). Qed.
Lemma lem6779404 {_125019 : Type'} (i : _125019) (P : _125019 -> Prop) : (term11 _125019 i P) = (term12 _125019 i P).
Proof. exact (MK_COMB (@lem6779403 _125019) (@lem6779402 _125019 i P)). Qed.
Lemma lem6779409 {_125019 : Type'} (P : _125019 -> Prop) : (term13 _125019 P) = (term14 _125019 P).
Proof. exact (fun_ext (fun i : _125019 => @lem6779404 _125019 i P)). Qed.
Lemma lem6779410 {_125019 : Type'} : (@all _125019) = (@all _125019).
Proof. exact (eq_refl (@all _125019)). Qed.
Lemma lem6779411 {_125019 : Type'} (P : _125019 -> Prop) : (term15 _125019 P) = (term16 _125019 P).
Proof. exact (MK_COMB (@lem6779410 _125019) (@lem6779409 _125019 P)). Qed.
Lemma lem6779416 {_125019 : Type'} : (term17 _125019) = (term18 _125019).
Proof. exact (fun_ext (fun P : _125019 -> Prop => @lem6779411 _125019 P)). Qed.
Lemma lem6779417 {_125019 : Type'} : (@all (_125019 -> Prop)) = (@all (_125019 -> Prop)).
Proof. exact (eq_refl (@all (_125019 -> Prop))). Qed.
Lemma lem6779426 {_125019 : Type'} : (term19 _125019) = (term20 _125019).
Proof. exact (MK_COMB (@lem6779417 _125019) (@lem6779416 _125019)). Qed.
Lemma lem6779427 {_125019 : Type'} (P : _125019 -> Prop) (j : _125019) : (P j) = (P j).
Proof. exact (eq_refl (P j)). Qed.
Lemma lem6779428 {_125019 : Type'} (P : _125019 -> Prop) : (term21 _125019 P) = (term21 _125019 P).
Proof. exact (fun_ext (fun j : _125019 => @lem6779427 _125019 P j)). Qed.
Lemma lem6779429 {_125019 : Type'} : (@ex _125019) = (@ex _125019).
Proof. exact (eq_refl (@ex _125019)). Qed.
Lemma lem6779430 {_125019 : Type'} (P : _125019 -> Prop) : (term22 _125019 P) = (term22 _125019 P).
Proof. exact (MK_COMB (@lem6779429 _125019) (@lem6779428 _125019 P)). Qed.
Lemma lem6779437 {_125019 : Type'} (t : _125019) (P : _125019 -> Prop) (i : _125019) : (term23 _125019 t P i) = (term23 _125019 t P i).
Proof. exact (eq_refl (term23 _125019 t P i)). Qed.
Lemma lem6779438 {_125019 : Type'} (t : _125019) (i : _125019) (P : _125019 -> Prop) : (term24 _125019 t i P) = (term24 _125019 t i P).
Proof. exact (MK_COMB (@lem6779437 _125019 t P i) (@lem6779430 _125019 P)). Qed.
Lemma lem6779441 {_125019 : Type'} (t : _125019) (i : _125019) : (term25 _125019 t i) = (term25 _125019 t i).
Proof. exact (eq_refl (term25 _125019 t i)). Qed.
Lemma lem6779442 {_125019 : Type'} (t : _125019) (i : _125019) (P : _125019 -> Prop) : (term1 _125019 t i P) = (term1 _125019 t i P).
Proof. exact (MK_COMB (@lem6779441 _125019 t i) (@lem6779438 _125019 t i P)). Qed.
Lemma lem6779443 {_125019 : Type'} (i : _125019) (P : _125019 -> Prop) : (term10 _125019 i P) = (term10 _125019 i P).
Proof. exact (fun_ext (fun t : _125019 => @lem6779442 _125019 t i P)). Qed.
Lemma lem6779444 {_125019 : Type'} : (@all _125019) = (@all _125019).
Proof. exact (eq_refl (@all _125019)). Qed.
Lemma lem6779445 {_125019 : Type'} (i : _125019) (P : _125019 -> Prop) : (term12 _125019 i P) = (term12 _125019 i P).
Proof. exact (MK_COMB (@lem6779444 _125019) (@lem6779443 _125019 i P)). Qed.
Lemma lem6779446 {_125019 : Type'} (P : _125019 -> Prop) : (term14 _125019 P) = (term14 _125019 P).
Proof. exact (fun_ext (fun i : _125019 => @lem6779445 _125019 i P)). Qed.
Lemma lem6779447 {_125019 : Type'} : (@all _125019) = (@all _125019).
Proof. exact (eq_refl (@all _125019)). Qed.
Lemma lem6779448 {_125019 : Type'} (P : _125019 -> Prop) : (term16 _125019 P) = (term16 _125019 P).
Proof. exact (MK_COMB (@lem6779447 _125019) (@lem6779446 _125019 P)). Qed.
Lemma lem6779449 {_125019 : Type'} : (term18 _125019) = (term18 _125019).
Proof. exact (fun_ext (fun P : _125019 -> Prop => @lem6779448 _125019 P)). Qed.
Lemma lem6779450 {_125019 : Type'} : (@all (_125019 -> Prop)) = (@all (_125019 -> Prop)).
Proof. exact (eq_refl (@all (_125019 -> Prop))). Qed.
Lemma lem6779451 {_125019 : Type'} : (term20 _125019) = (term20 _125019).
Proof. exact (MK_COMB (@lem6779450 _125019) (@lem6779449 _125019)). Qed.
Lemma lem6779484 {_125019 : Type'} : (term19 _125019) = (term20 _125019).
Proof. exact (TRANS (@lem6779426 _125019) (@lem6779451 _125019)). Qed.
Lemma lem6779485 {_125019 : Type'} : (term20 _125019) = (term19 _125019).
Proof. exact (SYM (@lem6779484 _125019)). Qed.
Lemma lem6779487 {_125019 : Type'} (t : _125019) (P : _125019 -> Prop) (i : _125019) (h1 : term26 _125019 t P i) : term26 _125019 t P i.
Proof. exact (h1). Qed.
Lemma lem6779489 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6779490 {_125019 : Type'} (P : _125019 -> Prop) : (term22 _125019 P) = (term27 _125019 P).
Proof. exact (@lem6779489 (term22 _125019 P)). Qed.
Lemma lem6779491 {_125019 : Type'} (P : _125019 -> Prop) : (term27 _125019 P) = (term22 _125019 P).
Proof. exact (SYM (@lem6779490 _125019 P)). Qed.
Lemma lem6779492 {_125019 : Type'} (P : _125019 -> Prop) (h1 : term28 _125019 P) : term28 _125019 P.
Proof. exact (h1). Qed.
Lemma lem6779498 {_125019 : Type'} (t : _125019) (i : _125019) (h1 : t = i) : t = i.
Proof. exact (h1). Qed.
Lemma lem6779509 {_125019 : Type'} (t : _125019) (P : _125019 -> Prop) (i : _125019) : (term26 _125019 t P i) = (term29 _125019 t P i).
Proof. exact (@lem17265 (t = i) (P i)). Qed.
Lemma lem6779512 {_125019 : Type'} (P : _125019 -> Prop) : (term30 _125019 P) = (term31 _125019 P).
Proof. exact (@lem18394 _125019 P). Qed.
Lemma lem6779513 {_125019 : Type'} (P : _125019 -> Prop) : (term28 _125019 P) = (term32 _125019 P).
Proof. exact (@lem6779512 _125019 (term21 _125019 P)). Qed.
Lemma lem6779514 {_125019 : Type'} (P : _125019 -> Prop) (j : _125019) : (term33 _125019 P j) = (P j).
Proof. exact (eq_refl (term33 _125019 P j)). Qed.
Lemma lem6779515 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6779517 {_125019 : Type'} (P : _125019 -> Prop) (j : _125019) : (term34 _125019 P j) = (term35 _125019 P j).
Proof. exact (MK_COMB (@lem6779515) (@lem6779514 _125019 P j)). Qed.
Lemma lem6779518 {_125019 : Type'} (P : _125019 -> Prop) : (term36 _125019 P) = (term37 _125019 P).
Proof. exact (fun_ext (fun j : _125019 => @lem6779517 _125019 P j)). Qed.
Lemma lem6779519 {_125019 : Type'} : (@all _125019) = (@all _125019).
Proof. exact (eq_refl (@all _125019)). Qed.
Lemma lem6779520 {_125019 : Type'} (P : _125019 -> Prop) : (term32 _125019 P) = (term31 _125019 P).
Proof. exact (MK_COMB (@lem6779519 _125019) (@lem6779518 _125019 P)). Qed.
Lemma lem6779529 {_125019 : Type'} (P : _125019 -> Prop) : (term28 _125019 P) = (term31 _125019 P).
Proof. exact (TRANS (@lem6779513 _125019 P) (@lem6779520 _125019 P)). Qed.
Lemma lem6779530 {_125019 : Type'} (P : _125019 -> Prop) (h1 : term28 _125019 P) : term31 _125019 P.
Proof. exact (EQ_MP (@lem6779529 _125019 P) (@lem6779492 _125019 P h1)). Qed.
Lemma lem6779536 {_125019 : Type'} (t : _125019) (i : _125019) (h1 : t = i) : t = i.
Proof. exact (h1). Qed.
Lemma lem6779550 {_125019 : Type'} (t : _125019) (P : _125019 -> Prop) (i : _125019) (h1 : term26 _125019 t P i) : term29 _125019 t P i.
Proof. exact (EQ_MP (@lem6779509 _125019 t P i) (@lem6779487 _125019 t P i h1)). Qed.
Lemma lem6779555 {_125019 : Type'} (P : _125019 -> Prop) (j : _125019) : (term35 _125019 P j) = (term35 _125019 P j).
Proof. exact (eq_refl (term35 _125019 P j)). Qed.
Lemma lem6779556 {_125019 : Type'} (P : _125019 -> Prop) : (term37 _125019 P) = (term37 _125019 P).
Proof. exact (fun_ext (fun j : _125019 => @lem6779555 _125019 P j)). Qed.
Lemma lem6779557 {_125019 : Type'} : (@all _125019) = (@all _125019).
Proof. exact (eq_refl (@all _125019)). Qed.
Lemma lem6779558 {_125019 : Type'} (P : _125019 -> Prop) : (term31 _125019 P) = (term31 _125019 P).
Proof. exact (MK_COMB (@lem6779557 _125019) (@lem6779556 _125019 P)). Qed.
Lemma lem6779559 {_125019 : Type'} (P : _125019 -> Prop) (h1 : term28 _125019 P) : term31 _125019 P.
Proof. exact (EQ_MP (@lem6779558 _125019 P) (@lem6779530 _125019 P h1)). Qed.
Lemma lem6779565 {_125019 : Type'} (t : _125019) (i : _125019) (h1 : t = i) : t = i.
Proof. exact (h1). Qed.
Lemma lem6779576 {_125019 : Type'} (t : _125019) (i : _125019) (h1 : term38 _125019 t i) : term38 _125019 t i.
Proof. exact (h1). Qed.
Lemma lem6779582 {_125019 : Type'} (P : _125019 -> Prop) (j : _125019) : (term35 _125019 P j) = (term35 _125019 P j).
Proof. exact (eq_refl (term35 _125019 P j)). Qed.
Lemma lem6779583 {_125019 : Type'} (P : _125019 -> Prop) : (term37 _125019 P) = (term37 _125019 P).
Proof. exact (fun_ext (fun j : _125019 => @lem6779582 _125019 P j)). Qed.
Lemma lem6779584 {_125019 : Type'} : (@all _125019) = (@all _125019).
Proof. exact (eq_refl (@all _125019)). Qed.
Lemma lem6779586 {_125019 : Type'} (P : _125019 -> Prop) : (term31 _125019 P) = (term31 _125019 P).
Proof. exact (MK_COMB (@lem6779584 _125019) (@lem6779583 _125019 P)). Qed.
Lemma lem6779587 {_125019 : Type'} (P : _125019 -> Prop) (h1 : term28 _125019 P) : term31 _125019 P.
Proof. exact (EQ_MP (@lem6779586 _125019 P) (@lem6779559 _125019 P h1)). Qed.
Lemma lem6779591 {_125019 : Type'} (P : _125019 -> Prop) (i : _125019) (h1 : P i) : P i.
Proof. exact (h1). Qed.
Lemma lem6779595 {_125019 : Type'} (_88846 : _125019) (P : _125019 -> Prop) (h1 : term28 _125019 P) : term39 _125019 P _88846.
Proof. exact (@lem6779587 _125019 P h1 _88846). Qed.
Lemma lem6779596 {_125019 : Type'} (P : _125019 -> Prop) (_88846 : _125019) : (term39 _125019 P _88846) = (term35 _125019 P _88846).
Proof. exact (eq_refl (term39 _125019 P _88846)). Qed.
Lemma lem6779599 {_125019 : Type'} (t : _125019) (i : _125019) (h1 : t = i) : t = i.
Proof. exact (h1). Qed.
Lemma lem6779603 {_125019 : Type'} (t : _125019) (i : _125019) (h1 : term38 _125019 t i) : term38 _125019 t i.
Proof. exact (h1). Qed.
Lemma lem6779609 {_125019 : Type'} (P : _125019 -> Prop) (i : _125019) (h1 : P i) : P i.
Proof. exact (h1). Qed.
Lemma lem6779638 {_125019 : Type'} (i : _125019) : (term40 _125019 i) = (term40 _125019 i).
Proof. exact (eq_refl (term40 _125019 i)). Qed.
Lemma lem6779639 {_125019 : Type'} (t : _125019) (i : _125019) (h1 : t = i) : (term41 _125019 i t) = (term42 _125019 i).
Proof. exact (MK_COMB (@lem6779638 _125019 i) (@lem6779599 _125019 t i h1)). Qed.
Lemma lem6779640 {_125019 : Type'} (i : _125019) : (term42 _125019 i) = (term43 _125019 i).
Proof. exact (eq_refl (term42 _125019 i)). Qed.
Lemma lem6779641 {_125019 : Type'} (i : _125019) (t : _125019) : (term44 _125019 i t) = (term44 _125019 i t).
Proof. exact (eq_refl (term44 _125019 i t)). Qed.
Lemma lem6779642 {_125019 : Type'} (t : _125019) (i : _125019) : ((term41 _125019 i t) = (term42 _125019 i)) = ((term41 _125019 i t) = (term43 _125019 i)).
Proof. exact (MK_COMB (@lem6779641 _125019 i t) (@lem6779640 _125019 i)). Qed.
Lemma lem6779643 {_125019 : Type'} (t : _125019) (i : _125019) : (term41 _125019 i t) = (term38 _125019 t i).
Proof. exact (eq_refl (term41 _125019 i t)). Qed.
Lemma lem6779644 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6779645 {_125019 : Type'} (t : _125019) (i : _125019) : (term44 _125019 i t) = (term45 _125019 t i).
Proof. exact (MK_COMB (@lem6779644) (@lem6779643 _125019 t i)). Qed.
Lemma lem6779646 {_125019 : Type'} (i : _125019) : (term43 _125019 i) = (term43 _125019 i).
Proof. exact (eq_refl (term43 _125019 i)). Qed.
Lemma lem6779647 {_125019 : Type'} (t : _125019) (i : _125019) : ((term41 _125019 i t) = (term43 _125019 i)) = ((term38 _125019 t i) = (term43 _125019 i)).
Proof. exact (MK_COMB (@lem6779645 _125019 t i) (@lem6779646 _125019 i)). Qed.
Lemma lem6779648 {_125019 : Type'} (t : _125019) (i : _125019) : ((term41 _125019 i t) = (term42 _125019 i)) = ((term38 _125019 t i) = (term43 _125019 i)).
Proof. exact (TRANS (@lem6779642 _125019 t i) (@lem6779647 _125019 t i)). Qed.
Lemma lem6779649 {_125019 : Type'} (t : _125019) (i : _125019) (h1 : t = i) : (term38 _125019 t i) = (term43 _125019 i).
Proof. exact (EQ_MP (@lem6779648 _125019 t i) (@lem6779639 _125019 t i h1)). Qed.
Lemma lem6779650 {_125019 : Type'} (t : _125019) (i : _125019) (h1 : term38 _125019 t i) (h2 : t = i) : term43 _125019 i.
Proof. exact (EQ_MP (@lem6779649 _125019 t i h2) (@lem6779603 _125019 t i h1)). Qed.
Lemma lem6779678 {_125019 : Type'} (_88846 : _125019) (P : _125019 -> Prop) (h1 : term28 _125019 P) : term35 _125019 P _88846.
Proof. exact (EQ_MP (@lem6779596 _125019 P _88846) (@lem6779595 _125019 _88846 P h1)). Qed.
Lemma lem6779692 {_125019 : Type'} (P : _125019 -> Prop) (i : _125019) (h1 : P i) : P i.
Proof. exact (h1). Qed.
Lemma lem6779708 {_125019 : Type'} (x : _125019) : x = x.
Proof. exact (@lem21386 _125019 x). Qed.
Lemma lem6779709 {_125019 : Type'} (x : _125019) : x = x.
Proof. exact (@lem6779708 _125019 x). Qed.
Lemma lem6779710 {_125019 : Type'} (i : _125019) : i = i.
Proof. exact (@lem6779709 _125019 i). Qed.
Lemma lem6779711 {_125019 : Type'} (i : _125019) : term46 _125019 i.
Proof. exact (fun h0 : term43 _125019 i => @lem6779710 _125019 i). Qed.
Lemma lem6779713 (p : Prop) : (term47 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6779714 {_125019 : Type'} (i : _125019) : (term46 _125019 i) = (i = i).
Proof. exact (@lem6779713 (i = i)). Qed.
Lemma lem6779715 {_125019 : Type'} (i : _125019) : i = i.
Proof. exact (EQ_MP (@lem6779714 _125019 i) (@lem6779711 _125019 i)). Qed.
Lemma lem6779718 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6779720 {_125019 : Type'} (i : _125019) : (term43 _125019 i) = (term48 _125019 i).
Proof. exact (@lem6779718 (i = i)). Qed.
Lemma lem6779723 {_125019 : Type'} (t : _125019) (i : _125019) (h1 : term38 _125019 t i) (h2 : t = i) : term48 _125019 i.
Proof. exact (EQ_MP (@lem6779720 _125019 i) (@lem6779650 _125019 t i h1 h2)). Qed.
Lemma lem6779726 {_125019 : Type'} (t : _125019) (i : _125019) (h1 : term38 _125019 t i) (h2 : t = i) : False.
Proof. exact (@lem6779723 _125019 t i h1 h2 (@lem6779715 _125019 i)). Qed.
Lemma lem6779727 {_125019 : Type'} (t : _125019) (i : _125019) (h1 : term38 _125019 t i) (h2 : t = i) : term49.
Proof. exact (fun h0 : ~ False => @lem6779726 _125019 t i h1 h2). Qed.
Lemma lem6779729 (p : Prop) : (term47 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6779730 : term49 = False.
Proof. exact (@lem6779729 False). Qed.
Lemma lem6779733 {_125019 : Type'} (P : _125019 -> Prop) (i : _125019) (h1 : P i) : P i.
Proof. exact (h1). Qed.
Lemma lem6779734 {_125019 : Type'} (P : _125019 -> Prop) (i : _125019) (h1 : P i) : term50 _125019 P i.
Proof. exact (fun h0 : term35 _125019 P i => @lem6779733 _125019 P i h1). Qed.
Lemma lem6779736 (p : Prop) : (term47 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6779737 {_125019 : Type'} (P : _125019 -> Prop) (i : _125019) : (term50 _125019 P i) = (P i).
Proof. exact (@lem6779736 (P i)). Qed.
Lemma lem6779738 {_125019 : Type'} (P : _125019 -> Prop) (i : _125019) (h1 : P i) : P i.
Proof. exact (EQ_MP (@lem6779737 _125019 P i) (@lem6779734 _125019 P i h1)). Qed.
Lemma lem6779741 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6779743 {_125019 : Type'} (P : _125019 -> Prop) (_88846 : _125019) : (term35 _125019 P _88846) = (term51 _125019 P _88846).
Proof. exact (@lem6779741 (P _88846)). Qed.
Lemma lem6779746 {_125019 : Type'} (_88846 : _125019) (P : _125019 -> Prop) (h1 : term28 _125019 P) : term51 _125019 P _88846.
Proof. exact (EQ_MP (@lem6779743 _125019 P _88846) (@lem6779678 _125019 _88846 P h1)). Qed.
Lemma lem6779747 {_125019 : Type'} (_88846 : _125019) (P : _125019 -> Prop) (h1 : term28 _125019 P) : term51 _125019 P _88846.
Proof. exact (@lem6779746 _125019 _88846 P h1). Qed.
Lemma lem6779748 {_125019 : Type'} (i : _125019) (P : _125019 -> Prop) (h1 : term28 _125019 P) : term51 _125019 P i.
Proof. exact (@lem6779747 _125019 i P h1). Qed.
Lemma lem6779751 {_125019 : Type'} (P : _125019 -> Prop) (i : _125019) (h1 : term28 _125019 P) (h2 : P i) : False.
Proof. exact (@lem6779748 _125019 i P h1 (@lem6779738 _125019 P i h2)). Qed.
Lemma lem6779752 {_125019 : Type'} (P : _125019 -> Prop) (i : _125019) (h1 : term28 _125019 P) (h2 : P i) : term49.
Proof. exact (fun h0 : ~ False => @lem6779751 _125019 P i h1 h2). Qed.
Lemma lem6779754 (p : Prop) : (term47 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6779755 : term49 = False.
Proof. exact (@lem6779754 False). Qed.
Lemma lem6779756 {_125019 : Type'} (P : _125019 -> Prop) (i : _125019) (h1 : term28 _125019 P) (h2 : P i) : False.
Proof. exact (EQ_MP (@lem6779755) (@lem6779752 _125019 P i h1 h2)). Qed.
Lemma lem6779757 {_125019 : Type'} (P : _125019 -> Prop) (i : _125019) (h1 : term28 _125019 P) (h2 : P i) : (P i) = False.
Proof. exact (prop_ext (fun h3 : P i => @lem6779756 _125019 P i h1 h2) (fun h3 : False => @lem6779692 _125019 P i h2)). Qed.
Lemma lem6779759 {_125019 : Type'} (P : _125019 -> Prop) (i : _125019) (h1 : term28 _125019 P) (h2 : P i) : False.
Proof. exact (EQ_MP (@lem6779757 _125019 P i h1 h2) (@lem6779692 _125019 P i h2)). Qed.
Lemma lem6779760 {_125019 : Type'} (t : _125019) (i : _125019) (h1 : term38 _125019 t i) (h2 : t = i) : False.
Proof. exact (EQ_MP (@lem6779730) (@lem6779727 _125019 t i h1 h2)). Qed.
Lemma lem6779761 {_125019 : Type'} (P : _125019 -> Prop) (i : _125019) (h1 : term28 _125019 P) (h2 : P i) : (P i) = False.
Proof. exact (prop_ext (fun h3 : P i => @lem6779759 _125019 P i h1 h2) (fun h3 : False => @lem6779609 _125019 P i h2)). Qed.
Lemma lem6779762 {_125019 : Type'} (P : _125019 -> Prop) (i : _125019) (h1 : term28 _125019 P) (h2 : P i) : False.
Proof. exact (EQ_MP (@lem6779761 _125019 P i h1 h2) (@lem6779609 _125019 P i h2)). Qed.
Lemma lem6779763 {_125019 : Type'} (t : _125019) (i : _125019) (h1 : term38 _125019 t i) (h2 : t = i) : (term38 _125019 t i) = False.
Proof. exact (prop_ext (fun h3 : term38 _125019 t i => @lem6779760 _125019 t i h1 h2) (fun h3 : False => @lem6779603 _125019 t i h1)). Qed.
Lemma lem6779764 {_125019 : Type'} (t : _125019) (i : _125019) (h1 : term38 _125019 t i) (h2 : t = i) : False.
Proof. exact (EQ_MP (@lem6779763 _125019 t i h1 h2) (@lem6779603 _125019 t i h1)). Qed.
Lemma lem6779765 {_125019 : Type'} (t : _125019) (i : _125019) (h1 : term38 _125019 t i) (h2 : t = i) : (t = i) = False.
Proof. exact (prop_ext (fun h3 : t = i => @lem6779764 _125019 t i h1 h2) (fun h3 : False => @lem6779599 _125019 t i h2)). Qed.
Lemma lem6779766 {_125019 : Type'} (t : _125019) (i : _125019) (h1 : term38 _125019 t i) (h2 : t = i) : False.
Proof. exact (EQ_MP (@lem6779765 _125019 t i h1 h2) (@lem6779599 _125019 t i h2)). Qed.
Lemma lem6779767 {_125019 : Type'} (P : _125019 -> Prop) (i : _125019) (h1 : term28 _125019 P) (h2 : P i) : (P i) = False.
Proof. exact (prop_ext (fun h3 : P i => @lem6779762 _125019 P i h1 h2) (fun h3 : False => @lem6779591 _125019 P i h2)). Qed.
Lemma lem6779768 {_125019 : Type'} (P : _125019 -> Prop) (i : _125019) (h1 : term28 _125019 P) (h2 : P i) : False.
Proof. exact (EQ_MP (@lem6779767 _125019 P i h1 h2) (@lem6779591 _125019 P i h2)). Qed.
Lemma lem6779769 {_125019 : Type'} (t : _125019) (i : _125019) (h1 : term38 _125019 t i) (h2 : t = i) : (term38 _125019 t i) = False.
Proof. exact (prop_ext (fun h3 : term38 _125019 t i => @lem6779766 _125019 t i h1 h2) (fun h3 : False => @lem6779576 _125019 t i h1)). Qed.
Lemma lem6779770 {_125019 : Type'} (t : _125019) (i : _125019) (h1 : term38 _125019 t i) (h2 : t = i) : False.
Proof. exact (EQ_MP (@lem6779769 _125019 t i h1 h2) (@lem6779576 _125019 t i h1)). Qed.
Lemma lem6779771 {_125019 : Type'} (t : _125019) (i : _125019) (h1 : term38 _125019 t i) (h2 : t = i) : (t = i) = False.
Proof. exact (prop_ext (fun h3 : t = i => @lem6779770 _125019 t i h1 h2) (fun h3 : False => @lem6779565 _125019 t i h2)). Qed.
Lemma lem6779772 {_125019 : Type'} (t : _125019) (i : _125019) (h1 : term38 _125019 t i) (h2 : t = i) : False.
Proof. exact (EQ_MP (@lem6779771 _125019 t i h1 h2) (@lem6779565 _125019 t i h2)). Qed.
Lemma lem6779773 {_125019 : Type'} (P : _125019 -> Prop) (i : _125019) (h1 : term28 _125019 P) (h2 : P i) : (P i) = False.
Proof. exact (prop_ext (fun h3 : P i => @lem6779768 _125019 P i h1 h2) (fun h3 : False => @lem6779591 _125019 P i h2)). Qed.
Lemma lem6779774 {_125019 : Type'} (P : _125019 -> Prop) (i : _125019) (h1 : term28 _125019 P) (h2 : P i) : False.
Proof. exact (EQ_MP (@lem6779773 _125019 P i h1 h2) (@lem6779591 _125019 P i h2)). Qed.
Lemma lem6779775 {_125019 : Type'} (t : _125019) (i : _125019) (h1 : term38 _125019 t i) (h2 : t = i) : (term38 _125019 t i) = False.
Proof. exact (prop_ext (fun h3 : term38 _125019 t i => @lem6779772 _125019 t i h1 h2) (fun h3 : False => @lem6779576 _125019 t i h1)). Qed.
Lemma lem6779776 {_125019 : Type'} (t : _125019) (i : _125019) (h1 : term38 _125019 t i) (h2 : t = i) : False.
Proof. exact (EQ_MP (@lem6779775 _125019 t i h1 h2) (@lem6779576 _125019 t i h1)). Qed.
Lemma lem6779777 {_125019 : Type'} (t : _125019) (i : _125019) (h1 : term38 _125019 t i) (h2 : t = i) : (t = i) = False.
Proof. exact (prop_ext (fun h3 : t = i => @lem6779776 _125019 t i h1 h2) (fun h3 : False => @lem6779565 _125019 t i h2)). Qed.
Lemma lem6779778 {_125019 : Type'} (t : _125019) (i : _125019) (h1 : term38 _125019 t i) (h2 : t = i) : False.
Proof. exact (EQ_MP (@lem6779777 _125019 t i h1 h2) (@lem6779565 _125019 t i h2)). Qed.
Lemma lem6779779 {_125019 : Type'} (t : _125019) (P : _125019 -> Prop) (i : _125019) (h1 : term28 _125019 P) (h2 : t = i) (h3 : term26 _125019 t P i) : False.
Proof. exact (or_elim (@lem6779550 _125019 t P i h3) (fun h0 : term38 _125019 t i => @lem6779778 _125019 t i h0 h2) (fun h0 : P i => @lem6779774 _125019 P i h1 h0)). Qed.
Lemma lem6779780 {_125019 : Type'} (t : _125019) (P : _125019 -> Prop) (i : _125019) (h1 : term28 _125019 P) (h2 : t = i) (h3 : term26 _125019 t P i) : (t = i) = False.
Proof. exact (prop_ext (fun h4 : t = i => @lem6779779 _125019 t P i h1 h2 h3) (fun h4 : False => @lem6779536 _125019 t i h2)). Qed.
Lemma lem6779781 {_125019 : Type'} (t : _125019) (P : _125019 -> Prop) (i : _125019) (h1 : term28 _125019 P) (h2 : t = i) (h3 : term26 _125019 t P i) : False.
Proof. exact (EQ_MP (@lem6779780 _125019 t P i h1 h2 h3) (@lem6779536 _125019 t i h2)). Qed.
Lemma lem6779782 {_125019 : Type'} (t : _125019) (P : _125019 -> Prop) (i : _125019) (h1 : term28 _125019 P) (h2 : t = i) (h3 : term26 _125019 t P i) : (t = i) = False.
Proof. exact (prop_ext (fun h4 : t = i => @lem6779781 _125019 t P i h1 h2 h3) (fun h4 : False => @lem6779498 _125019 t i h2)). Qed.
Lemma lem6779783 {_125019 : Type'} (t : _125019) (P : _125019 -> Prop) (i : _125019) (h1 : term28 _125019 P) (h2 : t = i) (h3 : term26 _125019 t P i) : False.
Proof. exact (EQ_MP (@lem6779782 _125019 t P i h1 h2 h3) (@lem6779498 _125019 t i h2)). Qed.
Lemma lem6779784 {_125019 : Type'} (t : _125019) (P : _125019 -> Prop) (i : _125019) (h1 : term28 _125019 P) (h2 : t = i) (h3 : term26 _125019 t P i) : (term28 _125019 P) = False.
Proof. exact (prop_ext (fun h4 : term28 _125019 P => @lem6779783 _125019 t P i h1 h2 h3) (fun h4 : False => @lem6779492 _125019 P h1)). Qed.
Lemma lem6779785 {_125019 : Type'} (t : _125019) (P : _125019 -> Prop) (i : _125019) (h1 : term28 _125019 P) (h2 : t = i) (h3 : term26 _125019 t P i) : False.
Proof. exact (EQ_MP (@lem6779784 _125019 t P i h1 h2 h3) (@lem6779492 _125019 P h1)). Qed.
Lemma lem6779786 {_125019 : Type'} (t : _125019) (P : _125019 -> Prop) (i : _125019) (h1 : t = i) (h2 : term26 _125019 t P i) : term27 _125019 P.
Proof. exact (fun h0 : term28 _125019 P => @lem6779785 _125019 t P i h0 h1 h2). Qed.
Lemma lem6779787 {_125019 : Type'} (t : _125019) (P : _125019 -> Prop) (i : _125019) (h1 : t = i) (h2 : term26 _125019 t P i) : term22 _125019 P.
Proof. exact (EQ_MP (@lem6779491 _125019 P) (@lem6779786 _125019 t P i h1 h2)). Qed.
Lemma lem6779788 {_125019 : Type'} (P : _125019 -> Prop) (t : _125019) (i : _125019) (h1 : t = i) : term24 _125019 t i P.
Proof. exact (fun h0 : term26 _125019 t P i => @lem6779787 _125019 t P i h1 h0). Qed.
Lemma lem6779789 {_125019 : Type'} (t : _125019) (i : _125019) (P : _125019 -> Prop) : term1 _125019 t i P.
Proof. exact (fun h0 : t = i => @lem6779788 _125019 P t i h0). Qed.
Lemma lem6779794 {_125019 : Type'} (i : _125019) (P : _125019 -> Prop) : term12 _125019 i P.
Proof. exact (fun t : _125019 => @lem6779789 _125019 t i P). Qed.
Lemma lem6779799 {_125019 : Type'} (P : _125019 -> Prop) : term16 _125019 P.
Proof. exact (fun i : _125019 => @lem6779794 _125019 i P). Qed.
Lemma lem6779804 {_125019 : Type'} : term20 _125019.
Proof. exact (fun P : _125019 -> Prop => @lem6779799 _125019 P). Qed.
Lemma lem6779805 {_125019 : Type'} : term19 _125019.
Proof. exact (EQ_MP (@lem6779485 _125019) (@lem6779804 _125019)). Qed.
Lemma lem6779806 {_125019 : Type'} (P : _125019 -> Prop) : term52 _125019 P.
Proof. exact (@lem6779805 _125019 P). Qed.
Lemma lem6779807 {_125019 : Type'} (P : _125019 -> Prop) : (term52 _125019 P) = (term15 _125019 P).
Proof. exact (eq_refl (term52 _125019 P)). Qed.
Lemma lem6779808 {_125019 : Type'} (P : _125019 -> Prop) : term15 _125019 P.
Proof. exact (EQ_MP (@lem6779807 _125019 P) (@lem6779806 _125019 P)). Qed.
Lemma lem6779809 {_125019 : Type'} (P : _125019 -> Prop) (i : _125019) : term53 _125019 P i.
Proof. exact (@lem6779808 _125019 P i). Qed.
Lemma lem6779810 {_125019 : Type'} (i : _125019) (P : _125019 -> Prop) : (term53 _125019 P i) = (term11 _125019 i P).
Proof. exact (eq_refl (term53 _125019 P i)). Qed.
Lemma lem6779811 {_125019 : Type'} (i : _125019) (P : _125019 -> Prop) : term11 _125019 i P.
Proof. exact (EQ_MP (@lem6779810 _125019 i P) (@lem6779809 _125019 P i)). Qed.
Lemma lem6779812 {_125019 : Type'} (i : _125019) (P : _125019 -> Prop) (t : _125019) : term54 _125019 i P t.
Proof. exact (@lem6779811 _125019 i P t). Qed.
Lemma lem6779813 {_125019 : Type'} (t : _125019) (i : _125019) (P : _125019 -> Prop) : (term54 _125019 i P t) = (term2 _125019 t i P).
Proof. exact (eq_refl (term54 _125019 i P t)). Qed.
Lemma lem6779814 {_125019 : Type'} (t : _125019) (i : _125019) (P : _125019 -> Prop) : term2 _125019 t i P.
Proof. exact (EQ_MP (@lem6779813 _125019 t i P) (@lem6779812 _125019 i P t)). Qed.
Lemma lem6779816 {_125019 : Type'} (t : _125019) (i : _125019) (P : _125019 -> Prop) : term2 _125019 t i P.
Proof. exact (@lem6779372 _125019 t i P (@lem6779814 _125019 t i P)). Qed.
Lemma lem6779817 {_125019 : Type'} (t : _125019) (i : _125019) (P : _125019 -> Prop) (h1 : term3 _125019 t i P) : False.
Proof. exact (@lem6779816 _125019 t i P (@lem6779356 _125019 t i P h1)). Qed.
Lemma lem6779818 {_125019 : Type'} (t : _125019) (i : _125019) (P : _125019 -> Prop) (h1 : term3 _125019 t i P) : (term3 _125019 t i P) = False.
Proof. exact (prop_ext (fun h2 : term3 _125019 t i P => @lem6779817 _125019 t i P h1) (fun h2 : False => @lem6779356 _125019 t i P h1)). Qed.
Lemma lem6779819 {_125019 : Type'} (t : _125019) (i : _125019) (P : _125019 -> Prop) (h1 : term3 _125019 t i P) : False.
Proof. exact (EQ_MP (@lem6779818 _125019 t i P h1) (@lem6779356 _125019 t i P h1)). Qed.
Lemma lem6779820 {_125019 : Type'} (t : _125019) (i : _125019) (P : _125019 -> Prop) : term2 _125019 t i P.
Proof. exact (fun h0 : term3 _125019 t i P => @lem6779819 _125019 t i P h0). Qed.
Lemma lem6779828 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (h1 : (term55 A K op ltle k dom neut f) = (@iterato A K dom neut op ltle k f)) : (term55 A K op ltle k dom neut f) = (@iterato A K dom neut op ltle k f).
Proof. exact (h1). Qed.
Lemma lem6779829 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (h1 : (term55 A K op ltle k dom neut f) = (@iterato A K dom neut op ltle k f)) : (@iterato A K dom neut op ltle k f) = (term55 A K op ltle k dom neut f).
Proof. exact (SYM (@lem6779828 A K dom neut op ltle k f h1)). Qed.
Lemma lem6779830 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) (f : K -> A) (h1 : (@iterato A K dom neut op ltle k f) = (term55 A K op ltle k dom neut f)) : (@iterato A K dom neut op ltle k f) = (term55 A K op ltle k dom neut f).
Proof. exact (h1). Qed.
Lemma lem6779831 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) (f : K -> A) (h1 : (@iterato A K dom neut op ltle k f) = (term55 A K op ltle k dom neut f)) : (term55 A K op ltle k dom neut f) = (@iterato A K dom neut op ltle k f).
Proof. exact (SYM (@lem6779830 A K op ltle k dom neut f h1)). Qed.
Lemma lem6779832 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) (f : K -> A) : ((term55 A K op ltle k dom neut f) = (@iterato A K dom neut op ltle k f)) = ((@iterato A K dom neut op ltle k f) = (term55 A K op ltle k dom neut f)).
Proof. exact (prop_ext (fun h1 : (term55 A K op ltle k dom neut f) = (@iterato A K dom neut op ltle k f) => @lem6779829 A K dom neut op ltle k f h1) (fun h1 : (@iterato A K dom neut op ltle k f) = (term55 A K op ltle k dom neut f) => @lem6779831 A K op ltle k dom neut f h1)). Qed.
Lemma lem6779833 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) : (term56 A K dom neut op ltle k) = (term57 A K op ltle k dom neut).
Proof. exact (fun_ext (fun f : K -> A => @lem6779832 A K op ltle k dom neut f)). Qed.
Lemma lem6779834 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem6779835 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) : (term58 A K dom neut op ltle k) = (term59 A K op ltle k dom neut).
Proof. exact (MK_COMB (@lem6779834 A K) (@lem6779833 A K op ltle k dom neut)). Qed.
Lemma lem6779836 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (dom : A -> Prop) (neut : A) : (term60 A K dom neut op ltle) = (term61 A K op ltle dom neut).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6779835 A K op ltle k dom neut)). Qed.
Lemma lem6779837 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6779838 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (dom : A -> Prop) (neut : A) : (term62 A K dom neut op ltle) = (term63 A K op ltle dom neut).
Proof. exact (MK_COMB (@lem6779837 K) (@lem6779836 A K op ltle dom neut)). Qed.
Lemma lem6779839 {A K : Type'} (op : type1400 A) (dom : A -> Prop) (neut : A) : (term64 A K dom neut op) = (term65 A K op dom neut).
Proof. exact (fun_ext (fun ltle : type1402 K => @lem6779838 A K op ltle dom neut)). Qed.
Lemma lem6779840 {K : Type'} : (@all (K -> K -> Prop)) = (@all (K -> K -> Prop)).
Proof. exact (eq_refl (@all (K -> K -> Prop))). Qed.
Lemma lem6779841 {A K : Type'} (op : type1400 A) (dom : A -> Prop) (neut : A) : (term66 A K dom neut op) = (term67 A K op dom neut).
Proof. exact (MK_COMB (@lem6779840 K) (@lem6779839 A K op dom neut)). Qed.
Lemma lem6779842 {A K : Type'} (dom : A -> Prop) (neut : A) : (term68 A K dom neut) = (term69 A K dom neut).
Proof. exact (fun_ext (fun op : type1400 A => @lem6779841 A K op dom neut)). Qed.
Lemma lem6779843 {A : Type'} : (@all (A -> A -> A)) = (@all (A -> A -> A)).
Proof. exact (eq_refl (@all (A -> A -> A))). Qed.
Lemma lem6779844 {A K : Type'} (dom : A -> Prop) (neut : A) : (term70 A K dom neut) = (term71 A K dom neut).
Proof. exact (MK_COMB (@lem6779843 A) (@lem6779842 A K dom neut)). Qed.
Lemma lem6779845 {A K : Type'} (dom : A -> Prop) : (term72 A K dom) = (term73 A K dom).
Proof. exact (fun_ext (fun neut : A => @lem6779844 A K dom neut)). Qed.
Lemma lem6779846 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6779847 {A K : Type'} (dom : A -> Prop) : (term74 A K dom) = (term75 A K dom).
Proof. exact (MK_COMB (@lem6779846 A) (@lem6779845 A K dom)). Qed.
Lemma lem6779848 {A K : Type'} : (term76 A K) = (term77 A K).
Proof. exact (fun_ext (fun dom : A -> Prop => @lem6779847 A K dom)). Qed.
Lemma lem6779849 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6779850 {A K : Type'} : (term78 A K) = (term79 A K).
Proof. exact (MK_COMB (@lem6779849 A) (@lem6779848 A K)). Qed.
Lemma lem6779851 {A K : Type'} : term79 A K.
Proof. exact (EQ_MP (@lem6779850 A K) (@lem6449238 A K)). Qed.
Lemma lem6779852 {A K : Type'} (dom : A -> Prop) : term80 A K dom.
Proof. exact (@lem6779851 A K dom). Qed.
Lemma lem6779853 {A K : Type'} (dom : A -> Prop) : (term80 A K dom) = (term75 A K dom).
Proof. exact (eq_refl (term80 A K dom)). Qed.
Lemma lem6779854 {A K : Type'} (dom : A -> Prop) : term75 A K dom.
Proof. exact (EQ_MP (@lem6779853 A K dom) (@lem6779852 A K dom)). Qed.
Lemma lem6779855 {A K : Type'} (dom : A -> Prop) (neut : A) : term81 A K dom neut.
Proof. exact (@lem6779854 A K dom neut). Qed.
Lemma lem6779856 {A K : Type'} (dom : A -> Prop) (neut : A) : (term81 A K dom neut) = (term71 A K dom neut).
Proof. exact (eq_refl (term81 A K dom neut)). Qed.
Lemma lem6779857 {A K : Type'} (dom : A -> Prop) (neut : A) : term71 A K dom neut.
Proof. exact (EQ_MP (@lem6779856 A K dom neut) (@lem6779855 A K dom neut)). Qed.
Lemma lem6779858 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) : term82 A K dom neut op.
Proof. exact (@lem6779857 A K dom neut op). Qed.
Lemma lem6779859 {A K : Type'} (op : type1400 A) (dom : A -> Prop) (neut : A) : (term82 A K dom neut op) = (term67 A K op dom neut).
Proof. exact (eq_refl (term82 A K dom neut op)). Qed.
Lemma lem6779860 {A K : Type'} (op : type1400 A) (dom : A -> Prop) (neut : A) : term67 A K op dom neut.
Proof. exact (EQ_MP (@lem6779859 A K op dom neut) (@lem6779858 A K dom neut op)). Qed.
Lemma lem6779861 {A K : Type'} (op : type1400 A) (dom : A -> Prop) (neut : A) (ltle : type1402 K) : term83 A K op dom neut ltle.
Proof. exact (@lem6779860 A K op dom neut ltle). Qed.
Lemma lem6779862 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (dom : A -> Prop) (neut : A) : (term83 A K op dom neut ltle) = (term63 A K op ltle dom neut).
Proof. exact (eq_refl (term83 A K op dom neut ltle)). Qed.
Lemma lem6779863 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (dom : A -> Prop) (neut : A) : term63 A K op ltle dom neut.
Proof. exact (EQ_MP (@lem6779862 A K op ltle dom neut) (@lem6779861 A K op dom neut ltle)). Qed.
Lemma lem6779864 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (dom : A -> Prop) (neut : A) (k : K -> Prop) : term84 A K op ltle dom neut k.
Proof. exact (@lem6779863 A K op ltle dom neut k). Qed.
Lemma lem6779865 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) : (term84 A K op ltle dom neut k) = (term59 A K op ltle k dom neut).
Proof. exact (eq_refl (term84 A K op ltle dom neut k)). Qed.
Lemma lem6779866 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) : term59 A K op ltle k dom neut.
Proof. exact (EQ_MP (@lem6779865 A K op ltle k dom neut) (@lem6779864 A K op ltle dom neut k)). Qed.
Lemma lem6779867 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) (f : K -> A) : term85 A K op ltle k dom neut f.
Proof. exact (@lem6779866 A K op ltle k dom neut f). Qed.
Lemma lem6779868 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) (f : K -> A) : (term85 A K op ltle k dom neut f) = ((@iterato A K dom neut op ltle k f) = (term55 A K op ltle k dom neut f)).
Proof. exact (eq_refl (term85 A K op ltle k dom neut f)). Qed.
Lemma lem6779870 {A K : Type'} (dom : A -> Prop) : term86 A K dom.
Proof. exact (@lem6401305 A K dom). Qed.
Lemma lem6779871 {A K : Type'} (dom : A -> Prop) : (term86 A K dom) = (term87 A K dom).
Proof. exact (eq_refl (term86 A K dom)). Qed.
Lemma lem6779872 {A K : Type'} (dom : A -> Prop) : term87 A K dom.
Proof. exact (EQ_MP (@lem6779871 A K dom) (@lem6779870 A K dom)). Qed.
Lemma lem6779873 {A K : Type'} (dom : A -> Prop) (neut : A) : term88 A K dom neut.
Proof. exact (@lem6779872 A K dom neut). Qed.
Lemma lem6779874 {A K : Type'} (dom : A -> Prop) (neut : A) : (term88 A K dom neut) = (term89 A K dom neut).
Proof. exact (eq_refl (term88 A K dom neut)). Qed.
Lemma lem6779875 {A K : Type'} (dom : A -> Prop) (neut : A) : term89 A K dom neut.
Proof. exact (EQ_MP (@lem6779874 A K dom neut) (@lem6779873 A K dom neut)). Qed.
Lemma lem6779876 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) : term90 A K dom neut op.
Proof. exact (@lem6779875 A K dom neut op). Qed.
Lemma lem6779877 {A K : Type'} (op : type1400 A) (dom : A -> Prop) (neut : A) : (term90 A K dom neut op) = (term91 A K op dom neut).
Proof. exact (eq_refl (term90 A K dom neut op)). Qed.
Lemma lem6779878 {A K : Type'} (op : type1400 A) (dom : A -> Prop) (neut : A) : term91 A K op dom neut.
Proof. exact (EQ_MP (@lem6779877 A K op dom neut) (@lem6779876 A K dom neut op)). Qed.
Lemma lem6779879 {A K : Type'} (op : type1400 A) (dom : A -> Prop) (neut : A) (ltle : type1402 K) : term92 A K op dom neut ltle.
Proof. exact (@lem6779878 A K op dom neut ltle). Qed.
Lemma lem6779880 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (dom : A -> Prop) (neut : A) : (term92 A K op dom neut ltle) = (term93 A K op ltle dom neut).
Proof. exact (eq_refl (term92 A K op dom neut ltle)). Qed.
Lemma lem6779881 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (dom : A -> Prop) (neut : A) : term93 A K op ltle dom neut.
Proof. exact (EQ_MP (@lem6779880 A K op ltle dom neut) (@lem6779879 A K op dom neut ltle)). Qed.
Lemma lem6779882 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (dom : A -> Prop) (neut : A) (k : K -> Prop) : term94 A K op ltle dom neut k.
Proof. exact (@lem6779881 A K op ltle dom neut k). Qed.
Lemma lem6779883 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) : (term94 A K op ltle dom neut k) = (term95 A K op ltle k dom neut).
Proof. exact (eq_refl (term94 A K op ltle dom neut k)). Qed.
Lemma lem6779884 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) : term95 A K op ltle k dom neut.
Proof. exact (EQ_MP (@lem6779883 A K op ltle k dom neut) (@lem6779882 A K op ltle dom neut k)). Qed.
Lemma lem6779885 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) (f : K -> A) : term96 A K op ltle k dom neut f.
Proof. exact (@lem6779884 A K op ltle k dom neut f). Qed.
Lemma lem6779886 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term96 A K op ltle k dom neut f) = ((@iterato A K dom neut op ltle k f) = (term97 A K op ltle k f dom neut)).
Proof. exact (eq_refl (term96 A K op ltle k dom neut f)). Qed.
Lemma lem6779888 {A K : Type'} (dom : A -> Prop) : term86 A K dom.
Proof. exact (@lem6401305 A K dom). Qed.
Lemma lem6779889 {A K : Type'} (dom : A -> Prop) : (term86 A K dom) = (term87 A K dom).
Proof. exact (eq_refl (term86 A K dom)). Qed.
Lemma lem6779890 {A K : Type'} (dom : A -> Prop) : term87 A K dom.
Proof. exact (EQ_MP (@lem6779889 A K dom) (@lem6779888 A K dom)). Qed.
Lemma lem6779891 {A K : Type'} (dom : A -> Prop) (neut : A) : term88 A K dom neut.
Proof. exact (@lem6779890 A K dom neut). Qed.
Lemma lem6779892 {A K : Type'} (dom : A -> Prop) (neut : A) : (term88 A K dom neut) = (term89 A K dom neut).
Proof. exact (eq_refl (term88 A K dom neut)). Qed.
Lemma lem6779893 {A K : Type'} (dom : A -> Prop) (neut : A) : term89 A K dom neut.
Proof. exact (EQ_MP (@lem6779892 A K dom neut) (@lem6779891 A K dom neut)). Qed.
Lemma lem6779894 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) : term90 A K dom neut op.
Proof. exact (@lem6779893 A K dom neut op). Qed.
Lemma lem6779895 {A K : Type'} (op : type1400 A) (dom : A -> Prop) (neut : A) : (term90 A K dom neut op) = (term91 A K op dom neut).
Proof. exact (eq_refl (term90 A K dom neut op)). Qed.
Lemma lem6779896 {A K : Type'} (op : type1400 A) (dom : A -> Prop) (neut : A) : term91 A K op dom neut.
Proof. exact (EQ_MP (@lem6779895 A K op dom neut) (@lem6779894 A K dom neut op)). Qed.
Lemma lem6779897 {A K : Type'} (op : type1400 A) (dom : A -> Prop) (neut : A) (ltle : type1402 K) : term92 A K op dom neut ltle.
Proof. exact (@lem6779896 A K op dom neut ltle). Qed.
Lemma lem6779898 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (dom : A -> Prop) (neut : A) : (term92 A K op dom neut ltle) = (term93 A K op ltle dom neut).
Proof. exact (eq_refl (term92 A K op dom neut ltle)). Qed.
Lemma lem6779899 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (dom : A -> Prop) (neut : A) : term93 A K op ltle dom neut.
Proof. exact (EQ_MP (@lem6779898 A K op ltle dom neut) (@lem6779897 A K op dom neut ltle)). Qed.
Lemma lem6779900 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (dom : A -> Prop) (neut : A) (k : K -> Prop) : term94 A K op ltle dom neut k.
Proof. exact (@lem6779899 A K op ltle dom neut k). Qed.
Lemma lem6779901 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) : (term94 A K op ltle dom neut k) = (term95 A K op ltle k dom neut).
Proof. exact (eq_refl (term94 A K op ltle dom neut k)). Qed.
Lemma lem6779902 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) : term95 A K op ltle k dom neut.
Proof. exact (EQ_MP (@lem6779901 A K op ltle k dom neut) (@lem6779900 A K op ltle dom neut k)). Qed.
Lemma lem6779903 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) (f : K -> A) : term96 A K op ltle k dom neut f.
Proof. exact (@lem6779902 A K op ltle k dom neut f). Qed.
Lemma lem6779904 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term96 A K op ltle k dom neut f) = ((@iterato A K dom neut op ltle k f) = (term97 A K op ltle k f dom neut)).
Proof. exact (eq_refl (term96 A K op ltle k dom neut f)). Qed.
Lemma lem6779907 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (@iterato A K dom neut op ltle k f) = (term97 A K op ltle k f dom neut).
Proof. exact (EQ_MP (@lem6779904 A K op ltle k f dom neut) (@lem6779903 A K op ltle k dom neut f)). Qed.
Lemma lem6779908 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (@iterato A K dom neut op ltle k f) = (term97 A K op ltle k f dom neut).
Proof. exact (@lem6779907 A K op ltle k f dom neut). Qed.
Lemma lem6779909 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (f : K -> A) (dom : A -> Prop) (neut : A) : (@iterato A K dom neut op ltle (@EMPTY K) f) = (term98 A K op ltle f dom neut).
Proof. exact (@lem6779908 A K op ltle (@EMPTY K) f dom neut). Qed.
Lemma lem6779910 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem6779911 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (f : K -> A) (dom : A -> Prop) (neut : A) : (term99 A K dom neut op ltle f) = (term100 A K op ltle f dom neut).
Proof. exact (MK_COMB (@lem6779910 A) (@lem6779909 A K op ltle f dom neut)). Qed.
Lemma lem6779912 {A : Type'} (neut : A) : neut = neut.
Proof. exact (eq_refl neut). Qed.
Lemma lem6779913 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (f : K -> A) (dom : A -> Prop) (neut : A) : ((@iterato A K dom neut op ltle (@EMPTY K) f) = neut) = ((term98 A K op ltle f dom neut) = neut).
Proof. exact (MK_COMB (@lem6779911 A K op ltle f dom neut) (@lem6779912 A neut)). Qed.
Lemma lem6779914 {A K : Type'} (dom : A -> Prop) (op : type1400 A) (ltle : type1402 K) (f : K -> A) (neut : A) : ((term98 A K op ltle f dom neut) = neut) = ((@iterato A K dom neut op ltle (@EMPTY K) f) = neut).
Proof. exact (SYM (@lem6779913 A K op ltle f dom neut)). Qed.
Lemma lem6779915 {A : Type'} (x : A) : term101 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem6779916 {A : Type'} (x : A) : (term101 A x) = (term102 A x).
Proof. exact (eq_refl (term101 A x)). Qed.
Lemma lem6779917 {A : Type'} (x : A) : term102 A x.
Proof. exact (EQ_MP (@lem6779916 A x) (@lem6779915 A x)). Qed.
Lemma lem6779918 {A : Type'} (x : A) : term103 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem6779931 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem6779918 A x (@lem6779917 A x)). Qed.
Lemma lem6779932 {K : Type'} (x : K) : (@IN K x (@EMPTY K)) = False.
Proof. exact (@lem6779931 K x). Qed.
Lemma lem6779933 {K : Type'} (i : K) : (@IN K i (@EMPTY K)) = False.
Proof. exact (@lem6779932 K i). Qed.
Lemma lem6779934 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6779935 {K : Type'} (i : K) : (term104 K i) = (and False).
Proof. exact (MK_COMB (@lem6779934) (@lem6779933 K i)). Qed.
Lemma lem6779936 {A K : Type'} (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term105 A K f i dom neut) = (term105 A K f i dom neut).
Proof. exact (eq_refl (term105 A K f i dom neut)). Qed.
Lemma lem6779937 {A K : Type'} (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term106 A K f i dom neut) = (term107 A K f i dom neut).
Proof. exact (MK_COMB (@lem6779935 K i) (@lem6779936 A K f i dom neut)). Qed.
Lemma lem6779939 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem6779940 {A K : Type'} (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term107 A K f i dom neut) = False.
Proof. exact (@lem6779939 (term105 A K f i dom neut)). Qed.
Lemma lem6779941 {A K : Type'} (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term106 A K f i dom neut) = False.
Proof. exact (TRANS (@lem6779937 A K f i dom neut) (@lem6779940 A K f i dom neut)). Qed.
Lemma lem6779942 {K : Type'} (GEN_PVAR_263 : K) : (@SETSPEC K GEN_PVAR_263) = (@SETSPEC K GEN_PVAR_263).
Proof. exact (eq_refl (@SETSPEC K GEN_PVAR_263)). Qed.
Lemma lem6779943 {A K : Type'} (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) (GEN_PVAR_263 : K) : (term108 A K GEN_PVAR_263 f i dom neut) = (@SETSPEC K GEN_PVAR_263 False).
Proof. exact (MK_COMB (@lem6779942 K GEN_PVAR_263) (@lem6779941 A K f i dom neut)). Qed.
Lemma lem6779944 {K : Type'} (i : K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem6779945 {A K : Type'} (f : K -> A) (dom : A -> Prop) (neut : A) (GEN_PVAR_263 : K) (i : K) : (term109 A K GEN_PVAR_263 f dom neut i) = (@SETSPEC K GEN_PVAR_263 False i).
Proof. exact (MK_COMB (@lem6779943 A K f i dom neut GEN_PVAR_263) (@lem6779944 K i)). Qed.
Lemma lem6779946 {A K : Type'} (f : K -> A) (dom : A -> Prop) (neut : A) (GEN_PVAR_263 : K) : (term110 A K GEN_PVAR_263 f dom neut) = (term111 K GEN_PVAR_263).
Proof. exact (fun_ext (fun i : K => @lem6779945 A K f dom neut GEN_PVAR_263 i)). Qed.
Lemma lem6779947 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem6779948 {A K : Type'} (f : K -> A) (dom : A -> Prop) (neut : A) (GEN_PVAR_263 : K) : (term112 A K GEN_PVAR_263 f dom neut) = (term113 K GEN_PVAR_263).
Proof. exact (MK_COMB (@lem6779947 K) (@lem6779946 A K f dom neut GEN_PVAR_263)). Qed.
Lemma lem6779953 {A K : Type'} (f : K -> A) (dom : A -> Prop) (neut : A) : (term114 A K f dom neut) = (term115 K).
Proof. exact (fun_ext (fun GEN_PVAR_263 : K => @lem6779948 A K f dom neut GEN_PVAR_263)). Qed.
Lemma lem6779954 {K : Type'} : (@GSPEC K) = (@GSPEC K).
Proof. exact (eq_refl (@GSPEC K)). Qed.
Lemma lem6779955 {A K : Type'} (f : K -> A) (dom : A -> Prop) (neut : A) : (term116 A K f dom neut) = (term117 K).
Proof. exact (MK_COMB (@lem6779954 K) (@lem6779953 A K f dom neut)). Qed.
Lemma lem6779957 {_88295 : Type'} : (term117 _88295) = (@EMPTY _88295).
Proof. exact (EQ_MP (@lem3399706 _88295) (@lem3399757 _88295)). Qed.
Lemma lem6779958 {K : Type'} : (term117 K) = (@EMPTY K).
Proof. exact (@lem6779957 K). Qed.
Lemma lem6779959 {A K : Type'} (f : K -> A) (dom : A -> Prop) (neut : A) : (term116 A K f dom neut) = (@EMPTY K).
Proof. exact (TRANS (@lem6779955 A K f dom neut) (@lem6779958 K)). Qed.
Lemma lem6779960 {K : Type'} : (@FINITE K) = (@FINITE K).
Proof. exact (eq_refl (@FINITE K)). Qed.
Lemma lem6779961 {A K : Type'} (f : K -> A) (dom : A -> Prop) (neut : A) : (term118 A K f dom neut) = (@FINITE K (@EMPTY K)).
Proof. exact (MK_COMB (@lem6779960 K) (@lem6779959 A K f dom neut)). Qed.
Lemma lem6779962 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6779963 {A K : Type'} (f : K -> A) (dom : A -> Prop) (neut : A) : (term119 A K f dom neut) = (term120 K).
Proof. exact (MK_COMB (@lem6779962) (@lem6779961 A K f dom neut)). Qed.
Lemma lem6779973 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem6779918 A x (@lem6779917 A x)). Qed.
Lemma lem6779974 {K : Type'} (x : K) : (@IN K x (@EMPTY K)) = False.
Proof. exact (@lem6779973 K x). Qed.
Lemma lem6779975 {K : Type'} (i : K) : (@IN K i (@EMPTY K)) = False.
Proof. exact (@lem6779974 K i). Qed.
Lemma lem6779976 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6779977 {K : Type'} (i : K) : (term104 K i) = (and False).
Proof. exact (MK_COMB (@lem6779976) (@lem6779975 K i)). Qed.
Lemma lem6779978 {A K : Type'} (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term105 A K f i dom neut) = (term105 A K f i dom neut).
Proof. exact (eq_refl (term105 A K f i dom neut)). Qed.
Lemma lem6779979 {A K : Type'} (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term106 A K f i dom neut) = (term107 A K f i dom neut).
Proof. exact (MK_COMB (@lem6779977 K i) (@lem6779978 A K f i dom neut)). Qed.
Lemma lem6779981 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem6779982 {A K : Type'} (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term107 A K f i dom neut) = False.
Proof. exact (@lem6779981 (term105 A K f i dom neut)). Qed.
Lemma lem6779983 {A K : Type'} (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term106 A K f i dom neut) = False.
Proof. exact (TRANS (@lem6779979 A K f i dom neut) (@lem6779982 A K f i dom neut)). Qed.
Lemma lem6779984 {K : Type'} (GEN_PVAR_264 : K) : (@SETSPEC K GEN_PVAR_264) = (@SETSPEC K GEN_PVAR_264).
Proof. exact (eq_refl (@SETSPEC K GEN_PVAR_264)). Qed.
Lemma lem6779985 {A K : Type'} (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) (GEN_PVAR_264 : K) : (term108 A K GEN_PVAR_264 f i dom neut) = (@SETSPEC K GEN_PVAR_264 False).
Proof. exact (MK_COMB (@lem6779984 K GEN_PVAR_264) (@lem6779983 A K f i dom neut)). Qed.
Lemma lem6779986 {K : Type'} (i : K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem6779987 {A K : Type'} (f : K -> A) (dom : A -> Prop) (neut : A) (GEN_PVAR_264 : K) (i : K) : (term109 A K GEN_PVAR_264 f dom neut i) = (@SETSPEC K GEN_PVAR_264 False i).
Proof. exact (MK_COMB (@lem6779985 A K f i dom neut GEN_PVAR_264) (@lem6779986 K i)). Qed.
Lemma lem6779988 {A K : Type'} (f : K -> A) (dom : A -> Prop) (neut : A) (GEN_PVAR_264 : K) : (term110 A K GEN_PVAR_264 f dom neut) = (term111 K GEN_PVAR_264).
Proof. exact (fun_ext (fun i : K => @lem6779987 A K f dom neut GEN_PVAR_264 i)). Qed.
Lemma lem6779989 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem6779990 {A K : Type'} (f : K -> A) (dom : A -> Prop) (neut : A) (GEN_PVAR_264 : K) : (term112 A K GEN_PVAR_264 f dom neut) = (term113 K GEN_PVAR_264).
Proof. exact (MK_COMB (@lem6779989 K) (@lem6779988 A K f dom neut GEN_PVAR_264)). Qed.
Lemma lem6779995 {A K : Type'} (f : K -> A) (dom : A -> Prop) (neut : A) : (term114 A K f dom neut) = (term115 K).
Proof. exact (fun_ext (fun GEN_PVAR_264 : K => @lem6779990 A K f dom neut GEN_PVAR_264)). Qed.
Lemma lem6779996 {K : Type'} : (@GSPEC K) = (@GSPEC K).
Proof. exact (eq_refl (@GSPEC K)). Qed.
Lemma lem6779997 {A K : Type'} (f : K -> A) (dom : A -> Prop) (neut : A) : (term116 A K f dom neut) = (term117 K).
Proof. exact (MK_COMB (@lem6779996 K) (@lem6779995 A K f dom neut)). Qed.
Lemma lem6779999 {_88295 : Type'} : (term117 _88295) = (@EMPTY _88295).
Proof. exact (EQ_MP (@lem3399706 _88295) (@lem3399757 _88295)). Qed.
Lemma lem6780000 {K : Type'} : (term117 K) = (@EMPTY K).
Proof. exact (@lem6779999 K). Qed.
Lemma lem6780001 {A K : Type'} (f : K -> A) (dom : A -> Prop) (neut : A) : (term116 A K f dom neut) = (@EMPTY K).
Proof. exact (TRANS (@lem6779997 A K f dom neut) (@lem6780000 K)). Qed.
Lemma lem6780002 {K : Type'} : (@eq (K -> Prop)) = (@eq (K -> Prop)).
Proof. exact (eq_refl (@eq (K -> Prop))). Qed.
Lemma lem6780003 {A K : Type'} (f : K -> A) (dom : A -> Prop) (neut : A) : (term121 A K f dom neut) = (@eq (K -> Prop) (@EMPTY K)).
Proof. exact (MK_COMB (@lem6780002 K) (@lem6780001 A K f dom neut)). Qed.
Lemma lem6780004 {K : Type'} : (@EMPTY K) = (@EMPTY K).
Proof. exact (eq_refl (@EMPTY K)). Qed.
Lemma lem6780005 {A K : Type'} (f : K -> A) (dom : A -> Prop) (neut : A) : ((term116 A K f dom neut) = (@EMPTY K)) = ((@EMPTY K) = (@EMPTY K)).
Proof. exact (MK_COMB (@lem6780003 A K f dom neut) (@lem6780004 K)). Qed.
Lemma lem6780007 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6780008 {K : Type'} (x : K -> Prop) : (x = x) = True.
Proof. exact (@lem6780007 (K -> Prop) x). Qed.
Lemma lem6780009 {K : Type'} : ((@EMPTY K) = (@EMPTY K)) = True.
Proof. exact (@lem6780008 K (@EMPTY K)). Qed.
Lemma lem6780010 {A K : Type'} (f : K -> A) (dom : A -> Prop) (neut : A) : ((term116 A K f dom neut) = (@EMPTY K)) = True.
Proof. exact (TRANS (@lem6780005 A K f dom neut) (@lem6780009 K)). Qed.
Lemma lem6780011 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6780012 {A K : Type'} (f : K -> A) (dom : A -> Prop) (neut : A) : (term122 A K f dom neut) = (~ True).
Proof. exact (MK_COMB (@lem6780011) (@lem6780010 A K f dom neut)). Qed.
Lemma lem6780014 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem6780015 {A K : Type'} (f : K -> A) (dom : A -> Prop) (neut : A) : (term122 A K f dom neut) = False.
Proof. exact (TRANS (@lem6780012 A K f dom neut) (@lem6780014)). Qed.
Lemma lem6780016 {A K : Type'} (f : K -> A) (dom : A -> Prop) (neut : A) : (term123 A K f dom neut) = (term124 K).
Proof. exact (MK_COMB (@lem6779963 A K f dom neut) (@lem6780015 A K f dom neut)). Qed.
Lemma lem6780018 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem6780019 {K : Type'} : (term124 K) = False.
Proof. exact (@lem6780018 (@FINITE K (@EMPTY K))). Qed.
Lemma lem6780020 {A K : Type'} (f : K -> A) (dom : A -> Prop) (neut : A) : (term123 A K f dom neut) = False.
Proof. exact (TRANS (@lem6780016 A K f dom neut) (@lem6780019 K)). Qed.
Lemma lem6780021 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem6780022 {A K : Type'} (f : K -> A) (dom : A -> Prop) (neut : A) : (term125 A K f dom neut) = (@COND A False).
Proof. exact (MK_COMB (@lem6780021 A) (@lem6780020 A K f dom neut)). Qed.
Lemma lem6780036 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem6779918 A x (@lem6779917 A x)). Qed.
Lemma lem6780037 {K : Type'} (x : K) : (@IN K x (@EMPTY K)) = False.
Proof. exact (@lem6780036 K x). Qed.
Lemma lem6780038 {K : Type'} (i : K) : (@IN K i (@EMPTY K)) = False.
Proof. exact (@lem6780037 K i). Qed.
Lemma lem6780039 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6780040 {K : Type'} (i : K) : (term104 K i) = (and False).
Proof. exact (MK_COMB (@lem6780039) (@lem6780038 K i)). Qed.
Lemma lem6780054 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem6779918 A x (@lem6779917 A x)). Qed.
Lemma lem6780055 {K : Type'} (x : K) : (@IN K x (@EMPTY K)) = False.
Proof. exact (@lem6780054 K x). Qed.
Lemma lem6780056 {K : Type'} (j : K) : (@IN K j (@EMPTY K)) = False.
Proof. exact (@lem6780055 K j). Qed.
Lemma lem6780057 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6780058 {K : Type'} (j : K) : (term104 K j) = (and False).
Proof. exact (MK_COMB (@lem6780057) (@lem6780056 K j)). Qed.
Lemma lem6780059 {A K : Type'} (f : K -> A) (j : K) (dom : A -> Prop) (neut : A) : (term105 A K f j dom neut) = (term105 A K f j dom neut).
Proof. exact (eq_refl (term105 A K f j dom neut)). Qed.
Lemma lem6780060 {A K : Type'} (f : K -> A) (j : K) (dom : A -> Prop) (neut : A) : (term106 A K f j dom neut) = (term107 A K f j dom neut).
Proof. exact (MK_COMB (@lem6780058 K j) (@lem6780059 A K f j dom neut)). Qed.
Lemma lem6780062 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem6780063 {A K : Type'} (f : K -> A) (j : K) (dom : A -> Prop) (neut : A) : (term107 A K f j dom neut) = False.
Proof. exact (@lem6780062 (term105 A K f j dom neut)). Qed.
Lemma lem6780064 {A K : Type'} (f : K -> A) (j : K) (dom : A -> Prop) (neut : A) : (term106 A K f j dom neut) = False.
Proof. exact (TRANS (@lem6780060 A K f j dom neut) (@lem6780063 A K f j dom neut)). Qed.
Lemma lem6780065 {K : Type'} (ltle : type1402 K) (j : K) (i : K) : (term126 K ltle j i) = (term126 K ltle j i).
Proof. exact (eq_refl (term126 K ltle j i)). Qed.
Lemma lem6780066 {A K : Type'} (f : K -> A) (dom : A -> Prop) (neut : A) (ltle : type1402 K) (j : K) (i : K) : (term127 A K ltle i f j dom neut) = (term128 K ltle j i).
Proof. exact (MK_COMB (@lem6780065 K ltle j i) (@lem6780064 A K f j dom neut)). Qed.
Lemma lem6780068 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem6780069 {K : Type'} (ltle : type1402 K) (j : K) (i : K) : (term128 K ltle j i) = False.
Proof. exact (@lem6780068 (ltle j i)). Qed.
Lemma lem6780070 {A K : Type'} (ltle : type1402 K) (i : K) (f : K -> A) (j : K) (dom : A -> Prop) (neut : A) : (term127 A K ltle i f j dom neut) = False.
Proof. exact (TRANS (@lem6780066 A K f dom neut ltle j i) (@lem6780069 K ltle j i)). Qed.
Lemma lem6780071 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6780072 {A K : Type'} (ltle : type1402 K) (i : K) (f : K -> A) (j : K) (dom : A -> Prop) (neut : A) : (term129 A K ltle i f j dom neut) = (imp False).
Proof. exact (MK_COMB (@lem6780071) (@lem6780070 A K ltle i f j dom neut)). Qed.
Lemma lem6780075 {K : Type'} (j : K) (i : K) : (j = i) = (j = i).
Proof. exact (eq_refl (j = i)). Qed.
Lemma lem6780076 {A K : Type'} (ltle : type1402 K) (f : K -> A) (dom : A -> Prop) (neut : A) (j : K) (i : K) : (term130 A K ltle f dom neut j i) = (term131 K j i).
Proof. exact (MK_COMB (@lem6780072 A K ltle i f j dom neut) (@lem6780075 K j i)). Qed.
Lemma lem6780078 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem6780079 {K : Type'} (j : K) (i : K) : (term131 K j i) = True.
Proof. exact (@lem6780078 (j = i)). Qed.
Lemma lem6780080 {A K : Type'} (ltle : type1402 K) (f : K -> A) (dom : A -> Prop) (neut : A) (j : K) (i : K) : (term130 A K ltle f dom neut j i) = True.
Proof. exact (TRANS (@lem6780076 A K ltle f dom neut j i) (@lem6780079 K j i)). Qed.
Lemma lem6780081 {A K : Type'} (ltle : type1402 K) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term132 A K ltle f dom neut i) = (term133 K).
Proof. exact (fun_ext (fun j : K => @lem6780080 A K ltle f dom neut j i)). Qed.
Lemma lem6780082 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6780083 {A K : Type'} (ltle : type1402 K) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term134 A K ltle f dom neut i) = (term135 K).
Proof. exact (MK_COMB (@lem6780082 K) (@lem6780081 A K ltle f dom neut i)). Qed.
Lemma lem6780085 {A : Type'} (t : Prop) : (term136 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6780086 {K : Type'} (t : Prop) : (term136 K t) = t.
Proof. exact (@lem6780085 K t). Qed.
Lemma lem6780087 {K : Type'} : (term135 K) = True.
Proof. exact (@lem6780086 K True). Qed.
Lemma lem6780088 {A K : Type'} (ltle : type1402 K) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term134 A K ltle f dom neut i) = True.
Proof. exact (TRANS (@lem6780083 A K ltle f dom neut i) (@lem6780087 K)). Qed.
Lemma lem6780089 {A K : Type'} (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term137 A K f i dom neut) = (term137 A K f i dom neut).
Proof. exact (eq_refl (term137 A K f i dom neut)). Qed.
Lemma lem6780090 {A K : Type'} (ltle : type1402 K) (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term138 A K ltle f dom neut i) = (term139 A K f i dom neut).
Proof. exact (MK_COMB (@lem6780089 A K f i dom neut) (@lem6780088 A K ltle f dom neut i)). Qed.
Lemma lem6780092 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem6780093 {A K : Type'} (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term139 A K f i dom neut) = (term105 A K f i dom neut).
Proof. exact (@lem6780092 (term105 A K f i dom neut)). Qed.
Lemma lem6780094 {A K : Type'} (ltle : type1402 K) (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term138 A K ltle f dom neut i) = (term105 A K f i dom neut).
Proof. exact (TRANS (@lem6780090 A K ltle f i dom neut) (@lem6780093 A K f i dom neut)). Qed.
Lemma lem6780095 {A K : Type'} (ltle : type1402 K) (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term140 A K ltle f dom neut i) = (term107 A K f i dom neut).
Proof. exact (MK_COMB (@lem6780040 K i) (@lem6780094 A K ltle f i dom neut)). Qed.
Lemma lem6780097 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem6780098 {A K : Type'} (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term107 A K f i dom neut) = False.
Proof. exact (@lem6780097 (term105 A K f i dom neut)). Qed.
Lemma lem6780099 {A K : Type'} (ltle : type1402 K) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term140 A K ltle f dom neut i) = False.
Proof. exact (TRANS (@lem6780095 A K ltle f i dom neut) (@lem6780098 A K f i dom neut)). Qed.
Lemma lem6780100 {A K : Type'} (ltle : type1402 K) (f : K -> A) (dom : A -> Prop) (neut : A) : (term141 A K ltle f dom neut) = (term142 K).
Proof. exact (fun_ext (fun i : K => @lem6780099 A K ltle f dom neut i)). Qed.
Lemma lem6780101 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem6780102 {A K : Type'} (ltle : type1402 K) (f : K -> A) (dom : A -> Prop) (neut : A) : (term143 A K ltle f dom neut) = (term144 K).
Proof. exact (MK_COMB (@lem6780101 K) (@lem6780100 A K ltle f dom neut)). Qed.
Lemma lem6780104 {A : Type'} (t : Prop) : (term145 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem6780105 {K : Type'} (t : Prop) : (term145 K t) = t.
Proof. exact (@lem6780104 K t). Qed.
Lemma lem6780106 {K : Type'} : (term144 K) = False.
Proof. exact (@lem6780105 K False). Qed.
Lemma lem6780107 {A K : Type'} (ltle : type1402 K) (f : K -> A) (dom : A -> Prop) (neut : A) : (term143 A K ltle f dom neut) = False.
Proof. exact (TRANS (@lem6780102 A K ltle f dom neut) (@lem6780106 K)). Qed.
Lemma lem6780108 {K : Type'} : (@COND K) = (@COND K).
Proof. exact (eq_refl (@COND K)). Qed.
Lemma lem6780109 {A K : Type'} (ltle : type1402 K) (f : K -> A) (dom : A -> Prop) (neut : A) : (term146 A K ltle f dom neut) = (@COND K False).
Proof. exact (MK_COMB (@lem6780108 K) (@lem6780107 A K ltle f dom neut)). Qed.
Lemma lem6780113 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem6779918 A x (@lem6779917 A x)). Qed.
Lemma lem6780114 {K : Type'} (x : K) : (@IN K x (@EMPTY K)) = False.
Proof. exact (@lem6780113 K x). Qed.
Lemma lem6780115 {K : Type'} (i : K) : (@IN K i (@EMPTY K)) = False.
Proof. exact (@lem6780114 K i). Qed.
Lemma lem6780116 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6780117 {K : Type'} (i : K) : (term104 K i) = (and False).
Proof. exact (MK_COMB (@lem6780116) (@lem6780115 K i)). Qed.
Lemma lem6780131 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem6779918 A x (@lem6779917 A x)). Qed.
Lemma lem6780132 {K : Type'} (x : K) : (@IN K x (@EMPTY K)) = False.
Proof. exact (@lem6780131 K x). Qed.
Lemma lem6780133 {K : Type'} (j : K) : (@IN K j (@EMPTY K)) = False.
Proof. exact (@lem6780132 K j). Qed.
Lemma lem6780134 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6780135 {K : Type'} (j : K) : (term104 K j) = (and False).
Proof. exact (MK_COMB (@lem6780134) (@lem6780133 K j)). Qed.
Lemma lem6780136 {A K : Type'} (f : K -> A) (j : K) (dom : A -> Prop) (neut : A) : (term105 A K f j dom neut) = (term105 A K f j dom neut).
Proof. exact (eq_refl (term105 A K f j dom neut)). Qed.
Lemma lem6780137 {A K : Type'} (f : K -> A) (j : K) (dom : A -> Prop) (neut : A) : (term106 A K f j dom neut) = (term107 A K f j dom neut).
Proof. exact (MK_COMB (@lem6780135 K j) (@lem6780136 A K f j dom neut)). Qed.
Lemma lem6780139 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem6780140 {A K : Type'} (f : K -> A) (j : K) (dom : A -> Prop) (neut : A) : (term107 A K f j dom neut) = False.
Proof. exact (@lem6780139 (term105 A K f j dom neut)). Qed.
Lemma lem6780141 {A K : Type'} (f : K -> A) (j : K) (dom : A -> Prop) (neut : A) : (term106 A K f j dom neut) = False.
Proof. exact (TRANS (@lem6780137 A K f j dom neut) (@lem6780140 A K f j dom neut)). Qed.
Lemma lem6780142 {K : Type'} (ltle : type1402 K) (j : K) (i : K) : (term126 K ltle j i) = (term126 K ltle j i).
Proof. exact (eq_refl (term126 K ltle j i)). Qed.
Lemma lem6780143 {A K : Type'} (f : K -> A) (dom : A -> Prop) (neut : A) (ltle : type1402 K) (j : K) (i : K) : (term127 A K ltle i f j dom neut) = (term128 K ltle j i).
Proof. exact (MK_COMB (@lem6780142 K ltle j i) (@lem6780141 A K f j dom neut)). Qed.
Lemma lem6780145 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem6780146 {K : Type'} (ltle : type1402 K) (j : K) (i : K) : (term128 K ltle j i) = False.
Proof. exact (@lem6780145 (ltle j i)). Qed.
Lemma lem6780147 {A K : Type'} (ltle : type1402 K) (i : K) (f : K -> A) (j : K) (dom : A -> Prop) (neut : A) : (term127 A K ltle i f j dom neut) = False.
Proof. exact (TRANS (@lem6780143 A K f dom neut ltle j i) (@lem6780146 K ltle j i)). Qed.
Lemma lem6780148 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6780149 {A K : Type'} (ltle : type1402 K) (i : K) (f : K -> A) (j : K) (dom : A -> Prop) (neut : A) : (term129 A K ltle i f j dom neut) = (imp False).
Proof. exact (MK_COMB (@lem6780148) (@lem6780147 A K ltle i f j dom neut)). Qed.
Lemma lem6780152 {K : Type'} (j : K) (i : K) : (j = i) = (j = i).
Proof. exact (eq_refl (j = i)). Qed.
Lemma lem6780153 {A K : Type'} (ltle : type1402 K) (f : K -> A) (dom : A -> Prop) (neut : A) (j : K) (i : K) : (term130 A K ltle f dom neut j i) = (term131 K j i).
Proof. exact (MK_COMB (@lem6780149 A K ltle i f j dom neut) (@lem6780152 K j i)). Qed.
Lemma lem6780155 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem6780156 {K : Type'} (j : K) (i : K) : (term131 K j i) = True.
Proof. exact (@lem6780155 (j = i)). Qed.
Lemma lem6780157 {A K : Type'} (ltle : type1402 K) (f : K -> A) (dom : A -> Prop) (neut : A) (j : K) (i : K) : (term130 A K ltle f dom neut j i) = True.
Proof. exact (TRANS (@lem6780153 A K ltle f dom neut j i) (@lem6780156 K j i)). Qed.
Lemma lem6780158 {A K : Type'} (ltle : type1402 K) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term132 A K ltle f dom neut i) = (term133 K).
Proof. exact (fun_ext (fun j : K => @lem6780157 A K ltle f dom neut j i)). Qed.
Lemma lem6780159 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6780160 {A K : Type'} (ltle : type1402 K) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term134 A K ltle f dom neut i) = (term135 K).
Proof. exact (MK_COMB (@lem6780159 K) (@lem6780158 A K ltle f dom neut i)). Qed.
Lemma lem6780162 {A : Type'} (t : Prop) : (term136 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6780163 {K : Type'} (t : Prop) : (term136 K t) = t.
Proof. exact (@lem6780162 K t). Qed.
Lemma lem6780164 {K : Type'} : (term135 K) = True.
Proof. exact (@lem6780163 K True). Qed.
Lemma lem6780165 {A K : Type'} (ltle : type1402 K) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term134 A K ltle f dom neut i) = True.
Proof. exact (TRANS (@lem6780160 A K ltle f dom neut i) (@lem6780164 K)). Qed.
Lemma lem6780166 {A K : Type'} (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term137 A K f i dom neut) = (term137 A K f i dom neut).
Proof. exact (eq_refl (term137 A K f i dom neut)). Qed.
Lemma lem6780167 {A K : Type'} (ltle : type1402 K) (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term138 A K ltle f dom neut i) = (term139 A K f i dom neut).
Proof. exact (MK_COMB (@lem6780166 A K f i dom neut) (@lem6780165 A K ltle f dom neut i)). Qed.
Lemma lem6780169 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem6780170 {A K : Type'} (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term139 A K f i dom neut) = (term105 A K f i dom neut).
Proof. exact (@lem6780169 (term105 A K f i dom neut)). Qed.
Lemma lem6780171 {A K : Type'} (ltle : type1402 K) (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term138 A K ltle f dom neut i) = (term105 A K f i dom neut).
Proof. exact (TRANS (@lem6780167 A K ltle f i dom neut) (@lem6780170 A K f i dom neut)). Qed.
Lemma lem6780172 {A K : Type'} (ltle : type1402 K) (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term140 A K ltle f dom neut i) = (term107 A K f i dom neut).
Proof. exact (MK_COMB (@lem6780117 K i) (@lem6780171 A K ltle f i dom neut)). Qed.
Lemma lem6780174 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem6780175 {A K : Type'} (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term107 A K f i dom neut) = False.
Proof. exact (@lem6780174 (term105 A K f i dom neut)). Qed.
Lemma lem6780176 {A K : Type'} (ltle : type1402 K) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term140 A K ltle f dom neut i) = False.
Proof. exact (TRANS (@lem6780172 A K ltle f i dom neut) (@lem6780175 A K f i dom neut)). Qed.
Lemma lem6780177 {A K : Type'} (ltle : type1402 K) (f : K -> A) (dom : A -> Prop) (neut : A) : (term141 A K ltle f dom neut) = (term142 K).
Proof. exact (fun_ext (fun i : K => @lem6780176 A K ltle f dom neut i)). Qed.
Lemma lem6780178 {K : Type'} : (@ε K) = (@ε K).
Proof. exact (eq_refl (@ε K)). Qed.
Lemma lem6780179 {A K : Type'} (ltle : type1402 K) (f : K -> A) (dom : A -> Prop) (neut : A) : (term147 A K ltle f dom neut) = (term148 K).
Proof. exact (MK_COMB (@lem6780178 K) (@lem6780177 A K ltle f dom neut)). Qed.
Lemma lem6780180 {A K : Type'} (ltle : type1402 K) (f : K -> A) (dom : A -> Prop) (neut : A) : (term149 A K ltle f dom neut) = (term150 K).
Proof. exact (MK_COMB (@lem6780109 A K ltle f dom neut) (@lem6780179 A K ltle f dom neut)). Qed.
Lemma lem6780184 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem6779918 A x (@lem6779917 A x)). Qed.
Lemma lem6780185 {K : Type'} (x : K) : (@IN K x (@EMPTY K)) = False.
Proof. exact (@lem6780184 K x). Qed.
Lemma lem6780186 {K : Type'} (i : K) : (@IN K i (@EMPTY K)) = False.
Proof. exact (@lem6780185 K i). Qed.
Lemma lem6780187 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6780188 {K : Type'} (i : K) : (term104 K i) = (and False).
Proof. exact (MK_COMB (@lem6780187) (@lem6780186 K i)). Qed.
Lemma lem6780189 {A K : Type'} (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term105 A K f i dom neut) = (term105 A K f i dom neut).
Proof. exact (eq_refl (term105 A K f i dom neut)). Qed.
Lemma lem6780190 {A K : Type'} (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term106 A K f i dom neut) = (term107 A K f i dom neut).
Proof. exact (MK_COMB (@lem6780188 K i) (@lem6780189 A K f i dom neut)). Qed.
Lemma lem6780192 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem6780193 {A K : Type'} (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term107 A K f i dom neut) = False.
Proof. exact (@lem6780192 (term105 A K f i dom neut)). Qed.
Lemma lem6780194 {A K : Type'} (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term106 A K f i dom neut) = False.
Proof. exact (TRANS (@lem6780190 A K f i dom neut) (@lem6780193 A K f i dom neut)). Qed.
Lemma lem6780195 {A K : Type'} (f : K -> A) (dom : A -> Prop) (neut : A) : (term151 A K f dom neut) = (term142 K).
Proof. exact (fun_ext (fun i : K => @lem6780194 A K f i dom neut)). Qed.
Lemma lem6780196 {K : Type'} : (@ε K) = (@ε K).
Proof. exact (eq_refl (@ε K)). Qed.
Lemma lem6780197 {A K : Type'} (f : K -> A) (dom : A -> Prop) (neut : A) : (term152 A K f dom neut) = (term148 K).
Proof. exact (MK_COMB (@lem6780196 K) (@lem6780195 A K f dom neut)). Qed.
Lemma lem6780198 {A K : Type'} (ltle : type1402 K) (f : K -> A) (dom : A -> Prop) (neut : A) : (term153 A K ltle f dom neut) = (term154 K).
Proof. exact (MK_COMB (@lem6780180 A K ltle f dom neut) (@lem6780197 A K f dom neut)). Qed.
Lemma lem6780200 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem6780201 {K : Type'} (t1 : K) (t2 : K) : (@COND K False t1 t2) = t2.
Proof. exact (@lem6780200 K t1 t2). Qed.
Lemma lem6780202 {K : Type'} : (term154 K) = (term148 K).
Proof. exact (@lem6780201 K (term148 K) (term148 K)). Qed.
Lemma lem6780203 {A K : Type'} (ltle : type1402 K) (f : K -> A) (dom : A -> Prop) (neut : A) : (term153 A K ltle f dom neut) = (term148 K).
Proof. exact (TRANS (@lem6780198 A K ltle f dom neut) (@lem6780202 K)). Qed.
Lemma lem6780204 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (dom : A -> Prop) (neut : A) (f : K -> A) : (term155 A K op ltle dom neut f) = (term155 A K op ltle dom neut f).
Proof. exact (eq_refl (term155 A K op ltle dom neut f)). Qed.
Lemma lem6780205 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (dom : A -> Prop) (neut : A) (f : K -> A) : (term156 A K op ltle f dom neut) = (term157 A K op ltle dom neut f).
Proof. exact (MK_COMB (@lem6780204 A K op ltle dom neut f) (@lem6780203 A K ltle f dom neut)). Qed.
Lemma lem6780206 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (dom : A -> Prop) (neut : A) (f : K -> A) : (term158 A K op ltle f dom neut) = (term159 A K op ltle dom neut f).
Proof. exact (MK_COMB (@lem6780022 A K f dom neut) (@lem6780205 A K op ltle dom neut f)). Qed.
Lemma lem6780207 {A : Type'} (neut : A) : neut = neut.
Proof. exact (eq_refl neut). Qed.
Lemma lem6780208 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (dom : A -> Prop) (f : K -> A) (neut : A) : (term98 A K op ltle f dom neut) = (term160 A K op ltle dom f neut).
Proof. exact (MK_COMB (@lem6780206 A K op ltle dom neut f) (@lem6780207 A neut)). Qed.
Lemma lem6780210 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem6780211 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (@lem6780210 A t1 t2). Qed.
Lemma lem6780212 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (dom : A -> Prop) (f : K -> A) (neut : A) : (term160 A K op ltle dom f neut) = neut.
Proof. exact (@lem6780211 A (term157 A K op ltle dom neut f) neut). Qed.
Lemma lem6780213 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (f : K -> A) (dom : A -> Prop) (neut : A) : (term98 A K op ltle f dom neut) = neut.
Proof. exact (TRANS (@lem6780208 A K op ltle dom f neut) (@lem6780212 A K op ltle dom f neut)). Qed.
Lemma lem6780214 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem6780215 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (f : K -> A) (dom : A -> Prop) (neut : A) : (term100 A K op ltle f dom neut) = (@eq A neut).
Proof. exact (MK_COMB (@lem6780214 A) (@lem6780213 A K op ltle f dom neut)). Qed.
Lemma lem6780216 {A : Type'} (neut : A) : neut = neut.
Proof. exact (eq_refl neut). Qed.
Lemma lem6780217 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (f : K -> A) (dom : A -> Prop) (neut : A) : ((term98 A K op ltle f dom neut) = neut) = (neut = neut).
Proof. exact (MK_COMB (@lem6780215 A K op ltle f dom neut) (@lem6780216 A neut)). Qed.
Lemma lem6780219 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6780220 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem6780219 A x). Qed.
Lemma lem6780221 {A : Type'} (neut : A) : (neut = neut) = True.
Proof. exact (@lem6780220 A neut). Qed.
Lemma lem6780222 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (f : K -> A) (dom : A -> Prop) (neut : A) : ((term98 A K op ltle f dom neut) = neut) = True.
Proof. exact (TRANS (@lem6780217 A K op ltle f dom neut) (@lem6780221 A neut)). Qed.
Lemma lem6780223 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (f : K -> A) (dom : A -> Prop) (neut : A) : True = ((term98 A K op ltle f dom neut) = neut).
Proof. exact (SYM (@lem6780222 A K op ltle f dom neut)). Qed.
Lemma lem6780224 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (f : K -> A) (dom : A -> Prop) (neut : A) : (term98 A K op ltle f dom neut) = neut.
Proof. exact (EQ_MP (@lem6780223 A K op ltle f dom neut) (@lem0)). Qed.
Lemma lem6780225 {A K : Type'} (dom : A -> Prop) (op : type1400 A) (ltle : type1402 K) (f : K -> A) (neut : A) : (@iterato A K dom neut op ltle (@EMPTY K) f) = neut.
Proof. exact (EQ_MP (@lem6779914 A K dom op ltle f neut) (@lem6780224 A K op ltle f dom neut)). Qed.
Lemma lem6780226 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term161 A K k f dom neut) : term161 A K k f dom neut.
Proof. exact (h1). Qed.
Lemma lem6780227 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term162 A K k f dom neut) : term162 A K k f dom neut.
Proof. exact (h1). Qed.
Lemma lem6780228 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term163 A K k f dom neut) : term163 A K k f dom neut.
Proof. exact (h1). Qed.
Lemma lem6780230 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (@iterato A K dom neut op ltle k f) = (term97 A K op ltle k f dom neut).
Proof. exact (EQ_MP (@lem6779886 A K op ltle k f dom neut) (@lem6779885 A K op ltle k dom neut f)). Qed.
Lemma lem6780231 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (@iterato A K dom neut op ltle k f) = (term97 A K op ltle k f dom neut).
Proof. exact (@lem6780230 A K op ltle k f dom neut). Qed.
Lemma lem6780232 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem6780233 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term164 A K dom neut op ltle k f) = (term165 A K op ltle k f dom neut).
Proof. exact (MK_COMB (@lem6780232 A) (@lem6780231 A K op ltle k f dom neut)). Qed.
Lemma lem6780234 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i : K) (f : K -> A) : (term166 A K dom neut op ltle k i f) = (term166 A K dom neut op ltle k i f).
Proof. exact (eq_refl (term166 A K dom neut op ltle k i f)). Qed.
Lemma lem6780235 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i : K) (f : K -> A) : ((@iterato A K dom neut op ltle k f) = (term166 A K dom neut op ltle k i f)) = ((term97 A K op ltle k f dom neut) = (term166 A K dom neut op ltle k i f)).
Proof. exact (MK_COMB (@lem6780233 A K op ltle k f dom neut) (@lem6780234 A K dom neut op ltle k i f)). Qed.
Lemma lem6780236 {A K : Type'} (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term137 A K f i dom neut) = (term137 A K f i dom neut).
Proof. exact (eq_refl (term137 A K f i dom neut)). Qed.
Lemma lem6780237 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i : K) (f : K -> A) : (term167 A K dom neut op ltle k i f) = (term168 A K dom neut op ltle k i f).
Proof. exact (MK_COMB (@lem6780236 A K f i dom neut) (@lem6780235 A K dom neut op ltle k i f)). Qed.
Lemma lem6780238 {K : Type'} (i : K) (k : K -> Prop) : (term169 K i k) = (term169 K i k).
Proof. exact (eq_refl (term169 K i k)). Qed.
Lemma lem6780239 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i : K) (f : K -> A) : (term170 A K dom neut op ltle k i f) = (term171 A K dom neut op ltle k i f).
Proof. exact (MK_COMB (@lem6780238 K i k) (@lem6780237 A K dom neut op ltle k i f)). Qed.
Lemma lem6780240 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) : (term172 A K dom neut op ltle k f) = (term173 A K dom neut op ltle k f).
Proof. exact (fun_ext (fun i : K => @lem6780239 A K dom neut op ltle k i f)). Qed.
Lemma lem6780241 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem6780242 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) : (term174 A K dom neut op ltle k f) = (term175 A K dom neut op ltle k f).
Proof. exact (MK_COMB (@lem6780241 K) (@lem6780240 A K dom neut op ltle k f)). Qed.
Lemma lem6780243 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) : (term175 A K dom neut op ltle k f) = (term174 A K dom neut op ltle k f).
Proof. exact (SYM (@lem6780242 A K dom neut op ltle k f)). Qed.
Lemma lem6780244 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term163 A K k f dom neut) = ((term163 A K k f dom neut) = True).
Proof. exact (@lem7 (term163 A K k f dom neut)). Qed.
Lemma lem6780246 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : term176 A K k f dom neut.
Proof. exact (@lem82 ((term177 A K k f dom neut) = (@EMPTY K))). Qed.
Lemma lem6780272 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term163 A K k f dom neut) : (term163 A K k f dom neut) = True.
Proof. exact (EQ_MP (@lem6780244 A K k f dom neut) (@lem6780228 A K k f dom neut h1)). Qed.
Lemma lem6780273 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term163 A K k f dom neut) : (term163 A K k f dom neut) = True.
Proof. exact (@lem6780272 A K k f dom neut h1). Qed.
Lemma lem6780274 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6780275 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term163 A K k f dom neut) : (term178 A K k f dom neut) = (and True).
Proof. exact (MK_COMB (@lem6780274) (@lem6780273 A K k f dom neut h1)). Qed.
Lemma lem6780277 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term162 A K k f dom neut) : ((term177 A K k f dom neut) = (@EMPTY K)) = False.
Proof. exact (@lem6780246 A K k f dom neut (@lem6780227 A K k f dom neut h1)). Qed.
Lemma lem6780278 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term162 A K k f dom neut) : ((term177 A K k f dom neut) = (@EMPTY K)) = False.
Proof. exact (@lem6780277 A K k f dom neut h1). Qed.
Lemma lem6780279 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6780280 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term162 A K k f dom neut) : (term162 A K k f dom neut) = (~ False).
Proof. exact (MK_COMB (@lem6780279) (@lem6780278 A K k f dom neut h1)). Qed.
Lemma lem6780282 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem6780283 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term162 A K k f dom neut) : (term162 A K k f dom neut) = True.
Proof. exact (TRANS (@lem6780280 A K k f dom neut h1) (@lem6780282)). Qed.
Lemma lem6780284 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term163 A K k f dom neut) (h2 : term162 A K k f dom neut) : (term161 A K k f dom neut) = (True /\ True).
Proof. exact (MK_COMB (@lem6780275 A K k f dom neut h1) (@lem6780283 A K k f dom neut h2)). Qed.
Lemma lem6780286 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6780287 : (True /\ True) = True.
Proof. exact (@lem6780286 True). Qed.
Lemma lem6780288 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term163 A K k f dom neut) (h2 : term162 A K k f dom neut) : (term161 A K k f dom neut) = True.
Proof. exact (TRANS (@lem6780284 A K k f dom neut h1 h2) (@lem6780287)). Qed.
Lemma lem6780289 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem6780290 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term163 A K k f dom neut) (h2 : term162 A K k f dom neut) : (term179 A K k f dom neut) = (@COND A True).
Proof. exact (MK_COMB (@lem6780289 A) (@lem6780288 A K k f dom neut h1 h2)). Qed.
Lemma lem6780335 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term180 A K op ltle k f dom neut) = (term180 A K op ltle k f dom neut).
Proof. exact (eq_refl (term180 A K op ltle k f dom neut)). Qed.
Lemma lem6780336 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term163 A K k f dom neut) (h2 : term162 A K k f dom neut) : (term181 A K op ltle k f dom neut) = (term182 A K op ltle k f dom neut).
Proof. exact (MK_COMB (@lem6780290 A K k f dom neut h1 h2) (@lem6780335 A K op ltle k f dom neut)). Qed.
Lemma lem6780337 {A : Type'} (neut : A) : neut = neut.
Proof. exact (eq_refl neut). Qed.
Lemma lem6780338 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term163 A K k f dom neut) (h2 : term162 A K k f dom neut) : (term97 A K op ltle k f dom neut) = (term183 A K op ltle k f dom neut).
Proof. exact (MK_COMB (@lem6780336 A K op ltle k f dom neut h1 h2) (@lem6780337 A neut)). Qed.
Lemma lem6780340 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem6780341 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (@lem6780340 A t2 t1). Qed.
Lemma lem6780342 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term183 A K op ltle k f dom neut) = (term180 A K op ltle k f dom neut).
Proof. exact (@lem6780341 A neut (term180 A K op ltle k f dom neut)). Qed.
Lemma lem6780387 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term163 A K k f dom neut) (h2 : term162 A K k f dom neut) : (term97 A K op ltle k f dom neut) = (term180 A K op ltle k f dom neut).
Proof. exact (TRANS (@lem6780338 A K op ltle k f dom neut h1 h2) (@lem6780342 A K op ltle k f dom neut)). Qed.
Lemma lem6780388 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem6780389 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term163 A K k f dom neut) (h2 : term162 A K k f dom neut) : (term165 A K op ltle k f dom neut) = (term184 A K op ltle k f dom neut).
Proof. exact (MK_COMB (@lem6780388 A) (@lem6780387 A K op ltle k f dom neut h1 h2)). Qed.
Lemma lem6780390 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i : K) (f : K -> A) : (term166 A K dom neut op ltle k i f) = (term166 A K dom neut op ltle k i f).
Proof. exact (eq_refl (term166 A K dom neut op ltle k i f)). Qed.
Lemma lem6780391 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (i : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term163 A K k f dom neut) (h2 : term162 A K k f dom neut) : ((term97 A K op ltle k f dom neut) = (term166 A K dom neut op ltle k i f)) = ((term180 A K op ltle k f dom neut) = (term166 A K dom neut op ltle k i f)).
Proof. exact (MK_COMB (@lem6780389 A K op ltle k f dom neut h1 h2) (@lem6780390 A K dom neut op ltle k i f)). Qed.
Lemma lem6780394 {A K : Type'} (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term137 A K f i dom neut) = (term137 A K f i dom neut).
Proof. exact (eq_refl (term137 A K f i dom neut)). Qed.
Lemma lem6780395 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (i : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term163 A K k f dom neut) (h2 : term162 A K k f dom neut) : (term168 A K dom neut op ltle k i f) = (term185 A K dom neut op ltle k i f).
Proof. exact (MK_COMB (@lem6780394 A K f i dom neut) (@lem6780391 A K op ltle i k f dom neut h1 h2)). Qed.
Lemma lem6780398 {K : Type'} (i : K) (k : K -> Prop) : (term169 K i k) = (term169 K i k).
Proof. exact (eq_refl (term169 K i k)). Qed.
Lemma lem6780399 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (i : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term163 A K k f dom neut) (h2 : term162 A K k f dom neut) : (term171 A K dom neut op ltle k i f) = (term186 A K dom neut op ltle k i f).
Proof. exact (MK_COMB (@lem6780398 K i k) (@lem6780395 A K op ltle i k f dom neut h1 h2)). Qed.
Lemma lem6780402 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term163 A K k f dom neut) (h2 : term162 A K k f dom neut) : (term173 A K dom neut op ltle k f) = (term187 A K dom neut op ltle k f).
Proof. exact (fun_ext (fun i : K => @lem6780399 A K op ltle i k f dom neut h1 h2)). Qed.
Lemma lem6780403 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem6780404 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term163 A K k f dom neut) (h2 : term162 A K k f dom neut) : (term175 A K dom neut op ltle k f) = (term188 A K dom neut op ltle k f).
Proof. exact (MK_COMB (@lem6780403 K) (@lem6780402 A K op ltle k f dom neut h1 h2)). Qed.
Lemma lem6780409 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term163 A K k f dom neut) (h2 : term162 A K k f dom neut) : (term188 A K dom neut op ltle k f) = (term175 A K dom neut op ltle k f).
Proof. exact (SYM (@lem6780404 A K op ltle k f dom neut h1 h2)). Qed.
Lemma lem6780413 {A K : Type'} (i : K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : i = (term189 A K ltle k f dom neut)) : i = (term189 A K ltle k f dom neut).
Proof. exact (h1). Qed.
Lemma lem6780414 {A K : Type'} (i : K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : i = (term189 A K ltle k f dom neut)) : term190 A K ltle k f dom neut.
Proof. exact (ex_intro (term191 A K ltle k f dom neut) i (@lem6780413 A K i ltle k f dom neut h1)). Qed.
Lemma lem6780415 {A K : Type'} (i : K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : term192 A K i ltle k f dom neut.
Proof. exact (fun h0 : i = (term189 A K ltle k f dom neut) => @lem6780414 A K i ltle k f dom neut h0). Qed.
Lemma lem6780416 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : term193 A K ltle k f dom neut.
Proof. exact (@lem6780415 A K (term189 A K ltle k f dom neut) ltle k f dom neut). Qed.
Lemma lem6780426 {_5989 : Type'} (x : _5989) : (x = x) = True.
Proof. exact (EQ_MP (@lem68127 _5989 x) (@lem0)). Qed.
Lemma lem6780427 {K : Type'} (x : K) : (x = x) = True.
Proof. exact (@lem6780426 K x). Qed.
Lemma lem6780428 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : ((term189 A K ltle k f dom neut) = (term189 A K ltle k f dom neut)) = True.
Proof. exact (@lem6780427 K (term189 A K ltle k f dom neut)). Qed.
Lemma lem6780429 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6780430 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term194 A K ltle k f dom neut) = (imp True).
Proof. exact (MK_COMB (@lem6780429) (@lem6780428 A K ltle k f dom neut)). Qed.
Lemma lem6780431 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term190 A K ltle k f dom neut) = (term190 A K ltle k f dom neut).
Proof. exact (eq_refl (term190 A K ltle k f dom neut)). Qed.
Lemma lem6780432 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term193 A K ltle k f dom neut) = (term195 A K ltle k f dom neut).
Proof. exact (MK_COMB (@lem6780430 A K ltle k f dom neut) (@lem6780431 A K ltle k f dom neut)). Qed.
Lemma lem6780433 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : term195 A K ltle k f dom neut.
Proof. exact (EQ_MP (@lem6780432 A K ltle k f dom neut) (@lem6780416 A K ltle k f dom neut)). Qed.
Lemma lem6780434 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : term190 A K ltle k f dom neut.
Proof. exact (@lem6780433 A K ltle k f dom neut (@lem0)). Qed.
Lemma lem6780435 {A K : Type'} (i : K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : i = (term189 A K ltle k f dom neut)) : i = (term189 A K ltle k f dom neut).
Proof. exact (h1). Qed.
Lemma lem6780436 {A K : Type'} (i : K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : i = (term189 A K ltle k f dom neut)) : (term189 A K ltle k f dom neut) = i.
Proof. exact (SYM (@lem6780435 A K i ltle k f dom neut h1)). Qed.
Lemma lem6780437 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) : (term196 A K dom neut op ltle k f) = (term196 A K dom neut op ltle k f).
Proof. exact (eq_refl (term196 A K dom neut op ltle k f)). Qed.
Lemma lem6780438 {A K : Type'} (op : type1400 A) (i : K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : i = (term189 A K ltle k f dom neut)) : (term197 A K op ltle k f dom neut) = (term198 A K dom neut op ltle k f i).
Proof. exact (MK_COMB (@lem6780437 A K dom neut op ltle k f) (@lem6780436 A K i ltle k f dom neut h1)). Qed.
Lemma lem6780439 {A K : Type'} (i : K) (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) : (term198 A K dom neut op ltle k f i) = (term199 A K i dom neut op ltle k f).
Proof. exact (eq_refl (term198 A K dom neut op ltle k f i)). Qed.
Lemma lem6780440 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term200 A K op ltle k f dom neut) = (term200 A K op ltle k f dom neut).
Proof. exact (eq_refl (term200 A K op ltle k f dom neut)). Qed.
Lemma lem6780441 {A K : Type'} (i : K) (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) : ((term197 A K op ltle k f dom neut) = (term198 A K dom neut op ltle k f i)) = ((term197 A K op ltle k f dom neut) = (term199 A K i dom neut op ltle k f)).
Proof. exact (MK_COMB (@lem6780440 A K op ltle k f dom neut) (@lem6780439 A K i dom neut op ltle k f)). Qed.
Lemma lem6780442 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) : (term197 A K op ltle k f dom neut) = (term188 A K dom neut op ltle k f).
Proof. exact (eq_refl (term197 A K op ltle k f dom neut)). Qed.
Lemma lem6780443 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6780444 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) : (term200 A K op ltle k f dom neut) = (term201 A K dom neut op ltle k f).
Proof. exact (MK_COMB (@lem6780443) (@lem6780442 A K dom neut op ltle k f)). Qed.
Lemma lem6780445 {A K : Type'} (i : K) (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) : (term199 A K i dom neut op ltle k f) = (term199 A K i dom neut op ltle k f).
Proof. exact (eq_refl (term199 A K i dom neut op ltle k f)). Qed.
Lemma lem6780446 {A K : Type'} (i : K) (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) : ((term197 A K op ltle k f dom neut) = (term199 A K i dom neut op ltle k f)) = ((term188 A K dom neut op ltle k f) = (term199 A K i dom neut op ltle k f)).
Proof. exact (MK_COMB (@lem6780444 A K dom neut op ltle k f) (@lem6780445 A K i dom neut op ltle k f)). Qed.
Lemma lem6780447 {A K : Type'} (i : K) (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) : ((term197 A K op ltle k f dom neut) = (term198 A K dom neut op ltle k f i)) = ((term188 A K dom neut op ltle k f) = (term199 A K i dom neut op ltle k f)).
Proof. exact (TRANS (@lem6780441 A K i dom neut op ltle k f) (@lem6780446 A K i dom neut op ltle k f)). Qed.
Lemma lem6780448 {A K : Type'} (op : type1400 A) (i : K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : i = (term189 A K ltle k f dom neut)) : (term188 A K dom neut op ltle k f) = (term199 A K i dom neut op ltle k f).
Proof. exact (EQ_MP (@lem6780447 A K i dom neut op ltle k f) (@lem6780438 A K op i ltle k f dom neut h1)). Qed.
Lemma lem6780449 {A K : Type'} (op : type1400 A) (i : K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : i = (term189 A K ltle k f dom neut)) : (term199 A K i dom neut op ltle k f) = (term188 A K dom neut op ltle k f).
Proof. exact (SYM (@lem6780448 A K op i ltle k f dom neut h1)). Qed.
Lemma lem6780463 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term163 A K k f dom neut) : term163 A K k f dom neut.
Proof. exact (h1). Qed.
Lemma lem6780477 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term162 A K k f dom neut) : term162 A K k f dom neut.
Proof. exact (h1). Qed.
Lemma lem6780479 {A B : Type'} (f : A -> B) (x : A) : (@LET A B f x) = (f x).
Proof. exact (EQ_MP (@lem57692 A B f x) (@lem57691 A B f x)). Qed.
Lemma lem6780480 {A K : Type'} (f : K -> A) (x : K) : (@LET K A f x) = (f x).
Proof. exact (@lem6780479 K A f x). Qed.
Lemma lem6780481 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) (f : K -> A) (i : K) : (term202 A K op ltle k dom neut f i) = (term203 A K op ltle k dom neut f i).
Proof. exact (@lem6780480 A K (term204 A K op ltle k dom neut f) i). Qed.
Lemma lem6780482 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i : K) (dom : A -> Prop) (neut : A) (f : K -> A) : (term203 A K op ltle k dom neut f i) = (term205 A K op ltle k i dom neut f).
Proof. exact (eq_refl (term203 A K op ltle k dom neut f i)). Qed.
Lemma lem6780483 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i : K) (dom : A -> Prop) (neut : A) (f : K -> A) : (term202 A K op ltle k dom neut f i) = (term205 A K op ltle k i dom neut f).
Proof. exact (TRANS (@lem6780481 A K op ltle k dom neut f i) (@lem6780482 A K op ltle k i dom neut f)). Qed.
Lemma lem6780485 {A : Type'} (t : A) : (@LET_END A t) = t.
Proof. exact (EQ_MP (@lem57695 A t) (@lem57694 A t)). Qed.
Lemma lem6780486 {A : Type'} (t : A) : (@LET_END A t) = t.
Proof. exact (@lem6780485 A t). Qed.
Lemma lem6780487 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i : K) (dom : A -> Prop) (neut : A) (f : K -> A) : (term205 A K op ltle k i dom neut f) = (term206 A K op ltle k i dom neut f).
Proof. exact (@lem6780486 A (term206 A K op ltle k i dom neut f)). Qed.
Lemma lem6780488 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i : K) (dom : A -> Prop) (neut : A) (f : K -> A) : (term202 A K op ltle k dom neut f i) = (term206 A K op ltle k i dom neut f).
Proof. exact (TRANS (@lem6780483 A K op ltle k i dom neut f) (@lem6780487 A K op ltle k i dom neut f)). Qed.
Lemma lem6780489 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem6780490 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i : K) (dom : A -> Prop) (neut : A) (f : K -> A) : (term207 A K op ltle k dom neut f i) = (term208 A K op ltle k i dom neut f).
Proof. exact (MK_COMB (@lem6780489 A) (@lem6780488 A K op ltle k i dom neut f)). Qed.
Lemma lem6780491 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i' : K) (f : K -> A) : (term166 A K dom neut op ltle k i' f) = (term166 A K dom neut op ltle k i' f).
Proof. exact (eq_refl (term166 A K dom neut op ltle k i' f)). Qed.
Lemma lem6780492 {A K : Type'} (i : K) (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i' : K) (f : K -> A) : ((term202 A K op ltle k dom neut f i) = (term166 A K dom neut op ltle k i' f)) = ((term206 A K op ltle k i dom neut f) = (term166 A K dom neut op ltle k i' f)).
Proof. exact (MK_COMB (@lem6780490 A K op ltle k i dom neut f) (@lem6780491 A K dom neut op ltle k i' f)). Qed.
Lemma lem6780493 {A K : Type'} (f : K -> A) (i' : K) (dom : A -> Prop) (neut : A) : (term137 A K f i' dom neut) = (term137 A K f i' dom neut).
Proof. exact (eq_refl (term137 A K f i' dom neut)). Qed.
Lemma lem6780494 {A K : Type'} (i : K) (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i' : K) (f : K -> A) : (term209 A K i dom neut op ltle k i' f) = (term210 A K i dom neut op ltle k i' f).
Proof. exact (MK_COMB (@lem6780493 A K f i' dom neut) (@lem6780492 A K i dom neut op ltle k i' f)). Qed.
Lemma lem6780495 {K : Type'} (i' : K) (k : K -> Prop) : (term169 K i' k) = (term169 K i' k).
Proof. exact (eq_refl (term169 K i' k)). Qed.
Lemma lem6780496 {A K : Type'} (i : K) (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i' : K) (f : K -> A) : (term211 A K i dom neut op ltle k i' f) = (term212 A K i dom neut op ltle k i' f).
Proof. exact (MK_COMB (@lem6780495 K i' k) (@lem6780494 A K i dom neut op ltle k i' f)). Qed.
Lemma lem6780497 {A K : Type'} (i : K) (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) : (term213 A K i dom neut op ltle k f) = (term214 A K i dom neut op ltle k f).
Proof. exact (fun_ext (fun i' : K => @lem6780496 A K i dom neut op ltle k i' f)). Qed.
Lemma lem6780498 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem6780499 {A K : Type'} (i : K) (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) : (term199 A K i dom neut op ltle k f) = (term215 A K i dom neut op ltle k f).
Proof. exact (MK_COMB (@lem6780498 K) (@lem6780497 A K i dom neut op ltle k f)). Qed.
Lemma lem6780500 {A K : Type'} (i : K) (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) : (term215 A K i dom neut op ltle k f) = (term199 A K i dom neut op ltle k f).
Proof. exact (SYM (@lem6780499 A K i dom neut op ltle k f)). Qed.
Lemma lem6780502 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) (f : K -> A) : (@iterato A K dom neut op ltle k f) = (term55 A K op ltle k dom neut f).
Proof. exact (EQ_MP (@lem6779868 A K op ltle k dom neut f) (@lem6779867 A K op ltle k dom neut f)). Qed.
Lemma lem6780503 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) (f : K -> A) : (@iterato A K dom neut op ltle k f) = (term55 A K op ltle k dom neut f).
Proof. exact (@lem6780502 A K op ltle k dom neut f). Qed.
Lemma lem6780504 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i' : K) (dom : A -> Prop) (neut : A) (f : K -> A) : (term216 A K dom neut op ltle k i' f) = (term217 A K op ltle k i' dom neut f).
Proof. exact (@lem6780503 A K op ltle (@DELETE K k i') dom neut f). Qed.
Lemma lem6780505 {A K : Type'} (op : type1400 A) (f : K -> A) (i' : K) : (term218 A K op f i') = (term218 A K op f i').
Proof. exact (eq_refl (term218 A K op f i')). Qed.
Lemma lem6780506 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i' : K) (dom : A -> Prop) (neut : A) (f : K -> A) : (term166 A K dom neut op ltle k i' f) = (term206 A K op ltle k i' dom neut f).
Proof. exact (MK_COMB (@lem6780505 A K op f i') (@lem6780504 A K op ltle k i' dom neut f)). Qed.
Lemma lem6780507 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i : K) (dom : A -> Prop) (neut : A) (f : K -> A) : (term208 A K op ltle k i dom neut f) = (term208 A K op ltle k i dom neut f).
Proof. exact (eq_refl (term208 A K op ltle k i dom neut f)). Qed.
Lemma lem6780508 {A K : Type'} (i : K) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i' : K) (dom : A -> Prop) (neut : A) (f : K -> A) : ((term206 A K op ltle k i dom neut f) = (term166 A K dom neut op ltle k i' f)) = ((term206 A K op ltle k i dom neut f) = (term206 A K op ltle k i' dom neut f)).
Proof. exact (MK_COMB (@lem6780507 A K op ltle k i dom neut f) (@lem6780506 A K op ltle k i' dom neut f)). Qed.
Lemma lem6780509 {A K : Type'} (f : K -> A) (i' : K) (dom : A -> Prop) (neut : A) : (term137 A K f i' dom neut) = (term137 A K f i' dom neut).
Proof. exact (eq_refl (term137 A K f i' dom neut)). Qed.
Lemma lem6780510 {A K : Type'} (i : K) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i' : K) (dom : A -> Prop) (neut : A) (f : K -> A) : (term210 A K i dom neut op ltle k i' f) = (term219 A K i op ltle k i' dom neut f).
Proof. exact (MK_COMB (@lem6780509 A K f i' dom neut) (@lem6780508 A K i op ltle k i' dom neut f)). Qed.
Lemma lem6780511 {K : Type'} (i' : K) (k : K -> Prop) : (term169 K i' k) = (term169 K i' k).
Proof. exact (eq_refl (term169 K i' k)). Qed.
Lemma lem6780512 {A K : Type'} (i : K) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i' : K) (dom : A -> Prop) (neut : A) (f : K -> A) : (term212 A K i dom neut op ltle k i' f) = (term220 A K i op ltle k i' dom neut f).
Proof. exact (MK_COMB (@lem6780511 K i' k) (@lem6780510 A K i op ltle k i' dom neut f)). Qed.
Lemma lem6780513 {A K : Type'} (i : K) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) (f : K -> A) : (term214 A K i dom neut op ltle k f) = (term221 A K i op ltle k dom neut f).
Proof. exact (fun_ext (fun i' : K => @lem6780512 A K i op ltle k i' dom neut f)). Qed.
Lemma lem6780514 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem6780515 {A K : Type'} (i : K) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) (f : K -> A) : (term215 A K i dom neut op ltle k f) = (term222 A K i op ltle k dom neut f).
Proof. exact (MK_COMB (@lem6780514 K) (@lem6780513 A K i op ltle k dom neut f)). Qed.
Lemma lem6780516 {A K : Type'} (i : K) (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) : (term222 A K i op ltle k dom neut f) = (term215 A K i dom neut op ltle k f).
Proof. exact (SYM (@lem6780515 A K i op ltle k dom neut f)). Qed.
Lemma lem6780518 {_125019 : Type'} (t : _125019) (i : _125019) (P : _125019 -> Prop) : term1 _125019 t i P.
Proof. exact (EQ_MP (@lem6779355 _125019 t i P) (@lem6779820 _125019 t i P)). Qed.
Lemma lem6780519 {K : Type'} (t : K) (i : K) (P : K -> Prop) : term1 K t i P.
Proof. exact (@lem6780518 K t i P). Qed.
Lemma lem6780520 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (P : K -> Prop) : term223 A K ltle k f dom neut i P.
Proof. exact (@lem6780519 K (term189 A K ltle k f dom neut) i P). Qed.
Lemma lem6780521 {A K : Type'} (P : K -> Prop) (i : K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : i = (term189 A K ltle k f dom neut)) : term224 A K ltle k f dom neut i P.
Proof. exact (@lem6780520 A K ltle k f dom neut i P (@lem6780436 A K i ltle k f dom neut h1)). Qed.
Lemma lem6780522 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (P : K -> Prop) (h1 : term224 A K ltle k f dom neut i P) : term224 A K ltle k f dom neut i P.
Proof. exact (h1). Qed.
Lemma lem6780523 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (P : K -> Prop) (i : K) (h1 : term225 A K ltle k f dom neut P i) : term225 A K ltle k f dom neut P i.
Proof. exact (h1). Qed.
Lemma lem6780524 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (P : K -> Prop) (h1 : term225 A K ltle k f dom neut P i) (h2 : term224 A K ltle k f dom neut i P) : term22 K P.
Proof. exact (@lem6780522 A K ltle k f dom neut i P h2 (@lem6780523 A K ltle k f dom neut P i h1)). Qed.
Lemma lem6780525 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (P : K -> Prop) (i : K) (h1 : term225 A K ltle k f dom neut P i) : term226 A K ltle k f dom neut i P.
Proof. exact (fun h0 : term224 A K ltle k f dom neut i P => @lem6780524 A K ltle k f dom neut i P h1 h0). Qed.
Lemma lem6780526 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (P : K -> Prop) (h1 : term224 A K ltle k f dom neut i P) : term224 A K ltle k f dom neut i P.
Proof. exact (h1). Qed.
Lemma lem6780527 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (P : K -> Prop) (h1 : term225 A K ltle k f dom neut P i) (h2 : term224 A K ltle k f dom neut i P) : term22 K P.
Proof. exact (@lem6780525 A K ltle k f dom neut P i h1 (@lem6780526 A K ltle k f dom neut i P h2)). Qed.
Lemma lem6780528 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (P : K -> Prop) (h1 : term224 A K ltle k f dom neut i P) : term224 A K ltle k f dom neut i P.
Proof. exact (fun h0 : term225 A K ltle k f dom neut P i => @lem6780527 A K ltle k f dom neut i P h0 h1). Qed.
Lemma lem6780529 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (P : K -> Prop) : term227 A K ltle k f dom neut i P.
Proof. exact (fun h0 : term224 A K ltle k f dom neut i P => @lem6780528 A K ltle k f dom neut i P h0). Qed.
Lemma lem6780532 {A K : Type'} (P : K -> Prop) (i : K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : i = (term189 A K ltle k f dom neut)) : term224 A K ltle k f dom neut i P.
Proof. exact (@lem6780529 A K ltle k f dom neut i P (@lem6780521 A K P i ltle k f dom neut h1)). Qed.
Lemma lem6780533 {A K : Type'} (P : K -> Prop) (i : K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : i = (term189 A K ltle k f dom neut)) : term224 A K ltle k f dom neut i P.
Proof. exact (@lem6780532 A K P i ltle k f dom neut h1). Qed.
Lemma lem6780534 {A K : Type'} (op : type1400 A) (i : K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : i = (term189 A K ltle k f dom neut)) : term228 A K i op ltle k dom neut f.
Proof. exact (@lem6780533 A K (term221 A K i op ltle k dom neut f) i ltle k f dom neut h1). Qed.
Lemma lem6780535 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i : K) (dom : A -> Prop) (neut : A) (f : K -> A) : (term229 A K op ltle k dom neut f i) = (term230 A K op ltle k i dom neut f).
Proof. exact (eq_refl (term229 A K op ltle k dom neut f i)). Qed.
Lemma lem6780536 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term231 A K ltle k f dom neut i) = (term231 A K ltle k f dom neut i).
Proof. exact (eq_refl (term231 A K ltle k f dom neut i)). Qed.
Lemma lem6780537 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i : K) (dom : A -> Prop) (neut : A) (f : K -> A) : (term232 A K op ltle k dom neut f i) = (term233 A K op ltle k i dom neut f).
Proof. exact (MK_COMB (@lem6780536 A K ltle k f dom neut i) (@lem6780535 A K op ltle k i dom neut f)). Qed.
Lemma lem6780538 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6780539 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i : K) (dom : A -> Prop) (neut : A) (f : K -> A) : (term234 A K op ltle k dom neut f i) = (term235 A K op ltle k i dom neut f).
Proof. exact (MK_COMB (@lem6780538) (@lem6780537 A K op ltle k i dom neut f)). Qed.
Lemma lem6780540 {A K : Type'} (i : K) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i' : K) (dom : A -> Prop) (neut : A) (f : K -> A) : (term236 A K i op ltle k dom neut f i') = (term220 A K i op ltle k i' dom neut f).
Proof. exact (eq_refl (term236 A K i op ltle k dom neut f i')). Qed.
Lemma lem6780541 {A K : Type'} (i : K) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) (f : K -> A) : (term237 A K i op ltle k dom neut f) = (term221 A K i op ltle k dom neut f).
Proof. exact (fun_ext (fun i' : K => @lem6780540 A K i op ltle k i' dom neut f)). Qed.
Lemma lem6780542 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem6780543 {A K : Type'} (i : K) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) (f : K -> A) : (term238 A K i op ltle k dom neut f) = (term222 A K i op ltle k dom neut f).
Proof. exact (MK_COMB (@lem6780542 K) (@lem6780541 A K i op ltle k dom neut f)). Qed.
Lemma lem6780544 {A K : Type'} (i : K) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) (f : K -> A) : (term228 A K i op ltle k dom neut f) = (term239 A K i op ltle k dom neut f).
Proof. exact (MK_COMB (@lem6780539 A K op ltle k i dom neut f) (@lem6780543 A K i op ltle k dom neut f)). Qed.
Lemma lem6780545 {A K : Type'} (op : type1400 A) (i : K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : i = (term189 A K ltle k f dom neut)) : term239 A K i op ltle k dom neut f.
Proof. exact (EQ_MP (@lem6780544 A K i op ltle k dom neut f) (@lem6780534 A K op i ltle k f dom neut h1)). Qed.
Lemma lem6780595 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6780596 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem6780595 A x). Qed.
Lemma lem6780597 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i : K) (dom : A -> Prop) (neut : A) (f : K -> A) : ((term206 A K op ltle k i dom neut f) = (term206 A K op ltle k i dom neut f)) = True.
Proof. exact (@lem6780596 A (term206 A K op ltle k i dom neut f)). Qed.
Lemma lem6780600 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i : K) (dom : A -> Prop) (neut : A) (f : K -> A) : (term240 A K op ltle k i dom neut f) = (term240 A K op ltle k i dom neut f).
Proof. exact (eq_refl (term240 A K op ltle k i dom neut f)). Qed.
Lemma lem6780601 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i : K) (dom : A -> Prop) (neut : A) (f : K -> A) : (term240 A K op ltle k i dom neut f) = (((term206 A K op ltle k i dom neut f) = (term206 A K op ltle k i dom neut f)) = True).
Proof. exact (eq_refl (term240 A K op ltle k i dom neut f)). Qed.
Lemma lem6780602 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i : K) (dom : A -> Prop) (neut : A) (f : K -> A) : (term241 A K op ltle k i dom neut f) = (term241 A K op ltle k i dom neut f).
Proof. exact (eq_refl (term241 A K op ltle k i dom neut f)). Qed.
Lemma lem6780603 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i : K) (dom : A -> Prop) (neut : A) (f : K -> A) : ((term240 A K op ltle k i dom neut f) = (term240 A K op ltle k i dom neut f)) = ((term240 A K op ltle k i dom neut f) = (((term206 A K op ltle k i dom neut f) = (term206 A K op ltle k i dom neut f)) = True)).
Proof. exact (MK_COMB (@lem6780602 A K op ltle k i dom neut f) (@lem6780601 A K op ltle k i dom neut f)). Qed.
Lemma lem6780604 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i : K) (dom : A -> Prop) (neut : A) (f : K -> A) : (term240 A K op ltle k i dom neut f) = (((term206 A K op ltle k i dom neut f) = (term206 A K op ltle k i dom neut f)) = True).
Proof. exact (eq_refl (term240 A K op ltle k i dom neut f)). Qed.
Lemma lem6780605 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6780606 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i : K) (dom : A -> Prop) (neut : A) (f : K -> A) : (term241 A K op ltle k i dom neut f) = (term242 A K op ltle k i dom neut f).
Proof. exact (MK_COMB (@lem6780605) (@lem6780604 A K op ltle k i dom neut f)). Qed.
Lemma lem6780607 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i : K) (dom : A -> Prop) (neut : A) (f : K -> A) : (((term206 A K op ltle k i dom neut f) = (term206 A K op ltle k i dom neut f)) = True) = (((term206 A K op ltle k i dom neut f) = (term206 A K op ltle k i dom neut f)) = True).
Proof. exact (eq_refl (((term206 A K op ltle k i dom neut f) = (term206 A K op ltle k i dom neut f)) = True)). Qed.
Lemma lem6780608 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i : K) (dom : A -> Prop) (neut : A) (f : K -> A) : ((term240 A K op ltle k i dom neut f) = (((term206 A K op ltle k i dom neut f) = (term206 A K op ltle k i dom neut f)) = True)) = ((((term206 A K op ltle k i dom neut f) = (term206 A K op ltle k i dom neut f)) = True) = (((term206 A K op ltle k i dom neut f) = (term206 A K op ltle k i dom neut f)) = True)).
Proof. exact (MK_COMB (@lem6780606 A K op ltle k i dom neut f) (@lem6780607 A K op ltle k i dom neut f)). Qed.
Lemma lem6780609 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i : K) (dom : A -> Prop) (neut : A) (f : K -> A) : ((term240 A K op ltle k i dom neut f) = (term240 A K op ltle k i dom neut f)) = ((((term206 A K op ltle k i dom neut f) = (term206 A K op ltle k i dom neut f)) = True) = (((term206 A K op ltle k i dom neut f) = (term206 A K op ltle k i dom neut f)) = True)).
Proof. exact (TRANS (@lem6780603 A K op ltle k i dom neut f) (@lem6780608 A K op ltle k i dom neut f)). Qed.
Lemma lem6780610 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i : K) (dom : A -> Prop) (neut : A) (f : K -> A) : (((term206 A K op ltle k i dom neut f) = (term206 A K op ltle k i dom neut f)) = True) = (((term206 A K op ltle k i dom neut f) = (term206 A K op ltle k i dom neut f)) = True).
Proof. exact (EQ_MP (@lem6780609 A K op ltle k i dom neut f) (@lem6780600 A K op ltle k i dom neut f)). Qed.
Lemma lem6780611 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i : K) (dom : A -> Prop) (neut : A) (f : K -> A) : ((term206 A K op ltle k i dom neut f) = (term206 A K op ltle k i dom neut f)) = True.
Proof. exact (EQ_MP (@lem6780610 A K op ltle k i dom neut f) (@lem6780597 A K op ltle k i dom neut f)). Qed.
Lemma lem6780612 {A K : Type'} (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term137 A K f i dom neut) = (term137 A K f i dom neut).
Proof. exact (eq_refl (term137 A K f i dom neut)). Qed.
Lemma lem6780613 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term243 A K op ltle k i dom neut f) = (term139 A K f i dom neut).
Proof. exact (MK_COMB (@lem6780612 A K f i dom neut) (@lem6780611 A K op ltle k i dom neut f)). Qed.
Lemma lem6780615 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem6780616 {A K : Type'} (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term139 A K f i dom neut) = (term105 A K f i dom neut).
Proof. exact (@lem6780615 (term105 A K f i dom neut)). Qed.
Lemma lem6780617 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term243 A K op ltle k i dom neut f) = (term105 A K f i dom neut).
Proof. exact (TRANS (@lem6780613 A K op ltle k f i dom neut) (@lem6780616 A K f i dom neut)). Qed.
Lemma lem6780618 {K : Type'} (i : K) (k : K -> Prop) : (term169 K i k) = (term169 K i k).
Proof. exact (eq_refl (term169 K i k)). Qed.
Lemma lem6780619 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term230 A K op ltle k i dom neut f) = (term244 A K k f i dom neut).
Proof. exact (MK_COMB (@lem6780618 K i k) (@lem6780617 A K op ltle k f i dom neut)). Qed.
Lemma lem6780622 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term231 A K ltle k f dom neut i) = (term231 A K ltle k f dom neut i).
Proof. exact (eq_refl (term231 A K ltle k f dom neut i)). Qed.
Lemma lem6780623 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term233 A K op ltle k i dom neut f) = (term245 A K ltle k f i dom neut).
Proof. exact (MK_COMB (@lem6780622 A K ltle k f dom neut i) (@lem6780619 A K op ltle k f i dom neut)). Qed.
Lemma lem6780628 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i : K) (dom : A -> Prop) (neut : A) (f : K -> A) : (term245 A K ltle k f i dom neut) = (term233 A K op ltle k i dom neut f).
Proof. exact (SYM (@lem6780623 A K op ltle k f i dom neut)). Qed.
Lemma lem6780629 {K : Type'} (_474 : K) (_475 : Prop) (_476 : K -> Prop) (_477 : K) : (term246 K _476 _475 _474 _477) = (term247 K _474 _475 _476 _477).
Proof. exact (@lem13473 K _474 _475 _476 _477). Qed.
Lemma lem6780630 {A K : Type'} (_474 : K) (_475 : Prop) (k : K -> Prop) (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) (_477 : K) : (term248 A K k f i dom neut _475 _474 _477) = (term249 A K _474 _475 k f i dom neut _477).
Proof. exact (@lem6780629 K _474 _475 (term250 A K k f i dom neut) _477). Qed.
Lemma lem6780631 {A K : Type'} (ltle : type1402 K) (i : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term251 A K i ltle k f dom neut) = (term252 A K ltle i k f dom neut).
Proof. exact (@lem6780630 A K (term253 A K ltle k f dom neut) (term254 A K ltle k f dom neut) k f i dom neut (term255 A K k f dom neut)). Qed.
Lemma lem6780632 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term256 A K i k f dom neut) = (term257 A K k f i dom neut).
Proof. exact (eq_refl (term256 A K i k f dom neut)). Qed.
Lemma lem6780633 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term258 A K ltle k f dom neut) = (term258 A K ltle k f dom neut).
Proof. exact (eq_refl (term258 A K ltle k f dom neut)). Qed.
Lemma lem6780634 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term259 A K ltle i k f dom neut) = (term260 A K ltle k f i dom neut).
Proof. exact (MK_COMB (@lem6780633 A K ltle k f dom neut) (@lem6780632 A K k f i dom neut)). Qed.
Lemma lem6780635 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term261 A K i ltle k f dom neut) = (term262 A K ltle k f i dom neut).
Proof. exact (eq_refl (term261 A K i ltle k f dom neut)). Qed.
Lemma lem6780636 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term263 A K ltle k f dom neut) = (term263 A K ltle k f dom neut).
Proof. exact (eq_refl (term263 A K ltle k f dom neut)). Qed.
Lemma lem6780637 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term264 A K i ltle k f dom neut) = (term265 A K ltle k f i dom neut).
Proof. exact (MK_COMB (@lem6780636 A K ltle k f dom neut) (@lem6780635 A K ltle k f i dom neut)). Qed.
Lemma lem6780638 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6780639 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term266 A K i ltle k f dom neut) = (term267 A K ltle k f i dom neut).
Proof. exact (MK_COMB (@lem6780638) (@lem6780637 A K ltle k f i dom neut)). Qed.
Lemma lem6780640 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term252 A K ltle i k f dom neut) = (term268 A K ltle k f i dom neut).
Proof. exact (MK_COMB (@lem6780639 A K ltle k f i dom neut) (@lem6780634 A K ltle k f i dom neut)). Qed.
Lemma lem6780641 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term251 A K i ltle k f dom neut) = (term245 A K ltle k f i dom neut).
Proof. exact (eq_refl (term251 A K i ltle k f dom neut)). Qed.
Lemma lem6780642 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6780643 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term269 A K i ltle k f dom neut) = (term270 A K ltle k f i dom neut).
Proof. exact (MK_COMB (@lem6780642) (@lem6780641 A K ltle k f i dom neut)). Qed.
Lemma lem6780644 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : ((term251 A K i ltle k f dom neut) = (term252 A K ltle i k f dom neut)) = ((term245 A K ltle k f i dom neut) = (term268 A K ltle k f i dom neut)).
Proof. exact (MK_COMB (@lem6780643 A K ltle k f i dom neut) (@lem6780640 A K ltle k f i dom neut)). Qed.
Lemma lem6780645 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term245 A K ltle k f i dom neut) = (term268 A K ltle k f i dom neut).
Proof. exact (EQ_MP (@lem6780644 A K ltle k f i dom neut) (@lem6780631 A K ltle i k f dom neut)). Qed.
Lemma lem6780646 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term268 A K ltle k f i dom neut) = (term245 A K ltle k f i dom neut).
Proof. exact (SYM (@lem6780645 A K ltle k f i dom neut)). Qed.
Lemma lem6780647 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term254 A K ltle k f dom neut) : term254 A K ltle k f dom neut.
Proof. exact (h1). Qed.
Lemma lem6780664 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term271 A K ltle k f dom neut) : term271 A K ltle k f dom neut.
Proof. exact (h1). Qed.
Lemma lem6780682 (t1 : Prop) : term272 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem6780683 (t1 : Prop) : (term272 t1) = (term273 t1).
Proof. exact (eq_refl (term272 t1)). Qed.
Lemma lem6780684 (t1 : Prop) : term273 t1.
Proof. exact (EQ_MP (@lem6780683 t1) (@lem6780682 t1)). Qed.
Lemma lem6780685 (t1 : Prop) (t2 : Prop) : term274 t1 t2.
Proof. exact (@lem6780684 t1 t2). Qed.
Lemma lem6780686 (t1 : Prop) (t2 : Prop) : (term274 t1 t2) = (term275 t1 t2).
Proof. exact (eq_refl (term274 t1 t2)). Qed.
Lemma lem6780687 (t1 : Prop) (t2 : Prop) : term275 t1 t2.
Proof. exact (EQ_MP (@lem6780686 t1 t2) (@lem6780685 t1 t2)). Qed.
Lemma lem6780688 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term276 t1 t2 t3.
Proof. exact (@lem6780687 t1 t2 t3). Qed.
Lemma lem6780689 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term276 t1 t2 t3) = ((term277 t1 t2 t3) = (term278 t1 t2 t3)).
Proof. exact (eq_refl (term276 t1 t2 t3)). Qed.
Lemma lem6780690 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term277 t1 t2 t3) = (term278 t1 t2 t3).
Proof. exact (EQ_MP (@lem6780689 t1 t2 t3) (@lem6780688 t1 t2 t3)). Qed.
Lemma lem6780691 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term278 t1 t2 t3) = (term277 t1 t2 t3).
Proof. exact (SYM (@lem6780690 t1 t2 t3)). Qed.
Lemma lem6780692 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term163 A K k f dom neut) (h2 : term162 A K k f dom neut) : term279 A K k f dom neut.
Proof. exact (conj (@lem6780477 A K k f dom neut h2) (@lem6780463 A K k f dom neut h1)). Qed.
Lemma lem6780693 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term163 A K k f dom neut) (h2 : term271 A K ltle k f dom neut) (h3 : term162 A K k f dom neut) : term280 A K ltle k f dom neut.
Proof. exact (conj (@lem6780664 A K ltle k f dom neut h2) (@lem6780692 A K k f dom neut h1 h3)). Qed.
Lemma lem6780725 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term281 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem6780726 {K : Type'} (s : K -> Prop) (t : K -> Prop) : (s = t) = (term281 K s t).
Proof. exact (@lem6780725 K s t). Qed.
Lemma lem6780727 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : ((term177 A K k f dom neut) = (@EMPTY K)) = (term282 A K k f dom neut).
Proof. exact (@lem6780726 K (term177 A K k f dom neut) (@EMPTY K)). Qed.
Lemma lem6780742 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6780743 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term162 A K k f dom neut) = (term283 A K k f dom neut).
Proof. exact (MK_COMB (@lem6780742) (@lem6780727 A K k f dom neut)). Qed.
Lemma lem6780744 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6780745 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term284 A K k f dom neut) = (term285 A K k f dom neut).
Proof. exact (MK_COMB (@lem6780744) (@lem6780743 A K k f dom neut)). Qed.
Lemma lem6780752 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term163 A K k f dom neut) = (term163 A K k f dom neut).
Proof. exact (eq_refl (term163 A K k f dom neut)). Qed.
Lemma lem6780753 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term279 A K k f dom neut) = (term286 A K k f dom neut).
Proof. exact (MK_COMB (@lem6780745 A K k f dom neut) (@lem6780752 A K k f dom neut)). Qed.
Lemma lem6780756 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term287 A K ltle k f dom neut) = (term287 A K ltle k f dom neut).
Proof. exact (eq_refl (term287 A K ltle k f dom neut)). Qed.
Lemma lem6780757 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term280 A K ltle k f dom neut) = (term288 A K ltle k f dom neut).
Proof. exact (MK_COMB (@lem6780756 A K ltle k f dom neut) (@lem6780753 A K k f dom neut)). Qed.
Lemma lem6780760 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6780761 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term289 A K ltle k f dom neut) = (term290 A K ltle k f dom neut).
Proof. exact (MK_COMB (@lem6780760) (@lem6780757 A K ltle k f dom neut)). Qed.
Lemma lem6780774 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term257 A K k f i dom neut) = (term257 A K k f i dom neut).
Proof. exact (eq_refl (term257 A K k f i dom neut)). Qed.
Lemma lem6780775 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term291 A K ltle k f i dom neut) = (term292 A K ltle k f i dom neut).
Proof. exact (MK_COMB (@lem6780761 A K ltle k f dom neut) (@lem6780774 A K k f i dom neut)). Qed.
Lemma lem6780778 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term292 A K ltle k f i dom neut) = (term291 A K ltle k f i dom neut).
Proof. exact (SYM (@lem6780775 A K ltle k f i dom neut)). Qed.
Lemma lem6780790 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem6780791 {K : Type'} (P : K -> Prop) (x : K) : (@IN K x P) = (P x).
Proof. exact (@lem6780790 K P x). Qed.
Lemma lem6780792 {K : Type'} (k : K -> Prop) (i : K) : (@IN K i k) = (k i).
Proof. exact (@lem6780791 K k i). Qed.
Lemma lem6780793 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6780794 {K : Type'} (k : K -> Prop) (i : K) : (term169 K i k) = (term293 K k i).
Proof. exact (MK_COMB (@lem6780793) (@lem6780792 K k i)). Qed.
Lemma lem6780798 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term294 A x s t) = (term295 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem6780799 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term294 A x s t) = (term295 A s x t).
Proof. exact (@lem6780798 A s x t). Qed.
Lemma lem6780800 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term105 A K f i dom neut) = (term296 A K dom f i neut).
Proof. exact (@lem6780799 A dom (f i) (@INSERT A neut (@EMPTY A))). Qed.
Lemma lem6780804 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem6780805 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem6780804 A P x). Qed.
Lemma lem6780806 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) : (term297 A K f i dom) = (term298 A K dom f i).
Proof. exact (@lem6780805 A dom (f i)). Qed.
Lemma lem6780807 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6780808 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) : (term299 A K f i dom) = (term300 A K dom f i).
Proof. exact (MK_COMB (@lem6780807) (@lem6780806 A K dom f i)). Qed.
Lemma lem6780810 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term301 A x y s) = (term302 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem6780811 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term301 A x y s) = (term302 A y x s).
Proof. exact (@lem6780810 A y x s). Qed.
Lemma lem6780812 {A K : Type'} (neut : A) (f : K -> A) (i : K) : (term303 A K f i neut) = (term304 A K neut f i).
Proof. exact (@lem6780811 A neut (f i) (@EMPTY A)). Qed.
Lemma lem6780818 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem6780819 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem6780818 A x). Qed.
Lemma lem6780820 {A K : Type'} (f : K -> A) (i : K) : (term305 A K f i) = False.
Proof. exact (@lem6780819 A (f i)). Qed.
Lemma lem6780821 {A K : Type'} (f : K -> A) (i : K) (neut : A) : (term306 A K f i neut) = (term306 A K f i neut).
Proof. exact (eq_refl (term306 A K f i neut)). Qed.
Lemma lem6780822 {A K : Type'} (f : K -> A) (i : K) (neut : A) : (term304 A K neut f i) = (term307 A K f i neut).
Proof. exact (MK_COMB (@lem6780821 A K f i neut) (@lem6780820 A K f i)). Qed.
Lemma lem6780824 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem6780825 {A K : Type'} (f : K -> A) (i : K) (neut : A) : (term307 A K f i neut) = ((f i) = neut).
Proof. exact (@lem6780824 ((f i) = neut)). Qed.
Lemma lem6780828 {A K : Type'} (f : K -> A) (i : K) (neut : A) : (term304 A K neut f i) = ((f i) = neut).
Proof. exact (TRANS (@lem6780822 A K f i neut) (@lem6780825 A K f i neut)). Qed.
Lemma lem6780829 {A K : Type'} (f : K -> A) (i : K) (neut : A) : (term303 A K f i neut) = ((f i) = neut).
Proof. exact (TRANS (@lem6780812 A K neut f i) (@lem6780828 A K f i neut)). Qed.
Lemma lem6780830 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6780831 {A K : Type'} (f : K -> A) (i : K) (neut : A) : (term308 A K f i neut) = (term309 A K f i neut).
Proof. exact (MK_COMB (@lem6780830) (@lem6780829 A K f i neut)). Qed.
Lemma lem6780832 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term296 A K dom f i neut) = (term310 A K dom f i neut).
Proof. exact (MK_COMB (@lem6780808 A K dom f i) (@lem6780831 A K f i neut)). Qed.
Lemma lem6780835 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term105 A K f i dom neut) = (term310 A K dom f i neut).
Proof. exact (TRANS (@lem6780800 A K dom f i neut) (@lem6780832 A K dom f i neut)). Qed.
Lemma lem6780836 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6780837 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term137 A K f i dom neut) = (term311 A K dom f i neut).
Proof. exact (MK_COMB (@lem6780836) (@lem6780835 A K dom f i neut)). Qed.
Lemma lem6780849 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem6780850 {K : Type'} (P : K -> Prop) (x : K) : (@IN K x P) = (P x).
Proof. exact (@lem6780849 K P x). Qed.
Lemma lem6780851 {K : Type'} (k : K -> Prop) (i' : K) : (@IN K i' k) = (k i').
Proof. exact (@lem6780850 K k i'). Qed.
Lemma lem6780852 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6780853 {K : Type'} (k : K -> Prop) (i' : K) : (term169 K i' k) = (term293 K k i').
Proof. exact (MK_COMB (@lem6780852) (@lem6780851 K k i')). Qed.
Lemma lem6780855 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term294 A x s t) = (term295 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem6780856 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term294 A x s t) = (term295 A s x t).
Proof. exact (@lem6780855 A s x t). Qed.
Lemma lem6780857 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i' : K) (neut : A) : (term105 A K f i' dom neut) = (term296 A K dom f i' neut).
Proof. exact (@lem6780856 A dom (f i') (@INSERT A neut (@EMPTY A))). Qed.
Lemma lem6780861 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem6780862 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem6780861 A P x). Qed.
Lemma lem6780863 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i' : K) : (term297 A K f i' dom) = (term298 A K dom f i').
Proof. exact (@lem6780862 A dom (f i')). Qed.
Lemma lem6780864 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6780865 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i' : K) : (term299 A K f i' dom) = (term300 A K dom f i').
Proof. exact (MK_COMB (@lem6780864) (@lem6780863 A K dom f i')). Qed.
Lemma lem6780867 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term301 A x y s) = (term302 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem6780868 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term301 A x y s) = (term302 A y x s).
Proof. exact (@lem6780867 A y x s). Qed.
Lemma lem6780869 {A K : Type'} (neut : A) (f : K -> A) (i' : K) : (term303 A K f i' neut) = (term304 A K neut f i').
Proof. exact (@lem6780868 A neut (f i') (@EMPTY A)). Qed.
Lemma lem6780875 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem6780876 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem6780875 A x). Qed.
Lemma lem6780877 {A K : Type'} (f : K -> A) (i' : K) : (term305 A K f i') = False.
Proof. exact (@lem6780876 A (f i')). Qed.
Lemma lem6780878 {A K : Type'} (f : K -> A) (i' : K) (neut : A) : (term306 A K f i' neut) = (term306 A K f i' neut).
Proof. exact (eq_refl (term306 A K f i' neut)). Qed.
Lemma lem6780879 {A K : Type'} (f : K -> A) (i' : K) (neut : A) : (term304 A K neut f i') = (term307 A K f i' neut).
Proof. exact (MK_COMB (@lem6780878 A K f i' neut) (@lem6780877 A K f i')). Qed.
Lemma lem6780881 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem6780882 {A K : Type'} (f : K -> A) (i' : K) (neut : A) : (term307 A K f i' neut) = ((f i') = neut).
Proof. exact (@lem6780881 ((f i') = neut)). Qed.
Lemma lem6780885 {A K : Type'} (f : K -> A) (i' : K) (neut : A) : (term304 A K neut f i') = ((f i') = neut).
Proof. exact (TRANS (@lem6780879 A K f i' neut) (@lem6780882 A K f i' neut)). Qed.
Lemma lem6780886 {A K : Type'} (f : K -> A) (i' : K) (neut : A) : (term303 A K f i' neut) = ((f i') = neut).
Proof. exact (TRANS (@lem6780869 A K neut f i') (@lem6780885 A K f i' neut)). Qed.
Lemma lem6780887 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6780888 {A K : Type'} (f : K -> A) (i' : K) (neut : A) : (term308 A K f i' neut) = (term309 A K f i' neut).
Proof. exact (MK_COMB (@lem6780887) (@lem6780886 A K f i' neut)). Qed.
Lemma lem6780889 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i' : K) (neut : A) : (term296 A K dom f i' neut) = (term310 A K dom f i' neut).
Proof. exact (MK_COMB (@lem6780865 A K dom f i') (@lem6780888 A K f i' neut)). Qed.
Lemma lem6780892 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i' : K) (neut : A) : (term105 A K f i' dom neut) = (term310 A K dom f i' neut).
Proof. exact (TRANS (@lem6780857 A K dom f i' neut) (@lem6780889 A K dom f i' neut)). Qed.
Lemma lem6780893 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i' : K) (neut : A) : (term244 A K k f i' dom neut) = (term312 A K k dom f i' neut).
Proof. exact (MK_COMB (@lem6780853 K k i') (@lem6780892 A K dom f i' neut)). Qed.
Lemma lem6780896 {K : Type'} (ltle : type1402 K) (i' : K) (i : K) : (term126 K ltle i' i) = (term126 K ltle i' i).
Proof. exact (eq_refl (term126 K ltle i' i)). Qed.
Lemma lem6780897 {A K : Type'} (ltle : type1402 K) (i : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i' : K) (neut : A) : (term313 A K ltle i k f i' dom neut) = (term314 A K ltle i k dom f i' neut).
Proof. exact (MK_COMB (@lem6780896 K ltle i' i) (@lem6780893 A K k dom f i' neut)). Qed.
Lemma lem6780900 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6780901 {A K : Type'} (ltle : type1402 K) (i : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i' : K) (neut : A) : (term315 A K ltle i k f i' dom neut) = (term316 A K ltle i k dom f i' neut).
Proof. exact (MK_COMB (@lem6780900) (@lem6780897 A K ltle i k dom f i' neut)). Qed.
Lemma lem6780904 {K : Type'} (i' : K) (i : K) : (i' = i) = (i' = i).
Proof. exact (eq_refl (i' = i)). Qed.
Lemma lem6780905 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i' : K) (i : K) : (term317 A K ltle k f dom neut i' i) = (term318 A K ltle k dom f neut i' i).
Proof. exact (MK_COMB (@lem6780901 A K ltle i k dom f i' neut) (@lem6780904 K i' i)). Qed.
Lemma lem6780908 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term319 A K ltle k f dom neut i) = (term320 A K ltle k dom f neut i).
Proof. exact (fun_ext (fun i' : K => @lem6780905 A K ltle k dom f neut i' i)). Qed.
Lemma lem6780909 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6780910 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term321 A K ltle k f dom neut i) = (term322 A K ltle k dom f neut i).
Proof. exact (MK_COMB (@lem6780909 K) (@lem6780908 A K ltle k dom f neut i)). Qed.
Lemma lem6780915 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term323 A K ltle k f dom neut i) = (term324 A K ltle k dom f neut i).
Proof. exact (MK_COMB (@lem6780837 A K dom f i neut) (@lem6780910 A K ltle k dom f neut i)). Qed.
Lemma lem6780918 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term325 A K ltle k f dom neut i) = (term326 A K ltle k dom f neut i).
Proof. exact (MK_COMB (@lem6780794 K k i) (@lem6780915 A K ltle k dom f neut i)). Qed.
Lemma lem6780921 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term327 A K ltle k f dom neut) = (term328 A K ltle k dom f neut).
Proof. exact (fun_ext (fun i : K => @lem6780918 A K ltle k dom f neut i)). Qed.
Lemma lem6780922 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem6780923 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term254 A K ltle k f dom neut) = (term329 A K ltle k dom f neut).
Proof. exact (MK_COMB (@lem6780922 K) (@lem6780921 A K ltle k dom f neut)). Qed.
Lemma lem6780928 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6780929 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term271 A K ltle k f dom neut) = (term330 A K ltle k dom f neut).
Proof. exact (MK_COMB (@lem6780928) (@lem6780923 A K ltle k dom f neut)). Qed.
Lemma lem6780930 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6780931 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term287 A K ltle k f dom neut) = (term331 A K ltle k dom f neut).
Proof. exact (MK_COMB (@lem6780930) (@lem6780929 A K ltle k dom f neut)). Qed.
Lemma lem6780941 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term332 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem6780942 {K : Type'} (p : K -> Prop) (x : K) : (term332 K x p) = (p x).
Proof. exact (@lem6780941 K p x). Qed.
Lemma lem6780943 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (x : K) : (term333 A K x k f dom neut) = (term334 A K k f dom neut x).
Proof. exact (@lem6780942 K (term335 A K k f dom neut) x). Qed.
Lemma lem6780944 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term334 A K k f dom neut i) = (term244 A K k f i dom neut).
Proof. exact (eq_refl (term334 A K k f dom neut i)). Qed.
Lemma lem6780945 {K : Type'} (GEN_PVAR_275 : K) : (@SETSPEC K GEN_PVAR_275) = (@SETSPEC K GEN_PVAR_275).
Proof. exact (eq_refl (@SETSPEC K GEN_PVAR_275)). Qed.
Lemma lem6780946 {A K : Type'} (GEN_PVAR_275 : K) (k : K -> Prop) (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term336 A K GEN_PVAR_275 k f dom neut i) = (term337 A K GEN_PVAR_275 k f i dom neut).
Proof. exact (MK_COMB (@lem6780945 K GEN_PVAR_275) (@lem6780944 A K k f i dom neut)). Qed.
Lemma lem6780947 {K : Type'} (i : K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem6780948 {A K : Type'} (GEN_PVAR_275 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term338 A K GEN_PVAR_275 k f dom neut i) = (term339 A K GEN_PVAR_275 k f dom neut i).
Proof. exact (MK_COMB (@lem6780946 A K GEN_PVAR_275 k f i dom neut) (@lem6780947 K i)). Qed.
Lemma lem6780949 {A K : Type'} (GEN_PVAR_275 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term340 A K GEN_PVAR_275 k f dom neut) = (term341 A K GEN_PVAR_275 k f dom neut).
Proof. exact (fun_ext (fun i : K => @lem6780948 A K GEN_PVAR_275 k f dom neut i)). Qed.
Lemma lem6780950 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem6780951 {A K : Type'} (GEN_PVAR_275 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term342 A K GEN_PVAR_275 k f dom neut) = (term343 A K GEN_PVAR_275 k f dom neut).
Proof. exact (MK_COMB (@lem6780950 K) (@lem6780949 A K GEN_PVAR_275 k f dom neut)). Qed.
Lemma lem6780952 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term344 A K k f dom neut) = (term345 A K k f dom neut).
Proof. exact (fun_ext (fun GEN_PVAR_275 : K => @lem6780951 A K GEN_PVAR_275 k f dom neut)). Qed.
Lemma lem6780953 {K : Type'} : (@GSPEC K) = (@GSPEC K).
Proof. exact (eq_refl (@GSPEC K)). Qed.
Lemma lem6780954 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term346 A K k f dom neut) = (term177 A K k f dom neut).
Proof. exact (MK_COMB (@lem6780953 K) (@lem6780952 A K k f dom neut)). Qed.
Lemma lem6780955 {K : Type'} (x : K) : (@IN K x) = (@IN K x).
Proof. exact (eq_refl (@IN K x)). Qed.
Lemma lem6780956 {A K : Type'} (x : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term333 A K x k f dom neut) = (term347 A K x k f dom neut).
Proof. exact (MK_COMB (@lem6780955 K x) (@lem6780954 A K k f dom neut)). Qed.
Lemma lem6780957 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6780958 {A K : Type'} (x : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term348 A K x k f dom neut) = (term349 A K x k f dom neut).
Proof. exact (MK_COMB (@lem6780957) (@lem6780956 A K x k f dom neut)). Qed.
Lemma lem6780959 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K) (dom : A -> Prop) (neut : A) : (term334 A K k f dom neut x) = (term244 A K k f x dom neut).
Proof. exact (eq_refl (term334 A K k f dom neut x)). Qed.
Lemma lem6780960 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K) (dom : A -> Prop) (neut : A) : ((term333 A K x k f dom neut) = (term334 A K k f dom neut x)) = ((term347 A K x k f dom neut) = (term244 A K k f x dom neut)).
Proof. exact (MK_COMB (@lem6780958 A K x k f dom neut) (@lem6780959 A K k f x dom neut)). Qed.
Lemma lem6780961 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K) (dom : A -> Prop) (neut : A) : (term347 A K x k f dom neut) = (term244 A K k f x dom neut).
Proof. exact (EQ_MP (@lem6780960 A K k f x dom neut) (@lem6780943 A K k f dom neut x)). Qed.
Lemma lem6780965 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem6780966 {K : Type'} (P : K -> Prop) (x : K) : (@IN K x P) = (P x).
Proof. exact (@lem6780965 K P x). Qed.
Lemma lem6780967 {K : Type'} (k : K -> Prop) (x : K) : (@IN K x k) = (k x).
Proof. exact (@lem6780966 K k x). Qed.
Lemma lem6780968 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6780969 {K : Type'} (k : K -> Prop) (x : K) : (term169 K x k) = (term293 K k x).
Proof. exact (MK_COMB (@lem6780968) (@lem6780967 K k x)). Qed.
Lemma lem6780971 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term294 A x s t) = (term295 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem6780972 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term294 A x s t) = (term295 A s x t).
Proof. exact (@lem6780971 A s x t). Qed.
Lemma lem6780973 {A K : Type'} (dom : A -> Prop) (f : K -> A) (x : K) (neut : A) : (term105 A K f x dom neut) = (term296 A K dom f x neut).
Proof. exact (@lem6780972 A dom (f x) (@INSERT A neut (@EMPTY A))). Qed.
Lemma lem6780977 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem6780978 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem6780977 A P x). Qed.
Lemma lem6780979 {A K : Type'} (dom : A -> Prop) (f : K -> A) (x : K) : (term297 A K f x dom) = (term298 A K dom f x).
Proof. exact (@lem6780978 A dom (f x)). Qed.
Lemma lem6780980 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6780981 {A K : Type'} (dom : A -> Prop) (f : K -> A) (x : K) : (term299 A K f x dom) = (term300 A K dom f x).
Proof. exact (MK_COMB (@lem6780980) (@lem6780979 A K dom f x)). Qed.
Lemma lem6780983 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term301 A x y s) = (term302 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem6780984 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term301 A x y s) = (term302 A y x s).
Proof. exact (@lem6780983 A y x s). Qed.
Lemma lem6780985 {A K : Type'} (neut : A) (f : K -> A) (x : K) : (term303 A K f x neut) = (term304 A K neut f x).
Proof. exact (@lem6780984 A neut (f x) (@EMPTY A)). Qed.
Lemma lem6780991 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem6780992 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem6780991 A x). Qed.
Lemma lem6780993 {A K : Type'} (f : K -> A) (x : K) : (term305 A K f x) = False.
Proof. exact (@lem6780992 A (f x)). Qed.
Lemma lem6780994 {A K : Type'} (f : K -> A) (x : K) (neut : A) : (term306 A K f x neut) = (term306 A K f x neut).
Proof. exact (eq_refl (term306 A K f x neut)). Qed.
Lemma lem6780995 {A K : Type'} (f : K -> A) (x : K) (neut : A) : (term304 A K neut f x) = (term307 A K f x neut).
Proof. exact (MK_COMB (@lem6780994 A K f x neut) (@lem6780993 A K f x)). Qed.
Lemma lem6780997 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem6780998 {A K : Type'} (f : K -> A) (x : K) (neut : A) : (term307 A K f x neut) = ((f x) = neut).
Proof. exact (@lem6780997 ((f x) = neut)). Qed.
Lemma lem6781001 {A K : Type'} (f : K -> A) (x : K) (neut : A) : (term304 A K neut f x) = ((f x) = neut).
Proof. exact (TRANS (@lem6780995 A K f x neut) (@lem6780998 A K f x neut)). Qed.
Lemma lem6781002 {A K : Type'} (f : K -> A) (x : K) (neut : A) : (term303 A K f x neut) = ((f x) = neut).
Proof. exact (TRANS (@lem6780985 A K neut f x) (@lem6781001 A K f x neut)). Qed.
Lemma lem6781003 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6781004 {A K : Type'} (f : K -> A) (x : K) (neut : A) : (term308 A K f x neut) = (term309 A K f x neut).
Proof. exact (MK_COMB (@lem6781003) (@lem6781002 A K f x neut)). Qed.
Lemma lem6781005 {A K : Type'} (dom : A -> Prop) (f : K -> A) (x : K) (neut : A) : (term296 A K dom f x neut) = (term310 A K dom f x neut).
Proof. exact (MK_COMB (@lem6780981 A K dom f x) (@lem6781004 A K f x neut)). Qed.
Lemma lem6781008 {A K : Type'} (dom : A -> Prop) (f : K -> A) (x : K) (neut : A) : (term105 A K f x dom neut) = (term310 A K dom f x neut).
Proof. exact (TRANS (@lem6780973 A K dom f x neut) (@lem6781005 A K dom f x neut)). Qed.
Lemma lem6781009 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (x : K) (neut : A) : (term244 A K k f x dom neut) = (term312 A K k dom f x neut).
Proof. exact (MK_COMB (@lem6780969 K k x) (@lem6781008 A K dom f x neut)). Qed.
Lemma lem6781012 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (x : K) (neut : A) : (term347 A K x k f dom neut) = (term312 A K k dom f x neut).
Proof. exact (TRANS (@lem6780961 A K k f x dom neut) (@lem6781009 A K k dom f x neut)). Qed.
Lemma lem6781013 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6781014 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (x : K) (neut : A) : (term349 A K x k f dom neut) = (term350 A K k dom f x neut).
Proof. exact (MK_COMB (@lem6781013) (@lem6781012 A K k dom f x neut)). Qed.
Lemma lem6781016 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem6781017 {K : Type'} (x : K) : (@IN K x (@EMPTY K)) = False.
Proof. exact (@lem6781016 K x). Qed.
Lemma lem6781018 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (x : K) (neut : A) : ((term347 A K x k f dom neut) = (@IN K x (@EMPTY K))) = ((term312 A K k dom f x neut) = False).
Proof. exact (MK_COMB (@lem6781014 A K k dom f x neut) (@lem6781017 K x)). Qed.
Lemma lem6781020 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem6781021 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (x : K) (neut : A) : ((term312 A K k dom f x neut) = False) = (term351 A K k dom f x neut).
Proof. exact (@lem6781020 (term312 A K k dom f x neut)). Qed.
Lemma lem6781028 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (x : K) (neut : A) : ((term347 A K x k f dom neut) = (@IN K x (@EMPTY K))) = (term351 A K k dom f x neut).
Proof. exact (TRANS (@lem6781018 A K k dom f x neut) (@lem6781021 A K k dom f x neut)). Qed.
Lemma lem6781029 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term352 A K k f dom neut) = (term353 A K k dom f neut).
Proof. exact (fun_ext (fun x : K => @lem6781028 A K k dom f x neut)). Qed.
Lemma lem6781030 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6781031 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term282 A K k f dom neut) = (term354 A K k dom f neut).
Proof. exact (MK_COMB (@lem6781030 K) (@lem6781029 A K k dom f neut)). Qed.
Lemma lem6781036 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6781037 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term283 A K k f dom neut) = (term355 A K k dom f neut).
Proof. exact (MK_COMB (@lem6781036) (@lem6781031 A K k dom f neut)). Qed.
Lemma lem6781038 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6781039 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term285 A K k f dom neut) = (term356 A K k dom f neut).
Proof. exact (MK_COMB (@lem6781038) (@lem6781037 A K k dom f neut)). Qed.
Lemma lem6781047 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem6781048 {K : Type'} (P : K -> Prop) (x : K) : (@IN K x P) = (P x).
Proof. exact (@lem6781047 K P x). Qed.
Lemma lem6781049 {K : Type'} (k : K -> Prop) (i : K) : (@IN K i k) = (k i).
Proof. exact (@lem6781048 K k i). Qed.
Lemma lem6781050 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6781051 {K : Type'} (k : K -> Prop) (i : K) : (term169 K i k) = (term293 K k i).
Proof. exact (MK_COMB (@lem6781050) (@lem6781049 K k i)). Qed.
Lemma lem6781053 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term294 A x s t) = (term295 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem6781054 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term294 A x s t) = (term295 A s x t).
Proof. exact (@lem6781053 A s x t). Qed.
Lemma lem6781055 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term105 A K f i dom neut) = (term296 A K dom f i neut).
Proof. exact (@lem6781054 A dom (f i) (@INSERT A neut (@EMPTY A))). Qed.
Lemma lem6781059 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem6781060 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem6781059 A P x). Qed.
Lemma lem6781061 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) : (term297 A K f i dom) = (term298 A K dom f i).
Proof. exact (@lem6781060 A dom (f i)). Qed.
Lemma lem6781062 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6781063 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) : (term299 A K f i dom) = (term300 A K dom f i).
Proof. exact (MK_COMB (@lem6781062) (@lem6781061 A K dom f i)). Qed.
Lemma lem6781065 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term301 A x y s) = (term302 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem6781066 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term301 A x y s) = (term302 A y x s).
Proof. exact (@lem6781065 A y x s). Qed.
Lemma lem6781067 {A K : Type'} (neut : A) (f : K -> A) (i : K) : (term303 A K f i neut) = (term304 A K neut f i).
Proof. exact (@lem6781066 A neut (f i) (@EMPTY A)). Qed.
Lemma lem6781073 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem6781074 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem6781073 A x). Qed.
Lemma lem6781075 {A K : Type'} (f : K -> A) (i : K) : (term305 A K f i) = False.
Proof. exact (@lem6781074 A (f i)). Qed.
Lemma lem6781076 {A K : Type'} (f : K -> A) (i : K) (neut : A) : (term306 A K f i neut) = (term306 A K f i neut).
Proof. exact (eq_refl (term306 A K f i neut)). Qed.
Lemma lem6781077 {A K : Type'} (f : K -> A) (i : K) (neut : A) : (term304 A K neut f i) = (term307 A K f i neut).
Proof. exact (MK_COMB (@lem6781076 A K f i neut) (@lem6781075 A K f i)). Qed.
Lemma lem6781079 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem6781080 {A K : Type'} (f : K -> A) (i : K) (neut : A) : (term307 A K f i neut) = ((f i) = neut).
Proof. exact (@lem6781079 ((f i) = neut)). Qed.
Lemma lem6781083 {A K : Type'} (f : K -> A) (i : K) (neut : A) : (term304 A K neut f i) = ((f i) = neut).
Proof. exact (TRANS (@lem6781077 A K f i neut) (@lem6781080 A K f i neut)). Qed.
Lemma lem6781084 {A K : Type'} (f : K -> A) (i : K) (neut : A) : (term303 A K f i neut) = ((f i) = neut).
Proof. exact (TRANS (@lem6781067 A K neut f i) (@lem6781083 A K f i neut)). Qed.
Lemma lem6781085 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6781086 {A K : Type'} (f : K -> A) (i : K) (neut : A) : (term308 A K f i neut) = (term309 A K f i neut).
Proof. exact (MK_COMB (@lem6781085) (@lem6781084 A K f i neut)). Qed.
Lemma lem6781087 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term296 A K dom f i neut) = (term310 A K dom f i neut).
Proof. exact (MK_COMB (@lem6781063 A K dom f i) (@lem6781086 A K f i neut)). Qed.
Lemma lem6781090 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term105 A K f i dom neut) = (term310 A K dom f i neut).
Proof. exact (TRANS (@lem6781055 A K dom f i neut) (@lem6781087 A K dom f i neut)). Qed.
Lemma lem6781091 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term244 A K k f i dom neut) = (term312 A K k dom f i neut).
Proof. exact (MK_COMB (@lem6781051 K k i) (@lem6781090 A K dom f i neut)). Qed.
Lemma lem6781094 {K : Type'} (GEN_PVAR_274 : K) : (@SETSPEC K GEN_PVAR_274) = (@SETSPEC K GEN_PVAR_274).
Proof. exact (eq_refl (@SETSPEC K GEN_PVAR_274)). Qed.
Lemma lem6781095 {A K : Type'} (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term337 A K GEN_PVAR_274 k f i dom neut) = (term357 A K GEN_PVAR_274 k dom f i neut).
Proof. exact (MK_COMB (@lem6781094 K GEN_PVAR_274) (@lem6781091 A K k dom f i neut)). Qed.
Lemma lem6781096 {K : Type'} (i : K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem6781097 {A K : Type'} (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term339 A K GEN_PVAR_274 k f dom neut i) = (term358 A K GEN_PVAR_274 k dom f neut i).
Proof. exact (MK_COMB (@lem6781095 A K GEN_PVAR_274 k dom f i neut) (@lem6781096 K i)). Qed.
Lemma lem6781098 {A K : Type'} (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term341 A K GEN_PVAR_274 k f dom neut) = (term359 A K GEN_PVAR_274 k dom f neut).
Proof. exact (fun_ext (fun i : K => @lem6781097 A K GEN_PVAR_274 k dom f neut i)). Qed.
Lemma lem6781099 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem6781100 {A K : Type'} (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term343 A K GEN_PVAR_274 k f dom neut) = (term360 A K GEN_PVAR_274 k dom f neut).
Proof. exact (MK_COMB (@lem6781099 K) (@lem6781098 A K GEN_PVAR_274 k dom f neut)). Qed.
Lemma lem6781105 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term345 A K k f dom neut) = (term361 A K k dom f neut).
Proof. exact (fun_ext (fun GEN_PVAR_274 : K => @lem6781100 A K GEN_PVAR_274 k dom f neut)). Qed.
Lemma lem6781106 {K : Type'} : (@GSPEC K) = (@GSPEC K).
Proof. exact (eq_refl (@GSPEC K)). Qed.
Lemma lem6781107 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term177 A K k f dom neut) = (term362 A K k dom f neut).
Proof. exact (MK_COMB (@lem6781106 K) (@lem6781105 A K k dom f neut)). Qed.
Lemma lem6781108 {K : Type'} : (@FINITE K) = (@FINITE K).
Proof. exact (eq_refl (@FINITE K)). Qed.
Lemma lem6781109 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term163 A K k f dom neut) = (term363 A K k dom f neut).
Proof. exact (MK_COMB (@lem6781108 K) (@lem6781107 A K k dom f neut)). Qed.
Lemma lem6781110 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term286 A K k f dom neut) = (term364 A K k dom f neut).
Proof. exact (MK_COMB (@lem6781039 A K k dom f neut) (@lem6781109 A K k dom f neut)). Qed.
Lemma lem6781113 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term288 A K ltle k f dom neut) = (term365 A K ltle k dom f neut).
Proof. exact (MK_COMB (@lem6780931 A K ltle k dom f neut) (@lem6781110 A K k dom f neut)). Qed.
Lemma lem6781116 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6781117 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term290 A K ltle k f dom neut) = (term366 A K ltle k dom f neut).
Proof. exact (MK_COMB (@lem6781116) (@lem6781113 A K ltle k dom f neut)). Qed.
Lemma lem6781127 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem6781128 {K : Type'} (P : K -> Prop) (x : K) : (@IN K x P) = (P x).
Proof. exact (@lem6781127 K P x). Qed.
Lemma lem6781129 {K : Type'} (k : K -> Prop) (i : K) : (@IN K i k) = (k i).
Proof. exact (@lem6781128 K k i). Qed.
Lemma lem6781130 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6781131 {K : Type'} (k : K -> Prop) (i : K) : (term169 K i k) = (term293 K k i).
Proof. exact (MK_COMB (@lem6781130) (@lem6781129 K k i)). Qed.
Lemma lem6781133 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term294 A x s t) = (term295 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem6781134 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term294 A x s t) = (term295 A s x t).
Proof. exact (@lem6781133 A s x t). Qed.
Lemma lem6781135 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term105 A K f i dom neut) = (term296 A K dom f i neut).
Proof. exact (@lem6781134 A dom (f i) (@INSERT A neut (@EMPTY A))). Qed.
Lemma lem6781139 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem6781140 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem6781139 A P x). Qed.
Lemma lem6781141 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) : (term297 A K f i dom) = (term298 A K dom f i).
Proof. exact (@lem6781140 A dom (f i)). Qed.
Lemma lem6781142 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6781143 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) : (term299 A K f i dom) = (term300 A K dom f i).
Proof. exact (MK_COMB (@lem6781142) (@lem6781141 A K dom f i)). Qed.
Lemma lem6781145 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term301 A x y s) = (term302 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem6781146 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term301 A x y s) = (term302 A y x s).
Proof. exact (@lem6781145 A y x s). Qed.
Lemma lem6781147 {A K : Type'} (neut : A) (f : K -> A) (i : K) : (term303 A K f i neut) = (term304 A K neut f i).
Proof. exact (@lem6781146 A neut (f i) (@EMPTY A)). Qed.
Lemma lem6781153 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem6781154 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem6781153 A x). Qed.
Lemma lem6781155 {A K : Type'} (f : K -> A) (i : K) : (term305 A K f i) = False.
Proof. exact (@lem6781154 A (f i)). Qed.
Lemma lem6781156 {A K : Type'} (f : K -> A) (i : K) (neut : A) : (term306 A K f i neut) = (term306 A K f i neut).
Proof. exact (eq_refl (term306 A K f i neut)). Qed.
Lemma lem6781157 {A K : Type'} (f : K -> A) (i : K) (neut : A) : (term304 A K neut f i) = (term307 A K f i neut).
Proof. exact (MK_COMB (@lem6781156 A K f i neut) (@lem6781155 A K f i)). Qed.
Lemma lem6781159 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem6781160 {A K : Type'} (f : K -> A) (i : K) (neut : A) : (term307 A K f i neut) = ((f i) = neut).
Proof. exact (@lem6781159 ((f i) = neut)). Qed.
Lemma lem6781163 {A K : Type'} (f : K -> A) (i : K) (neut : A) : (term304 A K neut f i) = ((f i) = neut).
Proof. exact (TRANS (@lem6781157 A K f i neut) (@lem6781160 A K f i neut)). Qed.
Lemma lem6781164 {A K : Type'} (f : K -> A) (i : K) (neut : A) : (term303 A K f i neut) = ((f i) = neut).
Proof. exact (TRANS (@lem6781147 A K neut f i) (@lem6781163 A K f i neut)). Qed.
Lemma lem6781165 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6781166 {A K : Type'} (f : K -> A) (i : K) (neut : A) : (term308 A K f i neut) = (term309 A K f i neut).
Proof. exact (MK_COMB (@lem6781165) (@lem6781164 A K f i neut)). Qed.
Lemma lem6781167 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term296 A K dom f i neut) = (term310 A K dom f i neut).
Proof. exact (MK_COMB (@lem6781143 A K dom f i) (@lem6781166 A K f i neut)). Qed.
Lemma lem6781170 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term105 A K f i dom neut) = (term310 A K dom f i neut).
Proof. exact (TRANS (@lem6781135 A K dom f i neut) (@lem6781167 A K dom f i neut)). Qed.
Lemma lem6781171 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term244 A K k f i dom neut) = (term312 A K k dom f i neut).
Proof. exact (MK_COMB (@lem6781131 K k i) (@lem6781170 A K dom f i neut)). Qed.
Lemma lem6781174 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term335 A K k f dom neut) = (term367 A K k dom f neut).
Proof. exact (fun_ext (fun i : K => @lem6781171 A K k dom f i neut)). Qed.
Lemma lem6781175 {K : Type'} : (@ε K) = (@ε K).
Proof. exact (eq_refl (@ε K)). Qed.
Lemma lem6781176 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term255 A K k f dom neut) = (term368 A K k dom f neut).
Proof. exact (MK_COMB (@lem6781175 K) (@lem6781174 A K k dom f neut)). Qed.
Lemma lem6781177 {K : Type'} : (@eq K) = (@eq K).
Proof. exact (eq_refl (@eq K)). Qed.
Lemma lem6781178 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term369 A K k f dom neut) = (term370 A K k dom f neut).
Proof. exact (MK_COMB (@lem6781177 K) (@lem6781176 A K k dom f neut)). Qed.
Lemma lem6781179 {K : Type'} (i : K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem6781180 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : ((term255 A K k f dom neut) = i) = ((term368 A K k dom f neut) = i).
Proof. exact (MK_COMB (@lem6781178 A K k dom f neut) (@lem6781179 K i)). Qed.
Lemma lem6781183 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6781184 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term371 A K k f dom neut i) = (term372 A K k dom f neut i).
Proof. exact (MK_COMB (@lem6781183) (@lem6781180 A K k dom f neut i)). Qed.
Lemma lem6781188 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem6781189 {K : Type'} (P : K -> Prop) (x : K) : (@IN K x P) = (P x).
Proof. exact (@lem6781188 K P x). Qed.
Lemma lem6781190 {K : Type'} (k : K -> Prop) (i : K) : (@IN K i k) = (k i).
Proof. exact (@lem6781189 K k i). Qed.
Lemma lem6781191 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6781192 {K : Type'} (k : K -> Prop) (i : K) : (term169 K i k) = (term293 K k i).
Proof. exact (MK_COMB (@lem6781191) (@lem6781190 K k i)). Qed.
Lemma lem6781194 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term294 A x s t) = (term295 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem6781195 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term294 A x s t) = (term295 A s x t).
Proof. exact (@lem6781194 A s x t). Qed.
Lemma lem6781196 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term105 A K f i dom neut) = (term296 A K dom f i neut).
Proof. exact (@lem6781195 A dom (f i) (@INSERT A neut (@EMPTY A))). Qed.
Lemma lem6781200 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem6781201 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem6781200 A P x). Qed.
Lemma lem6781202 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) : (term297 A K f i dom) = (term298 A K dom f i).
Proof. exact (@lem6781201 A dom (f i)). Qed.
Lemma lem6781203 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6781204 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) : (term299 A K f i dom) = (term300 A K dom f i).
Proof. exact (MK_COMB (@lem6781203) (@lem6781202 A K dom f i)). Qed.
Lemma lem6781206 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term301 A x y s) = (term302 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem6781207 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term301 A x y s) = (term302 A y x s).
Proof. exact (@lem6781206 A y x s). Qed.
Lemma lem6781208 {A K : Type'} (neut : A) (f : K -> A) (i : K) : (term303 A K f i neut) = (term304 A K neut f i).
Proof. exact (@lem6781207 A neut (f i) (@EMPTY A)). Qed.
Lemma lem6781214 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem6781215 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem6781214 A x). Qed.
Lemma lem6781216 {A K : Type'} (f : K -> A) (i : K) : (term305 A K f i) = False.
Proof. exact (@lem6781215 A (f i)). Qed.
Lemma lem6781217 {A K : Type'} (f : K -> A) (i : K) (neut : A) : (term306 A K f i neut) = (term306 A K f i neut).
Proof. exact (eq_refl (term306 A K f i neut)). Qed.
Lemma lem6781218 {A K : Type'} (f : K -> A) (i : K) (neut : A) : (term304 A K neut f i) = (term307 A K f i neut).
Proof. exact (MK_COMB (@lem6781217 A K f i neut) (@lem6781216 A K f i)). Qed.
Lemma lem6781220 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem6781221 {A K : Type'} (f : K -> A) (i : K) (neut : A) : (term307 A K f i neut) = ((f i) = neut).
Proof. exact (@lem6781220 ((f i) = neut)). Qed.
Lemma lem6781224 {A K : Type'} (f : K -> A) (i : K) (neut : A) : (term304 A K neut f i) = ((f i) = neut).
Proof. exact (TRANS (@lem6781218 A K f i neut) (@lem6781221 A K f i neut)). Qed.
Lemma lem6781225 {A K : Type'} (f : K -> A) (i : K) (neut : A) : (term303 A K f i neut) = ((f i) = neut).
Proof. exact (TRANS (@lem6781208 A K neut f i) (@lem6781224 A K f i neut)). Qed.
Lemma lem6781226 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6781227 {A K : Type'} (f : K -> A) (i : K) (neut : A) : (term308 A K f i neut) = (term309 A K f i neut).
Proof. exact (MK_COMB (@lem6781226) (@lem6781225 A K f i neut)). Qed.
Lemma lem6781228 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term296 A K dom f i neut) = (term310 A K dom f i neut).
Proof. exact (MK_COMB (@lem6781204 A K dom f i) (@lem6781227 A K f i neut)). Qed.
Lemma lem6781231 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term105 A K f i dom neut) = (term310 A K dom f i neut).
Proof. exact (TRANS (@lem6781196 A K dom f i neut) (@lem6781228 A K dom f i neut)). Qed.
Lemma lem6781232 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term244 A K k f i dom neut) = (term312 A K k dom f i neut).
Proof. exact (MK_COMB (@lem6781192 K k i) (@lem6781231 A K dom f i neut)). Qed.
Lemma lem6781235 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term257 A K k f i dom neut) = (term373 A K k dom f i neut).
Proof. exact (MK_COMB (@lem6781184 A K k dom f neut i) (@lem6781232 A K k dom f i neut)). Qed.
Lemma lem6781240 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term292 A K ltle k f i dom neut) = (term374 A K ltle k dom f i neut).
Proof. exact (MK_COMB (@lem6781117 A K ltle k dom f neut) (@lem6781235 A K k dom f i neut)). Qed.
Lemma lem6781243 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term374 A K ltle k dom f i neut) = (term292 A K ltle k f i dom neut).
Proof. exact (SYM (@lem6781240 A K ltle k dom f i neut)). Qed.
Lemma lem6781245 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6781246 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term374 A K ltle k dom f i neut) = (term375 A K ltle k dom f i neut).
Proof. exact (@lem6781245 (term374 A K ltle k dom f i neut)). Qed.
Lemma lem6781247 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term375 A K ltle k dom f i neut) = (term374 A K ltle k dom f i neut).
Proof. exact (SYM (@lem6781246 A K ltle k dom f i neut)). Qed.
Lemma lem6781248 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (h1 : term376 A K ltle k dom f i neut) : term376 A K ltle k dom f i neut.
Proof. exact (h1). Qed.
Lemma lem6781269 {K : Type'} (P : K -> Prop) : term377 K P.
Proof. exact (@lem19732 K P). Qed.
Lemma lem6781270 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : term378 A K k dom f neut.
Proof. exact (@lem6781269 K (term367 A K k dom f neut)). Qed.
Lemma lem6781271 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term379 A K k dom f neut) = (term380 A K k dom f neut).
Proof. exact (eq_refl (term379 A K k dom f neut)). Qed.
Lemma lem6781272 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (x : K) (neut : A) : (term381 A K k dom f neut x) = (term312 A K k dom f x neut).
Proof. exact (eq_refl (term381 A K k dom f neut x)). Qed.
Lemma lem6781273 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6781274 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (x : K) (neut : A) : (term382 A K k dom f neut x) = (term383 A K k dom f x neut).
Proof. exact (MK_COMB (@lem6781273) (@lem6781272 A K k dom f x neut)). Qed.
Lemma lem6781275 {A K : Type'} (x : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term384 A K x k dom f neut) = (term385 A K x k dom f neut).
Proof. exact (MK_COMB (@lem6781274 A K k dom f x neut) (@lem6781271 A K k dom f neut)). Qed.
Lemma lem6781276 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term386 A K k dom f neut) = (term387 A K k dom f neut).
Proof. exact (fun_ext (fun x : K => @lem6781275 A K x k dom f neut)). Qed.
Lemma lem6781277 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6781278 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term378 A K k dom f neut) = (term388 A K k dom f neut).
Proof. exact (MK_COMB (@lem6781277 K) (@lem6781276 A K k dom f neut)). Qed.
Lemma lem6781279 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : term388 A K k dom f neut.
Proof. exact (EQ_MP (@lem6781278 A K k dom f neut) (@lem6781270 A K k dom f neut)). Qed.
Lemma lem6781280 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : term389 A K k dom f.
Proof. exact (fun neut : A => @lem6781279 A K k dom f neut). Qed.
Lemma lem6781281 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) : term390 A K k dom.
Proof. exact (fun f : K -> A => @lem6781280 A K k dom f). Qed.
Lemma lem6781282 {A K : Type'} (k : K -> Prop) : term391 A K k.
Proof. exact (fun dom : A -> Prop => @lem6781281 A K k dom). Qed.
Lemma lem6781283 {A K : Type'} : term392 A K.
Proof. exact (fun k : K -> Prop => @lem6781282 A K k). Qed.
Lemma lem6781284 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (h1 : term393 A K ltle k dom f i neut) : term393 A K ltle k dom f i neut.
Proof. exact (h1). Qed.
Lemma lem6781285 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (h1 : term393 A K ltle k dom f i neut) : term375 A K ltle k dom f i neut.
Proof. exact (@lem6781284 A K ltle k dom f i neut h1 (@lem6781283 A K)). Qed.
Lemma lem6781286 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : term394 A K ltle k dom f i neut.
Proof. exact (fun h0 : term393 A K ltle k dom f i neut => @lem6781285 A K ltle k dom f i neut h0). Qed.
Lemma lem6781287 {A K : Type'} (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : _88875 = (term395 A K).
Proof. exact (h1). Qed.
Lemma lem6781288 {K : Type'} (k : K -> Prop) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem6781289 {A K : Type'} (k : K -> Prop) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (_88875 k) = (term396 A K k).
Proof. exact (MK_COMB (@lem6781287 A K _88875 h1) (@lem6781288 K k)). Qed.
Lemma lem6781290 {A K : Type'} (k : K -> Prop) : (term396 A K k) = (term397 A K k).
Proof. exact (eq_refl (term396 A K k)). Qed.
Lemma lem6781291 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) : (term398 A K _88875 k) = (term398 A K _88875 k).
Proof. exact (eq_refl (term398 A K _88875 k)). Qed.
Lemma lem6781292 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) : ((_88875 k) = (term396 A K k)) = ((_88875 k) = (term397 A K k)).
Proof. exact (MK_COMB (@lem6781291 A K _88875 k) (@lem6781290 A K k)). Qed.
Lemma lem6781293 {A K : Type'} (k : K -> Prop) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (_88875 k) = (term397 A K k).
Proof. exact (EQ_MP (@lem6781292 A K _88875 k) (@lem6781289 A K k _88875 h1)). Qed.
Lemma lem6781294 {A : Type'} (dom : A -> Prop) : dom = dom.
Proof. exact (eq_refl dom). Qed.
Lemma lem6781295 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (_88875 k dom) = (term399 A K k dom).
Proof. exact (MK_COMB (@lem6781293 A K k _88875 h1) (@lem6781294 A dom)). Qed.
Lemma lem6781296 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) : (term399 A K k dom) = (term400 A K k dom).
Proof. exact (eq_refl (term399 A K k dom)). Qed.
Lemma lem6781297 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) : (term401 A K _88875 k dom) = (term401 A K _88875 k dom).
Proof. exact (eq_refl (term401 A K _88875 k dom)). Qed.
Lemma lem6781298 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) : ((_88875 k dom) = (term399 A K k dom)) = ((_88875 k dom) = (term400 A K k dom)).
Proof. exact (MK_COMB (@lem6781297 A K _88875 k dom) (@lem6781296 A K k dom)). Qed.
Lemma lem6781299 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (_88875 k dom) = (term400 A K k dom).
Proof. exact (EQ_MP (@lem6781298 A K _88875 k dom) (@lem6781295 A K k dom _88875 h1)). Qed.
Lemma lem6781300 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6781301 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (_88875 k dom f) = (term402 A K k dom f).
Proof. exact (MK_COMB (@lem6781299 A K k dom _88875 h1) (@lem6781300 A K f)). Qed.
Lemma lem6781302 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term402 A K k dom f) = (term403 A K k dom f).
Proof. exact (eq_refl (term402 A K k dom f)). Qed.
Lemma lem6781303 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term404 A K _88875 k dom f) = (term404 A K _88875 k dom f).
Proof. exact (eq_refl (term404 A K _88875 k dom f)). Qed.
Lemma lem6781304 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : ((_88875 k dom f) = (term402 A K k dom f)) = ((_88875 k dom f) = (term403 A K k dom f)).
Proof. exact (MK_COMB (@lem6781303 A K _88875 k dom f) (@lem6781302 A K k dom f)). Qed.
Lemma lem6781305 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (_88875 k dom f) = (term403 A K k dom f).
Proof. exact (EQ_MP (@lem6781304 A K _88875 k dom f) (@lem6781301 A K k dom f _88875 h1)). Qed.
Lemma lem6781306 {A : Type'} (neut : A) : neut = neut.
Proof. exact (eq_refl neut). Qed.
Lemma lem6781307 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (_88875 k dom f neut) = (term405 A K k dom f neut).
Proof. exact (MK_COMB (@lem6781305 A K k dom f _88875 h1) (@lem6781306 A neut)). Qed.
Lemma lem6781308 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term405 A K k dom f neut) = (term368 A K k dom f neut).
Proof. exact (eq_refl (term405 A K k dom f neut)). Qed.
Lemma lem6781309 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term406 A K _88875 k dom f neut) = (term406 A K _88875 k dom f neut).
Proof. exact (eq_refl (term406 A K _88875 k dom f neut)). Qed.
Lemma lem6781310 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : ((_88875 k dom f neut) = (term405 A K k dom f neut)) = ((_88875 k dom f neut) = (term368 A K k dom f neut)).
Proof. exact (MK_COMB (@lem6781309 A K _88875 k dom f neut) (@lem6781308 A K k dom f neut)). Qed.
Lemma lem6781311 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (_88875 k dom f neut) = (term368 A K k dom f neut).
Proof. exact (EQ_MP (@lem6781310 A K _88875 k dom f neut) (@lem6781307 A K k dom f neut _88875 h1)). Qed.
Lemma lem6781312 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (term368 A K k dom f neut) = (_88875 k dom f neut).
Proof. exact (SYM (@lem6781311 A K k dom f neut _88875 h1)). Qed.
Lemma lem6781313 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : term407 A K _88875 k dom f.
Proof. exact (fun neut : A => @lem6781312 A K k dom f neut _88875 h1). Qed.
Lemma lem6781314 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : term408 A K _88875 k dom.
Proof. exact (fun f : K -> A => @lem6781313 A K k dom f _88875 h1). Qed.
Lemma lem6781315 {A K : Type'} (k : K -> Prop) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : term409 A K _88875 k.
Proof. exact (fun dom : A -> Prop => @lem6781314 A K k dom _88875 h1). Qed.
Lemma lem6781316 {A K : Type'} (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : term410 A K _88875.
Proof. exact (fun k : K -> Prop => @lem6781315 A K k _88875 h1). Qed.
Lemma lem6781317 {A K : Type'} (k : K -> Prop) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : term411 A K _88875 k.
Proof. exact (@lem6781316 A K _88875 h1 k). Qed.
Lemma lem6781318 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) : (term411 A K _88875 k) = (term409 A K _88875 k).
Proof. exact (eq_refl (term411 A K _88875 k)). Qed.
Lemma lem6781319 {A K : Type'} (k : K -> Prop) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : term409 A K _88875 k.
Proof. exact (EQ_MP (@lem6781318 A K _88875 k) (@lem6781317 A K k _88875 h1)). Qed.
Lemma lem6781320 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : term412 A K _88875 k dom.
Proof. exact (@lem6781319 A K k _88875 h1 dom). Qed.
Lemma lem6781321 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) : (term412 A K _88875 k dom) = (term408 A K _88875 k dom).
Proof. exact (eq_refl (term412 A K _88875 k dom)). Qed.
Lemma lem6781322 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : term408 A K _88875 k dom.
Proof. exact (EQ_MP (@lem6781321 A K _88875 k dom) (@lem6781320 A K k dom _88875 h1)). Qed.
Lemma lem6781323 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : term413 A K _88875 k dom f.
Proof. exact (@lem6781322 A K k dom _88875 h1 f). Qed.
Lemma lem6781324 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term413 A K _88875 k dom f) = (term407 A K _88875 k dom f).
Proof. exact (eq_refl (term413 A K _88875 k dom f)). Qed.
Lemma lem6781325 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : term407 A K _88875 k dom f.
Proof. exact (EQ_MP (@lem6781324 A K _88875 k dom f) (@lem6781323 A K k dom f _88875 h1)). Qed.
Lemma lem6781326 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : term414 A K _88875 k dom f neut.
Proof. exact (@lem6781325 A K k dom f _88875 h1 neut). Qed.
Lemma lem6781327 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term414 A K _88875 k dom f neut) = ((term368 A K k dom f neut) = (_88875 k dom f neut)).
Proof. exact (eq_refl (term414 A K _88875 k dom f neut)). Qed.
Lemma lem6781330 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (term368 A K k dom f neut) = (_88875 k dom f neut).
Proof. exact (EQ_MP (@lem6781327 A K _88875 k dom f neut) (@lem6781326 A K k dom f neut _88875 h1)). Qed.
Lemma lem6781331 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (term368 A K k dom f neut) = (_88875 k dom f neut).
Proof. exact (@lem6781330 A K k dom f neut _88875 h1). Qed.
Lemma lem6781332 {K : Type'} (k : K -> Prop) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem6781333 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (term415 A K k dom f neut) = (term416 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6781332 K k) (@lem6781331 A K k dom f neut _88875 h1)). Qed.
Lemma lem6781334 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6781335 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (term417 A K k dom f neut) = (term418 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6781334) (@lem6781333 A K k dom f neut _88875 h1)). Qed.
Lemma lem6781337 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (term368 A K k dom f neut) = (_88875 k dom f neut).
Proof. exact (EQ_MP (@lem6781327 A K _88875 k dom f neut) (@lem6781326 A K k dom f neut _88875 h1)). Qed.
Lemma lem6781338 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (term368 A K k dom f neut) = (_88875 k dom f neut).
Proof. exact (@lem6781337 A K k dom f neut _88875 h1). Qed.
Lemma lem6781339 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6781340 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (term419 A K k dom f neut) = (term420 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6781339 A K f) (@lem6781338 A K k dom f neut _88875 h1)). Qed.
Lemma lem6781341 {A : Type'} (dom : A -> Prop) : dom = dom.
Proof. exact (eq_refl dom). Qed.
Lemma lem6781342 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (term421 A K k dom f neut) = (term422 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6781341 A dom) (@lem6781340 A K k dom f neut _88875 h1)). Qed.
Lemma lem6781343 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6781344 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (term423 A K k dom f neut) = (term424 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6781343) (@lem6781342 A K k dom f neut _88875 h1)). Qed.
Lemma lem6781346 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (term368 A K k dom f neut) = (_88875 k dom f neut).
Proof. exact (EQ_MP (@lem6781327 A K _88875 k dom f neut) (@lem6781326 A K k dom f neut _88875 h1)). Qed.
Lemma lem6781347 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (term368 A K k dom f neut) = (_88875 k dom f neut).
Proof. exact (@lem6781346 A K k dom f neut _88875 h1). Qed.
Lemma lem6781348 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6781349 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (term419 A K k dom f neut) = (term420 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6781348 A K f) (@lem6781347 A K k dom f neut _88875 h1)). Qed.
Lemma lem6781350 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem6781351 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (term425 A K k dom f neut) = (term426 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6781350 A) (@lem6781349 A K k dom f neut _88875 h1)). Qed.
Lemma lem6781352 {A : Type'} (neut : A) : neut = neut.
Proof. exact (eq_refl neut). Qed.
Lemma lem6781353 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : ((term419 A K k dom f neut) = neut) = ((term420 A K _88875 k dom f neut) = neut).
Proof. exact (MK_COMB (@lem6781351 A K k dom f neut _88875 h1) (@lem6781352 A neut)). Qed.
Lemma lem6781354 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6781355 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (term427 A K k dom f neut) = (term428 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6781354) (@lem6781353 A K k dom f neut _88875 h1)). Qed.
Lemma lem6781356 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (term429 A K k dom f neut) = (term430 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6781344 A K k dom f neut _88875 h1) (@lem6781355 A K k dom f neut _88875 h1)). Qed.
Lemma lem6781357 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (term380 A K k dom f neut) = (term431 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6781335 A K k dom f neut _88875 h1) (@lem6781356 A K k dom f neut _88875 h1)). Qed.
Lemma lem6781358 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (x : K) (neut : A) : (term383 A K k dom f x neut) = (term383 A K k dom f x neut).
Proof. exact (eq_refl (term383 A K k dom f x neut)). Qed.
Lemma lem6781359 {A K : Type'} (x : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (term385 A K x k dom f neut) = (term432 A K x _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6781358 A K k dom f x neut) (@lem6781357 A K k dom f neut _88875 h1)). Qed.
Lemma lem6781360 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (term387 A K k dom f neut) = (term433 A K _88875 k dom f neut).
Proof. exact (fun_ext (fun x : K => @lem6781359 A K x k dom f neut _88875 h1)). Qed.
Lemma lem6781361 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6781362 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (term388 A K k dom f neut) = (term434 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6781361 K) (@lem6781360 A K k dom f neut _88875 h1)). Qed.
Lemma lem6781363 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (term435 A K k dom f) = (term436 A K _88875 k dom f).
Proof. exact (fun_ext (fun neut : A => @lem6781362 A K k dom f neut _88875 h1)). Qed.
Lemma lem6781364 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6781365 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (term389 A K k dom f) = (term437 A K _88875 k dom f).
Proof. exact (MK_COMB (@lem6781364 A) (@lem6781363 A K k dom f _88875 h1)). Qed.
Lemma lem6781366 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (term438 A K k dom) = (term439 A K _88875 k dom).
Proof. exact (fun_ext (fun f : K -> A => @lem6781365 A K k dom f _88875 h1)). Qed.
Lemma lem6781367 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem6781368 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (term390 A K k dom) = (term440 A K _88875 k dom).
Proof. exact (MK_COMB (@lem6781367 A K) (@lem6781366 A K k dom _88875 h1)). Qed.
Lemma lem6781369 {A K : Type'} (k : K -> Prop) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (term441 A K k) = (term442 A K _88875 k).
Proof. exact (fun_ext (fun dom : A -> Prop => @lem6781368 A K k dom _88875 h1)). Qed.
Lemma lem6781370 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6781371 {A K : Type'} (k : K -> Prop) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (term391 A K k) = (term443 A K _88875 k).
Proof. exact (MK_COMB (@lem6781370 A) (@lem6781369 A K k _88875 h1)). Qed.
Lemma lem6781372 {A K : Type'} (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (term444 A K) = (term445 A K _88875).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6781371 A K k _88875 h1)). Qed.
Lemma lem6781373 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6781374 {A K : Type'} (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (term392 A K) = (term446 A K _88875).
Proof. exact (MK_COMB (@lem6781373 K) (@lem6781372 A K _88875 h1)). Qed.
Lemma lem6781375 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6781376 {A K : Type'} (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (term447 A K) = (term448 A K _88875).
Proof. exact (MK_COMB (@lem6781375) (@lem6781374 A K _88875 h1)). Qed.
Lemma lem6781378 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (term368 A K k dom f neut) = (_88875 k dom f neut).
Proof. exact (EQ_MP (@lem6781327 A K _88875 k dom f neut) (@lem6781326 A K k dom f neut _88875 h1)). Qed.
Lemma lem6781379 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (term368 A K k dom f neut) = (_88875 k dom f neut).
Proof. exact (@lem6781378 A K k dom f neut _88875 h1). Qed.
Lemma lem6781380 {K : Type'} : (@eq K) = (@eq K).
Proof. exact (eq_refl (@eq K)). Qed.
Lemma lem6781381 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (term370 A K k dom f neut) = (term406 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6781380 K) (@lem6781379 A K k dom f neut _88875 h1)). Qed.
Lemma lem6781382 {K : Type'} (i : K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem6781383 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : ((term368 A K k dom f neut) = i) = ((_88875 k dom f neut) = i).
Proof. exact (MK_COMB (@lem6781381 A K k dom f neut _88875 h1) (@lem6781382 K i)). Qed.
Lemma lem6781384 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6781385 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (term372 A K k dom f neut i) = (term449 A K _88875 k dom f neut i).
Proof. exact (MK_COMB (@lem6781384) (@lem6781383 A K k dom f neut i _88875 h1)). Qed.
Lemma lem6781386 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term312 A K k dom f i neut) = (term312 A K k dom f i neut).
Proof. exact (eq_refl (term312 A K k dom f i neut)). Qed.
Lemma lem6781387 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (term373 A K k dom f i neut) = (term450 A K _88875 k dom f i neut).
Proof. exact (MK_COMB (@lem6781385 A K k dom f neut i _88875 h1) (@lem6781386 A K k dom f i neut)). Qed.
Lemma lem6781388 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term366 A K ltle k dom f neut) = (term366 A K ltle k dom f neut).
Proof. exact (eq_refl (term366 A K ltle k dom f neut)). Qed.
Lemma lem6781389 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (term374 A K ltle k dom f i neut) = (term451 A K ltle _88875 k dom f i neut).
Proof. exact (MK_COMB (@lem6781388 A K ltle k dom f neut) (@lem6781387 A K k dom f i neut _88875 h1)). Qed.
Lemma lem6781390 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6781391 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (term376 A K ltle k dom f i neut) = (term452 A K ltle _88875 k dom f i neut).
Proof. exact (MK_COMB (@lem6781390) (@lem6781389 A K ltle k dom f i neut _88875 h1)). Qed.
Lemma lem6781392 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6781393 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (term453 A K ltle k dom f i neut) = (term454 A K ltle _88875 k dom f i neut).
Proof. exact (MK_COMB (@lem6781392) (@lem6781391 A K ltle k dom f i neut _88875 h1)). Qed.
Lemma lem6781394 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem6781395 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (term375 A K ltle k dom f i neut) = (term455 A K ltle _88875 k dom f i neut).
Proof. exact (MK_COMB (@lem6781393 A K ltle k dom f i neut _88875 h1) (@lem6781394)). Qed.
Lemma lem6781396 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (term393 A K ltle k dom f i neut) = (term456 A K ltle _88875 k dom f i neut).
Proof. exact (MK_COMB (@lem6781376 A K _88875 h1) (@lem6781395 A K ltle k dom f i neut _88875 h1)). Qed.
Lemma lem6781397 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (h1 : term457 A K ltle k dom f i neut) : term457 A K ltle k dom f i neut.
Proof. exact (h1). Qed.
Lemma lem6781398 {A K : Type'} (_88875 : type836 A K) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (h1 : term457 A K ltle k dom f i neut) : term458 A K ltle k dom f i neut _88875.
Proof. exact (@lem6781397 A K ltle k dom f i neut h1 _88875). Qed.
Lemma lem6781399 {A K : Type'} (ltle : type1402 K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term458 A K ltle k dom f i neut _88875) = (term456 A K ltle _88875 k dom f i neut).
Proof. exact (eq_refl (term458 A K ltle k dom f i neut _88875)). Qed.
Lemma lem6781400 {A K : Type'} (_88875 : type836 A K) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (h1 : term457 A K ltle k dom f i neut) : term456 A K ltle _88875 k dom f i neut.
Proof. exact (EQ_MP (@lem6781399 A K ltle _88875 k dom f i neut) (@lem6781398 A K _88875 ltle k dom f i neut h1)). Qed.
Lemma lem6781401 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : (term456 A K ltle _88875 k dom f i neut) = (term393 A K ltle k dom f i neut).
Proof. exact (SYM (@lem6781396 A K ltle k dom f i neut _88875 h1)). Qed.
Lemma lem6781402 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (_88875 : type836 A K) (h1 : term457 A K ltle k dom f i neut) (h2 : _88875 = (term395 A K)) : term393 A K ltle k dom f i neut.
Proof. exact (EQ_MP (@lem6781401 A K ltle k dom f i neut _88875 h2) (@lem6781400 A K _88875 ltle k dom f i neut h1)). Qed.
Lemma lem6781403 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : term459 A K ltle k dom f i neut.
Proof. exact (fun h0 : term457 A K ltle k dom f i neut => @lem6781402 A K ltle k dom f i neut _88875 h0 h1). Qed.
Lemma lem6781404 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : term460 A K ltle k dom f i neut.
Proof. exact (@lem51 (term393 A K ltle k dom f i neut) (term457 A K ltle k dom f i neut) (term375 A K ltle k dom f i neut)). Qed.
Lemma lem6781405 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : term461 A K ltle k dom f i neut.
Proof. exact (@lem6781404 A K ltle k dom f i neut (@lem6781403 A K ltle k dom f i neut _88875 h1)). Qed.
Lemma lem6781406 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (_88875 : type836 A K) (h1 : _88875 = (term395 A K)) : term462 A K ltle k dom f i neut.
Proof. exact (@lem6781405 A K ltle k dom f i neut _88875 h1 (@lem6781286 A K ltle k dom f i neut)). Qed.
Lemma lem6781407 {A K : Type'} : (term395 A K) = (term395 A K).
Proof. exact (eq_refl (term395 A K)). Qed.
Lemma lem6781408 {A K : Type'} (_88875 : type836 A K) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : term463 A K _88875 ltle k dom f i neut.
Proof. exact (fun h0 : _88875 = (term395 A K) => @lem6781406 A K ltle k dom f i neut _88875 h0). Qed.
Lemma lem6781409 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : term464 A K ltle k dom f i neut.
Proof. exact (@lem6781408 A K (term395 A K) ltle k dom f i neut). Qed.
Lemma lem6781410 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : term462 A K ltle k dom f i neut.
Proof. exact (@lem6781409 A K ltle k dom f i neut (@lem6781407 A K)). Qed.
Lemma lem6781411 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (h1 : term457 A K ltle k dom f i neut) : term457 A K ltle k dom f i neut.
Proof. exact (h1). Qed.
Lemma lem6781412 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : term465 A K ltle k dom f i neut.
Proof. exact (fun h0 : term457 A K ltle k dom f i neut => @lem6781411 A K ltle k dom f i neut h0). Qed.
Lemma lem6781413 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : term466 A K ltle k dom f i neut.
Proof. exact (@lem51 (term457 A K ltle k dom f i neut) (term457 A K ltle k dom f i neut) (term375 A K ltle k dom f i neut)). Qed.
Lemma lem6781414 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : term467 A K ltle k dom f i neut.
Proof. exact (@lem6781413 A K ltle k dom f i neut (@lem6781412 A K ltle k dom f i neut)). Qed.
Lemma lem6781415 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : term462 A K ltle k dom f i neut.
Proof. exact (@lem6781414 A K ltle k dom f i neut (@lem6781410 A K ltle k dom f i neut)). Qed.
Lemma lem6781416 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (h1 : term462 A K ltle k dom f i neut) : term462 A K ltle k dom f i neut.
Proof. exact (h1). Qed.
Lemma lem6781417 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (h1 : term457 A K ltle k dom f i neut) : term457 A K ltle k dom f i neut.
Proof. exact (h1). Qed.
Lemma lem6781418 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (h1 : term457 A K ltle k dom f i neut) (h2 : term462 A K ltle k dom f i neut) : term375 A K ltle k dom f i neut.
Proof. exact (@lem6781416 A K ltle k dom f i neut h2 (@lem6781417 A K ltle k dom f i neut h1)). Qed.
Lemma lem6781419 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (h1 : term457 A K ltle k dom f i neut) : term468 A K ltle k dom f i neut.
Proof. exact (fun h0 : term462 A K ltle k dom f i neut => @lem6781418 A K ltle k dom f i neut h1 h0). Qed.
Lemma lem6781420 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (h1 : term462 A K ltle k dom f i neut) : term462 A K ltle k dom f i neut.
Proof. exact (h1). Qed.
Lemma lem6781421 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (h1 : term457 A K ltle k dom f i neut) (h2 : term462 A K ltle k dom f i neut) : term375 A K ltle k dom f i neut.
Proof. exact (@lem6781419 A K ltle k dom f i neut h1 (@lem6781420 A K ltle k dom f i neut h2)). Qed.
Lemma lem6781422 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (h1 : term462 A K ltle k dom f i neut) : term462 A K ltle k dom f i neut.
Proof. exact (fun h0 : term457 A K ltle k dom f i neut => @lem6781421 A K ltle k dom f i neut h0 h1). Qed.
Lemma lem6781423 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : term467 A K ltle k dom f i neut.
Proof. exact (fun h0 : term462 A K ltle k dom f i neut => @lem6781422 A K ltle k dom f i neut h0). Qed.
Lemma lem6781426 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : term462 A K ltle k dom f i neut.
Proof. exact (@lem6781423 A K ltle k dom f i neut (@lem6781415 A K ltle k dom f i neut)). Qed.
Lemma lem6781427 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : term462 A K ltle k dom f i neut.
Proof. exact (@lem6781426 A K ltle k dom f i neut). Qed.
Lemma lem6781489 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem6781490 {A K : Type'} (ltle : type1402 K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term455 A K ltle _88875 k dom f i neut) = (term469 A K ltle _88875 k dom f i neut).
Proof. exact (@lem6781489 (term452 A K ltle _88875 k dom f i neut)). Qed.
Lemma lem6781492 (t : Prop) : (term8 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem6781493 {A K : Type'} (ltle : type1402 K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term469 A K ltle _88875 k dom f i neut) = (term451 A K ltle _88875 k dom f i neut).
Proof. exact (@lem6781492 (term451 A K ltle _88875 k dom f i neut)). Qed.
Lemma lem6781496 {A K : Type'} (ltle : type1402 K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term455 A K ltle _88875 k dom f i neut) = (term451 A K ltle _88875 k dom f i neut).
Proof. exact (TRANS (@lem6781490 A K ltle _88875 k dom f i neut) (@lem6781493 A K ltle _88875 k dom f i neut)). Qed.
Lemma lem6781569 {A K : Type'} (_88875 : type836 A K) : (term448 A K _88875) = (term448 A K _88875).
Proof. exact (eq_refl (term448 A K _88875)). Qed.
Lemma lem6781570 {A K : Type'} (ltle : type1402 K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term456 A K ltle _88875 k dom f i neut) = (term470 A K ltle _88875 k dom f i neut).
Proof. exact (MK_COMB (@lem6781569 A K _88875) (@lem6781496 A K ltle _88875 k dom f i neut)). Qed.
Lemma lem6781573 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term471 A K ltle k dom f i neut) = (term472 A K ltle k dom f i neut).
Proof. exact (fun_ext (fun _88875 : type836 A K => @lem6781570 A K ltle _88875 k dom f i neut)). Qed.
Lemma lem6781574 {A K : Type'} : (@all ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K)) = (@all ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K)).
Proof. exact (eq_refl (@all ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K))). Qed.
Lemma lem6781575 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term457 A K ltle k dom f i neut) = (term473 A K ltle k dom f i neut).
Proof. exact (MK_COMB (@lem6781574 A K) (@lem6781573 A K ltle k dom f i neut)). Qed.
Lemma lem6781580 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term474 A K k dom f i neut) = (term475 A K k dom f i neut).
Proof. exact (fun_ext (fun ltle : type1402 K => @lem6781575 A K ltle k dom f i neut)). Qed.
Lemma lem6781581 {K : Type'} : (@all (K -> K -> Prop)) = (@all (K -> K -> Prop)).
Proof. exact (eq_refl (@all (K -> K -> Prop))). Qed.
Lemma lem6781582 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term476 A K k dom f i neut) = (term477 A K k dom f i neut).
Proof. exact (MK_COMB (@lem6781581 K) (@lem6781580 A K k dom f i neut)). Qed.
Lemma lem6781587 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term478 A K dom f i neut) = (term479 A K dom f i neut).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6781582 A K k dom f i neut)). Qed.
Lemma lem6781588 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6781589 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term480 A K dom f i neut) = (term481 A K dom f i neut).
Proof. exact (MK_COMB (@lem6781588 K) (@lem6781587 A K dom f i neut)). Qed.
Lemma lem6781594 {A K : Type'} (f : K -> A) (i : K) (neut : A) : (term482 A K f i neut) = (term483 A K f i neut).
Proof. exact (fun_ext (fun dom : A -> Prop => @lem6781589 A K dom f i neut)). Qed.
Lemma lem6781595 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6781596 {A K : Type'} (f : K -> A) (i : K) (neut : A) : (term484 A K f i neut) = (term485 A K f i neut).
Proof. exact (MK_COMB (@lem6781595 A) (@lem6781594 A K f i neut)). Qed.
Lemma lem6781601 {A K : Type'} (i : K) (neut : A) : (term486 A K i neut) = (term487 A K i neut).
Proof. exact (fun_ext (fun f : K -> A => @lem6781596 A K f i neut)). Qed.
Lemma lem6781602 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem6781603 {A K : Type'} (i : K) (neut : A) : (term488 A K i neut) = (term489 A K i neut).
Proof. exact (MK_COMB (@lem6781602 A K) (@lem6781601 A K i neut)). Qed.
Lemma lem6781608 {A K : Type'} (neut : A) : (term490 A K neut) = (term491 A K neut).
Proof. exact (fun_ext (fun i : K => @lem6781603 A K i neut)). Qed.
Lemma lem6781609 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6781610 {A K : Type'} (neut : A) : (term492 A K neut) = (term493 A K neut).
Proof. exact (MK_COMB (@lem6781609 K) (@lem6781608 A K neut)). Qed.
Lemma lem6781615 {A K : Type'} : (term494 A K) = (term495 A K).
Proof. exact (fun_ext (fun neut : A => @lem6781610 A K neut)). Qed.
Lemma lem6781616 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6781623 {A K : Type'} : (term496 A K) = (term497 A K).
Proof. exact (MK_COMB (@lem6781616 A) (@lem6781615 A K)). Qed.
Lemma lem6781624 {A K : Type'} (_88876 : type835 A K) (h1 : _88876 = (term498 A K)) : _88876 = (term498 A K).
Proof. exact (h1). Qed.
Lemma lem6781625 {K : Type'} (k : K -> Prop) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem6781626 {A K : Type'} (k : K -> Prop) (_88876 : type835 A K) (h1 : _88876 = (term498 A K)) : (_88876 k) = (term499 A K k).
Proof. exact (MK_COMB (@lem6781624 A K _88876 h1) (@lem6781625 K k)). Qed.
Lemma lem6781627 {A K : Type'} (k : K -> Prop) : (term499 A K k) = (term500 A K k).
Proof. exact (eq_refl (term499 A K k)). Qed.
Lemma lem6781628 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (term501 A K _88876 k) = (term501 A K _88876 k).
Proof. exact (eq_refl (term501 A K _88876 k)). Qed.
Lemma lem6781629 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : ((_88876 k) = (term499 A K k)) = ((_88876 k) = (term500 A K k)).
Proof. exact (MK_COMB (@lem6781628 A K _88876 k) (@lem6781627 A K k)). Qed.
Lemma lem6781630 {A K : Type'} (k : K -> Prop) (_88876 : type835 A K) (h1 : _88876 = (term498 A K)) : (_88876 k) = (term500 A K k).
Proof. exact (EQ_MP (@lem6781629 A K _88876 k) (@lem6781626 A K k _88876 h1)). Qed.
Lemma lem6781631 {A : Type'} (dom : A -> Prop) : dom = dom.
Proof. exact (eq_refl dom). Qed.
Lemma lem6781632 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (_88876 : type835 A K) (h1 : _88876 = (term498 A K)) : (_88876 k dom) = (term502 A K k dom).
Proof. exact (MK_COMB (@lem6781630 A K k _88876 h1) (@lem6781631 A dom)). Qed.
Lemma lem6781633 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) : (term502 A K k dom) = (term503 A K k dom).
Proof. exact (eq_refl (term502 A K k dom)). Qed.
Lemma lem6781634 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (term504 A K _88876 k dom) = (term504 A K _88876 k dom).
Proof. exact (eq_refl (term504 A K _88876 k dom)). Qed.
Lemma lem6781635 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : ((_88876 k dom) = (term502 A K k dom)) = ((_88876 k dom) = (term503 A K k dom)).
Proof. exact (MK_COMB (@lem6781634 A K _88876 k dom) (@lem6781633 A K k dom)). Qed.
Lemma lem6781636 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (_88876 : type835 A K) (h1 : _88876 = (term498 A K)) : (_88876 k dom) = (term503 A K k dom).
Proof. exact (EQ_MP (@lem6781635 A K _88876 k dom) (@lem6781632 A K k dom _88876 h1)). Qed.
Lemma lem6781637 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6781638 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (_88876 : type835 A K) (h1 : _88876 = (term498 A K)) : (_88876 k dom f) = (term505 A K k dom f).
Proof. exact (MK_COMB (@lem6781636 A K k dom _88876 h1) (@lem6781637 A K f)). Qed.
Lemma lem6781639 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term505 A K k dom f) = (term506 A K k dom f).
Proof. exact (eq_refl (term505 A K k dom f)). Qed.
Lemma lem6781640 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term507 A K _88876 k dom f) = (term507 A K _88876 k dom f).
Proof. exact (eq_refl (term507 A K _88876 k dom f)). Qed.
Lemma lem6781641 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : ((_88876 k dom f) = (term505 A K k dom f)) = ((_88876 k dom f) = (term506 A K k dom f)).
Proof. exact (MK_COMB (@lem6781640 A K _88876 k dom f) (@lem6781639 A K k dom f)). Qed.
Lemma lem6781642 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (_88876 : type835 A K) (h1 : _88876 = (term498 A K)) : (_88876 k dom f) = (term506 A K k dom f).
Proof. exact (EQ_MP (@lem6781641 A K _88876 k dom f) (@lem6781638 A K k dom f _88876 h1)). Qed.
Lemma lem6781643 {A : Type'} (neut : A) : neut = neut.
Proof. exact (eq_refl neut). Qed.
Lemma lem6781644 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (_88876 : type835 A K) (h1 : _88876 = (term498 A K)) : (_88876 k dom f neut) = (term508 A K k dom f neut).
Proof. exact (MK_COMB (@lem6781642 A K k dom f _88876 h1) (@lem6781643 A neut)). Qed.
Lemma lem6781645 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term508 A K k dom f neut) = (term361 A K k dom f neut).
Proof. exact (eq_refl (term508 A K k dom f neut)). Qed.
Lemma lem6781646 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term509 A K _88876 k dom f neut) = (term509 A K _88876 k dom f neut).
Proof. exact (eq_refl (term509 A K _88876 k dom f neut)). Qed.
Lemma lem6781647 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : ((_88876 k dom f neut) = (term508 A K k dom f neut)) = ((_88876 k dom f neut) = (term361 A K k dom f neut)).
Proof. exact (MK_COMB (@lem6781646 A K _88876 k dom f neut) (@lem6781645 A K k dom f neut)). Qed.
Lemma lem6781648 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (_88876 : type835 A K) (h1 : _88876 = (term498 A K)) : (_88876 k dom f neut) = (term361 A K k dom f neut).
Proof. exact (EQ_MP (@lem6781647 A K _88876 k dom f neut) (@lem6781644 A K k dom f neut _88876 h1)). Qed.
Lemma lem6781688 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term450 A K _88875 k dom f i neut) = (term450 A K _88875 k dom f i neut).
Proof. exact (eq_refl (term450 A K _88875 k dom f i neut)). Qed.
Lemma lem6781690 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (_88876 : type835 A K) (h1 : _88876 = (term498 A K)) : (term361 A K k dom f neut) = (_88876 k dom f neut).
Proof. exact (SYM (@lem6781648 A K k dom f neut _88876 h1)). Qed.
Lemma lem6781691 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (_88876 : type835 A K) (h1 : _88876 = (term498 A K)) : (term361 A K k dom f neut) = (_88876 k dom f neut).
Proof. exact (@lem6781690 A K k dom f neut _88876 h1). Qed.
Lemma lem6781692 {K : Type'} : (@GSPEC K) = (@GSPEC K).
Proof. exact (eq_refl (@GSPEC K)). Qed.
Lemma lem6781693 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (_88876 : type835 A K) (h1 : _88876 = (term498 A K)) : (term362 A K k dom f neut) = (term510 A K _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6781692 K) (@lem6781691 A K k dom f neut _88876 h1)). Qed.
Lemma lem6781694 {K : Type'} : (@FINITE K) = (@FINITE K).
Proof. exact (eq_refl (@FINITE K)). Qed.
Lemma lem6781695 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (_88876 : type835 A K) (h1 : _88876 = (term498 A K)) : (term363 A K k dom f neut) = (term511 A K _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6781694 K) (@lem6781693 A K k dom f neut _88876 h1)). Qed.
Lemma lem6781720 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (x : K) (neut : A) : (term351 A K k dom f x neut) = (term351 A K k dom f x neut).
Proof. exact (eq_refl (term351 A K k dom f x neut)). Qed.
Lemma lem6781721 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term353 A K k dom f neut) = (term353 A K k dom f neut).
Proof. exact (fun_ext (fun x : K => @lem6781720 A K k dom f x neut)). Qed.
Lemma lem6781722 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6781723 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term354 A K k dom f neut) = (term354 A K k dom f neut).
Proof. exact (MK_COMB (@lem6781722 K) (@lem6781721 A K k dom f neut)). Qed.
Lemma lem6781724 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6781725 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term355 A K k dom f neut) = (term355 A K k dom f neut).
Proof. exact (MK_COMB (@lem6781724) (@lem6781723 A K k dom f neut)). Qed.
Lemma lem6781726 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6781727 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term356 A K k dom f neut) = (term356 A K k dom f neut).
Proof. exact (MK_COMB (@lem6781726) (@lem6781725 A K k dom f neut)). Qed.
Lemma lem6781728 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (_88876 : type835 A K) (h1 : _88876 = (term498 A K)) : (term364 A K k dom f neut) = (term512 A K _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6781727 A K k dom f neut) (@lem6781695 A K k dom f neut _88876 h1)). Qed.
Lemma lem6781767 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i' : K) (i : K) : (term318 A K ltle k dom f neut i' i) = (term318 A K ltle k dom f neut i' i).
Proof. exact (eq_refl (term318 A K ltle k dom f neut i' i)). Qed.
Lemma lem6781768 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term320 A K ltle k dom f neut i) = (term320 A K ltle k dom f neut i).
Proof. exact (fun_ext (fun i' : K => @lem6781767 A K ltle k dom f neut i' i)). Qed.
Lemma lem6781769 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6781770 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term322 A K ltle k dom f neut i) = (term322 A K ltle k dom f neut i).
Proof. exact (MK_COMB (@lem6781769 K) (@lem6781768 A K ltle k dom f neut i)). Qed.
Lemma lem6781789 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term311 A K dom f i neut) = (term311 A K dom f i neut).
Proof. exact (eq_refl (term311 A K dom f i neut)). Qed.
Lemma lem6781790 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term324 A K ltle k dom f neut i) = (term324 A K ltle k dom f neut i).
Proof. exact (MK_COMB (@lem6781789 A K dom f i neut) (@lem6781770 A K ltle k dom f neut i)). Qed.
Lemma lem6781795 {K : Type'} (k : K -> Prop) (i : K) : (term293 K k i) = (term293 K k i).
Proof. exact (eq_refl (term293 K k i)). Qed.
Lemma lem6781796 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term326 A K ltle k dom f neut i) = (term326 A K ltle k dom f neut i).
Proof. exact (MK_COMB (@lem6781795 K k i) (@lem6781790 A K ltle k dom f neut i)). Qed.
Lemma lem6781797 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term328 A K ltle k dom f neut) = (term328 A K ltle k dom f neut).
Proof. exact (fun_ext (fun i : K => @lem6781796 A K ltle k dom f neut i)). Qed.
Lemma lem6781798 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem6781799 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term329 A K ltle k dom f neut) = (term329 A K ltle k dom f neut).
Proof. exact (MK_COMB (@lem6781798 K) (@lem6781797 A K ltle k dom f neut)). Qed.
Lemma lem6781800 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6781801 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term330 A K ltle k dom f neut) = (term330 A K ltle k dom f neut).
Proof. exact (MK_COMB (@lem6781800) (@lem6781799 A K ltle k dom f neut)). Qed.
Lemma lem6781802 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6781803 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term331 A K ltle k dom f neut) = (term331 A K ltle k dom f neut).
Proof. exact (MK_COMB (@lem6781802) (@lem6781801 A K ltle k dom f neut)). Qed.
Lemma lem6781804 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (_88876 : type835 A K) (h1 : _88876 = (term498 A K)) : (term365 A K ltle k dom f neut) = (term513 A K ltle _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6781803 A K ltle k dom f neut) (@lem6781728 A K k dom f neut _88876 h1)). Qed.
Lemma lem6781805 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6781806 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (_88876 : type835 A K) (h1 : _88876 = (term498 A K)) : (term366 A K ltle k dom f neut) = (term514 A K ltle _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6781805) (@lem6781804 A K ltle k dom f neut _88876 h1)). Qed.
Lemma lem6781807 {A K : Type'} (ltle : type1402 K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (_88876 : type835 A K) (h1 : _88876 = (term498 A K)) : (term451 A K ltle _88875 k dom f i neut) = (term515 A K ltle _88876 _88875 k dom f i neut).
Proof. exact (MK_COMB (@lem6781806 A K ltle k dom f neut _88876 h1) (@lem6781688 A K _88875 k dom f i neut)). Qed.
Lemma lem6781880 {A K : Type'} (x : K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term432 A K x _88875 k dom f neut) = (term432 A K x _88875 k dom f neut).
Proof. exact (eq_refl (term432 A K x _88875 k dom f neut)). Qed.
Lemma lem6781881 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term433 A K _88875 k dom f neut) = (term433 A K _88875 k dom f neut).
Proof. exact (fun_ext (fun x : K => @lem6781880 A K x _88875 k dom f neut)). Qed.
Lemma lem6781882 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6781883 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term434 A K _88875 k dom f neut) = (term434 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6781882 K) (@lem6781881 A K _88875 k dom f neut)). Qed.
Lemma lem6781884 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term436 A K _88875 k dom f) = (term436 A K _88875 k dom f).
Proof. exact (fun_ext (fun neut : A => @lem6781883 A K _88875 k dom f neut)). Qed.
Lemma lem6781885 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6781886 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term437 A K _88875 k dom f) = (term437 A K _88875 k dom f).
Proof. exact (MK_COMB (@lem6781885 A) (@lem6781884 A K _88875 k dom f)). Qed.
Lemma lem6781887 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) : (term439 A K _88875 k dom) = (term439 A K _88875 k dom).
Proof. exact (fun_ext (fun f : K -> A => @lem6781886 A K _88875 k dom f)). Qed.
Lemma lem6781888 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem6781889 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) : (term440 A K _88875 k dom) = (term440 A K _88875 k dom).
Proof. exact (MK_COMB (@lem6781888 A K) (@lem6781887 A K _88875 k dom)). Qed.
Lemma lem6781890 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) : (term442 A K _88875 k) = (term442 A K _88875 k).
Proof. exact (fun_ext (fun dom : A -> Prop => @lem6781889 A K _88875 k dom)). Qed.
Lemma lem6781891 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6781892 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) : (term443 A K _88875 k) = (term443 A K _88875 k).
Proof. exact (MK_COMB (@lem6781891 A) (@lem6781890 A K _88875 k)). Qed.
Lemma lem6781893 {A K : Type'} (_88875 : type836 A K) : (term445 A K _88875) = (term445 A K _88875).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6781892 A K _88875 k)). Qed.
Lemma lem6781894 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6781895 {A K : Type'} (_88875 : type836 A K) : (term446 A K _88875) = (term446 A K _88875).
Proof. exact (MK_COMB (@lem6781894 K) (@lem6781893 A K _88875)). Qed.
Lemma lem6781896 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6781897 {A K : Type'} (_88875 : type836 A K) : (term448 A K _88875) = (term448 A K _88875).
Proof. exact (MK_COMB (@lem6781896) (@lem6781895 A K _88875)). Qed.
Lemma lem6781898 {A K : Type'} (ltle : type1402 K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (_88876 : type835 A K) (h1 : _88876 = (term498 A K)) : (term470 A K ltle _88875 k dom f i neut) = (term516 A K ltle _88876 _88875 k dom f i neut).
Proof. exact (MK_COMB (@lem6781897 A K _88875) (@lem6781807 A K ltle _88875 k dom f i neut _88876 h1)). Qed.
Lemma lem6781899 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (_88876 : type835 A K) (h1 : _88876 = (term498 A K)) : (term472 A K ltle k dom f i neut) = (term517 A K ltle _88876 k dom f i neut).
Proof. exact (fun_ext (fun _88875 : type836 A K => @lem6781898 A K ltle _88875 k dom f i neut _88876 h1)). Qed.
Lemma lem6781900 {A K : Type'} : (@all ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K)) = (@all ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K)).
Proof. exact (eq_refl (@all ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K))). Qed.
Lemma lem6781901 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (_88876 : type835 A K) (h1 : _88876 = (term498 A K)) : (term473 A K ltle k dom f i neut) = (term518 A K ltle _88876 k dom f i neut).
Proof. exact (MK_COMB (@lem6781900 A K) (@lem6781899 A K ltle k dom f i neut _88876 h1)). Qed.
Lemma lem6781902 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (_88876 : type835 A K) (h1 : _88876 = (term498 A K)) : (term475 A K k dom f i neut) = (term519 A K _88876 k dom f i neut).
Proof. exact (fun_ext (fun ltle : type1402 K => @lem6781901 A K ltle k dom f i neut _88876 h1)). Qed.
Lemma lem6781903 {K : Type'} : (@all (K -> K -> Prop)) = (@all (K -> K -> Prop)).
Proof. exact (eq_refl (@all (K -> K -> Prop))). Qed.
Lemma lem6781904 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (_88876 : type835 A K) (h1 : _88876 = (term498 A K)) : (term477 A K k dom f i neut) = (term520 A K _88876 k dom f i neut).
Proof. exact (MK_COMB (@lem6781903 K) (@lem6781902 A K k dom f i neut _88876 h1)). Qed.
Lemma lem6781905 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (_88876 : type835 A K) (h1 : _88876 = (term498 A K)) : (term479 A K dom f i neut) = (term521 A K _88876 dom f i neut).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6781904 A K k dom f i neut _88876 h1)). Qed.
Lemma lem6781906 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6781907 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (_88876 : type835 A K) (h1 : _88876 = (term498 A K)) : (term481 A K dom f i neut) = (term522 A K _88876 dom f i neut).
Proof. exact (MK_COMB (@lem6781906 K) (@lem6781905 A K dom f i neut _88876 h1)). Qed.
Lemma lem6781908 {A K : Type'} (f : K -> A) (i : K) (neut : A) (_88876 : type835 A K) (h1 : _88876 = (term498 A K)) : (term483 A K f i neut) = (term523 A K _88876 f i neut).
Proof. exact (fun_ext (fun dom : A -> Prop => @lem6781907 A K dom f i neut _88876 h1)). Qed.
Lemma lem6781909 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6781910 {A K : Type'} (f : K -> A) (i : K) (neut : A) (_88876 : type835 A K) (h1 : _88876 = (term498 A K)) : (term485 A K f i neut) = (term524 A K _88876 f i neut).
Proof. exact (MK_COMB (@lem6781909 A) (@lem6781908 A K f i neut _88876 h1)). Qed.
Lemma lem6781911 {A K : Type'} (i : K) (neut : A) (_88876 : type835 A K) (h1 : _88876 = (term498 A K)) : (term487 A K i neut) = (term525 A K _88876 i neut).
Proof. exact (fun_ext (fun f : K -> A => @lem6781910 A K f i neut _88876 h1)). Qed.
Lemma lem6781912 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem6781913 {A K : Type'} (i : K) (neut : A) (_88876 : type835 A K) (h1 : _88876 = (term498 A K)) : (term489 A K i neut) = (term526 A K _88876 i neut).
Proof. exact (MK_COMB (@lem6781912 A K) (@lem6781911 A K i neut _88876 h1)). Qed.
Lemma lem6781914 {A K : Type'} (neut : A) (_88876 : type835 A K) (h1 : _88876 = (term498 A K)) : (term491 A K neut) = (term527 A K _88876 neut).
Proof. exact (fun_ext (fun i : K => @lem6781913 A K i neut _88876 h1)). Qed.
Lemma lem6781915 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6781916 {A K : Type'} (neut : A) (_88876 : type835 A K) (h1 : _88876 = (term498 A K)) : (term493 A K neut) = (term528 A K _88876 neut).
Proof. exact (MK_COMB (@lem6781915 K) (@lem6781914 A K neut _88876 h1)). Qed.
Lemma lem6781917 {A K : Type'} (_88876 : type835 A K) (h1 : _88876 = (term498 A K)) : (term495 A K) = (term529 A K _88876).
Proof. exact (fun_ext (fun neut : A => @lem6781916 A K neut _88876 h1)). Qed.
Lemma lem6781918 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6781919 {A K : Type'} (_88876 : type835 A K) (h1 : _88876 = (term498 A K)) : (term497 A K) = (term530 A K _88876).
Proof. exact (MK_COMB (@lem6781918 A) (@lem6781917 A K _88876 h1)). Qed.
Lemma lem6781920 {A K : Type'} (_88876 : type835 A K) : term531 A K _88876.
Proof. exact (fun h0 : _88876 = (term498 A K) => @lem6781919 A K _88876 h0). Qed.
Lemma lem6781921 {A K : Type'} : term532 A K.
Proof. exact (fun _88876 : type835 A K => @lem6781920 A K _88876). Qed.
Lemma lem6781923 {_3603 : Type'} (P : Prop) (c : _3603) (Q : _3603 -> Prop) : term533 _3603 P c Q.
Proof. exact (EQ_MP (@lem20230 _3603 P c Q) (@lem0)). Qed.
Lemma lem6781924 {A K : Type'} (P : Prop) (c : type835 A K) (Q : type212 A K) : term534 A K P c Q.
Proof. exact (@lem6781923 (type835 A K) P c Q). Qed.
Lemma lem6781925 {A K : Type'} : term535 A K.
Proof. exact (@lem6781924 A K (term497 A K) (term498 A K) (term536 A K)). Qed.
Lemma lem6781926 {A K : Type'} (_88876 : type835 A K) : (term537 A K _88876) = (term530 A K _88876).
Proof. exact (eq_refl (term537 A K _88876)). Qed.
Lemma lem6781927 {A K : Type'} : (term538 A K) = (term538 A K).
Proof. exact (eq_refl (term538 A K)). Qed.
Lemma lem6781928 {A K : Type'} (_88876 : type835 A K) : ((term497 A K) = (term537 A K _88876)) = ((term497 A K) = (term530 A K _88876)).
Proof. exact (MK_COMB (@lem6781927 A K) (@lem6781926 A K _88876)). Qed.
Lemma lem6781929 {A K : Type'} (_88876 : type835 A K) : (term539 A K _88876) = (term539 A K _88876).
Proof. exact (eq_refl (term539 A K _88876)). Qed.
Lemma lem6781930 {A K : Type'} (_88876 : type835 A K) : (term540 A K _88876) = (term531 A K _88876).
Proof. exact (MK_COMB (@lem6781929 A K _88876) (@lem6781928 A K _88876)). Qed.
Lemma lem6781931 {A K : Type'} : (term541 A K) = (term542 A K).
Proof. exact (fun_ext (fun _88876 : type835 A K => @lem6781930 A K _88876)). Qed.
Lemma lem6781932 {A K : Type'} : (@all ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K -> Prop)) = (@all ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K -> Prop)).
Proof. exact (eq_refl (@all ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K -> Prop))). Qed.
Lemma lem6781933 {A K : Type'} : (term543 A K) = (term532 A K).
Proof. exact (MK_COMB (@lem6781932 A K) (@lem6781931 A K)). Qed.
Lemma lem6781934 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6781935 {A K : Type'} : (term544 A K) = (term545 A K).
Proof. exact (MK_COMB (@lem6781934) (@lem6781933 A K)). Qed.
Lemma lem6781936 {A K : Type'} (_88876 : type835 A K) : (term537 A K _88876) = (term530 A K _88876).
Proof. exact (eq_refl (term537 A K _88876)). Qed.
Lemma lem6781937 {A K : Type'} (_88876 : type835 A K) : (term539 A K _88876) = (term539 A K _88876).
Proof. exact (eq_refl (term539 A K _88876)). Qed.
Lemma lem6781938 {A K : Type'} (_88876 : type835 A K) : (term546 A K _88876) = (term547 A K _88876).
Proof. exact (MK_COMB (@lem6781937 A K _88876) (@lem6781936 A K _88876)). Qed.
Lemma lem6781939 {A K : Type'} : (term548 A K) = (term549 A K).
Proof. exact (fun_ext (fun _88876 : type835 A K => @lem6781938 A K _88876)). Qed.
Lemma lem6781940 {A K : Type'} : (@all ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K -> Prop)) = (@all ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K -> Prop)).
Proof. exact (eq_refl (@all ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K -> Prop))). Qed.
Lemma lem6781941 {A K : Type'} : (term550 A K) = (term551 A K).
Proof. exact (MK_COMB (@lem6781940 A K) (@lem6781939 A K)). Qed.
Lemma lem6781942 {A K : Type'} : (term538 A K) = (term538 A K).
Proof. exact (eq_refl (term538 A K)). Qed.
Lemma lem6781943 {A K : Type'} : ((term497 A K) = (term550 A K)) = ((term497 A K) = (term551 A K)).
Proof. exact (MK_COMB (@lem6781942 A K) (@lem6781941 A K)). Qed.
Lemma lem6781944 {A K : Type'} : (term535 A K) = (term552 A K).
Proof. exact (MK_COMB (@lem6781935 A K) (@lem6781943 A K)). Qed.
Lemma lem6781945 {A K : Type'} : term552 A K.
Proof. exact (EQ_MP (@lem6781944 A K) (@lem6781925 A K)). Qed.
Lemma lem6781946 {A K : Type'} : (term497 A K) = (term551 A K).
Proof. exact (@lem6781945 A K (@lem6781921 A K)). Qed.
Lemma lem6781948 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term553 _3571 _3575 t)) = (term554 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem6781949 {A K : Type'} (s : type835 A K) (t : type835 A K) : (s = (term555 A K t)) = (term556 A K s t).
Proof. exact (@lem6781948 (type650 A K) (K -> Prop) s t). Qed.
Lemma lem6781950 {A K : Type'} (_88876 : type835 A K) : (_88876 = (term557 A K)) = (term558 A K _88876).
Proof. exact (@lem6781949 A K _88876 (term498 A K)). Qed.
Lemma lem6781951 {A K : Type'} (k : K -> Prop) : (term499 A K k) = (term500 A K k).
Proof. exact (eq_refl (term499 A K k)). Qed.
Lemma lem6781952 {A K : Type'} : (term557 A K) = (term498 A K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6781951 A K k)). Qed.
Lemma lem6781953 {A K : Type'} (_88876 : type835 A K) : (@eq ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K -> Prop) _88876) = (@eq ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K -> Prop) _88876).
Proof. exact (eq_refl (@eq ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K -> Prop) _88876)). Qed.
Lemma lem6781954 {A K : Type'} (_88876 : type835 A K) : (_88876 = (term557 A K)) = (_88876 = (term498 A K)).
Proof. exact (MK_COMB (@lem6781953 A K _88876) (@lem6781952 A K)). Qed.
Lemma lem6781955 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6781956 {A K : Type'} (_88876 : type835 A K) : (term559 A K _88876) = (term560 A K _88876).
Proof. exact (MK_COMB (@lem6781955) (@lem6781954 A K _88876)). Qed.
Lemma lem6781957 {A K : Type'} (k : K -> Prop) : (term499 A K k) = (term500 A K k).
Proof. exact (eq_refl (term499 A K k)). Qed.
Lemma lem6781958 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (term501 A K _88876 k) = (term501 A K _88876 k).
Proof. exact (eq_refl (term501 A K _88876 k)). Qed.
Lemma lem6781959 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : ((_88876 k) = (term499 A K k)) = ((_88876 k) = (term500 A K k)).
Proof. exact (MK_COMB (@lem6781958 A K _88876 k) (@lem6781957 A K k)). Qed.
Lemma lem6781960 {A K : Type'} (_88876 : type835 A K) : (term561 A K _88876) = (term562 A K _88876).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6781959 A K _88876 k)). Qed.
Lemma lem6781961 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6781962 {A K : Type'} (_88876 : type835 A K) : (term558 A K _88876) = (term563 A K _88876).
Proof. exact (MK_COMB (@lem6781961 K) (@lem6781960 A K _88876)). Qed.
Lemma lem6781963 {A K : Type'} (_88876 : type835 A K) : ((_88876 = (term557 A K)) = (term558 A K _88876)) = ((_88876 = (term498 A K)) = (term563 A K _88876)).
Proof. exact (MK_COMB (@lem6781956 A K _88876) (@lem6781962 A K _88876)). Qed.
Lemma lem6781964 {A K : Type'} (_88876 : type835 A K) : (_88876 = (term498 A K)) = (term563 A K _88876).
Proof. exact (EQ_MP (@lem6781963 A K _88876) (@lem6781950 A K _88876)). Qed.
Lemma lem6781966 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term553 _3571 _3575 t)) = (term554 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem6781967 {A K : Type'} (s : type650 A K) (t : type650 A K) : (s = (term564 A K t)) = (term565 A K s t).
Proof. exact (@lem6781966 (type793 A K) (A -> Prop) s t). Qed.
Lemma lem6781968 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : ((_88876 k) = (term566 A K k)) = (term567 A K _88876 k).
Proof. exact (@lem6781967 A K (_88876 k) (term500 A K k)). Qed.
Lemma lem6781969 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) : (term502 A K k dom) = (term503 A K k dom).
Proof. exact (eq_refl (term502 A K k dom)). Qed.
Lemma lem6781970 {A K : Type'} (k : K -> Prop) : (term566 A K k) = (term500 A K k).
Proof. exact (fun_ext (fun dom : A -> Prop => @lem6781969 A K k dom)). Qed.
Lemma lem6781971 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (term501 A K _88876 k) = (term501 A K _88876 k).
Proof. exact (eq_refl (term501 A K _88876 k)). Qed.
Lemma lem6781972 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : ((_88876 k) = (term566 A K k)) = ((_88876 k) = (term500 A K k)).
Proof. exact (MK_COMB (@lem6781971 A K _88876 k) (@lem6781970 A K k)). Qed.
Lemma lem6781973 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6781974 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (term568 A K _88876 k) = (term569 A K _88876 k).
Proof. exact (MK_COMB (@lem6781973) (@lem6781972 A K _88876 k)). Qed.
Lemma lem6781975 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) : (term502 A K k dom) = (term503 A K k dom).
Proof. exact (eq_refl (term502 A K k dom)). Qed.
Lemma lem6781976 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (term504 A K _88876 k dom) = (term504 A K _88876 k dom).
Proof. exact (eq_refl (term504 A K _88876 k dom)). Qed.
Lemma lem6781977 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : ((_88876 k dom) = (term502 A K k dom)) = ((_88876 k dom) = (term503 A K k dom)).
Proof. exact (MK_COMB (@lem6781976 A K _88876 k dom) (@lem6781975 A K k dom)). Qed.
Lemma lem6781978 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (term570 A K _88876 k) = (term571 A K _88876 k).
Proof. exact (fun_ext (fun dom : A -> Prop => @lem6781977 A K _88876 k dom)). Qed.
Lemma lem6781979 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6781980 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (term567 A K _88876 k) = (term572 A K _88876 k).
Proof. exact (MK_COMB (@lem6781979 A) (@lem6781978 A K _88876 k)). Qed.
Lemma lem6781981 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (((_88876 k) = (term566 A K k)) = (term567 A K _88876 k)) = (((_88876 k) = (term500 A K k)) = (term572 A K _88876 k)).
Proof. exact (MK_COMB (@lem6781974 A K _88876 k) (@lem6781980 A K _88876 k)). Qed.
Lemma lem6781982 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : ((_88876 k) = (term500 A K k)) = (term572 A K _88876 k).
Proof. exact (EQ_MP (@lem6781981 A K _88876 k) (@lem6781968 A K _88876 k)). Qed.
Lemma lem6781984 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term553 _3571 _3575 t)) = (term554 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem6781985 {A K : Type'} (s : type793 A K) (t : type793 A K) : (s = (term573 A K t)) = (term574 A K s t).
Proof. exact (@lem6781984 (type1413 A K) (K -> A) s t). Qed.
Lemma lem6781986 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : ((_88876 k dom) = (term575 A K k dom)) = (term576 A K _88876 k dom).
Proof. exact (@lem6781985 A K (_88876 k dom) (term503 A K k dom)). Qed.
Lemma lem6781987 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term505 A K k dom f) = (term506 A K k dom f).
Proof. exact (eq_refl (term505 A K k dom f)). Qed.
Lemma lem6781988 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) : (term575 A K k dom) = (term503 A K k dom).
Proof. exact (fun_ext (fun f : K -> A => @lem6781987 A K k dom f)). Qed.
Lemma lem6781989 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (term504 A K _88876 k dom) = (term504 A K _88876 k dom).
Proof. exact (eq_refl (term504 A K _88876 k dom)). Qed.
Lemma lem6781990 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : ((_88876 k dom) = (term575 A K k dom)) = ((_88876 k dom) = (term503 A K k dom)).
Proof. exact (MK_COMB (@lem6781989 A K _88876 k dom) (@lem6781988 A K k dom)). Qed.
Lemma lem6781991 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6781992 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (term577 A K _88876 k dom) = (term578 A K _88876 k dom).
Proof. exact (MK_COMB (@lem6781991) (@lem6781990 A K _88876 k dom)). Qed.
Lemma lem6781993 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term505 A K k dom f) = (term506 A K k dom f).
Proof. exact (eq_refl (term505 A K k dom f)). Qed.
Lemma lem6781994 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term507 A K _88876 k dom f) = (term507 A K _88876 k dom f).
Proof. exact (eq_refl (term507 A K _88876 k dom f)). Qed.
Lemma lem6781995 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : ((_88876 k dom f) = (term505 A K k dom f)) = ((_88876 k dom f) = (term506 A K k dom f)).
Proof. exact (MK_COMB (@lem6781994 A K _88876 k dom f) (@lem6781993 A K k dom f)). Qed.
Lemma lem6781996 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (term579 A K _88876 k dom) = (term580 A K _88876 k dom).
Proof. exact (fun_ext (fun f : K -> A => @lem6781995 A K _88876 k dom f)). Qed.
Lemma lem6781997 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem6781998 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (term576 A K _88876 k dom) = (term581 A K _88876 k dom).
Proof. exact (MK_COMB (@lem6781997 A K) (@lem6781996 A K _88876 k dom)). Qed.
Lemma lem6781999 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (((_88876 k dom) = (term575 A K k dom)) = (term576 A K _88876 k dom)) = (((_88876 k dom) = (term503 A K k dom)) = (term581 A K _88876 k dom)).
Proof. exact (MK_COMB (@lem6781992 A K _88876 k dom) (@lem6781998 A K _88876 k dom)). Qed.
Lemma lem6782000 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : ((_88876 k dom) = (term503 A K k dom)) = (term581 A K _88876 k dom).
Proof. exact (EQ_MP (@lem6781999 A K _88876 k dom) (@lem6781986 A K _88876 k dom)). Qed.
Lemma lem6782002 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term553 _3571 _3575 t)) = (term554 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem6782003 {A K : Type'} (s : type1413 A K) (t : type1413 A K) : (s = (term582 A K t)) = (term583 A K s t).
Proof. exact (@lem6782002 (K -> Prop) A s t). Qed.
Lemma lem6782004 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : ((_88876 k dom f) = (term584 A K k dom f)) = (term585 A K _88876 k dom f).
Proof. exact (@lem6782003 A K (_88876 k dom f) (term506 A K k dom f)). Qed.
Lemma lem6782005 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term508 A K k dom f neut) = (term361 A K k dom f neut).
Proof. exact (eq_refl (term508 A K k dom f neut)). Qed.
Lemma lem6782006 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term584 A K k dom f) = (term506 A K k dom f).
Proof. exact (fun_ext (fun neut : A => @lem6782005 A K k dom f neut)). Qed.
Lemma lem6782007 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term507 A K _88876 k dom f) = (term507 A K _88876 k dom f).
Proof. exact (eq_refl (term507 A K _88876 k dom f)). Qed.
Lemma lem6782008 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : ((_88876 k dom f) = (term584 A K k dom f)) = ((_88876 k dom f) = (term506 A K k dom f)).
Proof. exact (MK_COMB (@lem6782007 A K _88876 k dom f) (@lem6782006 A K k dom f)). Qed.
Lemma lem6782009 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6782010 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term586 A K _88876 k dom f) = (term587 A K _88876 k dom f).
Proof. exact (MK_COMB (@lem6782009) (@lem6782008 A K _88876 k dom f)). Qed.
Lemma lem6782011 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term508 A K k dom f neut) = (term361 A K k dom f neut).
Proof. exact (eq_refl (term508 A K k dom f neut)). Qed.
Lemma lem6782012 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term509 A K _88876 k dom f neut) = (term509 A K _88876 k dom f neut).
Proof. exact (eq_refl (term509 A K _88876 k dom f neut)). Qed.
Lemma lem6782013 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : ((_88876 k dom f neut) = (term508 A K k dom f neut)) = ((_88876 k dom f neut) = (term361 A K k dom f neut)).
Proof. exact (MK_COMB (@lem6782012 A K _88876 k dom f neut) (@lem6782011 A K k dom f neut)). Qed.
Lemma lem6782014 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term588 A K _88876 k dom f) = (term589 A K _88876 k dom f).
Proof. exact (fun_ext (fun neut : A => @lem6782013 A K _88876 k dom f neut)). Qed.
Lemma lem6782015 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6782016 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term585 A K _88876 k dom f) = (term590 A K _88876 k dom f).
Proof. exact (MK_COMB (@lem6782015 A) (@lem6782014 A K _88876 k dom f)). Qed.
Lemma lem6782017 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (((_88876 k dom f) = (term584 A K k dom f)) = (term585 A K _88876 k dom f)) = (((_88876 k dom f) = (term506 A K k dom f)) = (term590 A K _88876 k dom f)).
Proof. exact (MK_COMB (@lem6782010 A K _88876 k dom f) (@lem6782016 A K _88876 k dom f)). Qed.
Lemma lem6782018 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : ((_88876 k dom f) = (term506 A K k dom f)) = (term590 A K _88876 k dom f).
Proof. exact (EQ_MP (@lem6782017 A K _88876 k dom f) (@lem6782004 A K _88876 k dom f)). Qed.
Lemma lem6782020 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term553 _3571 _3575 t)) = (term554 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem6782021 {K : Type'} (s : K -> Prop) (t : K -> Prop) : (s = (term21 K t)) = (term591 K s t).
Proof. exact (@lem6782020 Prop K s t). Qed.
Lemma lem6782022 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : ((_88876 k dom f neut) = (term592 A K k dom f neut)) = (term593 A K _88876 k dom f neut).
Proof. exact (@lem6782021 K (_88876 k dom f neut) (term361 A K k dom f neut)). Qed.
Lemma lem6782023 {A K : Type'} (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term594 A K k dom f neut GEN_PVAR_274) = (term360 A K GEN_PVAR_274 k dom f neut).
Proof. exact (eq_refl (term594 A K k dom f neut GEN_PVAR_274)). Qed.
Lemma lem6782024 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term592 A K k dom f neut) = (term361 A K k dom f neut).
Proof. exact (fun_ext (fun GEN_PVAR_274 : K => @lem6782023 A K GEN_PVAR_274 k dom f neut)). Qed.
Lemma lem6782025 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term509 A K _88876 k dom f neut) = (term509 A K _88876 k dom f neut).
Proof. exact (eq_refl (term509 A K _88876 k dom f neut)). Qed.
Lemma lem6782026 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : ((_88876 k dom f neut) = (term592 A K k dom f neut)) = ((_88876 k dom f neut) = (term361 A K k dom f neut)).
Proof. exact (MK_COMB (@lem6782025 A K _88876 k dom f neut) (@lem6782024 A K k dom f neut)). Qed.
Lemma lem6782027 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6782028 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term595 A K _88876 k dom f neut) = (term596 A K _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6782027) (@lem6782026 A K _88876 k dom f neut)). Qed.
Lemma lem6782029 {A K : Type'} (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term594 A K k dom f neut GEN_PVAR_274) = (term360 A K GEN_PVAR_274 k dom f neut).
Proof. exact (eq_refl (term594 A K k dom f neut GEN_PVAR_274)). Qed.
Lemma lem6782030 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (GEN_PVAR_274 : K) : (term597 A K _88876 k dom f neut GEN_PVAR_274) = (term597 A K _88876 k dom f neut GEN_PVAR_274).
Proof. exact (eq_refl (term597 A K _88876 k dom f neut GEN_PVAR_274)). Qed.
Lemma lem6782031 {A K : Type'} (_88876 : type835 A K) (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : ((_88876 k dom f neut GEN_PVAR_274) = (term594 A K k dom f neut GEN_PVAR_274)) = ((_88876 k dom f neut GEN_PVAR_274) = (term360 A K GEN_PVAR_274 k dom f neut)).
Proof. exact (MK_COMB (@lem6782030 A K _88876 k dom f neut GEN_PVAR_274) (@lem6782029 A K GEN_PVAR_274 k dom f neut)). Qed.
Lemma lem6782032 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term598 A K _88876 k dom f neut) = (term599 A K _88876 k dom f neut).
Proof. exact (fun_ext (fun GEN_PVAR_274 : K => @lem6782031 A K _88876 GEN_PVAR_274 k dom f neut)). Qed.
Lemma lem6782033 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6782034 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term593 A K _88876 k dom f neut) = (term600 A K _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6782033 K) (@lem6782032 A K _88876 k dom f neut)). Qed.
Lemma lem6782035 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (((_88876 k dom f neut) = (term592 A K k dom f neut)) = (term593 A K _88876 k dom f neut)) = (((_88876 k dom f neut) = (term361 A K k dom f neut)) = (term600 A K _88876 k dom f neut)).
Proof. exact (MK_COMB (@lem6782028 A K _88876 k dom f neut) (@lem6782034 A K _88876 k dom f neut)). Qed.
Lemma lem6782036 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : ((_88876 k dom f neut) = (term361 A K k dom f neut)) = (term600 A K _88876 k dom f neut).
Proof. exact (EQ_MP (@lem6782035 A K _88876 k dom f neut) (@lem6782022 A K _88876 k dom f neut)). Qed.
Lemma lem6782037 {A K : Type'} (_88876 : type835 A K) (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : ((_88876 k dom f neut GEN_PVAR_274) = (term360 A K GEN_PVAR_274 k dom f neut)) = ((_88876 k dom f neut GEN_PVAR_274) = (term360 A K GEN_PVAR_274 k dom f neut)).
Proof. exact (eq_refl ((_88876 k dom f neut GEN_PVAR_274) = (term360 A K GEN_PVAR_274 k dom f neut))). Qed.
Lemma lem6782038 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term599 A K _88876 k dom f neut) = (term599 A K _88876 k dom f neut).
Proof. exact (fun_ext (fun GEN_PVAR_274 : K => @lem6782037 A K _88876 GEN_PVAR_274 k dom f neut)). Qed.
Lemma lem6782039 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6782040 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term600 A K _88876 k dom f neut) = (term600 A K _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6782039 K) (@lem6782038 A K _88876 k dom f neut)). Qed.
Lemma lem6782041 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : ((_88876 k dom f neut) = (term361 A K k dom f neut)) = (term600 A K _88876 k dom f neut).
Proof. exact (TRANS (@lem6782036 A K _88876 k dom f neut) (@lem6782040 A K _88876 k dom f neut)). Qed.
Lemma lem6782042 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term589 A K _88876 k dom f) = (term601 A K _88876 k dom f).
Proof. exact (fun_ext (fun neut : A => @lem6782041 A K _88876 k dom f neut)). Qed.
Lemma lem6782043 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6782044 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term590 A K _88876 k dom f) = (term602 A K _88876 k dom f).
Proof. exact (MK_COMB (@lem6782043 A) (@lem6782042 A K _88876 k dom f)). Qed.
Lemma lem6782045 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : ((_88876 k dom f) = (term506 A K k dom f)) = (term602 A K _88876 k dom f).
Proof. exact (TRANS (@lem6782018 A K _88876 k dom f) (@lem6782044 A K _88876 k dom f)). Qed.
Lemma lem6782046 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (term580 A K _88876 k dom) = (term603 A K _88876 k dom).
Proof. exact (fun_ext (fun f : K -> A => @lem6782045 A K _88876 k dom f)). Qed.
Lemma lem6782047 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem6782048 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (term581 A K _88876 k dom) = (term604 A K _88876 k dom).
Proof. exact (MK_COMB (@lem6782047 A K) (@lem6782046 A K _88876 k dom)). Qed.
Lemma lem6782049 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : ((_88876 k dom) = (term503 A K k dom)) = (term604 A K _88876 k dom).
Proof. exact (TRANS (@lem6782000 A K _88876 k dom) (@lem6782048 A K _88876 k dom)). Qed.
Lemma lem6782050 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (term571 A K _88876 k) = (term605 A K _88876 k).
Proof. exact (fun_ext (fun dom : A -> Prop => @lem6782049 A K _88876 k dom)). Qed.
Lemma lem6782051 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6782052 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (term572 A K _88876 k) = (term606 A K _88876 k).
Proof. exact (MK_COMB (@lem6782051 A) (@lem6782050 A K _88876 k)). Qed.
Lemma lem6782053 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : ((_88876 k) = (term500 A K k)) = (term606 A K _88876 k).
Proof. exact (TRANS (@lem6781982 A K _88876 k) (@lem6782052 A K _88876 k)). Qed.
Lemma lem6782054 {A K : Type'} (_88876 : type835 A K) : (term562 A K _88876) = (term607 A K _88876).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6782053 A K _88876 k)). Qed.
Lemma lem6782055 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6782056 {A K : Type'} (_88876 : type835 A K) : (term563 A K _88876) = (term608 A K _88876).
Proof. exact (MK_COMB (@lem6782055 K) (@lem6782054 A K _88876)). Qed.
Lemma lem6782057 {A K : Type'} (_88876 : type835 A K) : (_88876 = (term498 A K)) = (term608 A K _88876).
Proof. exact (TRANS (@lem6781964 A K _88876) (@lem6782056 A K _88876)). Qed.
Lemma lem6782058 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6782059 {A K : Type'} (_88876 : type835 A K) : (term539 A K _88876) = (term609 A K _88876).
Proof. exact (MK_COMB (@lem6782058) (@lem6782057 A K _88876)). Qed.
Lemma lem6782060 {A K : Type'} (_88876 : type835 A K) : (term530 A K _88876) = (term530 A K _88876).
Proof. exact (eq_refl (term530 A K _88876)). Qed.
Lemma lem6782061 {A K : Type'} (_88876 : type835 A K) : (term547 A K _88876) = (term610 A K _88876).
Proof. exact (MK_COMB (@lem6782059 A K _88876) (@lem6782060 A K _88876)). Qed.
Lemma lem6782062 {A K : Type'} : (term549 A K) = (term611 A K).
Proof. exact (fun_ext (fun _88876 : type835 A K => @lem6782061 A K _88876)). Qed.
Lemma lem6782063 {A K : Type'} : (@all ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K -> Prop)) = (@all ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K -> Prop)).
Proof. exact (eq_refl (@all ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K -> Prop))). Qed.
Lemma lem6782064 {A K : Type'} : (term551 A K) = (term612 A K).
Proof. exact (MK_COMB (@lem6782063 A K) (@lem6782062 A K)). Qed.
Lemma lem6782065 {A K : Type'} : (term538 A K) = (term538 A K).
Proof. exact (eq_refl (term538 A K)). Qed.
Lemma lem6782066 {A K : Type'} : ((term497 A K) = (term551 A K)) = ((term497 A K) = (term612 A K)).
Proof. exact (MK_COMB (@lem6782065 A K) (@lem6782064 A K)). Qed.
Lemma lem6782069 {A K : Type'} : (term497 A K) = (term612 A K).
Proof. exact (EQ_MP (@lem6782066 A K) (@lem6781946 A K)). Qed.
Lemma lem6782070 {A K : Type'} : (term496 A K) = (term612 A K).
Proof. exact (TRANS (@lem6781623 A K) (@lem6782069 A K)). Qed.
Lemma lem6782085 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term450 A K _88875 k dom f i neut) = (term450 A K _88875 k dom f i neut).
Proof. exact (eq_refl (term450 A K _88875 k dom f i neut)). Qed.
Lemma lem6782086 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term511 A K _88876 k dom f neut) = (term511 A K _88876 k dom f neut).
Proof. exact (eq_refl (term511 A K _88876 k dom f neut)). Qed.
Lemma lem6782099 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (x : K) (neut : A) : (term351 A K k dom f x neut) = (term351 A K k dom f x neut).
Proof. exact (eq_refl (term351 A K k dom f x neut)). Qed.
Lemma lem6782100 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term353 A K k dom f neut) = (term353 A K k dom f neut).
Proof. exact (fun_ext (fun x : K => @lem6782099 A K k dom f x neut)). Qed.
Lemma lem6782101 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6782102 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term354 A K k dom f neut) = (term354 A K k dom f neut).
Proof. exact (MK_COMB (@lem6782101 K) (@lem6782100 A K k dom f neut)). Qed.
Lemma lem6782103 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6782104 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term355 A K k dom f neut) = (term355 A K k dom f neut).
Proof. exact (MK_COMB (@lem6782103) (@lem6782102 A K k dom f neut)). Qed.
Lemma lem6782105 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6782106 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term356 A K k dom f neut) = (term356 A K k dom f neut).
Proof. exact (MK_COMB (@lem6782105) (@lem6782104 A K k dom f neut)). Qed.
Lemma lem6782107 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term512 A K _88876 k dom f neut) = (term512 A K _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6782106 A K k dom f neut) (@lem6782086 A K _88876 k dom f neut)). Qed.
Lemma lem6782126 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i' : K) (i : K) : (term318 A K ltle k dom f neut i' i) = (term318 A K ltle k dom f neut i' i).
Proof. exact (eq_refl (term318 A K ltle k dom f neut i' i)). Qed.
Lemma lem6782127 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term320 A K ltle k dom f neut i) = (term320 A K ltle k dom f neut i).
Proof. exact (fun_ext (fun i' : K => @lem6782126 A K ltle k dom f neut i' i)). Qed.
Lemma lem6782128 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6782129 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term322 A K ltle k dom f neut i) = (term322 A K ltle k dom f neut i).
Proof. exact (MK_COMB (@lem6782128 K) (@lem6782127 A K ltle k dom f neut i)). Qed.
Lemma lem6782138 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term311 A K dom f i neut) = (term311 A K dom f i neut).
Proof. exact (eq_refl (term311 A K dom f i neut)). Qed.
Lemma lem6782139 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term324 A K ltle k dom f neut i) = (term324 A K ltle k dom f neut i).
Proof. exact (MK_COMB (@lem6782138 A K dom f i neut) (@lem6782129 A K ltle k dom f neut i)). Qed.
Lemma lem6782142 {K : Type'} (k : K -> Prop) (i : K) : (term293 K k i) = (term293 K k i).
Proof. exact (eq_refl (term293 K k i)). Qed.
Lemma lem6782143 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term326 A K ltle k dom f neut i) = (term326 A K ltle k dom f neut i).
Proof. exact (MK_COMB (@lem6782142 K k i) (@lem6782139 A K ltle k dom f neut i)). Qed.
Lemma lem6782144 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term328 A K ltle k dom f neut) = (term328 A K ltle k dom f neut).
Proof. exact (fun_ext (fun i : K => @lem6782143 A K ltle k dom f neut i)). Qed.
Lemma lem6782145 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem6782146 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term329 A K ltle k dom f neut) = (term329 A K ltle k dom f neut).
Proof. exact (MK_COMB (@lem6782145 K) (@lem6782144 A K ltle k dom f neut)). Qed.
Lemma lem6782147 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6782148 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term330 A K ltle k dom f neut) = (term330 A K ltle k dom f neut).
Proof. exact (MK_COMB (@lem6782147) (@lem6782146 A K ltle k dom f neut)). Qed.
Lemma lem6782149 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6782150 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term331 A K ltle k dom f neut) = (term331 A K ltle k dom f neut).
Proof. exact (MK_COMB (@lem6782149) (@lem6782148 A K ltle k dom f neut)). Qed.
Lemma lem6782151 {A K : Type'} (ltle : type1402 K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term513 A K ltle _88876 k dom f neut) = (term513 A K ltle _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6782150 A K ltle k dom f neut) (@lem6782107 A K _88876 k dom f neut)). Qed.
Lemma lem6782152 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6782153 {A K : Type'} (ltle : type1402 K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term514 A K ltle _88876 k dom f neut) = (term514 A K ltle _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6782152) (@lem6782151 A K ltle _88876 k dom f neut)). Qed.
Lemma lem6782154 {A K : Type'} (ltle : type1402 K) (_88876 : type835 A K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term515 A K ltle _88876 _88875 k dom f i neut) = (term515 A K ltle _88876 _88875 k dom f i neut).
Proof. exact (MK_COMB (@lem6782153 A K ltle _88876 k dom f neut) (@lem6782085 A K _88875 k dom f i neut)). Qed.
Lemma lem6782179 {A K : Type'} (x : K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term432 A K x _88875 k dom f neut) = (term432 A K x _88875 k dom f neut).
Proof. exact (eq_refl (term432 A K x _88875 k dom f neut)). Qed.
Lemma lem6782180 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term433 A K _88875 k dom f neut) = (term433 A K _88875 k dom f neut).
Proof. exact (fun_ext (fun x : K => @lem6782179 A K x _88875 k dom f neut)). Qed.
Lemma lem6782181 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6782182 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term434 A K _88875 k dom f neut) = (term434 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6782181 K) (@lem6782180 A K _88875 k dom f neut)). Qed.
Lemma lem6782183 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term436 A K _88875 k dom f) = (term436 A K _88875 k dom f).
Proof. exact (fun_ext (fun neut : A => @lem6782182 A K _88875 k dom f neut)). Qed.
Lemma lem6782184 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6782185 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term437 A K _88875 k dom f) = (term437 A K _88875 k dom f).
Proof. exact (MK_COMB (@lem6782184 A) (@lem6782183 A K _88875 k dom f)). Qed.
Lemma lem6782186 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) : (term439 A K _88875 k dom) = (term439 A K _88875 k dom).
Proof. exact (fun_ext (fun f : K -> A => @lem6782185 A K _88875 k dom f)). Qed.
Lemma lem6782187 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem6782188 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) : (term440 A K _88875 k dom) = (term440 A K _88875 k dom).
Proof. exact (MK_COMB (@lem6782187 A K) (@lem6782186 A K _88875 k dom)). Qed.
Lemma lem6782189 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) : (term442 A K _88875 k) = (term442 A K _88875 k).
Proof. exact (fun_ext (fun dom : A -> Prop => @lem6782188 A K _88875 k dom)). Qed.
Lemma lem6782190 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6782191 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) : (term443 A K _88875 k) = (term443 A K _88875 k).
Proof. exact (MK_COMB (@lem6782190 A) (@lem6782189 A K _88875 k)). Qed.
Lemma lem6782192 {A K : Type'} (_88875 : type836 A K) : (term445 A K _88875) = (term445 A K _88875).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6782191 A K _88875 k)). Qed.
Lemma lem6782193 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6782194 {A K : Type'} (_88875 : type836 A K) : (term446 A K _88875) = (term446 A K _88875).
Proof. exact (MK_COMB (@lem6782193 K) (@lem6782192 A K _88875)). Qed.
Lemma lem6782195 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6782196 {A K : Type'} (_88875 : type836 A K) : (term448 A K _88875) = (term448 A K _88875).
Proof. exact (MK_COMB (@lem6782195) (@lem6782194 A K _88875)). Qed.
Lemma lem6782197 {A K : Type'} (ltle : type1402 K) (_88876 : type835 A K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term516 A K ltle _88876 _88875 k dom f i neut) = (term516 A K ltle _88876 _88875 k dom f i neut).
Proof. exact (MK_COMB (@lem6782196 A K _88875) (@lem6782154 A K ltle _88876 _88875 k dom f i neut)). Qed.
Lemma lem6782198 {A K : Type'} (ltle : type1402 K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term517 A K ltle _88876 k dom f i neut) = (term517 A K ltle _88876 k dom f i neut).
Proof. exact (fun_ext (fun _88875 : type836 A K => @lem6782197 A K ltle _88876 _88875 k dom f i neut)). Qed.
Lemma lem6782199 {A K : Type'} : (@all ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K)) = (@all ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K)).
Proof. exact (eq_refl (@all ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K))). Qed.
Lemma lem6782200 {A K : Type'} (ltle : type1402 K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term518 A K ltle _88876 k dom f i neut) = (term518 A K ltle _88876 k dom f i neut).
Proof. exact (MK_COMB (@lem6782199 A K) (@lem6782198 A K ltle _88876 k dom f i neut)). Qed.
Lemma lem6782201 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term519 A K _88876 k dom f i neut) = (term519 A K _88876 k dom f i neut).
Proof. exact (fun_ext (fun ltle : type1402 K => @lem6782200 A K ltle _88876 k dom f i neut)). Qed.
Lemma lem6782202 {K : Type'} : (@all (K -> K -> Prop)) = (@all (K -> K -> Prop)).
Proof. exact (eq_refl (@all (K -> K -> Prop))). Qed.
Lemma lem6782203 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term520 A K _88876 k dom f i neut) = (term520 A K _88876 k dom f i neut).
Proof. exact (MK_COMB (@lem6782202 K) (@lem6782201 A K _88876 k dom f i neut)). Qed.
Lemma lem6782204 {A K : Type'} (_88876 : type835 A K) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term521 A K _88876 dom f i neut) = (term521 A K _88876 dom f i neut).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6782203 A K _88876 k dom f i neut)). Qed.
Lemma lem6782205 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6782206 {A K : Type'} (_88876 : type835 A K) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term522 A K _88876 dom f i neut) = (term522 A K _88876 dom f i neut).
Proof. exact (MK_COMB (@lem6782205 K) (@lem6782204 A K _88876 dom f i neut)). Qed.
Lemma lem6782207 {A K : Type'} (_88876 : type835 A K) (f : K -> A) (i : K) (neut : A) : (term523 A K _88876 f i neut) = (term523 A K _88876 f i neut).
Proof. exact (fun_ext (fun dom : A -> Prop => @lem6782206 A K _88876 dom f i neut)). Qed.
Lemma lem6782208 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6782209 {A K : Type'} (_88876 : type835 A K) (f : K -> A) (i : K) (neut : A) : (term524 A K _88876 f i neut) = (term524 A K _88876 f i neut).
Proof. exact (MK_COMB (@lem6782208 A) (@lem6782207 A K _88876 f i neut)). Qed.
Lemma lem6782210 {A K : Type'} (_88876 : type835 A K) (i : K) (neut : A) : (term525 A K _88876 i neut) = (term525 A K _88876 i neut).
Proof. exact (fun_ext (fun f : K -> A => @lem6782209 A K _88876 f i neut)). Qed.
Lemma lem6782211 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem6782212 {A K : Type'} (_88876 : type835 A K) (i : K) (neut : A) : (term526 A K _88876 i neut) = (term526 A K _88876 i neut).
Proof. exact (MK_COMB (@lem6782211 A K) (@lem6782210 A K _88876 i neut)). Qed.
Lemma lem6782213 {A K : Type'} (_88876 : type835 A K) (neut : A) : (term527 A K _88876 neut) = (term527 A K _88876 neut).
Proof. exact (fun_ext (fun i : K => @lem6782212 A K _88876 i neut)). Qed.
Lemma lem6782214 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6782215 {A K : Type'} (_88876 : type835 A K) (neut : A) : (term528 A K _88876 neut) = (term528 A K _88876 neut).
Proof. exact (MK_COMB (@lem6782214 K) (@lem6782213 A K _88876 neut)). Qed.
Lemma lem6782216 {A K : Type'} (_88876 : type835 A K) : (term529 A K _88876) = (term529 A K _88876).
Proof. exact (fun_ext (fun neut : A => @lem6782215 A K _88876 neut)). Qed.
Lemma lem6782217 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6782218 {A K : Type'} (_88876 : type835 A K) : (term530 A K _88876) = (term530 A K _88876).
Proof. exact (MK_COMB (@lem6782217 A) (@lem6782216 A K _88876)). Qed.
Lemma lem6782219 {A K : Type'} (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term358 A K GEN_PVAR_274 k dom f neut i) = (term358 A K GEN_PVAR_274 k dom f neut i).
Proof. exact (eq_refl (term358 A K GEN_PVAR_274 k dom f neut i)). Qed.
Lemma lem6782220 {A K : Type'} (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term359 A K GEN_PVAR_274 k dom f neut) = (term359 A K GEN_PVAR_274 k dom f neut).
Proof. exact (fun_ext (fun i : K => @lem6782219 A K GEN_PVAR_274 k dom f neut i)). Qed.
Lemma lem6782221 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem6782222 {A K : Type'} (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term360 A K GEN_PVAR_274 k dom f neut) = (term360 A K GEN_PVAR_274 k dom f neut).
Proof. exact (MK_COMB (@lem6782221 K) (@lem6782220 A K GEN_PVAR_274 k dom f neut)). Qed.
Lemma lem6782225 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (GEN_PVAR_274 : K) : (term597 A K _88876 k dom f neut GEN_PVAR_274) = (term597 A K _88876 k dom f neut GEN_PVAR_274).
Proof. exact (eq_refl (term597 A K _88876 k dom f neut GEN_PVAR_274)). Qed.
Lemma lem6782226 {A K : Type'} (_88876 : type835 A K) (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : ((_88876 k dom f neut GEN_PVAR_274) = (term360 A K GEN_PVAR_274 k dom f neut)) = ((_88876 k dom f neut GEN_PVAR_274) = (term360 A K GEN_PVAR_274 k dom f neut)).
Proof. exact (MK_COMB (@lem6782225 A K _88876 k dom f neut GEN_PVAR_274) (@lem6782222 A K GEN_PVAR_274 k dom f neut)). Qed.
Lemma lem6782227 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term599 A K _88876 k dom f neut) = (term599 A K _88876 k dom f neut).
Proof. exact (fun_ext (fun GEN_PVAR_274 : K => @lem6782226 A K _88876 GEN_PVAR_274 k dom f neut)). Qed.
Lemma lem6782228 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6782229 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term600 A K _88876 k dom f neut) = (term600 A K _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6782228 K) (@lem6782227 A K _88876 k dom f neut)). Qed.
Lemma lem6782230 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term601 A K _88876 k dom f) = (term601 A K _88876 k dom f).
Proof. exact (fun_ext (fun neut : A => @lem6782229 A K _88876 k dom f neut)). Qed.
Lemma lem6782231 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6782232 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term602 A K _88876 k dom f) = (term602 A K _88876 k dom f).
Proof. exact (MK_COMB (@lem6782231 A) (@lem6782230 A K _88876 k dom f)). Qed.
Lemma lem6782233 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (term603 A K _88876 k dom) = (term603 A K _88876 k dom).
Proof. exact (fun_ext (fun f : K -> A => @lem6782232 A K _88876 k dom f)). Qed.
Lemma lem6782234 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem6782235 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (term604 A K _88876 k dom) = (term604 A K _88876 k dom).
Proof. exact (MK_COMB (@lem6782234 A K) (@lem6782233 A K _88876 k dom)). Qed.
Lemma lem6782236 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (term605 A K _88876 k) = (term605 A K _88876 k).
Proof. exact (fun_ext (fun dom : A -> Prop => @lem6782235 A K _88876 k dom)). Qed.
Lemma lem6782237 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6782238 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (term606 A K _88876 k) = (term606 A K _88876 k).
Proof. exact (MK_COMB (@lem6782237 A) (@lem6782236 A K _88876 k)). Qed.
Lemma lem6782239 {A K : Type'} (_88876 : type835 A K) : (term607 A K _88876) = (term607 A K _88876).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6782238 A K _88876 k)). Qed.
Lemma lem6782240 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6782241 {A K : Type'} (_88876 : type835 A K) : (term608 A K _88876) = (term608 A K _88876).
Proof. exact (MK_COMB (@lem6782240 K) (@lem6782239 A K _88876)). Qed.
Lemma lem6782242 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6782243 {A K : Type'} (_88876 : type835 A K) : (term609 A K _88876) = (term609 A K _88876).
Proof. exact (MK_COMB (@lem6782242) (@lem6782241 A K _88876)). Qed.
Lemma lem6782244 {A K : Type'} (_88876 : type835 A K) : (term610 A K _88876) = (term610 A K _88876).
Proof. exact (MK_COMB (@lem6782243 A K _88876) (@lem6782218 A K _88876)). Qed.
Lemma lem6782245 {A K : Type'} : (term611 A K) = (term611 A K).
Proof. exact (fun_ext (fun _88876 : type835 A K => @lem6782244 A K _88876)). Qed.
Lemma lem6782246 {A K : Type'} : (@all ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K -> Prop)) = (@all ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K -> Prop)).
Proof. exact (eq_refl (@all ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K -> Prop))). Qed.
Lemma lem6782247 {A K : Type'} : (term612 A K) = (term612 A K).
Proof. exact (MK_COMB (@lem6782246 A K) (@lem6782245 A K)). Qed.
Lemma lem6782430 {A K : Type'} : (term496 A K) = (term612 A K).
Proof. exact (TRANS (@lem6782070 A K) (@lem6782247 A K)). Qed.
Lemma lem6782431 {A K : Type'} : (term612 A K) = (term496 A K).
Proof. exact (SYM (@lem6782430 A K)). Qed.
Lemma lem6782432 {A K : Type'} (_88876 : type835 A K) (h1 : term608 A K _88876) : term608 A K _88876.
Proof. exact (h1). Qed.
Lemma lem6782433 {A K : Type'} (_88875 : type836 A K) (h1 : term446 A K _88875) : term446 A K _88875.
Proof. exact (h1). Qed.
Lemma lem6782434 {A K : Type'} (ltle : type1402 K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (h1 : term513 A K ltle _88876 k dom f neut) : term513 A K ltle _88876 k dom f neut.
Proof. exact (h1). Qed.
Lemma lem6782437 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6782438 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term312 A K k dom f i neut) = (term613 A K k dom f i neut).
Proof. exact (@lem6782437 (term312 A K k dom f i neut)). Qed.
Lemma lem6782439 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term613 A K k dom f i neut) = (term312 A K k dom f i neut).
Proof. exact (SYM (@lem6782438 A K k dom f i neut)). Qed.
Lemma lem6782440 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (h1 : term351 A K k dom f i neut) : term351 A K k dom f i neut.
Proof. exact (h1). Qed.
Lemma lem6782444 {A K : Type'} (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term358 A K GEN_PVAR_274 k dom f neut i) = (term358 A K GEN_PVAR_274 k dom f neut i).
Proof. exact (eq_refl (term358 A K GEN_PVAR_274 k dom f neut i)). Qed.
Lemma lem6782445 {K : Type'} (P : K -> Prop) : (term30 K P) = (term31 K P).
Proof. exact (@lem18394 K P). Qed.
Lemma lem6782446 {A K : Type'} (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term614 A K GEN_PVAR_274 k dom f neut) = (term615 A K GEN_PVAR_274 k dom f neut).
Proof. exact (@lem6782445 K (term359 A K GEN_PVAR_274 k dom f neut)). Qed.
Lemma lem6782447 {A K : Type'} (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term616 A K GEN_PVAR_274 k dom f neut i) = (term358 A K GEN_PVAR_274 k dom f neut i).
Proof. exact (eq_refl (term616 A K GEN_PVAR_274 k dom f neut i)). Qed.
Lemma lem6782448 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6782450 {A K : Type'} (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term617 A K GEN_PVAR_274 k dom f neut i) = (term618 A K GEN_PVAR_274 k dom f neut i).
Proof. exact (MK_COMB (@lem6782448) (@lem6782447 A K GEN_PVAR_274 k dom f neut i)). Qed.
Lemma lem6782451 {A K : Type'} (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term619 A K GEN_PVAR_274 k dom f neut) = (term620 A K GEN_PVAR_274 k dom f neut).
Proof. exact (fun_ext (fun i : K => @lem6782450 A K GEN_PVAR_274 k dom f neut i)). Qed.
Lemma lem6782452 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6782453 {A K : Type'} (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term615 A K GEN_PVAR_274 k dom f neut) = (term621 A K GEN_PVAR_274 k dom f neut).
Proof. exact (MK_COMB (@lem6782452 K) (@lem6782451 A K GEN_PVAR_274 k dom f neut)). Qed.
Lemma lem6782454 {A K : Type'} (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term614 A K GEN_PVAR_274 k dom f neut) = (term621 A K GEN_PVAR_274 k dom f neut).
Proof. exact (TRANS (@lem6782446 A K GEN_PVAR_274 k dom f neut) (@lem6782453 A K GEN_PVAR_274 k dom f neut)). Qed.
Lemma lem6782455 {A K : Type'} (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term359 A K GEN_PVAR_274 k dom f neut) = (term359 A K GEN_PVAR_274 k dom f neut).
Proof. exact (fun_ext (fun i : K => @lem6782444 A K GEN_PVAR_274 k dom f neut i)). Qed.
Lemma lem6782456 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem6782457 {A K : Type'} (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term360 A K GEN_PVAR_274 k dom f neut) = (term360 A K GEN_PVAR_274 k dom f neut).
Proof. exact (MK_COMB (@lem6782456 K) (@lem6782455 A K GEN_PVAR_274 k dom f neut)). Qed.
Lemma lem6782459 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (GEN_PVAR_274 : K) : (term622 A K _88876 k dom f neut GEN_PVAR_274) = (term622 A K _88876 k dom f neut GEN_PVAR_274).
Proof. exact (eq_refl (term622 A K _88876 k dom f neut GEN_PVAR_274)). Qed.
Lemma lem6782460 {A K : Type'} (_88876 : type835 A K) (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term623 A K _88876 GEN_PVAR_274 k dom f neut) = (term623 A K _88876 GEN_PVAR_274 k dom f neut).
Proof. exact (MK_COMB (@lem6782459 A K _88876 k dom f neut GEN_PVAR_274) (@lem6782457 A K GEN_PVAR_274 k dom f neut)). Qed.
Lemma lem6782462 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (GEN_PVAR_274 : K) : (term624 A K _88876 k dom f neut GEN_PVAR_274) = (term624 A K _88876 k dom f neut GEN_PVAR_274).
Proof. exact (eq_refl (term624 A K _88876 k dom f neut GEN_PVAR_274)). Qed.
Lemma lem6782463 {A K : Type'} (_88876 : type835 A K) (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term625 A K _88876 GEN_PVAR_274 k dom f neut) = (term626 A K _88876 GEN_PVAR_274 k dom f neut).
Proof. exact (MK_COMB (@lem6782462 A K _88876 k dom f neut GEN_PVAR_274) (@lem6782454 A K GEN_PVAR_274 k dom f neut)). Qed.
Lemma lem6782464 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6782465 {A K : Type'} (_88876 : type835 A K) (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term627 A K _88876 GEN_PVAR_274 k dom f neut) = (term628 A K _88876 GEN_PVAR_274 k dom f neut).
Proof. exact (MK_COMB (@lem6782464) (@lem6782463 A K _88876 GEN_PVAR_274 k dom f neut)). Qed.
Lemma lem6782466 {A K : Type'} (_88876 : type835 A K) (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term629 A K _88876 GEN_PVAR_274 k dom f neut) = (term630 A K _88876 GEN_PVAR_274 k dom f neut).
Proof. exact (MK_COMB (@lem6782465 A K _88876 GEN_PVAR_274 k dom f neut) (@lem6782460 A K _88876 GEN_PVAR_274 k dom f neut)). Qed.
Lemma lem6782467 {A K : Type'} (_88876 : type835 A K) (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : ((_88876 k dom f neut GEN_PVAR_274) = (term360 A K GEN_PVAR_274 k dom f neut)) = (term629 A K _88876 GEN_PVAR_274 k dom f neut).
Proof. exact (@lem17784 (_88876 k dom f neut GEN_PVAR_274) (term360 A K GEN_PVAR_274 k dom f neut)). Qed.
Lemma lem6782468 {A K : Type'} (_88876 : type835 A K) (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : ((_88876 k dom f neut GEN_PVAR_274) = (term360 A K GEN_PVAR_274 k dom f neut)) = (term630 A K _88876 GEN_PVAR_274 k dom f neut).
Proof. exact (TRANS (@lem6782467 A K _88876 GEN_PVAR_274 k dom f neut) (@lem6782466 A K _88876 GEN_PVAR_274 k dom f neut)). Qed.
Lemma lem6782469 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term599 A K _88876 k dom f neut) = (term631 A K _88876 k dom f neut).
Proof. exact (fun_ext (fun GEN_PVAR_274 : K => @lem6782468 A K _88876 GEN_PVAR_274 k dom f neut)). Qed.
Lemma lem6782470 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6782471 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term600 A K _88876 k dom f neut) = (term632 A K _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6782470 K) (@lem6782469 A K _88876 k dom f neut)). Qed.
Lemma lem6782472 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term601 A K _88876 k dom f) = (term633 A K _88876 k dom f).
Proof. exact (fun_ext (fun neut : A => @lem6782471 A K _88876 k dom f neut)). Qed.
Lemma lem6782473 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6782474 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term602 A K _88876 k dom f) = (term634 A K _88876 k dom f).
Proof. exact (MK_COMB (@lem6782473 A) (@lem6782472 A K _88876 k dom f)). Qed.
Lemma lem6782475 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (term603 A K _88876 k dom) = (term635 A K _88876 k dom).
Proof. exact (fun_ext (fun f : K -> A => @lem6782474 A K _88876 k dom f)). Qed.
Lemma lem6782476 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem6782477 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (term604 A K _88876 k dom) = (term636 A K _88876 k dom).
Proof. exact (MK_COMB (@lem6782476 A K) (@lem6782475 A K _88876 k dom)). Qed.
Lemma lem6782478 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (term605 A K _88876 k) = (term637 A K _88876 k).
Proof. exact (fun_ext (fun dom : A -> Prop => @lem6782477 A K _88876 k dom)). Qed.
Lemma lem6782479 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6782480 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (term606 A K _88876 k) = (term638 A K _88876 k).
Proof. exact (MK_COMB (@lem6782479 A) (@lem6782478 A K _88876 k)). Qed.
Lemma lem6782481 {A K : Type'} (_88876 : type835 A K) : (term607 A K _88876) = (term639 A K _88876).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6782480 A K _88876 k)). Qed.
Lemma lem6782482 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6782483 {A K : Type'} (_88876 : type835 A K) : (term608 A K _88876) = (term640 A K _88876).
Proof. exact (MK_COMB (@lem6782482 K) (@lem6782481 A K _88876)). Qed.
Lemma lem6782501 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term641 A P Q) = (term642 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem6782502 {K : Type'} (P : K -> Prop) (Q : K -> Prop) : (term641 K P Q) = (term642 K P Q).
Proof. exact (@lem6782501 K P Q). Qed.
Lemma lem6782503 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term643 A K _88876 k dom f neut) = (term644 A K _88876 k dom f neut).
Proof. exact (@lem6782502 K (term645 A K _88876 k dom f neut) (term646 A K _88876 k dom f neut)). Qed.
Lemma lem6782504 {A K : Type'} (_88876 : type835 A K) (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term647 A K _88876 k dom f neut GEN_PVAR_274) = (term626 A K _88876 GEN_PVAR_274 k dom f neut).
Proof. exact (eq_refl (term647 A K _88876 k dom f neut GEN_PVAR_274)). Qed.
Lemma lem6782505 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6782506 {A K : Type'} (_88876 : type835 A K) (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term648 A K _88876 k dom f neut GEN_PVAR_274) = (term628 A K _88876 GEN_PVAR_274 k dom f neut).
Proof. exact (MK_COMB (@lem6782505) (@lem6782504 A K _88876 GEN_PVAR_274 k dom f neut)). Qed.
Lemma lem6782507 {A K : Type'} (_88876 : type835 A K) (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term649 A K _88876 k dom f neut GEN_PVAR_274) = (term623 A K _88876 GEN_PVAR_274 k dom f neut).
Proof. exact (eq_refl (term649 A K _88876 k dom f neut GEN_PVAR_274)). Qed.
Lemma lem6782508 {A K : Type'} (_88876 : type835 A K) (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term650 A K _88876 k dom f neut GEN_PVAR_274) = (term630 A K _88876 GEN_PVAR_274 k dom f neut).
Proof. exact (MK_COMB (@lem6782506 A K _88876 GEN_PVAR_274 k dom f neut) (@lem6782507 A K _88876 GEN_PVAR_274 k dom f neut)). Qed.
Lemma lem6782509 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term651 A K _88876 k dom f neut) = (term631 A K _88876 k dom f neut).
Proof. exact (fun_ext (fun GEN_PVAR_274 : K => @lem6782508 A K _88876 GEN_PVAR_274 k dom f neut)). Qed.
Lemma lem6782510 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6782511 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term643 A K _88876 k dom f neut) = (term632 A K _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6782510 K) (@lem6782509 A K _88876 k dom f neut)). Qed.
Lemma lem6782512 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6782513 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term652 A K _88876 k dom f neut) = (term653 A K _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6782512) (@lem6782511 A K _88876 k dom f neut)). Qed.
Lemma lem6782514 {A K : Type'} (_88876 : type835 A K) (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term647 A K _88876 k dom f neut GEN_PVAR_274) = (term626 A K _88876 GEN_PVAR_274 k dom f neut).
Proof. exact (eq_refl (term647 A K _88876 k dom f neut GEN_PVAR_274)). Qed.
Lemma lem6782515 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term654 A K _88876 k dom f neut) = (term645 A K _88876 k dom f neut).
Proof. exact (fun_ext (fun GEN_PVAR_274 : K => @lem6782514 A K _88876 GEN_PVAR_274 k dom f neut)). Qed.
Lemma lem6782516 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6782517 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term655 A K _88876 k dom f neut) = (term656 A K _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6782516 K) (@lem6782515 A K _88876 k dom f neut)). Qed.
Lemma lem6782518 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6782519 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term657 A K _88876 k dom f neut) = (term658 A K _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6782518) (@lem6782517 A K _88876 k dom f neut)). Qed.
Lemma lem6782520 {A K : Type'} (_88876 : type835 A K) (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term649 A K _88876 k dom f neut GEN_PVAR_274) = (term623 A K _88876 GEN_PVAR_274 k dom f neut).
Proof. exact (eq_refl (term649 A K _88876 k dom f neut GEN_PVAR_274)). Qed.
Lemma lem6782521 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term659 A K _88876 k dom f neut) = (term646 A K _88876 k dom f neut).
Proof. exact (fun_ext (fun GEN_PVAR_274 : K => @lem6782520 A K _88876 GEN_PVAR_274 k dom f neut)). Qed.
Lemma lem6782522 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6782523 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term660 A K _88876 k dom f neut) = (term661 A K _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6782522 K) (@lem6782521 A K _88876 k dom f neut)). Qed.
Lemma lem6782524 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term644 A K _88876 k dom f neut) = (term662 A K _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6782519 A K _88876 k dom f neut) (@lem6782523 A K _88876 k dom f neut)). Qed.
Lemma lem6782525 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : ((term643 A K _88876 k dom f neut) = (term644 A K _88876 k dom f neut)) = ((term632 A K _88876 k dom f neut) = (term662 A K _88876 k dom f neut)).
Proof. exact (MK_COMB (@lem6782513 A K _88876 k dom f neut) (@lem6782524 A K _88876 k dom f neut)). Qed.
Lemma lem6782526 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term632 A K _88876 k dom f neut) = (term662 A K _88876 k dom f neut).
Proof. exact (EQ_MP (@lem6782525 A K _88876 k dom f neut) (@lem6782503 A K _88876 k dom f neut)). Qed.
Lemma lem6782631 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term633 A K _88876 k dom f) = (term663 A K _88876 k dom f).
Proof. exact (fun_ext (fun neut : A => @lem6782526 A K _88876 k dom f neut)). Qed.
Lemma lem6782632 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6782633 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term634 A K _88876 k dom f) = (term664 A K _88876 k dom f).
Proof. exact (MK_COMB (@lem6782632 A) (@lem6782631 A K _88876 k dom f)). Qed.
Lemma lem6782635 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term641 A P Q) = (term642 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem6782636 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term641 A P Q) = (term642 A P Q).
Proof. exact (@lem6782635 A P Q). Qed.
Lemma lem6782637 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term665 A K _88876 k dom f) = (term666 A K _88876 k dom f).
Proof. exact (@lem6782636 A (term667 A K _88876 k dom f) (term668 A K _88876 k dom f)). Qed.
Lemma lem6782638 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term669 A K _88876 k dom f neut) = (term656 A K _88876 k dom f neut).
Proof. exact (eq_refl (term669 A K _88876 k dom f neut)). Qed.
Lemma lem6782639 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6782640 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term670 A K _88876 k dom f neut) = (term658 A K _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6782639) (@lem6782638 A K _88876 k dom f neut)). Qed.
Lemma lem6782641 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term671 A K _88876 k dom f neut) = (term661 A K _88876 k dom f neut).
Proof. exact (eq_refl (term671 A K _88876 k dom f neut)). Qed.
Lemma lem6782642 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term672 A K _88876 k dom f neut) = (term662 A K _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6782640 A K _88876 k dom f neut) (@lem6782641 A K _88876 k dom f neut)). Qed.
Lemma lem6782643 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term673 A K _88876 k dom f) = (term663 A K _88876 k dom f).
Proof. exact (fun_ext (fun neut : A => @lem6782642 A K _88876 k dom f neut)). Qed.
Lemma lem6782644 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6782645 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term665 A K _88876 k dom f) = (term664 A K _88876 k dom f).
Proof. exact (MK_COMB (@lem6782644 A) (@lem6782643 A K _88876 k dom f)). Qed.
Lemma lem6782646 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6782647 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term674 A K _88876 k dom f) = (term675 A K _88876 k dom f).
Proof. exact (MK_COMB (@lem6782646) (@lem6782645 A K _88876 k dom f)). Qed.
Lemma lem6782648 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term669 A K _88876 k dom f neut) = (term656 A K _88876 k dom f neut).
Proof. exact (eq_refl (term669 A K _88876 k dom f neut)). Qed.
Lemma lem6782649 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term676 A K _88876 k dom f) = (term667 A K _88876 k dom f).
Proof. exact (fun_ext (fun neut : A => @lem6782648 A K _88876 k dom f neut)). Qed.
Lemma lem6782650 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6782651 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term677 A K _88876 k dom f) = (term678 A K _88876 k dom f).
Proof. exact (MK_COMB (@lem6782650 A) (@lem6782649 A K _88876 k dom f)). Qed.
Lemma lem6782652 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6782653 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term679 A K _88876 k dom f) = (term680 A K _88876 k dom f).
Proof. exact (MK_COMB (@lem6782652) (@lem6782651 A K _88876 k dom f)). Qed.
Lemma lem6782654 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term671 A K _88876 k dom f neut) = (term661 A K _88876 k dom f neut).
Proof. exact (eq_refl (term671 A K _88876 k dom f neut)). Qed.
Lemma lem6782655 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term681 A K _88876 k dom f) = (term668 A K _88876 k dom f).
Proof. exact (fun_ext (fun neut : A => @lem6782654 A K _88876 k dom f neut)). Qed.
Lemma lem6782656 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6782657 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term682 A K _88876 k dom f) = (term683 A K _88876 k dom f).
Proof. exact (MK_COMB (@lem6782656 A) (@lem6782655 A K _88876 k dom f)). Qed.
Lemma lem6782658 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term666 A K _88876 k dom f) = (term684 A K _88876 k dom f).
Proof. exact (MK_COMB (@lem6782653 A K _88876 k dom f) (@lem6782657 A K _88876 k dom f)). Qed.
Lemma lem6782659 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : ((term665 A K _88876 k dom f) = (term666 A K _88876 k dom f)) = ((term664 A K _88876 k dom f) = (term684 A K _88876 k dom f)).
Proof. exact (MK_COMB (@lem6782647 A K _88876 k dom f) (@lem6782658 A K _88876 k dom f)). Qed.
Lemma lem6782660 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term664 A K _88876 k dom f) = (term684 A K _88876 k dom f).
Proof. exact (EQ_MP (@lem6782659 A K _88876 k dom f) (@lem6782637 A K _88876 k dom f)). Qed.
Lemma lem6782773 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term634 A K _88876 k dom f) = (term684 A K _88876 k dom f).
Proof. exact (TRANS (@lem6782633 A K _88876 k dom f) (@lem6782660 A K _88876 k dom f)). Qed.
Lemma lem6782774 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (term635 A K _88876 k dom) = (term685 A K _88876 k dom).
Proof. exact (fun_ext (fun f : K -> A => @lem6782773 A K _88876 k dom f)). Qed.
Lemma lem6782775 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem6782776 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (term636 A K _88876 k dom) = (term686 A K _88876 k dom).
Proof. exact (MK_COMB (@lem6782775 A K) (@lem6782774 A K _88876 k dom)). Qed.
Lemma lem6782778 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term641 A P Q) = (term642 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem6782779 {A K : Type'} (P : type805 A K) (Q : type805 A K) : (term687 A K P Q) = (term688 A K P Q).
Proof. exact (@lem6782778 (K -> A) P Q). Qed.
Lemma lem6782780 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (term689 A K _88876 k dom) = (term690 A K _88876 k dom).
Proof. exact (@lem6782779 A K (term691 A K _88876 k dom) (term692 A K _88876 k dom)). Qed.
Lemma lem6782781 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term693 A K _88876 k dom f) = (term678 A K _88876 k dom f).
Proof. exact (eq_refl (term693 A K _88876 k dom f)). Qed.
Lemma lem6782782 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6782783 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term694 A K _88876 k dom f) = (term680 A K _88876 k dom f).
Proof. exact (MK_COMB (@lem6782782) (@lem6782781 A K _88876 k dom f)). Qed.
Lemma lem6782784 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term695 A K _88876 k dom f) = (term683 A K _88876 k dom f).
Proof. exact (eq_refl (term695 A K _88876 k dom f)). Qed.
Lemma lem6782785 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term696 A K _88876 k dom f) = (term684 A K _88876 k dom f).
Proof. exact (MK_COMB (@lem6782783 A K _88876 k dom f) (@lem6782784 A K _88876 k dom f)). Qed.
Lemma lem6782786 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (term697 A K _88876 k dom) = (term685 A K _88876 k dom).
Proof. exact (fun_ext (fun f : K -> A => @lem6782785 A K _88876 k dom f)). Qed.
Lemma lem6782787 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem6782788 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (term689 A K _88876 k dom) = (term686 A K _88876 k dom).
Proof. exact (MK_COMB (@lem6782787 A K) (@lem6782786 A K _88876 k dom)). Qed.
Lemma lem6782789 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6782790 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (term698 A K _88876 k dom) = (term699 A K _88876 k dom).
Proof. exact (MK_COMB (@lem6782789) (@lem6782788 A K _88876 k dom)). Qed.
Lemma lem6782791 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term693 A K _88876 k dom f) = (term678 A K _88876 k dom f).
Proof. exact (eq_refl (term693 A K _88876 k dom f)). Qed.
Lemma lem6782792 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (term700 A K _88876 k dom) = (term691 A K _88876 k dom).
Proof. exact (fun_ext (fun f : K -> A => @lem6782791 A K _88876 k dom f)). Qed.
Lemma lem6782793 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem6782794 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (term701 A K _88876 k dom) = (term702 A K _88876 k dom).
Proof. exact (MK_COMB (@lem6782793 A K) (@lem6782792 A K _88876 k dom)). Qed.
Lemma lem6782795 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6782796 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (term703 A K _88876 k dom) = (term704 A K _88876 k dom).
Proof. exact (MK_COMB (@lem6782795) (@lem6782794 A K _88876 k dom)). Qed.
Lemma lem6782797 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term695 A K _88876 k dom f) = (term683 A K _88876 k dom f).
Proof. exact (eq_refl (term695 A K _88876 k dom f)). Qed.
Lemma lem6782798 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (term705 A K _88876 k dom) = (term692 A K _88876 k dom).
Proof. exact (fun_ext (fun f : K -> A => @lem6782797 A K _88876 k dom f)). Qed.
Lemma lem6782799 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem6782800 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (term706 A K _88876 k dom) = (term707 A K _88876 k dom).
Proof. exact (MK_COMB (@lem6782799 A K) (@lem6782798 A K _88876 k dom)). Qed.
Lemma lem6782801 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (term690 A K _88876 k dom) = (term708 A K _88876 k dom).
Proof. exact (MK_COMB (@lem6782796 A K _88876 k dom) (@lem6782800 A K _88876 k dom)). Qed.
Lemma lem6782802 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : ((term689 A K _88876 k dom) = (term690 A K _88876 k dom)) = ((term686 A K _88876 k dom) = (term708 A K _88876 k dom)).
Proof. exact (MK_COMB (@lem6782790 A K _88876 k dom) (@lem6782801 A K _88876 k dom)). Qed.
Lemma lem6782803 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (term686 A K _88876 k dom) = (term708 A K _88876 k dom).
Proof. exact (EQ_MP (@lem6782802 A K _88876 k dom) (@lem6782780 A K _88876 k dom)). Qed.
Lemma lem6782924 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (term636 A K _88876 k dom) = (term708 A K _88876 k dom).
Proof. exact (TRANS (@lem6782776 A K _88876 k dom) (@lem6782803 A K _88876 k dom)). Qed.
Lemma lem6782925 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (term637 A K _88876 k) = (term709 A K _88876 k).
Proof. exact (fun_ext (fun dom : A -> Prop => @lem6782924 A K _88876 k dom)). Qed.
Lemma lem6782926 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6782927 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (term638 A K _88876 k) = (term710 A K _88876 k).
Proof. exact (MK_COMB (@lem6782926 A) (@lem6782925 A K _88876 k)). Qed.
Lemma lem6782929 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term641 A P Q) = (term642 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem6782930 {A : Type'} (P : type686 A) (Q : type686 A) : (term711 A P Q) = (term712 A P Q).
Proof. exact (@lem6782929 (A -> Prop) P Q). Qed.
Lemma lem6782931 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (term713 A K _88876 k) = (term714 A K _88876 k).
Proof. exact (@lem6782930 A (term715 A K _88876 k) (term716 A K _88876 k)). Qed.
Lemma lem6782932 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (term717 A K _88876 k dom) = (term702 A K _88876 k dom).
Proof. exact (eq_refl (term717 A K _88876 k dom)). Qed.
Lemma lem6782933 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6782934 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (term718 A K _88876 k dom) = (term704 A K _88876 k dom).
Proof. exact (MK_COMB (@lem6782933) (@lem6782932 A K _88876 k dom)). Qed.
Lemma lem6782935 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (term719 A K _88876 k dom) = (term707 A K _88876 k dom).
Proof. exact (eq_refl (term719 A K _88876 k dom)). Qed.
Lemma lem6782936 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (term720 A K _88876 k dom) = (term708 A K _88876 k dom).
Proof. exact (MK_COMB (@lem6782934 A K _88876 k dom) (@lem6782935 A K _88876 k dom)). Qed.
Lemma lem6782937 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (term721 A K _88876 k) = (term709 A K _88876 k).
Proof. exact (fun_ext (fun dom : A -> Prop => @lem6782936 A K _88876 k dom)). Qed.
Lemma lem6782938 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6782939 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (term713 A K _88876 k) = (term710 A K _88876 k).
Proof. exact (MK_COMB (@lem6782938 A) (@lem6782937 A K _88876 k)). Qed.
Lemma lem6782940 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6782941 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (term722 A K _88876 k) = (term723 A K _88876 k).
Proof. exact (MK_COMB (@lem6782940) (@lem6782939 A K _88876 k)). Qed.
Lemma lem6782942 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (term717 A K _88876 k dom) = (term702 A K _88876 k dom).
Proof. exact (eq_refl (term717 A K _88876 k dom)). Qed.
Lemma lem6782943 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (term724 A K _88876 k) = (term715 A K _88876 k).
Proof. exact (fun_ext (fun dom : A -> Prop => @lem6782942 A K _88876 k dom)). Qed.
Lemma lem6782944 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6782945 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (term725 A K _88876 k) = (term726 A K _88876 k).
Proof. exact (MK_COMB (@lem6782944 A) (@lem6782943 A K _88876 k)). Qed.
Lemma lem6782946 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6782947 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (term727 A K _88876 k) = (term728 A K _88876 k).
Proof. exact (MK_COMB (@lem6782946) (@lem6782945 A K _88876 k)). Qed.
Lemma lem6782948 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (term719 A K _88876 k dom) = (term707 A K _88876 k dom).
Proof. exact (eq_refl (term719 A K _88876 k dom)). Qed.
Lemma lem6782949 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (term729 A K _88876 k) = (term716 A K _88876 k).
Proof. exact (fun_ext (fun dom : A -> Prop => @lem6782948 A K _88876 k dom)). Qed.
Lemma lem6782950 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6782951 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (term730 A K _88876 k) = (term731 A K _88876 k).
Proof. exact (MK_COMB (@lem6782950 A) (@lem6782949 A K _88876 k)). Qed.
Lemma lem6782952 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (term714 A K _88876 k) = (term732 A K _88876 k).
Proof. exact (MK_COMB (@lem6782947 A K _88876 k) (@lem6782951 A K _88876 k)). Qed.
Lemma lem6782953 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : ((term713 A K _88876 k) = (term714 A K _88876 k)) = ((term710 A K _88876 k) = (term732 A K _88876 k)).
Proof. exact (MK_COMB (@lem6782941 A K _88876 k) (@lem6782952 A K _88876 k)). Qed.
Lemma lem6782954 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (term710 A K _88876 k) = (term732 A K _88876 k).
Proof. exact (EQ_MP (@lem6782953 A K _88876 k) (@lem6782931 A K _88876 k)). Qed.
Lemma lem6783083 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (term638 A K _88876 k) = (term732 A K _88876 k).
Proof. exact (TRANS (@lem6782927 A K _88876 k) (@lem6782954 A K _88876 k)). Qed.
Lemma lem6783084 {A K : Type'} (_88876 : type835 A K) : (term639 A K _88876) = (term733 A K _88876).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6783083 A K _88876 k)). Qed.
Lemma lem6783085 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6783086 {A K : Type'} (_88876 : type835 A K) : (term640 A K _88876) = (term734 A K _88876).
Proof. exact (MK_COMB (@lem6783085 K) (@lem6783084 A K _88876)). Qed.
Lemma lem6783088 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term641 A P Q) = (term642 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem6783089 {K : Type'} (P : type686 K) (Q : type686 K) : (term711 K P Q) = (term712 K P Q).
Proof. exact (@lem6783088 (K -> Prop) P Q). Qed.
Lemma lem6783090 {A K : Type'} (_88876 : type835 A K) : (term735 A K _88876) = (term736 A K _88876).
Proof. exact (@lem6783089 K (term737 A K _88876) (term738 A K _88876)). Qed.
Lemma lem6783091 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (term739 A K _88876 k) = (term726 A K _88876 k).
Proof. exact (eq_refl (term739 A K _88876 k)). Qed.
Lemma lem6783092 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6783093 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (term740 A K _88876 k) = (term728 A K _88876 k).
Proof. exact (MK_COMB (@lem6783092) (@lem6783091 A K _88876 k)). Qed.
Lemma lem6783094 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (term741 A K _88876 k) = (term731 A K _88876 k).
Proof. exact (eq_refl (term741 A K _88876 k)). Qed.
Lemma lem6783095 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (term742 A K _88876 k) = (term732 A K _88876 k).
Proof. exact (MK_COMB (@lem6783093 A K _88876 k) (@lem6783094 A K _88876 k)). Qed.
Lemma lem6783096 {A K : Type'} (_88876 : type835 A K) : (term743 A K _88876) = (term733 A K _88876).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6783095 A K _88876 k)). Qed.
Lemma lem6783097 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6783098 {A K : Type'} (_88876 : type835 A K) : (term735 A K _88876) = (term734 A K _88876).
Proof. exact (MK_COMB (@lem6783097 K) (@lem6783096 A K _88876)). Qed.
Lemma lem6783099 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6783100 {A K : Type'} (_88876 : type835 A K) : (term744 A K _88876) = (term745 A K _88876).
Proof. exact (MK_COMB (@lem6783099) (@lem6783098 A K _88876)). Qed.
Lemma lem6783101 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (term739 A K _88876 k) = (term726 A K _88876 k).
Proof. exact (eq_refl (term739 A K _88876 k)). Qed.
Lemma lem6783102 {A K : Type'} (_88876 : type835 A K) : (term746 A K _88876) = (term737 A K _88876).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6783101 A K _88876 k)). Qed.
Lemma lem6783103 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6783104 {A K : Type'} (_88876 : type835 A K) : (term747 A K _88876) = (term748 A K _88876).
Proof. exact (MK_COMB (@lem6783103 K) (@lem6783102 A K _88876)). Qed.
Lemma lem6783105 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6783106 {A K : Type'} (_88876 : type835 A K) : (term749 A K _88876) = (term750 A K _88876).
Proof. exact (MK_COMB (@lem6783105) (@lem6783104 A K _88876)). Qed.
Lemma lem6783107 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (term741 A K _88876 k) = (term731 A K _88876 k).
Proof. exact (eq_refl (term741 A K _88876 k)). Qed.
Lemma lem6783108 {A K : Type'} (_88876 : type835 A K) : (term751 A K _88876) = (term738 A K _88876).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6783107 A K _88876 k)). Qed.
Lemma lem6783109 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6783110 {A K : Type'} (_88876 : type835 A K) : (term752 A K _88876) = (term753 A K _88876).
Proof. exact (MK_COMB (@lem6783109 K) (@lem6783108 A K _88876)). Qed.
Lemma lem6783111 {A K : Type'} (_88876 : type835 A K) : (term736 A K _88876) = (term754 A K _88876).
Proof. exact (MK_COMB (@lem6783106 A K _88876) (@lem6783110 A K _88876)). Qed.
Lemma lem6783112 {A K : Type'} (_88876 : type835 A K) : ((term735 A K _88876) = (term736 A K _88876)) = ((term734 A K _88876) = (term754 A K _88876)).
Proof. exact (MK_COMB (@lem6783100 A K _88876) (@lem6783111 A K _88876)). Qed.
Lemma lem6783113 {A K : Type'} (_88876 : type835 A K) : (term734 A K _88876) = (term754 A K _88876).
Proof. exact (EQ_MP (@lem6783112 A K _88876) (@lem6783090 A K _88876)). Qed.
Lemma lem6783250 {A K : Type'} (_88876 : type835 A K) : (term640 A K _88876) = (term754 A K _88876).
Proof. exact (TRANS (@lem6783086 A K _88876) (@lem6783113 A K _88876)). Qed.
Lemma lem6783252 {A : Type'} (P : Prop) (Q : A -> Prop) : (term755 A P Q) = (term756 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6783253 {K : Type'} (P : Prop) (Q : K -> Prop) : (term755 K P Q) = (term756 K P Q).
Proof. exact (@lem6783252 K P Q). Qed.
Lemma lem6783254 {A K : Type'} (_88876 : type835 A K) (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term757 A K _88876 GEN_PVAR_274 k dom f neut) = (term758 A K _88876 GEN_PVAR_274 k dom f neut).
Proof. exact (@lem6783253 K (term759 A K _88876 k dom f neut GEN_PVAR_274) (term359 A K GEN_PVAR_274 k dom f neut)). Qed.
Lemma lem6783255 {A K : Type'} (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term616 A K GEN_PVAR_274 k dom f neut i) = (term358 A K GEN_PVAR_274 k dom f neut i).
Proof. exact (eq_refl (term616 A K GEN_PVAR_274 k dom f neut i)). Qed.
Lemma lem6783256 {A K : Type'} (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term760 A K GEN_PVAR_274 k dom f neut) = (term359 A K GEN_PVAR_274 k dom f neut).
Proof. exact (fun_ext (fun i : K => @lem6783255 A K GEN_PVAR_274 k dom f neut i)). Qed.
Lemma lem6783257 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem6783258 {A K : Type'} (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term761 A K GEN_PVAR_274 k dom f neut) = (term360 A K GEN_PVAR_274 k dom f neut).
Proof. exact (MK_COMB (@lem6783257 K) (@lem6783256 A K GEN_PVAR_274 k dom f neut)). Qed.
Lemma lem6783259 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (GEN_PVAR_274 : K) : (term622 A K _88876 k dom f neut GEN_PVAR_274) = (term622 A K _88876 k dom f neut GEN_PVAR_274).
Proof. exact (eq_refl (term622 A K _88876 k dom f neut GEN_PVAR_274)). Qed.
Lemma lem6783260 {A K : Type'} (_88876 : type835 A K) (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term757 A K _88876 GEN_PVAR_274 k dom f neut) = (term623 A K _88876 GEN_PVAR_274 k dom f neut).
Proof. exact (MK_COMB (@lem6783259 A K _88876 k dom f neut GEN_PVAR_274) (@lem6783258 A K GEN_PVAR_274 k dom f neut)). Qed.
Lemma lem6783261 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6783262 {A K : Type'} (_88876 : type835 A K) (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term762 A K _88876 GEN_PVAR_274 k dom f neut) = (term763 A K _88876 GEN_PVAR_274 k dom f neut).
Proof. exact (MK_COMB (@lem6783261) (@lem6783260 A K _88876 GEN_PVAR_274 k dom f neut)). Qed.
Lemma lem6783263 {A K : Type'} (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term616 A K GEN_PVAR_274 k dom f neut i) = (term358 A K GEN_PVAR_274 k dom f neut i).
Proof. exact (eq_refl (term616 A K GEN_PVAR_274 k dom f neut i)). Qed.
Lemma lem6783264 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (GEN_PVAR_274 : K) : (term622 A K _88876 k dom f neut GEN_PVAR_274) = (term622 A K _88876 k dom f neut GEN_PVAR_274).
Proof. exact (eq_refl (term622 A K _88876 k dom f neut GEN_PVAR_274)). Qed.
Lemma lem6783265 {A K : Type'} (_88876 : type835 A K) (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term764 A K _88876 GEN_PVAR_274 k dom f neut i) = (term765 A K _88876 GEN_PVAR_274 k dom f neut i).
Proof. exact (MK_COMB (@lem6783264 A K _88876 k dom f neut GEN_PVAR_274) (@lem6783263 A K GEN_PVAR_274 k dom f neut i)). Qed.
Lemma lem6783266 {A K : Type'} (_88876 : type835 A K) (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term766 A K _88876 GEN_PVAR_274 k dom f neut) = (term767 A K _88876 GEN_PVAR_274 k dom f neut).
Proof. exact (fun_ext (fun i : K => @lem6783265 A K _88876 GEN_PVAR_274 k dom f neut i)). Qed.
Lemma lem6783267 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem6783268 {A K : Type'} (_88876 : type835 A K) (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term758 A K _88876 GEN_PVAR_274 k dom f neut) = (term768 A K _88876 GEN_PVAR_274 k dom f neut).
Proof. exact (MK_COMB (@lem6783267 K) (@lem6783266 A K _88876 GEN_PVAR_274 k dom f neut)). Qed.
Lemma lem6783269 {A K : Type'} (_88876 : type835 A K) (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : ((term757 A K _88876 GEN_PVAR_274 k dom f neut) = (term758 A K _88876 GEN_PVAR_274 k dom f neut)) = ((term623 A K _88876 GEN_PVAR_274 k dom f neut) = (term768 A K _88876 GEN_PVAR_274 k dom f neut)).
Proof. exact (MK_COMB (@lem6783262 A K _88876 GEN_PVAR_274 k dom f neut) (@lem6783268 A K _88876 GEN_PVAR_274 k dom f neut)). Qed.
Lemma lem6783270 {A K : Type'} (_88876 : type835 A K) (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term623 A K _88876 GEN_PVAR_274 k dom f neut) = (term768 A K _88876 GEN_PVAR_274 k dom f neut).
Proof. exact (EQ_MP (@lem6783269 A K _88876 GEN_PVAR_274 k dom f neut) (@lem6783254 A K _88876 GEN_PVAR_274 k dom f neut)). Qed.
Lemma lem6783271 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term646 A K _88876 k dom f neut) = (term769 A K _88876 k dom f neut).
Proof. exact (fun_ext (fun GEN_PVAR_274 : K => @lem6783270 A K _88876 GEN_PVAR_274 k dom f neut)). Qed.
Lemma lem6783272 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6783273 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term661 A K _88876 k dom f neut) = (term770 A K _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6783272 K) (@lem6783271 A K _88876 k dom f neut)). Qed.
Lemma lem6783275 {A B : Type'} (P : type1413 A B) : (term771 A B P) = (term772 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6783276 {K : Type'} (P : type1402 K) : (term773 K P) = (term774 K P).
Proof. exact (@lem6783275 K K P). Qed.
Lemma lem6783277 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term775 A K _88876 k dom f neut) = (term776 A K _88876 k dom f neut).
Proof. exact (@lem6783276 K (term777 A K _88876 k dom f neut)). Qed.
Lemma lem6783278 {A K : Type'} (_88876 : type835 A K) (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term778 A K _88876 k dom f neut GEN_PVAR_274) = (term767 A K _88876 GEN_PVAR_274 k dom f neut).
Proof. exact (eq_refl (term778 A K _88876 k dom f neut GEN_PVAR_274)). Qed.
Lemma lem6783279 {K : Type'} (i : K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem6783280 {A K : Type'} (_88876 : type835 A K) (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term779 A K _88876 k dom f neut GEN_PVAR_274 i) = (term780 A K _88876 GEN_PVAR_274 k dom f neut i).
Proof. exact (MK_COMB (@lem6783278 A K _88876 GEN_PVAR_274 k dom f neut) (@lem6783279 K i)). Qed.
Lemma lem6783281 {A K : Type'} (_88876 : type835 A K) (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term780 A K _88876 GEN_PVAR_274 k dom f neut i) = (term765 A K _88876 GEN_PVAR_274 k dom f neut i).
Proof. exact (eq_refl (term780 A K _88876 GEN_PVAR_274 k dom f neut i)). Qed.
Lemma lem6783282 {A K : Type'} (_88876 : type835 A K) (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term779 A K _88876 k dom f neut GEN_PVAR_274 i) = (term765 A K _88876 GEN_PVAR_274 k dom f neut i).
Proof. exact (TRANS (@lem6783280 A K _88876 GEN_PVAR_274 k dom f neut i) (@lem6783281 A K _88876 GEN_PVAR_274 k dom f neut i)). Qed.
Lemma lem6783283 {A K : Type'} (_88876 : type835 A K) (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term781 A K _88876 k dom f neut GEN_PVAR_274) = (term767 A K _88876 GEN_PVAR_274 k dom f neut).
Proof. exact (fun_ext (fun i : K => @lem6783282 A K _88876 GEN_PVAR_274 k dom f neut i)). Qed.
Lemma lem6783284 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem6783285 {A K : Type'} (_88876 : type835 A K) (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term782 A K _88876 k dom f neut GEN_PVAR_274) = (term768 A K _88876 GEN_PVAR_274 k dom f neut).
Proof. exact (MK_COMB (@lem6783284 K) (@lem6783283 A K _88876 GEN_PVAR_274 k dom f neut)). Qed.
Lemma lem6783286 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term783 A K _88876 k dom f neut) = (term769 A K _88876 k dom f neut).
Proof. exact (fun_ext (fun GEN_PVAR_274 : K => @lem6783285 A K _88876 GEN_PVAR_274 k dom f neut)). Qed.
Lemma lem6783287 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6783288 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term775 A K _88876 k dom f neut) = (term770 A K _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6783287 K) (@lem6783286 A K _88876 k dom f neut)). Qed.
Lemma lem6783289 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6783290 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term784 A K _88876 k dom f neut) = (term785 A K _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6783289) (@lem6783288 A K _88876 k dom f neut)). Qed.
Lemma lem6783291 {A K : Type'} (_88876 : type835 A K) (GEN_PVAR_274 : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term778 A K _88876 k dom f neut GEN_PVAR_274) = (term767 A K _88876 GEN_PVAR_274 k dom f neut).
Proof. exact (eq_refl (term778 A K _88876 k dom f neut GEN_PVAR_274)). Qed.
Lemma lem6783292 {K : Type'} (i : K -> K) (GEN_PVAR_274 : K) : (i GEN_PVAR_274) = (i GEN_PVAR_274).
Proof. exact (eq_refl (i GEN_PVAR_274)). Qed.
Lemma lem6783293 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K -> K) (GEN_PVAR_274 : K) : (term786 A K _88876 k dom f neut i GEN_PVAR_274) = (term787 A K _88876 k dom f neut i GEN_PVAR_274).
Proof. exact (MK_COMB (@lem6783291 A K _88876 GEN_PVAR_274 k dom f neut) (@lem6783292 K i GEN_PVAR_274)). Qed.
Lemma lem6783294 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K -> K) (GEN_PVAR_274 : K) : (term787 A K _88876 k dom f neut i GEN_PVAR_274) = (term788 A K _88876 k dom f neut i GEN_PVAR_274).
Proof. exact (eq_refl (term787 A K _88876 k dom f neut i GEN_PVAR_274)). Qed.
Lemma lem6783295 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K -> K) (GEN_PVAR_274 : K) : (term786 A K _88876 k dom f neut i GEN_PVAR_274) = (term788 A K _88876 k dom f neut i GEN_PVAR_274).
Proof. exact (TRANS (@lem6783293 A K _88876 k dom f neut i GEN_PVAR_274) (@lem6783294 A K _88876 k dom f neut i GEN_PVAR_274)). Qed.
Lemma lem6783296 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K -> K) : (term789 A K _88876 k dom f neut i) = (term790 A K _88876 k dom f neut i).
Proof. exact (fun_ext (fun GEN_PVAR_274 : K => @lem6783295 A K _88876 k dom f neut i GEN_PVAR_274)). Qed.
Lemma lem6783297 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6783298 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K -> K) : (term791 A K _88876 k dom f neut i) = (term792 A K _88876 k dom f neut i).
Proof. exact (MK_COMB (@lem6783297 K) (@lem6783296 A K _88876 k dom f neut i)). Qed.
Lemma lem6783299 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term793 A K _88876 k dom f neut) = (term794 A K _88876 k dom f neut).
Proof. exact (fun_ext (fun i : K -> K => @lem6783298 A K _88876 k dom f neut i)). Qed.
Lemma lem6783300 {K : Type'} : (@ex (K -> K)) = (@ex (K -> K)).
Proof. exact (eq_refl (@ex (K -> K))). Qed.
Lemma lem6783301 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term776 A K _88876 k dom f neut) = (term795 A K _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6783300 K) (@lem6783299 A K _88876 k dom f neut)). Qed.
Lemma lem6783302 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : ((term775 A K _88876 k dom f neut) = (term776 A K _88876 k dom f neut)) = ((term770 A K _88876 k dom f neut) = (term795 A K _88876 k dom f neut)).
Proof. exact (MK_COMB (@lem6783290 A K _88876 k dom f neut) (@lem6783301 A K _88876 k dom f neut)). Qed.
Lemma lem6783303 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term770 A K _88876 k dom f neut) = (term795 A K _88876 k dom f neut).
Proof. exact (EQ_MP (@lem6783302 A K _88876 k dom f neut) (@lem6783277 A K _88876 k dom f neut)). Qed.
Lemma lem6783304 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term661 A K _88876 k dom f neut) = (term795 A K _88876 k dom f neut).
Proof. exact (TRANS (@lem6783273 A K _88876 k dom f neut) (@lem6783303 A K _88876 k dom f neut)). Qed.
Lemma lem6783305 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term668 A K _88876 k dom f) = (term796 A K _88876 k dom f).
Proof. exact (fun_ext (fun neut : A => @lem6783304 A K _88876 k dom f neut)). Qed.
Lemma lem6783306 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6783307 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term683 A K _88876 k dom f) = (term797 A K _88876 k dom f).
Proof. exact (MK_COMB (@lem6783306 A) (@lem6783305 A K _88876 k dom f)). Qed.
Lemma lem6783309 {A B : Type'} (P : type1413 A B) : (term771 A B P) = (term772 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6783310 {A K : Type'} (P : type1373 A K) : (term798 A K P) = (term799 A K P).
Proof. exact (@lem6783309 A (K -> K) P). Qed.
Lemma lem6783311 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term800 A K _88876 k dom f) = (term801 A K _88876 k dom f).
Proof. exact (@lem6783310 A K (term802 A K _88876 k dom f)). Qed.
Lemma lem6783312 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term803 A K _88876 k dom f neut) = (term794 A K _88876 k dom f neut).
Proof. exact (eq_refl (term803 A K _88876 k dom f neut)). Qed.
Lemma lem6783313 {K : Type'} (i : K -> K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem6783314 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K -> K) : (term804 A K _88876 k dom f neut i) = (term805 A K _88876 k dom f neut i).
Proof. exact (MK_COMB (@lem6783312 A K _88876 k dom f neut) (@lem6783313 K i)). Qed.
Lemma lem6783315 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K -> K) : (term805 A K _88876 k dom f neut i) = (term792 A K _88876 k dom f neut i).
Proof. exact (eq_refl (term805 A K _88876 k dom f neut i)). Qed.
Lemma lem6783316 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K -> K) : (term804 A K _88876 k dom f neut i) = (term792 A K _88876 k dom f neut i).
Proof. exact (TRANS (@lem6783314 A K _88876 k dom f neut i) (@lem6783315 A K _88876 k dom f neut i)). Qed.
Lemma lem6783317 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term806 A K _88876 k dom f neut) = (term794 A K _88876 k dom f neut).
Proof. exact (fun_ext (fun i : K -> K => @lem6783316 A K _88876 k dom f neut i)). Qed.
Lemma lem6783318 {K : Type'} : (@ex (K -> K)) = (@ex (K -> K)).
Proof. exact (eq_refl (@ex (K -> K))). Qed.
Lemma lem6783319 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term807 A K _88876 k dom f neut) = (term795 A K _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6783318 K) (@lem6783317 A K _88876 k dom f neut)). Qed.
Lemma lem6783320 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term808 A K _88876 k dom f) = (term796 A K _88876 k dom f).
Proof. exact (fun_ext (fun neut : A => @lem6783319 A K _88876 k dom f neut)). Qed.
Lemma lem6783321 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6783322 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term800 A K _88876 k dom f) = (term797 A K _88876 k dom f).
Proof. exact (MK_COMB (@lem6783321 A) (@lem6783320 A K _88876 k dom f)). Qed.
Lemma lem6783323 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6783324 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term809 A K _88876 k dom f) = (term810 A K _88876 k dom f).
Proof. exact (MK_COMB (@lem6783323) (@lem6783322 A K _88876 k dom f)). Qed.
Lemma lem6783325 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term803 A K _88876 k dom f neut) = (term794 A K _88876 k dom f neut).
Proof. exact (eq_refl (term803 A K _88876 k dom f neut)). Qed.
Lemma lem6783326 {A K : Type'} (i : type1411 A K) (neut : A) : (i neut) = (i neut).
Proof. exact (eq_refl (i neut)). Qed.
Lemma lem6783327 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : type1411 A K) (neut : A) : (term811 A K _88876 k dom f i neut) = (term812 A K _88876 k dom f i neut).
Proof. exact (MK_COMB (@lem6783325 A K _88876 k dom f neut) (@lem6783326 A K i neut)). Qed.
Lemma lem6783328 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : type1411 A K) (neut : A) : (term812 A K _88876 k dom f i neut) = (term813 A K _88876 k dom f i neut).
Proof. exact (eq_refl (term812 A K _88876 k dom f i neut)). Qed.
Lemma lem6783329 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : type1411 A K) (neut : A) : (term811 A K _88876 k dom f i neut) = (term813 A K _88876 k dom f i neut).
Proof. exact (TRANS (@lem6783327 A K _88876 k dom f i neut) (@lem6783328 A K _88876 k dom f i neut)). Qed.
Lemma lem6783330 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : type1411 A K) : (term814 A K _88876 k dom f i) = (term815 A K _88876 k dom f i).
Proof. exact (fun_ext (fun neut : A => @lem6783329 A K _88876 k dom f i neut)). Qed.
Lemma lem6783331 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6783332 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : type1411 A K) : (term816 A K _88876 k dom f i) = (term817 A K _88876 k dom f i).
Proof. exact (MK_COMB (@lem6783331 A) (@lem6783330 A K _88876 k dom f i)). Qed.
Lemma lem6783333 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term818 A K _88876 k dom f) = (term819 A K _88876 k dom f).
Proof. exact (fun_ext (fun i : type1411 A K => @lem6783332 A K _88876 k dom f i)). Qed.
Lemma lem6783334 {A K : Type'} : (@ex (A -> K -> K)) = (@ex (A -> K -> K)).
Proof. exact (eq_refl (@ex (A -> K -> K))). Qed.
Lemma lem6783335 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term801 A K _88876 k dom f) = (term820 A K _88876 k dom f).
Proof. exact (MK_COMB (@lem6783334 A K) (@lem6783333 A K _88876 k dom f)). Qed.
Lemma lem6783336 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : ((term800 A K _88876 k dom f) = (term801 A K _88876 k dom f)) = ((term797 A K _88876 k dom f) = (term820 A K _88876 k dom f)).
Proof. exact (MK_COMB (@lem6783324 A K _88876 k dom f) (@lem6783335 A K _88876 k dom f)). Qed.
Lemma lem6783337 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term797 A K _88876 k dom f) = (term820 A K _88876 k dom f).
Proof. exact (EQ_MP (@lem6783336 A K _88876 k dom f) (@lem6783311 A K _88876 k dom f)). Qed.
Lemma lem6783338 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term683 A K _88876 k dom f) = (term820 A K _88876 k dom f).
Proof. exact (TRANS (@lem6783307 A K _88876 k dom f) (@lem6783337 A K _88876 k dom f)). Qed.
Lemma lem6783339 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (term692 A K _88876 k dom) = (term821 A K _88876 k dom).
Proof. exact (fun_ext (fun f : K -> A => @lem6783338 A K _88876 k dom f)). Qed.
Lemma lem6783340 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem6783341 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (term707 A K _88876 k dom) = (term822 A K _88876 k dom).
Proof. exact (MK_COMB (@lem6783340 A K) (@lem6783339 A K _88876 k dom)). Qed.
Lemma lem6783343 {A B : Type'} (P : type1413 A B) : (term771 A B P) = (term772 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6783344 {A K : Type'} (P : type778 A K) : (term823 A K P) = (term824 A K P).
Proof. exact (@lem6783343 (K -> A) (type1411 A K) P). Qed.
Lemma lem6783345 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (term825 A K _88876 k dom) = (term826 A K _88876 k dom).
Proof. exact (@lem6783344 A K (term827 A K _88876 k dom)). Qed.
Lemma lem6783346 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term828 A K _88876 k dom f) = (term819 A K _88876 k dom f).
Proof. exact (eq_refl (term828 A K _88876 k dom f)). Qed.
Lemma lem6783347 {A K : Type'} (i : type1411 A K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem6783348 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : type1411 A K) : (term829 A K _88876 k dom f i) = (term830 A K _88876 k dom f i).
Proof. exact (MK_COMB (@lem6783346 A K _88876 k dom f) (@lem6783347 A K i)). Qed.
Lemma lem6783349 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : type1411 A K) : (term830 A K _88876 k dom f i) = (term817 A K _88876 k dom f i).
Proof. exact (eq_refl (term830 A K _88876 k dom f i)). Qed.
Lemma lem6783350 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : type1411 A K) : (term829 A K _88876 k dom f i) = (term817 A K _88876 k dom f i).
Proof. exact (TRANS (@lem6783348 A K _88876 k dom f i) (@lem6783349 A K _88876 k dom f i)). Qed.
Lemma lem6783351 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term831 A K _88876 k dom f) = (term819 A K _88876 k dom f).
Proof. exact (fun_ext (fun i : type1411 A K => @lem6783350 A K _88876 k dom f i)). Qed.
Lemma lem6783352 {A K : Type'} : (@ex (A -> K -> K)) = (@ex (A -> K -> K)).
Proof. exact (eq_refl (@ex (A -> K -> K))). Qed.
Lemma lem6783353 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term832 A K _88876 k dom f) = (term820 A K _88876 k dom f).
Proof. exact (MK_COMB (@lem6783352 A K) (@lem6783351 A K _88876 k dom f)). Qed.
Lemma lem6783354 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (term833 A K _88876 k dom) = (term821 A K _88876 k dom).
Proof. exact (fun_ext (fun f : K -> A => @lem6783353 A K _88876 k dom f)). Qed.
Lemma lem6783355 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem6783356 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (term825 A K _88876 k dom) = (term822 A K _88876 k dom).
Proof. exact (MK_COMB (@lem6783355 A K) (@lem6783354 A K _88876 k dom)). Qed.
Lemma lem6783357 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6783358 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (term834 A K _88876 k dom) = (term835 A K _88876 k dom).
Proof. exact (MK_COMB (@lem6783357) (@lem6783356 A K _88876 k dom)). Qed.
Lemma lem6783359 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term828 A K _88876 k dom f) = (term819 A K _88876 k dom f).
Proof. exact (eq_refl (term828 A K _88876 k dom f)). Qed.
Lemma lem6783360 {A K : Type'} (i : type792 A K) (f : K -> A) : (i f) = (i f).
Proof. exact (eq_refl (i f)). Qed.
Lemma lem6783361 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (i : type792 A K) (f : K -> A) : (term836 A K _88876 k dom i f) = (term837 A K _88876 k dom i f).
Proof. exact (MK_COMB (@lem6783359 A K _88876 k dom f) (@lem6783360 A K i f)). Qed.
Lemma lem6783362 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (i : type792 A K) (f : K -> A) : (term837 A K _88876 k dom i f) = (term838 A K _88876 k dom i f).
Proof. exact (eq_refl (term837 A K _88876 k dom i f)). Qed.
Lemma lem6783363 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (i : type792 A K) (f : K -> A) : (term836 A K _88876 k dom i f) = (term838 A K _88876 k dom i f).
Proof. exact (TRANS (@lem6783361 A K _88876 k dom i f) (@lem6783362 A K _88876 k dom i f)). Qed.
Lemma lem6783364 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (i : type792 A K) : (term839 A K _88876 k dom i) = (term840 A K _88876 k dom i).
Proof. exact (fun_ext (fun f : K -> A => @lem6783363 A K _88876 k dom i f)). Qed.
Lemma lem6783365 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem6783366 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (i : type792 A K) : (term841 A K _88876 k dom i) = (term842 A K _88876 k dom i).
Proof. exact (MK_COMB (@lem6783365 A K) (@lem6783364 A K _88876 k dom i)). Qed.
Lemma lem6783367 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (term843 A K _88876 k dom) = (term844 A K _88876 k dom).
Proof. exact (fun_ext (fun i : type792 A K => @lem6783366 A K _88876 k dom i)). Qed.
Lemma lem6783368 {A K : Type'} : (@ex ((K -> A) -> A -> K -> K)) = (@ex ((K -> A) -> A -> K -> K)).
Proof. exact (eq_refl (@ex ((K -> A) -> A -> K -> K))). Qed.
Lemma lem6783369 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (term826 A K _88876 k dom) = (term845 A K _88876 k dom).
Proof. exact (MK_COMB (@lem6783368 A K) (@lem6783367 A K _88876 k dom)). Qed.
Lemma lem6783370 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : ((term825 A K _88876 k dom) = (term826 A K _88876 k dom)) = ((term822 A K _88876 k dom) = (term845 A K _88876 k dom)).
Proof. exact (MK_COMB (@lem6783358 A K _88876 k dom) (@lem6783369 A K _88876 k dom)). Qed.
Lemma lem6783371 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (term822 A K _88876 k dom) = (term845 A K _88876 k dom).
Proof. exact (EQ_MP (@lem6783370 A K _88876 k dom) (@lem6783345 A K _88876 k dom)). Qed.
Lemma lem6783372 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (term707 A K _88876 k dom) = (term845 A K _88876 k dom).
Proof. exact (TRANS (@lem6783341 A K _88876 k dom) (@lem6783371 A K _88876 k dom)). Qed.
Lemma lem6783373 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (term716 A K _88876 k) = (term846 A K _88876 k).
Proof. exact (fun_ext (fun dom : A -> Prop => @lem6783372 A K _88876 k dom)). Qed.
Lemma lem6783374 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6783375 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (term731 A K _88876 k) = (term847 A K _88876 k).
Proof. exact (MK_COMB (@lem6783374 A) (@lem6783373 A K _88876 k)). Qed.
Lemma lem6783377 {A B : Type'} (P : type1413 A B) : (term771 A B P) = (term772 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6783378 {A K : Type'} (P : type604 A K) : (term848 A K P) = (term849 A K P).
Proof. exact (@lem6783377 (A -> Prop) (type792 A K) P). Qed.
Lemma lem6783379 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (term850 A K _88876 k) = (term851 A K _88876 k).
Proof. exact (@lem6783378 A K (term852 A K _88876 k)). Qed.
Lemma lem6783380 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (term853 A K _88876 k dom) = (term844 A K _88876 k dom).
Proof. exact (eq_refl (term853 A K _88876 k dom)). Qed.
Lemma lem6783381 {A K : Type'} (i : type792 A K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem6783382 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (i : type792 A K) : (term854 A K _88876 k dom i) = (term855 A K _88876 k dom i).
Proof. exact (MK_COMB (@lem6783380 A K _88876 k dom) (@lem6783381 A K i)). Qed.
Lemma lem6783383 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (i : type792 A K) : (term855 A K _88876 k dom i) = (term842 A K _88876 k dom i).
Proof. exact (eq_refl (term855 A K _88876 k dom i)). Qed.
Lemma lem6783384 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (i : type792 A K) : (term854 A K _88876 k dom i) = (term842 A K _88876 k dom i).
Proof. exact (TRANS (@lem6783382 A K _88876 k dom i) (@lem6783383 A K _88876 k dom i)). Qed.
Lemma lem6783385 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (term856 A K _88876 k dom) = (term844 A K _88876 k dom).
Proof. exact (fun_ext (fun i : type792 A K => @lem6783384 A K _88876 k dom i)). Qed.
Lemma lem6783386 {A K : Type'} : (@ex ((K -> A) -> A -> K -> K)) = (@ex ((K -> A) -> A -> K -> K)).
Proof. exact (eq_refl (@ex ((K -> A) -> A -> K -> K))). Qed.
Lemma lem6783387 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (term857 A K _88876 k dom) = (term845 A K _88876 k dom).
Proof. exact (MK_COMB (@lem6783386 A K) (@lem6783385 A K _88876 k dom)). Qed.
Lemma lem6783388 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (term858 A K _88876 k) = (term846 A K _88876 k).
Proof. exact (fun_ext (fun dom : A -> Prop => @lem6783387 A K _88876 k dom)). Qed.
Lemma lem6783389 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6783390 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (term850 A K _88876 k) = (term847 A K _88876 k).
Proof. exact (MK_COMB (@lem6783389 A) (@lem6783388 A K _88876 k)). Qed.
Lemma lem6783391 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6783392 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (term859 A K _88876 k) = (term860 A K _88876 k).
Proof. exact (MK_COMB (@lem6783391) (@lem6783390 A K _88876 k)). Qed.
Lemma lem6783393 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (term853 A K _88876 k dom) = (term844 A K _88876 k dom).
Proof. exact (eq_refl (term853 A K _88876 k dom)). Qed.
Lemma lem6783394 {A K : Type'} (i : type649 A K) (dom : A -> Prop) : (i dom) = (i dom).
Proof. exact (eq_refl (i dom)). Qed.
Lemma lem6783395 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (i : type649 A K) (dom : A -> Prop) : (term861 A K _88876 k i dom) = (term862 A K _88876 k i dom).
Proof. exact (MK_COMB (@lem6783393 A K _88876 k dom) (@lem6783394 A K i dom)). Qed.
Lemma lem6783396 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (i : type649 A K) (dom : A -> Prop) : (term862 A K _88876 k i dom) = (term863 A K _88876 k i dom).
Proof. exact (eq_refl (term862 A K _88876 k i dom)). Qed.
Lemma lem6783397 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (i : type649 A K) (dom : A -> Prop) : (term861 A K _88876 k i dom) = (term863 A K _88876 k i dom).
Proof. exact (TRANS (@lem6783395 A K _88876 k i dom) (@lem6783396 A K _88876 k i dom)). Qed.
Lemma lem6783398 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (i : type649 A K) : (term864 A K _88876 k i) = (term865 A K _88876 k i).
Proof. exact (fun_ext (fun dom : A -> Prop => @lem6783397 A K _88876 k i dom)). Qed.
Lemma lem6783399 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6783400 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (i : type649 A K) : (term866 A K _88876 k i) = (term867 A K _88876 k i).
Proof. exact (MK_COMB (@lem6783399 A) (@lem6783398 A K _88876 k i)). Qed.
Lemma lem6783401 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (term868 A K _88876 k) = (term869 A K _88876 k).
Proof. exact (fun_ext (fun i : type649 A K => @lem6783400 A K _88876 k i)). Qed.
Lemma lem6783402 {A K : Type'} : (@ex ((A -> Prop) -> (K -> A) -> A -> K -> K)) = (@ex ((A -> Prop) -> (K -> A) -> A -> K -> K)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (K -> A) -> A -> K -> K))). Qed.
Lemma lem6783403 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (term851 A K _88876 k) = (term870 A K _88876 k).
Proof. exact (MK_COMB (@lem6783402 A K) (@lem6783401 A K _88876 k)). Qed.
Lemma lem6783404 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : ((term850 A K _88876 k) = (term851 A K _88876 k)) = ((term847 A K _88876 k) = (term870 A K _88876 k)).
Proof. exact (MK_COMB (@lem6783392 A K _88876 k) (@lem6783403 A K _88876 k)). Qed.
Lemma lem6783405 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (term847 A K _88876 k) = (term870 A K _88876 k).
Proof. exact (EQ_MP (@lem6783404 A K _88876 k) (@lem6783379 A K _88876 k)). Qed.
Lemma lem6783406 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (term731 A K _88876 k) = (term870 A K _88876 k).
Proof. exact (TRANS (@lem6783375 A K _88876 k) (@lem6783405 A K _88876 k)). Qed.
Lemma lem6783407 {A K : Type'} (_88876 : type835 A K) : (term738 A K _88876) = (term871 A K _88876).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6783406 A K _88876 k)). Qed.
Lemma lem6783408 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6783409 {A K : Type'} (_88876 : type835 A K) : (term753 A K _88876) = (term872 A K _88876).
Proof. exact (MK_COMB (@lem6783408 K) (@lem6783407 A K _88876)). Qed.
Lemma lem6783411 {A B : Type'} (P : type1413 A B) : (term771 A B P) = (term772 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6783412 {A K : Type'} (P : type819 A K) : (term873 A K P) = (term874 A K P).
Proof. exact (@lem6783411 (K -> Prop) (type649 A K) P). Qed.
Lemma lem6783413 {A K : Type'} (_88876 : type835 A K) : (term875 A K _88876) = (term876 A K _88876).
Proof. exact (@lem6783412 A K (term877 A K _88876)). Qed.
Lemma lem6783414 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (term878 A K _88876 k) = (term869 A K _88876 k).
Proof. exact (eq_refl (term878 A K _88876 k)). Qed.
Lemma lem6783415 {A K : Type'} (i : type649 A K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem6783416 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (i : type649 A K) : (term879 A K _88876 k i) = (term880 A K _88876 k i).
Proof. exact (MK_COMB (@lem6783414 A K _88876 k) (@lem6783415 A K i)). Qed.
Lemma lem6783417 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (i : type649 A K) : (term880 A K _88876 k i) = (term867 A K _88876 k i).
Proof. exact (eq_refl (term880 A K _88876 k i)). Qed.
Lemma lem6783418 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (i : type649 A K) : (term879 A K _88876 k i) = (term867 A K _88876 k i).
Proof. exact (TRANS (@lem6783416 A K _88876 k i) (@lem6783417 A K _88876 k i)). Qed.
Lemma lem6783419 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (term881 A K _88876 k) = (term869 A K _88876 k).
Proof. exact (fun_ext (fun i : type649 A K => @lem6783418 A K _88876 k i)). Qed.
Lemma lem6783420 {A K : Type'} : (@ex ((A -> Prop) -> (K -> A) -> A -> K -> K)) = (@ex ((A -> Prop) -> (K -> A) -> A -> K -> K)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (K -> A) -> A -> K -> K))). Qed.
Lemma lem6783421 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (term882 A K _88876 k) = (term870 A K _88876 k).
Proof. exact (MK_COMB (@lem6783420 A K) (@lem6783419 A K _88876 k)). Qed.
Lemma lem6783422 {A K : Type'} (_88876 : type835 A K) : (term883 A K _88876) = (term871 A K _88876).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6783421 A K _88876 k)). Qed.
Lemma lem6783423 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6783424 {A K : Type'} (_88876 : type835 A K) : (term875 A K _88876) = (term872 A K _88876).
Proof. exact (MK_COMB (@lem6783423 K) (@lem6783422 A K _88876)). Qed.
Lemma lem6783425 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6783426 {A K : Type'} (_88876 : type835 A K) : (term884 A K _88876) = (term885 A K _88876).
Proof. exact (MK_COMB (@lem6783425) (@lem6783424 A K _88876)). Qed.
Lemma lem6783427 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (term878 A K _88876 k) = (term869 A K _88876 k).
Proof. exact (eq_refl (term878 A K _88876 k)). Qed.
Lemma lem6783428 {A K : Type'} (i : type834 A K) (k : K -> Prop) : (i k) = (i k).
Proof. exact (eq_refl (i k)). Qed.
Lemma lem6783429 {A K : Type'} (_88876 : type835 A K) (i : type834 A K) (k : K -> Prop) : (term886 A K _88876 i k) = (term887 A K _88876 i k).
Proof. exact (MK_COMB (@lem6783427 A K _88876 k) (@lem6783428 A K i k)). Qed.
Lemma lem6783430 {A K : Type'} (_88876 : type835 A K) (i : type834 A K) (k : K -> Prop) : (term887 A K _88876 i k) = (term888 A K _88876 i k).
Proof. exact (eq_refl (term887 A K _88876 i k)). Qed.
Lemma lem6783431 {A K : Type'} (_88876 : type835 A K) (i : type834 A K) (k : K -> Prop) : (term886 A K _88876 i k) = (term888 A K _88876 i k).
Proof. exact (TRANS (@lem6783429 A K _88876 i k) (@lem6783430 A K _88876 i k)). Qed.
Lemma lem6783432 {A K : Type'} (_88876 : type835 A K) (i : type834 A K) : (term889 A K _88876 i) = (term890 A K _88876 i).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6783431 A K _88876 i k)). Qed.
Lemma lem6783433 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6783434 {A K : Type'} (_88876 : type835 A K) (i : type834 A K) : (term891 A K _88876 i) = (term892 A K _88876 i).
Proof. exact (MK_COMB (@lem6783433 K) (@lem6783432 A K _88876 i)). Qed.
Lemma lem6783435 {A K : Type'} (_88876 : type835 A K) : (term893 A K _88876) = (term894 A K _88876).
Proof. exact (fun_ext (fun i : type834 A K => @lem6783434 A K _88876 i)). Qed.
Lemma lem6783436 {A K : Type'} : (@ex ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K -> K)) = (@ex ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K -> K)).
Proof. exact (eq_refl (@ex ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K -> K))). Qed.
Lemma lem6783437 {A K : Type'} (_88876 : type835 A K) : (term876 A K _88876) = (term895 A K _88876).
Proof. exact (MK_COMB (@lem6783436 A K) (@lem6783435 A K _88876)). Qed.
Lemma lem6783438 {A K : Type'} (_88876 : type835 A K) : ((term875 A K _88876) = (term876 A K _88876)) = ((term872 A K _88876) = (term895 A K _88876)).
Proof. exact (MK_COMB (@lem6783426 A K _88876) (@lem6783437 A K _88876)). Qed.
Lemma lem6783439 {A K : Type'} (_88876 : type835 A K) : (term872 A K _88876) = (term895 A K _88876).
Proof. exact (EQ_MP (@lem6783438 A K _88876) (@lem6783413 A K _88876)). Qed.
Lemma lem6783440 {A K : Type'} (_88876 : type835 A K) : (term753 A K _88876) = (term895 A K _88876).
Proof. exact (TRANS (@lem6783409 A K _88876) (@lem6783439 A K _88876)). Qed.
Lemma lem6783441 {A K : Type'} (_88876 : type835 A K) : (term750 A K _88876) = (term750 A K _88876).
Proof. exact (eq_refl (term750 A K _88876)). Qed.
Lemma lem6783442 {A K : Type'} (_88876 : type835 A K) : (term754 A K _88876) = (term896 A K _88876).
Proof. exact (MK_COMB (@lem6783441 A K _88876) (@lem6783440 A K _88876)). Qed.
Lemma lem6783444 {A : Type'} (P : Prop) (Q : A -> Prop) : (term897 A P Q) = (term898 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem6783445 {A K : Type'} (P : Prop) (Q : type210 A K) : (term899 A K P Q) = (term900 A K P Q).
Proof. exact (@lem6783444 (type834 A K) P Q). Qed.
Lemma lem6783446 {A K : Type'} (_88876 : type835 A K) : (term901 A K _88876) = (term902 A K _88876).
Proof. exact (@lem6783445 A K (term748 A K _88876) (term894 A K _88876)). Qed.
Lemma lem6783447 {A K : Type'} (_88876 : type835 A K) (i : type834 A K) : (term903 A K _88876 i) = (term892 A K _88876 i).
Proof. exact (eq_refl (term903 A K _88876 i)). Qed.
Lemma lem6783448 {A K : Type'} (_88876 : type835 A K) : (term904 A K _88876) = (term894 A K _88876).
Proof. exact (fun_ext (fun i : type834 A K => @lem6783447 A K _88876 i)). Qed.
Lemma lem6783449 {A K : Type'} : (@ex ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K -> K)) = (@ex ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K -> K)).
Proof. exact (eq_refl (@ex ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K -> K))). Qed.
Lemma lem6783450 {A K : Type'} (_88876 : type835 A K) : (term905 A K _88876) = (term895 A K _88876).
Proof. exact (MK_COMB (@lem6783449 A K) (@lem6783448 A K _88876)). Qed.
Lemma lem6783451 {A K : Type'} (_88876 : type835 A K) : (term750 A K _88876) = (term750 A K _88876).
Proof. exact (eq_refl (term750 A K _88876)). Qed.
Lemma lem6783452 {A K : Type'} (_88876 : type835 A K) : (term901 A K _88876) = (term896 A K _88876).
Proof. exact (MK_COMB (@lem6783451 A K _88876) (@lem6783450 A K _88876)). Qed.
Lemma lem6783453 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6783454 {A K : Type'} (_88876 : type835 A K) : (term906 A K _88876) = (term907 A K _88876).
Proof. exact (MK_COMB (@lem6783453) (@lem6783452 A K _88876)). Qed.
Lemma lem6783455 {A K : Type'} (_88876 : type835 A K) (i : type834 A K) : (term903 A K _88876 i) = (term892 A K _88876 i).
Proof. exact (eq_refl (term903 A K _88876 i)). Qed.
Lemma lem6783456 {A K : Type'} (_88876 : type835 A K) : (term750 A K _88876) = (term750 A K _88876).
Proof. exact (eq_refl (term750 A K _88876)). Qed.
Lemma lem6783457 {A K : Type'} (_88876 : type835 A K) (i : type834 A K) : (term908 A K _88876 i) = (term909 A K _88876 i).
Proof. exact (MK_COMB (@lem6783456 A K _88876) (@lem6783455 A K _88876 i)). Qed.
Lemma lem6783458 {A K : Type'} (_88876 : type835 A K) : (term910 A K _88876) = (term911 A K _88876).
Proof. exact (fun_ext (fun i : type834 A K => @lem6783457 A K _88876 i)). Qed.
Lemma lem6783459 {A K : Type'} : (@ex ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K -> K)) = (@ex ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K -> K)).
Proof. exact (eq_refl (@ex ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K -> K))). Qed.
Lemma lem6783460 {A K : Type'} (_88876 : type835 A K) : (term902 A K _88876) = (term912 A K _88876).
Proof. exact (MK_COMB (@lem6783459 A K) (@lem6783458 A K _88876)). Qed.
Lemma lem6783461 {A K : Type'} (_88876 : type835 A K) : ((term901 A K _88876) = (term902 A K _88876)) = ((term896 A K _88876) = (term912 A K _88876)).
Proof. exact (MK_COMB (@lem6783454 A K _88876) (@lem6783460 A K _88876)). Qed.
Lemma lem6783462 {A K : Type'} (_88876 : type835 A K) : (term896 A K _88876) = (term912 A K _88876).
Proof. exact (EQ_MP (@lem6783461 A K _88876) (@lem6783446 A K _88876)). Qed.
Lemma lem6783463 {A K : Type'} (_88876 : type835 A K) : (term754 A K _88876) = (term912 A K _88876).
Proof. exact (TRANS (@lem6783442 A K _88876) (@lem6783462 A K _88876)). Qed.
Lemma lem6783464 {A K : Type'} (_88876 : type835 A K) : (term640 A K _88876) = (term912 A K _88876).
Proof. exact (TRANS (@lem6783250 A K _88876) (@lem6783463 A K _88876)). Qed.
Lemma lem6783465 {A K : Type'} (_88876 : type835 A K) : (term608 A K _88876) = (term912 A K _88876).
Proof. exact (TRANS (@lem6782483 A K _88876) (@lem6783464 A K _88876)). Qed.
Lemma lem6783466 {A K : Type'} (_88876 : type835 A K) (h1 : term608 A K _88876) : term912 A K _88876.
Proof. exact (EQ_MP (@lem6783465 A K _88876) (@lem6782432 A K _88876 h1)). Qed.
Lemma lem6783471 {A K : Type'} (f : K -> A) (x : K) (neut : A) : (term913 A K f x neut) = ((f x) = neut).
Proof. exact (@lem16933 ((f x) = neut)). Qed.
Lemma lem6783473 {A K : Type'} (dom : A -> Prop) (f : K -> A) (x : K) : (term914 A K dom f x) = (term914 A K dom f x).
Proof. exact (eq_refl (term914 A K dom f x)). Qed.
Lemma lem6783474 {A K : Type'} (dom : A -> Prop) (f : K -> A) (x : K) (neut : A) : (term915 A K dom f x neut) = (term916 A K dom f x neut).
Proof. exact (MK_COMB (@lem6783473 A K dom f x) (@lem6783471 A K f x neut)). Qed.
Lemma lem6783475 {A K : Type'} (dom : A -> Prop) (f : K -> A) (x : K) (neut : A) : (term917 A K dom f x neut) = (term915 A K dom f x neut).
Proof. exact (@lem17045 (term298 A K dom f x) (term309 A K f x neut)). Qed.
Lemma lem6783476 {A K : Type'} (dom : A -> Prop) (f : K -> A) (x : K) (neut : A) : (term917 A K dom f x neut) = (term916 A K dom f x neut).
Proof. exact (TRANS (@lem6783475 A K dom f x neut) (@lem6783474 A K dom f x neut)). Qed.
Lemma lem6783478 {K : Type'} (k : K -> Prop) (x : K) : (term918 K k x) = (term918 K k x).
Proof. exact (eq_refl (term918 K k x)). Qed.
Lemma lem6783479 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (x : K) (neut : A) : (term919 A K k dom f x neut) = (term920 A K k dom f x neut).
Proof. exact (MK_COMB (@lem6783478 K k x) (@lem6783476 A K dom f x neut)). Qed.
Lemma lem6783480 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (x : K) (neut : A) : (term351 A K k dom f x neut) = (term919 A K k dom f x neut).
Proof. exact (@lem17045 (k x) (term310 A K dom f x neut)). Qed.
Lemma lem6783481 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (x : K) (neut : A) : (term351 A K k dom f x neut) = (term920 A K k dom f x neut).
Proof. exact (TRANS (@lem6783480 A K k dom f x neut) (@lem6783479 A K k dom f x neut)). Qed.
Lemma lem6783490 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term431 A K _88875 k dom f neut) = (term431 A K _88875 k dom f neut).
Proof. exact (eq_refl (term431 A K _88875 k dom f neut)). Qed.
Lemma lem6783491 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6783492 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (x : K) (neut : A) : (term921 A K k dom f x neut) = (term922 A K k dom f x neut).
Proof. exact (MK_COMB (@lem6783491) (@lem6783481 A K k dom f x neut)). Qed.
Lemma lem6783493 {A K : Type'} (x : K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term923 A K x _88875 k dom f neut) = (term924 A K x _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6783492 A K k dom f x neut) (@lem6783490 A K _88875 k dom f neut)). Qed.
Lemma lem6783494 {A K : Type'} (x : K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term432 A K x _88875 k dom f neut) = (term923 A K x _88875 k dom f neut).
Proof. exact (@lem17265 (term312 A K k dom f x neut) (term431 A K _88875 k dom f neut)). Qed.
Lemma lem6783495 {A K : Type'} (x : K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term432 A K x _88875 k dom f neut) = (term924 A K x _88875 k dom f neut).
Proof. exact (TRANS (@lem6783494 A K x _88875 k dom f neut) (@lem6783493 A K x _88875 k dom f neut)). Qed.
Lemma lem6783496 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term433 A K _88875 k dom f neut) = (term925 A K _88875 k dom f neut).
Proof. exact (fun_ext (fun x : K => @lem6783495 A K x _88875 k dom f neut)). Qed.
Lemma lem6783497 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6783498 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term434 A K _88875 k dom f neut) = (term926 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6783497 K) (@lem6783496 A K _88875 k dom f neut)). Qed.
Lemma lem6783499 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term436 A K _88875 k dom f) = (term927 A K _88875 k dom f).
Proof. exact (fun_ext (fun neut : A => @lem6783498 A K _88875 k dom f neut)). Qed.
Lemma lem6783500 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6783501 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term437 A K _88875 k dom f) = (term928 A K _88875 k dom f).
Proof. exact (MK_COMB (@lem6783500 A) (@lem6783499 A K _88875 k dom f)). Qed.
Lemma lem6783502 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) : (term439 A K _88875 k dom) = (term929 A K _88875 k dom).
Proof. exact (fun_ext (fun f : K -> A => @lem6783501 A K _88875 k dom f)). Qed.
Lemma lem6783503 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem6783504 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) : (term440 A K _88875 k dom) = (term930 A K _88875 k dom).
Proof. exact (MK_COMB (@lem6783503 A K) (@lem6783502 A K _88875 k dom)). Qed.
Lemma lem6783505 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) : (term442 A K _88875 k) = (term931 A K _88875 k).
Proof. exact (fun_ext (fun dom : A -> Prop => @lem6783504 A K _88875 k dom)). Qed.
Lemma lem6783506 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6783507 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) : (term443 A K _88875 k) = (term932 A K _88875 k).
Proof. exact (MK_COMB (@lem6783506 A) (@lem6783505 A K _88875 k)). Qed.
Lemma lem6783508 {A K : Type'} (_88875 : type836 A K) : (term445 A K _88875) = (term933 A K _88875).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6783507 A K _88875 k)). Qed.
Lemma lem6783509 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6783510 {A K : Type'} (_88875 : type836 A K) : (term446 A K _88875) = (term934 A K _88875).
Proof. exact (MK_COMB (@lem6783509 K) (@lem6783508 A K _88875)). Qed.
Lemma lem6783548 {A : Type'} (P : A -> Prop) (Q : Prop) : (term935 A P Q) = (term936 A P Q).
Proof. exact (EQ_MP (@lem18947 A P Q) (@lem18946 A P Q)). Qed.
Lemma lem6783549 {K : Type'} (P : K -> Prop) (Q : Prop) : (term935 K P Q) = (term936 K P Q).
Proof. exact (@lem6783548 K P Q). Qed.
Lemma lem6783550 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term937 A K _88875 k dom f neut) = (term938 A K _88875 k dom f neut).
Proof. exact (@lem6783549 K (term939 A K k dom f neut) (term431 A K _88875 k dom f neut)). Qed.
Lemma lem6783551 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (x : K) (neut : A) : (term940 A K k dom f neut x) = (term920 A K k dom f x neut).
Proof. exact (eq_refl (term940 A K k dom f neut x)). Qed.
Lemma lem6783552 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6783553 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (x : K) (neut : A) : (term941 A K k dom f neut x) = (term922 A K k dom f x neut).
Proof. exact (MK_COMB (@lem6783552) (@lem6783551 A K k dom f x neut)). Qed.
Lemma lem6783554 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term431 A K _88875 k dom f neut) = (term431 A K _88875 k dom f neut).
Proof. exact (eq_refl (term431 A K _88875 k dom f neut)). Qed.
Lemma lem6783555 {A K : Type'} (x : K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term942 A K x _88875 k dom f neut) = (term924 A K x _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6783553 A K k dom f x neut) (@lem6783554 A K _88875 k dom f neut)). Qed.
Lemma lem6783556 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term943 A K _88875 k dom f neut) = (term925 A K _88875 k dom f neut).
Proof. exact (fun_ext (fun x : K => @lem6783555 A K x _88875 k dom f neut)). Qed.
Lemma lem6783557 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6783558 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term937 A K _88875 k dom f neut) = (term926 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6783557 K) (@lem6783556 A K _88875 k dom f neut)). Qed.
Lemma lem6783559 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6783560 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term944 A K _88875 k dom f neut) = (term945 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6783559) (@lem6783558 A K _88875 k dom f neut)). Qed.
Lemma lem6783561 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (x : K) (neut : A) : (term940 A K k dom f neut x) = (term920 A K k dom f x neut).
Proof. exact (eq_refl (term940 A K k dom f neut x)). Qed.
Lemma lem6783562 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term946 A K k dom f neut) = (term939 A K k dom f neut).
Proof. exact (fun_ext (fun x : K => @lem6783561 A K k dom f x neut)). Qed.
Lemma lem6783563 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6783564 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term947 A K k dom f neut) = (term948 A K k dom f neut).
Proof. exact (MK_COMB (@lem6783563 K) (@lem6783562 A K k dom f neut)). Qed.
Lemma lem6783565 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6783566 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term949 A K k dom f neut) = (term950 A K k dom f neut).
Proof. exact (MK_COMB (@lem6783565) (@lem6783564 A K k dom f neut)). Qed.
Lemma lem6783567 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term431 A K _88875 k dom f neut) = (term431 A K _88875 k dom f neut).
Proof. exact (eq_refl (term431 A K _88875 k dom f neut)). Qed.
Lemma lem6783568 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term938 A K _88875 k dom f neut) = (term951 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6783566 A K k dom f neut) (@lem6783567 A K _88875 k dom f neut)). Qed.
Lemma lem6783569 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : ((term937 A K _88875 k dom f neut) = (term938 A K _88875 k dom f neut)) = ((term926 A K _88875 k dom f neut) = (term951 A K _88875 k dom f neut)).
Proof. exact (MK_COMB (@lem6783560 A K _88875 k dom f neut) (@lem6783568 A K _88875 k dom f neut)). Qed.
Lemma lem6783570 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term926 A K _88875 k dom f neut) = (term951 A K _88875 k dom f neut).
Proof. exact (EQ_MP (@lem6783569 A K _88875 k dom f neut) (@lem6783550 A K _88875 k dom f neut)). Qed.
Lemma lem6783619 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term927 A K _88875 k dom f) = (term952 A K _88875 k dom f).
Proof. exact (fun_ext (fun neut : A => @lem6783570 A K _88875 k dom f neut)). Qed.
Lemma lem6783620 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6783621 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term928 A K _88875 k dom f) = (term953 A K _88875 k dom f).
Proof. exact (MK_COMB (@lem6783620 A) (@lem6783619 A K _88875 k dom f)). Qed.
Lemma lem6783670 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) : (term929 A K _88875 k dom) = (term954 A K _88875 k dom).
Proof. exact (fun_ext (fun f : K -> A => @lem6783621 A K _88875 k dom f)). Qed.
Lemma lem6783671 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem6783672 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) : (term930 A K _88875 k dom) = (term955 A K _88875 k dom).
Proof. exact (MK_COMB (@lem6783671 A K) (@lem6783670 A K _88875 k dom)). Qed.
Lemma lem6783677 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) : (term931 A K _88875 k) = (term956 A K _88875 k).
Proof. exact (fun_ext (fun dom : A -> Prop => @lem6783672 A K _88875 k dom)). Qed.
Lemma lem6783678 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6783679 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) : (term932 A K _88875 k) = (term957 A K _88875 k).
Proof. exact (MK_COMB (@lem6783678 A) (@lem6783677 A K _88875 k)). Qed.
Lemma lem6783684 {A K : Type'} (_88875 : type836 A K) : (term933 A K _88875) = (term958 A K _88875).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6783679 A K _88875 k)). Qed.
Lemma lem6783685 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6783692 {A K : Type'} (_88875 : type836 A K) : (term934 A K _88875) = (term959 A K _88875).
Proof. exact (MK_COMB (@lem6783685 K) (@lem6783684 A K _88875)). Qed.
Lemma lem6783693 {A K : Type'} (_88875 : type836 A K) : (term446 A K _88875) = (term959 A K _88875).
Proof. exact (TRANS (@lem6783510 A K _88875) (@lem6783692 A K _88875)). Qed.
Lemma lem6783694 {A K : Type'} (_88875 : type836 A K) (h1 : term446 A K _88875) : term959 A K _88875.
Proof. exact (EQ_MP (@lem6783693 A K _88875) (@lem6782433 A K _88875 h1)). Qed.
Lemma lem6783699 {A K : Type'} (f : K -> A) (i : K) (neut : A) : (term913 A K f i neut) = ((f i) = neut).
Proof. exact (@lem16933 ((f i) = neut)). Qed.
Lemma lem6783701 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) : (term914 A K dom f i) = (term914 A K dom f i).
Proof. exact (eq_refl (term914 A K dom f i)). Qed.
Lemma lem6783702 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term915 A K dom f i neut) = (term916 A K dom f i neut).
Proof. exact (MK_COMB (@lem6783701 A K dom f i) (@lem6783699 A K f i neut)). Qed.
Lemma lem6783703 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term917 A K dom f i neut) = (term915 A K dom f i neut).
Proof. exact (@lem17045 (term298 A K dom f i) (term309 A K f i neut)). Qed.
Lemma lem6783704 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term917 A K dom f i neut) = (term916 A K dom f i neut).
Proof. exact (TRANS (@lem6783703 A K dom f i neut) (@lem6783702 A K dom f i neut)). Qed.
Lemma lem6783723 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i' : K) (i : K) : (term960 A K ltle k dom f neut i' i) = (term961 A K ltle k dom f neut i' i).
Proof. exact (@lem17362 (term314 A K ltle i k dom f i' neut) (i' = i)). Qed.
Lemma lem6783724 {K : Type'} (P : K -> Prop) : (term962 K P) = (term963 K P).
Proof. exact (@lem18392 K P). Qed.
Lemma lem6783725 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term964 A K ltle k dom f neut i) = (term965 A K ltle k dom f neut i).
Proof. exact (@lem6783724 K (term320 A K ltle k dom f neut i)). Qed.
Lemma lem6783726 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i' : K) (i : K) : (term966 A K ltle k dom f neut i i') = (term318 A K ltle k dom f neut i' i).
Proof. exact (eq_refl (term966 A K ltle k dom f neut i i')). Qed.
Lemma lem6783727 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6783728 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i' : K) (i : K) : (term967 A K ltle k dom f neut i i') = (term960 A K ltle k dom f neut i' i).
Proof. exact (MK_COMB (@lem6783727) (@lem6783726 A K ltle k dom f neut i' i)). Qed.
Lemma lem6783729 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i' : K) (i : K) : (term967 A K ltle k dom f neut i i') = (term961 A K ltle k dom f neut i' i).
Proof. exact (TRANS (@lem6783728 A K ltle k dom f neut i' i) (@lem6783723 A K ltle k dom f neut i' i)). Qed.
Lemma lem6783730 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term968 A K ltle k dom f neut i) = (term969 A K ltle k dom f neut i).
Proof. exact (fun_ext (fun i' : K => @lem6783729 A K ltle k dom f neut i' i)). Qed.
Lemma lem6783731 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem6783732 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term965 A K ltle k dom f neut i) = (term970 A K ltle k dom f neut i).
Proof. exact (MK_COMB (@lem6783731 K) (@lem6783730 A K ltle k dom f neut i)). Qed.
Lemma lem6783733 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term964 A K ltle k dom f neut i) = (term970 A K ltle k dom f neut i).
Proof. exact (TRANS (@lem6783725 A K ltle k dom f neut i) (@lem6783732 A K ltle k dom f neut i)). Qed.
Lemma lem6783734 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6783735 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term971 A K dom f i neut) = (term972 A K dom f i neut).
Proof. exact (MK_COMB (@lem6783734) (@lem6783704 A K dom f i neut)). Qed.
Lemma lem6783736 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term973 A K ltle k dom f neut i) = (term974 A K ltle k dom f neut i).
Proof. exact (MK_COMB (@lem6783735 A K dom f i neut) (@lem6783733 A K ltle k dom f neut i)). Qed.
Lemma lem6783737 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term975 A K ltle k dom f neut i) = (term973 A K ltle k dom f neut i).
Proof. exact (@lem17045 (term310 A K dom f i neut) (term322 A K ltle k dom f neut i)). Qed.
Lemma lem6783738 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term975 A K ltle k dom f neut i) = (term974 A K ltle k dom f neut i).
Proof. exact (TRANS (@lem6783737 A K ltle k dom f neut i) (@lem6783736 A K ltle k dom f neut i)). Qed.
Lemma lem6783740 {K : Type'} (k : K -> Prop) (i : K) : (term918 K k i) = (term918 K k i).
Proof. exact (eq_refl (term918 K k i)). Qed.
Lemma lem6783741 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term976 A K ltle k dom f neut i) = (term977 A K ltle k dom f neut i).
Proof. exact (MK_COMB (@lem6783740 K k i) (@lem6783738 A K ltle k dom f neut i)). Qed.
Lemma lem6783742 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term978 A K ltle k dom f neut i) = (term976 A K ltle k dom f neut i).
Proof. exact (@lem17045 (k i) (term324 A K ltle k dom f neut i)). Qed.
Lemma lem6783743 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term978 A K ltle k dom f neut i) = (term977 A K ltle k dom f neut i).
Proof. exact (TRANS (@lem6783742 A K ltle k dom f neut i) (@lem6783741 A K ltle k dom f neut i)). Qed.
Lemma lem6783744 {K : Type'} (P : K -> Prop) : (term30 K P) = (term31 K P).
Proof. exact (@lem18394 K P). Qed.
Lemma lem6783745 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term330 A K ltle k dom f neut) = (term979 A K ltle k dom f neut).
Proof. exact (@lem6783744 K (term328 A K ltle k dom f neut)). Qed.
Lemma lem6783746 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term980 A K ltle k dom f neut i) = (term326 A K ltle k dom f neut i).
Proof. exact (eq_refl (term980 A K ltle k dom f neut i)). Qed.
Lemma lem6783747 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6783748 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term981 A K ltle k dom f neut i) = (term978 A K ltle k dom f neut i).
Proof. exact (MK_COMB (@lem6783747) (@lem6783746 A K ltle k dom f neut i)). Qed.
Lemma lem6783749 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term981 A K ltle k dom f neut i) = (term977 A K ltle k dom f neut i).
Proof. exact (TRANS (@lem6783748 A K ltle k dom f neut i) (@lem6783743 A K ltle k dom f neut i)). Qed.
Lemma lem6783750 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term982 A K ltle k dom f neut) = (term983 A K ltle k dom f neut).
Proof. exact (fun_ext (fun i : K => @lem6783749 A K ltle k dom f neut i)). Qed.
Lemma lem6783751 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6783752 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term979 A K ltle k dom f neut) = (term984 A K ltle k dom f neut).
Proof. exact (MK_COMB (@lem6783751 K) (@lem6783750 A K ltle k dom f neut)). Qed.
Lemma lem6783753 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term330 A K ltle k dom f neut) = (term984 A K ltle k dom f neut).
Proof. exact (TRANS (@lem6783745 A K ltle k dom f neut) (@lem6783752 A K ltle k dom f neut)). Qed.
Lemma lem6783764 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (x : K) (neut : A) : (term985 A K k dom f x neut) = (term312 A K k dom f x neut).
Proof. exact (@lem16933 (term312 A K k dom f x neut)). Qed.
Lemma lem6783765 {K : Type'} (P : K -> Prop) : (term962 K P) = (term963 K P).
Proof. exact (@lem18392 K P). Qed.
Lemma lem6783766 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term355 A K k dom f neut) = (term986 A K k dom f neut).
Proof. exact (@lem6783765 K (term353 A K k dom f neut)). Qed.
Lemma lem6783767 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (x : K) (neut : A) : (term987 A K k dom f neut x) = (term351 A K k dom f x neut).
Proof. exact (eq_refl (term987 A K k dom f neut x)). Qed.
Lemma lem6783768 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6783769 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (x : K) (neut : A) : (term988 A K k dom f neut x) = (term985 A K k dom f x neut).
Proof. exact (MK_COMB (@lem6783768) (@lem6783767 A K k dom f x neut)). Qed.
Lemma lem6783770 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (x : K) (neut : A) : (term988 A K k dom f neut x) = (term312 A K k dom f x neut).
Proof. exact (TRANS (@lem6783769 A K k dom f x neut) (@lem6783764 A K k dom f x neut)). Qed.
Lemma lem6783771 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term989 A K k dom f neut) = (term367 A K k dom f neut).
Proof. exact (fun_ext (fun x : K => @lem6783770 A K k dom f x neut)). Qed.
Lemma lem6783772 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem6783773 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term986 A K k dom f neut) = (term990 A K k dom f neut).
Proof. exact (MK_COMB (@lem6783772 K) (@lem6783771 A K k dom f neut)). Qed.
Lemma lem6783774 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term355 A K k dom f neut) = (term990 A K k dom f neut).
Proof. exact (TRANS (@lem6783766 A K k dom f neut) (@lem6783773 A K k dom f neut)). Qed.
Lemma lem6783775 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term511 A K _88876 k dom f neut) = (term511 A K _88876 k dom f neut).
Proof. exact (eq_refl (term511 A K _88876 k dom f neut)). Qed.
Lemma lem6783776 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6783777 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term356 A K k dom f neut) = (term991 A K k dom f neut).
Proof. exact (MK_COMB (@lem6783776) (@lem6783774 A K k dom f neut)). Qed.
Lemma lem6783778 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term512 A K _88876 k dom f neut) = (term992 A K _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6783777 A K k dom f neut) (@lem6783775 A K _88876 k dom f neut)). Qed.
Lemma lem6783779 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6783780 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term331 A K ltle k dom f neut) = (term993 A K ltle k dom f neut).
Proof. exact (MK_COMB (@lem6783779) (@lem6783753 A K ltle k dom f neut)). Qed.
Lemma lem6783781 {A K : Type'} (ltle : type1402 K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term513 A K ltle _88876 k dom f neut) = (term994 A K ltle _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6783780 A K ltle k dom f neut) (@lem6783778 A K _88876 k dom f neut)). Qed.
Lemma lem6783908 {A : Type'} (P : Prop) (Q : A -> Prop) : (term755 A P Q) = (term756 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6783909 {K : Type'} (P : Prop) (Q : K -> Prop) : (term755 K P Q) = (term756 K P Q).
Proof. exact (@lem6783908 K P Q). Qed.
Lemma lem6783910 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term995 A K ltle k dom f neut i) = (term996 A K ltle k dom f neut i).
Proof. exact (@lem6783909 K (term916 A K dom f i neut) (term969 A K ltle k dom f neut i)). Qed.
Lemma lem6783911 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i' : K) (i : K) : (term997 A K ltle k dom f neut i i') = (term961 A K ltle k dom f neut i' i).
Proof. exact (eq_refl (term997 A K ltle k dom f neut i i')). Qed.
Lemma lem6783912 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term998 A K ltle k dom f neut i) = (term969 A K ltle k dom f neut i).
Proof. exact (fun_ext (fun i' : K => @lem6783911 A K ltle k dom f neut i' i)). Qed.
Lemma lem6783913 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem6783914 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term999 A K ltle k dom f neut i) = (term970 A K ltle k dom f neut i).
Proof. exact (MK_COMB (@lem6783913 K) (@lem6783912 A K ltle k dom f neut i)). Qed.
Lemma lem6783915 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term972 A K dom f i neut) = (term972 A K dom f i neut).
Proof. exact (eq_refl (term972 A K dom f i neut)). Qed.
Lemma lem6783916 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term995 A K ltle k dom f neut i) = (term974 A K ltle k dom f neut i).
Proof. exact (MK_COMB (@lem6783915 A K dom f i neut) (@lem6783914 A K ltle k dom f neut i)). Qed.
Lemma lem6783917 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6783918 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term1000 A K ltle k dom f neut i) = (term1001 A K ltle k dom f neut i).
Proof. exact (MK_COMB (@lem6783917) (@lem6783916 A K ltle k dom f neut i)). Qed.
Lemma lem6783919 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i' : K) (i : K) : (term997 A K ltle k dom f neut i i') = (term961 A K ltle k dom f neut i' i).
Proof. exact (eq_refl (term997 A K ltle k dom f neut i i')). Qed.
Lemma lem6783920 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term972 A K dom f i neut) = (term972 A K dom f i neut).
Proof. exact (eq_refl (term972 A K dom f i neut)). Qed.
Lemma lem6783921 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i' : K) (i : K) : (term1002 A K ltle k dom f neut i i') = (term1003 A K ltle k dom f neut i' i).
Proof. exact (MK_COMB (@lem6783920 A K dom f i neut) (@lem6783919 A K ltle k dom f neut i' i)). Qed.
Lemma lem6783922 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term1004 A K ltle k dom f neut i) = (term1005 A K ltle k dom f neut i).
Proof. exact (fun_ext (fun i' : K => @lem6783921 A K ltle k dom f neut i' i)). Qed.
Lemma lem6783923 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem6783924 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term996 A K ltle k dom f neut i) = (term1006 A K ltle k dom f neut i).
Proof. exact (MK_COMB (@lem6783923 K) (@lem6783922 A K ltle k dom f neut i)). Qed.
Lemma lem6783925 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : ((term995 A K ltle k dom f neut i) = (term996 A K ltle k dom f neut i)) = ((term974 A K ltle k dom f neut i) = (term1006 A K ltle k dom f neut i)).
Proof. exact (MK_COMB (@lem6783918 A K ltle k dom f neut i) (@lem6783924 A K ltle k dom f neut i)). Qed.
Lemma lem6783926 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term974 A K ltle k dom f neut i) = (term1006 A K ltle k dom f neut i).
Proof. exact (EQ_MP (@lem6783925 A K ltle k dom f neut i) (@lem6783910 A K ltle k dom f neut i)). Qed.
Lemma lem6783927 {K : Type'} (k : K -> Prop) (i : K) : (term918 K k i) = (term918 K k i).
Proof. exact (eq_refl (term918 K k i)). Qed.
Lemma lem6783928 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term977 A K ltle k dom f neut i) = (term1007 A K ltle k dom f neut i).
Proof. exact (MK_COMB (@lem6783927 K k i) (@lem6783926 A K ltle k dom f neut i)). Qed.
Lemma lem6783930 {A : Type'} (P : Prop) (Q : A -> Prop) : (term755 A P Q) = (term756 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6783931 {K : Type'} (P : Prop) (Q : K -> Prop) : (term755 K P Q) = (term756 K P Q).
Proof. exact (@lem6783930 K P Q). Qed.
Lemma lem6783932 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term1008 A K ltle k dom f neut i) = (term1009 A K ltle k dom f neut i).
Proof. exact (@lem6783931 K (term35 K k i) (term1005 A K ltle k dom f neut i)). Qed.
Lemma lem6783933 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i' : K) (i : K) : (term1010 A K ltle k dom f neut i i') = (term1003 A K ltle k dom f neut i' i).
Proof. exact (eq_refl (term1010 A K ltle k dom f neut i i')). Qed.
Lemma lem6783934 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term1011 A K ltle k dom f neut i) = (term1005 A K ltle k dom f neut i).
Proof. exact (fun_ext (fun i' : K => @lem6783933 A K ltle k dom f neut i' i)). Qed.
Lemma lem6783935 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem6783936 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term1012 A K ltle k dom f neut i) = (term1006 A K ltle k dom f neut i).
Proof. exact (MK_COMB (@lem6783935 K) (@lem6783934 A K ltle k dom f neut i)). Qed.
Lemma lem6783937 {K : Type'} (k : K -> Prop) (i : K) : (term918 K k i) = (term918 K k i).
Proof. exact (eq_refl (term918 K k i)). Qed.
Lemma lem6783938 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term1008 A K ltle k dom f neut i) = (term1007 A K ltle k dom f neut i).
Proof. exact (MK_COMB (@lem6783937 K k i) (@lem6783936 A K ltle k dom f neut i)). Qed.
Lemma lem6783939 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6783940 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term1013 A K ltle k dom f neut i) = (term1014 A K ltle k dom f neut i).
Proof. exact (MK_COMB (@lem6783939) (@lem6783938 A K ltle k dom f neut i)). Qed.
Lemma lem6783941 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i' : K) (i : K) : (term1010 A K ltle k dom f neut i i') = (term1003 A K ltle k dom f neut i' i).
Proof. exact (eq_refl (term1010 A K ltle k dom f neut i i')). Qed.
Lemma lem6783942 {K : Type'} (k : K -> Prop) (i : K) : (term918 K k i) = (term918 K k i).
Proof. exact (eq_refl (term918 K k i)). Qed.
Lemma lem6783943 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i' : K) (i : K) : (term1015 A K ltle k dom f neut i i') = (term1016 A K ltle k dom f neut i' i).
Proof. exact (MK_COMB (@lem6783942 K k i) (@lem6783941 A K ltle k dom f neut i' i)). Qed.
Lemma lem6783944 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term1017 A K ltle k dom f neut i) = (term1018 A K ltle k dom f neut i).
Proof. exact (fun_ext (fun i' : K => @lem6783943 A K ltle k dom f neut i' i)). Qed.
Lemma lem6783945 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem6783946 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term1009 A K ltle k dom f neut i) = (term1019 A K ltle k dom f neut i).
Proof. exact (MK_COMB (@lem6783945 K) (@lem6783944 A K ltle k dom f neut i)). Qed.
Lemma lem6783947 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : ((term1008 A K ltle k dom f neut i) = (term1009 A K ltle k dom f neut i)) = ((term1007 A K ltle k dom f neut i) = (term1019 A K ltle k dom f neut i)).
Proof. exact (MK_COMB (@lem6783940 A K ltle k dom f neut i) (@lem6783946 A K ltle k dom f neut i)). Qed.
Lemma lem6783948 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term1007 A K ltle k dom f neut i) = (term1019 A K ltle k dom f neut i).
Proof. exact (EQ_MP (@lem6783947 A K ltle k dom f neut i) (@lem6783932 A K ltle k dom f neut i)). Qed.
Lemma lem6783949 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term977 A K ltle k dom f neut i) = (term1019 A K ltle k dom f neut i).
Proof. exact (TRANS (@lem6783928 A K ltle k dom f neut i) (@lem6783948 A K ltle k dom f neut i)). Qed.
Lemma lem6783950 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term983 A K ltle k dom f neut) = (term1020 A K ltle k dom f neut).
Proof. exact (fun_ext (fun i : K => @lem6783949 A K ltle k dom f neut i)). Qed.
Lemma lem6783951 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6783952 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term984 A K ltle k dom f neut) = (term1021 A K ltle k dom f neut).
Proof. exact (MK_COMB (@lem6783951 K) (@lem6783950 A K ltle k dom f neut)). Qed.
Lemma lem6783954 {A B : Type'} (P : type1413 A B) : (term771 A B P) = (term772 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6783955 {K : Type'} (P : type1402 K) : (term773 K P) = (term774 K P).
Proof. exact (@lem6783954 K K P). Qed.
Lemma lem6783956 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1022 A K ltle k dom f neut) = (term1023 A K ltle k dom f neut).
Proof. exact (@lem6783955 K (term1024 A K ltle k dom f neut)). Qed.
Lemma lem6783957 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term1025 A K ltle k dom f neut i) = (term1018 A K ltle k dom f neut i).
Proof. exact (eq_refl (term1025 A K ltle k dom f neut i)). Qed.
Lemma lem6783958 {K : Type'} (i' : K) : i' = i'.
Proof. exact (eq_refl i'). Qed.
Lemma lem6783959 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (i' : K) : (term1026 A K ltle k dom f neut i i') = (term1027 A K ltle k dom f neut i i').
Proof. exact (MK_COMB (@lem6783957 A K ltle k dom f neut i) (@lem6783958 K i')). Qed.
Lemma lem6783960 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i' : K) (i : K) : (term1027 A K ltle k dom f neut i i') = (term1016 A K ltle k dom f neut i' i).
Proof. exact (eq_refl (term1027 A K ltle k dom f neut i i')). Qed.
Lemma lem6783961 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i' : K) (i : K) : (term1026 A K ltle k dom f neut i i') = (term1016 A K ltle k dom f neut i' i).
Proof. exact (TRANS (@lem6783959 A K ltle k dom f neut i i') (@lem6783960 A K ltle k dom f neut i' i)). Qed.
Lemma lem6783962 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term1028 A K ltle k dom f neut i) = (term1018 A K ltle k dom f neut i).
Proof. exact (fun_ext (fun i' : K => @lem6783961 A K ltle k dom f neut i' i)). Qed.
Lemma lem6783963 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem6783964 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term1029 A K ltle k dom f neut i) = (term1019 A K ltle k dom f neut i).
Proof. exact (MK_COMB (@lem6783963 K) (@lem6783962 A K ltle k dom f neut i)). Qed.
Lemma lem6783965 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1030 A K ltle k dom f neut) = (term1020 A K ltle k dom f neut).
Proof. exact (fun_ext (fun i : K => @lem6783964 A K ltle k dom f neut i)). Qed.
Lemma lem6783966 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6783967 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1022 A K ltle k dom f neut) = (term1021 A K ltle k dom f neut).
Proof. exact (MK_COMB (@lem6783966 K) (@lem6783965 A K ltle k dom f neut)). Qed.
Lemma lem6783968 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6783969 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1031 A K ltle k dom f neut) = (term1032 A K ltle k dom f neut).
Proof. exact (MK_COMB (@lem6783968) (@lem6783967 A K ltle k dom f neut)). Qed.
Lemma lem6783970 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term1025 A K ltle k dom f neut i) = (term1018 A K ltle k dom f neut i).
Proof. exact (eq_refl (term1025 A K ltle k dom f neut i)). Qed.
Lemma lem6783971 {K : Type'} (i' : K -> K) (i : K) : (i' i) = (i' i).
Proof. exact (eq_refl (i' i)). Qed.
Lemma lem6783972 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i' : K -> K) (i : K) : (term1033 A K ltle k dom f neut i' i) = (term1034 A K ltle k dom f neut i' i).
Proof. exact (MK_COMB (@lem6783970 A K ltle k dom f neut i) (@lem6783971 K i' i)). Qed.
Lemma lem6783973 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i' : K -> K) (i : K) : (term1034 A K ltle k dom f neut i' i) = (term1035 A K ltle k dom f neut i' i).
Proof. exact (eq_refl (term1034 A K ltle k dom f neut i' i)). Qed.
Lemma lem6783974 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i' : K -> K) (i : K) : (term1033 A K ltle k dom f neut i' i) = (term1035 A K ltle k dom f neut i' i).
Proof. exact (TRANS (@lem6783972 A K ltle k dom f neut i' i) (@lem6783973 A K ltle k dom f neut i' i)). Qed.
Lemma lem6783975 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i' : K -> K) : (term1036 A K ltle k dom f neut i') = (term1037 A K ltle k dom f neut i').
Proof. exact (fun_ext (fun i : K => @lem6783974 A K ltle k dom f neut i' i)). Qed.
Lemma lem6783976 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6783977 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i' : K -> K) : (term1038 A K ltle k dom f neut i') = (term1039 A K ltle k dom f neut i').
Proof. exact (MK_COMB (@lem6783976 K) (@lem6783975 A K ltle k dom f neut i')). Qed.
Lemma lem6783978 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1040 A K ltle k dom f neut) = (term1041 A K ltle k dom f neut).
Proof. exact (fun_ext (fun i' : K -> K => @lem6783977 A K ltle k dom f neut i')). Qed.
Lemma lem6783979 {K : Type'} : (@ex (K -> K)) = (@ex (K -> K)).
Proof. exact (eq_refl (@ex (K -> K))). Qed.
Lemma lem6783980 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1023 A K ltle k dom f neut) = (term1042 A K ltle k dom f neut).
Proof. exact (MK_COMB (@lem6783979 K) (@lem6783978 A K ltle k dom f neut)). Qed.
Lemma lem6783981 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : ((term1022 A K ltle k dom f neut) = (term1023 A K ltle k dom f neut)) = ((term1021 A K ltle k dom f neut) = (term1042 A K ltle k dom f neut)).
Proof. exact (MK_COMB (@lem6783969 A K ltle k dom f neut) (@lem6783980 A K ltle k dom f neut)). Qed.
Lemma lem6783982 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1021 A K ltle k dom f neut) = (term1042 A K ltle k dom f neut).
Proof. exact (EQ_MP (@lem6783981 A K ltle k dom f neut) (@lem6783956 A K ltle k dom f neut)). Qed.
Lemma lem6783983 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term984 A K ltle k dom f neut) = (term1042 A K ltle k dom f neut).
Proof. exact (TRANS (@lem6783952 A K ltle k dom f neut) (@lem6783982 A K ltle k dom f neut)). Qed.
Lemma lem6783984 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6783985 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term993 A K ltle k dom f neut) = (term1043 A K ltle k dom f neut).
Proof. exact (MK_COMB (@lem6783984) (@lem6783983 A K ltle k dom f neut)). Qed.
Lemma lem6783987 {A : Type'} (P : A -> Prop) (Q : Prop) : (term1044 A P Q) = (term1045 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem6783988 {K : Type'} (P : K -> Prop) (Q : Prop) : (term1044 K P Q) = (term1045 K P Q).
Proof. exact (@lem6783987 K P Q). Qed.
Lemma lem6783989 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1046 A K _88876 k dom f neut) = (term1047 A K _88876 k dom f neut).
Proof. exact (@lem6783988 K (term367 A K k dom f neut) (term511 A K _88876 k dom f neut)). Qed.
Lemma lem6783990 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (x : K) (neut : A) : (term381 A K k dom f neut x) = (term312 A K k dom f x neut).
Proof. exact (eq_refl (term381 A K k dom f neut x)). Qed.
Lemma lem6783991 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1048 A K k dom f neut) = (term367 A K k dom f neut).
Proof. exact (fun_ext (fun x : K => @lem6783990 A K k dom f x neut)). Qed.
Lemma lem6783992 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem6783993 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1049 A K k dom f neut) = (term990 A K k dom f neut).
Proof. exact (MK_COMB (@lem6783992 K) (@lem6783991 A K k dom f neut)). Qed.
Lemma lem6783994 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6783995 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1050 A K k dom f neut) = (term991 A K k dom f neut).
Proof. exact (MK_COMB (@lem6783994) (@lem6783993 A K k dom f neut)). Qed.
Lemma lem6783996 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term511 A K _88876 k dom f neut) = (term511 A K _88876 k dom f neut).
Proof. exact (eq_refl (term511 A K _88876 k dom f neut)). Qed.
Lemma lem6783997 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1046 A K _88876 k dom f neut) = (term992 A K _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6783995 A K k dom f neut) (@lem6783996 A K _88876 k dom f neut)). Qed.
Lemma lem6783998 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6783999 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1051 A K _88876 k dom f neut) = (term1052 A K _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6783998) (@lem6783997 A K _88876 k dom f neut)). Qed.
Lemma lem6784000 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (x : K) (neut : A) : (term381 A K k dom f neut x) = (term312 A K k dom f x neut).
Proof. exact (eq_refl (term381 A K k dom f neut x)). Qed.
Lemma lem6784001 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6784002 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (x : K) (neut : A) : (term1053 A K k dom f neut x) = (term1054 A K k dom f x neut).
Proof. exact (MK_COMB (@lem6784001) (@lem6784000 A K k dom f x neut)). Qed.
Lemma lem6784003 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term511 A K _88876 k dom f neut) = (term511 A K _88876 k dom f neut).
Proof. exact (eq_refl (term511 A K _88876 k dom f neut)). Qed.
Lemma lem6784004 {A K : Type'} (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1055 A K x _88876 k dom f neut) = (term1056 A K x _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6784002 A K k dom f x neut) (@lem6784003 A K _88876 k dom f neut)). Qed.
Lemma lem6784005 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1057 A K _88876 k dom f neut) = (term1058 A K _88876 k dom f neut).
Proof. exact (fun_ext (fun x : K => @lem6784004 A K x _88876 k dom f neut)). Qed.
Lemma lem6784006 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem6784007 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1047 A K _88876 k dom f neut) = (term1059 A K _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6784006 K) (@lem6784005 A K _88876 k dom f neut)). Qed.
Lemma lem6784008 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : ((term1046 A K _88876 k dom f neut) = (term1047 A K _88876 k dom f neut)) = ((term992 A K _88876 k dom f neut) = (term1059 A K _88876 k dom f neut)).
Proof. exact (MK_COMB (@lem6783999 A K _88876 k dom f neut) (@lem6784007 A K _88876 k dom f neut)). Qed.
Lemma lem6784009 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term992 A K _88876 k dom f neut) = (term1059 A K _88876 k dom f neut).
Proof. exact (EQ_MP (@lem6784008 A K _88876 k dom f neut) (@lem6783989 A K _88876 k dom f neut)). Qed.
Lemma lem6784010 {A K : Type'} (ltle : type1402 K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term994 A K ltle _88876 k dom f neut) = (term1060 A K ltle _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6783985 A K ltle k dom f neut) (@lem6784009 A K _88876 k dom f neut)). Qed.
Lemma lem6784012 {A : Type'} (P : A -> Prop) (Q : Prop) : (term1044 A P Q) = (term1045 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem6784013 {K : Type'} (P : type488 K) (Q : Prop) : (term1061 K P Q) = (term1062 K P Q).
Proof. exact (@lem6784012 (K -> K) P Q). Qed.
Lemma lem6784014 {A K : Type'} (ltle : type1402 K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1063 A K ltle _88876 k dom f neut) = (term1064 A K ltle _88876 k dom f neut).
Proof. exact (@lem6784013 K (term1041 A K ltle k dom f neut) (term1059 A K _88876 k dom f neut)). Qed.
Lemma lem6784015 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i' : K -> K) : (term1065 A K ltle k dom f neut i') = (term1039 A K ltle k dom f neut i').
Proof. exact (eq_refl (term1065 A K ltle k dom f neut i')). Qed.
Lemma lem6784016 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1066 A K ltle k dom f neut) = (term1041 A K ltle k dom f neut).
Proof. exact (fun_ext (fun i' : K -> K => @lem6784015 A K ltle k dom f neut i')). Qed.
Lemma lem6784017 {K : Type'} : (@ex (K -> K)) = (@ex (K -> K)).
Proof. exact (eq_refl (@ex (K -> K))). Qed.
Lemma lem6784018 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1067 A K ltle k dom f neut) = (term1042 A K ltle k dom f neut).
Proof. exact (MK_COMB (@lem6784017 K) (@lem6784016 A K ltle k dom f neut)). Qed.
Lemma lem6784019 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6784020 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1068 A K ltle k dom f neut) = (term1043 A K ltle k dom f neut).
Proof. exact (MK_COMB (@lem6784019) (@lem6784018 A K ltle k dom f neut)). Qed.
Lemma lem6784021 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1059 A K _88876 k dom f neut) = (term1059 A K _88876 k dom f neut).
Proof. exact (eq_refl (term1059 A K _88876 k dom f neut)). Qed.
Lemma lem6784022 {A K : Type'} (ltle : type1402 K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1063 A K ltle _88876 k dom f neut) = (term1060 A K ltle _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6784020 A K ltle k dom f neut) (@lem6784021 A K _88876 k dom f neut)). Qed.
Lemma lem6784023 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6784024 {A K : Type'} (ltle : type1402 K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1069 A K ltle _88876 k dom f neut) = (term1070 A K ltle _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6784023) (@lem6784022 A K ltle _88876 k dom f neut)). Qed.
Lemma lem6784025 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i' : K -> K) : (term1065 A K ltle k dom f neut i') = (term1039 A K ltle k dom f neut i').
Proof. exact (eq_refl (term1065 A K ltle k dom f neut i')). Qed.
Lemma lem6784026 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6784027 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i' : K -> K) : (term1071 A K ltle k dom f neut i') = (term1072 A K ltle k dom f neut i').
Proof. exact (MK_COMB (@lem6784026) (@lem6784025 A K ltle k dom f neut i')). Qed.
Lemma lem6784028 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1059 A K _88876 k dom f neut) = (term1059 A K _88876 k dom f neut).
Proof. exact (eq_refl (term1059 A K _88876 k dom f neut)). Qed.
Lemma lem6784029 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1073 A K ltle i' _88876 k dom f neut) = (term1074 A K ltle i' _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6784027 A K ltle k dom f neut i') (@lem6784028 A K _88876 k dom f neut)). Qed.
Lemma lem6784030 {A K : Type'} (ltle : type1402 K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1075 A K ltle _88876 k dom f neut) = (term1076 A K ltle _88876 k dom f neut).
Proof. exact (fun_ext (fun i' : K -> K => @lem6784029 A K ltle i' _88876 k dom f neut)). Qed.
Lemma lem6784031 {K : Type'} : (@ex (K -> K)) = (@ex (K -> K)).
Proof. exact (eq_refl (@ex (K -> K))). Qed.
Lemma lem6784032 {A K : Type'} (ltle : type1402 K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1064 A K ltle _88876 k dom f neut) = (term1077 A K ltle _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6784031 K) (@lem6784030 A K ltle _88876 k dom f neut)). Qed.
Lemma lem6784033 {A K : Type'} (ltle : type1402 K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : ((term1063 A K ltle _88876 k dom f neut) = (term1064 A K ltle _88876 k dom f neut)) = ((term1060 A K ltle _88876 k dom f neut) = (term1077 A K ltle _88876 k dom f neut)).
Proof. exact (MK_COMB (@lem6784024 A K ltle _88876 k dom f neut) (@lem6784032 A K ltle _88876 k dom f neut)). Qed.
Lemma lem6784034 {A K : Type'} (ltle : type1402 K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1060 A K ltle _88876 k dom f neut) = (term1077 A K ltle _88876 k dom f neut).
Proof. exact (EQ_MP (@lem6784033 A K ltle _88876 k dom f neut) (@lem6784014 A K ltle _88876 k dom f neut)). Qed.
Lemma lem6784036 {A : Type'} (P : Prop) (Q : A -> Prop) : (term897 A P Q) = (term898 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem6784037 {K : Type'} (P : Prop) (Q : K -> Prop) : (term897 K P Q) = (term898 K P Q).
Proof. exact (@lem6784036 K P Q). Qed.
Lemma lem6784038 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1078 A K ltle i' _88876 k dom f neut) = (term1079 A K ltle i' _88876 k dom f neut).
Proof. exact (@lem6784037 K (term1039 A K ltle k dom f neut i') (term1058 A K _88876 k dom f neut)). Qed.
Lemma lem6784039 {A K : Type'} (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1080 A K _88876 k dom f neut x) = (term1056 A K x _88876 k dom f neut).
Proof. exact (eq_refl (term1080 A K _88876 k dom f neut x)). Qed.
Lemma lem6784040 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1081 A K _88876 k dom f neut) = (term1058 A K _88876 k dom f neut).
Proof. exact (fun_ext (fun x : K => @lem6784039 A K x _88876 k dom f neut)). Qed.
Lemma lem6784041 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem6784042 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1082 A K _88876 k dom f neut) = (term1059 A K _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6784041 K) (@lem6784040 A K _88876 k dom f neut)). Qed.
Lemma lem6784043 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i' : K -> K) : (term1072 A K ltle k dom f neut i') = (term1072 A K ltle k dom f neut i').
Proof. exact (eq_refl (term1072 A K ltle k dom f neut i')). Qed.
Lemma lem6784044 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1078 A K ltle i' _88876 k dom f neut) = (term1074 A K ltle i' _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6784043 A K ltle k dom f neut i') (@lem6784042 A K _88876 k dom f neut)). Qed.
Lemma lem6784045 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6784046 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1083 A K ltle i' _88876 k dom f neut) = (term1084 A K ltle i' _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6784045) (@lem6784044 A K ltle i' _88876 k dom f neut)). Qed.
Lemma lem6784047 {A K : Type'} (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1080 A K _88876 k dom f neut x) = (term1056 A K x _88876 k dom f neut).
Proof. exact (eq_refl (term1080 A K _88876 k dom f neut x)). Qed.
Lemma lem6784048 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i' : K -> K) : (term1072 A K ltle k dom f neut i') = (term1072 A K ltle k dom f neut i').
Proof. exact (eq_refl (term1072 A K ltle k dom f neut i')). Qed.
Lemma lem6784049 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1085 A K ltle i' _88876 k dom f neut x) = (term1086 A K ltle i' x _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6784048 A K ltle k dom f neut i') (@lem6784047 A K x _88876 k dom f neut)). Qed.
Lemma lem6784050 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1087 A K ltle i' _88876 k dom f neut) = (term1088 A K ltle i' _88876 k dom f neut).
Proof. exact (fun_ext (fun x : K => @lem6784049 A K ltle i' x _88876 k dom f neut)). Qed.
Lemma lem6784051 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem6784052 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1079 A K ltle i' _88876 k dom f neut) = (term1089 A K ltle i' _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6784051 K) (@lem6784050 A K ltle i' _88876 k dom f neut)). Qed.
Lemma lem6784053 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : ((term1078 A K ltle i' _88876 k dom f neut) = (term1079 A K ltle i' _88876 k dom f neut)) = ((term1074 A K ltle i' _88876 k dom f neut) = (term1089 A K ltle i' _88876 k dom f neut)).
Proof. exact (MK_COMB (@lem6784046 A K ltle i' _88876 k dom f neut) (@lem6784052 A K ltle i' _88876 k dom f neut)). Qed.
Lemma lem6784054 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1074 A K ltle i' _88876 k dom f neut) = (term1089 A K ltle i' _88876 k dom f neut).
Proof. exact (EQ_MP (@lem6784053 A K ltle i' _88876 k dom f neut) (@lem6784038 A K ltle i' _88876 k dom f neut)). Qed.
Lemma lem6784055 {A K : Type'} (ltle : type1402 K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1076 A K ltle _88876 k dom f neut) = (term1090 A K ltle _88876 k dom f neut).
Proof. exact (fun_ext (fun i' : K -> K => @lem6784054 A K ltle i' _88876 k dom f neut)). Qed.
Lemma lem6784056 {K : Type'} : (@ex (K -> K)) = (@ex (K -> K)).
Proof. exact (eq_refl (@ex (K -> K))). Qed.
Lemma lem6784057 {A K : Type'} (ltle : type1402 K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1077 A K ltle _88876 k dom f neut) = (term1091 A K ltle _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6784056 K) (@lem6784055 A K ltle _88876 k dom f neut)). Qed.
Lemma lem6784058 {A K : Type'} (ltle : type1402 K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1060 A K ltle _88876 k dom f neut) = (term1091 A K ltle _88876 k dom f neut).
Proof. exact (TRANS (@lem6784034 A K ltle _88876 k dom f neut) (@lem6784057 A K ltle _88876 k dom f neut)). Qed.
Lemma lem6784060 {A K : Type'} (ltle : type1402 K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term994 A K ltle _88876 k dom f neut) = (term1091 A K ltle _88876 k dom f neut).
Proof. exact (TRANS (@lem6784010 A K ltle _88876 k dom f neut) (@lem6784058 A K ltle _88876 k dom f neut)). Qed.
Lemma lem6784061 {A K : Type'} (ltle : type1402 K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term513 A K ltle _88876 k dom f neut) = (term1091 A K ltle _88876 k dom f neut).
Proof. exact (TRANS (@lem6783781 A K ltle _88876 k dom f neut) (@lem6784060 A K ltle _88876 k dom f neut)). Qed.
Lemma lem6784062 {A K : Type'} (ltle : type1402 K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (h1 : term513 A K ltle _88876 k dom f neut) : term1091 A K ltle _88876 k dom f neut.
Proof. exact (EQ_MP (@lem6784061 A K ltle _88876 k dom f neut) (@lem6782434 A K ltle _88876 k dom f neut h1)). Qed.
Lemma lem6784068 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : (_88875 k dom f neut) = i) : (_88875 k dom f neut) = i.
Proof. exact (h1). Qed.
Lemma lem6784073 {A K : Type'} (f : K -> A) (i : K) (neut : A) : (term913 A K f i neut) = ((f i) = neut).
Proof. exact (@lem16933 ((f i) = neut)). Qed.
Lemma lem6784075 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) : (term914 A K dom f i) = (term914 A K dom f i).
Proof. exact (eq_refl (term914 A K dom f i)). Qed.
Lemma lem6784076 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term915 A K dom f i neut) = (term916 A K dom f i neut).
Proof. exact (MK_COMB (@lem6784075 A K dom f i) (@lem6784073 A K f i neut)). Qed.
Lemma lem6784077 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term917 A K dom f i neut) = (term915 A K dom f i neut).
Proof. exact (@lem17045 (term298 A K dom f i) (term309 A K f i neut)). Qed.
Lemma lem6784078 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term917 A K dom f i neut) = (term916 A K dom f i neut).
Proof. exact (TRANS (@lem6784077 A K dom f i neut) (@lem6784076 A K dom f i neut)). Qed.
Lemma lem6784080 {K : Type'} (k : K -> Prop) (i : K) : (term918 K k i) = (term918 K k i).
Proof. exact (eq_refl (term918 K k i)). Qed.
Lemma lem6784081 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term919 A K k dom f i neut) = (term920 A K k dom f i neut).
Proof. exact (MK_COMB (@lem6784080 K k i) (@lem6784078 A K dom f i neut)). Qed.
Lemma lem6784082 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term351 A K k dom f i neut) = (term919 A K k dom f i neut).
Proof. exact (@lem17045 (k i) (term310 A K dom f i neut)). Qed.
Lemma lem6784087 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term351 A K k dom f i neut) = (term920 A K k dom f i neut).
Proof. exact (TRANS (@lem6784082 A K k dom f i neut) (@lem6784081 A K k dom f i neut)). Qed.
Lemma lem6784088 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (h1 : term351 A K k dom f i neut) : term920 A K k dom f i neut.
Proof. exact (EQ_MP (@lem6784087 A K k dom f i neut) (@lem6782440 A K k dom f i neut h1)). Qed.
Lemma lem6784089 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (h1 : term1089 A K ltle i' _88876 k dom f neut) : term1089 A K ltle i' _88876 k dom f neut.
Proof. exact (h1). Qed.
Lemma lem6784090 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (h1 : term1086 A K ltle i' x _88876 k dom f neut) : term1086 A K ltle i' x _88876 k dom f neut.
Proof. exact (h1). Qed.
Lemma lem6784092 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6784093 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem6784094 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6784105 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784106 {A K : Type'} (f : type836 A K) (x : K -> Prop) : (f x) = (@I ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K) f x).
Proof. exact (@lem6784105 (K -> Prop) (type651 A K) f x). Qed.
Lemma lem6784107 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) : (_88875 k) = (@I ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K) _88875 k).
Proof. exact (@lem6784106 A K _88875 k). Qed.
Lemma lem6784108 {A : Type'} (dom : A -> Prop) : dom = dom.
Proof. exact (eq_refl dom). Qed.
Lemma lem6784109 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) : (_88875 k dom) = (@I ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K) _88875 k dom).
Proof. exact (MK_COMB (@lem6784107 A K _88875 k) (@lem6784108 A dom)). Qed.
Lemma lem6784111 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784112 {A K : Type'} (f : type651 A K) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (K -> A) -> A -> K) f x).
Proof. exact (@lem6784111 (A -> Prop) (type794 A K) f x). Qed.
Lemma lem6784113 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) : (@I ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K) _88875 k dom) = (term1092 A K _88875 k dom).
Proof. exact (@lem6784112 A K (@I ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K) _88875 k) dom). Qed.
Lemma lem6784114 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) : (_88875 k dom) = (term1092 A K _88875 k dom).
Proof. exact (TRANS (@lem6784109 A K _88875 k dom) (@lem6784113 A K _88875 k dom)). Qed.
Lemma lem6784115 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6784116 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (_88875 k dom f) = (term1093 A K _88875 k dom f).
Proof. exact (MK_COMB (@lem6784114 A K _88875 k dom) (@lem6784115 A K f)). Qed.
Lemma lem6784118 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784119 {A K : Type'} (f : type794 A K) (x : K -> A) : (f x) = (@I ((K -> A) -> A -> K) f x).
Proof. exact (@lem6784118 (K -> A) (A -> K) f x). Qed.
Lemma lem6784120 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term1093 A K _88875 k dom f) = (term1094 A K _88875 k dom f).
Proof. exact (@lem6784119 A K (term1092 A K _88875 k dom) f). Qed.
Lemma lem6784121 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (_88875 k dom f) = (term1094 A K _88875 k dom f).
Proof. exact (TRANS (@lem6784116 A K _88875 k dom f) (@lem6784120 A K _88875 k dom f)). Qed.
Lemma lem6784122 {A : Type'} (neut : A) : neut = neut.
Proof. exact (eq_refl neut). Qed.
Lemma lem6784123 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (_88875 k dom f neut) = (term1095 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6784121 A K _88875 k dom f) (@lem6784122 A neut)). Qed.
Lemma lem6784125 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784126 {A K : Type'} (f : A -> K) (x : A) : (f x) = (@I (A -> K) f x).
Proof. exact (@lem6784125 A K f x). Qed.
Lemma lem6784127 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1095 A K _88875 k dom f neut) = (term1096 A K _88875 k dom f neut).
Proof. exact (@lem6784126 A K (term1094 A K _88875 k dom f) neut). Qed.
Lemma lem6784129 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (_88875 k dom f neut) = (term1096 A K _88875 k dom f neut).
Proof. exact (TRANS (@lem6784123 A K _88875 k dom f neut) (@lem6784127 A K _88875 k dom f neut)). Qed.
Lemma lem6784130 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term420 A K _88875 k dom f neut) = (term1097 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6784094 A K f) (@lem6784129 A K _88875 k dom f neut)). Qed.
Lemma lem6784132 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784133 {A K : Type'} (f : K -> A) (x : K) : (f x) = (@I (K -> A) f x).
Proof. exact (@lem6784132 K A f x). Qed.
Lemma lem6784134 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1097 A K _88875 k dom f neut) = (term1098 A K _88875 k dom f neut).
Proof. exact (@lem6784133 A K f (term1096 A K _88875 k dom f neut)). Qed.
Lemma lem6784135 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term420 A K _88875 k dom f neut) = (term1098 A K _88875 k dom f neut).
Proof. exact (TRANS (@lem6784130 A K _88875 k dom f neut) (@lem6784134 A K _88875 k dom f neut)). Qed.
Lemma lem6784136 {A : Type'} (neut : A) : neut = neut.
Proof. exact (eq_refl neut). Qed.
Lemma lem6784137 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term426 A K _88875 k dom f neut) = (term1099 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6784093 A) (@lem6784135 A K _88875 k dom f neut)). Qed.
Lemma lem6784138 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : ((term420 A K _88875 k dom f neut) = neut) = ((term1098 A K _88875 k dom f neut) = neut).
Proof. exact (MK_COMB (@lem6784137 A K _88875 k dom f neut) (@lem6784136 A neut)). Qed.
Lemma lem6784139 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term428 A K _88875 k dom f neut) = (term1100 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6784092) (@lem6784138 A K _88875 k dom f neut)). Qed.
Lemma lem6784140 {A : Type'} (dom : A -> Prop) : dom = dom.
Proof. exact (eq_refl dom). Qed.
Lemma lem6784141 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6784152 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784153 {A K : Type'} (f : type836 A K) (x : K -> Prop) : (f x) = (@I ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K) f x).
Proof. exact (@lem6784152 (K -> Prop) (type651 A K) f x). Qed.
Lemma lem6784154 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) : (_88875 k) = (@I ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K) _88875 k).
Proof. exact (@lem6784153 A K _88875 k). Qed.
Lemma lem6784155 {A : Type'} (dom : A -> Prop) : dom = dom.
Proof. exact (eq_refl dom). Qed.
Lemma lem6784156 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) : (_88875 k dom) = (@I ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K) _88875 k dom).
Proof. exact (MK_COMB (@lem6784154 A K _88875 k) (@lem6784155 A dom)). Qed.
Lemma lem6784158 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784159 {A K : Type'} (f : type651 A K) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (K -> A) -> A -> K) f x).
Proof. exact (@lem6784158 (A -> Prop) (type794 A K) f x). Qed.
Lemma lem6784160 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) : (@I ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K) _88875 k dom) = (term1092 A K _88875 k dom).
Proof. exact (@lem6784159 A K (@I ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K) _88875 k) dom). Qed.
Lemma lem6784161 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) : (_88875 k dom) = (term1092 A K _88875 k dom).
Proof. exact (TRANS (@lem6784156 A K _88875 k dom) (@lem6784160 A K _88875 k dom)). Qed.
Lemma lem6784162 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6784163 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (_88875 k dom f) = (term1093 A K _88875 k dom f).
Proof. exact (MK_COMB (@lem6784161 A K _88875 k dom) (@lem6784162 A K f)). Qed.
Lemma lem6784165 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784166 {A K : Type'} (f : type794 A K) (x : K -> A) : (f x) = (@I ((K -> A) -> A -> K) f x).
Proof. exact (@lem6784165 (K -> A) (A -> K) f x). Qed.
Lemma lem6784167 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term1093 A K _88875 k dom f) = (term1094 A K _88875 k dom f).
Proof. exact (@lem6784166 A K (term1092 A K _88875 k dom) f). Qed.
Lemma lem6784168 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (_88875 k dom f) = (term1094 A K _88875 k dom f).
Proof. exact (TRANS (@lem6784163 A K _88875 k dom f) (@lem6784167 A K _88875 k dom f)). Qed.
Lemma lem6784169 {A : Type'} (neut : A) : neut = neut.
Proof. exact (eq_refl neut). Qed.
Lemma lem6784170 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (_88875 k dom f neut) = (term1095 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6784168 A K _88875 k dom f) (@lem6784169 A neut)). Qed.
Lemma lem6784172 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784173 {A K : Type'} (f : A -> K) (x : A) : (f x) = (@I (A -> K) f x).
Proof. exact (@lem6784172 A K f x). Qed.
Lemma lem6784174 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1095 A K _88875 k dom f neut) = (term1096 A K _88875 k dom f neut).
Proof. exact (@lem6784173 A K (term1094 A K _88875 k dom f) neut). Qed.
Lemma lem6784176 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (_88875 k dom f neut) = (term1096 A K _88875 k dom f neut).
Proof. exact (TRANS (@lem6784170 A K _88875 k dom f neut) (@lem6784174 A K _88875 k dom f neut)). Qed.
Lemma lem6784177 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term420 A K _88875 k dom f neut) = (term1097 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6784141 A K f) (@lem6784176 A K _88875 k dom f neut)). Qed.
Lemma lem6784179 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784180 {A K : Type'} (f : K -> A) (x : K) : (f x) = (@I (K -> A) f x).
Proof. exact (@lem6784179 K A f x). Qed.
Lemma lem6784181 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1097 A K _88875 k dom f neut) = (term1098 A K _88875 k dom f neut).
Proof. exact (@lem6784180 A K f (term1096 A K _88875 k dom f neut)). Qed.
Lemma lem6784182 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term420 A K _88875 k dom f neut) = (term1098 A K _88875 k dom f neut).
Proof. exact (TRANS (@lem6784177 A K _88875 k dom f neut) (@lem6784181 A K _88875 k dom f neut)). Qed.
Lemma lem6784183 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term422 A K _88875 k dom f neut) = (term1101 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6784140 A dom) (@lem6784182 A K _88875 k dom f neut)). Qed.
Lemma lem6784185 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784186 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem6784185 A Prop f x). Qed.
Lemma lem6784187 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1101 A K _88875 k dom f neut) = (term1102 A K _88875 k dom f neut).
Proof. exact (@lem6784186 A dom (term1098 A K _88875 k dom f neut)). Qed.
Lemma lem6784188 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term422 A K _88875 k dom f neut) = (term1102 A K _88875 k dom f neut).
Proof. exact (TRANS (@lem6784183 A K _88875 k dom f neut) (@lem6784187 A K _88875 k dom f neut)). Qed.
Lemma lem6784189 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6784190 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term424 A K _88875 k dom f neut) = (term1103 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6784189) (@lem6784188 A K _88875 k dom f neut)). Qed.
Lemma lem6784191 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term430 A K _88875 k dom f neut) = (term1104 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6784190 A K _88875 k dom f neut) (@lem6784139 A K _88875 k dom f neut)). Qed.
Lemma lem6784192 {K : Type'} (k : K -> Prop) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem6784203 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784204 {A K : Type'} (f : type836 A K) (x : K -> Prop) : (f x) = (@I ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K) f x).
Proof. exact (@lem6784203 (K -> Prop) (type651 A K) f x). Qed.
Lemma lem6784205 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) : (_88875 k) = (@I ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K) _88875 k).
Proof. exact (@lem6784204 A K _88875 k). Qed.
Lemma lem6784206 {A : Type'} (dom : A -> Prop) : dom = dom.
Proof. exact (eq_refl dom). Qed.
Lemma lem6784207 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) : (_88875 k dom) = (@I ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K) _88875 k dom).
Proof. exact (MK_COMB (@lem6784205 A K _88875 k) (@lem6784206 A dom)). Qed.
Lemma lem6784209 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784210 {A K : Type'} (f : type651 A K) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (K -> A) -> A -> K) f x).
Proof. exact (@lem6784209 (A -> Prop) (type794 A K) f x). Qed.
Lemma lem6784211 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) : (@I ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K) _88875 k dom) = (term1092 A K _88875 k dom).
Proof. exact (@lem6784210 A K (@I ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K) _88875 k) dom). Qed.
Lemma lem6784212 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) : (_88875 k dom) = (term1092 A K _88875 k dom).
Proof. exact (TRANS (@lem6784207 A K _88875 k dom) (@lem6784211 A K _88875 k dom)). Qed.
Lemma lem6784213 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6784214 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (_88875 k dom f) = (term1093 A K _88875 k dom f).
Proof. exact (MK_COMB (@lem6784212 A K _88875 k dom) (@lem6784213 A K f)). Qed.
Lemma lem6784216 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784217 {A K : Type'} (f : type794 A K) (x : K -> A) : (f x) = (@I ((K -> A) -> A -> K) f x).
Proof. exact (@lem6784216 (K -> A) (A -> K) f x). Qed.
Lemma lem6784218 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term1093 A K _88875 k dom f) = (term1094 A K _88875 k dom f).
Proof. exact (@lem6784217 A K (term1092 A K _88875 k dom) f). Qed.
Lemma lem6784219 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (_88875 k dom f) = (term1094 A K _88875 k dom f).
Proof. exact (TRANS (@lem6784214 A K _88875 k dom f) (@lem6784218 A K _88875 k dom f)). Qed.
Lemma lem6784220 {A : Type'} (neut : A) : neut = neut.
Proof. exact (eq_refl neut). Qed.
Lemma lem6784221 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (_88875 k dom f neut) = (term1095 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6784219 A K _88875 k dom f) (@lem6784220 A neut)). Qed.
Lemma lem6784223 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784224 {A K : Type'} (f : A -> K) (x : A) : (f x) = (@I (A -> K) f x).
Proof. exact (@lem6784223 A K f x). Qed.
Lemma lem6784225 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1095 A K _88875 k dom f neut) = (term1096 A K _88875 k dom f neut).
Proof. exact (@lem6784224 A K (term1094 A K _88875 k dom f) neut). Qed.
Lemma lem6784227 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (_88875 k dom f neut) = (term1096 A K _88875 k dom f neut).
Proof. exact (TRANS (@lem6784221 A K _88875 k dom f neut) (@lem6784225 A K _88875 k dom f neut)). Qed.
Lemma lem6784228 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term416 A K _88875 k dom f neut) = (term1105 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6784192 K k) (@lem6784227 A K _88875 k dom f neut)). Qed.
Lemma lem6784230 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784231 {K : Type'} (f : K -> Prop) (x : K) : (f x) = (@I (K -> Prop) f x).
Proof. exact (@lem6784230 K Prop f x). Qed.
Lemma lem6784232 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1105 A K _88875 k dom f neut) = (term1106 A K _88875 k dom f neut).
Proof. exact (@lem6784231 K k (term1096 A K _88875 k dom f neut)). Qed.
Lemma lem6784233 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term416 A K _88875 k dom f neut) = (term1106 A K _88875 k dom f neut).
Proof. exact (TRANS (@lem6784228 A K _88875 k dom f neut) (@lem6784232 A K _88875 k dom f neut)). Qed.
Lemma lem6784234 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6784235 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term418 A K _88875 k dom f neut) = (term1107 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6784234) (@lem6784233 A K _88875 k dom f neut)). Qed.
Lemma lem6784236 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term431 A K _88875 k dom f neut) = (term1108 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6784235 A K _88875 k dom f neut) (@lem6784191 A K _88875 k dom f neut)). Qed.
Lemma lem6784237 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem6784242 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784244 {A K : Type'} (f : K -> A) (x : K) : (f x) = (@I (K -> A) f x).
Proof. exact (@lem6784242 K A f x). Qed.
Lemma lem6784245 {A : Type'} (neut : A) : neut = neut.
Proof. exact (eq_refl neut). Qed.
Lemma lem6784246 {A K : Type'} (f : K -> A) (x : K) : (term1109 A K f x) = (term1110 A K f x).
Proof. exact (MK_COMB (@lem6784237 A) (@lem6784244 A K f x)). Qed.
Lemma lem6784247 {A K : Type'} (f : K -> A) (x : K) (neut : A) : ((f x) = neut) = ((@I (K -> A) f x) = neut).
Proof. exact (MK_COMB (@lem6784246 A K f x) (@lem6784245 A neut)). Qed.
Lemma lem6784248 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6784249 {A : Type'} (dom : A -> Prop) : dom = dom.
Proof. exact (eq_refl dom). Qed.
Lemma lem6784254 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784256 {A K : Type'} (f : K -> A) (x : K) : (f x) = (@I (K -> A) f x).
Proof. exact (@lem6784254 K A f x). Qed.
Lemma lem6784257 {A K : Type'} (dom : A -> Prop) (f : K -> A) (x : K) : (term298 A K dom f x) = (term1111 A K dom f x).
Proof. exact (MK_COMB (@lem6784249 A dom) (@lem6784256 A K f x)). Qed.
Lemma lem6784259 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784260 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem6784259 A Prop f x). Qed.
Lemma lem6784261 {A K : Type'} (dom : A -> Prop) (f : K -> A) (x : K) : (term1111 A K dom f x) = (term1112 A K dom f x).
Proof. exact (@lem6784260 A dom (@I (K -> A) f x)). Qed.
Lemma lem6784262 {A K : Type'} (dom : A -> Prop) (f : K -> A) (x : K) : (term298 A K dom f x) = (term1112 A K dom f x).
Proof. exact (TRANS (@lem6784257 A K dom f x) (@lem6784261 A K dom f x)). Qed.
Lemma lem6784263 {A K : Type'} (dom : A -> Prop) (f : K -> A) (x : K) : (term1113 A K dom f x) = (term1114 A K dom f x).
Proof. exact (MK_COMB (@lem6784248) (@lem6784262 A K dom f x)). Qed.
Lemma lem6784264 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6784265 {A K : Type'} (dom : A -> Prop) (f : K -> A) (x : K) : (term914 A K dom f x) = (term1115 A K dom f x).
Proof. exact (MK_COMB (@lem6784264) (@lem6784263 A K dom f x)). Qed.
Lemma lem6784266 {A K : Type'} (dom : A -> Prop) (f : K -> A) (x : K) (neut : A) : (term916 A K dom f x neut) = (term1116 A K dom f x neut).
Proof. exact (MK_COMB (@lem6784265 A K dom f x) (@lem6784247 A K f x neut)). Qed.
Lemma lem6784267 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6784272 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784273 {K : Type'} (f : K -> Prop) (x : K) : (f x) = (@I (K -> Prop) f x).
Proof. exact (@lem6784272 K Prop f x). Qed.
Lemma lem6784275 {K : Type'} (k : K -> Prop) (x : K) : (k x) = (@I (K -> Prop) k x).
Proof. exact (@lem6784273 K k x). Qed.
Lemma lem6784276 {K : Type'} (k : K -> Prop) (x : K) : (term35 K k x) = (term1117 K k x).
Proof. exact (MK_COMB (@lem6784267) (@lem6784275 K k x)). Qed.
Lemma lem6784277 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6784278 {K : Type'} (k : K -> Prop) (x : K) : (term918 K k x) = (term1118 K k x).
Proof. exact (MK_COMB (@lem6784277) (@lem6784276 K k x)). Qed.
Lemma lem6784279 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (x : K) (neut : A) : (term920 A K k dom f x neut) = (term1119 A K k dom f x neut).
Proof. exact (MK_COMB (@lem6784278 K k x) (@lem6784266 A K dom f x neut)). Qed.
Lemma lem6784280 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term939 A K k dom f neut) = (term1120 A K k dom f neut).
Proof. exact (fun_ext (fun x : K => @lem6784279 A K k dom f x neut)). Qed.
Lemma lem6784281 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6784282 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term948 A K k dom f neut) = (term1121 A K k dom f neut).
Proof. exact (MK_COMB (@lem6784281 K) (@lem6784280 A K k dom f neut)). Qed.
Lemma lem6784283 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6784284 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term950 A K k dom f neut) = (term1122 A K k dom f neut).
Proof. exact (MK_COMB (@lem6784283) (@lem6784282 A K k dom f neut)). Qed.
Lemma lem6784285 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term951 A K _88875 k dom f neut) = (term1123 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6784284 A K k dom f neut) (@lem6784236 A K _88875 k dom f neut)). Qed.
Lemma lem6784286 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term952 A K _88875 k dom f) = (term1124 A K _88875 k dom f).
Proof. exact (fun_ext (fun neut : A => @lem6784285 A K _88875 k dom f neut)). Qed.
Lemma lem6784287 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6784288 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term953 A K _88875 k dom f) = (term1125 A K _88875 k dom f).
Proof. exact (MK_COMB (@lem6784287 A) (@lem6784286 A K _88875 k dom f)). Qed.
Lemma lem6784289 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) : (term954 A K _88875 k dom) = (term1126 A K _88875 k dom).
Proof. exact (fun_ext (fun f : K -> A => @lem6784288 A K _88875 k dom f)). Qed.
Lemma lem6784290 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem6784291 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) : (term955 A K _88875 k dom) = (term1127 A K _88875 k dom).
Proof. exact (MK_COMB (@lem6784290 A K) (@lem6784289 A K _88875 k dom)). Qed.
Lemma lem6784292 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) : (term956 A K _88875 k) = (term1128 A K _88875 k).
Proof. exact (fun_ext (fun dom : A -> Prop => @lem6784291 A K _88875 k dom)). Qed.
Lemma lem6784293 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6784294 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) : (term957 A K _88875 k) = (term1129 A K _88875 k).
Proof. exact (MK_COMB (@lem6784293 A) (@lem6784292 A K _88875 k)). Qed.
Lemma lem6784295 {A K : Type'} (_88875 : type836 A K) : (term958 A K _88875) = (term1130 A K _88875).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6784294 A K _88875 k)). Qed.
Lemma lem6784296 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6784297 {A K : Type'} (_88875 : type836 A K) : (term959 A K _88875) = (term1131 A K _88875).
Proof. exact (MK_COMB (@lem6784296 K) (@lem6784295 A K _88875)). Qed.
Lemma lem6784298 {A K : Type'} (_88875 : type836 A K) (h1 : term446 A K _88875) : term1131 A K _88875.
Proof. exact (EQ_MP (@lem6784297 A K _88875) (@lem6783694 A K _88875 h1)). Qed.
Lemma lem6784299 {K : Type'} : (@eq K) = (@eq K).
Proof. exact (eq_refl (@eq K)). Qed.
Lemma lem6784310 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784311 {A K : Type'} (f : type836 A K) (x : K -> Prop) : (f x) = (@I ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K) f x).
Proof. exact (@lem6784310 (K -> Prop) (type651 A K) f x). Qed.
Lemma lem6784312 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) : (_88875 k) = (@I ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K) _88875 k).
Proof. exact (@lem6784311 A K _88875 k). Qed.
Lemma lem6784313 {A : Type'} (dom : A -> Prop) : dom = dom.
Proof. exact (eq_refl dom). Qed.
Lemma lem6784314 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) : (_88875 k dom) = (@I ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K) _88875 k dom).
Proof. exact (MK_COMB (@lem6784312 A K _88875 k) (@lem6784313 A dom)). Qed.
Lemma lem6784316 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784317 {A K : Type'} (f : type651 A K) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (K -> A) -> A -> K) f x).
Proof. exact (@lem6784316 (A -> Prop) (type794 A K) f x). Qed.
Lemma lem6784318 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) : (@I ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K) _88875 k dom) = (term1092 A K _88875 k dom).
Proof. exact (@lem6784317 A K (@I ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K) _88875 k) dom). Qed.
Lemma lem6784319 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) : (_88875 k dom) = (term1092 A K _88875 k dom).
Proof. exact (TRANS (@lem6784314 A K _88875 k dom) (@lem6784318 A K _88875 k dom)). Qed.
Lemma lem6784320 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6784321 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (_88875 k dom f) = (term1093 A K _88875 k dom f).
Proof. exact (MK_COMB (@lem6784319 A K _88875 k dom) (@lem6784320 A K f)). Qed.
Lemma lem6784323 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784324 {A K : Type'} (f : type794 A K) (x : K -> A) : (f x) = (@I ((K -> A) -> A -> K) f x).
Proof. exact (@lem6784323 (K -> A) (A -> K) f x). Qed.
Lemma lem6784325 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term1093 A K _88875 k dom f) = (term1094 A K _88875 k dom f).
Proof. exact (@lem6784324 A K (term1092 A K _88875 k dom) f). Qed.
Lemma lem6784326 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (_88875 k dom f) = (term1094 A K _88875 k dom f).
Proof. exact (TRANS (@lem6784321 A K _88875 k dom f) (@lem6784325 A K _88875 k dom f)). Qed.
Lemma lem6784327 {A : Type'} (neut : A) : neut = neut.
Proof. exact (eq_refl neut). Qed.
Lemma lem6784328 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (_88875 k dom f neut) = (term1095 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6784326 A K _88875 k dom f) (@lem6784327 A neut)). Qed.
Lemma lem6784330 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784331 {A K : Type'} (f : A -> K) (x : A) : (f x) = (@I (A -> K) f x).
Proof. exact (@lem6784330 A K f x). Qed.
Lemma lem6784332 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1095 A K _88875 k dom f neut) = (term1096 A K _88875 k dom f neut).
Proof. exact (@lem6784331 A K (term1094 A K _88875 k dom f) neut). Qed.
Lemma lem6784334 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (_88875 k dom f neut) = (term1096 A K _88875 k dom f neut).
Proof. exact (TRANS (@lem6784328 A K _88875 k dom f neut) (@lem6784332 A K _88875 k dom f neut)). Qed.
Lemma lem6784335 {K : Type'} (i : K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem6784336 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term406 A K _88875 k dom f neut) = (term1132 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6784299 K) (@lem6784334 A K _88875 k dom f neut)). Qed.
Lemma lem6784337 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : ((_88875 k dom f neut) = i) = ((term1096 A K _88875 k dom f neut) = i).
Proof. exact (MK_COMB (@lem6784336 A K _88875 k dom f neut) (@lem6784335 K i)). Qed.
Lemma lem6784339 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem6784344 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784345 {A K : Type'} (f : K -> A) (x : K) : (f x) = (@I (K -> A) f x).
Proof. exact (@lem6784344 K A f x). Qed.
Lemma lem6784347 {A K : Type'} (f : K -> A) (i : K) : (f i) = (@I (K -> A) f i).
Proof. exact (@lem6784345 A K f i). Qed.
Lemma lem6784348 {A : Type'} (neut : A) : neut = neut.
Proof. exact (eq_refl neut). Qed.
Lemma lem6784349 {A K : Type'} (f : K -> A) (i : K) : (term1109 A K f i) = (term1110 A K f i).
Proof. exact (MK_COMB (@lem6784339 A) (@lem6784347 A K f i)). Qed.
Lemma lem6784350 {A K : Type'} (f : K -> A) (i : K) (neut : A) : ((f i) = neut) = ((@I (K -> A) f i) = neut).
Proof. exact (MK_COMB (@lem6784349 A K f i) (@lem6784348 A neut)). Qed.
Lemma lem6784351 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6784352 {A : Type'} (dom : A -> Prop) : dom = dom.
Proof. exact (eq_refl dom). Qed.
Lemma lem6784357 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784358 {A K : Type'} (f : K -> A) (x : K) : (f x) = (@I (K -> A) f x).
Proof. exact (@lem6784357 K A f x). Qed.
Lemma lem6784360 {A K : Type'} (f : K -> A) (i : K) : (f i) = (@I (K -> A) f i).
Proof. exact (@lem6784358 A K f i). Qed.
Lemma lem6784361 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) : (term298 A K dom f i) = (term1111 A K dom f i).
Proof. exact (MK_COMB (@lem6784352 A dom) (@lem6784360 A K f i)). Qed.
Lemma lem6784363 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784364 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem6784363 A Prop f x). Qed.
Lemma lem6784365 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) : (term1111 A K dom f i) = (term1112 A K dom f i).
Proof. exact (@lem6784364 A dom (@I (K -> A) f i)). Qed.
Lemma lem6784366 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) : (term298 A K dom f i) = (term1112 A K dom f i).
Proof. exact (TRANS (@lem6784361 A K dom f i) (@lem6784365 A K dom f i)). Qed.
Lemma lem6784367 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) : (term1113 A K dom f i) = (term1114 A K dom f i).
Proof. exact (MK_COMB (@lem6784351) (@lem6784366 A K dom f i)). Qed.
Lemma lem6784368 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6784369 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) : (term914 A K dom f i) = (term1115 A K dom f i).
Proof. exact (MK_COMB (@lem6784368) (@lem6784367 A K dom f i)). Qed.
Lemma lem6784370 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term916 A K dom f i neut) = (term1116 A K dom f i neut).
Proof. exact (MK_COMB (@lem6784369 A K dom f i) (@lem6784350 A K f i neut)). Qed.
Lemma lem6784371 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6784376 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784377 {K : Type'} (f : K -> Prop) (x : K) : (f x) = (@I (K -> Prop) f x).
Proof. exact (@lem6784376 K Prop f x). Qed.
Lemma lem6784379 {K : Type'} (k : K -> Prop) (i : K) : (k i) = (@I (K -> Prop) k i).
Proof. exact (@lem6784377 K k i). Qed.
Lemma lem6784380 {K : Type'} (k : K -> Prop) (i : K) : (term35 K k i) = (term1117 K k i).
Proof. exact (MK_COMB (@lem6784371) (@lem6784379 K k i)). Qed.
Lemma lem6784381 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6784382 {K : Type'} (k : K -> Prop) (i : K) : (term918 K k i) = (term1118 K k i).
Proof. exact (MK_COMB (@lem6784381) (@lem6784380 K k i)). Qed.
Lemma lem6784383 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term920 A K k dom f i neut) = (term1119 A K k dom f i neut).
Proof. exact (MK_COMB (@lem6784382 K k i) (@lem6784370 A K dom f i neut)). Qed.
Lemma lem6784384 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (h1 : term351 A K k dom f i neut) : term1119 A K k dom f i neut.
Proof. exact (EQ_MP (@lem6784383 A K k dom f i neut) (@lem6784088 A K k dom f i neut h1)). Qed.
Lemma lem6784385 {K : Type'} : (@FINITE K) = (@FINITE K).
Proof. exact (eq_refl (@FINITE K)). Qed.
Lemma lem6784386 {K : Type'} : (@GSPEC K) = (@GSPEC K).
Proof. exact (eq_refl (@GSPEC K)). Qed.
Lemma lem6784397 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784398 {A K : Type'} (f : type835 A K) (x : K -> Prop) : (f x) = (@I ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K -> Prop) f x).
Proof. exact (@lem6784397 (K -> Prop) (type650 A K) f x). Qed.
Lemma lem6784399 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) : (_88876 k) = (@I ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K -> Prop) _88876 k).
Proof. exact (@lem6784398 A K _88876 k). Qed.
Lemma lem6784400 {A : Type'} (dom : A -> Prop) : dom = dom.
Proof. exact (eq_refl dom). Qed.
Lemma lem6784401 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (_88876 k dom) = (@I ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K -> Prop) _88876 k dom).
Proof. exact (MK_COMB (@lem6784399 A K _88876 k) (@lem6784400 A dom)). Qed.
Lemma lem6784403 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784404 {A K : Type'} (f : type650 A K) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (K -> A) -> A -> K -> Prop) f x).
Proof. exact (@lem6784403 (A -> Prop) (type793 A K) f x). Qed.
Lemma lem6784405 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (@I ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K -> Prop) _88876 k dom) = (term1133 A K _88876 k dom).
Proof. exact (@lem6784404 A K (@I ((K -> Prop) -> (A -> Prop) -> (K -> A) -> A -> K -> Prop) _88876 k) dom). Qed.
Lemma lem6784406 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) : (_88876 k dom) = (term1133 A K _88876 k dom).
Proof. exact (TRANS (@lem6784401 A K _88876 k dom) (@lem6784405 A K _88876 k dom)). Qed.
Lemma lem6784407 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6784408 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (_88876 k dom f) = (term1134 A K _88876 k dom f).
Proof. exact (MK_COMB (@lem6784406 A K _88876 k dom) (@lem6784407 A K f)). Qed.
Lemma lem6784410 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784411 {A K : Type'} (f : type793 A K) (x : K -> A) : (f x) = (@I ((K -> A) -> A -> K -> Prop) f x).
Proof. exact (@lem6784410 (K -> A) (type1413 A K) f x). Qed.
Lemma lem6784412 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term1134 A K _88876 k dom f) = (term1135 A K _88876 k dom f).
Proof. exact (@lem6784411 A K (term1133 A K _88876 k dom) f). Qed.
Lemma lem6784413 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (_88876 k dom f) = (term1135 A K _88876 k dom f).
Proof. exact (TRANS (@lem6784408 A K _88876 k dom f) (@lem6784412 A K _88876 k dom f)). Qed.
Lemma lem6784414 {A : Type'} (neut : A) : neut = neut.
Proof. exact (eq_refl neut). Qed.
Lemma lem6784415 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (_88876 k dom f neut) = (term1136 A K _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6784413 A K _88876 k dom f) (@lem6784414 A neut)). Qed.
Lemma lem6784417 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784418 {A K : Type'} (f : type1413 A K) (x : A) : (f x) = (@I (A -> K -> Prop) f x).
Proof. exact (@lem6784417 A (K -> Prop) f x). Qed.
Lemma lem6784419 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1136 A K _88876 k dom f neut) = (term1137 A K _88876 k dom f neut).
Proof. exact (@lem6784418 A K (term1135 A K _88876 k dom f) neut). Qed.
Lemma lem6784421 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (_88876 k dom f neut) = (term1137 A K _88876 k dom f neut).
Proof. exact (TRANS (@lem6784415 A K _88876 k dom f neut) (@lem6784419 A K _88876 k dom f neut)). Qed.
Lemma lem6784422 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term510 A K _88876 k dom f neut) = (term1138 A K _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6784386 K) (@lem6784421 A K _88876 k dom f neut)). Qed.
Lemma lem6784424 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784425 {K : Type'} (f : type672 K) (x : K -> Prop) : (f x) = (@I ((K -> Prop) -> K -> Prop) f x).
Proof. exact (@lem6784424 (K -> Prop) (K -> Prop) f x). Qed.
Lemma lem6784426 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1138 A K _88876 k dom f neut) = (term1139 A K _88876 k dom f neut).
Proof. exact (@lem6784425 K (@GSPEC K) (term1137 A K _88876 k dom f neut)). Qed.
Lemma lem6784427 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term510 A K _88876 k dom f neut) = (term1139 A K _88876 k dom f neut).
Proof. exact (TRANS (@lem6784422 A K _88876 k dom f neut) (@lem6784426 A K _88876 k dom f neut)). Qed.
Lemma lem6784428 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term511 A K _88876 k dom f neut) = (term1140 A K _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6784385 K) (@lem6784427 A K _88876 k dom f neut)). Qed.
Lemma lem6784430 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784431 {K : Type'} (f : type686 K) (x : K -> Prop) : (f x) = (@I ((K -> Prop) -> Prop) f x).
Proof. exact (@lem6784430 (K -> Prop) Prop f x). Qed.
Lemma lem6784432 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1140 A K _88876 k dom f neut) = (term1141 A K _88876 k dom f neut).
Proof. exact (@lem6784431 K (@FINITE K) (term1139 A K _88876 k dom f neut)). Qed.
Lemma lem6784433 {A K : Type'} (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term511 A K _88876 k dom f neut) = (term1141 A K _88876 k dom f neut).
Proof. exact (TRANS (@lem6784428 A K _88876 k dom f neut) (@lem6784432 A K _88876 k dom f neut)). Qed.
Lemma lem6784434 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6784435 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem6784440 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784442 {A K : Type'} (f : K -> A) (x : K) : (f x) = (@I (K -> A) f x).
Proof. exact (@lem6784440 K A f x). Qed.
Lemma lem6784443 {A : Type'} (neut : A) : neut = neut.
Proof. exact (eq_refl neut). Qed.
Lemma lem6784444 {A K : Type'} (f : K -> A) (x : K) : (term1109 A K f x) = (term1110 A K f x).
Proof. exact (MK_COMB (@lem6784435 A) (@lem6784442 A K f x)). Qed.
Lemma lem6784445 {A K : Type'} (f : K -> A) (x : K) (neut : A) : ((f x) = neut) = ((@I (K -> A) f x) = neut).
Proof. exact (MK_COMB (@lem6784444 A K f x) (@lem6784443 A neut)). Qed.
Lemma lem6784446 {A K : Type'} (f : K -> A) (x : K) (neut : A) : (term309 A K f x neut) = (term1142 A K f x neut).
Proof. exact (MK_COMB (@lem6784434) (@lem6784445 A K f x neut)). Qed.
Lemma lem6784447 {A : Type'} (dom : A -> Prop) : dom = dom.
Proof. exact (eq_refl dom). Qed.
Lemma lem6784452 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784454 {A K : Type'} (f : K -> A) (x : K) : (f x) = (@I (K -> A) f x).
Proof. exact (@lem6784452 K A f x). Qed.
Lemma lem6784455 {A K : Type'} (dom : A -> Prop) (f : K -> A) (x : K) : (term298 A K dom f x) = (term1111 A K dom f x).
Proof. exact (MK_COMB (@lem6784447 A dom) (@lem6784454 A K f x)). Qed.
Lemma lem6784457 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784458 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem6784457 A Prop f x). Qed.
Lemma lem6784459 {A K : Type'} (dom : A -> Prop) (f : K -> A) (x : K) : (term1111 A K dom f x) = (term1112 A K dom f x).
Proof. exact (@lem6784458 A dom (@I (K -> A) f x)). Qed.
Lemma lem6784460 {A K : Type'} (dom : A -> Prop) (f : K -> A) (x : K) : (term298 A K dom f x) = (term1112 A K dom f x).
Proof. exact (TRANS (@lem6784455 A K dom f x) (@lem6784459 A K dom f x)). Qed.
Lemma lem6784461 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6784462 {A K : Type'} (dom : A -> Prop) (f : K -> A) (x : K) : (term300 A K dom f x) = (term1143 A K dom f x).
Proof. exact (MK_COMB (@lem6784461) (@lem6784460 A K dom f x)). Qed.
Lemma lem6784463 {A K : Type'} (dom : A -> Prop) (f : K -> A) (x : K) (neut : A) : (term310 A K dom f x neut) = (term1144 A K dom f x neut).
Proof. exact (MK_COMB (@lem6784462 A K dom f x) (@lem6784446 A K f x neut)). Qed.
Lemma lem6784468 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784469 {K : Type'} (f : K -> Prop) (x : K) : (f x) = (@I (K -> Prop) f x).
Proof. exact (@lem6784468 K Prop f x). Qed.
Lemma lem6784471 {K : Type'} (k : K -> Prop) (x : K) : (k x) = (@I (K -> Prop) k x).
Proof. exact (@lem6784469 K k x). Qed.
Lemma lem6784472 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6784473 {K : Type'} (k : K -> Prop) (x : K) : (term293 K k x) = (term1145 K k x).
Proof. exact (MK_COMB (@lem6784472) (@lem6784471 K k x)). Qed.
Lemma lem6784474 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (x : K) (neut : A) : (term312 A K k dom f x neut) = (term1146 A K k dom f x neut).
Proof. exact (MK_COMB (@lem6784473 K k x) (@lem6784463 A K dom f x neut)). Qed.
Lemma lem6784475 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6784476 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (x : K) (neut : A) : (term1054 A K k dom f x neut) = (term1147 A K k dom f x neut).
Proof. exact (MK_COMB (@lem6784475) (@lem6784474 A K k dom f x neut)). Qed.
Lemma lem6784477 {A K : Type'} (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1056 A K x _88876 k dom f neut) = (term1148 A K x _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6784476 A K k dom f x neut) (@lem6784433 A K _88876 k dom f neut)). Qed.
Lemma lem6784478 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6784479 {K : Type'} : (@eq K) = (@eq K).
Proof. exact (eq_refl (@eq K)). Qed.
Lemma lem6784484 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784485 {K : Type'} (f : K -> K) (x : K) : (f x) = (@I (K -> K) f x).
Proof. exact (@lem6784484 K K f x). Qed.
Lemma lem6784487 {K : Type'} (i' : K -> K) (i : K) : (i' i) = (@I (K -> K) i' i).
Proof. exact (@lem6784485 K i' i). Qed.
Lemma lem6784488 {K : Type'} (i : K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem6784489 {K : Type'} (i' : K -> K) (i : K) : (term1149 K i' i) = (term1150 K i' i).
Proof. exact (MK_COMB (@lem6784479 K) (@lem6784487 K i' i)). Qed.
Lemma lem6784490 {K : Type'} (i' : K -> K) (i : K) : ((i' i) = i) = ((@I (K -> K) i' i) = i).
Proof. exact (MK_COMB (@lem6784489 K i' i) (@lem6784488 K i)). Qed.
Lemma lem6784491 {K : Type'} (i' : K -> K) (i : K) : (term1151 K i' i) = (term1152 K i' i).
Proof. exact (MK_COMB (@lem6784478) (@lem6784490 K i' i)). Qed.
Lemma lem6784492 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6784493 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem6784494 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6784499 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784500 {K : Type'} (f : K -> K) (x : K) : (f x) = (@I (K -> K) f x).
Proof. exact (@lem6784499 K K f x). Qed.
Lemma lem6784502 {K : Type'} (i' : K -> K) (i : K) : (i' i) = (@I (K -> K) i' i).
Proof. exact (@lem6784500 K i' i). Qed.
Lemma lem6784503 {A K : Type'} (f : K -> A) (i' : K -> K) (i : K) : (term1153 A K f i' i) = (term1154 A K f i' i).
Proof. exact (MK_COMB (@lem6784494 A K f) (@lem6784502 K i' i)). Qed.
Lemma lem6784505 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784506 {A K : Type'} (f : K -> A) (x : K) : (f x) = (@I (K -> A) f x).
Proof. exact (@lem6784505 K A f x). Qed.
Lemma lem6784507 {A K : Type'} (f : K -> A) (i' : K -> K) (i : K) : (term1154 A K f i' i) = (term1155 A K f i' i).
Proof. exact (@lem6784506 A K f (@I (K -> K) i' i)). Qed.
Lemma lem6784508 {A K : Type'} (f : K -> A) (i' : K -> K) (i : K) : (term1153 A K f i' i) = (term1155 A K f i' i).
Proof. exact (TRANS (@lem6784503 A K f i' i) (@lem6784507 A K f i' i)). Qed.
Lemma lem6784509 {A : Type'} (neut : A) : neut = neut.
Proof. exact (eq_refl neut). Qed.
Lemma lem6784510 {A K : Type'} (f : K -> A) (i' : K -> K) (i : K) : (term1156 A K f i' i) = (term1157 A K f i' i).
Proof. exact (MK_COMB (@lem6784493 A) (@lem6784508 A K f i' i)). Qed.
Lemma lem6784511 {A K : Type'} (f : K -> A) (i' : K -> K) (i : K) (neut : A) : ((term1153 A K f i' i) = neut) = ((term1155 A K f i' i) = neut).
Proof. exact (MK_COMB (@lem6784510 A K f i' i) (@lem6784509 A neut)). Qed.
Lemma lem6784512 {A K : Type'} (f : K -> A) (i' : K -> K) (i : K) (neut : A) : (term1158 A K f i' i neut) = (term1159 A K f i' i neut).
Proof. exact (MK_COMB (@lem6784492) (@lem6784511 A K f i' i neut)). Qed.
Lemma lem6784513 {A : Type'} (dom : A -> Prop) : dom = dom.
Proof. exact (eq_refl dom). Qed.
Lemma lem6784514 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6784519 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784520 {K : Type'} (f : K -> K) (x : K) : (f x) = (@I (K -> K) f x).
Proof. exact (@lem6784519 K K f x). Qed.
Lemma lem6784522 {K : Type'} (i' : K -> K) (i : K) : (i' i) = (@I (K -> K) i' i).
Proof. exact (@lem6784520 K i' i). Qed.
Lemma lem6784523 {A K : Type'} (f : K -> A) (i' : K -> K) (i : K) : (term1153 A K f i' i) = (term1154 A K f i' i).
Proof. exact (MK_COMB (@lem6784514 A K f) (@lem6784522 K i' i)). Qed.
Lemma lem6784525 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784526 {A K : Type'} (f : K -> A) (x : K) : (f x) = (@I (K -> A) f x).
Proof. exact (@lem6784525 K A f x). Qed.
Lemma lem6784527 {A K : Type'} (f : K -> A) (i' : K -> K) (i : K) : (term1154 A K f i' i) = (term1155 A K f i' i).
Proof. exact (@lem6784526 A K f (@I (K -> K) i' i)). Qed.
Lemma lem6784528 {A K : Type'} (f : K -> A) (i' : K -> K) (i : K) : (term1153 A K f i' i) = (term1155 A K f i' i).
Proof. exact (TRANS (@lem6784523 A K f i' i) (@lem6784527 A K f i' i)). Qed.
Lemma lem6784529 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i' : K -> K) (i : K) : (term1160 A K dom f i' i) = (term1161 A K dom f i' i).
Proof. exact (MK_COMB (@lem6784513 A dom) (@lem6784528 A K f i' i)). Qed.
Lemma lem6784531 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784532 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem6784531 A Prop f x). Qed.
Lemma lem6784533 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i' : K -> K) (i : K) : (term1161 A K dom f i' i) = (term1162 A K dom f i' i).
Proof. exact (@lem6784532 A dom (term1155 A K f i' i)). Qed.
Lemma lem6784534 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i' : K -> K) (i : K) : (term1160 A K dom f i' i) = (term1162 A K dom f i' i).
Proof. exact (TRANS (@lem6784529 A K dom f i' i) (@lem6784533 A K dom f i' i)). Qed.
Lemma lem6784535 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6784536 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i' : K -> K) (i : K) : (term1163 A K dom f i' i) = (term1164 A K dom f i' i).
Proof. exact (MK_COMB (@lem6784535) (@lem6784534 A K dom f i' i)). Qed.
Lemma lem6784537 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i' : K -> K) (i : K) (neut : A) : (term1165 A K dom f i' i neut) = (term1166 A K dom f i' i neut).
Proof. exact (MK_COMB (@lem6784536 A K dom f i' i) (@lem6784512 A K f i' i neut)). Qed.
Lemma lem6784538 {K : Type'} (k : K -> Prop) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem6784543 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784544 {K : Type'} (f : K -> K) (x : K) : (f x) = (@I (K -> K) f x).
Proof. exact (@lem6784543 K K f x). Qed.
Lemma lem6784546 {K : Type'} (i' : K -> K) (i : K) : (i' i) = (@I (K -> K) i' i).
Proof. exact (@lem6784544 K i' i). Qed.
Lemma lem6784547 {K : Type'} (k : K -> Prop) (i' : K -> K) (i : K) : (term1167 K k i' i) = (term1168 K k i' i).
Proof. exact (MK_COMB (@lem6784538 K k) (@lem6784546 K i' i)). Qed.
Lemma lem6784549 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784550 {K : Type'} (f : K -> Prop) (x : K) : (f x) = (@I (K -> Prop) f x).
Proof. exact (@lem6784549 K Prop f x). Qed.
Lemma lem6784551 {K : Type'} (k : K -> Prop) (i' : K -> K) (i : K) : (term1168 K k i' i) = (term1169 K k i' i).
Proof. exact (@lem6784550 K k (@I (K -> K) i' i)). Qed.
Lemma lem6784552 {K : Type'} (k : K -> Prop) (i' : K -> K) (i : K) : (term1167 K k i' i) = (term1169 K k i' i).
Proof. exact (TRANS (@lem6784547 K k i' i) (@lem6784551 K k i' i)). Qed.
Lemma lem6784553 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6784554 {K : Type'} (k : K -> Prop) (i' : K -> K) (i : K) : (term1170 K k i' i) = (term1171 K k i' i).
Proof. exact (MK_COMB (@lem6784553) (@lem6784552 K k i' i)). Qed.
Lemma lem6784555 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i' : K -> K) (i : K) (neut : A) : (term1172 A K k dom f i' i neut) = (term1173 A K k dom f i' i neut).
Proof. exact (MK_COMB (@lem6784554 K k i' i) (@lem6784537 A K dom f i' i neut)). Qed.
Lemma lem6784556 {K : Type'} (ltle : type1402 K) : ltle = ltle.
Proof. exact (eq_refl ltle). Qed.
Lemma lem6784561 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784562 {K : Type'} (f : K -> K) (x : K) : (f x) = (@I (K -> K) f x).
Proof. exact (@lem6784561 K K f x). Qed.
Lemma lem6784564 {K : Type'} (i' : K -> K) (i : K) : (i' i) = (@I (K -> K) i' i).
Proof. exact (@lem6784562 K i' i). Qed.
Lemma lem6784565 {K : Type'} (i : K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem6784566 {K : Type'} (ltle : type1402 K) (i' : K -> K) (i : K) : (term1174 K ltle i' i) = (term1175 K ltle i' i).
Proof. exact (MK_COMB (@lem6784556 K ltle) (@lem6784564 K i' i)). Qed.
Lemma lem6784567 {K : Type'} (ltle : type1402 K) (i' : K -> K) (i : K) : (term1176 K ltle i' i) = (term1177 K ltle i' i).
Proof. exact (MK_COMB (@lem6784566 K ltle i' i) (@lem6784565 K i)). Qed.
Lemma lem6784569 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784570 {K : Type'} (f : type1402 K) (x : K) : (f x) = (@I (K -> K -> Prop) f x).
Proof. exact (@lem6784569 K (K -> Prop) f x). Qed.
Lemma lem6784571 {K : Type'} (ltle : type1402 K) (i' : K -> K) (i : K) : (term1175 K ltle i' i) = (term1178 K ltle i' i).
Proof. exact (@lem6784570 K ltle (@I (K -> K) i' i)). Qed.
Lemma lem6784572 {K : Type'} (i : K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem6784573 {K : Type'} (ltle : type1402 K) (i' : K -> K) (i : K) : (term1177 K ltle i' i) = (term1179 K ltle i' i).
Proof. exact (MK_COMB (@lem6784571 K ltle i' i) (@lem6784572 K i)). Qed.
Lemma lem6784575 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784576 {K : Type'} (f : K -> Prop) (x : K) : (f x) = (@I (K -> Prop) f x).
Proof. exact (@lem6784575 K Prop f x). Qed.
Lemma lem6784577 {K : Type'} (ltle : type1402 K) (i' : K -> K) (i : K) : (term1179 K ltle i' i) = (term1180 K ltle i' i).
Proof. exact (@lem6784576 K (term1178 K ltle i' i) i). Qed.
Lemma lem6784578 {K : Type'} (ltle : type1402 K) (i' : K -> K) (i : K) : (term1177 K ltle i' i) = (term1180 K ltle i' i).
Proof. exact (TRANS (@lem6784573 K ltle i' i) (@lem6784577 K ltle i' i)). Qed.
Lemma lem6784579 {K : Type'} (ltle : type1402 K) (i' : K -> K) (i : K) : (term1176 K ltle i' i) = (term1180 K ltle i' i).
Proof. exact (TRANS (@lem6784567 K ltle i' i) (@lem6784578 K ltle i' i)). Qed.
Lemma lem6784580 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6784581 {K : Type'} (ltle : type1402 K) (i' : K -> K) (i : K) : (term1181 K ltle i' i) = (term1182 K ltle i' i).
Proof. exact (MK_COMB (@lem6784580) (@lem6784579 K ltle i' i)). Qed.
Lemma lem6784582 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i' : K -> K) (i : K) (neut : A) : (term1183 A K ltle k dom f i' i neut) = (term1184 A K ltle k dom f i' i neut).
Proof. exact (MK_COMB (@lem6784581 K ltle i' i) (@lem6784555 A K k dom f i' i neut)). Qed.
Lemma lem6784583 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6784584 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i' : K -> K) (i : K) (neut : A) : (term1185 A K ltle k dom f i' i neut) = (term1186 A K ltle k dom f i' i neut).
Proof. exact (MK_COMB (@lem6784583) (@lem6784582 A K ltle k dom f i' i neut)). Qed.
Lemma lem6784585 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i' : K -> K) (i : K) : (term1187 A K ltle k dom f neut i' i) = (term1188 A K ltle k dom f neut i' i).
Proof. exact (MK_COMB (@lem6784584 A K ltle k dom f i' i neut) (@lem6784491 K i' i)). Qed.
Lemma lem6784586 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem6784591 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784592 {A K : Type'} (f : K -> A) (x : K) : (f x) = (@I (K -> A) f x).
Proof. exact (@lem6784591 K A f x). Qed.
Lemma lem6784594 {A K : Type'} (f : K -> A) (i : K) : (f i) = (@I (K -> A) f i).
Proof. exact (@lem6784592 A K f i). Qed.
Lemma lem6784595 {A : Type'} (neut : A) : neut = neut.
Proof. exact (eq_refl neut). Qed.
Lemma lem6784596 {A K : Type'} (f : K -> A) (i : K) : (term1109 A K f i) = (term1110 A K f i).
Proof. exact (MK_COMB (@lem6784586 A) (@lem6784594 A K f i)). Qed.
Lemma lem6784597 {A K : Type'} (f : K -> A) (i : K) (neut : A) : ((f i) = neut) = ((@I (K -> A) f i) = neut).
Proof. exact (MK_COMB (@lem6784596 A K f i) (@lem6784595 A neut)). Qed.
Lemma lem6784598 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6784599 {A : Type'} (dom : A -> Prop) : dom = dom.
Proof. exact (eq_refl dom). Qed.
Lemma lem6784604 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784605 {A K : Type'} (f : K -> A) (x : K) : (f x) = (@I (K -> A) f x).
Proof. exact (@lem6784604 K A f x). Qed.
Lemma lem6784607 {A K : Type'} (f : K -> A) (i : K) : (f i) = (@I (K -> A) f i).
Proof. exact (@lem6784605 A K f i). Qed.
Lemma lem6784608 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) : (term298 A K dom f i) = (term1111 A K dom f i).
Proof. exact (MK_COMB (@lem6784599 A dom) (@lem6784607 A K f i)). Qed.
Lemma lem6784610 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784611 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem6784610 A Prop f x). Qed.
Lemma lem6784612 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) : (term1111 A K dom f i) = (term1112 A K dom f i).
Proof. exact (@lem6784611 A dom (@I (K -> A) f i)). Qed.
Lemma lem6784613 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) : (term298 A K dom f i) = (term1112 A K dom f i).
Proof. exact (TRANS (@lem6784608 A K dom f i) (@lem6784612 A K dom f i)). Qed.
Lemma lem6784614 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) : (term1113 A K dom f i) = (term1114 A K dom f i).
Proof. exact (MK_COMB (@lem6784598) (@lem6784613 A K dom f i)). Qed.
Lemma lem6784615 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6784616 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) : (term914 A K dom f i) = (term1115 A K dom f i).
Proof. exact (MK_COMB (@lem6784615) (@lem6784614 A K dom f i)). Qed.
Lemma lem6784617 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term916 A K dom f i neut) = (term1116 A K dom f i neut).
Proof. exact (MK_COMB (@lem6784616 A K dom f i) (@lem6784597 A K f i neut)). Qed.
Lemma lem6784618 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6784619 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term972 A K dom f i neut) = (term1189 A K dom f i neut).
Proof. exact (MK_COMB (@lem6784618) (@lem6784617 A K dom f i neut)). Qed.
Lemma lem6784620 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i' : K -> K) (i : K) : (term1190 A K ltle k dom f neut i' i) = (term1191 A K ltle k dom f neut i' i).
Proof. exact (MK_COMB (@lem6784619 A K dom f i neut) (@lem6784585 A K ltle k dom f neut i' i)). Qed.
Lemma lem6784621 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6784626 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6784627 {K : Type'} (f : K -> Prop) (x : K) : (f x) = (@I (K -> Prop) f x).
Proof. exact (@lem6784626 K Prop f x). Qed.
Lemma lem6784629 {K : Type'} (k : K -> Prop) (i : K) : (k i) = (@I (K -> Prop) k i).
Proof. exact (@lem6784627 K k i). Qed.
Lemma lem6784630 {K : Type'} (k : K -> Prop) (i : K) : (term35 K k i) = (term1117 K k i).
Proof. exact (MK_COMB (@lem6784621) (@lem6784629 K k i)). Qed.
Lemma lem6784631 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6784632 {K : Type'} (k : K -> Prop) (i : K) : (term918 K k i) = (term1118 K k i).
Proof. exact (MK_COMB (@lem6784631) (@lem6784630 K k i)). Qed.
Lemma lem6784633 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i' : K -> K) (i : K) : (term1035 A K ltle k dom f neut i' i) = (term1192 A K ltle k dom f neut i' i).
Proof. exact (MK_COMB (@lem6784632 K k i) (@lem6784620 A K ltle k dom f neut i' i)). Qed.
Lemma lem6784634 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i' : K -> K) : (term1037 A K ltle k dom f neut i') = (term1193 A K ltle k dom f neut i').
Proof. exact (fun_ext (fun i : K => @lem6784633 A K ltle k dom f neut i' i)). Qed.
Lemma lem6784635 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6784636 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i' : K -> K) : (term1039 A K ltle k dom f neut i') = (term1194 A K ltle k dom f neut i').
Proof. exact (MK_COMB (@lem6784635 K) (@lem6784634 A K ltle k dom f neut i')). Qed.
Lemma lem6784637 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6784638 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i' : K -> K) : (term1072 A K ltle k dom f neut i') = (term1195 A K ltle k dom f neut i').
Proof. exact (MK_COMB (@lem6784637) (@lem6784636 A K ltle k dom f neut i')). Qed.
Lemma lem6784639 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1086 A K ltle i' x _88876 k dom f neut) = (term1196 A K ltle i' x _88876 k dom f neut).
Proof. exact (MK_COMB (@lem6784638 A K ltle k dom f neut i') (@lem6784477 A K x _88876 k dom f neut)). Qed.
Lemma lem6784640 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (h1 : term1086 A K ltle i' x _88876 k dom f neut) : term1196 A K ltle i' x _88876 k dom f neut.
Proof. exact (EQ_MP (@lem6784639 A K ltle i' x _88876 k dom f neut) (@lem6784090 A K ltle i' x _88876 k dom f neut h1)). Qed.
Lemma lem6785086 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (h1 : term1086 A K ltle i' x _88876 k dom f neut) : term1148 A K x _88876 k dom f neut.
Proof. exact (proj2 (@lem6784640 A K ltle i' x _88876 k dom f neut h1)). Qed.
Lemma lem6785089 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (h1 : term1086 A K ltle i' x _88876 k dom f neut) : term1146 A K k dom f x neut.
Proof. exact (proj1 (@lem6785086 A K ltle i' x _88876 k dom f neut h1)). Qed.
Lemma lem6785090 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (h1 : term1086 A K ltle i' x _88876 k dom f neut) : term1144 A K dom f x neut.
Proof. exact (proj2 (@lem6785089 A K ltle i' x _88876 k dom f neut h1)). Qed.
Lemma lem6785095 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (h1 : term1116 A K dom f i neut) : term1116 A K dom f i neut.
Proof. exact (h1). Qed.
Lemma lem6785099 {A : Type'} (P : A -> Prop) (Q : Prop) : (term936 A P Q) = (term935 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem6785100 {K : Type'} (P : K -> Prop) (Q : Prop) : (term936 K P Q) = (term935 K P Q).
Proof. exact (@lem6785099 K P Q). Qed.
Lemma lem6785101 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1197 A K _88875 k dom f neut) = (term1198 A K _88875 k dom f neut).
Proof. exact (@lem6785100 K (term1120 A K k dom f neut) (term1108 A K _88875 k dom f neut)). Qed.
Lemma lem6785102 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (x : K) (neut : A) : (term1199 A K k dom f neut x) = (term1119 A K k dom f x neut).
Proof. exact (eq_refl (term1199 A K k dom f neut x)). Qed.
Lemma lem6785103 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1200 A K k dom f neut) = (term1120 A K k dom f neut).
Proof. exact (fun_ext (fun x : K => @lem6785102 A K k dom f x neut)). Qed.
Lemma lem6785104 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6785105 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1201 A K k dom f neut) = (term1121 A K k dom f neut).
Proof. exact (MK_COMB (@lem6785104 K) (@lem6785103 A K k dom f neut)). Qed.
Lemma lem6785106 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6785107 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1202 A K k dom f neut) = (term1122 A K k dom f neut).
Proof. exact (MK_COMB (@lem6785106) (@lem6785105 A K k dom f neut)). Qed.
Lemma lem6785108 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1108 A K _88875 k dom f neut) = (term1108 A K _88875 k dom f neut).
Proof. exact (eq_refl (term1108 A K _88875 k dom f neut)). Qed.
Lemma lem6785109 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1197 A K _88875 k dom f neut) = (term1123 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6785107 A K k dom f neut) (@lem6785108 A K _88875 k dom f neut)). Qed.
Lemma lem6785110 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6785111 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1203 A K _88875 k dom f neut) = (term1204 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6785110) (@lem6785109 A K _88875 k dom f neut)). Qed.
Lemma lem6785112 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (x : K) (neut : A) : (term1199 A K k dom f neut x) = (term1119 A K k dom f x neut).
Proof. exact (eq_refl (term1199 A K k dom f neut x)). Qed.
Lemma lem6785113 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6785114 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (x : K) (neut : A) : (term1205 A K k dom f neut x) = (term1206 A K k dom f x neut).
Proof. exact (MK_COMB (@lem6785113) (@lem6785112 A K k dom f x neut)). Qed.
Lemma lem6785115 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1108 A K _88875 k dom f neut) = (term1108 A K _88875 k dom f neut).
Proof. exact (eq_refl (term1108 A K _88875 k dom f neut)). Qed.
Lemma lem6785116 {A K : Type'} (x : K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1207 A K x _88875 k dom f neut) = (term1208 A K x _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6785114 A K k dom f x neut) (@lem6785115 A K _88875 k dom f neut)). Qed.
Lemma lem6785117 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1209 A K _88875 k dom f neut) = (term1210 A K _88875 k dom f neut).
Proof. exact (fun_ext (fun x : K => @lem6785116 A K x _88875 k dom f neut)). Qed.
Lemma lem6785118 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6785119 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1198 A K _88875 k dom f neut) = (term1211 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6785118 K) (@lem6785117 A K _88875 k dom f neut)). Qed.
Lemma lem6785120 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : ((term1197 A K _88875 k dom f neut) = (term1198 A K _88875 k dom f neut)) = ((term1123 A K _88875 k dom f neut) = (term1211 A K _88875 k dom f neut)).
Proof. exact (MK_COMB (@lem6785111 A K _88875 k dom f neut) (@lem6785119 A K _88875 k dom f neut)). Qed.
Lemma lem6785121 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1123 A K _88875 k dom f neut) = (term1211 A K _88875 k dom f neut).
Proof. exact (EQ_MP (@lem6785120 A K _88875 k dom f neut) (@lem6785101 A K _88875 k dom f neut)). Qed.
Lemma lem6785122 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term1124 A K _88875 k dom f) = (term1212 A K _88875 k dom f).
Proof. exact (fun_ext (fun neut : A => @lem6785121 A K _88875 k dom f neut)). Qed.
Lemma lem6785123 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6785124 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term1125 A K _88875 k dom f) = (term1213 A K _88875 k dom f).
Proof. exact (MK_COMB (@lem6785123 A) (@lem6785122 A K _88875 k dom f)). Qed.
Lemma lem6785125 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) : (term1126 A K _88875 k dom) = (term1214 A K _88875 k dom).
Proof. exact (fun_ext (fun f : K -> A => @lem6785124 A K _88875 k dom f)). Qed.
Lemma lem6785126 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem6785127 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) : (term1127 A K _88875 k dom) = (term1215 A K _88875 k dom).
Proof. exact (MK_COMB (@lem6785126 A K) (@lem6785125 A K _88875 k dom)). Qed.
Lemma lem6785128 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) : (term1128 A K _88875 k) = (term1216 A K _88875 k).
Proof. exact (fun_ext (fun dom : A -> Prop => @lem6785127 A K _88875 k dom)). Qed.
Lemma lem6785129 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6785130 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) : (term1129 A K _88875 k) = (term1217 A K _88875 k).
Proof. exact (MK_COMB (@lem6785129 A) (@lem6785128 A K _88875 k)). Qed.
Lemma lem6785131 {A K : Type'} (_88875 : type836 A K) : (term1130 A K _88875) = (term1218 A K _88875).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6785130 A K _88875 k)). Qed.
Lemma lem6785132 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6785133 {A K : Type'} (_88875 : type836 A K) : (term1131 A K _88875) = (term1219 A K _88875).
Proof. exact (MK_COMB (@lem6785132 K) (@lem6785131 A K _88875)). Qed.
Lemma lem6785159 {A K : Type'} (x : K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1208 A K x _88875 k dom f neut) = (term1220 A K x _88875 k dom f neut).
Proof. exact (@lem19490 (term1106 A K _88875 k dom f neut) (term1119 A K k dom f x neut) (term1104 A K _88875 k dom f neut)). Qed.
Lemma lem6785166 {A K : Type'} (x : K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1221 A K x _88875 k dom f neut) = (term1222 A K x _88875 k dom f neut).
Proof. exact (@lem19490 (term1102 A K _88875 k dom f neut) (term1119 A K k dom f x neut) (term1100 A K _88875 k dom f neut)). Qed.
Lemma lem6785169 {A K : Type'} (x : K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1223 A K x _88875 k dom f neut) = (term1223 A K x _88875 k dom f neut).
Proof. exact (eq_refl (term1223 A K x _88875 k dom f neut)). Qed.
Lemma lem6785170 {A K : Type'} (x : K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1220 A K x _88875 k dom f neut) = (term1224 A K x _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6785169 A K x _88875 k dom f neut) (@lem6785166 A K x _88875 k dom f neut)). Qed.
Lemma lem6785172 {A K : Type'} (x : K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1208 A K x _88875 k dom f neut) = (term1224 A K x _88875 k dom f neut).
Proof. exact (TRANS (@lem6785159 A K x _88875 k dom f neut) (@lem6785170 A K x _88875 k dom f neut)). Qed.
Lemma lem6785173 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1210 A K _88875 k dom f neut) = (term1225 A K _88875 k dom f neut).
Proof. exact (fun_ext (fun x : K => @lem6785172 A K x _88875 k dom f neut)). Qed.
Lemma lem6785174 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6785175 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1211 A K _88875 k dom f neut) = (term1226 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6785174 K) (@lem6785173 A K _88875 k dom f neut)). Qed.
Lemma lem6785176 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term1212 A K _88875 k dom f) = (term1227 A K _88875 k dom f).
Proof. exact (fun_ext (fun neut : A => @lem6785175 A K _88875 k dom f neut)). Qed.
Lemma lem6785177 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6785178 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term1213 A K _88875 k dom f) = (term1228 A K _88875 k dom f).
Proof. exact (MK_COMB (@lem6785177 A) (@lem6785176 A K _88875 k dom f)). Qed.
Lemma lem6785179 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) : (term1214 A K _88875 k dom) = (term1229 A K _88875 k dom).
Proof. exact (fun_ext (fun f : K -> A => @lem6785178 A K _88875 k dom f)). Qed.
Lemma lem6785180 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem6785181 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) : (term1215 A K _88875 k dom) = (term1230 A K _88875 k dom).
Proof. exact (MK_COMB (@lem6785180 A K) (@lem6785179 A K _88875 k dom)). Qed.
Lemma lem6785182 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) : (term1216 A K _88875 k) = (term1231 A K _88875 k).
Proof. exact (fun_ext (fun dom : A -> Prop => @lem6785181 A K _88875 k dom)). Qed.
Lemma lem6785183 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6785184 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) : (term1217 A K _88875 k) = (term1232 A K _88875 k).
Proof. exact (MK_COMB (@lem6785183 A) (@lem6785182 A K _88875 k)). Qed.
Lemma lem6785185 {A K : Type'} (_88875 : type836 A K) : (term1218 A K _88875) = (term1233 A K _88875).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6785184 A K _88875 k)). Qed.
Lemma lem6785186 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6785187 {A K : Type'} (_88875 : type836 A K) : (term1219 A K _88875) = (term1234 A K _88875).
Proof. exact (MK_COMB (@lem6785186 K) (@lem6785185 A K _88875)). Qed.
Lemma lem6785188 {A K : Type'} (_88875 : type836 A K) : (term1131 A K _88875) = (term1234 A K _88875).
Proof. exact (TRANS (@lem6785133 A K _88875) (@lem6785187 A K _88875)). Qed.
Lemma lem6785189 {A K : Type'} (_88875 : type836 A K) (h1 : term446 A K _88875) : term1234 A K _88875.
Proof. exact (EQ_MP (@lem6785188 A K _88875) (@lem6784298 A K _88875 h1)). Qed.
Lemma lem6785389 {K : Type'} (k : K -> Prop) (i : K) (h1 : term1117 K k i) : term1117 K k i.
Proof. exact (h1). Qed.
Lemma lem6785391 {A : Type'} (P : A -> Prop) (Q : Prop) : (term936 A P Q) = (term935 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem6785392 {K : Type'} (P : K -> Prop) (Q : Prop) : (term936 K P Q) = (term935 K P Q).
Proof. exact (@lem6785391 K P Q). Qed.
Lemma lem6785393 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1197 A K _88875 k dom f neut) = (term1198 A K _88875 k dom f neut).
Proof. exact (@lem6785392 K (term1120 A K k dom f neut) (term1108 A K _88875 k dom f neut)). Qed.
Lemma lem6785394 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (x : K) (neut : A) : (term1199 A K k dom f neut x) = (term1119 A K k dom f x neut).
Proof. exact (eq_refl (term1199 A K k dom f neut x)). Qed.
Lemma lem6785395 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1200 A K k dom f neut) = (term1120 A K k dom f neut).
Proof. exact (fun_ext (fun x : K => @lem6785394 A K k dom f x neut)). Qed.
Lemma lem6785396 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6785397 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1201 A K k dom f neut) = (term1121 A K k dom f neut).
Proof. exact (MK_COMB (@lem6785396 K) (@lem6785395 A K k dom f neut)). Qed.
Lemma lem6785398 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6785399 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1202 A K k dom f neut) = (term1122 A K k dom f neut).
Proof. exact (MK_COMB (@lem6785398) (@lem6785397 A K k dom f neut)). Qed.
Lemma lem6785400 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1108 A K _88875 k dom f neut) = (term1108 A K _88875 k dom f neut).
Proof. exact (eq_refl (term1108 A K _88875 k dom f neut)). Qed.
Lemma lem6785401 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1197 A K _88875 k dom f neut) = (term1123 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6785399 A K k dom f neut) (@lem6785400 A K _88875 k dom f neut)). Qed.
Lemma lem6785402 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6785403 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1203 A K _88875 k dom f neut) = (term1204 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6785402) (@lem6785401 A K _88875 k dom f neut)). Qed.
Lemma lem6785404 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (x : K) (neut : A) : (term1199 A K k dom f neut x) = (term1119 A K k dom f x neut).
Proof. exact (eq_refl (term1199 A K k dom f neut x)). Qed.
Lemma lem6785405 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6785406 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (x : K) (neut : A) : (term1205 A K k dom f neut x) = (term1206 A K k dom f x neut).
Proof. exact (MK_COMB (@lem6785405) (@lem6785404 A K k dom f x neut)). Qed.
Lemma lem6785407 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1108 A K _88875 k dom f neut) = (term1108 A K _88875 k dom f neut).
Proof. exact (eq_refl (term1108 A K _88875 k dom f neut)). Qed.
Lemma lem6785408 {A K : Type'} (x : K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1207 A K x _88875 k dom f neut) = (term1208 A K x _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6785406 A K k dom f x neut) (@lem6785407 A K _88875 k dom f neut)). Qed.
Lemma lem6785409 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1209 A K _88875 k dom f neut) = (term1210 A K _88875 k dom f neut).
Proof. exact (fun_ext (fun x : K => @lem6785408 A K x _88875 k dom f neut)). Qed.
Lemma lem6785410 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6785411 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1198 A K _88875 k dom f neut) = (term1211 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6785410 K) (@lem6785409 A K _88875 k dom f neut)). Qed.
Lemma lem6785412 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : ((term1197 A K _88875 k dom f neut) = (term1198 A K _88875 k dom f neut)) = ((term1123 A K _88875 k dom f neut) = (term1211 A K _88875 k dom f neut)).
Proof. exact (MK_COMB (@lem6785403 A K _88875 k dom f neut) (@lem6785411 A K _88875 k dom f neut)). Qed.
Lemma lem6785413 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1123 A K _88875 k dom f neut) = (term1211 A K _88875 k dom f neut).
Proof. exact (EQ_MP (@lem6785412 A K _88875 k dom f neut) (@lem6785393 A K _88875 k dom f neut)). Qed.
Lemma lem6785414 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term1124 A K _88875 k dom f) = (term1212 A K _88875 k dom f).
Proof. exact (fun_ext (fun neut : A => @lem6785413 A K _88875 k dom f neut)). Qed.
Lemma lem6785415 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6785416 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term1125 A K _88875 k dom f) = (term1213 A K _88875 k dom f).
Proof. exact (MK_COMB (@lem6785415 A) (@lem6785414 A K _88875 k dom f)). Qed.
Lemma lem6785417 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) : (term1126 A K _88875 k dom) = (term1214 A K _88875 k dom).
Proof. exact (fun_ext (fun f : K -> A => @lem6785416 A K _88875 k dom f)). Qed.
Lemma lem6785418 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem6785419 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) : (term1127 A K _88875 k dom) = (term1215 A K _88875 k dom).
Proof. exact (MK_COMB (@lem6785418 A K) (@lem6785417 A K _88875 k dom)). Qed.
Lemma lem6785420 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) : (term1128 A K _88875 k) = (term1216 A K _88875 k).
Proof. exact (fun_ext (fun dom : A -> Prop => @lem6785419 A K _88875 k dom)). Qed.
Lemma lem6785421 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6785422 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) : (term1129 A K _88875 k) = (term1217 A K _88875 k).
Proof. exact (MK_COMB (@lem6785421 A) (@lem6785420 A K _88875 k)). Qed.
Lemma lem6785423 {A K : Type'} (_88875 : type836 A K) : (term1130 A K _88875) = (term1218 A K _88875).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6785422 A K _88875 k)). Qed.
Lemma lem6785424 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6785425 {A K : Type'} (_88875 : type836 A K) : (term1131 A K _88875) = (term1219 A K _88875).
Proof. exact (MK_COMB (@lem6785424 K) (@lem6785423 A K _88875)). Qed.
Lemma lem6785451 {A K : Type'} (x : K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1208 A K x _88875 k dom f neut) = (term1220 A K x _88875 k dom f neut).
Proof. exact (@lem19490 (term1106 A K _88875 k dom f neut) (term1119 A K k dom f x neut) (term1104 A K _88875 k dom f neut)). Qed.
Lemma lem6785458 {A K : Type'} (x : K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1221 A K x _88875 k dom f neut) = (term1222 A K x _88875 k dom f neut).
Proof. exact (@lem19490 (term1102 A K _88875 k dom f neut) (term1119 A K k dom f x neut) (term1100 A K _88875 k dom f neut)). Qed.
Lemma lem6785461 {A K : Type'} (x : K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1223 A K x _88875 k dom f neut) = (term1223 A K x _88875 k dom f neut).
Proof. exact (eq_refl (term1223 A K x _88875 k dom f neut)). Qed.
Lemma lem6785462 {A K : Type'} (x : K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1220 A K x _88875 k dom f neut) = (term1224 A K x _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6785461 A K x _88875 k dom f neut) (@lem6785458 A K x _88875 k dom f neut)). Qed.
Lemma lem6785464 {A K : Type'} (x : K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1208 A K x _88875 k dom f neut) = (term1224 A K x _88875 k dom f neut).
Proof. exact (TRANS (@lem6785451 A K x _88875 k dom f neut) (@lem6785462 A K x _88875 k dom f neut)). Qed.
Lemma lem6785465 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1210 A K _88875 k dom f neut) = (term1225 A K _88875 k dom f neut).
Proof. exact (fun_ext (fun x : K => @lem6785464 A K x _88875 k dom f neut)). Qed.
Lemma lem6785466 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6785467 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1211 A K _88875 k dom f neut) = (term1226 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6785466 K) (@lem6785465 A K _88875 k dom f neut)). Qed.
Lemma lem6785468 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term1212 A K _88875 k dom f) = (term1227 A K _88875 k dom f).
Proof. exact (fun_ext (fun neut : A => @lem6785467 A K _88875 k dom f neut)). Qed.
Lemma lem6785469 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6785470 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term1213 A K _88875 k dom f) = (term1228 A K _88875 k dom f).
Proof. exact (MK_COMB (@lem6785469 A) (@lem6785468 A K _88875 k dom f)). Qed.
Lemma lem6785471 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) : (term1214 A K _88875 k dom) = (term1229 A K _88875 k dom).
Proof. exact (fun_ext (fun f : K -> A => @lem6785470 A K _88875 k dom f)). Qed.
Lemma lem6785472 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem6785473 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) : (term1215 A K _88875 k dom) = (term1230 A K _88875 k dom).
Proof. exact (MK_COMB (@lem6785472 A K) (@lem6785471 A K _88875 k dom)). Qed.
Lemma lem6785474 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) : (term1216 A K _88875 k) = (term1231 A K _88875 k).
Proof. exact (fun_ext (fun dom : A -> Prop => @lem6785473 A K _88875 k dom)). Qed.
Lemma lem6785475 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6785476 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) : (term1217 A K _88875 k) = (term1232 A K _88875 k).
Proof. exact (MK_COMB (@lem6785475 A) (@lem6785474 A K _88875 k)). Qed.
Lemma lem6785477 {A K : Type'} (_88875 : type836 A K) : (term1218 A K _88875) = (term1233 A K _88875).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6785476 A K _88875 k)). Qed.
Lemma lem6785478 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6785479 {A K : Type'} (_88875 : type836 A K) : (term1219 A K _88875) = (term1234 A K _88875).
Proof. exact (MK_COMB (@lem6785478 K) (@lem6785477 A K _88875)). Qed.
Lemma lem6785480 {A K : Type'} (_88875 : type836 A K) : (term1131 A K _88875) = (term1234 A K _88875).
Proof. exact (TRANS (@lem6785425 A K _88875) (@lem6785479 A K _88875)). Qed.
Lemma lem6785481 {A K : Type'} (_88875 : type836 A K) (h1 : term446 A K _88875) : term1234 A K _88875.
Proof. exact (EQ_MP (@lem6785480 A K _88875) (@lem6784298 A K _88875 h1)). Qed.
Lemma lem6785681 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) (h1 : term1114 A K dom f i) : term1114 A K dom f i.
Proof. exact (h1). Qed.
Lemma lem6785683 {A : Type'} (P : A -> Prop) (Q : Prop) : (term936 A P Q) = (term935 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem6785684 {K : Type'} (P : K -> Prop) (Q : Prop) : (term936 K P Q) = (term935 K P Q).
Proof. exact (@lem6785683 K P Q). Qed.
Lemma lem6785685 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1197 A K _88875 k dom f neut) = (term1198 A K _88875 k dom f neut).
Proof. exact (@lem6785684 K (term1120 A K k dom f neut) (term1108 A K _88875 k dom f neut)). Qed.
Lemma lem6785686 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (x : K) (neut : A) : (term1199 A K k dom f neut x) = (term1119 A K k dom f x neut).
Proof. exact (eq_refl (term1199 A K k dom f neut x)). Qed.
Lemma lem6785687 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1200 A K k dom f neut) = (term1120 A K k dom f neut).
Proof. exact (fun_ext (fun x : K => @lem6785686 A K k dom f x neut)). Qed.
Lemma lem6785688 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6785689 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1201 A K k dom f neut) = (term1121 A K k dom f neut).
Proof. exact (MK_COMB (@lem6785688 K) (@lem6785687 A K k dom f neut)). Qed.
Lemma lem6785690 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6785691 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1202 A K k dom f neut) = (term1122 A K k dom f neut).
Proof. exact (MK_COMB (@lem6785690) (@lem6785689 A K k dom f neut)). Qed.
Lemma lem6785692 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1108 A K _88875 k dom f neut) = (term1108 A K _88875 k dom f neut).
Proof. exact (eq_refl (term1108 A K _88875 k dom f neut)). Qed.
Lemma lem6785693 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1197 A K _88875 k dom f neut) = (term1123 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6785691 A K k dom f neut) (@lem6785692 A K _88875 k dom f neut)). Qed.
Lemma lem6785694 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6785695 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1203 A K _88875 k dom f neut) = (term1204 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6785694) (@lem6785693 A K _88875 k dom f neut)). Qed.
Lemma lem6785696 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (x : K) (neut : A) : (term1199 A K k dom f neut x) = (term1119 A K k dom f x neut).
Proof. exact (eq_refl (term1199 A K k dom f neut x)). Qed.
Lemma lem6785697 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6785698 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (x : K) (neut : A) : (term1205 A K k dom f neut x) = (term1206 A K k dom f x neut).
Proof. exact (MK_COMB (@lem6785697) (@lem6785696 A K k dom f x neut)). Qed.
Lemma lem6785699 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1108 A K _88875 k dom f neut) = (term1108 A K _88875 k dom f neut).
Proof. exact (eq_refl (term1108 A K _88875 k dom f neut)). Qed.
Lemma lem6785700 {A K : Type'} (x : K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1207 A K x _88875 k dom f neut) = (term1208 A K x _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6785698 A K k dom f x neut) (@lem6785699 A K _88875 k dom f neut)). Qed.
Lemma lem6785701 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1209 A K _88875 k dom f neut) = (term1210 A K _88875 k dom f neut).
Proof. exact (fun_ext (fun x : K => @lem6785700 A K x _88875 k dom f neut)). Qed.
Lemma lem6785702 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6785703 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1198 A K _88875 k dom f neut) = (term1211 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6785702 K) (@lem6785701 A K _88875 k dom f neut)). Qed.
Lemma lem6785704 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : ((term1197 A K _88875 k dom f neut) = (term1198 A K _88875 k dom f neut)) = ((term1123 A K _88875 k dom f neut) = (term1211 A K _88875 k dom f neut)).
Proof. exact (MK_COMB (@lem6785695 A K _88875 k dom f neut) (@lem6785703 A K _88875 k dom f neut)). Qed.
Lemma lem6785705 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1123 A K _88875 k dom f neut) = (term1211 A K _88875 k dom f neut).
Proof. exact (EQ_MP (@lem6785704 A K _88875 k dom f neut) (@lem6785685 A K _88875 k dom f neut)). Qed.
Lemma lem6785706 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term1124 A K _88875 k dom f) = (term1212 A K _88875 k dom f).
Proof. exact (fun_ext (fun neut : A => @lem6785705 A K _88875 k dom f neut)). Qed.
Lemma lem6785707 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6785708 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term1125 A K _88875 k dom f) = (term1213 A K _88875 k dom f).
Proof. exact (MK_COMB (@lem6785707 A) (@lem6785706 A K _88875 k dom f)). Qed.
Lemma lem6785709 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) : (term1126 A K _88875 k dom) = (term1214 A K _88875 k dom).
Proof. exact (fun_ext (fun f : K -> A => @lem6785708 A K _88875 k dom f)). Qed.
Lemma lem6785710 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem6785711 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) : (term1127 A K _88875 k dom) = (term1215 A K _88875 k dom).
Proof. exact (MK_COMB (@lem6785710 A K) (@lem6785709 A K _88875 k dom)). Qed.
Lemma lem6785712 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) : (term1128 A K _88875 k) = (term1216 A K _88875 k).
Proof. exact (fun_ext (fun dom : A -> Prop => @lem6785711 A K _88875 k dom)). Qed.
Lemma lem6785713 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6785714 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) : (term1129 A K _88875 k) = (term1217 A K _88875 k).
Proof. exact (MK_COMB (@lem6785713 A) (@lem6785712 A K _88875 k)). Qed.
Lemma lem6785715 {A K : Type'} (_88875 : type836 A K) : (term1130 A K _88875) = (term1218 A K _88875).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6785714 A K _88875 k)). Qed.
Lemma lem6785716 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6785717 {A K : Type'} (_88875 : type836 A K) : (term1131 A K _88875) = (term1219 A K _88875).
Proof. exact (MK_COMB (@lem6785716 K) (@lem6785715 A K _88875)). Qed.
Lemma lem6785743 {A K : Type'} (x : K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1208 A K x _88875 k dom f neut) = (term1220 A K x _88875 k dom f neut).
Proof. exact (@lem19490 (term1106 A K _88875 k dom f neut) (term1119 A K k dom f x neut) (term1104 A K _88875 k dom f neut)). Qed.
Lemma lem6785750 {A K : Type'} (x : K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1221 A K x _88875 k dom f neut) = (term1222 A K x _88875 k dom f neut).
Proof. exact (@lem19490 (term1102 A K _88875 k dom f neut) (term1119 A K k dom f x neut) (term1100 A K _88875 k dom f neut)). Qed.
Lemma lem6785753 {A K : Type'} (x : K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1223 A K x _88875 k dom f neut) = (term1223 A K x _88875 k dom f neut).
Proof. exact (eq_refl (term1223 A K x _88875 k dom f neut)). Qed.
Lemma lem6785754 {A K : Type'} (x : K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1220 A K x _88875 k dom f neut) = (term1224 A K x _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6785753 A K x _88875 k dom f neut) (@lem6785750 A K x _88875 k dom f neut)). Qed.
Lemma lem6785756 {A K : Type'} (x : K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1208 A K x _88875 k dom f neut) = (term1224 A K x _88875 k dom f neut).
Proof. exact (TRANS (@lem6785743 A K x _88875 k dom f neut) (@lem6785754 A K x _88875 k dom f neut)). Qed.
Lemma lem6785757 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1210 A K _88875 k dom f neut) = (term1225 A K _88875 k dom f neut).
Proof. exact (fun_ext (fun x : K => @lem6785756 A K x _88875 k dom f neut)). Qed.
Lemma lem6785758 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6785759 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1211 A K _88875 k dom f neut) = (term1226 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6785758 K) (@lem6785757 A K _88875 k dom f neut)). Qed.
Lemma lem6785760 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term1212 A K _88875 k dom f) = (term1227 A K _88875 k dom f).
Proof. exact (fun_ext (fun neut : A => @lem6785759 A K _88875 k dom f neut)). Qed.
Lemma lem6785761 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6785762 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) : (term1213 A K _88875 k dom f) = (term1228 A K _88875 k dom f).
Proof. exact (MK_COMB (@lem6785761 A) (@lem6785760 A K _88875 k dom f)). Qed.
Lemma lem6785763 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) : (term1214 A K _88875 k dom) = (term1229 A K _88875 k dom).
Proof. exact (fun_ext (fun f : K -> A => @lem6785762 A K _88875 k dom f)). Qed.
Lemma lem6785764 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem6785765 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) : (term1215 A K _88875 k dom) = (term1230 A K _88875 k dom).
Proof. exact (MK_COMB (@lem6785764 A K) (@lem6785763 A K _88875 k dom)). Qed.
Lemma lem6785766 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) : (term1216 A K _88875 k) = (term1231 A K _88875 k).
Proof. exact (fun_ext (fun dom : A -> Prop => @lem6785765 A K _88875 k dom)). Qed.
Lemma lem6785767 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6785768 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) : (term1217 A K _88875 k) = (term1232 A K _88875 k).
Proof. exact (MK_COMB (@lem6785767 A) (@lem6785766 A K _88875 k)). Qed.
Lemma lem6785769 {A K : Type'} (_88875 : type836 A K) : (term1218 A K _88875) = (term1233 A K _88875).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6785768 A K _88875 k)). Qed.
Lemma lem6785770 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6785771 {A K : Type'} (_88875 : type836 A K) : (term1219 A K _88875) = (term1234 A K _88875).
Proof. exact (MK_COMB (@lem6785770 K) (@lem6785769 A K _88875)). Qed.
Lemma lem6785772 {A K : Type'} (_88875 : type836 A K) : (term1131 A K _88875) = (term1234 A K _88875).
Proof. exact (TRANS (@lem6785717 A K _88875) (@lem6785771 A K _88875)). Qed.
Lemma lem6785773 {A K : Type'} (_88875 : type836 A K) (h1 : term446 A K _88875) : term1234 A K _88875.
Proof. exact (EQ_MP (@lem6785772 A K _88875) (@lem6784298 A K _88875 h1)). Qed.
Lemma lem6785973 {A K : Type'} (f : K -> A) (i : K) (neut : A) (h1 : (@I (K -> A) f i) = neut) : (@I (K -> A) f i) = neut.
Proof. exact (h1). Qed.
Lemma lem6785974 {A K : Type'} (_88877 : K -> Prop) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1235 A K _88875 _88877.
Proof. exact (@lem6785189 A K _88875 h1 _88877). Qed.
Lemma lem6785975 {A K : Type'} (_88875 : type836 A K) (_88877 : K -> Prop) : (term1235 A K _88875 _88877) = (term1232 A K _88875 _88877).
Proof. exact (eq_refl (term1235 A K _88875 _88877)). Qed.
Lemma lem6785976 {A K : Type'} (_88877 : K -> Prop) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1232 A K _88875 _88877.
Proof. exact (EQ_MP (@lem6785975 A K _88875 _88877) (@lem6785974 A K _88877 _88875 h1)). Qed.
Lemma lem6785977 {A K : Type'} (_88877 : K -> Prop) (_88878 : A -> Prop) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1236 A K _88875 _88877 _88878.
Proof. exact (@lem6785976 A K _88877 _88875 h1 _88878). Qed.
Lemma lem6785978 {A K : Type'} (_88875 : type836 A K) (_88877 : K -> Prop) (_88878 : A -> Prop) : (term1236 A K _88875 _88877 _88878) = (term1230 A K _88875 _88877 _88878).
Proof. exact (eq_refl (term1236 A K _88875 _88877 _88878)). Qed.
Lemma lem6785979 {A K : Type'} (_88877 : K -> Prop) (_88878 : A -> Prop) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1230 A K _88875 _88877 _88878.
Proof. exact (EQ_MP (@lem6785978 A K _88875 _88877 _88878) (@lem6785977 A K _88877 _88878 _88875 h1)). Qed.
Lemma lem6785980 {A K : Type'} (_88877 : K -> Prop) (_88878 : A -> Prop) (_88879 : K -> A) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1237 A K _88875 _88877 _88878 _88879.
Proof. exact (@lem6785979 A K _88877 _88878 _88875 h1 _88879). Qed.
Lemma lem6785981 {A K : Type'} (_88875 : type836 A K) (_88877 : K -> Prop) (_88878 : A -> Prop) (_88879 : K -> A) : (term1237 A K _88875 _88877 _88878 _88879) = (term1228 A K _88875 _88877 _88878 _88879).
Proof. exact (eq_refl (term1237 A K _88875 _88877 _88878 _88879)). Qed.
Lemma lem6785982 {A K : Type'} (_88877 : K -> Prop) (_88878 : A -> Prop) (_88879 : K -> A) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1228 A K _88875 _88877 _88878 _88879.
Proof. exact (EQ_MP (@lem6785981 A K _88875 _88877 _88878 _88879) (@lem6785980 A K _88877 _88878 _88879 _88875 h1)). Qed.
Lemma lem6785983 {A K : Type'} (_88877 : K -> Prop) (_88878 : A -> Prop) (_88879 : K -> A) (_88880 : A) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1238 A K _88875 _88877 _88878 _88879 _88880.
Proof. exact (@lem6785982 A K _88877 _88878 _88879 _88875 h1 _88880). Qed.
Lemma lem6785984 {A K : Type'} (_88875 : type836 A K) (_88877 : K -> Prop) (_88878 : A -> Prop) (_88879 : K -> A) (_88880 : A) : (term1238 A K _88875 _88877 _88878 _88879 _88880) = (term1226 A K _88875 _88877 _88878 _88879 _88880).
Proof. exact (eq_refl (term1238 A K _88875 _88877 _88878 _88879 _88880)). Qed.
Lemma lem6785985 {A K : Type'} (_88877 : K -> Prop) (_88878 : A -> Prop) (_88879 : K -> A) (_88880 : A) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1226 A K _88875 _88877 _88878 _88879 _88880.
Proof. exact (EQ_MP (@lem6785984 A K _88875 _88877 _88878 _88879 _88880) (@lem6785983 A K _88877 _88878 _88879 _88880 _88875 h1)). Qed.
Lemma lem6785986 {A K : Type'} (_88877 : K -> Prop) (_88878 : A -> Prop) (_88879 : K -> A) (_88880 : A) (_88881 : K) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1239 A K _88875 _88877 _88878 _88879 _88880 _88881.
Proof. exact (@lem6785985 A K _88877 _88878 _88879 _88880 _88875 h1 _88881). Qed.
Lemma lem6785987 {A K : Type'} (_88881 : K) (_88875 : type836 A K) (_88877 : K -> Prop) (_88878 : A -> Prop) (_88879 : K -> A) (_88880 : A) : (term1239 A K _88875 _88877 _88878 _88879 _88880 _88881) = (term1224 A K _88881 _88875 _88877 _88878 _88879 _88880).
Proof. exact (eq_refl (term1239 A K _88875 _88877 _88878 _88879 _88880 _88881)). Qed.
Lemma lem6785988 {A K : Type'} (_88881 : K) (_88877 : K -> Prop) (_88878 : A -> Prop) (_88879 : K -> A) (_88880 : A) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1224 A K _88881 _88875 _88877 _88878 _88879 _88880.
Proof. exact (EQ_MP (@lem6785987 A K _88881 _88875 _88877 _88878 _88879 _88880) (@lem6785986 A K _88877 _88878 _88879 _88880 _88881 _88875 h1)). Qed.
Lemma lem6786025 {A K : Type'} (_88894 : K -> Prop) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1235 A K _88875 _88894.
Proof. exact (@lem6785481 A K _88875 h1 _88894). Qed.
Lemma lem6786026 {A K : Type'} (_88875 : type836 A K) (_88894 : K -> Prop) : (term1235 A K _88875 _88894) = (term1232 A K _88875 _88894).
Proof. exact (eq_refl (term1235 A K _88875 _88894)). Qed.
Lemma lem6786027 {A K : Type'} (_88894 : K -> Prop) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1232 A K _88875 _88894.
Proof. exact (EQ_MP (@lem6786026 A K _88875 _88894) (@lem6786025 A K _88894 _88875 h1)). Qed.
Lemma lem6786028 {A K : Type'} (_88894 : K -> Prop) (_88895 : A -> Prop) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1236 A K _88875 _88894 _88895.
Proof. exact (@lem6786027 A K _88894 _88875 h1 _88895). Qed.
Lemma lem6786029 {A K : Type'} (_88875 : type836 A K) (_88894 : K -> Prop) (_88895 : A -> Prop) : (term1236 A K _88875 _88894 _88895) = (term1230 A K _88875 _88894 _88895).
Proof. exact (eq_refl (term1236 A K _88875 _88894 _88895)). Qed.
Lemma lem6786030 {A K : Type'} (_88894 : K -> Prop) (_88895 : A -> Prop) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1230 A K _88875 _88894 _88895.
Proof. exact (EQ_MP (@lem6786029 A K _88875 _88894 _88895) (@lem6786028 A K _88894 _88895 _88875 h1)). Qed.
Lemma lem6786031 {A K : Type'} (_88894 : K -> Prop) (_88895 : A -> Prop) (_88896 : K -> A) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1237 A K _88875 _88894 _88895 _88896.
Proof. exact (@lem6786030 A K _88894 _88895 _88875 h1 _88896). Qed.
Lemma lem6786032 {A K : Type'} (_88875 : type836 A K) (_88894 : K -> Prop) (_88895 : A -> Prop) (_88896 : K -> A) : (term1237 A K _88875 _88894 _88895 _88896) = (term1228 A K _88875 _88894 _88895 _88896).
Proof. exact (eq_refl (term1237 A K _88875 _88894 _88895 _88896)). Qed.
Lemma lem6786033 {A K : Type'} (_88894 : K -> Prop) (_88895 : A -> Prop) (_88896 : K -> A) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1228 A K _88875 _88894 _88895 _88896.
Proof. exact (EQ_MP (@lem6786032 A K _88875 _88894 _88895 _88896) (@lem6786031 A K _88894 _88895 _88896 _88875 h1)). Qed.
Lemma lem6786034 {A K : Type'} (_88894 : K -> Prop) (_88895 : A -> Prop) (_88896 : K -> A) (_88897 : A) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1238 A K _88875 _88894 _88895 _88896 _88897.
Proof. exact (@lem6786033 A K _88894 _88895 _88896 _88875 h1 _88897). Qed.
Lemma lem6786035 {A K : Type'} (_88875 : type836 A K) (_88894 : K -> Prop) (_88895 : A -> Prop) (_88896 : K -> A) (_88897 : A) : (term1238 A K _88875 _88894 _88895 _88896 _88897) = (term1226 A K _88875 _88894 _88895 _88896 _88897).
Proof. exact (eq_refl (term1238 A K _88875 _88894 _88895 _88896 _88897)). Qed.
Lemma lem6786036 {A K : Type'} (_88894 : K -> Prop) (_88895 : A -> Prop) (_88896 : K -> A) (_88897 : A) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1226 A K _88875 _88894 _88895 _88896 _88897.
Proof. exact (EQ_MP (@lem6786035 A K _88875 _88894 _88895 _88896 _88897) (@lem6786034 A K _88894 _88895 _88896 _88897 _88875 h1)). Qed.
Lemma lem6786037 {A K : Type'} (_88894 : K -> Prop) (_88895 : A -> Prop) (_88896 : K -> A) (_88897 : A) (_88898 : K) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1239 A K _88875 _88894 _88895 _88896 _88897 _88898.
Proof. exact (@lem6786036 A K _88894 _88895 _88896 _88897 _88875 h1 _88898). Qed.
Lemma lem6786038 {A K : Type'} (_88898 : K) (_88875 : type836 A K) (_88894 : K -> Prop) (_88895 : A -> Prop) (_88896 : K -> A) (_88897 : A) : (term1239 A K _88875 _88894 _88895 _88896 _88897 _88898) = (term1224 A K _88898 _88875 _88894 _88895 _88896 _88897).
Proof. exact (eq_refl (term1239 A K _88875 _88894 _88895 _88896 _88897 _88898)). Qed.
Lemma lem6786039 {A K : Type'} (_88898 : K) (_88894 : K -> Prop) (_88895 : A -> Prop) (_88896 : K -> A) (_88897 : A) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1224 A K _88898 _88875 _88894 _88895 _88896 _88897.
Proof. exact (EQ_MP (@lem6786038 A K _88898 _88875 _88894 _88895 _88896 _88897) (@lem6786037 A K _88894 _88895 _88896 _88897 _88898 _88875 h1)). Qed.
Lemma lem6786076 {A K : Type'} (_88911 : K -> Prop) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1235 A K _88875 _88911.
Proof. exact (@lem6785773 A K _88875 h1 _88911). Qed.
Lemma lem6786077 {A K : Type'} (_88875 : type836 A K) (_88911 : K -> Prop) : (term1235 A K _88875 _88911) = (term1232 A K _88875 _88911).
Proof. exact (eq_refl (term1235 A K _88875 _88911)). Qed.
Lemma lem6786078 {A K : Type'} (_88911 : K -> Prop) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1232 A K _88875 _88911.
Proof. exact (EQ_MP (@lem6786077 A K _88875 _88911) (@lem6786076 A K _88911 _88875 h1)). Qed.
Lemma lem6786079 {A K : Type'} (_88911 : K -> Prop) (_88912 : A -> Prop) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1236 A K _88875 _88911 _88912.
Proof. exact (@lem6786078 A K _88911 _88875 h1 _88912). Qed.
Lemma lem6786080 {A K : Type'} (_88875 : type836 A K) (_88911 : K -> Prop) (_88912 : A -> Prop) : (term1236 A K _88875 _88911 _88912) = (term1230 A K _88875 _88911 _88912).
Proof. exact (eq_refl (term1236 A K _88875 _88911 _88912)). Qed.
Lemma lem6786081 {A K : Type'} (_88911 : K -> Prop) (_88912 : A -> Prop) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1230 A K _88875 _88911 _88912.
Proof. exact (EQ_MP (@lem6786080 A K _88875 _88911 _88912) (@lem6786079 A K _88911 _88912 _88875 h1)). Qed.
Lemma lem6786082 {A K : Type'} (_88911 : K -> Prop) (_88912 : A -> Prop) (_88913 : K -> A) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1237 A K _88875 _88911 _88912 _88913.
Proof. exact (@lem6786081 A K _88911 _88912 _88875 h1 _88913). Qed.
Lemma lem6786083 {A K : Type'} (_88875 : type836 A K) (_88911 : K -> Prop) (_88912 : A -> Prop) (_88913 : K -> A) : (term1237 A K _88875 _88911 _88912 _88913) = (term1228 A K _88875 _88911 _88912 _88913).
Proof. exact (eq_refl (term1237 A K _88875 _88911 _88912 _88913)). Qed.
Lemma lem6786084 {A K : Type'} (_88911 : K -> Prop) (_88912 : A -> Prop) (_88913 : K -> A) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1228 A K _88875 _88911 _88912 _88913.
Proof. exact (EQ_MP (@lem6786083 A K _88875 _88911 _88912 _88913) (@lem6786082 A K _88911 _88912 _88913 _88875 h1)). Qed.
Lemma lem6786085 {A K : Type'} (_88911 : K -> Prop) (_88912 : A -> Prop) (_88913 : K -> A) (_88914 : A) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1238 A K _88875 _88911 _88912 _88913 _88914.
Proof. exact (@lem6786084 A K _88911 _88912 _88913 _88875 h1 _88914). Qed.
Lemma lem6786086 {A K : Type'} (_88875 : type836 A K) (_88911 : K -> Prop) (_88912 : A -> Prop) (_88913 : K -> A) (_88914 : A) : (term1238 A K _88875 _88911 _88912 _88913 _88914) = (term1226 A K _88875 _88911 _88912 _88913 _88914).
Proof. exact (eq_refl (term1238 A K _88875 _88911 _88912 _88913 _88914)). Qed.
Lemma lem6786087 {A K : Type'} (_88911 : K -> Prop) (_88912 : A -> Prop) (_88913 : K -> A) (_88914 : A) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1226 A K _88875 _88911 _88912 _88913 _88914.
Proof. exact (EQ_MP (@lem6786086 A K _88875 _88911 _88912 _88913 _88914) (@lem6786085 A K _88911 _88912 _88913 _88914 _88875 h1)). Qed.
Lemma lem6786088 {A K : Type'} (_88911 : K -> Prop) (_88912 : A -> Prop) (_88913 : K -> A) (_88914 : A) (_88915 : K) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1239 A K _88875 _88911 _88912 _88913 _88914 _88915.
Proof. exact (@lem6786087 A K _88911 _88912 _88913 _88914 _88875 h1 _88915). Qed.
Lemma lem6786089 {A K : Type'} (_88915 : K) (_88875 : type836 A K) (_88911 : K -> Prop) (_88912 : A -> Prop) (_88913 : K -> A) (_88914 : A) : (term1239 A K _88875 _88911 _88912 _88913 _88914 _88915) = (term1224 A K _88915 _88875 _88911 _88912 _88913 _88914).
Proof. exact (eq_refl (term1239 A K _88875 _88911 _88912 _88913 _88914 _88915)). Qed.
Lemma lem6786090 {A K : Type'} (_88915 : K) (_88911 : K -> Prop) (_88912 : A -> Prop) (_88913 : K -> A) (_88914 : A) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1224 A K _88915 _88875 _88911 _88912 _88913 _88914.
Proof. exact (EQ_MP (@lem6786089 A K _88915 _88875 _88911 _88912 _88913 _88914) (@lem6786088 A K _88911 _88912 _88913 _88914 _88915 _88875 h1)). Qed.
Lemma lem6786136 {A K : Type'} (_88881 : K) (_88877 : K -> Prop) (_88878 : A -> Prop) (_88879 : K -> A) (_88880 : A) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1240 A K _88881 _88875 _88877 _88878 _88879 _88880.
Proof. exact (proj1 (@lem6785988 A K _88881 _88877 _88878 _88879 _88880 _88875 h1)). Qed.
Lemma lem6786147 {A K : Type'} (_88898 : K) (_88894 : K -> Prop) (_88895 : A -> Prop) (_88896 : K -> A) (_88897 : A) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1222 A K _88898 _88875 _88894 _88895 _88896 _88897.
Proof. exact (proj2 (@lem6786039 A K _88898 _88894 _88895 _88896 _88897 _88875 h1)). Qed.
Lemma lem6786150 {A K : Type'} (_88898 : K) (_88894 : K -> Prop) (_88895 : A -> Prop) (_88896 : K -> A) (_88897 : A) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1241 A K _88898 _88875 _88894 _88895 _88896 _88897.
Proof. exact (proj1 (@lem6786147 A K _88898 _88894 _88895 _88896 _88897 _88875 h1)). Qed.
Lemma lem6786159 {A K : Type'} (_88915 : K) (_88911 : K -> Prop) (_88912 : A -> Prop) (_88913 : K -> A) (_88914 : A) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1222 A K _88915 _88875 _88911 _88912 _88913 _88914.
Proof. exact (proj2 (@lem6786090 A K _88915 _88911 _88912 _88913 _88914 _88875 h1)). Qed.
Lemma lem6786161 {A K : Type'} (_88915 : K) (_88911 : K -> Prop) (_88912 : A -> Prop) (_88913 : K -> A) (_88914 : A) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1242 A K _88915 _88875 _88911 _88912 _88913 _88914.
Proof. exact (proj2 (@lem6786159 A K _88915 _88911 _88912 _88913 _88914 _88875 h1)). Qed.
Lemma lem6786164 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : (_88875 k dom f neut) = i) : (term1096 A K _88875 k dom f neut) = i.
Proof. exact (EQ_MP (@lem6784337 A K _88875 k dom f neut i) (@lem6784068 A K _88875 k dom f neut i h1)). Qed.
Lemma lem6786186 {K : Type'} (k : K -> Prop) (i : K) (h1 : term1117 K k i) : term1117 K k i.
Proof. exact (h1). Qed.
Lemma lem6786270 {A K : Type'} (_88881 : K) (_88875 : type836 A K) (_88877 : K -> Prop) (_88878 : A -> Prop) (_88879 : K -> A) (_88880 : A) : (term1240 A K _88881 _88875 _88877 _88878 _88879 _88880) = (term1243 A K _88881 _88875 _88877 _88878 _88879 _88880).
Proof. exact (@lem6780691 (term1117 K _88877 _88881) (term1116 A K _88878 _88879 _88881 _88880) (term1106 A K _88875 _88877 _88878 _88879 _88880)). Qed.
Lemma lem6786277 {A K : Type'} (_88881 : K) (_88875 : type836 A K) (_88877 : K -> Prop) (_88878 : A -> Prop) (_88879 : K -> A) (_88880 : A) : (term1244 A K _88881 _88875 _88877 _88878 _88879 _88880) = (term1245 A K _88881 _88875 _88877 _88878 _88879 _88880).
Proof. exact (@lem6780691 (term1114 A K _88878 _88879 _88881) ((@I (K -> A) _88879 _88881) = _88880) (term1106 A K _88875 _88877 _88878 _88879 _88880)). Qed.
Lemma lem6786278 {K : Type'} (_88877 : K -> Prop) (_88881 : K) : (term1118 K _88877 _88881) = (term1118 K _88877 _88881).
Proof. exact (eq_refl (term1118 K _88877 _88881)). Qed.
Lemma lem6786281 {A K : Type'} (_88881 : K) (_88875 : type836 A K) (_88877 : K -> Prop) (_88878 : A -> Prop) (_88879 : K -> A) (_88880 : A) : (term1243 A K _88881 _88875 _88877 _88878 _88879 _88880) = (term1246 A K _88881 _88875 _88877 _88878 _88879 _88880).
Proof. exact (MK_COMB (@lem6786278 K _88877 _88881) (@lem6786277 A K _88881 _88875 _88877 _88878 _88879 _88880)). Qed.
Lemma lem6786283 {A K : Type'} (_88881 : K) (_88875 : type836 A K) (_88877 : K -> Prop) (_88878 : A -> Prop) (_88879 : K -> A) (_88880 : A) : (term1240 A K _88881 _88875 _88877 _88878 _88879 _88880) = (term1246 A K _88881 _88875 _88877 _88878 _88879 _88880).
Proof. exact (TRANS (@lem6786270 A K _88881 _88875 _88877 _88878 _88879 _88880) (@lem6786281 A K _88881 _88875 _88877 _88878 _88879 _88880)). Qed.
Lemma lem6786322 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : (_88875 k dom f neut) = i) : (term1096 A K _88875 k dom f neut) = i.
Proof. exact (EQ_MP (@lem6784337 A K _88875 k dom f neut i) (@lem6784068 A K _88875 k dom f neut i h1)). Qed.
Lemma lem6786344 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) (h1 : term1114 A K dom f i) : term1114 A K dom f i.
Proof. exact (h1). Qed.
Lemma lem6786446 {A K : Type'} (_88898 : K) (_88875 : type836 A K) (_88894 : K -> Prop) (_88895 : A -> Prop) (_88896 : K -> A) (_88897 : A) : (term1241 A K _88898 _88875 _88894 _88895 _88896 _88897) = (term1247 A K _88898 _88875 _88894 _88895 _88896 _88897).
Proof. exact (@lem6780691 (term1117 K _88894 _88898) (term1116 A K _88895 _88896 _88898 _88897) (term1102 A K _88875 _88894 _88895 _88896 _88897)). Qed.
Lemma lem6786453 {A K : Type'} (_88898 : K) (_88875 : type836 A K) (_88894 : K -> Prop) (_88895 : A -> Prop) (_88896 : K -> A) (_88897 : A) : (term1248 A K _88898 _88875 _88894 _88895 _88896 _88897) = (term1249 A K _88898 _88875 _88894 _88895 _88896 _88897).
Proof. exact (@lem6780691 (term1114 A K _88895 _88896 _88898) ((@I (K -> A) _88896 _88898) = _88897) (term1102 A K _88875 _88894 _88895 _88896 _88897)). Qed.
Lemma lem6786454 {K : Type'} (_88894 : K -> Prop) (_88898 : K) : (term1118 K _88894 _88898) = (term1118 K _88894 _88898).
Proof. exact (eq_refl (term1118 K _88894 _88898)). Qed.
Lemma lem6786457 {A K : Type'} (_88898 : K) (_88875 : type836 A K) (_88894 : K -> Prop) (_88895 : A -> Prop) (_88896 : K -> A) (_88897 : A) : (term1247 A K _88898 _88875 _88894 _88895 _88896 _88897) = (term1250 A K _88898 _88875 _88894 _88895 _88896 _88897).
Proof. exact (MK_COMB (@lem6786454 K _88894 _88898) (@lem6786453 A K _88898 _88875 _88894 _88895 _88896 _88897)). Qed.
Lemma lem6786459 {A K : Type'} (_88898 : K) (_88875 : type836 A K) (_88894 : K -> Prop) (_88895 : A -> Prop) (_88896 : K -> A) (_88897 : A) : (term1241 A K _88898 _88875 _88894 _88895 _88896 _88897) = (term1250 A K _88898 _88875 _88894 _88895 _88896 _88897).
Proof. exact (TRANS (@lem6786446 A K _88898 _88875 _88894 _88895 _88896 _88897) (@lem6786457 A K _88898 _88875 _88894 _88895 _88896 _88897)). Qed.
Lemma lem6786480 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : (_88875 k dom f neut) = i) : (term1096 A K _88875 k dom f neut) = i.
Proof. exact (EQ_MP (@lem6784337 A K _88875 k dom f neut i) (@lem6784068 A K _88875 k dom f neut i h1)). Qed.
Lemma lem6786500 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (h1 : term1086 A K ltle i' x _88876 k dom f neut) : term1142 A K f x neut.
Proof. exact (proj2 (@lem6785090 A K ltle i' x _88876 k dom f neut h1)). Qed.
Lemma lem6786502 {A K : Type'} (f : K -> A) (i : K) (neut : A) (h1 : (@I (K -> A) f i) = neut) : (@I (K -> A) f i) = neut.
Proof. exact (h1). Qed.
Lemma lem6786622 {A K : Type'} (_88915 : K) (_88875 : type836 A K) (_88911 : K -> Prop) (_88912 : A -> Prop) (_88913 : K -> A) (_88914 : A) : (term1242 A K _88915 _88875 _88911 _88912 _88913 _88914) = (term1251 A K _88915 _88875 _88911 _88912 _88913 _88914).
Proof. exact (@lem6780691 (term1117 K _88911 _88915) (term1116 A K _88912 _88913 _88915 _88914) (term1100 A K _88875 _88911 _88912 _88913 _88914)). Qed.
Lemma lem6786629 {A K : Type'} (_88915 : K) (_88875 : type836 A K) (_88911 : K -> Prop) (_88912 : A -> Prop) (_88913 : K -> A) (_88914 : A) : (term1252 A K _88915 _88875 _88911 _88912 _88913 _88914) = (term1253 A K _88915 _88875 _88911 _88912 _88913 _88914).
Proof. exact (@lem6780691 (term1114 A K _88912 _88913 _88915) ((@I (K -> A) _88913 _88915) = _88914) (term1100 A K _88875 _88911 _88912 _88913 _88914)). Qed.
Lemma lem6786630 {K : Type'} (_88911 : K -> Prop) (_88915 : K) : (term1118 K _88911 _88915) = (term1118 K _88911 _88915).
Proof. exact (eq_refl (term1118 K _88911 _88915)). Qed.
Lemma lem6786633 {A K : Type'} (_88915 : K) (_88875 : type836 A K) (_88911 : K -> Prop) (_88912 : A -> Prop) (_88913 : K -> A) (_88914 : A) : (term1251 A K _88915 _88875 _88911 _88912 _88913 _88914) = (term1254 A K _88915 _88875 _88911 _88912 _88913 _88914).
Proof. exact (MK_COMB (@lem6786630 K _88911 _88915) (@lem6786629 A K _88915 _88875 _88911 _88912 _88913 _88914)). Qed.
Lemma lem6786635 {A K : Type'} (_88915 : K) (_88875 : type836 A K) (_88911 : K -> Prop) (_88912 : A -> Prop) (_88913 : K -> A) (_88914 : A) : (term1242 A K _88915 _88875 _88911 _88912 _88913 _88914) = (term1254 A K _88915 _88875 _88911 _88912 _88913 _88914).
Proof. exact (TRANS (@lem6786622 A K _88915 _88875 _88911 _88912 _88913 _88914) (@lem6786633 A K _88915 _88875 _88911 _88912 _88913 _88914)). Qed.
Lemma lem6786637 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : (_88875 k dom f neut) = i) : i = (term1096 A K _88875 k dom f neut).
Proof. exact (SYM (@lem6786164 A K _88875 k dom f neut i h1)). Qed.
Lemma lem6786736 {K : Type'} (k : K -> Prop) : (term1255 K k) = (term1255 K k).
Proof. exact (eq_refl (term1255 K k)). Qed.
Lemma lem6786737 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : (_88875 k dom f neut) = i) : (term1256 K k i) = (term1257 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6786736 K k) (@lem6786637 A K _88875 k dom f neut i h1)). Qed.
Lemma lem6786738 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1257 A K _88875 k dom f neut) = (term1258 A K _88875 k dom f neut).
Proof. exact (eq_refl (term1257 A K _88875 k dom f neut)). Qed.
Lemma lem6786739 {K : Type'} (k : K -> Prop) (i : K) : (term1259 K k i) = (term1259 K k i).
Proof. exact (eq_refl (term1259 K k i)). Qed.
Lemma lem6786740 {A K : Type'} (i : K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : ((term1256 K k i) = (term1257 A K _88875 k dom f neut)) = ((term1256 K k i) = (term1258 A K _88875 k dom f neut)).
Proof. exact (MK_COMB (@lem6786739 K k i) (@lem6786738 A K _88875 k dom f neut)). Qed.
Lemma lem6786741 {K : Type'} (k : K -> Prop) (i : K) : (term1256 K k i) = (term1117 K k i).
Proof. exact (eq_refl (term1256 K k i)). Qed.
Lemma lem6786742 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6786743 {K : Type'} (k : K -> Prop) (i : K) : (term1259 K k i) = (term1260 K k i).
Proof. exact (MK_COMB (@lem6786742) (@lem6786741 K k i)). Qed.
Lemma lem6786744 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1258 A K _88875 k dom f neut) = (term1258 A K _88875 k dom f neut).
Proof. exact (eq_refl (term1258 A K _88875 k dom f neut)). Qed.
Lemma lem6786745 {A K : Type'} (i : K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : ((term1256 K k i) = (term1258 A K _88875 k dom f neut)) = ((term1117 K k i) = (term1258 A K _88875 k dom f neut)).
Proof. exact (MK_COMB (@lem6786743 K k i) (@lem6786744 A K _88875 k dom f neut)). Qed.
Lemma lem6786746 {A K : Type'} (i : K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : ((term1256 K k i) = (term1257 A K _88875 k dom f neut)) = ((term1117 K k i) = (term1258 A K _88875 k dom f neut)).
Proof. exact (TRANS (@lem6786740 A K i _88875 k dom f neut) (@lem6786745 A K i _88875 k dom f neut)). Qed.
Lemma lem6786747 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : (_88875 k dom f neut) = i) : (term1117 K k i) = (term1258 A K _88875 k dom f neut).
Proof. exact (EQ_MP (@lem6786746 A K i _88875 k dom f neut) (@lem6786737 A K _88875 k dom f neut i h1)). Qed.
Lemma lem6786748 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : term1117 K k i) (h2 : (_88875 k dom f neut) = i) : term1258 A K _88875 k dom f neut.
Proof. exact (EQ_MP (@lem6786747 A K _88875 k dom f neut i h2) (@lem6786186 K k i h1)). Qed.
Lemma lem6786832 {A K : Type'} (_88881 : K) (_88877 : K -> Prop) (_88878 : A -> Prop) (_88879 : K -> A) (_88880 : A) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1246 A K _88881 _88875 _88877 _88878 _88879 _88880.
Proof. exact (EQ_MP (@lem6786283 A K _88881 _88875 _88877 _88878 _88879 _88880) (@lem6786136 A K _88881 _88877 _88878 _88879 _88880 _88875 h1)). Qed.
Lemma lem6786861 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : (_88875 k dom f neut) = i) : i = (term1096 A K _88875 k dom f neut).
Proof. exact (SYM (@lem6786322 A K _88875 k dom f neut i h1)). Qed.
Lemma lem6786960 {A K : Type'} (dom : A -> Prop) (f : K -> A) : (term1261 A K dom f) = (term1261 A K dom f).
Proof. exact (eq_refl (term1261 A K dom f)). Qed.
Lemma lem6786961 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : (_88875 k dom f neut) = i) : (term1262 A K dom f i) = (term1263 A K _88875 k dom f neut).
Proof. exact (MK_COMB (@lem6786960 A K dom f) (@lem6786861 A K _88875 k dom f neut i h1)). Qed.
Lemma lem6786962 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1263 A K _88875 k dom f neut) = (term1264 A K _88875 k dom f neut).
Proof. exact (eq_refl (term1263 A K _88875 k dom f neut)). Qed.
Lemma lem6786963 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) : (term1265 A K dom f i) = (term1265 A K dom f i).
Proof. exact (eq_refl (term1265 A K dom f i)). Qed.
Lemma lem6786964 {A K : Type'} (i : K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : ((term1262 A K dom f i) = (term1263 A K _88875 k dom f neut)) = ((term1262 A K dom f i) = (term1264 A K _88875 k dom f neut)).
Proof. exact (MK_COMB (@lem6786963 A K dom f i) (@lem6786962 A K _88875 k dom f neut)). Qed.
Lemma lem6786965 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) : (term1262 A K dom f i) = (term1114 A K dom f i).
Proof. exact (eq_refl (term1262 A K dom f i)). Qed.
Lemma lem6786966 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6786967 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) : (term1265 A K dom f i) = (term1266 A K dom f i).
Proof. exact (MK_COMB (@lem6786966) (@lem6786965 A K dom f i)). Qed.
Lemma lem6786968 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1264 A K _88875 k dom f neut) = (term1264 A K _88875 k dom f neut).
Proof. exact (eq_refl (term1264 A K _88875 k dom f neut)). Qed.
Lemma lem6786969 {A K : Type'} (i : K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : ((term1262 A K dom f i) = (term1264 A K _88875 k dom f neut)) = ((term1114 A K dom f i) = (term1264 A K _88875 k dom f neut)).
Proof. exact (MK_COMB (@lem6786967 A K dom f i) (@lem6786968 A K _88875 k dom f neut)). Qed.
Lemma lem6786970 {A K : Type'} (i : K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : ((term1262 A K dom f i) = (term1263 A K _88875 k dom f neut)) = ((term1114 A K dom f i) = (term1264 A K _88875 k dom f neut)).
Proof. exact (TRANS (@lem6786964 A K i _88875 k dom f neut) (@lem6786969 A K i _88875 k dom f neut)). Qed.
Lemma lem6786971 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : (_88875 k dom f neut) = i) : (term1114 A K dom f i) = (term1264 A K _88875 k dom f neut).
Proof. exact (EQ_MP (@lem6786970 A K i _88875 k dom f neut) (@lem6786961 A K _88875 k dom f neut i h1)). Qed.
Lemma lem6786972 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : term1114 A K dom f i) (h2 : (_88875 k dom f neut) = i) : term1264 A K _88875 k dom f neut.
Proof. exact (EQ_MP (@lem6786971 A K _88875 k dom f neut i h2) (@lem6786344 A K dom f i h1)). Qed.
Lemma lem6787070 {A K : Type'} (_88898 : K) (_88894 : K -> Prop) (_88895 : A -> Prop) (_88896 : K -> A) (_88897 : A) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1250 A K _88898 _88875 _88894 _88895 _88896 _88897.
Proof. exact (EQ_MP (@lem6786459 A K _88898 _88875 _88894 _88895 _88896 _88897) (@lem6786150 A K _88898 _88894 _88895 _88896 _88897 _88875 h1)). Qed.
Lemma lem6787085 {A K : Type'} (f : K -> A) (i : K) (neut : A) (h1 : (@I (K -> A) f i) = neut) : neut = (@I (K -> A) f i).
Proof. exact (SYM (@lem6786502 A K f i neut h1)). Qed.
Lemma lem6787100 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) : (term1267 A K _88875 k dom f i) = (term1267 A K _88875 k dom f i).
Proof. exact (eq_refl (term1267 A K _88875 k dom f i)). Qed.
Lemma lem6787101 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (h1 : (@I (K -> A) f i) = neut) : (term1268 A K _88875 k dom f i neut) = (term1269 A K _88875 k dom f i).
Proof. exact (MK_COMB (@lem6787100 A K _88875 k dom f i) (@lem6787085 A K f i neut h1)). Qed.
Lemma lem6787102 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) : (term1269 A K _88875 k dom f i) = ((term1270 A K _88875 k dom f i) = i).
Proof. exact (eq_refl (term1269 A K _88875 k dom f i)). Qed.
Lemma lem6787103 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term1271 A K _88875 k dom f i neut) = (term1271 A K _88875 k dom f i neut).
Proof. exact (eq_refl (term1271 A K _88875 k dom f i neut)). Qed.
Lemma lem6787104 {A K : Type'} (neut : A) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) : ((term1268 A K _88875 k dom f i neut) = (term1269 A K _88875 k dom f i)) = ((term1268 A K _88875 k dom f i neut) = ((term1270 A K _88875 k dom f i) = i)).
Proof. exact (MK_COMB (@lem6787103 A K _88875 k dom f i neut) (@lem6787102 A K _88875 k dom f i)). Qed.
Lemma lem6787105 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term1268 A K _88875 k dom f i neut) = ((term1096 A K _88875 k dom f neut) = i).
Proof. exact (eq_refl (term1268 A K _88875 k dom f i neut)). Qed.
Lemma lem6787106 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6787107 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) : (term1271 A K _88875 k dom f i neut) = (term1272 A K _88875 k dom f neut i).
Proof. exact (MK_COMB (@lem6787106) (@lem6787105 A K _88875 k dom f neut i)). Qed.
Lemma lem6787108 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) : ((term1270 A K _88875 k dom f i) = i) = ((term1270 A K _88875 k dom f i) = i).
Proof. exact (eq_refl ((term1270 A K _88875 k dom f i) = i)). Qed.
Lemma lem6787109 {A K : Type'} (neut : A) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) : ((term1268 A K _88875 k dom f i neut) = ((term1270 A K _88875 k dom f i) = i)) = (((term1096 A K _88875 k dom f neut) = i) = ((term1270 A K _88875 k dom f i) = i)).
Proof. exact (MK_COMB (@lem6787107 A K _88875 k dom f neut i) (@lem6787108 A K _88875 k dom f i)). Qed.
Lemma lem6787110 {A K : Type'} (neut : A) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) : ((term1268 A K _88875 k dom f i neut) = (term1269 A K _88875 k dom f i)) = (((term1096 A K _88875 k dom f neut) = i) = ((term1270 A K _88875 k dom f i) = i)).
Proof. exact (TRANS (@lem6787104 A K neut _88875 k dom f i) (@lem6787109 A K neut _88875 k dom f i)). Qed.
Lemma lem6787111 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (h1 : (@I (K -> A) f i) = neut) : ((term1096 A K _88875 k dom f neut) = i) = ((term1270 A K _88875 k dom f i) = i).
Proof. exact (EQ_MP (@lem6787110 A K neut _88875 k dom f i) (@lem6787101 A K _88875 k dom f i neut h1)). Qed.
Lemma lem6787182 {A K : Type'} (f : K -> A) (x : K) : (term1273 A K f x) = (term1273 A K f x).
Proof. exact (eq_refl (term1273 A K f x)). Qed.
Lemma lem6787183 {A K : Type'} (x : K) (f : K -> A) (i : K) (neut : A) (h1 : (@I (K -> A) f i) = neut) : (term1274 A K f x neut) = (term1275 A K x f i).
Proof. exact (MK_COMB (@lem6787182 A K f x) (@lem6787085 A K f i neut h1)). Qed.
Lemma lem6787184 {A K : Type'} (x : K) (f : K -> A) (i : K) : (term1275 A K x f i) = (term1276 A K x f i).
Proof. exact (eq_refl (term1275 A K x f i)). Qed.
Lemma lem6787185 {A K : Type'} (f : K -> A) (x : K) (neut : A) : (term1277 A K f x neut) = (term1277 A K f x neut).
Proof. exact (eq_refl (term1277 A K f x neut)). Qed.
Lemma lem6787186 {A K : Type'} (neut : A) (x : K) (f : K -> A) (i : K) : ((term1274 A K f x neut) = (term1275 A K x f i)) = ((term1274 A K f x neut) = (term1276 A K x f i)).
Proof. exact (MK_COMB (@lem6787185 A K f x neut) (@lem6787184 A K x f i)). Qed.
Lemma lem6787187 {A K : Type'} (f : K -> A) (x : K) (neut : A) : (term1274 A K f x neut) = (term1142 A K f x neut).
Proof. exact (eq_refl (term1274 A K f x neut)). Qed.
Lemma lem6787188 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6787189 {A K : Type'} (f : K -> A) (x : K) (neut : A) : (term1277 A K f x neut) = (term1278 A K f x neut).
Proof. exact (MK_COMB (@lem6787188) (@lem6787187 A K f x neut)). Qed.
Lemma lem6787190 {A K : Type'} (x : K) (f : K -> A) (i : K) : (term1276 A K x f i) = (term1276 A K x f i).
Proof. exact (eq_refl (term1276 A K x f i)). Qed.
Lemma lem6787191 {A K : Type'} (neut : A) (x : K) (f : K -> A) (i : K) : ((term1274 A K f x neut) = (term1276 A K x f i)) = ((term1142 A K f x neut) = (term1276 A K x f i)).
Proof. exact (MK_COMB (@lem6787189 A K f x neut) (@lem6787190 A K x f i)). Qed.
Lemma lem6787192 {A K : Type'} (neut : A) (x : K) (f : K -> A) (i : K) : ((term1274 A K f x neut) = (term1275 A K x f i)) = ((term1142 A K f x neut) = (term1276 A K x f i)).
Proof. exact (TRANS (@lem6787186 A K neut x f i) (@lem6787191 A K neut x f i)). Qed.
Lemma lem6787193 {A K : Type'} (x : K) (f : K -> A) (i : K) (neut : A) (h1 : (@I (K -> A) f i) = neut) : (term1142 A K f x neut) = (term1276 A K x f i).
Proof. exact (EQ_MP (@lem6787192 A K neut x f i) (@lem6787183 A K x f i neut h1)). Qed.
Lemma lem6787194 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (h1 : term1086 A K ltle i' x _88876 k dom f neut) (h2 : (@I (K -> A) f i) = neut) : term1276 A K x f i.
Proof. exact (EQ_MP (@lem6787193 A K x f i neut h2) (@lem6786500 A K ltle i' x _88876 k dom f neut h1)). Qed.
Lemma lem6787301 {A K : Type'} (_88915 : K) (_88911 : K -> Prop) (_88912 : A -> Prop) (_88913 : K -> A) (_88914 : A) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1254 A K _88915 _88875 _88911 _88912 _88913 _88914.
Proof. exact (EQ_MP (@lem6786635 A K _88915 _88875 _88911 _88912 _88913 _88914) (@lem6786161 A K _88915 _88911 _88912 _88913 _88914 _88875 h1)). Qed.
Lemma lem6787744 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (h1 : term1086 A K ltle i' x _88876 k dom f neut) : @I (K -> Prop) k x.
Proof. exact (proj1 (@lem6785089 A K ltle i' x _88876 k dom f neut h1)). Qed.
Lemma lem6787745 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (h1 : term1086 A K ltle i' x _88876 k dom f neut) : term1279 K k x.
Proof. exact (fun h0 : term1117 K k x => @lem6787744 A K ltle i' x _88876 k dom f neut h1). Qed.
Lemma lem6787747 (p : Prop) : (term47 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6787748 {K : Type'} (k : K -> Prop) (x : K) : (term1279 K k x) = (@I (K -> Prop) k x).
Proof. exact (@lem6787747 (@I (K -> Prop) k x)). Qed.
Lemma lem6787749 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (h1 : term1086 A K ltle i' x _88876 k dom f neut) : @I (K -> Prop) k x.
Proof. exact (EQ_MP (@lem6787748 K k x) (@lem6787745 A K ltle i' x _88876 k dom f neut h1)). Qed.
Lemma lem6787751 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (h1 : term1086 A K ltle i' x _88876 k dom f neut) : term1112 A K dom f x.
Proof. exact (proj1 (@lem6785090 A K ltle i' x _88876 k dom f neut h1)). Qed.
Lemma lem6787752 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (h1 : term1086 A K ltle i' x _88876 k dom f neut) : term1280 A K dom f x.
Proof. exact (fun h0 : term1114 A K dom f x => @lem6787751 A K ltle i' x _88876 k dom f neut h1). Qed.
Lemma lem6787754 (p : Prop) : (term47 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6787755 {A K : Type'} (dom : A -> Prop) (f : K -> A) (x : K) : (term1280 A K dom f x) = (term1112 A K dom f x).
Proof. exact (@lem6787754 (term1112 A K dom f x)). Qed.
Lemma lem6787756 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (h1 : term1086 A K ltle i' x _88876 k dom f neut) : term1112 A K dom f x.
Proof. exact (EQ_MP (@lem6787755 A K dom f x) (@lem6787752 A K ltle i' x _88876 k dom f neut h1)). Qed.
Lemma lem6787758 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (h1 : term1086 A K ltle i' x _88876 k dom f neut) : term1142 A K f x neut.
Proof. exact (proj2 (@lem6785090 A K ltle i' x _88876 k dom f neut h1)). Qed.
Lemma lem6787759 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (h1 : term1086 A K ltle i' x _88876 k dom f neut) : term1281 A K f x neut.
Proof. exact (fun h0 : (@I (K -> A) f x) = neut => @lem6787758 A K ltle i' x _88876 k dom f neut h1). Qed.
Lemma lem6787761 (p : Prop) : (term1282 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem6787762 {A K : Type'} (f : K -> A) (x : K) (neut : A) : (term1281 A K f x neut) = (term1142 A K f x neut).
Proof. exact (@lem6787761 ((@I (K -> A) f x) = neut)). Qed.
Lemma lem6787763 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (h1 : term1086 A K ltle i' x _88876 k dom f neut) : term1142 A K f x neut.
Proof. exact (EQ_MP (@lem6787762 A K f x neut) (@lem6787759 A K ltle i' x _88876 k dom f neut h1)). Qed.
Lemma lem6787769 (q : Prop) (p : Prop) (r : Prop) : (term277 p q r) = (term277 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6787770 {A K : Type'} (_88881 : K) (_88875 : type836 A K) (_88877 : K -> Prop) (_88878 : A -> Prop) (_88879 : K -> A) (_88880 : A) : (term1246 A K _88881 _88875 _88877 _88878 _88879 _88880) = (term1283 A K _88881 _88875 _88877 _88878 _88879 _88880).
Proof. exact (@lem6787769 (term1114 A K _88878 _88879 _88881) (term1117 K _88877 _88881) (term1284 A K _88881 _88875 _88877 _88878 _88879 _88880)). Qed.
Lemma lem6787784 (q : Prop) (p : Prop) (r : Prop) : (term277 p q r) = (term277 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6787785 {A K : Type'} (_88881 : K) (_88875 : type836 A K) (_88877 : K -> Prop) (_88878 : A -> Prop) (_88879 : K -> A) (_88880 : A) : (term1285 A K _88881 _88875 _88877 _88878 _88879 _88880) = (term1286 A K _88881 _88875 _88877 _88878 _88879 _88880).
Proof. exact (@lem6787784 ((@I (K -> A) _88879 _88881) = _88880) (term1117 K _88877 _88881) (term1106 A K _88875 _88877 _88878 _88879 _88880)). Qed.
Lemma lem6787801 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6787802 {A K : Type'} (_88875 : type836 A K) (_88878 : A -> Prop) (_88879 : K -> A) (_88880 : A) (_88877 : K -> Prop) (_88881 : K) : (term1287 A K _88881 _88875 _88877 _88878 _88879 _88880) = (term1288 A K _88875 _88878 _88879 _88880 _88877 _88881).
Proof. exact (@lem6787801 (term1106 A K _88875 _88877 _88878 _88879 _88880) (term1117 K _88877 _88881)). Qed.
Lemma lem6787808 {A K : Type'} (_88879 : K -> A) (_88881 : K) (_88880 : A) : (term1289 A K _88879 _88881 _88880) = (term1289 A K _88879 _88881 _88880).
Proof. exact (eq_refl (term1289 A K _88879 _88881 _88880)). Qed.
Lemma lem6787809 {A K : Type'} (_88875 : type836 A K) (_88878 : A -> Prop) (_88879 : K -> A) (_88880 : A) (_88877 : K -> Prop) (_88881 : K) : (term1286 A K _88881 _88875 _88877 _88878 _88879 _88880) = (term1290 A K _88875 _88878 _88879 _88880 _88877 _88881).
Proof. exact (MK_COMB (@lem6787808 A K _88879 _88881 _88880) (@lem6787802 A K _88875 _88878 _88879 _88880 _88877 _88881)). Qed.
Lemma lem6787820 {A K : Type'} (_88875 : type836 A K) (_88878 : A -> Prop) (_88879 : K -> A) (_88880 : A) (_88877 : K -> Prop) (_88881 : K) : (term1285 A K _88881 _88875 _88877 _88878 _88879 _88880) = (term1290 A K _88875 _88878 _88879 _88880 _88877 _88881).
Proof. exact (TRANS (@lem6787785 A K _88881 _88875 _88877 _88878 _88879 _88880) (@lem6787809 A K _88875 _88878 _88879 _88880 _88877 _88881)). Qed.
Lemma lem6787821 {A K : Type'} (_88878 : A -> Prop) (_88879 : K -> A) (_88881 : K) : (term1115 A K _88878 _88879 _88881) = (term1115 A K _88878 _88879 _88881).
Proof. exact (eq_refl (term1115 A K _88878 _88879 _88881)). Qed.
Lemma lem6787822 {A K : Type'} (_88875 : type836 A K) (_88878 : A -> Prop) (_88879 : K -> A) (_88880 : A) (_88877 : K -> Prop) (_88881 : K) : (term1283 A K _88881 _88875 _88877 _88878 _88879 _88880) = (term1291 A K _88875 _88878 _88879 _88880 _88877 _88881).
Proof. exact (MK_COMB (@lem6787821 A K _88878 _88879 _88881) (@lem6787820 A K _88875 _88878 _88879 _88880 _88877 _88881)). Qed.
Lemma lem6787826 (q : Prop) (p : Prop) (r : Prop) : (term277 p q r) = (term277 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6787827 {A K : Type'} (_88875 : type836 A K) (_88878 : A -> Prop) (_88879 : K -> A) (_88880 : A) (_88877 : K -> Prop) (_88881 : K) : (term1291 A K _88875 _88878 _88879 _88880 _88877 _88881) = (term1292 A K _88875 _88878 _88879 _88880 _88877 _88881).
Proof. exact (@lem6787826 ((@I (K -> A) _88879 _88881) = _88880) (term1114 A K _88878 _88879 _88881) (term1288 A K _88875 _88878 _88879 _88880 _88877 _88881)). Qed.
Lemma lem6787843 (q : Prop) (p : Prop) (r : Prop) : (term277 p q r) = (term277 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6787844 {A K : Type'} (_88875 : type836 A K) (_88880 : A) (_88878 : A -> Prop) (_88879 : K -> A) (_88877 : K -> Prop) (_88881 : K) : (term1293 A K _88875 _88878 _88879 _88880 _88877 _88881) = (term1294 A K _88875 _88880 _88878 _88879 _88877 _88881).
Proof. exact (@lem6787843 (term1106 A K _88875 _88877 _88878 _88879 _88880) (term1114 A K _88878 _88879 _88881) (term1117 K _88877 _88881)). Qed.
Lemma lem6787860 {A K : Type'} (_88879 : K -> A) (_88881 : K) (_88880 : A) : (term1289 A K _88879 _88881 _88880) = (term1289 A K _88879 _88881 _88880).
Proof. exact (eq_refl (term1289 A K _88879 _88881 _88880)). Qed.
Lemma lem6787861 {A K : Type'} (_88875 : type836 A K) (_88880 : A) (_88878 : A -> Prop) (_88879 : K -> A) (_88877 : K -> Prop) (_88881 : K) : (term1292 A K _88875 _88878 _88879 _88880 _88877 _88881) = (term1295 A K _88875 _88880 _88878 _88879 _88877 _88881).
Proof. exact (MK_COMB (@lem6787860 A K _88879 _88881 _88880) (@lem6787844 A K _88875 _88880 _88878 _88879 _88877 _88881)). Qed.
Lemma lem6787872 {A K : Type'} (_88875 : type836 A K) (_88880 : A) (_88878 : A -> Prop) (_88879 : K -> A) (_88877 : K -> Prop) (_88881 : K) : (term1291 A K _88875 _88878 _88879 _88880 _88877 _88881) = (term1295 A K _88875 _88880 _88878 _88879 _88877 _88881).
Proof. exact (TRANS (@lem6787827 A K _88875 _88878 _88879 _88880 _88877 _88881) (@lem6787861 A K _88875 _88880 _88878 _88879 _88877 _88881)). Qed.
Lemma lem6787873 {A K : Type'} (_88875 : type836 A K) (_88880 : A) (_88878 : A -> Prop) (_88879 : K -> A) (_88877 : K -> Prop) (_88881 : K) : (term1283 A K _88881 _88875 _88877 _88878 _88879 _88880) = (term1295 A K _88875 _88880 _88878 _88879 _88877 _88881).
Proof. exact (TRANS (@lem6787822 A K _88875 _88878 _88879 _88880 _88877 _88881) (@lem6787872 A K _88875 _88880 _88878 _88879 _88877 _88881)). Qed.
Lemma lem6787874 {A K : Type'} (_88875 : type836 A K) (_88880 : A) (_88878 : A -> Prop) (_88879 : K -> A) (_88877 : K -> Prop) (_88881 : K) : (term1246 A K _88881 _88875 _88877 _88878 _88879 _88880) = (term1295 A K _88875 _88880 _88878 _88879 _88877 _88881).
Proof. exact (TRANS (@lem6787770 A K _88881 _88875 _88877 _88878 _88879 _88880) (@lem6787873 A K _88875 _88880 _88878 _88879 _88877 _88881)). Qed.
Lemma lem6787875 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6787876 {A K : Type'} (_88875 : type836 A K) (_88880 : A) (_88878 : A -> Prop) (_88879 : K -> A) (_88877 : K -> Prop) (_88881 : K) : (term1296 A K _88881 _88875 _88877 _88878 _88879 _88880) = (term1297 A K _88875 _88880 _88878 _88879 _88877 _88881).
Proof. exact (MK_COMB (@lem6787875) (@lem6787874 A K _88875 _88880 _88878 _88879 _88877 _88881)). Qed.
Lemma lem6787890 (q : Prop) (p : Prop) (r : Prop) : (term277 p q r) = (term277 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6787891 {A K : Type'} (_88878 : A -> Prop) (_88877 : K -> Prop) (_88879 : K -> A) (_88881 : K) (_88880 : A) : (term1119 A K _88877 _88878 _88879 _88881 _88880) = (term1298 A K _88878 _88877 _88879 _88881 _88880).
Proof. exact (@lem6787890 (term1114 A K _88878 _88879 _88881) (term1117 K _88877 _88881) ((@I (K -> A) _88879 _88881) = _88880)). Qed.
Lemma lem6787905 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6787906 {A K : Type'} (_88879 : K -> A) (_88880 : A) (_88877 : K -> Prop) (_88881 : K) : (term1299 A K _88877 _88879 _88881 _88880) = (term1300 A K _88879 _88880 _88877 _88881).
Proof. exact (@lem6787905 ((@I (K -> A) _88879 _88881) = _88880) (term1117 K _88877 _88881)). Qed.
Lemma lem6787914 {A K : Type'} (_88878 : A -> Prop) (_88879 : K -> A) (_88881 : K) : (term1115 A K _88878 _88879 _88881) = (term1115 A K _88878 _88879 _88881).
Proof. exact (eq_refl (term1115 A K _88878 _88879 _88881)). Qed.
Lemma lem6787915 {A K : Type'} (_88878 : A -> Prop) (_88879 : K -> A) (_88880 : A) (_88877 : K -> Prop) (_88881 : K) : (term1298 A K _88878 _88877 _88879 _88881 _88880) = (term1301 A K _88878 _88879 _88880 _88877 _88881).
Proof. exact (MK_COMB (@lem6787914 A K _88878 _88879 _88881) (@lem6787906 A K _88879 _88880 _88877 _88881)). Qed.
Lemma lem6787919 (q : Prop) (p : Prop) (r : Prop) : (term277 p q r) = (term277 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6787920 {A K : Type'} (_88880 : A) (_88878 : A -> Prop) (_88879 : K -> A) (_88877 : K -> Prop) (_88881 : K) : (term1301 A K _88878 _88879 _88880 _88877 _88881) = (term1302 A K _88880 _88878 _88879 _88877 _88881).
Proof. exact (@lem6787919 ((@I (K -> A) _88879 _88881) = _88880) (term1114 A K _88878 _88879 _88881) (term1117 K _88877 _88881)). Qed.
Lemma lem6787938 {A K : Type'} (_88880 : A) (_88878 : A -> Prop) (_88879 : K -> A) (_88877 : K -> Prop) (_88881 : K) : (term1298 A K _88878 _88877 _88879 _88881 _88880) = (term1302 A K _88880 _88878 _88879 _88877 _88881).
Proof. exact (TRANS (@lem6787915 A K _88878 _88879 _88880 _88877 _88881) (@lem6787920 A K _88880 _88878 _88879 _88877 _88881)). Qed.
Lemma lem6787939 {A K : Type'} (_88880 : A) (_88878 : A -> Prop) (_88879 : K -> A) (_88877 : K -> Prop) (_88881 : K) : (term1119 A K _88877 _88878 _88879 _88881 _88880) = (term1302 A K _88880 _88878 _88879 _88877 _88881).
Proof. exact (TRANS (@lem6787891 A K _88878 _88877 _88879 _88881 _88880) (@lem6787938 A K _88880 _88878 _88879 _88877 _88881)). Qed.
Lemma lem6787940 {A K : Type'} (_88875 : type836 A K) (_88877 : K -> Prop) (_88878 : A -> Prop) (_88879 : K -> A) (_88880 : A) : (term1303 A K _88875 _88877 _88878 _88879 _88880) = (term1303 A K _88875 _88877 _88878 _88879 _88880).
Proof. exact (eq_refl (term1303 A K _88875 _88877 _88878 _88879 _88880)). Qed.
Lemma lem6787941 {A K : Type'} (_88875 : type836 A K) (_88880 : A) (_88878 : A -> Prop) (_88879 : K -> A) (_88877 : K -> Prop) (_88881 : K) : (term1304 A K _88875 _88877 _88878 _88879 _88881 _88880) = (term1305 A K _88875 _88880 _88878 _88879 _88877 _88881).
Proof. exact (MK_COMB (@lem6787940 A K _88875 _88877 _88878 _88879 _88880) (@lem6787939 A K _88880 _88878 _88879 _88877 _88881)). Qed.
Lemma lem6787945 (q : Prop) (p : Prop) (r : Prop) : (term277 p q r) = (term277 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6787946 {A K : Type'} (_88875 : type836 A K) (_88880 : A) (_88878 : A -> Prop) (_88879 : K -> A) (_88877 : K -> Prop) (_88881 : K) : (term1305 A K _88875 _88880 _88878 _88879 _88877 _88881) = (term1295 A K _88875 _88880 _88878 _88879 _88877 _88881).
Proof. exact (@lem6787945 ((@I (K -> A) _88879 _88881) = _88880) (term1106 A K _88875 _88877 _88878 _88879 _88880) (term1306 A K _88878 _88879 _88877 _88881)). Qed.
Lemma lem6787974 {A K : Type'} (_88875 : type836 A K) (_88880 : A) (_88878 : A -> Prop) (_88879 : K -> A) (_88877 : K -> Prop) (_88881 : K) : (term1304 A K _88875 _88877 _88878 _88879 _88881 _88880) = (term1295 A K _88875 _88880 _88878 _88879 _88877 _88881).
Proof. exact (TRANS (@lem6787941 A K _88875 _88880 _88878 _88879 _88877 _88881) (@lem6787946 A K _88875 _88880 _88878 _88879 _88877 _88881)). Qed.
Lemma lem6787975 {A K : Type'} (_88875 : type836 A K) (_88880 : A) (_88878 : A -> Prop) (_88879 : K -> A) (_88877 : K -> Prop) (_88881 : K) : ((term1246 A K _88881 _88875 _88877 _88878 _88879 _88880) = (term1304 A K _88875 _88877 _88878 _88879 _88881 _88880)) = ((term1295 A K _88875 _88880 _88878 _88879 _88877 _88881) = (term1295 A K _88875 _88880 _88878 _88879 _88877 _88881)).
Proof. exact (MK_COMB (@lem6787876 A K _88875 _88880 _88878 _88879 _88877 _88881) (@lem6787974 A K _88875 _88880 _88878 _88879 _88877 _88881)). Qed.
Lemma lem6787977 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6787978 (x : Prop) : (x = x) = True.
Proof. exact (@lem6787977 Prop x). Qed.
Lemma lem6787979 {A K : Type'} (_88875 : type836 A K) (_88880 : A) (_88878 : A -> Prop) (_88879 : K -> A) (_88877 : K -> Prop) (_88881 : K) : ((term1295 A K _88875 _88880 _88878 _88879 _88877 _88881) = (term1295 A K _88875 _88880 _88878 _88879 _88877 _88881)) = True.
Proof. exact (@lem6787978 (term1295 A K _88875 _88880 _88878 _88879 _88877 _88881)). Qed.
Lemma lem6787980 {A K : Type'} (_88875 : type836 A K) (_88877 : K -> Prop) (_88878 : A -> Prop) (_88879 : K -> A) (_88881 : K) (_88880 : A) : ((term1246 A K _88881 _88875 _88877 _88878 _88879 _88880) = (term1304 A K _88875 _88877 _88878 _88879 _88881 _88880)) = True.
Proof. exact (TRANS (@lem6787975 A K _88875 _88880 _88878 _88879 _88877 _88881) (@lem6787979 A K _88875 _88880 _88878 _88879 _88877 _88881)). Qed.
Lemma lem6787981 {A K : Type'} (_88875 : type836 A K) (_88877 : K -> Prop) (_88878 : A -> Prop) (_88879 : K -> A) (_88881 : K) (_88880 : A) : True = ((term1246 A K _88881 _88875 _88877 _88878 _88879 _88880) = (term1304 A K _88875 _88877 _88878 _88879 _88881 _88880)).
Proof. exact (SYM (@lem6787980 A K _88875 _88877 _88878 _88879 _88881 _88880)). Qed.
Lemma lem6787982 {A K : Type'} (_88875 : type836 A K) (_88877 : K -> Prop) (_88878 : A -> Prop) (_88879 : K -> A) (_88881 : K) (_88880 : A) : (term1246 A K _88881 _88875 _88877 _88878 _88879 _88880) = (term1304 A K _88875 _88877 _88878 _88879 _88881 _88880).
Proof. exact (EQ_MP (@lem6787981 A K _88875 _88877 _88878 _88879 _88881 _88880) (@lem0)). Qed.
Lemma lem6787983 {A K : Type'} (_88877 : K -> Prop) (_88878 : A -> Prop) (_88879 : K -> A) (_88881 : K) (_88880 : A) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1304 A K _88875 _88877 _88878 _88879 _88881 _88880.
Proof. exact (EQ_MP (@lem6787982 A K _88875 _88877 _88878 _88879 _88881 _88880) (@lem6786832 A K _88881 _88877 _88878 _88879 _88880 _88875 h1)). Qed.
Lemma lem6787985 (b : Prop) (a : Prop) : (a \/ b) = (term1307 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6787986 {A K : Type'} (_88881 : K) (_88875 : type836 A K) (_88877 : K -> Prop) (_88878 : A -> Prop) (_88879 : K -> A) (_88880 : A) : (term1304 A K _88875 _88877 _88878 _88879 _88881 _88880) = (term1308 A K _88881 _88875 _88877 _88878 _88879 _88880).
Proof. exact (@lem6787985 (term1119 A K _88877 _88878 _88879 _88881 _88880) (term1106 A K _88875 _88877 _88878 _88879 _88880)). Qed.
Lemma lem6787988 (a : Prop) (b : Prop) : (term1309 a b) = (term1310 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6787989 {A K : Type'} (_88877 : K -> Prop) (_88878 : A -> Prop) (_88879 : K -> A) (_88881 : K) (_88880 : A) : (term1311 A K _88877 _88878 _88879 _88881 _88880) = (term1312 A K _88877 _88878 _88879 _88881 _88880).
Proof. exact (@lem6787988 (term1117 K _88877 _88881) (term1116 A K _88878 _88879 _88881 _88880)). Qed.
Lemma lem6787991 (a : Prop) : (term8 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6787992 {K : Type'} (_88877 : K -> Prop) (_88881 : K) : (term1313 K _88877 _88881) = (@I (K -> Prop) _88877 _88881).
Proof. exact (@lem6787991 (@I (K -> Prop) _88877 _88881)). Qed.
Lemma lem6787993 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6787994 {K : Type'} (_88877 : K -> Prop) (_88881 : K) : (term1314 K _88877 _88881) = (term1145 K _88877 _88881).
Proof. exact (MK_COMB (@lem6787993) (@lem6787992 K _88877 _88881)). Qed.
Lemma lem6787996 (a : Prop) (b : Prop) : (term1309 a b) = (term1310 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6787997 {A K : Type'} (_88878 : A -> Prop) (_88879 : K -> A) (_88881 : K) (_88880 : A) : (term1315 A K _88878 _88879 _88881 _88880) = (term1316 A K _88878 _88879 _88881 _88880).
Proof. exact (@lem6787996 (term1114 A K _88878 _88879 _88881) ((@I (K -> A) _88879 _88881) = _88880)). Qed.
Lemma lem6787999 (a : Prop) : (term8 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6788000 {A K : Type'} (_88878 : A -> Prop) (_88879 : K -> A) (_88881 : K) : (term1317 A K _88878 _88879 _88881) = (term1112 A K _88878 _88879 _88881).
Proof. exact (@lem6787999 (term1112 A K _88878 _88879 _88881)). Qed.
Lemma lem6788001 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6788002 {A K : Type'} (_88878 : A -> Prop) (_88879 : K -> A) (_88881 : K) : (term1318 A K _88878 _88879 _88881) = (term1143 A K _88878 _88879 _88881).
Proof. exact (MK_COMB (@lem6788001) (@lem6788000 A K _88878 _88879 _88881)). Qed.
Lemma lem6788003 {A K : Type'} (_88879 : K -> A) (_88881 : K) (_88880 : A) : (term1142 A K _88879 _88881 _88880) = (term1142 A K _88879 _88881 _88880).
Proof. exact (eq_refl (term1142 A K _88879 _88881 _88880)). Qed.
Lemma lem6788004 {A K : Type'} (_88878 : A -> Prop) (_88879 : K -> A) (_88881 : K) (_88880 : A) : (term1316 A K _88878 _88879 _88881 _88880) = (term1144 A K _88878 _88879 _88881 _88880).
Proof. exact (MK_COMB (@lem6788002 A K _88878 _88879 _88881) (@lem6788003 A K _88879 _88881 _88880)). Qed.
Lemma lem6788005 {A K : Type'} (_88878 : A -> Prop) (_88879 : K -> A) (_88881 : K) (_88880 : A) : (term1315 A K _88878 _88879 _88881 _88880) = (term1144 A K _88878 _88879 _88881 _88880).
Proof. exact (TRANS (@lem6787997 A K _88878 _88879 _88881 _88880) (@lem6788004 A K _88878 _88879 _88881 _88880)). Qed.
Lemma lem6788006 {A K : Type'} (_88877 : K -> Prop) (_88878 : A -> Prop) (_88879 : K -> A) (_88881 : K) (_88880 : A) : (term1312 A K _88877 _88878 _88879 _88881 _88880) = (term1146 A K _88877 _88878 _88879 _88881 _88880).
Proof. exact (MK_COMB (@lem6787994 K _88877 _88881) (@lem6788005 A K _88878 _88879 _88881 _88880)). Qed.
Lemma lem6788007 {A K : Type'} (_88877 : K -> Prop) (_88878 : A -> Prop) (_88879 : K -> A) (_88881 : K) (_88880 : A) : (term1311 A K _88877 _88878 _88879 _88881 _88880) = (term1146 A K _88877 _88878 _88879 _88881 _88880).
Proof. exact (TRANS (@lem6787989 A K _88877 _88878 _88879 _88881 _88880) (@lem6788006 A K _88877 _88878 _88879 _88881 _88880)). Qed.
Lemma lem6788008 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6788009 {A K : Type'} (_88877 : K -> Prop) (_88878 : A -> Prop) (_88879 : K -> A) (_88881 : K) (_88880 : A) : (term1319 A K _88877 _88878 _88879 _88881 _88880) = (term1320 A K _88877 _88878 _88879 _88881 _88880).
Proof. exact (MK_COMB (@lem6788008) (@lem6788007 A K _88877 _88878 _88879 _88881 _88880)). Qed.
Lemma lem6788010 {A K : Type'} (_88875 : type836 A K) (_88877 : K -> Prop) (_88878 : A -> Prop) (_88879 : K -> A) (_88880 : A) : (term1106 A K _88875 _88877 _88878 _88879 _88880) = (term1106 A K _88875 _88877 _88878 _88879 _88880).
Proof. exact (eq_refl (term1106 A K _88875 _88877 _88878 _88879 _88880)). Qed.
Lemma lem6788011 {A K : Type'} (_88881 : K) (_88875 : type836 A K) (_88877 : K -> Prop) (_88878 : A -> Prop) (_88879 : K -> A) (_88880 : A) : (term1308 A K _88881 _88875 _88877 _88878 _88879 _88880) = (term1321 A K _88881 _88875 _88877 _88878 _88879 _88880).
Proof. exact (MK_COMB (@lem6788009 A K _88877 _88878 _88879 _88881 _88880) (@lem6788010 A K _88875 _88877 _88878 _88879 _88880)). Qed.
Lemma lem6788012 {A K : Type'} (_88881 : K) (_88875 : type836 A K) (_88877 : K -> Prop) (_88878 : A -> Prop) (_88879 : K -> A) (_88880 : A) : (term1304 A K _88875 _88877 _88878 _88879 _88881 _88880) = (term1321 A K _88881 _88875 _88877 _88878 _88879 _88880).
Proof. exact (TRANS (@lem6787986 A K _88881 _88875 _88877 _88878 _88879 _88880) (@lem6788011 A K _88881 _88875 _88877 _88878 _88879 _88880)). Qed.
Lemma lem6788014 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (h1 : term1086 A K ltle i' x _88876 k dom f neut) : term1144 A K dom f x neut.
Proof. exact (conj (@lem6787756 A K ltle i' x _88876 k dom f neut h1) (@lem6787763 A K ltle i' x _88876 k dom f neut h1)). Qed.
Lemma lem6788015 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (h1 : term1086 A K ltle i' x _88876 k dom f neut) : term1146 A K k dom f x neut.
Proof. exact (conj (@lem6787749 A K ltle i' x _88876 k dom f neut h1) (@lem6788014 A K ltle i' x _88876 k dom f neut h1)). Qed.
Lemma lem6788017 {A K : Type'} (_88881 : K) (_88877 : K -> Prop) (_88878 : A -> Prop) (_88879 : K -> A) (_88880 : A) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1321 A K _88881 _88875 _88877 _88878 _88879 _88880.
Proof. exact (EQ_MP (@lem6788012 A K _88881 _88875 _88877 _88878 _88879 _88880) (@lem6787983 A K _88877 _88878 _88879 _88881 _88880 _88875 h1)). Qed.
Lemma lem6788018 {A K : Type'} (_88881 : K) (_88877 : K -> Prop) (_88878 : A -> Prop) (_88879 : K -> A) (_88880 : A) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1321 A K _88881 _88875 _88877 _88878 _88879 _88880.
Proof. exact (@lem6788017 A K _88881 _88877 _88878 _88879 _88880 _88875 h1). Qed.
Lemma lem6788019 {A K : Type'} (x : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1321 A K x _88875 k dom f neut.
Proof. exact (@lem6788018 A K x k dom f neut _88875 h1). Qed.
Lemma lem6788022 {A K : Type'} (_88875 : type836 A K) (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (h1 : term446 A K _88875) (h2 : term1086 A K ltle i' x _88876 k dom f neut) : term1106 A K _88875 k dom f neut.
Proof. exact (@lem6788019 A K x k dom f neut _88875 h1 (@lem6788015 A K ltle i' x _88876 k dom f neut h2)). Qed.
Lemma lem6788023 {A K : Type'} (_88875 : type836 A K) (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (h1 : term446 A K _88875) (h2 : term1086 A K ltle i' x _88876 k dom f neut) : term1322 A K _88875 k dom f neut.
Proof. exact (fun h0 : term1258 A K _88875 k dom f neut => @lem6788022 A K _88875 ltle i' x _88876 k dom f neut h1 h2). Qed.
Lemma lem6788025 (p : Prop) : (term47 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6788026 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1322 A K _88875 k dom f neut) = (term1106 A K _88875 k dom f neut).
Proof. exact (@lem6788025 (term1106 A K _88875 k dom f neut)). Qed.
Lemma lem6788027 {A K : Type'} (_88875 : type836 A K) (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (h1 : term446 A K _88875) (h2 : term1086 A K ltle i' x _88876 k dom f neut) : term1106 A K _88875 k dom f neut.
Proof. exact (EQ_MP (@lem6788026 A K _88875 k dom f neut) (@lem6788023 A K _88875 ltle i' x _88876 k dom f neut h1 h2)). Qed.
Lemma lem6788030 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6788032 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1258 A K _88875 k dom f neut) = (term1323 A K _88875 k dom f neut).
Proof. exact (@lem6788030 (term1106 A K _88875 k dom f neut)). Qed.
Lemma lem6788035 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : term1117 K k i) (h2 : (_88875 k dom f neut) = i) : term1323 A K _88875 k dom f neut.
Proof. exact (EQ_MP (@lem6788032 A K _88875 k dom f neut) (@lem6786748 A K _88875 k dom f neut i h1 h2)). Qed.
Lemma lem6788038 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : term446 A K _88875) (h2 : term1117 K k i) (h3 : term1086 A K ltle i' x _88876 k dom f neut) (h4 : (_88875 k dom f neut) = i) : False.
Proof. exact (@lem6788035 A K _88875 k dom f neut i h2 h4 (@lem6788027 A K _88875 ltle i' x _88876 k dom f neut h1 h3)). Qed.
Lemma lem6788039 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : term446 A K _88875) (h2 : term1117 K k i) (h3 : term1086 A K ltle i' x _88876 k dom f neut) (h4 : (_88875 k dom f neut) = i) : term49.
Proof. exact (fun h0 : ~ False => @lem6788038 A K ltle i' x _88876 _88875 k dom f neut i h1 h2 h3 h4). Qed.
Lemma lem6788041 (p : Prop) : (term47 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6788042 : term49 = False.
Proof. exact (@lem6788041 False). Qed.
Lemma lem6788486 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (h1 : term1086 A K ltle i' x _88876 k dom f neut) : @I (K -> Prop) k x.
Proof. exact (proj1 (@lem6785089 A K ltle i' x _88876 k dom f neut h1)). Qed.
Lemma lem6788487 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (h1 : term1086 A K ltle i' x _88876 k dom f neut) : term1279 K k x.
Proof. exact (fun h0 : term1117 K k x => @lem6788486 A K ltle i' x _88876 k dom f neut h1). Qed.
Lemma lem6788489 (p : Prop) : (term47 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6788490 {K : Type'} (k : K -> Prop) (x : K) : (term1279 K k x) = (@I (K -> Prop) k x).
Proof. exact (@lem6788489 (@I (K -> Prop) k x)). Qed.
Lemma lem6788491 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (h1 : term1086 A K ltle i' x _88876 k dom f neut) : @I (K -> Prop) k x.
Proof. exact (EQ_MP (@lem6788490 K k x) (@lem6788487 A K ltle i' x _88876 k dom f neut h1)). Qed.
Lemma lem6788493 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (h1 : term1086 A K ltle i' x _88876 k dom f neut) : term1112 A K dom f x.
Proof. exact (proj1 (@lem6785090 A K ltle i' x _88876 k dom f neut h1)). Qed.
Lemma lem6788494 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (h1 : term1086 A K ltle i' x _88876 k dom f neut) : term1280 A K dom f x.
Proof. exact (fun h0 : term1114 A K dom f x => @lem6788493 A K ltle i' x _88876 k dom f neut h1). Qed.
Lemma lem6788496 (p : Prop) : (term47 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6788497 {A K : Type'} (dom : A -> Prop) (f : K -> A) (x : K) : (term1280 A K dom f x) = (term1112 A K dom f x).
Proof. exact (@lem6788496 (term1112 A K dom f x)). Qed.
Lemma lem6788498 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (h1 : term1086 A K ltle i' x _88876 k dom f neut) : term1112 A K dom f x.
Proof. exact (EQ_MP (@lem6788497 A K dom f x) (@lem6788494 A K ltle i' x _88876 k dom f neut h1)). Qed.
Lemma lem6788500 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (h1 : term1086 A K ltle i' x _88876 k dom f neut) : term1142 A K f x neut.
Proof. exact (proj2 (@lem6785090 A K ltle i' x _88876 k dom f neut h1)). Qed.
Lemma lem6788501 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (h1 : term1086 A K ltle i' x _88876 k dom f neut) : term1281 A K f x neut.
Proof. exact (fun h0 : (@I (K -> A) f x) = neut => @lem6788500 A K ltle i' x _88876 k dom f neut h1). Qed.
Lemma lem6788503 (p : Prop) : (term1282 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem6788504 {A K : Type'} (f : K -> A) (x : K) (neut : A) : (term1281 A K f x neut) = (term1142 A K f x neut).
Proof. exact (@lem6788503 ((@I (K -> A) f x) = neut)). Qed.
Lemma lem6788505 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (h1 : term1086 A K ltle i' x _88876 k dom f neut) : term1142 A K f x neut.
Proof. exact (EQ_MP (@lem6788504 A K f x neut) (@lem6788501 A K ltle i' x _88876 k dom f neut h1)). Qed.
Lemma lem6788511 (q : Prop) (p : Prop) (r : Prop) : (term277 p q r) = (term277 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6788512 {A K : Type'} (_88898 : K) (_88875 : type836 A K) (_88894 : K -> Prop) (_88895 : A -> Prop) (_88896 : K -> A) (_88897 : A) : (term1250 A K _88898 _88875 _88894 _88895 _88896 _88897) = (term1324 A K _88898 _88875 _88894 _88895 _88896 _88897).
Proof. exact (@lem6788511 (term1114 A K _88895 _88896 _88898) (term1117 K _88894 _88898) (term1325 A K _88898 _88875 _88894 _88895 _88896 _88897)). Qed.
Lemma lem6788526 (q : Prop) (p : Prop) (r : Prop) : (term277 p q r) = (term277 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6788527 {A K : Type'} (_88898 : K) (_88875 : type836 A K) (_88894 : K -> Prop) (_88895 : A -> Prop) (_88896 : K -> A) (_88897 : A) : (term1326 A K _88898 _88875 _88894 _88895 _88896 _88897) = (term1327 A K _88898 _88875 _88894 _88895 _88896 _88897).
Proof. exact (@lem6788526 ((@I (K -> A) _88896 _88898) = _88897) (term1117 K _88894 _88898) (term1102 A K _88875 _88894 _88895 _88896 _88897)). Qed.
Lemma lem6788543 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6788544 {A K : Type'} (_88875 : type836 A K) (_88895 : A -> Prop) (_88896 : K -> A) (_88897 : A) (_88894 : K -> Prop) (_88898 : K) : (term1328 A K _88898 _88875 _88894 _88895 _88896 _88897) = (term1329 A K _88875 _88895 _88896 _88897 _88894 _88898).
Proof. exact (@lem6788543 (term1102 A K _88875 _88894 _88895 _88896 _88897) (term1117 K _88894 _88898)). Qed.
Lemma lem6788550 {A K : Type'} (_88896 : K -> A) (_88898 : K) (_88897 : A) : (term1289 A K _88896 _88898 _88897) = (term1289 A K _88896 _88898 _88897).
Proof. exact (eq_refl (term1289 A K _88896 _88898 _88897)). Qed.
Lemma lem6788551 {A K : Type'} (_88875 : type836 A K) (_88895 : A -> Prop) (_88896 : K -> A) (_88897 : A) (_88894 : K -> Prop) (_88898 : K) : (term1327 A K _88898 _88875 _88894 _88895 _88896 _88897) = (term1330 A K _88875 _88895 _88896 _88897 _88894 _88898).
Proof. exact (MK_COMB (@lem6788550 A K _88896 _88898 _88897) (@lem6788544 A K _88875 _88895 _88896 _88897 _88894 _88898)). Qed.
Lemma lem6788562 {A K : Type'} (_88875 : type836 A K) (_88895 : A -> Prop) (_88896 : K -> A) (_88897 : A) (_88894 : K -> Prop) (_88898 : K) : (term1326 A K _88898 _88875 _88894 _88895 _88896 _88897) = (term1330 A K _88875 _88895 _88896 _88897 _88894 _88898).
Proof. exact (TRANS (@lem6788527 A K _88898 _88875 _88894 _88895 _88896 _88897) (@lem6788551 A K _88875 _88895 _88896 _88897 _88894 _88898)). Qed.
Lemma lem6788563 {A K : Type'} (_88895 : A -> Prop) (_88896 : K -> A) (_88898 : K) : (term1115 A K _88895 _88896 _88898) = (term1115 A K _88895 _88896 _88898).
Proof. exact (eq_refl (term1115 A K _88895 _88896 _88898)). Qed.
Lemma lem6788564 {A K : Type'} (_88875 : type836 A K) (_88895 : A -> Prop) (_88896 : K -> A) (_88897 : A) (_88894 : K -> Prop) (_88898 : K) : (term1324 A K _88898 _88875 _88894 _88895 _88896 _88897) = (term1331 A K _88875 _88895 _88896 _88897 _88894 _88898).
Proof. exact (MK_COMB (@lem6788563 A K _88895 _88896 _88898) (@lem6788562 A K _88875 _88895 _88896 _88897 _88894 _88898)). Qed.
Lemma lem6788568 (q : Prop) (p : Prop) (r : Prop) : (term277 p q r) = (term277 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6788569 {A K : Type'} (_88875 : type836 A K) (_88895 : A -> Prop) (_88896 : K -> A) (_88897 : A) (_88894 : K -> Prop) (_88898 : K) : (term1331 A K _88875 _88895 _88896 _88897 _88894 _88898) = (term1332 A K _88875 _88895 _88896 _88897 _88894 _88898).
Proof. exact (@lem6788568 ((@I (K -> A) _88896 _88898) = _88897) (term1114 A K _88895 _88896 _88898) (term1329 A K _88875 _88895 _88896 _88897 _88894 _88898)). Qed.
Lemma lem6788585 (q : Prop) (p : Prop) (r : Prop) : (term277 p q r) = (term277 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6788586 {A K : Type'} (_88875 : type836 A K) (_88897 : A) (_88895 : A -> Prop) (_88896 : K -> A) (_88894 : K -> Prop) (_88898 : K) : (term1333 A K _88875 _88895 _88896 _88897 _88894 _88898) = (term1334 A K _88875 _88897 _88895 _88896 _88894 _88898).
Proof. exact (@lem6788585 (term1102 A K _88875 _88894 _88895 _88896 _88897) (term1114 A K _88895 _88896 _88898) (term1117 K _88894 _88898)). Qed.
Lemma lem6788602 {A K : Type'} (_88896 : K -> A) (_88898 : K) (_88897 : A) : (term1289 A K _88896 _88898 _88897) = (term1289 A K _88896 _88898 _88897).
Proof. exact (eq_refl (term1289 A K _88896 _88898 _88897)). Qed.
Lemma lem6788603 {A K : Type'} (_88875 : type836 A K) (_88897 : A) (_88895 : A -> Prop) (_88896 : K -> A) (_88894 : K -> Prop) (_88898 : K) : (term1332 A K _88875 _88895 _88896 _88897 _88894 _88898) = (term1335 A K _88875 _88897 _88895 _88896 _88894 _88898).
Proof. exact (MK_COMB (@lem6788602 A K _88896 _88898 _88897) (@lem6788586 A K _88875 _88897 _88895 _88896 _88894 _88898)). Qed.
Lemma lem6788614 {A K : Type'} (_88875 : type836 A K) (_88897 : A) (_88895 : A -> Prop) (_88896 : K -> A) (_88894 : K -> Prop) (_88898 : K) : (term1331 A K _88875 _88895 _88896 _88897 _88894 _88898) = (term1335 A K _88875 _88897 _88895 _88896 _88894 _88898).
Proof. exact (TRANS (@lem6788569 A K _88875 _88895 _88896 _88897 _88894 _88898) (@lem6788603 A K _88875 _88897 _88895 _88896 _88894 _88898)). Qed.
Lemma lem6788615 {A K : Type'} (_88875 : type836 A K) (_88897 : A) (_88895 : A -> Prop) (_88896 : K -> A) (_88894 : K -> Prop) (_88898 : K) : (term1324 A K _88898 _88875 _88894 _88895 _88896 _88897) = (term1335 A K _88875 _88897 _88895 _88896 _88894 _88898).
Proof. exact (TRANS (@lem6788564 A K _88875 _88895 _88896 _88897 _88894 _88898) (@lem6788614 A K _88875 _88897 _88895 _88896 _88894 _88898)). Qed.
Lemma lem6788616 {A K : Type'} (_88875 : type836 A K) (_88897 : A) (_88895 : A -> Prop) (_88896 : K -> A) (_88894 : K -> Prop) (_88898 : K) : (term1250 A K _88898 _88875 _88894 _88895 _88896 _88897) = (term1335 A K _88875 _88897 _88895 _88896 _88894 _88898).
Proof. exact (TRANS (@lem6788512 A K _88898 _88875 _88894 _88895 _88896 _88897) (@lem6788615 A K _88875 _88897 _88895 _88896 _88894 _88898)). Qed.
Lemma lem6788617 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6788618 {A K : Type'} (_88875 : type836 A K) (_88897 : A) (_88895 : A -> Prop) (_88896 : K -> A) (_88894 : K -> Prop) (_88898 : K) : (term1336 A K _88898 _88875 _88894 _88895 _88896 _88897) = (term1337 A K _88875 _88897 _88895 _88896 _88894 _88898).
Proof. exact (MK_COMB (@lem6788617) (@lem6788616 A K _88875 _88897 _88895 _88896 _88894 _88898)). Qed.
Lemma lem6788632 (q : Prop) (p : Prop) (r : Prop) : (term277 p q r) = (term277 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6788633 {A K : Type'} (_88895 : A -> Prop) (_88894 : K -> Prop) (_88896 : K -> A) (_88898 : K) (_88897 : A) : (term1119 A K _88894 _88895 _88896 _88898 _88897) = (term1298 A K _88895 _88894 _88896 _88898 _88897).
Proof. exact (@lem6788632 (term1114 A K _88895 _88896 _88898) (term1117 K _88894 _88898) ((@I (K -> A) _88896 _88898) = _88897)). Qed.
Lemma lem6788647 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6788648 {A K : Type'} (_88896 : K -> A) (_88897 : A) (_88894 : K -> Prop) (_88898 : K) : (term1299 A K _88894 _88896 _88898 _88897) = (term1300 A K _88896 _88897 _88894 _88898).
Proof. exact (@lem6788647 ((@I (K -> A) _88896 _88898) = _88897) (term1117 K _88894 _88898)). Qed.
Lemma lem6788656 {A K : Type'} (_88895 : A -> Prop) (_88896 : K -> A) (_88898 : K) : (term1115 A K _88895 _88896 _88898) = (term1115 A K _88895 _88896 _88898).
Proof. exact (eq_refl (term1115 A K _88895 _88896 _88898)). Qed.
Lemma lem6788657 {A K : Type'} (_88895 : A -> Prop) (_88896 : K -> A) (_88897 : A) (_88894 : K -> Prop) (_88898 : K) : (term1298 A K _88895 _88894 _88896 _88898 _88897) = (term1301 A K _88895 _88896 _88897 _88894 _88898).
Proof. exact (MK_COMB (@lem6788656 A K _88895 _88896 _88898) (@lem6788648 A K _88896 _88897 _88894 _88898)). Qed.
Lemma lem6788661 (q : Prop) (p : Prop) (r : Prop) : (term277 p q r) = (term277 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6788662 {A K : Type'} (_88897 : A) (_88895 : A -> Prop) (_88896 : K -> A) (_88894 : K -> Prop) (_88898 : K) : (term1301 A K _88895 _88896 _88897 _88894 _88898) = (term1302 A K _88897 _88895 _88896 _88894 _88898).
Proof. exact (@lem6788661 ((@I (K -> A) _88896 _88898) = _88897) (term1114 A K _88895 _88896 _88898) (term1117 K _88894 _88898)). Qed.
Lemma lem6788680 {A K : Type'} (_88897 : A) (_88895 : A -> Prop) (_88896 : K -> A) (_88894 : K -> Prop) (_88898 : K) : (term1298 A K _88895 _88894 _88896 _88898 _88897) = (term1302 A K _88897 _88895 _88896 _88894 _88898).
Proof. exact (TRANS (@lem6788657 A K _88895 _88896 _88897 _88894 _88898) (@lem6788662 A K _88897 _88895 _88896 _88894 _88898)). Qed.
Lemma lem6788681 {A K : Type'} (_88897 : A) (_88895 : A -> Prop) (_88896 : K -> A) (_88894 : K -> Prop) (_88898 : K) : (term1119 A K _88894 _88895 _88896 _88898 _88897) = (term1302 A K _88897 _88895 _88896 _88894 _88898).
Proof. exact (TRANS (@lem6788633 A K _88895 _88894 _88896 _88898 _88897) (@lem6788680 A K _88897 _88895 _88896 _88894 _88898)). Qed.
Lemma lem6788682 {A K : Type'} (_88875 : type836 A K) (_88894 : K -> Prop) (_88895 : A -> Prop) (_88896 : K -> A) (_88897 : A) : (term1338 A K _88875 _88894 _88895 _88896 _88897) = (term1338 A K _88875 _88894 _88895 _88896 _88897).
Proof. exact (eq_refl (term1338 A K _88875 _88894 _88895 _88896 _88897)). Qed.
Lemma lem6788683 {A K : Type'} (_88875 : type836 A K) (_88897 : A) (_88895 : A -> Prop) (_88896 : K -> A) (_88894 : K -> Prop) (_88898 : K) : (term1339 A K _88875 _88894 _88895 _88896 _88898 _88897) = (term1340 A K _88875 _88897 _88895 _88896 _88894 _88898).
Proof. exact (MK_COMB (@lem6788682 A K _88875 _88894 _88895 _88896 _88897) (@lem6788681 A K _88897 _88895 _88896 _88894 _88898)). Qed.
Lemma lem6788687 (q : Prop) (p : Prop) (r : Prop) : (term277 p q r) = (term277 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6788688 {A K : Type'} (_88875 : type836 A K) (_88897 : A) (_88895 : A -> Prop) (_88896 : K -> A) (_88894 : K -> Prop) (_88898 : K) : (term1340 A K _88875 _88897 _88895 _88896 _88894 _88898) = (term1335 A K _88875 _88897 _88895 _88896 _88894 _88898).
Proof. exact (@lem6788687 ((@I (K -> A) _88896 _88898) = _88897) (term1102 A K _88875 _88894 _88895 _88896 _88897) (term1306 A K _88895 _88896 _88894 _88898)). Qed.
Lemma lem6788716 {A K : Type'} (_88875 : type836 A K) (_88897 : A) (_88895 : A -> Prop) (_88896 : K -> A) (_88894 : K -> Prop) (_88898 : K) : (term1339 A K _88875 _88894 _88895 _88896 _88898 _88897) = (term1335 A K _88875 _88897 _88895 _88896 _88894 _88898).
Proof. exact (TRANS (@lem6788683 A K _88875 _88897 _88895 _88896 _88894 _88898) (@lem6788688 A K _88875 _88897 _88895 _88896 _88894 _88898)). Qed.
Lemma lem6788717 {A K : Type'} (_88875 : type836 A K) (_88897 : A) (_88895 : A -> Prop) (_88896 : K -> A) (_88894 : K -> Prop) (_88898 : K) : ((term1250 A K _88898 _88875 _88894 _88895 _88896 _88897) = (term1339 A K _88875 _88894 _88895 _88896 _88898 _88897)) = ((term1335 A K _88875 _88897 _88895 _88896 _88894 _88898) = (term1335 A K _88875 _88897 _88895 _88896 _88894 _88898)).
Proof. exact (MK_COMB (@lem6788618 A K _88875 _88897 _88895 _88896 _88894 _88898) (@lem6788716 A K _88875 _88897 _88895 _88896 _88894 _88898)). Qed.
Lemma lem6788719 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6788720 (x : Prop) : (x = x) = True.
Proof. exact (@lem6788719 Prop x). Qed.
Lemma lem6788721 {A K : Type'} (_88875 : type836 A K) (_88897 : A) (_88895 : A -> Prop) (_88896 : K -> A) (_88894 : K -> Prop) (_88898 : K) : ((term1335 A K _88875 _88897 _88895 _88896 _88894 _88898) = (term1335 A K _88875 _88897 _88895 _88896 _88894 _88898)) = True.
Proof. exact (@lem6788720 (term1335 A K _88875 _88897 _88895 _88896 _88894 _88898)). Qed.
Lemma lem6788722 {A K : Type'} (_88875 : type836 A K) (_88894 : K -> Prop) (_88895 : A -> Prop) (_88896 : K -> A) (_88898 : K) (_88897 : A) : ((term1250 A K _88898 _88875 _88894 _88895 _88896 _88897) = (term1339 A K _88875 _88894 _88895 _88896 _88898 _88897)) = True.
Proof. exact (TRANS (@lem6788717 A K _88875 _88897 _88895 _88896 _88894 _88898) (@lem6788721 A K _88875 _88897 _88895 _88896 _88894 _88898)). Qed.
Lemma lem6788723 {A K : Type'} (_88875 : type836 A K) (_88894 : K -> Prop) (_88895 : A -> Prop) (_88896 : K -> A) (_88898 : K) (_88897 : A) : True = ((term1250 A K _88898 _88875 _88894 _88895 _88896 _88897) = (term1339 A K _88875 _88894 _88895 _88896 _88898 _88897)).
Proof. exact (SYM (@lem6788722 A K _88875 _88894 _88895 _88896 _88898 _88897)). Qed.
Lemma lem6788724 {A K : Type'} (_88875 : type836 A K) (_88894 : K -> Prop) (_88895 : A -> Prop) (_88896 : K -> A) (_88898 : K) (_88897 : A) : (term1250 A K _88898 _88875 _88894 _88895 _88896 _88897) = (term1339 A K _88875 _88894 _88895 _88896 _88898 _88897).
Proof. exact (EQ_MP (@lem6788723 A K _88875 _88894 _88895 _88896 _88898 _88897) (@lem0)). Qed.
Lemma lem6788725 {A K : Type'} (_88894 : K -> Prop) (_88895 : A -> Prop) (_88896 : K -> A) (_88898 : K) (_88897 : A) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1339 A K _88875 _88894 _88895 _88896 _88898 _88897.
Proof. exact (EQ_MP (@lem6788724 A K _88875 _88894 _88895 _88896 _88898 _88897) (@lem6787070 A K _88898 _88894 _88895 _88896 _88897 _88875 h1)). Qed.
Lemma lem6788727 (b : Prop) (a : Prop) : (a \/ b) = (term1307 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6788728 {A K : Type'} (_88898 : K) (_88875 : type836 A K) (_88894 : K -> Prop) (_88895 : A -> Prop) (_88896 : K -> A) (_88897 : A) : (term1339 A K _88875 _88894 _88895 _88896 _88898 _88897) = (term1341 A K _88898 _88875 _88894 _88895 _88896 _88897).
Proof. exact (@lem6788727 (term1119 A K _88894 _88895 _88896 _88898 _88897) (term1102 A K _88875 _88894 _88895 _88896 _88897)). Qed.
Lemma lem6788730 (a : Prop) (b : Prop) : (term1309 a b) = (term1310 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6788731 {A K : Type'} (_88894 : K -> Prop) (_88895 : A -> Prop) (_88896 : K -> A) (_88898 : K) (_88897 : A) : (term1311 A K _88894 _88895 _88896 _88898 _88897) = (term1312 A K _88894 _88895 _88896 _88898 _88897).
Proof. exact (@lem6788730 (term1117 K _88894 _88898) (term1116 A K _88895 _88896 _88898 _88897)). Qed.
Lemma lem6788733 (a : Prop) : (term8 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6788734 {K : Type'} (_88894 : K -> Prop) (_88898 : K) : (term1313 K _88894 _88898) = (@I (K -> Prop) _88894 _88898).
Proof. exact (@lem6788733 (@I (K -> Prop) _88894 _88898)). Qed.
Lemma lem6788735 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6788736 {K : Type'} (_88894 : K -> Prop) (_88898 : K) : (term1314 K _88894 _88898) = (term1145 K _88894 _88898).
Proof. exact (MK_COMB (@lem6788735) (@lem6788734 K _88894 _88898)). Qed.
Lemma lem6788738 (a : Prop) (b : Prop) : (term1309 a b) = (term1310 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6788739 {A K : Type'} (_88895 : A -> Prop) (_88896 : K -> A) (_88898 : K) (_88897 : A) : (term1315 A K _88895 _88896 _88898 _88897) = (term1316 A K _88895 _88896 _88898 _88897).
Proof. exact (@lem6788738 (term1114 A K _88895 _88896 _88898) ((@I (K -> A) _88896 _88898) = _88897)). Qed.
Lemma lem6788741 (a : Prop) : (term8 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6788742 {A K : Type'} (_88895 : A -> Prop) (_88896 : K -> A) (_88898 : K) : (term1317 A K _88895 _88896 _88898) = (term1112 A K _88895 _88896 _88898).
Proof. exact (@lem6788741 (term1112 A K _88895 _88896 _88898)). Qed.
Lemma lem6788743 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6788744 {A K : Type'} (_88895 : A -> Prop) (_88896 : K -> A) (_88898 : K) : (term1318 A K _88895 _88896 _88898) = (term1143 A K _88895 _88896 _88898).
Proof. exact (MK_COMB (@lem6788743) (@lem6788742 A K _88895 _88896 _88898)). Qed.
Lemma lem6788745 {A K : Type'} (_88896 : K -> A) (_88898 : K) (_88897 : A) : (term1142 A K _88896 _88898 _88897) = (term1142 A K _88896 _88898 _88897).
Proof. exact (eq_refl (term1142 A K _88896 _88898 _88897)). Qed.
Lemma lem6788746 {A K : Type'} (_88895 : A -> Prop) (_88896 : K -> A) (_88898 : K) (_88897 : A) : (term1316 A K _88895 _88896 _88898 _88897) = (term1144 A K _88895 _88896 _88898 _88897).
Proof. exact (MK_COMB (@lem6788744 A K _88895 _88896 _88898) (@lem6788745 A K _88896 _88898 _88897)). Qed.
Lemma lem6788747 {A K : Type'} (_88895 : A -> Prop) (_88896 : K -> A) (_88898 : K) (_88897 : A) : (term1315 A K _88895 _88896 _88898 _88897) = (term1144 A K _88895 _88896 _88898 _88897).
Proof. exact (TRANS (@lem6788739 A K _88895 _88896 _88898 _88897) (@lem6788746 A K _88895 _88896 _88898 _88897)). Qed.
Lemma lem6788748 {A K : Type'} (_88894 : K -> Prop) (_88895 : A -> Prop) (_88896 : K -> A) (_88898 : K) (_88897 : A) : (term1312 A K _88894 _88895 _88896 _88898 _88897) = (term1146 A K _88894 _88895 _88896 _88898 _88897).
Proof. exact (MK_COMB (@lem6788736 K _88894 _88898) (@lem6788747 A K _88895 _88896 _88898 _88897)). Qed.
Lemma lem6788749 {A K : Type'} (_88894 : K -> Prop) (_88895 : A -> Prop) (_88896 : K -> A) (_88898 : K) (_88897 : A) : (term1311 A K _88894 _88895 _88896 _88898 _88897) = (term1146 A K _88894 _88895 _88896 _88898 _88897).
Proof. exact (TRANS (@lem6788731 A K _88894 _88895 _88896 _88898 _88897) (@lem6788748 A K _88894 _88895 _88896 _88898 _88897)). Qed.
Lemma lem6788750 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6788751 {A K : Type'} (_88894 : K -> Prop) (_88895 : A -> Prop) (_88896 : K -> A) (_88898 : K) (_88897 : A) : (term1319 A K _88894 _88895 _88896 _88898 _88897) = (term1320 A K _88894 _88895 _88896 _88898 _88897).
Proof. exact (MK_COMB (@lem6788750) (@lem6788749 A K _88894 _88895 _88896 _88898 _88897)). Qed.
Lemma lem6788752 {A K : Type'} (_88875 : type836 A K) (_88894 : K -> Prop) (_88895 : A -> Prop) (_88896 : K -> A) (_88897 : A) : (term1102 A K _88875 _88894 _88895 _88896 _88897) = (term1102 A K _88875 _88894 _88895 _88896 _88897).
Proof. exact (eq_refl (term1102 A K _88875 _88894 _88895 _88896 _88897)). Qed.
Lemma lem6788753 {A K : Type'} (_88898 : K) (_88875 : type836 A K) (_88894 : K -> Prop) (_88895 : A -> Prop) (_88896 : K -> A) (_88897 : A) : (term1341 A K _88898 _88875 _88894 _88895 _88896 _88897) = (term1342 A K _88898 _88875 _88894 _88895 _88896 _88897).
Proof. exact (MK_COMB (@lem6788751 A K _88894 _88895 _88896 _88898 _88897) (@lem6788752 A K _88875 _88894 _88895 _88896 _88897)). Qed.
Lemma lem6788754 {A K : Type'} (_88898 : K) (_88875 : type836 A K) (_88894 : K -> Prop) (_88895 : A -> Prop) (_88896 : K -> A) (_88897 : A) : (term1339 A K _88875 _88894 _88895 _88896 _88898 _88897) = (term1342 A K _88898 _88875 _88894 _88895 _88896 _88897).
Proof. exact (TRANS (@lem6788728 A K _88898 _88875 _88894 _88895 _88896 _88897) (@lem6788753 A K _88898 _88875 _88894 _88895 _88896 _88897)). Qed.
Lemma lem6788756 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (h1 : term1086 A K ltle i' x _88876 k dom f neut) : term1144 A K dom f x neut.
Proof. exact (conj (@lem6788498 A K ltle i' x _88876 k dom f neut h1) (@lem6788505 A K ltle i' x _88876 k dom f neut h1)). Qed.
Lemma lem6788757 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (h1 : term1086 A K ltle i' x _88876 k dom f neut) : term1146 A K k dom f x neut.
Proof. exact (conj (@lem6788491 A K ltle i' x _88876 k dom f neut h1) (@lem6788756 A K ltle i' x _88876 k dom f neut h1)). Qed.
Lemma lem6788759 {A K : Type'} (_88898 : K) (_88894 : K -> Prop) (_88895 : A -> Prop) (_88896 : K -> A) (_88897 : A) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1342 A K _88898 _88875 _88894 _88895 _88896 _88897.
Proof. exact (EQ_MP (@lem6788754 A K _88898 _88875 _88894 _88895 _88896 _88897) (@lem6788725 A K _88894 _88895 _88896 _88898 _88897 _88875 h1)). Qed.
Lemma lem6788760 {A K : Type'} (_88898 : K) (_88894 : K -> Prop) (_88895 : A -> Prop) (_88896 : K -> A) (_88897 : A) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1342 A K _88898 _88875 _88894 _88895 _88896 _88897.
Proof. exact (@lem6788759 A K _88898 _88894 _88895 _88896 _88897 _88875 h1). Qed.
Lemma lem6788761 {A K : Type'} (x : K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1342 A K x _88875 k dom f neut.
Proof. exact (@lem6788760 A K x k dom f neut _88875 h1). Qed.
Lemma lem6788764 {A K : Type'} (_88875 : type836 A K) (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (h1 : term446 A K _88875) (h2 : term1086 A K ltle i' x _88876 k dom f neut) : term1102 A K _88875 k dom f neut.
Proof. exact (@lem6788761 A K x k dom f neut _88875 h1 (@lem6788757 A K ltle i' x _88876 k dom f neut h2)). Qed.
Lemma lem6788765 {A K : Type'} (_88875 : type836 A K) (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (h1 : term446 A K _88875) (h2 : term1086 A K ltle i' x _88876 k dom f neut) : term1343 A K _88875 k dom f neut.
Proof. exact (fun h0 : term1264 A K _88875 k dom f neut => @lem6788764 A K _88875 ltle i' x _88876 k dom f neut h1 h2). Qed.
Lemma lem6788767 (p : Prop) : (term47 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6788768 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1343 A K _88875 k dom f neut) = (term1102 A K _88875 k dom f neut).
Proof. exact (@lem6788767 (term1102 A K _88875 k dom f neut)). Qed.
Lemma lem6788769 {A K : Type'} (_88875 : type836 A K) (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (h1 : term446 A K _88875) (h2 : term1086 A K ltle i' x _88876 k dom f neut) : term1102 A K _88875 k dom f neut.
Proof. exact (EQ_MP (@lem6788768 A K _88875 k dom f neut) (@lem6788765 A K _88875 ltle i' x _88876 k dom f neut h1 h2)). Qed.
Lemma lem6788772 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6788774 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term1264 A K _88875 k dom f neut) = (term1344 A K _88875 k dom f neut).
Proof. exact (@lem6788772 (term1102 A K _88875 k dom f neut)). Qed.
Lemma lem6788777 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : term1114 A K dom f i) (h2 : (_88875 k dom f neut) = i) : term1344 A K _88875 k dom f neut.
Proof. exact (EQ_MP (@lem6788774 A K _88875 k dom f neut) (@lem6786972 A K _88875 k dom f neut i h1 h2)). Qed.
Lemma lem6788780 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : term446 A K _88875) (h2 : term1114 A K dom f i) (h3 : term1086 A K ltle i' x _88876 k dom f neut) (h4 : (_88875 k dom f neut) = i) : False.
Proof. exact (@lem6788777 A K _88875 k dom f neut i h2 h4 (@lem6788769 A K _88875 ltle i' x _88876 k dom f neut h1 h3)). Qed.
Lemma lem6788781 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : term446 A K _88875) (h2 : term1114 A K dom f i) (h3 : term1086 A K ltle i' x _88876 k dom f neut) (h4 : (_88875 k dom f neut) = i) : term49.
Proof. exact (fun h0 : ~ False => @lem6788780 A K ltle i' x _88876 _88875 k dom f neut i h1 h2 h3 h4). Qed.
Lemma lem6788783 (p : Prop) : (term47 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6788784 : term49 = False.
Proof. exact (@lem6788783 False). Qed.
Lemma lem6789151 {A K : Type'} : (@I (K -> A)) = (@I (K -> A)).
Proof. exact (eq_refl (@I (K -> A))). Qed.
Lemma lem6789152 {A K : Type'} (_89322 : K -> A) (_89324 : K -> A) (h1 : _89322 = _89324) : _89322 = _89324.
Proof. exact (h1). Qed.
Lemma lem6789153 {K : Type'} (_89323 : K) (_89325 : K) (h1 : _89323 = _89325) : _89323 = _89325.
Proof. exact (h1). Qed.
Lemma lem6789154 {A K : Type'} (_89322 : K -> A) (_89324 : K -> A) (h1 : _89322 = _89324) : (@I (K -> A) _89322) = (@I (K -> A) _89324).
Proof. exact (MK_COMB (@lem6789151 A K) (@lem6789152 A K _89322 _89324 h1)). Qed.
Lemma lem6789155 {A K : Type'} (_89323 : K) (_89325 : K) (_89322 : K -> A) (_89324 : K -> A) (h1 : _89323 = _89325) (h2 : _89322 = _89324) : (@I (K -> A) _89322 _89323) = (@I (K -> A) _89324 _89325).
Proof. exact (MK_COMB (@lem6789154 A K _89322 _89324 h2) (@lem6789153 K _89323 _89325 h1)). Qed.
Lemma lem6789156 {A K : Type'} (_89322 : K -> A) (_89324 : K -> A) (_89323 : K) (_89325 : K) (h1 : _89323 = _89325) : term1345 A K _89322 _89323 _89324 _89325.
Proof. exact (fun h0 : _89322 = _89324 => @lem6789155 A K _89323 _89325 _89322 _89324 h1 h0). Qed.
Lemma lem6789158 (a : Prop) (b : Prop) : (a -> b) = (term1346 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem6789159 {A K : Type'} (_89322 : K -> A) (_89323 : K) (_89324 : K -> A) (_89325 : K) : (term1345 A K _89322 _89323 _89324 _89325) = (term1347 A K _89322 _89323 _89324 _89325).
Proof. exact (@lem6789158 (_89322 = _89324) ((@I (K -> A) _89322 _89323) = (@I (K -> A) _89324 _89325))). Qed.
Lemma lem6789160 {A K : Type'} (_89322 : K -> A) (_89324 : K -> A) (_89323 : K) (_89325 : K) (h1 : _89323 = _89325) : term1347 A K _89322 _89323 _89324 _89325.
Proof. exact (EQ_MP (@lem6789159 A K _89322 _89323 _89324 _89325) (@lem6789156 A K _89322 _89324 _89323 _89325 h1)). Qed.
Lemma lem6789161 {A K : Type'} (_89322 : K -> A) (_89323 : K) (_89324 : K -> A) (_89325 : K) : term1348 A K _89322 _89323 _89324 _89325.
Proof. exact (fun h0 : _89323 = _89325 => @lem6789160 A K _89322 _89324 _89323 _89325 h0). Qed.
Lemma lem6789163 (a : Prop) (b : Prop) : (a -> b) = (term1346 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem6789164 {A K : Type'} (_89322 : K -> A) (_89323 : K) (_89324 : K -> A) (_89325 : K) : (term1348 A K _89322 _89323 _89324 _89325) = (term1349 A K _89322 _89323 _89324 _89325).
Proof. exact (@lem6789163 (_89323 = _89325) (term1347 A K _89322 _89323 _89324 _89325)). Qed.
Lemma lem6789165 {A K : Type'} (_89322 : K -> A) (_89323 : K) (_89324 : K -> A) (_89325 : K) : term1349 A K _89322 _89323 _89324 _89325.
Proof. exact (EQ_MP (@lem6789164 A K _89322 _89323 _89324 _89325) (@lem6789161 A K _89322 _89323 _89324 _89325)). Qed.
Lemma lem6789228 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (h1 : term1086 A K ltle i' x _88876 k dom f neut) : @I (K -> Prop) k x.
Proof. exact (proj1 (@lem6785089 A K ltle i' x _88876 k dom f neut h1)). Qed.
Lemma lem6789229 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (h1 : term1086 A K ltle i' x _88876 k dom f neut) : term1279 K k x.
Proof. exact (fun h0 : term1117 K k x => @lem6789228 A K ltle i' x _88876 k dom f neut h1). Qed.
Lemma lem6789231 (p : Prop) : (term47 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6789232 {K : Type'} (k : K -> Prop) (x : K) : (term1279 K k x) = (@I (K -> Prop) k x).
Proof. exact (@lem6789231 (@I (K -> Prop) k x)). Qed.
Lemma lem6789233 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (h1 : term1086 A K ltle i' x _88876 k dom f neut) : @I (K -> Prop) k x.
Proof. exact (EQ_MP (@lem6789232 K k x) (@lem6789229 A K ltle i' x _88876 k dom f neut h1)). Qed.
Lemma lem6789235 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (h1 : term1086 A K ltle i' x _88876 k dom f neut) : term1112 A K dom f x.
Proof. exact (proj1 (@lem6785090 A K ltle i' x _88876 k dom f neut h1)). Qed.
Lemma lem6789236 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (h1 : term1086 A K ltle i' x _88876 k dom f neut) : term1280 A K dom f x.
Proof. exact (fun h0 : term1114 A K dom f x => @lem6789235 A K ltle i' x _88876 k dom f neut h1). Qed.
Lemma lem6789238 (p : Prop) : (term47 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6789239 {A K : Type'} (dom : A -> Prop) (f : K -> A) (x : K) : (term1280 A K dom f x) = (term1112 A K dom f x).
Proof. exact (@lem6789238 (term1112 A K dom f x)). Qed.
Lemma lem6789240 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (h1 : term1086 A K ltle i' x _88876 k dom f neut) : term1112 A K dom f x.
Proof. exact (EQ_MP (@lem6789239 A K dom f x) (@lem6789236 A K ltle i' x _88876 k dom f neut h1)). Qed.
Lemma lem6789242 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : (@I (K -> A) f i) = neut) (h2 : (_88875 k dom f neut) = i) : (term1270 A K _88875 k dom f i) = i.
Proof. exact (EQ_MP (@lem6787111 A K _88875 k dom f i neut h1) (@lem6786480 A K _88875 k dom f neut i h2)). Qed.
Lemma lem6789243 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : (@I (K -> A) f i) = neut) (h2 : (_88875 k dom f neut) = i) : term1350 A K _88875 k dom f i.
Proof. exact (fun h0 : term1351 A K _88875 k dom f i => @lem6789242 A K _88875 k dom f neut i h1 h2). Qed.
Lemma lem6789245 (p : Prop) : (term47 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6789246 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) : (term1350 A K _88875 k dom f i) = ((term1270 A K _88875 k dom f i) = i).
Proof. exact (@lem6789245 ((term1270 A K _88875 k dom f i) = i)). Qed.
Lemma lem6789247 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : (@I (K -> A) f i) = neut) (h2 : (_88875 k dom f neut) = i) : (term1270 A K _88875 k dom f i) = i.
Proof. exact (EQ_MP (@lem6789246 A K _88875 k dom f i) (@lem6789243 A K _88875 k dom f neut i h1 h2)). Qed.
Lemma lem6789249 {A K : Type'} (x : K -> A) : x = x.
Proof. exact (@lem21386 (K -> A) x). Qed.
Lemma lem6789250 {A K : Type'} (x : K -> A) : x = x.
Proof. exact (@lem6789249 A K x). Qed.
Lemma lem6789251 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (@lem6789250 A K f). Qed.
Lemma lem6789252 {A K : Type'} (f : K -> A) : term1352 A K f.
Proof. exact (fun h0 : term1353 A K f => @lem6789251 A K f). Qed.
Lemma lem6789254 (p : Prop) : (term47 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6789255 {A K : Type'} (f : K -> A) : (term1352 A K f) = (f = f).
Proof. exact (@lem6789254 (f = f)). Qed.
Lemma lem6789256 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (EQ_MP (@lem6789255 A K f) (@lem6789252 A K f)). Qed.
Lemma lem6789274 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6789275 {A K : Type'} (_89323 : K) (_89325 : K) (_89322 : K -> A) (_89324 : K -> A) : (term1347 A K _89322 _89323 _89324 _89325) = (term1354 A K _89323 _89325 _89322 _89324).
Proof. exact (@lem6789274 ((@I (K -> A) _89322 _89323) = (@I (K -> A) _89324 _89325)) (term1355 A K _89322 _89324)). Qed.
Lemma lem6789285 {K : Type'} (_89323 : K) (_89325 : K) : (term1356 K _89323 _89325) = (term1356 K _89323 _89325).
Proof. exact (eq_refl (term1356 K _89323 _89325)). Qed.
Lemma lem6789286 {A K : Type'} (_89323 : K) (_89325 : K) (_89322 : K -> A) (_89324 : K -> A) : (term1349 A K _89322 _89323 _89324 _89325) = (term1357 A K _89323 _89325 _89322 _89324).
Proof. exact (MK_COMB (@lem6789285 K _89323 _89325) (@lem6789275 A K _89323 _89325 _89322 _89324)). Qed.
Lemma lem6789290 (q : Prop) (p : Prop) (r : Prop) : (term277 p q r) = (term277 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6789291 {A K : Type'} (_89323 : K) (_89325 : K) (_89322 : K -> A) (_89324 : K -> A) : (term1357 A K _89323 _89325 _89322 _89324) = (term1358 A K _89323 _89325 _89322 _89324).
Proof. exact (@lem6789290 ((@I (K -> A) _89322 _89323) = (@I (K -> A) _89324 _89325)) (term38 K _89323 _89325) (term1355 A K _89322 _89324)). Qed.
Lemma lem6789313 {A K : Type'} (_89323 : K) (_89325 : K) (_89322 : K -> A) (_89324 : K -> A) : (term1349 A K _89322 _89323 _89324 _89325) = (term1358 A K _89323 _89325 _89322 _89324).
Proof. exact (TRANS (@lem6789286 A K _89323 _89325 _89322 _89324) (@lem6789291 A K _89323 _89325 _89322 _89324)). Qed.
Lemma lem6789314 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6789315 {A K : Type'} (_89323 : K) (_89325 : K) (_89322 : K -> A) (_89324 : K -> A) : (term1359 A K _89322 _89323 _89324 _89325) = (term1360 A K _89323 _89325 _89322 _89324).
Proof. exact (MK_COMB (@lem6789314) (@lem6789313 A K _89323 _89325 _89322 _89324)). Qed.
Lemma lem6789337 {A K : Type'} (_89323 : K) (_89325 : K) (_89322 : K -> A) (_89324 : K -> A) : (term1358 A K _89323 _89325 _89322 _89324) = (term1358 A K _89323 _89325 _89322 _89324).
Proof. exact (eq_refl (term1358 A K _89323 _89325 _89322 _89324)). Qed.
Lemma lem6789338 {A K : Type'} (_89323 : K) (_89325 : K) (_89322 : K -> A) (_89324 : K -> A) : ((term1349 A K _89322 _89323 _89324 _89325) = (term1358 A K _89323 _89325 _89322 _89324)) = ((term1358 A K _89323 _89325 _89322 _89324) = (term1358 A K _89323 _89325 _89322 _89324)).
Proof. exact (MK_COMB (@lem6789315 A K _89323 _89325 _89322 _89324) (@lem6789337 A K _89323 _89325 _89322 _89324)). Qed.
Lemma lem6789340 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6789341 (x : Prop) : (x = x) = True.
Proof. exact (@lem6789340 Prop x). Qed.
Lemma lem6789342 {A K : Type'} (_89323 : K) (_89325 : K) (_89322 : K -> A) (_89324 : K -> A) : ((term1358 A K _89323 _89325 _89322 _89324) = (term1358 A K _89323 _89325 _89322 _89324)) = True.
Proof. exact (@lem6789341 (term1358 A K _89323 _89325 _89322 _89324)). Qed.
Lemma lem6789343 {A K : Type'} (_89323 : K) (_89325 : K) (_89322 : K -> A) (_89324 : K -> A) : ((term1349 A K _89322 _89323 _89324 _89325) = (term1358 A K _89323 _89325 _89322 _89324)) = True.
Proof. exact (TRANS (@lem6789338 A K _89323 _89325 _89322 _89324) (@lem6789342 A K _89323 _89325 _89322 _89324)). Qed.
Lemma lem6789344 {A K : Type'} (_89323 : K) (_89325 : K) (_89322 : K -> A) (_89324 : K -> A) : True = ((term1349 A K _89322 _89323 _89324 _89325) = (term1358 A K _89323 _89325 _89322 _89324)).
Proof. exact (SYM (@lem6789343 A K _89323 _89325 _89322 _89324)). Qed.
Lemma lem6789345 {A K : Type'} (_89323 : K) (_89325 : K) (_89322 : K -> A) (_89324 : K -> A) : (term1349 A K _89322 _89323 _89324 _89325) = (term1358 A K _89323 _89325 _89322 _89324).
Proof. exact (EQ_MP (@lem6789344 A K _89323 _89325 _89322 _89324) (@lem0)). Qed.
Lemma lem6789346 {A K : Type'} (_89323 : K) (_89325 : K) (_89322 : K -> A) (_89324 : K -> A) : term1358 A K _89323 _89325 _89322 _89324.
Proof. exact (EQ_MP (@lem6789345 A K _89323 _89325 _89322 _89324) (@lem6789165 A K _89322 _89323 _89324 _89325)). Qed.
Lemma lem6789348 (b : Prop) (a : Prop) : (a \/ b) = (term1307 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6789349 {A K : Type'} (_89322 : K -> A) (_89323 : K) (_89324 : K -> A) (_89325 : K) : (term1358 A K _89323 _89325 _89322 _89324) = (term1361 A K _89322 _89323 _89324 _89325).
Proof. exact (@lem6789348 (term1362 A K _89323 _89325 _89322 _89324) ((@I (K -> A) _89322 _89323) = (@I (K -> A) _89324 _89325))). Qed.
Lemma lem6789351 (a : Prop) (b : Prop) : (term1309 a b) = (term1310 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6789352 {A K : Type'} (_89323 : K) (_89325 : K) (_89322 : K -> A) (_89324 : K -> A) : (term1363 A K _89323 _89325 _89322 _89324) = (term1364 A K _89323 _89325 _89322 _89324).
Proof. exact (@lem6789351 (term38 K _89323 _89325) (term1355 A K _89322 _89324)). Qed.
Lemma lem6789354 (a : Prop) : (term8 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6789355 {K : Type'} (_89323 : K) (_89325 : K) : (term1365 K _89323 _89325) = (_89323 = _89325).
Proof. exact (@lem6789354 (_89323 = _89325)). Qed.
Lemma lem6789356 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6789357 {K : Type'} (_89323 : K) (_89325 : K) : (term1366 K _89323 _89325) = (term1367 K _89323 _89325).
Proof. exact (MK_COMB (@lem6789356) (@lem6789355 K _89323 _89325)). Qed.
Lemma lem6789359 (a : Prop) : (term8 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6789360 {A K : Type'} (_89322 : K -> A) (_89324 : K -> A) : (term1368 A K _89322 _89324) = (_89322 = _89324).
Proof. exact (@lem6789359 (_89322 = _89324)). Qed.
Lemma lem6789361 {A K : Type'} (_89323 : K) (_89325 : K) (_89322 : K -> A) (_89324 : K -> A) : (term1364 A K _89323 _89325 _89322 _89324) = (term1369 A K _89323 _89325 _89322 _89324).
Proof. exact (MK_COMB (@lem6789357 K _89323 _89325) (@lem6789360 A K _89322 _89324)). Qed.
Lemma lem6789362 {A K : Type'} (_89323 : K) (_89325 : K) (_89322 : K -> A) (_89324 : K -> A) : (term1363 A K _89323 _89325 _89322 _89324) = (term1369 A K _89323 _89325 _89322 _89324).
Proof. exact (TRANS (@lem6789352 A K _89323 _89325 _89322 _89324) (@lem6789361 A K _89323 _89325 _89322 _89324)). Qed.
Lemma lem6789363 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6789364 {A K : Type'} (_89323 : K) (_89325 : K) (_89322 : K -> A) (_89324 : K -> A) : (term1370 A K _89323 _89325 _89322 _89324) = (term1371 A K _89323 _89325 _89322 _89324).
Proof. exact (MK_COMB (@lem6789363) (@lem6789362 A K _89323 _89325 _89322 _89324)). Qed.
Lemma lem6789365 {A K : Type'} (_89322 : K -> A) (_89323 : K) (_89324 : K -> A) (_89325 : K) : ((@I (K -> A) _89322 _89323) = (@I (K -> A) _89324 _89325)) = ((@I (K -> A) _89322 _89323) = (@I (K -> A) _89324 _89325)).
Proof. exact (eq_refl ((@I (K -> A) _89322 _89323) = (@I (K -> A) _89324 _89325))). Qed.
Lemma lem6789366 {A K : Type'} (_89322 : K -> A) (_89323 : K) (_89324 : K -> A) (_89325 : K) : (term1361 A K _89322 _89323 _89324 _89325) = (term1372 A K _89322 _89323 _89324 _89325).
Proof. exact (MK_COMB (@lem6789364 A K _89323 _89325 _89322 _89324) (@lem6789365 A K _89322 _89323 _89324 _89325)). Qed.
Lemma lem6789367 {A K : Type'} (_89322 : K -> A) (_89323 : K) (_89324 : K -> A) (_89325 : K) : (term1358 A K _89323 _89325 _89322 _89324) = (term1372 A K _89322 _89323 _89324 _89325).
Proof. exact (TRANS (@lem6789349 A K _89322 _89323 _89324 _89325) (@lem6789366 A K _89322 _89323 _89324 _89325)). Qed.
Lemma lem6789369 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : (@I (K -> A) f i) = neut) (h2 : (_88875 k dom f neut) = i) : term1373 A K _88875 k dom i f.
Proof. exact (conj (@lem6789247 A K _88875 k dom f neut i h1 h2) (@lem6789256 A K f)). Qed.
Lemma lem6789371 {A K : Type'} (_89322 : K -> A) (_89323 : K) (_89324 : K -> A) (_89325 : K) : term1372 A K _89322 _89323 _89324 _89325.
Proof. exact (EQ_MP (@lem6789367 A K _89322 _89323 _89324 _89325) (@lem6789346 A K _89323 _89325 _89322 _89324)). Qed.
Lemma lem6789372 {A K : Type'} (_89322 : K -> A) (_89323 : K) (_89324 : K -> A) (_89325 : K) : term1372 A K _89322 _89323 _89324 _89325.
Proof. exact (@lem6789371 A K _89322 _89323 _89324 _89325). Qed.
Lemma lem6789373 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) : term1374 A K _88875 k dom f i.
Proof. exact (@lem6789372 A K f (term1270 A K _88875 k dom f i) f i). Qed.
Lemma lem6789376 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : (@I (K -> A) f i) = neut) (h2 : (_88875 k dom f neut) = i) : (term1375 A K _88875 k dom f i) = (@I (K -> A) f i).
Proof. exact (@lem6789373 A K _88875 k dom f i (@lem6789369 A K _88875 k dom f neut i h1 h2)). Qed.
Lemma lem6789377 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : (@I (K -> A) f i) = neut) (h2 : (_88875 k dom f neut) = i) : term1376 A K _88875 k dom f i.
Proof. exact (fun h0 : term1377 A K _88875 k dom f i => @lem6789376 A K _88875 k dom f neut i h1 h2). Qed.
Lemma lem6789379 (p : Prop) : (term47 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6789380 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) : (term1376 A K _88875 k dom f i) = ((term1375 A K _88875 k dom f i) = (@I (K -> A) f i)).
Proof. exact (@lem6789379 ((term1375 A K _88875 k dom f i) = (@I (K -> A) f i))). Qed.
Lemma lem6789381 {A K : Type'} (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : (@I (K -> A) f i) = neut) (h2 : (_88875 k dom f neut) = i) : (term1375 A K _88875 k dom f i) = (@I (K -> A) f i).
Proof. exact (EQ_MP (@lem6789380 A K _88875 k dom f i) (@lem6789377 A K _88875 k dom f neut i h1 h2)). Qed.
Lemma lem6789387 (q : Prop) (p : Prop) (r : Prop) : (term277 p q r) = (term277 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6789388 {A K : Type'} (_88915 : K) (_88875 : type836 A K) (_88911 : K -> Prop) (_88912 : A -> Prop) (_88913 : K -> A) (_88914 : A) : (term1254 A K _88915 _88875 _88911 _88912 _88913 _88914) = (term1378 A K _88915 _88875 _88911 _88912 _88913 _88914).
Proof. exact (@lem6789387 (term1114 A K _88912 _88913 _88915) (term1117 K _88911 _88915) (term1379 A K _88915 _88875 _88911 _88912 _88913 _88914)). Qed.
Lemma lem6789402 (q : Prop) (p : Prop) (r : Prop) : (term277 p q r) = (term277 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6789403 {A K : Type'} (_88915 : K) (_88875 : type836 A K) (_88911 : K -> Prop) (_88912 : A -> Prop) (_88913 : K -> A) (_88914 : A) : (term1380 A K _88915 _88875 _88911 _88912 _88913 _88914) = (term1381 A K _88915 _88875 _88911 _88912 _88913 _88914).
Proof. exact (@lem6789402 ((@I (K -> A) _88913 _88915) = _88914) (term1117 K _88911 _88915) (term1100 A K _88875 _88911 _88912 _88913 _88914)). Qed.
Lemma lem6789419 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6789420 {A K : Type'} (_88875 : type836 A K) (_88912 : A -> Prop) (_88913 : K -> A) (_88914 : A) (_88911 : K -> Prop) (_88915 : K) : (term1382 A K _88915 _88875 _88911 _88912 _88913 _88914) = (term1383 A K _88875 _88912 _88913 _88914 _88911 _88915).
Proof. exact (@lem6789419 (term1100 A K _88875 _88911 _88912 _88913 _88914) (term1117 K _88911 _88915)). Qed.
Lemma lem6789428 {A K : Type'} (_88913 : K -> A) (_88915 : K) (_88914 : A) : (term1289 A K _88913 _88915 _88914) = (term1289 A K _88913 _88915 _88914).
Proof. exact (eq_refl (term1289 A K _88913 _88915 _88914)). Qed.
Lemma lem6789429 {A K : Type'} (_88875 : type836 A K) (_88912 : A -> Prop) (_88913 : K -> A) (_88914 : A) (_88911 : K -> Prop) (_88915 : K) : (term1381 A K _88915 _88875 _88911 _88912 _88913 _88914) = (term1384 A K _88875 _88912 _88913 _88914 _88911 _88915).
Proof. exact (MK_COMB (@lem6789428 A K _88913 _88915 _88914) (@lem6789420 A K _88875 _88912 _88913 _88914 _88911 _88915)). Qed.
Lemma lem6789440 {A K : Type'} (_88875 : type836 A K) (_88912 : A -> Prop) (_88913 : K -> A) (_88914 : A) (_88911 : K -> Prop) (_88915 : K) : (term1380 A K _88915 _88875 _88911 _88912 _88913 _88914) = (term1384 A K _88875 _88912 _88913 _88914 _88911 _88915).
Proof. exact (TRANS (@lem6789403 A K _88915 _88875 _88911 _88912 _88913 _88914) (@lem6789429 A K _88875 _88912 _88913 _88914 _88911 _88915)). Qed.
Lemma lem6789441 {A K : Type'} (_88912 : A -> Prop) (_88913 : K -> A) (_88915 : K) : (term1115 A K _88912 _88913 _88915) = (term1115 A K _88912 _88913 _88915).
Proof. exact (eq_refl (term1115 A K _88912 _88913 _88915)). Qed.
Lemma lem6789442 {A K : Type'} (_88875 : type836 A K) (_88912 : A -> Prop) (_88913 : K -> A) (_88914 : A) (_88911 : K -> Prop) (_88915 : K) : (term1378 A K _88915 _88875 _88911 _88912 _88913 _88914) = (term1385 A K _88875 _88912 _88913 _88914 _88911 _88915).
Proof. exact (MK_COMB (@lem6789441 A K _88912 _88913 _88915) (@lem6789440 A K _88875 _88912 _88913 _88914 _88911 _88915)). Qed.
Lemma lem6789446 (q : Prop) (p : Prop) (r : Prop) : (term277 p q r) = (term277 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6789447 {A K : Type'} (_88875 : type836 A K) (_88912 : A -> Prop) (_88913 : K -> A) (_88914 : A) (_88911 : K -> Prop) (_88915 : K) : (term1385 A K _88875 _88912 _88913 _88914 _88911 _88915) = (term1386 A K _88875 _88912 _88913 _88914 _88911 _88915).
Proof. exact (@lem6789446 ((@I (K -> A) _88913 _88915) = _88914) (term1114 A K _88912 _88913 _88915) (term1383 A K _88875 _88912 _88913 _88914 _88911 _88915)). Qed.
Lemma lem6789463 (q : Prop) (p : Prop) (r : Prop) : (term277 p q r) = (term277 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6789464 {A K : Type'} (_88875 : type836 A K) (_88914 : A) (_88912 : A -> Prop) (_88913 : K -> A) (_88911 : K -> Prop) (_88915 : K) : (term1387 A K _88875 _88912 _88913 _88914 _88911 _88915) = (term1388 A K _88875 _88914 _88912 _88913 _88911 _88915).
Proof. exact (@lem6789463 (term1100 A K _88875 _88911 _88912 _88913 _88914) (term1114 A K _88912 _88913 _88915) (term1117 K _88911 _88915)). Qed.
Lemma lem6789482 {A K : Type'} (_88913 : K -> A) (_88915 : K) (_88914 : A) : (term1289 A K _88913 _88915 _88914) = (term1289 A K _88913 _88915 _88914).
Proof. exact (eq_refl (term1289 A K _88913 _88915 _88914)). Qed.
Lemma lem6789483 {A K : Type'} (_88875 : type836 A K) (_88914 : A) (_88912 : A -> Prop) (_88913 : K -> A) (_88911 : K -> Prop) (_88915 : K) : (term1386 A K _88875 _88912 _88913 _88914 _88911 _88915) = (term1389 A K _88875 _88914 _88912 _88913 _88911 _88915).
Proof. exact (MK_COMB (@lem6789482 A K _88913 _88915 _88914) (@lem6789464 A K _88875 _88914 _88912 _88913 _88911 _88915)). Qed.
Lemma lem6789494 {A K : Type'} (_88875 : type836 A K) (_88914 : A) (_88912 : A -> Prop) (_88913 : K -> A) (_88911 : K -> Prop) (_88915 : K) : (term1385 A K _88875 _88912 _88913 _88914 _88911 _88915) = (term1389 A K _88875 _88914 _88912 _88913 _88911 _88915).
Proof. exact (TRANS (@lem6789447 A K _88875 _88912 _88913 _88914 _88911 _88915) (@lem6789483 A K _88875 _88914 _88912 _88913 _88911 _88915)). Qed.
Lemma lem6789495 {A K : Type'} (_88875 : type836 A K) (_88914 : A) (_88912 : A -> Prop) (_88913 : K -> A) (_88911 : K -> Prop) (_88915 : K) : (term1378 A K _88915 _88875 _88911 _88912 _88913 _88914) = (term1389 A K _88875 _88914 _88912 _88913 _88911 _88915).
Proof. exact (TRANS (@lem6789442 A K _88875 _88912 _88913 _88914 _88911 _88915) (@lem6789494 A K _88875 _88914 _88912 _88913 _88911 _88915)). Qed.
Lemma lem6789496 {A K : Type'} (_88875 : type836 A K) (_88914 : A) (_88912 : A -> Prop) (_88913 : K -> A) (_88911 : K -> Prop) (_88915 : K) : (term1254 A K _88915 _88875 _88911 _88912 _88913 _88914) = (term1389 A K _88875 _88914 _88912 _88913 _88911 _88915).
Proof. exact (TRANS (@lem6789388 A K _88915 _88875 _88911 _88912 _88913 _88914) (@lem6789495 A K _88875 _88914 _88912 _88913 _88911 _88915)). Qed.
Lemma lem6789497 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6789498 {A K : Type'} (_88875 : type836 A K) (_88914 : A) (_88912 : A -> Prop) (_88913 : K -> A) (_88911 : K -> Prop) (_88915 : K) : (term1390 A K _88915 _88875 _88911 _88912 _88913 _88914) = (term1391 A K _88875 _88914 _88912 _88913 _88911 _88915).
Proof. exact (MK_COMB (@lem6789497) (@lem6789496 A K _88875 _88914 _88912 _88913 _88911 _88915)). Qed.
Lemma lem6789514 (q : Prop) (p : Prop) (r : Prop) : (term277 p q r) = (term277 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6789515 {A K : Type'} (_88915 : K) (_88875 : type836 A K) (_88911 : K -> Prop) (_88912 : A -> Prop) (_88913 : K -> A) (_88914 : A) : (term1392 A K _88915 _88875 _88911 _88912 _88913 _88914) = (term1393 A K _88915 _88875 _88911 _88912 _88913 _88914).
Proof. exact (@lem6789514 (term1114 A K _88912 _88913 _88915) (term1117 K _88911 _88915) (term1100 A K _88875 _88911 _88912 _88913 _88914)). Qed.
Lemma lem6789529 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6789530 {A K : Type'} (_88875 : type836 A K) (_88912 : A -> Prop) (_88913 : K -> A) (_88914 : A) (_88911 : K -> Prop) (_88915 : K) : (term1382 A K _88915 _88875 _88911 _88912 _88913 _88914) = (term1383 A K _88875 _88912 _88913 _88914 _88911 _88915).
Proof. exact (@lem6789529 (term1100 A K _88875 _88911 _88912 _88913 _88914) (term1117 K _88911 _88915)). Qed.
Lemma lem6789538 {A K : Type'} (_88912 : A -> Prop) (_88913 : K -> A) (_88915 : K) : (term1115 A K _88912 _88913 _88915) = (term1115 A K _88912 _88913 _88915).
Proof. exact (eq_refl (term1115 A K _88912 _88913 _88915)). Qed.
Lemma lem6789539 {A K : Type'} (_88875 : type836 A K) (_88912 : A -> Prop) (_88913 : K -> A) (_88914 : A) (_88911 : K -> Prop) (_88915 : K) : (term1393 A K _88915 _88875 _88911 _88912 _88913 _88914) = (term1387 A K _88875 _88912 _88913 _88914 _88911 _88915).
Proof. exact (MK_COMB (@lem6789538 A K _88912 _88913 _88915) (@lem6789530 A K _88875 _88912 _88913 _88914 _88911 _88915)). Qed.
Lemma lem6789543 (q : Prop) (p : Prop) (r : Prop) : (term277 p q r) = (term277 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6789544 {A K : Type'} (_88875 : type836 A K) (_88914 : A) (_88912 : A -> Prop) (_88913 : K -> A) (_88911 : K -> Prop) (_88915 : K) : (term1387 A K _88875 _88912 _88913 _88914 _88911 _88915) = (term1388 A K _88875 _88914 _88912 _88913 _88911 _88915).
Proof. exact (@lem6789543 (term1100 A K _88875 _88911 _88912 _88913 _88914) (term1114 A K _88912 _88913 _88915) (term1117 K _88911 _88915)). Qed.
Lemma lem6789562 {A K : Type'} (_88875 : type836 A K) (_88914 : A) (_88912 : A -> Prop) (_88913 : K -> A) (_88911 : K -> Prop) (_88915 : K) : (term1393 A K _88915 _88875 _88911 _88912 _88913 _88914) = (term1388 A K _88875 _88914 _88912 _88913 _88911 _88915).
Proof. exact (TRANS (@lem6789539 A K _88875 _88912 _88913 _88914 _88911 _88915) (@lem6789544 A K _88875 _88914 _88912 _88913 _88911 _88915)). Qed.
Lemma lem6789563 {A K : Type'} (_88875 : type836 A K) (_88914 : A) (_88912 : A -> Prop) (_88913 : K -> A) (_88911 : K -> Prop) (_88915 : K) : (term1392 A K _88915 _88875 _88911 _88912 _88913 _88914) = (term1388 A K _88875 _88914 _88912 _88913 _88911 _88915).
Proof. exact (TRANS (@lem6789515 A K _88915 _88875 _88911 _88912 _88913 _88914) (@lem6789562 A K _88875 _88914 _88912 _88913 _88911 _88915)). Qed.
Lemma lem6789564 {A K : Type'} (_88913 : K -> A) (_88915 : K) (_88914 : A) : (term1289 A K _88913 _88915 _88914) = (term1289 A K _88913 _88915 _88914).
Proof. exact (eq_refl (term1289 A K _88913 _88915 _88914)). Qed.
Lemma lem6789565 {A K : Type'} (_88875 : type836 A K) (_88914 : A) (_88912 : A -> Prop) (_88913 : K -> A) (_88911 : K -> Prop) (_88915 : K) : (term1394 A K _88915 _88875 _88911 _88912 _88913 _88914) = (term1389 A K _88875 _88914 _88912 _88913 _88911 _88915).
Proof. exact (MK_COMB (@lem6789564 A K _88913 _88915 _88914) (@lem6789563 A K _88875 _88914 _88912 _88913 _88911 _88915)). Qed.
Lemma lem6789576 {A K : Type'} (_88875 : type836 A K) (_88914 : A) (_88912 : A -> Prop) (_88913 : K -> A) (_88911 : K -> Prop) (_88915 : K) : ((term1254 A K _88915 _88875 _88911 _88912 _88913 _88914) = (term1394 A K _88915 _88875 _88911 _88912 _88913 _88914)) = ((term1389 A K _88875 _88914 _88912 _88913 _88911 _88915) = (term1389 A K _88875 _88914 _88912 _88913 _88911 _88915)).
Proof. exact (MK_COMB (@lem6789498 A K _88875 _88914 _88912 _88913 _88911 _88915) (@lem6789565 A K _88875 _88914 _88912 _88913 _88911 _88915)). Qed.
Lemma lem6789578 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6789579 (x : Prop) : (x = x) = True.
Proof. exact (@lem6789578 Prop x). Qed.
Lemma lem6789580 {A K : Type'} (_88875 : type836 A K) (_88914 : A) (_88912 : A -> Prop) (_88913 : K -> A) (_88911 : K -> Prop) (_88915 : K) : ((term1389 A K _88875 _88914 _88912 _88913 _88911 _88915) = (term1389 A K _88875 _88914 _88912 _88913 _88911 _88915)) = True.
Proof. exact (@lem6789579 (term1389 A K _88875 _88914 _88912 _88913 _88911 _88915)). Qed.
Lemma lem6789581 {A K : Type'} (_88915 : K) (_88875 : type836 A K) (_88911 : K -> Prop) (_88912 : A -> Prop) (_88913 : K -> A) (_88914 : A) : ((term1254 A K _88915 _88875 _88911 _88912 _88913 _88914) = (term1394 A K _88915 _88875 _88911 _88912 _88913 _88914)) = True.
Proof. exact (TRANS (@lem6789576 A K _88875 _88914 _88912 _88913 _88911 _88915) (@lem6789580 A K _88875 _88914 _88912 _88913 _88911 _88915)). Qed.
Lemma lem6789582 {A K : Type'} (_88915 : K) (_88875 : type836 A K) (_88911 : K -> Prop) (_88912 : A -> Prop) (_88913 : K -> A) (_88914 : A) : True = ((term1254 A K _88915 _88875 _88911 _88912 _88913 _88914) = (term1394 A K _88915 _88875 _88911 _88912 _88913 _88914)).
Proof. exact (SYM (@lem6789581 A K _88915 _88875 _88911 _88912 _88913 _88914)). Qed.
Lemma lem6789583 {A K : Type'} (_88915 : K) (_88875 : type836 A K) (_88911 : K -> Prop) (_88912 : A -> Prop) (_88913 : K -> A) (_88914 : A) : (term1254 A K _88915 _88875 _88911 _88912 _88913 _88914) = (term1394 A K _88915 _88875 _88911 _88912 _88913 _88914).
Proof. exact (EQ_MP (@lem6789582 A K _88915 _88875 _88911 _88912 _88913 _88914) (@lem0)). Qed.
Lemma lem6789584 {A K : Type'} (_88915 : K) (_88911 : K -> Prop) (_88912 : A -> Prop) (_88913 : K -> A) (_88914 : A) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1394 A K _88915 _88875 _88911 _88912 _88913 _88914.
Proof. exact (EQ_MP (@lem6789583 A K _88915 _88875 _88911 _88912 _88913 _88914) (@lem6787301 A K _88915 _88911 _88912 _88913 _88914 _88875 h1)). Qed.
Lemma lem6789586 (b : Prop) (a : Prop) : (a \/ b) = (term1307 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6789587 {A K : Type'} (_88875 : type836 A K) (_88911 : K -> Prop) (_88912 : A -> Prop) (_88913 : K -> A) (_88915 : K) (_88914 : A) : (term1394 A K _88915 _88875 _88911 _88912 _88913 _88914) = (term1395 A K _88875 _88911 _88912 _88913 _88915 _88914).
Proof. exact (@lem6789586 (term1392 A K _88915 _88875 _88911 _88912 _88913 _88914) ((@I (K -> A) _88913 _88915) = _88914)). Qed.
Lemma lem6789589 (a : Prop) (b : Prop) : (term1309 a b) = (term1310 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6789590 {A K : Type'} (_88915 : K) (_88875 : type836 A K) (_88911 : K -> Prop) (_88912 : A -> Prop) (_88913 : K -> A) (_88914 : A) : (term1396 A K _88915 _88875 _88911 _88912 _88913 _88914) = (term1397 A K _88915 _88875 _88911 _88912 _88913 _88914).
Proof. exact (@lem6789589 (term1117 K _88911 _88915) (term1398 A K _88915 _88875 _88911 _88912 _88913 _88914)). Qed.
Lemma lem6789592 (a : Prop) : (term8 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6789593 {K : Type'} (_88911 : K -> Prop) (_88915 : K) : (term1313 K _88911 _88915) = (@I (K -> Prop) _88911 _88915).
Proof. exact (@lem6789592 (@I (K -> Prop) _88911 _88915)). Qed.
Lemma lem6789594 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6789595 {K : Type'} (_88911 : K -> Prop) (_88915 : K) : (term1314 K _88911 _88915) = (term1145 K _88911 _88915).
Proof. exact (MK_COMB (@lem6789594) (@lem6789593 K _88911 _88915)). Qed.
Lemma lem6789597 (a : Prop) (b : Prop) : (term1309 a b) = (term1310 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6789598 {A K : Type'} (_88915 : K) (_88875 : type836 A K) (_88911 : K -> Prop) (_88912 : A -> Prop) (_88913 : K -> A) (_88914 : A) : (term1399 A K _88915 _88875 _88911 _88912 _88913 _88914) = (term1400 A K _88915 _88875 _88911 _88912 _88913 _88914).
Proof. exact (@lem6789597 (term1114 A K _88912 _88913 _88915) (term1100 A K _88875 _88911 _88912 _88913 _88914)). Qed.
Lemma lem6789600 (a : Prop) : (term8 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6789601 {A K : Type'} (_88912 : A -> Prop) (_88913 : K -> A) (_88915 : K) : (term1317 A K _88912 _88913 _88915) = (term1112 A K _88912 _88913 _88915).
Proof. exact (@lem6789600 (term1112 A K _88912 _88913 _88915)). Qed.
Lemma lem6789602 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6789603 {A K : Type'} (_88912 : A -> Prop) (_88913 : K -> A) (_88915 : K) : (term1318 A K _88912 _88913 _88915) = (term1143 A K _88912 _88913 _88915).
Proof. exact (MK_COMB (@lem6789602) (@lem6789601 A K _88912 _88913 _88915)). Qed.
Lemma lem6789605 (a : Prop) : (term8 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6789606 {A K : Type'} (_88875 : type836 A K) (_88911 : K -> Prop) (_88912 : A -> Prop) (_88913 : K -> A) (_88914 : A) : (term1401 A K _88875 _88911 _88912 _88913 _88914) = ((term1098 A K _88875 _88911 _88912 _88913 _88914) = _88914).
Proof. exact (@lem6789605 ((term1098 A K _88875 _88911 _88912 _88913 _88914) = _88914)). Qed.
Lemma lem6789607 {A K : Type'} (_88915 : K) (_88875 : type836 A K) (_88911 : K -> Prop) (_88912 : A -> Prop) (_88913 : K -> A) (_88914 : A) : (term1400 A K _88915 _88875 _88911 _88912 _88913 _88914) = (term1402 A K _88915 _88875 _88911 _88912 _88913 _88914).
Proof. exact (MK_COMB (@lem6789603 A K _88912 _88913 _88915) (@lem6789606 A K _88875 _88911 _88912 _88913 _88914)). Qed.
Lemma lem6789608 {A K : Type'} (_88915 : K) (_88875 : type836 A K) (_88911 : K -> Prop) (_88912 : A -> Prop) (_88913 : K -> A) (_88914 : A) : (term1399 A K _88915 _88875 _88911 _88912 _88913 _88914) = (term1402 A K _88915 _88875 _88911 _88912 _88913 _88914).
Proof. exact (TRANS (@lem6789598 A K _88915 _88875 _88911 _88912 _88913 _88914) (@lem6789607 A K _88915 _88875 _88911 _88912 _88913 _88914)). Qed.
Lemma lem6789609 {A K : Type'} (_88915 : K) (_88875 : type836 A K) (_88911 : K -> Prop) (_88912 : A -> Prop) (_88913 : K -> A) (_88914 : A) : (term1397 A K _88915 _88875 _88911 _88912 _88913 _88914) = (term1403 A K _88915 _88875 _88911 _88912 _88913 _88914).
Proof. exact (MK_COMB (@lem6789595 K _88911 _88915) (@lem6789608 A K _88915 _88875 _88911 _88912 _88913 _88914)). Qed.
Lemma lem6789610 {A K : Type'} (_88915 : K) (_88875 : type836 A K) (_88911 : K -> Prop) (_88912 : A -> Prop) (_88913 : K -> A) (_88914 : A) : (term1396 A K _88915 _88875 _88911 _88912 _88913 _88914) = (term1403 A K _88915 _88875 _88911 _88912 _88913 _88914).
Proof. exact (TRANS (@lem6789590 A K _88915 _88875 _88911 _88912 _88913 _88914) (@lem6789609 A K _88915 _88875 _88911 _88912 _88913 _88914)). Qed.
Lemma lem6789611 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6789612 {A K : Type'} (_88915 : K) (_88875 : type836 A K) (_88911 : K -> Prop) (_88912 : A -> Prop) (_88913 : K -> A) (_88914 : A) : (term1404 A K _88915 _88875 _88911 _88912 _88913 _88914) = (term1405 A K _88915 _88875 _88911 _88912 _88913 _88914).
Proof. exact (MK_COMB (@lem6789611) (@lem6789610 A K _88915 _88875 _88911 _88912 _88913 _88914)). Qed.
Lemma lem6789613 {A K : Type'} (_88913 : K -> A) (_88915 : K) (_88914 : A) : ((@I (K -> A) _88913 _88915) = _88914) = ((@I (K -> A) _88913 _88915) = _88914).
Proof. exact (eq_refl ((@I (K -> A) _88913 _88915) = _88914)). Qed.
Lemma lem6789614 {A K : Type'} (_88875 : type836 A K) (_88911 : K -> Prop) (_88912 : A -> Prop) (_88913 : K -> A) (_88915 : K) (_88914 : A) : (term1395 A K _88875 _88911 _88912 _88913 _88915 _88914) = (term1406 A K _88875 _88911 _88912 _88913 _88915 _88914).
Proof. exact (MK_COMB (@lem6789612 A K _88915 _88875 _88911 _88912 _88913 _88914) (@lem6789613 A K _88913 _88915 _88914)). Qed.
Lemma lem6789615 {A K : Type'} (_88875 : type836 A K) (_88911 : K -> Prop) (_88912 : A -> Prop) (_88913 : K -> A) (_88915 : K) (_88914 : A) : (term1394 A K _88915 _88875 _88911 _88912 _88913 _88914) = (term1406 A K _88875 _88911 _88912 _88913 _88915 _88914).
Proof. exact (TRANS (@lem6789587 A K _88875 _88911 _88912 _88913 _88915 _88914) (@lem6789614 A K _88875 _88911 _88912 _88913 _88915 _88914)). Qed.
Lemma lem6789617 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : term1086 A K ltle i' x _88876 k dom f neut) (h2 : (@I (K -> A) f i) = neut) (h3 : (_88875 k dom f neut) = i) : term1407 A K x _88875 k dom f i.
Proof. exact (conj (@lem6789240 A K ltle i' x _88876 k dom f neut h1) (@lem6789381 A K _88875 k dom f neut i h2 h3)). Qed.
Lemma lem6789618 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : term1086 A K ltle i' x _88876 k dom f neut) (h2 : (@I (K -> A) f i) = neut) (h3 : (_88875 k dom f neut) = i) : term1408 A K x _88875 k dom f i.
Proof. exact (conj (@lem6789233 A K ltle i' x _88876 k dom f neut h1) (@lem6789617 A K ltle i' x _88876 _88875 k dom f neut i h1 h2 h3)). Qed.
Lemma lem6789620 {A K : Type'} (_88911 : K -> Prop) (_88912 : A -> Prop) (_88913 : K -> A) (_88915 : K) (_88914 : A) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1406 A K _88875 _88911 _88912 _88913 _88915 _88914.
Proof. exact (EQ_MP (@lem6789615 A K _88875 _88911 _88912 _88913 _88915 _88914) (@lem6789584 A K _88915 _88911 _88912 _88913 _88914 _88875 h1)). Qed.
Lemma lem6789621 {A K : Type'} (_88911 : K -> Prop) (_88912 : A -> Prop) (_88913 : K -> A) (_88915 : K) (_88914 : A) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1406 A K _88875 _88911 _88912 _88913 _88915 _88914.
Proof. exact (@lem6789620 A K _88911 _88912 _88913 _88915 _88914 _88875 h1). Qed.
Lemma lem6789622 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (x : K) (f : K -> A) (i : K) (_88875 : type836 A K) (h1 : term446 A K _88875) : term1409 A K _88875 k dom x f i.
Proof. exact (@lem6789621 A K k dom f x (@I (K -> A) f i) _88875 h1). Qed.
Lemma lem6789625 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : term446 A K _88875) (h2 : term1086 A K ltle i' x _88876 k dom f neut) (h3 : (@I (K -> A) f i) = neut) (h4 : (_88875 k dom f neut) = i) : (@I (K -> A) f x) = (@I (K -> A) f i).
Proof. exact (@lem6789622 A K k dom x f i _88875 h1 (@lem6789618 A K ltle i' x _88876 _88875 k dom f neut i h2 h3 h4)). Qed.
Lemma lem6789626 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : term446 A K _88875) (h2 : term1086 A K ltle i' x _88876 k dom f neut) (h3 : (@I (K -> A) f i) = neut) (h4 : (_88875 k dom f neut) = i) : term1410 A K x f i.
Proof. exact (fun h0 : term1276 A K x f i => @lem6789625 A K ltle i' x _88876 _88875 k dom f neut i h1 h2 h3 h4). Qed.
Lemma lem6789628 (p : Prop) : (term47 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6789629 {A K : Type'} (x : K) (f : K -> A) (i : K) : (term1410 A K x f i) = ((@I (K -> A) f x) = (@I (K -> A) f i)).
Proof. exact (@lem6789628 ((@I (K -> A) f x) = (@I (K -> A) f i))). Qed.
Lemma lem6789630 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : term446 A K _88875) (h2 : term1086 A K ltle i' x _88876 k dom f neut) (h3 : (@I (K -> A) f i) = neut) (h4 : (_88875 k dom f neut) = i) : (@I (K -> A) f x) = (@I (K -> A) f i).
Proof. exact (EQ_MP (@lem6789629 A K x f i) (@lem6789626 A K ltle i' x _88876 _88875 k dom f neut i h1 h2 h3 h4)). Qed.
Lemma lem6789633 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6789635 {A K : Type'} (x : K) (f : K -> A) (i : K) : (term1276 A K x f i) = (term1411 A K x f i).
Proof. exact (@lem6789633 ((@I (K -> A) f x) = (@I (K -> A) f i))). Qed.
Lemma lem6789638 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (h1 : term1086 A K ltle i' x _88876 k dom f neut) (h2 : (@I (K -> A) f i) = neut) : term1411 A K x f i.
Proof. exact (EQ_MP (@lem6789635 A K x f i) (@lem6787194 A K ltle i' x _88876 k dom f i neut h1 h2)). Qed.
Lemma lem6789641 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : term446 A K _88875) (h2 : term1086 A K ltle i' x _88876 k dom f neut) (h3 : (@I (K -> A) f i) = neut) (h4 : (_88875 k dom f neut) = i) : False.
Proof. exact (@lem6789638 A K ltle i' x _88876 k dom f i neut h2 h3 (@lem6789630 A K ltle i' x _88876 _88875 k dom f neut i h1 h2 h3 h4)). Qed.
Lemma lem6789642 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : term446 A K _88875) (h2 : term1086 A K ltle i' x _88876 k dom f neut) (h3 : (@I (K -> A) f i) = neut) (h4 : (_88875 k dom f neut) = i) : term49.
Proof. exact (fun h0 : ~ False => @lem6789641 A K ltle i' x _88876 _88875 k dom f neut i h1 h2 h3 h4). Qed.
Lemma lem6789644 (p : Prop) : (term47 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6789645 : term49 = False.
Proof. exact (@lem6789644 False). Qed.
Lemma lem6789647 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : term446 A K _88875) (h2 : term1086 A K ltle i' x _88876 k dom f neut) (h3 : (@I (K -> A) f i) = neut) (h4 : (_88875 k dom f neut) = i) : False.
Proof. exact (EQ_MP (@lem6789645) (@lem6789642 A K ltle i' x _88876 _88875 k dom f neut i h1 h2 h3 h4)). Qed.
Lemma lem6789648 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : term446 A K _88875) (h2 : term1114 A K dom f i) (h3 : term1086 A K ltle i' x _88876 k dom f neut) (h4 : (_88875 k dom f neut) = i) : False.
Proof. exact (EQ_MP (@lem6788784) (@lem6788781 A K ltle i' x _88876 _88875 k dom f neut i h1 h2 h3 h4)). Qed.
Lemma lem6789649 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : term446 A K _88875) (h2 : term1117 K k i) (h3 : term1086 A K ltle i' x _88876 k dom f neut) (h4 : (_88875 k dom f neut) = i) : False.
Proof. exact (EQ_MP (@lem6788042) (@lem6788039 A K ltle i' x _88876 _88875 k dom f neut i h1 h2 h3 h4)). Qed.
Lemma lem6789650 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : term446 A K _88875) (h2 : term1086 A K ltle i' x _88876 k dom f neut) (h3 : (@I (K -> A) f i) = neut) (h4 : (_88875 k dom f neut) = i) : ((@I (K -> A) f i) = neut) = False.
Proof. exact (prop_ext (fun h5 : (@I (K -> A) f i) = neut => @lem6789647 A K ltle i' x _88876 _88875 k dom f neut i h1 h2 h3 h4) (fun h5 : False => @lem6786502 A K f i neut h3)). Qed.
Lemma lem6789651 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : term446 A K _88875) (h2 : term1086 A K ltle i' x _88876 k dom f neut) (h3 : (@I (K -> A) f i) = neut) (h4 : (_88875 k dom f neut) = i) : False.
Proof. exact (EQ_MP (@lem6789650 A K ltle i' x _88876 _88875 k dom f neut i h1 h2 h3 h4) (@lem6786502 A K f i neut h3)). Qed.
Lemma lem6789652 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : term446 A K _88875) (h2 : term1114 A K dom f i) (h3 : term1086 A K ltle i' x _88876 k dom f neut) (h4 : (_88875 k dom f neut) = i) : (term1114 A K dom f i) = False.
Proof. exact (prop_ext (fun h5 : term1114 A K dom f i => @lem6789648 A K ltle i' x _88876 _88875 k dom f neut i h1 h2 h3 h4) (fun h5 : False => @lem6786344 A K dom f i h2)). Qed.
Lemma lem6789653 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : term446 A K _88875) (h2 : term1114 A K dom f i) (h3 : term1086 A K ltle i' x _88876 k dom f neut) (h4 : (_88875 k dom f neut) = i) : False.
Proof. exact (EQ_MP (@lem6789652 A K ltle i' x _88876 _88875 k dom f neut i h1 h2 h3 h4) (@lem6786344 A K dom f i h2)). Qed.
Lemma lem6789654 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : term446 A K _88875) (h2 : term1117 K k i) (h3 : term1086 A K ltle i' x _88876 k dom f neut) (h4 : (_88875 k dom f neut) = i) : (term1117 K k i) = False.
Proof. exact (prop_ext (fun h5 : term1117 K k i => @lem6789649 A K ltle i' x _88876 _88875 k dom f neut i h1 h2 h3 h4) (fun h5 : False => @lem6786186 K k i h2)). Qed.
Lemma lem6789655 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : term446 A K _88875) (h2 : term1117 K k i) (h3 : term1086 A K ltle i' x _88876 k dom f neut) (h4 : (_88875 k dom f neut) = i) : False.
Proof. exact (EQ_MP (@lem6789654 A K ltle i' x _88876 _88875 k dom f neut i h1 h2 h3 h4) (@lem6786186 K k i h2)). Qed.
Lemma lem6789656 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : term446 A K _88875) (h2 : term1086 A K ltle i' x _88876 k dom f neut) (h3 : (@I (K -> A) f i) = neut) (h4 : (_88875 k dom f neut) = i) : ((@I (K -> A) f i) = neut) = False.
Proof. exact (prop_ext (fun h5 : (@I (K -> A) f i) = neut => @lem6789651 A K ltle i' x _88876 _88875 k dom f neut i h1 h2 h3 h4) (fun h5 : False => @lem6785973 A K f i neut h3)). Qed.
Lemma lem6789657 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : term446 A K _88875) (h2 : term1086 A K ltle i' x _88876 k dom f neut) (h3 : (@I (K -> A) f i) = neut) (h4 : (_88875 k dom f neut) = i) : False.
Proof. exact (EQ_MP (@lem6789656 A K ltle i' x _88876 _88875 k dom f neut i h1 h2 h3 h4) (@lem6785973 A K f i neut h3)). Qed.
Lemma lem6789658 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : term446 A K _88875) (h2 : term1114 A K dom f i) (h3 : term1086 A K ltle i' x _88876 k dom f neut) (h4 : (_88875 k dom f neut) = i) : (term1114 A K dom f i) = False.
Proof. exact (prop_ext (fun h5 : term1114 A K dom f i => @lem6789653 A K ltle i' x _88876 _88875 k dom f neut i h1 h2 h3 h4) (fun h5 : False => @lem6785681 A K dom f i h2)). Qed.
Lemma lem6789659 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : term446 A K _88875) (h2 : term1114 A K dom f i) (h3 : term1086 A K ltle i' x _88876 k dom f neut) (h4 : (_88875 k dom f neut) = i) : False.
Proof. exact (EQ_MP (@lem6789658 A K ltle i' x _88876 _88875 k dom f neut i h1 h2 h3 h4) (@lem6785681 A K dom f i h2)). Qed.
Lemma lem6789660 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : term446 A K _88875) (h2 : term1117 K k i) (h3 : term1086 A K ltle i' x _88876 k dom f neut) (h4 : (_88875 k dom f neut) = i) : (term1117 K k i) = False.
Proof. exact (prop_ext (fun h5 : term1117 K k i => @lem6789655 A K ltle i' x _88876 _88875 k dom f neut i h1 h2 h3 h4) (fun h5 : False => @lem6785389 K k i h2)). Qed.
Lemma lem6789661 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : term446 A K _88875) (h2 : term1117 K k i) (h3 : term1086 A K ltle i' x _88876 k dom f neut) (h4 : (_88875 k dom f neut) = i) : False.
Proof. exact (EQ_MP (@lem6789660 A K ltle i' x _88876 _88875 k dom f neut i h1 h2 h3 h4) (@lem6785389 K k i h2)). Qed.
Lemma lem6789662 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : term446 A K _88875) (h2 : term1086 A K ltle i' x _88876 k dom f neut) (h3 : (@I (K -> A) f i) = neut) (h4 : (_88875 k dom f neut) = i) : ((@I (K -> A) f i) = neut) = False.
Proof. exact (prop_ext (fun h5 : (@I (K -> A) f i) = neut => @lem6789657 A K ltle i' x _88876 _88875 k dom f neut i h1 h2 h3 h4) (fun h5 : False => @lem6785973 A K f i neut h3)). Qed.
Lemma lem6789663 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : term446 A K _88875) (h2 : term1086 A K ltle i' x _88876 k dom f neut) (h3 : (@I (K -> A) f i) = neut) (h4 : (_88875 k dom f neut) = i) : False.
Proof. exact (EQ_MP (@lem6789662 A K ltle i' x _88876 _88875 k dom f neut i h1 h2 h3 h4) (@lem6785973 A K f i neut h3)). Qed.
Lemma lem6789664 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : term446 A K _88875) (h2 : term1114 A K dom f i) (h3 : term1086 A K ltle i' x _88876 k dom f neut) (h4 : (_88875 k dom f neut) = i) : (term1114 A K dom f i) = False.
Proof. exact (prop_ext (fun h5 : term1114 A K dom f i => @lem6789659 A K ltle i' x _88876 _88875 k dom f neut i h1 h2 h3 h4) (fun h5 : False => @lem6785681 A K dom f i h2)). Qed.
Lemma lem6789665 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : term446 A K _88875) (h2 : term1114 A K dom f i) (h3 : term1086 A K ltle i' x _88876 k dom f neut) (h4 : (_88875 k dom f neut) = i) : False.
Proof. exact (EQ_MP (@lem6789664 A K ltle i' x _88876 _88875 k dom f neut i h1 h2 h3 h4) (@lem6785681 A K dom f i h2)). Qed.
Lemma lem6789666 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : term446 A K _88875) (h2 : term1117 K k i) (h3 : term1086 A K ltle i' x _88876 k dom f neut) (h4 : (_88875 k dom f neut) = i) : (term1117 K k i) = False.
Proof. exact (prop_ext (fun h5 : term1117 K k i => @lem6789661 A K ltle i' x _88876 _88875 k dom f neut i h1 h2 h3 h4) (fun h5 : False => @lem6785389 K k i h2)). Qed.
Lemma lem6789667 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : term446 A K _88875) (h2 : term1117 K k i) (h3 : term1086 A K ltle i' x _88876 k dom f neut) (h4 : (_88875 k dom f neut) = i) : False.
Proof. exact (EQ_MP (@lem6789666 A K ltle i' x _88876 _88875 k dom f neut i h1 h2 h3 h4) (@lem6785389 K k i h2)). Qed.
Lemma lem6789668 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (h1 : term446 A K _88875) (h2 : term1086 A K ltle i' x _88876 k dom f neut) (h3 : (_88875 k dom f neut) = i) (h4 : term1116 A K dom f i neut) : False.
Proof. exact (or_elim (@lem6785095 A K dom f i neut h4) (fun h0 : term1114 A K dom f i => @lem6789665 A K ltle i' x _88876 _88875 k dom f neut i h1 h0 h2 h3) (fun h0 : (@I (K -> A) f i) = neut => @lem6789663 A K ltle i' x _88876 _88875 k dom f neut i h1 h2 h0 h3)). Qed.
Lemma lem6789669 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : term446 A K _88875) (h2 : term351 A K k dom f i neut) (h3 : term1086 A K ltle i' x _88876 k dom f neut) (h4 : (_88875 k dom f neut) = i) : False.
Proof. exact (or_elim (@lem6784384 A K k dom f i neut h2) (fun h0 : term1117 K k i => @lem6789667 A K ltle i' x _88876 _88875 k dom f neut i h1 h0 h3 h4) (fun h0 : term1116 A K dom f i neut => @lem6789668 A K ltle i' x _88876 _88875 k dom f i neut h1 h3 h4 h0)). Qed.
Lemma lem6789670 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (x : K) (_88876 : type835 A K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : term608 A K _88876) (h2 : term446 A K _88875) (h3 : term351 A K k dom f i neut) (h4 : term1086 A K ltle i' x _88876 k dom f neut) (h5 : (_88875 k dom f neut) = i) : False.
Proof. exact (ex_elim (@lem6783466 A K _88876 h1) (fun i'' : type834 A K => fun h0 : term911 A K _88876 i'' => @lem6789669 A K ltle i' x _88876 _88875 k dom f neut i h2 h3 h4 h5)). Qed.
Lemma lem6789671 {A K : Type'} (ltle : type1402 K) (i' : K -> K) (_88876 : type835 A K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : term608 A K _88876) (h2 : term446 A K _88875) (h3 : term1089 A K ltle i' _88876 k dom f neut) (h4 : term351 A K k dom f i neut) (h5 : (_88875 k dom f neut) = i) : False.
Proof. exact (ex_elim (@lem6784089 A K ltle i' _88876 k dom f neut h3) (fun x : K => fun h0 : term1088 A K ltle i' _88876 k dom f neut x => @lem6789670 A K ltle i' x _88876 _88875 k dom f neut i h1 h2 h4 h0 h5)). Qed.
Lemma lem6789672 {A K : Type'} (ltle : type1402 K) (_88876 : type835 A K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : term608 A K _88876) (h2 : term446 A K _88875) (h3 : term351 A K k dom f i neut) (h4 : term513 A K ltle _88876 k dom f neut) (h5 : (_88875 k dom f neut) = i) : False.
Proof. exact (ex_elim (@lem6784062 A K ltle _88876 k dom f neut h4) (fun i' : K -> K => fun h0 : term1090 A K ltle _88876 k dom f neut i' => @lem6789671 A K ltle i' _88876 _88875 k dom f neut i h1 h2 h0 h3 h5)). Qed.
Lemma lem6789673 {A K : Type'} (ltle : type1402 K) (_88876 : type835 A K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : term608 A K _88876) (h2 : term446 A K _88875) (h3 : term351 A K k dom f i neut) (h4 : term513 A K ltle _88876 k dom f neut) (h5 : (_88875 k dom f neut) = i) : ((_88875 k dom f neut) = i) = False.
Proof. exact (prop_ext (fun h6 : (_88875 k dom f neut) = i => @lem6789672 A K ltle _88876 _88875 k dom f neut i h1 h2 h3 h4 h5) (fun h6 : False => @lem6784068 A K _88875 k dom f neut i h5)). Qed.
Lemma lem6789674 {A K : Type'} (ltle : type1402 K) (_88876 : type835 A K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : term608 A K _88876) (h2 : term446 A K _88875) (h3 : term351 A K k dom f i neut) (h4 : term513 A K ltle _88876 k dom f neut) (h5 : (_88875 k dom f neut) = i) : False.
Proof. exact (EQ_MP (@lem6789673 A K ltle _88876 _88875 k dom f neut i h1 h2 h3 h4 h5) (@lem6784068 A K _88875 k dom f neut i h5)). Qed.
Lemma lem6789675 {A K : Type'} (ltle : type1402 K) (_88876 : type835 A K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : term608 A K _88876) (h2 : term446 A K _88875) (h3 : term351 A K k dom f i neut) (h4 : term513 A K ltle _88876 k dom f neut) (h5 : (_88875 k dom f neut) = i) : (term351 A K k dom f i neut) = False.
Proof. exact (prop_ext (fun h6 : term351 A K k dom f i neut => @lem6789674 A K ltle _88876 _88875 k dom f neut i h1 h2 h3 h4 h5) (fun h6 : False => @lem6782440 A K k dom f i neut h3)). Qed.
Lemma lem6789676 {A K : Type'} (ltle : type1402 K) (_88876 : type835 A K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : term608 A K _88876) (h2 : term446 A K _88875) (h3 : term351 A K k dom f i neut) (h4 : term513 A K ltle _88876 k dom f neut) (h5 : (_88875 k dom f neut) = i) : False.
Proof. exact (EQ_MP (@lem6789675 A K ltle _88876 _88875 k dom f neut i h1 h2 h3 h4 h5) (@lem6782440 A K k dom f i neut h3)). Qed.
Lemma lem6789677 {A K : Type'} (ltle : type1402 K) (_88876 : type835 A K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : term608 A K _88876) (h2 : term446 A K _88875) (h3 : term513 A K ltle _88876 k dom f neut) (h4 : (_88875 k dom f neut) = i) : term613 A K k dom f i neut.
Proof. exact (fun h0 : term351 A K k dom f i neut => @lem6789676 A K ltle _88876 _88875 k dom f neut i h1 h2 h0 h3 h4). Qed.
Lemma lem6789678 {A K : Type'} (ltle : type1402 K) (_88876 : type835 A K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (i : K) (h1 : term608 A K _88876) (h2 : term446 A K _88875) (h3 : term513 A K ltle _88876 k dom f neut) (h4 : (_88875 k dom f neut) = i) : term312 A K k dom f i neut.
Proof. exact (EQ_MP (@lem6782439 A K k dom f i neut) (@lem6789677 A K ltle _88876 _88875 k dom f neut i h1 h2 h3 h4)). Qed.
Lemma lem6789679 {A K : Type'} (i : K) (_88875 : type836 A K) (ltle : type1402 K) (_88876 : type835 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) (h1 : term608 A K _88876) (h2 : term446 A K _88875) (h3 : term513 A K ltle _88876 k dom f neut) : term450 A K _88875 k dom f i neut.
Proof. exact (fun h0 : (_88875 k dom f neut) = i => @lem6789678 A K ltle _88876 _88875 k dom f neut i h1 h2 h3 h0). Qed.
Lemma lem6789680 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (_88876 : type835 A K) (_88875 : type836 A K) (h1 : term608 A K _88876) (h2 : term446 A K _88875) : term515 A K ltle _88876 _88875 k dom f i neut.
Proof. exact (fun h0 : term513 A K ltle _88876 k dom f neut => @lem6789679 A K i _88875 ltle _88876 k dom f neut h1 h2 h0). Qed.
Lemma lem6789681 {A K : Type'} (ltle : type1402 K) (_88875 : type836 A K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (_88876 : type835 A K) (h1 : term608 A K _88876) : term516 A K ltle _88876 _88875 k dom f i neut.
Proof. exact (fun h0 : term446 A K _88875 => @lem6789680 A K ltle k dom f i neut _88876 _88875 h1 h0). Qed.
Lemma lem6789686 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (_88876 : type835 A K) (h1 : term608 A K _88876) : term518 A K ltle _88876 k dom f i neut.
Proof. exact (fun _88875 : type836 A K => @lem6789681 A K ltle _88875 k dom f i neut _88876 h1). Qed.
Lemma lem6789691 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (_88876 : type835 A K) (h1 : term608 A K _88876) : term520 A K _88876 k dom f i neut.
Proof. exact (fun ltle : type1402 K => @lem6789686 A K ltle k dom f i neut _88876 h1). Qed.
Lemma lem6789696 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (_88876 : type835 A K) (h1 : term608 A K _88876) : term522 A K _88876 dom f i neut.
Proof. exact (fun k : K -> Prop => @lem6789691 A K k dom f i neut _88876 h1). Qed.
Lemma lem6789701 {A K : Type'} (f : K -> A) (i : K) (neut : A) (_88876 : type835 A K) (h1 : term608 A K _88876) : term524 A K _88876 f i neut.
Proof. exact (fun dom : A -> Prop => @lem6789696 A K dom f i neut _88876 h1). Qed.
Lemma lem6789706 {A K : Type'} (i : K) (neut : A) (_88876 : type835 A K) (h1 : term608 A K _88876) : term526 A K _88876 i neut.
Proof. exact (fun f : K -> A => @lem6789701 A K f i neut _88876 h1). Qed.
Lemma lem6789711 {A K : Type'} (neut : A) (_88876 : type835 A K) (h1 : term608 A K _88876) : term528 A K _88876 neut.
Proof. exact (fun i : K => @lem6789706 A K i neut _88876 h1). Qed.
Lemma lem6789716 {A K : Type'} (_88876 : type835 A K) (h1 : term608 A K _88876) : term530 A K _88876.
Proof. exact (fun neut : A => @lem6789711 A K neut _88876 h1). Qed.
Lemma lem6789717 {A K : Type'} (_88876 : type835 A K) : term610 A K _88876.
Proof. exact (fun h0 : term608 A K _88876 => @lem6789716 A K _88876 h0). Qed.
Lemma lem6789722 {A K : Type'} : term612 A K.
Proof. exact (fun _88876 : type835 A K => @lem6789717 A K _88876). Qed.
Lemma lem6789723 {A K : Type'} : term496 A K.
Proof. exact (EQ_MP (@lem6782431 A K) (@lem6789722 A K)). Qed.
Lemma lem6789724 {A K : Type'} (neut : A) : term1412 A K neut.
Proof. exact (@lem6789723 A K neut). Qed.
Lemma lem6789725 {A K : Type'} (neut : A) : (term1412 A K neut) = (term492 A K neut).
Proof. exact (eq_refl (term1412 A K neut)). Qed.
Lemma lem6789726 {A K : Type'} (neut : A) : term492 A K neut.
Proof. exact (EQ_MP (@lem6789725 A K neut) (@lem6789724 A K neut)). Qed.
Lemma lem6789727 {A K : Type'} (neut : A) (i : K) : term1413 A K neut i.
Proof. exact (@lem6789726 A K neut i). Qed.
Lemma lem6789728 {A K : Type'} (i : K) (neut : A) : (term1413 A K neut i) = (term488 A K i neut).
Proof. exact (eq_refl (term1413 A K neut i)). Qed.
Lemma lem6789729 {A K : Type'} (i : K) (neut : A) : term488 A K i neut.
Proof. exact (EQ_MP (@lem6789728 A K i neut) (@lem6789727 A K neut i)). Qed.
Lemma lem6789730 {A K : Type'} (i : K) (neut : A) (f : K -> A) : term1414 A K i neut f.
Proof. exact (@lem6789729 A K i neut f). Qed.
Lemma lem6789731 {A K : Type'} (f : K -> A) (i : K) (neut : A) : (term1414 A K i neut f) = (term484 A K f i neut).
Proof. exact (eq_refl (term1414 A K i neut f)). Qed.
Lemma lem6789732 {A K : Type'} (f : K -> A) (i : K) (neut : A) : term484 A K f i neut.
Proof. exact (EQ_MP (@lem6789731 A K f i neut) (@lem6789730 A K i neut f)). Qed.
Lemma lem6789733 {A K : Type'} (f : K -> A) (i : K) (neut : A) (dom : A -> Prop) : term1415 A K f i neut dom.
Proof. exact (@lem6789732 A K f i neut dom). Qed.
Lemma lem6789734 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term1415 A K f i neut dom) = (term480 A K dom f i neut).
Proof. exact (eq_refl (term1415 A K f i neut dom)). Qed.
Lemma lem6789735 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : term480 A K dom f i neut.
Proof. exact (EQ_MP (@lem6789734 A K dom f i neut) (@lem6789733 A K f i neut dom)). Qed.
Lemma lem6789736 {A K : Type'} (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (k : K -> Prop) : term1416 A K dom f i neut k.
Proof. exact (@lem6789735 A K dom f i neut k). Qed.
Lemma lem6789737 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term1416 A K dom f i neut k) = (term476 A K k dom f i neut).
Proof. exact (eq_refl (term1416 A K dom f i neut k)). Qed.
Lemma lem6789738 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : term476 A K k dom f i neut.
Proof. exact (EQ_MP (@lem6789737 A K k dom f i neut) (@lem6789736 A K dom f i neut k)). Qed.
Lemma lem6789739 {A K : Type'} (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (ltle : type1402 K) : term1417 A K k dom f i neut ltle.
Proof. exact (@lem6789738 A K k dom f i neut ltle). Qed.
Lemma lem6789740 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : (term1417 A K k dom f i neut ltle) = (term457 A K ltle k dom f i neut).
Proof. exact (eq_refl (term1417 A K k dom f i neut ltle)). Qed.
Lemma lem6789741 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : term457 A K ltle k dom f i neut.
Proof. exact (EQ_MP (@lem6789740 A K ltle k dom f i neut) (@lem6789739 A K k dom f i neut ltle)). Qed.
Lemma lem6789743 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : term375 A K ltle k dom f i neut.
Proof. exact (@lem6781427 A K ltle k dom f i neut (@lem6789741 A K ltle k dom f i neut)). Qed.
Lemma lem6789744 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (h1 : term376 A K ltle k dom f i neut) : False.
Proof. exact (@lem6789743 A K ltle k dom f i neut (@lem6781248 A K ltle k dom f i neut h1)). Qed.
Lemma lem6789745 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (h1 : term376 A K ltle k dom f i neut) : (term376 A K ltle k dom f i neut) = False.
Proof. exact (prop_ext (fun h2 : term376 A K ltle k dom f i neut => @lem6789744 A K ltle k dom f i neut h1) (fun h2 : False => @lem6781248 A K ltle k dom f i neut h1)). Qed.
Lemma lem6789746 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) (h1 : term376 A K ltle k dom f i neut) : False.
Proof. exact (EQ_MP (@lem6789745 A K ltle k dom f i neut h1) (@lem6781248 A K ltle k dom f i neut h1)). Qed.
Lemma lem6789747 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : term375 A K ltle k dom f i neut.
Proof. exact (fun h0 : term376 A K ltle k dom f i neut => @lem6789746 A K ltle k dom f i neut h0). Qed.
Lemma lem6789748 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (i : K) (neut : A) : term374 A K ltle k dom f i neut.
Proof. exact (EQ_MP (@lem6781247 A K ltle k dom f i neut) (@lem6789747 A K ltle k dom f i neut)). Qed.
Lemma lem6789749 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : term292 A K ltle k f i dom neut.
Proof. exact (EQ_MP (@lem6781243 A K ltle k f i dom neut) (@lem6789748 A K ltle k dom f i neut)). Qed.
Lemma lem6789750 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : term291 A K ltle k f i dom neut.
Proof. exact (EQ_MP (@lem6780778 A K ltle k f i dom neut) (@lem6789749 A K ltle k f i dom neut)). Qed.
Lemma lem6789752 {K : Type'} (P : K -> Prop) : term1418 K P.
Proof. exact (@lem9396 K P). Qed.
Lemma lem6789753 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : term1419 A K ltle k f dom neut.
Proof. exact (@lem6789752 K (term327 A K ltle k f dom neut)). Qed.
Lemma lem6789754 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term254 A K ltle k f dom neut) : term1420 A K ltle k f dom neut.
Proof. exact (@lem6789753 A K ltle k f dom neut (@lem6780647 A K ltle k f dom neut h1)). Qed.
Lemma lem6789755 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term1420 A K ltle k f dom neut) = (term1421 A K ltle k f dom neut).
Proof. exact (eq_refl (term1420 A K ltle k f dom neut)). Qed.
Lemma lem6789756 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term254 A K ltle k f dom neut) : term1421 A K ltle k f dom neut.
Proof. exact (EQ_MP (@lem6789755 A K ltle k f dom neut) (@lem6789754 A K ltle k f dom neut h1)). Qed.
Lemma lem6789777 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : (term253 A K ltle k f dom neut) = i) : (term253 A K ltle k f dom neut) = i.
Proof. exact (h1). Qed.
Lemma lem6789778 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : (term253 A K ltle k f dom neut) = i) : (term253 A K ltle k f dom neut) = i.
Proof. exact (@lem6789777 A K ltle k f dom neut i h1). Qed.
Lemma lem6789779 {K : Type'} : (@IN K) = (@IN K).
Proof. exact (eq_refl (@IN K)). Qed.
Lemma lem6789780 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : (term253 A K ltle k f dom neut) = i) : (term1422 A K ltle k f dom neut) = (@IN K i).
Proof. exact (MK_COMB (@lem6789779 K) (@lem6789778 A K ltle k f dom neut i h1)). Qed.
Lemma lem6789781 {K : Type'} (k : K -> Prop) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem6789782 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : (term253 A K ltle k f dom neut) = i) : (term1423 A K ltle f dom neut k) = (@IN K i k).
Proof. exact (MK_COMB (@lem6789780 A K ltle k f dom neut i h1) (@lem6789781 K k)). Qed.
Lemma lem6789783 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6789784 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : (term253 A K ltle k f dom neut) = i) : (term1424 A K ltle f dom neut k) = (term169 K i k).
Proof. exact (MK_COMB (@lem6789783) (@lem6789782 A K ltle k f dom neut i h1)). Qed.
Lemma lem6789788 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : (term253 A K ltle k f dom neut) = i) : (term253 A K ltle k f dom neut) = i.
Proof. exact (h1). Qed.
Lemma lem6789789 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : (term253 A K ltle k f dom neut) = i) : (term253 A K ltle k f dom neut) = i.
Proof. exact (@lem6789788 A K ltle k f dom neut i h1). Qed.
Lemma lem6789790 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6789791 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : (term253 A K ltle k f dom neut) = i) : (term1425 A K ltle k f dom neut) = (f i).
Proof. exact (MK_COMB (@lem6789790 A K f) (@lem6789789 A K ltle k f dom neut i h1)). Qed.
Lemma lem6789792 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem6789793 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : (term253 A K ltle k f dom neut) = i) : (term1426 A K ltle k f dom neut) = (term1427 A K f i).
Proof. exact (MK_COMB (@lem6789792 A) (@lem6789791 A K ltle k f dom neut i h1)). Qed.
Lemma lem6789794 {A : Type'} (dom : A -> Prop) (neut : A) : (term1428 A dom neut) = (term1428 A dom neut).
Proof. exact (eq_refl (term1428 A dom neut)). Qed.
Lemma lem6789795 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : (term253 A K ltle k f dom neut) = i) : (term1429 A K ltle k f dom neut) = (term105 A K f i dom neut).
Proof. exact (MK_COMB (@lem6789793 A K ltle k f dom neut i h1) (@lem6789794 A dom neut)). Qed.
Lemma lem6789796 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6789797 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : (term253 A K ltle k f dom neut) = i) : (term1430 A K ltle k f dom neut) = (term137 A K f i dom neut).
Proof. exact (MK_COMB (@lem6789796) (@lem6789795 A K ltle k f dom neut i h1)). Qed.
Lemma lem6789807 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : (term253 A K ltle k f dom neut) = i) : (term253 A K ltle k f dom neut) = i.
Proof. exact (h1). Qed.
Lemma lem6789808 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : (term253 A K ltle k f dom neut) = i) : (term253 A K ltle k f dom neut) = i.
Proof. exact (@lem6789807 A K ltle k f dom neut i h1). Qed.
Lemma lem6789809 {K : Type'} (ltle : type1402 K) (i' : K) : (ltle i') = (ltle i').
Proof. exact (eq_refl (ltle i')). Qed.
Lemma lem6789810 {A K : Type'} (i' : K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : (term253 A K ltle k f dom neut) = i) : (term1431 A K i' ltle k f dom neut) = (ltle i' i).
Proof. exact (MK_COMB (@lem6789809 K ltle i') (@lem6789808 A K ltle k f dom neut i h1)). Qed.
Lemma lem6789811 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6789812 {A K : Type'} (i' : K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : (term253 A K ltle k f dom neut) = i) : (term1432 A K i' ltle k f dom neut) = (term126 K ltle i' i).
Proof. exact (MK_COMB (@lem6789811) (@lem6789810 A K i' ltle k f dom neut i h1)). Qed.
Lemma lem6789815 {A K : Type'} (k : K -> Prop) (f : K -> A) (i' : K) (dom : A -> Prop) (neut : A) : (term244 A K k f i' dom neut) = (term244 A K k f i' dom neut).
Proof. exact (eq_refl (term244 A K k f i' dom neut)). Qed.
Lemma lem6789816 {A K : Type'} (i' : K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : (term253 A K ltle k f dom neut) = i) : (term1433 A K ltle k f i' dom neut) = (term313 A K ltle i k f i' dom neut).
Proof. exact (MK_COMB (@lem6789812 A K i' ltle k f dom neut i h1) (@lem6789815 A K k f i' dom neut)). Qed.
Lemma lem6789819 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6789820 {A K : Type'} (i' : K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : (term253 A K ltle k f dom neut) = i) : (term1434 A K ltle k f i' dom neut) = (term315 A K ltle i k f i' dom neut).
Proof. exact (MK_COMB (@lem6789819) (@lem6789816 A K i' ltle k f dom neut i h1)). Qed.
Lemma lem6789824 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : (term253 A K ltle k f dom neut) = i) : (term253 A K ltle k f dom neut) = i.
Proof. exact (h1). Qed.
Lemma lem6789825 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : (term253 A K ltle k f dom neut) = i) : (term253 A K ltle k f dom neut) = i.
Proof. exact (@lem6789824 A K ltle k f dom neut i h1). Qed.
Lemma lem6789826 {K : Type'} (i' : K) : (@eq K i') = (@eq K i').
Proof. exact (eq_refl (@eq K i')). Qed.
Lemma lem6789827 {A K : Type'} (i' : K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : (term253 A K ltle k f dom neut) = i) : (i' = (term253 A K ltle k f dom neut)) = (i' = i).
Proof. exact (MK_COMB (@lem6789826 K i') (@lem6789825 A K ltle k f dom neut i h1)). Qed.
Lemma lem6789830 {A K : Type'} (i' : K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : (term253 A K ltle k f dom neut) = i) : (term1435 A K i' ltle k f dom neut) = (term317 A K ltle k f dom neut i' i).
Proof. exact (MK_COMB (@lem6789820 A K i' ltle k f dom neut i h1) (@lem6789827 A K i' ltle k f dom neut i h1)). Qed.
Lemma lem6789833 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : (term253 A K ltle k f dom neut) = i) : (term1436 A K ltle k f dom neut) = (term319 A K ltle k f dom neut i).
Proof. exact (fun_ext (fun i' : K => @lem6789830 A K i' ltle k f dom neut i h1)). Qed.
Lemma lem6789834 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6789835 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : (term253 A K ltle k f dom neut) = i) : (term1437 A K ltle k f dom neut) = (term321 A K ltle k f dom neut i).
Proof. exact (MK_COMB (@lem6789834 K) (@lem6789833 A K ltle k f dom neut i h1)). Qed.
Lemma lem6789840 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : (term253 A K ltle k f dom neut) = i) : (term1438 A K ltle k f dom neut) = (term323 A K ltle k f dom neut i).
Proof. exact (MK_COMB (@lem6789797 A K ltle k f dom neut i h1) (@lem6789835 A K ltle k f dom neut i h1)). Qed.
Lemma lem6789843 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : (term253 A K ltle k f dom neut) = i) : (term1421 A K ltle k f dom neut) = (term325 A K ltle k f dom neut i).
Proof. exact (MK_COMB (@lem6789784 A K ltle k f dom neut i h1) (@lem6789840 A K ltle k f dom neut i h1)). Qed.
Lemma lem6789846 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6789847 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : (term253 A K ltle k f dom neut) = i) : (term1439 A K ltle k f dom neut) = (term1440 A K ltle k f dom neut i).
Proof. exact (MK_COMB (@lem6789846) (@lem6789843 A K ltle k f dom neut i h1)). Qed.
Lemma lem6789850 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term244 A K k f i dom neut) = (term244 A K k f i dom neut).
Proof. exact (eq_refl (term244 A K k f i dom neut)). Qed.
Lemma lem6789851 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : (term253 A K ltle k f dom neut) = i) : (term1441 A K ltle k f i dom neut) = (term1442 A K ltle k f i dom neut).
Proof. exact (MK_COMB (@lem6789847 A K ltle k f dom neut i h1) (@lem6789850 A K k f i dom neut)). Qed.
Lemma lem6789854 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : (term253 A K ltle k f dom neut) = i) : (term1442 A K ltle k f i dom neut) = (term1441 A K ltle k f i dom neut).
Proof. exact (SYM (@lem6789851 A K ltle k f dom neut i h1)). Qed.
Lemma lem6789858 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term1443 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6789859 (p : Prop) (q : Prop) (p' : Prop) : term1444 p q p'.
Proof. exact (fun q' : Prop => @lem6789858 p q p' q'). Qed.
Lemma lem6789860 (p : Prop) (q : Prop) : term1445 p q.
Proof. exact (fun p' : Prop => @lem6789859 p q p'). Qed.
Lemma lem6789861 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : term1446 A K ltle k f i dom neut.
Proof. exact (@lem6789860 (term325 A K ltle k f dom neut i) (term244 A K k f i dom neut)). Qed.
Lemma lem6789862 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) (p' : Prop) : term1447 A K ltle k f i dom neut p'.
Proof. exact (@lem6789861 A K ltle k f i dom neut p'). Qed.
Lemma lem6789863 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) (p' : Prop) : (term1447 A K ltle k f i dom neut p') = (term1448 A K ltle k f i dom neut p').
Proof. exact (eq_refl (term1447 A K ltle k f i dom neut p')). Qed.
Lemma lem6789864 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) (p' : Prop) : term1448 A K ltle k f i dom neut p'.
Proof. exact (EQ_MP (@lem6789863 A K ltle k f i dom neut p') (@lem6789862 A K ltle k f i dom neut p')). Qed.
Lemma lem6789865 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) (p' : Prop) (q' : Prop) : term1449 A K ltle k f i dom neut p' q'.
Proof. exact (@lem6789864 A K ltle k f i dom neut p' q'). Qed.
Lemma lem6789866 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) (p' : Prop) (q' : Prop) : (term1449 A K ltle k f i dom neut p' q') = (term1450 A K ltle k f i dom neut p' q').
Proof. exact (eq_refl (term1449 A K ltle k f i dom neut p' q')). Qed.
Lemma lem6789867 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) (p' : Prop) (q' : Prop) : term1450 A K ltle k f i dom neut p' q'.
Proof. exact (EQ_MP (@lem6789866 A K ltle k f i dom neut p' q') (@lem6789865 A K ltle k f i dom neut p' q')). Qed.
Lemma lem6789919 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term325 A K ltle k f dom neut i) = (term325 A K ltle k f dom neut i).
Proof. exact (eq_refl (term325 A K ltle k f dom neut i)). Qed.
Lemma lem6789920 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (q' : Prop) : term1451 A K ltle k f dom neut i q'.
Proof. exact (@lem6789867 A K ltle k f i dom neut (term325 A K ltle k f dom neut i) q'). Qed.
Lemma lem6789921 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (q' : Prop) : term1452 A K ltle k f dom neut i q'.
Proof. exact (@lem6789920 A K ltle k f dom neut i q' (@lem6789919 A K ltle k f dom neut i)). Qed.
Lemma lem6789922 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : term325 A K ltle k f dom neut i) : term325 A K ltle k f dom neut i.
Proof. exact (h1). Qed.
Lemma lem6789923 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : term325 A K ltle k f dom neut i) : term323 A K ltle k f dom neut i.
Proof. exact (proj2 (@lem6789922 A K ltle k f dom neut i h1)). Qed.
Lemma lem6789935 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : term325 A K ltle k f dom neut i) : term105 A K f i dom neut.
Proof. exact (proj1 (@lem6789923 A K ltle k f dom neut i h1)). Qed.
Lemma lem6789936 {A K : Type'} (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term105 A K f i dom neut) = ((term105 A K f i dom neut) = True).
Proof. exact (@lem7 (term105 A K f i dom neut)). Qed.
Lemma lem6789938 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : term325 A K ltle k f dom neut i) : @IN K i k.
Proof. exact (proj1 (@lem6789922 A K ltle k f dom neut i h1)). Qed.
Lemma lem6789939 {K : Type'} (i : K) (k : K -> Prop) : (@IN K i k) = ((@IN K i k) = True).
Proof. exact (@lem7 (@IN K i k)). Qed.
Lemma lem6789956 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : term325 A K ltle k f dom neut i) : (@IN K i k) = True.
Proof. exact (EQ_MP (@lem6789939 K i k) (@lem6789938 A K ltle k f dom neut i h1)). Qed.
Lemma lem6789961 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6789962 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : term325 A K ltle k f dom neut i) : (term169 K i k) = (and True).
Proof. exact (MK_COMB (@lem6789961) (@lem6789956 A K ltle k f dom neut i h1)). Qed.
Lemma lem6789976 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : term325 A K ltle k f dom neut i) : (term105 A K f i dom neut) = True.
Proof. exact (EQ_MP (@lem6789936 A K f i dom neut) (@lem6789935 A K ltle k f dom neut i h1)). Qed.
Lemma lem6789981 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : term325 A K ltle k f dom neut i) : (term244 A K k f i dom neut) = (True /\ True).
Proof. exact (MK_COMB (@lem6789962 A K ltle k f dom neut i h1) (@lem6789976 A K ltle k f dom neut i h1)). Qed.
Lemma lem6789983 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6789984 : (True /\ True) = True.
Proof. exact (@lem6789983 True). Qed.
Lemma lem6789989 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : term325 A K ltle k f dom neut i) : (term244 A K k f i dom neut) = True.
Proof. exact (TRANS (@lem6789981 A K ltle k f dom neut i h1) (@lem6789984)). Qed.
Lemma lem6789990 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : term1453 A K ltle k f i dom neut.
Proof. exact (fun h0 : term325 A K ltle k f dom neut i => @lem6789989 A K ltle k f dom neut i h0). Qed.
Lemma lem6789991 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : term1454 A K ltle k f dom neut i.
Proof. exact (@lem6789921 A K ltle k f dom neut i True). Qed.
Lemma lem6789992 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term1442 A K ltle k f i dom neut) = (term1455 A K ltle k f dom neut i).
Proof. exact (@lem6789991 A K ltle k f dom neut i (@lem6789990 A K ltle k f i dom neut)). Qed.
Lemma lem6789994 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem6789995 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term1455 A K ltle k f dom neut i) = True.
Proof. exact (@lem6789994 (term325 A K ltle k f dom neut i)). Qed.
Lemma lem6789996 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : (term1442 A K ltle k f i dom neut) = True.
Proof. exact (TRANS (@lem6789992 A K ltle k f dom neut i) (@lem6789995 A K ltle k f dom neut i)). Qed.
Lemma lem6789997 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : True = (term1442 A K ltle k f i dom neut).
Proof. exact (SYM (@lem6789996 A K ltle k f i dom neut)). Qed.
Lemma lem6789998 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : term1442 A K ltle k f i dom neut.
Proof. exact (EQ_MP (@lem6789997 A K ltle k f i dom neut) (@lem0)). Qed.
Lemma lem6789999 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : (term253 A K ltle k f dom neut) = i) : term1441 A K ltle k f i dom neut.
Proof. exact (EQ_MP (@lem6789854 A K ltle k f dom neut i h1) (@lem6789998 A K ltle k f i dom neut)). Qed.
Lemma lem6790000 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : term254 A K ltle k f dom neut) (h2 : (term253 A K ltle k f dom neut) = i) : term244 A K k f i dom neut.
Proof. exact (@lem6789999 A K ltle k f dom neut i h2 (@lem6789756 A K ltle k f dom neut h1)). Qed.
Lemma lem6790002 {A K : Type'} (i : K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term163 A K k f dom neut) (h2 : term271 A K ltle k f dom neut) (h3 : term162 A K k f dom neut) : term257 A K k f i dom neut.
Proof. exact (@lem6789750 A K ltle k f i dom neut (@lem6780693 A K ltle k f dom neut h1 h2 h3)). Qed.
Lemma lem6790003 {A K : Type'} (i : K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term163 A K k f dom neut) (h2 : term271 A K ltle k f dom neut) (h3 : term162 A K k f dom neut) : (term271 A K ltle k f dom neut) = (term257 A K k f i dom neut).
Proof. exact (prop_ext (fun h4 : term271 A K ltle k f dom neut => @lem6790002 A K i ltle k f dom neut h1 h2 h3) (fun h4 : term257 A K k f i dom neut => @lem6780664 A K ltle k f dom neut h2)). Qed.
Lemma lem6790004 {A K : Type'} (i : K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term163 A K k f dom neut) (h2 : term271 A K ltle k f dom neut) (h3 : term162 A K k f dom neut) : term257 A K k f i dom neut.
Proof. exact (EQ_MP (@lem6790003 A K i ltle k f dom neut h1 h2 h3) (@lem6780664 A K ltle k f dom neut h2)). Qed.
Lemma lem6790005 {A K : Type'} (ltle : type1402 K) (i : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term163 A K k f dom neut) (h2 : term162 A K k f dom neut) : term260 A K ltle k f i dom neut.
Proof. exact (fun h0 : term271 A K ltle k f dom neut => @lem6790004 A K i ltle k f dom neut h1 h0 h2). Qed.
Lemma lem6790006 {A K : Type'} (i : K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term254 A K ltle k f dom neut) : term262 A K ltle k f i dom neut.
Proof. exact (fun h0 : (term253 A K ltle k f dom neut) = i => @lem6790000 A K ltle k f dom neut i h1 h0). Qed.
Lemma lem6790007 {A K : Type'} (i : K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term254 A K ltle k f dom neut) : (term254 A K ltle k f dom neut) = (term262 A K ltle k f i dom neut).
Proof. exact (prop_ext (fun h2 : term254 A K ltle k f dom neut => @lem6790006 A K i ltle k f dom neut h1) (fun h2 : term262 A K ltle k f i dom neut => @lem6780647 A K ltle k f dom neut h1)). Qed.
Lemma lem6790008 {A K : Type'} (i : K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term254 A K ltle k f dom neut) : term262 A K ltle k f i dom neut.
Proof. exact (EQ_MP (@lem6790007 A K i ltle k f dom neut h1) (@lem6780647 A K ltle k f dom neut h1)). Qed.
Lemma lem6790009 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (i : K) (dom : A -> Prop) (neut : A) : term265 A K ltle k f i dom neut.
Proof. exact (fun h0 : term254 A K ltle k f dom neut => @lem6790008 A K i ltle k f dom neut h0). Qed.
Lemma lem6790010 {A K : Type'} (ltle : type1402 K) (i : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term163 A K k f dom neut) (h2 : term162 A K k f dom neut) : term268 A K ltle k f i dom neut.
Proof. exact (conj (@lem6790009 A K ltle k f i dom neut) (@lem6790005 A K ltle i k f dom neut h1 h2)). Qed.
Lemma lem6790011 {A K : Type'} (ltle : type1402 K) (i : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term163 A K k f dom neut) (h2 : term162 A K k f dom neut) : term245 A K ltle k f i dom neut.
Proof. exact (EQ_MP (@lem6780646 A K ltle k f i dom neut) (@lem6790010 A K ltle i k f dom neut h1 h2)). Qed.
Lemma lem6790012 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (i : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term163 A K k f dom neut) (h2 : term162 A K k f dom neut) : term233 A K op ltle k i dom neut f.
Proof. exact (EQ_MP (@lem6780628 A K op ltle k i dom neut f) (@lem6790011 A K ltle i k f dom neut h1 h2)). Qed.
Lemma lem6790013 {A K : Type'} (op : type1400 A) (i : K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term163 A K k f dom neut) (h2 : term162 A K k f dom neut) (h3 : i = (term189 A K ltle k f dom neut)) : term222 A K i op ltle k dom neut f.
Proof. exact (@lem6780545 A K op i ltle k f dom neut h3 (@lem6790012 A K op ltle i k f dom neut h1 h2)). Qed.
Lemma lem6790014 {A K : Type'} (op : type1400 A) (i : K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term163 A K k f dom neut) (h2 : term162 A K k f dom neut) (h3 : i = (term189 A K ltle k f dom neut)) : term215 A K i dom neut op ltle k f.
Proof. exact (EQ_MP (@lem6780516 A K i dom neut op ltle k f) (@lem6790013 A K op i ltle k f dom neut h1 h2 h3)). Qed.
Lemma lem6790015 {A K : Type'} (op : type1400 A) (i : K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term163 A K k f dom neut) (h2 : term162 A K k f dom neut) (h3 : i = (term189 A K ltle k f dom neut)) : term199 A K i dom neut op ltle k f.
Proof. exact (EQ_MP (@lem6780500 A K i dom neut op ltle k f) (@lem6790014 A K op i ltle k f dom neut h1 h2 h3)). Qed.
Lemma lem6790016 {A K : Type'} (op : type1400 A) (i : K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term163 A K k f dom neut) (h2 : term162 A K k f dom neut) (h3 : i = (term189 A K ltle k f dom neut)) : (term162 A K k f dom neut) = (term199 A K i dom neut op ltle k f).
Proof. exact (prop_ext (fun h4 : term162 A K k f dom neut => @lem6790015 A K op i ltle k f dom neut h1 h2 h3) (fun h4 : term199 A K i dom neut op ltle k f => @lem6780477 A K k f dom neut h2)). Qed.
Lemma lem6790017 {A K : Type'} (op : type1400 A) (i : K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term163 A K k f dom neut) (h2 : term162 A K k f dom neut) (h3 : i = (term189 A K ltle k f dom neut)) : term199 A K i dom neut op ltle k f.
Proof. exact (EQ_MP (@lem6790016 A K op i ltle k f dom neut h1 h2 h3) (@lem6780477 A K k f dom neut h2)). Qed.
Lemma lem6790018 {A K : Type'} (op : type1400 A) (i : K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term163 A K k f dom neut) (h2 : term162 A K k f dom neut) (h3 : i = (term189 A K ltle k f dom neut)) : (term163 A K k f dom neut) = (term199 A K i dom neut op ltle k f).
Proof. exact (prop_ext (fun h4 : term163 A K k f dom neut => @lem6790017 A K op i ltle k f dom neut h1 h2 h3) (fun h4 : term199 A K i dom neut op ltle k f => @lem6780463 A K k f dom neut h1)). Qed.
Lemma lem6790019 {A K : Type'} (op : type1400 A) (i : K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term163 A K k f dom neut) (h2 : term162 A K k f dom neut) (h3 : i = (term189 A K ltle k f dom neut)) : term199 A K i dom neut op ltle k f.
Proof. exact (EQ_MP (@lem6790018 A K op i ltle k f dom neut h1 h2 h3) (@lem6780463 A K k f dom neut h1)). Qed.
Lemma lem6790020 {A K : Type'} (op : type1400 A) (i : K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term163 A K k f dom neut) (h2 : term162 A K k f dom neut) (h3 : i = (term189 A K ltle k f dom neut)) : term188 A K dom neut op ltle k f.
Proof. exact (EQ_MP (@lem6780449 A K op i ltle k f dom neut h3) (@lem6790019 A K op i ltle k f dom neut h1 h2 h3)). Qed.
Lemma lem6790021 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term163 A K k f dom neut) (h2 : term162 A K k f dom neut) : term188 A K dom neut op ltle k f.
Proof. exact (ex_elim (@lem6780434 A K ltle k f dom neut) (fun i : K => fun h0 : term191 A K ltle k f dom neut i => @lem6790020 A K op i ltle k f dom neut h1 h2 h0)). Qed.
Lemma lem6790022 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term163 A K k f dom neut) (h2 : term162 A K k f dom neut) : term175 A K dom neut op ltle k f.
Proof. exact (EQ_MP (@lem6780409 A K op ltle k f dom neut h1 h2) (@lem6790021 A K op ltle k f dom neut h1 h2)). Qed.
Lemma lem6790023 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term163 A K k f dom neut) (h2 : term162 A K k f dom neut) : term174 A K dom neut op ltle k f.
Proof. exact (EQ_MP (@lem6780243 A K dom neut op ltle k f) (@lem6790022 A K op ltle k f dom neut h1 h2)). Qed.
Lemma lem6790024 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term161 A K k f dom neut) : term162 A K k f dom neut.
Proof. exact (proj2 (@lem6780226 A K k f dom neut h1)). Qed.
Lemma lem6790025 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term161 A K k f dom neut) : term163 A K k f dom neut.
Proof. exact (proj1 (@lem6780226 A K k f dom neut h1)). Qed.
Lemma lem6790026 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term163 A K k f dom neut) (h2 : term162 A K k f dom neut) : (term162 A K k f dom neut) = (term174 A K dom neut op ltle k f).
Proof. exact (prop_ext (fun h3 : term162 A K k f dom neut => @lem6790023 A K op ltle k f dom neut h1 h2) (fun h3 : term174 A K dom neut op ltle k f => @lem6780227 A K k f dom neut h2)). Qed.
Lemma lem6790027 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term163 A K k f dom neut) (h2 : term162 A K k f dom neut) : term174 A K dom neut op ltle k f.
Proof. exact (EQ_MP (@lem6790026 A K op ltle k f dom neut h1 h2) (@lem6780227 A K k f dom neut h2)). Qed.
Lemma lem6790028 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term163 A K k f dom neut) (h2 : term162 A K k f dom neut) : (term163 A K k f dom neut) = (term174 A K dom neut op ltle k f).
Proof. exact (prop_ext (fun h3 : term163 A K k f dom neut => @lem6790027 A K op ltle k f dom neut h1 h2) (fun h3 : term174 A K dom neut op ltle k f => @lem6780228 A K k f dom neut h1)). Qed.
Lemma lem6790029 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term163 A K k f dom neut) (h2 : term162 A K k f dom neut) : term174 A K dom neut op ltle k f.
Proof. exact (EQ_MP (@lem6790028 A K op ltle k f dom neut h1 h2) (@lem6780228 A K k f dom neut h1)). Qed.
Lemma lem6790030 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term163 A K k f dom neut) (h2 : term161 A K k f dom neut) : (term162 A K k f dom neut) = (term174 A K dom neut op ltle k f).
Proof. exact (prop_ext (fun h3 : term162 A K k f dom neut => @lem6790029 A K op ltle k f dom neut h1 h3) (fun h3 : term174 A K dom neut op ltle k f => @lem6790024 A K k f dom neut h2)). Qed.
Lemma lem6790031 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term163 A K k f dom neut) (h2 : term161 A K k f dom neut) : term174 A K dom neut op ltle k f.
Proof. exact (EQ_MP (@lem6790030 A K op ltle k f dom neut h1 h2) (@lem6790024 A K k f dom neut h2)). Qed.
Lemma lem6790032 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term161 A K k f dom neut) : (term163 A K k f dom neut) = (term174 A K dom neut op ltle k f).
Proof. exact (prop_ext (fun h2 : term163 A K k f dom neut => @lem6790031 A K op ltle k f dom neut h2 h1) (fun h2 : term174 A K dom neut op ltle k f => @lem6790025 A K k f dom neut h1)). Qed.
Lemma lem6790033 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term161 A K k f dom neut) : term174 A K dom neut op ltle k f.
Proof. exact (EQ_MP (@lem6790032 A K op ltle k f dom neut h1) (@lem6790025 A K k f dom neut h1)). Qed.
Lemma lem6790034 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) : term1456 A K dom neut op ltle k f.
Proof. exact (fun h0 : term161 A K k f dom neut => @lem6790033 A K op ltle k f dom neut h0). Qed.
Lemma lem6790039 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (f : K -> A) : term1457 A K dom neut op ltle f.
Proof. exact (fun k : K -> Prop => @lem6790034 A K dom neut op ltle k f). Qed.
Lemma lem6790040 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (f : K -> A) : term1458 A K dom neut op ltle f.
Proof. exact (conj (@lem6780225 A K dom op ltle f neut) (@lem6790039 A K dom neut op ltle f)). Qed.
Lemma lem6790045 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) : term1459 A K dom neut op ltle.
Proof. exact (fun f : K -> A => @lem6790040 A K dom neut op ltle f). Qed.
Lemma lem6790050 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) : term1460 A K dom neut op.
Proof. exact (fun ltle : type1402 K => @lem6790045 A K dom neut op ltle). Qed.
Lemma lem6790055 {A K : Type'} (dom : A -> Prop) (neut : A) : term1461 A K dom neut.
Proof. exact (fun op : type1400 A => @lem6790050 A K dom neut op). Qed.
Lemma lem6790060 {A K : Type'} (dom : A -> Prop) : term1462 A K dom.
Proof. exact (fun neut : A => @lem6790055 A K dom neut). Qed.
Lemma lem6790065 {A K : Type'} : term1463 A K.
Proof. exact (fun dom : A -> Prop => @lem6790060 A K dom). Qed.
