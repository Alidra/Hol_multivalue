Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import PCROSS_EQ_EMPTY_term_abbrevs.
Require Import DISJ_ASSOC_spec.
Require Import PCROSS_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1857_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211647_spec.
Require Import thm3211648_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem8004230 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem8004231 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem8004232 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem8004231 t1) (@lem8004230 t1)). Qed.
Lemma lem8004233 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem8004232 t1 t2). Qed.
Lemma lem8004234 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem8004235 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem8004234 t1 t2) (@lem8004233 t1 t2)). Qed.
Lemma lem8004236 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem8004235 t1 t2 t3). Qed.
Lemma lem8004237 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem8004238 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem8004237 t1 t2 t3) (@lem8004236 t1 t2 t3)). Qed.
Lemma lem8004239 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem8004238 t1 t2 t3)). Qed.
Lemma lem8004240 {A M N : Type'} (s : type24 A M) : term7 A M N s.
Proof. exact (@lem8003767 A M N s). Qed.
Lemma lem8004241 {A M N : Type'} (s : type24 A M) : (term7 A M N s) = (term8 A M N s).
Proof. exact (eq_refl (term7 A M N s)). Qed.
Lemma lem8004242 {A M N : Type'} (s : type24 A M) : term8 A M N s.
Proof. exact (EQ_MP (@lem8004241 A M N s) (@lem8004240 A M N s)). Qed.
Lemma lem8004243 {A M N : Type'} (s : type24 A M) (t : type24 A N) : term9 A M N s t.
Proof. exact (@lem8004242 A M N s t). Qed.
Lemma lem8004244 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term9 A M N s t) = ((@PCROSS A M N s t) = (term10 A M N s t)).
Proof. exact (eq_refl (term9 A M N s t)). Qed.
Lemma lem8004259 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (@PCROSS A M N s t) = (term10 A M N s t).
Proof. exact (EQ_MP (@lem8004244 A M N s t) (@lem8004243 A M N s t)). Qed.
Lemma lem8004260 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (@PCROSS _141954 _141955 _141956 s t) = (term10 _141954 _141955 _141956 s t).
Proof. exact (@lem8004259 _141954 _141955 _141956 s t). Qed.
Lemma lem8004271 {_141954 _141955 _141956 : Type'} : (@eq ((cart _141954 (finite_sum _141955 _141956)) -> Prop)) = (@eq ((cart _141954 (finite_sum _141955 _141956)) -> Prop)).
Proof. exact (eq_refl (@eq ((cart _141954 (finite_sum _141955 _141956)) -> Prop))). Qed.
Lemma lem8004272 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term11 _141954 _141955 _141956 s t) = (term12 _141954 _141955 _141956 s t).
Proof. exact (MK_COMB (@lem8004271 _141954 _141955 _141956) (@lem8004260 _141954 _141955 _141956 s t)). Qed.
Lemma lem8004273 {_141954 _141955 _141956 : Type'} : (@EMPTY (cart _141954 (finite_sum _141955 _141956))) = (@EMPTY (cart _141954 (finite_sum _141955 _141956))).
Proof. exact (eq_refl (@EMPTY (cart _141954 (finite_sum _141955 _141956)))). Qed.
Lemma lem8004274 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : ((@PCROSS _141954 _141955 _141956 s t) = (@EMPTY (cart _141954 (finite_sum _141955 _141956)))) = ((term10 _141954 _141955 _141956 s t) = (@EMPTY (cart _141954 (finite_sum _141955 _141956)))).
Proof. exact (MK_COMB (@lem8004272 _141954 _141955 _141956 s t) (@lem8004273 _141954 _141955 _141956)). Qed.
Lemma lem8004277 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8004278 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term13 _141954 _141955 _141956 s t) = (term14 _141954 _141955 _141956 s t).
Proof. exact (MK_COMB (@lem8004277) (@lem8004274 _141954 _141955 _141956 s t)). Qed.
Lemma lem8004285 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term15 _141954 _141955 _141956 s t) = (term15 _141954 _141955 _141956 s t).
Proof. exact (eq_refl (term15 _141954 _141955 _141956 s t)). Qed.
Lemma lem8004286 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (((@PCROSS _141954 _141955 _141956 s t) = (@EMPTY (cart _141954 (finite_sum _141955 _141956)))) = (term15 _141954 _141955 _141956 s t)) = (((term10 _141954 _141955 _141956 s t) = (@EMPTY (cart _141954 (finite_sum _141955 _141956)))) = (term15 _141954 _141955 _141956 s t)).
Proof. exact (MK_COMB (@lem8004278 _141954 _141955 _141956 s t) (@lem8004285 _141954 _141955 _141956 s t)). Qed.
Lemma lem8004289 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) : (term16 _141954 _141955 _141956 s) = (term17 _141954 _141955 _141956 s).
Proof. exact (fun_ext (fun t : type24 _141954 _141956 => @lem8004286 _141954 _141955 _141956 s t)). Qed.
Lemma lem8004290 {_141954 _141956 : Type'} : (@all ((cart _141954 _141956) -> Prop)) = (@all ((cart _141954 _141956) -> Prop)).
Proof. exact (eq_refl (@all ((cart _141954 _141956) -> Prop))). Qed.
Lemma lem8004291 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) : (term18 _141954 _141955 _141956 s) = (term19 _141954 _141955 _141956 s).
Proof. exact (MK_COMB (@lem8004290 _141954 _141956) (@lem8004289 _141954 _141955 _141956 s)). Qed.
Lemma lem8004296 {_141954 _141955 _141956 : Type'} : (term20 _141954 _141955 _141956) = (term21 _141954 _141955 _141956).
Proof. exact (fun_ext (fun s : type24 _141954 _141955 => @lem8004291 _141954 _141955 _141956 s)). Qed.
Lemma lem8004297 {_141954 _141955 : Type'} : (@all ((cart _141954 _141955) -> Prop)) = (@all ((cart _141954 _141955) -> Prop)).
Proof. exact (eq_refl (@all ((cart _141954 _141955) -> Prop))). Qed.
Lemma lem8004298 {_141954 _141955 _141956 : Type'} : (term22 _141954 _141955 _141956) = (term23 _141954 _141955 _141956).
Proof. exact (MK_COMB (@lem8004297 _141954 _141955) (@lem8004296 _141954 _141955 _141956)). Qed.
Lemma lem8004303 {_141954 _141955 _141956 : Type'} : (term23 _141954 _141955 _141956) = (term22 _141954 _141955 _141956).
Proof. exact (SYM (@lem8004298 _141954 _141955 _141956)). Qed.
Lemma lem8004319 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term24 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem8004320 {_141954 _141955 _141956 : Type'} (s : type16 _141954 _141955 _141956) (t : type16 _141954 _141955 _141956) : (s = t) = (term25 _141954 _141955 _141956 s t).
Proof. exact (@lem8004319 (type2 _141954 _141955 _141956) s t). Qed.
Lemma lem8004321 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : ((term10 _141954 _141955 _141956 s t) = (@EMPTY (cart _141954 (finite_sum _141955 _141956)))) = (term26 _141954 _141955 _141956 s t).
Proof. exact (@lem8004320 _141954 _141955 _141956 (term10 _141954 _141955 _141956 s t) (@EMPTY (cart _141954 (finite_sum _141955 _141956)))). Qed.
Lemma lem8004340 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8004341 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term14 _141954 _141955 _141956 s t) = (term27 _141954 _141955 _141956 s t).
Proof. exact (MK_COMB (@lem8004340) (@lem8004321 _141954 _141955 _141956 s t)). Qed.
Lemma lem8004347 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term24 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem8004348 {_141954 _141955 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141955) : (s = t) = (term28 _141954 _141955 s t).
Proof. exact (@lem8004347 (cart _141954 _141955) s t). Qed.
Lemma lem8004349 {_141954 _141955 : Type'} (s : type24 _141954 _141955) : (s = (@EMPTY (cart _141954 _141955))) = (term29 _141954 _141955 s).
Proof. exact (@lem8004348 _141954 _141955 s (@EMPTY (cart _141954 _141955))). Qed.
Lemma lem8004358 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8004359 {_141954 _141955 : Type'} (s : type24 _141954 _141955) : (term30 _141954 _141955 s) = (term31 _141954 _141955 s).
Proof. exact (MK_COMB (@lem8004358) (@lem8004349 _141954 _141955 s)). Qed.
Lemma lem8004363 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term24 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem8004364 {_141954 _141956 : Type'} (s : type24 _141954 _141956) (t : type24 _141954 _141956) : (s = t) = (term28 _141954 _141956 s t).
Proof. exact (@lem8004363 (cart _141954 _141956) s t). Qed.
Lemma lem8004365 {_141954 _141956 : Type'} (t : type24 _141954 _141956) : (t = (@EMPTY (cart _141954 _141956))) = (term29 _141954 _141956 t).
Proof. exact (@lem8004364 _141954 _141956 t (@EMPTY (cart _141954 _141956))). Qed.
Lemma lem8004374 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term15 _141954 _141955 _141956 s t) = (term32 _141954 _141955 _141956 s t).
Proof. exact (MK_COMB (@lem8004359 _141954 _141955 s) (@lem8004365 _141954 _141956 t)). Qed.
Lemma lem8004377 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (((term10 _141954 _141955 _141956 s t) = (@EMPTY (cart _141954 (finite_sum _141955 _141956)))) = (term15 _141954 _141955 _141956 s t)) = ((term26 _141954 _141955 _141956 s t) = (term32 _141954 _141955 _141956 s t)).
Proof. exact (MK_COMB (@lem8004341 _141954 _141955 _141956 s t) (@lem8004374 _141954 _141955 _141956 s t)). Qed.
Lemma lem8004382 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) : (term17 _141954 _141955 _141956 s) = (term33 _141954 _141955 _141956 s).
Proof. exact (fun_ext (fun t : type24 _141954 _141956 => @lem8004377 _141954 _141955 _141956 s t)). Qed.
Lemma lem8004383 {_141954 _141956 : Type'} : (@all ((cart _141954 _141956) -> Prop)) = (@all ((cart _141954 _141956) -> Prop)).
Proof. exact (eq_refl (@all ((cart _141954 _141956) -> Prop))). Qed.
Lemma lem8004384 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) : (term19 _141954 _141955 _141956 s) = (term34 _141954 _141955 _141956 s).
Proof. exact (MK_COMB (@lem8004383 _141954 _141956) (@lem8004382 _141954 _141955 _141956 s)). Qed.
Lemma lem8004389 {_141954 _141955 _141956 : Type'} : (term21 _141954 _141955 _141956) = (term35 _141954 _141955 _141956).
Proof. exact (fun_ext (fun s : type24 _141954 _141955 => @lem8004384 _141954 _141955 _141956 s)). Qed.
Lemma lem8004390 {_141954 _141955 : Type'} : (@all ((cart _141954 _141955) -> Prop)) = (@all ((cart _141954 _141955) -> Prop)).
Proof. exact (eq_refl (@all ((cart _141954 _141955) -> Prop))). Qed.
Lemma lem8004391 {_141954 _141955 _141956 : Type'} : (term23 _141954 _141955 _141956) = (term36 _141954 _141955 _141956).
Proof. exact (MK_COMB (@lem8004390 _141954 _141955) (@lem8004389 _141954 _141955 _141956)). Qed.
Lemma lem8004396 {_141954 _141955 _141956 : Type'} : (term36 _141954 _141955 _141956) = (term23 _141954 _141955 _141956).
Proof. exact (SYM (@lem8004391 _141954 _141955 _141956)). Qed.
Lemma lem8004414 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term37 _83064 x P) = (term38 _83064 P x).
Proof. exact (EQ_MP (@lem3211648 _83064 P x) (@lem3211647 _83064 P x)). Qed.
Lemma lem8004415 {_141954 _141955 _141956 : Type'} (P : type908 _141954 _141955 _141956) (x : type2 _141954 _141955 _141956) : (term39 _141954 _141955 _141956 x P) = (term40 _141954 _141955 _141956 P x).
Proof. exact (@lem8004414 (type2 _141954 _141955 _141956) P x). Qed.
Lemma lem8004416 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) : (term41 _141954 _141955 _141956 x s t) = (term42 _141954 _141955 _141956 s t x).
Proof. exact (@lem8004415 _141954 _141955 _141956 (term43 _141954 _141955 _141956 s t) x). Qed.
Lemma lem8004417 {_141954 _141955 _141956 : Type'} (GEN_PVAR_361 : type2 _141954 _141955 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term44 _141954 _141955 _141956 s t GEN_PVAR_361) = (term45 _141954 _141955 _141956 GEN_PVAR_361 s t).
Proof. exact (eq_refl (term44 _141954 _141955 _141956 s t GEN_PVAR_361)). Qed.
Lemma lem8004418 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term46 _141954 _141955 _141956 s t) = (term47 _141954 _141955 _141956 s t).
Proof. exact (fun_ext (fun GEN_PVAR_361 : type2 _141954 _141955 _141956 => @lem8004417 _141954 _141955 _141956 GEN_PVAR_361 s t)). Qed.
Lemma lem8004419 {_141954 _141955 _141956 : Type'} : (@GSPEC (cart _141954 (finite_sum _141955 _141956))) = (@GSPEC (cart _141954 (finite_sum _141955 _141956))).
Proof. exact (eq_refl (@GSPEC (cart _141954 (finite_sum _141955 _141956)))). Qed.
Lemma lem8004420 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term48 _141954 _141955 _141956 s t) = (term10 _141954 _141955 _141956 s t).
Proof. exact (MK_COMB (@lem8004419 _141954 _141955 _141956) (@lem8004418 _141954 _141955 _141956 s t)). Qed.
Lemma lem8004421 {_141954 _141955 _141956 : Type'} (x : type2 _141954 _141955 _141956) : (@IN (cart _141954 (finite_sum _141955 _141956)) x) = (@IN (cart _141954 (finite_sum _141955 _141956)) x).
Proof. exact (eq_refl (@IN (cart _141954 (finite_sum _141955 _141956)) x)). Qed.
Lemma lem8004422 {_141954 _141955 _141956 : Type'} (x : type2 _141954 _141955 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term41 _141954 _141955 _141956 x s t) = (term49 _141954 _141955 _141956 x s t).
Proof. exact (MK_COMB (@lem8004421 _141954 _141955 _141956 x) (@lem8004420 _141954 _141955 _141956 s t)). Qed.
Lemma lem8004423 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8004424 {_141954 _141955 _141956 : Type'} (x : type2 _141954 _141955 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term50 _141954 _141955 _141956 x s t) = (term51 _141954 _141955 _141956 x s t).
Proof. exact (MK_COMB (@lem8004423) (@lem8004422 _141954 _141955 _141956 x s t)). Qed.
Lemma lem8004425 {_141954 _141955 _141956 : Type'} (x : type2 _141954 _141955 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term42 _141954 _141955 _141956 s t x) = (term52 _141954 _141955 _141956 x s t).
Proof. exact (eq_refl (term42 _141954 _141955 _141956 s t x)). Qed.
Lemma lem8004426 {_141954 _141955 _141956 : Type'} (x : type2 _141954 _141955 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : ((term41 _141954 _141955 _141956 x s t) = (term42 _141954 _141955 _141956 s t x)) = ((term49 _141954 _141955 _141956 x s t) = (term52 _141954 _141955 _141956 x s t)).
Proof. exact (MK_COMB (@lem8004424 _141954 _141955 _141956 x s t) (@lem8004425 _141954 _141955 _141956 x s t)). Qed.
Lemma lem8004427 {_141954 _141955 _141956 : Type'} (x : type2 _141954 _141955 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term49 _141954 _141955 _141956 x s t) = (term52 _141954 _141955 _141956 x s t).
Proof. exact (EQ_MP (@lem8004426 _141954 _141955 _141956 x s t) (@lem8004416 _141954 _141955 _141956 s t x)). Qed.
Lemma lem8004437 {A B : Type'} (f : A -> B) (y : A) : (term53 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8004438 {_141954 _141955 _141956 : Type'} (f : type1526 _141954 _141955 _141956) (y : Prop) : (term54 _141954 _141955 _141956 f y) = (f y).
Proof. exact (@lem8004437 Prop (type16 _141954 _141955 _141956) f y). Qed.
Lemma lem8004439 {_141954 _141955 _141956 : Type'} (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) (s : type24 _141954 _141955) (y : cart _141954 _141956) (t : type24 _141954 _141956) : (term55 _141954 _141955 _141956 x x' s y t) = (term56 _141954 _141955 _141956 x x' s y t).
Proof. exact (@lem8004438 _141954 _141955 _141956 (term57 _141954 _141955 _141956 x) (term58 _141954 _141955 _141956 x' s y t)). Qed.
Lemma lem8004440 {_141954 _141955 _141956 : Type'} (p : Prop) (x : type2 _141954 _141955 _141956) : (term59 _141954 _141955 _141956 x p) = (term60 _141954 _141955 _141956 p x).
Proof. exact (eq_refl (term59 _141954 _141955 _141956 x p)). Qed.
Lemma lem8004441 {_141954 _141955 _141956 : Type'} (x : type2 _141954 _141955 _141956) : (term61 _141954 _141955 _141956 x) = (term57 _141954 _141955 _141956 x).
Proof. exact (fun_ext (fun p : Prop => @lem8004440 _141954 _141955 _141956 p x)). Qed.
Lemma lem8004442 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (s : type24 _141954 _141955) (y : cart _141954 _141956) (t : type24 _141954 _141956) : (term58 _141954 _141955 _141956 x s y t) = (term58 _141954 _141955 _141956 x s y t).
Proof. exact (eq_refl (term58 _141954 _141955 _141956 x s y t)). Qed.
Lemma lem8004443 {_141954 _141955 _141956 : Type'} (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) (s : type24 _141954 _141955) (y : cart _141954 _141956) (t : type24 _141954 _141956) : (term55 _141954 _141955 _141956 x x' s y t) = (term56 _141954 _141955 _141956 x x' s y t).
Proof. exact (MK_COMB (@lem8004441 _141954 _141955 _141956 x) (@lem8004442 _141954 _141955 _141956 x' s y t)). Qed.
Lemma lem8004444 {_141954 _141955 _141956 : Type'} : (@eq ((cart _141954 (finite_sum _141955 _141956)) -> Prop)) = (@eq ((cart _141954 (finite_sum _141955 _141956)) -> Prop)).
Proof. exact (eq_refl (@eq ((cart _141954 (finite_sum _141955 _141956)) -> Prop))). Qed.
Lemma lem8004445 {_141954 _141955 _141956 : Type'} (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) (s : type24 _141954 _141955) (y : cart _141954 _141956) (t : type24 _141954 _141956) : (term62 _141954 _141955 _141956 x x' s y t) = (term63 _141954 _141955 _141956 x x' s y t).
Proof. exact (MK_COMB (@lem8004444 _141954 _141955 _141956) (@lem8004443 _141954 _141955 _141956 x x' s y t)). Qed.
Lemma lem8004446 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (s : type24 _141954 _141955) (y : cart _141954 _141956) (t : type24 _141954 _141956) (x' : type2 _141954 _141955 _141956) : (term56 _141954 _141955 _141956 x' x s y t) = (term64 _141954 _141955 _141956 x s y t x').
Proof. exact (eq_refl (term56 _141954 _141955 _141956 x' x s y t)). Qed.
Lemma lem8004447 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (s : type24 _141954 _141955) (y : cart _141954 _141956) (t : type24 _141954 _141956) (x' : type2 _141954 _141955 _141956) : ((term55 _141954 _141955 _141956 x' x s y t) = (term56 _141954 _141955 _141956 x' x s y t)) = ((term56 _141954 _141955 _141956 x' x s y t) = (term64 _141954 _141955 _141956 x s y t x')).
Proof. exact (MK_COMB (@lem8004445 _141954 _141955 _141956 x' x s y t) (@lem8004446 _141954 _141955 _141956 x s y t x')). Qed.
Lemma lem8004448 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (s : type24 _141954 _141955) (y : cart _141954 _141956) (t : type24 _141954 _141956) (x' : type2 _141954 _141955 _141956) : (term56 _141954 _141955 _141956 x' x s y t) = (term64 _141954 _141955 _141956 x s y t x').
Proof. exact (EQ_MP (@lem8004447 _141954 _141955 _141956 x s y t x') (@lem8004439 _141954 _141955 _141956 x' x s y t)). Qed.
Lemma lem8004454 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8004455 {_141954 _141955 : Type'} (P : type24 _141954 _141955) (x : cart _141954 _141955) : (@IN (cart _141954 _141955) x P) = (P x).
Proof. exact (@lem8004454 (cart _141954 _141955) P x). Qed.
Lemma lem8004456 {_141954 _141955 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) : (@IN (cart _141954 _141955) x s) = (s x).
Proof. exact (@lem8004455 _141954 _141955 s x). Qed.
Lemma lem8004457 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8004458 {_141954 _141955 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) : (term65 _141954 _141955 x s) = (term66 _141954 _141955 s x).
Proof. exact (MK_COMB (@lem8004457) (@lem8004456 _141954 _141955 s x)). Qed.
Lemma lem8004460 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8004461 {_141954 _141956 : Type'} (P : type24 _141954 _141956) (x : cart _141954 _141956) : (@IN (cart _141954 _141956) x P) = (P x).
Proof. exact (@lem8004460 (cart _141954 _141956) P x). Qed.
Lemma lem8004462 {_141954 _141956 : Type'} (t : type24 _141954 _141956) (y : cart _141954 _141956) : (@IN (cart _141954 _141956) y t) = (t y).
Proof. exact (@lem8004461 _141954 _141956 t y). Qed.
Lemma lem8004463 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (y : cart _141954 _141956) : (term58 _141954 _141955 _141956 x s y t) = (term67 _141954 _141955 _141956 s x t y).
Proof. exact (MK_COMB (@lem8004458 _141954 _141955 s x) (@lem8004462 _141954 _141956 t y)). Qed.
Lemma lem8004466 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8004467 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (y : cart _141954 _141956) : (term68 _141954 _141955 _141956 x s y t) = (term69 _141954 _141955 _141956 s x t y).
Proof. exact (MK_COMB (@lem8004466) (@lem8004463 _141954 _141955 _141956 s x t y)). Qed.
Lemma lem8004470 {_141954 _141955 _141956 : Type'} (x : type2 _141954 _141955 _141956) (t : type2 _141954 _141955 _141956) : (x = t) = (x = t).
Proof. exact (eq_refl (x = t)). Qed.
Lemma lem8004471 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (y : cart _141954 _141956) (x' : type2 _141954 _141955 _141956) (t' : type2 _141954 _141955 _141956) : (term70 _141954 _141955 _141956 x s y t x' t') = (term71 _141954 _141955 _141956 s x t y x' t').
Proof. exact (MK_COMB (@lem8004467 _141954 _141955 _141956 s x t y) (@lem8004470 _141954 _141955 _141956 x' t')). Qed.
Lemma lem8004474 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (y : cart _141954 _141956) (x' : type2 _141954 _141955 _141956) : (term64 _141954 _141955 _141956 x s y t x') = (term72 _141954 _141955 _141956 s x t y x').
Proof. exact (fun_ext (fun t' : type2 _141954 _141955 _141956 => @lem8004471 _141954 _141955 _141956 s x t y x' t')). Qed.
Lemma lem8004475 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (y : cart _141954 _141956) (x' : type2 _141954 _141955 _141956) : (term56 _141954 _141955 _141956 x' x s y t) = (term72 _141954 _141955 _141956 s x t y x').
Proof. exact (TRANS (@lem8004448 _141954 _141955 _141956 x s y t x') (@lem8004474 _141954 _141955 _141956 s x t y x')). Qed.
Lemma lem8004476 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (y : cart _141954 _141956) : (@pastecart _141954 _141955 _141956 x y) = (@pastecart _141954 _141955 _141956 x y).
Proof. exact (eq_refl (@pastecart _141954 _141955 _141956 x y)). Qed.
Lemma lem8004477 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) (y : cart _141954 _141956) : (term73 _141954 _141955 _141956 x s t x' y) = (term74 _141954 _141955 _141956 s t x x' y).
Proof. exact (MK_COMB (@lem8004475 _141954 _141955 _141956 s x' t y x) (@lem8004476 _141954 _141955 _141956 x' y)). Qed.
Lemma lem8004479 {A B : Type'} (f : A -> B) (y : A) : (term53 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8004480 {_141954 _141955 _141956 : Type'} (f : type16 _141954 _141955 _141956) (y : type2 _141954 _141955 _141956) : (term75 _141954 _141955 _141956 f y) = (f y).
Proof. exact (@lem8004479 (type2 _141954 _141955 _141956) Prop f y). Qed.
Lemma lem8004481 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) (y : cart _141954 _141956) : (term76 _141954 _141955 _141956 s t x x' y) = (term74 _141954 _141955 _141956 s t x x' y).
Proof. exact (@lem8004480 _141954 _141955 _141956 (term72 _141954 _141955 _141956 s x' t y x) (@pastecart _141954 _141955 _141956 x' y)). Qed.
Lemma lem8004482 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (y : cart _141954 _141956) (x' : type2 _141954 _141955 _141956) (t' : type2 _141954 _141955 _141956) : (term77 _141954 _141955 _141956 s x t y x' t') = (term71 _141954 _141955 _141956 s x t y x' t').
Proof. exact (eq_refl (term77 _141954 _141955 _141956 s x t y x' t')). Qed.
Lemma lem8004483 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (y : cart _141954 _141956) (x' : type2 _141954 _141955 _141956) : (term78 _141954 _141955 _141956 s x t y x') = (term72 _141954 _141955 _141956 s x t y x').
Proof. exact (fun_ext (fun t' : type2 _141954 _141955 _141956 => @lem8004482 _141954 _141955 _141956 s x t y x' t')). Qed.
Lemma lem8004484 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (y : cart _141954 _141956) : (@pastecart _141954 _141955 _141956 x y) = (@pastecart _141954 _141955 _141956 x y).
Proof. exact (eq_refl (@pastecart _141954 _141955 _141956 x y)). Qed.
Lemma lem8004485 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) (y : cart _141954 _141956) : (term76 _141954 _141955 _141956 s t x x' y) = (term74 _141954 _141955 _141956 s t x x' y).
Proof. exact (MK_COMB (@lem8004483 _141954 _141955 _141956 s x' t y x) (@lem8004484 _141954 _141955 _141956 x' y)). Qed.
Lemma lem8004486 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8004487 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) (y : cart _141954 _141956) : (term79 _141954 _141955 _141956 s t x x' y) = (term80 _141954 _141955 _141956 s t x x' y).
Proof. exact (MK_COMB (@lem8004486) (@lem8004485 _141954 _141955 _141956 s t x x' y)). Qed.
Lemma lem8004488 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) (y : cart _141954 _141956) : (term74 _141954 _141955 _141956 s t x x' y) = (term81 _141954 _141955 _141956 s t x x' y).
Proof. exact (eq_refl (term74 _141954 _141955 _141956 s t x x' y)). Qed.
Lemma lem8004489 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) (y : cart _141954 _141956) : ((term76 _141954 _141955 _141956 s t x x' y) = (term74 _141954 _141955 _141956 s t x x' y)) = ((term74 _141954 _141955 _141956 s t x x' y) = (term81 _141954 _141955 _141956 s t x x' y)).
Proof. exact (MK_COMB (@lem8004487 _141954 _141955 _141956 s t x x' y) (@lem8004488 _141954 _141955 _141956 s t x x' y)). Qed.
Lemma lem8004490 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) (y : cart _141954 _141956) : (term74 _141954 _141955 _141956 s t x x' y) = (term81 _141954 _141955 _141956 s t x x' y).
Proof. exact (EQ_MP (@lem8004489 _141954 _141955 _141956 s t x x' y) (@lem8004481 _141954 _141955 _141956 s t x x' y)). Qed.
Lemma lem8004497 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) (y : cart _141954 _141956) : (term73 _141954 _141955 _141956 x s t x' y) = (term81 _141954 _141955 _141956 s t x x' y).
Proof. exact (TRANS (@lem8004477 _141954 _141955 _141956 s t x x' y) (@lem8004490 _141954 _141955 _141956 s t x x' y)). Qed.
Lemma lem8004498 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) : (term82 _141954 _141955 _141956 x s t x') = (term83 _141954 _141955 _141956 s t x x').
Proof. exact (fun_ext (fun y : cart _141954 _141956 => @lem8004497 _141954 _141955 _141956 s t x x' y)). Qed.
Lemma lem8004499 {_141954 _141956 : Type'} : (@ex (cart _141954 _141956)) = (@ex (cart _141954 _141956)).
Proof. exact (eq_refl (@ex (cart _141954 _141956))). Qed.
Lemma lem8004500 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) : (term84 _141954 _141955 _141956 x s t x') = (term85 _141954 _141955 _141956 s t x x').
Proof. exact (MK_COMB (@lem8004499 _141954 _141956) (@lem8004498 _141954 _141955 _141956 s t x x')). Qed.
Lemma lem8004505 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) : (term86 _141954 _141955 _141956 x s t) = (term87 _141954 _141955 _141956 s t x).
Proof. exact (fun_ext (fun x' : cart _141954 _141955 => @lem8004500 _141954 _141955 _141956 s t x x')). Qed.
Lemma lem8004506 {_141954 _141955 : Type'} : (@ex (cart _141954 _141955)) = (@ex (cart _141954 _141955)).
Proof. exact (eq_refl (@ex (cart _141954 _141955))). Qed.
Lemma lem8004507 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) : (term52 _141954 _141955 _141956 x s t) = (term88 _141954 _141955 _141956 s t x).
Proof. exact (MK_COMB (@lem8004506 _141954 _141955) (@lem8004505 _141954 _141955 _141956 s t x)). Qed.
Lemma lem8004512 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) : (term49 _141954 _141955 _141956 x s t) = (term88 _141954 _141955 _141956 s t x).
Proof. exact (TRANS (@lem8004427 _141954 _141955 _141956 x s t) (@lem8004507 _141954 _141955 _141956 s t x)). Qed.
Lemma lem8004513 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8004514 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) : (term51 _141954 _141955 _141956 x s t) = (term89 _141954 _141955 _141956 s t x).
Proof. exact (MK_COMB (@lem8004513) (@lem8004512 _141954 _141955 _141956 s t x)). Qed.
Lemma lem8004516 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem8004517 {_141954 _141955 _141956 : Type'} (x : type2 _141954 _141955 _141956) : (@IN (cart _141954 (finite_sum _141955 _141956)) x (@EMPTY (cart _141954 (finite_sum _141955 _141956)))) = False.
Proof. exact (@lem8004516 (type2 _141954 _141955 _141956) x). Qed.
Lemma lem8004518 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) : ((term49 _141954 _141955 _141956 x s t) = (@IN (cart _141954 (finite_sum _141955 _141956)) x (@EMPTY (cart _141954 (finite_sum _141955 _141956))))) = ((term88 _141954 _141955 _141956 s t x) = False).
Proof. exact (MK_COMB (@lem8004514 _141954 _141955 _141956 s t x) (@lem8004517 _141954 _141955 _141956 x)). Qed.
Lemma lem8004520 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem8004521 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) : ((term88 _141954 _141955 _141956 s t x) = False) = (term90 _141954 _141955 _141956 s t x).
Proof. exact (@lem8004520 (term88 _141954 _141955 _141956 s t x)). Qed.
Lemma lem8004536 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) : ((term49 _141954 _141955 _141956 x s t) = (@IN (cart _141954 (finite_sum _141955 _141956)) x (@EMPTY (cart _141954 (finite_sum _141955 _141956))))) = (term90 _141954 _141955 _141956 s t x).
Proof. exact (TRANS (@lem8004518 _141954 _141955 _141956 s t x) (@lem8004521 _141954 _141955 _141956 s t x)). Qed.
Lemma lem8004537 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term91 _141954 _141955 _141956 s t) = (term92 _141954 _141955 _141956 s t).
Proof. exact (fun_ext (fun x : type2 _141954 _141955 _141956 => @lem8004536 _141954 _141955 _141956 s t x)). Qed.
Lemma lem8004538 {_141954 _141955 _141956 : Type'} : (@all (cart _141954 (finite_sum _141955 _141956))) = (@all (cart _141954 (finite_sum _141955 _141956))).
Proof. exact (eq_refl (@all (cart _141954 (finite_sum _141955 _141956)))). Qed.
Lemma lem8004539 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term26 _141954 _141955 _141956 s t) = (term93 _141954 _141955 _141956 s t).
Proof. exact (MK_COMB (@lem8004538 _141954 _141955 _141956) (@lem8004537 _141954 _141955 _141956 s t)). Qed.
Lemma lem8004544 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8004545 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term27 _141954 _141955 _141956 s t) = (term94 _141954 _141955 _141956 s t).
Proof. exact (MK_COMB (@lem8004544) (@lem8004539 _141954 _141955 _141956 s t)). Qed.
Lemma lem8004555 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8004556 {_141954 _141955 : Type'} (P : type24 _141954 _141955) (x : cart _141954 _141955) : (@IN (cart _141954 _141955) x P) = (P x).
Proof. exact (@lem8004555 (cart _141954 _141955) P x). Qed.
Lemma lem8004557 {_141954 _141955 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) : (@IN (cart _141954 _141955) x s) = (s x).
Proof. exact (@lem8004556 _141954 _141955 s x). Qed.
Lemma lem8004558 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8004559 {_141954 _141955 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) : (term95 _141954 _141955 x s) = (term96 _141954 _141955 s x).
Proof. exact (MK_COMB (@lem8004558) (@lem8004557 _141954 _141955 s x)). Qed.
Lemma lem8004561 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem8004562 {_141954 _141955 : Type'} (x : cart _141954 _141955) : (@IN (cart _141954 _141955) x (@EMPTY (cart _141954 _141955))) = False.
Proof. exact (@lem8004561 (cart _141954 _141955) x). Qed.
Lemma lem8004563 {_141954 _141955 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) : ((@IN (cart _141954 _141955) x s) = (@IN (cart _141954 _141955) x (@EMPTY (cart _141954 _141955)))) = ((s x) = False).
Proof. exact (MK_COMB (@lem8004559 _141954 _141955 s x) (@lem8004562 _141954 _141955 x)). Qed.
Lemma lem8004565 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem8004566 {_141954 _141955 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) : ((s x) = False) = (term97 _141954 _141955 s x).
Proof. exact (@lem8004565 (s x)). Qed.
Lemma lem8004567 {_141954 _141955 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) : ((@IN (cart _141954 _141955) x s) = (@IN (cart _141954 _141955) x (@EMPTY (cart _141954 _141955)))) = (term97 _141954 _141955 s x).
Proof. exact (TRANS (@lem8004563 _141954 _141955 s x) (@lem8004566 _141954 _141955 s x)). Qed.
Lemma lem8004568 {_141954 _141955 : Type'} (s : type24 _141954 _141955) : (term98 _141954 _141955 s) = (term99 _141954 _141955 s).
Proof. exact (fun_ext (fun x : cart _141954 _141955 => @lem8004567 _141954 _141955 s x)). Qed.
Lemma lem8004569 {_141954 _141955 : Type'} : (@all (cart _141954 _141955)) = (@all (cart _141954 _141955)).
Proof. exact (eq_refl (@all (cart _141954 _141955))). Qed.
Lemma lem8004570 {_141954 _141955 : Type'} (s : type24 _141954 _141955) : (term29 _141954 _141955 s) = (term100 _141954 _141955 s).
Proof. exact (MK_COMB (@lem8004569 _141954 _141955) (@lem8004568 _141954 _141955 s)). Qed.
Lemma lem8004575 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8004576 {_141954 _141955 : Type'} (s : type24 _141954 _141955) : (term31 _141954 _141955 s) = (term101 _141954 _141955 s).
Proof. exact (MK_COMB (@lem8004575) (@lem8004570 _141954 _141955 s)). Qed.
Lemma lem8004584 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8004585 {_141954 _141956 : Type'} (P : type24 _141954 _141956) (x : cart _141954 _141956) : (@IN (cart _141954 _141956) x P) = (P x).
Proof. exact (@lem8004584 (cart _141954 _141956) P x). Qed.
Lemma lem8004586 {_141954 _141956 : Type'} (t : type24 _141954 _141956) (x : cart _141954 _141956) : (@IN (cart _141954 _141956) x t) = (t x).
Proof. exact (@lem8004585 _141954 _141956 t x). Qed.
Lemma lem8004587 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8004588 {_141954 _141956 : Type'} (t : type24 _141954 _141956) (x : cart _141954 _141956) : (term95 _141954 _141956 x t) = (term96 _141954 _141956 t x).
Proof. exact (MK_COMB (@lem8004587) (@lem8004586 _141954 _141956 t x)). Qed.
Lemma lem8004590 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem8004591 {_141954 _141956 : Type'} (x : cart _141954 _141956) : (@IN (cart _141954 _141956) x (@EMPTY (cart _141954 _141956))) = False.
Proof. exact (@lem8004590 (cart _141954 _141956) x). Qed.
Lemma lem8004592 {_141954 _141956 : Type'} (t : type24 _141954 _141956) (x : cart _141954 _141956) : ((@IN (cart _141954 _141956) x t) = (@IN (cart _141954 _141956) x (@EMPTY (cart _141954 _141956)))) = ((t x) = False).
Proof. exact (MK_COMB (@lem8004588 _141954 _141956 t x) (@lem8004591 _141954 _141956 x)). Qed.
Lemma lem8004594 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem8004595 {_141954 _141956 : Type'} (t : type24 _141954 _141956) (x : cart _141954 _141956) : ((t x) = False) = (term97 _141954 _141956 t x).
Proof. exact (@lem8004594 (t x)). Qed.
Lemma lem8004596 {_141954 _141956 : Type'} (t : type24 _141954 _141956) (x : cart _141954 _141956) : ((@IN (cart _141954 _141956) x t) = (@IN (cart _141954 _141956) x (@EMPTY (cart _141954 _141956)))) = (term97 _141954 _141956 t x).
Proof. exact (TRANS (@lem8004592 _141954 _141956 t x) (@lem8004595 _141954 _141956 t x)). Qed.
Lemma lem8004597 {_141954 _141956 : Type'} (t : type24 _141954 _141956) : (term98 _141954 _141956 t) = (term99 _141954 _141956 t).
Proof. exact (fun_ext (fun x : cart _141954 _141956 => @lem8004596 _141954 _141956 t x)). Qed.
Lemma lem8004598 {_141954 _141956 : Type'} : (@all (cart _141954 _141956)) = (@all (cart _141954 _141956)).
Proof. exact (eq_refl (@all (cart _141954 _141956))). Qed.
Lemma lem8004599 {_141954 _141956 : Type'} (t : type24 _141954 _141956) : (term29 _141954 _141956 t) = (term100 _141954 _141956 t).
Proof. exact (MK_COMB (@lem8004598 _141954 _141956) (@lem8004597 _141954 _141956 t)). Qed.
Lemma lem8004604 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term32 _141954 _141955 _141956 s t) = (term102 _141954 _141955 _141956 s t).
Proof. exact (MK_COMB (@lem8004576 _141954 _141955 s) (@lem8004599 _141954 _141956 t)). Qed.
Lemma lem8004607 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : ((term26 _141954 _141955 _141956 s t) = (term32 _141954 _141955 _141956 s t)) = ((term93 _141954 _141955 _141956 s t) = (term102 _141954 _141955 _141956 s t)).
Proof. exact (MK_COMB (@lem8004545 _141954 _141955 _141956 s t) (@lem8004604 _141954 _141955 _141956 s t)). Qed.
Lemma lem8004610 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) : (term33 _141954 _141955 _141956 s) = (term103 _141954 _141955 _141956 s).
Proof. exact (fun_ext (fun t : type24 _141954 _141956 => @lem8004607 _141954 _141955 _141956 s t)). Qed.
Lemma lem8004611 {_141954 _141956 : Type'} : (@all ((cart _141954 _141956) -> Prop)) = (@all ((cart _141954 _141956) -> Prop)).
Proof. exact (eq_refl (@all ((cart _141954 _141956) -> Prop))). Qed.
Lemma lem8004612 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) : (term34 _141954 _141955 _141956 s) = (term104 _141954 _141955 _141956 s).
Proof. exact (MK_COMB (@lem8004611 _141954 _141956) (@lem8004610 _141954 _141955 _141956 s)). Qed.
Lemma lem8004617 {_141954 _141955 _141956 : Type'} : (term35 _141954 _141955 _141956) = (term105 _141954 _141955 _141956).
Proof. exact (fun_ext (fun s : type24 _141954 _141955 => @lem8004612 _141954 _141955 _141956 s)). Qed.
Lemma lem8004618 {_141954 _141955 : Type'} : (@all ((cart _141954 _141955) -> Prop)) = (@all ((cart _141954 _141955) -> Prop)).
Proof. exact (eq_refl (@all ((cart _141954 _141955) -> Prop))). Qed.
Lemma lem8004619 {_141954 _141955 _141956 : Type'} : (term36 _141954 _141955 _141956) = (term106 _141954 _141955 _141956).
Proof. exact (MK_COMB (@lem8004618 _141954 _141955) (@lem8004617 _141954 _141955 _141956)). Qed.
Lemma lem8004624 {_141954 _141955 _141956 : Type'} : (term106 _141954 _141955 _141956) = (term36 _141954 _141955 _141956).
Proof. exact (SYM (@lem8004619 _141954 _141955 _141956)). Qed.
Lemma lem8004626 (p : Prop) : p = (term107 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8004627 {_141954 _141955 _141956 : Type'} : (term106 _141954 _141955 _141956) = (term108 _141954 _141955 _141956).
Proof. exact (@lem8004626 (term106 _141954 _141955 _141956)). Qed.
Lemma lem8004628 {_141954 _141955 _141956 : Type'} : (term108 _141954 _141955 _141956) = (term106 _141954 _141955 _141956).
Proof. exact (SYM (@lem8004627 _141954 _141955 _141956)). Qed.
Lemma lem8004629 {_141954 _141955 _141956 : Type'} (h1 : term109 _141954 _141955 _141956) : term109 _141954 _141955 _141956.
Proof. exact (h1). Qed.
Lemma lem8004632 {_141954 _141955 _141956 : Type'} (h1 : term108 _141954 _141955 _141956) : term108 _141954 _141955 _141956.
Proof. exact (h1). Qed.
Lemma lem8004633 {_141954 _141955 _141956 : Type'} : term110 _141954 _141955 _141956.
Proof. exact (fun h0 : term108 _141954 _141955 _141956 => @lem8004632 _141954 _141955 _141956 h0). Qed.
Lemma lem8004634 {_141954 _141955 _141956 : Type'} (h1 : term110 _141954 _141955 _141956) : term110 _141954 _141955 _141956.
Proof. exact (h1). Qed.
Lemma lem8004635 {_141954 _141955 _141956 : Type'} (h1 : term108 _141954 _141955 _141956) : term108 _141954 _141955 _141956.
Proof. exact (h1). Qed.
Lemma lem8004636 {_141954 _141955 _141956 : Type'} (h1 : term108 _141954 _141955 _141956) (h2 : term110 _141954 _141955 _141956) : term108 _141954 _141955 _141956.
Proof. exact (@lem8004634 _141954 _141955 _141956 h2 (@lem8004635 _141954 _141955 _141956 h1)). Qed.
Lemma lem8004637 {_141954 _141955 _141956 : Type'} (h1 : term108 _141954 _141955 _141956) : term111 _141954 _141955 _141956.
Proof. exact (fun h0 : term110 _141954 _141955 _141956 => @lem8004636 _141954 _141955 _141956 h1 h0). Qed.
Lemma lem8004638 {_141954 _141955 _141956 : Type'} (h1 : term110 _141954 _141955 _141956) : term110 _141954 _141955 _141956.
Proof. exact (h1). Qed.
Lemma lem8004639 {_141954 _141955 _141956 : Type'} (h1 : term108 _141954 _141955 _141956) (h2 : term110 _141954 _141955 _141956) : term108 _141954 _141955 _141956.
Proof. exact (@lem8004637 _141954 _141955 _141956 h1 (@lem8004638 _141954 _141955 _141956 h2)). Qed.
Lemma lem8004640 {_141954 _141955 _141956 : Type'} (h1 : term110 _141954 _141955 _141956) : term110 _141954 _141955 _141956.
Proof. exact (fun h0 : term108 _141954 _141955 _141956 => @lem8004639 _141954 _141955 _141956 h0 h1). Qed.
Lemma lem8004641 {_141954 _141955 _141956 : Type'} : term112 _141954 _141955 _141956.
Proof. exact (fun h0 : term110 _141954 _141955 _141956 => @lem8004640 _141954 _141955 _141956 h0). Qed.
Lemma lem8004644 {_141954 _141955 _141956 : Type'} : term110 _141954 _141955 _141956.
Proof. exact (@lem8004641 _141954 _141955 _141956 (@lem8004633 _141954 _141955 _141956)). Qed.
Lemma lem8004645 {_141954 _141955 _141956 : Type'} : term110 _141954 _141955 _141956.
Proof. exact (@lem8004644 _141954 _141955 _141956). Qed.
Lemma lem8004647 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem8004648 {_141954 _141955 _141956 : Type'} : (term108 _141954 _141955 _141956) = (term113 _141954 _141955 _141956).
Proof. exact (@lem8004647 (term109 _141954 _141955 _141956)). Qed.
Lemma lem8004650 (t : Prop) : (term114 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem8004651 {_141954 _141955 _141956 : Type'} : (term113 _141954 _141955 _141956) = (term106 _141954 _141955 _141956).
Proof. exact (@lem8004650 (term106 _141954 _141955 _141956)). Qed.
Lemma lem8004734 {_141954 _141955 _141956 : Type'} : (term108 _141954 _141955 _141956) = (term106 _141954 _141955 _141956).
Proof. exact (TRANS (@lem8004648 _141954 _141955 _141956) (@lem8004651 _141954 _141955 _141956)). Qed.
Lemma lem8004737 {_141954 _141956 : Type'} (t : type24 _141954 _141956) (x : cart _141954 _141956) : (term97 _141954 _141956 t x) = (term97 _141954 _141956 t x).
Proof. exact (eq_refl (term97 _141954 _141956 t x)). Qed.
Lemma lem8004738 {_141954 _141956 : Type'} (t : type24 _141954 _141956) : (term99 _141954 _141956 t) = (term99 _141954 _141956 t).
Proof. exact (fun_ext (fun x : cart _141954 _141956 => @lem8004737 _141954 _141956 t x)). Qed.
Lemma lem8004739 {_141954 _141956 : Type'} : (@all (cart _141954 _141956)) = (@all (cart _141954 _141956)).
Proof. exact (eq_refl (@all (cart _141954 _141956))). Qed.
Lemma lem8004740 {_141954 _141956 : Type'} (t : type24 _141954 _141956) : (term100 _141954 _141956 t) = (term100 _141954 _141956 t).
Proof. exact (MK_COMB (@lem8004739 _141954 _141956) (@lem8004738 _141954 _141956 t)). Qed.
Lemma lem8004743 {_141954 _141955 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) : (term97 _141954 _141955 s x) = (term97 _141954 _141955 s x).
Proof. exact (eq_refl (term97 _141954 _141955 s x)). Qed.
Lemma lem8004744 {_141954 _141955 : Type'} (s : type24 _141954 _141955) : (term99 _141954 _141955 s) = (term99 _141954 _141955 s).
Proof. exact (fun_ext (fun x : cart _141954 _141955 => @lem8004743 _141954 _141955 s x)). Qed.
Lemma lem8004745 {_141954 _141955 : Type'} : (@all (cart _141954 _141955)) = (@all (cart _141954 _141955)).
Proof. exact (eq_refl (@all (cart _141954 _141955))). Qed.
Lemma lem8004746 {_141954 _141955 : Type'} (s : type24 _141954 _141955) : (term100 _141954 _141955 s) = (term100 _141954 _141955 s).
Proof. exact (MK_COMB (@lem8004745 _141954 _141955) (@lem8004744 _141954 _141955 s)). Qed.
Lemma lem8004747 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8004748 {_141954 _141955 : Type'} (s : type24 _141954 _141955) : (term101 _141954 _141955 s) = (term101 _141954 _141955 s).
Proof. exact (MK_COMB (@lem8004747) (@lem8004746 _141954 _141955 s)). Qed.
Lemma lem8004749 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term102 _141954 _141955 _141956 s t) = (term102 _141954 _141955 _141956 s t).
Proof. exact (MK_COMB (@lem8004748 _141954 _141955 s) (@lem8004740 _141954 _141956 t)). Qed.
Lemma lem8004758 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) (y : cart _141954 _141956) : (term81 _141954 _141955 _141956 s t x x' y) = (term81 _141954 _141955 _141956 s t x x' y).
Proof. exact (eq_refl (term81 _141954 _141955 _141956 s t x x' y)). Qed.
Lemma lem8004759 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) : (term83 _141954 _141955 _141956 s t x x') = (term83 _141954 _141955 _141956 s t x x').
Proof. exact (fun_ext (fun y : cart _141954 _141956 => @lem8004758 _141954 _141955 _141956 s t x x' y)). Qed.
Lemma lem8004760 {_141954 _141956 : Type'} : (@ex (cart _141954 _141956)) = (@ex (cart _141954 _141956)).
Proof. exact (eq_refl (@ex (cart _141954 _141956))). Qed.
Lemma lem8004761 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) : (term85 _141954 _141955 _141956 s t x x') = (term85 _141954 _141955 _141956 s t x x').
Proof. exact (MK_COMB (@lem8004760 _141954 _141956) (@lem8004759 _141954 _141955 _141956 s t x x')). Qed.
Lemma lem8004762 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) : (term87 _141954 _141955 _141956 s t x) = (term87 _141954 _141955 _141956 s t x).
Proof. exact (fun_ext (fun x' : cart _141954 _141955 => @lem8004761 _141954 _141955 _141956 s t x x')). Qed.
Lemma lem8004763 {_141954 _141955 : Type'} : (@ex (cart _141954 _141955)) = (@ex (cart _141954 _141955)).
Proof. exact (eq_refl (@ex (cart _141954 _141955))). Qed.
Lemma lem8004764 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) : (term88 _141954 _141955 _141956 s t x) = (term88 _141954 _141955 _141956 s t x).
Proof. exact (MK_COMB (@lem8004763 _141954 _141955) (@lem8004762 _141954 _141955 _141956 s t x)). Qed.
Lemma lem8004765 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8004766 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) : (term90 _141954 _141955 _141956 s t x) = (term90 _141954 _141955 _141956 s t x).
Proof. exact (MK_COMB (@lem8004765) (@lem8004764 _141954 _141955 _141956 s t x)). Qed.
Lemma lem8004767 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term92 _141954 _141955 _141956 s t) = (term92 _141954 _141955 _141956 s t).
Proof. exact (fun_ext (fun x : type2 _141954 _141955 _141956 => @lem8004766 _141954 _141955 _141956 s t x)). Qed.
Lemma lem8004768 {_141954 _141955 _141956 : Type'} : (@all (cart _141954 (finite_sum _141955 _141956))) = (@all (cart _141954 (finite_sum _141955 _141956))).
Proof. exact (eq_refl (@all (cart _141954 (finite_sum _141955 _141956)))). Qed.
Lemma lem8004769 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term93 _141954 _141955 _141956 s t) = (term93 _141954 _141955 _141956 s t).
Proof. exact (MK_COMB (@lem8004768 _141954 _141955 _141956) (@lem8004767 _141954 _141955 _141956 s t)). Qed.
Lemma lem8004770 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8004771 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term94 _141954 _141955 _141956 s t) = (term94 _141954 _141955 _141956 s t).
Proof. exact (MK_COMB (@lem8004770) (@lem8004769 _141954 _141955 _141956 s t)). Qed.
Lemma lem8004772 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : ((term93 _141954 _141955 _141956 s t) = (term102 _141954 _141955 _141956 s t)) = ((term93 _141954 _141955 _141956 s t) = (term102 _141954 _141955 _141956 s t)).
Proof. exact (MK_COMB (@lem8004771 _141954 _141955 _141956 s t) (@lem8004749 _141954 _141955 _141956 s t)). Qed.
Lemma lem8004773 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) : (term103 _141954 _141955 _141956 s) = (term103 _141954 _141955 _141956 s).
Proof. exact (fun_ext (fun t : type24 _141954 _141956 => @lem8004772 _141954 _141955 _141956 s t)). Qed.
Lemma lem8004774 {_141954 _141956 : Type'} : (@all ((cart _141954 _141956) -> Prop)) = (@all ((cart _141954 _141956) -> Prop)).
Proof. exact (eq_refl (@all ((cart _141954 _141956) -> Prop))). Qed.
Lemma lem8004775 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) : (term104 _141954 _141955 _141956 s) = (term104 _141954 _141955 _141956 s).
Proof. exact (MK_COMB (@lem8004774 _141954 _141956) (@lem8004773 _141954 _141955 _141956 s)). Qed.
Lemma lem8004776 {_141954 _141955 _141956 : Type'} : (term105 _141954 _141955 _141956) = (term105 _141954 _141955 _141956).
Proof. exact (fun_ext (fun s : type24 _141954 _141955 => @lem8004775 _141954 _141955 _141956 s)). Qed.
Lemma lem8004777 {_141954 _141955 : Type'} : (@all ((cart _141954 _141955) -> Prop)) = (@all ((cart _141954 _141955) -> Prop)).
Proof. exact (eq_refl (@all ((cart _141954 _141955) -> Prop))). Qed.
Lemma lem8004778 {_141954 _141955 _141956 : Type'} : (term106 _141954 _141955 _141956) = (term106 _141954 _141955 _141956).
Proof. exact (MK_COMB (@lem8004777 _141954 _141955) (@lem8004776 _141954 _141955 _141956)). Qed.
Lemma lem8004829 {_141954 _141955 _141956 : Type'} : (term108 _141954 _141955 _141956) = (term106 _141954 _141955 _141956).
Proof. exact (TRANS (@lem8004734 _141954 _141955 _141956) (@lem8004778 _141954 _141955 _141956)). Qed.
Lemma lem8004830 {_141954 _141955 _141956 : Type'} : (term106 _141954 _141955 _141956) = (term108 _141954 _141955 _141956).
Proof. exact (SYM (@lem8004829 _141954 _141955 _141956)). Qed.
Lemma lem8004832 (p : Prop) : p = (term107 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8004833 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : ((term93 _141954 _141955 _141956 s t) = (term102 _141954 _141955 _141956 s t)) = (term115 _141954 _141955 _141956 s t).
Proof. exact (@lem8004832 ((term93 _141954 _141955 _141956 s t) = (term102 _141954 _141955 _141956 s t))). Qed.
Lemma lem8004834 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term115 _141954 _141955 _141956 s t) = ((term93 _141954 _141955 _141956 s t) = (term102 _141954 _141955 _141956 s t)).
Proof. exact (SYM (@lem8004833 _141954 _141955 _141956 s t)). Qed.
Lemma lem8004835 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (h1 : term116 _141954 _141955 _141956 s t) : term116 _141954 _141955 _141956 s t.
Proof. exact (h1). Qed.
Lemma lem8004844 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (y : cart _141954 _141956) : (term117 _141954 _141955 _141956 s x t y) = (term118 _141954 _141955 _141956 s x t y).
Proof. exact (@lem17045 (s x) (t y)). Qed.
Lemma lem8004848 {_141954 _141955 _141956 : Type'} (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) (y : cart _141954 _141956) : (term119 _141954 _141955 _141956 x x' y) = (term119 _141954 _141955 _141956 x x' y).
Proof. exact (eq_refl (term119 _141954 _141955 _141956 x x' y)). Qed.
Lemma lem8004850 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8004851 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (y : cart _141954 _141956) : (term120 _141954 _141955 _141956 s x t y) = (term121 _141954 _141955 _141956 s x t y).
Proof. exact (MK_COMB (@lem8004850) (@lem8004844 _141954 _141955 _141956 s x t y)). Qed.
Lemma lem8004852 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) (y : cart _141954 _141956) : (term122 _141954 _141955 _141956 s t x x' y) = (term123 _141954 _141955 _141956 s t x x' y).
Proof. exact (MK_COMB (@lem8004851 _141954 _141955 _141956 s x' t y) (@lem8004848 _141954 _141955 _141956 x x' y)). Qed.
Lemma lem8004853 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) (y : cart _141954 _141956) : (term124 _141954 _141955 _141956 s t x x' y) = (term122 _141954 _141955 _141956 s t x x' y).
Proof. exact (@lem17045 (term67 _141954 _141955 _141956 s x' t y) (x = (@pastecart _141954 _141955 _141956 x' y))). Qed.
Lemma lem8004854 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) (y : cart _141954 _141956) : (term124 _141954 _141955 _141956 s t x x' y) = (term123 _141954 _141955 _141956 s t x x' y).
Proof. exact (TRANS (@lem8004853 _141954 _141955 _141956 s t x x' y) (@lem8004852 _141954 _141955 _141956 s t x x' y)). Qed.
Lemma lem8004857 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) (y : cart _141954 _141956) : (term81 _141954 _141955 _141956 s t x x' y) = (term81 _141954 _141955 _141956 s t x x' y).
Proof. exact (eq_refl (term81 _141954 _141955 _141956 s t x x' y)). Qed.
Lemma lem8004858 {_141954 _141956 : Type'} (P : type24 _141954 _141956) : (term125 _141954 _141956 P) = (term100 _141954 _141956 P).
Proof. exact (@lem18394 (cart _141954 _141956) P). Qed.
Lemma lem8004859 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) : (term126 _141954 _141955 _141956 s t x x') = (term127 _141954 _141955 _141956 s t x x').
Proof. exact (@lem8004858 _141954 _141956 (term83 _141954 _141955 _141956 s t x x')). Qed.
Lemma lem8004860 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) (y : cart _141954 _141956) : (term128 _141954 _141955 _141956 s t x x' y) = (term81 _141954 _141955 _141956 s t x x' y).
Proof. exact (eq_refl (term128 _141954 _141955 _141956 s t x x' y)). Qed.
Lemma lem8004861 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8004862 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) (y : cart _141954 _141956) : (term129 _141954 _141955 _141956 s t x x' y) = (term124 _141954 _141955 _141956 s t x x' y).
Proof. exact (MK_COMB (@lem8004861) (@lem8004860 _141954 _141955 _141956 s t x x' y)). Qed.
Lemma lem8004863 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) (y : cart _141954 _141956) : (term129 _141954 _141955 _141956 s t x x' y) = (term123 _141954 _141955 _141956 s t x x' y).
Proof. exact (TRANS (@lem8004862 _141954 _141955 _141956 s t x x' y) (@lem8004854 _141954 _141955 _141956 s t x x' y)). Qed.
Lemma lem8004864 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) : (term130 _141954 _141955 _141956 s t x x') = (term131 _141954 _141955 _141956 s t x x').
Proof. exact (fun_ext (fun y : cart _141954 _141956 => @lem8004863 _141954 _141955 _141956 s t x x' y)). Qed.
Lemma lem8004865 {_141954 _141956 : Type'} : (@all (cart _141954 _141956)) = (@all (cart _141954 _141956)).
Proof. exact (eq_refl (@all (cart _141954 _141956))). Qed.
Lemma lem8004866 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) : (term127 _141954 _141955 _141956 s t x x') = (term132 _141954 _141955 _141956 s t x x').
Proof. exact (MK_COMB (@lem8004865 _141954 _141956) (@lem8004864 _141954 _141955 _141956 s t x x')). Qed.
Lemma lem8004867 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) : (term126 _141954 _141955 _141956 s t x x') = (term132 _141954 _141955 _141956 s t x x').
Proof. exact (TRANS (@lem8004859 _141954 _141955 _141956 s t x x') (@lem8004866 _141954 _141955 _141956 s t x x')). Qed.
Lemma lem8004868 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) : (term83 _141954 _141955 _141956 s t x x') = (term83 _141954 _141955 _141956 s t x x').
Proof. exact (fun_ext (fun y : cart _141954 _141956 => @lem8004857 _141954 _141955 _141956 s t x x' y)). Qed.
Lemma lem8004869 {_141954 _141956 : Type'} : (@ex (cart _141954 _141956)) = (@ex (cart _141954 _141956)).
Proof. exact (eq_refl (@ex (cart _141954 _141956))). Qed.
Lemma lem8004870 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) : (term85 _141954 _141955 _141956 s t x x') = (term85 _141954 _141955 _141956 s t x x').
Proof. exact (MK_COMB (@lem8004869 _141954 _141956) (@lem8004868 _141954 _141955 _141956 s t x x')). Qed.
Lemma lem8004871 {_141954 _141955 : Type'} (P : type24 _141954 _141955) : (term125 _141954 _141955 P) = (term100 _141954 _141955 P).
Proof. exact (@lem18394 (cart _141954 _141955) P). Qed.
Lemma lem8004872 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) : (term90 _141954 _141955 _141956 s t x) = (term133 _141954 _141955 _141956 s t x).
Proof. exact (@lem8004871 _141954 _141955 (term87 _141954 _141955 _141956 s t x)). Qed.
Lemma lem8004873 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) : (term134 _141954 _141955 _141956 s t x x') = (term85 _141954 _141955 _141956 s t x x').
Proof. exact (eq_refl (term134 _141954 _141955 _141956 s t x x')). Qed.
Lemma lem8004874 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8004875 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) : (term135 _141954 _141955 _141956 s t x x') = (term126 _141954 _141955 _141956 s t x x').
Proof. exact (MK_COMB (@lem8004874) (@lem8004873 _141954 _141955 _141956 s t x x')). Qed.
Lemma lem8004876 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) : (term135 _141954 _141955 _141956 s t x x') = (term132 _141954 _141955 _141956 s t x x').
Proof. exact (TRANS (@lem8004875 _141954 _141955 _141956 s t x x') (@lem8004867 _141954 _141955 _141956 s t x x')). Qed.
Lemma lem8004877 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) : (term136 _141954 _141955 _141956 s t x) = (term137 _141954 _141955 _141956 s t x).
Proof. exact (fun_ext (fun x' : cart _141954 _141955 => @lem8004876 _141954 _141955 _141956 s t x x')). Qed.
Lemma lem8004878 {_141954 _141955 : Type'} : (@all (cart _141954 _141955)) = (@all (cart _141954 _141955)).
Proof. exact (eq_refl (@all (cart _141954 _141955))). Qed.
Lemma lem8004879 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) : (term133 _141954 _141955 _141956 s t x) = (term138 _141954 _141955 _141956 s t x).
Proof. exact (MK_COMB (@lem8004878 _141954 _141955) (@lem8004877 _141954 _141955 _141956 s t x)). Qed.
Lemma lem8004880 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) : (term90 _141954 _141955 _141956 s t x) = (term138 _141954 _141955 _141956 s t x).
Proof. exact (TRANS (@lem8004872 _141954 _141955 _141956 s t x) (@lem8004879 _141954 _141955 _141956 s t x)). Qed.
Lemma lem8004881 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) : (term87 _141954 _141955 _141956 s t x) = (term87 _141954 _141955 _141956 s t x).
Proof. exact (fun_ext (fun x' : cart _141954 _141955 => @lem8004870 _141954 _141955 _141956 s t x x')). Qed.
Lemma lem8004882 {_141954 _141955 : Type'} : (@ex (cart _141954 _141955)) = (@ex (cart _141954 _141955)).
Proof. exact (eq_refl (@ex (cart _141954 _141955))). Qed.
Lemma lem8004883 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) : (term88 _141954 _141955 _141956 s t x) = (term88 _141954 _141955 _141956 s t x).
Proof. exact (MK_COMB (@lem8004882 _141954 _141955) (@lem8004881 _141954 _141955 _141956 s t x)). Qed.
Lemma lem8004884 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) : (term139 _141954 _141955 _141956 s t x) = (term88 _141954 _141955 _141956 s t x).
Proof. exact (@lem16933 (term88 _141954 _141955 _141956 s t x)). Qed.
Lemma lem8004885 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) : (term139 _141954 _141955 _141956 s t x) = (term88 _141954 _141955 _141956 s t x).
Proof. exact (TRANS (@lem8004884 _141954 _141955 _141956 s t x) (@lem8004883 _141954 _141955 _141956 s t x)). Qed.
Lemma lem8004886 {_141954 _141955 _141956 : Type'} (P : type16 _141954 _141955 _141956) : (term140 _141954 _141955 _141956 P) = (term141 _141954 _141955 _141956 P).
Proof. exact (@lem18392 (type2 _141954 _141955 _141956) P). Qed.
Lemma lem8004887 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term142 _141954 _141955 _141956 s t) = (term143 _141954 _141955 _141956 s t).
Proof. exact (@lem8004886 _141954 _141955 _141956 (term92 _141954 _141955 _141956 s t)). Qed.
Lemma lem8004888 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) : (term144 _141954 _141955 _141956 s t x) = (term90 _141954 _141955 _141956 s t x).
Proof. exact (eq_refl (term144 _141954 _141955 _141956 s t x)). Qed.
Lemma lem8004889 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8004890 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) : (term145 _141954 _141955 _141956 s t x) = (term139 _141954 _141955 _141956 s t x).
Proof. exact (MK_COMB (@lem8004889) (@lem8004888 _141954 _141955 _141956 s t x)). Qed.
Lemma lem8004891 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) : (term145 _141954 _141955 _141956 s t x) = (term88 _141954 _141955 _141956 s t x).
Proof. exact (TRANS (@lem8004890 _141954 _141955 _141956 s t x) (@lem8004885 _141954 _141955 _141956 s t x)). Qed.
Lemma lem8004892 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term146 _141954 _141955 _141956 s t) = (term147 _141954 _141955 _141956 s t).
Proof. exact (fun_ext (fun x : type2 _141954 _141955 _141956 => @lem8004891 _141954 _141955 _141956 s t x)). Qed.
Lemma lem8004893 {_141954 _141955 _141956 : Type'} : (@ex (cart _141954 (finite_sum _141955 _141956))) = (@ex (cart _141954 (finite_sum _141955 _141956))).
Proof. exact (eq_refl (@ex (cart _141954 (finite_sum _141955 _141956)))). Qed.
Lemma lem8004894 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term143 _141954 _141955 _141956 s t) = (term148 _141954 _141955 _141956 s t).
Proof. exact (MK_COMB (@lem8004893 _141954 _141955 _141956) (@lem8004892 _141954 _141955 _141956 s t)). Qed.
Lemma lem8004895 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term142 _141954 _141955 _141956 s t) = (term148 _141954 _141955 _141956 s t).
Proof. exact (TRANS (@lem8004887 _141954 _141955 _141956 s t) (@lem8004894 _141954 _141955 _141956 s t)). Qed.
Lemma lem8004896 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term92 _141954 _141955 _141956 s t) = (term149 _141954 _141955 _141956 s t).
Proof. exact (fun_ext (fun x : type2 _141954 _141955 _141956 => @lem8004880 _141954 _141955 _141956 s t x)). Qed.
Lemma lem8004897 {_141954 _141955 _141956 : Type'} : (@all (cart _141954 (finite_sum _141955 _141956))) = (@all (cart _141954 (finite_sum _141955 _141956))).
Proof. exact (eq_refl (@all (cart _141954 (finite_sum _141955 _141956)))). Qed.
Lemma lem8004898 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term93 _141954 _141955 _141956 s t) = (term150 _141954 _141955 _141956 s t).
Proof. exact (MK_COMB (@lem8004897 _141954 _141955 _141956) (@lem8004896 _141954 _141955 _141956 s t)). Qed.
Lemma lem8004899 {_141954 _141955 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) : (term97 _141954 _141955 s x) = (term97 _141954 _141955 s x).
Proof. exact (eq_refl (term97 _141954 _141955 s x)). Qed.
Lemma lem8004902 {_141954 _141955 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) : (term151 _141954 _141955 s x) = (s x).
Proof. exact (@lem16933 (s x)). Qed.
Lemma lem8004903 {_141954 _141955 : Type'} (P : type24 _141954 _141955) : (term152 _141954 _141955 P) = (term153 _141954 _141955 P).
Proof. exact (@lem18392 (cart _141954 _141955) P). Qed.
Lemma lem8004904 {_141954 _141955 : Type'} (s : type24 _141954 _141955) : (term154 _141954 _141955 s) = (term155 _141954 _141955 s).
Proof. exact (@lem8004903 _141954 _141955 (term99 _141954 _141955 s)). Qed.
Lemma lem8004905 {_141954 _141955 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) : (term156 _141954 _141955 s x) = (term97 _141954 _141955 s x).
Proof. exact (eq_refl (term156 _141954 _141955 s x)). Qed.
Lemma lem8004906 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8004907 {_141954 _141955 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) : (term157 _141954 _141955 s x) = (term151 _141954 _141955 s x).
Proof. exact (MK_COMB (@lem8004906) (@lem8004905 _141954 _141955 s x)). Qed.
Lemma lem8004908 {_141954 _141955 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) : (term157 _141954 _141955 s x) = (s x).
Proof. exact (TRANS (@lem8004907 _141954 _141955 s x) (@lem8004902 _141954 _141955 s x)). Qed.
Lemma lem8004909 {_141954 _141955 : Type'} (s : type24 _141954 _141955) : (term158 _141954 _141955 s) = (term159 _141954 _141955 s).
Proof. exact (fun_ext (fun x : cart _141954 _141955 => @lem8004908 _141954 _141955 s x)). Qed.
Lemma lem8004910 {_141954 _141955 : Type'} : (@ex (cart _141954 _141955)) = (@ex (cart _141954 _141955)).
Proof. exact (eq_refl (@ex (cart _141954 _141955))). Qed.
Lemma lem8004911 {_141954 _141955 : Type'} (s : type24 _141954 _141955) : (term155 _141954 _141955 s) = (term160 _141954 _141955 s).
Proof. exact (MK_COMB (@lem8004910 _141954 _141955) (@lem8004909 _141954 _141955 s)). Qed.
Lemma lem8004912 {_141954 _141955 : Type'} (s : type24 _141954 _141955) : (term154 _141954 _141955 s) = (term160 _141954 _141955 s).
Proof. exact (TRANS (@lem8004904 _141954 _141955 s) (@lem8004911 _141954 _141955 s)). Qed.
Lemma lem8004913 {_141954 _141955 : Type'} (s : type24 _141954 _141955) : (term99 _141954 _141955 s) = (term99 _141954 _141955 s).
Proof. exact (fun_ext (fun x : cart _141954 _141955 => @lem8004899 _141954 _141955 s x)). Qed.
Lemma lem8004914 {_141954 _141955 : Type'} : (@all (cart _141954 _141955)) = (@all (cart _141954 _141955)).
Proof. exact (eq_refl (@all (cart _141954 _141955))). Qed.
Lemma lem8004915 {_141954 _141955 : Type'} (s : type24 _141954 _141955) : (term100 _141954 _141955 s) = (term100 _141954 _141955 s).
Proof. exact (MK_COMB (@lem8004914 _141954 _141955) (@lem8004913 _141954 _141955 s)). Qed.
Lemma lem8004916 {_141954 _141956 : Type'} (t : type24 _141954 _141956) (x : cart _141954 _141956) : (term97 _141954 _141956 t x) = (term97 _141954 _141956 t x).
Proof. exact (eq_refl (term97 _141954 _141956 t x)). Qed.
Lemma lem8004919 {_141954 _141956 : Type'} (t : type24 _141954 _141956) (x : cart _141954 _141956) : (term151 _141954 _141956 t x) = (t x).
Proof. exact (@lem16933 (t x)). Qed.
Lemma lem8004920 {_141954 _141956 : Type'} (P : type24 _141954 _141956) : (term152 _141954 _141956 P) = (term153 _141954 _141956 P).
Proof. exact (@lem18392 (cart _141954 _141956) P). Qed.
Lemma lem8004921 {_141954 _141956 : Type'} (t : type24 _141954 _141956) : (term154 _141954 _141956 t) = (term155 _141954 _141956 t).
Proof. exact (@lem8004920 _141954 _141956 (term99 _141954 _141956 t)). Qed.
Lemma lem8004922 {_141954 _141956 : Type'} (t : type24 _141954 _141956) (x : cart _141954 _141956) : (term156 _141954 _141956 t x) = (term97 _141954 _141956 t x).
Proof. exact (eq_refl (term156 _141954 _141956 t x)). Qed.
Lemma lem8004923 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8004924 {_141954 _141956 : Type'} (t : type24 _141954 _141956) (x : cart _141954 _141956) : (term157 _141954 _141956 t x) = (term151 _141954 _141956 t x).
Proof. exact (MK_COMB (@lem8004923) (@lem8004922 _141954 _141956 t x)). Qed.
Lemma lem8004925 {_141954 _141956 : Type'} (t : type24 _141954 _141956) (x : cart _141954 _141956) : (term157 _141954 _141956 t x) = (t x).
Proof. exact (TRANS (@lem8004924 _141954 _141956 t x) (@lem8004919 _141954 _141956 t x)). Qed.
Lemma lem8004926 {_141954 _141956 : Type'} (t : type24 _141954 _141956) : (term158 _141954 _141956 t) = (term159 _141954 _141956 t).
Proof. exact (fun_ext (fun x : cart _141954 _141956 => @lem8004925 _141954 _141956 t x)). Qed.
Lemma lem8004927 {_141954 _141956 : Type'} : (@ex (cart _141954 _141956)) = (@ex (cart _141954 _141956)).
Proof. exact (eq_refl (@ex (cart _141954 _141956))). Qed.
Lemma lem8004928 {_141954 _141956 : Type'} (t : type24 _141954 _141956) : (term155 _141954 _141956 t) = (term160 _141954 _141956 t).
Proof. exact (MK_COMB (@lem8004927 _141954 _141956) (@lem8004926 _141954 _141956 t)). Qed.
Lemma lem8004929 {_141954 _141956 : Type'} (t : type24 _141954 _141956) : (term154 _141954 _141956 t) = (term160 _141954 _141956 t).
Proof. exact (TRANS (@lem8004921 _141954 _141956 t) (@lem8004928 _141954 _141956 t)). Qed.
Lemma lem8004930 {_141954 _141956 : Type'} (t : type24 _141954 _141956) : (term99 _141954 _141956 t) = (term99 _141954 _141956 t).
Proof. exact (fun_ext (fun x : cart _141954 _141956 => @lem8004916 _141954 _141956 t x)). Qed.
Lemma lem8004931 {_141954 _141956 : Type'} : (@all (cart _141954 _141956)) = (@all (cart _141954 _141956)).
Proof. exact (eq_refl (@all (cart _141954 _141956))). Qed.
Lemma lem8004932 {_141954 _141956 : Type'} (t : type24 _141954 _141956) : (term100 _141954 _141956 t) = (term100 _141954 _141956 t).
Proof. exact (MK_COMB (@lem8004931 _141954 _141956) (@lem8004930 _141954 _141956 t)). Qed.
Lemma lem8004933 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8004934 {_141954 _141955 : Type'} (s : type24 _141954 _141955) : (term161 _141954 _141955 s) = (term162 _141954 _141955 s).
Proof. exact (MK_COMB (@lem8004933) (@lem8004912 _141954 _141955 s)). Qed.
Lemma lem8004935 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term163 _141954 _141955 _141956 s t) = (term164 _141954 _141955 _141956 s t).
Proof. exact (MK_COMB (@lem8004934 _141954 _141955 s) (@lem8004929 _141954 _141956 t)). Qed.
Lemma lem8004936 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term165 _141954 _141955 _141956 s t) = (term163 _141954 _141955 _141956 s t).
Proof. exact (@lem17160 (term100 _141954 _141955 s) (term100 _141954 _141956 t)). Qed.
Lemma lem8004937 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term165 _141954 _141955 _141956 s t) = (term164 _141954 _141955 _141956 s t).
Proof. exact (TRANS (@lem8004936 _141954 _141955 _141956 s t) (@lem8004935 _141954 _141955 _141956 s t)). Qed.
Lemma lem8004938 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8004939 {_141954 _141955 : Type'} (s : type24 _141954 _141955) : (term101 _141954 _141955 s) = (term101 _141954 _141955 s).
Proof. exact (MK_COMB (@lem8004938) (@lem8004915 _141954 _141955 s)). Qed.
Lemma lem8004940 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term102 _141954 _141955 _141956 s t) = (term102 _141954 _141955 _141956 s t).
Proof. exact (MK_COMB (@lem8004939 _141954 _141955 s) (@lem8004932 _141954 _141956 t)). Qed.
Lemma lem8004941 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8004942 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term166 _141954 _141955 _141956 s t) = (term167 _141954 _141955 _141956 s t).
Proof. exact (MK_COMB (@lem8004941) (@lem8004895 _141954 _141955 _141956 s t)). Qed.
Lemma lem8004943 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term168 _141954 _141955 _141956 s t) = (term169 _141954 _141955 _141956 s t).
Proof. exact (MK_COMB (@lem8004942 _141954 _141955 _141956 s t) (@lem8004940 _141954 _141955 _141956 s t)). Qed.
Lemma lem8004944 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8004945 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term170 _141954 _141955 _141956 s t) = (term171 _141954 _141955 _141956 s t).
Proof. exact (MK_COMB (@lem8004944) (@lem8004898 _141954 _141955 _141956 s t)). Qed.
Lemma lem8004946 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term172 _141954 _141955 _141956 s t) = (term173 _141954 _141955 _141956 s t).
Proof. exact (MK_COMB (@lem8004945 _141954 _141955 _141956 s t) (@lem8004937 _141954 _141955 _141956 s t)). Qed.
Lemma lem8004947 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8004948 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term174 _141954 _141955 _141956 s t) = (term175 _141954 _141955 _141956 s t).
Proof. exact (MK_COMB (@lem8004947) (@lem8004946 _141954 _141955 _141956 s t)). Qed.
Lemma lem8004949 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term176 _141954 _141955 _141956 s t) = (term177 _141954 _141955 _141956 s t).
Proof. exact (MK_COMB (@lem8004948 _141954 _141955 _141956 s t) (@lem8004943 _141954 _141955 _141956 s t)). Qed.
Lemma lem8004950 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term116 _141954 _141955 _141956 s t) = (term176 _141954 _141955 _141956 s t).
Proof. exact (@lem17646 (term93 _141954 _141955 _141956 s t) (term102 _141954 _141955 _141956 s t)). Qed.
Lemma lem8004951 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term116 _141954 _141955 _141956 s t) = (term177 _141954 _141955 _141956 s t).
Proof. exact (TRANS (@lem8004950 _141954 _141955 _141956 s t) (@lem8004949 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005082 {A : Type'} (P : A -> Prop) (Q : Prop) : (term178 A P Q) = (term179 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem8005083 {_141954 _141955 : Type'} (P : type24 _141954 _141955) (Q : Prop) : (term180 _141954 _141955 P Q) = (term181 _141954 _141955 P Q).
Proof. exact (@lem8005082 (cart _141954 _141955) P Q). Qed.
Lemma lem8005084 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term164 _141954 _141955 _141956 s t) = (term182 _141954 _141955 _141956 s t).
Proof. exact (@lem8005083 _141954 _141955 s (term160 _141954 _141956 t)). Qed.
Lemma lem8005086 {A : Type'} (P : Prop) (Q : A -> Prop) : (term183 A P Q) = (term184 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem8005087 {_141954 _141956 : Type'} (P : Prop) (Q : type24 _141954 _141956) : (term185 _141954 _141956 P Q) = (term186 _141954 _141956 P Q).
Proof. exact (@lem8005086 (cart _141954 _141956) P Q). Qed.
Lemma lem8005088 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) : (term187 _141954 _141955 _141956 s x t) = (term188 _141954 _141955 _141956 s x t).
Proof. exact (@lem8005087 _141954 _141956 (s x) t). Qed.
Lemma lem8005089 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term189 _141954 _141955 _141956 s t) = (term190 _141954 _141955 _141956 s t).
Proof. exact (fun_ext (fun x : cart _141954 _141955 => @lem8005088 _141954 _141955 _141956 s x t)). Qed.
Lemma lem8005090 {_141954 _141955 : Type'} : (@ex (cart _141954 _141955)) = (@ex (cart _141954 _141955)).
Proof. exact (eq_refl (@ex (cart _141954 _141955))). Qed.
Lemma lem8005091 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term182 _141954 _141955 _141956 s t) = (term191 _141954 _141955 _141956 s t).
Proof. exact (MK_COMB (@lem8005090 _141954 _141955) (@lem8005089 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005092 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term164 _141954 _141955 _141956 s t) = (term191 _141954 _141955 _141956 s t).
Proof. exact (TRANS (@lem8005084 _141954 _141955 _141956 s t) (@lem8005091 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005093 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term171 _141954 _141955 _141956 s t) = (term171 _141954 _141955 _141956 s t).
Proof. exact (eq_refl (term171 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005094 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term173 _141954 _141955 _141956 s t) = (term192 _141954 _141955 _141956 s t).
Proof. exact (MK_COMB (@lem8005093 _141954 _141955 _141956 s t) (@lem8005092 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005096 {A : Type'} (P : Prop) (Q : A -> Prop) : (term183 A P Q) = (term184 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem8005097 {_141954 _141955 : Type'} (P : Prop) (Q : type24 _141954 _141955) : (term185 _141954 _141955 P Q) = (term186 _141954 _141955 P Q).
Proof. exact (@lem8005096 (cart _141954 _141955) P Q). Qed.
Lemma lem8005098 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term193 _141954 _141955 _141956 s t) = (term194 _141954 _141955 _141956 s t).
Proof. exact (@lem8005097 _141954 _141955 (term150 _141954 _141955 _141956 s t) (term190 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005099 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) : (term195 _141954 _141955 _141956 s t x) = (term188 _141954 _141955 _141956 s x t).
Proof. exact (eq_refl (term195 _141954 _141955 _141956 s t x)). Qed.
Lemma lem8005100 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term196 _141954 _141955 _141956 s t) = (term190 _141954 _141955 _141956 s t).
Proof. exact (fun_ext (fun x : cart _141954 _141955 => @lem8005099 _141954 _141955 _141956 s x t)). Qed.
Lemma lem8005101 {_141954 _141955 : Type'} : (@ex (cart _141954 _141955)) = (@ex (cart _141954 _141955)).
Proof. exact (eq_refl (@ex (cart _141954 _141955))). Qed.
Lemma lem8005102 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term197 _141954 _141955 _141956 s t) = (term191 _141954 _141955 _141956 s t).
Proof. exact (MK_COMB (@lem8005101 _141954 _141955) (@lem8005100 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005103 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term171 _141954 _141955 _141956 s t) = (term171 _141954 _141955 _141956 s t).
Proof. exact (eq_refl (term171 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005104 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term193 _141954 _141955 _141956 s t) = (term192 _141954 _141955 _141956 s t).
Proof. exact (MK_COMB (@lem8005103 _141954 _141955 _141956 s t) (@lem8005102 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005105 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8005106 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term198 _141954 _141955 _141956 s t) = (term199 _141954 _141955 _141956 s t).
Proof. exact (MK_COMB (@lem8005105) (@lem8005104 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005107 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) : (term195 _141954 _141955 _141956 s t x) = (term188 _141954 _141955 _141956 s x t).
Proof. exact (eq_refl (term195 _141954 _141955 _141956 s t x)). Qed.
Lemma lem8005108 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term171 _141954 _141955 _141956 s t) = (term171 _141954 _141955 _141956 s t).
Proof. exact (eq_refl (term171 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005109 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) : (term200 _141954 _141955 _141956 s t x) = (term201 _141954 _141955 _141956 s x t).
Proof. exact (MK_COMB (@lem8005108 _141954 _141955 _141956 s t) (@lem8005107 _141954 _141955 _141956 s x t)). Qed.
Lemma lem8005110 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term202 _141954 _141955 _141956 s t) = (term203 _141954 _141955 _141956 s t).
Proof. exact (fun_ext (fun x : cart _141954 _141955 => @lem8005109 _141954 _141955 _141956 s x t)). Qed.
Lemma lem8005111 {_141954 _141955 : Type'} : (@ex (cart _141954 _141955)) = (@ex (cart _141954 _141955)).
Proof. exact (eq_refl (@ex (cart _141954 _141955))). Qed.
Lemma lem8005112 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term194 _141954 _141955 _141956 s t) = (term204 _141954 _141955 _141956 s t).
Proof. exact (MK_COMB (@lem8005111 _141954 _141955) (@lem8005110 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005113 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : ((term193 _141954 _141955 _141956 s t) = (term194 _141954 _141955 _141956 s t)) = ((term192 _141954 _141955 _141956 s t) = (term204 _141954 _141955 _141956 s t)).
Proof. exact (MK_COMB (@lem8005106 _141954 _141955 _141956 s t) (@lem8005112 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005114 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term192 _141954 _141955 _141956 s t) = (term204 _141954 _141955 _141956 s t).
Proof. exact (EQ_MP (@lem8005113 _141954 _141955 _141956 s t) (@lem8005098 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005116 {A : Type'} (P : Prop) (Q : A -> Prop) : (term183 A P Q) = (term184 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem8005117 {_141954 _141956 : Type'} (P : Prop) (Q : type24 _141954 _141956) : (term185 _141954 _141956 P Q) = (term186 _141954 _141956 P Q).
Proof. exact (@lem8005116 (cart _141954 _141956) P Q). Qed.
Lemma lem8005118 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) : (term205 _141954 _141955 _141956 s x t) = (term206 _141954 _141955 _141956 s x t).
Proof. exact (@lem8005117 _141954 _141956 (term150 _141954 _141955 _141956 s t) (term207 _141954 _141955 _141956 s x t)). Qed.
Lemma lem8005119 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (x' : cart _141954 _141956) : (term208 _141954 _141955 _141956 s x t x') = (term67 _141954 _141955 _141956 s x t x').
Proof. exact (eq_refl (term208 _141954 _141955 _141956 s x t x')). Qed.
Lemma lem8005120 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) : (term209 _141954 _141955 _141956 s x t) = (term207 _141954 _141955 _141956 s x t).
Proof. exact (fun_ext (fun x' : cart _141954 _141956 => @lem8005119 _141954 _141955 _141956 s x t x')). Qed.
Lemma lem8005121 {_141954 _141956 : Type'} : (@ex (cart _141954 _141956)) = (@ex (cart _141954 _141956)).
Proof. exact (eq_refl (@ex (cart _141954 _141956))). Qed.
Lemma lem8005122 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) : (term210 _141954 _141955 _141956 s x t) = (term188 _141954 _141955 _141956 s x t).
Proof. exact (MK_COMB (@lem8005121 _141954 _141956) (@lem8005120 _141954 _141955 _141956 s x t)). Qed.
Lemma lem8005123 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term171 _141954 _141955 _141956 s t) = (term171 _141954 _141955 _141956 s t).
Proof. exact (eq_refl (term171 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005124 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) : (term205 _141954 _141955 _141956 s x t) = (term201 _141954 _141955 _141956 s x t).
Proof. exact (MK_COMB (@lem8005123 _141954 _141955 _141956 s t) (@lem8005122 _141954 _141955 _141956 s x t)). Qed.
Lemma lem8005125 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8005126 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) : (term211 _141954 _141955 _141956 s x t) = (term212 _141954 _141955 _141956 s x t).
Proof. exact (MK_COMB (@lem8005125) (@lem8005124 _141954 _141955 _141956 s x t)). Qed.
Lemma lem8005127 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (x' : cart _141954 _141956) : (term208 _141954 _141955 _141956 s x t x') = (term67 _141954 _141955 _141956 s x t x').
Proof. exact (eq_refl (term208 _141954 _141955 _141956 s x t x')). Qed.
Lemma lem8005128 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term171 _141954 _141955 _141956 s t) = (term171 _141954 _141955 _141956 s t).
Proof. exact (eq_refl (term171 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005129 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (x' : cart _141954 _141956) : (term213 _141954 _141955 _141956 s x t x') = (term214 _141954 _141955 _141956 s x t x').
Proof. exact (MK_COMB (@lem8005128 _141954 _141955 _141956 s t) (@lem8005127 _141954 _141955 _141956 s x t x')). Qed.
Lemma lem8005130 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) : (term215 _141954 _141955 _141956 s x t) = (term216 _141954 _141955 _141956 s x t).
Proof. exact (fun_ext (fun x' : cart _141954 _141956 => @lem8005129 _141954 _141955 _141956 s x t x')). Qed.
Lemma lem8005131 {_141954 _141956 : Type'} : (@ex (cart _141954 _141956)) = (@ex (cart _141954 _141956)).
Proof. exact (eq_refl (@ex (cart _141954 _141956))). Qed.
Lemma lem8005132 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) : (term206 _141954 _141955 _141956 s x t) = (term217 _141954 _141955 _141956 s x t).
Proof. exact (MK_COMB (@lem8005131 _141954 _141956) (@lem8005130 _141954 _141955 _141956 s x t)). Qed.
Lemma lem8005133 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) : ((term205 _141954 _141955 _141956 s x t) = (term206 _141954 _141955 _141956 s x t)) = ((term201 _141954 _141955 _141956 s x t) = (term217 _141954 _141955 _141956 s x t)).
Proof. exact (MK_COMB (@lem8005126 _141954 _141955 _141956 s x t) (@lem8005132 _141954 _141955 _141956 s x t)). Qed.
Lemma lem8005134 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) : (term201 _141954 _141955 _141956 s x t) = (term217 _141954 _141955 _141956 s x t).
Proof. exact (EQ_MP (@lem8005133 _141954 _141955 _141956 s x t) (@lem8005118 _141954 _141955 _141956 s x t)). Qed.
Lemma lem8005135 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term203 _141954 _141955 _141956 s t) = (term218 _141954 _141955 _141956 s t).
Proof. exact (fun_ext (fun x : cart _141954 _141955 => @lem8005134 _141954 _141955 _141956 s x t)). Qed.
Lemma lem8005136 {_141954 _141955 : Type'} : (@ex (cart _141954 _141955)) = (@ex (cart _141954 _141955)).
Proof. exact (eq_refl (@ex (cart _141954 _141955))). Qed.
Lemma lem8005137 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term204 _141954 _141955 _141956 s t) = (term219 _141954 _141955 _141956 s t).
Proof. exact (MK_COMB (@lem8005136 _141954 _141955) (@lem8005135 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005138 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term192 _141954 _141955 _141956 s t) = (term219 _141954 _141955 _141956 s t).
Proof. exact (TRANS (@lem8005114 _141954 _141955 _141956 s t) (@lem8005137 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005139 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term173 _141954 _141955 _141956 s t) = (term219 _141954 _141955 _141956 s t).
Proof. exact (TRANS (@lem8005094 _141954 _141955 _141956 s t) (@lem8005138 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005140 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8005141 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term175 _141954 _141955 _141956 s t) = (term220 _141954 _141955 _141956 s t).
Proof. exact (MK_COMB (@lem8005140) (@lem8005139 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005143 {A : Type'} (P : A -> Prop) (Q : Prop) : (term178 A P Q) = (term179 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem8005144 {_141954 _141955 _141956 : Type'} (P : type16 _141954 _141955 _141956) (Q : Prop) : (term221 _141954 _141955 _141956 P Q) = (term222 _141954 _141955 _141956 P Q).
Proof. exact (@lem8005143 (type2 _141954 _141955 _141956) P Q). Qed.
Lemma lem8005145 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term223 _141954 _141955 _141956 s t) = (term224 _141954 _141955 _141956 s t).
Proof. exact (@lem8005144 _141954 _141955 _141956 (term147 _141954 _141955 _141956 s t) (term102 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005146 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) : (term225 _141954 _141955 _141956 s t x) = (term88 _141954 _141955 _141956 s t x).
Proof. exact (eq_refl (term225 _141954 _141955 _141956 s t x)). Qed.
Lemma lem8005147 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term226 _141954 _141955 _141956 s t) = (term147 _141954 _141955 _141956 s t).
Proof. exact (fun_ext (fun x : type2 _141954 _141955 _141956 => @lem8005146 _141954 _141955 _141956 s t x)). Qed.
Lemma lem8005148 {_141954 _141955 _141956 : Type'} : (@ex (cart _141954 (finite_sum _141955 _141956))) = (@ex (cart _141954 (finite_sum _141955 _141956))).
Proof. exact (eq_refl (@ex (cart _141954 (finite_sum _141955 _141956)))). Qed.
Lemma lem8005149 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term227 _141954 _141955 _141956 s t) = (term148 _141954 _141955 _141956 s t).
Proof. exact (MK_COMB (@lem8005148 _141954 _141955 _141956) (@lem8005147 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005150 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8005151 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term228 _141954 _141955 _141956 s t) = (term167 _141954 _141955 _141956 s t).
Proof. exact (MK_COMB (@lem8005150) (@lem8005149 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005152 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term102 _141954 _141955 _141956 s t) = (term102 _141954 _141955 _141956 s t).
Proof. exact (eq_refl (term102 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005153 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term223 _141954 _141955 _141956 s t) = (term169 _141954 _141955 _141956 s t).
Proof. exact (MK_COMB (@lem8005151 _141954 _141955 _141956 s t) (@lem8005152 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005154 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8005155 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term229 _141954 _141955 _141956 s t) = (term230 _141954 _141955 _141956 s t).
Proof. exact (MK_COMB (@lem8005154) (@lem8005153 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005156 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) : (term225 _141954 _141955 _141956 s t x) = (term88 _141954 _141955 _141956 s t x).
Proof. exact (eq_refl (term225 _141954 _141955 _141956 s t x)). Qed.
Lemma lem8005157 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8005158 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) : (term231 _141954 _141955 _141956 s t x) = (term232 _141954 _141955 _141956 s t x).
Proof. exact (MK_COMB (@lem8005157) (@lem8005156 _141954 _141955 _141956 s t x)). Qed.
Lemma lem8005159 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term102 _141954 _141955 _141956 s t) = (term102 _141954 _141955 _141956 s t).
Proof. exact (eq_refl (term102 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005160 {_141954 _141955 _141956 : Type'} (x : type2 _141954 _141955 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term233 _141954 _141955 _141956 x s t) = (term234 _141954 _141955 _141956 x s t).
Proof. exact (MK_COMB (@lem8005158 _141954 _141955 _141956 s t x) (@lem8005159 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005161 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term235 _141954 _141955 _141956 s t) = (term236 _141954 _141955 _141956 s t).
Proof. exact (fun_ext (fun x : type2 _141954 _141955 _141956 => @lem8005160 _141954 _141955 _141956 x s t)). Qed.
Lemma lem8005162 {_141954 _141955 _141956 : Type'} : (@ex (cart _141954 (finite_sum _141955 _141956))) = (@ex (cart _141954 (finite_sum _141955 _141956))).
Proof. exact (eq_refl (@ex (cart _141954 (finite_sum _141955 _141956)))). Qed.
Lemma lem8005163 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term224 _141954 _141955 _141956 s t) = (term237 _141954 _141955 _141956 s t).
Proof. exact (MK_COMB (@lem8005162 _141954 _141955 _141956) (@lem8005161 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005164 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : ((term223 _141954 _141955 _141956 s t) = (term224 _141954 _141955 _141956 s t)) = ((term169 _141954 _141955 _141956 s t) = (term237 _141954 _141955 _141956 s t)).
Proof. exact (MK_COMB (@lem8005155 _141954 _141955 _141956 s t) (@lem8005163 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005165 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term169 _141954 _141955 _141956 s t) = (term237 _141954 _141955 _141956 s t).
Proof. exact (EQ_MP (@lem8005164 _141954 _141955 _141956 s t) (@lem8005145 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005167 {A : Type'} (P : A -> Prop) (Q : Prop) : (term178 A P Q) = (term179 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem8005168 {_141954 _141955 : Type'} (P : type24 _141954 _141955) (Q : Prop) : (term180 _141954 _141955 P Q) = (term181 _141954 _141955 P Q).
Proof. exact (@lem8005167 (cart _141954 _141955) P Q). Qed.
Lemma lem8005169 {_141954 _141955 _141956 : Type'} (x : type2 _141954 _141955 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term238 _141954 _141955 _141956 x s t) = (term239 _141954 _141955 _141956 x s t).
Proof. exact (@lem8005168 _141954 _141955 (term87 _141954 _141955 _141956 s t x) (term102 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005170 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) : (term134 _141954 _141955 _141956 s t x x') = (term85 _141954 _141955 _141956 s t x x').
Proof. exact (eq_refl (term134 _141954 _141955 _141956 s t x x')). Qed.
Lemma lem8005171 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) : (term240 _141954 _141955 _141956 s t x) = (term87 _141954 _141955 _141956 s t x).
Proof. exact (fun_ext (fun x' : cart _141954 _141955 => @lem8005170 _141954 _141955 _141956 s t x x')). Qed.
Lemma lem8005172 {_141954 _141955 : Type'} : (@ex (cart _141954 _141955)) = (@ex (cart _141954 _141955)).
Proof. exact (eq_refl (@ex (cart _141954 _141955))). Qed.
Lemma lem8005173 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) : (term241 _141954 _141955 _141956 s t x) = (term88 _141954 _141955 _141956 s t x).
Proof. exact (MK_COMB (@lem8005172 _141954 _141955) (@lem8005171 _141954 _141955 _141956 s t x)). Qed.
Lemma lem8005174 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8005175 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) : (term242 _141954 _141955 _141956 s t x) = (term232 _141954 _141955 _141956 s t x).
Proof. exact (MK_COMB (@lem8005174) (@lem8005173 _141954 _141955 _141956 s t x)). Qed.
Lemma lem8005176 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term102 _141954 _141955 _141956 s t) = (term102 _141954 _141955 _141956 s t).
Proof. exact (eq_refl (term102 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005177 {_141954 _141955 _141956 : Type'} (x : type2 _141954 _141955 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term238 _141954 _141955 _141956 x s t) = (term234 _141954 _141955 _141956 x s t).
Proof. exact (MK_COMB (@lem8005175 _141954 _141955 _141956 s t x) (@lem8005176 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005178 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8005179 {_141954 _141955 _141956 : Type'} (x : type2 _141954 _141955 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term243 _141954 _141955 _141956 x s t) = (term244 _141954 _141955 _141956 x s t).
Proof. exact (MK_COMB (@lem8005178) (@lem8005177 _141954 _141955 _141956 x s t)). Qed.
Lemma lem8005180 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) : (term134 _141954 _141955 _141956 s t x x') = (term85 _141954 _141955 _141956 s t x x').
Proof. exact (eq_refl (term134 _141954 _141955 _141956 s t x x')). Qed.
Lemma lem8005181 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8005182 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) : (term245 _141954 _141955 _141956 s t x x') = (term246 _141954 _141955 _141956 s t x x').
Proof. exact (MK_COMB (@lem8005181) (@lem8005180 _141954 _141955 _141956 s t x x')). Qed.
Lemma lem8005183 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term102 _141954 _141955 _141956 s t) = (term102 _141954 _141955 _141956 s t).
Proof. exact (eq_refl (term102 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005184 {_141954 _141955 _141956 : Type'} (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term247 _141954 _141955 _141956 x x' s t) = (term248 _141954 _141955 _141956 x x' s t).
Proof. exact (MK_COMB (@lem8005182 _141954 _141955 _141956 s t x x') (@lem8005183 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005185 {_141954 _141955 _141956 : Type'} (x : type2 _141954 _141955 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term249 _141954 _141955 _141956 x s t) = (term250 _141954 _141955 _141956 x s t).
Proof. exact (fun_ext (fun x' : cart _141954 _141955 => @lem8005184 _141954 _141955 _141956 x x' s t)). Qed.
Lemma lem8005186 {_141954 _141955 : Type'} : (@ex (cart _141954 _141955)) = (@ex (cart _141954 _141955)).
Proof. exact (eq_refl (@ex (cart _141954 _141955))). Qed.
Lemma lem8005187 {_141954 _141955 _141956 : Type'} (x : type2 _141954 _141955 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term239 _141954 _141955 _141956 x s t) = (term251 _141954 _141955 _141956 x s t).
Proof. exact (MK_COMB (@lem8005186 _141954 _141955) (@lem8005185 _141954 _141955 _141956 x s t)). Qed.
Lemma lem8005188 {_141954 _141955 _141956 : Type'} (x : type2 _141954 _141955 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : ((term238 _141954 _141955 _141956 x s t) = (term239 _141954 _141955 _141956 x s t)) = ((term234 _141954 _141955 _141956 x s t) = (term251 _141954 _141955 _141956 x s t)).
Proof. exact (MK_COMB (@lem8005179 _141954 _141955 _141956 x s t) (@lem8005187 _141954 _141955 _141956 x s t)). Qed.
Lemma lem8005189 {_141954 _141955 _141956 : Type'} (x : type2 _141954 _141955 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term234 _141954 _141955 _141956 x s t) = (term251 _141954 _141955 _141956 x s t).
Proof. exact (EQ_MP (@lem8005188 _141954 _141955 _141956 x s t) (@lem8005169 _141954 _141955 _141956 x s t)). Qed.
Lemma lem8005191 {A : Type'} (P : A -> Prop) (Q : Prop) : (term178 A P Q) = (term179 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem8005192 {_141954 _141956 : Type'} (P : type24 _141954 _141956) (Q : Prop) : (term180 _141954 _141956 P Q) = (term181 _141954 _141956 P Q).
Proof. exact (@lem8005191 (cart _141954 _141956) P Q). Qed.
Lemma lem8005193 {_141954 _141955 _141956 : Type'} (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term252 _141954 _141955 _141956 x x' s t) = (term253 _141954 _141955 _141956 x x' s t).
Proof. exact (@lem8005192 _141954 _141956 (term83 _141954 _141955 _141956 s t x x') (term102 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005194 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) (y : cart _141954 _141956) : (term128 _141954 _141955 _141956 s t x x' y) = (term81 _141954 _141955 _141956 s t x x' y).
Proof. exact (eq_refl (term128 _141954 _141955 _141956 s t x x' y)). Qed.
Lemma lem8005195 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) : (term254 _141954 _141955 _141956 s t x x') = (term83 _141954 _141955 _141956 s t x x').
Proof. exact (fun_ext (fun y : cart _141954 _141956 => @lem8005194 _141954 _141955 _141956 s t x x' y)). Qed.
Lemma lem8005196 {_141954 _141956 : Type'} : (@ex (cart _141954 _141956)) = (@ex (cart _141954 _141956)).
Proof. exact (eq_refl (@ex (cart _141954 _141956))). Qed.
Lemma lem8005197 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) : (term255 _141954 _141955 _141956 s t x x') = (term85 _141954 _141955 _141956 s t x x').
Proof. exact (MK_COMB (@lem8005196 _141954 _141956) (@lem8005195 _141954 _141955 _141956 s t x x')). Qed.
Lemma lem8005198 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8005199 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) : (term256 _141954 _141955 _141956 s t x x') = (term246 _141954 _141955 _141956 s t x x').
Proof. exact (MK_COMB (@lem8005198) (@lem8005197 _141954 _141955 _141956 s t x x')). Qed.
Lemma lem8005200 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term102 _141954 _141955 _141956 s t) = (term102 _141954 _141955 _141956 s t).
Proof. exact (eq_refl (term102 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005201 {_141954 _141955 _141956 : Type'} (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term252 _141954 _141955 _141956 x x' s t) = (term248 _141954 _141955 _141956 x x' s t).
Proof. exact (MK_COMB (@lem8005199 _141954 _141955 _141956 s t x x') (@lem8005200 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005202 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8005203 {_141954 _141955 _141956 : Type'} (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term257 _141954 _141955 _141956 x x' s t) = (term258 _141954 _141955 _141956 x x' s t).
Proof. exact (MK_COMB (@lem8005202) (@lem8005201 _141954 _141955 _141956 x x' s t)). Qed.
Lemma lem8005204 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) (y : cart _141954 _141956) : (term128 _141954 _141955 _141956 s t x x' y) = (term81 _141954 _141955 _141956 s t x x' y).
Proof. exact (eq_refl (term128 _141954 _141955 _141956 s t x x' y)). Qed.
Lemma lem8005205 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8005206 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) (y : cart _141954 _141956) : (term259 _141954 _141955 _141956 s t x x' y) = (term260 _141954 _141955 _141956 s t x x' y).
Proof. exact (MK_COMB (@lem8005205) (@lem8005204 _141954 _141955 _141956 s t x x' y)). Qed.
Lemma lem8005207 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term102 _141954 _141955 _141956 s t) = (term102 _141954 _141955 _141956 s t).
Proof. exact (eq_refl (term102 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005208 {_141954 _141955 _141956 : Type'} (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) (y : cart _141954 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term261 _141954 _141955 _141956 x x' y s t) = (term262 _141954 _141955 _141956 x x' y s t).
Proof. exact (MK_COMB (@lem8005206 _141954 _141955 _141956 s t x x' y) (@lem8005207 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005209 {_141954 _141955 _141956 : Type'} (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term263 _141954 _141955 _141956 x x' s t) = (term264 _141954 _141955 _141956 x x' s t).
Proof. exact (fun_ext (fun y : cart _141954 _141956 => @lem8005208 _141954 _141955 _141956 x x' y s t)). Qed.
Lemma lem8005210 {_141954 _141956 : Type'} : (@ex (cart _141954 _141956)) = (@ex (cart _141954 _141956)).
Proof. exact (eq_refl (@ex (cart _141954 _141956))). Qed.
Lemma lem8005211 {_141954 _141955 _141956 : Type'} (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term253 _141954 _141955 _141956 x x' s t) = (term265 _141954 _141955 _141956 x x' s t).
Proof. exact (MK_COMB (@lem8005210 _141954 _141956) (@lem8005209 _141954 _141955 _141956 x x' s t)). Qed.
Lemma lem8005212 {_141954 _141955 _141956 : Type'} (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : ((term252 _141954 _141955 _141956 x x' s t) = (term253 _141954 _141955 _141956 x x' s t)) = ((term248 _141954 _141955 _141956 x x' s t) = (term265 _141954 _141955 _141956 x x' s t)).
Proof. exact (MK_COMB (@lem8005203 _141954 _141955 _141956 x x' s t) (@lem8005211 _141954 _141955 _141956 x x' s t)). Qed.
Lemma lem8005213 {_141954 _141955 _141956 : Type'} (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term248 _141954 _141955 _141956 x x' s t) = (term265 _141954 _141955 _141956 x x' s t).
Proof. exact (EQ_MP (@lem8005212 _141954 _141955 _141956 x x' s t) (@lem8005193 _141954 _141955 _141956 x x' s t)). Qed.
Lemma lem8005214 {_141954 _141955 _141956 : Type'} (x : type2 _141954 _141955 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term250 _141954 _141955 _141956 x s t) = (term266 _141954 _141955 _141956 x s t).
Proof. exact (fun_ext (fun x' : cart _141954 _141955 => @lem8005213 _141954 _141955 _141956 x x' s t)). Qed.
Lemma lem8005215 {_141954 _141955 : Type'} : (@ex (cart _141954 _141955)) = (@ex (cart _141954 _141955)).
Proof. exact (eq_refl (@ex (cart _141954 _141955))). Qed.
Lemma lem8005216 {_141954 _141955 _141956 : Type'} (x : type2 _141954 _141955 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term251 _141954 _141955 _141956 x s t) = (term267 _141954 _141955 _141956 x s t).
Proof. exact (MK_COMB (@lem8005215 _141954 _141955) (@lem8005214 _141954 _141955 _141956 x s t)). Qed.
Lemma lem8005217 {_141954 _141955 _141956 : Type'} (x : type2 _141954 _141955 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term234 _141954 _141955 _141956 x s t) = (term267 _141954 _141955 _141956 x s t).
Proof. exact (TRANS (@lem8005189 _141954 _141955 _141956 x s t) (@lem8005216 _141954 _141955 _141956 x s t)). Qed.
Lemma lem8005218 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term236 _141954 _141955 _141956 s t) = (term268 _141954 _141955 _141956 s t).
Proof. exact (fun_ext (fun x : type2 _141954 _141955 _141956 => @lem8005217 _141954 _141955 _141956 x s t)). Qed.
Lemma lem8005219 {_141954 _141955 _141956 : Type'} : (@ex (cart _141954 (finite_sum _141955 _141956))) = (@ex (cart _141954 (finite_sum _141955 _141956))).
Proof. exact (eq_refl (@ex (cart _141954 (finite_sum _141955 _141956)))). Qed.
Lemma lem8005220 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term237 _141954 _141955 _141956 s t) = (term269 _141954 _141955 _141956 s t).
Proof. exact (MK_COMB (@lem8005219 _141954 _141955 _141956) (@lem8005218 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005221 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term169 _141954 _141955 _141956 s t) = (term269 _141954 _141955 _141956 s t).
Proof. exact (TRANS (@lem8005165 _141954 _141955 _141956 s t) (@lem8005220 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005222 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term177 _141954 _141955 _141956 s t) = (term270 _141954 _141955 _141956 s t).
Proof. exact (MK_COMB (@lem8005141 _141954 _141955 _141956 s t) (@lem8005221 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005226 {A : Type'} (P : A -> Prop) (Q : Prop) : (term271 A P Q) = (term272 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem8005227 {_141954 _141955 : Type'} (P : type24 _141954 _141955) (Q : Prop) : (term273 _141954 _141955 P Q) = (term274 _141954 _141955 P Q).
Proof. exact (@lem8005226 (cart _141954 _141955) P Q). Qed.
Lemma lem8005228 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term275 _141954 _141955 _141956 s t) = (term276 _141954 _141955 _141956 s t).
Proof. exact (@lem8005227 _141954 _141955 (term218 _141954 _141955 _141956 s t) (term269 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005229 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) : (term277 _141954 _141955 _141956 s t x) = (term217 _141954 _141955 _141956 s x t).
Proof. exact (eq_refl (term277 _141954 _141955 _141956 s t x)). Qed.
Lemma lem8005230 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term278 _141954 _141955 _141956 s t) = (term218 _141954 _141955 _141956 s t).
Proof. exact (fun_ext (fun x : cart _141954 _141955 => @lem8005229 _141954 _141955 _141956 s x t)). Qed.
Lemma lem8005231 {_141954 _141955 : Type'} : (@ex (cart _141954 _141955)) = (@ex (cart _141954 _141955)).
Proof. exact (eq_refl (@ex (cart _141954 _141955))). Qed.
Lemma lem8005232 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term279 _141954 _141955 _141956 s t) = (term219 _141954 _141955 _141956 s t).
Proof. exact (MK_COMB (@lem8005231 _141954 _141955) (@lem8005230 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005233 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8005234 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term280 _141954 _141955 _141956 s t) = (term220 _141954 _141955 _141956 s t).
Proof. exact (MK_COMB (@lem8005233) (@lem8005232 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005235 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term269 _141954 _141955 _141956 s t) = (term269 _141954 _141955 _141956 s t).
Proof. exact (eq_refl (term269 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005236 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term275 _141954 _141955 _141956 s t) = (term270 _141954 _141955 _141956 s t).
Proof. exact (MK_COMB (@lem8005234 _141954 _141955 _141956 s t) (@lem8005235 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005237 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8005238 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term281 _141954 _141955 _141956 s t) = (term282 _141954 _141955 _141956 s t).
Proof. exact (MK_COMB (@lem8005237) (@lem8005236 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005239 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) : (term277 _141954 _141955 _141956 s t x) = (term217 _141954 _141955 _141956 s x t).
Proof. exact (eq_refl (term277 _141954 _141955 _141956 s t x)). Qed.
Lemma lem8005240 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8005241 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) : (term283 _141954 _141955 _141956 s t x) = (term284 _141954 _141955 _141956 s x t).
Proof. exact (MK_COMB (@lem8005240) (@lem8005239 _141954 _141955 _141956 s x t)). Qed.
Lemma lem8005242 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term269 _141954 _141955 _141956 s t) = (term269 _141954 _141955 _141956 s t).
Proof. exact (eq_refl (term269 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005243 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term285 _141954 _141955 _141956 x s t) = (term286 _141954 _141955 _141956 x s t).
Proof. exact (MK_COMB (@lem8005241 _141954 _141955 _141956 s x t) (@lem8005242 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005244 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term287 _141954 _141955 _141956 s t) = (term288 _141954 _141955 _141956 s t).
Proof. exact (fun_ext (fun x : cart _141954 _141955 => @lem8005243 _141954 _141955 _141956 x s t)). Qed.
Lemma lem8005245 {_141954 _141955 : Type'} : (@ex (cart _141954 _141955)) = (@ex (cart _141954 _141955)).
Proof. exact (eq_refl (@ex (cart _141954 _141955))). Qed.
Lemma lem8005246 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term276 _141954 _141955 _141956 s t) = (term289 _141954 _141955 _141956 s t).
Proof. exact (MK_COMB (@lem8005245 _141954 _141955) (@lem8005244 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005247 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : ((term275 _141954 _141955 _141956 s t) = (term276 _141954 _141955 _141956 s t)) = ((term270 _141954 _141955 _141956 s t) = (term289 _141954 _141955 _141956 s t)).
Proof. exact (MK_COMB (@lem8005238 _141954 _141955 _141956 s t) (@lem8005246 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005248 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term270 _141954 _141955 _141956 s t) = (term289 _141954 _141955 _141956 s t).
Proof. exact (EQ_MP (@lem8005247 _141954 _141955 _141956 s t) (@lem8005228 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005252 {A : Type'} (P : A -> Prop) (Q : Prop) : (term271 A P Q) = (term272 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem8005253 {_141954 _141956 : Type'} (P : type24 _141954 _141956) (Q : Prop) : (term273 _141954 _141956 P Q) = (term274 _141954 _141956 P Q).
Proof. exact (@lem8005252 (cart _141954 _141956) P Q). Qed.
Lemma lem8005254 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term290 _141954 _141955 _141956 x s t) = (term291 _141954 _141955 _141956 x s t).
Proof. exact (@lem8005253 _141954 _141956 (term216 _141954 _141955 _141956 s x t) (term269 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005255 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (x' : cart _141954 _141956) : (term292 _141954 _141955 _141956 s x t x') = (term214 _141954 _141955 _141956 s x t x').
Proof. exact (eq_refl (term292 _141954 _141955 _141956 s x t x')). Qed.
Lemma lem8005256 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) : (term293 _141954 _141955 _141956 s x t) = (term216 _141954 _141955 _141956 s x t).
Proof. exact (fun_ext (fun x' : cart _141954 _141956 => @lem8005255 _141954 _141955 _141956 s x t x')). Qed.
Lemma lem8005257 {_141954 _141956 : Type'} : (@ex (cart _141954 _141956)) = (@ex (cart _141954 _141956)).
Proof. exact (eq_refl (@ex (cart _141954 _141956))). Qed.
Lemma lem8005258 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) : (term294 _141954 _141955 _141956 s x t) = (term217 _141954 _141955 _141956 s x t).
Proof. exact (MK_COMB (@lem8005257 _141954 _141956) (@lem8005256 _141954 _141955 _141956 s x t)). Qed.
Lemma lem8005259 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8005260 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) : (term295 _141954 _141955 _141956 s x t) = (term284 _141954 _141955 _141956 s x t).
Proof. exact (MK_COMB (@lem8005259) (@lem8005258 _141954 _141955 _141956 s x t)). Qed.
Lemma lem8005261 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term269 _141954 _141955 _141956 s t) = (term269 _141954 _141955 _141956 s t).
Proof. exact (eq_refl (term269 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005262 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term290 _141954 _141955 _141956 x s t) = (term286 _141954 _141955 _141956 x s t).
Proof. exact (MK_COMB (@lem8005260 _141954 _141955 _141956 s x t) (@lem8005261 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005263 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8005264 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term296 _141954 _141955 _141956 x s t) = (term297 _141954 _141955 _141956 x s t).
Proof. exact (MK_COMB (@lem8005263) (@lem8005262 _141954 _141955 _141956 x s t)). Qed.
Lemma lem8005265 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (x' : cart _141954 _141956) : (term292 _141954 _141955 _141956 s x t x') = (term214 _141954 _141955 _141956 s x t x').
Proof. exact (eq_refl (term292 _141954 _141955 _141956 s x t x')). Qed.
Lemma lem8005266 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8005267 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (x' : cart _141954 _141956) : (term298 _141954 _141955 _141956 s x t x') = (term299 _141954 _141955 _141956 s x t x').
Proof. exact (MK_COMB (@lem8005266) (@lem8005265 _141954 _141955 _141956 s x t x')). Qed.
Lemma lem8005268 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term269 _141954 _141955 _141956 s t) = (term269 _141954 _141955 _141956 s t).
Proof. exact (eq_refl (term269 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005269 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (x' : cart _141954 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term300 _141954 _141955 _141956 x x' s t) = (term301 _141954 _141955 _141956 x x' s t).
Proof. exact (MK_COMB (@lem8005267 _141954 _141955 _141956 s x t x') (@lem8005268 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005270 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term302 _141954 _141955 _141956 x s t) = (term303 _141954 _141955 _141956 x s t).
Proof. exact (fun_ext (fun x' : cart _141954 _141956 => @lem8005269 _141954 _141955 _141956 x x' s t)). Qed.
Lemma lem8005271 {_141954 _141956 : Type'} : (@ex (cart _141954 _141956)) = (@ex (cart _141954 _141956)).
Proof. exact (eq_refl (@ex (cart _141954 _141956))). Qed.
Lemma lem8005272 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term291 _141954 _141955 _141956 x s t) = (term304 _141954 _141955 _141956 x s t).
Proof. exact (MK_COMB (@lem8005271 _141954 _141956) (@lem8005270 _141954 _141955 _141956 x s t)). Qed.
Lemma lem8005273 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : ((term290 _141954 _141955 _141956 x s t) = (term291 _141954 _141955 _141956 x s t)) = ((term286 _141954 _141955 _141956 x s t) = (term304 _141954 _141955 _141956 x s t)).
Proof. exact (MK_COMB (@lem8005264 _141954 _141955 _141956 x s t) (@lem8005272 _141954 _141955 _141956 x s t)). Qed.
Lemma lem8005274 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term286 _141954 _141955 _141956 x s t) = (term304 _141954 _141955 _141956 x s t).
Proof. exact (EQ_MP (@lem8005273 _141954 _141955 _141956 x s t) (@lem8005254 _141954 _141955 _141956 x s t)). Qed.
Lemma lem8005276 {A : Type'} (P : Prop) (Q : A -> Prop) : (term305 A P Q) = (term306 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem8005277 {_141954 _141955 _141956 : Type'} (P : Prop) (Q : type16 _141954 _141955 _141956) : (term307 _141954 _141955 _141956 P Q) = (term308 _141954 _141955 _141956 P Q).
Proof. exact (@lem8005276 (type2 _141954 _141955 _141956) P Q). Qed.
Lemma lem8005278 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (x' : cart _141954 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term309 _141954 _141955 _141956 x x' s t) = (term310 _141954 _141955 _141956 x x' s t).
Proof. exact (@lem8005277 _141954 _141955 _141956 (term214 _141954 _141955 _141956 s x t x') (term268 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005279 {_141954 _141955 _141956 : Type'} (x : type2 _141954 _141955 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term311 _141954 _141955 _141956 s t x) = (term267 _141954 _141955 _141956 x s t).
Proof. exact (eq_refl (term311 _141954 _141955 _141956 s t x)). Qed.
Lemma lem8005280 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term312 _141954 _141955 _141956 s t) = (term268 _141954 _141955 _141956 s t).
Proof. exact (fun_ext (fun x : type2 _141954 _141955 _141956 => @lem8005279 _141954 _141955 _141956 x s t)). Qed.
Lemma lem8005281 {_141954 _141955 _141956 : Type'} : (@ex (cart _141954 (finite_sum _141955 _141956))) = (@ex (cart _141954 (finite_sum _141955 _141956))).
Proof. exact (eq_refl (@ex (cart _141954 (finite_sum _141955 _141956)))). Qed.
Lemma lem8005282 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term313 _141954 _141955 _141956 s t) = (term269 _141954 _141955 _141956 s t).
Proof. exact (MK_COMB (@lem8005281 _141954 _141955 _141956) (@lem8005280 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005283 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (x' : cart _141954 _141956) : (term299 _141954 _141955 _141956 s x t x') = (term299 _141954 _141955 _141956 s x t x').
Proof. exact (eq_refl (term299 _141954 _141955 _141956 s x t x')). Qed.
Lemma lem8005284 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (x' : cart _141954 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term309 _141954 _141955 _141956 x x' s t) = (term301 _141954 _141955 _141956 x x' s t).
Proof. exact (MK_COMB (@lem8005283 _141954 _141955 _141956 s x t x') (@lem8005282 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005285 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8005286 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (x' : cart _141954 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term314 _141954 _141955 _141956 x x' s t) = (term315 _141954 _141955 _141956 x x' s t).
Proof. exact (MK_COMB (@lem8005285) (@lem8005284 _141954 _141955 _141956 x x' s t)). Qed.
Lemma lem8005287 {_141954 _141955 _141956 : Type'} (x : type2 _141954 _141955 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term311 _141954 _141955 _141956 s t x) = (term267 _141954 _141955 _141956 x s t).
Proof. exact (eq_refl (term311 _141954 _141955 _141956 s t x)). Qed.
Lemma lem8005288 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (x' : cart _141954 _141956) : (term299 _141954 _141955 _141956 s x t x') = (term299 _141954 _141955 _141956 s x t x').
Proof. exact (eq_refl (term299 _141954 _141955 _141956 s x t x')). Qed.
Lemma lem8005289 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (x' : cart _141954 _141956) (x'' : type2 _141954 _141955 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term316 _141954 _141955 _141956 x x' s t x'') = (term317 _141954 _141955 _141956 x x' x'' s t).
Proof. exact (MK_COMB (@lem8005288 _141954 _141955 _141956 s x t x') (@lem8005287 _141954 _141955 _141956 x'' s t)). Qed.
Lemma lem8005290 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (x' : cart _141954 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term318 _141954 _141955 _141956 x x' s t) = (term319 _141954 _141955 _141956 x x' s t).
Proof. exact (fun_ext (fun x'' : type2 _141954 _141955 _141956 => @lem8005289 _141954 _141955 _141956 x x' x'' s t)). Qed.
Lemma lem8005291 {_141954 _141955 _141956 : Type'} : (@ex (cart _141954 (finite_sum _141955 _141956))) = (@ex (cart _141954 (finite_sum _141955 _141956))).
Proof. exact (eq_refl (@ex (cart _141954 (finite_sum _141955 _141956)))). Qed.
Lemma lem8005292 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (x' : cart _141954 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term310 _141954 _141955 _141956 x x' s t) = (term320 _141954 _141955 _141956 x x' s t).
Proof. exact (MK_COMB (@lem8005291 _141954 _141955 _141956) (@lem8005290 _141954 _141955 _141956 x x' s t)). Qed.
Lemma lem8005293 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (x' : cart _141954 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : ((term309 _141954 _141955 _141956 x x' s t) = (term310 _141954 _141955 _141956 x x' s t)) = ((term301 _141954 _141955 _141956 x x' s t) = (term320 _141954 _141955 _141956 x x' s t)).
Proof. exact (MK_COMB (@lem8005286 _141954 _141955 _141956 x x' s t) (@lem8005292 _141954 _141955 _141956 x x' s t)). Qed.
Lemma lem8005294 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (x' : cart _141954 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term301 _141954 _141955 _141956 x x' s t) = (term320 _141954 _141955 _141956 x x' s t).
Proof. exact (EQ_MP (@lem8005293 _141954 _141955 _141956 x x' s t) (@lem8005278 _141954 _141955 _141956 x x' s t)). Qed.
Lemma lem8005296 {A : Type'} (P : Prop) (Q : A -> Prop) : (term305 A P Q) = (term306 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem8005297 {_141954 _141955 : Type'} (P : Prop) (Q : type24 _141954 _141955) : (term321 _141954 _141955 P Q) = (term322 _141954 _141955 P Q).
Proof. exact (@lem8005296 (cart _141954 _141955) P Q). Qed.
Lemma lem8005298 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (x' : cart _141954 _141956) (x'' : type2 _141954 _141955 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term323 _141954 _141955 _141956 x x' x'' s t) = (term324 _141954 _141955 _141956 x x' x'' s t).
Proof. exact (@lem8005297 _141954 _141955 (term214 _141954 _141955 _141956 s x t x') (term266 _141954 _141955 _141956 x'' s t)). Qed.
Lemma lem8005299 {_141954 _141955 _141956 : Type'} (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term325 _141954 _141955 _141956 x s t x') = (term265 _141954 _141955 _141956 x x' s t).
Proof. exact (eq_refl (term325 _141954 _141955 _141956 x s t x')). Qed.
Lemma lem8005300 {_141954 _141955 _141956 : Type'} (x : type2 _141954 _141955 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term326 _141954 _141955 _141956 x s t) = (term266 _141954 _141955 _141956 x s t).
Proof. exact (fun_ext (fun x' : cart _141954 _141955 => @lem8005299 _141954 _141955 _141956 x x' s t)). Qed.
Lemma lem8005301 {_141954 _141955 : Type'} : (@ex (cart _141954 _141955)) = (@ex (cart _141954 _141955)).
Proof. exact (eq_refl (@ex (cart _141954 _141955))). Qed.
Lemma lem8005302 {_141954 _141955 _141956 : Type'} (x : type2 _141954 _141955 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term327 _141954 _141955 _141956 x s t) = (term267 _141954 _141955 _141956 x s t).
Proof. exact (MK_COMB (@lem8005301 _141954 _141955) (@lem8005300 _141954 _141955 _141956 x s t)). Qed.
Lemma lem8005303 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (x' : cart _141954 _141956) : (term299 _141954 _141955 _141956 s x t x') = (term299 _141954 _141955 _141956 s x t x').
Proof. exact (eq_refl (term299 _141954 _141955 _141956 s x t x')). Qed.
Lemma lem8005304 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (x' : cart _141954 _141956) (x'' : type2 _141954 _141955 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term323 _141954 _141955 _141956 x x' x'' s t) = (term317 _141954 _141955 _141956 x x' x'' s t).
Proof. exact (MK_COMB (@lem8005303 _141954 _141955 _141956 s x t x') (@lem8005302 _141954 _141955 _141956 x'' s t)). Qed.
Lemma lem8005305 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8005306 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (x' : cart _141954 _141956) (x'' : type2 _141954 _141955 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term328 _141954 _141955 _141956 x x' x'' s t) = (term329 _141954 _141955 _141956 x x' x'' s t).
Proof. exact (MK_COMB (@lem8005305) (@lem8005304 _141954 _141955 _141956 x x' x'' s t)). Qed.
Lemma lem8005307 {_141954 _141955 _141956 : Type'} (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term325 _141954 _141955 _141956 x s t x') = (term265 _141954 _141955 _141956 x x' s t).
Proof. exact (eq_refl (term325 _141954 _141955 _141956 x s t x')). Qed.
Lemma lem8005308 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (x' : cart _141954 _141956) : (term299 _141954 _141955 _141956 s x t x') = (term299 _141954 _141955 _141956 s x t x').
Proof. exact (eq_refl (term299 _141954 _141955 _141956 s x t x')). Qed.
Lemma lem8005309 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (x' : cart _141954 _141956) (x'' : type2 _141954 _141955 _141956) (x''' : cart _141954 _141955) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term330 _141954 _141955 _141956 x x' x'' s t x''') = (term331 _141954 _141955 _141956 x x' x'' x''' s t).
Proof. exact (MK_COMB (@lem8005308 _141954 _141955 _141956 s x t x') (@lem8005307 _141954 _141955 _141956 x'' x''' s t)). Qed.
Lemma lem8005310 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (x' : cart _141954 _141956) (x'' : type2 _141954 _141955 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term332 _141954 _141955 _141956 x x' x'' s t) = (term333 _141954 _141955 _141956 x x' x'' s t).
Proof. exact (fun_ext (fun x''' : cart _141954 _141955 => @lem8005309 _141954 _141955 _141956 x x' x'' x''' s t)). Qed.
Lemma lem8005311 {_141954 _141955 : Type'} : (@ex (cart _141954 _141955)) = (@ex (cart _141954 _141955)).
Proof. exact (eq_refl (@ex (cart _141954 _141955))). Qed.
Lemma lem8005312 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (x' : cart _141954 _141956) (x'' : type2 _141954 _141955 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term324 _141954 _141955 _141956 x x' x'' s t) = (term334 _141954 _141955 _141956 x x' x'' s t).
Proof. exact (MK_COMB (@lem8005311 _141954 _141955) (@lem8005310 _141954 _141955 _141956 x x' x'' s t)). Qed.
Lemma lem8005313 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (x' : cart _141954 _141956) (x'' : type2 _141954 _141955 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : ((term323 _141954 _141955 _141956 x x' x'' s t) = (term324 _141954 _141955 _141956 x x' x'' s t)) = ((term317 _141954 _141955 _141956 x x' x'' s t) = (term334 _141954 _141955 _141956 x x' x'' s t)).
Proof. exact (MK_COMB (@lem8005306 _141954 _141955 _141956 x x' x'' s t) (@lem8005312 _141954 _141955 _141956 x x' x'' s t)). Qed.
Lemma lem8005314 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (x' : cart _141954 _141956) (x'' : type2 _141954 _141955 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term317 _141954 _141955 _141956 x x' x'' s t) = (term334 _141954 _141955 _141956 x x' x'' s t).
Proof. exact (EQ_MP (@lem8005313 _141954 _141955 _141956 x x' x'' s t) (@lem8005298 _141954 _141955 _141956 x x' x'' s t)). Qed.
Lemma lem8005316 {A : Type'} (P : Prop) (Q : A -> Prop) : (term305 A P Q) = (term306 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem8005317 {_141954 _141956 : Type'} (P : Prop) (Q : type24 _141954 _141956) : (term321 _141954 _141956 P Q) = (term322 _141954 _141956 P Q).
Proof. exact (@lem8005316 (cart _141954 _141956) P Q). Qed.
Lemma lem8005318 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (x' : cart _141954 _141956) (x'' : type2 _141954 _141955 _141956) (x''' : cart _141954 _141955) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term335 _141954 _141955 _141956 x x' x'' x''' s t) = (term336 _141954 _141955 _141956 x x' x'' x''' s t).
Proof. exact (@lem8005317 _141954 _141956 (term214 _141954 _141955 _141956 s x t x') (term264 _141954 _141955 _141956 x'' x''' s t)). Qed.
Lemma lem8005319 {_141954 _141955 _141956 : Type'} (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) (y : cart _141954 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term337 _141954 _141955 _141956 x x' s t y) = (term262 _141954 _141955 _141956 x x' y s t).
Proof. exact (eq_refl (term337 _141954 _141955 _141956 x x' s t y)). Qed.
Lemma lem8005320 {_141954 _141955 _141956 : Type'} (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term338 _141954 _141955 _141956 x x' s t) = (term264 _141954 _141955 _141956 x x' s t).
Proof. exact (fun_ext (fun y : cart _141954 _141956 => @lem8005319 _141954 _141955 _141956 x x' y s t)). Qed.
Lemma lem8005321 {_141954 _141956 : Type'} : (@ex (cart _141954 _141956)) = (@ex (cart _141954 _141956)).
Proof. exact (eq_refl (@ex (cart _141954 _141956))). Qed.
Lemma lem8005322 {_141954 _141955 _141956 : Type'} (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term339 _141954 _141955 _141956 x x' s t) = (term265 _141954 _141955 _141956 x x' s t).
Proof. exact (MK_COMB (@lem8005321 _141954 _141956) (@lem8005320 _141954 _141955 _141956 x x' s t)). Qed.
Lemma lem8005323 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (x' : cart _141954 _141956) : (term299 _141954 _141955 _141956 s x t x') = (term299 _141954 _141955 _141956 s x t x').
Proof. exact (eq_refl (term299 _141954 _141955 _141956 s x t x')). Qed.
Lemma lem8005324 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (x' : cart _141954 _141956) (x'' : type2 _141954 _141955 _141956) (x''' : cart _141954 _141955) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term335 _141954 _141955 _141956 x x' x'' x''' s t) = (term331 _141954 _141955 _141956 x x' x'' x''' s t).
Proof. exact (MK_COMB (@lem8005323 _141954 _141955 _141956 s x t x') (@lem8005322 _141954 _141955 _141956 x'' x''' s t)). Qed.
Lemma lem8005325 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8005326 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (x' : cart _141954 _141956) (x'' : type2 _141954 _141955 _141956) (x''' : cart _141954 _141955) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term340 _141954 _141955 _141956 x x' x'' x''' s t) = (term341 _141954 _141955 _141956 x x' x'' x''' s t).
Proof. exact (MK_COMB (@lem8005325) (@lem8005324 _141954 _141955 _141956 x x' x'' x''' s t)). Qed.
Lemma lem8005327 {_141954 _141955 _141956 : Type'} (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) (y : cart _141954 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term337 _141954 _141955 _141956 x x' s t y) = (term262 _141954 _141955 _141956 x x' y s t).
Proof. exact (eq_refl (term337 _141954 _141955 _141956 x x' s t y)). Qed.
Lemma lem8005328 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (x' : cart _141954 _141956) : (term299 _141954 _141955 _141956 s x t x') = (term299 _141954 _141955 _141956 s x t x').
Proof. exact (eq_refl (term299 _141954 _141955 _141956 s x t x')). Qed.
Lemma lem8005329 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (x' : cart _141954 _141956) (x'' : type2 _141954 _141955 _141956) (x''' : cart _141954 _141955) (y : cart _141954 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term342 _141954 _141955 _141956 x x' x'' x''' s t y) = (term343 _141954 _141955 _141956 x x' x'' x''' y s t).
Proof. exact (MK_COMB (@lem8005328 _141954 _141955 _141956 s x t x') (@lem8005327 _141954 _141955 _141956 x'' x''' y s t)). Qed.
Lemma lem8005330 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (x' : cart _141954 _141956) (x'' : type2 _141954 _141955 _141956) (x''' : cart _141954 _141955) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term344 _141954 _141955 _141956 x x' x'' x''' s t) = (term345 _141954 _141955 _141956 x x' x'' x''' s t).
Proof. exact (fun_ext (fun y : cart _141954 _141956 => @lem8005329 _141954 _141955 _141956 x x' x'' x''' y s t)). Qed.
Lemma lem8005331 {_141954 _141956 : Type'} : (@ex (cart _141954 _141956)) = (@ex (cart _141954 _141956)).
Proof. exact (eq_refl (@ex (cart _141954 _141956))). Qed.
Lemma lem8005332 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (x' : cart _141954 _141956) (x'' : type2 _141954 _141955 _141956) (x''' : cart _141954 _141955) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term336 _141954 _141955 _141956 x x' x'' x''' s t) = (term346 _141954 _141955 _141956 x x' x'' x''' s t).
Proof. exact (MK_COMB (@lem8005331 _141954 _141956) (@lem8005330 _141954 _141955 _141956 x x' x'' x''' s t)). Qed.
Lemma lem8005333 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (x' : cart _141954 _141956) (x'' : type2 _141954 _141955 _141956) (x''' : cart _141954 _141955) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : ((term335 _141954 _141955 _141956 x x' x'' x''' s t) = (term336 _141954 _141955 _141956 x x' x'' x''' s t)) = ((term331 _141954 _141955 _141956 x x' x'' x''' s t) = (term346 _141954 _141955 _141956 x x' x'' x''' s t)).
Proof. exact (MK_COMB (@lem8005326 _141954 _141955 _141956 x x' x'' x''' s t) (@lem8005332 _141954 _141955 _141956 x x' x'' x''' s t)). Qed.
Lemma lem8005334 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (x' : cart _141954 _141956) (x'' : type2 _141954 _141955 _141956) (x''' : cart _141954 _141955) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term331 _141954 _141955 _141956 x x' x'' x''' s t) = (term346 _141954 _141955 _141956 x x' x'' x''' s t).
Proof. exact (EQ_MP (@lem8005333 _141954 _141955 _141956 x x' x'' x''' s t) (@lem8005318 _141954 _141955 _141956 x x' x'' x''' s t)). Qed.
Lemma lem8005335 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (x' : cart _141954 _141956) (x'' : type2 _141954 _141955 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term333 _141954 _141955 _141956 x x' x'' s t) = (term347 _141954 _141955 _141956 x x' x'' s t).
Proof. exact (fun_ext (fun x''' : cart _141954 _141955 => @lem8005334 _141954 _141955 _141956 x x' x'' x''' s t)). Qed.
Lemma lem8005336 {_141954 _141955 : Type'} : (@ex (cart _141954 _141955)) = (@ex (cart _141954 _141955)).
Proof. exact (eq_refl (@ex (cart _141954 _141955))). Qed.
Lemma lem8005337 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (x' : cart _141954 _141956) (x'' : type2 _141954 _141955 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term334 _141954 _141955 _141956 x x' x'' s t) = (term348 _141954 _141955 _141956 x x' x'' s t).
Proof. exact (MK_COMB (@lem8005336 _141954 _141955) (@lem8005335 _141954 _141955 _141956 x x' x'' s t)). Qed.
Lemma lem8005338 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (x' : cart _141954 _141956) (x'' : type2 _141954 _141955 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term317 _141954 _141955 _141956 x x' x'' s t) = (term348 _141954 _141955 _141956 x x' x'' s t).
Proof. exact (TRANS (@lem8005314 _141954 _141955 _141956 x x' x'' s t) (@lem8005337 _141954 _141955 _141956 x x' x'' s t)). Qed.
Lemma lem8005339 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (x' : cart _141954 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term319 _141954 _141955 _141956 x x' s t) = (term349 _141954 _141955 _141956 x x' s t).
Proof. exact (fun_ext (fun x'' : type2 _141954 _141955 _141956 => @lem8005338 _141954 _141955 _141956 x x' x'' s t)). Qed.
Lemma lem8005340 {_141954 _141955 _141956 : Type'} : (@ex (cart _141954 (finite_sum _141955 _141956))) = (@ex (cart _141954 (finite_sum _141955 _141956))).
Proof. exact (eq_refl (@ex (cart _141954 (finite_sum _141955 _141956)))). Qed.
Lemma lem8005341 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (x' : cart _141954 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term320 _141954 _141955 _141956 x x' s t) = (term350 _141954 _141955 _141956 x x' s t).
Proof. exact (MK_COMB (@lem8005340 _141954 _141955 _141956) (@lem8005339 _141954 _141955 _141956 x x' s t)). Qed.
Lemma lem8005342 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (x' : cart _141954 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term301 _141954 _141955 _141956 x x' s t) = (term350 _141954 _141955 _141956 x x' s t).
Proof. exact (TRANS (@lem8005294 _141954 _141955 _141956 x x' s t) (@lem8005341 _141954 _141955 _141956 x x' s t)). Qed.
Lemma lem8005343 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term303 _141954 _141955 _141956 x s t) = (term351 _141954 _141955 _141956 x s t).
Proof. exact (fun_ext (fun x' : cart _141954 _141956 => @lem8005342 _141954 _141955 _141956 x x' s t)). Qed.
Lemma lem8005344 {_141954 _141956 : Type'} : (@ex (cart _141954 _141956)) = (@ex (cart _141954 _141956)).
Proof. exact (eq_refl (@ex (cart _141954 _141956))). Qed.
Lemma lem8005345 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term304 _141954 _141955 _141956 x s t) = (term352 _141954 _141955 _141956 x s t).
Proof. exact (MK_COMB (@lem8005344 _141954 _141956) (@lem8005343 _141954 _141955 _141956 x s t)). Qed.
Lemma lem8005346 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term286 _141954 _141955 _141956 x s t) = (term352 _141954 _141955 _141956 x s t).
Proof. exact (TRANS (@lem8005274 _141954 _141955 _141956 x s t) (@lem8005345 _141954 _141955 _141956 x s t)). Qed.
Lemma lem8005347 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term288 _141954 _141955 _141956 s t) = (term353 _141954 _141955 _141956 s t).
Proof. exact (fun_ext (fun x : cart _141954 _141955 => @lem8005346 _141954 _141955 _141956 x s t)). Qed.
Lemma lem8005348 {_141954 _141955 : Type'} : (@ex (cart _141954 _141955)) = (@ex (cart _141954 _141955)).
Proof. exact (eq_refl (@ex (cart _141954 _141955))). Qed.
Lemma lem8005349 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term289 _141954 _141955 _141956 s t) = (term354 _141954 _141955 _141956 s t).
Proof. exact (MK_COMB (@lem8005348 _141954 _141955) (@lem8005347 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005350 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term270 _141954 _141955 _141956 s t) = (term354 _141954 _141955 _141956 s t).
Proof. exact (TRANS (@lem8005248 _141954 _141955 _141956 s t) (@lem8005349 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005352 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term177 _141954 _141955 _141956 s t) = (term354 _141954 _141955 _141956 s t).
Proof. exact (TRANS (@lem8005222 _141954 _141955 _141956 s t) (@lem8005350 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005353 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term116 _141954 _141955 _141956 s t) = (term354 _141954 _141955 _141956 s t).
Proof. exact (TRANS (@lem8004951 _141954 _141955 _141956 s t) (@lem8005352 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005354 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (h1 : term116 _141954 _141955 _141956 s t) : term354 _141954 _141955 _141956 s t.
Proof. exact (EQ_MP (@lem8005353 _141954 _141955 _141956 s t) (@lem8004835 _141954 _141955 _141956 s t h1)). Qed.
Lemma lem8005355 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (s : type24 _141954 _141955) (t : type24 _141954 _141956) (h1 : term352 _141954 _141955 _141956 x s t) : term352 _141954 _141955 _141956 x s t.
Proof. exact (h1). Qed.
Lemma lem8005356 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (x' : cart _141954 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) (h1 : term350 _141954 _141955 _141956 x x' s t) : term350 _141954 _141955 _141956 x x' s t.
Proof. exact (h1). Qed.
Lemma lem8005357 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (x' : cart _141954 _141956) (x'' : type2 _141954 _141955 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) (h1 : term348 _141954 _141955 _141956 x x' x'' s t) : term348 _141954 _141955 _141956 x x' x'' s t.
Proof. exact (h1). Qed.
Lemma lem8005358 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (x' : cart _141954 _141956) (x'' : type2 _141954 _141955 _141956) (x''' : cart _141954 _141955) (s : type24 _141954 _141955) (t : type24 _141954 _141956) (h1 : term346 _141954 _141955 _141956 x x' x'' x''' s t) : term346 _141954 _141955 _141956 x x' x'' x''' s t.
Proof. exact (h1). Qed.
Lemma lem8005359 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (x' : cart _141954 _141956) (x'' : type2 _141954 _141955 _141956) (x''' : cart _141954 _141955) (y : cart _141954 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) (h1 : term343 _141954 _141955 _141956 x x' x'' x''' y s t) : term343 _141954 _141955 _141956 x x' x'' x''' y s t.
Proof. exact (h1). Qed.
Lemma lem8005364 {_141954 _141956 : Type'} (t : type24 _141954 _141956) (x : cart _141954 _141956) : (term97 _141954 _141956 t x) = (term97 _141954 _141956 t x).
Proof. exact (eq_refl (term97 _141954 _141956 t x)). Qed.
Lemma lem8005365 {_141954 _141956 : Type'} (t : type24 _141954 _141956) : (term99 _141954 _141956 t) = (term99 _141954 _141956 t).
Proof. exact (fun_ext (fun x : cart _141954 _141956 => @lem8005364 _141954 _141956 t x)). Qed.
Lemma lem8005366 {_141954 _141956 : Type'} : (@all (cart _141954 _141956)) = (@all (cart _141954 _141956)).
Proof. exact (eq_refl (@all (cart _141954 _141956))). Qed.
Lemma lem8005367 {_141954 _141956 : Type'} (t : type24 _141954 _141956) : (term100 _141954 _141956 t) = (term100 _141954 _141956 t).
Proof. exact (MK_COMB (@lem8005366 _141954 _141956) (@lem8005365 _141954 _141956 t)). Qed.
Lemma lem8005372 {_141954 _141955 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) : (term97 _141954 _141955 s x) = (term97 _141954 _141955 s x).
Proof. exact (eq_refl (term97 _141954 _141955 s x)). Qed.
Lemma lem8005373 {_141954 _141955 : Type'} (s : type24 _141954 _141955) : (term99 _141954 _141955 s) = (term99 _141954 _141955 s).
Proof. exact (fun_ext (fun x : cart _141954 _141955 => @lem8005372 _141954 _141955 s x)). Qed.
Lemma lem8005374 {_141954 _141955 : Type'} : (@all (cart _141954 _141955)) = (@all (cart _141954 _141955)).
Proof. exact (eq_refl (@all (cart _141954 _141955))). Qed.
Lemma lem8005375 {_141954 _141955 : Type'} (s : type24 _141954 _141955) : (term100 _141954 _141955 s) = (term100 _141954 _141955 s).
Proof. exact (MK_COMB (@lem8005374 _141954 _141955) (@lem8005373 _141954 _141955 s)). Qed.
Lemma lem8005376 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8005377 {_141954 _141955 : Type'} (s : type24 _141954 _141955) : (term101 _141954 _141955 s) = (term101 _141954 _141955 s).
Proof. exact (MK_COMB (@lem8005376) (@lem8005375 _141954 _141955 s)). Qed.
Lemma lem8005378 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term102 _141954 _141955 _141956 s t) = (term102 _141954 _141955 _141956 s t).
Proof. exact (MK_COMB (@lem8005377 _141954 _141955 s) (@lem8005367 _141954 _141956 t)). Qed.
Lemma lem8005401 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x'' : type2 _141954 _141955 _141956) (x''' : cart _141954 _141955) (y : cart _141954 _141956) : (term260 _141954 _141955 _141956 s t x'' x''' y) = (term260 _141954 _141955 _141956 s t x'' x''' y).
Proof. exact (eq_refl (term260 _141954 _141955 _141956 s t x'' x''' y)). Qed.
Lemma lem8005402 {_141954 _141955 _141956 : Type'} (x'' : type2 _141954 _141955 _141956) (x''' : cart _141954 _141955) (y : cart _141954 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term262 _141954 _141955 _141956 x'' x''' y s t) = (term262 _141954 _141955 _141956 x'' x''' y s t).
Proof. exact (MK_COMB (@lem8005401 _141954 _141955 _141956 s t x'' x''' y) (@lem8005378 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005411 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (x' : cart _141954 _141956) : (term67 _141954 _141955 _141956 s x t x') = (term67 _141954 _141955 _141956 s x t x').
Proof. exact (eq_refl (term67 _141954 _141955 _141956 s x t x')). Qed.
Lemma lem8005438 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) (y : cart _141954 _141956) : (term123 _141954 _141955 _141956 s t x x' y) = (term123 _141954 _141955 _141956 s t x x' y).
Proof. exact (eq_refl (term123 _141954 _141955 _141956 s t x x' y)). Qed.
Lemma lem8005439 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) : (term131 _141954 _141955 _141956 s t x x') = (term131 _141954 _141955 _141956 s t x x').
Proof. exact (fun_ext (fun y : cart _141954 _141956 => @lem8005438 _141954 _141955 _141956 s t x x' y)). Qed.
Lemma lem8005440 {_141954 _141956 : Type'} : (@all (cart _141954 _141956)) = (@all (cart _141954 _141956)).
Proof. exact (eq_refl (@all (cart _141954 _141956))). Qed.
Lemma lem8005441 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) : (term132 _141954 _141955 _141956 s t x x') = (term132 _141954 _141955 _141956 s t x x').
Proof. exact (MK_COMB (@lem8005440 _141954 _141956) (@lem8005439 _141954 _141955 _141956 s t x x')). Qed.
Lemma lem8005442 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) : (term137 _141954 _141955 _141956 s t x) = (term137 _141954 _141955 _141956 s t x).
Proof. exact (fun_ext (fun x' : cart _141954 _141955 => @lem8005441 _141954 _141955 _141956 s t x x')). Qed.
Lemma lem8005443 {_141954 _141955 : Type'} : (@all (cart _141954 _141955)) = (@all (cart _141954 _141955)).
Proof. exact (eq_refl (@all (cart _141954 _141955))). Qed.
Lemma lem8005444 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) : (term138 _141954 _141955 _141956 s t x) = (term138 _141954 _141955 _141956 s t x).
Proof. exact (MK_COMB (@lem8005443 _141954 _141955) (@lem8005442 _141954 _141955 _141956 s t x)). Qed.
Lemma lem8005445 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term149 _141954 _141955 _141956 s t) = (term149 _141954 _141955 _141956 s t).
Proof. exact (fun_ext (fun x : type2 _141954 _141955 _141956 => @lem8005444 _141954 _141955 _141956 s t x)). Qed.
Lemma lem8005446 {_141954 _141955 _141956 : Type'} : (@all (cart _141954 (finite_sum _141955 _141956))) = (@all (cart _141954 (finite_sum _141955 _141956))).
Proof. exact (eq_refl (@all (cart _141954 (finite_sum _141955 _141956)))). Qed.
Lemma lem8005447 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term150 _141954 _141955 _141956 s t) = (term150 _141954 _141955 _141956 s t).
Proof. exact (MK_COMB (@lem8005446 _141954 _141955 _141956) (@lem8005445 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005448 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8005449 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term171 _141954 _141955 _141956 s t) = (term171 _141954 _141955 _141956 s t).
Proof. exact (MK_COMB (@lem8005448) (@lem8005447 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005450 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (x' : cart _141954 _141956) : (term214 _141954 _141955 _141956 s x t x') = (term214 _141954 _141955 _141956 s x t x').
Proof. exact (MK_COMB (@lem8005449 _141954 _141955 _141956 s t) (@lem8005411 _141954 _141955 _141956 s x t x')). Qed.
Lemma lem8005451 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8005452 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (x' : cart _141954 _141956) : (term299 _141954 _141955 _141956 s x t x') = (term299 _141954 _141955 _141956 s x t x').
Proof. exact (MK_COMB (@lem8005451) (@lem8005450 _141954 _141955 _141956 s x t x')). Qed.
Lemma lem8005453 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (x' : cart _141954 _141956) (x'' : type2 _141954 _141955 _141956) (x''' : cart _141954 _141955) (y : cart _141954 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term343 _141954 _141955 _141956 x x' x'' x''' y s t) = (term343 _141954 _141955 _141956 x x' x'' x''' y s t).
Proof. exact (MK_COMB (@lem8005452 _141954 _141955 _141956 s x t x') (@lem8005402 _141954 _141955 _141956 x'' x''' y s t)). Qed.
Lemma lem8005454 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (x' : cart _141954 _141956) (x'' : type2 _141954 _141955 _141956) (x''' : cart _141954 _141955) (y : cart _141954 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) (h1 : term343 _141954 _141955 _141956 x x' x'' x''' y s t) : term343 _141954 _141955 _141956 x x' x'' x''' y s t.
Proof. exact (EQ_MP (@lem8005453 _141954 _141955 _141956 x x' x'' x''' y s t) (@lem8005359 _141954 _141955 _141956 x x' x'' x''' y s t h1)). Qed.
Lemma lem8005455 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (x' : cart _141954 _141956) (h1 : term214 _141954 _141955 _141956 s x t x') : term214 _141954 _141955 _141956 s x t x'.
Proof. exact (h1). Qed.
Lemma lem8005456 {_141954 _141955 _141956 : Type'} (x'' : type2 _141954 _141955 _141956) (x''' : cart _141954 _141955) (y : cart _141954 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) (h1 : term262 _141954 _141955 _141956 x'' x''' y s t) : term262 _141954 _141955 _141956 x'' x''' y s t.
Proof. exact (h1). Qed.
Lemma lem8005457 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (x' : cart _141954 _141956) (h1 : term214 _141954 _141955 _141956 s x t x') : term67 _141954 _141955 _141956 s x t x'.
Proof. exact (proj2 (@lem8005455 _141954 _141955 _141956 s x t x' h1)). Qed.
Lemma lem8005458 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (x' : cart _141954 _141956) (h1 : term214 _141954 _141955 _141956 s x t x') : term150 _141954 _141955 _141956 s t.
Proof. exact (proj1 (@lem8005455 _141954 _141955 _141956 s x t x' h1)). Qed.
Lemma lem8005461 {_141954 _141955 _141956 : Type'} (x'' : type2 _141954 _141955 _141956) (x''' : cart _141954 _141955) (y : cart _141954 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) (h1 : term262 _141954 _141955 _141956 x'' x''' y s t) : term102 _141954 _141955 _141956 s t.
Proof. exact (proj2 (@lem8005456 _141954 _141955 _141956 x'' x''' y s t h1)). Qed.
Lemma lem8005462 {_141954 _141955 _141956 : Type'} (x'' : type2 _141954 _141955 _141956) (x''' : cart _141954 _141955) (y : cart _141954 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) (h1 : term262 _141954 _141955 _141956 x'' x''' y s t) : term81 _141954 _141955 _141956 s t x'' x''' y.
Proof. exact (proj1 (@lem8005456 _141954 _141955 _141956 x'' x''' y s t h1)). Qed.
Lemma lem8005464 {_141954 _141955 _141956 : Type'} (x'' : type2 _141954 _141955 _141956) (x''' : cart _141954 _141955) (y : cart _141954 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) (h1 : term262 _141954 _141955 _141956 x'' x''' y s t) : term67 _141954 _141955 _141956 s x''' t y.
Proof. exact (proj1 (@lem8005462 _141954 _141955 _141956 x'' x''' y s t h1)). Qed.
Lemma lem8005467 {_141954 _141955 : Type'} (s : type24 _141954 _141955) (h1 : term100 _141954 _141955 s) : term100 _141954 _141955 s.
Proof. exact (h1). Qed.
Lemma lem8005468 {_141954 _141956 : Type'} (t : type24 _141954 _141956) (h1 : term100 _141954 _141956 t) : term100 _141954 _141956 t.
Proof. exact (h1). Qed.
Lemma lem8005482 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) (y : cart _141954 _141956) : (term123 _141954 _141955 _141956 s t x x' y) = (term123 _141954 _141955 _141956 s t x x' y).
Proof. exact (eq_refl (term123 _141954 _141955 _141956 s t x x' y)). Qed.
Lemma lem8005483 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) : (term131 _141954 _141955 _141956 s t x x') = (term131 _141954 _141955 _141956 s t x x').
Proof. exact (fun_ext (fun y : cart _141954 _141956 => @lem8005482 _141954 _141955 _141956 s t x x' y)). Qed.
Lemma lem8005484 {_141954 _141956 : Type'} : (@all (cart _141954 _141956)) = (@all (cart _141954 _141956)).
Proof. exact (eq_refl (@all (cart _141954 _141956))). Qed.
Lemma lem8005485 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) (x' : cart _141954 _141955) : (term132 _141954 _141955 _141956 s t x x') = (term132 _141954 _141955 _141956 s t x x').
Proof. exact (MK_COMB (@lem8005484 _141954 _141956) (@lem8005483 _141954 _141955 _141956 s t x x')). Qed.
Lemma lem8005486 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) : (term137 _141954 _141955 _141956 s t x) = (term137 _141954 _141955 _141956 s t x).
Proof. exact (fun_ext (fun x' : cart _141954 _141955 => @lem8005485 _141954 _141955 _141956 s t x x')). Qed.
Lemma lem8005487 {_141954 _141955 : Type'} : (@all (cart _141954 _141955)) = (@all (cart _141954 _141955)).
Proof. exact (eq_refl (@all (cart _141954 _141955))). Qed.
Lemma lem8005488 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (x : type2 _141954 _141955 _141956) : (term138 _141954 _141955 _141956 s t x) = (term138 _141954 _141955 _141956 s t x).
Proof. exact (MK_COMB (@lem8005487 _141954 _141955) (@lem8005486 _141954 _141955 _141956 s t x)). Qed.
Lemma lem8005489 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term149 _141954 _141955 _141956 s t) = (term149 _141954 _141955 _141956 s t).
Proof. exact (fun_ext (fun x : type2 _141954 _141955 _141956 => @lem8005488 _141954 _141955 _141956 s t x)). Qed.
Lemma lem8005490 {_141954 _141955 _141956 : Type'} : (@all (cart _141954 (finite_sum _141955 _141956))) = (@all (cart _141954 (finite_sum _141955 _141956))).
Proof. exact (eq_refl (@all (cart _141954 (finite_sum _141955 _141956)))). Qed.
Lemma lem8005492 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term150 _141954 _141955 _141956 s t) = (term150 _141954 _141955 _141956 s t).
Proof. exact (MK_COMB (@lem8005490 _141954 _141955 _141956) (@lem8005489 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005493 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (x' : cart _141954 _141956) (h1 : term214 _141954 _141955 _141956 s x t x') : term150 _141954 _141955 _141956 s t.
Proof. exact (EQ_MP (@lem8005492 _141954 _141955 _141956 s t) (@lem8005458 _141954 _141955 _141956 s x t x' h1)). Qed.
Lemma lem8005515 {_141954 _141955 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) : (term97 _141954 _141955 s x) = (term97 _141954 _141955 s x).
Proof. exact (eq_refl (term97 _141954 _141955 s x)). Qed.
Lemma lem8005516 {_141954 _141955 : Type'} (s : type24 _141954 _141955) : (term99 _141954 _141955 s) = (term99 _141954 _141955 s).
Proof. exact (fun_ext (fun x : cart _141954 _141955 => @lem8005515 _141954 _141955 s x)). Qed.
Lemma lem8005517 {_141954 _141955 : Type'} : (@all (cart _141954 _141955)) = (@all (cart _141954 _141955)).
Proof. exact (eq_refl (@all (cart _141954 _141955))). Qed.
Lemma lem8005519 {_141954 _141955 : Type'} (s : type24 _141954 _141955) : (term100 _141954 _141955 s) = (term100 _141954 _141955 s).
Proof. exact (MK_COMB (@lem8005517 _141954 _141955) (@lem8005516 _141954 _141955 s)). Qed.
Lemma lem8005520 {_141954 _141955 : Type'} (s : type24 _141954 _141955) (h1 : term100 _141954 _141955 s) : term100 _141954 _141955 s.
Proof. exact (EQ_MP (@lem8005519 _141954 _141955 s) (@lem8005467 _141954 _141955 s h1)). Qed.
Lemma lem8005534 {_141954 _141956 : Type'} (t : type24 _141954 _141956) (x : cart _141954 _141956) : (term97 _141954 _141956 t x) = (term97 _141954 _141956 t x).
Proof. exact (eq_refl (term97 _141954 _141956 t x)). Qed.
Lemma lem8005535 {_141954 _141956 : Type'} (t : type24 _141954 _141956) : (term99 _141954 _141956 t) = (term99 _141954 _141956 t).
Proof. exact (fun_ext (fun x : cart _141954 _141956 => @lem8005534 _141954 _141956 t x)). Qed.
Lemma lem8005536 {_141954 _141956 : Type'} : (@all (cart _141954 _141956)) = (@all (cart _141954 _141956)).
Proof. exact (eq_refl (@all (cart _141954 _141956))). Qed.
Lemma lem8005538 {_141954 _141956 : Type'} (t : type24 _141954 _141956) : (term100 _141954 _141956 t) = (term100 _141954 _141956 t).
Proof. exact (MK_COMB (@lem8005536 _141954 _141956) (@lem8005535 _141954 _141956 t)). Qed.
Lemma lem8005539 {_141954 _141956 : Type'} (t : type24 _141954 _141956) (h1 : term100 _141954 _141956 t) : term100 _141954 _141956 t.
Proof. exact (EQ_MP (@lem8005538 _141954 _141956 t) (@lem8005468 _141954 _141956 t h1)). Qed.
Lemma lem8005540 {_141954 _141955 _141956 : Type'} (_105633 : type2 _141954 _141955 _141956) (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (x' : cart _141954 _141956) (h1 : term214 _141954 _141955 _141956 s x t x') : term355 _141954 _141955 _141956 s t _105633.
Proof. exact (@lem8005493 _141954 _141955 _141956 s x t x' h1 _105633). Qed.
Lemma lem8005541 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (_105633 : type2 _141954 _141955 _141956) : (term355 _141954 _141955 _141956 s t _105633) = (term138 _141954 _141955 _141956 s t _105633).
Proof. exact (eq_refl (term355 _141954 _141955 _141956 s t _105633)). Qed.
Lemma lem8005542 {_141954 _141955 _141956 : Type'} (_105633 : type2 _141954 _141955 _141956) (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (x' : cart _141954 _141956) (h1 : term214 _141954 _141955 _141956 s x t x') : term138 _141954 _141955 _141956 s t _105633.
Proof. exact (EQ_MP (@lem8005541 _141954 _141955 _141956 s t _105633) (@lem8005540 _141954 _141955 _141956 _105633 s x t x' h1)). Qed.
Lemma lem8005543 {_141954 _141955 _141956 : Type'} (_105633 : type2 _141954 _141955 _141956) (_105634 : cart _141954 _141955) (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (x' : cart _141954 _141956) (h1 : term214 _141954 _141955 _141956 s x t x') : term356 _141954 _141955 _141956 s t _105633 _105634.
Proof. exact (@lem8005542 _141954 _141955 _141956 _105633 s x t x' h1 _105634). Qed.
Lemma lem8005544 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (_105633 : type2 _141954 _141955 _141956) (_105634 : cart _141954 _141955) : (term356 _141954 _141955 _141956 s t _105633 _105634) = (term132 _141954 _141955 _141956 s t _105633 _105634).
Proof. exact (eq_refl (term356 _141954 _141955 _141956 s t _105633 _105634)). Qed.
Lemma lem8005545 {_141954 _141955 _141956 : Type'} (_105633 : type2 _141954 _141955 _141956) (_105634 : cart _141954 _141955) (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (x' : cart _141954 _141956) (h1 : term214 _141954 _141955 _141956 s x t x') : term132 _141954 _141955 _141956 s t _105633 _105634.
Proof. exact (EQ_MP (@lem8005544 _141954 _141955 _141956 s t _105633 _105634) (@lem8005543 _141954 _141955 _141956 _105633 _105634 s x t x' h1)). Qed.
Lemma lem8005546 {_141954 _141955 _141956 : Type'} (_105633 : type2 _141954 _141955 _141956) (_105634 : cart _141954 _141955) (_105635 : cart _141954 _141956) (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (x' : cart _141954 _141956) (h1 : term214 _141954 _141955 _141956 s x t x') : term357 _141954 _141955 _141956 s t _105633 _105634 _105635.
Proof. exact (@lem8005545 _141954 _141955 _141956 _105633 _105634 s x t x' h1 _105635). Qed.
Lemma lem8005547 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (_105633 : type2 _141954 _141955 _141956) (_105634 : cart _141954 _141955) (_105635 : cart _141954 _141956) : (term357 _141954 _141955 _141956 s t _105633 _105634 _105635) = (term123 _141954 _141955 _141956 s t _105633 _105634 _105635).
Proof. exact (eq_refl (term357 _141954 _141955 _141956 s t _105633 _105634 _105635)). Qed.
Lemma lem8005548 {_141954 _141955 _141956 : Type'} (_105633 : type2 _141954 _141955 _141956) (_105634 : cart _141954 _141955) (_105635 : cart _141954 _141956) (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (x' : cart _141954 _141956) (h1 : term214 _141954 _141955 _141956 s x t x') : term123 _141954 _141955 _141956 s t _105633 _105634 _105635.
Proof. exact (EQ_MP (@lem8005547 _141954 _141955 _141956 s t _105633 _105634 _105635) (@lem8005546 _141954 _141955 _141956 _105633 _105634 _105635 s x t x' h1)). Qed.
Lemma lem8005549 {_141954 _141955 : Type'} (_105636 : cart _141954 _141955) (s : type24 _141954 _141955) (h1 : term100 _141954 _141955 s) : term156 _141954 _141955 s _105636.
Proof. exact (@lem8005520 _141954 _141955 s h1 _105636). Qed.
Lemma lem8005550 {_141954 _141955 : Type'} (s : type24 _141954 _141955) (_105636 : cart _141954 _141955) : (term156 _141954 _141955 s _105636) = (term97 _141954 _141955 s _105636).
Proof. exact (eq_refl (term156 _141954 _141955 s _105636)). Qed.
Lemma lem8005552 {_141954 _141956 : Type'} (_105637 : cart _141954 _141956) (t : type24 _141954 _141956) (h1 : term100 _141954 _141956 t) : term156 _141954 _141956 t _105637.
Proof. exact (@lem8005539 _141954 _141956 t h1 _105637). Qed.
Lemma lem8005553 {_141954 _141956 : Type'} (t : type24 _141954 _141956) (_105637 : cart _141954 _141956) : (term156 _141954 _141956 t _105637) = (term97 _141954 _141956 t _105637).
Proof. exact (eq_refl (term156 _141954 _141956 t _105637)). Qed.
Lemma lem8005565 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (_105633 : type2 _141954 _141955 _141956) (_105634 : cart _141954 _141955) (_105635 : cart _141954 _141956) : (term123 _141954 _141955 _141956 s t _105633 _105634 _105635) = (term358 _141954 _141955 _141956 s t _105633 _105634 _105635).
Proof. exact (@lem8004239 (term97 _141954 _141955 s _105634) (term97 _141954 _141956 t _105635) (term119 _141954 _141955 _141956 _105633 _105634 _105635)). Qed.
Lemma lem8005566 {_141954 _141955 _141956 : Type'} (_105633 : type2 _141954 _141955 _141956) (_105634 : cart _141954 _141955) (_105635 : cart _141954 _141956) (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (x' : cart _141954 _141956) (h1 : term214 _141954 _141955 _141956 s x t x') : term358 _141954 _141955 _141956 s t _105633 _105634 _105635.
Proof. exact (EQ_MP (@lem8005565 _141954 _141955 _141956 s t _105633 _105634 _105635) (@lem8005548 _141954 _141955 _141956 _105633 _105634 _105635 s x t x' h1)). Qed.
Lemma lem8005642 {_141954 _141955 : Type'} (_105636 : cart _141954 _141955) (s : type24 _141954 _141955) (h1 : term100 _141954 _141955 s) : term97 _141954 _141955 s _105636.
Proof. exact (EQ_MP (@lem8005550 _141954 _141955 s _105636) (@lem8005549 _141954 _141955 _105636 s h1)). Qed.
Lemma lem8005698 {_141954 _141956 : Type'} (_105637 : cart _141954 _141956) (t : type24 _141954 _141956) (h1 : term100 _141954 _141956 t) : term97 _141954 _141956 t _105637.
Proof. exact (EQ_MP (@lem8005553 _141954 _141956 t _105637) (@lem8005552 _141954 _141956 _105637 t h1)). Qed.
Lemma lem8005745 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (x' : cart _141954 _141956) (h1 : term214 _141954 _141955 _141956 s x t x') : s x.
Proof. exact (proj1 (@lem8005457 _141954 _141955 _141956 s x t x' h1)). Qed.
Lemma lem8005746 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (x' : cart _141954 _141956) (h1 : term214 _141954 _141955 _141956 s x t x') : term359 _141954 _141955 s x.
Proof. exact (fun h0 : term97 _141954 _141955 s x => @lem8005745 _141954 _141955 _141956 s x t x' h1). Qed.
Lemma lem8005748 (p : Prop) : (term360 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8005749 {_141954 _141955 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) : (term359 _141954 _141955 s x) = (s x).
Proof. exact (@lem8005748 (s x)). Qed.
Lemma lem8005750 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (x' : cart _141954 _141956) (h1 : term214 _141954 _141955 _141956 s x t x') : s x.
Proof. exact (EQ_MP (@lem8005749 _141954 _141955 s x) (@lem8005746 _141954 _141955 _141956 s x t x' h1)). Qed.
Lemma lem8005752 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (x' : cart _141954 _141956) (h1 : term214 _141954 _141955 _141956 s x t x') : t x'.
Proof. exact (proj2 (@lem8005457 _141954 _141955 _141956 s x t x' h1)). Qed.
Lemma lem8005753 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (x' : cart _141954 _141956) (h1 : term214 _141954 _141955 _141956 s x t x') : term359 _141954 _141956 t x'.
Proof. exact (fun h0 : term97 _141954 _141956 t x' => @lem8005752 _141954 _141955 _141956 s x t x' h1). Qed.
Lemma lem8005755 (p : Prop) : (term360 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8005756 {_141954 _141956 : Type'} (t : type24 _141954 _141956) (x' : cart _141954 _141956) : (term359 _141954 _141956 t x') = (t x').
Proof. exact (@lem8005755 (t x')). Qed.
Lemma lem8005757 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (x' : cart _141954 _141956) (h1 : term214 _141954 _141955 _141956 s x t x') : t x'.
Proof. exact (EQ_MP (@lem8005756 _141954 _141956 t x') (@lem8005753 _141954 _141955 _141956 s x t x' h1)). Qed.
Lemma lem8005759 {_141954 _141955 _141956 : Type'} (x : type2 _141954 _141955 _141956) : x = x.
Proof. exact (@lem21386 (type2 _141954 _141955 _141956) x). Qed.
Lemma lem8005760 {_141954 _141955 _141956 : Type'} (x : type2 _141954 _141955 _141956) : x = x.
Proof. exact (@lem8005759 _141954 _141955 _141956 x). Qed.
Lemma lem8005761 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (x' : cart _141954 _141956) : (@pastecart _141954 _141955 _141956 x x') = (@pastecart _141954 _141955 _141956 x x').
Proof. exact (@lem8005760 _141954 _141955 _141956 (@pastecart _141954 _141955 _141956 x x')). Qed.
Lemma lem8005762 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (x' : cart _141954 _141956) : term361 _141954 _141955 _141956 x x'.
Proof. exact (fun h0 : term362 _141954 _141955 _141956 x x' => @lem8005761 _141954 _141955 _141956 x x'). Qed.
Lemma lem8005764 (p : Prop) : (term360 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8005765 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (x' : cart _141954 _141956) : (term361 _141954 _141955 _141956 x x') = ((@pastecart _141954 _141955 _141956 x x') = (@pastecart _141954 _141955 _141956 x x')).
Proof. exact (@lem8005764 ((@pastecart _141954 _141955 _141956 x x') = (@pastecart _141954 _141955 _141956 x x'))). Qed.
Lemma lem8005766 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (x' : cart _141954 _141956) : (@pastecart _141954 _141955 _141956 x x') = (@pastecart _141954 _141955 _141956 x x').
Proof. exact (EQ_MP (@lem8005765 _141954 _141955 _141956 x x') (@lem8005762 _141954 _141955 _141956 x x')). Qed.
Lemma lem8005768 (a : Prop) (b : Prop) : (term363 a b) = (term364 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem8005769 {_141954 _141955 _141956 : Type'} (t : type24 _141954 _141956) (_105633 : type2 _141954 _141955 _141956) (_105634 : cart _141954 _141955) (_105635 : cart _141954 _141956) : (term365 _141954 _141955 _141956 t _105633 _105634 _105635) = (term366 _141954 _141955 _141956 t _105633 _105634 _105635).
Proof. exact (@lem8005768 (t _105635) (_105633 = (@pastecart _141954 _141955 _141956 _105634 _105635))). Qed.
Lemma lem8005770 {_141954 _141955 : Type'} (s : type24 _141954 _141955) (_105634 : cart _141954 _141955) : (term367 _141954 _141955 s _105634) = (term367 _141954 _141955 s _105634).
Proof. exact (eq_refl (term367 _141954 _141955 s _105634)). Qed.
Lemma lem8005771 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (_105633 : type2 _141954 _141955 _141956) (_105634 : cart _141954 _141955) (_105635 : cart _141954 _141956) : (term358 _141954 _141955 _141956 s t _105633 _105634 _105635) = (term368 _141954 _141955 _141956 s t _105633 _105634 _105635).
Proof. exact (MK_COMB (@lem8005770 _141954 _141955 s _105634) (@lem8005769 _141954 _141955 _141956 t _105633 _105634 _105635)). Qed.
Lemma lem8005773 (a : Prop) (b : Prop) : (term363 a b) = (term364 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem8005774 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (_105633 : type2 _141954 _141955 _141956) (_105634 : cart _141954 _141955) (_105635 : cart _141954 _141956) : (term368 _141954 _141955 _141956 s t _105633 _105634 _105635) = (term369 _141954 _141955 _141956 s t _105633 _105634 _105635).
Proof. exact (@lem8005773 (s _105634) (term370 _141954 _141955 _141956 t _105633 _105634 _105635)). Qed.
Lemma lem8005775 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (_105633 : type2 _141954 _141955 _141956) (_105634 : cart _141954 _141955) (_105635 : cart _141954 _141956) : (term358 _141954 _141955 _141956 s t _105633 _105634 _105635) = (term369 _141954 _141955 _141956 s t _105633 _105634 _105635).
Proof. exact (TRANS (@lem8005771 _141954 _141955 _141956 s t _105633 _105634 _105635) (@lem8005774 _141954 _141955 _141956 s t _105633 _105634 _105635)). Qed.
Lemma lem8005777 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8005778 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (_105633 : type2 _141954 _141955 _141956) (_105634 : cart _141954 _141955) (_105635 : cart _141954 _141956) : (term369 _141954 _141955 _141956 s t _105633 _105634 _105635) = (term371 _141954 _141955 _141956 s t _105633 _105634 _105635).
Proof. exact (@lem8005777 (term372 _141954 _141955 _141956 s t _105633 _105634 _105635)). Qed.
Lemma lem8005779 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (_105633 : type2 _141954 _141955 _141956) (_105634 : cart _141954 _141955) (_105635 : cart _141954 _141956) : (term358 _141954 _141955 _141956 s t _105633 _105634 _105635) = (term371 _141954 _141955 _141956 s t _105633 _105634 _105635).
Proof. exact (TRANS (@lem8005775 _141954 _141955 _141956 s t _105633 _105634 _105635) (@lem8005778 _141954 _141955 _141956 s t _105633 _105634 _105635)). Qed.
Lemma lem8005781 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (x' : cart _141954 _141956) (h1 : term214 _141954 _141955 _141956 s x t x') : term373 _141954 _141955 _141956 t x x'.
Proof. exact (conj (@lem8005757 _141954 _141955 _141956 s x t x' h1) (@lem8005766 _141954 _141955 _141956 x x')). Qed.
Lemma lem8005782 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (x' : cart _141954 _141956) (h1 : term214 _141954 _141955 _141956 s x t x') : term374 _141954 _141955 _141956 s t x x'.
Proof. exact (conj (@lem8005750 _141954 _141955 _141956 s x t x' h1) (@lem8005781 _141954 _141955 _141956 s x t x' h1)). Qed.
Lemma lem8005784 {_141954 _141955 _141956 : Type'} (_105633 : type2 _141954 _141955 _141956) (_105634 : cart _141954 _141955) (_105635 : cart _141954 _141956) (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (x' : cart _141954 _141956) (h1 : term214 _141954 _141955 _141956 s x t x') : term371 _141954 _141955 _141956 s t _105633 _105634 _105635.
Proof. exact (EQ_MP (@lem8005779 _141954 _141955 _141956 s t _105633 _105634 _105635) (@lem8005566 _141954 _141955 _141956 _105633 _105634 _105635 s x t x' h1)). Qed.
Lemma lem8005785 {_141954 _141955 _141956 : Type'} (_105633 : type2 _141954 _141955 _141956) (_105634 : cart _141954 _141955) (_105635 : cart _141954 _141956) (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (x' : cart _141954 _141956) (h1 : term214 _141954 _141955 _141956 s x t x') : term371 _141954 _141955 _141956 s t _105633 _105634 _105635.
Proof. exact (@lem8005784 _141954 _141955 _141956 _105633 _105634 _105635 s x t x' h1). Qed.
Lemma lem8005786 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (x' : cart _141954 _141956) (h1 : term214 _141954 _141955 _141956 s x t x') : term375 _141954 _141955 _141956 s t x x'.
Proof. exact (@lem8005785 _141954 _141955 _141956 (@pastecart _141954 _141955 _141956 x x') x x' s x t x' h1). Qed.
Lemma lem8005789 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (x' : cart _141954 _141956) (h1 : term214 _141954 _141955 _141956 s x t x') : False.
Proof. exact (@lem8005786 _141954 _141955 _141956 s x t x' h1 (@lem8005782 _141954 _141955 _141956 s x t x' h1)). Qed.
Lemma lem8005790 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (x' : cart _141954 _141956) (h1 : term214 _141954 _141955 _141956 s x t x') : term376.
Proof. exact (fun h0 : ~ False => @lem8005789 _141954 _141955 _141956 s x t x' h1). Qed.
Lemma lem8005792 (p : Prop) : (term360 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8005793 : term376 = False.
Proof. exact (@lem8005792 False). Qed.
Lemma lem8005794 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (x : cart _141954 _141955) (t : type24 _141954 _141956) (x' : cart _141954 _141956) (h1 : term214 _141954 _141955 _141956 s x t x') : False.
Proof. exact (EQ_MP (@lem8005793) (@lem8005790 _141954 _141955 _141956 s x t x' h1)). Qed.
Lemma lem8005796 {_141954 _141955 _141956 : Type'} (x'' : type2 _141954 _141955 _141956) (x''' : cart _141954 _141955) (y : cart _141954 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) (h1 : term262 _141954 _141955 _141956 x'' x''' y s t) : s x'''.
Proof. exact (proj1 (@lem8005464 _141954 _141955 _141956 x'' x''' y s t h1)). Qed.
Lemma lem8005797 {_141954 _141955 _141956 : Type'} (x'' : type2 _141954 _141955 _141956) (x''' : cart _141954 _141955) (y : cart _141954 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) (h1 : term262 _141954 _141955 _141956 x'' x''' y s t) : term359 _141954 _141955 s x'''.
Proof. exact (fun h0 : term97 _141954 _141955 s x''' => @lem8005796 _141954 _141955 _141956 x'' x''' y s t h1). Qed.
Lemma lem8005799 (p : Prop) : (term360 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8005800 {_141954 _141955 : Type'} (s : type24 _141954 _141955) (x''' : cart _141954 _141955) : (term359 _141954 _141955 s x''') = (s x''').
Proof. exact (@lem8005799 (s x''')). Qed.
Lemma lem8005801 {_141954 _141955 _141956 : Type'} (x'' : type2 _141954 _141955 _141956) (x''' : cart _141954 _141955) (y : cart _141954 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) (h1 : term262 _141954 _141955 _141956 x'' x''' y s t) : s x'''.
Proof. exact (EQ_MP (@lem8005800 _141954 _141955 s x''') (@lem8005797 _141954 _141955 _141956 x'' x''' y s t h1)). Qed.
Lemma lem8005804 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8005806 {_141954 _141955 : Type'} (s : type24 _141954 _141955) (_105636 : cart _141954 _141955) : (term97 _141954 _141955 s _105636) = (term377 _141954 _141955 s _105636).
Proof. exact (@lem8005804 (s _105636)). Qed.
Lemma lem8005809 {_141954 _141955 : Type'} (_105636 : cart _141954 _141955) (s : type24 _141954 _141955) (h1 : term100 _141954 _141955 s) : term377 _141954 _141955 s _105636.
Proof. exact (EQ_MP (@lem8005806 _141954 _141955 s _105636) (@lem8005642 _141954 _141955 _105636 s h1)). Qed.
Lemma lem8005810 {_141954 _141955 : Type'} (_105636 : cart _141954 _141955) (s : type24 _141954 _141955) (h1 : term100 _141954 _141955 s) : term377 _141954 _141955 s _105636.
Proof. exact (@lem8005809 _141954 _141955 _105636 s h1). Qed.
Lemma lem8005811 {_141954 _141955 : Type'} (x''' : cart _141954 _141955) (s : type24 _141954 _141955) (h1 : term100 _141954 _141955 s) : term377 _141954 _141955 s x'''.
Proof. exact (@lem8005810 _141954 _141955 x''' s h1). Qed.
Lemma lem8005814 {_141954 _141955 _141956 : Type'} (x'' : type2 _141954 _141955 _141956) (x''' : cart _141954 _141955) (y : cart _141954 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) (h1 : term100 _141954 _141955 s) (h2 : term262 _141954 _141955 _141956 x'' x''' y s t) : False.
Proof. exact (@lem8005811 _141954 _141955 x''' s h1 (@lem8005801 _141954 _141955 _141956 x'' x''' y s t h2)). Qed.
Lemma lem8005815 {_141954 _141955 _141956 : Type'} (x'' : type2 _141954 _141955 _141956) (x''' : cart _141954 _141955) (y : cart _141954 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) (h1 : term100 _141954 _141955 s) (h2 : term262 _141954 _141955 _141956 x'' x''' y s t) : term376.
Proof. exact (fun h0 : ~ False => @lem8005814 _141954 _141955 _141956 x'' x''' y s t h1 h2). Qed.
Lemma lem8005817 (p : Prop) : (term360 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8005818 : term376 = False.
Proof. exact (@lem8005817 False). Qed.
Lemma lem8005821 {_141954 _141955 _141956 : Type'} (x'' : type2 _141954 _141955 _141956) (x''' : cart _141954 _141955) (y : cart _141954 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) (h1 : term262 _141954 _141955 _141956 x'' x''' y s t) : t y.
Proof. exact (proj2 (@lem8005464 _141954 _141955 _141956 x'' x''' y s t h1)). Qed.
Lemma lem8005822 {_141954 _141955 _141956 : Type'} (x'' : type2 _141954 _141955 _141956) (x''' : cart _141954 _141955) (y : cart _141954 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) (h1 : term262 _141954 _141955 _141956 x'' x''' y s t) : term359 _141954 _141956 t y.
Proof. exact (fun h0 : term97 _141954 _141956 t y => @lem8005821 _141954 _141955 _141956 x'' x''' y s t h1). Qed.
Lemma lem8005824 (p : Prop) : (term360 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8005825 {_141954 _141956 : Type'} (t : type24 _141954 _141956) (y : cart _141954 _141956) : (term359 _141954 _141956 t y) = (t y).
Proof. exact (@lem8005824 (t y)). Qed.
Lemma lem8005826 {_141954 _141955 _141956 : Type'} (x'' : type2 _141954 _141955 _141956) (x''' : cart _141954 _141955) (y : cart _141954 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) (h1 : term262 _141954 _141955 _141956 x'' x''' y s t) : t y.
Proof. exact (EQ_MP (@lem8005825 _141954 _141956 t y) (@lem8005822 _141954 _141955 _141956 x'' x''' y s t h1)). Qed.
Lemma lem8005829 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8005831 {_141954 _141956 : Type'} (t : type24 _141954 _141956) (_105637 : cart _141954 _141956) : (term97 _141954 _141956 t _105637) = (term377 _141954 _141956 t _105637).
Proof. exact (@lem8005829 (t _105637)). Qed.
Lemma lem8005834 {_141954 _141956 : Type'} (_105637 : cart _141954 _141956) (t : type24 _141954 _141956) (h1 : term100 _141954 _141956 t) : term377 _141954 _141956 t _105637.
Proof. exact (EQ_MP (@lem8005831 _141954 _141956 t _105637) (@lem8005698 _141954 _141956 _105637 t h1)). Qed.
Lemma lem8005835 {_141954 _141956 : Type'} (_105637 : cart _141954 _141956) (t : type24 _141954 _141956) (h1 : term100 _141954 _141956 t) : term377 _141954 _141956 t _105637.
Proof. exact (@lem8005834 _141954 _141956 _105637 t h1). Qed.
Lemma lem8005836 {_141954 _141956 : Type'} (y : cart _141954 _141956) (t : type24 _141954 _141956) (h1 : term100 _141954 _141956 t) : term377 _141954 _141956 t y.
Proof. exact (@lem8005835 _141954 _141956 y t h1). Qed.
Lemma lem8005839 {_141954 _141955 _141956 : Type'} (x'' : type2 _141954 _141955 _141956) (x''' : cart _141954 _141955) (y : cart _141954 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) (h1 : term100 _141954 _141956 t) (h2 : term262 _141954 _141955 _141956 x'' x''' y s t) : False.
Proof. exact (@lem8005836 _141954 _141956 y t h1 (@lem8005826 _141954 _141955 _141956 x'' x''' y s t h2)). Qed.
Lemma lem8005840 {_141954 _141955 _141956 : Type'} (x'' : type2 _141954 _141955 _141956) (x''' : cart _141954 _141955) (y : cart _141954 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) (h1 : term100 _141954 _141956 t) (h2 : term262 _141954 _141955 _141956 x'' x''' y s t) : term376.
Proof. exact (fun h0 : ~ False => @lem8005839 _141954 _141955 _141956 x'' x''' y s t h1 h2). Qed.
Lemma lem8005842 (p : Prop) : (term360 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8005843 : term376 = False.
Proof. exact (@lem8005842 False). Qed.
Lemma lem8005845 {_141954 _141955 _141956 : Type'} (x'' : type2 _141954 _141955 _141956) (x''' : cart _141954 _141955) (y : cart _141954 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) (h1 : term100 _141954 _141956 t) (h2 : term262 _141954 _141955 _141956 x'' x''' y s t) : False.
Proof. exact (EQ_MP (@lem8005843) (@lem8005840 _141954 _141955 _141956 x'' x''' y s t h1 h2)). Qed.
Lemma lem8005846 {_141954 _141955 _141956 : Type'} (x'' : type2 _141954 _141955 _141956) (x''' : cart _141954 _141955) (y : cart _141954 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) (h1 : term100 _141954 _141955 s) (h2 : term262 _141954 _141955 _141956 x'' x''' y s t) : False.
Proof. exact (EQ_MP (@lem8005818) (@lem8005815 _141954 _141955 _141956 x'' x''' y s t h1 h2)). Qed.
Lemma lem8005847 {_141954 _141955 _141956 : Type'} (x'' : type2 _141954 _141955 _141956) (x''' : cart _141954 _141955) (y : cart _141954 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) (h1 : term100 _141954 _141956 t) (h2 : term262 _141954 _141955 _141956 x'' x''' y s t) : (term100 _141954 _141956 t) = False.
Proof. exact (prop_ext (fun h3 : term100 _141954 _141956 t => @lem8005845 _141954 _141955 _141956 x'' x''' y s t h1 h2) (fun h3 : False => @lem8005539 _141954 _141956 t h1)). Qed.
Lemma lem8005848 {_141954 _141955 _141956 : Type'} (x'' : type2 _141954 _141955 _141956) (x''' : cart _141954 _141955) (y : cart _141954 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) (h1 : term100 _141954 _141956 t) (h2 : term262 _141954 _141955 _141956 x'' x''' y s t) : False.
Proof. exact (EQ_MP (@lem8005847 _141954 _141955 _141956 x'' x''' y s t h1 h2) (@lem8005539 _141954 _141956 t h1)). Qed.
Lemma lem8005849 {_141954 _141955 _141956 : Type'} (x'' : type2 _141954 _141955 _141956) (x''' : cart _141954 _141955) (y : cart _141954 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) (h1 : term100 _141954 _141955 s) (h2 : term262 _141954 _141955 _141956 x'' x''' y s t) : (term100 _141954 _141955 s) = False.
Proof. exact (prop_ext (fun h3 : term100 _141954 _141955 s => @lem8005846 _141954 _141955 _141956 x'' x''' y s t h1 h2) (fun h3 : False => @lem8005520 _141954 _141955 s h1)). Qed.
Lemma lem8005850 {_141954 _141955 _141956 : Type'} (x'' : type2 _141954 _141955 _141956) (x''' : cart _141954 _141955) (y : cart _141954 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) (h1 : term100 _141954 _141955 s) (h2 : term262 _141954 _141955 _141956 x'' x''' y s t) : False.
Proof. exact (EQ_MP (@lem8005849 _141954 _141955 _141956 x'' x''' y s t h1 h2) (@lem8005520 _141954 _141955 s h1)). Qed.
Lemma lem8005851 {_141954 _141955 _141956 : Type'} (x'' : type2 _141954 _141955 _141956) (x''' : cart _141954 _141955) (y : cart _141954 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) (h1 : term262 _141954 _141955 _141956 x'' x''' y s t) : False.
Proof. exact (or_elim (@lem8005461 _141954 _141955 _141956 x'' x''' y s t h1) (fun h0 : term100 _141954 _141955 s => @lem8005850 _141954 _141955 _141956 x'' x''' y s t h0 h1) (fun h0 : term100 _141954 _141956 t => @lem8005848 _141954 _141955 _141956 x'' x''' y s t h0 h1)). Qed.
Lemma lem8005852 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (x' : cart _141954 _141956) (x'' : type2 _141954 _141955 _141956) (x''' : cart _141954 _141955) (y : cart _141954 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) (h1 : term343 _141954 _141955 _141956 x x' x'' x''' y s t) : False.
Proof. exact (or_elim (@lem8005454 _141954 _141955 _141956 x x' x'' x''' y s t h1) (fun h0 : term214 _141954 _141955 _141956 s x t x' => @lem8005794 _141954 _141955 _141956 s x t x' h0) (fun h0 : term262 _141954 _141955 _141956 x'' x''' y s t => @lem8005851 _141954 _141955 _141956 x'' x''' y s t h0)). Qed.
Lemma lem8005853 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (x' : cart _141954 _141956) (x'' : type2 _141954 _141955 _141956) (x''' : cart _141954 _141955) (y : cart _141954 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) (h1 : term343 _141954 _141955 _141956 x x' x'' x''' y s t) : (term343 _141954 _141955 _141956 x x' x'' x''' y s t) = False.
Proof. exact (prop_ext (fun h2 : term343 _141954 _141955 _141956 x x' x'' x''' y s t => @lem8005852 _141954 _141955 _141956 x x' x'' x''' y s t h1) (fun h2 : False => @lem8005454 _141954 _141955 _141956 x x' x'' x''' y s t h1)). Qed.
Lemma lem8005854 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (x' : cart _141954 _141956) (x'' : type2 _141954 _141955 _141956) (x''' : cart _141954 _141955) (y : cart _141954 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) (h1 : term343 _141954 _141955 _141956 x x' x'' x''' y s t) : False.
Proof. exact (EQ_MP (@lem8005853 _141954 _141955 _141956 x x' x'' x''' y s t h1) (@lem8005454 _141954 _141955 _141956 x x' x'' x''' y s t h1)). Qed.
Lemma lem8005855 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (x' : cart _141954 _141956) (x'' : type2 _141954 _141955 _141956) (x''' : cart _141954 _141955) (s : type24 _141954 _141955) (t : type24 _141954 _141956) (h1 : term346 _141954 _141955 _141956 x x' x'' x''' s t) : False.
Proof. exact (ex_elim (@lem8005358 _141954 _141955 _141956 x x' x'' x''' s t h1) (fun y : cart _141954 _141956 => fun h0 : term345 _141954 _141955 _141956 x x' x'' x''' s t y => @lem8005854 _141954 _141955 _141956 x x' x'' x''' y s t h0)). Qed.
Lemma lem8005856 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (x' : cart _141954 _141956) (x'' : type2 _141954 _141955 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) (h1 : term348 _141954 _141955 _141956 x x' x'' s t) : False.
Proof. exact (ex_elim (@lem8005357 _141954 _141955 _141956 x x' x'' s t h1) (fun x''' : cart _141954 _141955 => fun h0 : term347 _141954 _141955 _141956 x x' x'' s t x''' => @lem8005855 _141954 _141955 _141956 x x' x'' x''' s t h0)). Qed.
Lemma lem8005857 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (x' : cart _141954 _141956) (s : type24 _141954 _141955) (t : type24 _141954 _141956) (h1 : term350 _141954 _141955 _141956 x x' s t) : False.
Proof. exact (ex_elim (@lem8005356 _141954 _141955 _141956 x x' s t h1) (fun x'' : type2 _141954 _141955 _141956 => fun h0 : term349 _141954 _141955 _141956 x x' s t x'' => @lem8005856 _141954 _141955 _141956 x x' x'' s t h0)). Qed.
Lemma lem8005858 {_141954 _141955 _141956 : Type'} (x : cart _141954 _141955) (s : type24 _141954 _141955) (t : type24 _141954 _141956) (h1 : term352 _141954 _141955 _141956 x s t) : False.
Proof. exact (ex_elim (@lem8005355 _141954 _141955 _141956 x s t h1) (fun x' : cart _141954 _141956 => fun h0 : term351 _141954 _141955 _141956 x s t x' => @lem8005857 _141954 _141955 _141956 x x' s t h0)). Qed.
Lemma lem8005859 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (h1 : term116 _141954 _141955 _141956 s t) : False.
Proof. exact (ex_elim (@lem8005354 _141954 _141955 _141956 s t h1) (fun x : cart _141954 _141955 => fun h0 : term353 _141954 _141955 _141956 s t x => @lem8005858 _141954 _141955 _141956 x s t h0)). Qed.
Lemma lem8005860 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (h1 : term116 _141954 _141955 _141956 s t) : (term116 _141954 _141955 _141956 s t) = False.
Proof. exact (prop_ext (fun h2 : term116 _141954 _141955 _141956 s t => @lem8005859 _141954 _141955 _141956 s t h1) (fun h2 : False => @lem8004835 _141954 _141955 _141956 s t h1)). Qed.
Lemma lem8005861 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) (h1 : term116 _141954 _141955 _141956 s t) : False.
Proof. exact (EQ_MP (@lem8005860 _141954 _141955 _141956 s t h1) (@lem8004835 _141954 _141955 _141956 s t h1)). Qed.
Lemma lem8005862 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : term115 _141954 _141955 _141956 s t.
Proof. exact (fun h0 : term116 _141954 _141955 _141956 s t => @lem8005861 _141954 _141955 _141956 s t h0). Qed.
Lemma lem8005863 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term93 _141954 _141955 _141956 s t) = (term102 _141954 _141955 _141956 s t).
Proof. exact (EQ_MP (@lem8004834 _141954 _141955 _141956 s t) (@lem8005862 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005868 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) : term104 _141954 _141955 _141956 s.
Proof. exact (fun t : type24 _141954 _141956 => @lem8005863 _141954 _141955 _141956 s t). Qed.
Lemma lem8005873 {_141954 _141955 _141956 : Type'} : term106 _141954 _141955 _141956.
Proof. exact (fun s : type24 _141954 _141955 => @lem8005868 _141954 _141955 _141956 s). Qed.
Lemma lem8005874 {_141954 _141955 _141956 : Type'} : term108 _141954 _141955 _141956.
Proof. exact (EQ_MP (@lem8004830 _141954 _141955 _141956) (@lem8005873 _141954 _141955 _141956)). Qed.
Lemma lem8005876 {_141954 _141955 _141956 : Type'} : term108 _141954 _141955 _141956.
Proof. exact (@lem8004645 _141954 _141955 _141956 (@lem8005874 _141954 _141955 _141956)). Qed.
Lemma lem8005877 {_141954 _141955 _141956 : Type'} (h1 : term109 _141954 _141955 _141956) : False.
Proof. exact (@lem8005876 _141954 _141955 _141956 (@lem8004629 _141954 _141955 _141956 h1)). Qed.
Lemma lem8005878 {_141954 _141955 _141956 : Type'} (h1 : term109 _141954 _141955 _141956) : (term109 _141954 _141955 _141956) = False.
Proof. exact (prop_ext (fun h2 : term109 _141954 _141955 _141956 => @lem8005877 _141954 _141955 _141956 h1) (fun h2 : False => @lem8004629 _141954 _141955 _141956 h1)). Qed.
Lemma lem8005879 {_141954 _141955 _141956 : Type'} (h1 : term109 _141954 _141955 _141956) : False.
Proof. exact (EQ_MP (@lem8005878 _141954 _141955 _141956 h1) (@lem8004629 _141954 _141955 _141956 h1)). Qed.
Lemma lem8005880 {_141954 _141955 _141956 : Type'} : term108 _141954 _141955 _141956.
Proof. exact (fun h0 : term109 _141954 _141955 _141956 => @lem8005879 _141954 _141955 _141956 h0). Qed.
Lemma lem8005881 {_141954 _141955 _141956 : Type'} : term106 _141954 _141955 _141956.
Proof. exact (EQ_MP (@lem8004628 _141954 _141955 _141956) (@lem8005880 _141954 _141955 _141956)). Qed.
Lemma lem8005882 {_141954 _141955 _141956 : Type'} : term36 _141954 _141955 _141956.
Proof. exact (EQ_MP (@lem8004624 _141954 _141955 _141956) (@lem8005881 _141954 _141955 _141956)). Qed.
Lemma lem8005883 {_141954 _141955 _141956 : Type'} : term23 _141954 _141955 _141956.
Proof. exact (EQ_MP (@lem8004396 _141954 _141955 _141956) (@lem8005882 _141954 _141955 _141956)). Qed.
Lemma lem8005884 {_141954 _141955 _141956 : Type'} : term22 _141954 _141955 _141956.
Proof. exact (EQ_MP (@lem8004303 _141954 _141955 _141956) (@lem8005883 _141954 _141955 _141956)). Qed.
