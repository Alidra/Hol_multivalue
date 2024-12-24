Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FORALL_FINITE_INDEX_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_INDEX_WORKS_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18897_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18940_spec.
Require Import thm18941_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
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
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Lemma lem7612101 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem7612102 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem7612103 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem7612102 t1) (@lem7612101 t1)). Qed.
Lemma lem7612104 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem7612103 t1 t2). Qed.
Lemma lem7612105 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem7612106 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem7612105 t1 t2) (@lem7612104 t1 t2)). Qed.
Lemma lem7612107 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem7612106 t1 t2 t3). Qed.
Lemma lem7612108 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem7612109 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem7612108 t1 t2 t3) (@lem7612107 t1 t2 t3)). Qed.
Lemma lem7612110 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem7612109 t1 t2 t3)). Qed.
Lemma lem7612112 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7612113 {N : Type'} (P : type33 N) : ((term8 N P) = (term9 N P)) = (term10 N P).
Proof. exact (@lem7612112 ((term8 N P) = (term9 N P))). Qed.
Lemma lem7612114 {N : Type'} (P : type33 N) : (term10 N P) = ((term8 N P) = (term9 N P)).
Proof. exact (SYM (@lem7612113 N P)). Qed.
Lemma lem7612115 {N : Type'} (P : type33 N) (h1 : term11 N P) : term11 N P.
Proof. exact (h1). Qed.
Lemma lem7612116 {N : Type'} : term12 N.
Proof. exact (@lem7609879 N). Qed.
Lemma lem7612121 {A N : Type'} (P : type33 N) (h1 : term13 A N P) : term13 A N P.
Proof. exact (h1). Qed.
Lemma lem7612122 {A N : Type'} (P : type33 N) : term14 A N P.
Proof. exact (fun h0 : term13 A N P => @lem7612121 A N P h0). Qed.
Lemma lem7612123 {A N : Type'} (P : type33 N) (h1 : term14 A N P) : term14 A N P.
Proof. exact (h1). Qed.
Lemma lem7612124 {A N : Type'} (P : type33 N) (h1 : term13 A N P) : term13 A N P.
Proof. exact (h1). Qed.
Lemma lem7612125 {A N : Type'} (P : type33 N) (h1 : term13 A N P) (h2 : term14 A N P) : term13 A N P.
Proof. exact (@lem7612123 A N P h2 (@lem7612124 A N P h1)). Qed.
Lemma lem7612126 {A N : Type'} (P : type33 N) (h1 : term13 A N P) : term15 A N P.
Proof. exact (fun h0 : term14 A N P => @lem7612125 A N P h1 h0). Qed.
Lemma lem7612127 {A N : Type'} (P : type33 N) (h1 : term14 A N P) : term14 A N P.
Proof. exact (h1). Qed.
Lemma lem7612128 {A N : Type'} (P : type33 N) (h1 : term13 A N P) (h2 : term14 A N P) : term13 A N P.
Proof. exact (@lem7612126 A N P h1 (@lem7612127 A N P h2)). Qed.
Lemma lem7612129 {A N : Type'} (P : type33 N) (h1 : term14 A N P) : term14 A N P.
Proof. exact (fun h0 : term13 A N P => @lem7612128 A N P h0 h1). Qed.
Lemma lem7612130 {A N : Type'} (P : type33 N) : term16 A N P.
Proof. exact (fun h0 : term14 A N P => @lem7612129 A N P h0). Qed.
Lemma lem7612133 {A N : Type'} (P : type33 N) : term14 A N P.
Proof. exact (@lem7612130 A N P (@lem7612122 A N P)). Qed.
Lemma lem7612134 {A N : Type'} (P : type33 N) : term14 A N P.
Proof. exact (@lem7612133 A N P). Qed.
Lemma lem7612164 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7612165 {N : Type'} : (term17 N) = (term18 N).
Proof. exact (@lem7612164 (term12 N)). Qed.
Lemma lem7612174 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (eq_refl (term19 A)). Qed.
Lemma lem7612175 {A N : Type'} : (term20 A N) = (term21 A N).
Proof. exact (MK_COMB (@lem7612174 A) (@lem7612165 N)). Qed.
Lemma lem7612178 {N : Type'} (P : type33 N) : (term22 N P) = (term22 N P).
Proof. exact (eq_refl (term22 N P)). Qed.
Lemma lem7612179 {A N : Type'} (P : type33 N) : (term13 A N P) = (term23 A N P).
Proof. exact (MK_COMB (@lem7612178 N P) (@lem7612175 A N)). Qed.
Lemma lem7612182 {A N : Type'} : (term24 A N) = (term25 A N).
Proof. exact (fun_ext (fun P : type33 N => @lem7612179 A N P)). Qed.
Lemma lem7612183 {N : Type'} : (@all ((finite_image N) -> Prop)) = (@all ((finite_image N) -> Prop)).
Proof. exact (eq_refl (@all ((finite_image N) -> Prop))). Qed.
Lemma lem7612192 {A N : Type'} : (term26 A N) = (term27 A N).
Proof. exact (MK_COMB (@lem7612183 N) (@lem7612182 A N)). Qed.
Lemma lem7612201 {N : Type'} (n : nat) (i : finite_image N) : (term28 N n i) = (term28 N n i).
Proof. exact (eq_refl (term28 N n i)). Qed.
Lemma lem7612202 {N : Type'} (i : finite_image N) : (term29 N i) = (term29 N i).
Proof. exact (fun_ext (fun n : nat => @lem7612201 N n i)). Qed.
Lemma lem7612203 : (@ex1 nat) = (@ex1 nat).
Proof. exact (eq_refl (@ex1 nat)). Qed.
Lemma lem7612204 {N : Type'} (i : finite_image N) : (term30 N i) = (term30 N i).
Proof. exact (MK_COMB (@lem7612203) (@lem7612202 N i)). Qed.
Lemma lem7612205 {N : Type'} : (term31 N) = (term31 N).
Proof. exact (fun_ext (fun i : finite_image N => @lem7612204 N i)). Qed.
Lemma lem7612206 {N : Type'} : (@all (finite_image N)) = (@all (finite_image N)).
Proof. exact (eq_refl (@all (finite_image N))). Qed.
Lemma lem7612207 {N : Type'} : (term12 N) = (term12 N).
Proof. exact (MK_COMB (@lem7612206 N) (@lem7612205 N)). Qed.
Lemma lem7612208 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7612209 {N : Type'} : (term18 N) = (term18 N).
Proof. exact (MK_COMB (@lem7612208) (@lem7612207 N)). Qed.
Lemma lem7612218 {A : Type'} (n : nat) (i : finite_image A) : (term28 A n i) = (term28 A n i).
Proof. exact (eq_refl (term28 A n i)). Qed.
Lemma lem7612219 {A : Type'} (i : finite_image A) : (term29 A i) = (term29 A i).
Proof. exact (fun_ext (fun n : nat => @lem7612218 A n i)). Qed.
Lemma lem7612220 : (@ex1 nat) = (@ex1 nat).
Proof. exact (eq_refl (@ex1 nat)). Qed.
Lemma lem7612221 {A : Type'} (i : finite_image A) : (term30 A i) = (term30 A i).
Proof. exact (MK_COMB (@lem7612220) (@lem7612219 A i)). Qed.
Lemma lem7612222 {A : Type'} : (term31 A) = (term31 A).
Proof. exact (fun_ext (fun i : finite_image A => @lem7612221 A i)). Qed.
Lemma lem7612223 {A : Type'} : (@all (finite_image A)) = (@all (finite_image A)).
Proof. exact (eq_refl (@all (finite_image A))). Qed.
Lemma lem7612224 {A : Type'} : (term12 A) = (term12 A).
Proof. exact (MK_COMB (@lem7612223 A) (@lem7612222 A)). Qed.
Lemma lem7612225 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7612226 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (MK_COMB (@lem7612225) (@lem7612224 A)). Qed.
Lemma lem7612227 {A N : Type'} : (term21 A N) = (term21 A N).
Proof. exact (MK_COMB (@lem7612226 A) (@lem7612209 N)). Qed.
Lemma lem7612236 {N : Type'} (P : type33 N) (i : nat) : (term32 N P i) = (term32 N P i).
Proof. exact (eq_refl (term32 N P i)). Qed.
Lemma lem7612237 {N : Type'} (P : type33 N) : (term33 N P) = (term33 N P).
Proof. exact (fun_ext (fun i : nat => @lem7612236 N P i)). Qed.
Lemma lem7612238 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7612239 {N : Type'} (P : type33 N) : (term9 N P) = (term9 N P).
Proof. exact (MK_COMB (@lem7612238) (@lem7612237 N P)). Qed.
Lemma lem7612240 {N : Type'} (P : type33 N) (k : finite_image N) : (P k) = (P k).
Proof. exact (eq_refl (P k)). Qed.
Lemma lem7612241 {N : Type'} (P : type33 N) : (term34 N P) = (term34 N P).
Proof. exact (fun_ext (fun k : finite_image N => @lem7612240 N P k)). Qed.
Lemma lem7612242 {N : Type'} : (@all (finite_image N)) = (@all (finite_image N)).
Proof. exact (eq_refl (@all (finite_image N))). Qed.
Lemma lem7612243 {N : Type'} (P : type33 N) : (term8 N P) = (term8 N P).
Proof. exact (MK_COMB (@lem7612242 N) (@lem7612241 N P)). Qed.
Lemma lem7612244 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7612245 {N : Type'} (P : type33 N) : (term35 N P) = (term35 N P).
Proof. exact (MK_COMB (@lem7612244) (@lem7612243 N P)). Qed.
Lemma lem7612246 {N : Type'} (P : type33 N) : ((term8 N P) = (term9 N P)) = ((term8 N P) = (term9 N P)).
Proof. exact (MK_COMB (@lem7612245 N P) (@lem7612239 N P)). Qed.
Lemma lem7612247 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7612248 {N : Type'} (P : type33 N) : (term11 N P) = (term11 N P).
Proof. exact (MK_COMB (@lem7612247) (@lem7612246 N P)). Qed.
Lemma lem7612249 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7612250 {N : Type'} (P : type33 N) : (term22 N P) = (term22 N P).
Proof. exact (MK_COMB (@lem7612249) (@lem7612248 N P)). Qed.
Lemma lem7612251 {A N : Type'} (P : type33 N) : (term23 A N P) = (term23 A N P).
Proof. exact (MK_COMB (@lem7612250 N P) (@lem7612227 A N)). Qed.
Lemma lem7612252 {A N : Type'} : (term25 A N) = (term25 A N).
Proof. exact (fun_ext (fun P : type33 N => @lem7612251 A N P)). Qed.
Lemma lem7612253 {N : Type'} : (@all ((finite_image N) -> Prop)) = (@all ((finite_image N) -> Prop)).
Proof. exact (eq_refl (@all ((finite_image N) -> Prop))). Qed.
Lemma lem7612254 {A N : Type'} : (term27 A N) = (term27 A N).
Proof. exact (MK_COMB (@lem7612253 N) (@lem7612252 A N)). Qed.
Lemma lem7612303 {A N : Type'} : (term26 A N) = (term27 A N).
Proof. exact (TRANS (@lem7612192 A N) (@lem7612254 A N)). Qed.
Lemma lem7612304 {A N : Type'} : (term27 A N) = (term26 A N).
Proof. exact (SYM (@lem7612303 A N)). Qed.
Lemma lem7612305 {N : Type'} (P : type33 N) (h1 : term11 N P) : term11 N P.
Proof. exact (h1). Qed.
Lemma lem7612306 {A : Type'} (h1 : term12 A) : term12 A.
Proof. exact (h1). Qed.
Lemma lem7612307 {N : Type'} (h1 : term12 N) : term12 N.
Proof. exact (h1). Qed.
Lemma lem7612309 {N : Type'} (P : type33 N) (k : finite_image N) : (P k) = (P k).
Proof. exact (eq_refl (P k)). Qed.
Lemma lem7612310 {N : Type'} (P : type33 N) : (term36 N P) = (term37 N P).
Proof. exact (@lem18392 (finite_image N) P). Qed.
Lemma lem7612311 {N : Type'} (P : type33 N) : (term38 N P) = (term39 N P).
Proof. exact (@lem7612310 N (term34 N P)). Qed.
Lemma lem7612312 {N : Type'} (P : type33 N) (k : finite_image N) : (term40 N P k) = (P k).
Proof. exact (eq_refl (term40 N P k)). Qed.
Lemma lem7612313 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7612315 {N : Type'} (P : type33 N) (k : finite_image N) : (term41 N P k) = (term42 N P k).
Proof. exact (MK_COMB (@lem7612313) (@lem7612312 N P k)). Qed.
Lemma lem7612316 {N : Type'} (P : type33 N) : (term43 N P) = (term44 N P).
Proof. exact (fun_ext (fun k : finite_image N => @lem7612315 N P k)). Qed.
Lemma lem7612317 {N : Type'} : (@ex (finite_image N)) = (@ex (finite_image N)).
Proof. exact (eq_refl (@ex (finite_image N))). Qed.
Lemma lem7612318 {N : Type'} (P : type33 N) : (term39 N P) = (term37 N P).
Proof. exact (MK_COMB (@lem7612317 N) (@lem7612316 N P)). Qed.
Lemma lem7612319 {N : Type'} (P : type33 N) : (term38 N P) = (term37 N P).
Proof. exact (TRANS (@lem7612311 N P) (@lem7612318 N P)). Qed.
Lemma lem7612320 {N : Type'} (P : type33 N) : (term34 N P) = (term34 N P).
Proof. exact (fun_ext (fun k : finite_image N => @lem7612309 N P k)). Qed.
Lemma lem7612321 {N : Type'} : (@all (finite_image N)) = (@all (finite_image N)).
Proof. exact (eq_refl (@all (finite_image N))). Qed.
Lemma lem7612322 {N : Type'} (P : type33 N) : (term8 N P) = (term8 N P).
Proof. exact (MK_COMB (@lem7612321 N) (@lem7612320 N P)). Qed.
Lemma lem7612331 {N : Type'} (i : nat) : (term45 N i) = (term46 N i).
Proof. exact (@lem17045 (term47 i) (term48 N i)). Qed.
Lemma lem7612336 {N : Type'} (P : type33 N) (i : nat) : (term49 N P i) = (term49 N P i).
Proof. exact (eq_refl (term49 N P i)). Qed.
Lemma lem7612341 {N : Type'} (P : type33 N) (i : nat) : (term50 N P i) = (term51 N P i).
Proof. exact (@lem17362 (term52 N i) (term49 N P i)). Qed.
Lemma lem7612342 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7612343 {N : Type'} (i : nat) : (term53 N i) = (term54 N i).
Proof. exact (MK_COMB (@lem7612342) (@lem7612331 N i)). Qed.
Lemma lem7612344 {N : Type'} (P : type33 N) (i : nat) : (term55 N P i) = (term56 N P i).
Proof. exact (MK_COMB (@lem7612343 N i) (@lem7612336 N P i)). Qed.
Lemma lem7612345 {N : Type'} (P : type33 N) (i : nat) : (term32 N P i) = (term55 N P i).
Proof. exact (@lem17265 (term52 N i) (term49 N P i)). Qed.
Lemma lem7612346 {N : Type'} (P : type33 N) (i : nat) : (term32 N P i) = (term56 N P i).
Proof. exact (TRANS (@lem7612345 N P i) (@lem7612344 N P i)). Qed.
Lemma lem7612347 (P : nat -> Prop) : (term57 P) = (term58 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem7612348 {N : Type'} (P : type33 N) : (term59 N P) = (term60 N P).
Proof. exact (@lem7612347 (term33 N P)). Qed.
Lemma lem7612349 {N : Type'} (P : type33 N) (i : nat) : (term61 N P i) = (term32 N P i).
Proof. exact (eq_refl (term61 N P i)). Qed.
Lemma lem7612350 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7612351 {N : Type'} (P : type33 N) (i : nat) : (term62 N P i) = (term50 N P i).
Proof. exact (MK_COMB (@lem7612350) (@lem7612349 N P i)). Qed.
Lemma lem7612352 {N : Type'} (P : type33 N) (i : nat) : (term62 N P i) = (term51 N P i).
Proof. exact (TRANS (@lem7612351 N P i) (@lem7612341 N P i)). Qed.
Lemma lem7612353 {N : Type'} (P : type33 N) : (term63 N P) = (term64 N P).
Proof. exact (fun_ext (fun i : nat => @lem7612352 N P i)). Qed.
Lemma lem7612354 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7612355 {N : Type'} (P : type33 N) : (term60 N P) = (term65 N P).
Proof. exact (MK_COMB (@lem7612354) (@lem7612353 N P)). Qed.
Lemma lem7612356 {N : Type'} (P : type33 N) : (term59 N P) = (term65 N P).
Proof. exact (TRANS (@lem7612348 N P) (@lem7612355 N P)). Qed.
Lemma lem7612357 {N : Type'} (P : type33 N) : (term33 N P) = (term66 N P).
Proof. exact (fun_ext (fun i : nat => @lem7612346 N P i)). Qed.
Lemma lem7612358 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7612359 {N : Type'} (P : type33 N) : (term9 N P) = (term67 N P).
Proof. exact (MK_COMB (@lem7612358) (@lem7612357 N P)). Qed.
Lemma lem7612360 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7612361 {N : Type'} (P : type33 N) : (term68 N P) = (term69 N P).
Proof. exact (MK_COMB (@lem7612360) (@lem7612319 N P)). Qed.
Lemma lem7612362 {N : Type'} (P : type33 N) : (term70 N P) = (term71 N P).
Proof. exact (MK_COMB (@lem7612361 N P) (@lem7612359 N P)). Qed.
Lemma lem7612363 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7612364 {N : Type'} (P : type33 N) : (term72 N P) = (term72 N P).
Proof. exact (MK_COMB (@lem7612363) (@lem7612322 N P)). Qed.
Lemma lem7612365 {N : Type'} (P : type33 N) : (term73 N P) = (term74 N P).
Proof. exact (MK_COMB (@lem7612364 N P) (@lem7612356 N P)). Qed.
Lemma lem7612366 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7612367 {N : Type'} (P : type33 N) : (term75 N P) = (term76 N P).
Proof. exact (MK_COMB (@lem7612366) (@lem7612365 N P)). Qed.
Lemma lem7612368 {N : Type'} (P : type33 N) : (term77 N P) = (term78 N P).
Proof. exact (MK_COMB (@lem7612367 N P) (@lem7612362 N P)). Qed.
Lemma lem7612369 {N : Type'} (P : type33 N) : (term11 N P) = (term77 N P).
Proof. exact (@lem17646 (term8 N P) (term9 N P)). Qed.
Lemma lem7612370 {N : Type'} (P : type33 N) : (term11 N P) = (term78 N P).
Proof. exact (TRANS (@lem7612369 N P) (@lem7612368 N P)). Qed.
Lemma lem7612477 {A : Type'} (P : Prop) (Q : A -> Prop) : (term79 A P Q) = (term80 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem7612478 (P : Prop) (Q : nat -> Prop) : (term81 P Q) = (term82 P Q).
Proof. exact (@lem7612477 nat P Q). Qed.
Lemma lem7612479 {N : Type'} (P : type33 N) : (term83 N P) = (term84 N P).
Proof. exact (@lem7612478 (term8 N P) (term64 N P)). Qed.
Lemma lem7612480 {N : Type'} (P : type33 N) (i : nat) : (term85 N P i) = (term51 N P i).
Proof. exact (eq_refl (term85 N P i)). Qed.
Lemma lem7612481 {N : Type'} (P : type33 N) : (term86 N P) = (term64 N P).
Proof. exact (fun_ext (fun i : nat => @lem7612480 N P i)). Qed.
Lemma lem7612482 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7612483 {N : Type'} (P : type33 N) : (term87 N P) = (term65 N P).
Proof. exact (MK_COMB (@lem7612482) (@lem7612481 N P)). Qed.
Lemma lem7612484 {N : Type'} (P : type33 N) : (term72 N P) = (term72 N P).
Proof. exact (eq_refl (term72 N P)). Qed.
Lemma lem7612485 {N : Type'} (P : type33 N) : (term83 N P) = (term74 N P).
Proof. exact (MK_COMB (@lem7612484 N P) (@lem7612483 N P)). Qed.
Lemma lem7612486 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7612487 {N : Type'} (P : type33 N) : (term88 N P) = (term89 N P).
Proof. exact (MK_COMB (@lem7612486) (@lem7612485 N P)). Qed.
Lemma lem7612488 {N : Type'} (P : type33 N) (i : nat) : (term85 N P i) = (term51 N P i).
Proof. exact (eq_refl (term85 N P i)). Qed.
Lemma lem7612489 {N : Type'} (P : type33 N) : (term72 N P) = (term72 N P).
Proof. exact (eq_refl (term72 N P)). Qed.
Lemma lem7612490 {N : Type'} (P : type33 N) (i : nat) : (term90 N P i) = (term91 N P i).
Proof. exact (MK_COMB (@lem7612489 N P) (@lem7612488 N P i)). Qed.
Lemma lem7612491 {N : Type'} (P : type33 N) : (term92 N P) = (term93 N P).
Proof. exact (fun_ext (fun i : nat => @lem7612490 N P i)). Qed.
Lemma lem7612492 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7612493 {N : Type'} (P : type33 N) : (term84 N P) = (term94 N P).
Proof. exact (MK_COMB (@lem7612492) (@lem7612491 N P)). Qed.
Lemma lem7612494 {N : Type'} (P : type33 N) : ((term83 N P) = (term84 N P)) = ((term74 N P) = (term94 N P)).
Proof. exact (MK_COMB (@lem7612487 N P) (@lem7612493 N P)). Qed.
Lemma lem7612495 {N : Type'} (P : type33 N) : (term74 N P) = (term94 N P).
Proof. exact (EQ_MP (@lem7612494 N P) (@lem7612479 N P)). Qed.
Lemma lem7612496 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7612497 {N : Type'} (P : type33 N) : (term76 N P) = (term95 N P).
Proof. exact (MK_COMB (@lem7612496) (@lem7612495 N P)). Qed.
Lemma lem7612499 {A : Type'} (P : A -> Prop) (Q : Prop) : (term96 A P Q) = (term97 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem7612500 {N : Type'} (P : type33 N) (Q : Prop) : (term98 N P Q) = (term99 N P Q).
Proof. exact (@lem7612499 (finite_image N) P Q). Qed.
Lemma lem7612501 {N : Type'} (P : type33 N) : (term100 N P) = (term101 N P).
Proof. exact (@lem7612500 N (term44 N P) (term67 N P)). Qed.
Lemma lem7612502 {N : Type'} (P : type33 N) (k : finite_image N) : (term102 N P k) = (term42 N P k).
Proof. exact (eq_refl (term102 N P k)). Qed.
Lemma lem7612503 {N : Type'} (P : type33 N) : (term103 N P) = (term44 N P).
Proof. exact (fun_ext (fun k : finite_image N => @lem7612502 N P k)). Qed.
Lemma lem7612504 {N : Type'} : (@ex (finite_image N)) = (@ex (finite_image N)).
Proof. exact (eq_refl (@ex (finite_image N))). Qed.
Lemma lem7612505 {N : Type'} (P : type33 N) : (term104 N P) = (term37 N P).
Proof. exact (MK_COMB (@lem7612504 N) (@lem7612503 N P)). Qed.
Lemma lem7612506 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7612507 {N : Type'} (P : type33 N) : (term105 N P) = (term69 N P).
Proof. exact (MK_COMB (@lem7612506) (@lem7612505 N P)). Qed.
Lemma lem7612508 {N : Type'} (P : type33 N) : (term67 N P) = (term67 N P).
Proof. exact (eq_refl (term67 N P)). Qed.
Lemma lem7612509 {N : Type'} (P : type33 N) : (term100 N P) = (term71 N P).
Proof. exact (MK_COMB (@lem7612507 N P) (@lem7612508 N P)). Qed.
Lemma lem7612510 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7612511 {N : Type'} (P : type33 N) : (term106 N P) = (term107 N P).
Proof. exact (MK_COMB (@lem7612510) (@lem7612509 N P)). Qed.
Lemma lem7612512 {N : Type'} (P : type33 N) (k : finite_image N) : (term102 N P k) = (term42 N P k).
Proof. exact (eq_refl (term102 N P k)). Qed.
Lemma lem7612513 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7612514 {N : Type'} (P : type33 N) (k : finite_image N) : (term108 N P k) = (term109 N P k).
Proof. exact (MK_COMB (@lem7612513) (@lem7612512 N P k)). Qed.
Lemma lem7612515 {N : Type'} (P : type33 N) : (term67 N P) = (term67 N P).
Proof. exact (eq_refl (term67 N P)). Qed.
Lemma lem7612516 {N : Type'} (k : finite_image N) (P : type33 N) : (term110 N k P) = (term111 N k P).
Proof. exact (MK_COMB (@lem7612514 N P k) (@lem7612515 N P)). Qed.
Lemma lem7612517 {N : Type'} (P : type33 N) : (term112 N P) = (term113 N P).
Proof. exact (fun_ext (fun k : finite_image N => @lem7612516 N k P)). Qed.
Lemma lem7612518 {N : Type'} : (@ex (finite_image N)) = (@ex (finite_image N)).
Proof. exact (eq_refl (@ex (finite_image N))). Qed.
Lemma lem7612519 {N : Type'} (P : type33 N) : (term101 N P) = (term114 N P).
Proof. exact (MK_COMB (@lem7612518 N) (@lem7612517 N P)). Qed.
Lemma lem7612520 {N : Type'} (P : type33 N) : ((term100 N P) = (term101 N P)) = ((term71 N P) = (term114 N P)).
Proof. exact (MK_COMB (@lem7612511 N P) (@lem7612519 N P)). Qed.
Lemma lem7612521 {N : Type'} (P : type33 N) : (term71 N P) = (term114 N P).
Proof. exact (EQ_MP (@lem7612520 N P) (@lem7612501 N P)). Qed.
Lemma lem7612522 {N : Type'} (P : type33 N) : (term78 N P) = (term115 N P).
Proof. exact (MK_COMB (@lem7612497 N P) (@lem7612521 N P)). Qed.
Lemma lem7612526 {A : Type'} (P : A -> Prop) (Q : Prop) : (term116 A P Q) = (term117 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7612527 (P : nat -> Prop) (Q : Prop) : (term118 P Q) = (term119 P Q).
Proof. exact (@lem7612526 nat P Q). Qed.
Lemma lem7612528 {N : Type'} (P : type33 N) : (term120 N P) = (term121 N P).
Proof. exact (@lem7612527 (term93 N P) (term114 N P)). Qed.
Lemma lem7612529 {N : Type'} (P : type33 N) (i : nat) : (term122 N P i) = (term91 N P i).
Proof. exact (eq_refl (term122 N P i)). Qed.
Lemma lem7612530 {N : Type'} (P : type33 N) : (term123 N P) = (term93 N P).
Proof. exact (fun_ext (fun i : nat => @lem7612529 N P i)). Qed.
Lemma lem7612531 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7612532 {N : Type'} (P : type33 N) : (term124 N P) = (term94 N P).
Proof. exact (MK_COMB (@lem7612531) (@lem7612530 N P)). Qed.
Lemma lem7612533 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7612534 {N : Type'} (P : type33 N) : (term125 N P) = (term95 N P).
Proof. exact (MK_COMB (@lem7612533) (@lem7612532 N P)). Qed.
Lemma lem7612535 {N : Type'} (P : type33 N) : (term114 N P) = (term114 N P).
Proof. exact (eq_refl (term114 N P)). Qed.
Lemma lem7612536 {N : Type'} (P : type33 N) : (term120 N P) = (term115 N P).
Proof. exact (MK_COMB (@lem7612534 N P) (@lem7612535 N P)). Qed.
Lemma lem7612537 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7612538 {N : Type'} (P : type33 N) : (term126 N P) = (term127 N P).
Proof. exact (MK_COMB (@lem7612537) (@lem7612536 N P)). Qed.
Lemma lem7612539 {N : Type'} (P : type33 N) (i : nat) : (term122 N P i) = (term91 N P i).
Proof. exact (eq_refl (term122 N P i)). Qed.
Lemma lem7612540 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7612541 {N : Type'} (P : type33 N) (i : nat) : (term128 N P i) = (term129 N P i).
Proof. exact (MK_COMB (@lem7612540) (@lem7612539 N P i)). Qed.
Lemma lem7612542 {N : Type'} (P : type33 N) : (term114 N P) = (term114 N P).
Proof. exact (eq_refl (term114 N P)). Qed.
Lemma lem7612543 {N : Type'} (i : nat) (P : type33 N) : (term130 N i P) = (term131 N i P).
Proof. exact (MK_COMB (@lem7612541 N P i) (@lem7612542 N P)). Qed.
Lemma lem7612544 {N : Type'} (P : type33 N) : (term132 N P) = (term133 N P).
Proof. exact (fun_ext (fun i : nat => @lem7612543 N i P)). Qed.
Lemma lem7612545 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7612546 {N : Type'} (P : type33 N) : (term121 N P) = (term134 N P).
Proof. exact (MK_COMB (@lem7612545) (@lem7612544 N P)). Qed.
Lemma lem7612547 {N : Type'} (P : type33 N) : ((term120 N P) = (term121 N P)) = ((term115 N P) = (term134 N P)).
Proof. exact (MK_COMB (@lem7612538 N P) (@lem7612546 N P)). Qed.
Lemma lem7612548 {N : Type'} (P : type33 N) : (term115 N P) = (term134 N P).
Proof. exact (EQ_MP (@lem7612547 N P) (@lem7612528 N P)). Qed.
Lemma lem7612550 {A : Type'} (P : Prop) (Q : A -> Prop) : (term135 A P Q) = (term136 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7612551 {N : Type'} (P : Prop) (Q : type33 N) : (term137 N P Q) = (term138 N P Q).
Proof. exact (@lem7612550 (finite_image N) P Q). Qed.
Lemma lem7612552 {N : Type'} (i : nat) (P : type33 N) : (term139 N i P) = (term140 N i P).
Proof. exact (@lem7612551 N (term91 N P i) (term113 N P)). Qed.
Lemma lem7612553 {N : Type'} (k : finite_image N) (P : type33 N) : (term141 N P k) = (term111 N k P).
Proof. exact (eq_refl (term141 N P k)). Qed.
Lemma lem7612554 {N : Type'} (P : type33 N) : (term142 N P) = (term113 N P).
Proof. exact (fun_ext (fun k : finite_image N => @lem7612553 N k P)). Qed.
Lemma lem7612555 {N : Type'} : (@ex (finite_image N)) = (@ex (finite_image N)).
Proof. exact (eq_refl (@ex (finite_image N))). Qed.
Lemma lem7612556 {N : Type'} (P : type33 N) : (term143 N P) = (term114 N P).
Proof. exact (MK_COMB (@lem7612555 N) (@lem7612554 N P)). Qed.
Lemma lem7612557 {N : Type'} (P : type33 N) (i : nat) : (term129 N P i) = (term129 N P i).
Proof. exact (eq_refl (term129 N P i)). Qed.
Lemma lem7612558 {N : Type'} (i : nat) (P : type33 N) : (term139 N i P) = (term131 N i P).
Proof. exact (MK_COMB (@lem7612557 N P i) (@lem7612556 N P)). Qed.
Lemma lem7612559 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7612560 {N : Type'} (i : nat) (P : type33 N) : (term144 N i P) = (term145 N i P).
Proof. exact (MK_COMB (@lem7612559) (@lem7612558 N i P)). Qed.
Lemma lem7612561 {N : Type'} (k : finite_image N) (P : type33 N) : (term141 N P k) = (term111 N k P).
Proof. exact (eq_refl (term141 N P k)). Qed.
Lemma lem7612562 {N : Type'} (P : type33 N) (i : nat) : (term129 N P i) = (term129 N P i).
Proof. exact (eq_refl (term129 N P i)). Qed.
Lemma lem7612563 {N : Type'} (i : nat) (k : finite_image N) (P : type33 N) : (term146 N i P k) = (term147 N i k P).
Proof. exact (MK_COMB (@lem7612562 N P i) (@lem7612561 N k P)). Qed.
Lemma lem7612564 {N : Type'} (i : nat) (P : type33 N) : (term148 N i P) = (term149 N i P).
Proof. exact (fun_ext (fun k : finite_image N => @lem7612563 N i k P)). Qed.
Lemma lem7612565 {N : Type'} : (@ex (finite_image N)) = (@ex (finite_image N)).
Proof. exact (eq_refl (@ex (finite_image N))). Qed.
Lemma lem7612566 {N : Type'} (i : nat) (P : type33 N) : (term140 N i P) = (term150 N i P).
Proof. exact (MK_COMB (@lem7612565 N) (@lem7612564 N i P)). Qed.
Lemma lem7612567 {N : Type'} (i : nat) (P : type33 N) : ((term139 N i P) = (term140 N i P)) = ((term131 N i P) = (term150 N i P)).
Proof. exact (MK_COMB (@lem7612560 N i P) (@lem7612566 N i P)). Qed.
Lemma lem7612568 {N : Type'} (i : nat) (P : type33 N) : (term131 N i P) = (term150 N i P).
Proof. exact (EQ_MP (@lem7612567 N i P) (@lem7612552 N i P)). Qed.
Lemma lem7612569 {N : Type'} (P : type33 N) : (term133 N P) = (term151 N P).
Proof. exact (fun_ext (fun i : nat => @lem7612568 N i P)). Qed.
Lemma lem7612570 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7612571 {N : Type'} (P : type33 N) : (term134 N P) = (term152 N P).
Proof. exact (MK_COMB (@lem7612570) (@lem7612569 N P)). Qed.
Lemma lem7612572 {N : Type'} (P : type33 N) : (term115 N P) = (term152 N P).
Proof. exact (TRANS (@lem7612548 N P) (@lem7612571 N P)). Qed.
Lemma lem7612574 {N : Type'} (P : type33 N) : (term78 N P) = (term152 N P).
Proof. exact (TRANS (@lem7612522 N P) (@lem7612572 N P)). Qed.
Lemma lem7612575 {N : Type'} (P : type33 N) : (term11 N P) = (term152 N P).
Proof. exact (TRANS (@lem7612370 N P) (@lem7612574 N P)). Qed.
Lemma lem7612576 {N : Type'} (P : type33 N) (h1 : term11 N P) : term152 N P.
Proof. exact (EQ_MP (@lem7612575 N P) (@lem7612305 N P h1)). Qed.
Lemma lem7612587 {A : Type'} (n : nat) (i : finite_image A) : (term153 A n i) = (term154 A n i).
Proof. exact (@lem17045 (term48 A n) ((@finite_index A n) = i)). Qed.
Lemma lem7612592 (n : nat) : (term155 n) = (term155 n).
Proof. exact (eq_refl (term155 n)). Qed.
Lemma lem7612593 {A : Type'} (n : nat) (i : finite_image A) : (term156 A n i) = (term157 A n i).
Proof. exact (MK_COMB (@lem7612592 n) (@lem7612587 A n i)). Qed.
Lemma lem7612594 {A : Type'} (n : nat) (i : finite_image A) : (term158 A n i) = (term156 A n i).
Proof. exact (@lem17045 (term47 n) (term159 A n i)). Qed.
Lemma lem7612595 {A : Type'} (n : nat) (i : finite_image A) : (term158 A n i) = (term157 A n i).
Proof. exact (TRANS (@lem7612594 A n i) (@lem7612593 A n i)). Qed.
Lemma lem7612600 (n' : nat) (n : nat) : (n' = n) = (n' = n).
Proof. exact (eq_refl (n' = n)). Qed.
Lemma lem7612601 {A : Type'} (n : nat) (i : finite_image A) : (term160 A i n) = (term28 A n i).
Proof. exact (eq_refl (term160 A i n)). Qed.
Lemma lem7612602 {A : Type'} (n' : nat) (i : finite_image A) : (term160 A i n') = (term28 A n' i).
Proof. exact (eq_refl (term160 A i n')). Qed.
Lemma lem7612603 {A : Type'} (n' : nat) (i : finite_image A) : (term158 A n' i) = (term157 A n' i).
Proof. exact (@lem7612595 A n' i). Qed.
Lemma lem7612604 (P : nat -> Prop) : (@ex1 nat P) = (term161 P).
Proof. exact (@lem18897 nat P). Qed.
Lemma lem7612605 {A : Type'} (i : finite_image A) : (term30 A i) = (term162 A i).
Proof. exact (@lem7612604 (term29 A i)). Qed.
Lemma lem7612606 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7612607 {A : Type'} (n' : nat) (i : finite_image A) : (term163 A i n') = (term158 A n' i).
Proof. exact (MK_COMB (@lem7612606) (@lem7612602 A n' i)). Qed.
Lemma lem7612608 {A : Type'} (n' : nat) (i : finite_image A) : (term163 A i n') = (term157 A n' i).
Proof. exact (TRANS (@lem7612607 A n' i) (@lem7612603 A n' i)). Qed.
Lemma lem7612609 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7612610 {A : Type'} (n' : nat) (i : finite_image A) : (term164 A i n') = (term165 A n' i).
Proof. exact (MK_COMB (@lem7612609) (@lem7612608 A n' i)). Qed.
Lemma lem7612611 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) : (term166 A i n' n) = (term167 A i n' n).
Proof. exact (MK_COMB (@lem7612610 A n' i) (@lem7612600 n' n)). Qed.
Lemma lem7612612 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7612613 {A : Type'} (n : nat) (i : finite_image A) : (term163 A i n) = (term158 A n i).
Proof. exact (MK_COMB (@lem7612612) (@lem7612601 A n i)). Qed.
Lemma lem7612614 {A : Type'} (n : nat) (i : finite_image A) : (term163 A i n) = (term157 A n i).
Proof. exact (TRANS (@lem7612613 A n i) (@lem7612595 A n i)). Qed.
Lemma lem7612615 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7612616 {A : Type'} (n : nat) (i : finite_image A) : (term164 A i n) = (term165 A n i).
Proof. exact (MK_COMB (@lem7612615) (@lem7612614 A n i)). Qed.
Lemma lem7612617 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) : (term168 A i n' n) = (term169 A i n' n).
Proof. exact (MK_COMB (@lem7612616 A n i) (@lem7612611 A i n' n)). Qed.
Lemma lem7612618 {A : Type'} (i : finite_image A) (n : nat) : (term170 A i n) = (term171 A i n).
Proof. exact (fun_ext (fun n' : nat => @lem7612617 A i n' n)). Qed.
Lemma lem7612619 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7612620 {A : Type'} (i : finite_image A) (n : nat) : (term172 A i n) = (term173 A i n).
Proof. exact (MK_COMB (@lem7612619) (@lem7612618 A i n)). Qed.
Lemma lem7612621 {A : Type'} (i : finite_image A) : (term174 A i) = (term175 A i).
Proof. exact (fun_ext (fun n : nat => @lem7612620 A i n)). Qed.
Lemma lem7612622 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7612623 {A : Type'} (i : finite_image A) : (term176 A i) = (term177 A i).
Proof. exact (MK_COMB (@lem7612622) (@lem7612621 A i)). Qed.
Lemma lem7612624 {A : Type'} (n : nat) (i : finite_image A) : (term160 A i n) = (term28 A n i).
Proof. exact (eq_refl (term160 A i n)). Qed.
Lemma lem7612625 {A : Type'} (i : finite_image A) : (term178 A i) = (term29 A i).
Proof. exact (fun_ext (fun n : nat => @lem7612624 A n i)). Qed.
Lemma lem7612626 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7612627 {A : Type'} (i : finite_image A) : (term179 A i) = (term180 A i).
Proof. exact (MK_COMB (@lem7612626) (@lem7612625 A i)). Qed.
Lemma lem7612628 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7612629 {A : Type'} (i : finite_image A) : (term181 A i) = (term182 A i).
Proof. exact (MK_COMB (@lem7612628) (@lem7612627 A i)). Qed.
Lemma lem7612630 {A : Type'} (i : finite_image A) : (term162 A i) = (term183 A i).
Proof. exact (MK_COMB (@lem7612629 A i) (@lem7612623 A i)). Qed.
Lemma lem7612631 {A : Type'} (i : finite_image A) : (term30 A i) = (term183 A i).
Proof. exact (TRANS (@lem7612605 A i) (@lem7612630 A i)). Qed.
Lemma lem7612632 {A : Type'} : (term31 A) = (term184 A).
Proof. exact (fun_ext (fun i : finite_image A => @lem7612631 A i)). Qed.
Lemma lem7612633 {A : Type'} : (@all (finite_image A)) = (@all (finite_image A)).
Proof. exact (eq_refl (@all (finite_image A))). Qed.
Lemma lem7612634 {A : Type'} : (term12 A) = (term185 A).
Proof. exact (MK_COMB (@lem7612633 A) (@lem7612632 A)). Qed.
Lemma lem7612636 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term186 A P Q) = (term187 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7612637 {A : Type'} (P : type33 A) (Q : type33 A) : (term188 A P Q) = (term189 A P Q).
Proof. exact (@lem7612636 (finite_image A) P Q). Qed.
Lemma lem7612638 {A : Type'} : (term190 A) = (term191 A).
Proof. exact (@lem7612637 A (term192 A) (term193 A)). Qed.
Lemma lem7612639 {A : Type'} (i : finite_image A) : (term194 A i) = (term180 A i).
Proof. exact (eq_refl (term194 A i)). Qed.
Lemma lem7612640 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7612641 {A : Type'} (i : finite_image A) : (term195 A i) = (term182 A i).
Proof. exact (MK_COMB (@lem7612640) (@lem7612639 A i)). Qed.
Lemma lem7612642 {A : Type'} (i : finite_image A) : (term196 A i) = (term177 A i).
Proof. exact (eq_refl (term196 A i)). Qed.
Lemma lem7612643 {A : Type'} (i : finite_image A) : (term197 A i) = (term183 A i).
Proof. exact (MK_COMB (@lem7612641 A i) (@lem7612642 A i)). Qed.
Lemma lem7612644 {A : Type'} : (term198 A) = (term184 A).
Proof. exact (fun_ext (fun i : finite_image A => @lem7612643 A i)). Qed.
Lemma lem7612645 {A : Type'} : (@all (finite_image A)) = (@all (finite_image A)).
Proof. exact (eq_refl (@all (finite_image A))). Qed.
Lemma lem7612646 {A : Type'} : (term190 A) = (term185 A).
Proof. exact (MK_COMB (@lem7612645 A) (@lem7612644 A)). Qed.
Lemma lem7612647 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7612648 {A : Type'} : (term199 A) = (term200 A).
Proof. exact (MK_COMB (@lem7612647) (@lem7612646 A)). Qed.
Lemma lem7612649 {A : Type'} (i : finite_image A) : (term194 A i) = (term180 A i).
Proof. exact (eq_refl (term194 A i)). Qed.
Lemma lem7612650 {A : Type'} : (term201 A) = (term192 A).
Proof. exact (fun_ext (fun i : finite_image A => @lem7612649 A i)). Qed.
Lemma lem7612651 {A : Type'} : (@all (finite_image A)) = (@all (finite_image A)).
Proof. exact (eq_refl (@all (finite_image A))). Qed.
Lemma lem7612652 {A : Type'} : (term202 A) = (term203 A).
Proof. exact (MK_COMB (@lem7612651 A) (@lem7612650 A)). Qed.
Lemma lem7612653 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7612654 {A : Type'} : (term204 A) = (term205 A).
Proof. exact (MK_COMB (@lem7612653) (@lem7612652 A)). Qed.
Lemma lem7612655 {A : Type'} (i : finite_image A) : (term196 A i) = (term177 A i).
Proof. exact (eq_refl (term196 A i)). Qed.
Lemma lem7612656 {A : Type'} : (term206 A) = (term193 A).
Proof. exact (fun_ext (fun i : finite_image A => @lem7612655 A i)). Qed.
Lemma lem7612657 {A : Type'} : (@all (finite_image A)) = (@all (finite_image A)).
Proof. exact (eq_refl (@all (finite_image A))). Qed.
Lemma lem7612658 {A : Type'} : (term207 A) = (term208 A).
Proof. exact (MK_COMB (@lem7612657 A) (@lem7612656 A)). Qed.
Lemma lem7612659 {A : Type'} : (term191 A) = (term209 A).
Proof. exact (MK_COMB (@lem7612654 A) (@lem7612658 A)). Qed.
Lemma lem7612660 {A : Type'} : ((term190 A) = (term191 A)) = ((term185 A) = (term209 A)).
Proof. exact (MK_COMB (@lem7612648 A) (@lem7612659 A)). Qed.
Lemma lem7612661 {A : Type'} : (term185 A) = (term209 A).
Proof. exact (EQ_MP (@lem7612660 A) (@lem7612638 A)). Qed.
Lemma lem7612723 {A : Type'} (P : Prop) (Q : A -> Prop) : (term210 A P Q) = (term211 A P Q).
Proof. exact (EQ_MP (@lem18941 A P Q) (@lem18940 A P Q)). Qed.
Lemma lem7612724 (P : Prop) (Q : nat -> Prop) : (term212 P Q) = (term213 P Q).
Proof. exact (@lem7612723 nat P Q). Qed.
Lemma lem7612725 {A : Type'} (i : finite_image A) (n : nat) : (term214 A i n) = (term215 A i n).
Proof. exact (@lem7612724 (term157 A n i) (term216 A i n)). Qed.
Lemma lem7612726 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) : (term217 A i n n') = (term167 A i n' n).
Proof. exact (eq_refl (term217 A i n n')). Qed.
Lemma lem7612727 {A : Type'} (n : nat) (i : finite_image A) : (term165 A n i) = (term165 A n i).
Proof. exact (eq_refl (term165 A n i)). Qed.
Lemma lem7612728 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) : (term218 A i n n') = (term169 A i n' n).
Proof. exact (MK_COMB (@lem7612727 A n i) (@lem7612726 A i n' n)). Qed.
Lemma lem7612729 {A : Type'} (i : finite_image A) (n : nat) : (term219 A i n) = (term171 A i n).
Proof. exact (fun_ext (fun n' : nat => @lem7612728 A i n' n)). Qed.
Lemma lem7612730 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7612731 {A : Type'} (i : finite_image A) (n : nat) : (term214 A i n) = (term173 A i n).
Proof. exact (MK_COMB (@lem7612730) (@lem7612729 A i n)). Qed.
Lemma lem7612732 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7612733 {A : Type'} (i : finite_image A) (n : nat) : (term220 A i n) = (term221 A i n).
Proof. exact (MK_COMB (@lem7612732) (@lem7612731 A i n)). Qed.
Lemma lem7612734 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) : (term217 A i n n') = (term167 A i n' n).
Proof. exact (eq_refl (term217 A i n n')). Qed.
Lemma lem7612735 {A : Type'} (i : finite_image A) (n : nat) : (term222 A i n) = (term216 A i n).
Proof. exact (fun_ext (fun n' : nat => @lem7612734 A i n' n)). Qed.
Lemma lem7612736 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7612737 {A : Type'} (i : finite_image A) (n : nat) : (term223 A i n) = (term224 A i n).
Proof. exact (MK_COMB (@lem7612736) (@lem7612735 A i n)). Qed.
Lemma lem7612738 {A : Type'} (n : nat) (i : finite_image A) : (term165 A n i) = (term165 A n i).
Proof. exact (eq_refl (term165 A n i)). Qed.
Lemma lem7612739 {A : Type'} (i : finite_image A) (n : nat) : (term215 A i n) = (term225 A i n).
Proof. exact (MK_COMB (@lem7612738 A n i) (@lem7612737 A i n)). Qed.
Lemma lem7612740 {A : Type'} (i : finite_image A) (n : nat) : ((term214 A i n) = (term215 A i n)) = ((term173 A i n) = (term225 A i n)).
Proof. exact (MK_COMB (@lem7612733 A i n) (@lem7612739 A i n)). Qed.
Lemma lem7612741 {A : Type'} (i : finite_image A) (n : nat) : (term173 A i n) = (term225 A i n).
Proof. exact (EQ_MP (@lem7612740 A i n) (@lem7612725 A i n)). Qed.
Lemma lem7612790 {A : Type'} (i : finite_image A) : (term175 A i) = (term226 A i).
Proof. exact (fun_ext (fun n : nat => @lem7612741 A i n)). Qed.
Lemma lem7612791 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7612792 {A : Type'} (i : finite_image A) : (term177 A i) = (term227 A i).
Proof. exact (MK_COMB (@lem7612791) (@lem7612790 A i)). Qed.
Lemma lem7612841 {A : Type'} : (term193 A) = (term228 A).
Proof. exact (fun_ext (fun i : finite_image A => @lem7612792 A i)). Qed.
Lemma lem7612842 {A : Type'} : (@all (finite_image A)) = (@all (finite_image A)).
Proof. exact (eq_refl (@all (finite_image A))). Qed.
Lemma lem7612843 {A : Type'} : (term208 A) = (term229 A).
Proof. exact (MK_COMB (@lem7612842 A) (@lem7612841 A)). Qed.
Lemma lem7612848 {A : Type'} : (term205 A) = (term205 A).
Proof. exact (eq_refl (term205 A)). Qed.
Lemma lem7612849 {A : Type'} : (term209 A) = (term230 A).
Proof. exact (MK_COMB (@lem7612848 A) (@lem7612843 A)). Qed.
Lemma lem7612850 {A : Type'} : (term185 A) = (term230 A).
Proof. exact (TRANS (@lem7612661 A) (@lem7612849 A)). Qed.
Lemma lem7612852 {A B : Type'} (P : type1413 A B) : (term231 A B P) = (term232 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7612853 {A : Type'} (P : type32 A) : (term233 A P) = (term234 A P).
Proof. exact (@lem7612852 (finite_image A) nat P). Qed.
Lemma lem7612854 {A : Type'} : (term235 A) = (term236 A).
Proof. exact (@lem7612853 A (term237 A)). Qed.
Lemma lem7612855 {A : Type'} (i : finite_image A) : (term238 A i) = (term29 A i).
Proof. exact (eq_refl (term238 A i)). Qed.
Lemma lem7612856 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7612857 {A : Type'} (i : finite_image A) (n : nat) : (term239 A i n) = (term160 A i n).
Proof. exact (MK_COMB (@lem7612855 A i) (@lem7612856 n)). Qed.
Lemma lem7612858 {A : Type'} (n : nat) (i : finite_image A) : (term160 A i n) = (term28 A n i).
Proof. exact (eq_refl (term160 A i n)). Qed.
Lemma lem7612859 {A : Type'} (n : nat) (i : finite_image A) : (term239 A i n) = (term28 A n i).
Proof. exact (TRANS (@lem7612857 A i n) (@lem7612858 A n i)). Qed.
Lemma lem7612860 {A : Type'} (i : finite_image A) : (term240 A i) = (term29 A i).
Proof. exact (fun_ext (fun n : nat => @lem7612859 A n i)). Qed.
Lemma lem7612861 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7612862 {A : Type'} (i : finite_image A) : (term241 A i) = (term180 A i).
Proof. exact (MK_COMB (@lem7612861) (@lem7612860 A i)). Qed.
Lemma lem7612863 {A : Type'} : (term242 A) = (term192 A).
Proof. exact (fun_ext (fun i : finite_image A => @lem7612862 A i)). Qed.
Lemma lem7612864 {A : Type'} : (@all (finite_image A)) = (@all (finite_image A)).
Proof. exact (eq_refl (@all (finite_image A))). Qed.
Lemma lem7612865 {A : Type'} : (term235 A) = (term203 A).
Proof. exact (MK_COMB (@lem7612864 A) (@lem7612863 A)). Qed.
Lemma lem7612866 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7612867 {A : Type'} : (term243 A) = (term244 A).
Proof. exact (MK_COMB (@lem7612866) (@lem7612865 A)). Qed.
Lemma lem7612868 {A : Type'} (i : finite_image A) : (term238 A i) = (term29 A i).
Proof. exact (eq_refl (term238 A i)). Qed.
Lemma lem7612869 {A : Type'} (n : type34 A) (i : finite_image A) : (n i) = (n i).
Proof. exact (eq_refl (n i)). Qed.
Lemma lem7612870 {A : Type'} (n : type34 A) (i : finite_image A) : (term245 A n i) = (term246 A n i).
Proof. exact (MK_COMB (@lem7612868 A i) (@lem7612869 A n i)). Qed.
Lemma lem7612871 {A : Type'} (n : type34 A) (i : finite_image A) : (term246 A n i) = (term247 A n i).
Proof. exact (eq_refl (term246 A n i)). Qed.
Lemma lem7612872 {A : Type'} (n : type34 A) (i : finite_image A) : (term245 A n i) = (term247 A n i).
Proof. exact (TRANS (@lem7612870 A n i) (@lem7612871 A n i)). Qed.
Lemma lem7612873 {A : Type'} (n : type34 A) : (term248 A n) = (term249 A n).
Proof. exact (fun_ext (fun i : finite_image A => @lem7612872 A n i)). Qed.
Lemma lem7612874 {A : Type'} : (@all (finite_image A)) = (@all (finite_image A)).
Proof. exact (eq_refl (@all (finite_image A))). Qed.
Lemma lem7612875 {A : Type'} (n : type34 A) : (term250 A n) = (term251 A n).
Proof. exact (MK_COMB (@lem7612874 A) (@lem7612873 A n)). Qed.
Lemma lem7612876 {A : Type'} : (term252 A) = (term253 A).
Proof. exact (fun_ext (fun n : type34 A => @lem7612875 A n)). Qed.
Lemma lem7612877 {A : Type'} : (@ex ((finite_image A) -> nat)) = (@ex ((finite_image A) -> nat)).
Proof. exact (eq_refl (@ex ((finite_image A) -> nat))). Qed.
Lemma lem7612878 {A : Type'} : (term236 A) = (term254 A).
Proof. exact (MK_COMB (@lem7612877 A) (@lem7612876 A)). Qed.
Lemma lem7612879 {A : Type'} : ((term235 A) = (term236 A)) = ((term203 A) = (term254 A)).
Proof. exact (MK_COMB (@lem7612867 A) (@lem7612878 A)). Qed.
Lemma lem7612880 {A : Type'} : (term203 A) = (term254 A).
Proof. exact (EQ_MP (@lem7612879 A) (@lem7612854 A)). Qed.
Lemma lem7612881 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7612882 {A : Type'} : (term205 A) = (term255 A).
Proof. exact (MK_COMB (@lem7612881) (@lem7612880 A)). Qed.
Lemma lem7612883 {A : Type'} : (term229 A) = (term229 A).
Proof. exact (eq_refl (term229 A)). Qed.
Lemma lem7612884 {A : Type'} : (term230 A) = (term256 A).
Proof. exact (MK_COMB (@lem7612882 A) (@lem7612883 A)). Qed.
Lemma lem7612886 {A : Type'} (P : A -> Prop) (Q : Prop) : (term96 A P Q) = (term97 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem7612887 {A : Type'} (P : type60 A) (Q : Prop) : (term257 A P Q) = (term258 A P Q).
Proof. exact (@lem7612886 (type34 A) P Q). Qed.
Lemma lem7612888 {A : Type'} : (term259 A) = (term260 A).
Proof. exact (@lem7612887 A (term253 A) (term229 A)). Qed.
Lemma lem7612889 {A : Type'} (n : type34 A) : (term261 A n) = (term251 A n).
Proof. exact (eq_refl (term261 A n)). Qed.
Lemma lem7612890 {A : Type'} : (term262 A) = (term253 A).
Proof. exact (fun_ext (fun n : type34 A => @lem7612889 A n)). Qed.
Lemma lem7612891 {A : Type'} : (@ex ((finite_image A) -> nat)) = (@ex ((finite_image A) -> nat)).
Proof. exact (eq_refl (@ex ((finite_image A) -> nat))). Qed.
Lemma lem7612892 {A : Type'} : (term263 A) = (term254 A).
Proof. exact (MK_COMB (@lem7612891 A) (@lem7612890 A)). Qed.
Lemma lem7612893 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7612894 {A : Type'} : (term264 A) = (term255 A).
Proof. exact (MK_COMB (@lem7612893) (@lem7612892 A)). Qed.
Lemma lem7612895 {A : Type'} : (term229 A) = (term229 A).
Proof. exact (eq_refl (term229 A)). Qed.
Lemma lem7612896 {A : Type'} : (term259 A) = (term256 A).
Proof. exact (MK_COMB (@lem7612894 A) (@lem7612895 A)). Qed.
Lemma lem7612897 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7612898 {A : Type'} : (term265 A) = (term266 A).
Proof. exact (MK_COMB (@lem7612897) (@lem7612896 A)). Qed.
Lemma lem7612899 {A : Type'} (n : type34 A) : (term261 A n) = (term251 A n).
Proof. exact (eq_refl (term261 A n)). Qed.
Lemma lem7612900 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7612901 {A : Type'} (n : type34 A) : (term267 A n) = (term268 A n).
Proof. exact (MK_COMB (@lem7612900) (@lem7612899 A n)). Qed.
Lemma lem7612902 {A : Type'} : (term229 A) = (term229 A).
Proof. exact (eq_refl (term229 A)). Qed.
Lemma lem7612903 {A : Type'} (n : type34 A) : (term269 A n) = (term270 A n).
Proof. exact (MK_COMB (@lem7612901 A n) (@lem7612902 A)). Qed.
Lemma lem7612904 {A : Type'} : (term271 A) = (term272 A).
Proof. exact (fun_ext (fun n : type34 A => @lem7612903 A n)). Qed.
Lemma lem7612905 {A : Type'} : (@ex ((finite_image A) -> nat)) = (@ex ((finite_image A) -> nat)).
Proof. exact (eq_refl (@ex ((finite_image A) -> nat))). Qed.
Lemma lem7612906 {A : Type'} : (term260 A) = (term273 A).
Proof. exact (MK_COMB (@lem7612905 A) (@lem7612904 A)). Qed.
Lemma lem7612907 {A : Type'} : ((term259 A) = (term260 A)) = ((term256 A) = (term273 A)).
Proof. exact (MK_COMB (@lem7612898 A) (@lem7612906 A)). Qed.
Lemma lem7612908 {A : Type'} : (term256 A) = (term273 A).
Proof. exact (EQ_MP (@lem7612907 A) (@lem7612888 A)). Qed.
Lemma lem7612909 {A : Type'} : (term230 A) = (term273 A).
Proof. exact (TRANS (@lem7612884 A) (@lem7612908 A)). Qed.
Lemma lem7612910 {A : Type'} : (term185 A) = (term273 A).
Proof. exact (TRANS (@lem7612850 A) (@lem7612909 A)). Qed.
Lemma lem7612911 {A : Type'} : (term12 A) = (term273 A).
Proof. exact (TRANS (@lem7612634 A) (@lem7612910 A)). Qed.
Lemma lem7612912 {A : Type'} (h1 : term12 A) : term273 A.
Proof. exact (EQ_MP (@lem7612911 A) (@lem7612306 A h1)). Qed.
Lemma lem7612923 {N : Type'} (n : nat) (i : finite_image N) : (term153 N n i) = (term154 N n i).
Proof. exact (@lem17045 (term48 N n) ((@finite_index N n) = i)). Qed.
Lemma lem7612928 (n : nat) : (term155 n) = (term155 n).
Proof. exact (eq_refl (term155 n)). Qed.
Lemma lem7612929 {N : Type'} (n : nat) (i : finite_image N) : (term156 N n i) = (term157 N n i).
Proof. exact (MK_COMB (@lem7612928 n) (@lem7612923 N n i)). Qed.
Lemma lem7612930 {N : Type'} (n : nat) (i : finite_image N) : (term158 N n i) = (term156 N n i).
Proof. exact (@lem17045 (term47 n) (term159 N n i)). Qed.
Lemma lem7612931 {N : Type'} (n : nat) (i : finite_image N) : (term158 N n i) = (term157 N n i).
Proof. exact (TRANS (@lem7612930 N n i) (@lem7612929 N n i)). Qed.
Lemma lem7612936 (n' : nat) (n : nat) : (n' = n) = (n' = n).
Proof. exact (eq_refl (n' = n)). Qed.
Lemma lem7612937 {N : Type'} (n : nat) (i : finite_image N) : (term160 N i n) = (term28 N n i).
Proof. exact (eq_refl (term160 N i n)). Qed.
Lemma lem7612938 {N : Type'} (n' : nat) (i : finite_image N) : (term160 N i n') = (term28 N n' i).
Proof. exact (eq_refl (term160 N i n')). Qed.
Lemma lem7612939 {N : Type'} (n' : nat) (i : finite_image N) : (term158 N n' i) = (term157 N n' i).
Proof. exact (@lem7612931 N n' i). Qed.
Lemma lem7612940 (P : nat -> Prop) : (@ex1 nat P) = (term161 P).
Proof. exact (@lem18897 nat P). Qed.
Lemma lem7612941 {N : Type'} (i : finite_image N) : (term30 N i) = (term162 N i).
Proof. exact (@lem7612940 (term29 N i)). Qed.
Lemma lem7612942 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7612943 {N : Type'} (n' : nat) (i : finite_image N) : (term163 N i n') = (term158 N n' i).
Proof. exact (MK_COMB (@lem7612942) (@lem7612938 N n' i)). Qed.
Lemma lem7612944 {N : Type'} (n' : nat) (i : finite_image N) : (term163 N i n') = (term157 N n' i).
Proof. exact (TRANS (@lem7612943 N n' i) (@lem7612939 N n' i)). Qed.
Lemma lem7612945 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7612946 {N : Type'} (n' : nat) (i : finite_image N) : (term164 N i n') = (term165 N n' i).
Proof. exact (MK_COMB (@lem7612945) (@lem7612944 N n' i)). Qed.
Lemma lem7612947 {N : Type'} (i : finite_image N) (n' : nat) (n : nat) : (term166 N i n' n) = (term167 N i n' n).
Proof. exact (MK_COMB (@lem7612946 N n' i) (@lem7612936 n' n)). Qed.
Lemma lem7612948 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7612949 {N : Type'} (n : nat) (i : finite_image N) : (term163 N i n) = (term158 N n i).
Proof. exact (MK_COMB (@lem7612948) (@lem7612937 N n i)). Qed.
Lemma lem7612950 {N : Type'} (n : nat) (i : finite_image N) : (term163 N i n) = (term157 N n i).
Proof. exact (TRANS (@lem7612949 N n i) (@lem7612931 N n i)). Qed.
Lemma lem7612951 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7612952 {N : Type'} (n : nat) (i : finite_image N) : (term164 N i n) = (term165 N n i).
Proof. exact (MK_COMB (@lem7612951) (@lem7612950 N n i)). Qed.
Lemma lem7612953 {N : Type'} (i : finite_image N) (n' : nat) (n : nat) : (term168 N i n' n) = (term169 N i n' n).
Proof. exact (MK_COMB (@lem7612952 N n i) (@lem7612947 N i n' n)). Qed.
Lemma lem7612954 {N : Type'} (i : finite_image N) (n : nat) : (term170 N i n) = (term171 N i n).
Proof. exact (fun_ext (fun n' : nat => @lem7612953 N i n' n)). Qed.
Lemma lem7612955 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7612956 {N : Type'} (i : finite_image N) (n : nat) : (term172 N i n) = (term173 N i n).
Proof. exact (MK_COMB (@lem7612955) (@lem7612954 N i n)). Qed.
Lemma lem7612957 {N : Type'} (i : finite_image N) : (term174 N i) = (term175 N i).
Proof. exact (fun_ext (fun n : nat => @lem7612956 N i n)). Qed.
Lemma lem7612958 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7612959 {N : Type'} (i : finite_image N) : (term176 N i) = (term177 N i).
Proof. exact (MK_COMB (@lem7612958) (@lem7612957 N i)). Qed.
Lemma lem7612960 {N : Type'} (n : nat) (i : finite_image N) : (term160 N i n) = (term28 N n i).
Proof. exact (eq_refl (term160 N i n)). Qed.
Lemma lem7612961 {N : Type'} (i : finite_image N) : (term178 N i) = (term29 N i).
Proof. exact (fun_ext (fun n : nat => @lem7612960 N n i)). Qed.
Lemma lem7612962 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7612963 {N : Type'} (i : finite_image N) : (term179 N i) = (term180 N i).
Proof. exact (MK_COMB (@lem7612962) (@lem7612961 N i)). Qed.
Lemma lem7612964 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7612965 {N : Type'} (i : finite_image N) : (term181 N i) = (term182 N i).
Proof. exact (MK_COMB (@lem7612964) (@lem7612963 N i)). Qed.
Lemma lem7612966 {N : Type'} (i : finite_image N) : (term162 N i) = (term183 N i).
Proof. exact (MK_COMB (@lem7612965 N i) (@lem7612959 N i)). Qed.
Lemma lem7612967 {N : Type'} (i : finite_image N) : (term30 N i) = (term183 N i).
Proof. exact (TRANS (@lem7612941 N i) (@lem7612966 N i)). Qed.
Lemma lem7612968 {N : Type'} : (term31 N) = (term184 N).
Proof. exact (fun_ext (fun i : finite_image N => @lem7612967 N i)). Qed.
Lemma lem7612969 {N : Type'} : (@all (finite_image N)) = (@all (finite_image N)).
Proof. exact (eq_refl (@all (finite_image N))). Qed.
Lemma lem7612970 {N : Type'} : (term12 N) = (term185 N).
Proof. exact (MK_COMB (@lem7612969 N) (@lem7612968 N)). Qed.
Lemma lem7612972 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term186 A P Q) = (term187 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7612973 {N : Type'} (P : type33 N) (Q : type33 N) : (term188 N P Q) = (term189 N P Q).
Proof. exact (@lem7612972 (finite_image N) P Q). Qed.
Lemma lem7612974 {N : Type'} : (term190 N) = (term191 N).
Proof. exact (@lem7612973 N (term192 N) (term193 N)). Qed.
Lemma lem7612975 {N : Type'} (i : finite_image N) : (term194 N i) = (term180 N i).
Proof. exact (eq_refl (term194 N i)). Qed.
Lemma lem7612976 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7612977 {N : Type'} (i : finite_image N) : (term195 N i) = (term182 N i).
Proof. exact (MK_COMB (@lem7612976) (@lem7612975 N i)). Qed.
Lemma lem7612978 {N : Type'} (i : finite_image N) : (term196 N i) = (term177 N i).
Proof. exact (eq_refl (term196 N i)). Qed.
Lemma lem7612979 {N : Type'} (i : finite_image N) : (term197 N i) = (term183 N i).
Proof. exact (MK_COMB (@lem7612977 N i) (@lem7612978 N i)). Qed.
Lemma lem7612980 {N : Type'} : (term198 N) = (term184 N).
Proof. exact (fun_ext (fun i : finite_image N => @lem7612979 N i)). Qed.
Lemma lem7612981 {N : Type'} : (@all (finite_image N)) = (@all (finite_image N)).
Proof. exact (eq_refl (@all (finite_image N))). Qed.
Lemma lem7612982 {N : Type'} : (term190 N) = (term185 N).
Proof. exact (MK_COMB (@lem7612981 N) (@lem7612980 N)). Qed.
Lemma lem7612983 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7612984 {N : Type'} : (term199 N) = (term200 N).
Proof. exact (MK_COMB (@lem7612983) (@lem7612982 N)). Qed.
Lemma lem7612985 {N : Type'} (i : finite_image N) : (term194 N i) = (term180 N i).
Proof. exact (eq_refl (term194 N i)). Qed.
Lemma lem7612986 {N : Type'} : (term201 N) = (term192 N).
Proof. exact (fun_ext (fun i : finite_image N => @lem7612985 N i)). Qed.
Lemma lem7612987 {N : Type'} : (@all (finite_image N)) = (@all (finite_image N)).
Proof. exact (eq_refl (@all (finite_image N))). Qed.
Lemma lem7612988 {N : Type'} : (term202 N) = (term203 N).
Proof. exact (MK_COMB (@lem7612987 N) (@lem7612986 N)). Qed.
Lemma lem7612989 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7612990 {N : Type'} : (term204 N) = (term205 N).
Proof. exact (MK_COMB (@lem7612989) (@lem7612988 N)). Qed.
Lemma lem7612991 {N : Type'} (i : finite_image N) : (term196 N i) = (term177 N i).
Proof. exact (eq_refl (term196 N i)). Qed.
Lemma lem7612992 {N : Type'} : (term206 N) = (term193 N).
Proof. exact (fun_ext (fun i : finite_image N => @lem7612991 N i)). Qed.
Lemma lem7612993 {N : Type'} : (@all (finite_image N)) = (@all (finite_image N)).
Proof. exact (eq_refl (@all (finite_image N))). Qed.
Lemma lem7612994 {N : Type'} : (term207 N) = (term208 N).
Proof. exact (MK_COMB (@lem7612993 N) (@lem7612992 N)). Qed.
Lemma lem7612995 {N : Type'} : (term191 N) = (term209 N).
Proof. exact (MK_COMB (@lem7612990 N) (@lem7612994 N)). Qed.
Lemma lem7612996 {N : Type'} : ((term190 N) = (term191 N)) = ((term185 N) = (term209 N)).
Proof. exact (MK_COMB (@lem7612984 N) (@lem7612995 N)). Qed.
Lemma lem7612997 {N : Type'} : (term185 N) = (term209 N).
Proof. exact (EQ_MP (@lem7612996 N) (@lem7612974 N)). Qed.
Lemma lem7613059 {A : Type'} (P : Prop) (Q : A -> Prop) : (term210 A P Q) = (term211 A P Q).
Proof. exact (EQ_MP (@lem18941 A P Q) (@lem18940 A P Q)). Qed.
Lemma lem7613060 (P : Prop) (Q : nat -> Prop) : (term212 P Q) = (term213 P Q).
Proof. exact (@lem7613059 nat P Q). Qed.
Lemma lem7613061 {N : Type'} (i : finite_image N) (n : nat) : (term214 N i n) = (term215 N i n).
Proof. exact (@lem7613060 (term157 N n i) (term216 N i n)). Qed.
Lemma lem7613062 {N : Type'} (i : finite_image N) (n' : nat) (n : nat) : (term217 N i n n') = (term167 N i n' n).
Proof. exact (eq_refl (term217 N i n n')). Qed.
Lemma lem7613063 {N : Type'} (n : nat) (i : finite_image N) : (term165 N n i) = (term165 N n i).
Proof. exact (eq_refl (term165 N n i)). Qed.
Lemma lem7613064 {N : Type'} (i : finite_image N) (n' : nat) (n : nat) : (term218 N i n n') = (term169 N i n' n).
Proof. exact (MK_COMB (@lem7613063 N n i) (@lem7613062 N i n' n)). Qed.
Lemma lem7613065 {N : Type'} (i : finite_image N) (n : nat) : (term219 N i n) = (term171 N i n).
Proof. exact (fun_ext (fun n' : nat => @lem7613064 N i n' n)). Qed.
Lemma lem7613066 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7613067 {N : Type'} (i : finite_image N) (n : nat) : (term214 N i n) = (term173 N i n).
Proof. exact (MK_COMB (@lem7613066) (@lem7613065 N i n)). Qed.
Lemma lem7613068 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7613069 {N : Type'} (i : finite_image N) (n : nat) : (term220 N i n) = (term221 N i n).
Proof. exact (MK_COMB (@lem7613068) (@lem7613067 N i n)). Qed.
Lemma lem7613070 {N : Type'} (i : finite_image N) (n' : nat) (n : nat) : (term217 N i n n') = (term167 N i n' n).
Proof. exact (eq_refl (term217 N i n n')). Qed.
Lemma lem7613071 {N : Type'} (i : finite_image N) (n : nat) : (term222 N i n) = (term216 N i n).
Proof. exact (fun_ext (fun n' : nat => @lem7613070 N i n' n)). Qed.
Lemma lem7613072 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7613073 {N : Type'} (i : finite_image N) (n : nat) : (term223 N i n) = (term224 N i n).
Proof. exact (MK_COMB (@lem7613072) (@lem7613071 N i n)). Qed.
Lemma lem7613074 {N : Type'} (n : nat) (i : finite_image N) : (term165 N n i) = (term165 N n i).
Proof. exact (eq_refl (term165 N n i)). Qed.
Lemma lem7613075 {N : Type'} (i : finite_image N) (n : nat) : (term215 N i n) = (term225 N i n).
Proof. exact (MK_COMB (@lem7613074 N n i) (@lem7613073 N i n)). Qed.
Lemma lem7613076 {N : Type'} (i : finite_image N) (n : nat) : ((term214 N i n) = (term215 N i n)) = ((term173 N i n) = (term225 N i n)).
Proof. exact (MK_COMB (@lem7613069 N i n) (@lem7613075 N i n)). Qed.
Lemma lem7613077 {N : Type'} (i : finite_image N) (n : nat) : (term173 N i n) = (term225 N i n).
Proof. exact (EQ_MP (@lem7613076 N i n) (@lem7613061 N i n)). Qed.
Lemma lem7613126 {N : Type'} (i : finite_image N) : (term175 N i) = (term226 N i).
Proof. exact (fun_ext (fun n : nat => @lem7613077 N i n)). Qed.
Lemma lem7613127 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7613128 {N : Type'} (i : finite_image N) : (term177 N i) = (term227 N i).
Proof. exact (MK_COMB (@lem7613127) (@lem7613126 N i)). Qed.
Lemma lem7613177 {N : Type'} : (term193 N) = (term228 N).
Proof. exact (fun_ext (fun i : finite_image N => @lem7613128 N i)). Qed.
Lemma lem7613178 {N : Type'} : (@all (finite_image N)) = (@all (finite_image N)).
Proof. exact (eq_refl (@all (finite_image N))). Qed.
Lemma lem7613179 {N : Type'} : (term208 N) = (term229 N).
Proof. exact (MK_COMB (@lem7613178 N) (@lem7613177 N)). Qed.
Lemma lem7613184 {N : Type'} : (term205 N) = (term205 N).
Proof. exact (eq_refl (term205 N)). Qed.
Lemma lem7613185 {N : Type'} : (term209 N) = (term230 N).
Proof. exact (MK_COMB (@lem7613184 N) (@lem7613179 N)). Qed.
Lemma lem7613186 {N : Type'} : (term185 N) = (term230 N).
Proof. exact (TRANS (@lem7612997 N) (@lem7613185 N)). Qed.
Lemma lem7613188 {A B : Type'} (P : type1413 A B) : (term231 A B P) = (term232 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7613189 {N : Type'} (P : type32 N) : (term233 N P) = (term234 N P).
Proof. exact (@lem7613188 (finite_image N) nat P). Qed.
Lemma lem7613190 {N : Type'} : (term235 N) = (term236 N).
Proof. exact (@lem7613189 N (term237 N)). Qed.
Lemma lem7613191 {N : Type'} (i : finite_image N) : (term238 N i) = (term29 N i).
Proof. exact (eq_refl (term238 N i)). Qed.
Lemma lem7613192 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7613193 {N : Type'} (i : finite_image N) (n : nat) : (term239 N i n) = (term160 N i n).
Proof. exact (MK_COMB (@lem7613191 N i) (@lem7613192 n)). Qed.
Lemma lem7613194 {N : Type'} (n : nat) (i : finite_image N) : (term160 N i n) = (term28 N n i).
Proof. exact (eq_refl (term160 N i n)). Qed.
Lemma lem7613195 {N : Type'} (n : nat) (i : finite_image N) : (term239 N i n) = (term28 N n i).
Proof. exact (TRANS (@lem7613193 N i n) (@lem7613194 N n i)). Qed.
Lemma lem7613196 {N : Type'} (i : finite_image N) : (term240 N i) = (term29 N i).
Proof. exact (fun_ext (fun n : nat => @lem7613195 N n i)). Qed.
Lemma lem7613197 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7613198 {N : Type'} (i : finite_image N) : (term241 N i) = (term180 N i).
Proof. exact (MK_COMB (@lem7613197) (@lem7613196 N i)). Qed.
Lemma lem7613199 {N : Type'} : (term242 N) = (term192 N).
Proof. exact (fun_ext (fun i : finite_image N => @lem7613198 N i)). Qed.
Lemma lem7613200 {N : Type'} : (@all (finite_image N)) = (@all (finite_image N)).
Proof. exact (eq_refl (@all (finite_image N))). Qed.
Lemma lem7613201 {N : Type'} : (term235 N) = (term203 N).
Proof. exact (MK_COMB (@lem7613200 N) (@lem7613199 N)). Qed.
Lemma lem7613202 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7613203 {N : Type'} : (term243 N) = (term244 N).
Proof. exact (MK_COMB (@lem7613202) (@lem7613201 N)). Qed.
Lemma lem7613204 {N : Type'} (i : finite_image N) : (term238 N i) = (term29 N i).
Proof. exact (eq_refl (term238 N i)). Qed.
Lemma lem7613205 {N : Type'} (n : type34 N) (i : finite_image N) : (n i) = (n i).
Proof. exact (eq_refl (n i)). Qed.
Lemma lem7613206 {N : Type'} (n : type34 N) (i : finite_image N) : (term245 N n i) = (term246 N n i).
Proof. exact (MK_COMB (@lem7613204 N i) (@lem7613205 N n i)). Qed.
Lemma lem7613207 {N : Type'} (n : type34 N) (i : finite_image N) : (term246 N n i) = (term247 N n i).
Proof. exact (eq_refl (term246 N n i)). Qed.
Lemma lem7613208 {N : Type'} (n : type34 N) (i : finite_image N) : (term245 N n i) = (term247 N n i).
Proof. exact (TRANS (@lem7613206 N n i) (@lem7613207 N n i)). Qed.
Lemma lem7613209 {N : Type'} (n : type34 N) : (term248 N n) = (term249 N n).
Proof. exact (fun_ext (fun i : finite_image N => @lem7613208 N n i)). Qed.
Lemma lem7613210 {N : Type'} : (@all (finite_image N)) = (@all (finite_image N)).
Proof. exact (eq_refl (@all (finite_image N))). Qed.
Lemma lem7613211 {N : Type'} (n : type34 N) : (term250 N n) = (term251 N n).
Proof. exact (MK_COMB (@lem7613210 N) (@lem7613209 N n)). Qed.
Lemma lem7613212 {N : Type'} : (term252 N) = (term253 N).
Proof. exact (fun_ext (fun n : type34 N => @lem7613211 N n)). Qed.
Lemma lem7613213 {N : Type'} : (@ex ((finite_image N) -> nat)) = (@ex ((finite_image N) -> nat)).
Proof. exact (eq_refl (@ex ((finite_image N) -> nat))). Qed.
Lemma lem7613214 {N : Type'} : (term236 N) = (term254 N).
Proof. exact (MK_COMB (@lem7613213 N) (@lem7613212 N)). Qed.
Lemma lem7613215 {N : Type'} : ((term235 N) = (term236 N)) = ((term203 N) = (term254 N)).
Proof. exact (MK_COMB (@lem7613203 N) (@lem7613214 N)). Qed.
Lemma lem7613216 {N : Type'} : (term203 N) = (term254 N).
Proof. exact (EQ_MP (@lem7613215 N) (@lem7613190 N)). Qed.
Lemma lem7613217 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7613218 {N : Type'} : (term205 N) = (term255 N).
Proof. exact (MK_COMB (@lem7613217) (@lem7613216 N)). Qed.
Lemma lem7613219 {N : Type'} : (term229 N) = (term229 N).
Proof. exact (eq_refl (term229 N)). Qed.
Lemma lem7613220 {N : Type'} : (term230 N) = (term256 N).
Proof. exact (MK_COMB (@lem7613218 N) (@lem7613219 N)). Qed.
Lemma lem7613222 {A : Type'} (P : A -> Prop) (Q : Prop) : (term96 A P Q) = (term97 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem7613223 {N : Type'} (P : type60 N) (Q : Prop) : (term257 N P Q) = (term258 N P Q).
Proof. exact (@lem7613222 (type34 N) P Q). Qed.
Lemma lem7613224 {N : Type'} : (term259 N) = (term260 N).
Proof. exact (@lem7613223 N (term253 N) (term229 N)). Qed.
Lemma lem7613225 {N : Type'} (n : type34 N) : (term261 N n) = (term251 N n).
Proof. exact (eq_refl (term261 N n)). Qed.
Lemma lem7613226 {N : Type'} : (term262 N) = (term253 N).
Proof. exact (fun_ext (fun n : type34 N => @lem7613225 N n)). Qed.
Lemma lem7613227 {N : Type'} : (@ex ((finite_image N) -> nat)) = (@ex ((finite_image N) -> nat)).
Proof. exact (eq_refl (@ex ((finite_image N) -> nat))). Qed.
Lemma lem7613228 {N : Type'} : (term263 N) = (term254 N).
Proof. exact (MK_COMB (@lem7613227 N) (@lem7613226 N)). Qed.
Lemma lem7613229 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7613230 {N : Type'} : (term264 N) = (term255 N).
Proof. exact (MK_COMB (@lem7613229) (@lem7613228 N)). Qed.
Lemma lem7613231 {N : Type'} : (term229 N) = (term229 N).
Proof. exact (eq_refl (term229 N)). Qed.
Lemma lem7613232 {N : Type'} : (term259 N) = (term256 N).
Proof. exact (MK_COMB (@lem7613230 N) (@lem7613231 N)). Qed.
Lemma lem7613233 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7613234 {N : Type'} : (term265 N) = (term266 N).
Proof. exact (MK_COMB (@lem7613233) (@lem7613232 N)). Qed.
Lemma lem7613235 {N : Type'} (n : type34 N) : (term261 N n) = (term251 N n).
Proof. exact (eq_refl (term261 N n)). Qed.
Lemma lem7613236 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7613237 {N : Type'} (n : type34 N) : (term267 N n) = (term268 N n).
Proof. exact (MK_COMB (@lem7613236) (@lem7613235 N n)). Qed.
Lemma lem7613238 {N : Type'} : (term229 N) = (term229 N).
Proof. exact (eq_refl (term229 N)). Qed.
Lemma lem7613239 {N : Type'} (n : type34 N) : (term269 N n) = (term270 N n).
Proof. exact (MK_COMB (@lem7613237 N n) (@lem7613238 N)). Qed.
Lemma lem7613240 {N : Type'} : (term271 N) = (term272 N).
Proof. exact (fun_ext (fun n : type34 N => @lem7613239 N n)). Qed.
Lemma lem7613241 {N : Type'} : (@ex ((finite_image N) -> nat)) = (@ex ((finite_image N) -> nat)).
Proof. exact (eq_refl (@ex ((finite_image N) -> nat))). Qed.
Lemma lem7613242 {N : Type'} : (term260 N) = (term273 N).
Proof. exact (MK_COMB (@lem7613241 N) (@lem7613240 N)). Qed.
Lemma lem7613243 {N : Type'} : ((term259 N) = (term260 N)) = ((term256 N) = (term273 N)).
Proof. exact (MK_COMB (@lem7613234 N) (@lem7613242 N)). Qed.
Lemma lem7613244 {N : Type'} : (term256 N) = (term273 N).
Proof. exact (EQ_MP (@lem7613243 N) (@lem7613224 N)). Qed.
Lemma lem7613245 {N : Type'} : (term230 N) = (term273 N).
Proof. exact (TRANS (@lem7613220 N) (@lem7613244 N)). Qed.
Lemma lem7613246 {N : Type'} : (term185 N) = (term273 N).
Proof. exact (TRANS (@lem7613186 N) (@lem7613245 N)). Qed.
Lemma lem7613247 {N : Type'} : (term12 N) = (term273 N).
Proof. exact (TRANS (@lem7612970 N) (@lem7613246 N)). Qed.
Lemma lem7613248 {N : Type'} (h1 : term12 N) : term273 N.
Proof. exact (EQ_MP (@lem7613247 N) (@lem7612307 N h1)). Qed.
Lemma lem7613249 {N : Type'} (n : type34 N) (h1 : term270 N n) : term270 N n.
Proof. exact (h1). Qed.
Lemma lem7613251 {N : Type'} (i : nat) (P : type33 N) (h1 : term150 N i P) : term150 N i P.
Proof. exact (h1). Qed.
Lemma lem7613252 {N : Type'} (i : nat) (k : finite_image N) (P : type33 N) (h1 : term147 N i k P) : term147 N i k P.
Proof. exact (h1). Qed.
Lemma lem7613295 {N : Type'} (i : finite_image N) (n' : nat) (n : nat) : (term167 N i n' n) = (term167 N i n' n).
Proof. exact (eq_refl (term167 N i n' n)). Qed.
Lemma lem7613296 {N : Type'} (i : finite_image N) (n : nat) : (term216 N i n) = (term216 N i n).
Proof. exact (fun_ext (fun n' : nat => @lem7613295 N i n' n)). Qed.
Lemma lem7613297 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7613298 {N : Type'} (i : finite_image N) (n : nat) : (term224 N i n) = (term224 N i n).
Proof. exact (MK_COMB (@lem7613297) (@lem7613296 N i n)). Qed.
Lemma lem7613335 {N : Type'} (n : nat) (i : finite_image N) : (term165 N n i) = (term165 N n i).
Proof. exact (eq_refl (term165 N n i)). Qed.
Lemma lem7613336 {N : Type'} (i : finite_image N) (n : nat) : (term225 N i n) = (term225 N i n).
Proof. exact (MK_COMB (@lem7613335 N n i) (@lem7613298 N i n)). Qed.
Lemma lem7613337 {N : Type'} (i : finite_image N) : (term226 N i) = (term226 N i).
Proof. exact (fun_ext (fun n : nat => @lem7613336 N i n)). Qed.
Lemma lem7613338 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7613339 {N : Type'} (i : finite_image N) : (term227 N i) = (term227 N i).
Proof. exact (MK_COMB (@lem7613338) (@lem7613337 N i)). Qed.
Lemma lem7613340 {N : Type'} : (term228 N) = (term228 N).
Proof. exact (fun_ext (fun i : finite_image N => @lem7613339 N i)). Qed.
Lemma lem7613341 {N : Type'} : (@all (finite_image N)) = (@all (finite_image N)).
Proof. exact (eq_refl (@all (finite_image N))). Qed.
Lemma lem7613342 {N : Type'} : (term229 N) = (term229 N).
Proof. exact (MK_COMB (@lem7613341 N) (@lem7613340 N)). Qed.
Lemma lem7613377 {N : Type'} (n : type34 N) (i : finite_image N) : (term247 N n i) = (term247 N n i).
Proof. exact (eq_refl (term247 N n i)). Qed.
Lemma lem7613378 {N : Type'} (n : type34 N) : (term249 N n) = (term249 N n).
Proof. exact (fun_ext (fun i : finite_image N => @lem7613377 N n i)). Qed.
Lemma lem7613379 {N : Type'} : (@all (finite_image N)) = (@all (finite_image N)).
Proof. exact (eq_refl (@all (finite_image N))). Qed.
Lemma lem7613380 {N : Type'} (n : type34 N) : (term251 N n) = (term251 N n).
Proof. exact (MK_COMB (@lem7613379 N) (@lem7613378 N n)). Qed.
Lemma lem7613381 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7613382 {N : Type'} (n : type34 N) : (term268 N n) = (term268 N n).
Proof. exact (MK_COMB (@lem7613381) (@lem7613380 N n)). Qed.
Lemma lem7613383 {N : Type'} (n : type34 N) : (term270 N n) = (term270 N n).
Proof. exact (MK_COMB (@lem7613382 N n) (@lem7613342 N)). Qed.
Lemma lem7613384 {N : Type'} (n : type34 N) (h1 : term270 N n) : term270 N n.
Proof. exact (EQ_MP (@lem7613383 N n) (@lem7613249 N n h1)). Qed.
Lemma lem7613547 {N : Type'} (P : type33 N) (i : nat) : (term56 N P i) = (term56 N P i).
Proof. exact (eq_refl (term56 N P i)). Qed.
Lemma lem7613548 {N : Type'} (P : type33 N) : (term66 N P) = (term66 N P).
Proof. exact (fun_ext (fun i : nat => @lem7613547 N P i)). Qed.
Lemma lem7613549 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7613550 {N : Type'} (P : type33 N) : (term67 N P) = (term67 N P).
Proof. exact (MK_COMB (@lem7613549) (@lem7613548 N P)). Qed.
Lemma lem7613557 {N : Type'} (P : type33 N) (k : finite_image N) : (term109 N P k) = (term109 N P k).
Proof. exact (eq_refl (term109 N P k)). Qed.
Lemma lem7613558 {N : Type'} (k : finite_image N) (P : type33 N) : (term111 N k P) = (term111 N k P).
Proof. exact (MK_COMB (@lem7613557 N P k) (@lem7613550 N P)). Qed.
Lemma lem7613587 {N : Type'} (P : type33 N) (i : nat) : (term51 N P i) = (term51 N P i).
Proof. exact (eq_refl (term51 N P i)). Qed.
Lemma lem7613590 {N : Type'} (P : type33 N) (k : finite_image N) : (P k) = (P k).
Proof. exact (eq_refl (P k)). Qed.
Lemma lem7613591 {N : Type'} (P : type33 N) : (term34 N P) = (term34 N P).
Proof. exact (fun_ext (fun k : finite_image N => @lem7613590 N P k)). Qed.
Lemma lem7613592 {N : Type'} : (@all (finite_image N)) = (@all (finite_image N)).
Proof. exact (eq_refl (@all (finite_image N))). Qed.
Lemma lem7613593 {N : Type'} (P : type33 N) : (term8 N P) = (term8 N P).
Proof. exact (MK_COMB (@lem7613592 N) (@lem7613591 N P)). Qed.
Lemma lem7613594 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7613595 {N : Type'} (P : type33 N) : (term72 N P) = (term72 N P).
Proof. exact (MK_COMB (@lem7613594) (@lem7613593 N P)). Qed.
Lemma lem7613596 {N : Type'} (P : type33 N) (i : nat) : (term91 N P i) = (term91 N P i).
Proof. exact (MK_COMB (@lem7613595 N P) (@lem7613587 N P i)). Qed.
Lemma lem7613597 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7613598 {N : Type'} (P : type33 N) (i : nat) : (term129 N P i) = (term129 N P i).
Proof. exact (MK_COMB (@lem7613597) (@lem7613596 N P i)). Qed.
Lemma lem7613599 {N : Type'} (i : nat) (k : finite_image N) (P : type33 N) : (term147 N i k P) = (term147 N i k P).
Proof. exact (MK_COMB (@lem7613598 N P i) (@lem7613558 N k P)). Qed.
Lemma lem7613600 {N : Type'} (i : nat) (k : finite_image N) (P : type33 N) (h1 : term147 N i k P) : term147 N i k P.
Proof. exact (EQ_MP (@lem7613599 N i k P) (@lem7613252 N i k P h1)). Qed.
Lemma lem7613604 {N : Type'} (n : type34 N) (h1 : term270 N n) : term251 N n.
Proof. exact (proj1 (@lem7613384 N n h1)). Qed.
Lemma lem7613605 {N : Type'} (P : type33 N) (i : nat) (h1 : term91 N P i) : term91 N P i.
Proof. exact (h1). Qed.
Lemma lem7613606 {N : Type'} (k : finite_image N) (P : type33 N) (h1 : term111 N k P) : term111 N k P.
Proof. exact (h1). Qed.
Lemma lem7613607 {N : Type'} (P : type33 N) (i : nat) (h1 : term91 N P i) : term51 N P i.
Proof. exact (proj2 (@lem7613605 N P i h1)). Qed.
Lemma lem7613608 {N : Type'} (P : type33 N) (i : nat) (h1 : term91 N P i) : term8 N P.
Proof. exact (proj1 (@lem7613605 N P i h1)). Qed.
Lemma lem7613613 {N : Type'} (k : finite_image N) (P : type33 N) (h1 : term111 N k P) : term67 N P.
Proof. exact (proj2 (@lem7613606 N k P h1)). Qed.
Lemma lem7613794 {N : Type'} (P : type33 N) (k : finite_image N) : (P k) = (P k).
Proof. exact (eq_refl (P k)). Qed.
Lemma lem7613795 {N : Type'} (P : type33 N) : (term34 N P) = (term34 N P).
Proof. exact (fun_ext (fun k : finite_image N => @lem7613794 N P k)). Qed.
Lemma lem7613796 {N : Type'} : (@all (finite_image N)) = (@all (finite_image N)).
Proof. exact (eq_refl (@all (finite_image N))). Qed.
Lemma lem7613798 {N : Type'} (P : type33 N) : (term8 N P) = (term8 N P).
Proof. exact (MK_COMB (@lem7613796 N) (@lem7613795 N P)). Qed.
Lemma lem7613799 {N : Type'} (P : type33 N) (i : nat) (h1 : term91 N P i) : term8 N P.
Proof. exact (EQ_MP (@lem7613798 N P) (@lem7613608 N P i h1)). Qed.
Lemma lem7613910 {N : Type'} (n : type34 N) (i : finite_image N) : (term247 N n i) = (term247 N n i).
Proof. exact (eq_refl (term247 N n i)). Qed.
Lemma lem7613911 {N : Type'} (n : type34 N) : (term249 N n) = (term249 N n).
Proof. exact (fun_ext (fun i : finite_image N => @lem7613910 N n i)). Qed.
Lemma lem7613912 {N : Type'} : (@all (finite_image N)) = (@all (finite_image N)).
Proof. exact (eq_refl (@all (finite_image N))). Qed.
Lemma lem7613914 {N : Type'} (n : type34 N) : (term251 N n) = (term251 N n).
Proof. exact (MK_COMB (@lem7613912 N) (@lem7613911 N n)). Qed.
Lemma lem7613915 {N : Type'} (n : type34 N) (h1 : term270 N n) : term251 N n.
Proof. exact (EQ_MP (@lem7613914 N n) (@lem7613604 N n h1)). Qed.
Lemma lem7614007 {N : Type'} (P : type33 N) (i : nat) : (term56 N P i) = (term56 N P i).
Proof. exact (eq_refl (term56 N P i)). Qed.
Lemma lem7614008 {N : Type'} (P : type33 N) : (term66 N P) = (term66 N P).
Proof. exact (fun_ext (fun i : nat => @lem7614007 N P i)). Qed.
Lemma lem7614009 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7614011 {N : Type'} (P : type33 N) : (term67 N P) = (term67 N P).
Proof. exact (MK_COMB (@lem7614009) (@lem7614008 N P)). Qed.
Lemma lem7614012 {N : Type'} (k : finite_image N) (P : type33 N) (h1 : term111 N k P) : term67 N P.
Proof. exact (EQ_MP (@lem7614011 N P) (@lem7613613 N k P h1)). Qed.
Lemma lem7614037 {N : Type'} (_97975 : finite_image N) (P : type33 N) (i : nat) (h1 : term91 N P i) : term40 N P _97975.
Proof. exact (@lem7613799 N P i h1 _97975). Qed.
Lemma lem7614038 {N : Type'} (P : type33 N) (_97975 : finite_image N) : (term40 N P _97975) = (P _97975).
Proof. exact (eq_refl (term40 N P _97975)). Qed.
Lemma lem7614052 {N : Type'} (_97980 : finite_image N) (n : type34 N) (h1 : term270 N n) : term274 N n _97980.
Proof. exact (@lem7613915 N n h1 _97980). Qed.
Lemma lem7614053 {N : Type'} (n : type34 N) (_97980 : finite_image N) : (term274 N n _97980) = (term247 N n _97980).
Proof. exact (eq_refl (term274 N n _97980)). Qed.
Lemma lem7614054 {N : Type'} (_97980 : finite_image N) (n : type34 N) (h1 : term270 N n) : term247 N n _97980.
Proof. exact (EQ_MP (@lem7614053 N n _97980) (@lem7614052 N _97980 n h1)). Qed.
Lemma lem7614064 {N : Type'} (_97984 : nat) (k : finite_image N) (P : type33 N) (h1 : term111 N k P) : term275 N P _97984.
Proof. exact (@lem7614012 N k P h1 _97984). Qed.
Lemma lem7614065 {N : Type'} (P : type33 N) (_97984 : nat) : (term275 N P _97984) = (term56 N P _97984).
Proof. exact (eq_refl (term275 N P _97984)). Qed.
Lemma lem7614066 {N : Type'} (_97984 : nat) (k : finite_image N) (P : type33 N) (h1 : term111 N k P) : term56 N P _97984.
Proof. exact (EQ_MP (@lem7614065 N P _97984) (@lem7614064 N _97984 k P h1)). Qed.
Lemma lem7614075 {N : Type'} (_97980 : finite_image N) (n : type34 N) (h1 : term270 N n) : term276 N n _97980.
Proof. exact (proj2 (@lem7614054 N _97980 n h1)). Qed.
Lemma lem7614154 {N : Type'} (P : type33 N) (i : nat) (h1 : term91 N P i) : term277 N P i.
Proof. exact (proj2 (@lem7613607 N P i h1)). Qed.
Lemma lem7614240 {N : Type'} (k : finite_image N) (P : type33 N) (h1 : term111 N k P) : term42 N P k.
Proof. exact (proj1 (@lem7613606 N k P h1)). Qed.
Lemma lem7614251 {N : Type'} (P : type33 N) (_97984 : nat) : (term56 N P _97984) = (term278 N P _97984).
Proof. exact (@lem7612110 (term279 _97984) (term280 N _97984) (term49 N P _97984)). Qed.
Lemma lem7614252 {N : Type'} (_97984 : nat) (k : finite_image N) (P : type33 N) (h1 : term111 N k P) : term278 N P _97984.
Proof. exact (EQ_MP (@lem7614251 N P _97984) (@lem7614066 N _97984 k P h1)). Qed.
Lemma lem7614371 {N : Type'} (_97975 : finite_image N) (P : type33 N) (i : nat) (h1 : term91 N P i) : P _97975.
Proof. exact (EQ_MP (@lem7614038 N P _97975) (@lem7614037 N _97975 P i h1)). Qed.
Lemma lem7614372 {N : Type'} (_97975 : finite_image N) (P : type33 N) (i : nat) (h1 : term91 N P i) : P _97975.
Proof. exact (@lem7614371 N _97975 P i h1). Qed.
Lemma lem7614373 {N : Type'} (P : type33 N) (i : nat) (h1 : term91 N P i) : term49 N P i.
Proof. exact (@lem7614372 N (@finite_index N i) P i h1). Qed.
Lemma lem7614374 {N : Type'} (P : type33 N) (i : nat) (h1 : term91 N P i) : term281 N P i.
Proof. exact (fun h0 : term277 N P i => @lem7614373 N P i h1). Qed.
Lemma lem7614376 (p : Prop) : (term282 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7614377 {N : Type'} (P : type33 N) (i : nat) : (term281 N P i) = (term49 N P i).
Proof. exact (@lem7614376 (term49 N P i)). Qed.
Lemma lem7614378 {N : Type'} (P : type33 N) (i : nat) (h1 : term91 N P i) : term49 N P i.
Proof. exact (EQ_MP (@lem7614377 N P i) (@lem7614374 N P i h1)). Qed.
Lemma lem7614381 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7614383 {N : Type'} (P : type33 N) (i : nat) : (term277 N P i) = (term283 N P i).
Proof. exact (@lem7614381 (term49 N P i)). Qed.
Lemma lem7614386 {N : Type'} (P : type33 N) (i : nat) (h1 : term91 N P i) : term283 N P i.
Proof. exact (EQ_MP (@lem7614383 N P i) (@lem7614154 N P i h1)). Qed.
Lemma lem7614389 {N : Type'} (P : type33 N) (i : nat) (h1 : term91 N P i) : False.
Proof. exact (@lem7614386 N P i h1 (@lem7614378 N P i h1)). Qed.
Lemma lem7614390 {N : Type'} (P : type33 N) (i : nat) (h1 : term91 N P i) : term284.
Proof. exact (fun h0 : ~ False => @lem7614389 N P i h1). Qed.
Lemma lem7614392 (p : Prop) : (term282 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7614393 : term284 = False.
Proof. exact (@lem7614392 False). Qed.
Lemma lem7614394 {N : Type'} (P : type33 N) (i : nat) (h1 : term91 N P i) : False.
Proof. exact (EQ_MP (@lem7614393) (@lem7614390 N P i h1)). Qed.
Lemma lem7614395 {N : Type'} (P : type33 N) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem7614396 {N : Type'} (_98007 : finite_image N) (_98008 : finite_image N) (h1 : _98007 = _98008) : _98007 = _98008.
Proof. exact (h1). Qed.
Lemma lem7614397 {N : Type'} (P : type33 N) (_98007 : finite_image N) (_98008 : finite_image N) (h1 : _98007 = _98008) : (P _98007) = (P _98008).
Proof. exact (MK_COMB (@lem7614395 N P) (@lem7614396 N _98007 _98008 h1)). Qed.
Lemma lem7614399 (b : Prop) (a : Prop) : term285 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem7614400 {N : Type'} (_98008 : finite_image N) (P : type33 N) (_98007 : finite_image N) : term286 N _98008 P _98007.
Proof. exact (@lem7614399 (P _98008) (P _98007)). Qed.
Lemma lem7614401 {N : Type'} (P : type33 N) (_98007 : finite_image N) (_98008 : finite_image N) (h1 : _98007 = _98008) : term287 N _98008 P _98007.
Proof. exact (@lem7614400 N _98008 P _98007 (@lem7614397 N P _98007 _98008 h1)). Qed.
Lemma lem7614402 {N : Type'} (_98008 : finite_image N) (P : type33 N) (_98007 : finite_image N) : term288 N _98008 P _98007.
Proof. exact (fun h0 : _98007 = _98008 => @lem7614401 N P _98007 _98008 h0). Qed.
Lemma lem7614404 (a : Prop) (b : Prop) : (a -> b) = (term289 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem7614405 {N : Type'} (_98008 : finite_image N) (P : type33 N) (_98007 : finite_image N) : (term288 N _98008 P _98007) = (term290 N _98008 P _98007).
Proof. exact (@lem7614404 (_98007 = _98008) (term287 N _98008 P _98007)). Qed.
Lemma lem7614406 {N : Type'} (_98008 : finite_image N) (P : type33 N) (_98007 : finite_image N) : term290 N _98008 P _98007.
Proof. exact (EQ_MP (@lem7614405 N _98008 P _98007) (@lem7614402 N _98008 P _98007)). Qed.
Lemma lem7614501 {N : Type'} (_97980 : finite_image N) (n : type34 N) (h1 : term270 N n) : (term291 N n _97980) = _97980.
Proof. exact (proj2 (@lem7614075 N _97980 n h1)). Qed.
Lemma lem7614502 {N : Type'} (_97980 : finite_image N) (n : type34 N) (h1 : term270 N n) : (term291 N n _97980) = _97980.
Proof. exact (@lem7614501 N _97980 n h1). Qed.
Lemma lem7614503 {N : Type'} (k : finite_image N) (n : type34 N) (h1 : term270 N n) : (term291 N n k) = k.
Proof. exact (@lem7614502 N k n h1). Qed.
Lemma lem7614504 {N : Type'} (k : finite_image N) (n : type34 N) (h1 : term270 N n) : term292 N n k.
Proof. exact (fun h0 : term293 N n k => @lem7614503 N k n h1). Qed.
Lemma lem7614506 (p : Prop) : (term282 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7614507 {N : Type'} (n : type34 N) (k : finite_image N) : (term292 N n k) = ((term291 N n k) = k).
Proof. exact (@lem7614506 ((term291 N n k) = k)). Qed.
Lemma lem7614508 {N : Type'} (k : finite_image N) (n : type34 N) (h1 : term270 N n) : (term291 N n k) = k.
Proof. exact (EQ_MP (@lem7614507 N n k) (@lem7614504 N k n h1)). Qed.
Lemma lem7614510 {N : Type'} (_97980 : finite_image N) (n : type34 N) (h1 : term270 N n) : term294 N n _97980.
Proof. exact (proj1 (@lem7614054 N _97980 n h1)). Qed.
Lemma lem7614511 {N : Type'} (_97980 : finite_image N) (n : type34 N) (h1 : term270 N n) : term294 N n _97980.
Proof. exact (@lem7614510 N _97980 n h1). Qed.
Lemma lem7614512 {N : Type'} (k : finite_image N) (n : type34 N) (h1 : term270 N n) : term294 N n k.
Proof. exact (@lem7614511 N k n h1). Qed.
Lemma lem7614513 {N : Type'} (k : finite_image N) (n : type34 N) (h1 : term270 N n) : term295 N n k.
Proof. exact (fun h0 : term296 N n k => @lem7614512 N k n h1). Qed.
Lemma lem7614515 (p : Prop) : (term282 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7614516 {N : Type'} (n : type34 N) (k : finite_image N) : (term295 N n k) = (term294 N n k).
Proof. exact (@lem7614515 (term294 N n k)). Qed.
Lemma lem7614517 {N : Type'} (k : finite_image N) (n : type34 N) (h1 : term270 N n) : term294 N n k.
Proof. exact (EQ_MP (@lem7614516 N n k) (@lem7614513 N k n h1)). Qed.
Lemma lem7614519 {N : Type'} (_97980 : finite_image N) (n : type34 N) (h1 : term270 N n) : term297 N n _97980.
Proof. exact (proj1 (@lem7614075 N _97980 n h1)). Qed.
Lemma lem7614520 {N : Type'} (_97980 : finite_image N) (n : type34 N) (h1 : term270 N n) : term297 N n _97980.
Proof. exact (@lem7614519 N _97980 n h1). Qed.
Lemma lem7614521 {N : Type'} (k : finite_image N) (n : type34 N) (h1 : term270 N n) : term297 N n k.
Proof. exact (@lem7614520 N k n h1). Qed.
Lemma lem7614522 {N : Type'} (k : finite_image N) (n : type34 N) (h1 : term270 N n) : term298 N n k.
Proof. exact (fun h0 : term299 N n k => @lem7614521 N k n h1). Qed.
Lemma lem7614524 (p : Prop) : (term282 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7614525 {N : Type'} (n : type34 N) (k : finite_image N) : (term298 N n k) = (term297 N n k).
Proof. exact (@lem7614524 (term297 N n k)). Qed.
Lemma lem7614526 {N : Type'} (k : finite_image N) (n : type34 N) (h1 : term270 N n) : term297 N n k.
Proof. exact (EQ_MP (@lem7614525 N n k) (@lem7614522 N k n h1)). Qed.
Lemma lem7614532 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7614533 {N : Type'} (P : type33 N) (_97984 : nat) : (term278 N P _97984) = (term300 N P _97984).
Proof. exact (@lem7614532 (term280 N _97984) (term279 _97984) (term49 N P _97984)). Qed.
Lemma lem7614547 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7614548 {N : Type'} (P : type33 N) (_97984 : nat) : (term301 N P _97984) = (term302 N P _97984).
Proof. exact (@lem7614547 (term49 N P _97984) (term279 _97984)). Qed.
Lemma lem7614554 {N : Type'} (_97984 : nat) : (term303 N _97984) = (term303 N _97984).
Proof. exact (eq_refl (term303 N _97984)). Qed.
Lemma lem7614555 {N : Type'} (P : type33 N) (_97984 : nat) : (term300 N P _97984) = (term304 N P _97984).
Proof. exact (MK_COMB (@lem7614554 N _97984) (@lem7614548 N P _97984)). Qed.
Lemma lem7614559 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7614560 {N : Type'} (P : type33 N) (_97984 : nat) : (term304 N P _97984) = (term305 N P _97984).
Proof. exact (@lem7614559 (term49 N P _97984) (term280 N _97984) (term279 _97984)). Qed.
Lemma lem7614576 {N : Type'} (P : type33 N) (_97984 : nat) : (term300 N P _97984) = (term305 N P _97984).
Proof. exact (TRANS (@lem7614555 N P _97984) (@lem7614560 N P _97984)). Qed.
Lemma lem7614577 {N : Type'} (P : type33 N) (_97984 : nat) : (term278 N P _97984) = (term305 N P _97984).
Proof. exact (TRANS (@lem7614533 N P _97984) (@lem7614576 N P _97984)). Qed.
Lemma lem7614578 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7614579 {N : Type'} (P : type33 N) (_97984 : nat) : (term306 N P _97984) = (term307 N P _97984).
Proof. exact (MK_COMB (@lem7614578) (@lem7614577 N P _97984)). Qed.
Lemma lem7614593 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7614594 {N : Type'} (_97984 : nat) : (term46 N _97984) = (term308 N _97984).
Proof. exact (@lem7614593 (term280 N _97984) (term279 _97984)). Qed.
Lemma lem7614600 {N : Type'} (P : type33 N) (_97984 : nat) : (term309 N P _97984) = (term309 N P _97984).
Proof. exact (eq_refl (term309 N P _97984)). Qed.
Lemma lem7614601 {N : Type'} (P : type33 N) (_97984 : nat) : (term310 N P _97984) = (term305 N P _97984).
Proof. exact (MK_COMB (@lem7614600 N P _97984) (@lem7614594 N _97984)). Qed.
Lemma lem7614612 {N : Type'} (P : type33 N) (_97984 : nat) : ((term278 N P _97984) = (term310 N P _97984)) = ((term305 N P _97984) = (term305 N P _97984)).
Proof. exact (MK_COMB (@lem7614579 N P _97984) (@lem7614601 N P _97984)). Qed.
Lemma lem7614614 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7614615 (x : Prop) : (x = x) = True.
Proof. exact (@lem7614614 Prop x). Qed.
Lemma lem7614616 {N : Type'} (P : type33 N) (_97984 : nat) : ((term305 N P _97984) = (term305 N P _97984)) = True.
Proof. exact (@lem7614615 (term305 N P _97984)). Qed.
Lemma lem7614617 {N : Type'} (P : type33 N) (_97984 : nat) : ((term278 N P _97984) = (term310 N P _97984)) = True.
Proof. exact (TRANS (@lem7614612 N P _97984) (@lem7614616 N P _97984)). Qed.
Lemma lem7614618 {N : Type'} (P : type33 N) (_97984 : nat) : True = ((term278 N P _97984) = (term310 N P _97984)).
Proof. exact (SYM (@lem7614617 N P _97984)). Qed.
Lemma lem7614619 {N : Type'} (P : type33 N) (_97984 : nat) : (term278 N P _97984) = (term310 N P _97984).
Proof. exact (EQ_MP (@lem7614618 N P _97984) (@lem0)). Qed.
Lemma lem7614620 {N : Type'} (_97984 : nat) (k : finite_image N) (P : type33 N) (h1 : term111 N k P) : term310 N P _97984.
Proof. exact (EQ_MP (@lem7614619 N P _97984) (@lem7614252 N _97984 k P h1)). Qed.
Lemma lem7614622 (b : Prop) (a : Prop) : (a \/ b) = (term311 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7614623 {N : Type'} (P : type33 N) (_97984 : nat) : (term310 N P _97984) = (term312 N P _97984).
Proof. exact (@lem7614622 (term46 N _97984) (term49 N P _97984)). Qed.
Lemma lem7614625 (a : Prop) (b : Prop) : (term313 a b) = (term314 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7614626 {N : Type'} (_97984 : nat) : (term315 N _97984) = (term316 N _97984).
Proof. exact (@lem7614625 (term279 _97984) (term280 N _97984)). Qed.
Lemma lem7614628 (a : Prop) : (term317 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7614629 (_97984 : nat) : (term318 _97984) = (term47 _97984).
Proof. exact (@lem7614628 (term47 _97984)). Qed.
Lemma lem7614630 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7614631 (_97984 : nat) : (term319 _97984) = (term320 _97984).
Proof. exact (MK_COMB (@lem7614630) (@lem7614629 _97984)). Qed.
Lemma lem7614633 (a : Prop) : (term317 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7614634 {N : Type'} (_97984 : nat) : (term321 N _97984) = (term48 N _97984).
Proof. exact (@lem7614633 (term48 N _97984)). Qed.
Lemma lem7614635 {N : Type'} (_97984 : nat) : (term316 N _97984) = (term52 N _97984).
Proof. exact (MK_COMB (@lem7614631 _97984) (@lem7614634 N _97984)). Qed.
Lemma lem7614636 {N : Type'} (_97984 : nat) : (term315 N _97984) = (term52 N _97984).
Proof. exact (TRANS (@lem7614626 N _97984) (@lem7614635 N _97984)). Qed.
Lemma lem7614637 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7614638 {N : Type'} (_97984 : nat) : (term322 N _97984) = (term323 N _97984).
Proof. exact (MK_COMB (@lem7614637) (@lem7614636 N _97984)). Qed.
Lemma lem7614639 {N : Type'} (P : type33 N) (_97984 : nat) : (term49 N P _97984) = (term49 N P _97984).
Proof. exact (eq_refl (term49 N P _97984)). Qed.
Lemma lem7614640 {N : Type'} (P : type33 N) (_97984 : nat) : (term312 N P _97984) = (term32 N P _97984).
Proof. exact (MK_COMB (@lem7614638 N _97984) (@lem7614639 N P _97984)). Qed.
Lemma lem7614641 {N : Type'} (P : type33 N) (_97984 : nat) : (term310 N P _97984) = (term32 N P _97984).
Proof. exact (TRANS (@lem7614623 N P _97984) (@lem7614640 N P _97984)). Qed.
Lemma lem7614643 {N : Type'} (k : finite_image N) (n : type34 N) (h1 : term270 N n) : term324 N n k.
Proof. exact (conj (@lem7614517 N k n h1) (@lem7614526 N k n h1)). Qed.
Lemma lem7614645 {N : Type'} (_97984 : nat) (k : finite_image N) (P : type33 N) (h1 : term111 N k P) : term32 N P _97984.
Proof. exact (EQ_MP (@lem7614641 N P _97984) (@lem7614620 N _97984 k P h1)). Qed.
Lemma lem7614646 {N : Type'} (n : type34 N) (k : finite_image N) (P : type33 N) (h1 : term111 N k P) : term325 N P n k.
Proof. exact (@lem7614645 N (n k) k P h1). Qed.
Lemma lem7614649 {N : Type'} (n : type34 N) (k : finite_image N) (P : type33 N) (h1 : term270 N n) (h2 : term111 N k P) : term326 N P n k.
Proof. exact (@lem7614646 N n k P h2 (@lem7614643 N k n h1)). Qed.
Lemma lem7614650 {N : Type'} (n : type34 N) (k : finite_image N) (P : type33 N) (h1 : term270 N n) (h2 : term111 N k P) : term327 N P n k.
Proof. exact (fun h0 : term328 N P n k => @lem7614649 N n k P h1 h2). Qed.
Lemma lem7614652 (p : Prop) : (term282 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7614653 {N : Type'} (P : type33 N) (n : type34 N) (k : finite_image N) : (term327 N P n k) = (term326 N P n k).
Proof. exact (@lem7614652 (term326 N P n k)). Qed.
Lemma lem7614654 {N : Type'} (n : type34 N) (k : finite_image N) (P : type33 N) (h1 : term270 N n) (h2 : term111 N k P) : term326 N P n k.
Proof. exact (EQ_MP (@lem7614653 N P n k) (@lem7614650 N n k P h1 h2)). Qed.
Lemma lem7614660 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7614661 {N : Type'} (_98008 : finite_image N) (P : type33 N) (_98007 : finite_image N) : (term290 N _98008 P _98007) = (term329 N _98008 P _98007).
Proof. exact (@lem7614660 (P _98008) (term330 N _98007 _98008) (term42 N P _98007)). Qed.
Lemma lem7614675 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7614676 {N : Type'} (P : type33 N) (_98007 : finite_image N) (_98008 : finite_image N) : (term331 N _98008 P _98007) = (term332 N P _98007 _98008).
Proof. exact (@lem7614675 (term42 N P _98007) (term330 N _98007 _98008)). Qed.
Lemma lem7614684 {N : Type'} (P : type33 N) (_98008 : finite_image N) : (term333 N P _98008) = (term333 N P _98008).
Proof. exact (eq_refl (term333 N P _98008)). Qed.
Lemma lem7614685 {N : Type'} (P : type33 N) (_98007 : finite_image N) (_98008 : finite_image N) : (term329 N _98008 P _98007) = (term334 N P _98007 _98008).
Proof. exact (MK_COMB (@lem7614684 N P _98008) (@lem7614676 N P _98007 _98008)). Qed.
Lemma lem7614696 {N : Type'} (P : type33 N) (_98007 : finite_image N) (_98008 : finite_image N) : (term290 N _98008 P _98007) = (term334 N P _98007 _98008).
Proof. exact (TRANS (@lem7614661 N _98008 P _98007) (@lem7614685 N P _98007 _98008)). Qed.
Lemma lem7614697 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7614698 {N : Type'} (P : type33 N) (_98007 : finite_image N) (_98008 : finite_image N) : (term335 N _98008 P _98007) = (term336 N P _98007 _98008).
Proof. exact (MK_COMB (@lem7614697) (@lem7614696 N P _98007 _98008)). Qed.
Lemma lem7614712 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7614713 {N : Type'} (P : type33 N) (_98007 : finite_image N) (_98008 : finite_image N) : (term331 N _98008 P _98007) = (term332 N P _98007 _98008).
Proof. exact (@lem7614712 (term42 N P _98007) (term330 N _98007 _98008)). Qed.
Lemma lem7614721 {N : Type'} (P : type33 N) (_98008 : finite_image N) : (term333 N P _98008) = (term333 N P _98008).
Proof. exact (eq_refl (term333 N P _98008)). Qed.
Lemma lem7614722 {N : Type'} (P : type33 N) (_98007 : finite_image N) (_98008 : finite_image N) : (term329 N _98008 P _98007) = (term334 N P _98007 _98008).
Proof. exact (MK_COMB (@lem7614721 N P _98008) (@lem7614713 N P _98007 _98008)). Qed.
Lemma lem7614733 {N : Type'} (P : type33 N) (_98007 : finite_image N) (_98008 : finite_image N) : ((term290 N _98008 P _98007) = (term329 N _98008 P _98007)) = ((term334 N P _98007 _98008) = (term334 N P _98007 _98008)).
Proof. exact (MK_COMB (@lem7614698 N P _98007 _98008) (@lem7614722 N P _98007 _98008)). Qed.
Lemma lem7614735 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7614736 (x : Prop) : (x = x) = True.
Proof. exact (@lem7614735 Prop x). Qed.
Lemma lem7614737 {N : Type'} (P : type33 N) (_98007 : finite_image N) (_98008 : finite_image N) : ((term334 N P _98007 _98008) = (term334 N P _98007 _98008)) = True.
Proof. exact (@lem7614736 (term334 N P _98007 _98008)). Qed.
Lemma lem7614738 {N : Type'} (_98008 : finite_image N) (P : type33 N) (_98007 : finite_image N) : ((term290 N _98008 P _98007) = (term329 N _98008 P _98007)) = True.
Proof. exact (TRANS (@lem7614733 N P _98007 _98008) (@lem7614737 N P _98007 _98008)). Qed.
Lemma lem7614739 {N : Type'} (_98008 : finite_image N) (P : type33 N) (_98007 : finite_image N) : True = ((term290 N _98008 P _98007) = (term329 N _98008 P _98007)).
Proof. exact (SYM (@lem7614738 N _98008 P _98007)). Qed.
Lemma lem7614740 {N : Type'} (_98008 : finite_image N) (P : type33 N) (_98007 : finite_image N) : (term290 N _98008 P _98007) = (term329 N _98008 P _98007).
Proof. exact (EQ_MP (@lem7614739 N _98008 P _98007) (@lem0)). Qed.
Lemma lem7614741 {N : Type'} (_98008 : finite_image N) (P : type33 N) (_98007 : finite_image N) : term329 N _98008 P _98007.
Proof. exact (EQ_MP (@lem7614740 N _98008 P _98007) (@lem7614406 N _98008 P _98007)). Qed.
Lemma lem7614743 (b : Prop) (a : Prop) : (a \/ b) = (term311 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7614744 {N : Type'} (_98007 : finite_image N) (P : type33 N) (_98008 : finite_image N) : (term329 N _98008 P _98007) = (term337 N _98007 P _98008).
Proof. exact (@lem7614743 (term331 N _98008 P _98007) (P _98008)). Qed.
Lemma lem7614746 (a : Prop) (b : Prop) : (term313 a b) = (term314 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7614747 {N : Type'} (_98008 : finite_image N) (P : type33 N) (_98007 : finite_image N) : (term338 N _98008 P _98007) = (term339 N _98008 P _98007).
Proof. exact (@lem7614746 (term330 N _98007 _98008) (term42 N P _98007)). Qed.
Lemma lem7614749 (a : Prop) : (term317 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7614750 {N : Type'} (_98007 : finite_image N) (_98008 : finite_image N) : (term340 N _98007 _98008) = (_98007 = _98008).
Proof. exact (@lem7614749 (_98007 = _98008)). Qed.
Lemma lem7614751 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7614752 {N : Type'} (_98007 : finite_image N) (_98008 : finite_image N) : (term341 N _98007 _98008) = (term342 N _98007 _98008).
Proof. exact (MK_COMB (@lem7614751) (@lem7614750 N _98007 _98008)). Qed.
Lemma lem7614754 (a : Prop) : (term317 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7614755 {N : Type'} (P : type33 N) (_98007 : finite_image N) : (term343 N P _98007) = (P _98007).
Proof. exact (@lem7614754 (P _98007)). Qed.
Lemma lem7614756 {N : Type'} (_98008 : finite_image N) (P : type33 N) (_98007 : finite_image N) : (term339 N _98008 P _98007) = (term344 N _98008 P _98007).
Proof. exact (MK_COMB (@lem7614752 N _98007 _98008) (@lem7614755 N P _98007)). Qed.
Lemma lem7614757 {N : Type'} (_98008 : finite_image N) (P : type33 N) (_98007 : finite_image N) : (term338 N _98008 P _98007) = (term344 N _98008 P _98007).
Proof. exact (TRANS (@lem7614747 N _98008 P _98007) (@lem7614756 N _98008 P _98007)). Qed.
Lemma lem7614758 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7614759 {N : Type'} (_98008 : finite_image N) (P : type33 N) (_98007 : finite_image N) : (term345 N _98008 P _98007) = (term346 N _98008 P _98007).
Proof. exact (MK_COMB (@lem7614758) (@lem7614757 N _98008 P _98007)). Qed.
Lemma lem7614760 {N : Type'} (P : type33 N) (_98008 : finite_image N) : (P _98008) = (P _98008).
Proof. exact (eq_refl (P _98008)). Qed.
Lemma lem7614761 {N : Type'} (_98007 : finite_image N) (P : type33 N) (_98008 : finite_image N) : (term337 N _98007 P _98008) = (term347 N _98007 P _98008).
Proof. exact (MK_COMB (@lem7614759 N _98008 P _98007) (@lem7614760 N P _98008)). Qed.
Lemma lem7614762 {N : Type'} (_98007 : finite_image N) (P : type33 N) (_98008 : finite_image N) : (term329 N _98008 P _98007) = (term347 N _98007 P _98008).
Proof. exact (TRANS (@lem7614744 N _98007 P _98008) (@lem7614761 N _98007 P _98008)). Qed.
Lemma lem7614764 {N : Type'} (n : type34 N) (k : finite_image N) (P : type33 N) (h1 : term270 N n) (h2 : term111 N k P) : term348 N P n k.
Proof. exact (conj (@lem7614508 N k n h1) (@lem7614654 N n k P h1 h2)). Qed.
Lemma lem7614766 {N : Type'} (_98007 : finite_image N) (P : type33 N) (_98008 : finite_image N) : term347 N _98007 P _98008.
Proof. exact (EQ_MP (@lem7614762 N _98007 P _98008) (@lem7614741 N _98008 P _98007)). Qed.
Lemma lem7614767 {N : Type'} (_98007 : finite_image N) (P : type33 N) (_98008 : finite_image N) : term347 N _98007 P _98008.
Proof. exact (@lem7614766 N _98007 P _98008). Qed.
Lemma lem7614768 {N : Type'} (n : type34 N) (P : type33 N) (k : finite_image N) : term349 N n P k.
Proof. exact (@lem7614767 N (term291 N n k) P k). Qed.
Lemma lem7614771 {N : Type'} (n : type34 N) (k : finite_image N) (P : type33 N) (h1 : term270 N n) (h2 : term111 N k P) : P k.
Proof. exact (@lem7614768 N n P k (@lem7614764 N n k P h1 h2)). Qed.
Lemma lem7614772 {N : Type'} (n : type34 N) (k : finite_image N) (P : type33 N) (h1 : term270 N n) (h2 : term111 N k P) : term350 N P k.
Proof. exact (fun h0 : term42 N P k => @lem7614771 N n k P h1 h2). Qed.
Lemma lem7614774 (p : Prop) : (term282 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7614775 {N : Type'} (P : type33 N) (k : finite_image N) : (term350 N P k) = (P k).
Proof. exact (@lem7614774 (P k)). Qed.
Lemma lem7614776 {N : Type'} (n : type34 N) (k : finite_image N) (P : type33 N) (h1 : term270 N n) (h2 : term111 N k P) : P k.
Proof. exact (EQ_MP (@lem7614775 N P k) (@lem7614772 N n k P h1 h2)). Qed.
Lemma lem7614779 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7614781 {N : Type'} (P : type33 N) (k : finite_image N) : (term42 N P k) = (term351 N P k).
Proof. exact (@lem7614779 (P k)). Qed.
Lemma lem7614784 {N : Type'} (k : finite_image N) (P : type33 N) (h1 : term111 N k P) : term351 N P k.
Proof. exact (EQ_MP (@lem7614781 N P k) (@lem7614240 N k P h1)). Qed.
Lemma lem7614787 {N : Type'} (n : type34 N) (k : finite_image N) (P : type33 N) (h1 : term270 N n) (h2 : term111 N k P) : False.
Proof. exact (@lem7614784 N k P h2 (@lem7614776 N n k P h1 h2)). Qed.
Lemma lem7614788 {N : Type'} (n : type34 N) (k : finite_image N) (P : type33 N) (h1 : term270 N n) (h2 : term111 N k P) : term284.
Proof. exact (fun h0 : ~ False => @lem7614787 N n k P h1 h2). Qed.
Lemma lem7614790 (p : Prop) : (term282 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7614791 : term284 = False.
Proof. exact (@lem7614790 False). Qed.
Lemma lem7614792 {N : Type'} (n : type34 N) (k : finite_image N) (P : type33 N) (h1 : term270 N n) (h2 : term111 N k P) : False.
Proof. exact (EQ_MP (@lem7614791) (@lem7614788 N n k P h1 h2)). Qed.
Lemma lem7614793 {N : Type'} (n : type34 N) (i : nat) (k : finite_image N) (P : type33 N) (h1 : term270 N n) (h2 : term147 N i k P) : False.
Proof. exact (or_elim (@lem7613600 N i k P h2) (fun h0 : term91 N P i => @lem7614394 N P i h0) (fun h0 : term111 N k P => @lem7614792 N n k P h1 h0)). Qed.
Lemma lem7614794 {N : Type'} (n : type34 N) (i : nat) (k : finite_image N) (P : type33 N) (h1 : term270 N n) (h2 : term147 N i k P) : (term147 N i k P) = False.
Proof. exact (prop_ext (fun h3 : term147 N i k P => @lem7614793 N n i k P h1 h2) (fun h3 : False => @lem7613600 N i k P h2)). Qed.
Lemma lem7614795 {N : Type'} (n : type34 N) (i : nat) (k : finite_image N) (P : type33 N) (h1 : term270 N n) (h2 : term147 N i k P) : False.
Proof. exact (EQ_MP (@lem7614794 N n i k P h1 h2) (@lem7613600 N i k P h2)). Qed.
Lemma lem7614796 {N : Type'} (n : type34 N) (i : nat) (k : finite_image N) (P : type33 N) (h1 : term270 N n) (h2 : term147 N i k P) : (term270 N n) = False.
Proof. exact (prop_ext (fun h3 : term270 N n => @lem7614795 N n i k P h1 h2) (fun h3 : False => @lem7613384 N n h1)). Qed.
Lemma lem7614797 {N : Type'} (n : type34 N) (i : nat) (k : finite_image N) (P : type33 N) (h1 : term270 N n) (h2 : term147 N i k P) : False.
Proof. exact (EQ_MP (@lem7614796 N n i k P h1 h2) (@lem7613384 N n h1)). Qed.
Lemma lem7614798 {N : Type'} (i : nat) (P : type33 N) (n : type34 N) (h1 : term150 N i P) (h2 : term270 N n) : False.
Proof. exact (ex_elim (@lem7613251 N i P h1) (fun k : finite_image N => fun h0 : term149 N i P k => @lem7614797 N n i k P h2 h0)). Qed.
Lemma lem7614799 {N : Type'} (P : type33 N) (n : type34 N) (h1 : term11 N P) (h2 : term270 N n) : False.
Proof. exact (ex_elim (@lem7612576 N P h1) (fun i : nat => fun h0 : term151 N P i => @lem7614798 N i P n h0 h2)). Qed.
Lemma lem7614800 {A N : Type'} (P : type33 N) (n : type34 N) (h1 : term12 A) (h2 : term11 N P) (h3 : term270 N n) : False.
Proof. exact (ex_elim (@lem7612912 A h1) (fun n' : type34 A => fun h0 : term272 A n' => @lem7614799 N P n h2 h3)). Qed.
Lemma lem7614801 {A N : Type'} (P : type33 N) (h1 : term12 A) (h2 : term12 N) (h3 : term11 N P) : False.
Proof. exact (ex_elim (@lem7613248 N h2) (fun n : type34 N => fun h0 : term272 N n => @lem7614800 A N P n h1 h3 h0)). Qed.
Lemma lem7614802 {A N : Type'} (P : type33 N) (h1 : term12 A) (h2 : term11 N P) : term17 N.
Proof. exact (fun h0 : term12 N => @lem7614801 A N P h1 h0 h2). Qed.
Lemma lem7614803 {N : Type'} : (term17 N) = (term18 N).
Proof. exact (@lem69 (term12 N)). Qed.
Lemma lem7614804 {A N : Type'} (P : type33 N) (h1 : term12 A) (h2 : term11 N P) : term18 N.
Proof. exact (EQ_MP (@lem7614803 N) (@lem7614802 A N P h1 h2)). Qed.
Lemma lem7614805 {A N : Type'} (P : type33 N) (h1 : term11 N P) : term21 A N.
Proof. exact (fun h0 : term12 A => @lem7614804 A N P h0 h1). Qed.
Lemma lem7614806 {A N : Type'} (P : type33 N) : term23 A N P.
Proof. exact (fun h0 : term11 N P => @lem7614805 A N P h0). Qed.
Lemma lem7614811 {A N : Type'} : term27 A N.
Proof. exact (fun P : type33 N => @lem7614806 A N P). Qed.
Lemma lem7614812 {A N : Type'} : term26 A N.
Proof. exact (EQ_MP (@lem7612304 A N) (@lem7614811 A N)). Qed.
Lemma lem7614813 {A N : Type'} (P : type33 N) : term352 A N P.
Proof. exact (@lem7614812 A N P). Qed.
Lemma lem7614814 {A N : Type'} (P : type33 N) : (term352 A N P) = (term13 A N P).
Proof. exact (eq_refl (term352 A N P)). Qed.
Lemma lem7614815 {A N : Type'} (P : type33 N) : term13 A N P.
Proof. exact (EQ_MP (@lem7614814 A N P) (@lem7614813 A N P)). Qed.
Lemma lem7614817 {A N : Type'} (P : type33 N) : term13 A N P.
Proof. exact (@lem7612134 A N P (@lem7614815 A N P)). Qed.
Lemma lem7614818 {A N : Type'} (P : type33 N) (h1 : term11 N P) : term20 A N.
Proof. exact (@lem7614817 A N P (@lem7612115 N P h1)). Qed.
Lemma lem7614819 {N : Type'} (P : type33 N) (h1 : term11 N P) : term17 N.
Proof. exact (@lem7614818 Prop N P h1 (@lem7609879 Prop)). Qed.
Lemma lem7614820 {N : Type'} (P : type33 N) (h1 : term11 N P) : False.
Proof. exact (@lem7614819 N P h1 (@lem7612116 N)). Qed.
Lemma lem7614821 {N : Type'} (P : type33 N) (h1 : term11 N P) : (term11 N P) = False.
Proof. exact (prop_ext (fun h2 : term11 N P => @lem7614820 N P h1) (fun h2 : False => @lem7612115 N P h1)). Qed.
Lemma lem7614822 {N : Type'} (P : type33 N) (h1 : term11 N P) : False.
Proof. exact (EQ_MP (@lem7614821 N P h1) (@lem7612115 N P h1)). Qed.
Lemma lem7614823 {N : Type'} (P : type33 N) : term10 N P.
Proof. exact (fun h0 : term11 N P => @lem7614822 N P h0). Qed.
Lemma lem7614824 {N : Type'} (P : type33 N) : (term8 N P) = (term9 N P).
Proof. exact (EQ_MP (@lem7612114 N P) (@lem7614823 N P)). Qed.
