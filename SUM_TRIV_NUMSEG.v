Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_TRIV_NUMSEG_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import LE_TRANS_spec.
Require Import NOT_LT_spec.
Require Import SUM_EQ_0_NUMSEG_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19699_spec.
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
Require Import thm69_spec.
Lemma lem7214062 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem7214063 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem7214064 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem7214063 t1) (@lem7214062 t1)). Qed.
Lemma lem7214065 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem7214064 t1 t2). Qed.
Lemma lem7214066 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem7214067 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem7214066 t1 t2) (@lem7214065 t1 t2)). Qed.
Lemma lem7214068 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem7214067 t1 t2 t3). Qed.
Lemma lem7214069 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem7214070 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem7214069 t1 t2 t3) (@lem7214068 t1 t2 t3)). Qed.
Lemma lem7214071 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem7214070 t1 t2 t3)). Qed.
Lemma lem7214073 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7214074 : term8 = term9.
Proof. exact (@lem7214073 term8). Qed.
Lemma lem7214075 : term9 = term8.
Proof. exact (SYM (@lem7214074)). Qed.
Lemma lem7214076 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem7214079 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem7214080 : term12.
Proof. exact (fun h0 : term11 => @lem7214079 h0). Qed.
Lemma lem7214081 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem7214082 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem7214083 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem7214081 h2 (@lem7214082 h1)). Qed.
Lemma lem7214084 (h1 : term11) : term13.
Proof. exact (fun h0 : term12 => @lem7214083 h1 h0). Qed.
Lemma lem7214085 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem7214086 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem7214084 h1 (@lem7214085 h2)). Qed.
Lemma lem7214087 (h1 : term12) : term12.
Proof. exact (fun h0 : term11 => @lem7214086 h0 h1). Qed.
Lemma lem7214088 : term14.
Proof. exact (fun h0 : term12 => @lem7214087 h0). Qed.
Lemma lem7214091 : term12.
Proof. exact (@lem7214088 (@lem7214080)). Qed.
Lemma lem7214137 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7214138 : term15 = term16.
Proof. exact (@lem7214137 term17). Qed.
Lemma lem7214161 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem7214162 : term19 = term20.
Proof. exact (MK_COMB (@lem7214161) (@lem7214138)). Qed.
Lemma lem7214165 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem7214166 : term22 = term23.
Proof. exact (MK_COMB (@lem7214165) (@lem7214162)). Qed.
Lemma lem7214169 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem7214176 : term11 = term25.
Proof. exact (MK_COMB (@lem7214169) (@lem7214166)). Qed.
Lemma lem7214177 (m : nat) (n : nat) (f : nat -> real) : ((term26 m n f) = term27) = ((term26 m n f) = term27).
Proof. exact (eq_refl ((term26 m n f) = term27)). Qed.
Lemma lem7214186 (m : nat) (n : nat) (f : nat -> real) (i : nat) : (term28 m n f i) = (term28 m n f i).
Proof. exact (eq_refl (term28 m n f i)). Qed.
Lemma lem7214187 (m : nat) (n : nat) (f : nat -> real) : (term29 m n f) = (term29 m n f).
Proof. exact (fun_ext (fun i : nat => @lem7214186 m n f i)). Qed.
Lemma lem7214188 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7214189 (m : nat) (n : nat) (f : nat -> real) : (term30 m n f) = (term30 m n f).
Proof. exact (MK_COMB (@lem7214188) (@lem7214187 m n f)). Qed.
Lemma lem7214190 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7214191 (m : nat) (n : nat) (f : nat -> real) : (term31 m n f) = (term31 m n f).
Proof. exact (MK_COMB (@lem7214190) (@lem7214189 m n f)). Qed.
Lemma lem7214192 (m : nat) (n : nat) (f : nat -> real) : (term32 m n f) = (term32 m n f).
Proof. exact (MK_COMB (@lem7214191 m n f) (@lem7214177 m n f)). Qed.
Lemma lem7214193 (m : nat) (f : nat -> real) : (term33 m f) = (term33 m f).
Proof. exact (fun_ext (fun n : nat => @lem7214192 m n f)). Qed.
Lemma lem7214194 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7214195 (m : nat) (f : nat -> real) : (term34 m f) = (term34 m f).
Proof. exact (MK_COMB (@lem7214194) (@lem7214193 m f)). Qed.
Lemma lem7214196 (f : nat -> real) : (term35 f) = (term35 f).
Proof. exact (fun_ext (fun m : nat => @lem7214195 m f)). Qed.
Lemma lem7214197 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7214198 (f : nat -> real) : (term36 f) = (term36 f).
Proof. exact (MK_COMB (@lem7214197) (@lem7214196 f)). Qed.
Lemma lem7214199 : term37 = term37.
Proof. exact (fun_ext (fun f : nat -> real => @lem7214198 f)). Qed.
Lemma lem7214200 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7214201 : term17 = term17.
Proof. exact (MK_COMB (@lem7214200) (@lem7214199)). Qed.
Lemma lem7214202 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7214203 : term16 = term16.
Proof. exact (MK_COMB (@lem7214202) (@lem7214201)). Qed.
Lemma lem7214212 (n : nat) (m : nat) (p : nat) : (term38 n m p) = (term38 n m p).
Proof. exact (eq_refl (term38 n m p)). Qed.
Lemma lem7214213 (n : nat) (m : nat) : (term39 n m) = (term39 n m).
Proof. exact (fun_ext (fun p : nat => @lem7214212 n m p)). Qed.
Lemma lem7214214 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7214215 (n : nat) (m : nat) : (term40 n m) = (term40 n m).
Proof. exact (MK_COMB (@lem7214214) (@lem7214213 n m)). Qed.
Lemma lem7214216 (m : nat) : (term41 m) = (term41 m).
Proof. exact (fun_ext (fun n : nat => @lem7214215 n m)). Qed.
Lemma lem7214217 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7214218 (m : nat) : (term42 m) = (term42 m).
Proof. exact (MK_COMB (@lem7214217) (@lem7214216 m)). Qed.
Lemma lem7214219 : term43 = term43.
Proof. exact (fun_ext (fun m : nat => @lem7214218 m)). Qed.
Lemma lem7214220 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7214221 : term44 = term44.
Proof. exact (MK_COMB (@lem7214220) (@lem7214219)). Qed.
Lemma lem7214222 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7214223 : term18 = term18.
Proof. exact (MK_COMB (@lem7214222) (@lem7214221)). Qed.
Lemma lem7214224 : term20 = term20.
Proof. exact (MK_COMB (@lem7214223) (@lem7214203)). Qed.
Lemma lem7214231 (n : nat) (m : nat) : ((term45 m n) = (Peano.le n m)) = ((term45 m n) = (Peano.le n m)).
Proof. exact (eq_refl ((term45 m n) = (Peano.le n m))). Qed.
Lemma lem7214232 (m : nat) : (term46 m) = (term46 m).
Proof. exact (fun_ext (fun n : nat => @lem7214231 n m)). Qed.
Lemma lem7214233 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7214234 (m : nat) : (term47 m) = (term47 m).
Proof. exact (MK_COMB (@lem7214233) (@lem7214232 m)). Qed.
Lemma lem7214235 : term48 = term48.
Proof. exact (fun_ext (fun m : nat => @lem7214234 m)). Qed.
Lemma lem7214236 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7214237 : term49 = term49.
Proof. exact (MK_COMB (@lem7214236) (@lem7214235)). Qed.
Lemma lem7214238 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7214239 : term21 = term21.
Proof. exact (MK_COMB (@lem7214238) (@lem7214237)). Qed.
Lemma lem7214240 : term23 = term23.
Proof. exact (MK_COMB (@lem7214239) (@lem7214224)). Qed.
Lemma lem7214245 (m : nat) (n : nat) (f : nat -> real) : (term50 m n f) = (term50 m n f).
Proof. exact (eq_refl (term50 m n f)). Qed.
Lemma lem7214246 (m : nat) (f : nat -> real) : (term51 m f) = (term51 m f).
Proof. exact (fun_ext (fun n : nat => @lem7214245 m n f)). Qed.
Lemma lem7214247 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7214248 (m : nat) (f : nat -> real) : (term52 m f) = (term52 m f).
Proof. exact (MK_COMB (@lem7214247) (@lem7214246 m f)). Qed.
Lemma lem7214249 (f : nat -> real) : (term53 f) = (term53 f).
Proof. exact (fun_ext (fun m : nat => @lem7214248 m f)). Qed.
Lemma lem7214250 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7214251 (f : nat -> real) : (term54 f) = (term54 f).
Proof. exact (MK_COMB (@lem7214250) (@lem7214249 f)). Qed.
Lemma lem7214252 : term55 = term55.
Proof. exact (fun_ext (fun f : nat -> real => @lem7214251 f)). Qed.
Lemma lem7214253 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7214254 : term8 = term8.
Proof. exact (MK_COMB (@lem7214253) (@lem7214252)). Qed.
Lemma lem7214255 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7214256 : term10 = term10.
Proof. exact (MK_COMB (@lem7214255) (@lem7214254)). Qed.
Lemma lem7214257 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7214258 : term24 = term24.
Proof. exact (MK_COMB (@lem7214257) (@lem7214256)). Qed.
Lemma lem7214259 : term25 = term25.
Proof. exact (MK_COMB (@lem7214258) (@lem7214240)). Qed.
Lemma lem7214352 : term11 = term25.
Proof. exact (TRANS (@lem7214176) (@lem7214259)). Qed.
Lemma lem7214353 : term25 = term11.
Proof. exact (SYM (@lem7214352)). Qed.
Lemma lem7214354 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem7214355 (h1 : term49) : term49.
Proof. exact (h1). Qed.
Lemma lem7214356 (h1 : term44) : term44.
Proof. exact (h1). Qed.
Lemma lem7214357 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem7214364 (m : nat) (n : nat) (f : nat -> real) : (term56 m n f) = (term57 m n f).
Proof. exact (@lem17362 (Peano.lt n m) ((term26 m n f) = term27)). Qed.
Lemma lem7214365 (P : nat -> Prop) : (term58 P) = (term59 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem7214366 (m : nat) (f : nat -> real) : (term60 m f) = (term61 m f).
Proof. exact (@lem7214365 (term51 m f)). Qed.
Lemma lem7214367 (m : nat) (n : nat) (f : nat -> real) : (term62 m f n) = (term50 m n f).
Proof. exact (eq_refl (term62 m f n)). Qed.
Lemma lem7214368 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7214369 (m : nat) (n : nat) (f : nat -> real) : (term63 m f n) = (term56 m n f).
Proof. exact (MK_COMB (@lem7214368) (@lem7214367 m n f)). Qed.
Lemma lem7214370 (m : nat) (n : nat) (f : nat -> real) : (term63 m f n) = (term57 m n f).
Proof. exact (TRANS (@lem7214369 m n f) (@lem7214364 m n f)). Qed.
Lemma lem7214371 (m : nat) (f : nat -> real) : (term64 m f) = (term65 m f).
Proof. exact (fun_ext (fun n : nat => @lem7214370 m n f)). Qed.
Lemma lem7214372 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7214373 (m : nat) (f : nat -> real) : (term61 m f) = (term66 m f).
Proof. exact (MK_COMB (@lem7214372) (@lem7214371 m f)). Qed.
Lemma lem7214374 (m : nat) (f : nat -> real) : (term60 m f) = (term66 m f).
Proof. exact (TRANS (@lem7214366 m f) (@lem7214373 m f)). Qed.
Lemma lem7214375 (P : nat -> Prop) : (term58 P) = (term59 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem7214376 (f : nat -> real) : (term67 f) = (term68 f).
Proof. exact (@lem7214375 (term53 f)). Qed.
Lemma lem7214377 (m : nat) (f : nat -> real) : (term69 f m) = (term52 m f).
Proof. exact (eq_refl (term69 f m)). Qed.
Lemma lem7214378 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7214379 (m : nat) (f : nat -> real) : (term70 f m) = (term60 m f).
Proof. exact (MK_COMB (@lem7214378) (@lem7214377 m f)). Qed.
Lemma lem7214380 (m : nat) (f : nat -> real) : (term70 f m) = (term66 m f).
Proof. exact (TRANS (@lem7214379 m f) (@lem7214374 m f)). Qed.
Lemma lem7214381 (f : nat -> real) : (term71 f) = (term72 f).
Proof. exact (fun_ext (fun m : nat => @lem7214380 m f)). Qed.
Lemma lem7214382 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7214383 (f : nat -> real) : (term68 f) = (term73 f).
Proof. exact (MK_COMB (@lem7214382) (@lem7214381 f)). Qed.
Lemma lem7214384 (f : nat -> real) : (term67 f) = (term73 f).
Proof. exact (TRANS (@lem7214376 f) (@lem7214383 f)). Qed.
Lemma lem7214385 (P : type1010) : (term74 P) = (term75 P).
Proof. exact (@lem18392 (nat -> real) P). Qed.
Lemma lem7214386 : term10 = term76.
Proof. exact (@lem7214385 term55). Qed.
Lemma lem7214387 (f : nat -> real) : (term77 f) = (term54 f).
Proof. exact (eq_refl (term77 f)). Qed.
Lemma lem7214388 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7214389 (f : nat -> real) : (term78 f) = (term67 f).
Proof. exact (MK_COMB (@lem7214388) (@lem7214387 f)). Qed.
Lemma lem7214390 (f : nat -> real) : (term78 f) = (term73 f).
Proof. exact (TRANS (@lem7214389 f) (@lem7214384 f)). Qed.
Lemma lem7214391 : term79 = term80.
Proof. exact (fun_ext (fun f : nat -> real => @lem7214390 f)). Qed.
Lemma lem7214392 : (@ex (nat -> real)) = (@ex (nat -> real)).
Proof. exact (eq_refl (@ex (nat -> real))). Qed.
Lemma lem7214393 : term76 = term81.
Proof. exact (MK_COMB (@lem7214392) (@lem7214391)). Qed.
Lemma lem7214454 : term10 = term81.
Proof. exact (TRANS (@lem7214386) (@lem7214393)). Qed.
Lemma lem7214455 (h1 : term10) : term81.
Proof. exact (EQ_MP (@lem7214454) (@lem7214354 h1)). Qed.
Lemma lem7214459 (m : nat) (n : nat) : (term82 m n) = (Peano.lt m n).
Proof. exact (@lem16933 (Peano.lt m n)). Qed.
Lemma lem7214461 (n : nat) (m : nat) : (Peano.le n m) = (Peano.le n m).
Proof. exact (eq_refl (Peano.le n m)). Qed.
Lemma lem7214462 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7214463 (m : nat) (n : nat) : (term83 m n) = (term84 m n).
Proof. exact (MK_COMB (@lem7214462) (@lem7214459 m n)). Qed.
Lemma lem7214464 (n : nat) (m : nat) : (term85 n m) = (term86 n m).
Proof. exact (MK_COMB (@lem7214463 m n) (@lem7214461 n m)). Qed.
Lemma lem7214469 (n : nat) (m : nat) : (term87 n m) = (term87 n m).
Proof. exact (eq_refl (term87 n m)). Qed.
Lemma lem7214470 (n : nat) (m : nat) : (term88 n m) = (term89 n m).
Proof. exact (MK_COMB (@lem7214469 n m) (@lem7214464 n m)). Qed.
Lemma lem7214471 (n : nat) (m : nat) : ((term45 m n) = (Peano.le n m)) = (term88 n m).
Proof. exact (@lem17784 (term45 m n) (Peano.le n m)). Qed.
Lemma lem7214472 (n : nat) (m : nat) : ((term45 m n) = (Peano.le n m)) = (term89 n m).
Proof. exact (TRANS (@lem7214471 n m) (@lem7214470 n m)). Qed.
Lemma lem7214473 (m : nat) : (term46 m) = (term90 m).
Proof. exact (fun_ext (fun n : nat => @lem7214472 n m)). Qed.
Lemma lem7214474 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7214475 (m : nat) : (term47 m) = (term91 m).
Proof. exact (MK_COMB (@lem7214474) (@lem7214473 m)). Qed.
Lemma lem7214476 : term48 = term92.
Proof. exact (fun_ext (fun m : nat => @lem7214475 m)). Qed.
Lemma lem7214477 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7214478 : term49 = term93.
Proof. exact (MK_COMB (@lem7214477) (@lem7214476)). Qed.
Lemma lem7214484 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term94 A P Q) = (term95 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7214485 (P : nat -> Prop) (Q : nat -> Prop) : (term96 P Q) = (term97 P Q).
Proof. exact (@lem7214484 nat P Q). Qed.
Lemma lem7214486 (m : nat) : (term98 m) = (term99 m).
Proof. exact (@lem7214485 (term100 m) (term101 m)). Qed.
Lemma lem7214487 (n : nat) (m : nat) : (term102 m n) = (term103 n m).
Proof. exact (eq_refl (term102 m n)). Qed.
Lemma lem7214488 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7214489 (n : nat) (m : nat) : (term104 m n) = (term87 n m).
Proof. exact (MK_COMB (@lem7214488) (@lem7214487 n m)). Qed.
Lemma lem7214490 (n : nat) (m : nat) : (term105 m n) = (term86 n m).
Proof. exact (eq_refl (term105 m n)). Qed.
Lemma lem7214491 (n : nat) (m : nat) : (term106 m n) = (term89 n m).
Proof. exact (MK_COMB (@lem7214489 n m) (@lem7214490 n m)). Qed.
Lemma lem7214492 (m : nat) : (term107 m) = (term90 m).
Proof. exact (fun_ext (fun n : nat => @lem7214491 n m)). Qed.
Lemma lem7214493 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7214494 (m : nat) : (term98 m) = (term91 m).
Proof. exact (MK_COMB (@lem7214493) (@lem7214492 m)). Qed.
Lemma lem7214495 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7214496 (m : nat) : (term108 m) = (term109 m).
Proof. exact (MK_COMB (@lem7214495) (@lem7214494 m)). Qed.
Lemma lem7214497 (n : nat) (m : nat) : (term102 m n) = (term103 n m).
Proof. exact (eq_refl (term102 m n)). Qed.
Lemma lem7214498 (m : nat) : (term110 m) = (term100 m).
Proof. exact (fun_ext (fun n : nat => @lem7214497 n m)). Qed.
Lemma lem7214499 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7214500 (m : nat) : (term111 m) = (term112 m).
Proof. exact (MK_COMB (@lem7214499) (@lem7214498 m)). Qed.
Lemma lem7214501 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7214502 (m : nat) : (term113 m) = (term114 m).
Proof. exact (MK_COMB (@lem7214501) (@lem7214500 m)). Qed.
Lemma lem7214503 (n : nat) (m : nat) : (term105 m n) = (term86 n m).
Proof. exact (eq_refl (term105 m n)). Qed.
Lemma lem7214504 (m : nat) : (term115 m) = (term101 m).
Proof. exact (fun_ext (fun n : nat => @lem7214503 n m)). Qed.
Lemma lem7214505 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7214506 (m : nat) : (term116 m) = (term117 m).
Proof. exact (MK_COMB (@lem7214505) (@lem7214504 m)). Qed.
Lemma lem7214507 (m : nat) : (term99 m) = (term118 m).
Proof. exact (MK_COMB (@lem7214502 m) (@lem7214506 m)). Qed.
Lemma lem7214508 (m : nat) : ((term98 m) = (term99 m)) = ((term91 m) = (term118 m)).
Proof. exact (MK_COMB (@lem7214496 m) (@lem7214507 m)). Qed.
Lemma lem7214509 (m : nat) : (term91 m) = (term118 m).
Proof. exact (EQ_MP (@lem7214508 m) (@lem7214486 m)). Qed.
Lemma lem7214606 : term92 = term119.
Proof. exact (fun_ext (fun m : nat => @lem7214509 m)). Qed.
Lemma lem7214607 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7214608 : term93 = term120.
Proof. exact (MK_COMB (@lem7214607) (@lem7214606)). Qed.
Lemma lem7214610 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term94 A P Q) = (term95 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7214611 (P : nat -> Prop) (Q : nat -> Prop) : (term96 P Q) = (term97 P Q).
Proof. exact (@lem7214610 nat P Q). Qed.
Lemma lem7214612 : term121 = term122.
Proof. exact (@lem7214611 term123 term124). Qed.
Lemma lem7214613 (m : nat) : (term125 m) = (term112 m).
Proof. exact (eq_refl (term125 m)). Qed.
Lemma lem7214614 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7214615 (m : nat) : (term126 m) = (term114 m).
Proof. exact (MK_COMB (@lem7214614) (@lem7214613 m)). Qed.
Lemma lem7214616 (m : nat) : (term127 m) = (term117 m).
Proof. exact (eq_refl (term127 m)). Qed.
Lemma lem7214617 (m : nat) : (term128 m) = (term118 m).
Proof. exact (MK_COMB (@lem7214615 m) (@lem7214616 m)). Qed.
Lemma lem7214618 : term129 = term119.
Proof. exact (fun_ext (fun m : nat => @lem7214617 m)). Qed.
Lemma lem7214619 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7214620 : term121 = term120.
Proof. exact (MK_COMB (@lem7214619) (@lem7214618)). Qed.
Lemma lem7214621 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7214622 : term130 = term131.
Proof. exact (MK_COMB (@lem7214621) (@lem7214620)). Qed.
Lemma lem7214623 (m : nat) : (term125 m) = (term112 m).
Proof. exact (eq_refl (term125 m)). Qed.
Lemma lem7214624 : term132 = term123.
Proof. exact (fun_ext (fun m : nat => @lem7214623 m)). Qed.
Lemma lem7214625 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7214626 : term133 = term134.
Proof. exact (MK_COMB (@lem7214625) (@lem7214624)). Qed.
Lemma lem7214627 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7214628 : term135 = term136.
Proof. exact (MK_COMB (@lem7214627) (@lem7214626)). Qed.
Lemma lem7214629 (m : nat) : (term127 m) = (term117 m).
Proof. exact (eq_refl (term127 m)). Qed.
Lemma lem7214630 : term137 = term124.
Proof. exact (fun_ext (fun m : nat => @lem7214629 m)). Qed.
Lemma lem7214631 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7214632 : term138 = term139.
Proof. exact (MK_COMB (@lem7214631) (@lem7214630)). Qed.
Lemma lem7214633 : term122 = term140.
Proof. exact (MK_COMB (@lem7214628) (@lem7214632)). Qed.
Lemma lem7214634 : (term121 = term122) = (term120 = term140).
Proof. exact (MK_COMB (@lem7214622) (@lem7214633)). Qed.
Lemma lem7214635 : term120 = term140.
Proof. exact (EQ_MP (@lem7214634) (@lem7214612)). Qed.
Lemma lem7214742 : term93 = term140.
Proof. exact (TRANS (@lem7214608) (@lem7214635)). Qed.
Lemma lem7214743 : term49 = term140.
Proof. exact (TRANS (@lem7214478) (@lem7214742)). Qed.
Lemma lem7214744 (h1 : term49) : term140.
Proof. exact (EQ_MP (@lem7214743) (@lem7214355 h1)). Qed.
Lemma lem7214751 (m : nat) (n : nat) (p : nat) : (term141 m n p) = (term142 m n p).
Proof. exact (@lem17045 (Peano.le m n) (Peano.le n p)). Qed.
Lemma lem7214752 (m : nat) (p : nat) : (Peano.le m p) = (Peano.le m p).
Proof. exact (eq_refl (Peano.le m p)). Qed.
Lemma lem7214753 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7214754 (m : nat) (n : nat) (p : nat) : (term143 m n p) = (term144 m n p).
Proof. exact (MK_COMB (@lem7214753) (@lem7214751 m n p)). Qed.
Lemma lem7214755 (n : nat) (m : nat) (p : nat) : (term145 n m p) = (term146 n m p).
Proof. exact (MK_COMB (@lem7214754 m n p) (@lem7214752 m p)). Qed.
Lemma lem7214756 (n : nat) (m : nat) (p : nat) : (term38 n m p) = (term145 n m p).
Proof. exact (@lem17265 (term147 m n p) (Peano.le m p)). Qed.
Lemma lem7214757 (n : nat) (m : nat) (p : nat) : (term38 n m p) = (term146 n m p).
Proof. exact (TRANS (@lem7214756 n m p) (@lem7214755 n m p)). Qed.
Lemma lem7214758 (n : nat) (m : nat) : (term39 n m) = (term148 n m).
Proof. exact (fun_ext (fun p : nat => @lem7214757 n m p)). Qed.
Lemma lem7214759 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7214760 (n : nat) (m : nat) : (term40 n m) = (term149 n m).
Proof. exact (MK_COMB (@lem7214759) (@lem7214758 n m)). Qed.
Lemma lem7214761 (m : nat) : (term41 m) = (term150 m).
Proof. exact (fun_ext (fun n : nat => @lem7214760 n m)). Qed.
Lemma lem7214762 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7214763 (m : nat) : (term42 m) = (term151 m).
Proof. exact (MK_COMB (@lem7214762) (@lem7214761 m)). Qed.
Lemma lem7214764 : term43 = term152.
Proof. exact (fun_ext (fun m : nat => @lem7214763 m)). Qed.
Lemma lem7214765 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7214826 : term44 = term153.
Proof. exact (MK_COMB (@lem7214765) (@lem7214764)). Qed.
Lemma lem7214827 (h1 : term44) : term153.
Proof. exact (EQ_MP (@lem7214826) (@lem7214356 h1)). Qed.
Lemma lem7214838 (m : nat) (n : nat) (f : nat -> real) (i : nat) : (term154 m n f i) = (term155 m n f i).
Proof. exact (@lem17362 (term147 m i n) ((f i) = term27)). Qed.
Lemma lem7214839 (P : nat -> Prop) : (term58 P) = (term59 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem7214840 (m : nat) (n : nat) (f : nat -> real) : (term156 m n f) = (term157 m n f).
Proof. exact (@lem7214839 (term29 m n f)). Qed.
Lemma lem7214841 (m : nat) (n : nat) (f : nat -> real) (i : nat) : (term158 m n f i) = (term28 m n f i).
Proof. exact (eq_refl (term158 m n f i)). Qed.
Lemma lem7214842 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7214843 (m : nat) (n : nat) (f : nat -> real) (i : nat) : (term159 m n f i) = (term154 m n f i).
Proof. exact (MK_COMB (@lem7214842) (@lem7214841 m n f i)). Qed.
Lemma lem7214844 (m : nat) (n : nat) (f : nat -> real) (i : nat) : (term159 m n f i) = (term155 m n f i).
Proof. exact (TRANS (@lem7214843 m n f i) (@lem7214838 m n f i)). Qed.
Lemma lem7214845 (m : nat) (n : nat) (f : nat -> real) : (term160 m n f) = (term161 m n f).
Proof. exact (fun_ext (fun i : nat => @lem7214844 m n f i)). Qed.
Lemma lem7214846 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7214847 (m : nat) (n : nat) (f : nat -> real) : (term157 m n f) = (term162 m n f).
Proof. exact (MK_COMB (@lem7214846) (@lem7214845 m n f)). Qed.
Lemma lem7214848 (m : nat) (n : nat) (f : nat -> real) : (term156 m n f) = (term162 m n f).
Proof. exact (TRANS (@lem7214840 m n f) (@lem7214847 m n f)). Qed.
Lemma lem7214849 (m : nat) (n : nat) (f : nat -> real) : ((term26 m n f) = term27) = ((term26 m n f) = term27).
Proof. exact (eq_refl ((term26 m n f) = term27)). Qed.
Lemma lem7214850 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7214851 (m : nat) (n : nat) (f : nat -> real) : (term163 m n f) = (term164 m n f).
Proof. exact (MK_COMB (@lem7214850) (@lem7214848 m n f)). Qed.
Lemma lem7214852 (m : nat) (n : nat) (f : nat -> real) : (term165 m n f) = (term166 m n f).
Proof. exact (MK_COMB (@lem7214851 m n f) (@lem7214849 m n f)). Qed.
Lemma lem7214853 (m : nat) (n : nat) (f : nat -> real) : (term32 m n f) = (term165 m n f).
Proof. exact (@lem17265 (term30 m n f) ((term26 m n f) = term27)). Qed.
Lemma lem7214854 (m : nat) (n : nat) (f : nat -> real) : (term32 m n f) = (term166 m n f).
Proof. exact (TRANS (@lem7214853 m n f) (@lem7214852 m n f)). Qed.
Lemma lem7214855 (m : nat) (f : nat -> real) : (term33 m f) = (term167 m f).
Proof. exact (fun_ext (fun n : nat => @lem7214854 m n f)). Qed.
Lemma lem7214856 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7214857 (m : nat) (f : nat -> real) : (term34 m f) = (term168 m f).
Proof. exact (MK_COMB (@lem7214856) (@lem7214855 m f)). Qed.
Lemma lem7214858 (f : nat -> real) : (term35 f) = (term169 f).
Proof. exact (fun_ext (fun m : nat => @lem7214857 m f)). Qed.
Lemma lem7214859 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7214860 (f : nat -> real) : (term36 f) = (term170 f).
Proof. exact (MK_COMB (@lem7214859) (@lem7214858 f)). Qed.
Lemma lem7214861 : term37 = term171.
Proof. exact (fun_ext (fun f : nat -> real => @lem7214860 f)). Qed.
Lemma lem7214862 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7214863 : term17 = term172.
Proof. exact (MK_COMB (@lem7214862) (@lem7214861)). Qed.
Lemma lem7214970 {A : Type'} (P : A -> Prop) (Q : Prop) : (term173 A P Q) = (term174 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7214971 (P : nat -> Prop) (Q : Prop) : (term175 P Q) = (term176 P Q).
Proof. exact (@lem7214970 nat P Q). Qed.
Lemma lem7214972 (m : nat) (n : nat) (f : nat -> real) : (term177 m n f) = (term178 m n f).
Proof. exact (@lem7214971 (term161 m n f) ((term26 m n f) = term27)). Qed.
Lemma lem7214973 (m : nat) (n : nat) (f : nat -> real) (i : nat) : (term179 m n f i) = (term155 m n f i).
Proof. exact (eq_refl (term179 m n f i)). Qed.
Lemma lem7214974 (m : nat) (n : nat) (f : nat -> real) : (term180 m n f) = (term161 m n f).
Proof. exact (fun_ext (fun i : nat => @lem7214973 m n f i)). Qed.
Lemma lem7214975 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7214976 (m : nat) (n : nat) (f : nat -> real) : (term181 m n f) = (term162 m n f).
Proof. exact (MK_COMB (@lem7214975) (@lem7214974 m n f)). Qed.
Lemma lem7214977 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7214978 (m : nat) (n : nat) (f : nat -> real) : (term182 m n f) = (term164 m n f).
Proof. exact (MK_COMB (@lem7214977) (@lem7214976 m n f)). Qed.
Lemma lem7214979 (m : nat) (n : nat) (f : nat -> real) : ((term26 m n f) = term27) = ((term26 m n f) = term27).
Proof. exact (eq_refl ((term26 m n f) = term27)). Qed.
Lemma lem7214980 (m : nat) (n : nat) (f : nat -> real) : (term177 m n f) = (term166 m n f).
Proof. exact (MK_COMB (@lem7214978 m n f) (@lem7214979 m n f)). Qed.
Lemma lem7214981 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7214982 (m : nat) (n : nat) (f : nat -> real) : (term183 m n f) = (term184 m n f).
Proof. exact (MK_COMB (@lem7214981) (@lem7214980 m n f)). Qed.
Lemma lem7214983 (m : nat) (n : nat) (f : nat -> real) (i : nat) : (term179 m n f i) = (term155 m n f i).
Proof. exact (eq_refl (term179 m n f i)). Qed.
Lemma lem7214984 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7214985 (m : nat) (n : nat) (f : nat -> real) (i : nat) : (term185 m n f i) = (term186 m n f i).
Proof. exact (MK_COMB (@lem7214984) (@lem7214983 m n f i)). Qed.
Lemma lem7214986 (m : nat) (n : nat) (f : nat -> real) : ((term26 m n f) = term27) = ((term26 m n f) = term27).
Proof. exact (eq_refl ((term26 m n f) = term27)). Qed.
Lemma lem7214987 (i : nat) (m : nat) (n : nat) (f : nat -> real) : (term187 i m n f) = (term188 i m n f).
Proof. exact (MK_COMB (@lem7214985 m n f i) (@lem7214986 m n f)). Qed.
Lemma lem7214988 (m : nat) (n : nat) (f : nat -> real) : (term189 m n f) = (term190 m n f).
Proof. exact (fun_ext (fun i : nat => @lem7214987 i m n f)). Qed.
Lemma lem7214989 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7214990 (m : nat) (n : nat) (f : nat -> real) : (term178 m n f) = (term191 m n f).
Proof. exact (MK_COMB (@lem7214989) (@lem7214988 m n f)). Qed.
Lemma lem7214991 (m : nat) (n : nat) (f : nat -> real) : ((term177 m n f) = (term178 m n f)) = ((term166 m n f) = (term191 m n f)).
Proof. exact (MK_COMB (@lem7214982 m n f) (@lem7214990 m n f)). Qed.
Lemma lem7214992 (m : nat) (n : nat) (f : nat -> real) : (term166 m n f) = (term191 m n f).
Proof. exact (EQ_MP (@lem7214991 m n f) (@lem7214972 m n f)). Qed.
Lemma lem7214993 (m : nat) (f : nat -> real) : (term167 m f) = (term192 m f).
Proof. exact (fun_ext (fun n : nat => @lem7214992 m n f)). Qed.
Lemma lem7214994 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7214995 (m : nat) (f : nat -> real) : (term168 m f) = (term193 m f).
Proof. exact (MK_COMB (@lem7214994) (@lem7214993 m f)). Qed.
Lemma lem7214997 {A B : Type'} (P : type1413 A B) : (term194 A B P) = (term195 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7214998 (P : type1605) : (term196 P) = (term197 P).
Proof. exact (@lem7214997 nat nat P). Qed.
Lemma lem7214999 (m : nat) (f : nat -> real) : (term198 m f) = (term199 m f).
Proof. exact (@lem7214998 (term200 m f)). Qed.
Lemma lem7215000 (m : nat) (n : nat) (f : nat -> real) : (term201 m f n) = (term190 m n f).
Proof. exact (eq_refl (term201 m f n)). Qed.
Lemma lem7215001 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem7215002 (m : nat) (n : nat) (f : nat -> real) (i : nat) : (term202 m f n i) = (term203 m n f i).
Proof. exact (MK_COMB (@lem7215000 m n f) (@lem7215001 i)). Qed.
Lemma lem7215003 (i : nat) (m : nat) (n : nat) (f : nat -> real) : (term203 m n f i) = (term188 i m n f).
Proof. exact (eq_refl (term203 m n f i)). Qed.
Lemma lem7215004 (i : nat) (m : nat) (n : nat) (f : nat -> real) : (term202 m f n i) = (term188 i m n f).
Proof. exact (TRANS (@lem7215002 m n f i) (@lem7215003 i m n f)). Qed.
Lemma lem7215005 (m : nat) (n : nat) (f : nat -> real) : (term204 m f n) = (term190 m n f).
Proof. exact (fun_ext (fun i : nat => @lem7215004 i m n f)). Qed.
Lemma lem7215006 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7215007 (m : nat) (n : nat) (f : nat -> real) : (term205 m f n) = (term191 m n f).
Proof. exact (MK_COMB (@lem7215006) (@lem7215005 m n f)). Qed.
Lemma lem7215008 (m : nat) (f : nat -> real) : (term206 m f) = (term192 m f).
Proof. exact (fun_ext (fun n : nat => @lem7215007 m n f)). Qed.
Lemma lem7215009 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7215010 (m : nat) (f : nat -> real) : (term198 m f) = (term193 m f).
Proof. exact (MK_COMB (@lem7215009) (@lem7215008 m f)). Qed.
Lemma lem7215011 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7215012 (m : nat) (f : nat -> real) : (term207 m f) = (term208 m f).
Proof. exact (MK_COMB (@lem7215011) (@lem7215010 m f)). Qed.
Lemma lem7215013 (m : nat) (n : nat) (f : nat -> real) : (term201 m f n) = (term190 m n f).
Proof. exact (eq_refl (term201 m f n)). Qed.
Lemma lem7215014 (i : nat -> nat) (n : nat) : (i n) = (i n).
Proof. exact (eq_refl (i n)). Qed.
Lemma lem7215015 (m : nat) (f : nat -> real) (i : nat -> nat) (n : nat) : (term209 m f i n) = (term210 m f i n).
Proof. exact (MK_COMB (@lem7215013 m n f) (@lem7215014 i n)). Qed.
Lemma lem7215016 (i : nat -> nat) (m : nat) (n : nat) (f : nat -> real) : (term210 m f i n) = (term211 i m n f).
Proof. exact (eq_refl (term210 m f i n)). Qed.
Lemma lem7215017 (i : nat -> nat) (m : nat) (n : nat) (f : nat -> real) : (term209 m f i n) = (term211 i m n f).
Proof. exact (TRANS (@lem7215015 m f i n) (@lem7215016 i m n f)). Qed.
Lemma lem7215018 (i : nat -> nat) (m : nat) (f : nat -> real) : (term212 m f i) = (term213 i m f).
Proof. exact (fun_ext (fun n : nat => @lem7215017 i m n f)). Qed.
Lemma lem7215019 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7215020 (i : nat -> nat) (m : nat) (f : nat -> real) : (term214 m f i) = (term215 i m f).
Proof. exact (MK_COMB (@lem7215019) (@lem7215018 i m f)). Qed.
Lemma lem7215021 (m : nat) (f : nat -> real) : (term216 m f) = (term217 m f).
Proof. exact (fun_ext (fun i : nat -> nat => @lem7215020 i m f)). Qed.
Lemma lem7215022 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem7215023 (m : nat) (f : nat -> real) : (term199 m f) = (term218 m f).
Proof. exact (MK_COMB (@lem7215022) (@lem7215021 m f)). Qed.
Lemma lem7215024 (m : nat) (f : nat -> real) : ((term198 m f) = (term199 m f)) = ((term193 m f) = (term218 m f)).
Proof. exact (MK_COMB (@lem7215012 m f) (@lem7215023 m f)). Qed.
Lemma lem7215025 (m : nat) (f : nat -> real) : (term193 m f) = (term218 m f).
Proof. exact (EQ_MP (@lem7215024 m f) (@lem7214999 m f)). Qed.
Lemma lem7215026 (m : nat) (f : nat -> real) : (term168 m f) = (term218 m f).
Proof. exact (TRANS (@lem7214995 m f) (@lem7215025 m f)). Qed.
Lemma lem7215027 (f : nat -> real) : (term169 f) = (term219 f).
Proof. exact (fun_ext (fun m : nat => @lem7215026 m f)). Qed.
Lemma lem7215028 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7215029 (f : nat -> real) : (term170 f) = (term220 f).
Proof. exact (MK_COMB (@lem7215028) (@lem7215027 f)). Qed.
Lemma lem7215031 {A B : Type'} (P : type1413 A B) : (term194 A B P) = (term195 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7215032 (P : type1586) : (term221 P) = (term222 P).
Proof. exact (@lem7215031 nat (nat -> nat) P). Qed.
Lemma lem7215033 (f : nat -> real) : (term223 f) = (term224 f).
Proof. exact (@lem7215032 (term225 f)). Qed.
Lemma lem7215034 (m : nat) (f : nat -> real) : (term226 f m) = (term217 m f).
Proof. exact (eq_refl (term226 f m)). Qed.
Lemma lem7215035 (i : nat -> nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem7215036 (m : nat) (f : nat -> real) (i : nat -> nat) : (term227 f m i) = (term228 m f i).
Proof. exact (MK_COMB (@lem7215034 m f) (@lem7215035 i)). Qed.
Lemma lem7215037 (i : nat -> nat) (m : nat) (f : nat -> real) : (term228 m f i) = (term215 i m f).
Proof. exact (eq_refl (term228 m f i)). Qed.
Lemma lem7215038 (i : nat -> nat) (m : nat) (f : nat -> real) : (term227 f m i) = (term215 i m f).
Proof. exact (TRANS (@lem7215036 m f i) (@lem7215037 i m f)). Qed.
Lemma lem7215039 (m : nat) (f : nat -> real) : (term229 f m) = (term217 m f).
Proof. exact (fun_ext (fun i : nat -> nat => @lem7215038 i m f)). Qed.
Lemma lem7215040 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem7215041 (m : nat) (f : nat -> real) : (term230 f m) = (term218 m f).
Proof. exact (MK_COMB (@lem7215040) (@lem7215039 m f)). Qed.
Lemma lem7215042 (f : nat -> real) : (term231 f) = (term219 f).
Proof. exact (fun_ext (fun m : nat => @lem7215041 m f)). Qed.
Lemma lem7215043 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7215044 (f : nat -> real) : (term223 f) = (term220 f).
Proof. exact (MK_COMB (@lem7215043) (@lem7215042 f)). Qed.
Lemma lem7215045 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7215046 (f : nat -> real) : (term232 f) = (term233 f).
Proof. exact (MK_COMB (@lem7215045) (@lem7215044 f)). Qed.
Lemma lem7215047 (m : nat) (f : nat -> real) : (term226 f m) = (term217 m f).
Proof. exact (eq_refl (term226 f m)). Qed.
Lemma lem7215048 (i : type1606) (m : nat) : (i m) = (i m).
Proof. exact (eq_refl (i m)). Qed.
Lemma lem7215049 (f : nat -> real) (i : type1606) (m : nat) : (term234 f i m) = (term235 f i m).
Proof. exact (MK_COMB (@lem7215047 m f) (@lem7215048 i m)). Qed.
Lemma lem7215050 (i : type1606) (m : nat) (f : nat -> real) : (term235 f i m) = (term236 i m f).
Proof. exact (eq_refl (term235 f i m)). Qed.
Lemma lem7215051 (i : type1606) (m : nat) (f : nat -> real) : (term234 f i m) = (term236 i m f).
Proof. exact (TRANS (@lem7215049 f i m) (@lem7215050 i m f)). Qed.
Lemma lem7215052 (i : type1606) (f : nat -> real) : (term237 f i) = (term238 i f).
Proof. exact (fun_ext (fun m : nat => @lem7215051 i m f)). Qed.
Lemma lem7215053 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7215054 (i : type1606) (f : nat -> real) : (term239 f i) = (term240 i f).
Proof. exact (MK_COMB (@lem7215053) (@lem7215052 i f)). Qed.
Lemma lem7215055 (f : nat -> real) : (term241 f) = (term242 f).
Proof. exact (fun_ext (fun i : type1606 => @lem7215054 i f)). Qed.
Lemma lem7215056 : (@ex (nat -> nat -> nat)) = (@ex (nat -> nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat -> nat))). Qed.
Lemma lem7215057 (f : nat -> real) : (term224 f) = (term243 f).
Proof. exact (MK_COMB (@lem7215056) (@lem7215055 f)). Qed.
Lemma lem7215058 (f : nat -> real) : ((term223 f) = (term224 f)) = ((term220 f) = (term243 f)).
Proof. exact (MK_COMB (@lem7215046 f) (@lem7215057 f)). Qed.
Lemma lem7215059 (f : nat -> real) : (term220 f) = (term243 f).
Proof. exact (EQ_MP (@lem7215058 f) (@lem7215033 f)). Qed.
Lemma lem7215060 (f : nat -> real) : (term170 f) = (term243 f).
Proof. exact (TRANS (@lem7215029 f) (@lem7215059 f)). Qed.
Lemma lem7215061 : term171 = term244.
Proof. exact (fun_ext (fun f : nat -> real => @lem7215060 f)). Qed.
Lemma lem7215062 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7215063 : term172 = term245.
Proof. exact (MK_COMB (@lem7215062) (@lem7215061)). Qed.
Lemma lem7215065 {A B : Type'} (P : type1413 A B) : (term194 A B P) = (term195 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7215066 (P : type1006) : (term246 P) = (term247 P).
Proof. exact (@lem7215065 (nat -> real) type1606 P). Qed.
Lemma lem7215067 : term248 = term249.
Proof. exact (@lem7215066 term250). Qed.
Lemma lem7215068 (f : nat -> real) : (term251 f) = (term242 f).
Proof. exact (eq_refl (term251 f)). Qed.
Lemma lem7215069 (i : type1606) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem7215070 (f : nat -> real) (i : type1606) : (term252 f i) = (term253 f i).
Proof. exact (MK_COMB (@lem7215068 f) (@lem7215069 i)). Qed.
Lemma lem7215071 (i : type1606) (f : nat -> real) : (term253 f i) = (term240 i f).
Proof. exact (eq_refl (term253 f i)). Qed.
Lemma lem7215072 (i : type1606) (f : nat -> real) : (term252 f i) = (term240 i f).
Proof. exact (TRANS (@lem7215070 f i) (@lem7215071 i f)). Qed.
Lemma lem7215073 (f : nat -> real) : (term254 f) = (term242 f).
Proof. exact (fun_ext (fun i : type1606 => @lem7215072 i f)). Qed.
Lemma lem7215074 : (@ex (nat -> nat -> nat)) = (@ex (nat -> nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat -> nat))). Qed.
Lemma lem7215075 (f : nat -> real) : (term255 f) = (term243 f).
Proof. exact (MK_COMB (@lem7215074) (@lem7215073 f)). Qed.
Lemma lem7215076 : term256 = term244.
Proof. exact (fun_ext (fun f : nat -> real => @lem7215075 f)). Qed.
Lemma lem7215077 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7215078 : term248 = term245.
Proof. exact (MK_COMB (@lem7215077) (@lem7215076)). Qed.
Lemma lem7215079 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7215080 : term257 = term258.
Proof. exact (MK_COMB (@lem7215079) (@lem7215078)). Qed.
Lemma lem7215081 (f : nat -> real) : (term251 f) = (term242 f).
Proof. exact (eq_refl (term251 f)). Qed.
Lemma lem7215082 (i : type1009) (f : nat -> real) : (i f) = (i f).
Proof. exact (eq_refl (i f)). Qed.
Lemma lem7215083 (i : type1009) (f : nat -> real) : (term259 i f) = (term260 i f).
Proof. exact (MK_COMB (@lem7215081 f) (@lem7215082 i f)). Qed.
Lemma lem7215084 (i : type1009) (f : nat -> real) : (term260 i f) = (term261 i f).
Proof. exact (eq_refl (term260 i f)). Qed.
Lemma lem7215085 (i : type1009) (f : nat -> real) : (term259 i f) = (term261 i f).
Proof. exact (TRANS (@lem7215083 i f) (@lem7215084 i f)). Qed.
Lemma lem7215086 (i : type1009) : (term262 i) = (term263 i).
Proof. exact (fun_ext (fun f : nat -> real => @lem7215085 i f)). Qed.
Lemma lem7215087 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7215088 (i : type1009) : (term264 i) = (term265 i).
Proof. exact (MK_COMB (@lem7215087) (@lem7215086 i)). Qed.
Lemma lem7215089 : term266 = term267.
Proof. exact (fun_ext (fun i : type1009 => @lem7215088 i)). Qed.
Lemma lem7215090 : (@ex ((nat -> real) -> nat -> nat -> nat)) = (@ex ((nat -> real) -> nat -> nat -> nat)).
Proof. exact (eq_refl (@ex ((nat -> real) -> nat -> nat -> nat))). Qed.
Lemma lem7215091 : term249 = term268.
Proof. exact (MK_COMB (@lem7215090) (@lem7215089)). Qed.
Lemma lem7215092 : (term248 = term249) = (term245 = term268).
Proof. exact (MK_COMB (@lem7215080) (@lem7215091)). Qed.
Lemma lem7215093 : term245 = term268.
Proof. exact (EQ_MP (@lem7215092) (@lem7215067)). Qed.
Lemma lem7215095 : term172 = term268.
Proof. exact (TRANS (@lem7215063) (@lem7215093)). Qed.
Lemma lem7215096 : term17 = term268.
Proof. exact (TRANS (@lem7214863) (@lem7215095)). Qed.
Lemma lem7215097 (h1 : term17) : term268.
Proof. exact (EQ_MP (@lem7215096) (@lem7214357 h1)). Qed.
Lemma lem7215098 (i : type1009) (h1 : term265 i) : term265 i.
Proof. exact (h1). Qed.
Lemma lem7215099 (f : nat -> real) (h1 : term73 f) : term73 f.
Proof. exact (h1). Qed.
Lemma lem7215100 (m : nat) (f : nat -> real) (h1 : term66 m f) : term66 m f.
Proof. exact (h1). Qed.
Lemma lem7215101 (m : nat) (n : nat) (f : nat -> real) (h1 : term57 m n f) : term57 m n f.
Proof. exact (h1). Qed.
Lemma lem7215108 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7215109 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7215108 nat (nat -> Prop) f x). Qed.
Lemma lem7215110 (n : nat) : (Peano.le n) = (@I (nat -> nat -> Prop) Peano.le n).
Proof. exact (@lem7215109 Peano.le n). Qed.
Lemma lem7215111 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem7215112 (n : nat) (m : nat) : (Peano.le n m) = (@I (nat -> nat -> Prop) Peano.le n m).
Proof. exact (MK_COMB (@lem7215110 n) (@lem7215111 m)). Qed.
Lemma lem7215114 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7215115 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7215114 nat Prop f x). Qed.
Lemma lem7215116 (n : nat) (m : nat) : (@I (nat -> nat -> Prop) Peano.le n m) = (term269 n m).
Proof. exact (@lem7215115 (@I (nat -> nat -> Prop) Peano.le n) m). Qed.
Lemma lem7215118 (n : nat) (m : nat) : (Peano.le n m) = (term269 n m).
Proof. exact (TRANS (@lem7215112 n m) (@lem7215116 n m)). Qed.
Lemma lem7215125 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7215126 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7215125 nat (nat -> Prop) f x). Qed.
Lemma lem7215127 (m : nat) : (Peano.lt m) = (@I (nat -> nat -> Prop) Peano.lt m).
Proof. exact (@lem7215126 Peano.lt m). Qed.
Lemma lem7215128 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7215129 (m : nat) (n : nat) : (Peano.lt m n) = (@I (nat -> nat -> Prop) Peano.lt m n).
Proof. exact (MK_COMB (@lem7215127 m) (@lem7215128 n)). Qed.
Lemma lem7215131 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7215132 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7215131 nat Prop f x). Qed.
Lemma lem7215133 (m : nat) (n : nat) : (@I (nat -> nat -> Prop) Peano.lt m n) = (term270 m n).
Proof. exact (@lem7215132 (@I (nat -> nat -> Prop) Peano.lt m) n). Qed.
Lemma lem7215135 (m : nat) (n : nat) : (Peano.lt m n) = (term270 m n).
Proof. exact (TRANS (@lem7215129 m n) (@lem7215133 m n)). Qed.
Lemma lem7215136 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7215137 (m : nat) (n : nat) : (term84 m n) = (term271 m n).
Proof. exact (MK_COMB (@lem7215136) (@lem7215135 m n)). Qed.
Lemma lem7215138 (n : nat) (m : nat) : (term86 n m) = (term272 n m).
Proof. exact (MK_COMB (@lem7215137 m n) (@lem7215118 n m)). Qed.
Lemma lem7215139 (m : nat) : (term101 m) = (term273 m).
Proof. exact (fun_ext (fun n : nat => @lem7215138 n m)). Qed.
Lemma lem7215140 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7215141 (m : nat) : (term117 m) = (term274 m).
Proof. exact (MK_COMB (@lem7215140) (@lem7215139 m)). Qed.
Lemma lem7215142 : term124 = term275.
Proof. exact (fun_ext (fun m : nat => @lem7215141 m)). Qed.
Lemma lem7215143 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7215144 : term139 = term276.
Proof. exact (MK_COMB (@lem7215143) (@lem7215142)). Qed.
Lemma lem7215145 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7215152 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7215153 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7215152 nat (nat -> Prop) f x). Qed.
Lemma lem7215154 (n : nat) : (Peano.le n) = (@I (nat -> nat -> Prop) Peano.le n).
Proof. exact (@lem7215153 Peano.le n). Qed.
Lemma lem7215155 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem7215156 (n : nat) (m : nat) : (Peano.le n m) = (@I (nat -> nat -> Prop) Peano.le n m).
Proof. exact (MK_COMB (@lem7215154 n) (@lem7215155 m)). Qed.
Lemma lem7215158 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7215159 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7215158 nat Prop f x). Qed.
Lemma lem7215160 (n : nat) (m : nat) : (@I (nat -> nat -> Prop) Peano.le n m) = (term269 n m).
Proof. exact (@lem7215159 (@I (nat -> nat -> Prop) Peano.le n) m). Qed.
Lemma lem7215162 (n : nat) (m : nat) : (Peano.le n m) = (term269 n m).
Proof. exact (TRANS (@lem7215156 n m) (@lem7215160 n m)). Qed.
Lemma lem7215163 (n : nat) (m : nat) : (term277 n m) = (term278 n m).
Proof. exact (MK_COMB (@lem7215145) (@lem7215162 n m)). Qed.
Lemma lem7215164 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7215171 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7215172 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7215171 nat (nat -> Prop) f x). Qed.
Lemma lem7215173 (m : nat) : (Peano.lt m) = (@I (nat -> nat -> Prop) Peano.lt m).
Proof. exact (@lem7215172 Peano.lt m). Qed.
Lemma lem7215174 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7215175 (m : nat) (n : nat) : (Peano.lt m n) = (@I (nat -> nat -> Prop) Peano.lt m n).
Proof. exact (MK_COMB (@lem7215173 m) (@lem7215174 n)). Qed.
Lemma lem7215177 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7215178 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7215177 nat Prop f x). Qed.
Lemma lem7215179 (m : nat) (n : nat) : (@I (nat -> nat -> Prop) Peano.lt m n) = (term270 m n).
Proof. exact (@lem7215178 (@I (nat -> nat -> Prop) Peano.lt m) n). Qed.
Lemma lem7215181 (m : nat) (n : nat) : (Peano.lt m n) = (term270 m n).
Proof. exact (TRANS (@lem7215175 m n) (@lem7215179 m n)). Qed.
Lemma lem7215182 (m : nat) (n : nat) : (term45 m n) = (term279 m n).
Proof. exact (MK_COMB (@lem7215164) (@lem7215181 m n)). Qed.
Lemma lem7215183 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7215184 (m : nat) (n : nat) : (term280 m n) = (term281 m n).
Proof. exact (MK_COMB (@lem7215183) (@lem7215182 m n)). Qed.
Lemma lem7215185 (n : nat) (m : nat) : (term103 n m) = (term282 n m).
Proof. exact (MK_COMB (@lem7215184 m n) (@lem7215163 n m)). Qed.
Lemma lem7215186 (m : nat) : (term100 m) = (term283 m).
Proof. exact (fun_ext (fun n : nat => @lem7215185 n m)). Qed.
Lemma lem7215187 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7215188 (m : nat) : (term112 m) = (term284 m).
Proof. exact (MK_COMB (@lem7215187) (@lem7215186 m)). Qed.
Lemma lem7215189 : term123 = term285.
Proof. exact (fun_ext (fun m : nat => @lem7215188 m)). Qed.
Lemma lem7215190 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7215191 : term134 = term286.
Proof. exact (MK_COMB (@lem7215190) (@lem7215189)). Qed.
Lemma lem7215192 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7215193 : term136 = term287.
Proof. exact (MK_COMB (@lem7215192) (@lem7215191)). Qed.
Lemma lem7215194 : term140 = term288.
Proof. exact (MK_COMB (@lem7215193) (@lem7215144)). Qed.
Lemma lem7215195 (h1 : term49) : term288.
Proof. exact (EQ_MP (@lem7215194) (@lem7214744 h1)). Qed.
Lemma lem7215202 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7215203 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7215202 nat (nat -> Prop) f x). Qed.
Lemma lem7215204 (m : nat) : (Peano.le m) = (@I (nat -> nat -> Prop) Peano.le m).
Proof. exact (@lem7215203 Peano.le m). Qed.
Lemma lem7215205 (p : nat) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem7215206 (m : nat) (p : nat) : (Peano.le m p) = (@I (nat -> nat -> Prop) Peano.le m p).
Proof. exact (MK_COMB (@lem7215204 m) (@lem7215205 p)). Qed.
Lemma lem7215208 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7215209 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7215208 nat Prop f x). Qed.
Lemma lem7215210 (m : nat) (p : nat) : (@I (nat -> nat -> Prop) Peano.le m p) = (term269 m p).
Proof. exact (@lem7215209 (@I (nat -> nat -> Prop) Peano.le m) p). Qed.
Lemma lem7215212 (m : nat) (p : nat) : (Peano.le m p) = (term269 m p).
Proof. exact (TRANS (@lem7215206 m p) (@lem7215210 m p)). Qed.
Lemma lem7215213 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7215220 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7215221 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7215220 nat (nat -> Prop) f x). Qed.
Lemma lem7215222 (n : nat) : (Peano.le n) = (@I (nat -> nat -> Prop) Peano.le n).
Proof. exact (@lem7215221 Peano.le n). Qed.
Lemma lem7215223 (p : nat) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem7215224 (n : nat) (p : nat) : (Peano.le n p) = (@I (nat -> nat -> Prop) Peano.le n p).
Proof. exact (MK_COMB (@lem7215222 n) (@lem7215223 p)). Qed.
Lemma lem7215226 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7215227 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7215226 nat Prop f x). Qed.
Lemma lem7215228 (n : nat) (p : nat) : (@I (nat -> nat -> Prop) Peano.le n p) = (term269 n p).
Proof. exact (@lem7215227 (@I (nat -> nat -> Prop) Peano.le n) p). Qed.
Lemma lem7215230 (n : nat) (p : nat) : (Peano.le n p) = (term269 n p).
Proof. exact (TRANS (@lem7215224 n p) (@lem7215228 n p)). Qed.
Lemma lem7215231 (n : nat) (p : nat) : (term277 n p) = (term278 n p).
Proof. exact (MK_COMB (@lem7215213) (@lem7215230 n p)). Qed.
Lemma lem7215232 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7215239 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7215240 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7215239 nat (nat -> Prop) f x). Qed.
Lemma lem7215241 (m : nat) : (Peano.le m) = (@I (nat -> nat -> Prop) Peano.le m).
Proof. exact (@lem7215240 Peano.le m). Qed.
Lemma lem7215242 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7215243 (m : nat) (n : nat) : (Peano.le m n) = (@I (nat -> nat -> Prop) Peano.le m n).
Proof. exact (MK_COMB (@lem7215241 m) (@lem7215242 n)). Qed.
Lemma lem7215245 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7215246 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7215245 nat Prop f x). Qed.
Lemma lem7215247 (m : nat) (n : nat) : (@I (nat -> nat -> Prop) Peano.le m n) = (term269 m n).
Proof. exact (@lem7215246 (@I (nat -> nat -> Prop) Peano.le m) n). Qed.
Lemma lem7215249 (m : nat) (n : nat) : (Peano.le m n) = (term269 m n).
Proof. exact (TRANS (@lem7215243 m n) (@lem7215247 m n)). Qed.
Lemma lem7215250 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (MK_COMB (@lem7215232) (@lem7215249 m n)). Qed.
Lemma lem7215251 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7215252 (m : nat) (n : nat) : (term289 m n) = (term290 m n).
Proof. exact (MK_COMB (@lem7215251) (@lem7215250 m n)). Qed.
Lemma lem7215253 (m : nat) (n : nat) (p : nat) : (term142 m n p) = (term291 m n p).
Proof. exact (MK_COMB (@lem7215252 m n) (@lem7215231 n p)). Qed.
Lemma lem7215254 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7215255 (m : nat) (n : nat) (p : nat) : (term144 m n p) = (term292 m n p).
Proof. exact (MK_COMB (@lem7215254) (@lem7215253 m n p)). Qed.
Lemma lem7215256 (n : nat) (m : nat) (p : nat) : (term146 n m p) = (term293 n m p).
Proof. exact (MK_COMB (@lem7215255 m n p) (@lem7215212 m p)). Qed.
Lemma lem7215257 (n : nat) (m : nat) : (term148 n m) = (term294 n m).
Proof. exact (fun_ext (fun p : nat => @lem7215256 n m p)). Qed.
Lemma lem7215258 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7215259 (n : nat) (m : nat) : (term149 n m) = (term295 n m).
Proof. exact (MK_COMB (@lem7215258) (@lem7215257 n m)). Qed.
Lemma lem7215260 (m : nat) : (term150 m) = (term296 m).
Proof. exact (fun_ext (fun n : nat => @lem7215259 n m)). Qed.
Lemma lem7215261 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7215262 (m : nat) : (term151 m) = (term297 m).
Proof. exact (MK_COMB (@lem7215261) (@lem7215260 m)). Qed.
Lemma lem7215263 : term152 = term298.
Proof. exact (fun_ext (fun m : nat => @lem7215262 m)). Qed.
Lemma lem7215264 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7215265 : term153 = term299.
Proof. exact (MK_COMB (@lem7215264) (@lem7215263)). Qed.
Lemma lem7215266 (h1 : term44) : term299.
Proof. exact (EQ_MP (@lem7215265) (@lem7214827 h1)). Qed.
Lemma lem7215267 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7215268 : (@sum nat) = (@sum nat).
Proof. exact (eq_refl (@sum nat)). Qed.
Lemma lem7215275 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7215276 (f : type1601) (x : nat) : (f x) = (@I (nat -> nat -> nat -> Prop) f x).
Proof. exact (@lem7215275 nat type1605 f x). Qed.
Lemma lem7215277 (m : nat) : (dotdot m) = (@I (nat -> nat -> nat -> Prop) dotdot m).
Proof. exact (@lem7215276 dotdot m). Qed.
Lemma lem7215278 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7215279 (m : nat) (n : nat) : (dotdot m n) = (@I (nat -> nat -> nat -> Prop) dotdot m n).
Proof. exact (MK_COMB (@lem7215277 m) (@lem7215278 n)). Qed.
Lemma lem7215281 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7215282 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7215281 nat (nat -> Prop) f x). Qed.
Lemma lem7215283 (m : nat) (n : nat) : (@I (nat -> nat -> nat -> Prop) dotdot m n) = (term300 m n).
Proof. exact (@lem7215282 (@I (nat -> nat -> nat -> Prop) dotdot m) n). Qed.
Lemma lem7215285 (m : nat) (n : nat) : (dotdot m n) = (term300 m n).
Proof. exact (TRANS (@lem7215279 m n) (@lem7215283 m n)). Qed.
Lemma lem7215286 (f : nat -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7215287 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (MK_COMB (@lem7215268) (@lem7215285 m n)). Qed.
Lemma lem7215288 (m : nat) (n : nat) (f : nat -> real) : (term26 m n f) = (term303 m n f).
Proof. exact (MK_COMB (@lem7215287 m n) (@lem7215286 f)). Qed.
Lemma lem7215290 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7215291 (f : type988) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> (nat -> real) -> real) f x).
Proof. exact (@lem7215290 (nat -> Prop) type1011 f x). Qed.
Lemma lem7215292 (m : nat) (n : nat) : (term302 m n) = (term304 m n).
Proof. exact (@lem7215291 (@sum nat) (term300 m n)). Qed.
Lemma lem7215293 (f : nat -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7215294 (m : nat) (n : nat) (f : nat -> real) : (term303 m n f) = (term305 m n f).
Proof. exact (MK_COMB (@lem7215292 m n) (@lem7215293 f)). Qed.
Lemma lem7215296 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7215297 (f : type1011) (x : nat -> real) : (f x) = (@I ((nat -> real) -> real) f x).
Proof. exact (@lem7215296 (nat -> real) real f x). Qed.
Lemma lem7215298 (m : nat) (n : nat) (f : nat -> real) : (term305 m n f) = (term306 m n f).
Proof. exact (@lem7215297 (term304 m n) f). Qed.
Lemma lem7215299 (m : nat) (n : nat) (f : nat -> real) : (term303 m n f) = (term306 m n f).
Proof. exact (TRANS (@lem7215294 m n f) (@lem7215298 m n f)). Qed.
Lemma lem7215300 (m : nat) (n : nat) (f : nat -> real) : (term26 m n f) = (term306 m n f).
Proof. exact (TRANS (@lem7215288 m n f) (@lem7215299 m n f)). Qed.
Lemma lem7215301 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7215306 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7215307 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7215306 nat nat f x). Qed.
Lemma lem7215309 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem7215307 NUMERAL 0). Qed.
Lemma lem7215310 : term27 = term307.
Proof. exact (MK_COMB (@lem7215301) (@lem7215309)). Qed.
Lemma lem7215312 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7215313 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7215312 nat real f x). Qed.
Lemma lem7215314 : term307 = term308.
Proof. exact (@lem7215313 real_of_num (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem7215315 : term27 = term308.
Proof. exact (TRANS (@lem7215310) (@lem7215314)). Qed.
Lemma lem7215316 (m : nat) (n : nat) (f : nat -> real) : (term309 m n f) = (term310 m n f).
Proof. exact (MK_COMB (@lem7215267) (@lem7215300 m n f)). Qed.
Lemma lem7215317 (m : nat) (n : nat) (f : nat -> real) : ((term26 m n f) = term27) = ((term306 m n f) = term308).
Proof. exact (MK_COMB (@lem7215316 m n f) (@lem7215315)). Qed.
Lemma lem7215318 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7215319 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7215320 (f : nat -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7215329 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7215330 (f : type1009) (x : nat -> real) : (f x) = (@I ((nat -> real) -> nat -> nat -> nat) f x).
Proof. exact (@lem7215329 (nat -> real) type1606 f x). Qed.
Lemma lem7215331 (i : type1009) (f : nat -> real) : (i f) = (@I ((nat -> real) -> nat -> nat -> nat) i f).
Proof. exact (@lem7215330 i f). Qed.
Lemma lem7215332 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem7215333 (i : type1009) (f : nat -> real) (m : nat) : (i f m) = (@I ((nat -> real) -> nat -> nat -> nat) i f m).
Proof. exact (MK_COMB (@lem7215331 i f) (@lem7215332 m)). Qed.
Lemma lem7215335 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7215336 (f : type1606) (x : nat) : (f x) = (@I (nat -> nat -> nat) f x).
Proof. exact (@lem7215335 nat (nat -> nat) f x). Qed.
Lemma lem7215337 (i : type1009) (f : nat -> real) (m : nat) : (@I ((nat -> real) -> nat -> nat -> nat) i f m) = (term311 i f m).
Proof. exact (@lem7215336 (@I ((nat -> real) -> nat -> nat -> nat) i f) m). Qed.
Lemma lem7215338 (i : type1009) (f : nat -> real) (m : nat) : (i f m) = (term311 i f m).
Proof. exact (TRANS (@lem7215333 i f m) (@lem7215337 i f m)). Qed.
Lemma lem7215339 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7215340 (i : type1009) (f : nat -> real) (m : nat) (n : nat) : (i f m n) = (term312 i f m n).
Proof. exact (MK_COMB (@lem7215338 i f m) (@lem7215339 n)). Qed.
Lemma lem7215342 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7215343 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7215342 nat nat f x). Qed.
Lemma lem7215344 (i : type1009) (f : nat -> real) (m : nat) (n : nat) : (term312 i f m n) = (term313 i f m n).
Proof. exact (@lem7215343 (term311 i f m) n). Qed.
Lemma lem7215346 (i : type1009) (f : nat -> real) (m : nat) (n : nat) : (i f m n) = (term313 i f m n).
Proof. exact (TRANS (@lem7215340 i f m n) (@lem7215344 i f m n)). Qed.
Lemma lem7215347 (i : type1009) (f : nat -> real) (m : nat) (n : nat) : (term314 i f m n) = (term315 i f m n).
Proof. exact (MK_COMB (@lem7215320 f) (@lem7215346 i f m n)). Qed.
Lemma lem7215349 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7215350 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7215349 nat real f x). Qed.
Lemma lem7215351 (i : type1009) (f : nat -> real) (m : nat) (n : nat) : (term315 i f m n) = (term316 i f m n).
Proof. exact (@lem7215350 f (term313 i f m n)). Qed.
Lemma lem7215352 (i : type1009) (f : nat -> real) (m : nat) (n : nat) : (term314 i f m n) = (term316 i f m n).
Proof. exact (TRANS (@lem7215347 i f m n) (@lem7215351 i f m n)). Qed.
Lemma lem7215353 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7215358 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7215359 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7215358 nat nat f x). Qed.
Lemma lem7215361 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem7215359 NUMERAL 0). Qed.
Lemma lem7215362 : term27 = term307.
Proof. exact (MK_COMB (@lem7215353) (@lem7215361)). Qed.
Lemma lem7215364 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7215365 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7215364 nat real f x). Qed.
Lemma lem7215366 : term307 = term308.
Proof. exact (@lem7215365 real_of_num (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem7215367 : term27 = term308.
Proof. exact (TRANS (@lem7215362) (@lem7215366)). Qed.
Lemma lem7215368 (i : type1009) (f : nat -> real) (m : nat) (n : nat) : (term317 i f m n) = (term318 i f m n).
Proof. exact (MK_COMB (@lem7215319) (@lem7215352 i f m n)). Qed.
Lemma lem7215369 (i : type1009) (f : nat -> real) (m : nat) (n : nat) : ((term314 i f m n) = term27) = ((term316 i f m n) = term308).
Proof. exact (MK_COMB (@lem7215368 i f m n) (@lem7215367)). Qed.
Lemma lem7215370 (i : type1009) (f : nat -> real) (m : nat) (n : nat) : (term319 i f m n) = (term320 i f m n).
Proof. exact (MK_COMB (@lem7215318) (@lem7215369 i f m n)). Qed.
Lemma lem7215371 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem7215380 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7215381 (f : type1009) (x : nat -> real) : (f x) = (@I ((nat -> real) -> nat -> nat -> nat) f x).
Proof. exact (@lem7215380 (nat -> real) type1606 f x). Qed.
Lemma lem7215382 (i : type1009) (f : nat -> real) : (i f) = (@I ((nat -> real) -> nat -> nat -> nat) i f).
Proof. exact (@lem7215381 i f). Qed.
Lemma lem7215383 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem7215384 (i : type1009) (f : nat -> real) (m : nat) : (i f m) = (@I ((nat -> real) -> nat -> nat -> nat) i f m).
Proof. exact (MK_COMB (@lem7215382 i f) (@lem7215383 m)). Qed.
Lemma lem7215386 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7215387 (f : type1606) (x : nat) : (f x) = (@I (nat -> nat -> nat) f x).
Proof. exact (@lem7215386 nat (nat -> nat) f x). Qed.
Lemma lem7215388 (i : type1009) (f : nat -> real) (m : nat) : (@I ((nat -> real) -> nat -> nat -> nat) i f m) = (term311 i f m).
Proof. exact (@lem7215387 (@I ((nat -> real) -> nat -> nat -> nat) i f) m). Qed.
Lemma lem7215389 (i : type1009) (f : nat -> real) (m : nat) : (i f m) = (term311 i f m).
Proof. exact (TRANS (@lem7215384 i f m) (@lem7215388 i f m)). Qed.
Lemma lem7215390 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7215391 (i : type1009) (f : nat -> real) (m : nat) (n : nat) : (i f m n) = (term312 i f m n).
Proof. exact (MK_COMB (@lem7215389 i f m) (@lem7215390 n)). Qed.
Lemma lem7215393 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7215394 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7215393 nat nat f x). Qed.
Lemma lem7215395 (i : type1009) (f : nat -> real) (m : nat) (n : nat) : (term312 i f m n) = (term313 i f m n).
Proof. exact (@lem7215394 (term311 i f m) n). Qed.
Lemma lem7215397 (i : type1009) (f : nat -> real) (m : nat) (n : nat) : (i f m n) = (term313 i f m n).
Proof. exact (TRANS (@lem7215391 i f m n) (@lem7215395 i f m n)). Qed.
Lemma lem7215398 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7215399 (i : type1009) (f : nat -> real) (m : nat) (n : nat) : (term321 i f m n) = (term322 i f m n).
Proof. exact (MK_COMB (@lem7215371) (@lem7215397 i f m n)). Qed.
Lemma lem7215400 (i : type1009) (f : nat -> real) (m : nat) (n : nat) : (term323 i f m n) = (term324 i f m n).
Proof. exact (MK_COMB (@lem7215399 i f m n) (@lem7215398 n)). Qed.
Lemma lem7215402 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7215403 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7215402 nat (nat -> Prop) f x). Qed.
Lemma lem7215404 (i : type1009) (f : nat -> real) (m : nat) (n : nat) : (term322 i f m n) = (term325 i f m n).
Proof. exact (@lem7215403 Peano.le (term313 i f m n)). Qed.
Lemma lem7215405 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7215406 (i : type1009) (f : nat -> real) (m : nat) (n : nat) : (term324 i f m n) = (term326 i f m n).
Proof. exact (MK_COMB (@lem7215404 i f m n) (@lem7215405 n)). Qed.
Lemma lem7215408 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7215409 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7215408 nat Prop f x). Qed.
Lemma lem7215410 (i : type1009) (f : nat -> real) (m : nat) (n : nat) : (term326 i f m n) = (term327 i f m n).
Proof. exact (@lem7215409 (term325 i f m n) n). Qed.
Lemma lem7215411 (i : type1009) (f : nat -> real) (m : nat) (n : nat) : (term324 i f m n) = (term327 i f m n).
Proof. exact (TRANS (@lem7215406 i f m n) (@lem7215410 i f m n)). Qed.
Lemma lem7215412 (i : type1009) (f : nat -> real) (m : nat) (n : nat) : (term323 i f m n) = (term327 i f m n).
Proof. exact (TRANS (@lem7215400 i f m n) (@lem7215411 i f m n)). Qed.
Lemma lem7215423 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7215424 (f : type1009) (x : nat -> real) : (f x) = (@I ((nat -> real) -> nat -> nat -> nat) f x).
Proof. exact (@lem7215423 (nat -> real) type1606 f x). Qed.
Lemma lem7215425 (i : type1009) (f : nat -> real) : (i f) = (@I ((nat -> real) -> nat -> nat -> nat) i f).
Proof. exact (@lem7215424 i f). Qed.
Lemma lem7215426 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem7215427 (i : type1009) (f : nat -> real) (m : nat) : (i f m) = (@I ((nat -> real) -> nat -> nat -> nat) i f m).
Proof. exact (MK_COMB (@lem7215425 i f) (@lem7215426 m)). Qed.
Lemma lem7215429 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7215430 (f : type1606) (x : nat) : (f x) = (@I (nat -> nat -> nat) f x).
Proof. exact (@lem7215429 nat (nat -> nat) f x). Qed.
Lemma lem7215431 (i : type1009) (f : nat -> real) (m : nat) : (@I ((nat -> real) -> nat -> nat -> nat) i f m) = (term311 i f m).
Proof. exact (@lem7215430 (@I ((nat -> real) -> nat -> nat -> nat) i f) m). Qed.
Lemma lem7215432 (i : type1009) (f : nat -> real) (m : nat) : (i f m) = (term311 i f m).
Proof. exact (TRANS (@lem7215427 i f m) (@lem7215431 i f m)). Qed.
Lemma lem7215433 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7215434 (i : type1009) (f : nat -> real) (m : nat) (n : nat) : (i f m n) = (term312 i f m n).
Proof. exact (MK_COMB (@lem7215432 i f m) (@lem7215433 n)). Qed.
Lemma lem7215436 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7215437 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7215436 nat nat f x). Qed.
Lemma lem7215438 (i : type1009) (f : nat -> real) (m : nat) (n : nat) : (term312 i f m n) = (term313 i f m n).
Proof. exact (@lem7215437 (term311 i f m) n). Qed.
Lemma lem7215440 (i : type1009) (f : nat -> real) (m : nat) (n : nat) : (i f m n) = (term313 i f m n).
Proof. exact (TRANS (@lem7215434 i f m n) (@lem7215438 i f m n)). Qed.
Lemma lem7215441 (m : nat) : (Peano.le m) = (Peano.le m).
Proof. exact (eq_refl (Peano.le m)). Qed.
Lemma lem7215442 (i : type1009) (f : nat -> real) (m : nat) (n : nat) : (term328 i f m n) = (term329 i f m n).
Proof. exact (MK_COMB (@lem7215441 m) (@lem7215440 i f m n)). Qed.
Lemma lem7215444 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7215445 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7215444 nat (nat -> Prop) f x). Qed.
Lemma lem7215446 (m : nat) : (Peano.le m) = (@I (nat -> nat -> Prop) Peano.le m).
Proof. exact (@lem7215445 Peano.le m). Qed.
Lemma lem7215447 (i : type1009) (f : nat -> real) (m : nat) (n : nat) : (term313 i f m n) = (term313 i f m n).
Proof. exact (eq_refl (term313 i f m n)). Qed.
Lemma lem7215448 (i : type1009) (f : nat -> real) (m : nat) (n : nat) : (term329 i f m n) = (term330 i f m n).
Proof. exact (MK_COMB (@lem7215446 m) (@lem7215447 i f m n)). Qed.
Lemma lem7215450 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7215451 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7215450 nat Prop f x). Qed.
Lemma lem7215452 (i : type1009) (f : nat -> real) (m : nat) (n : nat) : (term330 i f m n) = (term331 i f m n).
Proof. exact (@lem7215451 (@I (nat -> nat -> Prop) Peano.le m) (term313 i f m n)). Qed.
Lemma lem7215453 (i : type1009) (f : nat -> real) (m : nat) (n : nat) : (term329 i f m n) = (term331 i f m n).
Proof. exact (TRANS (@lem7215448 i f m n) (@lem7215452 i f m n)). Qed.
Lemma lem7215454 (i : type1009) (f : nat -> real) (m : nat) (n : nat) : (term328 i f m n) = (term331 i f m n).
Proof. exact (TRANS (@lem7215442 i f m n) (@lem7215453 i f m n)). Qed.
Lemma lem7215455 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7215456 (i : type1009) (f : nat -> real) (m : nat) (n : nat) : (term332 i f m n) = (term333 i f m n).
Proof. exact (MK_COMB (@lem7215455) (@lem7215454 i f m n)). Qed.
Lemma lem7215457 (i : type1009) (f : nat -> real) (m : nat) (n : nat) : (term334 i f m n) = (term335 i f m n).
Proof. exact (MK_COMB (@lem7215456 i f m n) (@lem7215412 i f m n)). Qed.
Lemma lem7215458 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7215459 (i : type1009) (f : nat -> real) (m : nat) (n : nat) : (term336 i f m n) = (term337 i f m n).
Proof. exact (MK_COMB (@lem7215458) (@lem7215457 i f m n)). Qed.
Lemma lem7215460 (i : type1009) (f : nat -> real) (m : nat) (n : nat) : (term338 i f m n) = (term339 i f m n).
Proof. exact (MK_COMB (@lem7215459 i f m n) (@lem7215370 i f m n)). Qed.
Lemma lem7215461 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7215462 (i : type1009) (f : nat -> real) (m : nat) (n : nat) : (term340 i f m n) = (term341 i f m n).
Proof. exact (MK_COMB (@lem7215461) (@lem7215460 i f m n)). Qed.
Lemma lem7215463 (i : type1009) (m : nat) (n : nat) (f : nat -> real) : (term342 i m n f) = (term343 i m n f).
Proof. exact (MK_COMB (@lem7215462 i f m n) (@lem7215317 m n f)). Qed.
Lemma lem7215464 (i : type1009) (m : nat) (f : nat -> real) : (term344 i m f) = (term345 i m f).
Proof. exact (fun_ext (fun n : nat => @lem7215463 i m n f)). Qed.
Lemma lem7215465 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7215466 (i : type1009) (m : nat) (f : nat -> real) : (term346 i m f) = (term347 i m f).
Proof. exact (MK_COMB (@lem7215465) (@lem7215464 i m f)). Qed.
Lemma lem7215467 (i : type1009) (f : nat -> real) : (term348 i f) = (term349 i f).
Proof. exact (fun_ext (fun m : nat => @lem7215466 i m f)). Qed.
Lemma lem7215468 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7215469 (i : type1009) (f : nat -> real) : (term261 i f) = (term350 i f).
Proof. exact (MK_COMB (@lem7215468) (@lem7215467 i f)). Qed.
Lemma lem7215470 (i : type1009) : (term263 i) = (term351 i).
Proof. exact (fun_ext (fun f : nat -> real => @lem7215469 i f)). Qed.
Lemma lem7215471 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7215472 (i : type1009) : (term265 i) = (term352 i).
Proof. exact (MK_COMB (@lem7215471) (@lem7215470 i)). Qed.
Lemma lem7215473 (i : type1009) (h1 : term265 i) : term352 i.
Proof. exact (EQ_MP (@lem7215472 i) (@lem7215098 i h1)). Qed.
Lemma lem7215474 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7215475 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7215476 : (@sum nat) = (@sum nat).
Proof. exact (eq_refl (@sum nat)). Qed.
Lemma lem7215483 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7215484 (f : type1601) (x : nat) : (f x) = (@I (nat -> nat -> nat -> Prop) f x).
Proof. exact (@lem7215483 nat type1605 f x). Qed.
Lemma lem7215485 (m : nat) : (dotdot m) = (@I (nat -> nat -> nat -> Prop) dotdot m).
Proof. exact (@lem7215484 dotdot m). Qed.
Lemma lem7215486 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7215487 (m : nat) (n : nat) : (dotdot m n) = (@I (nat -> nat -> nat -> Prop) dotdot m n).
Proof. exact (MK_COMB (@lem7215485 m) (@lem7215486 n)). Qed.
Lemma lem7215489 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7215490 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7215489 nat (nat -> Prop) f x). Qed.
Lemma lem7215491 (m : nat) (n : nat) : (@I (nat -> nat -> nat -> Prop) dotdot m n) = (term300 m n).
Proof. exact (@lem7215490 (@I (nat -> nat -> nat -> Prop) dotdot m) n). Qed.
Lemma lem7215493 (m : nat) (n : nat) : (dotdot m n) = (term300 m n).
Proof. exact (TRANS (@lem7215487 m n) (@lem7215491 m n)). Qed.
Lemma lem7215494 (f : nat -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7215495 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (MK_COMB (@lem7215476) (@lem7215493 m n)). Qed.
Lemma lem7215496 (m : nat) (n : nat) (f : nat -> real) : (term26 m n f) = (term303 m n f).
Proof. exact (MK_COMB (@lem7215495 m n) (@lem7215494 f)). Qed.
Lemma lem7215498 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7215499 (f : type988) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> (nat -> real) -> real) f x).
Proof. exact (@lem7215498 (nat -> Prop) type1011 f x). Qed.
Lemma lem7215500 (m : nat) (n : nat) : (term302 m n) = (term304 m n).
Proof. exact (@lem7215499 (@sum nat) (term300 m n)). Qed.
Lemma lem7215501 (f : nat -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7215502 (m : nat) (n : nat) (f : nat -> real) : (term303 m n f) = (term305 m n f).
Proof. exact (MK_COMB (@lem7215500 m n) (@lem7215501 f)). Qed.
Lemma lem7215504 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7215505 (f : type1011) (x : nat -> real) : (f x) = (@I ((nat -> real) -> real) f x).
Proof. exact (@lem7215504 (nat -> real) real f x). Qed.
Lemma lem7215506 (m : nat) (n : nat) (f : nat -> real) : (term305 m n f) = (term306 m n f).
Proof. exact (@lem7215505 (term304 m n) f). Qed.
Lemma lem7215507 (m : nat) (n : nat) (f : nat -> real) : (term303 m n f) = (term306 m n f).
Proof. exact (TRANS (@lem7215502 m n f) (@lem7215506 m n f)). Qed.
Lemma lem7215508 (m : nat) (n : nat) (f : nat -> real) : (term26 m n f) = (term306 m n f).
Proof. exact (TRANS (@lem7215496 m n f) (@lem7215507 m n f)). Qed.
Lemma lem7215509 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7215514 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7215515 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7215514 nat nat f x). Qed.
Lemma lem7215517 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem7215515 NUMERAL 0). Qed.
Lemma lem7215518 : term27 = term307.
Proof. exact (MK_COMB (@lem7215509) (@lem7215517)). Qed.
Lemma lem7215520 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7215521 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7215520 nat real f x). Qed.
Lemma lem7215522 : term307 = term308.
Proof. exact (@lem7215521 real_of_num (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem7215523 : term27 = term308.
Proof. exact (TRANS (@lem7215518) (@lem7215522)). Qed.
Lemma lem7215524 (m : nat) (n : nat) (f : nat -> real) : (term309 m n f) = (term310 m n f).
Proof. exact (MK_COMB (@lem7215475) (@lem7215508 m n f)). Qed.
Lemma lem7215525 (m : nat) (n : nat) (f : nat -> real) : ((term26 m n f) = term27) = ((term306 m n f) = term308).
Proof. exact (MK_COMB (@lem7215524 m n f) (@lem7215523)). Qed.
Lemma lem7215526 (m : nat) (n : nat) (f : nat -> real) : (term353 m n f) = (term354 m n f).
Proof. exact (MK_COMB (@lem7215474) (@lem7215525 m n f)). Qed.
Lemma lem7215533 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7215534 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7215533 nat (nat -> Prop) f x). Qed.
Lemma lem7215535 (n : nat) : (Peano.lt n) = (@I (nat -> nat -> Prop) Peano.lt n).
Proof. exact (@lem7215534 Peano.lt n). Qed.
Lemma lem7215536 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem7215537 (n : nat) (m : nat) : (Peano.lt n m) = (@I (nat -> nat -> Prop) Peano.lt n m).
Proof. exact (MK_COMB (@lem7215535 n) (@lem7215536 m)). Qed.
Lemma lem7215539 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7215540 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7215539 nat Prop f x). Qed.
Lemma lem7215541 (n : nat) (m : nat) : (@I (nat -> nat -> Prop) Peano.lt n m) = (term270 n m).
Proof. exact (@lem7215540 (@I (nat -> nat -> Prop) Peano.lt n) m). Qed.
Lemma lem7215543 (n : nat) (m : nat) : (Peano.lt n m) = (term270 n m).
Proof. exact (TRANS (@lem7215537 n m) (@lem7215541 n m)). Qed.
Lemma lem7215544 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7215545 (n : nat) (m : nat) : (term355 n m) = (term356 n m).
Proof. exact (MK_COMB (@lem7215544) (@lem7215543 n m)). Qed.
Lemma lem7215546 (m : nat) (n : nat) (f : nat -> real) : (term57 m n f) = (term357 m n f).
Proof. exact (MK_COMB (@lem7215545 n m) (@lem7215526 m n f)). Qed.
Lemma lem7215547 (m : nat) (n : nat) (f : nat -> real) (h1 : term57 m n f) : term357 m n f.
Proof. exact (EQ_MP (@lem7215546 m n f) (@lem7215101 m n f h1)). Qed.
Lemma lem7215551 (h1 : term49) : term286.
Proof. exact (proj1 (@lem7215195 h1)). Qed.
Lemma lem7215565 (n : nat) (m : nat) (p : nat) : (term293 n m p) = (term293 n m p).
Proof. exact (eq_refl (term293 n m p)). Qed.
Lemma lem7215566 (n : nat) (m : nat) : (term294 n m) = (term294 n m).
Proof. exact (fun_ext (fun p : nat => @lem7215565 n m p)). Qed.
Lemma lem7215567 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7215568 (n : nat) (m : nat) : (term295 n m) = (term295 n m).
Proof. exact (MK_COMB (@lem7215567) (@lem7215566 n m)). Qed.
Lemma lem7215569 (m : nat) : (term296 m) = (term296 m).
Proof. exact (fun_ext (fun n : nat => @lem7215568 n m)). Qed.
Lemma lem7215570 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7215571 (m : nat) : (term297 m) = (term297 m).
Proof. exact (MK_COMB (@lem7215570) (@lem7215569 m)). Qed.
Lemma lem7215572 : term298 = term298.
Proof. exact (fun_ext (fun m : nat => @lem7215571 m)). Qed.
Lemma lem7215573 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7215575 : term299 = term299.
Proof. exact (MK_COMB (@lem7215573) (@lem7215572)). Qed.
Lemma lem7215576 (h1 : term44) : term299.
Proof. exact (EQ_MP (@lem7215575) (@lem7215266 h1)). Qed.
Lemma lem7215591 (i : type1009) (m : nat) (n : nat) (f : nat -> real) : (term343 i m n f) = (term358 i m n f).
Proof. exact (@lem19699 (term335 i f m n) (term320 i f m n) ((term306 m n f) = term308)). Qed.
Lemma lem7215592 (i : type1009) (m : nat) (n : nat) (f : nat -> real) : (term359 i m n f) = (term359 i m n f).
Proof. exact (eq_refl (term359 i m n f)). Qed.
Lemma lem7215599 (i : type1009) (m : nat) (n : nat) (f : nat -> real) : (term360 i m n f) = (term361 i m n f).
Proof. exact (@lem19699 (term331 i f m n) (term327 i f m n) ((term306 m n f) = term308)). Qed.
Lemma lem7215600 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7215601 (i : type1009) (m : nat) (n : nat) (f : nat -> real) : (term362 i m n f) = (term363 i m n f).
Proof. exact (MK_COMB (@lem7215600) (@lem7215599 i m n f)). Qed.
Lemma lem7215602 (i : type1009) (m : nat) (n : nat) (f : nat -> real) : (term358 i m n f) = (term364 i m n f).
Proof. exact (MK_COMB (@lem7215601 i m n f) (@lem7215592 i m n f)). Qed.
Lemma lem7215604 (i : type1009) (m : nat) (n : nat) (f : nat -> real) : (term343 i m n f) = (term364 i m n f).
Proof. exact (TRANS (@lem7215591 i m n f) (@lem7215602 i m n f)). Qed.
Lemma lem7215605 (i : type1009) (m : nat) (f : nat -> real) : (term345 i m f) = (term365 i m f).
Proof. exact (fun_ext (fun n : nat => @lem7215604 i m n f)). Qed.
Lemma lem7215606 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7215607 (i : type1009) (m : nat) (f : nat -> real) : (term347 i m f) = (term366 i m f).
Proof. exact (MK_COMB (@lem7215606) (@lem7215605 i m f)). Qed.
Lemma lem7215608 (i : type1009) (f : nat -> real) : (term349 i f) = (term367 i f).
Proof. exact (fun_ext (fun m : nat => @lem7215607 i m f)). Qed.
Lemma lem7215609 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7215610 (i : type1009) (f : nat -> real) : (term350 i f) = (term368 i f).
Proof. exact (MK_COMB (@lem7215609) (@lem7215608 i f)). Qed.
Lemma lem7215611 (i : type1009) : (term351 i) = (term369 i).
Proof. exact (fun_ext (fun f : nat -> real => @lem7215610 i f)). Qed.
Lemma lem7215612 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7215614 (i : type1009) : (term352 i) = (term370 i).
Proof. exact (MK_COMB (@lem7215612) (@lem7215611 i)). Qed.
Lemma lem7215615 (i : type1009) (h1 : term265 i) : term370 i.
Proof. exact (EQ_MP (@lem7215614 i) (@lem7215473 i h1)). Qed.
Lemma lem7215631 (n : nat) (m : nat) : (term282 n m) = (term282 n m).
Proof. exact (eq_refl (term282 n m)). Qed.
Lemma lem7215632 (m : nat) : (term283 m) = (term283 m).
Proof. exact (fun_ext (fun n : nat => @lem7215631 n m)). Qed.
Lemma lem7215633 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7215634 (m : nat) : (term284 m) = (term284 m).
Proof. exact (MK_COMB (@lem7215633) (@lem7215632 m)). Qed.
Lemma lem7215635 : term285 = term285.
Proof. exact (fun_ext (fun m : nat => @lem7215634 m)). Qed.
Lemma lem7215636 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7215638 : term286 = term286.
Proof. exact (MK_COMB (@lem7215636) (@lem7215635)). Qed.
Lemma lem7215639 (h1 : term49) : term286.
Proof. exact (EQ_MP (@lem7215638) (@lem7215551 h1)). Qed.
Lemma lem7215656 (_96696 : nat) (h1 : term44) : term371 _96696.
Proof. exact (@lem7215576 h1 _96696). Qed.
Lemma lem7215657 (_96696 : nat) : (term371 _96696) = (term297 _96696).
Proof. exact (eq_refl (term371 _96696)). Qed.
Lemma lem7215658 (_96696 : nat) (h1 : term44) : term297 _96696.
Proof. exact (EQ_MP (@lem7215657 _96696) (@lem7215656 _96696 h1)). Qed.
Lemma lem7215659 (_96696 : nat) (_96697 : nat) (h1 : term44) : term372 _96696 _96697.
Proof. exact (@lem7215658 _96696 h1 _96697). Qed.
Lemma lem7215660 (_96697 : nat) (_96696 : nat) : (term372 _96696 _96697) = (term295 _96697 _96696).
Proof. exact (eq_refl (term372 _96696 _96697)). Qed.
Lemma lem7215661 (_96697 : nat) (_96696 : nat) (h1 : term44) : term295 _96697 _96696.
Proof. exact (EQ_MP (@lem7215660 _96697 _96696) (@lem7215659 _96696 _96697 h1)). Qed.
Lemma lem7215662 (_96697 : nat) (_96696 : nat) (_96698 : nat) (h1 : term44) : term373 _96697 _96696 _96698.
Proof. exact (@lem7215661 _96697 _96696 h1 _96698). Qed.
Lemma lem7215663 (_96697 : nat) (_96696 : nat) (_96698 : nat) : (term373 _96697 _96696 _96698) = (term293 _96697 _96696 _96698).
Proof. exact (eq_refl (term373 _96697 _96696 _96698)). Qed.
Lemma lem7215664 (_96697 : nat) (_96696 : nat) (_96698 : nat) (h1 : term44) : term293 _96697 _96696 _96698.
Proof. exact (EQ_MP (@lem7215663 _96697 _96696 _96698) (@lem7215662 _96697 _96696 _96698 h1)). Qed.
Lemma lem7215665 (_96699 : nat -> real) (i : type1009) (h1 : term265 i) : term374 i _96699.
Proof. exact (@lem7215615 i h1 _96699). Qed.
Lemma lem7215666 (i : type1009) (_96699 : nat -> real) : (term374 i _96699) = (term368 i _96699).
Proof. exact (eq_refl (term374 i _96699)). Qed.
Lemma lem7215667 (_96699 : nat -> real) (i : type1009) (h1 : term265 i) : term368 i _96699.
Proof. exact (EQ_MP (@lem7215666 i _96699) (@lem7215665 _96699 i h1)). Qed.
Lemma lem7215668 (_96699 : nat -> real) (_96700 : nat) (i : type1009) (h1 : term265 i) : term375 i _96699 _96700.
Proof. exact (@lem7215667 _96699 i h1 _96700). Qed.
Lemma lem7215669 (i : type1009) (_96700 : nat) (_96699 : nat -> real) : (term375 i _96699 _96700) = (term366 i _96700 _96699).
Proof. exact (eq_refl (term375 i _96699 _96700)). Qed.
Lemma lem7215670 (_96700 : nat) (_96699 : nat -> real) (i : type1009) (h1 : term265 i) : term366 i _96700 _96699.
Proof. exact (EQ_MP (@lem7215669 i _96700 _96699) (@lem7215668 _96699 _96700 i h1)). Qed.
Lemma lem7215671 (_96700 : nat) (_96699 : nat -> real) (_96701 : nat) (i : type1009) (h1 : term265 i) : term376 i _96700 _96699 _96701.
Proof. exact (@lem7215670 _96700 _96699 i h1 _96701). Qed.
Lemma lem7215672 (i : type1009) (_96700 : nat) (_96701 : nat) (_96699 : nat -> real) : (term376 i _96700 _96699 _96701) = (term364 i _96700 _96701 _96699).
Proof. exact (eq_refl (term376 i _96700 _96699 _96701)). Qed.
Lemma lem7215673 (_96700 : nat) (_96701 : nat) (_96699 : nat -> real) (i : type1009) (h1 : term265 i) : term364 i _96700 _96701 _96699.
Proof. exact (EQ_MP (@lem7215672 i _96700 _96701 _96699) (@lem7215671 _96700 _96699 _96701 i h1)). Qed.
Lemma lem7215674 (_96702 : nat) (h1 : term49) : term377 _96702.
Proof. exact (@lem7215639 h1 _96702). Qed.
Lemma lem7215675 (_96702 : nat) : (term377 _96702) = (term284 _96702).
Proof. exact (eq_refl (term377 _96702)). Qed.
Lemma lem7215676 (_96702 : nat) (h1 : term49) : term284 _96702.
Proof. exact (EQ_MP (@lem7215675 _96702) (@lem7215674 _96702 h1)). Qed.
Lemma lem7215677 (_96702 : nat) (_96703 : nat) (h1 : term49) : term378 _96702 _96703.
Proof. exact (@lem7215676 _96702 h1 _96703). Qed.
Lemma lem7215678 (_96703 : nat) (_96702 : nat) : (term378 _96702 _96703) = (term282 _96703 _96702).
Proof. exact (eq_refl (term378 _96702 _96703)). Qed.
Lemma lem7215687 (_96700 : nat) (_96701 : nat) (_96699 : nat -> real) (i : type1009) (h1 : term265 i) : term361 i _96700 _96701 _96699.
Proof. exact (proj1 (@lem7215673 _96700 _96701 _96699 i h1)). Qed.
Lemma lem7215700 (_96697 : nat) (_96696 : nat) (_96698 : nat) : (term293 _96697 _96696 _96698) = (term379 _96697 _96696 _96698).
Proof. exact (@lem7214071 (term278 _96696 _96697) (term278 _96697 _96698) (term269 _96696 _96698)). Qed.
Lemma lem7215701 (_96697 : nat) (_96696 : nat) (_96698 : nat) (h1 : term44) : term379 _96697 _96696 _96698.
Proof. exact (EQ_MP (@lem7215700 _96697 _96696 _96698) (@lem7215664 _96697 _96696 _96698 h1)). Qed.
Lemma lem7215705 (m : nat) (n : nat) (f : nat -> real) (h1 : term57 m n f) : term354 m n f.
Proof. exact (proj2 (@lem7215547 m n f h1)). Qed.
Lemma lem7215711 (_96703 : nat) (_96702 : nat) (h1 : term49) : term282 _96703 _96702.
Proof. exact (EQ_MP (@lem7215678 _96703 _96702) (@lem7215677 _96702 _96703 h1)). Qed.
Lemma lem7215729 (_96700 : nat) (_96701 : nat) (_96699 : nat -> real) (i : type1009) (h1 : term265 i) : term380 i _96700 _96701 _96699.
Proof. exact (proj1 (@lem7215687 _96700 _96701 _96699 i h1)). Qed.
Lemma lem7215735 (_96700 : nat) (_96701 : nat) (_96699 : nat -> real) (i : type1009) (h1 : term265 i) : term381 i _96700 _96701 _96699.
Proof. exact (proj2 (@lem7215687 _96700 _96701 _96699 i h1)). Qed.
Lemma lem7215899 (m : nat) (n : nat) (f : nat -> real) (h1 : term354 m n f) : term354 m n f.
Proof. exact (h1). Qed.
Lemma lem7215900 (m : nat) (n : nat) (f : nat -> real) (h1 : term354 m n f) : term382 m n f.
Proof. exact (fun h0 : (term306 m n f) = term308 => @lem7215899 m n f h1). Qed.
Lemma lem7215902 (p : Prop) : (term383 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7215903 (m : nat) (n : nat) (f : nat -> real) : (term382 m n f) = (term354 m n f).
Proof. exact (@lem7215902 ((term306 m n f) = term308)). Qed.
Lemma lem7215904 (m : nat) (n : nat) (f : nat -> real) (h1 : term354 m n f) : term354 m n f.
Proof. exact (EQ_MP (@lem7215903 m n f) (@lem7215900 m n f h1)). Qed.
Lemma lem7215906 (b : Prop) (a : Prop) : (a \/ b) = (term384 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7215909 (i : type1009) (_96699 : nat -> real) (_96700 : nat) (_96701 : nat) : (term380 i _96700 _96701 _96699) = (term385 i _96699 _96700 _96701).
Proof. exact (@lem7215906 ((term306 _96700 _96701 _96699) = term308) (term331 i _96699 _96700 _96701)). Qed.
Lemma lem7215912 (_96699 : nat -> real) (_96700 : nat) (_96701 : nat) (i : type1009) (h1 : term265 i) : term385 i _96699 _96700 _96701.
Proof. exact (EQ_MP (@lem7215909 i _96699 _96700 _96701) (@lem7215729 _96700 _96701 _96699 i h1)). Qed.
Lemma lem7215913 (f : nat -> real) (m : nat) (n : nat) (i : type1009) (h1 : term265 i) : term385 i f m n.
Proof. exact (@lem7215912 f m n i h1). Qed.
Lemma lem7215916 (i : type1009) (m : nat) (n : nat) (f : nat -> real) (h1 : term265 i) (h2 : term354 m n f) : term331 i f m n.
Proof. exact (@lem7215913 f m n i h1 (@lem7215904 m n f h2)). Qed.
Lemma lem7215917 (i : type1009) (m : nat) (n : nat) (f : nat -> real) (h1 : term265 i) (h2 : term354 m n f) : term386 i f m n.
Proof. exact (fun h0 : term387 i f m n => @lem7215916 i m n f h1 h2). Qed.
Lemma lem7215919 (p : Prop) : (term388 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7215920 (i : type1009) (f : nat -> real) (m : nat) (n : nat) : (term386 i f m n) = (term331 i f m n).
Proof. exact (@lem7215919 (term331 i f m n)). Qed.
Lemma lem7215921 (i : type1009) (m : nat) (n : nat) (f : nat -> real) (h1 : term265 i) (h2 : term354 m n f) : term331 i f m n.
Proof. exact (EQ_MP (@lem7215920 i f m n) (@lem7215917 i m n f h1 h2)). Qed.
Lemma lem7215923 (m : nat) (n : nat) (f : nat -> real) (h1 : term57 m n f) : term270 n m.
Proof. exact (proj1 (@lem7215547 m n f h1)). Qed.
Lemma lem7215924 (m : nat) (n : nat) (f : nat -> real) (h1 : term57 m n f) : term389 n m.
Proof. exact (fun h0 : term279 n m => @lem7215923 m n f h1). Qed.
Lemma lem7215926 (p : Prop) : (term388 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7215927 (n : nat) (m : nat) : (term389 n m) = (term270 n m).
Proof. exact (@lem7215926 (term270 n m)). Qed.
Lemma lem7215928 (m : nat) (n : nat) (f : nat -> real) (h1 : term57 m n f) : term270 n m.
Proof. exact (EQ_MP (@lem7215927 n m) (@lem7215924 m n f h1)). Qed.
Lemma lem7215939 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7215940 (_96703 : nat) (_96702 : nat) : (term390 _96702 _96703) = (term282 _96703 _96702).
Proof. exact (@lem7215939 (term279 _96702 _96703) (term278 _96703 _96702)). Qed.
Lemma lem7215946 (_96703 : nat) (_96702 : nat) : (term391 _96703 _96702) = (term391 _96703 _96702).
Proof. exact (eq_refl (term391 _96703 _96702)). Qed.
Lemma lem7215947 (_96703 : nat) (_96702 : nat) : ((term282 _96703 _96702) = (term390 _96702 _96703)) = ((term282 _96703 _96702) = (term282 _96703 _96702)).
Proof. exact (MK_COMB (@lem7215946 _96703 _96702) (@lem7215940 _96703 _96702)). Qed.
Lemma lem7215949 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7215950 (x : Prop) : (x = x) = True.
Proof. exact (@lem7215949 Prop x). Qed.
Lemma lem7215951 (_96703 : nat) (_96702 : nat) : ((term282 _96703 _96702) = (term282 _96703 _96702)) = True.
Proof. exact (@lem7215950 (term282 _96703 _96702)). Qed.
Lemma lem7215952 (_96702 : nat) (_96703 : nat) : ((term282 _96703 _96702) = (term390 _96702 _96703)) = True.
Proof. exact (TRANS (@lem7215947 _96703 _96702) (@lem7215951 _96703 _96702)). Qed.
Lemma lem7215953 (_96702 : nat) (_96703 : nat) : True = ((term282 _96703 _96702) = (term390 _96702 _96703)).
Proof. exact (SYM (@lem7215952 _96702 _96703)). Qed.
Lemma lem7215954 (_96702 : nat) (_96703 : nat) : (term282 _96703 _96702) = (term390 _96702 _96703).
Proof. exact (EQ_MP (@lem7215953 _96702 _96703) (@lem0)). Qed.
Lemma lem7215955 (_96702 : nat) (_96703 : nat) (h1 : term49) : term390 _96702 _96703.
Proof. exact (EQ_MP (@lem7215954 _96702 _96703) (@lem7215711 _96703 _96702 h1)). Qed.
Lemma lem7215957 (b : Prop) (a : Prop) : (a \/ b) = (term384 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7215958 (_96703 : nat) (_96702 : nat) : (term390 _96702 _96703) = (term392 _96703 _96702).
Proof. exact (@lem7215957 (term279 _96702 _96703) (term278 _96703 _96702)). Qed.
Lemma lem7215960 (a : Prop) : (term393 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7215961 (_96702 : nat) (_96703 : nat) : (term394 _96702 _96703) = (term270 _96702 _96703).
Proof. exact (@lem7215960 (term270 _96702 _96703)). Qed.
Lemma lem7215962 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7215963 (_96702 : nat) (_96703 : nat) : (term395 _96702 _96703) = (term396 _96702 _96703).
Proof. exact (MK_COMB (@lem7215962) (@lem7215961 _96702 _96703)). Qed.
Lemma lem7215964 (_96703 : nat) (_96702 : nat) : (term278 _96703 _96702) = (term278 _96703 _96702).
Proof. exact (eq_refl (term278 _96703 _96702)). Qed.
Lemma lem7215965 (_96703 : nat) (_96702 : nat) : (term392 _96703 _96702) = (term397 _96703 _96702).
Proof. exact (MK_COMB (@lem7215963 _96702 _96703) (@lem7215964 _96703 _96702)). Qed.
Lemma lem7215966 (_96703 : nat) (_96702 : nat) : (term390 _96702 _96703) = (term397 _96703 _96702).
Proof. exact (TRANS (@lem7215958 _96703 _96702) (@lem7215965 _96703 _96702)). Qed.
Lemma lem7215969 (_96703 : nat) (_96702 : nat) (h1 : term49) : term397 _96703 _96702.
Proof. exact (EQ_MP (@lem7215966 _96703 _96702) (@lem7215955 _96702 _96703 h1)). Qed.
Lemma lem7215970 (m : nat) (n : nat) (h1 : term49) : term397 m n.
Proof. exact (@lem7215969 m n h1). Qed.
Lemma lem7215973 (m : nat) (n : nat) (f : nat -> real) (h1 : term49) (h2 : term57 m n f) : term278 m n.
Proof. exact (@lem7215970 m n h1 (@lem7215928 m n f h2)). Qed.
Lemma lem7215974 (m : nat) (n : nat) (f : nat -> real) (h1 : term49) (h2 : term57 m n f) : term398 m n.
Proof. exact (fun h0 : term269 m n => @lem7215973 m n f h1 h2). Qed.
Lemma lem7215976 (p : Prop) : (term383 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7215977 (m : nat) (n : nat) : (term398 m n) = (term278 m n).
Proof. exact (@lem7215976 (term269 m n)). Qed.
Lemma lem7215978 (m : nat) (n : nat) (f : nat -> real) (h1 : term49) (h2 : term57 m n f) : term278 m n.
Proof. exact (EQ_MP (@lem7215977 m n) (@lem7215974 m n f h1 h2)). Qed.
Lemma lem7215994 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7215995 (_96696 : nat) (_96697 : nat) (_96698 : nat) : (term399 _96697 _96696 _96698) = (term400 _96696 _96697 _96698).
Proof. exact (@lem7215994 (term269 _96696 _96698) (term278 _96697 _96698)). Qed.
Lemma lem7216001 (_96696 : nat) (_96697 : nat) : (term290 _96696 _96697) = (term290 _96696 _96697).
Proof. exact (eq_refl (term290 _96696 _96697)). Qed.
Lemma lem7216002 (_96696 : nat) (_96697 : nat) (_96698 : nat) : (term379 _96697 _96696 _96698) = (term401 _96696 _96697 _96698).
Proof. exact (MK_COMB (@lem7216001 _96696 _96697) (@lem7215995 _96696 _96697 _96698)). Qed.
Lemma lem7216006 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7216007 (_96696 : nat) (_96697 : nat) (_96698 : nat) : (term401 _96696 _96697 _96698) = (term402 _96696 _96697 _96698).
Proof. exact (@lem7216006 (term269 _96696 _96698) (term278 _96696 _96697) (term278 _96697 _96698)). Qed.
Lemma lem7216023 (_96696 : nat) (_96697 : nat) (_96698 : nat) : (term379 _96697 _96696 _96698) = (term402 _96696 _96697 _96698).
Proof. exact (TRANS (@lem7216002 _96696 _96697 _96698) (@lem7216007 _96696 _96697 _96698)). Qed.
Lemma lem7216024 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7216025 (_96696 : nat) (_96697 : nat) (_96698 : nat) : (term403 _96697 _96696 _96698) = (term404 _96696 _96697 _96698).
Proof. exact (MK_COMB (@lem7216024) (@lem7216023 _96696 _96697 _96698)). Qed.
Lemma lem7216029 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7216030 (_96697 : nat) (_96696 : nat) (_96698 : nat) : (term405 _96697 _96696 _96698) = (term379 _96697 _96696 _96698).
Proof. exact (@lem7216029 (term278 _96696 _96697) (term278 _96697 _96698) (term269 _96696 _96698)). Qed.
Lemma lem7216044 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7216045 (_96696 : nat) (_96697 : nat) (_96698 : nat) : (term399 _96697 _96696 _96698) = (term400 _96696 _96697 _96698).
Proof. exact (@lem7216044 (term269 _96696 _96698) (term278 _96697 _96698)). Qed.
Lemma lem7216051 (_96696 : nat) (_96697 : nat) : (term290 _96696 _96697) = (term290 _96696 _96697).
Proof. exact (eq_refl (term290 _96696 _96697)). Qed.
Lemma lem7216052 (_96696 : nat) (_96697 : nat) (_96698 : nat) : (term379 _96697 _96696 _96698) = (term401 _96696 _96697 _96698).
Proof. exact (MK_COMB (@lem7216051 _96696 _96697) (@lem7216045 _96696 _96697 _96698)). Qed.
Lemma lem7216056 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7216057 (_96696 : nat) (_96697 : nat) (_96698 : nat) : (term401 _96696 _96697 _96698) = (term402 _96696 _96697 _96698).
Proof. exact (@lem7216056 (term269 _96696 _96698) (term278 _96696 _96697) (term278 _96697 _96698)). Qed.
Lemma lem7216073 (_96696 : nat) (_96697 : nat) (_96698 : nat) : (term379 _96697 _96696 _96698) = (term402 _96696 _96697 _96698).
Proof. exact (TRANS (@lem7216052 _96696 _96697 _96698) (@lem7216057 _96696 _96697 _96698)). Qed.
Lemma lem7216074 (_96696 : nat) (_96697 : nat) (_96698 : nat) : (term405 _96697 _96696 _96698) = (term402 _96696 _96697 _96698).
Proof. exact (TRANS (@lem7216030 _96697 _96696 _96698) (@lem7216073 _96696 _96697 _96698)). Qed.
Lemma lem7216075 (_96696 : nat) (_96697 : nat) (_96698 : nat) : ((term379 _96697 _96696 _96698) = (term405 _96697 _96696 _96698)) = ((term402 _96696 _96697 _96698) = (term402 _96696 _96697 _96698)).
Proof. exact (MK_COMB (@lem7216025 _96696 _96697 _96698) (@lem7216074 _96696 _96697 _96698)). Qed.
Lemma lem7216077 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7216078 (x : Prop) : (x = x) = True.
Proof. exact (@lem7216077 Prop x). Qed.
Lemma lem7216079 (_96696 : nat) (_96697 : nat) (_96698 : nat) : ((term402 _96696 _96697 _96698) = (term402 _96696 _96697 _96698)) = True.
Proof. exact (@lem7216078 (term402 _96696 _96697 _96698)). Qed.
Lemma lem7216080 (_96697 : nat) (_96696 : nat) (_96698 : nat) : ((term379 _96697 _96696 _96698) = (term405 _96697 _96696 _96698)) = True.
Proof. exact (TRANS (@lem7216075 _96696 _96697 _96698) (@lem7216079 _96696 _96697 _96698)). Qed.
Lemma lem7216081 (_96697 : nat) (_96696 : nat) (_96698 : nat) : True = ((term379 _96697 _96696 _96698) = (term405 _96697 _96696 _96698)).
Proof. exact (SYM (@lem7216080 _96697 _96696 _96698)). Qed.
Lemma lem7216082 (_96697 : nat) (_96696 : nat) (_96698 : nat) : (term379 _96697 _96696 _96698) = (term405 _96697 _96696 _96698).
Proof. exact (EQ_MP (@lem7216081 _96697 _96696 _96698) (@lem0)). Qed.
Lemma lem7216083 (_96697 : nat) (_96696 : nat) (_96698 : nat) (h1 : term44) : term405 _96697 _96696 _96698.
Proof. exact (EQ_MP (@lem7216082 _96697 _96696 _96698) (@lem7215701 _96697 _96696 _96698 h1)). Qed.
Lemma lem7216085 (b : Prop) (a : Prop) : (a \/ b) = (term384 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7216086 (_96696 : nat) (_96697 : nat) (_96698 : nat) : (term405 _96697 _96696 _96698) = (term406 _96696 _96697 _96698).
Proof. exact (@lem7216085 (term407 _96697 _96696 _96698) (term278 _96697 _96698)). Qed.
Lemma lem7216088 (a : Prop) (b : Prop) : (term408 a b) = (term409 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7216089 (_96697 : nat) (_96696 : nat) (_96698 : nat) : (term410 _96697 _96696 _96698) = (term411 _96697 _96696 _96698).
Proof. exact (@lem7216088 (term278 _96696 _96697) (term269 _96696 _96698)). Qed.
Lemma lem7216091 (a : Prop) : (term393 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7216092 (_96696 : nat) (_96697 : nat) : (term412 _96696 _96697) = (term269 _96696 _96697).
Proof. exact (@lem7216091 (term269 _96696 _96697)). Qed.
Lemma lem7216093 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7216094 (_96696 : nat) (_96697 : nat) : (term413 _96696 _96697) = (term414 _96696 _96697).
Proof. exact (MK_COMB (@lem7216093) (@lem7216092 _96696 _96697)). Qed.
Lemma lem7216095 (_96696 : nat) (_96698 : nat) : (term278 _96696 _96698) = (term278 _96696 _96698).
Proof. exact (eq_refl (term278 _96696 _96698)). Qed.
Lemma lem7216096 (_96697 : nat) (_96696 : nat) (_96698 : nat) : (term411 _96697 _96696 _96698) = (term415 _96697 _96696 _96698).
Proof. exact (MK_COMB (@lem7216094 _96696 _96697) (@lem7216095 _96696 _96698)). Qed.
Lemma lem7216097 (_96697 : nat) (_96696 : nat) (_96698 : nat) : (term410 _96697 _96696 _96698) = (term415 _96697 _96696 _96698).
Proof. exact (TRANS (@lem7216089 _96697 _96696 _96698) (@lem7216096 _96697 _96696 _96698)). Qed.
Lemma lem7216098 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7216099 (_96697 : nat) (_96696 : nat) (_96698 : nat) : (term416 _96697 _96696 _96698) = (term417 _96697 _96696 _96698).
Proof. exact (MK_COMB (@lem7216098) (@lem7216097 _96697 _96696 _96698)). Qed.
Lemma lem7216100 (_96697 : nat) (_96698 : nat) : (term278 _96697 _96698) = (term278 _96697 _96698).
Proof. exact (eq_refl (term278 _96697 _96698)). Qed.
Lemma lem7216101 (_96696 : nat) (_96697 : nat) (_96698 : nat) : (term406 _96696 _96697 _96698) = (term418 _96696 _96697 _96698).
Proof. exact (MK_COMB (@lem7216099 _96697 _96696 _96698) (@lem7216100 _96697 _96698)). Qed.
Lemma lem7216102 (_96696 : nat) (_96697 : nat) (_96698 : nat) : (term405 _96697 _96696 _96698) = (term418 _96696 _96697 _96698).
Proof. exact (TRANS (@lem7216086 _96696 _96697 _96698) (@lem7216101 _96696 _96697 _96698)). Qed.
Lemma lem7216104 (i : type1009) (m : nat) (n : nat) (f : nat -> real) (h1 : term265 i) (h2 : term49) (h3 : term354 m n f) (h4 : term57 m n f) : term419 i f m n.
Proof. exact (conj (@lem7215921 i m n f h1 h3) (@lem7215978 m n f h2 h4)). Qed.
Lemma lem7216106 (_96696 : nat) (_96697 : nat) (_96698 : nat) (h1 : term44) : term418 _96696 _96697 _96698.
Proof. exact (EQ_MP (@lem7216102 _96696 _96697 _96698) (@lem7216083 _96697 _96696 _96698 h1)). Qed.
Lemma lem7216107 (i : type1009) (f : nat -> real) (m : nat) (n : nat) (h1 : term44) : term420 i f m n.
Proof. exact (@lem7216106 m (term313 i f m n) n h1). Qed.
Lemma lem7216110 (i : type1009) (m : nat) (n : nat) (f : nat -> real) (h1 : term265 i) (h2 : term44) (h3 : term49) (h4 : term354 m n f) (h5 : term57 m n f) : term421 i f m n.
Proof. exact (@lem7216107 i f m n h2 (@lem7216104 i m n f h1 h3 h4 h5)). Qed.
Lemma lem7216111 (i : type1009) (m : nat) (n : nat) (f : nat -> real) (h1 : term265 i) (h2 : term44) (h3 : term49) (h4 : term354 m n f) (h5 : term57 m n f) : term422 i f m n.
Proof. exact (fun h0 : term327 i f m n => @lem7216110 i m n f h1 h2 h3 h4 h5). Qed.
Lemma lem7216113 (p : Prop) : (term383 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7216114 (i : type1009) (f : nat -> real) (m : nat) (n : nat) : (term422 i f m n) = (term421 i f m n).
Proof. exact (@lem7216113 (term327 i f m n)). Qed.
Lemma lem7216115 (i : type1009) (m : nat) (n : nat) (f : nat -> real) (h1 : term265 i) (h2 : term44) (h3 : term49) (h4 : term354 m n f) (h5 : term57 m n f) : term421 i f m n.
Proof. exact (EQ_MP (@lem7216114 i f m n) (@lem7216111 i m n f h1 h2 h3 h4 h5)). Qed.
Lemma lem7216121 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7216122 (i : type1009) (_96699 : nat -> real) (_96700 : nat) (_96701 : nat) : (term381 i _96700 _96701 _96699) = (term423 i _96699 _96700 _96701).
Proof. exact (@lem7216121 ((term306 _96700 _96701 _96699) = term308) (term327 i _96699 _96700 _96701)). Qed.
Lemma lem7216130 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7216131 (i : type1009) (_96699 : nat -> real) (_96700 : nat) (_96701 : nat) : (term424 i _96700 _96701 _96699) = (term425 i _96699 _96700 _96701).
Proof. exact (MK_COMB (@lem7216130) (@lem7216122 i _96699 _96700 _96701)). Qed.
Lemma lem7216139 (i : type1009) (_96699 : nat -> real) (_96700 : nat) (_96701 : nat) : (term423 i _96699 _96700 _96701) = (term423 i _96699 _96700 _96701).
Proof. exact (eq_refl (term423 i _96699 _96700 _96701)). Qed.
Lemma lem7216140 (i : type1009) (_96699 : nat -> real) (_96700 : nat) (_96701 : nat) : ((term381 i _96700 _96701 _96699) = (term423 i _96699 _96700 _96701)) = ((term423 i _96699 _96700 _96701) = (term423 i _96699 _96700 _96701)).
Proof. exact (MK_COMB (@lem7216131 i _96699 _96700 _96701) (@lem7216139 i _96699 _96700 _96701)). Qed.
Lemma lem7216142 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7216143 (x : Prop) : (x = x) = True.
Proof. exact (@lem7216142 Prop x). Qed.
Lemma lem7216144 (i : type1009) (_96699 : nat -> real) (_96700 : nat) (_96701 : nat) : ((term423 i _96699 _96700 _96701) = (term423 i _96699 _96700 _96701)) = True.
Proof. exact (@lem7216143 (term423 i _96699 _96700 _96701)). Qed.
Lemma lem7216145 (i : type1009) (_96699 : nat -> real) (_96700 : nat) (_96701 : nat) : ((term381 i _96700 _96701 _96699) = (term423 i _96699 _96700 _96701)) = True.
Proof. exact (TRANS (@lem7216140 i _96699 _96700 _96701) (@lem7216144 i _96699 _96700 _96701)). Qed.
Lemma lem7216146 (i : type1009) (_96699 : nat -> real) (_96700 : nat) (_96701 : nat) : True = ((term381 i _96700 _96701 _96699) = (term423 i _96699 _96700 _96701)).
Proof. exact (SYM (@lem7216145 i _96699 _96700 _96701)). Qed.
Lemma lem7216147 (i : type1009) (_96699 : nat -> real) (_96700 : nat) (_96701 : nat) : (term381 i _96700 _96701 _96699) = (term423 i _96699 _96700 _96701).
Proof. exact (EQ_MP (@lem7216146 i _96699 _96700 _96701) (@lem0)). Qed.
Lemma lem7216148 (_96699 : nat -> real) (_96700 : nat) (_96701 : nat) (i : type1009) (h1 : term265 i) : term423 i _96699 _96700 _96701.
Proof. exact (EQ_MP (@lem7216147 i _96699 _96700 _96701) (@lem7215735 _96700 _96701 _96699 i h1)). Qed.
Lemma lem7216150 (b : Prop) (a : Prop) : (a \/ b) = (term384 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7216153 (i : type1009) (_96700 : nat) (_96701 : nat) (_96699 : nat -> real) : (term423 i _96699 _96700 _96701) = (term426 i _96700 _96701 _96699).
Proof. exact (@lem7216150 (term327 i _96699 _96700 _96701) ((term306 _96700 _96701 _96699) = term308)). Qed.
Lemma lem7216156 (_96700 : nat) (_96701 : nat) (_96699 : nat -> real) (i : type1009) (h1 : term265 i) : term426 i _96700 _96701 _96699.
Proof. exact (EQ_MP (@lem7216153 i _96700 _96701 _96699) (@lem7216148 _96699 _96700 _96701 i h1)). Qed.
Lemma lem7216157 (m : nat) (n : nat) (f : nat -> real) (i : type1009) (h1 : term265 i) : term426 i m n f.
Proof. exact (@lem7216156 m n f i h1). Qed.
Lemma lem7216160 (i : type1009) (m : nat) (n : nat) (f : nat -> real) (h1 : term265 i) (h2 : term44) (h3 : term49) (h4 : term354 m n f) (h5 : term57 m n f) : (term306 m n f) = term308.
Proof. exact (@lem7216157 m n f i h1 (@lem7216115 i m n f h1 h2 h3 h4 h5)). Qed.
Lemma lem7216161 (i : type1009) (m : nat) (n : nat) (f : nat -> real) (h1 : term265 i) (h2 : term44) (h3 : term49) (h4 : term57 m n f) : term427 m n f.
Proof. exact (fun h0 : term354 m n f => @lem7216160 i m n f h1 h2 h3 h0 h4). Qed.
Lemma lem7216163 (p : Prop) : (term388 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7216164 (m : nat) (n : nat) (f : nat -> real) : (term427 m n f) = ((term306 m n f) = term308).
Proof. exact (@lem7216163 ((term306 m n f) = term308)). Qed.
Lemma lem7216165 (i : type1009) (m : nat) (n : nat) (f : nat -> real) (h1 : term265 i) (h2 : term44) (h3 : term49) (h4 : term57 m n f) : (term306 m n f) = term308.
Proof. exact (EQ_MP (@lem7216164 m n f) (@lem7216161 i m n f h1 h2 h3 h4)). Qed.
Lemma lem7216168 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7216170 (m : nat) (n : nat) (f : nat -> real) : (term354 m n f) = (term428 m n f).
Proof. exact (@lem7216168 ((term306 m n f) = term308)). Qed.
Lemma lem7216173 (m : nat) (n : nat) (f : nat -> real) (h1 : term57 m n f) : term428 m n f.
Proof. exact (EQ_MP (@lem7216170 m n f) (@lem7215705 m n f h1)). Qed.
Lemma lem7216176 (i : type1009) (m : nat) (n : nat) (f : nat -> real) (h1 : term265 i) (h2 : term44) (h3 : term49) (h4 : term57 m n f) : False.
Proof. exact (@lem7216173 m n f h4 (@lem7216165 i m n f h1 h2 h3 h4)). Qed.
Lemma lem7216177 (i : type1009) (m : nat) (n : nat) (f : nat -> real) (h1 : term265 i) (h2 : term44) (h3 : term49) (h4 : term57 m n f) : term429.
Proof. exact (fun h0 : ~ False => @lem7216176 i m n f h1 h2 h3 h4). Qed.
Lemma lem7216179 (p : Prop) : (term388 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7216180 : term429 = False.
Proof. exact (@lem7216179 False). Qed.
Lemma lem7216181 (i : type1009) (m : nat) (n : nat) (f : nat -> real) (h1 : term265 i) (h2 : term44) (h3 : term49) (h4 : term57 m n f) : False.
Proof. exact (EQ_MP (@lem7216180) (@lem7216177 i m n f h1 h2 h3 h4)). Qed.
Lemma lem7216182 (i : type1009) (m : nat) (f : nat -> real) (h1 : term265 i) (h2 : term44) (h3 : term49) (h4 : term66 m f) : False.
Proof. exact (ex_elim (@lem7215100 m f h4) (fun n : nat => fun h0 : term65 m f n => @lem7216181 i m n f h1 h2 h3 h0)). Qed.
Lemma lem7216183 (i : type1009) (f : nat -> real) (h1 : term265 i) (h2 : term44) (h3 : term49) (h4 : term73 f) : False.
Proof. exact (ex_elim (@lem7215099 f h4) (fun m : nat => fun h0 : term72 f m => @lem7216182 i m f h1 h2 h3 h0)). Qed.
Lemma lem7216184 (i : type1009) (h1 : term265 i) (h2 : term44) (h3 : term49) (h4 : term10) : False.
Proof. exact (ex_elim (@lem7214455 h4) (fun f : nat -> real => fun h0 : term80 f => @lem7216183 i f h1 h2 h3 h0)). Qed.
Lemma lem7216185 (h1 : term17) (h2 : term44) (h3 : term49) (h4 : term10) : False.
Proof. exact (ex_elim (@lem7215097 h1) (fun i : type1009 => fun h0 : term267 i => @lem7216184 i h0 h2 h3 h4)). Qed.
Lemma lem7216186 (h1 : term44) (h2 : term49) (h3 : term10) : term15.
Proof. exact (fun h0 : term17 => @lem7216185 h0 h1 h2 h3). Qed.
Lemma lem7216187 : term15 = term16.
Proof. exact (@lem69 term17). Qed.
Lemma lem7216188 (h1 : term44) (h2 : term49) (h3 : term10) : term16.
Proof. exact (EQ_MP (@lem7216187) (@lem7216186 h1 h2 h3)). Qed.
Lemma lem7216189 (h1 : term49) (h2 : term10) : term20.
Proof. exact (fun h0 : term44 => @lem7216188 h0 h1 h2). Qed.
Lemma lem7216190 (h1 : term10) : term23.
Proof. exact (fun h0 : term49 => @lem7216189 h0 h1). Qed.
Lemma lem7216191 : term25.
Proof. exact (fun h0 : term10 => @lem7216190 h0). Qed.
Lemma lem7216192 : term11.
Proof. exact (EQ_MP (@lem7214353) (@lem7216191)). Qed.
Lemma lem7216194 : term11.
Proof. exact (@lem7214091 (@lem7216192)). Qed.
Lemma lem7216195 (h1 : term10) : term22.
Proof. exact (@lem7216194 (@lem7214076 h1)). Qed.
Lemma lem7216196 (h1 : term10) : term19.
Proof. exact (@lem7216195 h1 (@lem98377)). Qed.
Lemma lem7216197 (h1 : term10) : term15.
Proof. exact (@lem7216196 h1 (@lem93743)). Qed.
Lemma lem7216198 (h1 : term10) : False.
Proof. exact (@lem7216197 h1 (@lem7214061)). Qed.
Lemma lem7216199 (h1 : term10) : term10 = False.
Proof. exact (prop_ext (fun h2 : term10 => @lem7216198 h1) (fun h2 : False => @lem7214076 h1)). Qed.
Lemma lem7216200 (h1 : term10) : False.
Proof. exact (EQ_MP (@lem7216199 h1) (@lem7214076 h1)). Qed.
Lemma lem7216201 : term9.
Proof. exact (fun h0 : term10 => @lem7216200 h0). Qed.
Lemma lem7216202 : term8.
Proof. exact (EQ_MP (@lem7214075) (@lem7216201)). Qed.
