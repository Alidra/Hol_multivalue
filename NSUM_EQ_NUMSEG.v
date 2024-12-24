Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_EQ_NUMSEG_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_NUMSEG_spec.
Require Import IN_NUMSEG_spec.
Require Import NSUM_EQ_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
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
Require Import thm19490_spec.
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
Lemma lem7041097 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem7041098 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem7041099 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem7041098 t1) (@lem7041097 t1)). Qed.
Lemma lem7041100 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem7041099 t1 t2). Qed.
Lemma lem7041101 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem7041102 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem7041101 t1 t2) (@lem7041100 t1 t2)). Qed.
Lemma lem7041103 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem7041102 t1 t2 t3). Qed.
Lemma lem7041104 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem7041105 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem7041104 t1 t2 t3) (@lem7041103 t1 t2 t3)). Qed.
Lemma lem7041106 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem7041105 t1 t2 t3)). Qed.
Lemma lem7041108 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7041109 : term8 = term9.
Proof. exact (@lem7041108 term8). Qed.
Lemma lem7041110 : term9 = term8.
Proof. exact (SYM (@lem7041109)). Qed.
Lemma lem7041111 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem7041112 : term11.
Proof. exact (@lem6938831 nat). Qed.
Lemma lem7041115 {_127166 : Type'} (h1 : term12 _127166) : term12 _127166.
Proof. exact (h1). Qed.
Lemma lem7041116 {_127166 : Type'} : term13 _127166.
Proof. exact (fun h0 : term12 _127166 => @lem7041115 _127166 h0). Qed.
Lemma lem7041117 {_127166 : Type'} (h1 : term13 _127166) : term13 _127166.
Proof. exact (h1). Qed.
Lemma lem7041118 {_127166 : Type'} (h1 : term12 _127166) : term12 _127166.
Proof. exact (h1). Qed.
Lemma lem7041119 {_127166 : Type'} (h1 : term12 _127166) (h2 : term13 _127166) : term12 _127166.
Proof. exact (@lem7041117 _127166 h2 (@lem7041118 _127166 h1)). Qed.
Lemma lem7041120 {_127166 : Type'} (h1 : term12 _127166) : term14 _127166.
Proof. exact (fun h0 : term13 _127166 => @lem7041119 _127166 h1 h0). Qed.
Lemma lem7041121 {_127166 : Type'} (h1 : term13 _127166) : term13 _127166.
Proof. exact (h1). Qed.
Lemma lem7041122 {_127166 : Type'} (h1 : term12 _127166) (h2 : term13 _127166) : term12 _127166.
Proof. exact (@lem7041120 _127166 h1 (@lem7041121 _127166 h2)). Qed.
Lemma lem7041123 {_127166 : Type'} (h1 : term13 _127166) : term13 _127166.
Proof. exact (fun h0 : term12 _127166 => @lem7041122 _127166 h0 h1). Qed.
Lemma lem7041124 {_127166 : Type'} : term15 _127166.
Proof. exact (fun h0 : term13 _127166 => @lem7041123 _127166 h0). Qed.
Lemma lem7041127 {_127166 : Type'} : term13 _127166.
Proof. exact (@lem7041124 _127166 (@lem7041116 _127166)). Qed.
Lemma lem7041128 {_127166 : Type'} : term13 _127166.
Proof. exact (@lem7041127 _127166). Qed.
Lemma lem7041206 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7041207 : term16 = term17.
Proof. exact (@lem7041206 term11). Qed.
Lemma lem7041228 {_127166 : Type'} : (term18 _127166) = (term18 _127166).
Proof. exact (eq_refl (term18 _127166)). Qed.
Lemma lem7041229 {_127166 : Type'} : (term19 _127166) = (term20 _127166).
Proof. exact (MK_COMB (@lem7041228 _127166) (@lem7041207)). Qed.
Lemma lem7041232 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem7041233 {_127166 : Type'} : (term22 _127166) = (term23 _127166).
Proof. exact (MK_COMB (@lem7041232) (@lem7041229 _127166)). Qed.
Lemma lem7041236 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem7041237 {_127166 : Type'} : (term25 _127166) = (term26 _127166).
Proof. exact (MK_COMB (@lem7041236) (@lem7041233 _127166)). Qed.
Lemma lem7041240 : term27 = term27.
Proof. exact (eq_refl term27). Qed.
Lemma lem7041247 {_127166 : Type'} : (term12 _127166) = (term28 _127166).
Proof. exact (MK_COMB (@lem7041240) (@lem7041237 _127166)). Qed.
Lemma lem7041248 (f : nat -> nat) (s : nat -> Prop) (g : nat -> nat) : ((@nsum nat s f) = (@nsum nat s g)) = ((@nsum nat s f) = (@nsum nat s g)).
Proof. exact (eq_refl ((@nsum nat s f) = (@nsum nat s g))). Qed.
Lemma lem7041253 (s : nat -> Prop) (f : nat -> nat) (g : nat -> nat) (x : nat) : (term29 s f g x) = (term29 s f g x).
Proof. exact (eq_refl (term29 s f g x)). Qed.
Lemma lem7041254 (s : nat -> Prop) (f : nat -> nat) (g : nat -> nat) : (term30 s f g) = (term30 s f g).
Proof. exact (fun_ext (fun x : nat => @lem7041253 s f g x)). Qed.
Lemma lem7041255 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7041256 (s : nat -> Prop) (f : nat -> nat) (g : nat -> nat) : (term31 s f g) = (term31 s f g).
Proof. exact (MK_COMB (@lem7041255) (@lem7041254 s f g)). Qed.
Lemma lem7041257 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7041258 (s : nat -> Prop) (f : nat -> nat) (g : nat -> nat) : (term32 s f g) = (term32 s f g).
Proof. exact (MK_COMB (@lem7041257) (@lem7041256 s f g)). Qed.
Lemma lem7041259 (f : nat -> nat) (s : nat -> Prop) (g : nat -> nat) : (term33 f s g) = (term33 f s g).
Proof. exact (MK_COMB (@lem7041258 s f g) (@lem7041248 f s g)). Qed.
Lemma lem7041260 (f : nat -> nat) (g : nat -> nat) : (term34 f g) = (term34 f g).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem7041259 f s g)). Qed.
Lemma lem7041261 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem7041262 (f : nat -> nat) (g : nat -> nat) : (term35 f g) = (term35 f g).
Proof. exact (MK_COMB (@lem7041261) (@lem7041260 f g)). Qed.
Lemma lem7041263 (f : nat -> nat) : (term36 f) = (term36 f).
Proof. exact (fun_ext (fun g : nat -> nat => @lem7041262 f g)). Qed.
Lemma lem7041264 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7041265 (f : nat -> nat) : (term37 f) = (term37 f).
Proof. exact (MK_COMB (@lem7041264) (@lem7041263 f)). Qed.
Lemma lem7041266 : term38 = term38.
Proof. exact (fun_ext (fun f : nat -> nat => @lem7041265 f)). Qed.
Lemma lem7041267 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7041268 : term11 = term11.
Proof. exact (MK_COMB (@lem7041267) (@lem7041266)). Qed.
Lemma lem7041269 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7041270 : term17 = term17.
Proof. exact (MK_COMB (@lem7041269) (@lem7041268)). Qed.
Lemma lem7041271 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : ((@nsum _127166 s f) = (@nsum _127166 s g)) = ((@nsum _127166 s f) = (@nsum _127166 s g)).
Proof. exact (eq_refl ((@nsum _127166 s f) = (@nsum _127166 s g))). Qed.
Lemma lem7041276 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) (x : _127166) : (term39 _127166 s f g x) = (term39 _127166 s f g x).
Proof. exact (eq_refl (term39 _127166 s f g x)). Qed.
Lemma lem7041277 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) : (term40 _127166 s f g) = (term40 _127166 s f g).
Proof. exact (fun_ext (fun x : _127166 => @lem7041276 _127166 s f g x)). Qed.
Lemma lem7041278 {_127166 : Type'} : (@all _127166) = (@all _127166).
Proof. exact (eq_refl (@all _127166)). Qed.
Lemma lem7041279 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) : (term41 _127166 s f g) = (term41 _127166 s f g).
Proof. exact (MK_COMB (@lem7041278 _127166) (@lem7041277 _127166 s f g)). Qed.
Lemma lem7041280 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7041281 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) : (term42 _127166 s f g) = (term42 _127166 s f g).
Proof. exact (MK_COMB (@lem7041280) (@lem7041279 _127166 s f g)). Qed.
Lemma lem7041282 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : (term43 _127166 f s g) = (term43 _127166 f s g).
Proof. exact (MK_COMB (@lem7041281 _127166 s f g) (@lem7041271 _127166 f s g)). Qed.
Lemma lem7041283 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) : (term44 _127166 f g) = (term44 _127166 f g).
Proof. exact (fun_ext (fun s : _127166 -> Prop => @lem7041282 _127166 f s g)). Qed.
Lemma lem7041284 {_127166 : Type'} : (@all (_127166 -> Prop)) = (@all (_127166 -> Prop)).
Proof. exact (eq_refl (@all (_127166 -> Prop))). Qed.
Lemma lem7041285 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) : (term45 _127166 f g) = (term45 _127166 f g).
Proof. exact (MK_COMB (@lem7041284 _127166) (@lem7041283 _127166 f g)). Qed.
Lemma lem7041286 {_127166 : Type'} (f : _127166 -> nat) : (term46 _127166 f) = (term46 _127166 f).
Proof. exact (fun_ext (fun g : _127166 -> nat => @lem7041285 _127166 f g)). Qed.
Lemma lem7041287 {_127166 : Type'} : (@all (_127166 -> nat)) = (@all (_127166 -> nat)).
Proof. exact (eq_refl (@all (_127166 -> nat))). Qed.
Lemma lem7041288 {_127166 : Type'} (f : _127166 -> nat) : (term47 _127166 f) = (term47 _127166 f).
Proof. exact (MK_COMB (@lem7041287 _127166) (@lem7041286 _127166 f)). Qed.
Lemma lem7041289 {_127166 : Type'} : (term48 _127166) = (term48 _127166).
Proof. exact (fun_ext (fun f : _127166 -> nat => @lem7041288 _127166 f)). Qed.
Lemma lem7041290 {_127166 : Type'} : (@all (_127166 -> nat)) = (@all (_127166 -> nat)).
Proof. exact (eq_refl (@all (_127166 -> nat))). Qed.
Lemma lem7041291 {_127166 : Type'} : (term49 _127166) = (term49 _127166).
Proof. exact (MK_COMB (@lem7041290 _127166) (@lem7041289 _127166)). Qed.
Lemma lem7041292 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7041293 {_127166 : Type'} : (term18 _127166) = (term18 _127166).
Proof. exact (MK_COMB (@lem7041292) (@lem7041291 _127166)). Qed.
Lemma lem7041294 {_127166 : Type'} : (term20 _127166) = (term20 _127166).
Proof. exact (MK_COMB (@lem7041293 _127166) (@lem7041270)). Qed.
Lemma lem7041295 (m : nat) (n : nat) : (term50 m n) = (term50 m n).
Proof. exact (eq_refl (term50 m n)). Qed.
Lemma lem7041296 (m : nat) : (term51 m) = (term51 m).
Proof. exact (fun_ext (fun n : nat => @lem7041295 m n)). Qed.
Lemma lem7041297 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7041298 (m : nat) : (term52 m) = (term52 m).
Proof. exact (MK_COMB (@lem7041297) (@lem7041296 m)). Qed.
Lemma lem7041299 : term53 = term53.
Proof. exact (fun_ext (fun m : nat => @lem7041298 m)). Qed.
Lemma lem7041300 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7041301 : term54 = term54.
Proof. exact (MK_COMB (@lem7041300) (@lem7041299)). Qed.
Lemma lem7041302 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7041303 : term21 = term21.
Proof. exact (MK_COMB (@lem7041302) (@lem7041301)). Qed.
Lemma lem7041304 {_127166 : Type'} : (term23 _127166) = (term23 _127166).
Proof. exact (MK_COMB (@lem7041303) (@lem7041294 _127166)). Qed.
Lemma lem7041313 (m : nat) (p : nat) (n : nat) : ((term55 p m n) = (term56 m p n)) = ((term55 p m n) = (term56 m p n)).
Proof. exact (eq_refl ((term55 p m n) = (term56 m p n))). Qed.
Lemma lem7041314 (m : nat) (n : nat) : (term57 m n) = (term57 m n).
Proof. exact (fun_ext (fun p : nat => @lem7041313 m p n)). Qed.
Lemma lem7041315 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7041316 (m : nat) (n : nat) : (term58 m n) = (term58 m n).
Proof. exact (MK_COMB (@lem7041315) (@lem7041314 m n)). Qed.
Lemma lem7041317 (m : nat) : (term59 m) = (term59 m).
Proof. exact (fun_ext (fun n : nat => @lem7041316 m n)). Qed.
Lemma lem7041318 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7041319 (m : nat) : (term60 m) = (term60 m).
Proof. exact (MK_COMB (@lem7041318) (@lem7041317 m)). Qed.
Lemma lem7041320 : term61 = term61.
Proof. exact (fun_ext (fun m : nat => @lem7041319 m)). Qed.
Lemma lem7041321 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7041322 : term62 = term62.
Proof. exact (MK_COMB (@lem7041321) (@lem7041320)). Qed.
Lemma lem7041323 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7041324 : term24 = term24.
Proof. exact (MK_COMB (@lem7041323) (@lem7041322)). Qed.
Lemma lem7041325 {_127166 : Type'} : (term26 _127166) = (term26 _127166).
Proof. exact (MK_COMB (@lem7041324) (@lem7041304 _127166)). Qed.
Lemma lem7041326 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) : ((term63 m n f) = (term63 m n g)) = ((term63 m n f) = (term63 m n g)).
Proof. exact (eq_refl ((term63 m n f) = (term63 m n g))). Qed.
Lemma lem7041335 (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) (i : nat) : (term64 m n f g i) = (term64 m n f g i).
Proof. exact (eq_refl (term64 m n f g i)). Qed.
Lemma lem7041336 (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) : (term65 m n f g) = (term65 m n f g).
Proof. exact (fun_ext (fun i : nat => @lem7041335 m n f g i)). Qed.
Lemma lem7041337 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7041338 (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) : (term66 m n f g) = (term66 m n f g).
Proof. exact (MK_COMB (@lem7041337) (@lem7041336 m n f g)). Qed.
Lemma lem7041339 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7041340 (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) : (term67 m n f g) = (term67 m n f g).
Proof. exact (MK_COMB (@lem7041339) (@lem7041338 m n f g)). Qed.
Lemma lem7041341 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) : (term68 f m n g) = (term68 f m n g).
Proof. exact (MK_COMB (@lem7041340 m n f g) (@lem7041326 f m n g)). Qed.
Lemma lem7041342 (f : nat -> nat) (m : nat) (g : nat -> nat) : (term69 f m g) = (term69 f m g).
Proof. exact (fun_ext (fun n : nat => @lem7041341 f m n g)). Qed.
Lemma lem7041343 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7041344 (f : nat -> nat) (m : nat) (g : nat -> nat) : (term70 f m g) = (term70 f m g).
Proof. exact (MK_COMB (@lem7041343) (@lem7041342 f m g)). Qed.
Lemma lem7041345 (f : nat -> nat) (g : nat -> nat) : (term71 f g) = (term71 f g).
Proof. exact (fun_ext (fun m : nat => @lem7041344 f m g)). Qed.
Lemma lem7041346 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7041347 (f : nat -> nat) (g : nat -> nat) : (term72 f g) = (term72 f g).
Proof. exact (MK_COMB (@lem7041346) (@lem7041345 f g)). Qed.
Lemma lem7041348 (f : nat -> nat) : (term73 f) = (term73 f).
Proof. exact (fun_ext (fun g : nat -> nat => @lem7041347 f g)). Qed.
Lemma lem7041349 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7041350 (f : nat -> nat) : (term74 f) = (term74 f).
Proof. exact (MK_COMB (@lem7041349) (@lem7041348 f)). Qed.
Lemma lem7041351 : term75 = term75.
Proof. exact (fun_ext (fun f : nat -> nat => @lem7041350 f)). Qed.
Lemma lem7041352 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7041353 : term8 = term8.
Proof. exact (MK_COMB (@lem7041352) (@lem7041351)). Qed.
Lemma lem7041354 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7041355 : term10 = term10.
Proof. exact (MK_COMB (@lem7041354) (@lem7041353)). Qed.
Lemma lem7041356 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7041357 : term27 = term27.
Proof. exact (MK_COMB (@lem7041356) (@lem7041355)). Qed.
Lemma lem7041358 {_127166 : Type'} : (term28 _127166) = (term28 _127166).
Proof. exact (MK_COMB (@lem7041357) (@lem7041325 _127166)). Qed.
Lemma lem7041493 {_127166 : Type'} : (term12 _127166) = (term28 _127166).
Proof. exact (TRANS (@lem7041247 _127166) (@lem7041358 _127166)). Qed.
Lemma lem7041494 {_127166 : Type'} : (term28 _127166) = (term12 _127166).
Proof. exact (SYM (@lem7041493 _127166)). Qed.
Lemma lem7041495 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem7041496 (h1 : term62) : term62.
Proof. exact (h1). Qed.
Lemma lem7041498 {_127166 : Type'} (h1 : term49 _127166) : term49 _127166.
Proof. exact (h1). Qed.
Lemma lem7041499 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem7041506 (m : nat) (i : nat) (n : nat) : (term76 m i n) = (term77 m i n).
Proof. exact (@lem17045 (Peano.le m i) (Peano.le i n)). Qed.
Lemma lem7041507 (f : nat -> nat) (g : nat -> nat) (i : nat) : ((f i) = (g i)) = ((f i) = (g i)).
Proof. exact (eq_refl ((f i) = (g i))). Qed.
Lemma lem7041508 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7041509 (m : nat) (i : nat) (n : nat) : (term78 m i n) = (term79 m i n).
Proof. exact (MK_COMB (@lem7041508) (@lem7041506 m i n)). Qed.
Lemma lem7041510 (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) (i : nat) : (term80 m n f g i) = (term81 m n f g i).
Proof. exact (MK_COMB (@lem7041509 m i n) (@lem7041507 f g i)). Qed.
Lemma lem7041511 (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) (i : nat) : (term64 m n f g i) = (term80 m n f g i).
Proof. exact (@lem17265 (term56 m i n) ((f i) = (g i))). Qed.
Lemma lem7041512 (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) (i : nat) : (term64 m n f g i) = (term81 m n f g i).
Proof. exact (TRANS (@lem7041511 m n f g i) (@lem7041510 m n f g i)). Qed.
Lemma lem7041513 (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) : (term65 m n f g) = (term82 m n f g).
Proof. exact (fun_ext (fun i : nat => @lem7041512 m n f g i)). Qed.
Lemma lem7041514 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7041515 (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) : (term66 m n f g) = (term83 m n f g).
Proof. exact (MK_COMB (@lem7041514) (@lem7041513 m n f g)). Qed.
Lemma lem7041516 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) : (term84 f m n g) = (term84 f m n g).
Proof. exact (eq_refl (term84 f m n g)). Qed.
Lemma lem7041517 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7041518 (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) : (term85 m n f g) = (term86 m n f g).
Proof. exact (MK_COMB (@lem7041517) (@lem7041515 m n f g)). Qed.
Lemma lem7041519 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) : (term87 f m n g) = (term88 f m n g).
Proof. exact (MK_COMB (@lem7041518 m n f g) (@lem7041516 f m n g)). Qed.
Lemma lem7041520 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) : (term89 f m n g) = (term87 f m n g).
Proof. exact (@lem17362 (term66 m n f g) ((term63 m n f) = (term63 m n g))). Qed.
Lemma lem7041521 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) : (term89 f m n g) = (term88 f m n g).
Proof. exact (TRANS (@lem7041520 f m n g) (@lem7041519 f m n g)). Qed.
Lemma lem7041522 (P : nat -> Prop) : (term90 P) = (term91 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem7041523 (f : nat -> nat) (m : nat) (g : nat -> nat) : (term92 f m g) = (term93 f m g).
Proof. exact (@lem7041522 (term69 f m g)). Qed.
Lemma lem7041524 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) : (term94 f m g n) = (term68 f m n g).
Proof. exact (eq_refl (term94 f m g n)). Qed.
Lemma lem7041525 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7041526 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) : (term95 f m g n) = (term89 f m n g).
Proof. exact (MK_COMB (@lem7041525) (@lem7041524 f m n g)). Qed.
Lemma lem7041527 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) : (term95 f m g n) = (term88 f m n g).
Proof. exact (TRANS (@lem7041526 f m n g) (@lem7041521 f m n g)). Qed.
Lemma lem7041528 (f : nat -> nat) (m : nat) (g : nat -> nat) : (term96 f m g) = (term97 f m g).
Proof. exact (fun_ext (fun n : nat => @lem7041527 f m n g)). Qed.
Lemma lem7041529 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7041530 (f : nat -> nat) (m : nat) (g : nat -> nat) : (term93 f m g) = (term98 f m g).
Proof. exact (MK_COMB (@lem7041529) (@lem7041528 f m g)). Qed.
Lemma lem7041531 (f : nat -> nat) (m : nat) (g : nat -> nat) : (term92 f m g) = (term98 f m g).
Proof. exact (TRANS (@lem7041523 f m g) (@lem7041530 f m g)). Qed.
Lemma lem7041532 (P : nat -> Prop) : (term90 P) = (term91 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem7041533 (f : nat -> nat) (g : nat -> nat) : (term99 f g) = (term100 f g).
Proof. exact (@lem7041532 (term71 f g)). Qed.
Lemma lem7041534 (f : nat -> nat) (m : nat) (g : nat -> nat) : (term101 f g m) = (term70 f m g).
Proof. exact (eq_refl (term101 f g m)). Qed.
Lemma lem7041535 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7041536 (f : nat -> nat) (m : nat) (g : nat -> nat) : (term102 f g m) = (term92 f m g).
Proof. exact (MK_COMB (@lem7041535) (@lem7041534 f m g)). Qed.
Lemma lem7041537 (f : nat -> nat) (m : nat) (g : nat -> nat) : (term102 f g m) = (term98 f m g).
Proof. exact (TRANS (@lem7041536 f m g) (@lem7041531 f m g)). Qed.
Lemma lem7041538 (f : nat -> nat) (g : nat -> nat) : (term103 f g) = (term104 f g).
Proof. exact (fun_ext (fun m : nat => @lem7041537 f m g)). Qed.
Lemma lem7041539 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7041540 (f : nat -> nat) (g : nat -> nat) : (term100 f g) = (term105 f g).
Proof. exact (MK_COMB (@lem7041539) (@lem7041538 f g)). Qed.
Lemma lem7041541 (f : nat -> nat) (g : nat -> nat) : (term99 f g) = (term105 f g).
Proof. exact (TRANS (@lem7041533 f g) (@lem7041540 f g)). Qed.
Lemma lem7041542 (P : type1002) : (term106 P) = (term107 P).
Proof. exact (@lem18392 (nat -> nat) P). Qed.
Lemma lem7041543 (f : nat -> nat) : (term108 f) = (term109 f).
Proof. exact (@lem7041542 (term73 f)). Qed.
Lemma lem7041544 (f : nat -> nat) (g : nat -> nat) : (term110 f g) = (term72 f g).
Proof. exact (eq_refl (term110 f g)). Qed.
Lemma lem7041545 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7041546 (f : nat -> nat) (g : nat -> nat) : (term111 f g) = (term99 f g).
Proof. exact (MK_COMB (@lem7041545) (@lem7041544 f g)). Qed.
Lemma lem7041547 (f : nat -> nat) (g : nat -> nat) : (term111 f g) = (term105 f g).
Proof. exact (TRANS (@lem7041546 f g) (@lem7041541 f g)). Qed.
Lemma lem7041548 (f : nat -> nat) : (term112 f) = (term113 f).
Proof. exact (fun_ext (fun g : nat -> nat => @lem7041547 f g)). Qed.
Lemma lem7041549 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem7041550 (f : nat -> nat) : (term109 f) = (term114 f).
Proof. exact (MK_COMB (@lem7041549) (@lem7041548 f)). Qed.
Lemma lem7041551 (f : nat -> nat) : (term108 f) = (term114 f).
Proof. exact (TRANS (@lem7041543 f) (@lem7041550 f)). Qed.
Lemma lem7041552 (P : type1002) : (term106 P) = (term107 P).
Proof. exact (@lem18392 (nat -> nat) P). Qed.
Lemma lem7041553 : term10 = term115.
Proof. exact (@lem7041552 term75). Qed.
Lemma lem7041554 (f : nat -> nat) : (term116 f) = (term74 f).
Proof. exact (eq_refl (term116 f)). Qed.
Lemma lem7041555 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7041556 (f : nat -> nat) : (term117 f) = (term108 f).
Proof. exact (MK_COMB (@lem7041555) (@lem7041554 f)). Qed.
Lemma lem7041557 (f : nat -> nat) : (term117 f) = (term114 f).
Proof. exact (TRANS (@lem7041556 f) (@lem7041551 f)). Qed.
Lemma lem7041558 : term118 = term119.
Proof. exact (fun_ext (fun f : nat -> nat => @lem7041557 f)). Qed.
Lemma lem7041559 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem7041560 : term115 = term120.
Proof. exact (MK_COMB (@lem7041559) (@lem7041558)). Qed.
Lemma lem7041673 : term10 = term120.
Proof. exact (TRANS (@lem7041553) (@lem7041560)). Qed.
Lemma lem7041674 (h1 : term10) : term120.
Proof. exact (EQ_MP (@lem7041673) (@lem7041495 h1)). Qed.
Lemma lem7041685 (m : nat) (p : nat) (n : nat) : (term76 m p n) = (term77 m p n).
Proof. exact (@lem17045 (Peano.le m p) (Peano.le p n)). Qed.
Lemma lem7041691 (m : nat) (p : nat) (n : nat) : (term121 m p n) = (term121 m p n).
Proof. exact (eq_refl (term121 m p n)). Qed.
Lemma lem7041693 (p : nat) (m : nat) (n : nat) : (term122 p m n) = (term122 p m n).
Proof. exact (eq_refl (term122 p m n)). Qed.
Lemma lem7041694 (m : nat) (p : nat) (n : nat) : (term123 m p n) = (term124 m p n).
Proof. exact (MK_COMB (@lem7041693 p m n) (@lem7041685 m p n)). Qed.
Lemma lem7041695 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7041696 (m : nat) (p : nat) (n : nat) : (term125 m p n) = (term126 m p n).
Proof. exact (MK_COMB (@lem7041695) (@lem7041694 m p n)). Qed.
Lemma lem7041697 (m : nat) (p : nat) (n : nat) : (term127 m p n) = (term128 m p n).
Proof. exact (MK_COMB (@lem7041696 m p n) (@lem7041691 m p n)). Qed.
Lemma lem7041698 (m : nat) (p : nat) (n : nat) : ((term55 p m n) = (term56 m p n)) = (term127 m p n).
Proof. exact (@lem17784 (term55 p m n) (term56 m p n)). Qed.
Lemma lem7041699 (m : nat) (p : nat) (n : nat) : ((term55 p m n) = (term56 m p n)) = (term128 m p n).
Proof. exact (TRANS (@lem7041698 m p n) (@lem7041697 m p n)). Qed.
Lemma lem7041700 (m : nat) (n : nat) : (term57 m n) = (term129 m n).
Proof. exact (fun_ext (fun p : nat => @lem7041699 m p n)). Qed.
Lemma lem7041701 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7041702 (m : nat) (n : nat) : (term58 m n) = (term130 m n).
Proof. exact (MK_COMB (@lem7041701) (@lem7041700 m n)). Qed.
Lemma lem7041703 (m : nat) : (term59 m) = (term131 m).
Proof. exact (fun_ext (fun n : nat => @lem7041702 m n)). Qed.
Lemma lem7041704 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7041705 (m : nat) : (term60 m) = (term132 m).
Proof. exact (MK_COMB (@lem7041704) (@lem7041703 m)). Qed.
Lemma lem7041706 : term61 = term133.
Proof. exact (fun_ext (fun m : nat => @lem7041705 m)). Qed.
Lemma lem7041707 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7041708 : term62 = term134.
Proof. exact (MK_COMB (@lem7041707) (@lem7041706)). Qed.
Lemma lem7041718 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term135 A P Q) = (term136 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7041719 (P : nat -> Prop) (Q : nat -> Prop) : (term137 P Q) = (term138 P Q).
Proof. exact (@lem7041718 nat P Q). Qed.
Lemma lem7041720 (m : nat) (n : nat) : (term139 m n) = (term140 m n).
Proof. exact (@lem7041719 (term141 m n) (term142 m n)). Qed.
Lemma lem7041721 (m : nat) (p : nat) (n : nat) : (term143 m n p) = (term124 m p n).
Proof. exact (eq_refl (term143 m n p)). Qed.
Lemma lem7041722 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7041723 (m : nat) (p : nat) (n : nat) : (term144 m n p) = (term126 m p n).
Proof. exact (MK_COMB (@lem7041722) (@lem7041721 m p n)). Qed.
Lemma lem7041724 (m : nat) (p : nat) (n : nat) : (term145 m n p) = (term121 m p n).
Proof. exact (eq_refl (term145 m n p)). Qed.
Lemma lem7041725 (m : nat) (p : nat) (n : nat) : (term146 m n p) = (term128 m p n).
Proof. exact (MK_COMB (@lem7041723 m p n) (@lem7041724 m p n)). Qed.
Lemma lem7041726 (m : nat) (n : nat) : (term147 m n) = (term129 m n).
Proof. exact (fun_ext (fun p : nat => @lem7041725 m p n)). Qed.
Lemma lem7041727 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7041728 (m : nat) (n : nat) : (term139 m n) = (term130 m n).
Proof. exact (MK_COMB (@lem7041727) (@lem7041726 m n)). Qed.
Lemma lem7041729 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7041730 (m : nat) (n : nat) : (term148 m n) = (term149 m n).
Proof. exact (MK_COMB (@lem7041729) (@lem7041728 m n)). Qed.
Lemma lem7041731 (m : nat) (p : nat) (n : nat) : (term143 m n p) = (term124 m p n).
Proof. exact (eq_refl (term143 m n p)). Qed.
Lemma lem7041732 (m : nat) (n : nat) : (term150 m n) = (term141 m n).
Proof. exact (fun_ext (fun p : nat => @lem7041731 m p n)). Qed.
Lemma lem7041733 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7041734 (m : nat) (n : nat) : (term151 m n) = (term152 m n).
Proof. exact (MK_COMB (@lem7041733) (@lem7041732 m n)). Qed.
Lemma lem7041735 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7041736 (m : nat) (n : nat) : (term153 m n) = (term154 m n).
Proof. exact (MK_COMB (@lem7041735) (@lem7041734 m n)). Qed.
Lemma lem7041737 (m : nat) (p : nat) (n : nat) : (term145 m n p) = (term121 m p n).
Proof. exact (eq_refl (term145 m n p)). Qed.
Lemma lem7041738 (m : nat) (n : nat) : (term155 m n) = (term142 m n).
Proof. exact (fun_ext (fun p : nat => @lem7041737 m p n)). Qed.
Lemma lem7041739 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7041740 (m : nat) (n : nat) : (term156 m n) = (term157 m n).
Proof. exact (MK_COMB (@lem7041739) (@lem7041738 m n)). Qed.
Lemma lem7041741 (m : nat) (n : nat) : (term140 m n) = (term158 m n).
Proof. exact (MK_COMB (@lem7041736 m n) (@lem7041740 m n)). Qed.
Lemma lem7041742 (m : nat) (n : nat) : ((term139 m n) = (term140 m n)) = ((term130 m n) = (term158 m n)).
Proof. exact (MK_COMB (@lem7041730 m n) (@lem7041741 m n)). Qed.
Lemma lem7041743 (m : nat) (n : nat) : (term130 m n) = (term158 m n).
Proof. exact (EQ_MP (@lem7041742 m n) (@lem7041720 m n)). Qed.
Lemma lem7041840 (m : nat) : (term131 m) = (term159 m).
Proof. exact (fun_ext (fun n : nat => @lem7041743 m n)). Qed.
Lemma lem7041841 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7041842 (m : nat) : (term132 m) = (term160 m).
Proof. exact (MK_COMB (@lem7041841) (@lem7041840 m)). Qed.
Lemma lem7041844 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term135 A P Q) = (term136 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7041845 (P : nat -> Prop) (Q : nat -> Prop) : (term137 P Q) = (term138 P Q).
Proof. exact (@lem7041844 nat P Q). Qed.
Lemma lem7041846 (m : nat) : (term161 m) = (term162 m).
Proof. exact (@lem7041845 (term163 m) (term164 m)). Qed.
Lemma lem7041847 (m : nat) (n : nat) : (term165 m n) = (term152 m n).
Proof. exact (eq_refl (term165 m n)). Qed.
Lemma lem7041848 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7041849 (m : nat) (n : nat) : (term166 m n) = (term154 m n).
Proof. exact (MK_COMB (@lem7041848) (@lem7041847 m n)). Qed.
Lemma lem7041850 (m : nat) (n : nat) : (term167 m n) = (term157 m n).
Proof. exact (eq_refl (term167 m n)). Qed.
Lemma lem7041851 (m : nat) (n : nat) : (term168 m n) = (term158 m n).
Proof. exact (MK_COMB (@lem7041849 m n) (@lem7041850 m n)). Qed.
Lemma lem7041852 (m : nat) : (term169 m) = (term159 m).
Proof. exact (fun_ext (fun n : nat => @lem7041851 m n)). Qed.
Lemma lem7041853 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7041854 (m : nat) : (term161 m) = (term160 m).
Proof. exact (MK_COMB (@lem7041853) (@lem7041852 m)). Qed.
Lemma lem7041855 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7041856 (m : nat) : (term170 m) = (term171 m).
Proof. exact (MK_COMB (@lem7041855) (@lem7041854 m)). Qed.
Lemma lem7041857 (m : nat) (n : nat) : (term165 m n) = (term152 m n).
Proof. exact (eq_refl (term165 m n)). Qed.
Lemma lem7041858 (m : nat) : (term172 m) = (term163 m).
Proof. exact (fun_ext (fun n : nat => @lem7041857 m n)). Qed.
Lemma lem7041859 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7041860 (m : nat) : (term173 m) = (term174 m).
Proof. exact (MK_COMB (@lem7041859) (@lem7041858 m)). Qed.
Lemma lem7041861 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7041862 (m : nat) : (term175 m) = (term176 m).
Proof. exact (MK_COMB (@lem7041861) (@lem7041860 m)). Qed.
Lemma lem7041863 (m : nat) (n : nat) : (term167 m n) = (term157 m n).
Proof. exact (eq_refl (term167 m n)). Qed.
Lemma lem7041864 (m : nat) : (term177 m) = (term164 m).
Proof. exact (fun_ext (fun n : nat => @lem7041863 m n)). Qed.
Lemma lem7041865 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7041866 (m : nat) : (term178 m) = (term179 m).
Proof. exact (MK_COMB (@lem7041865) (@lem7041864 m)). Qed.
Lemma lem7041867 (m : nat) : (term162 m) = (term180 m).
Proof. exact (MK_COMB (@lem7041862 m) (@lem7041866 m)). Qed.
Lemma lem7041868 (m : nat) : ((term161 m) = (term162 m)) = ((term160 m) = (term180 m)).
Proof. exact (MK_COMB (@lem7041856 m) (@lem7041867 m)). Qed.
Lemma lem7041869 (m : nat) : (term160 m) = (term180 m).
Proof. exact (EQ_MP (@lem7041868 m) (@lem7041846 m)). Qed.
Lemma lem7041974 (m : nat) : (term132 m) = (term180 m).
Proof. exact (TRANS (@lem7041842 m) (@lem7041869 m)). Qed.
Lemma lem7041975 : term133 = term181.
Proof. exact (fun_ext (fun m : nat => @lem7041974 m)). Qed.
Lemma lem7041976 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7041977 : term134 = term182.
Proof. exact (MK_COMB (@lem7041976) (@lem7041975)). Qed.
Lemma lem7041979 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term135 A P Q) = (term136 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7041980 (P : nat -> Prop) (Q : nat -> Prop) : (term137 P Q) = (term138 P Q).
Proof. exact (@lem7041979 nat P Q). Qed.
Lemma lem7041981 : term183 = term184.
Proof. exact (@lem7041980 term185 term186). Qed.
Lemma lem7041982 (m : nat) : (term187 m) = (term174 m).
Proof. exact (eq_refl (term187 m)). Qed.
Lemma lem7041983 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7041984 (m : nat) : (term188 m) = (term176 m).
Proof. exact (MK_COMB (@lem7041983) (@lem7041982 m)). Qed.
Lemma lem7041985 (m : nat) : (term189 m) = (term179 m).
Proof. exact (eq_refl (term189 m)). Qed.
Lemma lem7041986 (m : nat) : (term190 m) = (term180 m).
Proof. exact (MK_COMB (@lem7041984 m) (@lem7041985 m)). Qed.
Lemma lem7041987 : term191 = term181.
Proof. exact (fun_ext (fun m : nat => @lem7041986 m)). Qed.
Lemma lem7041988 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7041989 : term183 = term182.
Proof. exact (MK_COMB (@lem7041988) (@lem7041987)). Qed.
Lemma lem7041990 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7041991 : term192 = term193.
Proof. exact (MK_COMB (@lem7041990) (@lem7041989)). Qed.
Lemma lem7041992 (m : nat) : (term187 m) = (term174 m).
Proof. exact (eq_refl (term187 m)). Qed.
Lemma lem7041993 : term194 = term185.
Proof. exact (fun_ext (fun m : nat => @lem7041992 m)). Qed.
Lemma lem7041994 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7041995 : term195 = term196.
Proof. exact (MK_COMB (@lem7041994) (@lem7041993)). Qed.
Lemma lem7041996 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7041997 : term197 = term198.
Proof. exact (MK_COMB (@lem7041996) (@lem7041995)). Qed.
Lemma lem7041998 (m : nat) : (term189 m) = (term179 m).
Proof. exact (eq_refl (term189 m)). Qed.
Lemma lem7041999 : term199 = term186.
Proof. exact (fun_ext (fun m : nat => @lem7041998 m)). Qed.
Lemma lem7042000 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7042001 : term200 = term201.
Proof. exact (MK_COMB (@lem7042000) (@lem7041999)). Qed.
Lemma lem7042002 : term184 = term202.
Proof. exact (MK_COMB (@lem7041997) (@lem7042001)). Qed.
Lemma lem7042003 : (term183 = term184) = (term182 = term202).
Proof. exact (MK_COMB (@lem7041991) (@lem7042002)). Qed.
Lemma lem7042004 : term182 = term202.
Proof. exact (EQ_MP (@lem7042003) (@lem7041981)). Qed.
Lemma lem7042119 : term134 = term202.
Proof. exact (TRANS (@lem7041977) (@lem7042004)). Qed.
Lemma lem7042120 : term62 = term202.
Proof. exact (TRANS (@lem7041708) (@lem7042119)). Qed.
Lemma lem7042121 (h1 : term62) : term202.
Proof. exact (EQ_MP (@lem7042120) (@lem7041496 h1)). Qed.
Lemma lem7042148 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) (x : _127166) : (term203 _127166 s f g x) = (term204 _127166 s f g x).
Proof. exact (@lem17362 (@IN _127166 x s) ((f x) = (g x))). Qed.
Lemma lem7042149 {_127166 : Type'} (P : _127166 -> Prop) : (term205 _127166 P) = (term206 _127166 P).
Proof. exact (@lem18392 _127166 P). Qed.
Lemma lem7042150 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) : (term207 _127166 s f g) = (term208 _127166 s f g).
Proof. exact (@lem7042149 _127166 (term40 _127166 s f g)). Qed.
Lemma lem7042151 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) (x : _127166) : (term209 _127166 s f g x) = (term39 _127166 s f g x).
Proof. exact (eq_refl (term209 _127166 s f g x)). Qed.
Lemma lem7042152 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7042153 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) (x : _127166) : (term210 _127166 s f g x) = (term203 _127166 s f g x).
Proof. exact (MK_COMB (@lem7042152) (@lem7042151 _127166 s f g x)). Qed.
Lemma lem7042154 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) (x : _127166) : (term210 _127166 s f g x) = (term204 _127166 s f g x).
Proof. exact (TRANS (@lem7042153 _127166 s f g x) (@lem7042148 _127166 s f g x)). Qed.
Lemma lem7042155 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) : (term211 _127166 s f g) = (term212 _127166 s f g).
Proof. exact (fun_ext (fun x : _127166 => @lem7042154 _127166 s f g x)). Qed.
Lemma lem7042156 {_127166 : Type'} : (@ex _127166) = (@ex _127166).
Proof. exact (eq_refl (@ex _127166)). Qed.
Lemma lem7042157 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) : (term208 _127166 s f g) = (term213 _127166 s f g).
Proof. exact (MK_COMB (@lem7042156 _127166) (@lem7042155 _127166 s f g)). Qed.
Lemma lem7042158 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) : (term207 _127166 s f g) = (term213 _127166 s f g).
Proof. exact (TRANS (@lem7042150 _127166 s f g) (@lem7042157 _127166 s f g)). Qed.
Lemma lem7042159 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : ((@nsum _127166 s f) = (@nsum _127166 s g)) = ((@nsum _127166 s f) = (@nsum _127166 s g)).
Proof. exact (eq_refl ((@nsum _127166 s f) = (@nsum _127166 s g))). Qed.
Lemma lem7042160 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7042161 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) : (term214 _127166 s f g) = (term215 _127166 s f g).
Proof. exact (MK_COMB (@lem7042160) (@lem7042158 _127166 s f g)). Qed.
Lemma lem7042162 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : (term216 _127166 f s g) = (term217 _127166 f s g).
Proof. exact (MK_COMB (@lem7042161 _127166 s f g) (@lem7042159 _127166 f s g)). Qed.
Lemma lem7042163 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : (term43 _127166 f s g) = (term216 _127166 f s g).
Proof. exact (@lem17265 (term41 _127166 s f g) ((@nsum _127166 s f) = (@nsum _127166 s g))). Qed.
Lemma lem7042164 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : (term43 _127166 f s g) = (term217 _127166 f s g).
Proof. exact (TRANS (@lem7042163 _127166 f s g) (@lem7042162 _127166 f s g)). Qed.
Lemma lem7042165 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) : (term44 _127166 f g) = (term218 _127166 f g).
Proof. exact (fun_ext (fun s : _127166 -> Prop => @lem7042164 _127166 f s g)). Qed.
Lemma lem7042166 {_127166 : Type'} : (@all (_127166 -> Prop)) = (@all (_127166 -> Prop)).
Proof. exact (eq_refl (@all (_127166 -> Prop))). Qed.
Lemma lem7042167 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) : (term45 _127166 f g) = (term219 _127166 f g).
Proof. exact (MK_COMB (@lem7042166 _127166) (@lem7042165 _127166 f g)). Qed.
Lemma lem7042168 {_127166 : Type'} (f : _127166 -> nat) : (term46 _127166 f) = (term220 _127166 f).
Proof. exact (fun_ext (fun g : _127166 -> nat => @lem7042167 _127166 f g)). Qed.
Lemma lem7042169 {_127166 : Type'} : (@all (_127166 -> nat)) = (@all (_127166 -> nat)).
Proof. exact (eq_refl (@all (_127166 -> nat))). Qed.
Lemma lem7042170 {_127166 : Type'} (f : _127166 -> nat) : (term47 _127166 f) = (term221 _127166 f).
Proof. exact (MK_COMB (@lem7042169 _127166) (@lem7042168 _127166 f)). Qed.
Lemma lem7042171 {_127166 : Type'} : (term48 _127166) = (term222 _127166).
Proof. exact (fun_ext (fun f : _127166 -> nat => @lem7042170 _127166 f)). Qed.
Lemma lem7042172 {_127166 : Type'} : (@all (_127166 -> nat)) = (@all (_127166 -> nat)).
Proof. exact (eq_refl (@all (_127166 -> nat))). Qed.
Lemma lem7042173 {_127166 : Type'} : (term49 _127166) = (term223 _127166).
Proof. exact (MK_COMB (@lem7042172 _127166) (@lem7042171 _127166)). Qed.
Lemma lem7042280 {A : Type'} (P : A -> Prop) (Q : Prop) : (term224 A P Q) = (term225 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7042281 {_127166 : Type'} (P : _127166 -> Prop) (Q : Prop) : (term224 _127166 P Q) = (term225 _127166 P Q).
Proof. exact (@lem7042280 _127166 P Q). Qed.
Lemma lem7042282 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : (term226 _127166 f s g) = (term227 _127166 f s g).
Proof. exact (@lem7042281 _127166 (term212 _127166 s f g) ((@nsum _127166 s f) = (@nsum _127166 s g))). Qed.
Lemma lem7042283 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) (x : _127166) : (term228 _127166 s f g x) = (term204 _127166 s f g x).
Proof. exact (eq_refl (term228 _127166 s f g x)). Qed.
Lemma lem7042284 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) : (term229 _127166 s f g) = (term212 _127166 s f g).
Proof. exact (fun_ext (fun x : _127166 => @lem7042283 _127166 s f g x)). Qed.
Lemma lem7042285 {_127166 : Type'} : (@ex _127166) = (@ex _127166).
Proof. exact (eq_refl (@ex _127166)). Qed.
Lemma lem7042286 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) : (term230 _127166 s f g) = (term213 _127166 s f g).
Proof. exact (MK_COMB (@lem7042285 _127166) (@lem7042284 _127166 s f g)). Qed.
Lemma lem7042287 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7042288 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) : (term231 _127166 s f g) = (term215 _127166 s f g).
Proof. exact (MK_COMB (@lem7042287) (@lem7042286 _127166 s f g)). Qed.
Lemma lem7042289 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : ((@nsum _127166 s f) = (@nsum _127166 s g)) = ((@nsum _127166 s f) = (@nsum _127166 s g)).
Proof. exact (eq_refl ((@nsum _127166 s f) = (@nsum _127166 s g))). Qed.
Lemma lem7042290 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : (term226 _127166 f s g) = (term217 _127166 f s g).
Proof. exact (MK_COMB (@lem7042288 _127166 s f g) (@lem7042289 _127166 f s g)). Qed.
Lemma lem7042291 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7042292 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : (term232 _127166 f s g) = (term233 _127166 f s g).
Proof. exact (MK_COMB (@lem7042291) (@lem7042290 _127166 f s g)). Qed.
Lemma lem7042293 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) (x : _127166) : (term228 _127166 s f g x) = (term204 _127166 s f g x).
Proof. exact (eq_refl (term228 _127166 s f g x)). Qed.
Lemma lem7042294 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7042295 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) (x : _127166) : (term234 _127166 s f g x) = (term235 _127166 s f g x).
Proof. exact (MK_COMB (@lem7042294) (@lem7042293 _127166 s f g x)). Qed.
Lemma lem7042296 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : ((@nsum _127166 s f) = (@nsum _127166 s g)) = ((@nsum _127166 s f) = (@nsum _127166 s g)).
Proof. exact (eq_refl ((@nsum _127166 s f) = (@nsum _127166 s g))). Qed.
Lemma lem7042297 {_127166 : Type'} (x : _127166) (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : (term236 _127166 x f s g) = (term237 _127166 x f s g).
Proof. exact (MK_COMB (@lem7042295 _127166 s f g x) (@lem7042296 _127166 f s g)). Qed.
Lemma lem7042298 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : (term238 _127166 f s g) = (term239 _127166 f s g).
Proof. exact (fun_ext (fun x : _127166 => @lem7042297 _127166 x f s g)). Qed.
Lemma lem7042299 {_127166 : Type'} : (@ex _127166) = (@ex _127166).
Proof. exact (eq_refl (@ex _127166)). Qed.
Lemma lem7042300 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : (term227 _127166 f s g) = (term240 _127166 f s g).
Proof. exact (MK_COMB (@lem7042299 _127166) (@lem7042298 _127166 f s g)). Qed.
Lemma lem7042301 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : ((term226 _127166 f s g) = (term227 _127166 f s g)) = ((term217 _127166 f s g) = (term240 _127166 f s g)).
Proof. exact (MK_COMB (@lem7042292 _127166 f s g) (@lem7042300 _127166 f s g)). Qed.
Lemma lem7042302 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : (term217 _127166 f s g) = (term240 _127166 f s g).
Proof. exact (EQ_MP (@lem7042301 _127166 f s g) (@lem7042282 _127166 f s g)). Qed.
Lemma lem7042303 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) : (term218 _127166 f g) = (term241 _127166 f g).
Proof. exact (fun_ext (fun s : _127166 -> Prop => @lem7042302 _127166 f s g)). Qed.
Lemma lem7042304 {_127166 : Type'} : (@all (_127166 -> Prop)) = (@all (_127166 -> Prop)).
Proof. exact (eq_refl (@all (_127166 -> Prop))). Qed.
Lemma lem7042305 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) : (term219 _127166 f g) = (term242 _127166 f g).
Proof. exact (MK_COMB (@lem7042304 _127166) (@lem7042303 _127166 f g)). Qed.
Lemma lem7042307 {A B : Type'} (P : type1413 A B) : (term243 A B P) = (term244 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7042308 {_127166 : Type'} (P : type672 _127166) : (term245 _127166 P) = (term246 _127166 P).
Proof. exact (@lem7042307 (_127166 -> Prop) _127166 P). Qed.
Lemma lem7042309 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) : (term247 _127166 f g) = (term248 _127166 f g).
Proof. exact (@lem7042308 _127166 (term249 _127166 f g)). Qed.
Lemma lem7042310 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : (term250 _127166 f g s) = (term239 _127166 f s g).
Proof. exact (eq_refl (term250 _127166 f g s)). Qed.
Lemma lem7042311 {_127166 : Type'} (x : _127166) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7042312 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) (x : _127166) : (term251 _127166 f g s x) = (term252 _127166 f s g x).
Proof. exact (MK_COMB (@lem7042310 _127166 f s g) (@lem7042311 _127166 x)). Qed.
Lemma lem7042313 {_127166 : Type'} (x : _127166) (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : (term252 _127166 f s g x) = (term237 _127166 x f s g).
Proof. exact (eq_refl (term252 _127166 f s g x)). Qed.
Lemma lem7042314 {_127166 : Type'} (x : _127166) (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : (term251 _127166 f g s x) = (term237 _127166 x f s g).
Proof. exact (TRANS (@lem7042312 _127166 f s g x) (@lem7042313 _127166 x f s g)). Qed.
Lemma lem7042315 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : (term253 _127166 f g s) = (term239 _127166 f s g).
Proof. exact (fun_ext (fun x : _127166 => @lem7042314 _127166 x f s g)). Qed.
Lemma lem7042316 {_127166 : Type'} : (@ex _127166) = (@ex _127166).
Proof. exact (eq_refl (@ex _127166)). Qed.
Lemma lem7042317 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : (term254 _127166 f g s) = (term240 _127166 f s g).
Proof. exact (MK_COMB (@lem7042316 _127166) (@lem7042315 _127166 f s g)). Qed.
Lemma lem7042318 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) : (term255 _127166 f g) = (term241 _127166 f g).
Proof. exact (fun_ext (fun s : _127166 -> Prop => @lem7042317 _127166 f s g)). Qed.
Lemma lem7042319 {_127166 : Type'} : (@all (_127166 -> Prop)) = (@all (_127166 -> Prop)).
Proof. exact (eq_refl (@all (_127166 -> Prop))). Qed.
Lemma lem7042320 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) : (term247 _127166 f g) = (term242 _127166 f g).
Proof. exact (MK_COMB (@lem7042319 _127166) (@lem7042318 _127166 f g)). Qed.
Lemma lem7042321 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7042322 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) : (term256 _127166 f g) = (term257 _127166 f g).
Proof. exact (MK_COMB (@lem7042321) (@lem7042320 _127166 f g)). Qed.
Lemma lem7042323 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : (term250 _127166 f g s) = (term239 _127166 f s g).
Proof. exact (eq_refl (term250 _127166 f g s)). Qed.
Lemma lem7042324 {_127166 : Type'} (x : type684 _127166) (s : _127166 -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem7042325 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) (x : type684 _127166) (s : _127166 -> Prop) : (term258 _127166 f g x s) = (term259 _127166 f g x s).
Proof. exact (MK_COMB (@lem7042323 _127166 f s g) (@lem7042324 _127166 x s)). Qed.
Lemma lem7042326 {_127166 : Type'} (x : type684 _127166) (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : (term259 _127166 f g x s) = (term260 _127166 x f s g).
Proof. exact (eq_refl (term259 _127166 f g x s)). Qed.
Lemma lem7042327 {_127166 : Type'} (x : type684 _127166) (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : (term258 _127166 f g x s) = (term260 _127166 x f s g).
Proof. exact (TRANS (@lem7042325 _127166 f g x s) (@lem7042326 _127166 x f s g)). Qed.
Lemma lem7042328 {_127166 : Type'} (x : type684 _127166) (f : _127166 -> nat) (g : _127166 -> nat) : (term261 _127166 f g x) = (term262 _127166 x f g).
Proof. exact (fun_ext (fun s : _127166 -> Prop => @lem7042327 _127166 x f s g)). Qed.
Lemma lem7042329 {_127166 : Type'} : (@all (_127166 -> Prop)) = (@all (_127166 -> Prop)).
Proof. exact (eq_refl (@all (_127166 -> Prop))). Qed.
Lemma lem7042330 {_127166 : Type'} (x : type684 _127166) (f : _127166 -> nat) (g : _127166 -> nat) : (term263 _127166 f g x) = (term264 _127166 x f g).
Proof. exact (MK_COMB (@lem7042329 _127166) (@lem7042328 _127166 x f g)). Qed.
Lemma lem7042331 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) : (term265 _127166 f g) = (term266 _127166 f g).
Proof. exact (fun_ext (fun x : type684 _127166 => @lem7042330 _127166 x f g)). Qed.
Lemma lem7042332 {_127166 : Type'} : (@ex ((_127166 -> Prop) -> _127166)) = (@ex ((_127166 -> Prop) -> _127166)).
Proof. exact (eq_refl (@ex ((_127166 -> Prop) -> _127166))). Qed.
Lemma lem7042333 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) : (term248 _127166 f g) = (term267 _127166 f g).
Proof. exact (MK_COMB (@lem7042332 _127166) (@lem7042331 _127166 f g)). Qed.
Lemma lem7042334 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) : ((term247 _127166 f g) = (term248 _127166 f g)) = ((term242 _127166 f g) = (term267 _127166 f g)).
Proof. exact (MK_COMB (@lem7042322 _127166 f g) (@lem7042333 _127166 f g)). Qed.
Lemma lem7042335 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) : (term242 _127166 f g) = (term267 _127166 f g).
Proof. exact (EQ_MP (@lem7042334 _127166 f g) (@lem7042309 _127166 f g)). Qed.
Lemma lem7042336 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) : (term219 _127166 f g) = (term267 _127166 f g).
Proof. exact (TRANS (@lem7042305 _127166 f g) (@lem7042335 _127166 f g)). Qed.
Lemma lem7042337 {_127166 : Type'} (f : _127166 -> nat) : (term220 _127166 f) = (term268 _127166 f).
Proof. exact (fun_ext (fun g : _127166 -> nat => @lem7042336 _127166 f g)). Qed.
Lemma lem7042338 {_127166 : Type'} : (@all (_127166 -> nat)) = (@all (_127166 -> nat)).
Proof. exact (eq_refl (@all (_127166 -> nat))). Qed.
Lemma lem7042339 {_127166 : Type'} (f : _127166 -> nat) : (term221 _127166 f) = (term269 _127166 f).
Proof. exact (MK_COMB (@lem7042338 _127166) (@lem7042337 _127166 f)). Qed.
Lemma lem7042341 {A B : Type'} (P : type1413 A B) : (term243 A B P) = (term244 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7042342 {_127166 : Type'} (P : type690 _127166) : (term270 _127166 P) = (term271 _127166 P).
Proof. exact (@lem7042341 (_127166 -> nat) (type684 _127166) P). Qed.
Lemma lem7042343 {_127166 : Type'} (f : _127166 -> nat) : (term272 _127166 f) = (term273 _127166 f).
Proof. exact (@lem7042342 _127166 (term274 _127166 f)). Qed.
Lemma lem7042344 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) : (term275 _127166 f g) = (term266 _127166 f g).
Proof. exact (eq_refl (term275 _127166 f g)). Qed.
Lemma lem7042345 {_127166 : Type'} (x : type684 _127166) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7042346 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) (x : type684 _127166) : (term276 _127166 f g x) = (term277 _127166 f g x).
Proof. exact (MK_COMB (@lem7042344 _127166 f g) (@lem7042345 _127166 x)). Qed.
Lemma lem7042347 {_127166 : Type'} (x : type684 _127166) (f : _127166 -> nat) (g : _127166 -> nat) : (term277 _127166 f g x) = (term264 _127166 x f g).
Proof. exact (eq_refl (term277 _127166 f g x)). Qed.
Lemma lem7042348 {_127166 : Type'} (x : type684 _127166) (f : _127166 -> nat) (g : _127166 -> nat) : (term276 _127166 f g x) = (term264 _127166 x f g).
Proof. exact (TRANS (@lem7042346 _127166 f g x) (@lem7042347 _127166 x f g)). Qed.
Lemma lem7042349 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) : (term278 _127166 f g) = (term266 _127166 f g).
Proof. exact (fun_ext (fun x : type684 _127166 => @lem7042348 _127166 x f g)). Qed.
Lemma lem7042350 {_127166 : Type'} : (@ex ((_127166 -> Prop) -> _127166)) = (@ex ((_127166 -> Prop) -> _127166)).
Proof. exact (eq_refl (@ex ((_127166 -> Prop) -> _127166))). Qed.
Lemma lem7042351 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) : (term279 _127166 f g) = (term267 _127166 f g).
Proof. exact (MK_COMB (@lem7042350 _127166) (@lem7042349 _127166 f g)). Qed.
Lemma lem7042352 {_127166 : Type'} (f : _127166 -> nat) : (term280 _127166 f) = (term268 _127166 f).
Proof. exact (fun_ext (fun g : _127166 -> nat => @lem7042351 _127166 f g)). Qed.
Lemma lem7042353 {_127166 : Type'} : (@all (_127166 -> nat)) = (@all (_127166 -> nat)).
Proof. exact (eq_refl (@all (_127166 -> nat))). Qed.
Lemma lem7042354 {_127166 : Type'} (f : _127166 -> nat) : (term272 _127166 f) = (term269 _127166 f).
Proof. exact (MK_COMB (@lem7042353 _127166) (@lem7042352 _127166 f)). Qed.
Lemma lem7042355 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7042356 {_127166 : Type'} (f : _127166 -> nat) : (term281 _127166 f) = (term282 _127166 f).
Proof. exact (MK_COMB (@lem7042355) (@lem7042354 _127166 f)). Qed.
Lemma lem7042357 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) : (term275 _127166 f g) = (term266 _127166 f g).
Proof. exact (eq_refl (term275 _127166 f g)). Qed.
Lemma lem7042358 {_127166 : Type'} (x : type694 _127166) (g : _127166 -> nat) : (x g) = (x g).
Proof. exact (eq_refl (x g)). Qed.
Lemma lem7042359 {_127166 : Type'} (f : _127166 -> nat) (x : type694 _127166) (g : _127166 -> nat) : (term283 _127166 f x g) = (term284 _127166 f x g).
Proof. exact (MK_COMB (@lem7042357 _127166 f g) (@lem7042358 _127166 x g)). Qed.
Lemma lem7042360 {_127166 : Type'} (x : type694 _127166) (f : _127166 -> nat) (g : _127166 -> nat) : (term284 _127166 f x g) = (term285 _127166 x f g).
Proof. exact (eq_refl (term284 _127166 f x g)). Qed.
Lemma lem7042361 {_127166 : Type'} (x : type694 _127166) (f : _127166 -> nat) (g : _127166 -> nat) : (term283 _127166 f x g) = (term285 _127166 x f g).
Proof. exact (TRANS (@lem7042359 _127166 f x g) (@lem7042360 _127166 x f g)). Qed.
Lemma lem7042362 {_127166 : Type'} (x : type694 _127166) (f : _127166 -> nat) : (term286 _127166 f x) = (term287 _127166 x f).
Proof. exact (fun_ext (fun g : _127166 -> nat => @lem7042361 _127166 x f g)). Qed.
Lemma lem7042363 {_127166 : Type'} : (@all (_127166 -> nat)) = (@all (_127166 -> nat)).
Proof. exact (eq_refl (@all (_127166 -> nat))). Qed.
Lemma lem7042364 {_127166 : Type'} (x : type694 _127166) (f : _127166 -> nat) : (term288 _127166 f x) = (term289 _127166 x f).
Proof. exact (MK_COMB (@lem7042363 _127166) (@lem7042362 _127166 x f)). Qed.
Lemma lem7042365 {_127166 : Type'} (f : _127166 -> nat) : (term290 _127166 f) = (term291 _127166 f).
Proof. exact (fun_ext (fun x : type694 _127166 => @lem7042364 _127166 x f)). Qed.
Lemma lem7042366 {_127166 : Type'} : (@ex ((_127166 -> nat) -> (_127166 -> Prop) -> _127166)) = (@ex ((_127166 -> nat) -> (_127166 -> Prop) -> _127166)).
Proof. exact (eq_refl (@ex ((_127166 -> nat) -> (_127166 -> Prop) -> _127166))). Qed.
Lemma lem7042367 {_127166 : Type'} (f : _127166 -> nat) : (term273 _127166 f) = (term292 _127166 f).
Proof. exact (MK_COMB (@lem7042366 _127166) (@lem7042365 _127166 f)). Qed.
Lemma lem7042368 {_127166 : Type'} (f : _127166 -> nat) : ((term272 _127166 f) = (term273 _127166 f)) = ((term269 _127166 f) = (term292 _127166 f)).
Proof. exact (MK_COMB (@lem7042356 _127166 f) (@lem7042367 _127166 f)). Qed.
Lemma lem7042369 {_127166 : Type'} (f : _127166 -> nat) : (term269 _127166 f) = (term292 _127166 f).
Proof. exact (EQ_MP (@lem7042368 _127166 f) (@lem7042343 _127166 f)). Qed.
Lemma lem7042370 {_127166 : Type'} (f : _127166 -> nat) : (term221 _127166 f) = (term292 _127166 f).
Proof. exact (TRANS (@lem7042339 _127166 f) (@lem7042369 _127166 f)). Qed.
Lemma lem7042371 {_127166 : Type'} : (term222 _127166) = (term293 _127166).
Proof. exact (fun_ext (fun f : _127166 -> nat => @lem7042370 _127166 f)). Qed.
Lemma lem7042372 {_127166 : Type'} : (@all (_127166 -> nat)) = (@all (_127166 -> nat)).
Proof. exact (eq_refl (@all (_127166 -> nat))). Qed.
Lemma lem7042373 {_127166 : Type'} : (term223 _127166) = (term294 _127166).
Proof. exact (MK_COMB (@lem7042372 _127166) (@lem7042371 _127166)). Qed.
Lemma lem7042375 {A B : Type'} (P : type1413 A B) : (term243 A B P) = (term244 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7042376 {_127166 : Type'} (P : type691 _127166) : (term295 _127166 P) = (term296 _127166 P).
Proof. exact (@lem7042375 (_127166 -> nat) (type694 _127166) P). Qed.
Lemma lem7042377 {_127166 : Type'} : (term297 _127166) = (term298 _127166).
Proof. exact (@lem7042376 _127166 (term299 _127166)). Qed.
Lemma lem7042378 {_127166 : Type'} (f : _127166 -> nat) : (term300 _127166 f) = (term291 _127166 f).
Proof. exact (eq_refl (term300 _127166 f)). Qed.
Lemma lem7042379 {_127166 : Type'} (x : type694 _127166) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7042380 {_127166 : Type'} (f : _127166 -> nat) (x : type694 _127166) : (term301 _127166 f x) = (term302 _127166 f x).
Proof. exact (MK_COMB (@lem7042378 _127166 f) (@lem7042379 _127166 x)). Qed.
Lemma lem7042381 {_127166 : Type'} (x : type694 _127166) (f : _127166 -> nat) : (term302 _127166 f x) = (term289 _127166 x f).
Proof. exact (eq_refl (term302 _127166 f x)). Qed.
Lemma lem7042382 {_127166 : Type'} (x : type694 _127166) (f : _127166 -> nat) : (term301 _127166 f x) = (term289 _127166 x f).
Proof. exact (TRANS (@lem7042380 _127166 f x) (@lem7042381 _127166 x f)). Qed.
Lemma lem7042383 {_127166 : Type'} (f : _127166 -> nat) : (term303 _127166 f) = (term291 _127166 f).
Proof. exact (fun_ext (fun x : type694 _127166 => @lem7042382 _127166 x f)). Qed.
Lemma lem7042384 {_127166 : Type'} : (@ex ((_127166 -> nat) -> (_127166 -> Prop) -> _127166)) = (@ex ((_127166 -> nat) -> (_127166 -> Prop) -> _127166)).
Proof. exact (eq_refl (@ex ((_127166 -> nat) -> (_127166 -> Prop) -> _127166))). Qed.
Lemma lem7042385 {_127166 : Type'} (f : _127166 -> nat) : (term304 _127166 f) = (term292 _127166 f).
Proof. exact (MK_COMB (@lem7042384 _127166) (@lem7042383 _127166 f)). Qed.
Lemma lem7042386 {_127166 : Type'} : (term305 _127166) = (term293 _127166).
Proof. exact (fun_ext (fun f : _127166 -> nat => @lem7042385 _127166 f)). Qed.
Lemma lem7042387 {_127166 : Type'} : (@all (_127166 -> nat)) = (@all (_127166 -> nat)).
Proof. exact (eq_refl (@all (_127166 -> nat))). Qed.
Lemma lem7042388 {_127166 : Type'} : (term297 _127166) = (term294 _127166).
Proof. exact (MK_COMB (@lem7042387 _127166) (@lem7042386 _127166)). Qed.
Lemma lem7042389 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7042390 {_127166 : Type'} : (term306 _127166) = (term307 _127166).
Proof. exact (MK_COMB (@lem7042389) (@lem7042388 _127166)). Qed.
Lemma lem7042391 {_127166 : Type'} (f : _127166 -> nat) : (term300 _127166 f) = (term291 _127166 f).
Proof. exact (eq_refl (term300 _127166 f)). Qed.
Lemma lem7042392 {_127166 : Type'} (x : type695 _127166) (f : _127166 -> nat) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem7042393 {_127166 : Type'} (x : type695 _127166) (f : _127166 -> nat) : (term308 _127166 x f) = (term309 _127166 x f).
Proof. exact (MK_COMB (@lem7042391 _127166 f) (@lem7042392 _127166 x f)). Qed.
Lemma lem7042394 {_127166 : Type'} (x : type695 _127166) (f : _127166 -> nat) : (term309 _127166 x f) = (term310 _127166 x f).
Proof. exact (eq_refl (term309 _127166 x f)). Qed.
Lemma lem7042395 {_127166 : Type'} (x : type695 _127166) (f : _127166 -> nat) : (term308 _127166 x f) = (term310 _127166 x f).
Proof. exact (TRANS (@lem7042393 _127166 x f) (@lem7042394 _127166 x f)). Qed.
Lemma lem7042396 {_127166 : Type'} (x : type695 _127166) : (term311 _127166 x) = (term312 _127166 x).
Proof. exact (fun_ext (fun f : _127166 -> nat => @lem7042395 _127166 x f)). Qed.
Lemma lem7042397 {_127166 : Type'} : (@all (_127166 -> nat)) = (@all (_127166 -> nat)).
Proof. exact (eq_refl (@all (_127166 -> nat))). Qed.
Lemma lem7042398 {_127166 : Type'} (x : type695 _127166) : (term313 _127166 x) = (term314 _127166 x).
Proof. exact (MK_COMB (@lem7042397 _127166) (@lem7042396 _127166 x)). Qed.
Lemma lem7042399 {_127166 : Type'} : (term315 _127166) = (term316 _127166).
Proof. exact (fun_ext (fun x : type695 _127166 => @lem7042398 _127166 x)). Qed.
Lemma lem7042400 {_127166 : Type'} : (@ex ((_127166 -> nat) -> (_127166 -> nat) -> (_127166 -> Prop) -> _127166)) = (@ex ((_127166 -> nat) -> (_127166 -> nat) -> (_127166 -> Prop) -> _127166)).
Proof. exact (eq_refl (@ex ((_127166 -> nat) -> (_127166 -> nat) -> (_127166 -> Prop) -> _127166))). Qed.
Lemma lem7042401 {_127166 : Type'} : (term298 _127166) = (term317 _127166).
Proof. exact (MK_COMB (@lem7042400 _127166) (@lem7042399 _127166)). Qed.
Lemma lem7042402 {_127166 : Type'} : ((term297 _127166) = (term298 _127166)) = ((term294 _127166) = (term317 _127166)).
Proof. exact (MK_COMB (@lem7042390 _127166) (@lem7042401 _127166)). Qed.
Lemma lem7042403 {_127166 : Type'} : (term294 _127166) = (term317 _127166).
Proof. exact (EQ_MP (@lem7042402 _127166) (@lem7042377 _127166)). Qed.
Lemma lem7042405 {_127166 : Type'} : (term223 _127166) = (term317 _127166).
Proof. exact (TRANS (@lem7042373 _127166) (@lem7042403 _127166)). Qed.
Lemma lem7042406 {_127166 : Type'} : (term49 _127166) = (term317 _127166).
Proof. exact (TRANS (@lem7042173 _127166) (@lem7042405 _127166)). Qed.
Lemma lem7042407 {_127166 : Type'} (h1 : term49 _127166) : term317 _127166.
Proof. exact (EQ_MP (@lem7042406 _127166) (@lem7041498 _127166 h1)). Qed.
Lemma lem7042414 (s : nat -> Prop) (f : nat -> nat) (g : nat -> nat) (x : nat) : (term318 s f g x) = (term319 s f g x).
Proof. exact (@lem17362 (@IN nat x s) ((f x) = (g x))). Qed.
Lemma lem7042415 (P : nat -> Prop) : (term90 P) = (term91 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem7042416 (s : nat -> Prop) (f : nat -> nat) (g : nat -> nat) : (term320 s f g) = (term321 s f g).
Proof. exact (@lem7042415 (term30 s f g)). Qed.
Lemma lem7042417 (s : nat -> Prop) (f : nat -> nat) (g : nat -> nat) (x : nat) : (term322 s f g x) = (term29 s f g x).
Proof. exact (eq_refl (term322 s f g x)). Qed.
Lemma lem7042418 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7042419 (s : nat -> Prop) (f : nat -> nat) (g : nat -> nat) (x : nat) : (term323 s f g x) = (term318 s f g x).
Proof. exact (MK_COMB (@lem7042418) (@lem7042417 s f g x)). Qed.
Lemma lem7042420 (s : nat -> Prop) (f : nat -> nat) (g : nat -> nat) (x : nat) : (term323 s f g x) = (term319 s f g x).
Proof. exact (TRANS (@lem7042419 s f g x) (@lem7042414 s f g x)). Qed.
Lemma lem7042421 (s : nat -> Prop) (f : nat -> nat) (g : nat -> nat) : (term324 s f g) = (term325 s f g).
Proof. exact (fun_ext (fun x : nat => @lem7042420 s f g x)). Qed.
Lemma lem7042422 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7042423 (s : nat -> Prop) (f : nat -> nat) (g : nat -> nat) : (term321 s f g) = (term326 s f g).
Proof. exact (MK_COMB (@lem7042422) (@lem7042421 s f g)). Qed.
Lemma lem7042424 (s : nat -> Prop) (f : nat -> nat) (g : nat -> nat) : (term320 s f g) = (term326 s f g).
Proof. exact (TRANS (@lem7042416 s f g) (@lem7042423 s f g)). Qed.
Lemma lem7042425 (f : nat -> nat) (s : nat -> Prop) (g : nat -> nat) : ((@nsum nat s f) = (@nsum nat s g)) = ((@nsum nat s f) = (@nsum nat s g)).
Proof. exact (eq_refl ((@nsum nat s f) = (@nsum nat s g))). Qed.
Lemma lem7042426 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7042427 (s : nat -> Prop) (f : nat -> nat) (g : nat -> nat) : (term327 s f g) = (term328 s f g).
Proof. exact (MK_COMB (@lem7042426) (@lem7042424 s f g)). Qed.
Lemma lem7042428 (f : nat -> nat) (s : nat -> Prop) (g : nat -> nat) : (term329 f s g) = (term330 f s g).
Proof. exact (MK_COMB (@lem7042427 s f g) (@lem7042425 f s g)). Qed.
Lemma lem7042429 (f : nat -> nat) (s : nat -> Prop) (g : nat -> nat) : (term33 f s g) = (term329 f s g).
Proof. exact (@lem17265 (term31 s f g) ((@nsum nat s f) = (@nsum nat s g))). Qed.
Lemma lem7042430 (f : nat -> nat) (s : nat -> Prop) (g : nat -> nat) : (term33 f s g) = (term330 f s g).
Proof. exact (TRANS (@lem7042429 f s g) (@lem7042428 f s g)). Qed.
Lemma lem7042431 (f : nat -> nat) (g : nat -> nat) : (term34 f g) = (term331 f g).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem7042430 f s g)). Qed.
Lemma lem7042432 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem7042433 (f : nat -> nat) (g : nat -> nat) : (term35 f g) = (term332 f g).
Proof. exact (MK_COMB (@lem7042432) (@lem7042431 f g)). Qed.
Lemma lem7042434 (f : nat -> nat) : (term36 f) = (term333 f).
Proof. exact (fun_ext (fun g : nat -> nat => @lem7042433 f g)). Qed.
Lemma lem7042435 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7042436 (f : nat -> nat) : (term37 f) = (term334 f).
Proof. exact (MK_COMB (@lem7042435) (@lem7042434 f)). Qed.
Lemma lem7042437 : term38 = term335.
Proof. exact (fun_ext (fun f : nat -> nat => @lem7042436 f)). Qed.
Lemma lem7042438 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7042439 : term11 = term336.
Proof. exact (MK_COMB (@lem7042438) (@lem7042437)). Qed.
Lemma lem7042546 {A : Type'} (P : A -> Prop) (Q : Prop) : (term224 A P Q) = (term225 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7042547 (P : nat -> Prop) (Q : Prop) : (term337 P Q) = (term338 P Q).
Proof. exact (@lem7042546 nat P Q). Qed.
Lemma lem7042548 (f : nat -> nat) (s : nat -> Prop) (g : nat -> nat) : (term339 f s g) = (term340 f s g).
Proof. exact (@lem7042547 (term325 s f g) ((@nsum nat s f) = (@nsum nat s g))). Qed.
Lemma lem7042549 (s : nat -> Prop) (f : nat -> nat) (g : nat -> nat) (x : nat) : (term341 s f g x) = (term319 s f g x).
Proof. exact (eq_refl (term341 s f g x)). Qed.
Lemma lem7042550 (s : nat -> Prop) (f : nat -> nat) (g : nat -> nat) : (term342 s f g) = (term325 s f g).
Proof. exact (fun_ext (fun x : nat => @lem7042549 s f g x)). Qed.
Lemma lem7042551 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7042552 (s : nat -> Prop) (f : nat -> nat) (g : nat -> nat) : (term343 s f g) = (term326 s f g).
Proof. exact (MK_COMB (@lem7042551) (@lem7042550 s f g)). Qed.
Lemma lem7042553 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7042554 (s : nat -> Prop) (f : nat -> nat) (g : nat -> nat) : (term344 s f g) = (term328 s f g).
Proof. exact (MK_COMB (@lem7042553) (@lem7042552 s f g)). Qed.
Lemma lem7042555 (f : nat -> nat) (s : nat -> Prop) (g : nat -> nat) : ((@nsum nat s f) = (@nsum nat s g)) = ((@nsum nat s f) = (@nsum nat s g)).
Proof. exact (eq_refl ((@nsum nat s f) = (@nsum nat s g))). Qed.
Lemma lem7042556 (f : nat -> nat) (s : nat -> Prop) (g : nat -> nat) : (term339 f s g) = (term330 f s g).
Proof. exact (MK_COMB (@lem7042554 s f g) (@lem7042555 f s g)). Qed.
Lemma lem7042557 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7042558 (f : nat -> nat) (s : nat -> Prop) (g : nat -> nat) : (term345 f s g) = (term346 f s g).
Proof. exact (MK_COMB (@lem7042557) (@lem7042556 f s g)). Qed.
Lemma lem7042559 (s : nat -> Prop) (f : nat -> nat) (g : nat -> nat) (x : nat) : (term341 s f g x) = (term319 s f g x).
Proof. exact (eq_refl (term341 s f g x)). Qed.
Lemma lem7042560 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7042561 (s : nat -> Prop) (f : nat -> nat) (g : nat -> nat) (x : nat) : (term347 s f g x) = (term348 s f g x).
Proof. exact (MK_COMB (@lem7042560) (@lem7042559 s f g x)). Qed.
Lemma lem7042562 (f : nat -> nat) (s : nat -> Prop) (g : nat -> nat) : ((@nsum nat s f) = (@nsum nat s g)) = ((@nsum nat s f) = (@nsum nat s g)).
Proof. exact (eq_refl ((@nsum nat s f) = (@nsum nat s g))). Qed.
Lemma lem7042563 (x : nat) (f : nat -> nat) (s : nat -> Prop) (g : nat -> nat) : (term349 x f s g) = (term350 x f s g).
Proof. exact (MK_COMB (@lem7042561 s f g x) (@lem7042562 f s g)). Qed.
Lemma lem7042564 (f : nat -> nat) (s : nat -> Prop) (g : nat -> nat) : (term351 f s g) = (term352 f s g).
Proof. exact (fun_ext (fun x : nat => @lem7042563 x f s g)). Qed.
Lemma lem7042565 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7042566 (f : nat -> nat) (s : nat -> Prop) (g : nat -> nat) : (term340 f s g) = (term353 f s g).
Proof. exact (MK_COMB (@lem7042565) (@lem7042564 f s g)). Qed.
Lemma lem7042567 (f : nat -> nat) (s : nat -> Prop) (g : nat -> nat) : ((term339 f s g) = (term340 f s g)) = ((term330 f s g) = (term353 f s g)).
Proof. exact (MK_COMB (@lem7042558 f s g) (@lem7042566 f s g)). Qed.
Lemma lem7042568 (f : nat -> nat) (s : nat -> Prop) (g : nat -> nat) : (term330 f s g) = (term353 f s g).
Proof. exact (EQ_MP (@lem7042567 f s g) (@lem7042548 f s g)). Qed.
Lemma lem7042569 (f : nat -> nat) (g : nat -> nat) : (term331 f g) = (term354 f g).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem7042568 f s g)). Qed.
Lemma lem7042570 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem7042571 (f : nat -> nat) (g : nat -> nat) : (term332 f g) = (term355 f g).
Proof. exact (MK_COMB (@lem7042570) (@lem7042569 f g)). Qed.
Lemma lem7042573 {A B : Type'} (P : type1413 A B) : (term243 A B P) = (term244 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7042574 (P : type991) : (term356 P) = (term357 P).
Proof. exact (@lem7042573 (nat -> Prop) nat P). Qed.
Lemma lem7042575 (f : nat -> nat) (g : nat -> nat) : (term358 f g) = (term359 f g).
Proof. exact (@lem7042574 (term360 f g)). Qed.
Lemma lem7042576 (f : nat -> nat) (s : nat -> Prop) (g : nat -> nat) : (term361 f g s) = (term352 f s g).
Proof. exact (eq_refl (term361 f g s)). Qed.
Lemma lem7042577 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7042578 (f : nat -> nat) (s : nat -> Prop) (g : nat -> nat) (x : nat) : (term362 f g s x) = (term363 f s g x).
Proof. exact (MK_COMB (@lem7042576 f s g) (@lem7042577 x)). Qed.
Lemma lem7042579 (x : nat) (f : nat -> nat) (s : nat -> Prop) (g : nat -> nat) : (term363 f s g x) = (term350 x f s g).
Proof. exact (eq_refl (term363 f s g x)). Qed.
Lemma lem7042580 (x : nat) (f : nat -> nat) (s : nat -> Prop) (g : nat -> nat) : (term362 f g s x) = (term350 x f s g).
Proof. exact (TRANS (@lem7042578 f s g x) (@lem7042579 x f s g)). Qed.
Lemma lem7042581 (f : nat -> nat) (s : nat -> Prop) (g : nat -> nat) : (term364 f g s) = (term352 f s g).
Proof. exact (fun_ext (fun x : nat => @lem7042580 x f s g)). Qed.
Lemma lem7042582 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7042583 (f : nat -> nat) (s : nat -> Prop) (g : nat -> nat) : (term365 f g s) = (term353 f s g).
Proof. exact (MK_COMB (@lem7042582) (@lem7042581 f s g)). Qed.
Lemma lem7042584 (f : nat -> nat) (g : nat -> nat) : (term366 f g) = (term354 f g).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem7042583 f s g)). Qed.
Lemma lem7042585 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem7042586 (f : nat -> nat) (g : nat -> nat) : (term358 f g) = (term355 f g).
Proof. exact (MK_COMB (@lem7042585) (@lem7042584 f g)). Qed.
Lemma lem7042587 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7042588 (f : nat -> nat) (g : nat -> nat) : (term367 f g) = (term368 f g).
Proof. exact (MK_COMB (@lem7042587) (@lem7042586 f g)). Qed.
Lemma lem7042589 (f : nat -> nat) (s : nat -> Prop) (g : nat -> nat) : (term361 f g s) = (term352 f s g).
Proof. exact (eq_refl (term361 f g s)). Qed.
Lemma lem7042590 (x : type994) (s : nat -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem7042591 (f : nat -> nat) (g : nat -> nat) (x : type994) (s : nat -> Prop) : (term369 f g x s) = (term370 f g x s).
Proof. exact (MK_COMB (@lem7042589 f s g) (@lem7042590 x s)). Qed.
Lemma lem7042592 (x : type994) (f : nat -> nat) (s : nat -> Prop) (g : nat -> nat) : (term370 f g x s) = (term371 x f s g).
Proof. exact (eq_refl (term370 f g x s)). Qed.
Lemma lem7042593 (x : type994) (f : nat -> nat) (s : nat -> Prop) (g : nat -> nat) : (term369 f g x s) = (term371 x f s g).
Proof. exact (TRANS (@lem7042591 f g x s) (@lem7042592 x f s g)). Qed.
Lemma lem7042594 (x : type994) (f : nat -> nat) (g : nat -> nat) : (term372 f g x) = (term373 x f g).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem7042593 x f s g)). Qed.
Lemma lem7042595 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem7042596 (x : type994) (f : nat -> nat) (g : nat -> nat) : (term374 f g x) = (term375 x f g).
Proof. exact (MK_COMB (@lem7042595) (@lem7042594 x f g)). Qed.
Lemma lem7042597 (f : nat -> nat) (g : nat -> nat) : (term376 f g) = (term377 f g).
Proof. exact (fun_ext (fun x : type994 => @lem7042596 x f g)). Qed.
Lemma lem7042598 : (@ex ((nat -> Prop) -> nat)) = (@ex ((nat -> Prop) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> nat))). Qed.
Lemma lem7042599 (f : nat -> nat) (g : nat -> nat) : (term359 f g) = (term378 f g).
Proof. exact (MK_COMB (@lem7042598) (@lem7042597 f g)). Qed.
Lemma lem7042600 (f : nat -> nat) (g : nat -> nat) : ((term358 f g) = (term359 f g)) = ((term355 f g) = (term378 f g)).
Proof. exact (MK_COMB (@lem7042588 f g) (@lem7042599 f g)). Qed.
Lemma lem7042601 (f : nat -> nat) (g : nat -> nat) : (term355 f g) = (term378 f g).
Proof. exact (EQ_MP (@lem7042600 f g) (@lem7042575 f g)). Qed.
Lemma lem7042602 (f : nat -> nat) (g : nat -> nat) : (term332 f g) = (term378 f g).
Proof. exact (TRANS (@lem7042571 f g) (@lem7042601 f g)). Qed.
Lemma lem7042603 (f : nat -> nat) : (term333 f) = (term379 f).
Proof. exact (fun_ext (fun g : nat -> nat => @lem7042602 f g)). Qed.
Lemma lem7042604 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7042605 (f : nat -> nat) : (term334 f) = (term380 f).
Proof. exact (MK_COMB (@lem7042604) (@lem7042603 f)). Qed.
Lemma lem7042607 {A B : Type'} (P : type1413 A B) : (term243 A B P) = (term244 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7042608 (P : type995) : (term381 P) = (term382 P).
Proof. exact (@lem7042607 (nat -> nat) type994 P). Qed.
Lemma lem7042609 (f : nat -> nat) : (term383 f) = (term384 f).
Proof. exact (@lem7042608 (term385 f)). Qed.
Lemma lem7042610 (f : nat -> nat) (g : nat -> nat) : (term386 f g) = (term377 f g).
Proof. exact (eq_refl (term386 f g)). Qed.
Lemma lem7042611 (x : type994) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7042612 (f : nat -> nat) (g : nat -> nat) (x : type994) : (term387 f g x) = (term388 f g x).
Proof. exact (MK_COMB (@lem7042610 f g) (@lem7042611 x)). Qed.
Lemma lem7042613 (x : type994) (f : nat -> nat) (g : nat -> nat) : (term388 f g x) = (term375 x f g).
Proof. exact (eq_refl (term388 f g x)). Qed.
Lemma lem7042614 (x : type994) (f : nat -> nat) (g : nat -> nat) : (term387 f g x) = (term375 x f g).
Proof. exact (TRANS (@lem7042612 f g x) (@lem7042613 x f g)). Qed.
Lemma lem7042615 (f : nat -> nat) (g : nat -> nat) : (term389 f g) = (term377 f g).
Proof. exact (fun_ext (fun x : type994 => @lem7042614 x f g)). Qed.
Lemma lem7042616 : (@ex ((nat -> Prop) -> nat)) = (@ex ((nat -> Prop) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> Prop) -> nat))). Qed.
Lemma lem7042617 (f : nat -> nat) (g : nat -> nat) : (term390 f g) = (term378 f g).
Proof. exact (MK_COMB (@lem7042616) (@lem7042615 f g)). Qed.
Lemma lem7042618 (f : nat -> nat) : (term391 f) = (term379 f).
Proof. exact (fun_ext (fun g : nat -> nat => @lem7042617 f g)). Qed.
Lemma lem7042619 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7042620 (f : nat -> nat) : (term383 f) = (term380 f).
Proof. exact (MK_COMB (@lem7042619) (@lem7042618 f)). Qed.
Lemma lem7042621 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7042622 (f : nat -> nat) : (term392 f) = (term393 f).
Proof. exact (MK_COMB (@lem7042621) (@lem7042620 f)). Qed.
Lemma lem7042623 (f : nat -> nat) (g : nat -> nat) : (term386 f g) = (term377 f g).
Proof. exact (eq_refl (term386 f g)). Qed.
Lemma lem7042624 (x : type998) (g : nat -> nat) : (x g) = (x g).
Proof. exact (eq_refl (x g)). Qed.
Lemma lem7042625 (f : nat -> nat) (x : type998) (g : nat -> nat) : (term394 f x g) = (term395 f x g).
Proof. exact (MK_COMB (@lem7042623 f g) (@lem7042624 x g)). Qed.
Lemma lem7042626 (x : type998) (f : nat -> nat) (g : nat -> nat) : (term395 f x g) = (term396 x f g).
Proof. exact (eq_refl (term395 f x g)). Qed.
Lemma lem7042627 (x : type998) (f : nat -> nat) (g : nat -> nat) : (term394 f x g) = (term396 x f g).
Proof. exact (TRANS (@lem7042625 f x g) (@lem7042626 x f g)). Qed.
Lemma lem7042628 (x : type998) (f : nat -> nat) : (term397 f x) = (term398 x f).
Proof. exact (fun_ext (fun g : nat -> nat => @lem7042627 x f g)). Qed.
Lemma lem7042629 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7042630 (x : type998) (f : nat -> nat) : (term399 f x) = (term400 x f).
Proof. exact (MK_COMB (@lem7042629) (@lem7042628 x f)). Qed.
Lemma lem7042631 (f : nat -> nat) : (term401 f) = (term402 f).
Proof. exact (fun_ext (fun x : type998 => @lem7042630 x f)). Qed.
Lemma lem7042632 : (@ex ((nat -> nat) -> (nat -> Prop) -> nat)) = (@ex ((nat -> nat) -> (nat -> Prop) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> nat) -> (nat -> Prop) -> nat))). Qed.
Lemma lem7042633 (f : nat -> nat) : (term384 f) = (term403 f).
Proof. exact (MK_COMB (@lem7042632) (@lem7042631 f)). Qed.
Lemma lem7042634 (f : nat -> nat) : ((term383 f) = (term384 f)) = ((term380 f) = (term403 f)).
Proof. exact (MK_COMB (@lem7042622 f) (@lem7042633 f)). Qed.
Lemma lem7042635 (f : nat -> nat) : (term380 f) = (term403 f).
Proof. exact (EQ_MP (@lem7042634 f) (@lem7042609 f)). Qed.
Lemma lem7042636 (f : nat -> nat) : (term334 f) = (term403 f).
Proof. exact (TRANS (@lem7042605 f) (@lem7042635 f)). Qed.
Lemma lem7042637 : term335 = term404.
Proof. exact (fun_ext (fun f : nat -> nat => @lem7042636 f)). Qed.
Lemma lem7042638 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7042639 : term336 = term405.
Proof. exact (MK_COMB (@lem7042638) (@lem7042637)). Qed.
Lemma lem7042641 {A B : Type'} (P : type1413 A B) : (term243 A B P) = (term244 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7042642 (P : type996) : (term406 P) = (term407 P).
Proof. exact (@lem7042641 (nat -> nat) type998 P). Qed.
Lemma lem7042643 : term408 = term409.
Proof. exact (@lem7042642 term410). Qed.
Lemma lem7042644 (f : nat -> nat) : (term411 f) = (term402 f).
Proof. exact (eq_refl (term411 f)). Qed.
Lemma lem7042645 (x : type998) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7042646 (f : nat -> nat) (x : type998) : (term412 f x) = (term413 f x).
Proof. exact (MK_COMB (@lem7042644 f) (@lem7042645 x)). Qed.
Lemma lem7042647 (x : type998) (f : nat -> nat) : (term413 f x) = (term400 x f).
Proof. exact (eq_refl (term413 f x)). Qed.
Lemma lem7042648 (x : type998) (f : nat -> nat) : (term412 f x) = (term400 x f).
Proof. exact (TRANS (@lem7042646 f x) (@lem7042647 x f)). Qed.
Lemma lem7042649 (f : nat -> nat) : (term414 f) = (term402 f).
Proof. exact (fun_ext (fun x : type998 => @lem7042648 x f)). Qed.
Lemma lem7042650 : (@ex ((nat -> nat) -> (nat -> Prop) -> nat)) = (@ex ((nat -> nat) -> (nat -> Prop) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> nat) -> (nat -> Prop) -> nat))). Qed.
Lemma lem7042651 (f : nat -> nat) : (term415 f) = (term403 f).
Proof. exact (MK_COMB (@lem7042650) (@lem7042649 f)). Qed.
Lemma lem7042652 : term416 = term404.
Proof. exact (fun_ext (fun f : nat -> nat => @lem7042651 f)). Qed.
Lemma lem7042653 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7042654 : term408 = term405.
Proof. exact (MK_COMB (@lem7042653) (@lem7042652)). Qed.
Lemma lem7042655 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7042656 : term417 = term418.
Proof. exact (MK_COMB (@lem7042655) (@lem7042654)). Qed.
Lemma lem7042657 (f : nat -> nat) : (term411 f) = (term402 f).
Proof. exact (eq_refl (term411 f)). Qed.
Lemma lem7042658 (x : type999) (f : nat -> nat) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem7042659 (x : type999) (f : nat -> nat) : (term419 x f) = (term420 x f).
Proof. exact (MK_COMB (@lem7042657 f) (@lem7042658 x f)). Qed.
Lemma lem7042660 (x : type999) (f : nat -> nat) : (term420 x f) = (term421 x f).
Proof. exact (eq_refl (term420 x f)). Qed.
Lemma lem7042661 (x : type999) (f : nat -> nat) : (term419 x f) = (term421 x f).
Proof. exact (TRANS (@lem7042659 x f) (@lem7042660 x f)). Qed.
Lemma lem7042662 (x : type999) : (term422 x) = (term423 x).
Proof. exact (fun_ext (fun f : nat -> nat => @lem7042661 x f)). Qed.
Lemma lem7042663 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7042664 (x : type999) : (term424 x) = (term425 x).
Proof. exact (MK_COMB (@lem7042663) (@lem7042662 x)). Qed.
Lemma lem7042665 : term426 = term427.
Proof. exact (fun_ext (fun x : type999 => @lem7042664 x)). Qed.
Lemma lem7042666 : (@ex ((nat -> nat) -> (nat -> nat) -> (nat -> Prop) -> nat)) = (@ex ((nat -> nat) -> (nat -> nat) -> (nat -> Prop) -> nat)).
Proof. exact (eq_refl (@ex ((nat -> nat) -> (nat -> nat) -> (nat -> Prop) -> nat))). Qed.
Lemma lem7042667 : term409 = term428.
Proof. exact (MK_COMB (@lem7042666) (@lem7042665)). Qed.
Lemma lem7042668 : (term408 = term409) = (term405 = term428).
Proof. exact (MK_COMB (@lem7042656) (@lem7042667)). Qed.
Lemma lem7042669 : term405 = term428.
Proof. exact (EQ_MP (@lem7042668) (@lem7042643)). Qed.
Lemma lem7042671 : term336 = term428.
Proof. exact (TRANS (@lem7042639) (@lem7042669)). Qed.
Lemma lem7042672 : term11 = term428.
Proof. exact (TRANS (@lem7042439) (@lem7042671)). Qed.
Lemma lem7042673 (h1 : term11) : term428.
Proof. exact (EQ_MP (@lem7042672) (@lem7041499 h1)). Qed.
Lemma lem7042674 (x : type999) (h1 : term425 x) : term425 x.
Proof. exact (h1). Qed.
Lemma lem7042676 (f : nat -> nat) (h1 : term114 f) : term114 f.
Proof. exact (h1). Qed.
Lemma lem7042677 (f : nat -> nat) (g : nat -> nat) (h1 : term105 f g) : term105 f g.
Proof. exact (h1). Qed.
Lemma lem7042678 (f : nat -> nat) (m : nat) (g : nat -> nat) (h1 : term98 f m g) : term98 f m g.
Proof. exact (h1). Qed.
Lemma lem7042679 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (h1 : term88 f m n g) : term88 f m n g.
Proof. exact (h1). Qed.
Lemma lem7042686 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7042687 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7042686 nat (nat -> Prop) f x). Qed.
Lemma lem7042688 (p : nat) : (Peano.le p) = (@I (nat -> nat -> Prop) Peano.le p).
Proof. exact (@lem7042687 Peano.le p). Qed.
Lemma lem7042689 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7042690 (p : nat) (n : nat) : (Peano.le p n) = (@I (nat -> nat -> Prop) Peano.le p n).
Proof. exact (MK_COMB (@lem7042688 p) (@lem7042689 n)). Qed.
Lemma lem7042692 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7042693 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7042692 nat Prop f x). Qed.
Lemma lem7042694 (p : nat) (n : nat) : (@I (nat -> nat -> Prop) Peano.le p n) = (term429 p n).
Proof. exact (@lem7042693 (@I (nat -> nat -> Prop) Peano.le p) n). Qed.
Lemma lem7042696 (p : nat) (n : nat) : (Peano.le p n) = (term429 p n).
Proof. exact (TRANS (@lem7042690 p n) (@lem7042694 p n)). Qed.
Lemma lem7042703 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7042704 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7042703 nat (nat -> Prop) f x). Qed.
Lemma lem7042705 (m : nat) : (Peano.le m) = (@I (nat -> nat -> Prop) Peano.le m).
Proof. exact (@lem7042704 Peano.le m). Qed.
Lemma lem7042706 (p : nat) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem7042707 (m : nat) (p : nat) : (Peano.le m p) = (@I (nat -> nat -> Prop) Peano.le m p).
Proof. exact (MK_COMB (@lem7042705 m) (@lem7042706 p)). Qed.
Lemma lem7042709 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7042710 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7042709 nat Prop f x). Qed.
Lemma lem7042711 (m : nat) (p : nat) : (@I (nat -> nat -> Prop) Peano.le m p) = (term429 m p).
Proof. exact (@lem7042710 (@I (nat -> nat -> Prop) Peano.le m) p). Qed.
Lemma lem7042713 (m : nat) (p : nat) : (Peano.le m p) = (term429 m p).
Proof. exact (TRANS (@lem7042707 m p) (@lem7042711 m p)). Qed.
Lemma lem7042714 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7042715 (m : nat) (p : nat) : (term430 m p) = (term431 m p).
Proof. exact (MK_COMB (@lem7042714) (@lem7042713 m p)). Qed.
Lemma lem7042716 (m : nat) (p : nat) (n : nat) : (term56 m p n) = (term432 m p n).
Proof. exact (MK_COMB (@lem7042715 m p) (@lem7042696 p n)). Qed.
Lemma lem7042717 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7042726 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7042727 (f : type1601) (x : nat) : (f x) = (@I (nat -> nat -> nat -> Prop) f x).
Proof. exact (@lem7042726 nat type1605 f x). Qed.
Lemma lem7042728 (m : nat) : (dotdot m) = (@I (nat -> nat -> nat -> Prop) dotdot m).
Proof. exact (@lem7042727 dotdot m). Qed.
Lemma lem7042729 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7042730 (m : nat) (n : nat) : (dotdot m n) = (@I (nat -> nat -> nat -> Prop) dotdot m n).
Proof. exact (MK_COMB (@lem7042728 m) (@lem7042729 n)). Qed.
Lemma lem7042732 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7042733 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7042732 nat (nat -> Prop) f x). Qed.
Lemma lem7042734 (m : nat) (n : nat) : (@I (nat -> nat -> nat -> Prop) dotdot m n) = (term433 m n).
Proof. exact (@lem7042733 (@I (nat -> nat -> nat -> Prop) dotdot m) n). Qed.
Lemma lem7042736 (m : nat) (n : nat) : (dotdot m n) = (term433 m n).
Proof. exact (TRANS (@lem7042730 m n) (@lem7042734 m n)). Qed.
Lemma lem7042737 (p : nat) : (@IN nat p) = (@IN nat p).
Proof. exact (eq_refl (@IN nat p)). Qed.
Lemma lem7042738 (p : nat) (m : nat) (n : nat) : (term55 p m n) = (term434 p m n).
Proof. exact (MK_COMB (@lem7042737 p) (@lem7042736 m n)). Qed.
Lemma lem7042740 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7042741 (f : type1585) (x : nat) : (f x) = (@I (nat -> (nat -> Prop) -> Prop) f x).
Proof. exact (@lem7042740 nat type993 f x). Qed.
Lemma lem7042742 (p : nat) : (@IN nat p) = (@I (nat -> (nat -> Prop) -> Prop) (@IN nat) p).
Proof. exact (@lem7042741 (@IN nat) p). Qed.
Lemma lem7042743 (m : nat) (n : nat) : (term433 m n) = (term433 m n).
Proof. exact (eq_refl (term433 m n)). Qed.
Lemma lem7042744 (p : nat) (m : nat) (n : nat) : (term434 p m n) = (term435 p m n).
Proof. exact (MK_COMB (@lem7042742 p) (@lem7042743 m n)). Qed.
Lemma lem7042746 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7042747 (f : type993) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> Prop) f x).
Proof. exact (@lem7042746 (nat -> Prop) Prop f x). Qed.
Lemma lem7042748 (p : nat) (m : nat) (n : nat) : (term435 p m n) = (term436 p m n).
Proof. exact (@lem7042747 (@I (nat -> (nat -> Prop) -> Prop) (@IN nat) p) (term433 m n)). Qed.
Lemma lem7042749 (p : nat) (m : nat) (n : nat) : (term434 p m n) = (term436 p m n).
Proof. exact (TRANS (@lem7042744 p m n) (@lem7042748 p m n)). Qed.
Lemma lem7042750 (p : nat) (m : nat) (n : nat) : (term55 p m n) = (term436 p m n).
Proof. exact (TRANS (@lem7042738 p m n) (@lem7042749 p m n)). Qed.
Lemma lem7042751 (p : nat) (m : nat) (n : nat) : (term437 p m n) = (term438 p m n).
Proof. exact (MK_COMB (@lem7042717) (@lem7042750 p m n)). Qed.
Lemma lem7042752 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7042753 (p : nat) (m : nat) (n : nat) : (term439 p m n) = (term440 p m n).
Proof. exact (MK_COMB (@lem7042752) (@lem7042751 p m n)). Qed.
Lemma lem7042754 (m : nat) (p : nat) (n : nat) : (term121 m p n) = (term441 m p n).
Proof. exact (MK_COMB (@lem7042753 p m n) (@lem7042716 m p n)). Qed.
Lemma lem7042755 (m : nat) (n : nat) : (term142 m n) = (term442 m n).
Proof. exact (fun_ext (fun p : nat => @lem7042754 m p n)). Qed.
Lemma lem7042756 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7042757 (m : nat) (n : nat) : (term157 m n) = (term443 m n).
Proof. exact (MK_COMB (@lem7042756) (@lem7042755 m n)). Qed.
Lemma lem7042758 (m : nat) : (term164 m) = (term444 m).
Proof. exact (fun_ext (fun n : nat => @lem7042757 m n)). Qed.
Lemma lem7042759 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7042760 (m : nat) : (term179 m) = (term445 m).
Proof. exact (MK_COMB (@lem7042759) (@lem7042758 m)). Qed.
Lemma lem7042761 : term186 = term446.
Proof. exact (fun_ext (fun m : nat => @lem7042760 m)). Qed.
Lemma lem7042762 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7042763 : term201 = term447.
Proof. exact (MK_COMB (@lem7042762) (@lem7042761)). Qed.
Lemma lem7042764 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7042771 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7042772 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7042771 nat (nat -> Prop) f x). Qed.
Lemma lem7042773 (p : nat) : (Peano.le p) = (@I (nat -> nat -> Prop) Peano.le p).
Proof. exact (@lem7042772 Peano.le p). Qed.
Lemma lem7042774 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7042775 (p : nat) (n : nat) : (Peano.le p n) = (@I (nat -> nat -> Prop) Peano.le p n).
Proof. exact (MK_COMB (@lem7042773 p) (@lem7042774 n)). Qed.
Lemma lem7042777 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7042778 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7042777 nat Prop f x). Qed.
Lemma lem7042779 (p : nat) (n : nat) : (@I (nat -> nat -> Prop) Peano.le p n) = (term429 p n).
Proof. exact (@lem7042778 (@I (nat -> nat -> Prop) Peano.le p) n). Qed.
Lemma lem7042781 (p : nat) (n : nat) : (Peano.le p n) = (term429 p n).
Proof. exact (TRANS (@lem7042775 p n) (@lem7042779 p n)). Qed.
Lemma lem7042782 (p : nat) (n : nat) : (term448 p n) = (term449 p n).
Proof. exact (MK_COMB (@lem7042764) (@lem7042781 p n)). Qed.
Lemma lem7042783 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7042790 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7042791 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7042790 nat (nat -> Prop) f x). Qed.
Lemma lem7042792 (m : nat) : (Peano.le m) = (@I (nat -> nat -> Prop) Peano.le m).
Proof. exact (@lem7042791 Peano.le m). Qed.
Lemma lem7042793 (p : nat) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem7042794 (m : nat) (p : nat) : (Peano.le m p) = (@I (nat -> nat -> Prop) Peano.le m p).
Proof. exact (MK_COMB (@lem7042792 m) (@lem7042793 p)). Qed.
Lemma lem7042796 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7042797 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7042796 nat Prop f x). Qed.
Lemma lem7042798 (m : nat) (p : nat) : (@I (nat -> nat -> Prop) Peano.le m p) = (term429 m p).
Proof. exact (@lem7042797 (@I (nat -> nat -> Prop) Peano.le m) p). Qed.
Lemma lem7042800 (m : nat) (p : nat) : (Peano.le m p) = (term429 m p).
Proof. exact (TRANS (@lem7042794 m p) (@lem7042798 m p)). Qed.
Lemma lem7042801 (m : nat) (p : nat) : (term448 m p) = (term449 m p).
Proof. exact (MK_COMB (@lem7042783) (@lem7042800 m p)). Qed.
Lemma lem7042802 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7042803 (m : nat) (p : nat) : (term450 m p) = (term451 m p).
Proof. exact (MK_COMB (@lem7042802) (@lem7042801 m p)). Qed.
Lemma lem7042804 (m : nat) (p : nat) (n : nat) : (term77 m p n) = (term452 m p n).
Proof. exact (MK_COMB (@lem7042803 m p) (@lem7042782 p n)). Qed.
Lemma lem7042813 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7042814 (f : type1601) (x : nat) : (f x) = (@I (nat -> nat -> nat -> Prop) f x).
Proof. exact (@lem7042813 nat type1605 f x). Qed.
Lemma lem7042815 (m : nat) : (dotdot m) = (@I (nat -> nat -> nat -> Prop) dotdot m).
Proof. exact (@lem7042814 dotdot m). Qed.
Lemma lem7042816 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7042817 (m : nat) (n : nat) : (dotdot m n) = (@I (nat -> nat -> nat -> Prop) dotdot m n).
Proof. exact (MK_COMB (@lem7042815 m) (@lem7042816 n)). Qed.
Lemma lem7042819 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7042820 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7042819 nat (nat -> Prop) f x). Qed.
Lemma lem7042821 (m : nat) (n : nat) : (@I (nat -> nat -> nat -> Prop) dotdot m n) = (term433 m n).
Proof. exact (@lem7042820 (@I (nat -> nat -> nat -> Prop) dotdot m) n). Qed.
Lemma lem7042823 (m : nat) (n : nat) : (dotdot m n) = (term433 m n).
Proof. exact (TRANS (@lem7042817 m n) (@lem7042821 m n)). Qed.
Lemma lem7042824 (p : nat) : (@IN nat p) = (@IN nat p).
Proof. exact (eq_refl (@IN nat p)). Qed.
Lemma lem7042825 (p : nat) (m : nat) (n : nat) : (term55 p m n) = (term434 p m n).
Proof. exact (MK_COMB (@lem7042824 p) (@lem7042823 m n)). Qed.
Lemma lem7042827 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7042828 (f : type1585) (x : nat) : (f x) = (@I (nat -> (nat -> Prop) -> Prop) f x).
Proof. exact (@lem7042827 nat type993 f x). Qed.
Lemma lem7042829 (p : nat) : (@IN nat p) = (@I (nat -> (nat -> Prop) -> Prop) (@IN nat) p).
Proof. exact (@lem7042828 (@IN nat) p). Qed.
Lemma lem7042830 (m : nat) (n : nat) : (term433 m n) = (term433 m n).
Proof. exact (eq_refl (term433 m n)). Qed.
Lemma lem7042831 (p : nat) (m : nat) (n : nat) : (term434 p m n) = (term435 p m n).
Proof. exact (MK_COMB (@lem7042829 p) (@lem7042830 m n)). Qed.
Lemma lem7042833 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7042834 (f : type993) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> Prop) f x).
Proof. exact (@lem7042833 (nat -> Prop) Prop f x). Qed.
Lemma lem7042835 (p : nat) (m : nat) (n : nat) : (term435 p m n) = (term436 p m n).
Proof. exact (@lem7042834 (@I (nat -> (nat -> Prop) -> Prop) (@IN nat) p) (term433 m n)). Qed.
Lemma lem7042836 (p : nat) (m : nat) (n : nat) : (term434 p m n) = (term436 p m n).
Proof. exact (TRANS (@lem7042831 p m n) (@lem7042835 p m n)). Qed.
Lemma lem7042837 (p : nat) (m : nat) (n : nat) : (term55 p m n) = (term436 p m n).
Proof. exact (TRANS (@lem7042825 p m n) (@lem7042836 p m n)). Qed.
Lemma lem7042838 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7042839 (p : nat) (m : nat) (n : nat) : (term122 p m n) = (term453 p m n).
Proof. exact (MK_COMB (@lem7042838) (@lem7042837 p m n)). Qed.
Lemma lem7042840 (m : nat) (p : nat) (n : nat) : (term124 m p n) = (term454 m p n).
Proof. exact (MK_COMB (@lem7042839 p m n) (@lem7042804 m p n)). Qed.
Lemma lem7042841 (m : nat) (n : nat) : (term141 m n) = (term455 m n).
Proof. exact (fun_ext (fun p : nat => @lem7042840 m p n)). Qed.
Lemma lem7042842 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7042843 (m : nat) (n : nat) : (term152 m n) = (term456 m n).
Proof. exact (MK_COMB (@lem7042842) (@lem7042841 m n)). Qed.
Lemma lem7042844 (m : nat) : (term163 m) = (term457 m).
Proof. exact (fun_ext (fun n : nat => @lem7042843 m n)). Qed.
Lemma lem7042845 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7042846 (m : nat) : (term174 m) = (term458 m).
Proof. exact (MK_COMB (@lem7042845) (@lem7042844 m)). Qed.
Lemma lem7042847 : term185 = term459.
Proof. exact (fun_ext (fun m : nat => @lem7042846 m)). Qed.
Lemma lem7042848 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7042849 : term196 = term460.
Proof. exact (MK_COMB (@lem7042848) (@lem7042847)). Qed.
Lemma lem7042850 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7042851 : term198 = term461.
Proof. exact (MK_COMB (@lem7042850) (@lem7042849)). Qed.
Lemma lem7042852 : term202 = term462.
Proof. exact (MK_COMB (@lem7042851) (@lem7042763)). Qed.
Lemma lem7042853 (h1 : term62) : term462.
Proof. exact (EQ_MP (@lem7042852) (@lem7042121 h1)). Qed.
Lemma lem7042885 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7042892 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7042893 (f : type987) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> (nat -> nat) -> nat) f x).
Proof. exact (@lem7042892 (nat -> Prop) type1003 f x). Qed.
Lemma lem7042894 (s : nat -> Prop) : (@nsum nat s) = (@I ((nat -> Prop) -> (nat -> nat) -> nat) (@nsum nat) s).
Proof. exact (@lem7042893 (@nsum nat) s). Qed.
Lemma lem7042895 (f : nat -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7042896 (s : nat -> Prop) (f : nat -> nat) : (@nsum nat s f) = (@I ((nat -> Prop) -> (nat -> nat) -> nat) (@nsum nat) s f).
Proof. exact (MK_COMB (@lem7042894 s) (@lem7042895 f)). Qed.
Lemma lem7042898 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7042899 (f : type1003) (x : nat -> nat) : (f x) = (@I ((nat -> nat) -> nat) f x).
Proof. exact (@lem7042898 (nat -> nat) nat f x). Qed.
Lemma lem7042900 (s : nat -> Prop) (f : nat -> nat) : (@I ((nat -> Prop) -> (nat -> nat) -> nat) (@nsum nat) s f) = (term463 s f).
Proof. exact (@lem7042899 (@I ((nat -> Prop) -> (nat -> nat) -> nat) (@nsum nat) s) f). Qed.
Lemma lem7042902 (s : nat -> Prop) (f : nat -> nat) : (@nsum nat s f) = (term463 s f).
Proof. exact (TRANS (@lem7042896 s f) (@lem7042900 s f)). Qed.
Lemma lem7042909 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7042910 (f : type987) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> (nat -> nat) -> nat) f x).
Proof. exact (@lem7042909 (nat -> Prop) type1003 f x). Qed.
Lemma lem7042911 (s : nat -> Prop) : (@nsum nat s) = (@I ((nat -> Prop) -> (nat -> nat) -> nat) (@nsum nat) s).
Proof. exact (@lem7042910 (@nsum nat) s). Qed.
Lemma lem7042912 (g : nat -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7042913 (s : nat -> Prop) (g : nat -> nat) : (@nsum nat s g) = (@I ((nat -> Prop) -> (nat -> nat) -> nat) (@nsum nat) s g).
Proof. exact (MK_COMB (@lem7042911 s) (@lem7042912 g)). Qed.
Lemma lem7042915 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7042916 (f : type1003) (x : nat -> nat) : (f x) = (@I ((nat -> nat) -> nat) f x).
Proof. exact (@lem7042915 (nat -> nat) nat f x). Qed.
Lemma lem7042917 (s : nat -> Prop) (g : nat -> nat) : (@I ((nat -> Prop) -> (nat -> nat) -> nat) (@nsum nat) s g) = (term463 s g).
Proof. exact (@lem7042916 (@I ((nat -> Prop) -> (nat -> nat) -> nat) (@nsum nat) s) g). Qed.
Lemma lem7042919 (s : nat -> Prop) (g : nat -> nat) : (@nsum nat s g) = (term463 s g).
Proof. exact (TRANS (@lem7042913 s g) (@lem7042917 s g)). Qed.
Lemma lem7042920 (s : nat -> Prop) (f : nat -> nat) : (term464 s f) = (term465 s f).
Proof. exact (MK_COMB (@lem7042885) (@lem7042902 s f)). Qed.
Lemma lem7042921 (f : nat -> nat) (s : nat -> Prop) (g : nat -> nat) : ((@nsum nat s f) = (@nsum nat s g)) = ((term463 s f) = (term463 s g)).
Proof. exact (MK_COMB (@lem7042920 s f) (@lem7042919 s g)). Qed.
Lemma lem7042922 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7042923 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7042924 (f : nat -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7042933 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7042934 (f : type999) (x : nat -> nat) : (f x) = (@I ((nat -> nat) -> (nat -> nat) -> (nat -> Prop) -> nat) f x).
Proof. exact (@lem7042933 (nat -> nat) type998 f x). Qed.
Lemma lem7042935 (x : type999) (f : nat -> nat) : (x f) = (@I ((nat -> nat) -> (nat -> nat) -> (nat -> Prop) -> nat) x f).
Proof. exact (@lem7042934 x f). Qed.
Lemma lem7042936 (g : nat -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7042937 (x : type999) (f : nat -> nat) (g : nat -> nat) : (x f g) = (@I ((nat -> nat) -> (nat -> nat) -> (nat -> Prop) -> nat) x f g).
Proof. exact (MK_COMB (@lem7042935 x f) (@lem7042936 g)). Qed.
Lemma lem7042939 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7042940 (f : type998) (x : nat -> nat) : (f x) = (@I ((nat -> nat) -> (nat -> Prop) -> nat) f x).
Proof. exact (@lem7042939 (nat -> nat) type994 f x). Qed.
Lemma lem7042941 (x : type999) (f : nat -> nat) (g : nat -> nat) : (@I ((nat -> nat) -> (nat -> nat) -> (nat -> Prop) -> nat) x f g) = (term466 x f g).
Proof. exact (@lem7042940 (@I ((nat -> nat) -> (nat -> nat) -> (nat -> Prop) -> nat) x f) g). Qed.
Lemma lem7042942 (x : type999) (f : nat -> nat) (g : nat -> nat) : (x f g) = (term466 x f g).
Proof. exact (TRANS (@lem7042937 x f g) (@lem7042941 x f g)). Qed.
Lemma lem7042943 (s : nat -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7042944 (x : type999) (f : nat -> nat) (g : nat -> nat) (s : nat -> Prop) : (x f g s) = (term467 x f g s).
Proof. exact (MK_COMB (@lem7042942 x f g) (@lem7042943 s)). Qed.
Lemma lem7042946 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7042947 (f : type994) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> nat) f x).
Proof. exact (@lem7042946 (nat -> Prop) nat f x). Qed.
Lemma lem7042948 (x : type999) (f : nat -> nat) (g : nat -> nat) (s : nat -> Prop) : (term467 x f g s) = (term468 x f g s).
Proof. exact (@lem7042947 (term466 x f g) s). Qed.
Lemma lem7042950 (x : type999) (f : nat -> nat) (g : nat -> nat) (s : nat -> Prop) : (x f g s) = (term468 x f g s).
Proof. exact (TRANS (@lem7042944 x f g s) (@lem7042948 x f g s)). Qed.
Lemma lem7042951 (x : type999) (f : nat -> nat) (g : nat -> nat) (s : nat -> Prop) : (term469 x f g s) = (term470 x f g s).
Proof. exact (MK_COMB (@lem7042924 f) (@lem7042950 x f g s)). Qed.
Lemma lem7042953 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7042954 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7042953 nat nat f x). Qed.
Lemma lem7042955 (x : type999) (f : nat -> nat) (g : nat -> nat) (s : nat -> Prop) : (term470 x f g s) = (term471 x f g s).
Proof. exact (@lem7042954 f (term468 x f g s)). Qed.
Lemma lem7042956 (x : type999) (f : nat -> nat) (g : nat -> nat) (s : nat -> Prop) : (term469 x f g s) = (term471 x f g s).
Proof. exact (TRANS (@lem7042951 x f g s) (@lem7042955 x f g s)). Qed.
Lemma lem7042957 (g : nat -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7042966 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7042967 (f : type999) (x : nat -> nat) : (f x) = (@I ((nat -> nat) -> (nat -> nat) -> (nat -> Prop) -> nat) f x).
Proof. exact (@lem7042966 (nat -> nat) type998 f x). Qed.
Lemma lem7042968 (x : type999) (f : nat -> nat) : (x f) = (@I ((nat -> nat) -> (nat -> nat) -> (nat -> Prop) -> nat) x f).
Proof. exact (@lem7042967 x f). Qed.
Lemma lem7042969 (g : nat -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7042970 (x : type999) (f : nat -> nat) (g : nat -> nat) : (x f g) = (@I ((nat -> nat) -> (nat -> nat) -> (nat -> Prop) -> nat) x f g).
Proof. exact (MK_COMB (@lem7042968 x f) (@lem7042969 g)). Qed.
Lemma lem7042972 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7042973 (f : type998) (x : nat -> nat) : (f x) = (@I ((nat -> nat) -> (nat -> Prop) -> nat) f x).
Proof. exact (@lem7042972 (nat -> nat) type994 f x). Qed.
Lemma lem7042974 (x : type999) (f : nat -> nat) (g : nat -> nat) : (@I ((nat -> nat) -> (nat -> nat) -> (nat -> Prop) -> nat) x f g) = (term466 x f g).
Proof. exact (@lem7042973 (@I ((nat -> nat) -> (nat -> nat) -> (nat -> Prop) -> nat) x f) g). Qed.
Lemma lem7042975 (x : type999) (f : nat -> nat) (g : nat -> nat) : (x f g) = (term466 x f g).
Proof. exact (TRANS (@lem7042970 x f g) (@lem7042974 x f g)). Qed.
Lemma lem7042976 (s : nat -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7042977 (x : type999) (f : nat -> nat) (g : nat -> nat) (s : nat -> Prop) : (x f g s) = (term467 x f g s).
Proof. exact (MK_COMB (@lem7042975 x f g) (@lem7042976 s)). Qed.
Lemma lem7042979 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7042980 (f : type994) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> nat) f x).
Proof. exact (@lem7042979 (nat -> Prop) nat f x). Qed.
Lemma lem7042981 (x : type999) (f : nat -> nat) (g : nat -> nat) (s : nat -> Prop) : (term467 x f g s) = (term468 x f g s).
Proof. exact (@lem7042980 (term466 x f g) s). Qed.
Lemma lem7042983 (x : type999) (f : nat -> nat) (g : nat -> nat) (s : nat -> Prop) : (x f g s) = (term468 x f g s).
Proof. exact (TRANS (@lem7042977 x f g s) (@lem7042981 x f g s)). Qed.
Lemma lem7042984 (x : type999) (f : nat -> nat) (g : nat -> nat) (s : nat -> Prop) : (term472 x f g s) = (term473 x f g s).
Proof. exact (MK_COMB (@lem7042957 g) (@lem7042983 x f g s)). Qed.
Lemma lem7042986 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7042987 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7042986 nat nat f x). Qed.
Lemma lem7042988 (x : type999) (f : nat -> nat) (g : nat -> nat) (s : nat -> Prop) : (term473 x f g s) = (term474 x f g s).
Proof. exact (@lem7042987 g (term468 x f g s)). Qed.
Lemma lem7042989 (x : type999) (f : nat -> nat) (g : nat -> nat) (s : nat -> Prop) : (term472 x f g s) = (term474 x f g s).
Proof. exact (TRANS (@lem7042984 x f g s) (@lem7042988 x f g s)). Qed.
Lemma lem7042990 (x : type999) (f : nat -> nat) (g : nat -> nat) (s : nat -> Prop) : (term475 x f g s) = (term476 x f g s).
Proof. exact (MK_COMB (@lem7042923) (@lem7042956 x f g s)). Qed.
Lemma lem7042991 (x : type999) (f : nat -> nat) (g : nat -> nat) (s : nat -> Prop) : ((term469 x f g s) = (term472 x f g s)) = ((term471 x f g s) = (term474 x f g s)).
Proof. exact (MK_COMB (@lem7042990 x f g s) (@lem7042989 x f g s)). Qed.
Lemma lem7042992 (x : type999) (f : nat -> nat) (g : nat -> nat) (s : nat -> Prop) : (term477 x f g s) = (term478 x f g s).
Proof. exact (MK_COMB (@lem7042922) (@lem7042991 x f g s)). Qed.
Lemma lem7042993 : (@IN nat) = (@IN nat).
Proof. exact (eq_refl (@IN nat)). Qed.
Lemma lem7043002 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7043003 (f : type999) (x : nat -> nat) : (f x) = (@I ((nat -> nat) -> (nat -> nat) -> (nat -> Prop) -> nat) f x).
Proof. exact (@lem7043002 (nat -> nat) type998 f x). Qed.
Lemma lem7043004 (x : type999) (f : nat -> nat) : (x f) = (@I ((nat -> nat) -> (nat -> nat) -> (nat -> Prop) -> nat) x f).
Proof. exact (@lem7043003 x f). Qed.
Lemma lem7043005 (g : nat -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7043006 (x : type999) (f : nat -> nat) (g : nat -> nat) : (x f g) = (@I ((nat -> nat) -> (nat -> nat) -> (nat -> Prop) -> nat) x f g).
Proof. exact (MK_COMB (@lem7043004 x f) (@lem7043005 g)). Qed.
Lemma lem7043008 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7043009 (f : type998) (x : nat -> nat) : (f x) = (@I ((nat -> nat) -> (nat -> Prop) -> nat) f x).
Proof. exact (@lem7043008 (nat -> nat) type994 f x). Qed.
Lemma lem7043010 (x : type999) (f : nat -> nat) (g : nat -> nat) : (@I ((nat -> nat) -> (nat -> nat) -> (nat -> Prop) -> nat) x f g) = (term466 x f g).
Proof. exact (@lem7043009 (@I ((nat -> nat) -> (nat -> nat) -> (nat -> Prop) -> nat) x f) g). Qed.
Lemma lem7043011 (x : type999) (f : nat -> nat) (g : nat -> nat) : (x f g) = (term466 x f g).
Proof. exact (TRANS (@lem7043006 x f g) (@lem7043010 x f g)). Qed.
Lemma lem7043012 (s : nat -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7043013 (x : type999) (f : nat -> nat) (g : nat -> nat) (s : nat -> Prop) : (x f g s) = (term467 x f g s).
Proof. exact (MK_COMB (@lem7043011 x f g) (@lem7043012 s)). Qed.
Lemma lem7043015 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7043016 (f : type994) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> nat) f x).
Proof. exact (@lem7043015 (nat -> Prop) nat f x). Qed.
Lemma lem7043017 (x : type999) (f : nat -> nat) (g : nat -> nat) (s : nat -> Prop) : (term467 x f g s) = (term468 x f g s).
Proof. exact (@lem7043016 (term466 x f g) s). Qed.
Lemma lem7043019 (x : type999) (f : nat -> nat) (g : nat -> nat) (s : nat -> Prop) : (x f g s) = (term468 x f g s).
Proof. exact (TRANS (@lem7043013 x f g s) (@lem7043017 x f g s)). Qed.
Lemma lem7043020 (s : nat -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7043021 (x : type999) (f : nat -> nat) (g : nat -> nat) (s : nat -> Prop) : (term479 x f g s) = (term480 x f g s).
Proof. exact (MK_COMB (@lem7042993) (@lem7043019 x f g s)). Qed.
Lemma lem7043022 (x : type999) (f : nat -> nat) (g : nat -> nat) (s : nat -> Prop) : (term481 x f g s) = (term482 x f g s).
Proof. exact (MK_COMB (@lem7043021 x f g s) (@lem7043020 s)). Qed.
Lemma lem7043024 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7043025 (f : type1585) (x : nat) : (f x) = (@I (nat -> (nat -> Prop) -> Prop) f x).
Proof. exact (@lem7043024 nat type993 f x). Qed.
Lemma lem7043026 (x : type999) (f : nat -> nat) (g : nat -> nat) (s : nat -> Prop) : (term480 x f g s) = (term483 x f g s).
Proof. exact (@lem7043025 (@IN nat) (term468 x f g s)). Qed.
Lemma lem7043027 (s : nat -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7043028 (x : type999) (f : nat -> nat) (g : nat -> nat) (s : nat -> Prop) : (term482 x f g s) = (term484 x f g s).
Proof. exact (MK_COMB (@lem7043026 x f g s) (@lem7043027 s)). Qed.
Lemma lem7043030 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7043031 (f : type993) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> Prop) f x).
Proof. exact (@lem7043030 (nat -> Prop) Prop f x). Qed.
Lemma lem7043032 (x : type999) (f : nat -> nat) (g : nat -> nat) (s : nat -> Prop) : (term484 x f g s) = (term485 x f g s).
Proof. exact (@lem7043031 (term483 x f g s) s). Qed.
Lemma lem7043033 (x : type999) (f : nat -> nat) (g : nat -> nat) (s : nat -> Prop) : (term482 x f g s) = (term485 x f g s).
Proof. exact (TRANS (@lem7043028 x f g s) (@lem7043032 x f g s)). Qed.
Lemma lem7043034 (x : type999) (f : nat -> nat) (g : nat -> nat) (s : nat -> Prop) : (term481 x f g s) = (term485 x f g s).
Proof. exact (TRANS (@lem7043022 x f g s) (@lem7043033 x f g s)). Qed.
Lemma lem7043035 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7043036 (x : type999) (f : nat -> nat) (g : nat -> nat) (s : nat -> Prop) : (term486 x f g s) = (term487 x f g s).
Proof. exact (MK_COMB (@lem7043035) (@lem7043034 x f g s)). Qed.
Lemma lem7043037 (x : type999) (f : nat -> nat) (g : nat -> nat) (s : nat -> Prop) : (term488 x f g s) = (term489 x f g s).
Proof. exact (MK_COMB (@lem7043036 x f g s) (@lem7042992 x f g s)). Qed.
Lemma lem7043038 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7043039 (x : type999) (f : nat -> nat) (g : nat -> nat) (s : nat -> Prop) : (term490 x f g s) = (term491 x f g s).
Proof. exact (MK_COMB (@lem7043038) (@lem7043037 x f g s)). Qed.
Lemma lem7043040 (x : type999) (f : nat -> nat) (s : nat -> Prop) (g : nat -> nat) : (term492 x f s g) = (term493 x f s g).
Proof. exact (MK_COMB (@lem7043039 x f g s) (@lem7042921 f s g)). Qed.
Lemma lem7043041 (x : type999) (f : nat -> nat) (g : nat -> nat) : (term494 x f g) = (term495 x f g).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem7043040 x f s g)). Qed.
Lemma lem7043042 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem7043043 (x : type999) (f : nat -> nat) (g : nat -> nat) : (term496 x f g) = (term497 x f g).
Proof. exact (MK_COMB (@lem7043042) (@lem7043041 x f g)). Qed.
Lemma lem7043044 (x : type999) (f : nat -> nat) : (term498 x f) = (term499 x f).
Proof. exact (fun_ext (fun g : nat -> nat => @lem7043043 x f g)). Qed.
Lemma lem7043045 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7043046 (x : type999) (f : nat -> nat) : (term421 x f) = (term500 x f).
Proof. exact (MK_COMB (@lem7043045) (@lem7043044 x f)). Qed.
Lemma lem7043047 (x : type999) : (term423 x) = (term501 x).
Proof. exact (fun_ext (fun f : nat -> nat => @lem7043046 x f)). Qed.
Lemma lem7043048 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7043049 (x : type999) : (term425 x) = (term502 x).
Proof. exact (MK_COMB (@lem7043048) (@lem7043047 x)). Qed.
Lemma lem7043050 (x : type999) (h1 : term425 x) : term502 x.
Proof. exact (EQ_MP (@lem7043049 x) (@lem7042674 x h1)). Qed.
Lemma lem7043217 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7043218 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7043219 : (@nsum nat) = (@nsum nat).
Proof. exact (eq_refl (@nsum nat)). Qed.
Lemma lem7043226 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7043227 (f : type1601) (x : nat) : (f x) = (@I (nat -> nat -> nat -> Prop) f x).
Proof. exact (@lem7043226 nat type1605 f x). Qed.
Lemma lem7043228 (m : nat) : (dotdot m) = (@I (nat -> nat -> nat -> Prop) dotdot m).
Proof. exact (@lem7043227 dotdot m). Qed.
Lemma lem7043229 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7043230 (m : nat) (n : nat) : (dotdot m n) = (@I (nat -> nat -> nat -> Prop) dotdot m n).
Proof. exact (MK_COMB (@lem7043228 m) (@lem7043229 n)). Qed.
Lemma lem7043232 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7043233 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7043232 nat (nat -> Prop) f x). Qed.
Lemma lem7043234 (m : nat) (n : nat) : (@I (nat -> nat -> nat -> Prop) dotdot m n) = (term433 m n).
Proof. exact (@lem7043233 (@I (nat -> nat -> nat -> Prop) dotdot m) n). Qed.
Lemma lem7043236 (m : nat) (n : nat) : (dotdot m n) = (term433 m n).
Proof. exact (TRANS (@lem7043230 m n) (@lem7043234 m n)). Qed.
Lemma lem7043237 (f : nat -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7043238 (m : nat) (n : nat) : (term503 m n) = (term504 m n).
Proof. exact (MK_COMB (@lem7043219) (@lem7043236 m n)). Qed.
Lemma lem7043239 (m : nat) (n : nat) (f : nat -> nat) : (term63 m n f) = (term505 m n f).
Proof. exact (MK_COMB (@lem7043238 m n) (@lem7043237 f)). Qed.
Lemma lem7043241 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7043242 (f : type987) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> (nat -> nat) -> nat) f x).
Proof. exact (@lem7043241 (nat -> Prop) type1003 f x). Qed.
Lemma lem7043243 (m : nat) (n : nat) : (term504 m n) = (term506 m n).
Proof. exact (@lem7043242 (@nsum nat) (term433 m n)). Qed.
Lemma lem7043244 (f : nat -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7043245 (m : nat) (n : nat) (f : nat -> nat) : (term505 m n f) = (term507 m n f).
Proof. exact (MK_COMB (@lem7043243 m n) (@lem7043244 f)). Qed.
Lemma lem7043247 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7043248 (f : type1003) (x : nat -> nat) : (f x) = (@I ((nat -> nat) -> nat) f x).
Proof. exact (@lem7043247 (nat -> nat) nat f x). Qed.
Lemma lem7043249 (m : nat) (n : nat) (f : nat -> nat) : (term507 m n f) = (term508 m n f).
Proof. exact (@lem7043248 (term506 m n) f). Qed.
Lemma lem7043250 (m : nat) (n : nat) (f : nat -> nat) : (term505 m n f) = (term508 m n f).
Proof. exact (TRANS (@lem7043245 m n f) (@lem7043249 m n f)). Qed.
Lemma lem7043251 (m : nat) (n : nat) (f : nat -> nat) : (term63 m n f) = (term508 m n f).
Proof. exact (TRANS (@lem7043239 m n f) (@lem7043250 m n f)). Qed.
Lemma lem7043252 : (@nsum nat) = (@nsum nat).
Proof. exact (eq_refl (@nsum nat)). Qed.
Lemma lem7043259 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7043260 (f : type1601) (x : nat) : (f x) = (@I (nat -> nat -> nat -> Prop) f x).
Proof. exact (@lem7043259 nat type1605 f x). Qed.
Lemma lem7043261 (m : nat) : (dotdot m) = (@I (nat -> nat -> nat -> Prop) dotdot m).
Proof. exact (@lem7043260 dotdot m). Qed.
Lemma lem7043262 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7043263 (m : nat) (n : nat) : (dotdot m n) = (@I (nat -> nat -> nat -> Prop) dotdot m n).
Proof. exact (MK_COMB (@lem7043261 m) (@lem7043262 n)). Qed.
Lemma lem7043265 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7043266 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7043265 nat (nat -> Prop) f x). Qed.
Lemma lem7043267 (m : nat) (n : nat) : (@I (nat -> nat -> nat -> Prop) dotdot m n) = (term433 m n).
Proof. exact (@lem7043266 (@I (nat -> nat -> nat -> Prop) dotdot m) n). Qed.
Lemma lem7043269 (m : nat) (n : nat) : (dotdot m n) = (term433 m n).
Proof. exact (TRANS (@lem7043263 m n) (@lem7043267 m n)). Qed.
Lemma lem7043270 (g : nat -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7043271 (m : nat) (n : nat) : (term503 m n) = (term504 m n).
Proof. exact (MK_COMB (@lem7043252) (@lem7043269 m n)). Qed.
Lemma lem7043272 (m : nat) (n : nat) (g : nat -> nat) : (term63 m n g) = (term505 m n g).
Proof. exact (MK_COMB (@lem7043271 m n) (@lem7043270 g)). Qed.
Lemma lem7043274 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7043275 (f : type987) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> (nat -> nat) -> nat) f x).
Proof. exact (@lem7043274 (nat -> Prop) type1003 f x). Qed.
Lemma lem7043276 (m : nat) (n : nat) : (term504 m n) = (term506 m n).
Proof. exact (@lem7043275 (@nsum nat) (term433 m n)). Qed.
Lemma lem7043277 (g : nat -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7043278 (m : nat) (n : nat) (g : nat -> nat) : (term505 m n g) = (term507 m n g).
Proof. exact (MK_COMB (@lem7043276 m n) (@lem7043277 g)). Qed.
Lemma lem7043280 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7043281 (f : type1003) (x : nat -> nat) : (f x) = (@I ((nat -> nat) -> nat) f x).
Proof. exact (@lem7043280 (nat -> nat) nat f x). Qed.
Lemma lem7043282 (m : nat) (n : nat) (g : nat -> nat) : (term507 m n g) = (term508 m n g).
Proof. exact (@lem7043281 (term506 m n) g). Qed.
Lemma lem7043283 (m : nat) (n : nat) (g : nat -> nat) : (term505 m n g) = (term508 m n g).
Proof. exact (TRANS (@lem7043278 m n g) (@lem7043282 m n g)). Qed.
Lemma lem7043284 (m : nat) (n : nat) (g : nat -> nat) : (term63 m n g) = (term508 m n g).
Proof. exact (TRANS (@lem7043272 m n g) (@lem7043283 m n g)). Qed.
Lemma lem7043285 (m : nat) (n : nat) (f : nat -> nat) : (term509 m n f) = (term510 m n f).
Proof. exact (MK_COMB (@lem7043218) (@lem7043251 m n f)). Qed.
Lemma lem7043286 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) : ((term63 m n f) = (term63 m n g)) = ((term508 m n f) = (term508 m n g)).
Proof. exact (MK_COMB (@lem7043285 m n f) (@lem7043284 m n g)). Qed.
Lemma lem7043287 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) : (term84 f m n g) = (term511 f m n g).
Proof. exact (MK_COMB (@lem7043217) (@lem7043286 f m n g)). Qed.
Lemma lem7043288 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7043293 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7043294 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7043293 nat nat f x). Qed.
Lemma lem7043296 (f : nat -> nat) (i : nat) : (f i) = (@I (nat -> nat) f i).
Proof. exact (@lem7043294 f i). Qed.
Lemma lem7043301 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7043302 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7043301 nat nat f x). Qed.
Lemma lem7043304 (g : nat -> nat) (i : nat) : (g i) = (@I (nat -> nat) g i).
Proof. exact (@lem7043302 g i). Qed.
Lemma lem7043305 (f : nat -> nat) (i : nat) : (term512 f i) = (term513 f i).
Proof. exact (MK_COMB (@lem7043288) (@lem7043296 f i)). Qed.
Lemma lem7043306 (f : nat -> nat) (g : nat -> nat) (i : nat) : ((f i) = (g i)) = ((@I (nat -> nat) f i) = (@I (nat -> nat) g i)).
Proof. exact (MK_COMB (@lem7043305 f i) (@lem7043304 g i)). Qed.
Lemma lem7043307 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7043314 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7043315 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7043314 nat (nat -> Prop) f x). Qed.
Lemma lem7043316 (i : nat) : (Peano.le i) = (@I (nat -> nat -> Prop) Peano.le i).
Proof. exact (@lem7043315 Peano.le i). Qed.
Lemma lem7043317 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7043318 (i : nat) (n : nat) : (Peano.le i n) = (@I (nat -> nat -> Prop) Peano.le i n).
Proof. exact (MK_COMB (@lem7043316 i) (@lem7043317 n)). Qed.
Lemma lem7043320 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7043321 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7043320 nat Prop f x). Qed.
Lemma lem7043322 (i : nat) (n : nat) : (@I (nat -> nat -> Prop) Peano.le i n) = (term429 i n).
Proof. exact (@lem7043321 (@I (nat -> nat -> Prop) Peano.le i) n). Qed.
Lemma lem7043324 (i : nat) (n : nat) : (Peano.le i n) = (term429 i n).
Proof. exact (TRANS (@lem7043318 i n) (@lem7043322 i n)). Qed.
Lemma lem7043325 (i : nat) (n : nat) : (term448 i n) = (term449 i n).
Proof. exact (MK_COMB (@lem7043307) (@lem7043324 i n)). Qed.
Lemma lem7043326 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7043333 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7043334 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7043333 nat (nat -> Prop) f x). Qed.
Lemma lem7043335 (m : nat) : (Peano.le m) = (@I (nat -> nat -> Prop) Peano.le m).
Proof. exact (@lem7043334 Peano.le m). Qed.
Lemma lem7043336 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem7043337 (m : nat) (i : nat) : (Peano.le m i) = (@I (nat -> nat -> Prop) Peano.le m i).
Proof. exact (MK_COMB (@lem7043335 m) (@lem7043336 i)). Qed.
Lemma lem7043339 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7043340 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7043339 nat Prop f x). Qed.
Lemma lem7043341 (m : nat) (i : nat) : (@I (nat -> nat -> Prop) Peano.le m i) = (term429 m i).
Proof. exact (@lem7043340 (@I (nat -> nat -> Prop) Peano.le m) i). Qed.
Lemma lem7043343 (m : nat) (i : nat) : (Peano.le m i) = (term429 m i).
Proof. exact (TRANS (@lem7043337 m i) (@lem7043341 m i)). Qed.
Lemma lem7043344 (m : nat) (i : nat) : (term448 m i) = (term449 m i).
Proof. exact (MK_COMB (@lem7043326) (@lem7043343 m i)). Qed.
Lemma lem7043345 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7043346 (m : nat) (i : nat) : (term450 m i) = (term451 m i).
Proof. exact (MK_COMB (@lem7043345) (@lem7043344 m i)). Qed.
Lemma lem7043347 (m : nat) (i : nat) (n : nat) : (term77 m i n) = (term452 m i n).
Proof. exact (MK_COMB (@lem7043346 m i) (@lem7043325 i n)). Qed.
Lemma lem7043348 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7043349 (m : nat) (i : nat) (n : nat) : (term79 m i n) = (term514 m i n).
Proof. exact (MK_COMB (@lem7043348) (@lem7043347 m i n)). Qed.
Lemma lem7043350 (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) (i : nat) : (term81 m n f g i) = (term515 m n f g i).
Proof. exact (MK_COMB (@lem7043349 m i n) (@lem7043306 f g i)). Qed.
Lemma lem7043351 (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) : (term82 m n f g) = (term516 m n f g).
Proof. exact (fun_ext (fun i : nat => @lem7043350 m n f g i)). Qed.
Lemma lem7043352 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7043353 (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) : (term83 m n f g) = (term517 m n f g).
Proof. exact (MK_COMB (@lem7043352) (@lem7043351 m n f g)). Qed.
Lemma lem7043354 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7043355 (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) : (term86 m n f g) = (term518 m n f g).
Proof. exact (MK_COMB (@lem7043354) (@lem7043353 m n f g)). Qed.
Lemma lem7043356 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) : (term88 f m n g) = (term519 f m n g).
Proof. exact (MK_COMB (@lem7043355 m n f g) (@lem7043287 f m n g)). Qed.
Lemma lem7043357 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (h1 : term88 f m n g) : term519 f m n g.
Proof. exact (EQ_MP (@lem7043356 f m n g) (@lem7042679 f m n g h1)). Qed.
Lemma lem7043359 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (h1 : term88 f m n g) : term517 m n f g.
Proof. exact (proj1 (@lem7043357 f m n g h1)). Qed.
Lemma lem7043360 (h1 : term62) : term447.
Proof. exact (proj2 (@lem7042853 h1)). Qed.
Lemma lem7043389 (x : type999) (f : nat -> nat) (s : nat -> Prop) (g : nat -> nat) : (term493 x f s g) = (term520 x f s g).
Proof. exact (@lem19699 (term485 x f g s) (term478 x f g s) ((term463 s f) = (term463 s g))). Qed.
Lemma lem7043390 (x : type999) (f : nat -> nat) (g : nat -> nat) : (term495 x f g) = (term521 x f g).
Proof. exact (fun_ext (fun s : nat -> Prop => @lem7043389 x f s g)). Qed.
Lemma lem7043391 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem7043392 (x : type999) (f : nat -> nat) (g : nat -> nat) : (term497 x f g) = (term522 x f g).
Proof. exact (MK_COMB (@lem7043391) (@lem7043390 x f g)). Qed.
Lemma lem7043393 (x : type999) (f : nat -> nat) : (term499 x f) = (term523 x f).
Proof. exact (fun_ext (fun g : nat -> nat => @lem7043392 x f g)). Qed.
Lemma lem7043394 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7043395 (x : type999) (f : nat -> nat) : (term500 x f) = (term524 x f).
Proof. exact (MK_COMB (@lem7043394) (@lem7043393 x f)). Qed.
Lemma lem7043396 (x : type999) : (term501 x) = (term525 x).
Proof. exact (fun_ext (fun f : nat -> nat => @lem7043395 x f)). Qed.
Lemma lem7043397 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7043399 (x : type999) : (term502 x) = (term526 x).
Proof. exact (MK_COMB (@lem7043397) (@lem7043396 x)). Qed.
Lemma lem7043400 (x : type999) (h1 : term425 x) : term526 x.
Proof. exact (EQ_MP (@lem7043399 x) (@lem7043050 x h1)). Qed.
Lemma lem7043443 (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) (i : nat) : (term515 m n f g i) = (term515 m n f g i).
Proof. exact (eq_refl (term515 m n f g i)). Qed.
Lemma lem7043444 (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) : (term516 m n f g) = (term516 m n f g).
Proof. exact (fun_ext (fun i : nat => @lem7043443 m n f g i)). Qed.
Lemma lem7043445 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7043447 (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) : (term517 m n f g) = (term517 m n f g).
Proof. exact (MK_COMB (@lem7043445) (@lem7043444 m n f g)). Qed.
Lemma lem7043448 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (h1 : term88 f m n g) : term517 m n f g.
Proof. exact (EQ_MP (@lem7043447 m n f g) (@lem7043359 f m n g h1)). Qed.
Lemma lem7043495 (m : nat) (p : nat) (n : nat) : (term441 m p n) = (term527 m p n).
Proof. exact (@lem19490 (term429 m p) (term438 p m n) (term429 p n)). Qed.
Lemma lem7043496 (m : nat) (n : nat) : (term442 m n) = (term528 m n).
Proof. exact (fun_ext (fun p : nat => @lem7043495 m p n)). Qed.
Lemma lem7043497 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7043498 (m : nat) (n : nat) : (term443 m n) = (term529 m n).
Proof. exact (MK_COMB (@lem7043497) (@lem7043496 m n)). Qed.
Lemma lem7043499 (m : nat) : (term444 m) = (term530 m).
Proof. exact (fun_ext (fun n : nat => @lem7043498 m n)). Qed.
Lemma lem7043500 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7043501 (m : nat) : (term445 m) = (term531 m).
Proof. exact (MK_COMB (@lem7043500) (@lem7043499 m)). Qed.
Lemma lem7043502 : term446 = term532.
Proof. exact (fun_ext (fun m : nat => @lem7043501 m)). Qed.
Lemma lem7043503 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7043505 : term447 = term533.
Proof. exact (MK_COMB (@lem7043503) (@lem7043502)). Qed.
Lemma lem7043506 (h1 : term62) : term533.
Proof. exact (EQ_MP (@lem7043505) (@lem7043360 h1)). Qed.
Lemma lem7043513 (_94007 : nat -> nat) (x : type999) (h1 : term425 x) : term534 x _94007.
Proof. exact (@lem7043400 x h1 _94007). Qed.
Lemma lem7043514 (x : type999) (_94007 : nat -> nat) : (term534 x _94007) = (term524 x _94007).
Proof. exact (eq_refl (term534 x _94007)). Qed.
Lemma lem7043515 (_94007 : nat -> nat) (x : type999) (h1 : term425 x) : term524 x _94007.
Proof. exact (EQ_MP (@lem7043514 x _94007) (@lem7043513 _94007 x h1)). Qed.
Lemma lem7043516 (_94007 : nat -> nat) (_94008 : nat -> nat) (x : type999) (h1 : term425 x) : term535 x _94007 _94008.
Proof. exact (@lem7043515 _94007 x h1 _94008). Qed.
Lemma lem7043517 (x : type999) (_94007 : nat -> nat) (_94008 : nat -> nat) : (term535 x _94007 _94008) = (term522 x _94007 _94008).
Proof. exact (eq_refl (term535 x _94007 _94008)). Qed.
Lemma lem7043518 (_94007 : nat -> nat) (_94008 : nat -> nat) (x : type999) (h1 : term425 x) : term522 x _94007 _94008.
Proof. exact (EQ_MP (@lem7043517 x _94007 _94008) (@lem7043516 _94007 _94008 x h1)). Qed.
Lemma lem7043519 (_94007 : nat -> nat) (_94008 : nat -> nat) (_94009 : nat -> Prop) (x : type999) (h1 : term425 x) : term536 x _94007 _94008 _94009.
Proof. exact (@lem7043518 _94007 _94008 x h1 _94009). Qed.
Lemma lem7043520 (x : type999) (_94007 : nat -> nat) (_94009 : nat -> Prop) (_94008 : nat -> nat) : (term536 x _94007 _94008 _94009) = (term520 x _94007 _94009 _94008).
Proof. exact (eq_refl (term536 x _94007 _94008 _94009)). Qed.
Lemma lem7043521 (_94007 : nat -> nat) (_94009 : nat -> Prop) (_94008 : nat -> nat) (x : type999) (h1 : term425 x) : term520 x _94007 _94009 _94008.
Proof. exact (EQ_MP (@lem7043520 x _94007 _94009 _94008) (@lem7043519 _94007 _94008 _94009 x h1)). Qed.
Lemma lem7043531 (_94013 : nat) (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (h1 : term88 f m n g) : term537 m n f g _94013.
Proof. exact (@lem7043448 f m n g h1 _94013). Qed.
Lemma lem7043532 (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) (_94013 : nat) : (term537 m n f g _94013) = (term515 m n f g _94013).
Proof. exact (eq_refl (term537 m n f g _94013)). Qed.
Lemma lem7043533 (_94013 : nat) (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (h1 : term88 f m n g) : term515 m n f g _94013.
Proof. exact (EQ_MP (@lem7043532 m n f g _94013) (@lem7043531 _94013 f m n g h1)). Qed.
Lemma lem7043543 (_94017 : nat) (h1 : term62) : term538 _94017.
Proof. exact (@lem7043506 h1 _94017). Qed.
Lemma lem7043544 (_94017 : nat) : (term538 _94017) = (term531 _94017).
Proof. exact (eq_refl (term538 _94017)). Qed.
Lemma lem7043545 (_94017 : nat) (h1 : term62) : term531 _94017.
Proof. exact (EQ_MP (@lem7043544 _94017) (@lem7043543 _94017 h1)). Qed.
Lemma lem7043546 (_94017 : nat) (_94018 : nat) (h1 : term62) : term539 _94017 _94018.
Proof. exact (@lem7043545 _94017 h1 _94018). Qed.
Lemma lem7043547 (_94017 : nat) (_94018 : nat) : (term539 _94017 _94018) = (term529 _94017 _94018).
Proof. exact (eq_refl (term539 _94017 _94018)). Qed.
Lemma lem7043548 (_94017 : nat) (_94018 : nat) (h1 : term62) : term529 _94017 _94018.
Proof. exact (EQ_MP (@lem7043547 _94017 _94018) (@lem7043546 _94017 _94018 h1)). Qed.
Lemma lem7043549 (_94017 : nat) (_94018 : nat) (_94019 : nat) (h1 : term62) : term540 _94017 _94018 _94019.
Proof. exact (@lem7043548 _94017 _94018 h1 _94019). Qed.
Lemma lem7043550 (_94017 : nat) (_94019 : nat) (_94018 : nat) : (term540 _94017 _94018 _94019) = (term527 _94017 _94019 _94018).
Proof. exact (eq_refl (term540 _94017 _94018 _94019)). Qed.
Lemma lem7043551 (_94017 : nat) (_94019 : nat) (_94018 : nat) (h1 : term62) : term527 _94017 _94019 _94018.
Proof. exact (EQ_MP (@lem7043550 _94017 _94019 _94018) (@lem7043549 _94017 _94018 _94019 h1)). Qed.
Lemma lem7043570 (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) (_94013 : nat) : (term515 m n f g _94013) = (term541 m n f g _94013).
Proof. exact (@lem7041106 (term449 m _94013) (term449 _94013 n) ((@I (nat -> nat) f _94013) = (@I (nat -> nat) g _94013))). Qed.
Lemma lem7043571 (_94013 : nat) (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (h1 : term88 f m n g) : term541 m n f g _94013.
Proof. exact (EQ_MP (@lem7043570 m n f g _94013) (@lem7043533 _94013 f m n g h1)). Qed.
Lemma lem7043573 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (h1 : term88 f m n g) : term511 f m n g.
Proof. exact (proj2 (@lem7043357 f m n g h1)). Qed.
Lemma lem7043589 (_94018 : nat) (_94017 : nat) (_94019 : nat) (h1 : term62) : term542 _94018 _94017 _94019.
Proof. exact (proj1 (@lem7043551 _94017 _94019 _94018 h1)). Qed.
Lemma lem7043595 (_94017 : nat) (_94019 : nat) (_94018 : nat) (h1 : term62) : term543 _94017 _94019 _94018.
Proof. exact (proj2 (@lem7043551 _94017 _94019 _94018 h1)). Qed.
Lemma lem7043613 (_94007 : nat -> nat) (_94009 : nat -> Prop) (_94008 : nat -> nat) (x : type999) (h1 : term425 x) : term544 x _94007 _94009 _94008.
Proof. exact (proj1 (@lem7043521 _94007 _94009 _94008 x h1)). Qed.
Lemma lem7043619 (_94007 : nat -> nat) (_94009 : nat -> Prop) (_94008 : nat -> nat) (x : type999) (h1 : term425 x) : term545 x _94007 _94009 _94008.
Proof. exact (proj2 (@lem7043521 _94007 _94009 _94008 x h1)). Qed.
Lemma lem7043963 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (h1 : term511 f m n g) : term511 f m n g.
Proof. exact (h1). Qed.
Lemma lem7043964 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (h1 : term511 f m n g) : term546 f m n g.
Proof. exact (fun h0 : (term508 m n f) = (term508 m n g) => @lem7043963 f m n g h1). Qed.
Lemma lem7043966 (p : Prop) : (term547 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7043967 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) : (term546 f m n g) = (term511 f m n g).
Proof. exact (@lem7043966 ((term508 m n f) = (term508 m n g))). Qed.
Lemma lem7043968 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (h1 : term511 f m n g) : term511 f m n g.
Proof. exact (EQ_MP (@lem7043967 f m n g) (@lem7043964 f m n g h1)). Qed.
Lemma lem7043970 (b : Prop) (a : Prop) : (a \/ b) = (term548 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7043973 (x : type999) (_94007 : nat -> nat) (_94008 : nat -> nat) (_94009 : nat -> Prop) : (term544 x _94007 _94009 _94008) = (term549 x _94007 _94008 _94009).
Proof. exact (@lem7043970 ((term463 _94009 _94007) = (term463 _94009 _94008)) (term485 x _94007 _94008 _94009)). Qed.
Lemma lem7043976 (_94007 : nat -> nat) (_94008 : nat -> nat) (_94009 : nat -> Prop) (x : type999) (h1 : term425 x) : term549 x _94007 _94008 _94009.
Proof. exact (EQ_MP (@lem7043973 x _94007 _94008 _94009) (@lem7043613 _94007 _94009 _94008 x h1)). Qed.
Lemma lem7043977 (f : nat -> nat) (g : nat -> nat) (m : nat) (n : nat) (x : type999) (h1 : term425 x) : term550 x f g m n.
Proof. exact (@lem7043976 f g (term433 m n) x h1). Qed.
Lemma lem7043980 (x : type999) (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (h1 : term425 x) (h2 : term511 f m n g) : term551 x f g m n.
Proof. exact (@lem7043977 f g m n x h1 (@lem7043968 f m n g h2)). Qed.
Lemma lem7043981 (x : type999) (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (h1 : term425 x) (h2 : term511 f m n g) : term552 x f g m n.
Proof. exact (fun h0 : term553 x f g m n => @lem7043980 x f m n g h1 h2). Qed.
Lemma lem7043983 (p : Prop) : (term554 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7043984 (x : type999) (f : nat -> nat) (g : nat -> nat) (m : nat) (n : nat) : (term552 x f g m n) = (term551 x f g m n).
Proof. exact (@lem7043983 (term551 x f g m n)). Qed.
Lemma lem7043985 (x : type999) (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (h1 : term425 x) (h2 : term511 f m n g) : term551 x f g m n.
Proof. exact (EQ_MP (@lem7043984 x f g m n) (@lem7043981 x f m n g h1 h2)). Qed.
Lemma lem7043991 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7043992 (_94019 : nat) (_94017 : nat) (_94018 : nat) : (term542 _94018 _94017 _94019) = (term555 _94019 _94017 _94018).
Proof. exact (@lem7043991 (term429 _94017 _94019) (term438 _94019 _94017 _94018)). Qed.
Lemma lem7043998 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7043999 (_94019 : nat) (_94017 : nat) (_94018 : nat) : (term556 _94018 _94017 _94019) = (term557 _94019 _94017 _94018).
Proof. exact (MK_COMB (@lem7043998) (@lem7043992 _94019 _94017 _94018)). Qed.
Lemma lem7044005 (_94019 : nat) (_94017 : nat) (_94018 : nat) : (term555 _94019 _94017 _94018) = (term555 _94019 _94017 _94018).
Proof. exact (eq_refl (term555 _94019 _94017 _94018)). Qed.
Lemma lem7044006 (_94019 : nat) (_94017 : nat) (_94018 : nat) : ((term542 _94018 _94017 _94019) = (term555 _94019 _94017 _94018)) = ((term555 _94019 _94017 _94018) = (term555 _94019 _94017 _94018)).
Proof. exact (MK_COMB (@lem7043999 _94019 _94017 _94018) (@lem7044005 _94019 _94017 _94018)). Qed.
Lemma lem7044008 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7044009 (x : Prop) : (x = x) = True.
Proof. exact (@lem7044008 Prop x). Qed.
Lemma lem7044010 (_94019 : nat) (_94017 : nat) (_94018 : nat) : ((term555 _94019 _94017 _94018) = (term555 _94019 _94017 _94018)) = True.
Proof. exact (@lem7044009 (term555 _94019 _94017 _94018)). Qed.
Lemma lem7044011 (_94019 : nat) (_94017 : nat) (_94018 : nat) : ((term542 _94018 _94017 _94019) = (term555 _94019 _94017 _94018)) = True.
Proof. exact (TRANS (@lem7044006 _94019 _94017 _94018) (@lem7044010 _94019 _94017 _94018)). Qed.
Lemma lem7044012 (_94019 : nat) (_94017 : nat) (_94018 : nat) : True = ((term542 _94018 _94017 _94019) = (term555 _94019 _94017 _94018)).
Proof. exact (SYM (@lem7044011 _94019 _94017 _94018)). Qed.
Lemma lem7044013 (_94019 : nat) (_94017 : nat) (_94018 : nat) : (term542 _94018 _94017 _94019) = (term555 _94019 _94017 _94018).
Proof. exact (EQ_MP (@lem7044012 _94019 _94017 _94018) (@lem0)). Qed.
Lemma lem7044014 (_94019 : nat) (_94017 : nat) (_94018 : nat) (h1 : term62) : term555 _94019 _94017 _94018.
Proof. exact (EQ_MP (@lem7044013 _94019 _94017 _94018) (@lem7043589 _94018 _94017 _94019 h1)). Qed.
Lemma lem7044016 (b : Prop) (a : Prop) : (a \/ b) = (term548 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7044017 (_94018 : nat) (_94017 : nat) (_94019 : nat) : (term555 _94019 _94017 _94018) = (term558 _94018 _94017 _94019).
Proof. exact (@lem7044016 (term438 _94019 _94017 _94018) (term429 _94017 _94019)). Qed.
Lemma lem7044019 (a : Prop) : (term559 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7044020 (_94019 : nat) (_94017 : nat) (_94018 : nat) : (term560 _94019 _94017 _94018) = (term436 _94019 _94017 _94018).
Proof. exact (@lem7044019 (term436 _94019 _94017 _94018)). Qed.
Lemma lem7044021 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7044022 (_94019 : nat) (_94017 : nat) (_94018 : nat) : (term561 _94019 _94017 _94018) = (term562 _94019 _94017 _94018).
Proof. exact (MK_COMB (@lem7044021) (@lem7044020 _94019 _94017 _94018)). Qed.
Lemma lem7044023 (_94017 : nat) (_94019 : nat) : (term429 _94017 _94019) = (term429 _94017 _94019).
Proof. exact (eq_refl (term429 _94017 _94019)). Qed.
Lemma lem7044024 (_94018 : nat) (_94017 : nat) (_94019 : nat) : (term558 _94018 _94017 _94019) = (term563 _94018 _94017 _94019).
Proof. exact (MK_COMB (@lem7044022 _94019 _94017 _94018) (@lem7044023 _94017 _94019)). Qed.
Lemma lem7044025 (_94018 : nat) (_94017 : nat) (_94019 : nat) : (term555 _94019 _94017 _94018) = (term563 _94018 _94017 _94019).
Proof. exact (TRANS (@lem7044017 _94018 _94017 _94019) (@lem7044024 _94018 _94017 _94019)). Qed.
Lemma lem7044028 (_94018 : nat) (_94017 : nat) (_94019 : nat) (h1 : term62) : term563 _94018 _94017 _94019.
Proof. exact (EQ_MP (@lem7044025 _94018 _94017 _94019) (@lem7044014 _94019 _94017 _94018 h1)). Qed.
Lemma lem7044029 (x : type999) (f : nat -> nat) (g : nat -> nat) (m : nat) (n : nat) (h1 : term62) : term564 x f g m n.
Proof. exact (@lem7044028 n m (term565 x f g m n) h1). Qed.
Lemma lem7044032 (x : type999) (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (h1 : term425 x) (h2 : term62) (h3 : term511 f m n g) : term566 x f g m n.
Proof. exact (@lem7044029 x f g m n h2 (@lem7043985 x f m n g h1 h3)). Qed.
Lemma lem7044033 (x : type999) (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (h1 : term425 x) (h2 : term62) (h3 : term511 f m n g) : term567 x f g m n.
Proof. exact (fun h0 : term568 x f g m n => @lem7044032 x f m n g h1 h2 h3). Qed.
Lemma lem7044035 (p : Prop) : (term554 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7044036 (x : type999) (f : nat -> nat) (g : nat -> nat) (m : nat) (n : nat) : (term567 x f g m n) = (term566 x f g m n).
Proof. exact (@lem7044035 (term566 x f g m n)). Qed.
Lemma lem7044037 (x : type999) (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (h1 : term425 x) (h2 : term62) (h3 : term511 f m n g) : term566 x f g m n.
Proof. exact (EQ_MP (@lem7044036 x f g m n) (@lem7044033 x f m n g h1 h2 h3)). Qed.
Lemma lem7044040 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (h1 : term511 f m n g) : term511 f m n g.
Proof. exact (h1). Qed.
Lemma lem7044041 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (h1 : term511 f m n g) : term546 f m n g.
Proof. exact (fun h0 : (term508 m n f) = (term508 m n g) => @lem7044040 f m n g h1). Qed.
Lemma lem7044043 (p : Prop) : (term547 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7044044 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) : (term546 f m n g) = (term511 f m n g).
Proof. exact (@lem7044043 ((term508 m n f) = (term508 m n g))). Qed.
Lemma lem7044045 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (h1 : term511 f m n g) : term511 f m n g.
Proof. exact (EQ_MP (@lem7044044 f m n g) (@lem7044041 f m n g h1)). Qed.
Lemma lem7044047 (b : Prop) (a : Prop) : (a \/ b) = (term548 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7044050 (x : type999) (_94007 : nat -> nat) (_94008 : nat -> nat) (_94009 : nat -> Prop) : (term545 x _94007 _94009 _94008) = (term569 x _94007 _94008 _94009).
Proof. exact (@lem7044047 ((term463 _94009 _94007) = (term463 _94009 _94008)) (term478 x _94007 _94008 _94009)). Qed.
Lemma lem7044053 (_94007 : nat -> nat) (_94008 : nat -> nat) (_94009 : nat -> Prop) (x : type999) (h1 : term425 x) : term569 x _94007 _94008 _94009.
Proof. exact (EQ_MP (@lem7044050 x _94007 _94008 _94009) (@lem7043619 _94007 _94009 _94008 x h1)). Qed.
Lemma lem7044054 (f : nat -> nat) (g : nat -> nat) (m : nat) (n : nat) (x : type999) (h1 : term425 x) : term570 x f g m n.
Proof. exact (@lem7044053 f g (term433 m n) x h1). Qed.
Lemma lem7044057 (x : type999) (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (h1 : term425 x) (h2 : term511 f m n g) : term571 x f g m n.
Proof. exact (@lem7044054 f g m n x h1 (@lem7044045 f m n g h2)). Qed.
Lemma lem7044058 (x : type999) (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (h1 : term425 x) (h2 : term511 f m n g) : term572 x f g m n.
Proof. exact (fun h0 : (term573 x f g m n) = (term574 x f g m n) => @lem7044057 x f m n g h1 h2). Qed.
Lemma lem7044060 (p : Prop) : (term547 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7044061 (x : type999) (f : nat -> nat) (g : nat -> nat) (m : nat) (n : nat) : (term572 x f g m n) = (term571 x f g m n).
Proof. exact (@lem7044060 ((term573 x f g m n) = (term574 x f g m n))). Qed.
Lemma lem7044062 (x : type999) (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (h1 : term425 x) (h2 : term511 f m n g) : term571 x f g m n.
Proof. exact (EQ_MP (@lem7044061 x f g m n) (@lem7044058 x f m n g h1 h2)). Qed.
Lemma lem7044068 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7044069 (n : nat) (m : nat) (f : nat -> nat) (g : nat -> nat) (_94013 : nat) : (term541 m n f g _94013) = (term575 n m f g _94013).
Proof. exact (@lem7044068 (term449 _94013 n) (term449 m _94013) ((@I (nat -> nat) f _94013) = (@I (nat -> nat) g _94013))). Qed.
Lemma lem7044083 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7044084 (f : nat -> nat) (g : nat -> nat) (m : nat) (_94013 : nat) : (term576 m f g _94013) = (term577 f g m _94013).
Proof. exact (@lem7044083 ((@I (nat -> nat) f _94013) = (@I (nat -> nat) g _94013)) (term449 m _94013)). Qed.
Lemma lem7044092 (_94013 : nat) (n : nat) : (term451 _94013 n) = (term451 _94013 n).
Proof. exact (eq_refl (term451 _94013 n)). Qed.
Lemma lem7044093 (n : nat) (f : nat -> nat) (g : nat -> nat) (m : nat) (_94013 : nat) : (term575 n m f g _94013) = (term578 n f g m _94013).
Proof. exact (MK_COMB (@lem7044092 _94013 n) (@lem7044084 f g m _94013)). Qed.
Lemma lem7044097 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7044098 (f : nat -> nat) (g : nat -> nat) (n : nat) (m : nat) (_94013 : nat) : (term578 n f g m _94013) = (term579 f g n m _94013).
Proof. exact (@lem7044097 ((@I (nat -> nat) f _94013) = (@I (nat -> nat) g _94013)) (term449 _94013 n) (term449 m _94013)). Qed.
Lemma lem7044116 (f : nat -> nat) (g : nat -> nat) (n : nat) (m : nat) (_94013 : nat) : (term575 n m f g _94013) = (term579 f g n m _94013).
Proof. exact (TRANS (@lem7044093 n f g m _94013) (@lem7044098 f g n m _94013)). Qed.
Lemma lem7044117 (f : nat -> nat) (g : nat -> nat) (n : nat) (m : nat) (_94013 : nat) : (term541 m n f g _94013) = (term579 f g n m _94013).
Proof. exact (TRANS (@lem7044069 n m f g _94013) (@lem7044116 f g n m _94013)). Qed.
Lemma lem7044118 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7044119 (f : nat -> nat) (g : nat -> nat) (n : nat) (m : nat) (_94013 : nat) : (term580 m n f g _94013) = (term581 f g n m _94013).
Proof. exact (MK_COMB (@lem7044118) (@lem7044117 f g n m _94013)). Qed.
Lemma lem7044133 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7044134 (f : nat -> nat) (g : nat -> nat) (m : nat) (_94013 : nat) : (term576 m f g _94013) = (term577 f g m _94013).
Proof. exact (@lem7044133 ((@I (nat -> nat) f _94013) = (@I (nat -> nat) g _94013)) (term449 m _94013)). Qed.
Lemma lem7044142 (_94013 : nat) (n : nat) : (term451 _94013 n) = (term451 _94013 n).
Proof. exact (eq_refl (term451 _94013 n)). Qed.
Lemma lem7044143 (n : nat) (f : nat -> nat) (g : nat -> nat) (m : nat) (_94013 : nat) : (term575 n m f g _94013) = (term578 n f g m _94013).
Proof. exact (MK_COMB (@lem7044142 _94013 n) (@lem7044134 f g m _94013)). Qed.
Lemma lem7044147 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7044148 (f : nat -> nat) (g : nat -> nat) (n : nat) (m : nat) (_94013 : nat) : (term578 n f g m _94013) = (term579 f g n m _94013).
Proof. exact (@lem7044147 ((@I (nat -> nat) f _94013) = (@I (nat -> nat) g _94013)) (term449 _94013 n) (term449 m _94013)). Qed.
Lemma lem7044166 (f : nat -> nat) (g : nat -> nat) (n : nat) (m : nat) (_94013 : nat) : (term575 n m f g _94013) = (term579 f g n m _94013).
Proof. exact (TRANS (@lem7044143 n f g m _94013) (@lem7044148 f g n m _94013)). Qed.
Lemma lem7044167 (f : nat -> nat) (g : nat -> nat) (n : nat) (m : nat) (_94013 : nat) : ((term541 m n f g _94013) = (term575 n m f g _94013)) = ((term579 f g n m _94013) = (term579 f g n m _94013)).
Proof. exact (MK_COMB (@lem7044119 f g n m _94013) (@lem7044166 f g n m _94013)). Qed.
Lemma lem7044169 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7044170 (x : Prop) : (x = x) = True.
Proof. exact (@lem7044169 Prop x). Qed.
Lemma lem7044171 (f : nat -> nat) (g : nat -> nat) (n : nat) (m : nat) (_94013 : nat) : ((term579 f g n m _94013) = (term579 f g n m _94013)) = True.
Proof. exact (@lem7044170 (term579 f g n m _94013)). Qed.
Lemma lem7044172 (n : nat) (m : nat) (f : nat -> nat) (g : nat -> nat) (_94013 : nat) : ((term541 m n f g _94013) = (term575 n m f g _94013)) = True.
Proof. exact (TRANS (@lem7044167 f g n m _94013) (@lem7044171 f g n m _94013)). Qed.
Lemma lem7044173 (n : nat) (m : nat) (f : nat -> nat) (g : nat -> nat) (_94013 : nat) : True = ((term541 m n f g _94013) = (term575 n m f g _94013)).
Proof. exact (SYM (@lem7044172 n m f g _94013)). Qed.
Lemma lem7044174 (n : nat) (m : nat) (f : nat -> nat) (g : nat -> nat) (_94013 : nat) : (term541 m n f g _94013) = (term575 n m f g _94013).
Proof. exact (EQ_MP (@lem7044173 n m f g _94013) (@lem0)). Qed.
Lemma lem7044175 (_94013 : nat) (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (h1 : term88 f m n g) : term575 n m f g _94013.
Proof. exact (EQ_MP (@lem7044174 n m f g _94013) (@lem7043571 _94013 f m n g h1)). Qed.
Lemma lem7044177 (b : Prop) (a : Prop) : (a \/ b) = (term548 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7044178 (m : nat) (f : nat -> nat) (g : nat -> nat) (_94013 : nat) (n : nat) : (term575 n m f g _94013) = (term582 m f g _94013 n).
Proof. exact (@lem7044177 (term576 m f g _94013) (term449 _94013 n)). Qed.
Lemma lem7044180 (a : Prop) (b : Prop) : (term583 a b) = (term584 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7044181 (m : nat) (f : nat -> nat) (g : nat -> nat) (_94013 : nat) : (term585 m f g _94013) = (term586 m f g _94013).
Proof. exact (@lem7044180 (term449 m _94013) ((@I (nat -> nat) f _94013) = (@I (nat -> nat) g _94013))). Qed.
Lemma lem7044183 (a : Prop) : (term559 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7044184 (m : nat) (_94013 : nat) : (term587 m _94013) = (term429 m _94013).
Proof. exact (@lem7044183 (term429 m _94013)). Qed.
Lemma lem7044185 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7044186 (m : nat) (_94013 : nat) : (term588 m _94013) = (term431 m _94013).
Proof. exact (MK_COMB (@lem7044185) (@lem7044184 m _94013)). Qed.
Lemma lem7044187 (f : nat -> nat) (g : nat -> nat) (_94013 : nat) : (term589 f g _94013) = (term589 f g _94013).
Proof. exact (eq_refl (term589 f g _94013)). Qed.
Lemma lem7044188 (m : nat) (f : nat -> nat) (g : nat -> nat) (_94013 : nat) : (term586 m f g _94013) = (term590 m f g _94013).
Proof. exact (MK_COMB (@lem7044186 m _94013) (@lem7044187 f g _94013)). Qed.
Lemma lem7044189 (m : nat) (f : nat -> nat) (g : nat -> nat) (_94013 : nat) : (term585 m f g _94013) = (term590 m f g _94013).
Proof. exact (TRANS (@lem7044181 m f g _94013) (@lem7044188 m f g _94013)). Qed.
Lemma lem7044190 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7044191 (m : nat) (f : nat -> nat) (g : nat -> nat) (_94013 : nat) : (term591 m f g _94013) = (term592 m f g _94013).
Proof. exact (MK_COMB (@lem7044190) (@lem7044189 m f g _94013)). Qed.
Lemma lem7044192 (_94013 : nat) (n : nat) : (term449 _94013 n) = (term449 _94013 n).
Proof. exact (eq_refl (term449 _94013 n)). Qed.
Lemma lem7044193 (m : nat) (f : nat -> nat) (g : nat -> nat) (_94013 : nat) (n : nat) : (term582 m f g _94013 n) = (term593 m f g _94013 n).
Proof. exact (MK_COMB (@lem7044191 m f g _94013) (@lem7044192 _94013 n)). Qed.
Lemma lem7044194 (m : nat) (f : nat -> nat) (g : nat -> nat) (_94013 : nat) (n : nat) : (term575 n m f g _94013) = (term593 m f g _94013 n).
Proof. exact (TRANS (@lem7044178 m f g _94013 n) (@lem7044193 m f g _94013 n)). Qed.
Lemma lem7044196 (x : type999) (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (h1 : term425 x) (h2 : term62) (h3 : term511 f m n g) : term594 x f g m n.
Proof. exact (conj (@lem7044037 x f m n g h1 h2 h3) (@lem7044062 x f m n g h1 h3)). Qed.
Lemma lem7044198 (_94013 : nat) (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (h1 : term88 f m n g) : term593 m f g _94013 n.
Proof. exact (EQ_MP (@lem7044194 m f g _94013 n) (@lem7044175 _94013 f m n g h1)). Qed.
Lemma lem7044199 (x : type999) (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (h1 : term88 f m n g) : term595 x f g m n.
Proof. exact (@lem7044198 (term565 x f g m n) f m n g h1). Qed.
Lemma lem7044202 (x : type999) (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (h1 : term425 x) (h2 : term62) (h3 : term511 f m n g) (h4 : term88 f m n g) : term596 x f g m n.
Proof. exact (@lem7044199 x f m n g h4 (@lem7044196 x f m n g h1 h2 h3)). Qed.
Lemma lem7044203 (x : type999) (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (h1 : term425 x) (h2 : term62) (h3 : term511 f m n g) (h4 : term88 f m n g) : term597 x f g m n.
Proof. exact (fun h0 : term598 x f g m n => @lem7044202 x f m n g h1 h2 h3 h4). Qed.
Lemma lem7044205 (p : Prop) : (term547 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7044206 (x : type999) (f : nat -> nat) (g : nat -> nat) (m : nat) (n : nat) : (term597 x f g m n) = (term596 x f g m n).
Proof. exact (@lem7044205 (term598 x f g m n)). Qed.
Lemma lem7044207 (x : type999) (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (h1 : term425 x) (h2 : term62) (h3 : term511 f m n g) (h4 : term88 f m n g) : term596 x f g m n.
Proof. exact (EQ_MP (@lem7044206 x f g m n) (@lem7044203 x f m n g h1 h2 h3 h4)). Qed.
Lemma lem7044209 (b : Prop) (a : Prop) : (a \/ b) = (term548 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7044212 (_94019 : nat) (_94017 : nat) (_94018 : nat) : (term543 _94017 _94019 _94018) = (term599 _94019 _94017 _94018).
Proof. exact (@lem7044209 (term429 _94019 _94018) (term438 _94019 _94017 _94018)). Qed.
Lemma lem7044215 (_94019 : nat) (_94017 : nat) (_94018 : nat) (h1 : term62) : term599 _94019 _94017 _94018.
Proof. exact (EQ_MP (@lem7044212 _94019 _94017 _94018) (@lem7043595 _94017 _94019 _94018 h1)). Qed.
Lemma lem7044216 (x : type999) (f : nat -> nat) (g : nat -> nat) (m : nat) (_94017 : nat) (n : nat) (h1 : term62) : term600 x f g m _94017 n.
Proof. exact (@lem7044215 (term565 x f g m n) _94017 n h1). Qed.
Lemma lem7044219 (_94017 : nat) (x : type999) (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (h1 : term425 x) (h2 : term62) (h3 : term511 f m n g) (h4 : term88 f m n g) : term601 x f g m _94017 n.
Proof. exact (@lem7044216 x f g m _94017 n h2 (@lem7044207 x f m n g h1 h2 h3 h4)). Qed.
Lemma lem7044220 (x : type999) (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (h1 : term425 x) (h2 : term62) (h3 : term511 f m n g) (h4 : term88 f m n g) : term553 x f g m n.
Proof. exact (@lem7044219 m x f m n g h1 h2 h3 h4). Qed.
Lemma lem7044221 (x : type999) (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (h1 : term425 x) (h2 : term62) (h3 : term511 f m n g) (h4 : term88 f m n g) : term602 x f g m n.
Proof. exact (fun h0 : term551 x f g m n => @lem7044220 x f m n g h1 h2 h3 h4). Qed.
Lemma lem7044223 (p : Prop) : (term547 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7044224 (x : type999) (f : nat -> nat) (g : nat -> nat) (m : nat) (n : nat) : (term602 x f g m n) = (term553 x f g m n).
Proof. exact (@lem7044223 (term551 x f g m n)). Qed.
Lemma lem7044225 (x : type999) (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (h1 : term425 x) (h2 : term62) (h3 : term511 f m n g) (h4 : term88 f m n g) : term553 x f g m n.
Proof. exact (EQ_MP (@lem7044224 x f g m n) (@lem7044221 x f m n g h1 h2 h3 h4)). Qed.
Lemma lem7044231 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7044232 (x : type999) (_94007 : nat -> nat) (_94008 : nat -> nat) (_94009 : nat -> Prop) : (term544 x _94007 _94009 _94008) = (term603 x _94007 _94008 _94009).
Proof. exact (@lem7044231 ((term463 _94009 _94007) = (term463 _94009 _94008)) (term485 x _94007 _94008 _94009)). Qed.
Lemma lem7044240 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7044241 (x : type999) (_94007 : nat -> nat) (_94008 : nat -> nat) (_94009 : nat -> Prop) : (term604 x _94007 _94009 _94008) = (term605 x _94007 _94008 _94009).
Proof. exact (MK_COMB (@lem7044240) (@lem7044232 x _94007 _94008 _94009)). Qed.
Lemma lem7044249 (x : type999) (_94007 : nat -> nat) (_94008 : nat -> nat) (_94009 : nat -> Prop) : (term603 x _94007 _94008 _94009) = (term603 x _94007 _94008 _94009).
Proof. exact (eq_refl (term603 x _94007 _94008 _94009)). Qed.
Lemma lem7044250 (x : type999) (_94007 : nat -> nat) (_94008 : nat -> nat) (_94009 : nat -> Prop) : ((term544 x _94007 _94009 _94008) = (term603 x _94007 _94008 _94009)) = ((term603 x _94007 _94008 _94009) = (term603 x _94007 _94008 _94009)).
Proof. exact (MK_COMB (@lem7044241 x _94007 _94008 _94009) (@lem7044249 x _94007 _94008 _94009)). Qed.
Lemma lem7044252 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7044253 (x : Prop) : (x = x) = True.
Proof. exact (@lem7044252 Prop x). Qed.
Lemma lem7044254 (x : type999) (_94007 : nat -> nat) (_94008 : nat -> nat) (_94009 : nat -> Prop) : ((term603 x _94007 _94008 _94009) = (term603 x _94007 _94008 _94009)) = True.
Proof. exact (@lem7044253 (term603 x _94007 _94008 _94009)). Qed.
Lemma lem7044255 (x : type999) (_94007 : nat -> nat) (_94008 : nat -> nat) (_94009 : nat -> Prop) : ((term544 x _94007 _94009 _94008) = (term603 x _94007 _94008 _94009)) = True.
Proof. exact (TRANS (@lem7044250 x _94007 _94008 _94009) (@lem7044254 x _94007 _94008 _94009)). Qed.
Lemma lem7044256 (x : type999) (_94007 : nat -> nat) (_94008 : nat -> nat) (_94009 : nat -> Prop) : True = ((term544 x _94007 _94009 _94008) = (term603 x _94007 _94008 _94009)).
Proof. exact (SYM (@lem7044255 x _94007 _94008 _94009)). Qed.
Lemma lem7044257 (x : type999) (_94007 : nat -> nat) (_94008 : nat -> nat) (_94009 : nat -> Prop) : (term544 x _94007 _94009 _94008) = (term603 x _94007 _94008 _94009).
Proof. exact (EQ_MP (@lem7044256 x _94007 _94008 _94009) (@lem0)). Qed.
Lemma lem7044258 (_94007 : nat -> nat) (_94008 : nat -> nat) (_94009 : nat -> Prop) (x : type999) (h1 : term425 x) : term603 x _94007 _94008 _94009.
Proof. exact (EQ_MP (@lem7044257 x _94007 _94008 _94009) (@lem7043613 _94007 _94009 _94008 x h1)). Qed.
Lemma lem7044260 (b : Prop) (a : Prop) : (a \/ b) = (term548 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7044263 (x : type999) (_94007 : nat -> nat) (_94009 : nat -> Prop) (_94008 : nat -> nat) : (term603 x _94007 _94008 _94009) = (term606 x _94007 _94009 _94008).
Proof. exact (@lem7044260 (term485 x _94007 _94008 _94009) ((term463 _94009 _94007) = (term463 _94009 _94008))). Qed.
Lemma lem7044266 (_94007 : nat -> nat) (_94009 : nat -> Prop) (_94008 : nat -> nat) (x : type999) (h1 : term425 x) : term606 x _94007 _94009 _94008.
Proof. exact (EQ_MP (@lem7044263 x _94007 _94009 _94008) (@lem7044258 _94007 _94008 _94009 x h1)). Qed.
Lemma lem7044267 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (x : type999) (h1 : term425 x) : term607 x f m n g.
Proof. exact (@lem7044266 f (term433 m n) g x h1). Qed.
Lemma lem7044270 (x : type999) (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (h1 : term425 x) (h2 : term62) (h3 : term511 f m n g) (h4 : term88 f m n g) : (term508 m n f) = (term508 m n g).
Proof. exact (@lem7044267 f m n g x h1 (@lem7044225 x f m n g h1 h2 h3 h4)). Qed.
Lemma lem7044271 (x : type999) (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (h1 : term425 x) (h2 : term62) (h3 : term88 f m n g) : term608 f m n g.
Proof. exact (fun h0 : term511 f m n g => @lem7044270 x f m n g h1 h2 h0 h3). Qed.
Lemma lem7044273 (p : Prop) : (term554 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7044274 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) : (term608 f m n g) = ((term508 m n f) = (term508 m n g)).
Proof. exact (@lem7044273 ((term508 m n f) = (term508 m n g))). Qed.
Lemma lem7044275 (x : type999) (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (h1 : term425 x) (h2 : term62) (h3 : term88 f m n g) : (term508 m n f) = (term508 m n g).
Proof. exact (EQ_MP (@lem7044274 f m n g) (@lem7044271 x f m n g h1 h2 h3)). Qed.
Lemma lem7044278 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7044280 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) : (term511 f m n g) = (term609 f m n g).
Proof. exact (@lem7044278 ((term508 m n f) = (term508 m n g))). Qed.
Lemma lem7044283 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (h1 : term88 f m n g) : term609 f m n g.
Proof. exact (EQ_MP (@lem7044280 f m n g) (@lem7043573 f m n g h1)). Qed.
Lemma lem7044286 (x : type999) (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (h1 : term425 x) (h2 : term62) (h3 : term88 f m n g) : False.
Proof. exact (@lem7044283 f m n g h3 (@lem7044275 x f m n g h1 h2 h3)). Qed.
Lemma lem7044287 (x : type999) (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (h1 : term425 x) (h2 : term62) (h3 : term88 f m n g) : term610.
Proof. exact (fun h0 : ~ False => @lem7044286 x f m n g h1 h2 h3). Qed.
Lemma lem7044289 (p : Prop) : (term554 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7044290 : term610 = False.
Proof. exact (@lem7044289 False). Qed.
Lemma lem7044291 (x : type999) (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (h1 : term425 x) (h2 : term62) (h3 : term88 f m n g) : False.
Proof. exact (EQ_MP (@lem7044290) (@lem7044287 x f m n g h1 h2 h3)). Qed.
Lemma lem7044292 (x : type999) (f : nat -> nat) (m : nat) (g : nat -> nat) (h1 : term425 x) (h2 : term62) (h3 : term98 f m g) : False.
Proof. exact (ex_elim (@lem7042678 f m g h3) (fun n : nat => fun h0 : term97 f m g n => @lem7044291 x f m n g h1 h2 h0)). Qed.
Lemma lem7044293 (x : type999) (f : nat -> nat) (g : nat -> nat) (h1 : term425 x) (h2 : term62) (h3 : term105 f g) : False.
Proof. exact (ex_elim (@lem7042677 f g h3) (fun m : nat => fun h0 : term104 f g m => @lem7044292 x f m g h1 h2 h0)). Qed.
Lemma lem7044294 (x : type999) (f : nat -> nat) (h1 : term425 x) (h2 : term62) (h3 : term114 f) : False.
Proof. exact (ex_elim (@lem7042676 f h3) (fun g : nat -> nat => fun h0 : term113 f g => @lem7044293 x f g h1 h2 h0)). Qed.
Lemma lem7044295 (x : type999) (h1 : term425 x) (h2 : term62) (h3 : term10) : False.
Proof. exact (ex_elim (@lem7041674 h3) (fun f : nat -> nat => fun h0 : term119 f => @lem7044294 x f h1 h2 h0)). Qed.
Lemma lem7044296 {_127166 : Type'} (x : type999) (h1 : term49 _127166) (h2 : term425 x) (h3 : term62) (h4 : term10) : False.
Proof. exact (ex_elim (@lem7042407 _127166 h1) (fun x' : type695 _127166 => fun h0 : term316 _127166 x' => @lem7044295 x h2 h3 h4)). Qed.
Lemma lem7044297 {_127166 : Type'} (h1 : term49 _127166) (h2 : term11) (h3 : term62) (h4 : term10) : False.
Proof. exact (ex_elim (@lem7042673 h2) (fun x : type999 => fun h0 : term427 x => @lem7044296 _127166 x h1 h0 h3 h4)). Qed.
Lemma lem7044298 {_127166 : Type'} (h1 : term49 _127166) (h2 : term62) (h3 : term10) : term16.
Proof. exact (fun h0 : term11 => @lem7044297 _127166 h1 h0 h2 h3). Qed.
Lemma lem7044299 : term16 = term17.
Proof. exact (@lem69 term11). Qed.
Lemma lem7044300 {_127166 : Type'} (h1 : term49 _127166) (h2 : term62) (h3 : term10) : term17.
Proof. exact (EQ_MP (@lem7044299) (@lem7044298 _127166 h1 h2 h3)). Qed.
Lemma lem7044301 {_127166 : Type'} (h1 : term62) (h2 : term10) : term20 _127166.
Proof. exact (fun h0 : term49 _127166 => @lem7044300 _127166 h0 h1 h2). Qed.
Lemma lem7044302 {_127166 : Type'} (h1 : term62) (h2 : term10) : term23 _127166.
Proof. exact (fun h0 : term54 => @lem7044301 _127166 h1 h2). Qed.
Lemma lem7044303 {_127166 : Type'} (h1 : term10) : term26 _127166.
Proof. exact (fun h0 : term62 => @lem7044302 _127166 h0 h1). Qed.
Lemma lem7044304 {_127166 : Type'} : term28 _127166.
Proof. exact (fun h0 : term10 => @lem7044303 _127166 h0). Qed.
Lemma lem7044305 {_127166 : Type'} : term12 _127166.
Proof. exact (EQ_MP (@lem7041494 _127166) (@lem7044304 _127166)). Qed.
Lemma lem7044307 {_127166 : Type'} : term12 _127166.
Proof. exact (@lem7041128 _127166 (@lem7044305 _127166)). Qed.
Lemma lem7044308 {_127166 : Type'} (h1 : term10) : term25 _127166.
Proof. exact (@lem7044307 _127166 (@lem7041111 h1)). Qed.
Lemma lem7044309 {_127166 : Type'} (h1 : term10) : term22 _127166.
Proof. exact (@lem7044308 _127166 h1 (@lem5371273)). Qed.
Lemma lem7044310 {_127166 : Type'} (h1 : term10) : term19 _127166.
Proof. exact (@lem7044309 _127166 h1 (@lem5329299)). Qed.
Lemma lem7044311 (h1 : term10) : term16.
Proof. exact (@lem7044310 Prop h1 (@lem6938831 Prop)). Qed.
Lemma lem7044312 (h1 : term10) : False.
Proof. exact (@lem7044311 h1 (@lem7041112)). Qed.
Lemma lem7044313 (h1 : term10) : term10 = False.
Proof. exact (prop_ext (fun h2 : term10 => @lem7044312 h1) (fun h2 : False => @lem7041111 h1)). Qed.
Lemma lem7044314 (h1 : term10) : False.
Proof. exact (EQ_MP (@lem7044313 h1) (@lem7041111 h1)). Qed.
Lemma lem7044315 : term9.
Proof. exact (fun h0 : term10 => @lem7044314 h0). Qed.
Lemma lem7044316 : term8.
Proof. exact (EQ_MP (@lem7041110) (@lem7044315)). Qed.
