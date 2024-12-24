Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUP_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import MEMBER_NOT_EMPTY_spec.
Require Import REAL_COMPLETE_spec.
Require Import sup_spec.
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
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Require Import thm9425_spec.
Lemma lem5135119 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem5135120 (P : real -> Prop) (h1 : term0) : term1 P.
Proof. exact (@lem5135119 h1 P). Qed.
Lemma lem5135121 (P : real -> Prop) : (term1 P) = (term2 P).
Proof. exact (eq_refl (term1 P)). Qed.
Lemma lem5135122 (P : real -> Prop) (h1 : term0) : term2 P.
Proof. exact (EQ_MP (@lem5135121 P) (@lem5135120 P h1)). Qed.
Lemma lem5135123 (P : real -> Prop) (h1 : term3 P) : term3 P.
Proof. exact (h1). Qed.
Lemma lem5135124 (P : real -> Prop) (h1 : term0) (h2 : term3 P) : term4 P.
Proof. exact (@lem5135122 P h1 (@lem5135123 P h2)). Qed.
Lemma lem5135125 (P : real -> Prop) (h1 : term3 P) : term5 P.
Proof. exact (fun h0 : term0 => @lem5135124 P h0 h1). Qed.
Lemma lem5135126 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem5135127 (P : real -> Prop) (h1 : term0) (h2 : term3 P) : term4 P.
Proof. exact (@lem5135125 P h2 (@lem5135126 h1)). Qed.
Lemma lem5135128 (P : real -> Prop) (h1 : term0) : term2 P.
Proof. exact (fun h0 : term3 P => @lem5135127 P h1 h0). Qed.
Lemma lem5135129 (h1 : term0) : term0.
Proof. exact (fun P : real -> Prop => @lem5135128 P h1). Qed.
Lemma lem5135130 : term6.
Proof. exact (fun h0 : term0 => @lem5135129 h0). Qed.
Lemma lem5135131 : term0.
Proof. exact (@lem5135130 (@lem1351370)). Qed.
Lemma lem5135132 (P : real -> Prop) : term1 P.
Proof. exact (@lem5135131 P). Qed.
Lemma lem5135133 (P : real -> Prop) : (term1 P) = (term2 P).
Proof. exact (eq_refl (term1 P)). Qed.
Lemma lem5135135 (s : real -> Prop) : term7 s.
Proof. exact (@lem5133933 s). Qed.
Lemma lem5135136 (s : real -> Prop) : (term7 s) = ((sup s) = (term8 s)).
Proof. exact (eq_refl (term7 s)). Qed.
Lemma lem5135167 (s : real -> Prop) : (sup s) = (term8 s).
Proof. exact (EQ_MP (@lem5135136 s) (@lem5135135 s)). Qed.
Lemma lem5135188 (x : real) : (real_le x) = (real_le x).
Proof. exact (eq_refl (real_le x)). Qed.
Lemma lem5135189 (x : real) (s : real -> Prop) : (term9 x s) = (term10 x s).
Proof. exact (MK_COMB (@lem5135188 x) (@lem5135167 s)). Qed.
Lemma lem5135190 (x : real) (s : real -> Prop) : (term11 x s) = (term11 x s).
Proof. exact (eq_refl (term11 x s)). Qed.
Lemma lem5135191 (x : real) (s : real -> Prop) : (term12 x s) = (term13 x s).
Proof. exact (MK_COMB (@lem5135190 x s) (@lem5135189 x s)). Qed.
Lemma lem5135194 (s : real -> Prop) : (term14 s) = (term15 s).
Proof. exact (fun_ext (fun x : real => @lem5135191 x s)). Qed.
Lemma lem5135195 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5135196 (s : real -> Prop) : (term16 s) = (term17 s).
Proof. exact (MK_COMB (@lem5135195) (@lem5135194 s)). Qed.
Lemma lem5135201 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5135202 (s : real -> Prop) : (term18 s) = (term19 s).
Proof. exact (MK_COMB (@lem5135201) (@lem5135196 s)). Qed.
Lemma lem5135216 (s : real -> Prop) : (sup s) = (term8 s).
Proof. exact (EQ_MP (@lem5135136 s) (@lem5135135 s)). Qed.
Lemma lem5135237 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5135238 (s : real -> Prop) : (term20 s) = (term21 s).
Proof. exact (MK_COMB (@lem5135237) (@lem5135216 s)). Qed.
Lemma lem5135239 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem5135240 (s : real -> Prop) (b : real) : (term22 s b) = (term23 s b).
Proof. exact (MK_COMB (@lem5135238 s) (@lem5135239 b)). Qed.
Lemma lem5135241 (s : real -> Prop) (b : real) : (term24 s b) = (term24 s b).
Proof. exact (eq_refl (term24 s b)). Qed.
Lemma lem5135242 (s : real -> Prop) (b : real) : (term25 s b) = (term26 s b).
Proof. exact (MK_COMB (@lem5135241 s b) (@lem5135240 s b)). Qed.
Lemma lem5135245 (s : real -> Prop) : (term27 s) = (term28 s).
Proof. exact (fun_ext (fun b : real => @lem5135242 s b)). Qed.
Lemma lem5135246 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5135247 (s : real -> Prop) : (term29 s) = (term30 s).
Proof. exact (MK_COMB (@lem5135246) (@lem5135245 s)). Qed.
Lemma lem5135252 (s : real -> Prop) : (term31 s) = (term32 s).
Proof. exact (MK_COMB (@lem5135202 s) (@lem5135247 s)). Qed.
Lemma lem5135255 (s : real -> Prop) : (term33 s) = (term33 s).
Proof. exact (eq_refl (term33 s)). Qed.
Lemma lem5135256 (s : real -> Prop) : (term34 s) = (term35 s).
Proof. exact (MK_COMB (@lem5135255 s) (@lem5135252 s)). Qed.
Lemma lem5135259 : term36 = term37.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5135256 s)). Qed.
Lemma lem5135260 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5135261 : term38 = term39.
Proof. exact (MK_COMB (@lem5135260) (@lem5135259)). Qed.
Lemma lem5135266 : term39 = term38.
Proof. exact (SYM (@lem5135261)). Qed.
Lemma lem5135267 (P : real -> Prop) : (term40 P) = (ex P).
Proof. exact (@lem9425 real P). Qed.
Lemma lem5135268 (s : real -> Prop) : (term41 s) = (term42 s).
Proof. exact (@lem5135267 (term43 s)). Qed.
Lemma lem5135269 (s : real -> Prop) : (term41 s) = (term32 s).
Proof. exact (eq_refl (term41 s)). Qed.
Lemma lem5135270 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5135271 (s : real -> Prop) : (term44 s) = (term45 s).
Proof. exact (MK_COMB (@lem5135270) (@lem5135269 s)). Qed.
Lemma lem5135272 (s : real -> Prop) : (term42 s) = (term42 s).
Proof. exact (eq_refl (term42 s)). Qed.
Lemma lem5135273 (s : real -> Prop) : ((term41 s) = (term42 s)) = ((term32 s) = (term42 s)).
Proof. exact (MK_COMB (@lem5135271 s) (@lem5135272 s)). Qed.
Lemma lem5135274 (s : real -> Prop) : (term32 s) = (term42 s).
Proof. exact (EQ_MP (@lem5135273 s) (@lem5135268 s)). Qed.
Lemma lem5135275 (s : real -> Prop) : (term33 s) = (term33 s).
Proof. exact (eq_refl (term33 s)). Qed.
Lemma lem5135276 (s : real -> Prop) : (term35 s) = (term46 s).
Proof. exact (MK_COMB (@lem5135275 s) (@lem5135274 s)). Qed.
Lemma lem5135277 : term37 = term47.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5135276 s)). Qed.
Lemma lem5135278 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5135279 : term39 = term48.
Proof. exact (MK_COMB (@lem5135278) (@lem5135277)). Qed.
Lemma lem5135280 : term48 = term39.
Proof. exact (SYM (@lem5135279)). Qed.
Lemma lem5135281 (s : real -> Prop) (h1 : term49 s) : term49 s.
Proof. exact (h1). Qed.
Lemma lem5135282 (s : real -> Prop) (h1 : term50 s) : term50 s.
Proof. exact (h1). Qed.
Lemma lem5135283 (s : real -> Prop) (h1 : term51 s) : term51 s.
Proof. exact (h1). Qed.
Lemma lem5135284 (s : real -> Prop) (b : real) (h1 : term52 s b) : term52 s b.
Proof. exact (h1). Qed.
Lemma lem5135286 (P : real -> Prop) : term2 P.
Proof. exact (EQ_MP (@lem5135133 P) (@lem5135132 P)). Qed.
Lemma lem5135287 (s : real -> Prop) : term53 s.
Proof. exact (@lem5135286 (term54 s)). Qed.
Lemma lem5135288 (x : real) (s : real -> Prop) : (term55 s x) = (@IN real x s).
Proof. exact (eq_refl (term55 s x)). Qed.
Lemma lem5135289 (s : real -> Prop) : (term56 s) = (term54 s).
Proof. exact (fun_ext (fun x : real => @lem5135288 x s)). Qed.
Lemma lem5135290 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5135291 (s : real -> Prop) : (term57 s) = (term58 s).
Proof. exact (MK_COMB (@lem5135290) (@lem5135289 s)). Qed.
Lemma lem5135292 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5135293 (s : real -> Prop) : (term59 s) = (term60 s).
Proof. exact (MK_COMB (@lem5135292) (@lem5135291 s)). Qed.
Lemma lem5135294 (x : real) (s : real -> Prop) : (term55 s x) = (@IN real x s).
Proof. exact (eq_refl (term55 s x)). Qed.
Lemma lem5135295 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5135296 (x : real) (s : real -> Prop) : (term61 s x) = (term11 x s).
Proof. exact (MK_COMB (@lem5135295) (@lem5135294 x s)). Qed.
Lemma lem5135297 (x : real) (a : real) : (real_le x a) = (real_le x a).
Proof. exact (eq_refl (real_le x a)). Qed.
Lemma lem5135298 (s : real -> Prop) (x : real) (a : real) : (term62 s x a) = (term63 s x a).
Proof. exact (MK_COMB (@lem5135296 x s) (@lem5135297 x a)). Qed.
Lemma lem5135299 (s : real -> Prop) (a : real) : (term64 s a) = (term65 s a).
Proof. exact (fun_ext (fun x : real => @lem5135298 s x a)). Qed.
Lemma lem5135300 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5135301 (s : real -> Prop) (a : real) : (term66 s a) = (term52 s a).
Proof. exact (MK_COMB (@lem5135300) (@lem5135299 s a)). Qed.
Lemma lem5135302 (s : real -> Prop) : (term67 s) = (term68 s).
Proof. exact (fun_ext (fun a : real => @lem5135301 s a)). Qed.
Lemma lem5135303 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5135304 (s : real -> Prop) : (term69 s) = (term50 s).
Proof. exact (MK_COMB (@lem5135303) (@lem5135302 s)). Qed.
Lemma lem5135305 (s : real -> Prop) : (term70 s) = (term71 s).
Proof. exact (MK_COMB (@lem5135293 s) (@lem5135304 s)). Qed.
Lemma lem5135306 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5135307 (s : real -> Prop) : (term72 s) = (term73 s).
Proof. exact (MK_COMB (@lem5135306) (@lem5135305 s)). Qed.
Lemma lem5135308 (x : real) (s : real -> Prop) : (term55 s x) = (@IN real x s).
Proof. exact (eq_refl (term55 s x)). Qed.
Lemma lem5135309 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5135310 (x : real) (s : real -> Prop) : (term61 s x) = (term11 x s).
Proof. exact (MK_COMB (@lem5135309) (@lem5135308 x s)). Qed.
Lemma lem5135311 (x : real) (a : real) : (real_le x a) = (real_le x a).
Proof. exact (eq_refl (real_le x a)). Qed.
Lemma lem5135312 (s : real -> Prop) (x : real) (a : real) : (term62 s x a) = (term63 s x a).
Proof. exact (MK_COMB (@lem5135310 x s) (@lem5135311 x a)). Qed.
Lemma lem5135313 (s : real -> Prop) (a : real) : (term64 s a) = (term65 s a).
Proof. exact (fun_ext (fun x : real => @lem5135312 s x a)). Qed.
Lemma lem5135314 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5135315 (s : real -> Prop) (a : real) : (term66 s a) = (term52 s a).
Proof. exact (MK_COMB (@lem5135314) (@lem5135313 s a)). Qed.
Lemma lem5135316 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5135317 (s : real -> Prop) (a : real) : (term74 s a) = (term75 s a).
Proof. exact (MK_COMB (@lem5135316) (@lem5135315 s a)). Qed.
Lemma lem5135318 (x : real) (s : real -> Prop) : (term55 s x) = (@IN real x s).
Proof. exact (eq_refl (term55 s x)). Qed.
Lemma lem5135319 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5135320 (x : real) (s : real -> Prop) : (term61 s x) = (term11 x s).
Proof. exact (MK_COMB (@lem5135319) (@lem5135318 x s)). Qed.
Lemma lem5135321 (x : real) (b : real) : (real_le x b) = (real_le x b).
Proof. exact (eq_refl (real_le x b)). Qed.
Lemma lem5135322 (s : real -> Prop) (x : real) (b : real) : (term62 s x b) = (term63 s x b).
Proof. exact (MK_COMB (@lem5135320 x s) (@lem5135321 x b)). Qed.
Lemma lem5135323 (s : real -> Prop) (b : real) : (term64 s b) = (term65 s b).
Proof. exact (fun_ext (fun x : real => @lem5135322 s x b)). Qed.
Lemma lem5135324 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5135325 (s : real -> Prop) (b : real) : (term66 s b) = (term52 s b).
Proof. exact (MK_COMB (@lem5135324) (@lem5135323 s b)). Qed.
Lemma lem5135326 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5135327 (s : real -> Prop) (b : real) : (term76 s b) = (term24 s b).
Proof. exact (MK_COMB (@lem5135326) (@lem5135325 s b)). Qed.
Lemma lem5135328 (a : real) (b : real) : (real_le a b) = (real_le a b).
Proof. exact (eq_refl (real_le a b)). Qed.
Lemma lem5135329 (s : real -> Prop) (a : real) (b : real) : (term77 s a b) = (term78 s a b).
Proof. exact (MK_COMB (@lem5135327 s b) (@lem5135328 a b)). Qed.
Lemma lem5135330 (s : real -> Prop) (a : real) : (term79 s a) = (term80 s a).
Proof. exact (fun_ext (fun b : real => @lem5135329 s a b)). Qed.
Lemma lem5135331 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5135332 (s : real -> Prop) (a : real) : (term81 s a) = (term82 s a).
Proof. exact (MK_COMB (@lem5135331) (@lem5135330 s a)). Qed.
Lemma lem5135333 (s : real -> Prop) (a : real) : (term83 s a) = (term84 s a).
Proof. exact (MK_COMB (@lem5135317 s a) (@lem5135332 s a)). Qed.
Lemma lem5135334 (s : real -> Prop) : (term85 s) = (term43 s).
Proof. exact (fun_ext (fun a : real => @lem5135333 s a)). Qed.
Lemma lem5135335 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5135336 (s : real -> Prop) : (term86 s) = (term42 s).
Proof. exact (MK_COMB (@lem5135335) (@lem5135334 s)). Qed.
Lemma lem5135337 (s : real -> Prop) : (term53 s) = (term87 s).
Proof. exact (MK_COMB (@lem5135307 s) (@lem5135336 s)). Qed.
Lemma lem5135338 (s : real -> Prop) : term87 s.
Proof. exact (EQ_MP (@lem5135337 s) (@lem5135287 s)). Qed.
Lemma lem5135340 (p : Prop) : p = (term88 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5135341 (s : real -> Prop) : (term71 s) = (term89 s).
Proof. exact (@lem5135340 (term71 s)). Qed.
Lemma lem5135342 (s : real -> Prop) : (term89 s) = (term71 s).
Proof. exact (SYM (@lem5135341 s)). Qed.
Lemma lem5135343 (s : real -> Prop) (h1 : term90 s) : term90 s.
Proof. exact (h1). Qed.
Lemma lem5135344 : term91.
Proof. exact (@lem3216368 real). Qed.
Lemma lem5135349 (b : real) (s : real -> Prop) (h1 : term92 b s) : term92 b s.
Proof. exact (h1). Qed.
Lemma lem5135350 (b : real) (s : real -> Prop) : term93 b s.
Proof. exact (fun h0 : term92 b s => @lem5135349 b s h0). Qed.
Lemma lem5135351 (b : real) (s : real -> Prop) (h1 : term93 b s) : term93 b s.
Proof. exact (h1). Qed.
Lemma lem5135352 (b : real) (s : real -> Prop) (h1 : term92 b s) : term92 b s.
Proof. exact (h1). Qed.
Lemma lem5135353 (b : real) (s : real -> Prop) (h1 : term92 b s) (h2 : term93 b s) : term92 b s.
Proof. exact (@lem5135351 b s h2 (@lem5135352 b s h1)). Qed.
Lemma lem5135354 (b : real) (s : real -> Prop) (h1 : term92 b s) : term94 b s.
Proof. exact (fun h0 : term93 b s => @lem5135353 b s h1 h0). Qed.
Lemma lem5135355 (b : real) (s : real -> Prop) (h1 : term93 b s) : term93 b s.
Proof. exact (h1). Qed.
Lemma lem5135356 (b : real) (s : real -> Prop) (h1 : term92 b s) (h2 : term93 b s) : term92 b s.
Proof. exact (@lem5135354 b s h1 (@lem5135355 b s h2)). Qed.
Lemma lem5135357 (b : real) (s : real -> Prop) (h1 : term93 b s) : term93 b s.
Proof. exact (fun h0 : term92 b s => @lem5135356 b s h0 h1). Qed.
Lemma lem5135358 (b : real) (s : real -> Prop) : term95 b s.
Proof. exact (fun h0 : term93 b s => @lem5135357 b s h0). Qed.
Lemma lem5135361 (b : real) (s : real -> Prop) : term93 b s.
Proof. exact (@lem5135358 b s (@lem5135350 b s)). Qed.
Lemma lem5135399 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5135400 : term96 = term97.
Proof. exact (@lem5135399 term91). Qed.
Lemma lem5135409 (s : real -> Prop) : (term98 s) = (term98 s).
Proof. exact (eq_refl (term98 s)). Qed.
Lemma lem5135410 (s : real -> Prop) : (term99 s) = (term100 s).
Proof. exact (MK_COMB (@lem5135409 s) (@lem5135400)). Qed.
Lemma lem5135413 (s : real -> Prop) (b : real) : (term24 s b) = (term24 s b).
Proof. exact (eq_refl (term24 s b)). Qed.
Lemma lem5135414 (b : real) (s : real -> Prop) : (term101 b s) = (term102 b s).
Proof. exact (MK_COMB (@lem5135413 s b) (@lem5135410 s)). Qed.
Lemma lem5135417 (s : real -> Prop) : (term103 s) = (term103 s).
Proof. exact (eq_refl (term103 s)). Qed.
Lemma lem5135418 (b : real) (s : real -> Prop) : (term92 b s) = (term104 b s).
Proof. exact (MK_COMB (@lem5135417 s) (@lem5135414 b s)). Qed.
Lemma lem5135421 (s : real -> Prop) : (term105 s) = (term106 s).
Proof. exact (fun_ext (fun b : real => @lem5135418 b s)). Qed.
Lemma lem5135422 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5135423 (s : real -> Prop) : (term107 s) = (term108 s).
Proof. exact (MK_COMB (@lem5135422) (@lem5135421 s)). Qed.
Lemma lem5135428 : term109 = term110.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5135423 s)). Qed.
Lemma lem5135429 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5135438 : term111 = term112.
Proof. exact (MK_COMB (@lem5135429) (@lem5135428)). Qed.
Lemma lem5135441 (s : real -> Prop) : (term51 s) = (term51 s).
Proof. exact (eq_refl (term51 s)). Qed.
Lemma lem5135442 (x : real) (s : real -> Prop) : (@IN real x s) = (@IN real x s).
Proof. exact (eq_refl (@IN real x s)). Qed.
Lemma lem5135443 (s : real -> Prop) : (term54 s) = (term54 s).
Proof. exact (fun_ext (fun x : real => @lem5135442 x s)). Qed.
Lemma lem5135444 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5135445 (s : real -> Prop) : (term58 s) = (term58 s).
Proof. exact (MK_COMB (@lem5135444) (@lem5135443 s)). Qed.
Lemma lem5135446 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5135447 (s : real -> Prop) : (term113 s) = (term113 s).
Proof. exact (MK_COMB (@lem5135446) (@lem5135445 s)). Qed.
Lemma lem5135448 (s : real -> Prop) : ((term58 s) = (term51 s)) = ((term58 s) = (term51 s)).
Proof. exact (MK_COMB (@lem5135447 s) (@lem5135441 s)). Qed.
Lemma lem5135449 : term114 = term114.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5135448 s)). Qed.
Lemma lem5135450 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5135451 : term91 = term91.
Proof. exact (MK_COMB (@lem5135450) (@lem5135449)). Qed.
Lemma lem5135452 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5135453 : term97 = term97.
Proof. exact (MK_COMB (@lem5135452) (@lem5135451)). Qed.
Lemma lem5135458 (s : real -> Prop) (x : real) (a : real) : (term63 s x a) = (term63 s x a).
Proof. exact (eq_refl (term63 s x a)). Qed.
Lemma lem5135459 (s : real -> Prop) (a : real) : (term65 s a) = (term65 s a).
Proof. exact (fun_ext (fun x : real => @lem5135458 s x a)). Qed.
Lemma lem5135460 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5135461 (s : real -> Prop) (a : real) : (term52 s a) = (term52 s a).
Proof. exact (MK_COMB (@lem5135460) (@lem5135459 s a)). Qed.
Lemma lem5135462 (s : real -> Prop) : (term68 s) = (term68 s).
Proof. exact (fun_ext (fun a : real => @lem5135461 s a)). Qed.
Lemma lem5135463 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5135464 (s : real -> Prop) : (term50 s) = (term50 s).
Proof. exact (MK_COMB (@lem5135463) (@lem5135462 s)). Qed.
Lemma lem5135465 (x : real) (s : real -> Prop) : (@IN real x s) = (@IN real x s).
Proof. exact (eq_refl (@IN real x s)). Qed.
Lemma lem5135466 (s : real -> Prop) : (term54 s) = (term54 s).
Proof. exact (fun_ext (fun x : real => @lem5135465 x s)). Qed.
Lemma lem5135467 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5135468 (s : real -> Prop) : (term58 s) = (term58 s).
Proof. exact (MK_COMB (@lem5135467) (@lem5135466 s)). Qed.
Lemma lem5135469 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5135470 (s : real -> Prop) : (term60 s) = (term60 s).
Proof. exact (MK_COMB (@lem5135469) (@lem5135468 s)). Qed.
Lemma lem5135471 (s : real -> Prop) : (term71 s) = (term71 s).
Proof. exact (MK_COMB (@lem5135470 s) (@lem5135464 s)). Qed.
Lemma lem5135472 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5135473 (s : real -> Prop) : (term90 s) = (term90 s).
Proof. exact (MK_COMB (@lem5135472) (@lem5135471 s)). Qed.
Lemma lem5135474 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5135475 (s : real -> Prop) : (term98 s) = (term98 s).
Proof. exact (MK_COMB (@lem5135474) (@lem5135473 s)). Qed.
Lemma lem5135476 (s : real -> Prop) : (term100 s) = (term100 s).
Proof. exact (MK_COMB (@lem5135475 s) (@lem5135453)). Qed.
Lemma lem5135481 (s : real -> Prop) (x : real) (b : real) : (term63 s x b) = (term63 s x b).
Proof. exact (eq_refl (term63 s x b)). Qed.
Lemma lem5135482 (s : real -> Prop) (b : real) : (term65 s b) = (term65 s b).
Proof. exact (fun_ext (fun x : real => @lem5135481 s x b)). Qed.
Lemma lem5135483 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5135484 (s : real -> Prop) (b : real) : (term52 s b) = (term52 s b).
Proof. exact (MK_COMB (@lem5135483) (@lem5135482 s b)). Qed.
Lemma lem5135485 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5135486 (s : real -> Prop) (b : real) : (term24 s b) = (term24 s b).
Proof. exact (MK_COMB (@lem5135485) (@lem5135484 s b)). Qed.
Lemma lem5135487 (b : real) (s : real -> Prop) : (term102 b s) = (term102 b s).
Proof. exact (MK_COMB (@lem5135486 s b) (@lem5135476 s)). Qed.
Lemma lem5135492 (s : real -> Prop) : (term103 s) = (term103 s).
Proof. exact (eq_refl (term103 s)). Qed.
Lemma lem5135493 (b : real) (s : real -> Prop) : (term104 b s) = (term104 b s).
Proof. exact (MK_COMB (@lem5135492 s) (@lem5135487 b s)). Qed.
Lemma lem5135494 (s : real -> Prop) : (term106 s) = (term106 s).
Proof. exact (fun_ext (fun b : real => @lem5135493 b s)). Qed.
Lemma lem5135495 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5135496 (s : real -> Prop) : (term108 s) = (term108 s).
Proof. exact (MK_COMB (@lem5135495) (@lem5135494 s)). Qed.
Lemma lem5135497 : term110 = term110.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5135496 s)). Qed.
Lemma lem5135498 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5135499 : term112 = term112.
Proof. exact (MK_COMB (@lem5135498) (@lem5135497)). Qed.
Lemma lem5135562 : term111 = term112.
Proof. exact (TRANS (@lem5135438) (@lem5135499)). Qed.
Lemma lem5135563 : term112 = term111.
Proof. exact (SYM (@lem5135562)). Qed.
Lemma lem5135565 (s : real -> Prop) (b : real) (h1 : term52 s b) : term52 s b.
Proof. exact (h1). Qed.
Lemma lem5135566 (s : real -> Prop) (h1 : term90 s) : term90 s.
Proof. exact (h1). Qed.
Lemma lem5135567 (h1 : term91) : term91.
Proof. exact (h1). Qed.
Lemma lem5135573 (s : real -> Prop) (h1 : term51 s) : term51 s.
Proof. exact (h1). Qed.
Lemma lem5135580 (s : real -> Prop) (x : real) (b : real) : (term63 s x b) = (term115 s x b).
Proof. exact (@lem17265 (@IN real x s) (real_le x b)). Qed.
Lemma lem5135581 (s : real -> Prop) (b : real) : (term65 s b) = (term116 s b).
Proof. exact (fun_ext (fun x : real => @lem5135580 s x b)). Qed.
Lemma lem5135582 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5135635 (s : real -> Prop) (b : real) : (term52 s b) = (term117 s b).
Proof. exact (MK_COMB (@lem5135582) (@lem5135581 s b)). Qed.
Lemma lem5135636 (s : real -> Prop) (b : real) (h1 : term52 s b) : term117 s b.
Proof. exact (EQ_MP (@lem5135635 s b) (@lem5135565 s b h1)). Qed.
Lemma lem5135638 (P : real -> Prop) : (term118 P) = (term119 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5135639 (s : real -> Prop) : (term120 s) = (term121 s).
Proof. exact (@lem5135638 (term54 s)). Qed.
Lemma lem5135640 (x : real) (s : real -> Prop) : (term55 s x) = (@IN real x s).
Proof. exact (eq_refl (term55 s x)). Qed.
Lemma lem5135641 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5135643 (x : real) (s : real -> Prop) : (term122 s x) = (term123 x s).
Proof. exact (MK_COMB (@lem5135641) (@lem5135640 x s)). Qed.
Lemma lem5135644 (s : real -> Prop) : (term124 s) = (term125 s).
Proof. exact (fun_ext (fun x : real => @lem5135643 x s)). Qed.
Lemma lem5135645 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5135646 (s : real -> Prop) : (term121 s) = (term126 s).
Proof. exact (MK_COMB (@lem5135645) (@lem5135644 s)). Qed.
Lemma lem5135647 (s : real -> Prop) : (term120 s) = (term126 s).
Proof. exact (TRANS (@lem5135639 s) (@lem5135646 s)). Qed.
Lemma lem5135654 (s : real -> Prop) (x : real) (a : real) : (term127 s x a) = (term128 s x a).
Proof. exact (@lem17362 (@IN real x s) (real_le x a)). Qed.
Lemma lem5135655 (P : real -> Prop) : (term129 P) = (term130 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5135656 (s : real -> Prop) (a : real) : (term131 s a) = (term132 s a).
Proof. exact (@lem5135655 (term65 s a)). Qed.
Lemma lem5135657 (s : real -> Prop) (x : real) (a : real) : (term133 s a x) = (term63 s x a).
Proof. exact (eq_refl (term133 s a x)). Qed.
Lemma lem5135658 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5135659 (s : real -> Prop) (x : real) (a : real) : (term134 s a x) = (term127 s x a).
Proof. exact (MK_COMB (@lem5135658) (@lem5135657 s x a)). Qed.
Lemma lem5135660 (s : real -> Prop) (x : real) (a : real) : (term134 s a x) = (term128 s x a).
Proof. exact (TRANS (@lem5135659 s x a) (@lem5135654 s x a)). Qed.
Lemma lem5135661 (s : real -> Prop) (a : real) : (term135 s a) = (term136 s a).
Proof. exact (fun_ext (fun x : real => @lem5135660 s x a)). Qed.
Lemma lem5135662 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5135663 (s : real -> Prop) (a : real) : (term132 s a) = (term137 s a).
Proof. exact (MK_COMB (@lem5135662) (@lem5135661 s a)). Qed.
Lemma lem5135664 (s : real -> Prop) (a : real) : (term131 s a) = (term137 s a).
Proof. exact (TRANS (@lem5135656 s a) (@lem5135663 s a)). Qed.
Lemma lem5135665 (P : real -> Prop) : (term118 P) = (term119 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5135666 (s : real -> Prop) : (term138 s) = (term139 s).
Proof. exact (@lem5135665 (term68 s)). Qed.
Lemma lem5135667 (s : real -> Prop) (a : real) : (term140 s a) = (term52 s a).
Proof. exact (eq_refl (term140 s a)). Qed.
Lemma lem5135668 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5135669 (s : real -> Prop) (a : real) : (term141 s a) = (term131 s a).
Proof. exact (MK_COMB (@lem5135668) (@lem5135667 s a)). Qed.
Lemma lem5135670 (s : real -> Prop) (a : real) : (term141 s a) = (term137 s a).
Proof. exact (TRANS (@lem5135669 s a) (@lem5135664 s a)). Qed.
Lemma lem5135671 (s : real -> Prop) : (term142 s) = (term143 s).
Proof. exact (fun_ext (fun a : real => @lem5135670 s a)). Qed.
Lemma lem5135672 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5135673 (s : real -> Prop) : (term139 s) = (term144 s).
Proof. exact (MK_COMB (@lem5135672) (@lem5135671 s)). Qed.
Lemma lem5135674 (s : real -> Prop) : (term138 s) = (term144 s).
Proof. exact (TRANS (@lem5135666 s) (@lem5135673 s)). Qed.
Lemma lem5135675 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5135676 (s : real -> Prop) : (term145 s) = (term146 s).
Proof. exact (MK_COMB (@lem5135675) (@lem5135647 s)). Qed.
Lemma lem5135677 (s : real -> Prop) : (term147 s) = (term148 s).
Proof. exact (MK_COMB (@lem5135676 s) (@lem5135674 s)). Qed.
Lemma lem5135678 (s : real -> Prop) : (term90 s) = (term147 s).
Proof. exact (@lem17045 (term58 s) (term50 s)). Qed.
Lemma lem5135679 (s : real -> Prop) : (term90 s) = (term148 s).
Proof. exact (TRANS (@lem5135678 s) (@lem5135677 s)). Qed.
Lemma lem5135738 {A B : Type'} (P : type1413 A B) : (term149 A B P) = (term150 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5135739 (P : type1626) : (term151 P) = (term152 P).
Proof. exact (@lem5135738 real real P). Qed.
Lemma lem5135740 (s : real -> Prop) : (term153 s) = (term154 s).
Proof. exact (@lem5135739 (term155 s)). Qed.
Lemma lem5135741 (s : real -> Prop) (a : real) : (term156 s a) = (term136 s a).
Proof. exact (eq_refl (term156 s a)). Qed.
Lemma lem5135742 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5135743 (s : real -> Prop) (a : real) (x : real) : (term157 s a x) = (term158 s a x).
Proof. exact (MK_COMB (@lem5135741 s a) (@lem5135742 x)). Qed.
Lemma lem5135744 (s : real -> Prop) (x : real) (a : real) : (term158 s a x) = (term128 s x a).
Proof. exact (eq_refl (term158 s a x)). Qed.
Lemma lem5135745 (s : real -> Prop) (x : real) (a : real) : (term157 s a x) = (term128 s x a).
Proof. exact (TRANS (@lem5135743 s a x) (@lem5135744 s x a)). Qed.
Lemma lem5135746 (s : real -> Prop) (a : real) : (term159 s a) = (term136 s a).
Proof. exact (fun_ext (fun x : real => @lem5135745 s x a)). Qed.
Lemma lem5135747 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5135748 (s : real -> Prop) (a : real) : (term160 s a) = (term137 s a).
Proof. exact (MK_COMB (@lem5135747) (@lem5135746 s a)). Qed.
Lemma lem5135749 (s : real -> Prop) : (term161 s) = (term143 s).
Proof. exact (fun_ext (fun a : real => @lem5135748 s a)). Qed.
Lemma lem5135750 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5135751 (s : real -> Prop) : (term153 s) = (term144 s).
Proof. exact (MK_COMB (@lem5135750) (@lem5135749 s)). Qed.
Lemma lem5135752 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5135753 (s : real -> Prop) : (term162 s) = (term163 s).
Proof. exact (MK_COMB (@lem5135752) (@lem5135751 s)). Qed.
Lemma lem5135754 (s : real -> Prop) (a : real) : (term156 s a) = (term136 s a).
Proof. exact (eq_refl (term156 s a)). Qed.
Lemma lem5135755 (x : real -> real) (a : real) : (x a) = (x a).
Proof. exact (eq_refl (x a)). Qed.
Lemma lem5135756 (s : real -> Prop) (x : real -> real) (a : real) : (term164 s x a) = (term165 s x a).
Proof. exact (MK_COMB (@lem5135754 s a) (@lem5135755 x a)). Qed.
Lemma lem5135757 (s : real -> Prop) (x : real -> real) (a : real) : (term165 s x a) = (term166 s x a).
Proof. exact (eq_refl (term165 s x a)). Qed.
Lemma lem5135758 (s : real -> Prop) (x : real -> real) (a : real) : (term164 s x a) = (term166 s x a).
Proof. exact (TRANS (@lem5135756 s x a) (@lem5135757 s x a)). Qed.
Lemma lem5135759 (s : real -> Prop) (x : real -> real) : (term167 s x) = (term168 s x).
Proof. exact (fun_ext (fun a : real => @lem5135758 s x a)). Qed.
Lemma lem5135760 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5135761 (s : real -> Prop) (x : real -> real) : (term169 s x) = (term170 s x).
Proof. exact (MK_COMB (@lem5135760) (@lem5135759 s x)). Qed.
Lemma lem5135762 (s : real -> Prop) : (term171 s) = (term172 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5135761 s x)). Qed.
Lemma lem5135763 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5135764 (s : real -> Prop) : (term154 s) = (term173 s).
Proof. exact (MK_COMB (@lem5135763) (@lem5135762 s)). Qed.
Lemma lem5135765 (s : real -> Prop) : ((term153 s) = (term154 s)) = ((term144 s) = (term173 s)).
Proof. exact (MK_COMB (@lem5135753 s) (@lem5135764 s)). Qed.
Lemma lem5135766 (s : real -> Prop) : (term144 s) = (term173 s).
Proof. exact (EQ_MP (@lem5135765 s) (@lem5135740 s)). Qed.
Lemma lem5135767 (s : real -> Prop) : (term146 s) = (term146 s).
Proof. exact (eq_refl (term146 s)). Qed.
Lemma lem5135768 (s : real -> Prop) : (term148 s) = (term174 s).
Proof. exact (MK_COMB (@lem5135767 s) (@lem5135766 s)). Qed.
Lemma lem5135770 {A : Type'} (P : Prop) (Q : A -> Prop) : (term175 A P Q) = (term176 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5135771 (P : Prop) (Q : type1028) : (term177 P Q) = (term178 P Q).
Proof. exact (@lem5135770 (real -> real) P Q). Qed.
Lemma lem5135772 (s : real -> Prop) : (term179 s) = (term180 s).
Proof. exact (@lem5135771 (term126 s) (term172 s)). Qed.
Lemma lem5135773 (s : real -> Prop) (x : real -> real) : (term181 s x) = (term170 s x).
Proof. exact (eq_refl (term181 s x)). Qed.
Lemma lem5135774 (s : real -> Prop) : (term182 s) = (term172 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5135773 s x)). Qed.
Lemma lem5135775 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5135776 (s : real -> Prop) : (term183 s) = (term173 s).
Proof. exact (MK_COMB (@lem5135775) (@lem5135774 s)). Qed.
Lemma lem5135777 (s : real -> Prop) : (term146 s) = (term146 s).
Proof. exact (eq_refl (term146 s)). Qed.
Lemma lem5135778 (s : real -> Prop) : (term179 s) = (term174 s).
Proof. exact (MK_COMB (@lem5135777 s) (@lem5135776 s)). Qed.
Lemma lem5135779 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5135780 (s : real -> Prop) : (term184 s) = (term185 s).
Proof. exact (MK_COMB (@lem5135779) (@lem5135778 s)). Qed.
Lemma lem5135781 (s : real -> Prop) (x : real -> real) : (term181 s x) = (term170 s x).
Proof. exact (eq_refl (term181 s x)). Qed.
Lemma lem5135782 (s : real -> Prop) : (term146 s) = (term146 s).
Proof. exact (eq_refl (term146 s)). Qed.
Lemma lem5135783 (s : real -> Prop) (x : real -> real) : (term186 s x) = (term187 s x).
Proof. exact (MK_COMB (@lem5135782 s) (@lem5135781 s x)). Qed.
Lemma lem5135784 (s : real -> Prop) : (term188 s) = (term189 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5135783 s x)). Qed.
Lemma lem5135785 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5135786 (s : real -> Prop) : (term180 s) = (term190 s).
Proof. exact (MK_COMB (@lem5135785) (@lem5135784 s)). Qed.
Lemma lem5135787 (s : real -> Prop) : ((term179 s) = (term180 s)) = ((term174 s) = (term190 s)).
Proof. exact (MK_COMB (@lem5135780 s) (@lem5135786 s)). Qed.
Lemma lem5135788 (s : real -> Prop) : (term174 s) = (term190 s).
Proof. exact (EQ_MP (@lem5135787 s) (@lem5135772 s)). Qed.
Lemma lem5135790 (s : real -> Prop) : (term148 s) = (term190 s).
Proof. exact (TRANS (@lem5135768 s) (@lem5135788 s)). Qed.
Lemma lem5135791 (s : real -> Prop) : (term90 s) = (term190 s).
Proof. exact (TRANS (@lem5135679 s) (@lem5135790 s)). Qed.
Lemma lem5135792 (s : real -> Prop) (h1 : term90 s) : term190 s.
Proof. exact (EQ_MP (@lem5135791 s) (@lem5135566 s h1)). Qed.
Lemma lem5135794 (x : real) (s : real -> Prop) : (@IN real x s) = (@IN real x s).
Proof. exact (eq_refl (@IN real x s)). Qed.
Lemma lem5135795 (P : real -> Prop) : (term118 P) = (term119 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5135796 (s : real -> Prop) : (term120 s) = (term121 s).
Proof. exact (@lem5135795 (term54 s)). Qed.
Lemma lem5135797 (x : real) (s : real -> Prop) : (term55 s x) = (@IN real x s).
Proof. exact (eq_refl (term55 s x)). Qed.
Lemma lem5135798 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5135800 (x : real) (s : real -> Prop) : (term122 s x) = (term123 x s).
Proof. exact (MK_COMB (@lem5135798) (@lem5135797 x s)). Qed.
Lemma lem5135801 (s : real -> Prop) : (term124 s) = (term125 s).
Proof. exact (fun_ext (fun x : real => @lem5135800 x s)). Qed.
Lemma lem5135802 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5135803 (s : real -> Prop) : (term121 s) = (term126 s).
Proof. exact (MK_COMB (@lem5135802) (@lem5135801 s)). Qed.
Lemma lem5135804 (s : real -> Prop) : (term120 s) = (term126 s).
Proof. exact (TRANS (@lem5135796 s) (@lem5135803 s)). Qed.
Lemma lem5135805 (s : real -> Prop) : (term54 s) = (term54 s).
Proof. exact (fun_ext (fun x : real => @lem5135794 x s)). Qed.
Lemma lem5135806 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5135807 (s : real -> Prop) : (term58 s) = (term58 s).
Proof. exact (MK_COMB (@lem5135806) (@lem5135805 s)). Qed.
Lemma lem5135808 (s : real -> Prop) : (term51 s) = (term51 s).
Proof. exact (eq_refl (term51 s)). Qed.
Lemma lem5135811 (s : real -> Prop) : (term191 s) = (s = (@EMPTY real)).
Proof. exact (@lem16933 (s = (@EMPTY real))). Qed.
Lemma lem5135812 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5135813 (s : real -> Prop) : (term145 s) = (term146 s).
Proof. exact (MK_COMB (@lem5135812) (@lem5135804 s)). Qed.
Lemma lem5135814 (s : real -> Prop) : (term192 s) = (term193 s).
Proof. exact (MK_COMB (@lem5135813 s) (@lem5135808 s)). Qed.
Lemma lem5135815 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5135816 (s : real -> Prop) : (term194 s) = (term194 s).
Proof. exact (MK_COMB (@lem5135815) (@lem5135807 s)). Qed.
Lemma lem5135817 (s : real -> Prop) : (term195 s) = (term196 s).
Proof. exact (MK_COMB (@lem5135816 s) (@lem5135811 s)). Qed.
Lemma lem5135818 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5135819 (s : real -> Prop) : (term197 s) = (term198 s).
Proof. exact (MK_COMB (@lem5135818) (@lem5135817 s)). Qed.
Lemma lem5135820 (s : real -> Prop) : (term199 s) = (term200 s).
Proof. exact (MK_COMB (@lem5135819 s) (@lem5135814 s)). Qed.
Lemma lem5135821 (s : real -> Prop) : ((term58 s) = (term51 s)) = (term199 s).
Proof. exact (@lem17784 (term58 s) (term51 s)). Qed.
Lemma lem5135822 (s : real -> Prop) : ((term58 s) = (term51 s)) = (term200 s).
Proof. exact (TRANS (@lem5135821 s) (@lem5135820 s)). Qed.
Lemma lem5135823 : term114 = term201.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5135822 s)). Qed.
Lemma lem5135824 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5135825 : term91 = term202.
Proof. exact (MK_COMB (@lem5135824) (@lem5135823)). Qed.
Lemma lem5135827 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term203 A P Q) = (term204 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5135828 (P : type1022) (Q : type1022) : (term205 P Q) = (term206 P Q).
Proof. exact (@lem5135827 (real -> Prop) P Q). Qed.
Lemma lem5135829 : term207 = term208.
Proof. exact (@lem5135828 term209 term210). Qed.
Lemma lem5135830 (s : real -> Prop) : (term211 s) = (term196 s).
Proof. exact (eq_refl (term211 s)). Qed.
Lemma lem5135831 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5135832 (s : real -> Prop) : (term212 s) = (term198 s).
Proof. exact (MK_COMB (@lem5135831) (@lem5135830 s)). Qed.
Lemma lem5135833 (s : real -> Prop) : (term213 s) = (term193 s).
Proof. exact (eq_refl (term213 s)). Qed.
Lemma lem5135834 (s : real -> Prop) : (term214 s) = (term200 s).
Proof. exact (MK_COMB (@lem5135832 s) (@lem5135833 s)). Qed.
Lemma lem5135835 : term215 = term201.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5135834 s)). Qed.
Lemma lem5135836 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5135837 : term207 = term202.
Proof. exact (MK_COMB (@lem5135836) (@lem5135835)). Qed.
Lemma lem5135838 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5135839 : term216 = term217.
Proof. exact (MK_COMB (@lem5135838) (@lem5135837)). Qed.
Lemma lem5135840 (s : real -> Prop) : (term211 s) = (term196 s).
Proof. exact (eq_refl (term211 s)). Qed.
Lemma lem5135841 : term218 = term209.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5135840 s)). Qed.
Lemma lem5135842 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5135843 : term219 = term220.
Proof. exact (MK_COMB (@lem5135842) (@lem5135841)). Qed.
Lemma lem5135844 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5135845 : term221 = term222.
Proof. exact (MK_COMB (@lem5135844) (@lem5135843)). Qed.
Lemma lem5135846 (s : real -> Prop) : (term213 s) = (term193 s).
Proof. exact (eq_refl (term213 s)). Qed.
Lemma lem5135847 : term223 = term210.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5135846 s)). Qed.
Lemma lem5135848 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5135849 : term224 = term225.
Proof. exact (MK_COMB (@lem5135848) (@lem5135847)). Qed.
Lemma lem5135850 : term208 = term226.
Proof. exact (MK_COMB (@lem5135845) (@lem5135849)). Qed.
Lemma lem5135851 : (term207 = term208) = (term202 = term226).
Proof. exact (MK_COMB (@lem5135839) (@lem5135850)). Qed.
Lemma lem5135852 : term202 = term226.
Proof. exact (EQ_MP (@lem5135851) (@lem5135829)). Qed.
Lemma lem5135958 {A : Type'} (P : A -> Prop) (Q : Prop) : (term227 A P Q) = (term228 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5135959 (P : real -> Prop) (Q : Prop) : (term229 P Q) = (term230 P Q).
Proof. exact (@lem5135958 real P Q). Qed.
Lemma lem5135960 (s : real -> Prop) : (term231 s) = (term232 s).
Proof. exact (@lem5135959 (term54 s) (s = (@EMPTY real))). Qed.
Lemma lem5135961 (x : real) (s : real -> Prop) : (term55 s x) = (@IN real x s).
Proof. exact (eq_refl (term55 s x)). Qed.
Lemma lem5135962 (s : real -> Prop) : (term56 s) = (term54 s).
Proof. exact (fun_ext (fun x : real => @lem5135961 x s)). Qed.
Lemma lem5135963 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5135964 (s : real -> Prop) : (term57 s) = (term58 s).
Proof. exact (MK_COMB (@lem5135963) (@lem5135962 s)). Qed.
Lemma lem5135965 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5135966 (s : real -> Prop) : (term233 s) = (term194 s).
Proof. exact (MK_COMB (@lem5135965) (@lem5135964 s)). Qed.
Lemma lem5135967 (s : real -> Prop) : (s = (@EMPTY real)) = (s = (@EMPTY real)).
Proof. exact (eq_refl (s = (@EMPTY real))). Qed.
Lemma lem5135968 (s : real -> Prop) : (term231 s) = (term196 s).
Proof. exact (MK_COMB (@lem5135966 s) (@lem5135967 s)). Qed.
Lemma lem5135969 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5135970 (s : real -> Prop) : (term234 s) = (term235 s).
Proof. exact (MK_COMB (@lem5135969) (@lem5135968 s)). Qed.
Lemma lem5135971 (x : real) (s : real -> Prop) : (term55 s x) = (@IN real x s).
Proof. exact (eq_refl (term55 s x)). Qed.
Lemma lem5135972 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5135973 (x : real) (s : real -> Prop) : (term236 s x) = (term237 x s).
Proof. exact (MK_COMB (@lem5135972) (@lem5135971 x s)). Qed.
Lemma lem5135974 (s : real -> Prop) : (s = (@EMPTY real)) = (s = (@EMPTY real)).
Proof. exact (eq_refl (s = (@EMPTY real))). Qed.
Lemma lem5135975 (x : real) (s : real -> Prop) : (term238 x s) = (term239 x s).
Proof. exact (MK_COMB (@lem5135973 x s) (@lem5135974 s)). Qed.
Lemma lem5135976 (s : real -> Prop) : (term240 s) = (term241 s).
Proof. exact (fun_ext (fun x : real => @lem5135975 x s)). Qed.
Lemma lem5135977 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5135978 (s : real -> Prop) : (term232 s) = (term242 s).
Proof. exact (MK_COMB (@lem5135977) (@lem5135976 s)). Qed.
Lemma lem5135979 (s : real -> Prop) : ((term231 s) = (term232 s)) = ((term196 s) = (term242 s)).
Proof. exact (MK_COMB (@lem5135970 s) (@lem5135978 s)). Qed.
Lemma lem5135980 (s : real -> Prop) : (term196 s) = (term242 s).
Proof. exact (EQ_MP (@lem5135979 s) (@lem5135960 s)). Qed.
Lemma lem5135981 : term209 = term243.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5135980 s)). Qed.
Lemma lem5135982 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5135983 : term220 = term244.
Proof. exact (MK_COMB (@lem5135982) (@lem5135981)). Qed.
Lemma lem5135985 {A B : Type'} (P : type1413 A B) : (term149 A B P) = (term150 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5135986 (P : type1020) : (term245 P) = (term246 P).
Proof. exact (@lem5135985 (real -> Prop) real P). Qed.
Lemma lem5135987 : term247 = term248.
Proof. exact (@lem5135986 term249). Qed.
Lemma lem5135988 (s : real -> Prop) : (term250 s) = (term241 s).
Proof. exact (eq_refl (term250 s)). Qed.
Lemma lem5135989 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5135990 (s : real -> Prop) (x : real) : (term251 s x) = (term252 s x).
Proof. exact (MK_COMB (@lem5135988 s) (@lem5135989 x)). Qed.
Lemma lem5135991 (x : real) (s : real -> Prop) : (term252 s x) = (term239 x s).
Proof. exact (eq_refl (term252 s x)). Qed.
Lemma lem5135992 (x : real) (s : real -> Prop) : (term251 s x) = (term239 x s).
Proof. exact (TRANS (@lem5135990 s x) (@lem5135991 x s)). Qed.
Lemma lem5135993 (s : real -> Prop) : (term253 s) = (term241 s).
Proof. exact (fun_ext (fun x : real => @lem5135992 x s)). Qed.
Lemma lem5135994 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5135995 (s : real -> Prop) : (term254 s) = (term242 s).
Proof. exact (MK_COMB (@lem5135994) (@lem5135993 s)). Qed.
Lemma lem5135996 : term255 = term243.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5135995 s)). Qed.
Lemma lem5135997 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5135998 : term247 = term244.
Proof. exact (MK_COMB (@lem5135997) (@lem5135996)). Qed.
Lemma lem5135999 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5136000 : term256 = term257.
Proof. exact (MK_COMB (@lem5135999) (@lem5135998)). Qed.
Lemma lem5136001 (s : real -> Prop) : (term250 s) = (term241 s).
Proof. exact (eq_refl (term250 s)). Qed.
Lemma lem5136002 (x : type1023) (s : real -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem5136003 (x : type1023) (s : real -> Prop) : (term258 x s) = (term259 x s).
Proof. exact (MK_COMB (@lem5136001 s) (@lem5136002 x s)). Qed.
Lemma lem5136004 (x : type1023) (s : real -> Prop) : (term259 x s) = (term260 x s).
Proof. exact (eq_refl (term259 x s)). Qed.
Lemma lem5136005 (x : type1023) (s : real -> Prop) : (term258 x s) = (term260 x s).
Proof. exact (TRANS (@lem5136003 x s) (@lem5136004 x s)). Qed.
Lemma lem5136006 (x : type1023) : (term261 x) = (term262 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5136005 x s)). Qed.
Lemma lem5136007 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5136008 (x : type1023) : (term263 x) = (term264 x).
Proof. exact (MK_COMB (@lem5136007) (@lem5136006 x)). Qed.
Lemma lem5136009 : term265 = term266.
Proof. exact (fun_ext (fun x : type1023 => @lem5136008 x)). Qed.
Lemma lem5136010 : (@ex ((real -> Prop) -> real)) = (@ex ((real -> Prop) -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real))). Qed.
Lemma lem5136011 : term248 = term267.
Proof. exact (MK_COMB (@lem5136010) (@lem5136009)). Qed.
Lemma lem5136012 : (term247 = term248) = (term244 = term267).
Proof. exact (MK_COMB (@lem5136000) (@lem5136011)). Qed.
Lemma lem5136013 : term244 = term267.
Proof. exact (EQ_MP (@lem5136012) (@lem5135987)). Qed.
Lemma lem5136014 : term220 = term267.
Proof. exact (TRANS (@lem5135983) (@lem5136013)). Qed.
Lemma lem5136015 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5136016 : term222 = term268.
Proof. exact (MK_COMB (@lem5136015) (@lem5136014)). Qed.
Lemma lem5136017 : term225 = term225.
Proof. exact (eq_refl term225). Qed.
Lemma lem5136018 : term226 = term269.
Proof. exact (MK_COMB (@lem5136016) (@lem5136017)). Qed.
Lemma lem5136020 {A : Type'} (P : A -> Prop) (Q : Prop) : (term270 A P Q) = (term271 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5136021 (P : type257) (Q : Prop) : (term272 P Q) = (term273 P Q).
Proof. exact (@lem5136020 type1023 P Q). Qed.
Lemma lem5136022 : term274 = term275.
Proof. exact (@lem5136021 term266 term225). Qed.
Lemma lem5136023 (x : type1023) : (term276 x) = (term264 x).
Proof. exact (eq_refl (term276 x)). Qed.
Lemma lem5136024 : term277 = term266.
Proof. exact (fun_ext (fun x : type1023 => @lem5136023 x)). Qed.
Lemma lem5136025 : (@ex ((real -> Prop) -> real)) = (@ex ((real -> Prop) -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real))). Qed.
Lemma lem5136026 : term278 = term267.
Proof. exact (MK_COMB (@lem5136025) (@lem5136024)). Qed.
Lemma lem5136027 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5136028 : term279 = term268.
Proof. exact (MK_COMB (@lem5136027) (@lem5136026)). Qed.
Lemma lem5136029 : term225 = term225.
Proof. exact (eq_refl term225). Qed.
Lemma lem5136030 : term274 = term269.
Proof. exact (MK_COMB (@lem5136028) (@lem5136029)). Qed.
Lemma lem5136031 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5136032 : term280 = term281.
Proof. exact (MK_COMB (@lem5136031) (@lem5136030)). Qed.
Lemma lem5136033 (x : type1023) : (term276 x) = (term264 x).
Proof. exact (eq_refl (term276 x)). Qed.
Lemma lem5136034 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5136035 (x : type1023) : (term282 x) = (term283 x).
Proof. exact (MK_COMB (@lem5136034) (@lem5136033 x)). Qed.
Lemma lem5136036 : term225 = term225.
Proof. exact (eq_refl term225). Qed.
Lemma lem5136037 (x : type1023) : (term284 x) = (term285 x).
Proof. exact (MK_COMB (@lem5136035 x) (@lem5136036)). Qed.
Lemma lem5136038 : term286 = term287.
Proof. exact (fun_ext (fun x : type1023 => @lem5136037 x)). Qed.
Lemma lem5136039 : (@ex ((real -> Prop) -> real)) = (@ex ((real -> Prop) -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real))). Qed.
Lemma lem5136040 : term275 = term288.
Proof. exact (MK_COMB (@lem5136039) (@lem5136038)). Qed.
Lemma lem5136041 : (term274 = term275) = (term269 = term288).
Proof. exact (MK_COMB (@lem5136032) (@lem5136040)). Qed.
Lemma lem5136042 : term269 = term288.
Proof. exact (EQ_MP (@lem5136041) (@lem5136022)). Qed.
Lemma lem5136043 : term226 = term288.
Proof. exact (TRANS (@lem5136018) (@lem5136042)). Qed.
Lemma lem5136044 : term202 = term288.
Proof. exact (TRANS (@lem5135852) (@lem5136043)). Qed.
Lemma lem5136045 : term91 = term288.
Proof. exact (TRANS (@lem5135825) (@lem5136044)). Qed.
Lemma lem5136046 (h1 : term91) : term288.
Proof. exact (EQ_MP (@lem5136045) (@lem5135567 h1)). Qed.
Lemma lem5136047 (x : type1023) (h1 : term285 x) : term285 x.
Proof. exact (h1). Qed.
Lemma lem5136048 (s : real -> Prop) (x' : real -> real) (h1 : term187 s x') : term187 s x'.
Proof. exact (h1). Qed.
Lemma lem5136056 (s : real -> Prop) (h1 : term51 s) : term51 s.
Proof. exact (h1). Qed.
Lemma lem5136071 (s : real -> Prop) (x : real) (b : real) : (term115 s x b) = (term115 s x b).
Proof. exact (eq_refl (term115 s x b)). Qed.
Lemma lem5136072 (s : real -> Prop) (b : real) : (term116 s b) = (term116 s b).
Proof. exact (fun_ext (fun x : real => @lem5136071 s x b)). Qed.
Lemma lem5136073 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5136074 (s : real -> Prop) (b : real) : (term117 s b) = (term117 s b).
Proof. exact (MK_COMB (@lem5136073) (@lem5136072 s b)). Qed.
Lemma lem5136075 (s : real -> Prop) (b : real) (h1 : term52 s b) : term117 s b.
Proof. exact (EQ_MP (@lem5136074 s b) (@lem5135636 s b h1)). Qed.
Lemma lem5136082 (s : real -> Prop) : (term51 s) = (term51 s).
Proof. exact (eq_refl (term51 s)). Qed.
Lemma lem5136089 (x : real) (s : real -> Prop) : (term123 x s) = (term123 x s).
Proof. exact (eq_refl (term123 x s)). Qed.
Lemma lem5136090 (s : real -> Prop) : (term125 s) = (term125 s).
Proof. exact (fun_ext (fun x : real => @lem5136089 x s)). Qed.
Lemma lem5136091 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5136092 (s : real -> Prop) : (term126 s) = (term126 s).
Proof. exact (MK_COMB (@lem5136091) (@lem5136090 s)). Qed.
Lemma lem5136093 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5136094 (s : real -> Prop) : (term146 s) = (term146 s).
Proof. exact (MK_COMB (@lem5136093) (@lem5136092 s)). Qed.
Lemma lem5136095 (s : real -> Prop) : (term193 s) = (term193 s).
Proof. exact (MK_COMB (@lem5136094 s) (@lem5136082 s)). Qed.
Lemma lem5136096 : term210 = term210.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5136095 s)). Qed.
Lemma lem5136097 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5136098 : term225 = term225.
Proof. exact (MK_COMB (@lem5136097) (@lem5136096)). Qed.
Lemma lem5136113 (x : type1023) (s : real -> Prop) : (term260 x s) = (term260 x s).
Proof. exact (eq_refl (term260 x s)). Qed.
Lemma lem5136114 (x : type1023) : (term262 x) = (term262 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5136113 x s)). Qed.
Lemma lem5136115 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5136116 (x : type1023) : (term264 x) = (term264 x).
Proof. exact (MK_COMB (@lem5136115) (@lem5136114 x)). Qed.
Lemma lem5136117 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5136118 (x : type1023) : (term283 x) = (term283 x).
Proof. exact (MK_COMB (@lem5136117) (@lem5136116 x)). Qed.
Lemma lem5136119 (x : type1023) : (term285 x) = (term285 x).
Proof. exact (MK_COMB (@lem5136118 x) (@lem5136098)). Qed.
Lemma lem5136120 (x : type1023) (h1 : term285 x) : term285 x.
Proof. exact (EQ_MP (@lem5136119 x) (@lem5136047 x h1)). Qed.
Lemma lem5136139 (s : real -> Prop) (x' : real -> real) (a : real) : (term166 s x' a) = (term166 s x' a).
Proof. exact (eq_refl (term166 s x' a)). Qed.
Lemma lem5136140 (s : real -> Prop) (x' : real -> real) : (term168 s x') = (term168 s x').
Proof. exact (fun_ext (fun a : real => @lem5136139 s x' a)). Qed.
Lemma lem5136141 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5136142 (s : real -> Prop) (x' : real -> real) : (term170 s x') = (term170 s x').
Proof. exact (MK_COMB (@lem5136141) (@lem5136140 s x')). Qed.
Lemma lem5136149 (x : real) (s : real -> Prop) : (term123 x s) = (term123 x s).
Proof. exact (eq_refl (term123 x s)). Qed.
Lemma lem5136150 (s : real -> Prop) : (term125 s) = (term125 s).
Proof. exact (fun_ext (fun x : real => @lem5136149 x s)). Qed.
Lemma lem5136151 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5136152 (s : real -> Prop) : (term126 s) = (term126 s).
Proof. exact (MK_COMB (@lem5136151) (@lem5136150 s)). Qed.
Lemma lem5136153 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5136154 (s : real -> Prop) : (term146 s) = (term146 s).
Proof. exact (MK_COMB (@lem5136153) (@lem5136152 s)). Qed.
Lemma lem5136155 (s : real -> Prop) (x' : real -> real) : (term187 s x') = (term187 s x').
Proof. exact (MK_COMB (@lem5136154 s) (@lem5136142 s x')). Qed.
Lemma lem5136156 (s : real -> Prop) (x' : real -> real) (h1 : term187 s x') : term187 s x'.
Proof. exact (EQ_MP (@lem5136155 s x') (@lem5136048 s x' h1)). Qed.
Lemma lem5136158 (x : type1023) (h1 : term285 x) : term264 x.
Proof. exact (proj1 (@lem5136120 x h1)). Qed.
Lemma lem5136159 (s : real -> Prop) (h1 : term126 s) : term126 s.
Proof. exact (h1). Qed.
Lemma lem5136160 (s : real -> Prop) (x' : real -> real) (h1 : term170 s x') : term170 s x'.
Proof. exact (h1). Qed.
Lemma lem5136164 (s : real -> Prop) (h1 : term51 s) : term51 s.
Proof. exact (h1). Qed.
Lemma lem5136185 (x : type1023) (s : real -> Prop) : (term260 x s) = (term260 x s).
Proof. exact (eq_refl (term260 x s)). Qed.
Lemma lem5136186 (x : type1023) : (term262 x) = (term262 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5136185 x s)). Qed.
Lemma lem5136187 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5136189 (x : type1023) : (term264 x) = (term264 x).
Proof. exact (MK_COMB (@lem5136187) (@lem5136186 x)). Qed.
Lemma lem5136190 (x : type1023) (h1 : term285 x) : term264 x.
Proof. exact (EQ_MP (@lem5136189 x) (@lem5136158 x h1)). Qed.
Lemma lem5136234 (x : real) (s : real -> Prop) : (term123 x s) = (term123 x s).
Proof. exact (eq_refl (term123 x s)). Qed.
Lemma lem5136235 (s : real -> Prop) : (term125 s) = (term125 s).
Proof. exact (fun_ext (fun x : real => @lem5136234 x s)). Qed.
Lemma lem5136236 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5136238 (s : real -> Prop) : (term126 s) = (term126 s).
Proof. exact (MK_COMB (@lem5136236) (@lem5136235 s)). Qed.
Lemma lem5136239 (s : real -> Prop) (h1 : term126 s) : term126 s.
Proof. exact (EQ_MP (@lem5136238 s) (@lem5136159 s h1)). Qed.
Lemma lem5136251 (s : real -> Prop) (x : real) (b : real) : (term115 s x b) = (term115 s x b).
Proof. exact (eq_refl (term115 s x b)). Qed.
Lemma lem5136252 (s : real -> Prop) (b : real) : (term116 s b) = (term116 s b).
Proof. exact (fun_ext (fun x : real => @lem5136251 s x b)). Qed.
Lemma lem5136253 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5136255 (s : real -> Prop) (b : real) : (term117 s b) = (term117 s b).
Proof. exact (MK_COMB (@lem5136253) (@lem5136252 s b)). Qed.
Lemma lem5136256 (s : real -> Prop) (b : real) (h1 : term52 s b) : term117 s b.
Proof. exact (EQ_MP (@lem5136255 s b) (@lem5136075 s b h1)). Qed.
Lemma lem5136317 (s : real -> Prop) (x' : real -> real) (a : real) : (term166 s x' a) = (term166 s x' a).
Proof. exact (eq_refl (term166 s x' a)). Qed.
Lemma lem5136318 (s : real -> Prop) (x' : real -> real) : (term168 s x') = (term168 s x').
Proof. exact (fun_ext (fun a : real => @lem5136317 s x' a)). Qed.
Lemma lem5136319 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5136321 (s : real -> Prop) (x' : real -> real) : (term170 s x') = (term170 s x').
Proof. exact (MK_COMB (@lem5136319) (@lem5136318 s x')). Qed.
Lemma lem5136322 (s : real -> Prop) (x' : real -> real) (h1 : term170 s x') : term170 s x'.
Proof. exact (EQ_MP (@lem5136321 s x') (@lem5136160 s x' h1)). Qed.
Lemma lem5136326 (_67051 : real -> Prop) (x : type1023) (h1 : term285 x) : term289 x _67051.
Proof. exact (@lem5136190 x h1 _67051). Qed.
Lemma lem5136327 (x : type1023) (_67051 : real -> Prop) : (term289 x _67051) = (term260 x _67051).
Proof. exact (eq_refl (term289 x _67051)). Qed.
Lemma lem5136335 (_67054 : real) (s : real -> Prop) (h1 : term126 s) : term290 s _67054.
Proof. exact (@lem5136239 s h1 _67054). Qed.
Lemma lem5136336 (_67054 : real) (s : real -> Prop) : (term290 s _67054) = (term123 _67054 s).
Proof. exact (eq_refl (term290 s _67054)). Qed.
Lemma lem5136338 (_67055 : real) (s : real -> Prop) (b : real) (h1 : term52 s b) : term291 s b _67055.
Proof. exact (@lem5136256 s b h1 _67055). Qed.
Lemma lem5136339 (s : real -> Prop) (_67055 : real) (b : real) : (term291 s b _67055) = (term115 s _67055 b).
Proof. exact (eq_refl (term291 s b _67055)). Qed.
Lemma lem5136350 (_67059 : real) (s : real -> Prop) (x' : real -> real) (h1 : term170 s x') : term292 s x' _67059.
Proof. exact (@lem5136322 s x' h1 _67059). Qed.
Lemma lem5136351 (s : real -> Prop) (x' : real -> real) (_67059 : real) : (term292 s x' _67059) = (term166 s x' _67059).
Proof. exact (eq_refl (term292 s x' _67059)). Qed.
Lemma lem5136352 (_67059 : real) (s : real -> Prop) (x' : real -> real) (h1 : term170 s x') : term166 s x' _67059.
Proof. exact (EQ_MP (@lem5136351 s x' _67059) (@lem5136350 _67059 s x' h1)). Qed.
Lemma lem5136356 (s : real -> Prop) (h1 : term51 s) : term51 s.
Proof. exact (h1). Qed.
Lemma lem5136368 (_67051 : real -> Prop) (x : type1023) (h1 : term285 x) : term260 x _67051.
Proof. exact (EQ_MP (@lem5136327 x _67051) (@lem5136326 _67051 x h1)). Qed.
Lemma lem5136376 (_67054 : real) (s : real -> Prop) (h1 : term126 s) : term123 _67054 s.
Proof. exact (EQ_MP (@lem5136336 _67054 s) (@lem5136335 _67054 s h1)). Qed.
Lemma lem5136384 (_67055 : real) (s : real -> Prop) (b : real) (h1 : term52 s b) : term115 s _67055 b.
Proof. exact (EQ_MP (@lem5136339 s _67055 b) (@lem5136338 _67055 s b h1)). Qed.
Lemma lem5136400 (_67059 : real) (s : real -> Prop) (x' : real -> real) (h1 : term170 s x') : term293 x' _67059.
Proof. exact (proj2 (@lem5136352 _67059 s x' h1)). Qed.
Lemma lem5136452 (s : real -> Prop) (h1 : term51 s) : term51 s.
Proof. exact (h1). Qed.
Lemma lem5136453 (s : real -> Prop) (h1 : term51 s) : term294 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5136452 s h1). Qed.
Lemma lem5136455 (p : Prop) : (term295 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5136456 (s : real -> Prop) : (term294 s) = (term51 s).
Proof. exact (@lem5136455 (s = (@EMPTY real))). Qed.
Lemma lem5136457 (s : real -> Prop) (h1 : term51 s) : term51 s.
Proof. exact (EQ_MP (@lem5136456 s) (@lem5136453 s h1)). Qed.
Lemma lem5136459 (b : Prop) (a : Prop) : (a \/ b) = (term296 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5136462 (x : type1023) (_67051 : real -> Prop) : (term260 x _67051) = (term297 x _67051).
Proof. exact (@lem5136459 (_67051 = (@EMPTY real)) (term298 x _67051)). Qed.
Lemma lem5136465 (_67051 : real -> Prop) (x : type1023) (h1 : term285 x) : term297 x _67051.
Proof. exact (EQ_MP (@lem5136462 x _67051) (@lem5136368 _67051 x h1)). Qed.
Lemma lem5136466 (s : real -> Prop) (x : type1023) (h1 : term285 x) : term297 x s.
Proof. exact (@lem5136465 s x h1). Qed.
Lemma lem5136469 (s : real -> Prop) (x : type1023) (h1 : term51 s) (h2 : term285 x) : term298 x s.
Proof. exact (@lem5136466 s x h2 (@lem5136457 s h1)). Qed.
Lemma lem5136470 (s : real -> Prop) (x : type1023) (h1 : term51 s) (h2 : term285 x) : term299 x s.
Proof. exact (fun h0 : term300 x s => @lem5136469 s x h1 h2). Qed.
Lemma lem5136472 (p : Prop) : (term301 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5136473 (x : type1023) (s : real -> Prop) : (term299 x s) = (term298 x s).
Proof. exact (@lem5136472 (term298 x s)). Qed.
Lemma lem5136474 (s : real -> Prop) (x : type1023) (h1 : term51 s) (h2 : term285 x) : term298 x s.
Proof. exact (EQ_MP (@lem5136473 x s) (@lem5136470 s x h1 h2)). Qed.
Lemma lem5136477 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5136479 (_67054 : real) (s : real -> Prop) : (term123 _67054 s) = (term302 _67054 s).
Proof. exact (@lem5136477 (@IN real _67054 s)). Qed.
Lemma lem5136482 (_67054 : real) (s : real -> Prop) (h1 : term126 s) : term302 _67054 s.
Proof. exact (EQ_MP (@lem5136479 _67054 s) (@lem5136376 _67054 s h1)). Qed.
Lemma lem5136483 (x : type1023) (s : real -> Prop) (h1 : term126 s) : term303 x s.
Proof. exact (@lem5136482 (x s) s h1). Qed.
Lemma lem5136486 (s : real -> Prop) (x : type1023) (h1 : term126 s) (h2 : term51 s) (h3 : term285 x) : False.
Proof. exact (@lem5136483 x s h1 (@lem5136474 s x h2 h3)). Qed.
Lemma lem5136487 (s : real -> Prop) (x : type1023) (h1 : term126 s) (h2 : term51 s) (h3 : term285 x) : term304.
Proof. exact (fun h0 : ~ False => @lem5136486 s x h1 h2 h3). Qed.
Lemma lem5136489 (p : Prop) : (term301 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5136490 : term304 = False.
Proof. exact (@lem5136489 False). Qed.
Lemma lem5136491 (s : real -> Prop) (x : type1023) (h1 : term126 s) (h2 : term51 s) (h3 : term285 x) : False.
Proof. exact (EQ_MP (@lem5136490) (@lem5136487 s x h1 h2 h3)). Qed.
Lemma lem5136551 (_67059 : real) (s : real -> Prop) (x' : real -> real) (h1 : term170 s x') : term305 x' _67059 s.
Proof. exact (proj1 (@lem5136352 _67059 s x' h1)). Qed.
Lemma lem5136552 (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term170 s x') : term305 x' b s.
Proof. exact (@lem5136551 b s x' h1). Qed.
Lemma lem5136553 (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term170 s x') : term306 x' b s.
Proof. exact (fun h0 : term307 x' b s => @lem5136552 b s x' h1). Qed.
Lemma lem5136555 (p : Prop) : (term301 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5136556 (x' : real -> real) (b : real) (s : real -> Prop) : (term306 x' b s) = (term305 x' b s).
Proof. exact (@lem5136555 (term305 x' b s)). Qed.
Lemma lem5136557 (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term170 s x') : term305 x' b s.
Proof. exact (EQ_MP (@lem5136556 x' b s) (@lem5136553 b s x' h1)). Qed.
Lemma lem5136563 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5136564 (b : real) (_67055 : real) (s : real -> Prop) : (term115 s _67055 b) = (term308 b _67055 s).
Proof. exact (@lem5136563 (real_le _67055 b) (term123 _67055 s)). Qed.
Lemma lem5136570 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5136571 (b : real) (_67055 : real) (s : real -> Prop) : (term309 s _67055 b) = (term310 b _67055 s).
Proof. exact (MK_COMB (@lem5136570) (@lem5136564 b _67055 s)). Qed.
Lemma lem5136577 (b : real) (_67055 : real) (s : real -> Prop) : (term308 b _67055 s) = (term308 b _67055 s).
Proof. exact (eq_refl (term308 b _67055 s)). Qed.
Lemma lem5136578 (b : real) (_67055 : real) (s : real -> Prop) : ((term115 s _67055 b) = (term308 b _67055 s)) = ((term308 b _67055 s) = (term308 b _67055 s)).
Proof. exact (MK_COMB (@lem5136571 b _67055 s) (@lem5136577 b _67055 s)). Qed.
Lemma lem5136580 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5136581 (x : Prop) : (x = x) = True.
Proof. exact (@lem5136580 Prop x). Qed.
Lemma lem5136582 (b : real) (_67055 : real) (s : real -> Prop) : ((term308 b _67055 s) = (term308 b _67055 s)) = True.
Proof. exact (@lem5136581 (term308 b _67055 s)). Qed.
Lemma lem5136583 (b : real) (_67055 : real) (s : real -> Prop) : ((term115 s _67055 b) = (term308 b _67055 s)) = True.
Proof. exact (TRANS (@lem5136578 b _67055 s) (@lem5136582 b _67055 s)). Qed.
Lemma lem5136584 (b : real) (_67055 : real) (s : real -> Prop) : True = ((term115 s _67055 b) = (term308 b _67055 s)).
Proof. exact (SYM (@lem5136583 b _67055 s)). Qed.
Lemma lem5136585 (b : real) (_67055 : real) (s : real -> Prop) : (term115 s _67055 b) = (term308 b _67055 s).
Proof. exact (EQ_MP (@lem5136584 b _67055 s) (@lem0)). Qed.
Lemma lem5136586 (_67055 : real) (s : real -> Prop) (b : real) (h1 : term52 s b) : term308 b _67055 s.
Proof. exact (EQ_MP (@lem5136585 b _67055 s) (@lem5136384 _67055 s b h1)). Qed.
Lemma lem5136588 (b : Prop) (a : Prop) : (a \/ b) = (term296 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5136589 (s : real -> Prop) (_67055 : real) (b : real) : (term308 b _67055 s) = (term311 s _67055 b).
Proof. exact (@lem5136588 (term123 _67055 s) (real_le _67055 b)). Qed.
Lemma lem5136591 (a : Prop) : (term312 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5136592 (_67055 : real) (s : real -> Prop) : (term313 _67055 s) = (@IN real _67055 s).
Proof. exact (@lem5136591 (@IN real _67055 s)). Qed.
Lemma lem5136593 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5136594 (_67055 : real) (s : real -> Prop) : (term314 _67055 s) = (term11 _67055 s).
Proof. exact (MK_COMB (@lem5136593) (@lem5136592 _67055 s)). Qed.
Lemma lem5136595 (_67055 : real) (b : real) : (real_le _67055 b) = (real_le _67055 b).
Proof. exact (eq_refl (real_le _67055 b)). Qed.
Lemma lem5136596 (s : real -> Prop) (_67055 : real) (b : real) : (term311 s _67055 b) = (term63 s _67055 b).
Proof. exact (MK_COMB (@lem5136594 _67055 s) (@lem5136595 _67055 b)). Qed.
Lemma lem5136597 (s : real -> Prop) (_67055 : real) (b : real) : (term308 b _67055 s) = (term63 s _67055 b).
Proof. exact (TRANS (@lem5136589 s _67055 b) (@lem5136596 s _67055 b)). Qed.
Lemma lem5136600 (_67055 : real) (s : real -> Prop) (b : real) (h1 : term52 s b) : term63 s _67055 b.
Proof. exact (EQ_MP (@lem5136597 s _67055 b) (@lem5136586 _67055 s b h1)). Qed.
Lemma lem5136601 (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term52 s b) : term315 s x' b.
Proof. exact (@lem5136600 (x' b) s b h1). Qed.
Lemma lem5136604 (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term170 s x') (h2 : term52 s b) : term316 x' b.
Proof. exact (@lem5136601 x' s b h2 (@lem5136557 b s x' h1)). Qed.
Lemma lem5136605 (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term170 s x') (h2 : term52 s b) : term317 x' b.
Proof. exact (fun h0 : term293 x' b => @lem5136604 x' s b h1 h2). Qed.
Lemma lem5136607 (p : Prop) : (term301 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5136608 (x' : real -> real) (b : real) : (term317 x' b) = (term316 x' b).
Proof. exact (@lem5136607 (term316 x' b)). Qed.
Lemma lem5136609 (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term170 s x') (h2 : term52 s b) : term316 x' b.
Proof. exact (EQ_MP (@lem5136608 x' b) (@lem5136605 x' s b h1 h2)). Qed.
Lemma lem5136612 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5136614 (x' : real -> real) (_67059 : real) : (term293 x' _67059) = (term318 x' _67059).
Proof. exact (@lem5136612 (term316 x' _67059)). Qed.
Lemma lem5136617 (_67059 : real) (s : real -> Prop) (x' : real -> real) (h1 : term170 s x') : term318 x' _67059.
Proof. exact (EQ_MP (@lem5136614 x' _67059) (@lem5136400 _67059 s x' h1)). Qed.
Lemma lem5136618 (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term170 s x') : term318 x' b.
Proof. exact (@lem5136617 b s x' h1). Qed.
Lemma lem5136621 (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term170 s x') (h2 : term52 s b) : False.
Proof. exact (@lem5136618 b s x' h1 (@lem5136609 x' s b h1 h2)). Qed.
Lemma lem5136622 (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term170 s x') (h2 : term52 s b) : term304.
Proof. exact (fun h0 : ~ False => @lem5136621 x' s b h1 h2). Qed.
Lemma lem5136624 (p : Prop) : (term301 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5136625 : term304 = False.
Proof. exact (@lem5136624 False). Qed.
Lemma lem5136626 (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term170 s x') (h2 : term52 s b) : False.
Proof. exact (EQ_MP (@lem5136625) (@lem5136622 x' s b h1 h2)). Qed.
Lemma lem5136627 (s : real -> Prop) (x : type1023) (h1 : term126 s) (h2 : term51 s) (h3 : term285 x) : (term51 s) = False.
Proof. exact (prop_ext (fun h4 : term51 s => @lem5136491 s x h1 h2 h3) (fun h4 : False => @lem5136356 s h2)). Qed.
Lemma lem5136628 (s : real -> Prop) (x : type1023) (h1 : term126 s) (h2 : term51 s) (h3 : term285 x) : False.
Proof. exact (EQ_MP (@lem5136627 s x h1 h2 h3) (@lem5136356 s h2)). Qed.
Lemma lem5136629 (s : real -> Prop) (x : type1023) (h1 : term126 s) (h2 : term51 s) (h3 : term285 x) : (term51 s) = False.
Proof. exact (prop_ext (fun h4 : term51 s => @lem5136628 s x h1 h2 h3) (fun h4 : False => @lem5136164 s h2)). Qed.
Lemma lem5136630 (s : real -> Prop) (x : type1023) (h1 : term126 s) (h2 : term51 s) (h3 : term285 x) : False.
Proof. exact (EQ_MP (@lem5136629 s x h1 h2 h3) (@lem5136164 s h2)). Qed.
Lemma lem5136631 (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term170 s x') (h2 : term52 s b) : (term170 s x') = False.
Proof. exact (prop_ext (fun h3 : term170 s x' => @lem5136626 x' s b h1 h2) (fun h3 : False => @lem5136322 s x' h1)). Qed.
Lemma lem5136632 (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term170 s x') (h2 : term52 s b) : False.
Proof. exact (EQ_MP (@lem5136631 x' s b h1 h2) (@lem5136322 s x' h1)). Qed.
Lemma lem5136633 (s : real -> Prop) (x : type1023) (h1 : term126 s) (h2 : term51 s) (h3 : term285 x) : (term126 s) = False.
Proof. exact (prop_ext (fun h4 : term126 s => @lem5136630 s x h1 h2 h3) (fun h4 : False => @lem5136239 s h1)). Qed.
Lemma lem5136634 (s : real -> Prop) (x : type1023) (h1 : term126 s) (h2 : term51 s) (h3 : term285 x) : False.
Proof. exact (EQ_MP (@lem5136633 s x h1 h2 h3) (@lem5136239 s h1)). Qed.
Lemma lem5136635 (s : real -> Prop) (x : type1023) (h1 : term126 s) (h2 : term51 s) (h3 : term285 x) : (term51 s) = False.
Proof. exact (prop_ext (fun h4 : term51 s => @lem5136634 s x h1 h2 h3) (fun h4 : False => @lem5136164 s h2)). Qed.
Lemma lem5136636 (s : real -> Prop) (x : type1023) (h1 : term126 s) (h2 : term51 s) (h3 : term285 x) : False.
Proof. exact (EQ_MP (@lem5136635 s x h1 h2 h3) (@lem5136164 s h2)). Qed.
Lemma lem5136637 (b : real) (x : type1023) (s : real -> Prop) (x' : real -> real) (h1 : term52 s b) (h2 : term51 s) (h3 : term285 x) (h4 : term187 s x') : False.
Proof. exact (or_elim (@lem5136156 s x' h4) (fun h0 : term126 s => @lem5136636 s x h0 h2 h3) (fun h0 : term170 s x' => @lem5136632 x' s b h0 h1)). Qed.
Lemma lem5136638 (b : real) (x : type1023) (s : real -> Prop) (x' : real -> real) (h1 : term52 s b) (h2 : term51 s) (h3 : term285 x) (h4 : term187 s x') : (term187 s x') = False.
Proof. exact (prop_ext (fun h5 : term187 s x' => @lem5136637 b x s x' h1 h2 h3 h4) (fun h5 : False => @lem5136156 s x' h4)). Qed.
Lemma lem5136639 (b : real) (x : type1023) (s : real -> Prop) (x' : real -> real) (h1 : term52 s b) (h2 : term51 s) (h3 : term285 x) (h4 : term187 s x') : False.
Proof. exact (EQ_MP (@lem5136638 b x s x' h1 h2 h3 h4) (@lem5136156 s x' h4)). Qed.
Lemma lem5136640 (b : real) (x : type1023) (s : real -> Prop) (x' : real -> real) (h1 : term52 s b) (h2 : term51 s) (h3 : term285 x) (h4 : term187 s x') : (term285 x) = False.
Proof. exact (prop_ext (fun h5 : term285 x => @lem5136639 b x s x' h1 h2 h3 h4) (fun h5 : False => @lem5136120 x h3)). Qed.
Lemma lem5136641 (b : real) (x : type1023) (s : real -> Prop) (x' : real -> real) (h1 : term52 s b) (h2 : term51 s) (h3 : term285 x) (h4 : term187 s x') : False.
Proof. exact (EQ_MP (@lem5136640 b x s x' h1 h2 h3 h4) (@lem5136120 x h3)). Qed.
Lemma lem5136642 (b : real) (x : type1023) (s : real -> Prop) (x' : real -> real) (h1 : term52 s b) (h2 : term51 s) (h3 : term285 x) (h4 : term187 s x') : (term51 s) = False.
Proof. exact (prop_ext (fun h5 : term51 s => @lem5136641 b x s x' h1 h2 h3 h4) (fun h5 : False => @lem5136056 s h2)). Qed.
Lemma lem5136643 (b : real) (x : type1023) (s : real -> Prop) (x' : real -> real) (h1 : term52 s b) (h2 : term51 s) (h3 : term285 x) (h4 : term187 s x') : False.
Proof. exact (EQ_MP (@lem5136642 b x s x' h1 h2 h3 h4) (@lem5136056 s h2)). Qed.
Lemma lem5136644 (b : real) (s : real -> Prop) (x : type1023) (h1 : term52 s b) (h2 : term90 s) (h3 : term51 s) (h4 : term285 x) : False.
Proof. exact (ex_elim (@lem5135792 s h2) (fun x' : real -> real => fun h0 : term189 s x' => @lem5136643 b x s x' h1 h3 h4 h0)). Qed.
Lemma lem5136645 (b : real) (s : real -> Prop) (h1 : term91) (h2 : term52 s b) (h3 : term90 s) (h4 : term51 s) : False.
Proof. exact (ex_elim (@lem5136046 h1) (fun x : type1023 => fun h0 : term287 x => @lem5136644 b s x h2 h3 h4 h0)). Qed.
Lemma lem5136646 (b : real) (s : real -> Prop) (h1 : term91) (h2 : term52 s b) (h3 : term90 s) (h4 : term51 s) : (term51 s) = False.
Proof. exact (prop_ext (fun h5 : term51 s => @lem5136645 b s h1 h2 h3 h4) (fun h5 : False => @lem5135573 s h4)). Qed.
Lemma lem5136647 (b : real) (s : real -> Prop) (h1 : term91) (h2 : term52 s b) (h3 : term90 s) (h4 : term51 s) : False.
Proof. exact (EQ_MP (@lem5136646 b s h1 h2 h3 h4) (@lem5135573 s h4)). Qed.
Lemma lem5136648 (b : real) (s : real -> Prop) (h1 : term52 s b) (h2 : term90 s) (h3 : term51 s) : term96.
Proof. exact (fun h0 : term91 => @lem5136647 b s h0 h1 h2 h3). Qed.
Lemma lem5136649 : term96 = term97.
Proof. exact (@lem69 term91). Qed.
Lemma lem5136650 (b : real) (s : real -> Prop) (h1 : term52 s b) (h2 : term90 s) (h3 : term51 s) : term97.
Proof. exact (EQ_MP (@lem5136649) (@lem5136648 b s h1 h2 h3)). Qed.
Lemma lem5136651 (b : real) (s : real -> Prop) (h1 : term52 s b) (h2 : term51 s) : term100 s.
Proof. exact (fun h0 : term90 s => @lem5136650 b s h1 h0 h2). Qed.
Lemma lem5136652 (b : real) (s : real -> Prop) (h1 : term51 s) : term102 b s.
Proof. exact (fun h0 : term52 s b => @lem5136651 b s h0 h1). Qed.
Lemma lem5136653 (b : real) (s : real -> Prop) : term104 b s.
Proof. exact (fun h0 : term51 s => @lem5136652 b s h0). Qed.
Lemma lem5136658 (s : real -> Prop) : term108 s.
Proof. exact (fun b : real => @lem5136653 b s). Qed.
Lemma lem5136663 : term112.
Proof. exact (fun s : real -> Prop => @lem5136658 s). Qed.
Lemma lem5136664 : term111.
Proof. exact (EQ_MP (@lem5135563) (@lem5136663)). Qed.
Lemma lem5136665 (s : real -> Prop) : term319 s.
Proof. exact (@lem5136664 s). Qed.
Lemma lem5136666 (s : real -> Prop) : (term319 s) = (term107 s).
Proof. exact (eq_refl (term319 s)). Qed.
Lemma lem5136667 (s : real -> Prop) : term107 s.
Proof. exact (EQ_MP (@lem5136666 s) (@lem5136665 s)). Qed.
Lemma lem5136668 (s : real -> Prop) (b : real) : term320 s b.
Proof. exact (@lem5136667 s b). Qed.
Lemma lem5136669 (b : real) (s : real -> Prop) : (term320 s b) = (term92 b s).
Proof. exact (eq_refl (term320 s b)). Qed.
Lemma lem5136670 (b : real) (s : real -> Prop) : term92 b s.
Proof. exact (EQ_MP (@lem5136669 b s) (@lem5136668 s b)). Qed.
Lemma lem5136672 (b : real) (s : real -> Prop) : term92 b s.
Proof. exact (@lem5135361 b s (@lem5136670 b s)). Qed.
Lemma lem5136673 (b : real) (s : real -> Prop) (h1 : term51 s) : term101 b s.
Proof. exact (@lem5136672 b s (@lem5135283 s h1)). Qed.
Lemma lem5136674 (b : real) (s : real -> Prop) (h1 : term52 s b) (h2 : term51 s) : term99 s.
Proof. exact (@lem5136673 b s h2 (@lem5135284 s b h1)). Qed.
Lemma lem5136675 (b : real) (s : real -> Prop) (h1 : term52 s b) (h2 : term90 s) (h3 : term51 s) : term96.
Proof. exact (@lem5136674 b s h1 h3 (@lem5135343 s h2)). Qed.
Lemma lem5136676 (b : real) (s : real -> Prop) (h1 : term52 s b) (h2 : term90 s) (h3 : term51 s) : False.
Proof. exact (@lem5136675 b s h1 h2 h3 (@lem5135344)). Qed.
Lemma lem5136677 (b : real) (s : real -> Prop) (h1 : term52 s b) (h2 : term90 s) (h3 : term51 s) : (term90 s) = False.
Proof. exact (prop_ext (fun h4 : term90 s => @lem5136676 b s h1 h2 h3) (fun h4 : False => @lem5135343 s h2)). Qed.
Lemma lem5136678 (b : real) (s : real -> Prop) (h1 : term52 s b) (h2 : term90 s) (h3 : term51 s) : False.
Proof. exact (EQ_MP (@lem5136677 b s h1 h2 h3) (@lem5135343 s h2)). Qed.
Lemma lem5136679 (b : real) (s : real -> Prop) (h1 : term52 s b) (h2 : term51 s) : term89 s.
Proof. exact (fun h0 : term90 s => @lem5136678 b s h1 h0 h2). Qed.
Lemma lem5136680 (b : real) (s : real -> Prop) (h1 : term52 s b) (h2 : term51 s) : term71 s.
Proof. exact (EQ_MP (@lem5135342 s) (@lem5136679 b s h1 h2)). Qed.
Lemma lem5136681 (b : real) (s : real -> Prop) (h1 : term52 s b) (h2 : term51 s) : term42 s.
Proof. exact (@lem5135338 s (@lem5136680 b s h1 h2)). Qed.
Lemma lem5136682 (s : real -> Prop) (h1 : term49 s) : term50 s.
Proof. exact (proj2 (@lem5135281 s h1)). Qed.
Lemma lem5136683 (s : real -> Prop) (h1 : term49 s) : term51 s.
Proof. exact (proj1 (@lem5135281 s h1)). Qed.
Lemma lem5136684 (b : real) (s : real -> Prop) (h1 : term52 s b) (h2 : term51 s) : (term52 s b) = (term42 s).
Proof. exact (prop_ext (fun h3 : term52 s b => @lem5136681 b s h1 h2) (fun h3 : term42 s => @lem5135284 s b h1)). Qed.
Lemma lem5136685 (b : real) (s : real -> Prop) (h1 : term52 s b) (h2 : term51 s) : term42 s.
Proof. exact (EQ_MP (@lem5136684 b s h1 h2) (@lem5135284 s b h1)). Qed.
Lemma lem5136686 (s : real -> Prop) (h1 : term50 s) (h2 : term51 s) : term42 s.
Proof. exact (ex_elim (@lem5135282 s h1) (fun b : real => fun h0 : term68 s b => @lem5136685 b s h0 h2)). Qed.
Lemma lem5136687 (s : real -> Prop) (h1 : term50 s) (h2 : term51 s) : (term51 s) = (term42 s).
Proof. exact (prop_ext (fun h3 : term51 s => @lem5136686 s h1 h2) (fun h3 : term42 s => @lem5135283 s h2)). Qed.
Lemma lem5136688 (s : real -> Prop) (h1 : term50 s) (h2 : term51 s) : term42 s.
Proof. exact (EQ_MP (@lem5136687 s h1 h2) (@lem5135283 s h2)). Qed.
Lemma lem5136689 (s : real -> Prop) (h1 : term51 s) (h2 : term49 s) : (term50 s) = (term42 s).
Proof. exact (prop_ext (fun h3 : term50 s => @lem5136688 s h3 h1) (fun h3 : term42 s => @lem5136682 s h2)). Qed.
Lemma lem5136690 (s : real -> Prop) (h1 : term51 s) (h2 : term49 s) : term42 s.
Proof. exact (EQ_MP (@lem5136689 s h1 h2) (@lem5136682 s h2)). Qed.
Lemma lem5136691 (s : real -> Prop) (h1 : term49 s) : (term51 s) = (term42 s).
Proof. exact (prop_ext (fun h2 : term51 s => @lem5136690 s h2 h1) (fun h2 : term42 s => @lem5136683 s h1)). Qed.
Lemma lem5136692 (s : real -> Prop) (h1 : term49 s) : term42 s.
Proof. exact (EQ_MP (@lem5136691 s h1) (@lem5136683 s h1)). Qed.
Lemma lem5136693 (s : real -> Prop) : term46 s.
Proof. exact (fun h0 : term49 s => @lem5136692 s h0). Qed.
Lemma lem5136698 : term48.
Proof. exact (fun s : real -> Prop => @lem5136693 s). Qed.
Lemma lem5136699 : term39.
Proof. exact (EQ_MP (@lem5135280) (@lem5136698)). Qed.
Lemma lem5136700 : term38.
Proof. exact (EQ_MP (@lem5135266) (@lem5136699)). Qed.
