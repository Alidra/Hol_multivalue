Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARD_SUBSET_term_abbrevs.
Require Import CARD_UNION_spec.
Require Import DISJ_ACI_spec.
Require Import FINITE_SUBSET_spec.
Require Import INT_POS_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm1842_spec.
Require Import thm1857_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980255_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982755_spec.
Require Import thm1982759_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988332_spec.
Require Import thm1988342_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm2318495_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318604_spec.
Require Import thm2841383_spec.
Require Import thm2841384_spec.
Require Import thm2841407_spec.
Require Import thm2841408_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211701_spec.
Require Import thm3211702_spec.
Require Import thm3211710_spec.
Require Import thm3211711_spec.
Require Import thm3211719_spec.
Require Import thm3211720_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem3900224 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem3900225 {A : Type'} (s : A -> Prop) (h1 : term0 A) : term1 A s.
Proof. exact (@lem3900224 A h1 s). Qed.
Lemma lem3900226 {A : Type'} (s : A -> Prop) : (term1 A s) = (term2 A s).
Proof. exact (eq_refl (term1 A s)). Qed.
Lemma lem3900227 {A : Type'} (s : A -> Prop) (h1 : term0 A) : term2 A s.
Proof. exact (EQ_MP (@lem3900226 A s) (@lem3900225 A s h1)). Qed.
Lemma lem3900228 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term0 A) : term3 A s t.
Proof. exact (@lem3900227 A s h1 t). Qed.
Lemma lem3900229 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term3 A s t) = (term4 A t s).
Proof. exact (eq_refl (term3 A s t)). Qed.
Lemma lem3900230 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term0 A) : term4 A t s.
Proof. exact (EQ_MP (@lem3900229 A t s) (@lem3900228 A s t h1)). Qed.
Lemma lem3900231 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term5 A s t) : term5 A s t.
Proof. exact (h1). Qed.
Lemma lem3900232 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term0 A) (h2 : term5 A s t) : @FINITE A s.
Proof. exact (@lem3900230 A t s h1 (@lem3900231 A s t h2)). Qed.
Lemma lem3900233 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term5 A s t) : term6 A s.
Proof. exact (fun h0 : term0 A => @lem3900232 A s t h0 h1). Qed.
Lemma lem3900234 {A : Type'} (s : A -> Prop) (h1 : term7 A s) : term7 A s.
Proof. exact (h1). Qed.
Lemma lem3900235 {A : Type'} (s : A -> Prop) (h1 : term7 A s) : term6 A s.
Proof. exact (ex_elim (@lem3900234 A s h1) (fun t : A -> Prop => fun h0 : term8 A s t => @lem3900233 A s t h0)). Qed.
Lemma lem3900236 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem3900237 {A : Type'} (s : A -> Prop) (h1 : term0 A) (h2 : term7 A s) : @FINITE A s.
Proof. exact (@lem3900235 A s h2 (@lem3900236 A h1)). Qed.
Lemma lem3900238 {A : Type'} (s : A -> Prop) (h1 : term0 A) : term9 A s.
Proof. exact (fun h0 : term7 A s => @lem3900237 A s h1 h0). Qed.
Lemma lem3900239 {A : Type'} (h1 : term0 A) : term10 A.
Proof. exact (fun s : A -> Prop => @lem3900238 A s h1). Qed.
Lemma lem3900240 {A : Type'} : term11 A.
Proof. exact (fun h0 : term0 A => @lem3900239 A h0). Qed.
Lemma lem3900241 {A : Type'} : term10 A.
Proof. exact (@lem3900240 A (@lem3599924 A)). Qed.
Lemma lem3900242 {A : Type'} (s : A -> Prop) : term12 A s.
Proof. exact (@lem3900241 A s). Qed.
Lemma lem3900243 {A : Type'} (s : A -> Prop) : (term12 A s) = (term9 A s).
Proof. exact (eq_refl (term12 A s)). Qed.
Lemma lem3900245 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem3900246 {A : Type'} (s : A -> Prop) (h1 : term0 A) : term1 A s.
Proof. exact (@lem3900245 A h1 s). Qed.
Lemma lem3900247 {A : Type'} (s : A -> Prop) : (term1 A s) = (term2 A s).
Proof. exact (eq_refl (term1 A s)). Qed.
Lemma lem3900248 {A : Type'} (s : A -> Prop) (h1 : term0 A) : term2 A s.
Proof. exact (EQ_MP (@lem3900247 A s) (@lem3900246 A s h1)). Qed.
Lemma lem3900249 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term0 A) : term3 A s t.
Proof. exact (@lem3900248 A s h1 t). Qed.
Lemma lem3900250 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term3 A s t) = (term4 A t s).
Proof. exact (eq_refl (term3 A s t)). Qed.
Lemma lem3900251 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term0 A) : term4 A t s.
Proof. exact (EQ_MP (@lem3900250 A t s) (@lem3900249 A s t h1)). Qed.
Lemma lem3900252 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term5 A s t) : term5 A s t.
Proof. exact (h1). Qed.
Lemma lem3900253 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term0 A) (h2 : term5 A s t) : @FINITE A s.
Proof. exact (@lem3900251 A t s h1 (@lem3900252 A s t h2)). Qed.
Lemma lem3900254 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term5 A s t) : term6 A s.
Proof. exact (fun h0 : term0 A => @lem3900253 A s t h0 h1). Qed.
Lemma lem3900255 {A : Type'} (s : A -> Prop) (h1 : term7 A s) : term7 A s.
Proof. exact (h1). Qed.
Lemma lem3900256 {A : Type'} (s : A -> Prop) (h1 : term7 A s) : term6 A s.
Proof. exact (ex_elim (@lem3900255 A s h1) (fun t : A -> Prop => fun h0 : term8 A s t => @lem3900254 A s t h0)). Qed.
Lemma lem3900257 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem3900258 {A : Type'} (s : A -> Prop) (h1 : term0 A) (h2 : term7 A s) : @FINITE A s.
Proof. exact (@lem3900256 A s h2 (@lem3900257 A h1)). Qed.
Lemma lem3900259 {A : Type'} (s : A -> Prop) (h1 : term0 A) : term9 A s.
Proof. exact (fun h0 : term7 A s => @lem3900258 A s h1 h0). Qed.
Lemma lem3900260 {A : Type'} (h1 : term0 A) : term10 A.
Proof. exact (fun s : A -> Prop => @lem3900259 A s h1). Qed.
Lemma lem3900261 {A : Type'} : term11 A.
Proof. exact (fun h0 : term0 A => @lem3900260 A h0). Qed.
Lemma lem3900262 {A : Type'} : term10 A.
Proof. exact (@lem3900261 A (@lem3599924 A)). Qed.
Lemma lem3900263 {A : Type'} (s : A -> Prop) : term12 A s.
Proof. exact (@lem3900262 A s). Qed.
Lemma lem3900264 {A : Type'} (s : A -> Prop) : (term12 A s) = (term9 A s).
Proof. exact (eq_refl (term12 A s)). Qed.
Lemma lem3900266 {A : Type'} (h1 : term13 A) : term13 A.
Proof. exact (h1). Qed.
Lemma lem3900267 {A : Type'} (s : A -> Prop) (h1 : term13 A) : term14 A s.
Proof. exact (@lem3900266 A h1 s). Qed.
Lemma lem3900268 {A : Type'} (s : A -> Prop) : (term14 A s) = (term15 A s).
Proof. exact (eq_refl (term14 A s)). Qed.
Lemma lem3900269 {A : Type'} (s : A -> Prop) (h1 : term13 A) : term15 A s.
Proof. exact (EQ_MP (@lem3900268 A s) (@lem3900267 A s h1)). Qed.
Lemma lem3900270 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term13 A) : term16 A s t.
Proof. exact (@lem3900269 A s h1 t). Qed.
Lemma lem3900271 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term16 A s t) = (term17 A s t).
Proof. exact (eq_refl (term16 A s t)). Qed.
Lemma lem3900272 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term13 A) : term17 A s t.
Proof. exact (EQ_MP (@lem3900271 A s t) (@lem3900270 A s t h1)). Qed.
Lemma lem3900273 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term18 A s t) : term18 A s t.
Proof. exact (h1). Qed.
Lemma lem3900274 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term13 A) (h2 : term18 A s t) : (term19 A s t) = (term20 A s t).
Proof. exact (@lem3900272 A s t h1 (@lem3900273 A s t h2)). Qed.
Lemma lem3900275 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term18 A s t) : term21 A s t.
Proof. exact (fun h0 : term13 A => @lem3900274 A s t h0 h1). Qed.
Lemma lem3900276 {A : Type'} (h1 : term13 A) : term13 A.
Proof. exact (h1). Qed.
Lemma lem3900277 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term13 A) (h2 : term18 A s t) : (term19 A s t) = (term20 A s t).
Proof. exact (@lem3900275 A s t h2 (@lem3900276 A h1)). Qed.
Lemma lem3900278 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term13 A) : term17 A s t.
Proof. exact (fun h0 : term18 A s t => @lem3900277 A s t h1 h0). Qed.
Lemma lem3900279 {A : Type'} (s : A -> Prop) (h1 : term13 A) : term15 A s.
Proof. exact (fun t : A -> Prop => @lem3900278 A s t h1). Qed.
Lemma lem3900280 {A : Type'} (h1 : term13 A) : term13 A.
Proof. exact (fun s : A -> Prop => @lem3900279 A s h1). Qed.
Lemma lem3900281 {A : Type'} : term22 A.
Proof. exact (fun h0 : term13 A => @lem3900280 A h0). Qed.
Lemma lem3900282 {A : Type'} : term13 A.
Proof. exact (@lem3900281 A (@lem3843862 A)). Qed.
Lemma lem3900283 {A : Type'} (s : A -> Prop) : term14 A s.
Proof. exact (@lem3900282 A s). Qed.
Lemma lem3900284 {A : Type'} (s : A -> Prop) : (term14 A s) = (term15 A s).
Proof. exact (eq_refl (term14 A s)). Qed.
Lemma lem3900285 {A : Type'} (s : A -> Prop) : term15 A s.
Proof. exact (EQ_MP (@lem3900284 A s) (@lem3900283 A s)). Qed.
Lemma lem3900286 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term16 A s t.
Proof. exact (@lem3900285 A s t). Qed.
Lemma lem3900287 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term16 A s t) = (term17 A s t).
Proof. exact (eq_refl (term16 A s t)). Qed.
Lemma lem3900299 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term23 A a b) : term23 A a b.
Proof. exact (h1). Qed.
Lemma lem3900300 {A : Type'} (b : A -> Prop) (h1 : @FINITE A b) : @FINITE A b.
Proof. exact (h1). Qed.
Lemma lem3900301 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @SUBSET A a b) : @SUBSET A a b.
Proof. exact (h1). Qed.
Lemma lem3900302 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : b = (term24 A b a)) : b = (term24 A b a).
Proof. exact (h1). Qed.
Lemma lem3900303 {A : Type'} (a : A -> Prop) : (term25 A a) = (term25 A a).
Proof. exact (eq_refl (term25 A a)). Qed.
Lemma lem3900304 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : b = (term24 A b a)) : (term26 A a b) = (term27 A b a).
Proof. exact (MK_COMB (@lem3900303 A a) (@lem3900302 A b a h1)). Qed.
Lemma lem3900305 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term27 A b a) = (term28 A b a).
Proof. exact (eq_refl (term27 A b a)). Qed.
Lemma lem3900306 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term29 A a b) = (term29 A a b).
Proof. exact (eq_refl (term29 A a b)). Qed.
Lemma lem3900307 {A : Type'} (b : A -> Prop) (a : A -> Prop) : ((term26 A a b) = (term27 A b a)) = ((term26 A a b) = (term28 A b a)).
Proof. exact (MK_COMB (@lem3900306 A a b) (@lem3900305 A b a)). Qed.
Lemma lem3900308 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term26 A a b) = (term30 A a b).
Proof. exact (eq_refl (term26 A a b)). Qed.
Lemma lem3900309 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3900310 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term29 A a b) = (term31 A a b).
Proof. exact (MK_COMB (@lem3900309) (@lem3900308 A a b)). Qed.
Lemma lem3900311 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term28 A b a) = (term28 A b a).
Proof. exact (eq_refl (term28 A b a)). Qed.
Lemma lem3900312 {A : Type'} (b : A -> Prop) (a : A -> Prop) : ((term26 A a b) = (term28 A b a)) = ((term30 A a b) = (term28 A b a)).
Proof. exact (MK_COMB (@lem3900310 A a b) (@lem3900311 A b a)). Qed.
Lemma lem3900313 {A : Type'} (b : A -> Prop) (a : A -> Prop) : ((term26 A a b) = (term27 A b a)) = ((term30 A a b) = (term28 A b a)).
Proof. exact (TRANS (@lem3900307 A b a) (@lem3900312 A b a)). Qed.
Lemma lem3900314 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : b = (term24 A b a)) : (term30 A a b) = (term28 A b a).
Proof. exact (EQ_MP (@lem3900313 A b a) (@lem3900304 A b a h1)). Qed.
Lemma lem3900315 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : b = (term24 A b a)) : (term28 A b a) = (term30 A a b).
Proof. exact (SYM (@lem3900314 A b a h1)). Qed.
Lemma lem3900319 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term32 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3900320 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term32 A s t).
Proof. exact (@lem3900319 A s t). Qed.
Lemma lem3900321 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (@SUBSET A a b) = (term32 A a b).
Proof. exact (@lem3900320 A a b). Qed.
Lemma lem3900328 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3900329 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term33 A a b) = (term34 A a b).
Proof. exact (MK_COMB (@lem3900328) (@lem3900321 A a b)). Qed.
Lemma lem3900333 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term35 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3900334 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term35 A s t).
Proof. exact (@lem3900333 A s t). Qed.
Lemma lem3900335 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (b = (term24 A b a)) = (term36 A b a).
Proof. exact (@lem3900334 A b (term24 A b a)). Qed.
Lemma lem3900344 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term37 A b a) = (term38 A b a).
Proof. exact (MK_COMB (@lem3900329 A a b) (@lem3900335 A b a)). Qed.
Lemma lem3900347 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term38 A b a) = (term37 A b a).
Proof. exact (SYM (@lem3900344 A b a)). Qed.
Lemma lem3900357 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3900358 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3900357 A P x). Qed.
Lemma lem3900359 {A : Type'} (a : A -> Prop) (x : A) : (@IN A x a) = (a x).
Proof. exact (@lem3900358 A a x). Qed.
Lemma lem3900360 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3900361 {A : Type'} (a : A -> Prop) (x : A) : (term39 A x a) = (term40 A a x).
Proof. exact (MK_COMB (@lem3900360) (@lem3900359 A a x)). Qed.
Lemma lem3900363 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3900364 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3900363 A P x). Qed.
Lemma lem3900365 {A : Type'} (b : A -> Prop) (x : A) : (@IN A x b) = (b x).
Proof. exact (@lem3900364 A b x). Qed.
Lemma lem3900366 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) : (term41 A a x b) = (term42 A a b x).
Proof. exact (MK_COMB (@lem3900361 A a x) (@lem3900365 A b x)). Qed.
Lemma lem3900369 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term43 A a b) = (term44 A a b).
Proof. exact (fun_ext (fun x : A => @lem3900366 A a b x)). Qed.
Lemma lem3900370 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3900371 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term32 A a b) = (term45 A a b).
Proof. exact (MK_COMB (@lem3900370 A) (@lem3900369 A a b)). Qed.
Lemma lem3900376 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3900377 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term34 A a b) = (term46 A a b).
Proof. exact (MK_COMB (@lem3900376) (@lem3900371 A a b)). Qed.
Lemma lem3900385 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3900386 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3900385 A P x). Qed.
Lemma lem3900387 {A : Type'} (b : A -> Prop) (x : A) : (@IN A x b) = (b x).
Proof. exact (@lem3900386 A b x). Qed.
Lemma lem3900388 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3900389 {A : Type'} (b : A -> Prop) (x : A) : (term47 A x b) = (term48 A b x).
Proof. exact (MK_COMB (@lem3900388) (@lem3900387 A b x)). Qed.
Lemma lem3900391 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term49 A x s t) = (term50 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3900392 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term49 A x s t) = (term50 A s x t).
Proof. exact (@lem3900391 A s x t). Qed.
Lemma lem3900393 {A : Type'} (x : A) (b : A -> Prop) (a : A -> Prop) : (term51 A x b a) = (term52 A x b a).
Proof. exact (@lem3900392 A a x (@DIFF A b a)). Qed.
Lemma lem3900397 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3900398 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3900397 A P x). Qed.
Lemma lem3900399 {A : Type'} (a : A -> Prop) (x : A) : (@IN A x a) = (a x).
Proof. exact (@lem3900398 A a x). Qed.
Lemma lem3900400 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3900401 {A : Type'} (a : A -> Prop) (x : A) : (term53 A x a) = (term54 A a x).
Proof. exact (MK_COMB (@lem3900400) (@lem3900399 A a x)). Qed.
Lemma lem3900403 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term55 A x s t) = (term56 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem3900404 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term55 A x s t) = (term56 A s x t).
Proof. exact (@lem3900403 A s x t). Qed.
Lemma lem3900405 {A : Type'} (b : A -> Prop) (x : A) (a : A -> Prop) : (term55 A x b a) = (term56 A b x a).
Proof. exact (@lem3900404 A b x a). Qed.
Lemma lem3900409 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3900410 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3900409 A P x). Qed.
Lemma lem3900411 {A : Type'} (b : A -> Prop) (x : A) : (@IN A x b) = (b x).
Proof. exact (@lem3900410 A b x). Qed.
Lemma lem3900412 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3900413 {A : Type'} (b : A -> Prop) (x : A) : (term57 A x b) = (term58 A b x).
Proof. exact (MK_COMB (@lem3900412) (@lem3900411 A b x)). Qed.
Lemma lem3900415 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3900416 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3900415 A P x). Qed.
Lemma lem3900417 {A : Type'} (a : A -> Prop) (x : A) : (@IN A x a) = (a x).
Proof. exact (@lem3900416 A a x). Qed.
Lemma lem3900418 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3900419 {A : Type'} (a : A -> Prop) (x : A) : (term59 A x a) = (term60 A a x).
Proof. exact (MK_COMB (@lem3900418) (@lem3900417 A a x)). Qed.
Lemma lem3900420 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term56 A b x a) = (term61 A b a x).
Proof. exact (MK_COMB (@lem3900413 A b x) (@lem3900419 A a x)). Qed.
Lemma lem3900423 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term55 A x b a) = (term61 A b a x).
Proof. exact (TRANS (@lem3900405 A b x a) (@lem3900420 A b a x)). Qed.
Lemma lem3900424 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term52 A x b a) = (term62 A b a x).
Proof. exact (MK_COMB (@lem3900401 A a x) (@lem3900423 A b a x)). Qed.
Lemma lem3900427 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term51 A x b a) = (term62 A b a x).
Proof. exact (TRANS (@lem3900393 A x b a) (@lem3900424 A b a x)). Qed.
Lemma lem3900428 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : ((@IN A x b) = (term51 A x b a)) = ((b x) = (term62 A b a x)).
Proof. exact (MK_COMB (@lem3900389 A b x) (@lem3900427 A b a x)). Qed.
Lemma lem3900431 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term63 A b a) = (term64 A b a).
Proof. exact (fun_ext (fun x : A => @lem3900428 A b a x)). Qed.
Lemma lem3900432 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3900433 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term36 A b a) = (term65 A b a).
Proof. exact (MK_COMB (@lem3900432 A) (@lem3900431 A b a)). Qed.
Lemma lem3900438 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term38 A b a) = (term66 A b a).
Proof. exact (MK_COMB (@lem3900377 A a b) (@lem3900433 A b a)). Qed.
Lemma lem3900441 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term66 A b a) = (term38 A b a).
Proof. exact (SYM (@lem3900438 A b a)). Qed.
Lemma lem3900443 (p : Prop) : p = (term67 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3900444 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term66 A b a) = (term68 A b a).
Proof. exact (@lem3900443 (term66 A b a)). Qed.
Lemma lem3900445 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term68 A b a) = (term66 A b a).
Proof. exact (SYM (@lem3900444 A b a)). Qed.
Lemma lem3900446 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term69 A b a) : term69 A b a.
Proof. exact (h1). Qed.
Lemma lem3900449 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term68 A b a) : term68 A b a.
Proof. exact (h1). Qed.
Lemma lem3900450 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term70 A b a.
Proof. exact (fun h0 : term68 A b a => @lem3900449 A b a h0). Qed.
Lemma lem3900451 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term70 A b a) : term70 A b a.
Proof. exact (h1). Qed.
Lemma lem3900452 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term68 A b a) : term68 A b a.
Proof. exact (h1). Qed.
Lemma lem3900453 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term68 A b a) (h2 : term70 A b a) : term68 A b a.
Proof. exact (@lem3900451 A b a h2 (@lem3900452 A b a h1)). Qed.
Lemma lem3900454 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term68 A b a) : term71 A b a.
Proof. exact (fun h0 : term70 A b a => @lem3900453 A b a h1 h0). Qed.
Lemma lem3900455 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term70 A b a) : term70 A b a.
Proof. exact (h1). Qed.
Lemma lem3900456 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term68 A b a) (h2 : term70 A b a) : term68 A b a.
Proof. exact (@lem3900454 A b a h1 (@lem3900455 A b a h2)). Qed.
Lemma lem3900457 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term70 A b a) : term70 A b a.
Proof. exact (fun h0 : term68 A b a => @lem3900456 A b a h0 h1). Qed.
Lemma lem3900458 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term72 A b a.
Proof. exact (fun h0 : term70 A b a => @lem3900457 A b a h0). Qed.
Lemma lem3900461 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term70 A b a.
Proof. exact (@lem3900458 A b a (@lem3900450 A b a)). Qed.
Lemma lem3900462 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term70 A b a.
Proof. exact (@lem3900461 A b a). Qed.
Lemma lem3900472 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3900473 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term68 A b a) = (term73 A b a).
Proof. exact (@lem3900472 (term69 A b a)). Qed.
Lemma lem3900475 (t : Prop) : (term74 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3900476 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term73 A b a) = (term66 A b a).
Proof. exact (@lem3900475 (term66 A b a)). Qed.
Lemma lem3900479 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term68 A b a) = (term66 A b a).
Proof. exact (TRANS (@lem3900473 A b a) (@lem3900476 A b a)). Qed.
Lemma lem3900494 {A : Type'} (a : A -> Prop) : (term75 A a) = (term76 A a).
Proof. exact (fun_ext (fun b : A -> Prop => @lem3900479 A b a)). Qed.
Lemma lem3900495 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3900496 {A : Type'} (a : A -> Prop) : (term77 A a) = (term78 A a).
Proof. exact (MK_COMB (@lem3900495 A) (@lem3900494 A a)). Qed.
Lemma lem3900501 {A : Type'} : (term79 A) = (term80 A).
Proof. exact (fun_ext (fun a : A -> Prop => @lem3900496 A a)). Qed.
Lemma lem3900502 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3900511 {A : Type'} : (term81 A) = (term82 A).
Proof. exact (MK_COMB (@lem3900502 A) (@lem3900501 A)). Qed.
Lemma lem3900526 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : ((b x) = (term62 A b a x)) = ((b x) = (term62 A b a x)).
Proof. exact (eq_refl ((b x) = (term62 A b a x))). Qed.
Lemma lem3900527 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term64 A b a) = (term64 A b a).
Proof. exact (fun_ext (fun x : A => @lem3900526 A b a x)). Qed.
Lemma lem3900528 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3900529 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term65 A b a) = (term65 A b a).
Proof. exact (MK_COMB (@lem3900528 A) (@lem3900527 A b a)). Qed.
Lemma lem3900534 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) : (term42 A a b x) = (term42 A a b x).
Proof. exact (eq_refl (term42 A a b x)). Qed.
Lemma lem3900535 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term44 A a b) = (term44 A a b).
Proof. exact (fun_ext (fun x : A => @lem3900534 A a b x)). Qed.
Lemma lem3900536 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3900537 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term45 A a b) = (term45 A a b).
Proof. exact (MK_COMB (@lem3900536 A) (@lem3900535 A a b)). Qed.
Lemma lem3900538 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3900539 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term46 A a b) = (term46 A a b).
Proof. exact (MK_COMB (@lem3900538) (@lem3900537 A a b)). Qed.
Lemma lem3900540 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term66 A b a) = (term66 A b a).
Proof. exact (MK_COMB (@lem3900539 A a b) (@lem3900529 A b a)). Qed.
Lemma lem3900541 {A : Type'} (a : A -> Prop) : (term76 A a) = (term76 A a).
Proof. exact (fun_ext (fun b : A -> Prop => @lem3900540 A b a)). Qed.
Lemma lem3900542 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3900543 {A : Type'} (a : A -> Prop) : (term78 A a) = (term78 A a).
Proof. exact (MK_COMB (@lem3900542 A) (@lem3900541 A a)). Qed.
Lemma lem3900544 {A : Type'} : (term80 A) = (term80 A).
Proof. exact (fun_ext (fun a : A -> Prop => @lem3900543 A a)). Qed.
Lemma lem3900545 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3900546 {A : Type'} : (term82 A) = (term82 A).
Proof. exact (MK_COMB (@lem3900545 A) (@lem3900544 A)). Qed.
Lemma lem3900581 {A : Type'} : (term81 A) = (term82 A).
Proof. exact (TRANS (@lem3900511 A) (@lem3900546 A)). Qed.
Lemma lem3900582 {A : Type'} : (term82 A) = (term81 A).
Proof. exact (SYM (@lem3900581 A)). Qed.
Lemma lem3900583 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term45 A a b) : term45 A a b.
Proof. exact (h1). Qed.
Lemma lem3900585 (p : Prop) : p = (term67 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3900586 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : ((b x) = (term62 A b a x)) = (term83 A b a x).
Proof. exact (@lem3900585 ((b x) = (term62 A b a x))). Qed.
Lemma lem3900587 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term83 A b a x) = ((b x) = (term62 A b a x)).
Proof. exact (SYM (@lem3900586 A b a x)). Qed.
Lemma lem3900588 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term84 A b a x) : term84 A b a x.
Proof. exact (h1). Qed.
Lemma lem3900595 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) : (term42 A a b x) = (term85 A a b x).
Proof. exact (@lem17265 (a x) (b x)). Qed.
Lemma lem3900596 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term44 A a b) = (term86 A a b).
Proof. exact (fun_ext (fun x : A => @lem3900595 A a b x)). Qed.
Lemma lem3900597 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3900634 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term45 A a b) = (term87 A a b).
Proof. exact (MK_COMB (@lem3900597 A) (@lem3900596 A a b)). Qed.
Lemma lem3900635 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term45 A a b) : term87 A a b.
Proof. exact (EQ_MP (@lem3900634 A a b) (@lem3900583 A a b h1)). Qed.
Lemma lem3900645 {A : Type'} (a : A -> Prop) (x : A) : (term88 A a x) = (a x).
Proof. exact (@lem16933 (a x)). Qed.
Lemma lem3900647 {A : Type'} (b : A -> Prop) (x : A) : (term89 A b x) = (term89 A b x).
Proof. exact (eq_refl (term89 A b x)). Qed.
Lemma lem3900648 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term90 A b a x) = (term85 A b a x).
Proof. exact (MK_COMB (@lem3900647 A b x) (@lem3900645 A a x)). Qed.
Lemma lem3900649 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term91 A b a x) = (term90 A b a x).
Proof. exact (@lem17045 (b x) (term60 A a x)). Qed.
Lemma lem3900650 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term91 A b a x) = (term85 A b a x).
Proof. exact (TRANS (@lem3900649 A b a x) (@lem3900648 A b a x)). Qed.
Lemma lem3900655 {A : Type'} (a : A -> Prop) (x : A) : (term92 A a x) = (term92 A a x).
Proof. exact (eq_refl (term92 A a x)). Qed.
Lemma lem3900656 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term93 A b a x) = (term94 A b a x).
Proof. exact (MK_COMB (@lem3900655 A a x) (@lem3900650 A b a x)). Qed.
Lemma lem3900657 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term95 A b a x) = (term93 A b a x).
Proof. exact (@lem17160 (a x) (term61 A b a x)). Qed.
Lemma lem3900658 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term95 A b a x) = (term94 A b a x).
Proof. exact (TRANS (@lem3900657 A b a x) (@lem3900656 A b a x)). Qed.
Lemma lem3900664 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term96 A b a x) = (term96 A b a x).
Proof. exact (eq_refl (term96 A b a x)). Qed.
Lemma lem3900666 {A : Type'} (b : A -> Prop) (x : A) : (term58 A b x) = (term58 A b x).
Proof. exact (eq_refl (term58 A b x)). Qed.
Lemma lem3900667 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term97 A b a x) = (term98 A b a x).
Proof. exact (MK_COMB (@lem3900666 A b x) (@lem3900658 A b a x)). Qed.
Lemma lem3900668 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3900669 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term99 A b a x) = (term100 A b a x).
Proof. exact (MK_COMB (@lem3900668) (@lem3900667 A b a x)). Qed.
Lemma lem3900670 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term101 A b a x) = (term102 A b a x).
Proof. exact (MK_COMB (@lem3900669 A b a x) (@lem3900664 A b a x)). Qed.
Lemma lem3900671 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term84 A b a x) = (term101 A b a x).
Proof. exact (@lem17646 (b x) (term62 A b a x)). Qed.
Lemma lem3900676 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term84 A b a x) = (term102 A b a x).
Proof. exact (TRANS (@lem3900671 A b a x) (@lem3900670 A b a x)). Qed.
Lemma lem3900688 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) : (term85 A a b x) = (term85 A a b x).
Proof. exact (eq_refl (term85 A a b x)). Qed.
Lemma lem3900689 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term86 A a b) = (term86 A a b).
Proof. exact (fun_ext (fun x : A => @lem3900688 A a b x)). Qed.
Lemma lem3900690 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3900691 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term87 A a b) = (term87 A a b).
Proof. exact (MK_COMB (@lem3900690 A) (@lem3900689 A a b)). Qed.
Lemma lem3900692 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term45 A a b) : term87 A a b.
Proof. exact (EQ_MP (@lem3900691 A a b) (@lem3900635 A a b h1)). Qed.
Lemma lem3900746 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term84 A b a x) : term102 A b a x.
Proof. exact (EQ_MP (@lem3900676 A b a x) (@lem3900588 A b a x h1)). Qed.
Lemma lem3900747 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term98 A b a x) : term98 A b a x.
Proof. exact (h1). Qed.
Lemma lem3900748 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term96 A b a x) : term96 A b a x.
Proof. exact (h1). Qed.
Lemma lem3900749 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term98 A b a x) : term94 A b a x.
Proof. exact (proj2 (@lem3900747 A b a x h1)). Qed.
Lemma lem3900751 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term98 A b a x) : term85 A b a x.
Proof. exact (proj2 (@lem3900749 A b a x h1)). Qed.
Lemma lem3900755 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term96 A b a x) : term62 A b a x.
Proof. exact (proj2 (@lem3900748 A b a x h1)). Qed.
Lemma lem3900758 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term61 A b a x) : term61 A b a x.
Proof. exact (h1). Qed.
Lemma lem3900785 {A : Type'} (b : A -> Prop) (x : A) (h1 : term60 A b x) : term60 A b x.
Proof. exact (h1). Qed.
Lemma lem3900810 {A : Type'} (a : A -> Prop) (x : A) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem3900818 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) : (term85 A a b x) = (term85 A a b x).
Proof. exact (eq_refl (term85 A a b x)). Qed.
Lemma lem3900819 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term86 A a b) = (term86 A a b).
Proof. exact (fun_ext (fun x : A => @lem3900818 A a b x)). Qed.
Lemma lem3900820 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3900822 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term87 A a b) = (term87 A a b).
Proof. exact (MK_COMB (@lem3900820 A) (@lem3900819 A a b)). Qed.
Lemma lem3900823 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term45 A a b) : term87 A a b.
Proof. exact (EQ_MP (@lem3900822 A a b) (@lem3900692 A a b h1)). Qed.
Lemma lem3900831 {A : Type'} (a : A -> Prop) (x : A) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem3900863 {A : Type'} (_45308 : A) (a : A -> Prop) (b : A -> Prop) (h1 : term45 A a b) : term103 A a b _45308.
Proof. exact (@lem3900823 A a b h1 _45308). Qed.
Lemma lem3900864 {A : Type'} (a : A -> Prop) (b : A -> Prop) (_45308 : A) : (term103 A a b _45308) = (term85 A a b _45308).
Proof. exact (eq_refl (term103 A a b _45308)). Qed.
Lemma lem3900880 {A : Type'} (b : A -> Prop) (x : A) (h1 : term60 A b x) : term60 A b x.
Proof. exact (h1). Qed.
Lemma lem3900890 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term98 A b a x) : term60 A a x.
Proof. exact (proj1 (@lem3900749 A b a x h1)). Qed.
Lemma lem3900892 {A : Type'} (a : A -> Prop) (x : A) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem3900898 {A : Type'} (_45308 : A) (a : A -> Prop) (b : A -> Prop) (h1 : term45 A a b) : term85 A a b _45308.
Proof. exact (EQ_MP (@lem3900864 A a b _45308) (@lem3900863 A _45308 a b h1)). Qed.
Lemma lem3900900 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term96 A b a x) : term60 A b x.
Proof. exact (proj1 (@lem3900748 A b a x h1)). Qed.
Lemma lem3900902 {A : Type'} (a : A -> Prop) (x : A) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem3900910 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term96 A b a x) : term60 A b x.
Proof. exact (proj1 (@lem3900748 A b a x h1)). Qed.
Lemma lem3900916 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term98 A b a x) : b x.
Proof. exact (proj1 (@lem3900747 A b a x h1)). Qed.
Lemma lem3900917 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term98 A b a x) : term104 A b x.
Proof. exact (fun h0 : term60 A b x => @lem3900916 A b a x h1). Qed.
Lemma lem3900919 (p : Prop) : (term105 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3900920 {A : Type'} (b : A -> Prop) (x : A) : (term104 A b x) = (b x).
Proof. exact (@lem3900919 (b x)). Qed.
Lemma lem3900921 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term98 A b a x) : b x.
Proof. exact (EQ_MP (@lem3900920 A b x) (@lem3900917 A b a x h1)). Qed.
Lemma lem3900924 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3900926 {A : Type'} (b : A -> Prop) (x : A) : (term60 A b x) = (term106 A b x).
Proof. exact (@lem3900924 (b x)). Qed.
Lemma lem3900929 {A : Type'} (b : A -> Prop) (x : A) (h1 : term60 A b x) : term106 A b x.
Proof. exact (EQ_MP (@lem3900926 A b x) (@lem3900880 A b x h1)). Qed.
Lemma lem3900932 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term60 A b x) (h2 : term98 A b a x) : False.
Proof. exact (@lem3900929 A b x h1 (@lem3900921 A b a x h2)). Qed.
Lemma lem3900933 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term60 A b x) (h2 : term98 A b a x) : term107.
Proof. exact (fun h0 : ~ False => @lem3900932 A b a x h1 h2). Qed.
Lemma lem3900935 (p : Prop) : (term105 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3900936 : term107 = False.
Proof. exact (@lem3900935 False). Qed.
Lemma lem3900937 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term60 A b x) (h2 : term98 A b a x) : False.
Proof. exact (EQ_MP (@lem3900936) (@lem3900933 A b a x h1 h2)). Qed.
Lemma lem3900939 {A : Type'} (a : A -> Prop) (x : A) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem3900940 {A : Type'} (a : A -> Prop) (x : A) (h1 : a x) : term104 A a x.
Proof. exact (fun h0 : term60 A a x => @lem3900939 A a x h1). Qed.
Lemma lem3900942 (p : Prop) : (term105 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3900943 {A : Type'} (a : A -> Prop) (x : A) : (term104 A a x) = (a x).
Proof. exact (@lem3900942 (a x)). Qed.
Lemma lem3900944 {A : Type'} (a : A -> Prop) (x : A) (h1 : a x) : a x.
Proof. exact (EQ_MP (@lem3900943 A a x) (@lem3900940 A a x h1)). Qed.
Lemma lem3900947 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3900949 {A : Type'} (a : A -> Prop) (x : A) : (term60 A a x) = (term106 A a x).
Proof. exact (@lem3900947 (a x)). Qed.
Lemma lem3900952 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term98 A b a x) : term106 A a x.
Proof. exact (EQ_MP (@lem3900949 A a x) (@lem3900890 A b a x h1)). Qed.
Lemma lem3900955 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : a x) (h2 : term98 A b a x) : False.
Proof. exact (@lem3900952 A b a x h2 (@lem3900944 A a x h1)). Qed.
Lemma lem3900956 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : a x) (h2 : term98 A b a x) : term107.
Proof. exact (fun h0 : ~ False => @lem3900955 A b a x h1 h2). Qed.
Lemma lem3900958 (p : Prop) : (term105 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3900959 : term107 = False.
Proof. exact (@lem3900958 False). Qed.
Lemma lem3900960 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : a x) (h2 : term98 A b a x) : False.
Proof. exact (EQ_MP (@lem3900959) (@lem3900956 A b a x h1 h2)). Qed.
Lemma lem3900962 {A : Type'} (a : A -> Prop) (x : A) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem3900963 {A : Type'} (a : A -> Prop) (x : A) (h1 : a x) : term104 A a x.
Proof. exact (fun h0 : term60 A a x => @lem3900962 A a x h1). Qed.
Lemma lem3900965 (p : Prop) : (term105 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3900966 {A : Type'} (a : A -> Prop) (x : A) : (term104 A a x) = (a x).
Proof. exact (@lem3900965 (a x)). Qed.
Lemma lem3900967 {A : Type'} (a : A -> Prop) (x : A) (h1 : a x) : a x.
Proof. exact (EQ_MP (@lem3900966 A a x) (@lem3900963 A a x h1)). Qed.
Lemma lem3900973 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3900974 {A : Type'} (b : A -> Prop) (a : A -> Prop) (_45308 : A) : (term85 A a b _45308) = (term108 A b a _45308).
Proof. exact (@lem3900973 (b _45308) (term60 A a _45308)). Qed.
Lemma lem3900980 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3900981 {A : Type'} (b : A -> Prop) (a : A -> Prop) (_45308 : A) : (term109 A a b _45308) = (term110 A b a _45308).
Proof. exact (MK_COMB (@lem3900980) (@lem3900974 A b a _45308)). Qed.
Lemma lem3900987 {A : Type'} (b : A -> Prop) (a : A -> Prop) (_45308 : A) : (term108 A b a _45308) = (term108 A b a _45308).
Proof. exact (eq_refl (term108 A b a _45308)). Qed.
Lemma lem3900988 {A : Type'} (b : A -> Prop) (a : A -> Prop) (_45308 : A) : ((term85 A a b _45308) = (term108 A b a _45308)) = ((term108 A b a _45308) = (term108 A b a _45308)).
Proof. exact (MK_COMB (@lem3900981 A b a _45308) (@lem3900987 A b a _45308)). Qed.
Lemma lem3900990 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3900991 (x : Prop) : (x = x) = True.
Proof. exact (@lem3900990 Prop x). Qed.
Lemma lem3900992 {A : Type'} (b : A -> Prop) (a : A -> Prop) (_45308 : A) : ((term108 A b a _45308) = (term108 A b a _45308)) = True.
Proof. exact (@lem3900991 (term108 A b a _45308)). Qed.
Lemma lem3900993 {A : Type'} (b : A -> Prop) (a : A -> Prop) (_45308 : A) : ((term85 A a b _45308) = (term108 A b a _45308)) = True.
Proof. exact (TRANS (@lem3900988 A b a _45308) (@lem3900992 A b a _45308)). Qed.
Lemma lem3900994 {A : Type'} (b : A -> Prop) (a : A -> Prop) (_45308 : A) : True = ((term85 A a b _45308) = (term108 A b a _45308)).
Proof. exact (SYM (@lem3900993 A b a _45308)). Qed.
Lemma lem3900995 {A : Type'} (b : A -> Prop) (a : A -> Prop) (_45308 : A) : (term85 A a b _45308) = (term108 A b a _45308).
Proof. exact (EQ_MP (@lem3900994 A b a _45308) (@lem0)). Qed.
Lemma lem3900996 {A : Type'} (_45308 : A) (a : A -> Prop) (b : A -> Prop) (h1 : term45 A a b) : term108 A b a _45308.
Proof. exact (EQ_MP (@lem3900995 A b a _45308) (@lem3900898 A _45308 a b h1)). Qed.
Lemma lem3900998 (b : Prop) (a : Prop) : (a \/ b) = (term111 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3900999 {A : Type'} (a : A -> Prop) (b : A -> Prop) (_45308 : A) : (term108 A b a _45308) = (term112 A a b _45308).
Proof. exact (@lem3900998 (term60 A a _45308) (b _45308)). Qed.
Lemma lem3901001 (a : Prop) : (term74 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3901002 {A : Type'} (a : A -> Prop) (_45308 : A) : (term88 A a _45308) = (a _45308).
Proof. exact (@lem3901001 (a _45308)). Qed.
Lemma lem3901003 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3901004 {A : Type'} (a : A -> Prop) (_45308 : A) : (term113 A a _45308) = (term40 A a _45308).
Proof. exact (MK_COMB (@lem3901003) (@lem3901002 A a _45308)). Qed.
Lemma lem3901005 {A : Type'} (b : A -> Prop) (_45308 : A) : (b _45308) = (b _45308).
Proof. exact (eq_refl (b _45308)). Qed.
Lemma lem3901006 {A : Type'} (a : A -> Prop) (b : A -> Prop) (_45308 : A) : (term112 A a b _45308) = (term42 A a b _45308).
Proof. exact (MK_COMB (@lem3901004 A a _45308) (@lem3901005 A b _45308)). Qed.
Lemma lem3901007 {A : Type'} (a : A -> Prop) (b : A -> Prop) (_45308 : A) : (term108 A b a _45308) = (term42 A a b _45308).
Proof. exact (TRANS (@lem3900999 A a b _45308) (@lem3901006 A a b _45308)). Qed.
Lemma lem3901010 {A : Type'} (_45308 : A) (a : A -> Prop) (b : A -> Prop) (h1 : term45 A a b) : term42 A a b _45308.
Proof. exact (EQ_MP (@lem3901007 A a b _45308) (@lem3900996 A _45308 a b h1)). Qed.
Lemma lem3901011 {A : Type'} (_45308 : A) (a : A -> Prop) (b : A -> Prop) (h1 : term45 A a b) : term42 A a b _45308.
Proof. exact (@lem3901010 A _45308 a b h1). Qed.
Lemma lem3901012 {A : Type'} (x : A) (a : A -> Prop) (b : A -> Prop) (h1 : term45 A a b) : term42 A a b x.
Proof. exact (@lem3901011 A x a b h1). Qed.
Lemma lem3901015 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term45 A a b) (h2 : a x) : b x.
Proof. exact (@lem3901012 A x a b h1 (@lem3900967 A a x h2)). Qed.
Lemma lem3901016 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term45 A a b) (h2 : a x) : term104 A b x.
Proof. exact (fun h0 : term60 A b x => @lem3901015 A b a x h1 h2). Qed.
Lemma lem3901018 (p : Prop) : (term105 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3901019 {A : Type'} (b : A -> Prop) (x : A) : (term104 A b x) = (b x).
Proof. exact (@lem3901018 (b x)). Qed.
Lemma lem3901020 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term45 A a b) (h2 : a x) : b x.
Proof. exact (EQ_MP (@lem3901019 A b x) (@lem3901016 A b a x h1 h2)). Qed.
Lemma lem3901023 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3901025 {A : Type'} (b : A -> Prop) (x : A) : (term60 A b x) = (term106 A b x).
Proof. exact (@lem3901023 (b x)). Qed.
Lemma lem3901028 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term96 A b a x) : term106 A b x.
Proof. exact (EQ_MP (@lem3901025 A b x) (@lem3900900 A b a x h1)). Qed.
Lemma lem3901031 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term45 A a b) (h2 : a x) (h3 : term96 A b a x) : False.
Proof. exact (@lem3901028 A b a x h3 (@lem3901020 A b a x h1 h2)). Qed.
Lemma lem3901032 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term45 A a b) (h2 : a x) (h3 : term96 A b a x) : term107.
Proof. exact (fun h0 : ~ False => @lem3901031 A b a x h1 h2 h3). Qed.
Lemma lem3901034 (p : Prop) : (term105 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3901035 : term107 = False.
Proof. exact (@lem3901034 False). Qed.
Lemma lem3901036 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term45 A a b) (h2 : a x) (h3 : term96 A b a x) : False.
Proof. exact (EQ_MP (@lem3901035) (@lem3901032 A b a x h1 h2 h3)). Qed.
Lemma lem3901038 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term61 A b a x) : b x.
Proof. exact (proj1 (@lem3900758 A b a x h1)). Qed.
Lemma lem3901039 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term61 A b a x) : term104 A b x.
Proof. exact (fun h0 : term60 A b x => @lem3901038 A b a x h1). Qed.
Lemma lem3901041 (p : Prop) : (term105 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3901042 {A : Type'} (b : A -> Prop) (x : A) : (term104 A b x) = (b x).
Proof. exact (@lem3901041 (b x)). Qed.
Lemma lem3901043 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term61 A b a x) : b x.
Proof. exact (EQ_MP (@lem3901042 A b x) (@lem3901039 A b a x h1)). Qed.
Lemma lem3901046 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3901048 {A : Type'} (b : A -> Prop) (x : A) : (term60 A b x) = (term106 A b x).
Proof. exact (@lem3901046 (b x)). Qed.
Lemma lem3901051 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term96 A b a x) : term106 A b x.
Proof. exact (EQ_MP (@lem3901048 A b x) (@lem3900910 A b a x h1)). Qed.
Lemma lem3901054 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term96 A b a x) (h2 : term61 A b a x) : False.
Proof. exact (@lem3901051 A b a x h1 (@lem3901043 A b a x h2)). Qed.
Lemma lem3901055 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term96 A b a x) (h2 : term61 A b a x) : term107.
Proof. exact (fun h0 : ~ False => @lem3901054 A b a x h1 h2). Qed.
Lemma lem3901057 (p : Prop) : (term105 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3901058 : term107 = False.
Proof. exact (@lem3901057 False). Qed.
Lemma lem3901059 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term96 A b a x) (h2 : term61 A b a x) : False.
Proof. exact (EQ_MP (@lem3901058) (@lem3901055 A b a x h1 h2)). Qed.
Lemma lem3901060 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term45 A a b) (h2 : a x) (h3 : term96 A b a x) : (a x) = False.
Proof. exact (prop_ext (fun h4 : a x => @lem3901036 A b a x h1 h2 h3) (fun h4 : False => @lem3900902 A a x h2)). Qed.
Lemma lem3901061 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term45 A a b) (h2 : a x) (h3 : term96 A b a x) : False.
Proof. exact (EQ_MP (@lem3901060 A b a x h1 h2 h3) (@lem3900902 A a x h2)). Qed.
Lemma lem3901062 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : a x) (h2 : term98 A b a x) : (a x) = False.
Proof. exact (prop_ext (fun h3 : a x => @lem3900960 A b a x h1 h2) (fun h3 : False => @lem3900892 A a x h1)). Qed.
Lemma lem3901063 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : a x) (h2 : term98 A b a x) : False.
Proof. exact (EQ_MP (@lem3901062 A b a x h1 h2) (@lem3900892 A a x h1)). Qed.
Lemma lem3901064 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term60 A b x) (h2 : term98 A b a x) : (term60 A b x) = False.
Proof. exact (prop_ext (fun h3 : term60 A b x => @lem3900937 A b a x h1 h2) (fun h3 : False => @lem3900880 A b x h1)). Qed.
Lemma lem3901065 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term60 A b x) (h2 : term98 A b a x) : False.
Proof. exact (EQ_MP (@lem3901064 A b a x h1 h2) (@lem3900880 A b x h1)). Qed.
Lemma lem3901066 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term45 A a b) (h2 : a x) (h3 : term96 A b a x) : (a x) = False.
Proof. exact (prop_ext (fun h4 : a x => @lem3901061 A b a x h1 h2 h3) (fun h4 : False => @lem3900831 A a x h2)). Qed.
Lemma lem3901067 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term45 A a b) (h2 : a x) (h3 : term96 A b a x) : False.
Proof. exact (EQ_MP (@lem3901066 A b a x h1 h2 h3) (@lem3900831 A a x h2)). Qed.
Lemma lem3901068 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : a x) (h2 : term98 A b a x) : (a x) = False.
Proof. exact (prop_ext (fun h3 : a x => @lem3901063 A b a x h1 h2) (fun h3 : False => @lem3900810 A a x h1)). Qed.
Lemma lem3901069 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : a x) (h2 : term98 A b a x) : False.
Proof. exact (EQ_MP (@lem3901068 A b a x h1 h2) (@lem3900810 A a x h1)). Qed.
Lemma lem3901070 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term60 A b x) (h2 : term98 A b a x) : (term60 A b x) = False.
Proof. exact (prop_ext (fun h3 : term60 A b x => @lem3901065 A b a x h1 h2) (fun h3 : False => @lem3900785 A b x h1)). Qed.
Lemma lem3901071 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term60 A b x) (h2 : term98 A b a x) : False.
Proof. exact (EQ_MP (@lem3901070 A b a x h1 h2) (@lem3900785 A b x h1)). Qed.
Lemma lem3901072 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term45 A a b) (h2 : a x) (h3 : term96 A b a x) : (a x) = False.
Proof. exact (prop_ext (fun h4 : a x => @lem3901067 A b a x h1 h2 h3) (fun h4 : False => @lem3900831 A a x h2)). Qed.
Lemma lem3901073 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term45 A a b) (h2 : a x) (h3 : term96 A b a x) : False.
Proof. exact (EQ_MP (@lem3901072 A b a x h1 h2 h3) (@lem3900831 A a x h2)). Qed.
Lemma lem3901074 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : a x) (h2 : term98 A b a x) : (a x) = False.
Proof. exact (prop_ext (fun h3 : a x => @lem3901069 A b a x h1 h2) (fun h3 : False => @lem3900810 A a x h1)). Qed.
Lemma lem3901075 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : a x) (h2 : term98 A b a x) : False.
Proof. exact (EQ_MP (@lem3901074 A b a x h1 h2) (@lem3900810 A a x h1)). Qed.
Lemma lem3901076 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term60 A b x) (h2 : term98 A b a x) : (term60 A b x) = False.
Proof. exact (prop_ext (fun h3 : term60 A b x => @lem3901071 A b a x h1 h2) (fun h3 : False => @lem3900785 A b x h1)). Qed.
Lemma lem3901077 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term60 A b x) (h2 : term98 A b a x) : False.
Proof. exact (EQ_MP (@lem3901076 A b a x h1 h2) (@lem3900785 A b x h1)). Qed.
Lemma lem3901078 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term45 A a b) (h2 : term96 A b a x) : False.
Proof. exact (or_elim (@lem3900755 A b a x h2) (fun h0 : a x => @lem3901073 A b a x h1 h0 h2) (fun h0 : term61 A b a x => @lem3901059 A b a x h2 h0)). Qed.
Lemma lem3901079 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term98 A b a x) : False.
Proof. exact (or_elim (@lem3900751 A b a x h1) (fun h0 : term60 A b x => @lem3901077 A b a x h0 h1) (fun h0 : a x => @lem3901075 A b a x h0 h1)). Qed.
Lemma lem3901080 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term45 A a b) (h2 : term84 A b a x) : False.
Proof. exact (or_elim (@lem3900746 A b a x h2) (fun h0 : term98 A b a x => @lem3901079 A b a x h0) (fun h0 : term96 A b a x => @lem3901078 A b a x h1 h0)). Qed.
Lemma lem3901081 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term45 A a b) (h2 : term84 A b a x) : (term84 A b a x) = False.
Proof. exact (prop_ext (fun h3 : term84 A b a x => @lem3901080 A b a x h1 h2) (fun h3 : False => @lem3900588 A b a x h2)). Qed.
Lemma lem3901082 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term45 A a b) (h2 : term84 A b a x) : False.
Proof. exact (EQ_MP (@lem3901081 A b a x h1 h2) (@lem3900588 A b a x h2)). Qed.
Lemma lem3901083 {A : Type'} (x : A) (a : A -> Prop) (b : A -> Prop) (h1 : term45 A a b) : term83 A b a x.
Proof. exact (fun h0 : term84 A b a x => @lem3901082 A b a x h1 h0). Qed.
Lemma lem3901084 {A : Type'} (x : A) (a : A -> Prop) (b : A -> Prop) (h1 : term45 A a b) : (b x) = (term62 A b a x).
Proof. exact (EQ_MP (@lem3900587 A b a x) (@lem3901083 A x a b h1)). Qed.
Lemma lem3901089 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term45 A a b) : term65 A b a.
Proof. exact (fun x : A => @lem3901084 A x a b h1). Qed.
Lemma lem3901090 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term66 A b a.
Proof. exact (fun h0 : term45 A a b => @lem3901089 A a b h0). Qed.
Lemma lem3901095 {A : Type'} (a : A -> Prop) : term78 A a.
Proof. exact (fun b : A -> Prop => @lem3901090 A b a). Qed.
Lemma lem3901100 {A : Type'} : term82 A.
Proof. exact (fun a : A -> Prop => @lem3901095 A a). Qed.
Lemma lem3901101 {A : Type'} : term81 A.
Proof. exact (EQ_MP (@lem3900582 A) (@lem3901100 A)). Qed.
Lemma lem3901102 {A : Type'} (a : A -> Prop) : term114 A a.
Proof. exact (@lem3901101 A a). Qed.
Lemma lem3901103 {A : Type'} (a : A -> Prop) : (term114 A a) = (term77 A a).
Proof. exact (eq_refl (term114 A a)). Qed.
Lemma lem3901104 {A : Type'} (a : A -> Prop) : term77 A a.
Proof. exact (EQ_MP (@lem3901103 A a) (@lem3901102 A a)). Qed.
Lemma lem3901105 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term115 A a b.
Proof. exact (@lem3901104 A a b). Qed.
Lemma lem3901106 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term115 A a b) = (term68 A b a).
Proof. exact (eq_refl (term115 A a b)). Qed.
Lemma lem3901107 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term68 A b a.
Proof. exact (EQ_MP (@lem3901106 A b a) (@lem3901105 A a b)). Qed.
Lemma lem3901109 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term68 A b a.
Proof. exact (@lem3900462 A b a (@lem3901107 A b a)). Qed.
Lemma lem3901110 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term69 A b a) : False.
Proof. exact (@lem3901109 A b a (@lem3900446 A b a h1)). Qed.
Lemma lem3901111 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term69 A b a) : (term69 A b a) = False.
Proof. exact (prop_ext (fun h2 : term69 A b a => @lem3901110 A b a h1) (fun h2 : False => @lem3900446 A b a h1)). Qed.
Lemma lem3901112 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term69 A b a) : False.
Proof. exact (EQ_MP (@lem3901111 A b a h1) (@lem3900446 A b a h1)). Qed.
Lemma lem3901113 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term68 A b a.
Proof. exact (fun h0 : term69 A b a => @lem3901112 A b a h0). Qed.
Lemma lem3901114 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term66 A b a.
Proof. exact (EQ_MP (@lem3900445 A b a) (@lem3901113 A b a)). Qed.
Lemma lem3901115 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term38 A b a.
Proof. exact (EQ_MP (@lem3900441 A b a) (@lem3901114 A b a)). Qed.
Lemma lem3901116 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term37 A b a.
Proof. exact (EQ_MP (@lem3900347 A b a) (@lem3901115 A b a)). Qed.
Lemma lem3901117 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @SUBSET A a b) : b = (term24 A b a).
Proof. exact (@lem3901116 A b a (@lem3900301 A a b h1)). Qed.
Lemma lem3901118 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : (term116 A b a) = (term117 A b a)) : (term116 A b a) = (term117 A b a).
Proof. exact (h1). Qed.
Lemma lem3901119 {A : Type'} (a : A -> Prop) : (term118 A a) = (term118 A a).
Proof. exact (eq_refl (term118 A a)). Qed.
Lemma lem3901120 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : (term116 A b a) = (term117 A b a)) : (term119 A b a) = (term120 A b a).
Proof. exact (MK_COMB (@lem3901119 A a) (@lem3901118 A b a h1)). Qed.
Lemma lem3901121 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term120 A b a) = (term121 A b a).
Proof. exact (eq_refl (term120 A b a)). Qed.
Lemma lem3901122 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term122 A b a) = (term122 A b a).
Proof. exact (eq_refl (term122 A b a)). Qed.
Lemma lem3901123 {A : Type'} (b : A -> Prop) (a : A -> Prop) : ((term119 A b a) = (term120 A b a)) = ((term119 A b a) = (term121 A b a)).
Proof. exact (MK_COMB (@lem3901122 A b a) (@lem3901121 A b a)). Qed.
Lemma lem3901124 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term119 A b a) = (term28 A b a).
Proof. exact (eq_refl (term119 A b a)). Qed.
Lemma lem3901125 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3901126 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term122 A b a) = (term123 A b a).
Proof. exact (MK_COMB (@lem3901125) (@lem3901124 A b a)). Qed.
Lemma lem3901127 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term121 A b a) = (term121 A b a).
Proof. exact (eq_refl (term121 A b a)). Qed.
Lemma lem3901128 {A : Type'} (b : A -> Prop) (a : A -> Prop) : ((term119 A b a) = (term121 A b a)) = ((term28 A b a) = (term121 A b a)).
Proof. exact (MK_COMB (@lem3901126 A b a) (@lem3901127 A b a)). Qed.
Lemma lem3901129 {A : Type'} (b : A -> Prop) (a : A -> Prop) : ((term119 A b a) = (term120 A b a)) = ((term28 A b a) = (term121 A b a)).
Proof. exact (TRANS (@lem3901123 A b a) (@lem3901128 A b a)). Qed.
Lemma lem3901130 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : (term116 A b a) = (term117 A b a)) : (term28 A b a) = (term121 A b a).
Proof. exact (EQ_MP (@lem3901129 A b a) (@lem3901120 A b a h1)). Qed.
Lemma lem3901131 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : (term116 A b a) = (term117 A b a)) : (term121 A b a) = (term28 A b a).
Proof. exact (SYM (@lem3901130 A b a h1)). Qed.
Lemma lem3901133 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term17 A s t.
Proof. exact (EQ_MP (@lem3900287 A s t) (@lem3900286 A s t)). Qed.
Lemma lem3901134 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term17 A s t.
Proof. exact (@lem3901133 A s t). Qed.
Lemma lem3901135 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term124 A b a.
Proof. exact (@lem3901134 A a (@DIFF A b a)). Qed.
Lemma lem3901137 {A : Type'} (s : A -> Prop) : term9 A s.
Proof. exact (EQ_MP (@lem3900264 A s) (@lem3900263 A s)). Qed.
Lemma lem3901138 {A : Type'} (s : A -> Prop) : term9 A s.
Proof. exact (@lem3901137 A s). Qed.
Lemma lem3901139 {A : Type'} (a : A -> Prop) : term9 A a.
Proof. exact (@lem3901138 A a). Qed.
Lemma lem3901140 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (@SUBSET A a b) = ((@SUBSET A a b) = True).
Proof. exact (@lem7 (@SUBSET A a b)). Qed.
Lemma lem3901142 {A : Type'} (b : A -> Prop) : (@FINITE A b) = ((@FINITE A b) = True).
Proof. exact (@lem7 (@FINITE A b)). Qed.
Lemma lem3901147 {A : Type'} (b : A -> Prop) (h1 : @FINITE A b) : (@FINITE A b) = True.
Proof. exact (EQ_MP (@lem3901142 A b) (@lem3900300 A b h1)). Qed.
Lemma lem3901148 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3901149 {A : Type'} (b : A -> Prop) (h1 : @FINITE A b) : (term125 A b) = (and True).
Proof. exact (MK_COMB (@lem3901148) (@lem3901147 A b h1)). Qed.
Lemma lem3901151 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @SUBSET A a b) : (@SUBSET A a b) = True.
Proof. exact (EQ_MP (@lem3901140 A a b) (@lem3900301 A a b h1)). Qed.
Lemma lem3901152 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) (h2 : @SUBSET A a b) : (term5 A a b) = (True /\ True).
Proof. exact (MK_COMB (@lem3901149 A b h1) (@lem3901151 A a b h2)). Qed.
Lemma lem3901154 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3901155 : (True /\ True) = True.
Proof. exact (@lem3901154 True). Qed.
Lemma lem3901156 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) (h2 : @SUBSET A a b) : (term5 A a b) = True.
Proof. exact (TRANS (@lem3901152 A a b h1 h2) (@lem3901155)). Qed.
Lemma lem3901157 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) (h2 : @SUBSET A a b) : True = (term5 A a b).
Proof. exact (SYM (@lem3901156 A a b h1 h2)). Qed.
Lemma lem3901158 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) (h2 : @SUBSET A a b) : term5 A a b.
Proof. exact (EQ_MP (@lem3901157 A a b h1 h2) (@lem0)). Qed.
Lemma lem3901159 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) (h2 : @SUBSET A a b) : term7 A a.
Proof. exact (ex_intro (term8 A a) b (@lem3901158 A a b h1 h2)). Qed.
Lemma lem3901160 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) (h2 : @SUBSET A a b) : @FINITE A a.
Proof. exact (@lem3901139 A a (@lem3901159 A a b h1 h2)). Qed.
Lemma lem3901162 {A : Type'} (s : A -> Prop) : term9 A s.
Proof. exact (EQ_MP (@lem3900243 A s) (@lem3900242 A s)). Qed.
Lemma lem3901163 {A : Type'} (s : A -> Prop) : term9 A s.
Proof. exact (@lem3901162 A s). Qed.
Lemma lem3901164 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term126 A b a.
Proof. exact (@lem3901163 A (@DIFF A b a)). Qed.
Lemma lem3901167 {A : Type'} (b : A -> Prop) : (@FINITE A b) = ((@FINITE A b) = True).
Proof. exact (@lem7 (@FINITE A b)). Qed.
Lemma lem3901172 {A : Type'} (b : A -> Prop) (h1 : @FINITE A b) : (@FINITE A b) = True.
Proof. exact (EQ_MP (@lem3901167 A b) (@lem3900300 A b h1)). Qed.
Lemma lem3901173 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3901174 {A : Type'} (b : A -> Prop) (h1 : @FINITE A b) : (term125 A b) = (and True).
Proof. exact (MK_COMB (@lem3901173) (@lem3901172 A b h1)). Qed.
Lemma lem3901175 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term127 A a b) = (term127 A a b).
Proof. exact (eq_refl (term127 A a b)). Qed.
Lemma lem3901176 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) : (term128 A a b) = (term129 A a b).
Proof. exact (MK_COMB (@lem3901174 A b h1) (@lem3901175 A a b)). Qed.
Lemma lem3901178 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3901179 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term129 A a b) = (term127 A a b).
Proof. exact (@lem3901178 (term127 A a b)). Qed.
Lemma lem3901180 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) : (term128 A a b) = (term127 A a b).
Proof. exact (TRANS (@lem3901176 A a b h1) (@lem3901179 A a b)). Qed.
Lemma lem3901181 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) : (term127 A a b) = (term128 A a b).
Proof. exact (SYM (@lem3901180 A a b h1)). Qed.
Lemma lem3901183 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term32 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3901184 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term32 A s t).
Proof. exact (@lem3901183 A s t). Qed.
Lemma lem3901185 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term127 A a b) = (term130 A a b).
Proof. exact (@lem3901184 A (@DIFF A b a) b). Qed.
Lemma lem3901192 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term130 A a b) = (term127 A a b).
Proof. exact (SYM (@lem3901185 A a b)). Qed.
Lemma lem3901200 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term55 A x s t) = (term56 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem3901201 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term55 A x s t) = (term56 A s x t).
Proof. exact (@lem3901200 A s x t). Qed.
Lemma lem3901202 {A : Type'} (b : A -> Prop) (x : A) (a : A -> Prop) : (term55 A x b a) = (term56 A b x a).
Proof. exact (@lem3901201 A b x a). Qed.
Lemma lem3901206 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3901207 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3901206 A P x). Qed.
Lemma lem3901208 {A : Type'} (b : A -> Prop) (x : A) : (@IN A x b) = (b x).
Proof. exact (@lem3901207 A b x). Qed.
Lemma lem3901209 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3901210 {A : Type'} (b : A -> Prop) (x : A) : (term57 A x b) = (term58 A b x).
Proof. exact (MK_COMB (@lem3901209) (@lem3901208 A b x)). Qed.
Lemma lem3901212 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3901213 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3901212 A P x). Qed.
Lemma lem3901214 {A : Type'} (a : A -> Prop) (x : A) : (@IN A x a) = (a x).
Proof. exact (@lem3901213 A a x). Qed.
Lemma lem3901215 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3901216 {A : Type'} (a : A -> Prop) (x : A) : (term59 A x a) = (term60 A a x).
Proof. exact (MK_COMB (@lem3901215) (@lem3901214 A a x)). Qed.
Lemma lem3901217 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term56 A b x a) = (term61 A b a x).
Proof. exact (MK_COMB (@lem3901210 A b x) (@lem3901216 A a x)). Qed.
Lemma lem3901220 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term55 A x b a) = (term61 A b a x).
Proof. exact (TRANS (@lem3901202 A b x a) (@lem3901217 A b a x)). Qed.
Lemma lem3901221 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3901222 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term131 A x b a) = (term132 A b a x).
Proof. exact (MK_COMB (@lem3901221) (@lem3901220 A b a x)). Qed.
Lemma lem3901224 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3901225 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3901224 A P x). Qed.
Lemma lem3901226 {A : Type'} (b : A -> Prop) (x : A) : (@IN A x b) = (b x).
Proof. exact (@lem3901225 A b x). Qed.
Lemma lem3901227 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) : (term133 A a x b) = (term134 A a b x).
Proof. exact (MK_COMB (@lem3901222 A b a x) (@lem3901226 A b x)). Qed.
Lemma lem3901230 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term135 A a b) = (term136 A a b).
Proof. exact (fun_ext (fun x : A => @lem3901227 A a b x)). Qed.
Lemma lem3901231 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3901232 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term130 A a b) = (term137 A a b).
Proof. exact (MK_COMB (@lem3901231 A) (@lem3901230 A a b)). Qed.
Lemma lem3901237 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term137 A a b) = (term130 A a b).
Proof. exact (SYM (@lem3901232 A a b)). Qed.
Lemma lem3901239 (p : Prop) : p = (term67 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3901240 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term137 A a b) = (term138 A a b).
Proof. exact (@lem3901239 (term137 A a b)). Qed.
Lemma lem3901241 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term138 A a b) = (term137 A a b).
Proof. exact (SYM (@lem3901240 A a b)). Qed.
Lemma lem3901242 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term139 A a b) : term139 A a b.
Proof. exact (h1). Qed.
Lemma lem3901245 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term138 A a b) : term138 A a b.
Proof. exact (h1). Qed.
Lemma lem3901246 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term140 A a b.
Proof. exact (fun h0 : term138 A a b => @lem3901245 A a b h0). Qed.
Lemma lem3901247 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term140 A a b) : term140 A a b.
Proof. exact (h1). Qed.
Lemma lem3901248 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term138 A a b) : term138 A a b.
Proof. exact (h1). Qed.
Lemma lem3901249 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term138 A a b) (h2 : term140 A a b) : term138 A a b.
Proof. exact (@lem3901247 A a b h2 (@lem3901248 A a b h1)). Qed.
Lemma lem3901250 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term138 A a b) : term141 A a b.
Proof. exact (fun h0 : term140 A a b => @lem3901249 A a b h1 h0). Qed.
Lemma lem3901251 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term140 A a b) : term140 A a b.
Proof. exact (h1). Qed.
Lemma lem3901252 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term138 A a b) (h2 : term140 A a b) : term138 A a b.
Proof. exact (@lem3901250 A a b h1 (@lem3901251 A a b h2)). Qed.
Lemma lem3901253 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term140 A a b) : term140 A a b.
Proof. exact (fun h0 : term138 A a b => @lem3901252 A a b h0 h1). Qed.
Lemma lem3901254 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term142 A a b.
Proof. exact (fun h0 : term140 A a b => @lem3901253 A a b h0). Qed.
Lemma lem3901257 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term140 A a b.
Proof. exact (@lem3901254 A a b (@lem3901246 A a b)). Qed.
Lemma lem3901258 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term140 A a b.
Proof. exact (@lem3901257 A a b). Qed.
Lemma lem3901268 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3901269 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term138 A a b) = (term143 A a b).
Proof. exact (@lem3901268 (term139 A a b)). Qed.
Lemma lem3901271 (t : Prop) : (term74 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3901272 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term143 A a b) = (term137 A a b).
Proof. exact (@lem3901271 (term137 A a b)). Qed.
Lemma lem3901277 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term138 A a b) = (term137 A a b).
Proof. exact (TRANS (@lem3901269 A a b) (@lem3901272 A a b)). Qed.
Lemma lem3901282 {A : Type'} (b : A -> Prop) : (term144 A b) = (term145 A b).
Proof. exact (fun_ext (fun a : A -> Prop => @lem3901277 A a b)). Qed.
Lemma lem3901283 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3901284 {A : Type'} (b : A -> Prop) : (term146 A b) = (term147 A b).
Proof. exact (MK_COMB (@lem3901283 A) (@lem3901282 A b)). Qed.
Lemma lem3901289 {A : Type'} : (term148 A) = (term149 A).
Proof. exact (fun_ext (fun b : A -> Prop => @lem3901284 A b)). Qed.
Lemma lem3901290 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3901299 {A : Type'} : (term150 A) = (term151 A).
Proof. exact (MK_COMB (@lem3901290 A) (@lem3901289 A)). Qed.
Lemma lem3901310 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) : (term134 A a b x) = (term134 A a b x).
Proof. exact (eq_refl (term134 A a b x)). Qed.
Lemma lem3901311 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term136 A a b) = (term136 A a b).
Proof. exact (fun_ext (fun x : A => @lem3901310 A a b x)). Qed.
Lemma lem3901312 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3901313 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term137 A a b) = (term137 A a b).
Proof. exact (MK_COMB (@lem3901312 A) (@lem3901311 A a b)). Qed.
Lemma lem3901314 {A : Type'} (b : A -> Prop) : (term145 A b) = (term145 A b).
Proof. exact (fun_ext (fun a : A -> Prop => @lem3901313 A a b)). Qed.
Lemma lem3901315 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3901316 {A : Type'} (b : A -> Prop) : (term147 A b) = (term147 A b).
Proof. exact (MK_COMB (@lem3901315 A) (@lem3901314 A b)). Qed.
Lemma lem3901317 {A : Type'} : (term149 A) = (term149 A).
Proof. exact (fun_ext (fun b : A -> Prop => @lem3901316 A b)). Qed.
Lemma lem3901318 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3901319 {A : Type'} : (term151 A) = (term151 A).
Proof. exact (MK_COMB (@lem3901318 A) (@lem3901317 A)). Qed.
Lemma lem3901344 {A : Type'} : (term150 A) = (term151 A).
Proof. exact (TRANS (@lem3901299 A) (@lem3901319 A)). Qed.
Lemma lem3901345 {A : Type'} : (term151 A) = (term150 A).
Proof. exact (SYM (@lem3901344 A)). Qed.
Lemma lem3901348 (p : Prop) : p = (term67 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3901349 {A : Type'} (b : A -> Prop) (x : A) : (b x) = (term152 A b x).
Proof. exact (@lem3901348 (b x)). Qed.
Lemma lem3901350 {A : Type'} (b : A -> Prop) (x : A) : (term152 A b x) = (b x).
Proof. exact (SYM (@lem3901349 A b x)). Qed.
Lemma lem3901351 {A : Type'} (b : A -> Prop) (x : A) (h1 : term60 A b x) : term60 A b x.
Proof. exact (h1). Qed.
Lemma lem3901361 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term61 A b a x) : term61 A b a x.
Proof. exact (h1). Qed.
Lemma lem3901367 {A : Type'} (b : A -> Prop) (x : A) (h1 : term60 A b x) : term60 A b x.
Proof. exact (h1). Qed.
Lemma lem3901379 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term61 A b a x) : term61 A b a x.
Proof. exact (h1). Qed.
Lemma lem3901385 {A : Type'} (b : A -> Prop) (x : A) (h1 : term60 A b x) : term60 A b x.
Proof. exact (h1). Qed.
Lemma lem3901391 {A : Type'} (b : A -> Prop) (x : A) (h1 : term60 A b x) : term60 A b x.
Proof. exact (h1). Qed.
Lemma lem3901401 {A : Type'} (b : A -> Prop) (x : A) (h1 : term60 A b x) : term60 A b x.
Proof. exact (h1). Qed.
Lemma lem3901407 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term61 A b a x) : b x.
Proof. exact (proj1 (@lem3901379 A b a x h1)). Qed.
Lemma lem3901408 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term61 A b a x) : term104 A b x.
Proof. exact (fun h0 : term60 A b x => @lem3901407 A b a x h1). Qed.
Lemma lem3901410 (p : Prop) : (term105 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3901411 {A : Type'} (b : A -> Prop) (x : A) : (term104 A b x) = (b x).
Proof. exact (@lem3901410 (b x)). Qed.
Lemma lem3901412 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term61 A b a x) : b x.
Proof. exact (EQ_MP (@lem3901411 A b x) (@lem3901408 A b a x h1)). Qed.
Lemma lem3901415 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3901417 {A : Type'} (b : A -> Prop) (x : A) : (term60 A b x) = (term106 A b x).
Proof. exact (@lem3901415 (b x)). Qed.
Lemma lem3901420 {A : Type'} (b : A -> Prop) (x : A) (h1 : term60 A b x) : term106 A b x.
Proof. exact (EQ_MP (@lem3901417 A b x) (@lem3901401 A b x h1)). Qed.
Lemma lem3901423 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term60 A b x) (h2 : term61 A b a x) : False.
Proof. exact (@lem3901420 A b x h1 (@lem3901412 A b a x h2)). Qed.
Lemma lem3901424 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term60 A b x) (h2 : term61 A b a x) : term107.
Proof. exact (fun h0 : ~ False => @lem3901423 A b a x h1 h2). Qed.
Lemma lem3901426 (p : Prop) : (term105 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3901427 : term107 = False.
Proof. exact (@lem3901426 False). Qed.
Lemma lem3901428 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term60 A b x) (h2 : term61 A b a x) : False.
Proof. exact (EQ_MP (@lem3901427) (@lem3901424 A b a x h1 h2)). Qed.
Lemma lem3901429 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term60 A b x) (h2 : term61 A b a x) : (term60 A b x) = False.
Proof. exact (prop_ext (fun h3 : term60 A b x => @lem3901428 A b a x h1 h2) (fun h3 : False => @lem3901401 A b x h1)). Qed.
Lemma lem3901430 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term60 A b x) (h2 : term61 A b a x) : False.
Proof. exact (EQ_MP (@lem3901429 A b a x h1 h2) (@lem3901401 A b x h1)). Qed.
Lemma lem3901431 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term60 A b x) (h2 : term61 A b a x) : (term60 A b x) = False.
Proof. exact (prop_ext (fun h3 : term60 A b x => @lem3901430 A b a x h1 h2) (fun h3 : False => @lem3901391 A b x h1)). Qed.
Lemma lem3901432 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term60 A b x) (h2 : term61 A b a x) : False.
Proof. exact (EQ_MP (@lem3901431 A b a x h1 h2) (@lem3901391 A b x h1)). Qed.
Lemma lem3901433 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term60 A b x) (h2 : term61 A b a x) : (term60 A b x) = False.
Proof. exact (prop_ext (fun h3 : term60 A b x => @lem3901432 A b a x h1 h2) (fun h3 : False => @lem3901391 A b x h1)). Qed.
Lemma lem3901434 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term60 A b x) (h2 : term61 A b a x) : False.
Proof. exact (EQ_MP (@lem3901433 A b a x h1 h2) (@lem3901391 A b x h1)). Qed.
Lemma lem3901435 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term60 A b x) (h2 : term61 A b a x) : (term60 A b x) = False.
Proof. exact (prop_ext (fun h3 : term60 A b x => @lem3901434 A b a x h1 h2) (fun h3 : False => @lem3901385 A b x h1)). Qed.
Lemma lem3901436 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term60 A b x) (h2 : term61 A b a x) : False.
Proof. exact (EQ_MP (@lem3901435 A b a x h1 h2) (@lem3901385 A b x h1)). Qed.
Lemma lem3901437 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term60 A b x) (h2 : term61 A b a x) : (term61 A b a x) = False.
Proof. exact (prop_ext (fun h3 : term61 A b a x => @lem3901436 A b a x h1 h2) (fun h3 : False => @lem3901379 A b a x h2)). Qed.
Lemma lem3901438 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term60 A b x) (h2 : term61 A b a x) : False.
Proof. exact (EQ_MP (@lem3901437 A b a x h1 h2) (@lem3901379 A b a x h2)). Qed.
Lemma lem3901439 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term60 A b x) (h2 : term61 A b a x) : (term60 A b x) = False.
Proof. exact (prop_ext (fun h3 : term60 A b x => @lem3901438 A b a x h1 h2) (fun h3 : False => @lem3901367 A b x h1)). Qed.
Lemma lem3901440 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term60 A b x) (h2 : term61 A b a x) : False.
Proof. exact (EQ_MP (@lem3901439 A b a x h1 h2) (@lem3901367 A b x h1)). Qed.
Lemma lem3901441 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term60 A b x) (h2 : term61 A b a x) : (term61 A b a x) = False.
Proof. exact (prop_ext (fun h3 : term61 A b a x => @lem3901440 A b a x h1 h2) (fun h3 : False => @lem3901361 A b a x h2)). Qed.
Lemma lem3901442 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term60 A b x) (h2 : term61 A b a x) : False.
Proof. exact (EQ_MP (@lem3901441 A b a x h1 h2) (@lem3901361 A b a x h2)). Qed.
Lemma lem3901443 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term60 A b x) (h2 : term61 A b a x) : (term60 A b x) = False.
Proof. exact (prop_ext (fun h3 : term60 A b x => @lem3901442 A b a x h1 h2) (fun h3 : False => @lem3901351 A b x h1)). Qed.
Lemma lem3901444 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term60 A b x) (h2 : term61 A b a x) : False.
Proof. exact (EQ_MP (@lem3901443 A b a x h1 h2) (@lem3901351 A b x h1)). Qed.
Lemma lem3901445 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term61 A b a x) : term152 A b x.
Proof. exact (fun h0 : term60 A b x => @lem3901444 A b a x h0 h1). Qed.
Lemma lem3901446 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term61 A b a x) : b x.
Proof. exact (EQ_MP (@lem3901350 A b x) (@lem3901445 A b a x h1)). Qed.
Lemma lem3901447 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) : term134 A a b x.
Proof. exact (fun h0 : term61 A b a x => @lem3901446 A b a x h0). Qed.
Lemma lem3901452 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term137 A a b.
Proof. exact (fun x : A => @lem3901447 A a b x). Qed.
Lemma lem3901457 {A : Type'} (b : A -> Prop) : term147 A b.
Proof. exact (fun a : A -> Prop => @lem3901452 A a b). Qed.
Lemma lem3901462 {A : Type'} : term151 A.
Proof. exact (fun b : A -> Prop => @lem3901457 A b). Qed.
Lemma lem3901463 {A : Type'} : term150 A.
Proof. exact (EQ_MP (@lem3901345 A) (@lem3901462 A)). Qed.
Lemma lem3901464 {A : Type'} (b : A -> Prop) : term153 A b.
Proof. exact (@lem3901463 A b). Qed.
Lemma lem3901465 {A : Type'} (b : A -> Prop) : (term153 A b) = (term146 A b).
Proof. exact (eq_refl (term153 A b)). Qed.
Lemma lem3901466 {A : Type'} (b : A -> Prop) : term146 A b.
Proof. exact (EQ_MP (@lem3901465 A b) (@lem3901464 A b)). Qed.
Lemma lem3901467 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term154 A b a.
Proof. exact (@lem3901466 A b a). Qed.
Lemma lem3901468 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term154 A b a) = (term138 A a b).
Proof. exact (eq_refl (term154 A b a)). Qed.
Lemma lem3901469 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term138 A a b.
Proof. exact (EQ_MP (@lem3901468 A a b) (@lem3901467 A b a)). Qed.
Lemma lem3901471 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term138 A a b.
Proof. exact (@lem3901258 A a b (@lem3901469 A a b)). Qed.
Lemma lem3901472 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term139 A a b) : False.
Proof. exact (@lem3901471 A a b (@lem3901242 A a b h1)). Qed.
Lemma lem3901473 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term139 A a b) : (term139 A a b) = False.
Proof. exact (prop_ext (fun h2 : term139 A a b => @lem3901472 A a b h1) (fun h2 : False => @lem3901242 A a b h1)). Qed.
Lemma lem3901474 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term139 A a b) : False.
Proof. exact (EQ_MP (@lem3901473 A a b h1) (@lem3901242 A a b h1)). Qed.
Lemma lem3901475 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term138 A a b.
Proof. exact (fun h0 : term139 A a b => @lem3901474 A a b h0). Qed.
Lemma lem3901476 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term137 A a b.
Proof. exact (EQ_MP (@lem3901241 A a b) (@lem3901475 A a b)). Qed.
Lemma lem3901477 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term130 A a b.
Proof. exact (EQ_MP (@lem3901237 A a b) (@lem3901476 A a b)). Qed.
Lemma lem3901478 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term127 A a b.
Proof. exact (EQ_MP (@lem3901192 A a b) (@lem3901477 A a b)). Qed.
Lemma lem3901479 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) : term128 A a b.
Proof. exact (EQ_MP (@lem3901181 A a b h1) (@lem3901478 A a b)). Qed.
Lemma lem3901480 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) : term155 A b a.
Proof. exact (ex_intro (term156 A b a) b (@lem3901479 A a b h1)). Qed.
Lemma lem3901481 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) : term157 A b a.
Proof. exact (@lem3901164 A b a (@lem3901480 A a b h1)). Qed.
Lemma lem3901485 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term35 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3901486 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term35 A s t).
Proof. exact (@lem3901485 A s t). Qed.
Lemma lem3901487 {A : Type'} (b : A -> Prop) (a : A -> Prop) : ((term158 A b a) = (@EMPTY A)) = (term159 A b a).
Proof. exact (@lem3901486 A (term158 A b a) (@EMPTY A)). Qed.
Lemma lem3901496 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term159 A b a) = ((term158 A b a) = (@EMPTY A)).
Proof. exact (SYM (@lem3901487 A b a)). Qed.
Lemma lem3901504 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term160 A x s t) = (term161 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3901505 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term160 A x s t) = (term161 A s x t).
Proof. exact (@lem3901504 A s x t). Qed.
Lemma lem3901506 {A : Type'} (x : A) (b : A -> Prop) (a : A -> Prop) : (term162 A x b a) = (term163 A x b a).
Proof. exact (@lem3901505 A a x (@DIFF A b a)). Qed.
Lemma lem3901510 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3901511 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3901510 A P x). Qed.
Lemma lem3901512 {A : Type'} (a : A -> Prop) (x : A) : (@IN A x a) = (a x).
Proof. exact (@lem3901511 A a x). Qed.
Lemma lem3901513 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3901514 {A : Type'} (a : A -> Prop) (x : A) : (term57 A x a) = (term58 A a x).
Proof. exact (MK_COMB (@lem3901513) (@lem3901512 A a x)). Qed.
Lemma lem3901516 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term55 A x s t) = (term56 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem3901517 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term55 A x s t) = (term56 A s x t).
Proof. exact (@lem3901516 A s x t). Qed.
Lemma lem3901518 {A : Type'} (b : A -> Prop) (x : A) (a : A -> Prop) : (term55 A x b a) = (term56 A b x a).
Proof. exact (@lem3901517 A b x a). Qed.
Lemma lem3901522 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3901523 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3901522 A P x). Qed.
Lemma lem3901524 {A : Type'} (b : A -> Prop) (x : A) : (@IN A x b) = (b x).
Proof. exact (@lem3901523 A b x). Qed.
Lemma lem3901525 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3901526 {A : Type'} (b : A -> Prop) (x : A) : (term57 A x b) = (term58 A b x).
Proof. exact (MK_COMB (@lem3901525) (@lem3901524 A b x)). Qed.
Lemma lem3901528 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3901529 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3901528 A P x). Qed.
Lemma lem3901530 {A : Type'} (a : A -> Prop) (x : A) : (@IN A x a) = (a x).
Proof. exact (@lem3901529 A a x). Qed.
Lemma lem3901531 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3901532 {A : Type'} (a : A -> Prop) (x : A) : (term59 A x a) = (term60 A a x).
Proof. exact (MK_COMB (@lem3901531) (@lem3901530 A a x)). Qed.
Lemma lem3901533 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term56 A b x a) = (term61 A b a x).
Proof. exact (MK_COMB (@lem3901526 A b x) (@lem3901532 A a x)). Qed.
Lemma lem3901536 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term55 A x b a) = (term61 A b a x).
Proof. exact (TRANS (@lem3901518 A b x a) (@lem3901533 A b a x)). Qed.
Lemma lem3901537 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term163 A x b a) = (term164 A b a x).
Proof. exact (MK_COMB (@lem3901514 A a x) (@lem3901536 A b a x)). Qed.
Lemma lem3901540 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term162 A x b a) = (term164 A b a x).
Proof. exact (TRANS (@lem3901506 A x b a) (@lem3901537 A b a x)). Qed.
Lemma lem3901541 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3901542 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term165 A x b a) = (term166 A b a x).
Proof. exact (MK_COMB (@lem3901541) (@lem3901540 A b a x)). Qed.
Lemma lem3901544 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3901545 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3901544 A x). Qed.
Lemma lem3901546 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : ((term162 A x b a) = (@IN A x (@EMPTY A))) = ((term164 A b a x) = False).
Proof. exact (MK_COMB (@lem3901542 A b a x) (@lem3901545 A x)). Qed.
Lemma lem3901548 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3901549 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : ((term164 A b a x) = False) = (term167 A b a x).
Proof. exact (@lem3901548 (term164 A b a x)). Qed.
Lemma lem3901554 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : ((term162 A x b a) = (@IN A x (@EMPTY A))) = (term167 A b a x).
Proof. exact (TRANS (@lem3901546 A b a x) (@lem3901549 A b a x)). Qed.
Lemma lem3901555 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term168 A b a) = (term169 A b a).
Proof. exact (fun_ext (fun x : A => @lem3901554 A b a x)). Qed.
Lemma lem3901556 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3901557 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term159 A b a) = (term170 A b a).
Proof. exact (MK_COMB (@lem3901556 A) (@lem3901555 A b a)). Qed.
Lemma lem3901562 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term170 A b a) = (term159 A b a).
Proof. exact (SYM (@lem3901557 A b a)). Qed.
Lemma lem3901564 (p : Prop) : p = (term67 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3901565 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term170 A b a) = (term171 A b a).
Proof. exact (@lem3901564 (term170 A b a)). Qed.
Lemma lem3901566 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term171 A b a) = (term170 A b a).
Proof. exact (SYM (@lem3901565 A b a)). Qed.
Lemma lem3901567 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term172 A b a) : term172 A b a.
Proof. exact (h1). Qed.
Lemma lem3901570 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term171 A b a) : term171 A b a.
Proof. exact (h1). Qed.
Lemma lem3901571 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term173 A b a.
Proof. exact (fun h0 : term171 A b a => @lem3901570 A b a h0). Qed.
Lemma lem3901572 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term173 A b a) : term173 A b a.
Proof. exact (h1). Qed.
Lemma lem3901573 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term171 A b a) : term171 A b a.
Proof. exact (h1). Qed.
Lemma lem3901574 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term171 A b a) (h2 : term173 A b a) : term171 A b a.
Proof. exact (@lem3901572 A b a h2 (@lem3901573 A b a h1)). Qed.
Lemma lem3901575 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term171 A b a) : term174 A b a.
Proof. exact (fun h0 : term173 A b a => @lem3901574 A b a h1 h0). Qed.
Lemma lem3901576 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term173 A b a) : term173 A b a.
Proof. exact (h1). Qed.
Lemma lem3901577 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term171 A b a) (h2 : term173 A b a) : term171 A b a.
Proof. exact (@lem3901575 A b a h1 (@lem3901576 A b a h2)). Qed.
Lemma lem3901578 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term173 A b a) : term173 A b a.
Proof. exact (fun h0 : term171 A b a => @lem3901577 A b a h0 h1). Qed.
Lemma lem3901579 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term175 A b a.
Proof. exact (fun h0 : term173 A b a => @lem3901578 A b a h0). Qed.
Lemma lem3901582 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term173 A b a.
Proof. exact (@lem3901579 A b a (@lem3901571 A b a)). Qed.
Lemma lem3901583 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term173 A b a.
Proof. exact (@lem3901582 A b a). Qed.
Lemma lem3901593 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3901594 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term171 A b a) = (term176 A b a).
Proof. exact (@lem3901593 (term172 A b a)). Qed.
Lemma lem3901596 (t : Prop) : (term74 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3901597 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term176 A b a) = (term170 A b a).
Proof. exact (@lem3901596 (term170 A b a)). Qed.
Lemma lem3901602 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term171 A b a) = (term170 A b a).
Proof. exact (TRANS (@lem3901594 A b a) (@lem3901597 A b a)). Qed.
Lemma lem3901607 {A : Type'} (a : A -> Prop) : (term177 A a) = (term178 A a).
Proof. exact (fun_ext (fun b : A -> Prop => @lem3901602 A b a)). Qed.
Lemma lem3901608 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3901609 {A : Type'} (a : A -> Prop) : (term179 A a) = (term180 A a).
Proof. exact (MK_COMB (@lem3901608 A) (@lem3901607 A a)). Qed.
Lemma lem3901614 {A : Type'} : (term181 A) = (term182 A).
Proof. exact (fun_ext (fun a : A -> Prop => @lem3901609 A a)). Qed.
Lemma lem3901615 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3901624 {A : Type'} : (term183 A) = (term184 A).
Proof. exact (MK_COMB (@lem3901615 A) (@lem3901614 A)). Qed.
Lemma lem3901637 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term167 A b a x) = (term167 A b a x).
Proof. exact (eq_refl (term167 A b a x)). Qed.
Lemma lem3901638 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term169 A b a) = (term169 A b a).
Proof. exact (fun_ext (fun x : A => @lem3901637 A b a x)). Qed.
Lemma lem3901639 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3901640 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term170 A b a) = (term170 A b a).
Proof. exact (MK_COMB (@lem3901639 A) (@lem3901638 A b a)). Qed.
Lemma lem3901641 {A : Type'} (a : A -> Prop) : (term178 A a) = (term178 A a).
Proof. exact (fun_ext (fun b : A -> Prop => @lem3901640 A b a)). Qed.
Lemma lem3901642 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3901643 {A : Type'} (a : A -> Prop) : (term180 A a) = (term180 A a).
Proof. exact (MK_COMB (@lem3901642 A) (@lem3901641 A a)). Qed.
Lemma lem3901644 {A : Type'} : (term182 A) = (term182 A).
Proof. exact (fun_ext (fun a : A -> Prop => @lem3901643 A a)). Qed.
Lemma lem3901645 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3901646 {A : Type'} : (term184 A) = (term184 A).
Proof. exact (MK_COMB (@lem3901645 A) (@lem3901644 A)). Qed.
Lemma lem3901671 {A : Type'} : (term183 A) = (term184 A).
Proof. exact (TRANS (@lem3901624 A) (@lem3901646 A)). Qed.
Lemma lem3901672 {A : Type'} : (term184 A) = (term183 A).
Proof. exact (SYM (@lem3901671 A)). Qed.
Lemma lem3901687 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term164 A b a x) : term164 A b a x.
Proof. exact (h1). Qed.
Lemma lem3901705 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term164 A b a x) : term164 A b a x.
Proof. exact (h1). Qed.
Lemma lem3901706 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term164 A b a x) : term61 A b a x.
Proof. exact (proj2 (@lem3901705 A b a x h1)). Qed.
Lemma lem3901727 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term164 A b a x) : term60 A a x.
Proof. exact (proj2 (@lem3901706 A b a x h1)). Qed.
Lemma lem3901729 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term164 A b a x) : a x.
Proof. exact (proj1 (@lem3901705 A b a x h1)). Qed.
Lemma lem3901730 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term164 A b a x) : term104 A a x.
Proof. exact (fun h0 : term60 A a x => @lem3901729 A b a x h1). Qed.
Lemma lem3901732 (p : Prop) : (term105 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3901733 {A : Type'} (a : A -> Prop) (x : A) : (term104 A a x) = (a x).
Proof. exact (@lem3901732 (a x)). Qed.
Lemma lem3901734 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term164 A b a x) : a x.
Proof. exact (EQ_MP (@lem3901733 A a x) (@lem3901730 A b a x h1)). Qed.
Lemma lem3901737 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3901739 {A : Type'} (a : A -> Prop) (x : A) : (term60 A a x) = (term106 A a x).
Proof. exact (@lem3901737 (a x)). Qed.
Lemma lem3901742 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term164 A b a x) : term106 A a x.
Proof. exact (EQ_MP (@lem3901739 A a x) (@lem3901727 A b a x h1)). Qed.
Lemma lem3901745 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term164 A b a x) : False.
Proof. exact (@lem3901742 A b a x h1 (@lem3901734 A b a x h1)). Qed.
Lemma lem3901746 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term164 A b a x) : term107.
Proof. exact (fun h0 : ~ False => @lem3901745 A b a x h1). Qed.
Lemma lem3901748 (p : Prop) : (term105 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3901749 : term107 = False.
Proof. exact (@lem3901748 False). Qed.
Lemma lem3901750 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term164 A b a x) : False.
Proof. exact (EQ_MP (@lem3901749) (@lem3901746 A b a x h1)). Qed.
Lemma lem3901751 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term164 A b a x) : (term164 A b a x) = False.
Proof. exact (prop_ext (fun h2 : term164 A b a x => @lem3901750 A b a x h1) (fun h2 : False => @lem3901705 A b a x h1)). Qed.
Lemma lem3901752 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term164 A b a x) : False.
Proof. exact (EQ_MP (@lem3901751 A b a x h1) (@lem3901705 A b a x h1)). Qed.
Lemma lem3901753 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term164 A b a x) : (term164 A b a x) = False.
Proof. exact (prop_ext (fun h2 : term164 A b a x => @lem3901752 A b a x h1) (fun h2 : False => @lem3901687 A b a x h1)). Qed.
Lemma lem3901754 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term164 A b a x) : False.
Proof. exact (EQ_MP (@lem3901753 A b a x h1) (@lem3901687 A b a x h1)). Qed.
Lemma lem3901755 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : term185 A b a x.
Proof. exact (fun h0 : term164 A b a x => @lem3901754 A b a x h0). Qed.
Lemma lem3901756 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term185 A b a x) = (term167 A b a x).
Proof. exact (@lem69 (term164 A b a x)). Qed.
Lemma lem3901757 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : term167 A b a x.
Proof. exact (EQ_MP (@lem3901756 A b a x) (@lem3901755 A b a x)). Qed.
Lemma lem3901762 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term170 A b a.
Proof. exact (fun x : A => @lem3901757 A b a x). Qed.
Lemma lem3901767 {A : Type'} (a : A -> Prop) : term180 A a.
Proof. exact (fun b : A -> Prop => @lem3901762 A b a). Qed.
Lemma lem3901772 {A : Type'} : term184 A.
Proof. exact (fun a : A -> Prop => @lem3901767 A a). Qed.
Lemma lem3901773 {A : Type'} : term183 A.
Proof. exact (EQ_MP (@lem3901672 A) (@lem3901772 A)). Qed.
Lemma lem3901774 {A : Type'} (a : A -> Prop) : term186 A a.
Proof. exact (@lem3901773 A a). Qed.
Lemma lem3901775 {A : Type'} (a : A -> Prop) : (term186 A a) = (term179 A a).
Proof. exact (eq_refl (term186 A a)). Qed.
Lemma lem3901776 {A : Type'} (a : A -> Prop) : term179 A a.
Proof. exact (EQ_MP (@lem3901775 A a) (@lem3901774 A a)). Qed.
Lemma lem3901777 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term187 A a b.
Proof. exact (@lem3901776 A a b). Qed.
Lemma lem3901778 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term187 A a b) = (term171 A b a).
Proof. exact (eq_refl (term187 A a b)). Qed.
Lemma lem3901779 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term171 A b a.
Proof. exact (EQ_MP (@lem3901778 A b a) (@lem3901777 A a b)). Qed.
Lemma lem3901781 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term171 A b a.
Proof. exact (@lem3901583 A b a (@lem3901779 A b a)). Qed.
Lemma lem3901782 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term172 A b a) : False.
Proof. exact (@lem3901781 A b a (@lem3901567 A b a h1)). Qed.
Lemma lem3901783 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term172 A b a) : (term172 A b a) = False.
Proof. exact (prop_ext (fun h2 : term172 A b a => @lem3901782 A b a h1) (fun h2 : False => @lem3901567 A b a h1)). Qed.
Lemma lem3901784 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term172 A b a) : False.
Proof. exact (EQ_MP (@lem3901783 A b a h1) (@lem3901567 A b a h1)). Qed.
Lemma lem3901785 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term171 A b a.
Proof. exact (fun h0 : term172 A b a => @lem3901784 A b a h0). Qed.
Lemma lem3901786 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term170 A b a.
Proof. exact (EQ_MP (@lem3901566 A b a) (@lem3901785 A b a)). Qed.
Lemma lem3901787 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term159 A b a.
Proof. exact (EQ_MP (@lem3901562 A b a) (@lem3901786 A b a)). Qed.
Lemma lem3901788 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term158 A b a) = (@EMPTY A).
Proof. exact (EQ_MP (@lem3901496 A b a) (@lem3901787 A b a)). Qed.
Lemma lem3901789 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) : term188 A b a.
Proof. exact (conj (@lem3901481 A a b h1) (@lem3901788 A b a)). Qed.
Lemma lem3901790 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) (h2 : @SUBSET A a b) : term189 A b a.
Proof. exact (conj (@lem3901160 A a b h1 h2) (@lem3901789 A a b h1)). Qed.
Lemma lem3901791 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) (h2 : @SUBSET A a b) : (term116 A b a) = (term117 A b a).
Proof. exact (@lem3901135 A b a (@lem3901790 A a b h1 h2)). Qed.
Lemma lem3901820 (m : nat) (n : nat) : (Peano.le m n) = (term190 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem3901821 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term121 A b a) = (term191 A b a).
Proof. exact (@lem3901820 (@CARD A a) (term117 A b a)). Qed.
Lemma lem3901823 (m : nat) (n : nat) : (term192 m n) = (term193 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem3901824 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term194 A b a) = (term195 A b a).
Proof. exact (@lem3901823 (@CARD A a) (term196 A b a)). Qed.
Lemma lem3901825 {A : Type'} (a : A -> Prop) : (term197 A a) = (term197 A a).
Proof. exact (eq_refl (term197 A a)). Qed.
Lemma lem3901826 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term191 A b a) = (term198 A b a).
Proof. exact (MK_COMB (@lem3901825 A a) (@lem3901824 A b a)). Qed.
Lemma lem3901828 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term121 A b a) = (term198 A b a).
Proof. exact (TRANS (@lem3901821 A b a) (@lem3901826 A b a)). Qed.
Lemma lem3901829 {A : Type'} (a : A -> Prop) : term199 A a.
Proof. exact (@lem2307535 (@CARD A a)). Qed.
Lemma lem3901830 {A : Type'} (a : A -> Prop) : (term199 A a) = (term200 A a).
Proof. exact (eq_refl (term199 A a)). Qed.
Lemma lem3901831 {A : Type'} (a : A -> Prop) : term200 A a.
Proof. exact (EQ_MP (@lem3901830 A a) (@lem3901829 A a)). Qed.
Lemma lem3901832 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term201 A b a.
Proof. exact (@lem2307535 (term196 A b a)). Qed.
Lemma lem3901833 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term201 A b a) = (term202 A b a).
Proof. exact (eq_refl (term201 A b a)). Qed.
Lemma lem3901834 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term202 A b a.
Proof. exact (EQ_MP (@lem3901833 A b a) (@lem3901832 A b a)). Qed.
Lemma lem3901835 (_45312 : int) (_45313 : int) : (term203 _45312 _45313) = (term204 _45312 _45313).
Proof. exact (@lem2318604 (term204 _45312 _45313)). Qed.
Lemma lem3901852 (_45312 : int) (_45313 : int) : (term205 _45312 _45313) = (term206 _45312 _45313).
Proof. exact (@lem17362 (term207 _45313) (term208 _45312 _45313)). Qed.
Lemma lem3901854 (_45312 : int) : (term209 _45312) = (term209 _45312).
Proof. exact (eq_refl (term209 _45312)). Qed.
Lemma lem3901855 (_45312 : int) (_45313 : int) : (term210 _45312 _45313) = (term211 _45312 _45313).
Proof. exact (MK_COMB (@lem3901854 _45312) (@lem3901852 _45312 _45313)). Qed.
Lemma lem3901856 (_45312 : int) (_45313 : int) : (term212 _45312 _45313) = (term210 _45312 _45313).
Proof. exact (@lem17362 (term207 _45312) (term213 _45312 _45313)). Qed.
Lemma lem3901870 (_45312 : int) (_45313 : int) : (term212 _45312 _45313) = (term211 _45312 _45313).
Proof. exact (TRANS (@lem3901856 _45312 _45313) (@lem3901855 _45312 _45313)). Qed.
Lemma lem3901873 (x : int) (y : int) : (int_le x y) = (term214 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3901874 (_45312 : int) : (term207 _45312) = (term215 _45312).
Proof. exact (@lem3901873 term216 _45312). Qed.
Lemma lem3901876 (n : nat) : (term217 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3901877 : term218 = term219.
Proof. exact (@lem3901876 (NUMERAL 0)). Qed.
Lemma lem3901878 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3901879 : term220 = term221.
Proof. exact (MK_COMB (@lem3901878) (@lem3901877)). Qed.
Lemma lem3901880 (_45312 : int) : (real_of_int _45312) = (real_of_int _45312).
Proof. exact (eq_refl (real_of_int _45312)). Qed.
Lemma lem3901881 (_45312 : int) : (term215 _45312) = (term222 _45312).
Proof. exact (MK_COMB (@lem3901879) (@lem3901880 _45312)). Qed.
Lemma lem3901883 (_45312 : int) : (term207 _45312) = (term222 _45312).
Proof. exact (TRANS (@lem3901874 _45312) (@lem3901881 _45312)). Qed.
Lemma lem3901886 (x : int) (y : int) : (int_le x y) = (term214 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3901887 (_45313 : int) : (term207 _45313) = (term215 _45313).
Proof. exact (@lem3901886 term216 _45313). Qed.
Lemma lem3901889 (n : nat) : (term217 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3901890 : term218 = term219.
Proof. exact (@lem3901889 (NUMERAL 0)). Qed.
Lemma lem3901891 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3901892 : term220 = term221.
Proof. exact (MK_COMB (@lem3901891) (@lem3901890)). Qed.
Lemma lem3901893 (_45313 : int) : (real_of_int _45313) = (real_of_int _45313).
Proof. exact (eq_refl (real_of_int _45313)). Qed.
Lemma lem3901894 (_45313 : int) : (term215 _45313) = (term222 _45313).
Proof. exact (MK_COMB (@lem3901892) (@lem3901893 _45313)). Qed.
Lemma lem3901896 (_45313 : int) : (term207 _45313) = (term222 _45313).
Proof. exact (TRANS (@lem3901887 _45313) (@lem3901894 _45313)). Qed.
Lemma lem3901898 (y : int) (x : int) : (term223 x y) = (term224 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem3901899 (_45313 : int) (_45312 : int) : (term225 _45312 _45313) = (term226 _45313 _45312).
Proof. exact (@lem3901898 (int_add _45312 _45313) _45312). Qed.
Lemma lem3901901 (x : int) (y : int) : (int_le x y) = (term214 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3901902 (_45313 : int) (_45312 : int) : (term226 _45313 _45312) = (term227 _45313 _45312).
Proof. exact (@lem3901901 (term228 _45312 _45313) _45312). Qed.
Lemma lem3901904 (x : int) (y : int) : (term229 x y) = (term230 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3901905 (_45312 : int) (_45313 : int) : (term231 _45312 _45313) = (term232 _45312 _45313).
Proof. exact (@lem3901904 (int_add _45312 _45313) term233). Qed.
Lemma lem3901907 (x : int) (y : int) : (term229 x y) = (term230 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3901908 (_45312 : int) (_45313 : int) : (term229 _45312 _45313) = (term230 _45312 _45313).
Proof. exact (@lem3901907 _45312 _45313). Qed.
Lemma lem3901909 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3901910 (_45312 : int) (_45313 : int) : (term234 _45312 _45313) = (term235 _45312 _45313).
Proof. exact (MK_COMB (@lem3901909) (@lem3901908 _45312 _45313)). Qed.
Lemma lem3901912 (n : nat) : (term217 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3901913 : term236 = term237.
Proof. exact (@lem3901912 term238). Qed.
Lemma lem3901914 (_45312 : int) (_45313 : int) : (term232 _45312 _45313) = (term239 _45312 _45313).
Proof. exact (MK_COMB (@lem3901910 _45312 _45313) (@lem3901913)). Qed.
Lemma lem3901915 (_45312 : int) (_45313 : int) : (term231 _45312 _45313) = (term239 _45312 _45313).
Proof. exact (TRANS (@lem3901905 _45312 _45313) (@lem3901914 _45312 _45313)). Qed.
Lemma lem3901916 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3901917 (_45312 : int) (_45313 : int) : (term240 _45312 _45313) = (term241 _45312 _45313).
Proof. exact (MK_COMB (@lem3901916) (@lem3901915 _45312 _45313)). Qed.
Lemma lem3901918 (_45312 : int) : (real_of_int _45312) = (real_of_int _45312).
Proof. exact (eq_refl (real_of_int _45312)). Qed.
Lemma lem3901919 (_45313 : int) (_45312 : int) : (term227 _45313 _45312) = (term242 _45313 _45312).
Proof. exact (MK_COMB (@lem3901917 _45312 _45313) (@lem3901918 _45312)). Qed.
Lemma lem3901920 (_45313 : int) (_45312 : int) : (term226 _45313 _45312) = (term242 _45313 _45312).
Proof. exact (TRANS (@lem3901902 _45313 _45312) (@lem3901919 _45313 _45312)). Qed.
Lemma lem3901921 (_45313 : int) (_45312 : int) : (term225 _45312 _45313) = (term242 _45313 _45312).
Proof. exact (TRANS (@lem3901899 _45313 _45312) (@lem3901920 _45313 _45312)). Qed.
Lemma lem3901922 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3901923 (_45313 : int) : (term209 _45313) = (term243 _45313).
Proof. exact (MK_COMB (@lem3901922) (@lem3901896 _45313)). Qed.
Lemma lem3901924 (_45313 : int) (_45312 : int) : (term206 _45312 _45313) = (term244 _45313 _45312).
Proof. exact (MK_COMB (@lem3901923 _45313) (@lem3901921 _45313 _45312)). Qed.
Lemma lem3901925 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3901926 (_45312 : int) : (term209 _45312) = (term243 _45312).
Proof. exact (MK_COMB (@lem3901925) (@lem3901883 _45312)). Qed.
Lemma lem3901927 (_45313 : int) (_45312 : int) : (term211 _45312 _45313) = (term245 _45313 _45312).
Proof. exact (MK_COMB (@lem3901926 _45312) (@lem3901924 _45313 _45312)). Qed.
Lemma lem3901928 (_45313 : int) (_45312 : int) : (term212 _45312 _45313) = (term245 _45313 _45312).
Proof. exact (TRANS (@lem3901870 _45312 _45313) (@lem3901927 _45313 _45312)). Qed.
Lemma lem3901932 (t : Prop) : (term74 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3901958 (_45313 : int) (_45312 : int) : (term246 _45313 _45312) = (term245 _45313 _45312).
Proof. exact (@lem3901932 (term245 _45313 _45312)). Qed.
Lemma lem3901959 (_45312 : int) : (term222 _45312) = (term247 _45312).
Proof. exact (@lem1988287 (real_of_int _45312) term219). Qed.
Lemma lem3901965 (_45312 : int) : (term248 _45312) = (term249 _45312).
Proof. exact (@lem1982792 (real_of_int _45312) term219). Qed.
Lemma lem3901967 (x : nat) : (real_of_num x) = (term250 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3901968 : term219 = term251.
Proof. exact (@lem3901967 (NUMERAL 0)). Qed.
Lemma lem3901970 (x : nat) : (term252 x) = (term253 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3901971 : term254 = term255.
Proof. exact (@lem3901970 term238). Qed.
Lemma lem3901972 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3901973 : term256 = term257.
Proof. exact (MK_COMB (@lem3901972) (@lem3901971)). Qed.
Lemma lem3901974 : term258 = term259.
Proof. exact (MK_COMB (@lem3901973) (@lem3901968)). Qed.
Lemma lem3901975 : term259 = term260.
Proof. exact (@lem1981613 term254 term219 term237 term237). Qed.
Lemma lem3901977 (m : nat) (n : nat) : (term261 m n) = (term262 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3901978 : term263 = term264.
Proof. exact (@lem3901977 term238 term238). Qed.
Lemma lem3901979 : (term265 = (BIT1 0)) = (term266 = term238).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3901980 : term266 = term238.
Proof. exact (EQ_MP (@lem3901979) (@lem940073)). Qed.
Lemma lem3901981 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3901982 : term264 = term237.
Proof. exact (MK_COMB (@lem3901981) (@lem3901980)). Qed.
Lemma lem3901983 : term263 = term237.
Proof. exact (TRANS (@lem3901978) (@lem3901982)). Qed.
Lemma lem3901985 (x : nat) : (term267 x) = term219.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem3901986 : term258 = term219.
Proof. exact (@lem3901985 term238). Qed.
Lemma lem3901987 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3901988 : term268 = term269.
Proof. exact (MK_COMB (@lem3901987) (@lem3901986)). Qed.
Lemma lem3901989 : term260 = term251.
Proof. exact (MK_COMB (@lem3901988) (@lem3901983)). Qed.
Lemma lem3901990 : term259 = term251.
Proof. exact (TRANS (@lem3901975) (@lem3901989)). Qed.
Lemma lem3901991 : term258 = term251.
Proof. exact (TRANS (@lem3901974) (@lem3901990)). Qed.
Lemma lem3901993 (x : real) : (term270 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3901994 : term251 = term219.
Proof. exact (@lem3901993 term219). Qed.
Lemma lem3901995 : term258 = term219.
Proof. exact (TRANS (@lem3901991) (@lem3901994)). Qed.
Lemma lem3901996 (_45312 : int) : (term271 _45312) = (term271 _45312).
Proof. exact (eq_refl (term271 _45312)). Qed.
Lemma lem3901997 (_45312 : int) : (term249 _45312) = (term272 _45312).
Proof. exact (MK_COMB (@lem3901996 _45312) (@lem3901995)). Qed.
Lemma lem3901998 (_45312 : int) : (term272 _45312) = (real_of_int _45312).
Proof. exact (@lem1982723 (real_of_int _45312)). Qed.
Lemma lem3901999 (_45312 : int) : (term249 _45312) = (real_of_int _45312).
Proof. exact (TRANS (@lem3901997 _45312) (@lem3901998 _45312)). Qed.
Lemma lem3902001 (_45312 : int) : (term248 _45312) = (real_of_int _45312).
Proof. exact (TRANS (@lem3901965 _45312) (@lem3901999 _45312)). Qed.
Lemma lem3902002 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3902003 (_45312 : int) : (term273 _45312) = (term274 _45312).
Proof. exact (MK_COMB (@lem3902002) (@lem3902001 _45312)). Qed.
Lemma lem3902004 : term219 = term219.
Proof. exact (eq_refl term219). Qed.
Lemma lem3902005 (_45312 : int) : (term247 _45312) = (term275 _45312).
Proof. exact (MK_COMB (@lem3902003 _45312) (@lem3902004)). Qed.
Lemma lem3902006 (_45312 : int) : (term222 _45312) = (term275 _45312).
Proof. exact (TRANS (@lem3901959 _45312) (@lem3902005 _45312)). Qed.
Lemma lem3902007 (_45313 : int) : (term222 _45313) = (term247 _45313).
Proof. exact (@lem1988287 (real_of_int _45313) term219). Qed.
Lemma lem3902013 (_45313 : int) : (term248 _45313) = (term249 _45313).
Proof. exact (@lem1982792 (real_of_int _45313) term219). Qed.
Lemma lem3902015 (x : nat) : (real_of_num x) = (term250 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3902016 : term219 = term251.
Proof. exact (@lem3902015 (NUMERAL 0)). Qed.
Lemma lem3902018 (x : nat) : (term252 x) = (term253 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3902019 : term254 = term255.
Proof. exact (@lem3902018 term238). Qed.
Lemma lem3902020 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3902021 : term256 = term257.
Proof. exact (MK_COMB (@lem3902020) (@lem3902019)). Qed.
Lemma lem3902022 : term258 = term259.
Proof. exact (MK_COMB (@lem3902021) (@lem3902016)). Qed.
Lemma lem3902023 : term259 = term260.
Proof. exact (@lem1981613 term254 term219 term237 term237). Qed.
Lemma lem3902025 (m : nat) (n : nat) : (term261 m n) = (term262 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3902026 : term263 = term264.
Proof. exact (@lem3902025 term238 term238). Qed.
Lemma lem3902027 : (term265 = (BIT1 0)) = (term266 = term238).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3902028 : term266 = term238.
Proof. exact (EQ_MP (@lem3902027) (@lem940073)). Qed.
Lemma lem3902029 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3902030 : term264 = term237.
Proof. exact (MK_COMB (@lem3902029) (@lem3902028)). Qed.
Lemma lem3902031 : term263 = term237.
Proof. exact (TRANS (@lem3902026) (@lem3902030)). Qed.
Lemma lem3902033 (x : nat) : (term267 x) = term219.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem3902034 : term258 = term219.
Proof. exact (@lem3902033 term238). Qed.
Lemma lem3902035 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3902036 : term268 = term269.
Proof. exact (MK_COMB (@lem3902035) (@lem3902034)). Qed.
Lemma lem3902037 : term260 = term251.
Proof. exact (MK_COMB (@lem3902036) (@lem3902031)). Qed.
Lemma lem3902038 : term259 = term251.
Proof. exact (TRANS (@lem3902023) (@lem3902037)). Qed.
Lemma lem3902039 : term258 = term251.
Proof. exact (TRANS (@lem3902022) (@lem3902038)). Qed.
Lemma lem3902041 (x : real) : (term270 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3902042 : term251 = term219.
Proof. exact (@lem3902041 term219). Qed.
Lemma lem3902043 : term258 = term219.
Proof. exact (TRANS (@lem3902039) (@lem3902042)). Qed.
Lemma lem3902044 (_45313 : int) : (term271 _45313) = (term271 _45313).
Proof. exact (eq_refl (term271 _45313)). Qed.
Lemma lem3902045 (_45313 : int) : (term249 _45313) = (term272 _45313).
Proof. exact (MK_COMB (@lem3902044 _45313) (@lem3902043)). Qed.
Lemma lem3902046 (_45313 : int) : (term272 _45313) = (real_of_int _45313).
Proof. exact (@lem1982723 (real_of_int _45313)). Qed.
Lemma lem3902047 (_45313 : int) : (term249 _45313) = (real_of_int _45313).
Proof. exact (TRANS (@lem3902045 _45313) (@lem3902046 _45313)). Qed.
Lemma lem3902049 (_45313 : int) : (term248 _45313) = (real_of_int _45313).
Proof. exact (TRANS (@lem3902013 _45313) (@lem3902047 _45313)). Qed.
Lemma lem3902050 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3902051 (_45313 : int) : (term273 _45313) = (term274 _45313).
Proof. exact (MK_COMB (@lem3902050) (@lem3902049 _45313)). Qed.
Lemma lem3902052 : term219 = term219.
Proof. exact (eq_refl term219). Qed.
Lemma lem3902053 (_45313 : int) : (term247 _45313) = (term275 _45313).
Proof. exact (MK_COMB (@lem3902051 _45313) (@lem3902052)). Qed.
Lemma lem3902054 (_45313 : int) : (term222 _45313) = (term275 _45313).
Proof. exact (TRANS (@lem3902007 _45313) (@lem3902053 _45313)). Qed.
Lemma lem3902055 (_45312 : int) (_45313 : int) : (term242 _45313 _45312) = (term276 _45312 _45313).
Proof. exact (@lem1988287 (real_of_int _45312) (term239 _45312 _45313)). Qed.
Lemma lem3902072 (_45312 : int) (_45313 : int) : (term239 _45312 _45313) = (term277 _45312 _45313).
Proof. exact (@lem1982755 (real_of_int _45312) (real_of_int _45313) term237). Qed.
Lemma lem3902075 (_45312 : int) : (term278 _45312) = (term278 _45312).
Proof. exact (eq_refl (term278 _45312)). Qed.
Lemma lem3902076 (_45312 : int) (_45313 : int) : (term279 _45312 _45313) = (term280 _45312 _45313).
Proof. exact (MK_COMB (@lem3902075 _45312) (@lem3902072 _45312 _45313)). Qed.
Lemma lem3902077 (_45312 : int) (_45313 : int) : (term280 _45312 _45313) = (term281 _45312 _45313).
Proof. exact (@lem1982792 (real_of_int _45312) (term277 _45312 _45313)). Qed.
Lemma lem3902078 (_45312 : int) (_45313 : int) : (term282 _45312 _45313) = (term283 _45312 _45313).
Proof. exact (@lem1982781 (real_of_int _45312) term254 (term284 _45313)). Qed.
Lemma lem3902079 (_45313 : int) : (term285 _45313) = (term286 _45313).
Proof. exact (@lem1982781 (real_of_int _45313) term254 term237). Qed.
Lemma lem3902081 (x : nat) : (real_of_num x) = (term250 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3902082 : term237 = term287.
Proof. exact (@lem3902081 term238). Qed.
Lemma lem3902084 (x : nat) : (term252 x) = (term253 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3902085 : term254 = term255.
Proof. exact (@lem3902084 term238). Qed.
Lemma lem3902086 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3902087 : term256 = term257.
Proof. exact (MK_COMB (@lem3902086) (@lem3902085)). Qed.
Lemma lem3902088 : term288 = term289.
Proof. exact (MK_COMB (@lem3902087) (@lem3902082)). Qed.
Lemma lem3902089 : term289 = term290.
Proof. exact (@lem1981613 term254 term237 term237 term237). Qed.
Lemma lem3902091 (m : nat) (n : nat) : (term261 m n) = (term262 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3902092 : term263 = term264.
Proof. exact (@lem3902091 term238 term238). Qed.
Lemma lem3902093 : (term265 = (BIT1 0)) = (term266 = term238).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3902094 : term266 = term238.
Proof. exact (EQ_MP (@lem3902093) (@lem940073)). Qed.
Lemma lem3902095 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3902096 : term264 = term237.
Proof. exact (MK_COMB (@lem3902095) (@lem3902094)). Qed.
Lemma lem3902097 : term263 = term237.
Proof. exact (TRANS (@lem3902092) (@lem3902096)). Qed.
Lemma lem3902099 (m : nat) (n : nat) : (term291 m n) = (term292 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3902100 : term288 = term293.
Proof. exact (@lem3902099 term238 term238). Qed.
Lemma lem3902101 : (term265 = (BIT1 0)) = (term266 = term238).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3902102 : term266 = term238.
Proof. exact (EQ_MP (@lem3902101) (@lem940073)). Qed.
Lemma lem3902103 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3902104 : term264 = term237.
Proof. exact (MK_COMB (@lem3902103) (@lem3902102)). Qed.
Lemma lem3902105 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3902106 : term293 = term254.
Proof. exact (MK_COMB (@lem3902105) (@lem3902104)). Qed.
Lemma lem3902107 : term288 = term254.
Proof. exact (TRANS (@lem3902100) (@lem3902106)). Qed.
Lemma lem3902108 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3902109 : term294 = term295.
Proof. exact (MK_COMB (@lem3902108) (@lem3902107)). Qed.
Lemma lem3902110 : term290 = term255.
Proof. exact (MK_COMB (@lem3902109) (@lem3902097)). Qed.
Lemma lem3902111 : term289 = term255.
Proof. exact (TRANS (@lem3902089) (@lem3902110)). Qed.
Lemma lem3902112 : term288 = term255.
Proof. exact (TRANS (@lem3902088) (@lem3902111)). Qed.
Lemma lem3902114 (x : real) : (term270 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3902115 : term255 = term254.
Proof. exact (@lem3902114 term254). Qed.
Lemma lem3902116 : term288 = term254.
Proof. exact (TRANS (@lem3902112) (@lem3902115)). Qed.
Lemma lem3902119 (_45313 : int) : (term296 _45313) = (term296 _45313).
Proof. exact (eq_refl (term296 _45313)). Qed.
Lemma lem3902120 (_45313 : int) : (term286 _45313) = (term297 _45313).
Proof. exact (MK_COMB (@lem3902119 _45313) (@lem3902116)). Qed.
Lemma lem3902121 (_45313 : int) : (term285 _45313) = (term297 _45313).
Proof. exact (TRANS (@lem3902079 _45313) (@lem3902120 _45313)). Qed.
Lemma lem3902124 (_45312 : int) : (term296 _45312) = (term296 _45312).
Proof. exact (eq_refl (term296 _45312)). Qed.
Lemma lem3902125 (_45312 : int) (_45313 : int) : (term283 _45312 _45313) = (term298 _45312 _45313).
Proof. exact (MK_COMB (@lem3902124 _45312) (@lem3902121 _45313)). Qed.
Lemma lem3902126 (_45312 : int) (_45313 : int) : (term282 _45312 _45313) = (term298 _45312 _45313).
Proof. exact (TRANS (@lem3902078 _45312 _45313) (@lem3902125 _45312 _45313)). Qed.
Lemma lem3902127 (_45312 : int) : (term271 _45312) = (term271 _45312).
Proof. exact (eq_refl (term271 _45312)). Qed.
Lemma lem3902128 (_45312 : int) (_45313 : int) : (term281 _45312 _45313) = (term299 _45312 _45313).
Proof. exact (MK_COMB (@lem3902127 _45312) (@lem3902126 _45312 _45313)). Qed.
Lemma lem3902129 (_45312 : int) (_45313 : int) : (term299 _45312 _45313) = (term300 _45312 _45313).
Proof. exact (@lem1982763 (real_of_int _45312) (term301 _45312) (term297 _45313)). Qed.
Lemma lem3902130 (_45312 : int) : (term302 _45312) = (term303 _45312).
Proof. exact (@lem1982715 term254 (real_of_int _45312)). Qed.
Lemma lem3902132 (x : nat) : (real_of_num x) = (term250 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3902133 : term237 = term287.
Proof. exact (@lem3902132 term238). Qed.
Lemma lem3902135 (x : nat) : (term252 x) = (term253 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3902136 : term254 = term255.
Proof. exact (@lem3902135 term238). Qed.
Lemma lem3902137 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3902138 : term304 = term305.
Proof. exact (MK_COMB (@lem3902137) (@lem3902136)). Qed.
Lemma lem3902139 : term306 = term307.
Proof. exact (MK_COMB (@lem3902138) (@lem3902133)). Qed.
Lemma lem3902140 : term308.
Proof. exact (@lem1981473 term254 term237 term237 term237 term219 term237). Qed.
Lemma lem3902142 (m : nat) (n : nat) : (term309 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3902143 : term310 = term311.
Proof. exact (@lem3902142 (NUMERAL 0) term238). Qed.
Lemma lem3902144 : term312 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3902145 (h1 : term312 = (BIT1 0)) : term311 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3902146 : (term312 = (BIT1 0)) = (term311 = True).
Proof. exact (prop_ext (fun h1 : term312 = (BIT1 0) => @lem3902145 h1) (fun h1 : term311 = True => @lem3902144)). Qed.
Lemma lem3902147 : term311 = True.
Proof. exact (EQ_MP (@lem3902146) (@lem3902144)). Qed.
Lemma lem3902148 : term310 = True.
Proof. exact (TRANS (@lem3902143) (@lem3902147)). Qed.
Lemma lem3902149 : True = term310.
Proof. exact (SYM (@lem3902148)). Qed.
Lemma lem3902150 : term310.
Proof. exact (EQ_MP (@lem3902149) (@lem0)). Qed.
Lemma lem3902151 : term313.
Proof. exact (@lem3902140 (@lem3902150)). Qed.
Lemma lem3902153 (m : nat) (n : nat) : (term309 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3902154 : term310 = term311.
Proof. exact (@lem3902153 (NUMERAL 0) term238). Qed.
Lemma lem3902155 : term312 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3902156 (h1 : term312 = (BIT1 0)) : term311 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3902157 : (term312 = (BIT1 0)) = (term311 = True).
Proof. exact (prop_ext (fun h1 : term312 = (BIT1 0) => @lem3902156 h1) (fun h1 : term311 = True => @lem3902155)). Qed.
Lemma lem3902158 : term311 = True.
Proof. exact (EQ_MP (@lem3902157) (@lem3902155)). Qed.
Lemma lem3902159 : term310 = True.
Proof. exact (TRANS (@lem3902154) (@lem3902158)). Qed.
Lemma lem3902160 : True = term310.
Proof. exact (SYM (@lem3902159)). Qed.
Lemma lem3902161 : term310.
Proof. exact (EQ_MP (@lem3902160) (@lem0)). Qed.
Lemma lem3902162 : term314.
Proof. exact (@lem3902151 (@lem3902161)). Qed.
Lemma lem3902164 (m : nat) (n : nat) : (term309 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3902165 : term310 = term311.
Proof. exact (@lem3902164 (NUMERAL 0) term238). Qed.
Lemma lem3902166 : term312 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3902167 (h1 : term312 = (BIT1 0)) : term311 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3902168 : (term312 = (BIT1 0)) = (term311 = True).
Proof. exact (prop_ext (fun h1 : term312 = (BIT1 0) => @lem3902167 h1) (fun h1 : term311 = True => @lem3902166)). Qed.
Lemma lem3902169 : term311 = True.
Proof. exact (EQ_MP (@lem3902168) (@lem3902166)). Qed.
Lemma lem3902170 : term310 = True.
Proof. exact (TRANS (@lem3902165) (@lem3902169)). Qed.
Lemma lem3902171 : True = term310.
Proof. exact (SYM (@lem3902170)). Qed.
Lemma lem3902172 : term310.
Proof. exact (EQ_MP (@lem3902171) (@lem0)). Qed.
Lemma lem3902173 : term315.
Proof. exact (@lem3902162 (@lem3902172)). Qed.
Lemma lem3902175 (m : nat) (n : nat) : (term261 m n) = (term262 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3902176 : term263 = term264.
Proof. exact (@lem3902175 term238 term238). Qed.
Lemma lem3902177 : (term265 = (BIT1 0)) = (term266 = term238).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3902178 : term266 = term238.
Proof. exact (EQ_MP (@lem3902177) (@lem940073)). Qed.
Lemma lem3902179 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3902180 : term264 = term237.
Proof. exact (MK_COMB (@lem3902179) (@lem3902178)). Qed.
Lemma lem3902181 : term263 = term237.
Proof. exact (TRANS (@lem3902176) (@lem3902180)). Qed.
Lemma lem3902183 (m : nat) (n : nat) : (term291 m n) = (term292 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3902184 : term288 = term293.
Proof. exact (@lem3902183 term238 term238). Qed.
Lemma lem3902185 : (term265 = (BIT1 0)) = (term266 = term238).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3902186 : term266 = term238.
Proof. exact (EQ_MP (@lem3902185) (@lem940073)). Qed.
Lemma lem3902187 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3902188 : term264 = term237.
Proof. exact (MK_COMB (@lem3902187) (@lem3902186)). Qed.
Lemma lem3902189 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3902190 : term293 = term254.
Proof. exact (MK_COMB (@lem3902189) (@lem3902188)). Qed.
Lemma lem3902191 : term288 = term254.
Proof. exact (TRANS (@lem3902184) (@lem3902190)). Qed.
Lemma lem3902192 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3902193 : term316 = term304.
Proof. exact (MK_COMB (@lem3902192) (@lem3902191)). Qed.
Lemma lem3902194 : term317 = term306.
Proof. exact (MK_COMB (@lem3902193) (@lem3902181)). Qed.
Lemma lem3902196 (m : nat) : (term318 m) = term219.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3902197 : term306 = term219.
Proof. exact (@lem3902196 term238). Qed.
Lemma lem3902198 : term317 = term219.
Proof. exact (TRANS (@lem3902194) (@lem3902197)). Qed.
Lemma lem3902199 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3902200 : term319 = term320.
Proof. exact (MK_COMB (@lem3902199) (@lem3902198)). Qed.
Lemma lem3902201 : term237 = term237.
Proof. exact (eq_refl term237). Qed.
Lemma lem3902202 : term321 = term322.
Proof. exact (MK_COMB (@lem3902200) (@lem3902201)). Qed.
Lemma lem3902204 (x : nat) : (term323 x) = term219.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3902205 : term322 = term219.
Proof. exact (@lem3902204 term238). Qed.
Lemma lem3902206 : term321 = term219.
Proof. exact (TRANS (@lem3902202) (@lem3902205)). Qed.
Lemma lem3902208 (m : nat) (n : nat) : (term261 m n) = (term262 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3902209 : term263 = term264.
Proof. exact (@lem3902208 term238 term238). Qed.
Lemma lem3902210 : (term265 = (BIT1 0)) = (term266 = term238).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3902211 : term266 = term238.
Proof. exact (EQ_MP (@lem3902210) (@lem940073)). Qed.
Lemma lem3902212 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3902213 : term264 = term237.
Proof. exact (MK_COMB (@lem3902212) (@lem3902211)). Qed.
Lemma lem3902214 : term263 = term237.
Proof. exact (TRANS (@lem3902209) (@lem3902213)). Qed.
Lemma lem3902215 : term320 = term320.
Proof. exact (eq_refl term320). Qed.
Lemma lem3902216 : term324 = term322.
Proof. exact (MK_COMB (@lem3902215) (@lem3902214)). Qed.
Lemma lem3902218 (x : nat) : (term323 x) = term219.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3902219 : term322 = term219.
Proof. exact (@lem3902218 term238). Qed.
Lemma lem3902220 : term324 = term219.
Proof. exact (TRANS (@lem3902216) (@lem3902219)). Qed.
Lemma lem3902221 : term219 = term324.
Proof. exact (SYM (@lem3902220)). Qed.
Lemma lem3902222 : term321 = term324.
Proof. exact (TRANS (@lem3902206) (@lem3902221)). Qed.
Lemma lem3902223 : term307 = term251.
Proof. exact (@lem3902173 (@lem3902222)). Qed.
Lemma lem3902224 : term306 = term251.
Proof. exact (TRANS (@lem3902139) (@lem3902223)). Qed.
Lemma lem3902226 (x : real) : (term270 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3902227 : term251 = term219.
Proof. exact (@lem3902226 term219). Qed.
Lemma lem3902228 : term306 = term219.
Proof. exact (TRANS (@lem3902224) (@lem3902227)). Qed.
Lemma lem3902229 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3902230 : term325 = term320.
Proof. exact (MK_COMB (@lem3902229) (@lem3902228)). Qed.
Lemma lem3902231 (_45312 : int) : (real_of_int _45312) = (real_of_int _45312).
Proof. exact (eq_refl (real_of_int _45312)). Qed.
Lemma lem3902232 (_45312 : int) : (term303 _45312) = (term326 _45312).
Proof. exact (MK_COMB (@lem3902230) (@lem3902231 _45312)). Qed.
Lemma lem3902233 (_45312 : int) : (term302 _45312) = (term326 _45312).
Proof. exact (TRANS (@lem3902130 _45312) (@lem3902232 _45312)). Qed.
Lemma lem3902234 (_45312 : int) : (term326 _45312) = term219.
Proof. exact (@lem1982719 (real_of_int _45312)). Qed.
Lemma lem3902235 (_45312 : int) : (term302 _45312) = term219.
Proof. exact (TRANS (@lem3902233 _45312) (@lem3902234 _45312)). Qed.
Lemma lem3902236 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3902237 (_45312 : int) : (term327 _45312) = term328.
Proof. exact (MK_COMB (@lem3902236) (@lem3902235 _45312)). Qed.
Lemma lem3902238 (_45313 : int) : (term297 _45313) = (term297 _45313).
Proof. exact (eq_refl (term297 _45313)). Qed.
Lemma lem3902239 (_45312 : int) (_45313 : int) : (term300 _45312 _45313) = (term329 _45313).
Proof. exact (MK_COMB (@lem3902237 _45312) (@lem3902238 _45313)). Qed.
Lemma lem3902240 (_45312 : int) (_45313 : int) : (term299 _45312 _45313) = (term329 _45313).
Proof. exact (TRANS (@lem3902129 _45312 _45313) (@lem3902239 _45312 _45313)). Qed.
Lemma lem3902241 (_45313 : int) : (term329 _45313) = (term297 _45313).
Proof. exact (@lem1982721 (term297 _45313)). Qed.
Lemma lem3902242 (_45312 : int) (_45313 : int) : (term299 _45312 _45313) = (term297 _45313).
Proof. exact (TRANS (@lem3902240 _45312 _45313) (@lem3902241 _45313)). Qed.
Lemma lem3902243 (_45312 : int) (_45313 : int) : (term281 _45312 _45313) = (term297 _45313).
Proof. exact (TRANS (@lem3902128 _45312 _45313) (@lem3902242 _45312 _45313)). Qed.
Lemma lem3902244 (_45312 : int) (_45313 : int) : (term280 _45312 _45313) = (term297 _45313).
Proof. exact (TRANS (@lem3902077 _45312 _45313) (@lem3902243 _45312 _45313)). Qed.
Lemma lem3902245 (_45312 : int) (_45313 : int) : (term279 _45312 _45313) = (term297 _45313).
Proof. exact (TRANS (@lem3902076 _45312 _45313) (@lem3902244 _45312 _45313)). Qed.
Lemma lem3902246 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3902247 (_45312 : int) (_45313 : int) : (term330 _45312 _45313) = (term331 _45313).
Proof. exact (MK_COMB (@lem3902246) (@lem3902245 _45312 _45313)). Qed.
Lemma lem3902248 : term219 = term219.
Proof. exact (eq_refl term219). Qed.
Lemma lem3902249 (_45312 : int) (_45313 : int) : (term276 _45312 _45313) = (term332 _45313).
Proof. exact (MK_COMB (@lem3902247 _45312 _45313) (@lem3902248)). Qed.
Lemma lem3902250 (_45312 : int) (_45313 : int) : (term242 _45313 _45312) = (term332 _45313).
Proof. exact (TRANS (@lem3902055 _45312 _45313) (@lem3902249 _45312 _45313)). Qed.
Lemma lem3902251 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3902252 (_45313 : int) : (term243 _45313) = (term333 _45313).
Proof. exact (MK_COMB (@lem3902251) (@lem3902054 _45313)). Qed.
Lemma lem3902253 (_45312 : int) (_45313 : int) : (term244 _45313 _45312) = (term334 _45313).
Proof. exact (MK_COMB (@lem3902252 _45313) (@lem3902250 _45312 _45313)). Qed.
Lemma lem3902254 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3902255 (_45312 : int) : (term243 _45312) = (term333 _45312).
Proof. exact (MK_COMB (@lem3902254) (@lem3902006 _45312)). Qed.
Lemma lem3902256 (_45312 : int) (_45313 : int) : (term245 _45313 _45312) = (term335 _45312 _45313).
Proof. exact (MK_COMB (@lem3902255 _45312) (@lem3902253 _45312 _45313)). Qed.
Lemma lem3902277 (_45312 : int) (_45313 : int) : (term246 _45313 _45312) = (term335 _45312 _45313).
Proof. exact (TRANS (@lem3901958 _45313 _45312) (@lem3902256 _45312 _45313)). Qed.
Lemma lem3902281 (_45312 : int) (_45313 : int) (h1 : term335 _45312 _45313) : term335 _45312 _45313.
Proof. exact (h1). Qed.
Lemma lem3902282 (_45312 : int) (_45313 : int) (h1 : term335 _45312 _45313) : term334 _45313.
Proof. exact (proj2 (@lem3902281 _45312 _45313 h1)). Qed.
Lemma lem3902284 (_45312 : int) (_45313 : int) (h1 : term335 _45312 _45313) : term332 _45313.
Proof. exact (proj2 (@lem3902282 _45312 _45313 h1)). Qed.
Lemma lem3902285 (_45312 : int) (_45313 : int) (h1 : term335 _45312 _45313) : term275 _45313.
Proof. exact (proj1 (@lem3902282 _45312 _45313 h1)). Qed.
Lemma lem3902287 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3902288 : term336 = term310.
Proof. exact (@lem3902287 term219 term237). Qed.
Lemma lem3902290 (x : nat) : (real_of_num x) = (term250 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3902291 : term237 = term287.
Proof. exact (@lem3902290 term238). Qed.
Lemma lem3902293 (x : nat) : (real_of_num x) = (term250 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3902294 : term219 = term251.
Proof. exact (@lem3902293 (NUMERAL 0)). Qed.
Lemma lem3902295 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3902296 : term337 = term338.
Proof. exact (MK_COMB (@lem3902295) (@lem3902294)). Qed.
Lemma lem3902297 : term310 = term339.
Proof. exact (MK_COMB (@lem3902296) (@lem3902291)). Qed.
Lemma lem3902298 : term340.
Proof. exact (@lem1980255 term219 term237 term237 term237). Qed.
Lemma lem3902300 (m : nat) (n : nat) : (term309 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3902301 : term310 = term311.
Proof. exact (@lem3902300 (NUMERAL 0) term238). Qed.
Lemma lem3902302 : term312 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3902303 (h1 : term312 = (BIT1 0)) : term311 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3902304 : (term312 = (BIT1 0)) = (term311 = True).
Proof. exact (prop_ext (fun h1 : term312 = (BIT1 0) => @lem3902303 h1) (fun h1 : term311 = True => @lem3902302)). Qed.
Lemma lem3902305 : term311 = True.
Proof. exact (EQ_MP (@lem3902304) (@lem3902302)). Qed.
Lemma lem3902306 : term310 = True.
Proof. exact (TRANS (@lem3902301) (@lem3902305)). Qed.
Lemma lem3902307 : True = term310.
Proof. exact (SYM (@lem3902306)). Qed.
Lemma lem3902308 : term310.
Proof. exact (EQ_MP (@lem3902307) (@lem0)). Qed.
Lemma lem3902309 : term341.
Proof. exact (@lem3902298 (@lem3902308)). Qed.
Lemma lem3902311 (m : nat) (n : nat) : (term309 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3902312 : term310 = term311.
Proof. exact (@lem3902311 (NUMERAL 0) term238). Qed.
Lemma lem3902313 : term312 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3902314 (h1 : term312 = (BIT1 0)) : term311 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3902315 : (term312 = (BIT1 0)) = (term311 = True).
Proof. exact (prop_ext (fun h1 : term312 = (BIT1 0) => @lem3902314 h1) (fun h1 : term311 = True => @lem3902313)). Qed.
Lemma lem3902316 : term311 = True.
Proof. exact (EQ_MP (@lem3902315) (@lem3902313)). Qed.
Lemma lem3902317 : term310 = True.
Proof. exact (TRANS (@lem3902312) (@lem3902316)). Qed.
Lemma lem3902318 : True = term310.
Proof. exact (SYM (@lem3902317)). Qed.
Lemma lem3902319 : term310.
Proof. exact (EQ_MP (@lem3902318) (@lem0)). Qed.
Lemma lem3902320 : term339 = term342.
Proof. exact (@lem3902309 (@lem3902319)). Qed.
Lemma lem3902322 (m : nat) (n : nat) : (term261 m n) = (term262 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3902323 : term263 = term264.
Proof. exact (@lem3902322 term238 term238). Qed.
Lemma lem3902324 : (term265 = (BIT1 0)) = (term266 = term238).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3902325 : term266 = term238.
Proof. exact (EQ_MP (@lem3902324) (@lem940073)). Qed.
Lemma lem3902326 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3902327 : term264 = term237.
Proof. exact (MK_COMB (@lem3902326) (@lem3902325)). Qed.
Lemma lem3902328 : term263 = term237.
Proof. exact (TRANS (@lem3902323) (@lem3902327)). Qed.
Lemma lem3902330 (x : nat) : (term323 x) = term219.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3902331 : term322 = term219.
Proof. exact (@lem3902330 term238). Qed.
Lemma lem3902332 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3902333 : term343 = term337.
Proof. exact (MK_COMB (@lem3902332) (@lem3902331)). Qed.
Lemma lem3902334 : term342 = term310.
Proof. exact (MK_COMB (@lem3902333) (@lem3902328)). Qed.
Lemma lem3902336 (m : nat) (n : nat) : (term309 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3902337 : term310 = term311.
Proof. exact (@lem3902336 (NUMERAL 0) term238). Qed.
Lemma lem3902338 : term312 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3902339 (h1 : term312 = (BIT1 0)) : term311 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3902340 : (term312 = (BIT1 0)) = (term311 = True).
Proof. exact (prop_ext (fun h1 : term312 = (BIT1 0) => @lem3902339 h1) (fun h1 : term311 = True => @lem3902338)). Qed.
Lemma lem3902341 : term311 = True.
Proof. exact (EQ_MP (@lem3902340) (@lem3902338)). Qed.
Lemma lem3902342 : term310 = True.
Proof. exact (TRANS (@lem3902337) (@lem3902341)). Qed.
Lemma lem3902343 : term342 = True.
Proof. exact (TRANS (@lem3902334) (@lem3902342)). Qed.
Lemma lem3902344 : term339 = True.
Proof. exact (TRANS (@lem3902320) (@lem3902343)). Qed.
Lemma lem3902345 : term310 = True.
Proof. exact (TRANS (@lem3902297) (@lem3902344)). Qed.
Lemma lem3902346 : term336 = True.
Proof. exact (TRANS (@lem3902288) (@lem3902345)). Qed.
Lemma lem3902347 : True = term336.
Proof. exact (SYM (@lem3902346)). Qed.
Lemma lem3902348 : term336.
Proof. exact (EQ_MP (@lem3902347) (@lem0)). Qed.
Lemma lem3902349 (_45312 : int) (_45313 : int) (h1 : term335 _45312 _45313) : term344 _45313.
Proof. exact (conj (@lem3902348) (@lem3902285 _45312 _45313 h1)). Qed.
Lemma lem3902351 (x : real) (y : real) : term345 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3902352 (_45313 : int) : term346 _45313.
Proof. exact (@lem3902351 term237 (real_of_int _45313)). Qed.
Lemma lem3902353 (_45312 : int) (_45313 : int) (h1 : term335 _45312 _45313) : term347 _45313.
Proof. exact (@lem3902352 _45313 (@lem3902349 _45312 _45313 h1)). Qed.
Lemma lem3902354 (_45313 : int) : (term348 _45313) = (real_of_int _45313).
Proof. exact (@lem1982733 (real_of_int _45313)). Qed.
Lemma lem3902355 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3902356 (_45313 : int) : (term349 _45313) = (term274 _45313).
Proof. exact (MK_COMB (@lem3902355) (@lem3902354 _45313)). Qed.
Lemma lem3902357 : term219 = term219.
Proof. exact (eq_refl term219). Qed.
Lemma lem3902358 (_45313 : int) : (term347 _45313) = (term275 _45313).
Proof. exact (MK_COMB (@lem3902356 _45313) (@lem3902357)). Qed.
Lemma lem3902359 (_45312 : int) (_45313 : int) (h1 : term335 _45312 _45313) : term275 _45313.
Proof. exact (EQ_MP (@lem3902358 _45313) (@lem3902353 _45312 _45313 h1)). Qed.
Lemma lem3902361 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3902362 : term336 = term310.
Proof. exact (@lem3902361 term219 term237). Qed.
Lemma lem3902364 (x : nat) : (real_of_num x) = (term250 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3902365 : term237 = term287.
Proof. exact (@lem3902364 term238). Qed.
Lemma lem3902367 (x : nat) : (real_of_num x) = (term250 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3902368 : term219 = term251.
Proof. exact (@lem3902367 (NUMERAL 0)). Qed.
Lemma lem3902369 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3902370 : term337 = term338.
Proof. exact (MK_COMB (@lem3902369) (@lem3902368)). Qed.
Lemma lem3902371 : term310 = term339.
Proof. exact (MK_COMB (@lem3902370) (@lem3902365)). Qed.
Lemma lem3902372 : term340.
Proof. exact (@lem1980255 term219 term237 term237 term237). Qed.
Lemma lem3902374 (m : nat) (n : nat) : (term309 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3902375 : term310 = term311.
Proof. exact (@lem3902374 (NUMERAL 0) term238). Qed.
Lemma lem3902376 : term312 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3902377 (h1 : term312 = (BIT1 0)) : term311 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3902378 : (term312 = (BIT1 0)) = (term311 = True).
Proof. exact (prop_ext (fun h1 : term312 = (BIT1 0) => @lem3902377 h1) (fun h1 : term311 = True => @lem3902376)). Qed.
Lemma lem3902379 : term311 = True.
Proof. exact (EQ_MP (@lem3902378) (@lem3902376)). Qed.
Lemma lem3902380 : term310 = True.
Proof. exact (TRANS (@lem3902375) (@lem3902379)). Qed.
Lemma lem3902381 : True = term310.
Proof. exact (SYM (@lem3902380)). Qed.
Lemma lem3902382 : term310.
Proof. exact (EQ_MP (@lem3902381) (@lem0)). Qed.
Lemma lem3902383 : term341.
Proof. exact (@lem3902372 (@lem3902382)). Qed.
Lemma lem3902385 (m : nat) (n : nat) : (term309 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3902386 : term310 = term311.
Proof. exact (@lem3902385 (NUMERAL 0) term238). Qed.
Lemma lem3902387 : term312 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3902388 (h1 : term312 = (BIT1 0)) : term311 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3902389 : (term312 = (BIT1 0)) = (term311 = True).
Proof. exact (prop_ext (fun h1 : term312 = (BIT1 0) => @lem3902388 h1) (fun h1 : term311 = True => @lem3902387)). Qed.
Lemma lem3902390 : term311 = True.
Proof. exact (EQ_MP (@lem3902389) (@lem3902387)). Qed.
Lemma lem3902391 : term310 = True.
Proof. exact (TRANS (@lem3902386) (@lem3902390)). Qed.
Lemma lem3902392 : True = term310.
Proof. exact (SYM (@lem3902391)). Qed.
Lemma lem3902393 : term310.
Proof. exact (EQ_MP (@lem3902392) (@lem0)). Qed.
Lemma lem3902394 : term339 = term342.
Proof. exact (@lem3902383 (@lem3902393)). Qed.
Lemma lem3902396 (m : nat) (n : nat) : (term261 m n) = (term262 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3902397 : term263 = term264.
Proof. exact (@lem3902396 term238 term238). Qed.
Lemma lem3902398 : (term265 = (BIT1 0)) = (term266 = term238).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3902399 : term266 = term238.
Proof. exact (EQ_MP (@lem3902398) (@lem940073)). Qed.
Lemma lem3902400 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3902401 : term264 = term237.
Proof. exact (MK_COMB (@lem3902400) (@lem3902399)). Qed.
Lemma lem3902402 : term263 = term237.
Proof. exact (TRANS (@lem3902397) (@lem3902401)). Qed.
Lemma lem3902404 (x : nat) : (term323 x) = term219.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3902405 : term322 = term219.
Proof. exact (@lem3902404 term238). Qed.
Lemma lem3902406 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3902407 : term343 = term337.
Proof. exact (MK_COMB (@lem3902406) (@lem3902405)). Qed.
Lemma lem3902408 : term342 = term310.
Proof. exact (MK_COMB (@lem3902407) (@lem3902402)). Qed.
Lemma lem3902410 (m : nat) (n : nat) : (term309 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3902411 : term310 = term311.
Proof. exact (@lem3902410 (NUMERAL 0) term238). Qed.
Lemma lem3902412 : term312 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3902413 (h1 : term312 = (BIT1 0)) : term311 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3902414 : (term312 = (BIT1 0)) = (term311 = True).
Proof. exact (prop_ext (fun h1 : term312 = (BIT1 0) => @lem3902413 h1) (fun h1 : term311 = True => @lem3902412)). Qed.
Lemma lem3902415 : term311 = True.
Proof. exact (EQ_MP (@lem3902414) (@lem3902412)). Qed.
Lemma lem3902416 : term310 = True.
Proof. exact (TRANS (@lem3902411) (@lem3902415)). Qed.
Lemma lem3902417 : term342 = True.
Proof. exact (TRANS (@lem3902408) (@lem3902416)). Qed.
Lemma lem3902418 : term339 = True.
Proof. exact (TRANS (@lem3902394) (@lem3902417)). Qed.
Lemma lem3902419 : term310 = True.
Proof. exact (TRANS (@lem3902371) (@lem3902418)). Qed.
Lemma lem3902420 : term336 = True.
Proof. exact (TRANS (@lem3902362) (@lem3902419)). Qed.
Lemma lem3902421 : True = term336.
Proof. exact (SYM (@lem3902420)). Qed.
Lemma lem3902422 : term336.
Proof. exact (EQ_MP (@lem3902421) (@lem0)). Qed.
Lemma lem3902423 (_45312 : int) (_45313 : int) (h1 : term335 _45312 _45313) : term350 _45313.
Proof. exact (conj (@lem3902422) (@lem3902284 _45312 _45313 h1)). Qed.
Lemma lem3902425 (x : real) (y : real) : term345 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3902426 (_45313 : int) : term351 _45313.
Proof. exact (@lem3902425 term237 (term297 _45313)). Qed.
Lemma lem3902427 (_45312 : int) (_45313 : int) (h1 : term335 _45312 _45313) : term352 _45313.
Proof. exact (@lem3902426 _45313 (@lem3902423 _45312 _45313 h1)). Qed.
Lemma lem3902428 (_45313 : int) : (term353 _45313) = (term297 _45313).
Proof. exact (@lem1982733 (term297 _45313)). Qed.
Lemma lem3902429 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3902430 (_45313 : int) : (term354 _45313) = (term331 _45313).
Proof. exact (MK_COMB (@lem3902429) (@lem3902428 _45313)). Qed.
Lemma lem3902431 : term219 = term219.
Proof. exact (eq_refl term219). Qed.
Lemma lem3902432 (_45313 : int) : (term352 _45313) = (term332 _45313).
Proof. exact (MK_COMB (@lem3902430 _45313) (@lem3902431)). Qed.
Lemma lem3902433 (_45312 : int) (_45313 : int) (h1 : term335 _45312 _45313) : term332 _45313.
Proof. exact (EQ_MP (@lem3902432 _45313) (@lem3902427 _45312 _45313 h1)). Qed.
Lemma lem3902434 (_45312 : int) (_45313 : int) (h1 : term335 _45312 _45313) : term355 _45313.
Proof. exact (conj (@lem3902433 _45312 _45313 h1) (@lem3902359 _45312 _45313 h1)). Qed.
Lemma lem3902436 (x : real) (y : real) : term356 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem3902437 (_45313 : int) : term357 _45313.
Proof. exact (@lem3902436 (term297 _45313) (real_of_int _45313)). Qed.
Lemma lem3902438 (_45312 : int) (_45313 : int) (h1 : term335 _45312 _45313) : term358 _45313.
Proof. exact (@lem3902437 _45313 (@lem3902434 _45312 _45313 h1)). Qed.
Lemma lem3902439 (_45313 : int) : (term359 _45313) = (term360 _45313).
Proof. exact (@lem1982759 (term301 _45313) (real_of_int _45313) term254). Qed.
Lemma lem3902440 (_45313 : int) : (term361 _45313) = (term303 _45313).
Proof. exact (@lem1982713 term254 (real_of_int _45313)). Qed.
Lemma lem3902442 (x : nat) : (real_of_num x) = (term250 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3902443 : term237 = term287.
Proof. exact (@lem3902442 term238). Qed.
Lemma lem3902445 (x : nat) : (term252 x) = (term253 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3902446 : term254 = term255.
Proof. exact (@lem3902445 term238). Qed.
Lemma lem3902447 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3902448 : term304 = term305.
Proof. exact (MK_COMB (@lem3902447) (@lem3902446)). Qed.
Lemma lem3902449 : term306 = term307.
Proof. exact (MK_COMB (@lem3902448) (@lem3902443)). Qed.
Lemma lem3902450 : term308.
Proof. exact (@lem1981473 term254 term237 term237 term237 term219 term237). Qed.
Lemma lem3902452 (m : nat) (n : nat) : (term309 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3902453 : term310 = term311.
Proof. exact (@lem3902452 (NUMERAL 0) term238). Qed.
Lemma lem3902454 : term312 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3902455 (h1 : term312 = (BIT1 0)) : term311 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3902456 : (term312 = (BIT1 0)) = (term311 = True).
Proof. exact (prop_ext (fun h1 : term312 = (BIT1 0) => @lem3902455 h1) (fun h1 : term311 = True => @lem3902454)). Qed.
Lemma lem3902457 : term311 = True.
Proof. exact (EQ_MP (@lem3902456) (@lem3902454)). Qed.
Lemma lem3902458 : term310 = True.
Proof. exact (TRANS (@lem3902453) (@lem3902457)). Qed.
Lemma lem3902459 : True = term310.
Proof. exact (SYM (@lem3902458)). Qed.
Lemma lem3902460 : term310.
Proof. exact (EQ_MP (@lem3902459) (@lem0)). Qed.
Lemma lem3902461 : term313.
Proof. exact (@lem3902450 (@lem3902460)). Qed.
Lemma lem3902463 (m : nat) (n : nat) : (term309 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3902464 : term310 = term311.
Proof. exact (@lem3902463 (NUMERAL 0) term238). Qed.
Lemma lem3902465 : term312 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3902466 (h1 : term312 = (BIT1 0)) : term311 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3902467 : (term312 = (BIT1 0)) = (term311 = True).
Proof. exact (prop_ext (fun h1 : term312 = (BIT1 0) => @lem3902466 h1) (fun h1 : term311 = True => @lem3902465)). Qed.
Lemma lem3902468 : term311 = True.
Proof. exact (EQ_MP (@lem3902467) (@lem3902465)). Qed.
Lemma lem3902469 : term310 = True.
Proof. exact (TRANS (@lem3902464) (@lem3902468)). Qed.
Lemma lem3902470 : True = term310.
Proof. exact (SYM (@lem3902469)). Qed.
Lemma lem3902471 : term310.
Proof. exact (EQ_MP (@lem3902470) (@lem0)). Qed.
Lemma lem3902472 : term314.
Proof. exact (@lem3902461 (@lem3902471)). Qed.
Lemma lem3902474 (m : nat) (n : nat) : (term309 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3902475 : term310 = term311.
Proof. exact (@lem3902474 (NUMERAL 0) term238). Qed.
Lemma lem3902476 : term312 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3902477 (h1 : term312 = (BIT1 0)) : term311 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3902478 : (term312 = (BIT1 0)) = (term311 = True).
Proof. exact (prop_ext (fun h1 : term312 = (BIT1 0) => @lem3902477 h1) (fun h1 : term311 = True => @lem3902476)). Qed.
Lemma lem3902479 : term311 = True.
Proof. exact (EQ_MP (@lem3902478) (@lem3902476)). Qed.
Lemma lem3902480 : term310 = True.
Proof. exact (TRANS (@lem3902475) (@lem3902479)). Qed.
Lemma lem3902481 : True = term310.
Proof. exact (SYM (@lem3902480)). Qed.
Lemma lem3902482 : term310.
Proof. exact (EQ_MP (@lem3902481) (@lem0)). Qed.
Lemma lem3902483 : term315.
Proof. exact (@lem3902472 (@lem3902482)). Qed.
Lemma lem3902485 (m : nat) (n : nat) : (term261 m n) = (term262 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3902486 : term263 = term264.
Proof. exact (@lem3902485 term238 term238). Qed.
Lemma lem3902487 : (term265 = (BIT1 0)) = (term266 = term238).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3902488 : term266 = term238.
Proof. exact (EQ_MP (@lem3902487) (@lem940073)). Qed.
Lemma lem3902489 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3902490 : term264 = term237.
Proof. exact (MK_COMB (@lem3902489) (@lem3902488)). Qed.
Lemma lem3902491 : term263 = term237.
Proof. exact (TRANS (@lem3902486) (@lem3902490)). Qed.
Lemma lem3902493 (m : nat) (n : nat) : (term291 m n) = (term292 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3902494 : term288 = term293.
Proof. exact (@lem3902493 term238 term238). Qed.
Lemma lem3902495 : (term265 = (BIT1 0)) = (term266 = term238).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3902496 : term266 = term238.
Proof. exact (EQ_MP (@lem3902495) (@lem940073)). Qed.
Lemma lem3902497 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3902498 : term264 = term237.
Proof. exact (MK_COMB (@lem3902497) (@lem3902496)). Qed.
Lemma lem3902499 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3902500 : term293 = term254.
Proof. exact (MK_COMB (@lem3902499) (@lem3902498)). Qed.
Lemma lem3902501 : term288 = term254.
Proof. exact (TRANS (@lem3902494) (@lem3902500)). Qed.
Lemma lem3902502 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3902503 : term316 = term304.
Proof. exact (MK_COMB (@lem3902502) (@lem3902501)). Qed.
Lemma lem3902504 : term317 = term306.
Proof. exact (MK_COMB (@lem3902503) (@lem3902491)). Qed.
Lemma lem3902506 (m : nat) : (term318 m) = term219.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3902507 : term306 = term219.
Proof. exact (@lem3902506 term238). Qed.
Lemma lem3902508 : term317 = term219.
Proof. exact (TRANS (@lem3902504) (@lem3902507)). Qed.
Lemma lem3902509 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3902510 : term319 = term320.
Proof. exact (MK_COMB (@lem3902509) (@lem3902508)). Qed.
Lemma lem3902511 : term237 = term237.
Proof. exact (eq_refl term237). Qed.
Lemma lem3902512 : term321 = term322.
Proof. exact (MK_COMB (@lem3902510) (@lem3902511)). Qed.
Lemma lem3902514 (x : nat) : (term323 x) = term219.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3902515 : term322 = term219.
Proof. exact (@lem3902514 term238). Qed.
Lemma lem3902516 : term321 = term219.
Proof. exact (TRANS (@lem3902512) (@lem3902515)). Qed.
Lemma lem3902518 (m : nat) (n : nat) : (term261 m n) = (term262 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3902519 : term263 = term264.
Proof. exact (@lem3902518 term238 term238). Qed.
Lemma lem3902520 : (term265 = (BIT1 0)) = (term266 = term238).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3902521 : term266 = term238.
Proof. exact (EQ_MP (@lem3902520) (@lem940073)). Qed.
Lemma lem3902522 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3902523 : term264 = term237.
Proof. exact (MK_COMB (@lem3902522) (@lem3902521)). Qed.
Lemma lem3902524 : term263 = term237.
Proof. exact (TRANS (@lem3902519) (@lem3902523)). Qed.
Lemma lem3902525 : term320 = term320.
Proof. exact (eq_refl term320). Qed.
Lemma lem3902526 : term324 = term322.
Proof. exact (MK_COMB (@lem3902525) (@lem3902524)). Qed.
Lemma lem3902528 (x : nat) : (term323 x) = term219.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3902529 : term322 = term219.
Proof. exact (@lem3902528 term238). Qed.
Lemma lem3902530 : term324 = term219.
Proof. exact (TRANS (@lem3902526) (@lem3902529)). Qed.
Lemma lem3902531 : term219 = term324.
Proof. exact (SYM (@lem3902530)). Qed.
Lemma lem3902532 : term321 = term324.
Proof. exact (TRANS (@lem3902516) (@lem3902531)). Qed.
Lemma lem3902533 : term307 = term251.
Proof. exact (@lem3902483 (@lem3902532)). Qed.
Lemma lem3902534 : term306 = term251.
Proof. exact (TRANS (@lem3902449) (@lem3902533)). Qed.
Lemma lem3902536 (x : real) : (term270 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3902537 : term251 = term219.
Proof. exact (@lem3902536 term219). Qed.
Lemma lem3902538 : term306 = term219.
Proof. exact (TRANS (@lem3902534) (@lem3902537)). Qed.
Lemma lem3902539 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3902540 : term325 = term320.
Proof. exact (MK_COMB (@lem3902539) (@lem3902538)). Qed.
Lemma lem3902541 (_45313 : int) : (real_of_int _45313) = (real_of_int _45313).
Proof. exact (eq_refl (real_of_int _45313)). Qed.
Lemma lem3902542 (_45313 : int) : (term303 _45313) = (term326 _45313).
Proof. exact (MK_COMB (@lem3902540) (@lem3902541 _45313)). Qed.
Lemma lem3902543 (_45313 : int) : (term361 _45313) = (term326 _45313).
Proof. exact (TRANS (@lem3902440 _45313) (@lem3902542 _45313)). Qed.
Lemma lem3902544 (_45313 : int) : (term326 _45313) = term219.
Proof. exact (@lem1982719 (real_of_int _45313)). Qed.
Lemma lem3902545 (_45313 : int) : (term361 _45313) = term219.
Proof. exact (TRANS (@lem3902543 _45313) (@lem3902544 _45313)). Qed.
Lemma lem3902546 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3902547 (_45313 : int) : (term362 _45313) = term328.
Proof. exact (MK_COMB (@lem3902546) (@lem3902545 _45313)). Qed.
Lemma lem3902548 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem3902549 (_45313 : int) : (term360 _45313) = term363.
Proof. exact (MK_COMB (@lem3902547 _45313) (@lem3902548)). Qed.
Lemma lem3902550 (_45313 : int) : (term359 _45313) = term363.
Proof. exact (TRANS (@lem3902439 _45313) (@lem3902549 _45313)). Qed.
Lemma lem3902551 : term363 = term254.
Proof. exact (@lem1982721 term254). Qed.
Lemma lem3902552 (_45313 : int) : (term359 _45313) = term254.
Proof. exact (TRANS (@lem3902550 _45313) (@lem3902551)). Qed.
Lemma lem3902553 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3902554 (_45313 : int) : (term364 _45313) = term365.
Proof. exact (MK_COMB (@lem3902553) (@lem3902552 _45313)). Qed.
Lemma lem3902555 : term219 = term219.
Proof. exact (eq_refl term219). Qed.
Lemma lem3902556 (_45313 : int) : (term358 _45313) = term366.
Proof. exact (MK_COMB (@lem3902554 _45313) (@lem3902555)). Qed.
Lemma lem3902557 (_45312 : int) (_45313 : int) (h1 : term335 _45312 _45313) : term366.
Proof. exact (EQ_MP (@lem3902556 _45313) (@lem3902438 _45312 _45313 h1)). Qed.
Lemma lem3902559 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3902560 : term366 = term367.
Proof. exact (@lem3902559 term219 term254). Qed.
Lemma lem3902562 (x : nat) : (term252 x) = (term253 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3902563 : term254 = term255.
Proof. exact (@lem3902562 term238). Qed.
Lemma lem3902565 (x : nat) : (real_of_num x) = (term250 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3902566 : term219 = term251.
Proof. exact (@lem3902565 (NUMERAL 0)). Qed.
Lemma lem3902567 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3902568 : term221 = term368.
Proof. exact (MK_COMB (@lem3902567) (@lem3902566)). Qed.
Lemma lem3902569 : term367 = term369.
Proof. exact (MK_COMB (@lem3902568) (@lem3902563)). Qed.
Lemma lem3902570 : term370.
Proof. exact (@lem1980026 term219 term237 term254 term237). Qed.
Lemma lem3902572 (m : nat) (n : nat) : (term309 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3902573 : term310 = term311.
Proof. exact (@lem3902572 (NUMERAL 0) term238). Qed.
Lemma lem3902574 : term312 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3902575 (h1 : term312 = (BIT1 0)) : term311 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3902576 : (term312 = (BIT1 0)) = (term311 = True).
Proof. exact (prop_ext (fun h1 : term312 = (BIT1 0) => @lem3902575 h1) (fun h1 : term311 = True => @lem3902574)). Qed.
Lemma lem3902577 : term311 = True.
Proof. exact (EQ_MP (@lem3902576) (@lem3902574)). Qed.
Lemma lem3902578 : term310 = True.
Proof. exact (TRANS (@lem3902573) (@lem3902577)). Qed.
Lemma lem3902579 : True = term310.
Proof. exact (SYM (@lem3902578)). Qed.
Lemma lem3902580 : term310.
Proof. exact (EQ_MP (@lem3902579) (@lem0)). Qed.
Lemma lem3902581 : term371.
Proof. exact (@lem3902570 (@lem3902580)). Qed.
Lemma lem3902583 (m : nat) (n : nat) : (term309 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3902584 : term310 = term311.
Proof. exact (@lem3902583 (NUMERAL 0) term238). Qed.
Lemma lem3902585 : term312 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3902586 (h1 : term312 = (BIT1 0)) : term311 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3902587 : (term312 = (BIT1 0)) = (term311 = True).
Proof. exact (prop_ext (fun h1 : term312 = (BIT1 0) => @lem3902586 h1) (fun h1 : term311 = True => @lem3902585)). Qed.
Lemma lem3902588 : term311 = True.
Proof. exact (EQ_MP (@lem3902587) (@lem3902585)). Qed.
Lemma lem3902589 : term310 = True.
Proof. exact (TRANS (@lem3902584) (@lem3902588)). Qed.
Lemma lem3902590 : True = term310.
Proof. exact (SYM (@lem3902589)). Qed.
Lemma lem3902591 : term310.
Proof. exact (EQ_MP (@lem3902590) (@lem0)). Qed.
Lemma lem3902592 : term369 = term372.
Proof. exact (@lem3902581 (@lem3902591)). Qed.
Lemma lem3902594 (m : nat) (n : nat) : (term291 m n) = (term292 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3902595 : term288 = term293.
Proof. exact (@lem3902594 term238 term238). Qed.
Lemma lem3902596 : (term265 = (BIT1 0)) = (term266 = term238).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3902597 : term266 = term238.
Proof. exact (EQ_MP (@lem3902596) (@lem940073)). Qed.
Lemma lem3902598 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3902599 : term264 = term237.
Proof. exact (MK_COMB (@lem3902598) (@lem3902597)). Qed.
Lemma lem3902600 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3902601 : term293 = term254.
Proof. exact (MK_COMB (@lem3902600) (@lem3902599)). Qed.
Lemma lem3902602 : term288 = term254.
Proof. exact (TRANS (@lem3902595) (@lem3902601)). Qed.
Lemma lem3902604 (x : nat) : (term323 x) = term219.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3902605 : term322 = term219.
Proof. exact (@lem3902604 term238). Qed.
Lemma lem3902606 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3902607 : term373 = term221.
Proof. exact (MK_COMB (@lem3902606) (@lem3902605)). Qed.
Lemma lem3902608 : term372 = term367.
Proof. exact (MK_COMB (@lem3902607) (@lem3902602)). Qed.
Lemma lem3902610 (m : nat) (n : nat) : (term374 m n) = (term375 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3902611 : term367 = term376.
Proof. exact (@lem3902610 (NUMERAL 0) term238). Qed.
Lemma lem3902612 : term312 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3902613 (h1 : term312 = (BIT1 0)) : (term238 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3902614 : (term312 = (BIT1 0)) = ((term238 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term312 = (BIT1 0) => @lem3902613 h1) (fun h1 : (term238 = (NUMERAL 0)) = False => @lem3902612)). Qed.
Lemma lem3902615 : (term238 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3902614) (@lem3902612)). Qed.
Lemma lem3902616 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3902617 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3902618 : term377 = (and True).
Proof. exact (MK_COMB (@lem3902617) (@lem3902616)). Qed.
Lemma lem3902619 : term376 = (True /\ False).
Proof. exact (MK_COMB (@lem3902618) (@lem3902615)). Qed.
Lemma lem3902621 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3902622 : term376 = False.
Proof. exact (TRANS (@lem3902619) (@lem3902621)). Qed.
Lemma lem3902623 : term367 = False.
Proof. exact (TRANS (@lem3902611) (@lem3902622)). Qed.
Lemma lem3902624 : term372 = False.
Proof. exact (TRANS (@lem3902608) (@lem3902623)). Qed.
Lemma lem3902625 : term369 = False.
Proof. exact (TRANS (@lem3902592) (@lem3902624)). Qed.
Lemma lem3902626 : term367 = False.
Proof. exact (TRANS (@lem3902569) (@lem3902625)). Qed.
Lemma lem3902627 : term366 = False.
Proof. exact (TRANS (@lem3902560) (@lem3902626)). Qed.
Lemma lem3902628 (_45312 : int) (_45313 : int) (h1 : term335 _45312 _45313) : False.
Proof. exact (EQ_MP (@lem3902627) (@lem3902557 _45312 _45313 h1)). Qed.
Lemma lem3902630 (_45312 : int) (_45313 : int) (h1 : term335 _45312 _45313) : term335 _45312 _45313.
Proof. exact (h1). Qed.
Lemma lem3902631 (_45312 : int) (_45313 : int) (h1 : term335 _45312 _45313) : (term335 _45312 _45313) = False.
Proof. exact (prop_ext (fun h2 : term335 _45312 _45313 => @lem3902628 _45312 _45313 h1) (fun h2 : False => @lem3902630 _45312 _45313 h1)). Qed.
Lemma lem3902632 (_45312 : int) (_45313 : int) (h1 : term335 _45312 _45313) : False.
Proof. exact (EQ_MP (@lem3902631 _45312 _45313 h1) (@lem3902630 _45312 _45313 h1)). Qed.
Lemma lem3902633 (_45313 : int) (_45312 : int) (h1 : term246 _45313 _45312) : term246 _45313 _45312.
Proof. exact (h1). Qed.
Lemma lem3902634 (_45313 : int) (_45312 : int) (h1 : term246 _45313 _45312) : term335 _45312 _45313.
Proof. exact (EQ_MP (@lem3902277 _45312 _45313) (@lem3902633 _45313 _45312 h1)). Qed.
Lemma lem3902635 (_45313 : int) (_45312 : int) (h1 : term246 _45313 _45312) : (term335 _45312 _45313) = False.
Proof. exact (prop_ext (fun h2 : term335 _45312 _45313 => @lem3902632 _45312 _45313 h2) (fun h2 : False => @lem3902634 _45313 _45312 h1)). Qed.
Lemma lem3902636 (_45313 : int) (_45312 : int) (h1 : term246 _45313 _45312) : False.
Proof. exact (EQ_MP (@lem3902635 _45313 _45312 h1) (@lem3902634 _45313 _45312 h1)). Qed.
Lemma lem3902637 (_45313 : int) (_45312 : int) : term378 _45313 _45312.
Proof. exact (fun h0 : term246 _45313 _45312 => @lem3902636 _45313 _45312 h0). Qed.
Lemma lem3902638 (_45313 : int) (_45312 : int) : term379 _45313 _45312.
Proof. exact (@lem1386578 (term380 _45313 _45312)). Qed.
Lemma lem3902641 (_45313 : int) (_45312 : int) : term380 _45313 _45312.
Proof. exact (@lem3902638 _45313 _45312 (@lem3902637 _45313 _45312)). Qed.
Lemma lem3902642 (_45312 : int) (_45313 : int) : (term245 _45313 _45312) = (term212 _45312 _45313).
Proof. exact (SYM (@lem3901928 _45313 _45312)). Qed.
Lemma lem3902643 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3902644 (_45312 : int) (_45313 : int) : (term380 _45313 _45312) = (term203 _45312 _45313).
Proof. exact (MK_COMB (@lem3902643) (@lem3902642 _45312 _45313)). Qed.
Lemma lem3902645 (_45312 : int) (_45313 : int) : term203 _45312 _45313.
Proof. exact (EQ_MP (@lem3902644 _45312 _45313) (@lem3902641 _45313 _45312)). Qed.
Lemma lem3902646 (_45312 : int) (_45313 : int) : term204 _45312 _45313.
Proof. exact (EQ_MP (@lem3901835 _45312 _45313) (@lem3902645 _45312 _45313)). Qed.
Lemma lem3902647 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term381 A b a.
Proof. exact (@lem3902646 (term382 A a) (term383 A b a)). Qed.
Lemma lem3902648 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term384 A b a.
Proof. exact (@lem3902647 A b a (@lem3901831 A a)). Qed.
Lemma lem3902649 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term198 A b a.
Proof. exact (@lem3902648 A b a (@lem3901834 A b a)). Qed.
Lemma lem3902650 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term198 A b a) = (term121 A b a).
Proof. exact (SYM (@lem3901828 A b a)). Qed.
Lemma lem3902651 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term121 A b a.
Proof. exact (EQ_MP (@lem3902650 A b a) (@lem3902649 A b a)). Qed.
Lemma lem3902652 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term121 A b a) = ((term121 A b a) = True).
Proof. exact (@lem7 (term121 A b a)). Qed.
Lemma lem3902653 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term121 A b a) = True.
Proof. exact (EQ_MP (@lem3902652 A b a) (@lem3902651 A b a)). Qed.
Lemma lem3902654 {A : Type'} (b : A -> Prop) (a : A -> Prop) : True = (term121 A b a).
Proof. exact (SYM (@lem3902653 A b a)). Qed.
Lemma lem3902655 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term121 A b a.
Proof. exact (EQ_MP (@lem3902654 A b a) (@lem0)). Qed.
Lemma lem3902656 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : (term116 A b a) = (term117 A b a)) : term28 A b a.
Proof. exact (EQ_MP (@lem3901131 A b a h1) (@lem3902655 A b a)). Qed.
Lemma lem3902657 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) (h2 : @SUBSET A a b) : ((term116 A b a) = (term117 A b a)) = (term28 A b a).
Proof. exact (prop_ext (fun h3 : (term116 A b a) = (term117 A b a) => @lem3902656 A b a h3) (fun h3 : term28 A b a => @lem3901791 A a b h1 h2)). Qed.
Lemma lem3902658 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) (h2 : @SUBSET A a b) : term28 A b a.
Proof. exact (EQ_MP (@lem3902657 A a b h1 h2) (@lem3901791 A a b h1 h2)). Qed.
Lemma lem3902659 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) (h2 : b = (term24 A b a)) (h3 : @SUBSET A a b) : term30 A a b.
Proof. exact (EQ_MP (@lem3900315 A b a h2) (@lem3902658 A a b h1 h3)). Qed.
Lemma lem3902660 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) (h2 : @SUBSET A a b) : (b = (term24 A b a)) = (term30 A a b).
Proof. exact (prop_ext (fun h3 : b = (term24 A b a) => @lem3902659 A a b h1 h3 h2) (fun h3 : term30 A a b => @lem3901117 A a b h2)). Qed.
Lemma lem3902661 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) (h2 : @SUBSET A a b) : term30 A a b.
Proof. exact (EQ_MP (@lem3902660 A a b h1 h2) (@lem3901117 A a b h2)). Qed.
Lemma lem3902662 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term23 A a b) : @FINITE A b.
Proof. exact (proj2 (@lem3900299 A a b h1)). Qed.
Lemma lem3902663 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term23 A a b) : @SUBSET A a b.
Proof. exact (proj1 (@lem3900299 A a b h1)). Qed.
Lemma lem3902664 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) (h2 : @SUBSET A a b) : (@FINITE A b) = (term30 A a b).
Proof. exact (prop_ext (fun h3 : @FINITE A b => @lem3902661 A a b h1 h2) (fun h3 : term30 A a b => @lem3900300 A b h1)). Qed.
Lemma lem3902665 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) (h2 : @SUBSET A a b) : term30 A a b.
Proof. exact (EQ_MP (@lem3902664 A a b h1 h2) (@lem3900300 A b h1)). Qed.
Lemma lem3902666 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) (h2 : @SUBSET A a b) : (@SUBSET A a b) = (term30 A a b).
Proof. exact (prop_ext (fun h3 : @SUBSET A a b => @lem3902665 A a b h1 h2) (fun h3 : term30 A a b => @lem3900301 A a b h2)). Qed.
Lemma lem3902667 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) (h2 : @SUBSET A a b) : term30 A a b.
Proof. exact (EQ_MP (@lem3902666 A a b h1 h2) (@lem3900301 A a b h2)). Qed.
Lemma lem3902668 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term23 A a b) (h2 : @SUBSET A a b) : (@FINITE A b) = (term30 A a b).
Proof. exact (prop_ext (fun h3 : @FINITE A b => @lem3902667 A a b h3 h2) (fun h3 : term30 A a b => @lem3902662 A a b h1)). Qed.
Lemma lem3902669 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term23 A a b) (h2 : @SUBSET A a b) : term30 A a b.
Proof. exact (EQ_MP (@lem3902668 A a b h1 h2) (@lem3902662 A a b h1)). Qed.
Lemma lem3902670 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term23 A a b) : (@SUBSET A a b) = (term30 A a b).
Proof. exact (prop_ext (fun h2 : @SUBSET A a b => @lem3902669 A a b h1 h2) (fun h2 : term30 A a b => @lem3902663 A a b h1)). Qed.
Lemma lem3902671 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term23 A a b) : term30 A a b.
Proof. exact (EQ_MP (@lem3902670 A a b h1) (@lem3902663 A a b h1)). Qed.
Lemma lem3902672 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term385 A a b.
Proof. exact (fun h0 : term23 A a b => @lem3902671 A a b h0). Qed.
Lemma lem3902677 {A : Type'} (a : A -> Prop) : term386 A a.
Proof. exact (fun b : A -> Prop => @lem3902672 A a b). Qed.
Lemma lem3902682 {A : Type'} : term387 A.
Proof. exact (fun a : A -> Prop => @lem3902677 A a). Qed.
