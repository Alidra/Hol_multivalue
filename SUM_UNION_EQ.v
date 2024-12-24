Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_UNION_EQ_term_abbrevs.
Require Import DISJOINT_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_SUBSET_spec.
Require Import SUBSET_UNION_spec.
Require Import SUM_UNION_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18946_spec.
Require Import thm18947_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
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
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm69_spec.
Lemma lem7149042 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem7149043 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem7149044 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem7149043 t1) (@lem7149042 t1)). Qed.
Lemma lem7149045 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem7149044 t1 t2). Qed.
Lemma lem7149046 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem7149047 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem7149046 t1 t2) (@lem7149045 t1 t2)). Qed.
Lemma lem7149048 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem7149047 t1 t2 t3). Qed.
Lemma lem7149049 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem7149050 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem7149049 t1 t2 t3) (@lem7149048 t1 t2 t3)). Qed.
Lemma lem7149051 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem7149050 t1 t2 t3)). Qed.
Lemma lem7149053 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7149054 {_133751 : Type'} (f : _133751 -> real) : (term8 _133751 f) = (term9 _133751 f).
Proof. exact (@lem7149053 (term8 _133751 f)). Qed.
Lemma lem7149055 {_133751 : Type'} (f : _133751 -> real) : (term9 _133751 f) = (term8 _133751 f).
Proof. exact (SYM (@lem7149054 _133751 f)). Qed.
Lemma lem7149056 {_133751 : Type'} (f : _133751 -> real) (h1 : term10 _133751 f) : term10 _133751 f.
Proof. exact (h1). Qed.
Lemma lem7149057 {_133751 : Type'} : term11 _133751.
Proof. exact (@lem7067826 _133751). Qed.
Lemma lem7149060 {_133751 : Type'} : term12 _133751.
Proof. exact (@lem3196110 _133751). Qed.
Lemma lem7149061 {_131550 : Type'} : term12 _131550.
Proof. exact (@lem3196110 _131550). Qed.
Lemma lem7149065 {_133751 : Type'} : term13 _133751.
Proof. exact (@lem3599924 _133751). Qed.
Lemma lem7149066 {_131550 : Type'} : term13 _131550.
Proof. exact (@lem3599924 _131550). Qed.
Lemma lem7149067 {_133751 : Type'} : term14 _133751.
Proof. exact (@lem3234183 _133751). Qed.
Lemma lem7149068 {_131550 : Type'} : term14 _131550.
Proof. exact (@lem3234183 _131550). Qed.
Lemma lem7149073 {_131550 _133751 : Type'} (f : _133751 -> real) (h1 : term15 _131550 _133751 f) : term15 _131550 _133751 f.
Proof. exact (h1). Qed.
Lemma lem7149074 {_131550 _133751 : Type'} (f : _133751 -> real) : term16 _131550 _133751 f.
Proof. exact (fun h0 : term15 _131550 _133751 f => @lem7149073 _131550 _133751 f h0). Qed.
Lemma lem7149075 {_131550 _133751 : Type'} (f : _133751 -> real) (h1 : term16 _131550 _133751 f) : term16 _131550 _133751 f.
Proof. exact (h1). Qed.
Lemma lem7149076 {_131550 _133751 : Type'} (f : _133751 -> real) (h1 : term15 _131550 _133751 f) : term15 _131550 _133751 f.
Proof. exact (h1). Qed.
Lemma lem7149077 {_131550 _133751 : Type'} (f : _133751 -> real) (h1 : term15 _131550 _133751 f) (h2 : term16 _131550 _133751 f) : term15 _131550 _133751 f.
Proof. exact (@lem7149075 _131550 _133751 f h2 (@lem7149076 _131550 _133751 f h1)). Qed.
Lemma lem7149078 {_131550 _133751 : Type'} (f : _133751 -> real) (h1 : term15 _131550 _133751 f) : term17 _131550 _133751 f.
Proof. exact (fun h0 : term16 _131550 _133751 f => @lem7149077 _131550 _133751 f h1 h0). Qed.
Lemma lem7149079 {_131550 _133751 : Type'} (f : _133751 -> real) (h1 : term16 _131550 _133751 f) : term16 _131550 _133751 f.
Proof. exact (h1). Qed.
Lemma lem7149080 {_131550 _133751 : Type'} (f : _133751 -> real) (h1 : term15 _131550 _133751 f) (h2 : term16 _131550 _133751 f) : term15 _131550 _133751 f.
Proof. exact (@lem7149078 _131550 _133751 f h1 (@lem7149079 _131550 _133751 f h2)). Qed.
Lemma lem7149081 {_131550 _133751 : Type'} (f : _133751 -> real) (h1 : term16 _131550 _133751 f) : term16 _131550 _133751 f.
Proof. exact (fun h0 : term15 _131550 _133751 f => @lem7149080 _131550 _133751 f h0 h1). Qed.
Lemma lem7149082 {_131550 _133751 : Type'} (f : _133751 -> real) : term18 _131550 _133751 f.
Proof. exact (fun h0 : term16 _131550 _133751 f => @lem7149081 _131550 _133751 f h0). Qed.
Lemma lem7149085 {_131550 _133751 : Type'} (f : _133751 -> real) : term16 _131550 _133751 f.
Proof. exact (@lem7149082 _131550 _133751 f (@lem7149074 _131550 _133751 f)). Qed.
Lemma lem7149086 {_131550 _133751 : Type'} (f : _133751 -> real) : term16 _131550 _133751 f.
Proof. exact (@lem7149085 _131550 _133751 f). Qed.
Lemma lem7149220 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7149221 {_133751 : Type'} : (term19 _133751) = (term20 _133751).
Proof. exact (@lem7149220 (term11 _133751)). Qed.
Lemma lem7149240 {_131550 : Type'} : (term21 _131550) = (term21 _131550).
Proof. exact (eq_refl (term21 _131550)). Qed.
Lemma lem7149241 {_131550 _133751 : Type'} : (term22 _131550 _133751) = (term23 _131550 _133751).
Proof. exact (MK_COMB (@lem7149240 _131550) (@lem7149221 _133751)). Qed.
Lemma lem7149244 {_133751 : Type'} : (term24 _133751) = (term24 _133751).
Proof. exact (eq_refl (term24 _133751)). Qed.
Lemma lem7149245 {_131550 _133751 : Type'} : (term25 _131550 _133751) = (term26 _131550 _133751).
Proof. exact (MK_COMB (@lem7149244 _133751) (@lem7149241 _131550 _133751)). Qed.
Lemma lem7149248 {_131550 : Type'} : (term24 _131550) = (term24 _131550).
Proof. exact (eq_refl (term24 _131550)). Qed.
Lemma lem7149249 {_131550 _133751 : Type'} : (term27 _131550 _133751) = (term28 _131550 _133751).
Proof. exact (MK_COMB (@lem7149248 _131550) (@lem7149245 _131550 _133751)). Qed.
Lemma lem7149252 {_133751 : Type'} : (term29 _133751) = (term29 _133751).
Proof. exact (eq_refl (term29 _133751)). Qed.
Lemma lem7149253 {_131550 _133751 : Type'} : (term30 _131550 _133751) = (term31 _131550 _133751).
Proof. exact (MK_COMB (@lem7149252 _133751) (@lem7149249 _131550 _133751)). Qed.
Lemma lem7149256 {_131550 : Type'} : (term29 _131550) = (term29 _131550).
Proof. exact (eq_refl (term29 _131550)). Qed.
Lemma lem7149257 {_131550 _133751 : Type'} : (term32 _131550 _133751) = (term33 _131550 _133751).
Proof. exact (MK_COMB (@lem7149256 _131550) (@lem7149253 _131550 _133751)). Qed.
Lemma lem7149260 {_133751 : Type'} : (term34 _133751) = (term34 _133751).
Proof. exact (eq_refl (term34 _133751)). Qed.
Lemma lem7149261 {_131550 _133751 : Type'} : (term35 _131550 _133751) = (term36 _131550 _133751).
Proof. exact (MK_COMB (@lem7149260 _133751) (@lem7149257 _131550 _133751)). Qed.
Lemma lem7149264 {_131550 : Type'} : (term34 _131550) = (term34 _131550).
Proof. exact (eq_refl (term34 _131550)). Qed.
Lemma lem7149265 {_131550 _133751 : Type'} : (term37 _131550 _133751) = (term38 _131550 _133751).
Proof. exact (MK_COMB (@lem7149264 _131550) (@lem7149261 _131550 _133751)). Qed.
Lemma lem7149268 {_133751 : Type'} (f : _133751 -> real) : (term39 _133751 f) = (term39 _133751 f).
Proof. exact (eq_refl (term39 _133751 f)). Qed.
Lemma lem7149269 {_131550 _133751 : Type'} (f : _133751 -> real) : (term15 _131550 _133751 f) = (term40 _131550 _133751 f).
Proof. exact (MK_COMB (@lem7149268 _133751 f) (@lem7149265 _131550 _133751)). Qed.
Lemma lem7149272 {_131550 _133751 : Type'} : (term41 _131550 _133751) = (term42 _131550 _133751).
Proof. exact (fun_ext (fun f : _133751 -> real => @lem7149269 _131550 _133751 f)). Qed.
Lemma lem7149273 {_133751 : Type'} : (@all (_133751 -> real)) = (@all (_133751 -> real)).
Proof. exact (eq_refl (@all (_133751 -> real))). Qed.
Lemma lem7149282 {_131550 _133751 : Type'} : (term43 _131550 _133751) = (term44 _131550 _133751).
Proof. exact (MK_COMB (@lem7149273 _133751) (@lem7149272 _131550 _133751)). Qed.
Lemma lem7149295 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (f : _133751 -> real) : (term45 _133751 s t f) = (term45 _133751 s t f).
Proof. exact (eq_refl (term45 _133751 s t f)). Qed.
Lemma lem7149296 {_133751 : Type'} (s : _133751 -> Prop) (f : _133751 -> real) : (term46 _133751 s f) = (term46 _133751 s f).
Proof. exact (fun_ext (fun t : _133751 -> Prop => @lem7149295 _133751 s t f)). Qed.
Lemma lem7149297 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7149298 {_133751 : Type'} (s : _133751 -> Prop) (f : _133751 -> real) : (term47 _133751 s f) = (term47 _133751 s f).
Proof. exact (MK_COMB (@lem7149297 _133751) (@lem7149296 _133751 s f)). Qed.
Lemma lem7149299 {_133751 : Type'} (f : _133751 -> real) : (term48 _133751 f) = (term48 _133751 f).
Proof. exact (fun_ext (fun s : _133751 -> Prop => @lem7149298 _133751 s f)). Qed.
Lemma lem7149300 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7149301 {_133751 : Type'} (f : _133751 -> real) : (term49 _133751 f) = (term49 _133751 f).
Proof. exact (MK_COMB (@lem7149300 _133751) (@lem7149299 _133751 f)). Qed.
Lemma lem7149302 {_133751 : Type'} : (term50 _133751) = (term50 _133751).
Proof. exact (fun_ext (fun f : _133751 -> real => @lem7149301 _133751 f)). Qed.
Lemma lem7149303 {_133751 : Type'} : (@all (_133751 -> real)) = (@all (_133751 -> real)).
Proof. exact (eq_refl (@all (_133751 -> real))). Qed.
Lemma lem7149304 {_133751 : Type'} : (term11 _133751) = (term11 _133751).
Proof. exact (MK_COMB (@lem7149303 _133751) (@lem7149302 _133751)). Qed.
Lemma lem7149305 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7149306 {_133751 : Type'} : (term20 _133751) = (term20 _133751).
Proof. exact (MK_COMB (@lem7149305) (@lem7149304 _133751)). Qed.
Lemma lem7149319 {_131550 : Type'} (s : _131550 -> Prop) (t : _131550 -> Prop) (f : _131550 -> real) : (term45 _131550 s t f) = (term45 _131550 s t f).
Proof. exact (eq_refl (term45 _131550 s t f)). Qed.
Lemma lem7149320 {_131550 : Type'} (s : _131550 -> Prop) (f : _131550 -> real) : (term46 _131550 s f) = (term46 _131550 s f).
Proof. exact (fun_ext (fun t : _131550 -> Prop => @lem7149319 _131550 s t f)). Qed.
Lemma lem7149321 {_131550 : Type'} : (@all (_131550 -> Prop)) = (@all (_131550 -> Prop)).
Proof. exact (eq_refl (@all (_131550 -> Prop))). Qed.
Lemma lem7149322 {_131550 : Type'} (s : _131550 -> Prop) (f : _131550 -> real) : (term47 _131550 s f) = (term47 _131550 s f).
Proof. exact (MK_COMB (@lem7149321 _131550) (@lem7149320 _131550 s f)). Qed.
Lemma lem7149323 {_131550 : Type'} (f : _131550 -> real) : (term48 _131550 f) = (term48 _131550 f).
Proof. exact (fun_ext (fun s : _131550 -> Prop => @lem7149322 _131550 s f)). Qed.
Lemma lem7149324 {_131550 : Type'} : (@all (_131550 -> Prop)) = (@all (_131550 -> Prop)).
Proof. exact (eq_refl (@all (_131550 -> Prop))). Qed.
Lemma lem7149325 {_131550 : Type'} (f : _131550 -> real) : (term49 _131550 f) = (term49 _131550 f).
Proof. exact (MK_COMB (@lem7149324 _131550) (@lem7149323 _131550 f)). Qed.
Lemma lem7149326 {_131550 : Type'} : (term50 _131550) = (term50 _131550).
Proof. exact (fun_ext (fun f : _131550 -> real => @lem7149325 _131550 f)). Qed.
Lemma lem7149327 {_131550 : Type'} : (@all (_131550 -> real)) = (@all (_131550 -> real)).
Proof. exact (eq_refl (@all (_131550 -> real))). Qed.
Lemma lem7149328 {_131550 : Type'} : (term11 _131550) = (term11 _131550).
Proof. exact (MK_COMB (@lem7149327 _131550) (@lem7149326 _131550)). Qed.
Lemma lem7149329 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7149330 {_131550 : Type'} : (term21 _131550) = (term21 _131550).
Proof. exact (MK_COMB (@lem7149329) (@lem7149328 _131550)). Qed.
Lemma lem7149331 {_131550 _133751 : Type'} : (term23 _131550 _133751) = (term23 _131550 _133751).
Proof. exact (MK_COMB (@lem7149330 _131550) (@lem7149306 _133751)). Qed.
Lemma lem7149336 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) : ((@DISJOINT _133751 s t) = ((@INTER _133751 s t) = (@EMPTY _133751))) = ((@DISJOINT _133751 s t) = ((@INTER _133751 s t) = (@EMPTY _133751))).
Proof. exact (eq_refl ((@DISJOINT _133751 s t) = ((@INTER _133751 s t) = (@EMPTY _133751)))). Qed.
Lemma lem7149337 {_133751 : Type'} (s : _133751 -> Prop) : (term51 _133751 s) = (term51 _133751 s).
Proof. exact (fun_ext (fun t : _133751 -> Prop => @lem7149336 _133751 s t)). Qed.
Lemma lem7149338 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7149339 {_133751 : Type'} (s : _133751 -> Prop) : (term52 _133751 s) = (term52 _133751 s).
Proof. exact (MK_COMB (@lem7149338 _133751) (@lem7149337 _133751 s)). Qed.
Lemma lem7149340 {_133751 : Type'} : (term53 _133751) = (term53 _133751).
Proof. exact (fun_ext (fun s : _133751 -> Prop => @lem7149339 _133751 s)). Qed.
Lemma lem7149341 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7149342 {_133751 : Type'} : (term12 _133751) = (term12 _133751).
Proof. exact (MK_COMB (@lem7149341 _133751) (@lem7149340 _133751)). Qed.
Lemma lem7149343 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7149344 {_133751 : Type'} : (term24 _133751) = (term24 _133751).
Proof. exact (MK_COMB (@lem7149343) (@lem7149342 _133751)). Qed.
Lemma lem7149345 {_131550 _133751 : Type'} : (term26 _131550 _133751) = (term26 _131550 _133751).
Proof. exact (MK_COMB (@lem7149344 _133751) (@lem7149331 _131550 _133751)). Qed.
Lemma lem7149350 {_131550 : Type'} (s : _131550 -> Prop) (t : _131550 -> Prop) : ((@DISJOINT _131550 s t) = ((@INTER _131550 s t) = (@EMPTY _131550))) = ((@DISJOINT _131550 s t) = ((@INTER _131550 s t) = (@EMPTY _131550))).
Proof. exact (eq_refl ((@DISJOINT _131550 s t) = ((@INTER _131550 s t) = (@EMPTY _131550)))). Qed.
Lemma lem7149351 {_131550 : Type'} (s : _131550 -> Prop) : (term51 _131550 s) = (term51 _131550 s).
Proof. exact (fun_ext (fun t : _131550 -> Prop => @lem7149350 _131550 s t)). Qed.
Lemma lem7149352 {_131550 : Type'} : (@all (_131550 -> Prop)) = (@all (_131550 -> Prop)).
Proof. exact (eq_refl (@all (_131550 -> Prop))). Qed.
Lemma lem7149353 {_131550 : Type'} (s : _131550 -> Prop) : (term52 _131550 s) = (term52 _131550 s).
Proof. exact (MK_COMB (@lem7149352 _131550) (@lem7149351 _131550 s)). Qed.
Lemma lem7149354 {_131550 : Type'} : (term53 _131550) = (term53 _131550).
Proof. exact (fun_ext (fun s : _131550 -> Prop => @lem7149353 _131550 s)). Qed.
Lemma lem7149355 {_131550 : Type'} : (@all (_131550 -> Prop)) = (@all (_131550 -> Prop)).
Proof. exact (eq_refl (@all (_131550 -> Prop))). Qed.
Lemma lem7149356 {_131550 : Type'} : (term12 _131550) = (term12 _131550).
Proof. exact (MK_COMB (@lem7149355 _131550) (@lem7149354 _131550)). Qed.
Lemma lem7149357 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7149358 {_131550 : Type'} : (term24 _131550) = (term24 _131550).
Proof. exact (MK_COMB (@lem7149357) (@lem7149356 _131550)). Qed.
Lemma lem7149359 {_131550 _133751 : Type'} : (term28 _131550 _133751) = (term28 _131550 _133751).
Proof. exact (MK_COMB (@lem7149358 _131550) (@lem7149345 _131550 _133751)). Qed.
Lemma lem7149368 {_133751 : Type'} (t : _133751 -> Prop) (s : _133751 -> Prop) : (term54 _133751 t s) = (term54 _133751 t s).
Proof. exact (eq_refl (term54 _133751 t s)). Qed.
Lemma lem7149369 {_133751 : Type'} (s : _133751 -> Prop) : (term55 _133751 s) = (term55 _133751 s).
Proof. exact (fun_ext (fun t : _133751 -> Prop => @lem7149368 _133751 t s)). Qed.
Lemma lem7149370 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7149371 {_133751 : Type'} (s : _133751 -> Prop) : (term56 _133751 s) = (term56 _133751 s).
Proof. exact (MK_COMB (@lem7149370 _133751) (@lem7149369 _133751 s)). Qed.
Lemma lem7149372 {_133751 : Type'} : (term57 _133751) = (term57 _133751).
Proof. exact (fun_ext (fun s : _133751 -> Prop => @lem7149371 _133751 s)). Qed.
Lemma lem7149373 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7149374 {_133751 : Type'} : (term13 _133751) = (term13 _133751).
Proof. exact (MK_COMB (@lem7149373 _133751) (@lem7149372 _133751)). Qed.
Lemma lem7149375 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7149376 {_133751 : Type'} : (term29 _133751) = (term29 _133751).
Proof. exact (MK_COMB (@lem7149375) (@lem7149374 _133751)). Qed.
Lemma lem7149377 {_131550 _133751 : Type'} : (term31 _131550 _133751) = (term31 _131550 _133751).
Proof. exact (MK_COMB (@lem7149376 _133751) (@lem7149359 _131550 _133751)). Qed.
Lemma lem7149386 {_131550 : Type'} (t : _131550 -> Prop) (s : _131550 -> Prop) : (term54 _131550 t s) = (term54 _131550 t s).
Proof. exact (eq_refl (term54 _131550 t s)). Qed.
Lemma lem7149387 {_131550 : Type'} (s : _131550 -> Prop) : (term55 _131550 s) = (term55 _131550 s).
Proof. exact (fun_ext (fun t : _131550 -> Prop => @lem7149386 _131550 t s)). Qed.
Lemma lem7149388 {_131550 : Type'} : (@all (_131550 -> Prop)) = (@all (_131550 -> Prop)).
Proof. exact (eq_refl (@all (_131550 -> Prop))). Qed.
Lemma lem7149389 {_131550 : Type'} (s : _131550 -> Prop) : (term56 _131550 s) = (term56 _131550 s).
Proof. exact (MK_COMB (@lem7149388 _131550) (@lem7149387 _131550 s)). Qed.
Lemma lem7149390 {_131550 : Type'} : (term57 _131550) = (term57 _131550).
Proof. exact (fun_ext (fun s : _131550 -> Prop => @lem7149389 _131550 s)). Qed.
Lemma lem7149391 {_131550 : Type'} : (@all (_131550 -> Prop)) = (@all (_131550 -> Prop)).
Proof. exact (eq_refl (@all (_131550 -> Prop))). Qed.
Lemma lem7149392 {_131550 : Type'} : (term13 _131550) = (term13 _131550).
Proof. exact (MK_COMB (@lem7149391 _131550) (@lem7149390 _131550)). Qed.
Lemma lem7149393 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7149394 {_131550 : Type'} : (term29 _131550) = (term29 _131550).
Proof. exact (MK_COMB (@lem7149393) (@lem7149392 _131550)). Qed.
Lemma lem7149395 {_131550 _133751 : Type'} : (term33 _131550 _133751) = (term33 _131550 _133751).
Proof. exact (MK_COMB (@lem7149394 _131550) (@lem7149377 _131550 _133751)). Qed.
Lemma lem7149396 {_133751 : Type'} (t : _133751 -> Prop) (s : _133751 -> Prop) : (term58 _133751 t s) = (term58 _133751 t s).
Proof. exact (eq_refl (term58 _133751 t s)). Qed.
Lemma lem7149397 {_133751 : Type'} (s : _133751 -> Prop) : (term59 _133751 s) = (term59 _133751 s).
Proof. exact (fun_ext (fun t : _133751 -> Prop => @lem7149396 _133751 t s)). Qed.
Lemma lem7149398 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7149399 {_133751 : Type'} (s : _133751 -> Prop) : (term60 _133751 s) = (term60 _133751 s).
Proof. exact (MK_COMB (@lem7149398 _133751) (@lem7149397 _133751 s)). Qed.
Lemma lem7149400 {_133751 : Type'} : (term61 _133751) = (term61 _133751).
Proof. exact (fun_ext (fun s : _133751 -> Prop => @lem7149399 _133751 s)). Qed.
Lemma lem7149401 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7149402 {_133751 : Type'} : (term62 _133751) = (term62 _133751).
Proof. exact (MK_COMB (@lem7149401 _133751) (@lem7149400 _133751)). Qed.
Lemma lem7149403 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) : (term63 _133751 s t) = (term63 _133751 s t).
Proof. exact (eq_refl (term63 _133751 s t)). Qed.
Lemma lem7149404 {_133751 : Type'} (s : _133751 -> Prop) : (term64 _133751 s) = (term64 _133751 s).
Proof. exact (fun_ext (fun t : _133751 -> Prop => @lem7149403 _133751 s t)). Qed.
Lemma lem7149405 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7149406 {_133751 : Type'} (s : _133751 -> Prop) : (term65 _133751 s) = (term65 _133751 s).
Proof. exact (MK_COMB (@lem7149405 _133751) (@lem7149404 _133751 s)). Qed.
Lemma lem7149407 {_133751 : Type'} : (term66 _133751) = (term66 _133751).
Proof. exact (fun_ext (fun s : _133751 -> Prop => @lem7149406 _133751 s)). Qed.
Lemma lem7149408 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7149409 {_133751 : Type'} : (term67 _133751) = (term67 _133751).
Proof. exact (MK_COMB (@lem7149408 _133751) (@lem7149407 _133751)). Qed.
Lemma lem7149410 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7149411 {_133751 : Type'} : (term68 _133751) = (term68 _133751).
Proof. exact (MK_COMB (@lem7149410) (@lem7149409 _133751)). Qed.
Lemma lem7149412 {_133751 : Type'} : (term14 _133751) = (term14 _133751).
Proof. exact (MK_COMB (@lem7149411 _133751) (@lem7149402 _133751)). Qed.
Lemma lem7149413 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7149414 {_133751 : Type'} : (term34 _133751) = (term34 _133751).
Proof. exact (MK_COMB (@lem7149413) (@lem7149412 _133751)). Qed.
Lemma lem7149415 {_131550 _133751 : Type'} : (term36 _131550 _133751) = (term36 _131550 _133751).
Proof. exact (MK_COMB (@lem7149414 _133751) (@lem7149395 _131550 _133751)). Qed.
Lemma lem7149416 {_131550 : Type'} (t : _131550 -> Prop) (s : _131550 -> Prop) : (term58 _131550 t s) = (term58 _131550 t s).
Proof. exact (eq_refl (term58 _131550 t s)). Qed.
Lemma lem7149417 {_131550 : Type'} (s : _131550 -> Prop) : (term59 _131550 s) = (term59 _131550 s).
Proof. exact (fun_ext (fun t : _131550 -> Prop => @lem7149416 _131550 t s)). Qed.
Lemma lem7149418 {_131550 : Type'} : (@all (_131550 -> Prop)) = (@all (_131550 -> Prop)).
Proof. exact (eq_refl (@all (_131550 -> Prop))). Qed.
Lemma lem7149419 {_131550 : Type'} (s : _131550 -> Prop) : (term60 _131550 s) = (term60 _131550 s).
Proof. exact (MK_COMB (@lem7149418 _131550) (@lem7149417 _131550 s)). Qed.
Lemma lem7149420 {_131550 : Type'} : (term61 _131550) = (term61 _131550).
Proof. exact (fun_ext (fun s : _131550 -> Prop => @lem7149419 _131550 s)). Qed.
Lemma lem7149421 {_131550 : Type'} : (@all (_131550 -> Prop)) = (@all (_131550 -> Prop)).
Proof. exact (eq_refl (@all (_131550 -> Prop))). Qed.
Lemma lem7149422 {_131550 : Type'} : (term62 _131550) = (term62 _131550).
Proof. exact (MK_COMB (@lem7149421 _131550) (@lem7149420 _131550)). Qed.
Lemma lem7149423 {_131550 : Type'} (s : _131550 -> Prop) (t : _131550 -> Prop) : (term63 _131550 s t) = (term63 _131550 s t).
Proof. exact (eq_refl (term63 _131550 s t)). Qed.
Lemma lem7149424 {_131550 : Type'} (s : _131550 -> Prop) : (term64 _131550 s) = (term64 _131550 s).
Proof. exact (fun_ext (fun t : _131550 -> Prop => @lem7149423 _131550 s t)). Qed.
Lemma lem7149425 {_131550 : Type'} : (@all (_131550 -> Prop)) = (@all (_131550 -> Prop)).
Proof. exact (eq_refl (@all (_131550 -> Prop))). Qed.
Lemma lem7149426 {_131550 : Type'} (s : _131550 -> Prop) : (term65 _131550 s) = (term65 _131550 s).
Proof. exact (MK_COMB (@lem7149425 _131550) (@lem7149424 _131550 s)). Qed.
Lemma lem7149427 {_131550 : Type'} : (term66 _131550) = (term66 _131550).
Proof. exact (fun_ext (fun s : _131550 -> Prop => @lem7149426 _131550 s)). Qed.
Lemma lem7149428 {_131550 : Type'} : (@all (_131550 -> Prop)) = (@all (_131550 -> Prop)).
Proof. exact (eq_refl (@all (_131550 -> Prop))). Qed.
Lemma lem7149429 {_131550 : Type'} : (term67 _131550) = (term67 _131550).
Proof. exact (MK_COMB (@lem7149428 _131550) (@lem7149427 _131550)). Qed.
Lemma lem7149430 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7149431 {_131550 : Type'} : (term68 _131550) = (term68 _131550).
Proof. exact (MK_COMB (@lem7149430) (@lem7149429 _131550)). Qed.
Lemma lem7149432 {_131550 : Type'} : (term14 _131550) = (term14 _131550).
Proof. exact (MK_COMB (@lem7149431 _131550) (@lem7149422 _131550)). Qed.
Lemma lem7149433 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7149434 {_131550 : Type'} : (term34 _131550) = (term34 _131550).
Proof. exact (MK_COMB (@lem7149433) (@lem7149432 _131550)). Qed.
Lemma lem7149435 {_131550 _133751 : Type'} : (term38 _131550 _133751) = (term38 _131550 _133751).
Proof. exact (MK_COMB (@lem7149434 _131550) (@lem7149415 _131550 _133751)). Qed.
Lemma lem7149448 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) : (term69 _133751 s t u f) = (term69 _133751 s t u f).
Proof. exact (eq_refl (term69 _133751 s t u f)). Qed.
Lemma lem7149449 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (f : _133751 -> real) : (term70 _133751 s t f) = (term70 _133751 s t f).
Proof. exact (fun_ext (fun u : _133751 -> Prop => @lem7149448 _133751 s t u f)). Qed.
Lemma lem7149450 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7149451 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (f : _133751 -> real) : (term71 _133751 s t f) = (term71 _133751 s t f).
Proof. exact (MK_COMB (@lem7149450 _133751) (@lem7149449 _133751 s t f)). Qed.
Lemma lem7149452 {_133751 : Type'} (s : _133751 -> Prop) (f : _133751 -> real) : (term72 _133751 s f) = (term72 _133751 s f).
Proof. exact (fun_ext (fun t : _133751 -> Prop => @lem7149451 _133751 s t f)). Qed.
Lemma lem7149453 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7149454 {_133751 : Type'} (s : _133751 -> Prop) (f : _133751 -> real) : (term73 _133751 s f) = (term73 _133751 s f).
Proof. exact (MK_COMB (@lem7149453 _133751) (@lem7149452 _133751 s f)). Qed.
Lemma lem7149455 {_133751 : Type'} (f : _133751 -> real) : (term74 _133751 f) = (term74 _133751 f).
Proof. exact (fun_ext (fun s : _133751 -> Prop => @lem7149454 _133751 s f)). Qed.
Lemma lem7149456 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7149457 {_133751 : Type'} (f : _133751 -> real) : (term8 _133751 f) = (term8 _133751 f).
Proof. exact (MK_COMB (@lem7149456 _133751) (@lem7149455 _133751 f)). Qed.
Lemma lem7149458 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7149459 {_133751 : Type'} (f : _133751 -> real) : (term10 _133751 f) = (term10 _133751 f).
Proof. exact (MK_COMB (@lem7149458) (@lem7149457 _133751 f)). Qed.
Lemma lem7149460 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7149461 {_133751 : Type'} (f : _133751 -> real) : (term39 _133751 f) = (term39 _133751 f).
Proof. exact (MK_COMB (@lem7149460) (@lem7149459 _133751 f)). Qed.
Lemma lem7149462 {_131550 _133751 : Type'} (f : _133751 -> real) : (term40 _131550 _133751 f) = (term40 _131550 _133751 f).
Proof. exact (MK_COMB (@lem7149461 _133751 f) (@lem7149435 _131550 _133751)). Qed.
Lemma lem7149463 {_131550 _133751 : Type'} : (term42 _131550 _133751) = (term42 _131550 _133751).
Proof. exact (fun_ext (fun f : _133751 -> real => @lem7149462 _131550 _133751 f)). Qed.
Lemma lem7149464 {_133751 : Type'} : (@all (_133751 -> real)) = (@all (_133751 -> real)).
Proof. exact (eq_refl (@all (_133751 -> real))). Qed.
Lemma lem7149465 {_131550 _133751 : Type'} : (term44 _131550 _133751) = (term44 _131550 _133751).
Proof. exact (MK_COMB (@lem7149464 _133751) (@lem7149463 _131550 _133751)). Qed.
Lemma lem7149670 {_131550 _133751 : Type'} : (term43 _131550 _133751) = (term44 _131550 _133751).
Proof. exact (TRANS (@lem7149282 _131550 _133751) (@lem7149465 _131550 _133751)). Qed.
Lemma lem7149671 {_131550 _133751 : Type'} : (term44 _131550 _133751) = (term43 _131550 _133751).
Proof. exact (SYM (@lem7149670 _131550 _133751)). Qed.
Lemma lem7149672 {_133751 : Type'} (f : _133751 -> real) (h1 : term10 _133751 f) : term10 _133751 f.
Proof. exact (h1). Qed.
Lemma lem7149674 {_133751 : Type'} (h1 : term14 _133751) : term14 _133751.
Proof. exact (h1). Qed.
Lemma lem7149676 {_133751 : Type'} (h1 : term13 _133751) : term13 _133751.
Proof. exact (h1). Qed.
Lemma lem7149678 {_133751 : Type'} (h1 : term12 _133751) : term12 _133751.
Proof. exact (h1). Qed.
Lemma lem7149680 {_133751 : Type'} (h1 : term11 _133751) : term11 _133751.
Proof. exact (h1). Qed.
Lemma lem7149695 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) : (term75 _133751 s t u f) = (term76 _133751 s t u f).
Proof. exact (@lem17362 (term77 _133751 s t u) ((term78 _133751 s t f) = (@sum _133751 u f))). Qed.
Lemma lem7149696 {_133751 : Type'} (P : type686 _133751) : (term79 _133751 P) = (term80 _133751 P).
Proof. exact (@lem18392 (_133751 -> Prop) P). Qed.
Lemma lem7149697 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (f : _133751 -> real) : (term81 _133751 s t f) = (term82 _133751 s t f).
Proof. exact (@lem7149696 _133751 (term70 _133751 s t f)). Qed.
Lemma lem7149698 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) : (term83 _133751 s t f u) = (term69 _133751 s t u f).
Proof. exact (eq_refl (term83 _133751 s t f u)). Qed.
Lemma lem7149699 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7149700 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) : (term84 _133751 s t f u) = (term75 _133751 s t u f).
Proof. exact (MK_COMB (@lem7149699) (@lem7149698 _133751 s t u f)). Qed.
Lemma lem7149701 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) : (term84 _133751 s t f u) = (term76 _133751 s t u f).
Proof. exact (TRANS (@lem7149700 _133751 s t u f) (@lem7149695 _133751 s t u f)). Qed.
Lemma lem7149702 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (f : _133751 -> real) : (term85 _133751 s t f) = (term86 _133751 s t f).
Proof. exact (fun_ext (fun u : _133751 -> Prop => @lem7149701 _133751 s t u f)). Qed.
Lemma lem7149703 {_133751 : Type'} : (@ex (_133751 -> Prop)) = (@ex (_133751 -> Prop)).
Proof. exact (eq_refl (@ex (_133751 -> Prop))). Qed.
Lemma lem7149704 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (f : _133751 -> real) : (term82 _133751 s t f) = (term87 _133751 s t f).
Proof. exact (MK_COMB (@lem7149703 _133751) (@lem7149702 _133751 s t f)). Qed.
Lemma lem7149705 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (f : _133751 -> real) : (term81 _133751 s t f) = (term87 _133751 s t f).
Proof. exact (TRANS (@lem7149697 _133751 s t f) (@lem7149704 _133751 s t f)). Qed.
Lemma lem7149706 {_133751 : Type'} (P : type686 _133751) : (term79 _133751 P) = (term80 _133751 P).
Proof. exact (@lem18392 (_133751 -> Prop) P). Qed.
Lemma lem7149707 {_133751 : Type'} (s : _133751 -> Prop) (f : _133751 -> real) : (term88 _133751 s f) = (term89 _133751 s f).
Proof. exact (@lem7149706 _133751 (term72 _133751 s f)). Qed.
Lemma lem7149708 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (f : _133751 -> real) : (term90 _133751 s f t) = (term71 _133751 s t f).
Proof. exact (eq_refl (term90 _133751 s f t)). Qed.
Lemma lem7149709 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7149710 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (f : _133751 -> real) : (term91 _133751 s f t) = (term81 _133751 s t f).
Proof. exact (MK_COMB (@lem7149709) (@lem7149708 _133751 s t f)). Qed.
Lemma lem7149711 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (f : _133751 -> real) : (term91 _133751 s f t) = (term87 _133751 s t f).
Proof. exact (TRANS (@lem7149710 _133751 s t f) (@lem7149705 _133751 s t f)). Qed.
Lemma lem7149712 {_133751 : Type'} (s : _133751 -> Prop) (f : _133751 -> real) : (term92 _133751 s f) = (term93 _133751 s f).
Proof. exact (fun_ext (fun t : _133751 -> Prop => @lem7149711 _133751 s t f)). Qed.
Lemma lem7149713 {_133751 : Type'} : (@ex (_133751 -> Prop)) = (@ex (_133751 -> Prop)).
Proof. exact (eq_refl (@ex (_133751 -> Prop))). Qed.
Lemma lem7149714 {_133751 : Type'} (s : _133751 -> Prop) (f : _133751 -> real) : (term89 _133751 s f) = (term94 _133751 s f).
Proof. exact (MK_COMB (@lem7149713 _133751) (@lem7149712 _133751 s f)). Qed.
Lemma lem7149715 {_133751 : Type'} (s : _133751 -> Prop) (f : _133751 -> real) : (term88 _133751 s f) = (term94 _133751 s f).
Proof. exact (TRANS (@lem7149707 _133751 s f) (@lem7149714 _133751 s f)). Qed.
Lemma lem7149716 {_133751 : Type'} (P : type686 _133751) : (term79 _133751 P) = (term80 _133751 P).
Proof. exact (@lem18392 (_133751 -> Prop) P). Qed.
Lemma lem7149717 {_133751 : Type'} (f : _133751 -> real) : (term10 _133751 f) = (term95 _133751 f).
Proof. exact (@lem7149716 _133751 (term74 _133751 f)). Qed.
Lemma lem7149718 {_133751 : Type'} (s : _133751 -> Prop) (f : _133751 -> real) : (term96 _133751 f s) = (term73 _133751 s f).
Proof. exact (eq_refl (term96 _133751 f s)). Qed.
Lemma lem7149719 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7149720 {_133751 : Type'} (s : _133751 -> Prop) (f : _133751 -> real) : (term97 _133751 f s) = (term88 _133751 s f).
Proof. exact (MK_COMB (@lem7149719) (@lem7149718 _133751 s f)). Qed.
Lemma lem7149721 {_133751 : Type'} (s : _133751 -> Prop) (f : _133751 -> real) : (term97 _133751 f s) = (term94 _133751 s f).
Proof. exact (TRANS (@lem7149720 _133751 s f) (@lem7149715 _133751 s f)). Qed.
Lemma lem7149722 {_133751 : Type'} (f : _133751 -> real) : (term98 _133751 f) = (term99 _133751 f).
Proof. exact (fun_ext (fun s : _133751 -> Prop => @lem7149721 _133751 s f)). Qed.
Lemma lem7149723 {_133751 : Type'} : (@ex (_133751 -> Prop)) = (@ex (_133751 -> Prop)).
Proof. exact (eq_refl (@ex (_133751 -> Prop))). Qed.
Lemma lem7149724 {_133751 : Type'} (f : _133751 -> real) : (term95 _133751 f) = (term100 _133751 f).
Proof. exact (MK_COMB (@lem7149723 _133751) (@lem7149722 _133751 f)). Qed.
Lemma lem7149785 {_133751 : Type'} (f : _133751 -> real) : (term10 _133751 f) = (term100 _133751 f).
Proof. exact (TRANS (@lem7149717 _133751 f) (@lem7149724 _133751 f)). Qed.
Lemma lem7149786 {_133751 : Type'} (f : _133751 -> real) (h1 : term10 _133751 f) : term100 _133751 f.
Proof. exact (EQ_MP (@lem7149785 _133751 f) (@lem7149672 _133751 f h1)). Qed.
Lemma lem7149825 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) : (term63 _133751 s t) = (term63 _133751 s t).
Proof. exact (eq_refl (term63 _133751 s t)). Qed.
Lemma lem7149826 {_133751 : Type'} (s : _133751 -> Prop) : (term64 _133751 s) = (term64 _133751 s).
Proof. exact (fun_ext (fun t : _133751 -> Prop => @lem7149825 _133751 s t)). Qed.
Lemma lem7149827 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7149828 {_133751 : Type'} (s : _133751 -> Prop) : (term65 _133751 s) = (term65 _133751 s).
Proof. exact (MK_COMB (@lem7149827 _133751) (@lem7149826 _133751 s)). Qed.
Lemma lem7149829 {_133751 : Type'} : (term66 _133751) = (term66 _133751).
Proof. exact (fun_ext (fun s : _133751 -> Prop => @lem7149828 _133751 s)). Qed.
Lemma lem7149830 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7149831 {_133751 : Type'} : (term67 _133751) = (term67 _133751).
Proof. exact (MK_COMB (@lem7149830 _133751) (@lem7149829 _133751)). Qed.
Lemma lem7149832 {_133751 : Type'} (t : _133751 -> Prop) (s : _133751 -> Prop) : (term58 _133751 t s) = (term58 _133751 t s).
Proof. exact (eq_refl (term58 _133751 t s)). Qed.
Lemma lem7149833 {_133751 : Type'} (s : _133751 -> Prop) : (term59 _133751 s) = (term59 _133751 s).
Proof. exact (fun_ext (fun t : _133751 -> Prop => @lem7149832 _133751 t s)). Qed.
Lemma lem7149834 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7149835 {_133751 : Type'} (s : _133751 -> Prop) : (term60 _133751 s) = (term60 _133751 s).
Proof. exact (MK_COMB (@lem7149834 _133751) (@lem7149833 _133751 s)). Qed.
Lemma lem7149836 {_133751 : Type'} : (term61 _133751) = (term61 _133751).
Proof. exact (fun_ext (fun s : _133751 -> Prop => @lem7149835 _133751 s)). Qed.
Lemma lem7149837 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7149838 {_133751 : Type'} : (term62 _133751) = (term62 _133751).
Proof. exact (MK_COMB (@lem7149837 _133751) (@lem7149836 _133751)). Qed.
Lemma lem7149839 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7149840 {_133751 : Type'} : (term68 _133751) = (term68 _133751).
Proof. exact (MK_COMB (@lem7149839) (@lem7149831 _133751)). Qed.
Lemma lem7149861 {_133751 : Type'} : (term14 _133751) = (term14 _133751).
Proof. exact (MK_COMB (@lem7149840 _133751) (@lem7149838 _133751)). Qed.
Lemma lem7149862 {_133751 : Type'} (h1 : term14 _133751) : term14 _133751.
Proof. exact (EQ_MP (@lem7149861 _133751) (@lem7149674 _133751 h1)). Qed.
Lemma lem7150023 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) : (term101 _133751 s t) = (term102 _133751 s t).
Proof. exact (@lem17045 (@FINITE _133751 t) (@SUBSET _133751 s t)). Qed.
Lemma lem7150024 {_133751 : Type'} (s : _133751 -> Prop) : (@FINITE _133751 s) = (@FINITE _133751 s).
Proof. exact (eq_refl (@FINITE _133751 s)). Qed.
Lemma lem7150025 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7150026 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) : (term103 _133751 s t) = (term104 _133751 s t).
Proof. exact (MK_COMB (@lem7150025) (@lem7150023 _133751 s t)). Qed.
Lemma lem7150027 {_133751 : Type'} (t : _133751 -> Prop) (s : _133751 -> Prop) : (term105 _133751 t s) = (term106 _133751 t s).
Proof. exact (MK_COMB (@lem7150026 _133751 s t) (@lem7150024 _133751 s)). Qed.
Lemma lem7150028 {_133751 : Type'} (t : _133751 -> Prop) (s : _133751 -> Prop) : (term54 _133751 t s) = (term105 _133751 t s).
Proof. exact (@lem17265 (term107 _133751 s t) (@FINITE _133751 s)). Qed.
Lemma lem7150029 {_133751 : Type'} (t : _133751 -> Prop) (s : _133751 -> Prop) : (term54 _133751 t s) = (term106 _133751 t s).
Proof. exact (TRANS (@lem7150028 _133751 t s) (@lem7150027 _133751 t s)). Qed.
Lemma lem7150030 {_133751 : Type'} (s : _133751 -> Prop) : (term55 _133751 s) = (term108 _133751 s).
Proof. exact (fun_ext (fun t : _133751 -> Prop => @lem7150029 _133751 t s)). Qed.
Lemma lem7150031 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7150032 {_133751 : Type'} (s : _133751 -> Prop) : (term56 _133751 s) = (term109 _133751 s).
Proof. exact (MK_COMB (@lem7150031 _133751) (@lem7150030 _133751 s)). Qed.
Lemma lem7150033 {_133751 : Type'} : (term57 _133751) = (term110 _133751).
Proof. exact (fun_ext (fun s : _133751 -> Prop => @lem7150032 _133751 s)). Qed.
Lemma lem7150034 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7150035 {_133751 : Type'} : (term13 _133751) = (term111 _133751).
Proof. exact (MK_COMB (@lem7150034 _133751) (@lem7150033 _133751)). Qed.
Lemma lem7150061 {A : Type'} (P : A -> Prop) (Q : Prop) : (term112 A P Q) = (term113 A P Q).
Proof. exact (EQ_MP (@lem18947 A P Q) (@lem18946 A P Q)). Qed.
Lemma lem7150062 {_133751 : Type'} (P : type686 _133751) (Q : Prop) : (term114 _133751 P Q) = (term115 _133751 P Q).
Proof. exact (@lem7150061 (_133751 -> Prop) P Q). Qed.
Lemma lem7150063 {_133751 : Type'} (s : _133751 -> Prop) : (term116 _133751 s) = (term117 _133751 s).
Proof. exact (@lem7150062 _133751 (term118 _133751 s) (@FINITE _133751 s)). Qed.
Lemma lem7150064 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) : (term119 _133751 s t) = (term102 _133751 s t).
Proof. exact (eq_refl (term119 _133751 s t)). Qed.
Lemma lem7150065 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7150066 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) : (term120 _133751 s t) = (term104 _133751 s t).
Proof. exact (MK_COMB (@lem7150065) (@lem7150064 _133751 s t)). Qed.
Lemma lem7150067 {_133751 : Type'} (s : _133751 -> Prop) : (@FINITE _133751 s) = (@FINITE _133751 s).
Proof. exact (eq_refl (@FINITE _133751 s)). Qed.
Lemma lem7150068 {_133751 : Type'} (t : _133751 -> Prop) (s : _133751 -> Prop) : (term121 _133751 t s) = (term106 _133751 t s).
Proof. exact (MK_COMB (@lem7150066 _133751 s t) (@lem7150067 _133751 s)). Qed.
Lemma lem7150069 {_133751 : Type'} (s : _133751 -> Prop) : (term122 _133751 s) = (term108 _133751 s).
Proof. exact (fun_ext (fun t : _133751 -> Prop => @lem7150068 _133751 t s)). Qed.
Lemma lem7150070 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7150071 {_133751 : Type'} (s : _133751 -> Prop) : (term116 _133751 s) = (term109 _133751 s).
Proof. exact (MK_COMB (@lem7150070 _133751) (@lem7150069 _133751 s)). Qed.
Lemma lem7150072 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7150073 {_133751 : Type'} (s : _133751 -> Prop) : (term123 _133751 s) = (term124 _133751 s).
Proof. exact (MK_COMB (@lem7150072) (@lem7150071 _133751 s)). Qed.
Lemma lem7150074 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) : (term119 _133751 s t) = (term102 _133751 s t).
Proof. exact (eq_refl (term119 _133751 s t)). Qed.
Lemma lem7150075 {_133751 : Type'} (s : _133751 -> Prop) : (term125 _133751 s) = (term118 _133751 s).
Proof. exact (fun_ext (fun t : _133751 -> Prop => @lem7150074 _133751 s t)). Qed.
Lemma lem7150076 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7150077 {_133751 : Type'} (s : _133751 -> Prop) : (term126 _133751 s) = (term127 _133751 s).
Proof. exact (MK_COMB (@lem7150076 _133751) (@lem7150075 _133751 s)). Qed.
Lemma lem7150078 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7150079 {_133751 : Type'} (s : _133751 -> Prop) : (term128 _133751 s) = (term129 _133751 s).
Proof. exact (MK_COMB (@lem7150078) (@lem7150077 _133751 s)). Qed.
Lemma lem7150080 {_133751 : Type'} (s : _133751 -> Prop) : (@FINITE _133751 s) = (@FINITE _133751 s).
Proof. exact (eq_refl (@FINITE _133751 s)). Qed.
Lemma lem7150081 {_133751 : Type'} (s : _133751 -> Prop) : (term117 _133751 s) = (term130 _133751 s).
Proof. exact (MK_COMB (@lem7150079 _133751 s) (@lem7150080 _133751 s)). Qed.
Lemma lem7150082 {_133751 : Type'} (s : _133751 -> Prop) : ((term116 _133751 s) = (term117 _133751 s)) = ((term109 _133751 s) = (term130 _133751 s)).
Proof. exact (MK_COMB (@lem7150073 _133751 s) (@lem7150081 _133751 s)). Qed.
Lemma lem7150083 {_133751 : Type'} (s : _133751 -> Prop) : (term109 _133751 s) = (term130 _133751 s).
Proof. exact (EQ_MP (@lem7150082 _133751 s) (@lem7150063 _133751 s)). Qed.
Lemma lem7150132 {_133751 : Type'} : (term110 _133751) = (term131 _133751).
Proof. exact (fun_ext (fun s : _133751 -> Prop => @lem7150083 _133751 s)). Qed.
Lemma lem7150133 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7150168 {_133751 : Type'} : (term111 _133751) = (term132 _133751).
Proof. exact (MK_COMB (@lem7150133 _133751) (@lem7150132 _133751)). Qed.
Lemma lem7150169 {_133751 : Type'} : (term13 _133751) = (term132 _133751).
Proof. exact (TRANS (@lem7150035 _133751) (@lem7150168 _133751)). Qed.
Lemma lem7150170 {_133751 : Type'} (h1 : term13 _133751) : term132 _133751.
Proof. exact (EQ_MP (@lem7150169 _133751) (@lem7149676 _133751 h1)). Qed.
Lemma lem7150472 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) : ((@DISJOINT _133751 s t) = ((@INTER _133751 s t) = (@EMPTY _133751))) = (term133 _133751 s t).
Proof. exact (@lem17784 (@DISJOINT _133751 s t) ((@INTER _133751 s t) = (@EMPTY _133751))). Qed.
Lemma lem7150473 {_133751 : Type'} (s : _133751 -> Prop) : (term51 _133751 s) = (term134 _133751 s).
Proof. exact (fun_ext (fun t : _133751 -> Prop => @lem7150472 _133751 s t)). Qed.
Lemma lem7150474 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7150475 {_133751 : Type'} (s : _133751 -> Prop) : (term52 _133751 s) = (term135 _133751 s).
Proof. exact (MK_COMB (@lem7150474 _133751) (@lem7150473 _133751 s)). Qed.
Lemma lem7150476 {_133751 : Type'} : (term53 _133751) = (term136 _133751).
Proof. exact (fun_ext (fun s : _133751 -> Prop => @lem7150475 _133751 s)). Qed.
Lemma lem7150477 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7150478 {_133751 : Type'} : (term12 _133751) = (term137 _133751).
Proof. exact (MK_COMB (@lem7150477 _133751) (@lem7150476 _133751)). Qed.
Lemma lem7150484 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term138 A P Q) = (term139 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7150485 {_133751 : Type'} (P : type686 _133751) (Q : type686 _133751) : (term140 _133751 P Q) = (term141 _133751 P Q).
Proof. exact (@lem7150484 (_133751 -> Prop) P Q). Qed.
Lemma lem7150486 {_133751 : Type'} (s : _133751 -> Prop) : (term142 _133751 s) = (term143 _133751 s).
Proof. exact (@lem7150485 _133751 (term144 _133751 s) (term145 _133751 s)). Qed.
Lemma lem7150487 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) : (term146 _133751 s t) = (term147 _133751 s t).
Proof. exact (eq_refl (term146 _133751 s t)). Qed.
Lemma lem7150488 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7150489 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) : (term148 _133751 s t) = (term149 _133751 s t).
Proof. exact (MK_COMB (@lem7150488) (@lem7150487 _133751 s t)). Qed.
Lemma lem7150490 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) : (term150 _133751 s t) = (term151 _133751 s t).
Proof. exact (eq_refl (term150 _133751 s t)). Qed.
Lemma lem7150491 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) : (term152 _133751 s t) = (term133 _133751 s t).
Proof. exact (MK_COMB (@lem7150489 _133751 s t) (@lem7150490 _133751 s t)). Qed.
Lemma lem7150492 {_133751 : Type'} (s : _133751 -> Prop) : (term153 _133751 s) = (term134 _133751 s).
Proof. exact (fun_ext (fun t : _133751 -> Prop => @lem7150491 _133751 s t)). Qed.
Lemma lem7150493 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7150494 {_133751 : Type'} (s : _133751 -> Prop) : (term142 _133751 s) = (term135 _133751 s).
Proof. exact (MK_COMB (@lem7150493 _133751) (@lem7150492 _133751 s)). Qed.
Lemma lem7150495 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7150496 {_133751 : Type'} (s : _133751 -> Prop) : (term154 _133751 s) = (term155 _133751 s).
Proof. exact (MK_COMB (@lem7150495) (@lem7150494 _133751 s)). Qed.
Lemma lem7150497 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) : (term146 _133751 s t) = (term147 _133751 s t).
Proof. exact (eq_refl (term146 _133751 s t)). Qed.
Lemma lem7150498 {_133751 : Type'} (s : _133751 -> Prop) : (term156 _133751 s) = (term144 _133751 s).
Proof. exact (fun_ext (fun t : _133751 -> Prop => @lem7150497 _133751 s t)). Qed.
Lemma lem7150499 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7150500 {_133751 : Type'} (s : _133751 -> Prop) : (term157 _133751 s) = (term158 _133751 s).
Proof. exact (MK_COMB (@lem7150499 _133751) (@lem7150498 _133751 s)). Qed.
Lemma lem7150501 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7150502 {_133751 : Type'} (s : _133751 -> Prop) : (term159 _133751 s) = (term160 _133751 s).
Proof. exact (MK_COMB (@lem7150501) (@lem7150500 _133751 s)). Qed.
Lemma lem7150503 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) : (term150 _133751 s t) = (term151 _133751 s t).
Proof. exact (eq_refl (term150 _133751 s t)). Qed.
Lemma lem7150504 {_133751 : Type'} (s : _133751 -> Prop) : (term161 _133751 s) = (term145 _133751 s).
Proof. exact (fun_ext (fun t : _133751 -> Prop => @lem7150503 _133751 s t)). Qed.
Lemma lem7150505 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7150506 {_133751 : Type'} (s : _133751 -> Prop) : (term162 _133751 s) = (term163 _133751 s).
Proof. exact (MK_COMB (@lem7150505 _133751) (@lem7150504 _133751 s)). Qed.
Lemma lem7150507 {_133751 : Type'} (s : _133751 -> Prop) : (term143 _133751 s) = (term164 _133751 s).
Proof. exact (MK_COMB (@lem7150502 _133751 s) (@lem7150506 _133751 s)). Qed.
Lemma lem7150508 {_133751 : Type'} (s : _133751 -> Prop) : ((term142 _133751 s) = (term143 _133751 s)) = ((term135 _133751 s) = (term164 _133751 s)).
Proof. exact (MK_COMB (@lem7150496 _133751 s) (@lem7150507 _133751 s)). Qed.
Lemma lem7150509 {_133751 : Type'} (s : _133751 -> Prop) : (term135 _133751 s) = (term164 _133751 s).
Proof. exact (EQ_MP (@lem7150508 _133751 s) (@lem7150486 _133751 s)). Qed.
Lemma lem7150606 {_133751 : Type'} : (term136 _133751) = (term165 _133751).
Proof. exact (fun_ext (fun s : _133751 -> Prop => @lem7150509 _133751 s)). Qed.
Lemma lem7150607 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7150608 {_133751 : Type'} : (term137 _133751) = (term166 _133751).
Proof. exact (MK_COMB (@lem7150607 _133751) (@lem7150606 _133751)). Qed.
Lemma lem7150610 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term138 A P Q) = (term139 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7150611 {_133751 : Type'} (P : type686 _133751) (Q : type686 _133751) : (term140 _133751 P Q) = (term141 _133751 P Q).
Proof. exact (@lem7150610 (_133751 -> Prop) P Q). Qed.
Lemma lem7150612 {_133751 : Type'} : (term167 _133751) = (term168 _133751).
Proof. exact (@lem7150611 _133751 (term169 _133751) (term170 _133751)). Qed.
Lemma lem7150613 {_133751 : Type'} (s : _133751 -> Prop) : (term171 _133751 s) = (term158 _133751 s).
Proof. exact (eq_refl (term171 _133751 s)). Qed.
Lemma lem7150614 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7150615 {_133751 : Type'} (s : _133751 -> Prop) : (term172 _133751 s) = (term160 _133751 s).
Proof. exact (MK_COMB (@lem7150614) (@lem7150613 _133751 s)). Qed.
Lemma lem7150616 {_133751 : Type'} (s : _133751 -> Prop) : (term173 _133751 s) = (term163 _133751 s).
Proof. exact (eq_refl (term173 _133751 s)). Qed.
Lemma lem7150617 {_133751 : Type'} (s : _133751 -> Prop) : (term174 _133751 s) = (term164 _133751 s).
Proof. exact (MK_COMB (@lem7150615 _133751 s) (@lem7150616 _133751 s)). Qed.
Lemma lem7150618 {_133751 : Type'} : (term175 _133751) = (term165 _133751).
Proof. exact (fun_ext (fun s : _133751 -> Prop => @lem7150617 _133751 s)). Qed.
Lemma lem7150619 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7150620 {_133751 : Type'} : (term167 _133751) = (term166 _133751).
Proof. exact (MK_COMB (@lem7150619 _133751) (@lem7150618 _133751)). Qed.
Lemma lem7150621 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7150622 {_133751 : Type'} : (term176 _133751) = (term177 _133751).
Proof. exact (MK_COMB (@lem7150621) (@lem7150620 _133751)). Qed.
Lemma lem7150623 {_133751 : Type'} (s : _133751 -> Prop) : (term171 _133751 s) = (term158 _133751 s).
Proof. exact (eq_refl (term171 _133751 s)). Qed.
Lemma lem7150624 {_133751 : Type'} : (term178 _133751) = (term169 _133751).
Proof. exact (fun_ext (fun s : _133751 -> Prop => @lem7150623 _133751 s)). Qed.
Lemma lem7150625 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7150626 {_133751 : Type'} : (term179 _133751) = (term180 _133751).
Proof. exact (MK_COMB (@lem7150625 _133751) (@lem7150624 _133751)). Qed.
Lemma lem7150627 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7150628 {_133751 : Type'} : (term181 _133751) = (term182 _133751).
Proof. exact (MK_COMB (@lem7150627) (@lem7150626 _133751)). Qed.
Lemma lem7150629 {_133751 : Type'} (s : _133751 -> Prop) : (term173 _133751 s) = (term163 _133751 s).
Proof. exact (eq_refl (term173 _133751 s)). Qed.
Lemma lem7150630 {_133751 : Type'} : (term183 _133751) = (term170 _133751).
Proof. exact (fun_ext (fun s : _133751 -> Prop => @lem7150629 _133751 s)). Qed.
Lemma lem7150631 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7150632 {_133751 : Type'} : (term184 _133751) = (term185 _133751).
Proof. exact (MK_COMB (@lem7150631 _133751) (@lem7150630 _133751)). Qed.
Lemma lem7150633 {_133751 : Type'} : (term168 _133751) = (term186 _133751).
Proof. exact (MK_COMB (@lem7150628 _133751) (@lem7150632 _133751)). Qed.
Lemma lem7150634 {_133751 : Type'} : ((term167 _133751) = (term168 _133751)) = ((term166 _133751) = (term186 _133751)).
Proof. exact (MK_COMB (@lem7150622 _133751) (@lem7150633 _133751)). Qed.
Lemma lem7150635 {_133751 : Type'} : (term166 _133751) = (term186 _133751).
Proof. exact (EQ_MP (@lem7150634 _133751) (@lem7150612 _133751)). Qed.
Lemma lem7150742 {_133751 : Type'} : (term137 _133751) = (term186 _133751).
Proof. exact (TRANS (@lem7150608 _133751) (@lem7150635 _133751)). Qed.
Lemma lem7150743 {_133751 : Type'} : (term12 _133751) = (term186 _133751).
Proof. exact (TRANS (@lem7150478 _133751) (@lem7150742 _133751)). Qed.
Lemma lem7150744 {_133751 : Type'} (h1 : term12 _133751) : term186 _133751.
Proof. exact (EQ_MP (@lem7150743 _133751) (@lem7149678 _133751 h1)). Qed.
Lemma lem7150841 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) : (term187 _133751 s t) = (term188 _133751 s t).
Proof. exact (@lem17045 (@FINITE _133751 t) (@DISJOINT _133751 s t)). Qed.
Lemma lem7150843 {_133751 : Type'} (s : _133751 -> Prop) : (term189 _133751 s) = (term189 _133751 s).
Proof. exact (eq_refl (term189 _133751 s)). Qed.
Lemma lem7150844 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) : (term190 _133751 s t) = (term191 _133751 s t).
Proof. exact (MK_COMB (@lem7150843 _133751 s) (@lem7150841 _133751 s t)). Qed.
Lemma lem7150845 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) : (term192 _133751 s t) = (term190 _133751 s t).
Proof. exact (@lem17045 (@FINITE _133751 s) (term193 _133751 s t)). Qed.
Lemma lem7150846 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) : (term192 _133751 s t) = (term191 _133751 s t).
Proof. exact (TRANS (@lem7150845 _133751 s t) (@lem7150844 _133751 s t)). Qed.
Lemma lem7150847 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (f : _133751 -> real) : ((term194 _133751 s t f) = (term78 _133751 s t f)) = ((term194 _133751 s t f) = (term78 _133751 s t f)).
Proof. exact (eq_refl ((term194 _133751 s t f) = (term78 _133751 s t f))). Qed.
Lemma lem7150848 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7150849 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) : (term195 _133751 s t) = (term196 _133751 s t).
Proof. exact (MK_COMB (@lem7150848) (@lem7150846 _133751 s t)). Qed.
Lemma lem7150850 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (f : _133751 -> real) : (term197 _133751 s t f) = (term198 _133751 s t f).
Proof. exact (MK_COMB (@lem7150849 _133751 s t) (@lem7150847 _133751 s t f)). Qed.
Lemma lem7150851 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (f : _133751 -> real) : (term45 _133751 s t f) = (term197 _133751 s t f).
Proof. exact (@lem17265 (term199 _133751 s t) ((term194 _133751 s t f) = (term78 _133751 s t f))). Qed.
Lemma lem7150852 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (f : _133751 -> real) : (term45 _133751 s t f) = (term198 _133751 s t f).
Proof. exact (TRANS (@lem7150851 _133751 s t f) (@lem7150850 _133751 s t f)). Qed.
Lemma lem7150853 {_133751 : Type'} (s : _133751 -> Prop) (f : _133751 -> real) : (term46 _133751 s f) = (term200 _133751 s f).
Proof. exact (fun_ext (fun t : _133751 -> Prop => @lem7150852 _133751 s t f)). Qed.
Lemma lem7150854 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7150855 {_133751 : Type'} (s : _133751 -> Prop) (f : _133751 -> real) : (term47 _133751 s f) = (term201 _133751 s f).
Proof. exact (MK_COMB (@lem7150854 _133751) (@lem7150853 _133751 s f)). Qed.
Lemma lem7150856 {_133751 : Type'} (f : _133751 -> real) : (term48 _133751 f) = (term202 _133751 f).
Proof. exact (fun_ext (fun s : _133751 -> Prop => @lem7150855 _133751 s f)). Qed.
Lemma lem7150857 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7150858 {_133751 : Type'} (f : _133751 -> real) : (term49 _133751 f) = (term203 _133751 f).
Proof. exact (MK_COMB (@lem7150857 _133751) (@lem7150856 _133751 f)). Qed.
Lemma lem7150859 {_133751 : Type'} : (term50 _133751) = (term204 _133751).
Proof. exact (fun_ext (fun f : _133751 -> real => @lem7150858 _133751 f)). Qed.
Lemma lem7150860 {_133751 : Type'} : (@all (_133751 -> real)) = (@all (_133751 -> real)).
Proof. exact (eq_refl (@all (_133751 -> real))). Qed.
Lemma lem7150921 {_133751 : Type'} : (term11 _133751) = (term205 _133751).
Proof. exact (MK_COMB (@lem7150860 _133751) (@lem7150859 _133751)). Qed.
Lemma lem7150922 {_133751 : Type'} (h1 : term11 _133751) : term205 _133751.
Proof. exact (EQ_MP (@lem7150921 _133751) (@lem7149680 _133751 h1)). Qed.
Lemma lem7150923 {_133751 : Type'} (s : _133751 -> Prop) (f : _133751 -> real) (h1 : term94 _133751 s f) : term94 _133751 s f.
Proof. exact (h1). Qed.
Lemma lem7150924 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (f : _133751 -> real) (h1 : term87 _133751 s t f) : term87 _133751 s t f.
Proof. exact (h1). Qed.
Lemma lem7150968 {_133751 : Type'} (t : _133751 -> Prop) (s : _133751 -> Prop) : (term58 _133751 t s) = (term58 _133751 t s).
Proof. exact (eq_refl (term58 _133751 t s)). Qed.
Lemma lem7150969 {_133751 : Type'} (s : _133751 -> Prop) : (term59 _133751 s) = (term59 _133751 s).
Proof. exact (fun_ext (fun t : _133751 -> Prop => @lem7150968 _133751 t s)). Qed.
Lemma lem7150970 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7150971 {_133751 : Type'} (s : _133751 -> Prop) : (term60 _133751 s) = (term60 _133751 s).
Proof. exact (MK_COMB (@lem7150970 _133751) (@lem7150969 _133751 s)). Qed.
Lemma lem7150972 {_133751 : Type'} : (term61 _133751) = (term61 _133751).
Proof. exact (fun_ext (fun s : _133751 -> Prop => @lem7150971 _133751 s)). Qed.
Lemma lem7150973 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7150974 {_133751 : Type'} : (term62 _133751) = (term62 _133751).
Proof. exact (MK_COMB (@lem7150973 _133751) (@lem7150972 _133751)). Qed.
Lemma lem7150983 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) : (term63 _133751 s t) = (term63 _133751 s t).
Proof. exact (eq_refl (term63 _133751 s t)). Qed.
Lemma lem7150984 {_133751 : Type'} (s : _133751 -> Prop) : (term64 _133751 s) = (term64 _133751 s).
Proof. exact (fun_ext (fun t : _133751 -> Prop => @lem7150983 _133751 s t)). Qed.
Lemma lem7150985 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7150986 {_133751 : Type'} (s : _133751 -> Prop) : (term65 _133751 s) = (term65 _133751 s).
Proof. exact (MK_COMB (@lem7150985 _133751) (@lem7150984 _133751 s)). Qed.
Lemma lem7150987 {_133751 : Type'} : (term66 _133751) = (term66 _133751).
Proof. exact (fun_ext (fun s : _133751 -> Prop => @lem7150986 _133751 s)). Qed.
Lemma lem7150988 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7150989 {_133751 : Type'} : (term67 _133751) = (term67 _133751).
Proof. exact (MK_COMB (@lem7150988 _133751) (@lem7150987 _133751)). Qed.
Lemma lem7150990 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7150991 {_133751 : Type'} : (term68 _133751) = (term68 _133751).
Proof. exact (MK_COMB (@lem7150990) (@lem7150989 _133751)). Qed.
Lemma lem7150992 {_133751 : Type'} : (term14 _133751) = (term14 _133751).
Proof. exact (MK_COMB (@lem7150991 _133751) (@lem7150974 _133751)). Qed.
Lemma lem7150993 {_133751 : Type'} (h1 : term14 _133751) : term14 _133751.
Proof. exact (EQ_MP (@lem7150992 _133751) (@lem7149862 _133751 h1)). Qed.
Lemma lem7151024 {_133751 : Type'} (s : _133751 -> Prop) : (@FINITE _133751 s) = (@FINITE _133751 s).
Proof. exact (eq_refl (@FINITE _133751 s)). Qed.
Lemma lem7151039 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) : (term102 _133751 s t) = (term102 _133751 s t).
Proof. exact (eq_refl (term102 _133751 s t)). Qed.
Lemma lem7151040 {_133751 : Type'} (s : _133751 -> Prop) : (term118 _133751 s) = (term118 _133751 s).
Proof. exact (fun_ext (fun t : _133751 -> Prop => @lem7151039 _133751 s t)). Qed.
Lemma lem7151041 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7151042 {_133751 : Type'} (s : _133751 -> Prop) : (term127 _133751 s) = (term127 _133751 s).
Proof. exact (MK_COMB (@lem7151041 _133751) (@lem7151040 _133751 s)). Qed.
Lemma lem7151043 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7151044 {_133751 : Type'} (s : _133751 -> Prop) : (term129 _133751 s) = (term129 _133751 s).
Proof. exact (MK_COMB (@lem7151043) (@lem7151042 _133751 s)). Qed.
Lemma lem7151045 {_133751 : Type'} (s : _133751 -> Prop) : (term130 _133751 s) = (term130 _133751 s).
Proof. exact (MK_COMB (@lem7151044 _133751 s) (@lem7151024 _133751 s)). Qed.
Lemma lem7151046 {_133751 : Type'} : (term131 _133751) = (term131 _133751).
Proof. exact (fun_ext (fun s : _133751 -> Prop => @lem7151045 _133751 s)). Qed.
Lemma lem7151047 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7151048 {_133751 : Type'} : (term132 _133751) = (term132 _133751).
Proof. exact (MK_COMB (@lem7151047 _133751) (@lem7151046 _133751)). Qed.
Lemma lem7151049 {_133751 : Type'} (h1 : term13 _133751) : term132 _133751.
Proof. exact (EQ_MP (@lem7151048 _133751) (@lem7150170 _133751 h1)). Qed.
Lemma lem7151122 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) : (term151 _133751 s t) = (term151 _133751 s t).
Proof. exact (eq_refl (term151 _133751 s t)). Qed.
Lemma lem7151123 {_133751 : Type'} (s : _133751 -> Prop) : (term145 _133751 s) = (term145 _133751 s).
Proof. exact (fun_ext (fun t : _133751 -> Prop => @lem7151122 _133751 s t)). Qed.
Lemma lem7151124 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7151125 {_133751 : Type'} (s : _133751 -> Prop) : (term163 _133751 s) = (term163 _133751 s).
Proof. exact (MK_COMB (@lem7151124 _133751) (@lem7151123 _133751 s)). Qed.
Lemma lem7151126 {_133751 : Type'} : (term170 _133751) = (term170 _133751).
Proof. exact (fun_ext (fun s : _133751 -> Prop => @lem7151125 _133751 s)). Qed.
Lemma lem7151127 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7151128 {_133751 : Type'} : (term185 _133751) = (term185 _133751).
Proof. exact (MK_COMB (@lem7151127 _133751) (@lem7151126 _133751)). Qed.
Lemma lem7151147 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) : (term147 _133751 s t) = (term147 _133751 s t).
Proof. exact (eq_refl (term147 _133751 s t)). Qed.
Lemma lem7151148 {_133751 : Type'} (s : _133751 -> Prop) : (term144 _133751 s) = (term144 _133751 s).
Proof. exact (fun_ext (fun t : _133751 -> Prop => @lem7151147 _133751 s t)). Qed.
Lemma lem7151149 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7151150 {_133751 : Type'} (s : _133751 -> Prop) : (term158 _133751 s) = (term158 _133751 s).
Proof. exact (MK_COMB (@lem7151149 _133751) (@lem7151148 _133751 s)). Qed.
Lemma lem7151151 {_133751 : Type'} : (term169 _133751) = (term169 _133751).
Proof. exact (fun_ext (fun s : _133751 -> Prop => @lem7151150 _133751 s)). Qed.
Lemma lem7151152 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7151153 {_133751 : Type'} : (term180 _133751) = (term180 _133751).
Proof. exact (MK_COMB (@lem7151152 _133751) (@lem7151151 _133751)). Qed.
Lemma lem7151154 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7151155 {_133751 : Type'} : (term182 _133751) = (term182 _133751).
Proof. exact (MK_COMB (@lem7151154) (@lem7151153 _133751)). Qed.
Lemma lem7151156 {_133751 : Type'} : (term186 _133751) = (term186 _133751).
Proof. exact (MK_COMB (@lem7151155 _133751) (@lem7151128 _133751)). Qed.
Lemma lem7151157 {_133751 : Type'} (h1 : term12 _133751) : term186 _133751.
Proof. exact (EQ_MP (@lem7151156 _133751) (@lem7150744 _133751 h1)). Qed.
Lemma lem7151269 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (f : _133751 -> real) : (term198 _133751 s t f) = (term198 _133751 s t f).
Proof. exact (eq_refl (term198 _133751 s t f)). Qed.
Lemma lem7151270 {_133751 : Type'} (s : _133751 -> Prop) (f : _133751 -> real) : (term200 _133751 s f) = (term200 _133751 s f).
Proof. exact (fun_ext (fun t : _133751 -> Prop => @lem7151269 _133751 s t f)). Qed.
Lemma lem7151271 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7151272 {_133751 : Type'} (s : _133751 -> Prop) (f : _133751 -> real) : (term201 _133751 s f) = (term201 _133751 s f).
Proof. exact (MK_COMB (@lem7151271 _133751) (@lem7151270 _133751 s f)). Qed.
Lemma lem7151273 {_133751 : Type'} (f : _133751 -> real) : (term202 _133751 f) = (term202 _133751 f).
Proof. exact (fun_ext (fun s : _133751 -> Prop => @lem7151272 _133751 s f)). Qed.
Lemma lem7151274 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7151275 {_133751 : Type'} (f : _133751 -> real) : (term203 _133751 f) = (term203 _133751 f).
Proof. exact (MK_COMB (@lem7151274 _133751) (@lem7151273 _133751 f)). Qed.
Lemma lem7151276 {_133751 : Type'} : (term204 _133751) = (term204 _133751).
Proof. exact (fun_ext (fun f : _133751 -> real => @lem7151275 _133751 f)). Qed.
Lemma lem7151277 {_133751 : Type'} : (@all (_133751 -> real)) = (@all (_133751 -> real)).
Proof. exact (eq_refl (@all (_133751 -> real))). Qed.
Lemma lem7151278 {_133751 : Type'} : (term205 _133751) = (term205 _133751).
Proof. exact (MK_COMB (@lem7151277 _133751) (@lem7151276 _133751)). Qed.
Lemma lem7151279 {_133751 : Type'} (h1 : term11 _133751) : term205 _133751.
Proof. exact (EQ_MP (@lem7151278 _133751) (@lem7150922 _133751 h1)). Qed.
Lemma lem7151333 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term76 _133751 s t u f) : term76 _133751 s t u f.
Proof. exact (h1). Qed.
Lemma lem7151335 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term76 _133751 s t u f) : term77 _133751 s t u.
Proof. exact (proj1 (@lem7151333 _133751 s t u f h1)). Qed.
Lemma lem7151336 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term76 _133751 s t u f) : term206 _133751 s t u.
Proof. exact (proj2 (@lem7151335 _133751 s t u f h1)). Qed.
Lemma lem7151341 {_133751 : Type'} (h1 : term12 _133751) : term180 _133751.
Proof. exact (proj1 (@lem7151157 _133751 h1)). Qed.
Lemma lem7151344 {_133751 : Type'} (h1 : term14 _133751) : term62 _133751.
Proof. exact (proj2 (@lem7150993 _133751 h1)). Qed.
Lemma lem7151345 {_133751 : Type'} (h1 : term14 _133751) : term67 _133751.
Proof. exact (proj1 (@lem7150993 _133751 h1)). Qed.
Lemma lem7151397 {A : Type'} (P : A -> Prop) (Q : Prop) : (term113 A P Q) = (term112 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem7151398 {_133751 : Type'} (P : type686 _133751) (Q : Prop) : (term115 _133751 P Q) = (term114 _133751 P Q).
Proof. exact (@lem7151397 (_133751 -> Prop) P Q). Qed.
Lemma lem7151399 {_133751 : Type'} (s : _133751 -> Prop) : (term117 _133751 s) = (term116 _133751 s).
Proof. exact (@lem7151398 _133751 (term118 _133751 s) (@FINITE _133751 s)). Qed.
Lemma lem7151400 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) : (term119 _133751 s t) = (term102 _133751 s t).
Proof. exact (eq_refl (term119 _133751 s t)). Qed.
Lemma lem7151401 {_133751 : Type'} (s : _133751 -> Prop) : (term125 _133751 s) = (term118 _133751 s).
Proof. exact (fun_ext (fun t : _133751 -> Prop => @lem7151400 _133751 s t)). Qed.
Lemma lem7151402 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7151403 {_133751 : Type'} (s : _133751 -> Prop) : (term126 _133751 s) = (term127 _133751 s).
Proof. exact (MK_COMB (@lem7151402 _133751) (@lem7151401 _133751 s)). Qed.
Lemma lem7151404 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7151405 {_133751 : Type'} (s : _133751 -> Prop) : (term128 _133751 s) = (term129 _133751 s).
Proof. exact (MK_COMB (@lem7151404) (@lem7151403 _133751 s)). Qed.
Lemma lem7151406 {_133751 : Type'} (s : _133751 -> Prop) : (@FINITE _133751 s) = (@FINITE _133751 s).
Proof. exact (eq_refl (@FINITE _133751 s)). Qed.
Lemma lem7151407 {_133751 : Type'} (s : _133751 -> Prop) : (term117 _133751 s) = (term130 _133751 s).
Proof. exact (MK_COMB (@lem7151405 _133751 s) (@lem7151406 _133751 s)). Qed.
Lemma lem7151408 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7151409 {_133751 : Type'} (s : _133751 -> Prop) : (term207 _133751 s) = (term208 _133751 s).
Proof. exact (MK_COMB (@lem7151408) (@lem7151407 _133751 s)). Qed.
Lemma lem7151410 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) : (term119 _133751 s t) = (term102 _133751 s t).
Proof. exact (eq_refl (term119 _133751 s t)). Qed.
Lemma lem7151411 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7151412 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) : (term120 _133751 s t) = (term104 _133751 s t).
Proof. exact (MK_COMB (@lem7151411) (@lem7151410 _133751 s t)). Qed.
Lemma lem7151413 {_133751 : Type'} (s : _133751 -> Prop) : (@FINITE _133751 s) = (@FINITE _133751 s).
Proof. exact (eq_refl (@FINITE _133751 s)). Qed.
Lemma lem7151414 {_133751 : Type'} (t : _133751 -> Prop) (s : _133751 -> Prop) : (term121 _133751 t s) = (term106 _133751 t s).
Proof. exact (MK_COMB (@lem7151412 _133751 s t) (@lem7151413 _133751 s)). Qed.
Lemma lem7151415 {_133751 : Type'} (s : _133751 -> Prop) : (term122 _133751 s) = (term108 _133751 s).
Proof. exact (fun_ext (fun t : _133751 -> Prop => @lem7151414 _133751 t s)). Qed.
Lemma lem7151416 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7151417 {_133751 : Type'} (s : _133751 -> Prop) : (term116 _133751 s) = (term109 _133751 s).
Proof. exact (MK_COMB (@lem7151416 _133751) (@lem7151415 _133751 s)). Qed.
Lemma lem7151418 {_133751 : Type'} (s : _133751 -> Prop) : ((term117 _133751 s) = (term116 _133751 s)) = ((term130 _133751 s) = (term109 _133751 s)).
Proof. exact (MK_COMB (@lem7151409 _133751 s) (@lem7151417 _133751 s)). Qed.
Lemma lem7151419 {_133751 : Type'} (s : _133751 -> Prop) : (term130 _133751 s) = (term109 _133751 s).
Proof. exact (EQ_MP (@lem7151418 _133751 s) (@lem7151399 _133751 s)). Qed.
Lemma lem7151420 {_133751 : Type'} : (term131 _133751) = (term110 _133751).
Proof. exact (fun_ext (fun s : _133751 -> Prop => @lem7151419 _133751 s)). Qed.
Lemma lem7151421 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7151422 {_133751 : Type'} : (term132 _133751) = (term111 _133751).
Proof. exact (MK_COMB (@lem7151421 _133751) (@lem7151420 _133751)). Qed.
Lemma lem7151435 {_133751 : Type'} (t : _133751 -> Prop) (s : _133751 -> Prop) : (term106 _133751 t s) = (term106 _133751 t s).
Proof. exact (eq_refl (term106 _133751 t s)). Qed.
Lemma lem7151436 {_133751 : Type'} (s : _133751 -> Prop) : (term108 _133751 s) = (term108 _133751 s).
Proof. exact (fun_ext (fun t : _133751 -> Prop => @lem7151435 _133751 t s)). Qed.
Lemma lem7151437 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7151438 {_133751 : Type'} (s : _133751 -> Prop) : (term109 _133751 s) = (term109 _133751 s).
Proof. exact (MK_COMB (@lem7151437 _133751) (@lem7151436 _133751 s)). Qed.
Lemma lem7151439 {_133751 : Type'} : (term110 _133751) = (term110 _133751).
Proof. exact (fun_ext (fun s : _133751 -> Prop => @lem7151438 _133751 s)). Qed.
Lemma lem7151440 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7151441 {_133751 : Type'} : (term111 _133751) = (term111 _133751).
Proof. exact (MK_COMB (@lem7151440 _133751) (@lem7151439 _133751)). Qed.
Lemma lem7151442 {_133751 : Type'} : (term132 _133751) = (term111 _133751).
Proof. exact (TRANS (@lem7151422 _133751) (@lem7151441 _133751)). Qed.
Lemma lem7151443 {_133751 : Type'} (h1 : term13 _133751) : term111 _133751.
Proof. exact (EQ_MP (@lem7151442 _133751) (@lem7151049 _133751 h1)). Qed.
Lemma lem7151494 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (f : _133751 -> real) : (term198 _133751 s t f) = (term198 _133751 s t f).
Proof. exact (eq_refl (term198 _133751 s t f)). Qed.
Lemma lem7151495 {_133751 : Type'} (s : _133751 -> Prop) (f : _133751 -> real) : (term200 _133751 s f) = (term200 _133751 s f).
Proof. exact (fun_ext (fun t : _133751 -> Prop => @lem7151494 _133751 s t f)). Qed.
Lemma lem7151496 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7151497 {_133751 : Type'} (s : _133751 -> Prop) (f : _133751 -> real) : (term201 _133751 s f) = (term201 _133751 s f).
Proof. exact (MK_COMB (@lem7151496 _133751) (@lem7151495 _133751 s f)). Qed.
Lemma lem7151498 {_133751 : Type'} (f : _133751 -> real) : (term202 _133751 f) = (term202 _133751 f).
Proof. exact (fun_ext (fun s : _133751 -> Prop => @lem7151497 _133751 s f)). Qed.
Lemma lem7151499 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7151500 {_133751 : Type'} (f : _133751 -> real) : (term203 _133751 f) = (term203 _133751 f).
Proof. exact (MK_COMB (@lem7151499 _133751) (@lem7151498 _133751 f)). Qed.
Lemma lem7151501 {_133751 : Type'} : (term204 _133751) = (term204 _133751).
Proof. exact (fun_ext (fun f : _133751 -> real => @lem7151500 _133751 f)). Qed.
Lemma lem7151502 {_133751 : Type'} : (@all (_133751 -> real)) = (@all (_133751 -> real)).
Proof. exact (eq_refl (@all (_133751 -> real))). Qed.
Lemma lem7151504 {_133751 : Type'} : (term205 _133751) = (term205 _133751).
Proof. exact (MK_COMB (@lem7151502 _133751) (@lem7151501 _133751)). Qed.
Lemma lem7151505 {_133751 : Type'} (h1 : term11 _133751) : term205 _133751.
Proof. exact (EQ_MP (@lem7151504 _133751) (@lem7151279 _133751 h1)). Qed.
Lemma lem7151529 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) : (term147 _133751 s t) = (term147 _133751 s t).
Proof. exact (eq_refl (term147 _133751 s t)). Qed.
Lemma lem7151530 {_133751 : Type'} (s : _133751 -> Prop) : (term144 _133751 s) = (term144 _133751 s).
Proof. exact (fun_ext (fun t : _133751 -> Prop => @lem7151529 _133751 s t)). Qed.
Lemma lem7151531 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7151532 {_133751 : Type'} (s : _133751 -> Prop) : (term158 _133751 s) = (term158 _133751 s).
Proof. exact (MK_COMB (@lem7151531 _133751) (@lem7151530 _133751 s)). Qed.
Lemma lem7151533 {_133751 : Type'} : (term169 _133751) = (term169 _133751).
Proof. exact (fun_ext (fun s : _133751 -> Prop => @lem7151532 _133751 s)). Qed.
Lemma lem7151534 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7151536 {_133751 : Type'} : (term180 _133751) = (term180 _133751).
Proof. exact (MK_COMB (@lem7151534 _133751) (@lem7151533 _133751)). Qed.
Lemma lem7151537 {_133751 : Type'} (h1 : term12 _133751) : term180 _133751.
Proof. exact (EQ_MP (@lem7151536 _133751) (@lem7151341 _133751 h1)). Qed.
Lemma lem7151587 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) : (term63 _133751 s t) = (term63 _133751 s t).
Proof. exact (eq_refl (term63 _133751 s t)). Qed.
Lemma lem7151588 {_133751 : Type'} (s : _133751 -> Prop) : (term64 _133751 s) = (term64 _133751 s).
Proof. exact (fun_ext (fun t : _133751 -> Prop => @lem7151587 _133751 s t)). Qed.
Lemma lem7151589 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7151590 {_133751 : Type'} (s : _133751 -> Prop) : (term65 _133751 s) = (term65 _133751 s).
Proof. exact (MK_COMB (@lem7151589 _133751) (@lem7151588 _133751 s)). Qed.
Lemma lem7151591 {_133751 : Type'} : (term66 _133751) = (term66 _133751).
Proof. exact (fun_ext (fun s : _133751 -> Prop => @lem7151590 _133751 s)). Qed.
Lemma lem7151592 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7151594 {_133751 : Type'} : (term67 _133751) = (term67 _133751).
Proof. exact (MK_COMB (@lem7151592 _133751) (@lem7151591 _133751)). Qed.
Lemma lem7151595 {_133751 : Type'} (h1 : term14 _133751) : term67 _133751.
Proof. exact (EQ_MP (@lem7151594 _133751) (@lem7151345 _133751 h1)). Qed.
Lemma lem7151597 {_133751 : Type'} (t : _133751 -> Prop) (s : _133751 -> Prop) : (term58 _133751 t s) = (term58 _133751 t s).
Proof. exact (eq_refl (term58 _133751 t s)). Qed.
Lemma lem7151598 {_133751 : Type'} (s : _133751 -> Prop) : (term59 _133751 s) = (term59 _133751 s).
Proof. exact (fun_ext (fun t : _133751 -> Prop => @lem7151597 _133751 t s)). Qed.
Lemma lem7151599 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7151600 {_133751 : Type'} (s : _133751 -> Prop) : (term60 _133751 s) = (term60 _133751 s).
Proof. exact (MK_COMB (@lem7151599 _133751) (@lem7151598 _133751 s)). Qed.
Lemma lem7151601 {_133751 : Type'} : (term61 _133751) = (term61 _133751).
Proof. exact (fun_ext (fun s : _133751 -> Prop => @lem7151600 _133751 s)). Qed.
Lemma lem7151602 {_133751 : Type'} : (@all (_133751 -> Prop)) = (@all (_133751 -> Prop)).
Proof. exact (eq_refl (@all (_133751 -> Prop))). Qed.
Lemma lem7151604 {_133751 : Type'} : (term62 _133751) = (term62 _133751).
Proof. exact (MK_COMB (@lem7151602 _133751) (@lem7151601 _133751)). Qed.
Lemma lem7151605 {_133751 : Type'} (h1 : term14 _133751) : term62 _133751.
Proof. exact (EQ_MP (@lem7151604 _133751) (@lem7151344 _133751 h1)). Qed.
Lemma lem7151632 {_133751 : Type'} (_95597 : _133751 -> Prop) (h1 : term13 _133751) : term209 _133751 _95597.
Proof. exact (@lem7151443 _133751 h1 _95597). Qed.
Lemma lem7151633 {_133751 : Type'} (_95597 : _133751 -> Prop) : (term209 _133751 _95597) = (term109 _133751 _95597).
Proof. exact (eq_refl (term209 _133751 _95597)). Qed.
Lemma lem7151634 {_133751 : Type'} (_95597 : _133751 -> Prop) (h1 : term13 _133751) : term109 _133751 _95597.
Proof. exact (EQ_MP (@lem7151633 _133751 _95597) (@lem7151632 _133751 _95597 h1)). Qed.
Lemma lem7151635 {_133751 : Type'} (_95597 : _133751 -> Prop) (_95598 : _133751 -> Prop) (h1 : term13 _133751) : term210 _133751 _95597 _95598.
Proof. exact (@lem7151634 _133751 _95597 h1 _95598). Qed.
Lemma lem7151636 {_133751 : Type'} (_95598 : _133751 -> Prop) (_95597 : _133751 -> Prop) : (term210 _133751 _95597 _95598) = (term106 _133751 _95598 _95597).
Proof. exact (eq_refl (term210 _133751 _95597 _95598)). Qed.
Lemma lem7151637 {_133751 : Type'} (_95598 : _133751 -> Prop) (_95597 : _133751 -> Prop) (h1 : term13 _133751) : term106 _133751 _95598 _95597.
Proof. exact (EQ_MP (@lem7151636 _133751 _95598 _95597) (@lem7151635 _133751 _95597 _95598 h1)). Qed.
Lemma lem7151647 {_133751 : Type'} (_95602 : _133751 -> real) (h1 : term11 _133751) : term211 _133751 _95602.
Proof. exact (@lem7151505 _133751 h1 _95602). Qed.
Lemma lem7151648 {_133751 : Type'} (_95602 : _133751 -> real) : (term211 _133751 _95602) = (term203 _133751 _95602).
Proof. exact (eq_refl (term211 _133751 _95602)). Qed.
Lemma lem7151649 {_133751 : Type'} (_95602 : _133751 -> real) (h1 : term11 _133751) : term203 _133751 _95602.
Proof. exact (EQ_MP (@lem7151648 _133751 _95602) (@lem7151647 _133751 _95602 h1)). Qed.
Lemma lem7151650 {_133751 : Type'} (_95602 : _133751 -> real) (_95603 : _133751 -> Prop) (h1 : term11 _133751) : term212 _133751 _95602 _95603.
Proof. exact (@lem7151649 _133751 _95602 h1 _95603). Qed.
Lemma lem7151651 {_133751 : Type'} (_95603 : _133751 -> Prop) (_95602 : _133751 -> real) : (term212 _133751 _95602 _95603) = (term201 _133751 _95603 _95602).
Proof. exact (eq_refl (term212 _133751 _95602 _95603)). Qed.
Lemma lem7151652 {_133751 : Type'} (_95603 : _133751 -> Prop) (_95602 : _133751 -> real) (h1 : term11 _133751) : term201 _133751 _95603 _95602.
Proof. exact (EQ_MP (@lem7151651 _133751 _95603 _95602) (@lem7151650 _133751 _95602 _95603 h1)). Qed.
Lemma lem7151653 {_133751 : Type'} (_95603 : _133751 -> Prop) (_95602 : _133751 -> real) (_95604 : _133751 -> Prop) (h1 : term11 _133751) : term213 _133751 _95603 _95602 _95604.
Proof. exact (@lem7151652 _133751 _95603 _95602 h1 _95604). Qed.
Lemma lem7151654 {_133751 : Type'} (_95603 : _133751 -> Prop) (_95604 : _133751 -> Prop) (_95602 : _133751 -> real) : (term213 _133751 _95603 _95602 _95604) = (term198 _133751 _95603 _95604 _95602).
Proof. exact (eq_refl (term213 _133751 _95603 _95602 _95604)). Qed.
Lemma lem7151655 {_133751 : Type'} (_95603 : _133751 -> Prop) (_95604 : _133751 -> Prop) (_95602 : _133751 -> real) (h1 : term11 _133751) : term198 _133751 _95603 _95604 _95602.
Proof. exact (EQ_MP (@lem7151654 _133751 _95603 _95604 _95602) (@lem7151653 _133751 _95603 _95602 _95604 h1)). Qed.
Lemma lem7151656 {_133751 : Type'} (_95605 : _133751 -> Prop) (h1 : term12 _133751) : term171 _133751 _95605.
Proof. exact (@lem7151537 _133751 h1 _95605). Qed.
Lemma lem7151657 {_133751 : Type'} (_95605 : _133751 -> Prop) : (term171 _133751 _95605) = (term158 _133751 _95605).
Proof. exact (eq_refl (term171 _133751 _95605)). Qed.
Lemma lem7151658 {_133751 : Type'} (_95605 : _133751 -> Prop) (h1 : term12 _133751) : term158 _133751 _95605.
Proof. exact (EQ_MP (@lem7151657 _133751 _95605) (@lem7151656 _133751 _95605 h1)). Qed.
Lemma lem7151659 {_133751 : Type'} (_95605 : _133751 -> Prop) (_95606 : _133751 -> Prop) (h1 : term12 _133751) : term146 _133751 _95605 _95606.
Proof. exact (@lem7151658 _133751 _95605 h1 _95606). Qed.
Lemma lem7151660 {_133751 : Type'} (_95605 : _133751 -> Prop) (_95606 : _133751 -> Prop) : (term146 _133751 _95605 _95606) = (term147 _133751 _95605 _95606).
Proof. exact (eq_refl (term146 _133751 _95605 _95606)). Qed.
Lemma lem7151680 {_133751 : Type'} (_95613 : _133751 -> Prop) (h1 : term14 _133751) : term214 _133751 _95613.
Proof. exact (@lem7151595 _133751 h1 _95613). Qed.
Lemma lem7151681 {_133751 : Type'} (_95613 : _133751 -> Prop) : (term214 _133751 _95613) = (term65 _133751 _95613).
Proof. exact (eq_refl (term214 _133751 _95613)). Qed.
Lemma lem7151682 {_133751 : Type'} (_95613 : _133751 -> Prop) (h1 : term14 _133751) : term65 _133751 _95613.
Proof. exact (EQ_MP (@lem7151681 _133751 _95613) (@lem7151680 _133751 _95613 h1)). Qed.
Lemma lem7151683 {_133751 : Type'} (_95613 : _133751 -> Prop) (_95614 : _133751 -> Prop) (h1 : term14 _133751) : term215 _133751 _95613 _95614.
Proof. exact (@lem7151682 _133751 _95613 h1 _95614). Qed.
Lemma lem7151684 {_133751 : Type'} (_95613 : _133751 -> Prop) (_95614 : _133751 -> Prop) : (term215 _133751 _95613 _95614) = (term63 _133751 _95613 _95614).
Proof. exact (eq_refl (term215 _133751 _95613 _95614)). Qed.
Lemma lem7151686 {_133751 : Type'} (_95615 : _133751 -> Prop) (h1 : term14 _133751) : term216 _133751 _95615.
Proof. exact (@lem7151605 _133751 h1 _95615). Qed.
Lemma lem7151687 {_133751 : Type'} (_95615 : _133751 -> Prop) : (term216 _133751 _95615) = (term60 _133751 _95615).
Proof. exact (eq_refl (term216 _133751 _95615)). Qed.
Lemma lem7151688 {_133751 : Type'} (_95615 : _133751 -> Prop) (h1 : term14 _133751) : term60 _133751 _95615.
Proof. exact (EQ_MP (@lem7151687 _133751 _95615) (@lem7151686 _133751 _95615 h1)). Qed.
Lemma lem7151689 {_133751 : Type'} (_95615 : _133751 -> Prop) (_95616 : _133751 -> Prop) (h1 : term14 _133751) : term217 _133751 _95615 _95616.
Proof. exact (@lem7151688 _133751 _95615 h1 _95616). Qed.
Lemma lem7151690 {_133751 : Type'} (_95616 : _133751 -> Prop) (_95615 : _133751 -> Prop) : (term217 _133751 _95615 _95616) = (term58 _133751 _95616 _95615).
Proof. exact (eq_refl (term217 _133751 _95615 _95616)). Qed.
Lemma lem7151726 {_133751 : Type'} (_95598 : _133751 -> Prop) (_95597 : _133751 -> Prop) : (term106 _133751 _95598 _95597) = (term218 _133751 _95598 _95597).
Proof. exact (@lem7149051 (term219 _133751 _95598) (term220 _133751 _95597 _95598) (@FINITE _133751 _95597)). Qed.
Lemma lem7151749 {_133751 : Type'} (_95603 : _133751 -> Prop) (_95604 : _133751 -> Prop) (_95602 : _133751 -> real) : (term198 _133751 _95603 _95604 _95602) = (term221 _133751 _95603 _95604 _95602).
Proof. exact (@lem7149051 (term219 _133751 _95603) (term188 _133751 _95603 _95604) ((term194 _133751 _95603 _95604 _95602) = (term78 _133751 _95603 _95604 _95602))). Qed.
Lemma lem7151756 {_133751 : Type'} (_95603 : _133751 -> Prop) (_95604 : _133751 -> Prop) (_95602 : _133751 -> real) : (term222 _133751 _95603 _95604 _95602) = (term223 _133751 _95603 _95604 _95602).
Proof. exact (@lem7149051 (term219 _133751 _95604) (term224 _133751 _95603 _95604) ((term194 _133751 _95603 _95604 _95602) = (term78 _133751 _95603 _95604 _95602))). Qed.
Lemma lem7151757 {_133751 : Type'} (_95603 : _133751 -> Prop) : (term189 _133751 _95603) = (term189 _133751 _95603).
Proof. exact (eq_refl (term189 _133751 _95603)). Qed.
Lemma lem7151760 {_133751 : Type'} (_95603 : _133751 -> Prop) (_95604 : _133751 -> Prop) (_95602 : _133751 -> real) : (term221 _133751 _95603 _95604 _95602) = (term225 _133751 _95603 _95604 _95602).
Proof. exact (MK_COMB (@lem7151757 _133751 _95603) (@lem7151756 _133751 _95603 _95604 _95602)). Qed.
Lemma lem7151762 {_133751 : Type'} (_95603 : _133751 -> Prop) (_95604 : _133751 -> Prop) (_95602 : _133751 -> real) : (term198 _133751 _95603 _95604 _95602) = (term225 _133751 _95603 _95604 _95602).
Proof. exact (TRANS (@lem7151749 _133751 _95603 _95604 _95602) (@lem7151760 _133751 _95603 _95604 _95602)). Qed.
Lemma lem7151765 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term76 _133751 s t u f) : term226 _133751 s t u f.
Proof. exact (proj2 (@lem7151333 _133751 s t u f h1)). Qed.
Lemma lem7151767 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term76 _133751 s t u f) : @FINITE _133751 u.
Proof. exact (proj1 (@lem7151335 _133751 s t u f h1)). Qed.
Lemma lem7151771 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term76 _133751 s t u f) : (@UNION _133751 s t) = u.
Proof. exact (proj2 (@lem7151336 _133751 s t u f h1)). Qed.
Lemma lem7151804 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term76 _133751 s t u f) : u = (@UNION _133751 s t).
Proof. exact (SYM (@lem7151771 _133751 s t u f h1)). Qed.
Lemma lem7151875 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (f : _133751 -> real) : (term227 _133751 s t f) = (term227 _133751 s t f).
Proof. exact (eq_refl (term227 _133751 s t f)). Qed.
Lemma lem7151876 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term76 _133751 s t u f) : (term228 _133751 s t f u) = (term229 _133751 f s t).
Proof. exact (MK_COMB (@lem7151875 _133751 s t f) (@lem7151804 _133751 s t u f h1)). Qed.
Lemma lem7151877 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (f : _133751 -> real) : (term229 _133751 f s t) = (term230 _133751 s t f).
Proof. exact (eq_refl (term229 _133751 f s t)). Qed.
Lemma lem7151878 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (f : _133751 -> real) (u : _133751 -> Prop) : (term231 _133751 s t f u) = (term231 _133751 s t f u).
Proof. exact (eq_refl (term231 _133751 s t f u)). Qed.
Lemma lem7151879 {_133751 : Type'} (u : _133751 -> Prop) (s : _133751 -> Prop) (t : _133751 -> Prop) (f : _133751 -> real) : ((term228 _133751 s t f u) = (term229 _133751 f s t)) = ((term228 _133751 s t f u) = (term230 _133751 s t f)).
Proof. exact (MK_COMB (@lem7151878 _133751 s t f u) (@lem7151877 _133751 s t f)). Qed.
Lemma lem7151880 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) : (term228 _133751 s t f u) = (term226 _133751 s t u f).
Proof. exact (eq_refl (term228 _133751 s t f u)). Qed.
Lemma lem7151881 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7151882 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) : (term231 _133751 s t f u) = (term232 _133751 s t u f).
Proof. exact (MK_COMB (@lem7151881) (@lem7151880 _133751 s t u f)). Qed.
Lemma lem7151883 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (f : _133751 -> real) : (term230 _133751 s t f) = (term230 _133751 s t f).
Proof. exact (eq_refl (term230 _133751 s t f)). Qed.
Lemma lem7151884 {_133751 : Type'} (u : _133751 -> Prop) (s : _133751 -> Prop) (t : _133751 -> Prop) (f : _133751 -> real) : ((term228 _133751 s t f u) = (term230 _133751 s t f)) = ((term226 _133751 s t u f) = (term230 _133751 s t f)).
Proof. exact (MK_COMB (@lem7151882 _133751 s t u f) (@lem7151883 _133751 s t f)). Qed.
Lemma lem7151885 {_133751 : Type'} (u : _133751 -> Prop) (s : _133751 -> Prop) (t : _133751 -> Prop) (f : _133751 -> real) : ((term228 _133751 s t f u) = (term229 _133751 f s t)) = ((term226 _133751 s t u f) = (term230 _133751 s t f)).
Proof. exact (TRANS (@lem7151879 _133751 u s t f) (@lem7151884 _133751 u s t f)). Qed.
Lemma lem7151886 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term76 _133751 s t u f) : (term226 _133751 s t u f) = (term230 _133751 s t f).
Proof. exact (EQ_MP (@lem7151885 _133751 u s t f) (@lem7151876 _133751 s t u f h1)). Qed.
Lemma lem7151888 {_133751 : Type'} : (term233 _133751) = (term233 _133751).
Proof. exact (eq_refl (term233 _133751)). Qed.
Lemma lem7151889 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term76 _133751 s t u f) : (term234 _133751 u) = (term235 _133751 s t).
Proof. exact (MK_COMB (@lem7151888 _133751) (@lem7151804 _133751 s t u f h1)). Qed.
Lemma lem7151890 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) : (term235 _133751 s t) = (term236 _133751 s t).
Proof. exact (eq_refl (term235 _133751 s t)). Qed.
Lemma lem7151891 {_133751 : Type'} (u : _133751 -> Prop) : (term237 _133751 u) = (term237 _133751 u).
Proof. exact (eq_refl (term237 _133751 u)). Qed.
Lemma lem7151892 {_133751 : Type'} (u : _133751 -> Prop) (s : _133751 -> Prop) (t : _133751 -> Prop) : ((term234 _133751 u) = (term235 _133751 s t)) = ((term234 _133751 u) = (term236 _133751 s t)).
Proof. exact (MK_COMB (@lem7151891 _133751 u) (@lem7151890 _133751 s t)). Qed.
Lemma lem7151893 {_133751 : Type'} (u : _133751 -> Prop) : (term234 _133751 u) = (@FINITE _133751 u).
Proof. exact (eq_refl (term234 _133751 u)). Qed.
Lemma lem7151894 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7151895 {_133751 : Type'} (u : _133751 -> Prop) : (term237 _133751 u) = (term238 _133751 u).
Proof. exact (MK_COMB (@lem7151894) (@lem7151893 _133751 u)). Qed.
Lemma lem7151896 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) : (term236 _133751 s t) = (term236 _133751 s t).
Proof. exact (eq_refl (term236 _133751 s t)). Qed.
Lemma lem7151897 {_133751 : Type'} (u : _133751 -> Prop) (s : _133751 -> Prop) (t : _133751 -> Prop) : ((term234 _133751 u) = (term236 _133751 s t)) = ((@FINITE _133751 u) = (term236 _133751 s t)).
Proof. exact (MK_COMB (@lem7151895 _133751 u) (@lem7151896 _133751 s t)). Qed.
Lemma lem7151898 {_133751 : Type'} (u : _133751 -> Prop) (s : _133751 -> Prop) (t : _133751 -> Prop) : ((term234 _133751 u) = (term235 _133751 s t)) = ((@FINITE _133751 u) = (term236 _133751 s t)).
Proof. exact (TRANS (@lem7151892 _133751 u s t) (@lem7151897 _133751 u s t)). Qed.
Lemma lem7151899 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term76 _133751 s t u f) : (@FINITE _133751 u) = (term236 _133751 s t).
Proof. exact (EQ_MP (@lem7151898 _133751 u s t) (@lem7151889 _133751 s t u f h1)). Qed.
Lemma lem7151914 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term76 _133751 s t u f) : (@INTER _133751 s t) = (@EMPTY _133751).
Proof. exact (proj1 (@lem7151336 _133751 s t u f h1)). Qed.
Lemma lem7151928 {_133751 : Type'} (_95605 : _133751 -> Prop) (_95606 : _133751 -> Prop) (h1 : term12 _133751) : term147 _133751 _95605 _95606.
Proof. exact (EQ_MP (@lem7151660 _133751 _95605 _95606) (@lem7151659 _133751 _95605 _95606 h1)). Qed.
Lemma lem7152027 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term76 _133751 s t u f) : (@EMPTY _133751) = (@INTER _133751 s t).
Proof. exact (SYM (@lem7151914 _133751 s t u f h1)). Qed.
Lemma lem7152069 {_133751 : Type'} (_95598 : _133751 -> Prop) (_95597 : _133751 -> Prop) (h1 : term13 _133751) : term218 _133751 _95598 _95597.
Proof. exact (EQ_MP (@lem7151726 _133751 _95598 _95597) (@lem7151637 _133751 _95598 _95597 h1)). Qed.
Lemma lem7152097 {_133751 : Type'} (_95603 : _133751 -> Prop) (_95604 : _133751 -> Prop) (_95602 : _133751 -> real) (h1 : term11 _133751) : term225 _133751 _95603 _95604 _95602.
Proof. exact (EQ_MP (@lem7151762 _133751 _95603 _95604 _95602) (@lem7151655 _133751 _95603 _95604 _95602 h1)). Qed.
Lemma lem7152111 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term76 _133751 s t u f) : term230 _133751 s t f.
Proof. exact (EQ_MP (@lem7151886 _133751 s t u f h1) (@lem7151765 _133751 s t u f h1)). Qed.
Lemma lem7152126 {_133751 : Type'} (_95605 : _133751 -> Prop) (_95606 : _133751 -> Prop) : (term239 _133751 _95605 _95606) = (term239 _133751 _95605 _95606).
Proof. exact (eq_refl (term239 _133751 _95605 _95606)). Qed.
Lemma lem7152127 {_133751 : Type'} (_95605 : _133751 -> Prop) (_95606 : _133751 -> Prop) (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term76 _133751 s t u f) : (term240 _133751 _95605 _95606) = (term241 _133751 _95605 _95606 s t).
Proof. exact (MK_COMB (@lem7152126 _133751 _95605 _95606) (@lem7152027 _133751 s t u f h1)). Qed.
Lemma lem7152128 {_133751 : Type'} (_95605 : _133751 -> Prop) (_95606 : _133751 -> Prop) (s : _133751 -> Prop) (t : _133751 -> Prop) : (term241 _133751 _95605 _95606 s t) = (term242 _133751 _95605 _95606 s t).
Proof. exact (eq_refl (term241 _133751 _95605 _95606 s t)). Qed.
Lemma lem7152129 {_133751 : Type'} (_95605 : _133751 -> Prop) (_95606 : _133751 -> Prop) : (term243 _133751 _95605 _95606) = (term243 _133751 _95605 _95606).
Proof. exact (eq_refl (term243 _133751 _95605 _95606)). Qed.
Lemma lem7152130 {_133751 : Type'} (_95605 : _133751 -> Prop) (_95606 : _133751 -> Prop) (s : _133751 -> Prop) (t : _133751 -> Prop) : ((term240 _133751 _95605 _95606) = (term241 _133751 _95605 _95606 s t)) = ((term240 _133751 _95605 _95606) = (term242 _133751 _95605 _95606 s t)).
Proof. exact (MK_COMB (@lem7152129 _133751 _95605 _95606) (@lem7152128 _133751 _95605 _95606 s t)). Qed.
Lemma lem7152131 {_133751 : Type'} (_95605 : _133751 -> Prop) (_95606 : _133751 -> Prop) : (term240 _133751 _95605 _95606) = (term147 _133751 _95605 _95606).
Proof. exact (eq_refl (term240 _133751 _95605 _95606)). Qed.
Lemma lem7152132 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7152133 {_133751 : Type'} (_95605 : _133751 -> Prop) (_95606 : _133751 -> Prop) : (term243 _133751 _95605 _95606) = (term244 _133751 _95605 _95606).
Proof. exact (MK_COMB (@lem7152132) (@lem7152131 _133751 _95605 _95606)). Qed.
Lemma lem7152134 {_133751 : Type'} (_95605 : _133751 -> Prop) (_95606 : _133751 -> Prop) (s : _133751 -> Prop) (t : _133751 -> Prop) : (term242 _133751 _95605 _95606 s t) = (term242 _133751 _95605 _95606 s t).
Proof. exact (eq_refl (term242 _133751 _95605 _95606 s t)). Qed.
Lemma lem7152135 {_133751 : Type'} (_95605 : _133751 -> Prop) (_95606 : _133751 -> Prop) (s : _133751 -> Prop) (t : _133751 -> Prop) : ((term240 _133751 _95605 _95606) = (term242 _133751 _95605 _95606 s t)) = ((term147 _133751 _95605 _95606) = (term242 _133751 _95605 _95606 s t)).
Proof. exact (MK_COMB (@lem7152133 _133751 _95605 _95606) (@lem7152134 _133751 _95605 _95606 s t)). Qed.
Lemma lem7152136 {_133751 : Type'} (_95605 : _133751 -> Prop) (_95606 : _133751 -> Prop) (s : _133751 -> Prop) (t : _133751 -> Prop) : ((term240 _133751 _95605 _95606) = (term241 _133751 _95605 _95606 s t)) = ((term147 _133751 _95605 _95606) = (term242 _133751 _95605 _95606 s t)).
Proof. exact (TRANS (@lem7152130 _133751 _95605 _95606 s t) (@lem7152135 _133751 _95605 _95606 s t)). Qed.
Lemma lem7152137 {_133751 : Type'} (_95605 : _133751 -> Prop) (_95606 : _133751 -> Prop) (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term76 _133751 s t u f) : (term147 _133751 _95605 _95606) = (term242 _133751 _95605 _95606 s t).
Proof. exact (EQ_MP (@lem7152136 _133751 _95605 _95606 s t) (@lem7152127 _133751 _95605 _95606 s t u f h1)). Qed.
Lemma lem7152138 {_133751 : Type'} (_95605 : _133751 -> Prop) (_95606 : _133751 -> Prop) (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term12 _133751) (h2 : term76 _133751 s t u f) : term242 _133751 _95605 _95606 s t.
Proof. exact (EQ_MP (@lem7152137 _133751 _95605 _95606 s t u f h2) (@lem7151928 _133751 _95605 _95606 h1)). Qed.
Lemma lem7152442 (x : real) (y : real) (z : real) : term245 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem7152452 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term76 _133751 s t u f) : term236 _133751 s t.
Proof. exact (EQ_MP (@lem7151899 _133751 s t u f h1) (@lem7151767 _133751 s t u f h1)). Qed.
Lemma lem7152453 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term76 _133751 s t u f) : term246 _133751 s t.
Proof. exact (fun h0 : term247 _133751 s t => @lem7152452 _133751 s t u f h1). Qed.
Lemma lem7152455 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7152456 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) : (term246 _133751 s t) = (term236 _133751 s t).
Proof. exact (@lem7152455 (term236 _133751 s t)). Qed.
Lemma lem7152457 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term76 _133751 s t u f) : term236 _133751 s t.
Proof. exact (EQ_MP (@lem7152456 _133751 s t) (@lem7152453 _133751 s t u f h1)). Qed.
Lemma lem7152459 {_133751 : Type'} (_95613 : _133751 -> Prop) (_95614 : _133751 -> Prop) (h1 : term14 _133751) : term63 _133751 _95613 _95614.
Proof. exact (EQ_MP (@lem7151684 _133751 _95613 _95614) (@lem7151683 _133751 _95613 _95614 h1)). Qed.
Lemma lem7152460 {_133751 : Type'} (_95613 : _133751 -> Prop) (_95614 : _133751 -> Prop) (h1 : term14 _133751) : term63 _133751 _95613 _95614.
Proof. exact (@lem7152459 _133751 _95613 _95614 h1). Qed.
Lemma lem7152461 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (h1 : term14 _133751) : term63 _133751 s t.
Proof. exact (@lem7152460 _133751 s t h1). Qed.
Lemma lem7152462 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (h1 : term14 _133751) : term249 _133751 s t.
Proof. exact (fun h0 : term250 _133751 s t => @lem7152461 _133751 s t h1). Qed.
Lemma lem7152464 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7152465 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) : (term249 _133751 s t) = (term63 _133751 s t).
Proof. exact (@lem7152464 (term63 _133751 s t)). Qed.
Lemma lem7152466 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (h1 : term14 _133751) : term63 _133751 s t.
Proof. exact (EQ_MP (@lem7152465 _133751 s t) (@lem7152462 _133751 s t h1)). Qed.
Lemma lem7152482 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7152483 {_133751 : Type'} (_95597 : _133751 -> Prop) (_95598 : _133751 -> Prop) : (term251 _133751 _95598 _95597) = (term252 _133751 _95597 _95598).
Proof. exact (@lem7152482 (@FINITE _133751 _95597) (term220 _133751 _95597 _95598)). Qed.
Lemma lem7152489 {_133751 : Type'} (_95598 : _133751 -> Prop) : (term189 _133751 _95598) = (term189 _133751 _95598).
Proof. exact (eq_refl (term189 _133751 _95598)). Qed.
Lemma lem7152490 {_133751 : Type'} (_95597 : _133751 -> Prop) (_95598 : _133751 -> Prop) : (term218 _133751 _95598 _95597) = (term253 _133751 _95597 _95598).
Proof. exact (MK_COMB (@lem7152489 _133751 _95598) (@lem7152483 _133751 _95597 _95598)). Qed.
Lemma lem7152494 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7152495 {_133751 : Type'} (_95597 : _133751 -> Prop) (_95598 : _133751 -> Prop) : (term253 _133751 _95597 _95598) = (term254 _133751 _95597 _95598).
Proof. exact (@lem7152494 (@FINITE _133751 _95597) (term219 _133751 _95598) (term220 _133751 _95597 _95598)). Qed.
Lemma lem7152511 {_133751 : Type'} (_95597 : _133751 -> Prop) (_95598 : _133751 -> Prop) : (term218 _133751 _95598 _95597) = (term254 _133751 _95597 _95598).
Proof. exact (TRANS (@lem7152490 _133751 _95597 _95598) (@lem7152495 _133751 _95597 _95598)). Qed.
Lemma lem7152512 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7152513 {_133751 : Type'} (_95597 : _133751 -> Prop) (_95598 : _133751 -> Prop) : (term255 _133751 _95598 _95597) = (term256 _133751 _95597 _95598).
Proof. exact (MK_COMB (@lem7152512) (@lem7152511 _133751 _95597 _95598)). Qed.
Lemma lem7152529 {_133751 : Type'} (_95597 : _133751 -> Prop) (_95598 : _133751 -> Prop) : (term254 _133751 _95597 _95598) = (term254 _133751 _95597 _95598).
Proof. exact (eq_refl (term254 _133751 _95597 _95598)). Qed.
Lemma lem7152530 {_133751 : Type'} (_95597 : _133751 -> Prop) (_95598 : _133751 -> Prop) : ((term218 _133751 _95598 _95597) = (term254 _133751 _95597 _95598)) = ((term254 _133751 _95597 _95598) = (term254 _133751 _95597 _95598)).
Proof. exact (MK_COMB (@lem7152513 _133751 _95597 _95598) (@lem7152529 _133751 _95597 _95598)). Qed.
Lemma lem7152532 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7152533 (x : Prop) : (x = x) = True.
Proof. exact (@lem7152532 Prop x). Qed.
Lemma lem7152534 {_133751 : Type'} (_95597 : _133751 -> Prop) (_95598 : _133751 -> Prop) : ((term254 _133751 _95597 _95598) = (term254 _133751 _95597 _95598)) = True.
Proof. exact (@lem7152533 (term254 _133751 _95597 _95598)). Qed.
Lemma lem7152535 {_133751 : Type'} (_95597 : _133751 -> Prop) (_95598 : _133751 -> Prop) : ((term218 _133751 _95598 _95597) = (term254 _133751 _95597 _95598)) = True.
Proof. exact (TRANS (@lem7152530 _133751 _95597 _95598) (@lem7152534 _133751 _95597 _95598)). Qed.
Lemma lem7152536 {_133751 : Type'} (_95597 : _133751 -> Prop) (_95598 : _133751 -> Prop) : True = ((term218 _133751 _95598 _95597) = (term254 _133751 _95597 _95598)).
Proof. exact (SYM (@lem7152535 _133751 _95597 _95598)). Qed.
Lemma lem7152537 {_133751 : Type'} (_95597 : _133751 -> Prop) (_95598 : _133751 -> Prop) : (term218 _133751 _95598 _95597) = (term254 _133751 _95597 _95598).
Proof. exact (EQ_MP (@lem7152536 _133751 _95597 _95598) (@lem0)). Qed.
Lemma lem7152538 {_133751 : Type'} (_95597 : _133751 -> Prop) (_95598 : _133751 -> Prop) (h1 : term13 _133751) : term254 _133751 _95597 _95598.
Proof. exact (EQ_MP (@lem7152537 _133751 _95597 _95598) (@lem7152069 _133751 _95598 _95597 h1)). Qed.
Lemma lem7152540 (b : Prop) (a : Prop) : (a \/ b) = (term257 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7152541 {_133751 : Type'} (_95598 : _133751 -> Prop) (_95597 : _133751 -> Prop) : (term254 _133751 _95597 _95598) = (term258 _133751 _95598 _95597).
Proof. exact (@lem7152540 (term102 _133751 _95597 _95598) (@FINITE _133751 _95597)). Qed.
Lemma lem7152543 (a : Prop) (b : Prop) : (term259 a b) = (term260 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7152544 {_133751 : Type'} (_95597 : _133751 -> Prop) (_95598 : _133751 -> Prop) : (term261 _133751 _95597 _95598) = (term262 _133751 _95597 _95598).
Proof. exact (@lem7152543 (term219 _133751 _95598) (term220 _133751 _95597 _95598)). Qed.
Lemma lem7152546 (a : Prop) : (term263 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7152547 {_133751 : Type'} (_95598 : _133751 -> Prop) : (term264 _133751 _95598) = (@FINITE _133751 _95598).
Proof. exact (@lem7152546 (@FINITE _133751 _95598)). Qed.
Lemma lem7152548 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7152549 {_133751 : Type'} (_95598 : _133751 -> Prop) : (term265 _133751 _95598) = (term266 _133751 _95598).
Proof. exact (MK_COMB (@lem7152548) (@lem7152547 _133751 _95598)). Qed.
Lemma lem7152551 (a : Prop) : (term263 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7152552 {_133751 : Type'} (_95597 : _133751 -> Prop) (_95598 : _133751 -> Prop) : (term267 _133751 _95597 _95598) = (@SUBSET _133751 _95597 _95598).
Proof. exact (@lem7152551 (@SUBSET _133751 _95597 _95598)). Qed.
Lemma lem7152553 {_133751 : Type'} (_95597 : _133751 -> Prop) (_95598 : _133751 -> Prop) : (term262 _133751 _95597 _95598) = (term107 _133751 _95597 _95598).
Proof. exact (MK_COMB (@lem7152549 _133751 _95598) (@lem7152552 _133751 _95597 _95598)). Qed.
Lemma lem7152554 {_133751 : Type'} (_95597 : _133751 -> Prop) (_95598 : _133751 -> Prop) : (term261 _133751 _95597 _95598) = (term107 _133751 _95597 _95598).
Proof. exact (TRANS (@lem7152544 _133751 _95597 _95598) (@lem7152553 _133751 _95597 _95598)). Qed.
Lemma lem7152555 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7152556 {_133751 : Type'} (_95597 : _133751 -> Prop) (_95598 : _133751 -> Prop) : (term268 _133751 _95597 _95598) = (term269 _133751 _95597 _95598).
Proof. exact (MK_COMB (@lem7152555) (@lem7152554 _133751 _95597 _95598)). Qed.
Lemma lem7152557 {_133751 : Type'} (_95597 : _133751 -> Prop) : (@FINITE _133751 _95597) = (@FINITE _133751 _95597).
Proof. exact (eq_refl (@FINITE _133751 _95597)). Qed.
Lemma lem7152558 {_133751 : Type'} (_95598 : _133751 -> Prop) (_95597 : _133751 -> Prop) : (term258 _133751 _95598 _95597) = (term54 _133751 _95598 _95597).
Proof. exact (MK_COMB (@lem7152556 _133751 _95597 _95598) (@lem7152557 _133751 _95597)). Qed.
Lemma lem7152559 {_133751 : Type'} (_95598 : _133751 -> Prop) (_95597 : _133751 -> Prop) : (term254 _133751 _95597 _95598) = (term54 _133751 _95598 _95597).
Proof. exact (TRANS (@lem7152541 _133751 _95598 _95597) (@lem7152558 _133751 _95598 _95597)). Qed.
Lemma lem7152561 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term14 _133751) (h2 : term76 _133751 s t u f) : term270 _133751 s t.
Proof. exact (conj (@lem7152457 _133751 s t u f h2) (@lem7152466 _133751 s t h1)). Qed.
Lemma lem7152563 {_133751 : Type'} (_95598 : _133751 -> Prop) (_95597 : _133751 -> Prop) (h1 : term13 _133751) : term54 _133751 _95598 _95597.
Proof. exact (EQ_MP (@lem7152559 _133751 _95598 _95597) (@lem7152538 _133751 _95597 _95598 h1)). Qed.
Lemma lem7152564 {_133751 : Type'} (_95598 : _133751 -> Prop) (_95597 : _133751 -> Prop) (h1 : term13 _133751) : term54 _133751 _95598 _95597.
Proof. exact (@lem7152563 _133751 _95598 _95597 h1). Qed.
Lemma lem7152565 {_133751 : Type'} (t : _133751 -> Prop) (s : _133751 -> Prop) (h1 : term13 _133751) : term271 _133751 t s.
Proof. exact (@lem7152564 _133751 (@UNION _133751 s t) s h1). Qed.
Lemma lem7152568 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term13 _133751) (h2 : term14 _133751) (h3 : term76 _133751 s t u f) : @FINITE _133751 s.
Proof. exact (@lem7152565 _133751 t s h1 (@lem7152561 _133751 s t u f h2 h3)). Qed.
Lemma lem7152569 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term13 _133751) (h2 : term14 _133751) (h3 : term76 _133751 s t u f) : term272 _133751 s.
Proof. exact (fun h0 : term219 _133751 s => @lem7152568 _133751 s t u f h1 h2 h3). Qed.
Lemma lem7152571 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7152572 {_133751 : Type'} (s : _133751 -> Prop) : (term272 _133751 s) = (@FINITE _133751 s).
Proof. exact (@lem7152571 (@FINITE _133751 s)). Qed.
Lemma lem7152573 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term13 _133751) (h2 : term14 _133751) (h3 : term76 _133751 s t u f) : @FINITE _133751 s.
Proof. exact (EQ_MP (@lem7152572 _133751 s) (@lem7152569 _133751 s t u f h1 h2 h3)). Qed.
Lemma lem7152575 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term76 _133751 s t u f) : term236 _133751 s t.
Proof. exact (EQ_MP (@lem7151899 _133751 s t u f h1) (@lem7151767 _133751 s t u f h1)). Qed.
Lemma lem7152576 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term76 _133751 s t u f) : term246 _133751 s t.
Proof. exact (fun h0 : term247 _133751 s t => @lem7152575 _133751 s t u f h1). Qed.
Lemma lem7152578 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7152579 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) : (term246 _133751 s t) = (term236 _133751 s t).
Proof. exact (@lem7152578 (term236 _133751 s t)). Qed.
Lemma lem7152580 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term76 _133751 s t u f) : term236 _133751 s t.
Proof. exact (EQ_MP (@lem7152579 _133751 s t) (@lem7152576 _133751 s t u f h1)). Qed.
Lemma lem7152582 {_133751 : Type'} (_95616 : _133751 -> Prop) (_95615 : _133751 -> Prop) (h1 : term14 _133751) : term58 _133751 _95616 _95615.
Proof. exact (EQ_MP (@lem7151690 _133751 _95616 _95615) (@lem7151689 _133751 _95615 _95616 h1)). Qed.
Lemma lem7152583 {_133751 : Type'} (_95616 : _133751 -> Prop) (_95615 : _133751 -> Prop) (h1 : term14 _133751) : term58 _133751 _95616 _95615.
Proof. exact (@lem7152582 _133751 _95616 _95615 h1). Qed.
Lemma lem7152584 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (h1 : term14 _133751) : term58 _133751 s t.
Proof. exact (@lem7152583 _133751 s t h1). Qed.
Lemma lem7152585 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (h1 : term14 _133751) : term273 _133751 s t.
Proof. exact (fun h0 : term274 _133751 s t => @lem7152584 _133751 s t h1). Qed.
Lemma lem7152587 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7152588 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) : (term273 _133751 s t) = (term58 _133751 s t).
Proof. exact (@lem7152587 (term58 _133751 s t)). Qed.
Lemma lem7152589 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (h1 : term14 _133751) : term58 _133751 s t.
Proof. exact (EQ_MP (@lem7152588 _133751 s t) (@lem7152585 _133751 s t h1)). Qed.
Lemma lem7152590 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term14 _133751) (h2 : term76 _133751 s t u f) : term275 _133751 s t.
Proof. exact (conj (@lem7152580 _133751 s t u f h2) (@lem7152589 _133751 s t h1)). Qed.
Lemma lem7152592 {_133751 : Type'} (_95598 : _133751 -> Prop) (_95597 : _133751 -> Prop) (h1 : term13 _133751) : term54 _133751 _95598 _95597.
Proof. exact (EQ_MP (@lem7152559 _133751 _95598 _95597) (@lem7152538 _133751 _95597 _95598 h1)). Qed.
Lemma lem7152593 {_133751 : Type'} (_95598 : _133751 -> Prop) (_95597 : _133751 -> Prop) (h1 : term13 _133751) : term54 _133751 _95598 _95597.
Proof. exact (@lem7152592 _133751 _95598 _95597 h1). Qed.
Lemma lem7152594 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (h1 : term13 _133751) : term276 _133751 s t.
Proof. exact (@lem7152593 _133751 (@UNION _133751 s t) t h1). Qed.
Lemma lem7152597 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term13 _133751) (h2 : term14 _133751) (h3 : term76 _133751 s t u f) : @FINITE _133751 t.
Proof. exact (@lem7152594 _133751 s t h1 (@lem7152590 _133751 s t u f h2 h3)). Qed.
Lemma lem7152598 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term13 _133751) (h2 : term14 _133751) (h3 : term76 _133751 s t u f) : term272 _133751 t.
Proof. exact (fun h0 : term219 _133751 t => @lem7152597 _133751 s t u f h1 h2 h3). Qed.
Lemma lem7152600 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7152601 {_133751 : Type'} (t : _133751 -> Prop) : (term272 _133751 t) = (@FINITE _133751 t).
Proof. exact (@lem7152600 (@FINITE _133751 t)). Qed.
Lemma lem7152602 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term13 _133751) (h2 : term14 _133751) (h3 : term76 _133751 s t u f) : @FINITE _133751 t.
Proof. exact (EQ_MP (@lem7152601 _133751 t) (@lem7152598 _133751 s t u f h1 h2 h3)). Qed.
Lemma lem7152604 {_133751 : Type'} (x : _133751 -> Prop) : x = x.
Proof. exact (@lem21386 (_133751 -> Prop) x). Qed.
Lemma lem7152605 {_133751 : Type'} (x : _133751 -> Prop) : x = x.
Proof. exact (@lem7152604 _133751 x). Qed.
Lemma lem7152606 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) : (@INTER _133751 s t) = (@INTER _133751 s t).
Proof. exact (@lem7152605 _133751 (@INTER _133751 s t)). Qed.
Lemma lem7152607 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) : term277 _133751 s t.
Proof. exact (fun h0 : term278 _133751 s t => @lem7152606 _133751 s t). Qed.
Lemma lem7152609 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7152610 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) : (term277 _133751 s t) = ((@INTER _133751 s t) = (@INTER _133751 s t)).
Proof. exact (@lem7152609 ((@INTER _133751 s t) = (@INTER _133751 s t))). Qed.
Lemma lem7152611 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) : (@INTER _133751 s t) = (@INTER _133751 s t).
Proof. exact (EQ_MP (@lem7152610 _133751 s t) (@lem7152607 _133751 s t)). Qed.
Lemma lem7152613 (b : Prop) (a : Prop) : (a \/ b) = (term257 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7152614 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (_95605 : _133751 -> Prop) (_95606 : _133751 -> Prop) : (term242 _133751 _95605 _95606 s t) = (term279 _133751 s t _95605 _95606).
Proof. exact (@lem7152613 (term280 _133751 _95605 _95606 s t) (@DISJOINT _133751 _95605 _95606)). Qed.
Lemma lem7152616 (a : Prop) : (term263 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7152617 {_133751 : Type'} (_95605 : _133751 -> Prop) (_95606 : _133751 -> Prop) (s : _133751 -> Prop) (t : _133751 -> Prop) : (term281 _133751 _95605 _95606 s t) = ((@INTER _133751 _95605 _95606) = (@INTER _133751 s t)).
Proof. exact (@lem7152616 ((@INTER _133751 _95605 _95606) = (@INTER _133751 s t))). Qed.
Lemma lem7152618 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7152619 {_133751 : Type'} (_95605 : _133751 -> Prop) (_95606 : _133751 -> Prop) (s : _133751 -> Prop) (t : _133751 -> Prop) : (term282 _133751 _95605 _95606 s t) = (term283 _133751 _95605 _95606 s t).
Proof. exact (MK_COMB (@lem7152618) (@lem7152617 _133751 _95605 _95606 s t)). Qed.
Lemma lem7152620 {_133751 : Type'} (_95605 : _133751 -> Prop) (_95606 : _133751 -> Prop) : (@DISJOINT _133751 _95605 _95606) = (@DISJOINT _133751 _95605 _95606).
Proof. exact (eq_refl (@DISJOINT _133751 _95605 _95606)). Qed.
Lemma lem7152621 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (_95605 : _133751 -> Prop) (_95606 : _133751 -> Prop) : (term279 _133751 s t _95605 _95606) = (term284 _133751 s t _95605 _95606).
Proof. exact (MK_COMB (@lem7152619 _133751 _95605 _95606 s t) (@lem7152620 _133751 _95605 _95606)). Qed.
Lemma lem7152622 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (_95605 : _133751 -> Prop) (_95606 : _133751 -> Prop) : (term242 _133751 _95605 _95606 s t) = (term284 _133751 s t _95605 _95606).
Proof. exact (TRANS (@lem7152614 _133751 s t _95605 _95606) (@lem7152621 _133751 s t _95605 _95606)). Qed.
Lemma lem7152625 {_133751 : Type'} (_95605 : _133751 -> Prop) (_95606 : _133751 -> Prop) (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term12 _133751) (h2 : term76 _133751 s t u f) : term284 _133751 s t _95605 _95606.
Proof. exact (EQ_MP (@lem7152622 _133751 s t _95605 _95606) (@lem7152138 _133751 _95605 _95606 s t u f h1 h2)). Qed.
Lemma lem7152626 {_133751 : Type'} (_95605 : _133751 -> Prop) (_95606 : _133751 -> Prop) (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term12 _133751) (h2 : term76 _133751 s t u f) : term284 _133751 s t _95605 _95606.
Proof. exact (@lem7152625 _133751 _95605 _95606 s t u f h1 h2). Qed.
Lemma lem7152627 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term12 _133751) (h2 : term76 _133751 s t u f) : term285 _133751 s t.
Proof. exact (@lem7152626 _133751 s t s t u f h1 h2). Qed.
Lemma lem7152630 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term12 _133751) (h2 : term76 _133751 s t u f) : @DISJOINT _133751 s t.
Proof. exact (@lem7152627 _133751 s t u f h1 h2 (@lem7152611 _133751 s t)). Qed.
Lemma lem7152631 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term12 _133751) (h2 : term76 _133751 s t u f) : term286 _133751 s t.
Proof. exact (fun h0 : term224 _133751 s t => @lem7152630 _133751 s t u f h1 h2). Qed.
Lemma lem7152633 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7152634 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) : (term286 _133751 s t) = (@DISJOINT _133751 s t).
Proof. exact (@lem7152633 (@DISJOINT _133751 s t)). Qed.
Lemma lem7152635 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term12 _133751) (h2 : term76 _133751 s t u f) : @DISJOINT _133751 s t.
Proof. exact (EQ_MP (@lem7152634 _133751 s t) (@lem7152631 _133751 s t u f h1 h2)). Qed.
Lemma lem7152651 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7152652 {_133751 : Type'} (_95603 : _133751 -> Prop) (_95604 : _133751 -> Prop) (_95602 : _133751 -> real) : (term223 _133751 _95603 _95604 _95602) = (term287 _133751 _95603 _95604 _95602).
Proof. exact (@lem7152651 (term224 _133751 _95603 _95604) (term219 _133751 _95604) ((term194 _133751 _95603 _95604 _95602) = (term78 _133751 _95603 _95604 _95602))). Qed.
Lemma lem7152666 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7152667 {_133751 : Type'} (_95603 : _133751 -> Prop) (_95602 : _133751 -> real) (_95604 : _133751 -> Prop) : (term288 _133751 _95603 _95604 _95602) = (term289 _133751 _95603 _95602 _95604).
Proof. exact (@lem7152666 ((term194 _133751 _95603 _95604 _95602) = (term78 _133751 _95603 _95604 _95602)) (term219 _133751 _95604)). Qed.
Lemma lem7152675 {_133751 : Type'} (_95603 : _133751 -> Prop) (_95604 : _133751 -> Prop) : (term290 _133751 _95603 _95604) = (term290 _133751 _95603 _95604).
Proof. exact (eq_refl (term290 _133751 _95603 _95604)). Qed.
Lemma lem7152676 {_133751 : Type'} (_95603 : _133751 -> Prop) (_95602 : _133751 -> real) (_95604 : _133751 -> Prop) : (term287 _133751 _95603 _95604 _95602) = (term291 _133751 _95603 _95602 _95604).
Proof. exact (MK_COMB (@lem7152675 _133751 _95603 _95604) (@lem7152667 _133751 _95603 _95602 _95604)). Qed.
Lemma lem7152680 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7152681 {_133751 : Type'} (_95602 : _133751 -> real) (_95603 : _133751 -> Prop) (_95604 : _133751 -> Prop) : (term291 _133751 _95603 _95602 _95604) = (term292 _133751 _95602 _95603 _95604).
Proof. exact (@lem7152680 ((term194 _133751 _95603 _95604 _95602) = (term78 _133751 _95603 _95604 _95602)) (term224 _133751 _95603 _95604) (term219 _133751 _95604)). Qed.
Lemma lem7152699 {_133751 : Type'} (_95602 : _133751 -> real) (_95603 : _133751 -> Prop) (_95604 : _133751 -> Prop) : (term287 _133751 _95603 _95604 _95602) = (term292 _133751 _95602 _95603 _95604).
Proof. exact (TRANS (@lem7152676 _133751 _95603 _95602 _95604) (@lem7152681 _133751 _95602 _95603 _95604)). Qed.
Lemma lem7152700 {_133751 : Type'} (_95602 : _133751 -> real) (_95603 : _133751 -> Prop) (_95604 : _133751 -> Prop) : (term223 _133751 _95603 _95604 _95602) = (term292 _133751 _95602 _95603 _95604).
Proof. exact (TRANS (@lem7152652 _133751 _95603 _95604 _95602) (@lem7152699 _133751 _95602 _95603 _95604)). Qed.
Lemma lem7152701 {_133751 : Type'} (_95603 : _133751 -> Prop) : (term189 _133751 _95603) = (term189 _133751 _95603).
Proof. exact (eq_refl (term189 _133751 _95603)). Qed.
Lemma lem7152702 {_133751 : Type'} (_95602 : _133751 -> real) (_95603 : _133751 -> Prop) (_95604 : _133751 -> Prop) : (term225 _133751 _95603 _95604 _95602) = (term293 _133751 _95602 _95603 _95604).
Proof. exact (MK_COMB (@lem7152701 _133751 _95603) (@lem7152700 _133751 _95602 _95603 _95604)). Qed.
Lemma lem7152706 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7152707 {_133751 : Type'} (_95602 : _133751 -> real) (_95603 : _133751 -> Prop) (_95604 : _133751 -> Prop) : (term293 _133751 _95602 _95603 _95604) = (term294 _133751 _95602 _95603 _95604).
Proof. exact (@lem7152706 ((term194 _133751 _95603 _95604 _95602) = (term78 _133751 _95603 _95604 _95602)) (term219 _133751 _95603) (term295 _133751 _95603 _95604)). Qed.
Lemma lem7152723 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7152724 {_133751 : Type'} (_95603 : _133751 -> Prop) (_95604 : _133751 -> Prop) : (term296 _133751 _95603 _95604) = (term297 _133751 _95603 _95604).
Proof. exact (@lem7152723 (term224 _133751 _95603 _95604) (term219 _133751 _95603) (term219 _133751 _95604)). Qed.
Lemma lem7152740 {_133751 : Type'} (_95603 : _133751 -> Prop) (_95604 : _133751 -> Prop) (_95602 : _133751 -> real) : (term298 _133751 _95603 _95604 _95602) = (term298 _133751 _95603 _95604 _95602).
Proof. exact (eq_refl (term298 _133751 _95603 _95604 _95602)). Qed.
Lemma lem7152741 {_133751 : Type'} (_95602 : _133751 -> real) (_95603 : _133751 -> Prop) (_95604 : _133751 -> Prop) : (term294 _133751 _95602 _95603 _95604) = (term299 _133751 _95602 _95603 _95604).
Proof. exact (MK_COMB (@lem7152740 _133751 _95603 _95604 _95602) (@lem7152724 _133751 _95603 _95604)). Qed.
Lemma lem7152752 {_133751 : Type'} (_95602 : _133751 -> real) (_95603 : _133751 -> Prop) (_95604 : _133751 -> Prop) : (term293 _133751 _95602 _95603 _95604) = (term299 _133751 _95602 _95603 _95604).
Proof. exact (TRANS (@lem7152707 _133751 _95602 _95603 _95604) (@lem7152741 _133751 _95602 _95603 _95604)). Qed.
Lemma lem7152753 {_133751 : Type'} (_95602 : _133751 -> real) (_95603 : _133751 -> Prop) (_95604 : _133751 -> Prop) : (term225 _133751 _95603 _95604 _95602) = (term299 _133751 _95602 _95603 _95604).
Proof. exact (TRANS (@lem7152702 _133751 _95602 _95603 _95604) (@lem7152752 _133751 _95602 _95603 _95604)). Qed.
Lemma lem7152754 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7152755 {_133751 : Type'} (_95602 : _133751 -> real) (_95603 : _133751 -> Prop) (_95604 : _133751 -> Prop) : (term300 _133751 _95603 _95604 _95602) = (term301 _133751 _95602 _95603 _95604).
Proof. exact (MK_COMB (@lem7152754) (@lem7152753 _133751 _95602 _95603 _95604)). Qed.
Lemma lem7152781 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7152782 {_133751 : Type'} (_95603 : _133751 -> Prop) (_95604 : _133751 -> Prop) : (term188 _133751 _95603 _95604) = (term295 _133751 _95603 _95604).
Proof. exact (@lem7152781 (term224 _133751 _95603 _95604) (term219 _133751 _95604)). Qed.
Lemma lem7152788 {_133751 : Type'} (_95603 : _133751 -> Prop) : (term189 _133751 _95603) = (term189 _133751 _95603).
Proof. exact (eq_refl (term189 _133751 _95603)). Qed.
Lemma lem7152789 {_133751 : Type'} (_95603 : _133751 -> Prop) (_95604 : _133751 -> Prop) : (term191 _133751 _95603 _95604) = (term296 _133751 _95603 _95604).
Proof. exact (MK_COMB (@lem7152788 _133751 _95603) (@lem7152782 _133751 _95603 _95604)). Qed.
Lemma lem7152793 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7152794 {_133751 : Type'} (_95603 : _133751 -> Prop) (_95604 : _133751 -> Prop) : (term296 _133751 _95603 _95604) = (term297 _133751 _95603 _95604).
Proof. exact (@lem7152793 (term224 _133751 _95603 _95604) (term219 _133751 _95603) (term219 _133751 _95604)). Qed.
Lemma lem7152810 {_133751 : Type'} (_95603 : _133751 -> Prop) (_95604 : _133751 -> Prop) : (term191 _133751 _95603 _95604) = (term297 _133751 _95603 _95604).
Proof. exact (TRANS (@lem7152789 _133751 _95603 _95604) (@lem7152794 _133751 _95603 _95604)). Qed.
Lemma lem7152811 {_133751 : Type'} (_95603 : _133751 -> Prop) (_95604 : _133751 -> Prop) (_95602 : _133751 -> real) : (term298 _133751 _95603 _95604 _95602) = (term298 _133751 _95603 _95604 _95602).
Proof. exact (eq_refl (term298 _133751 _95603 _95604 _95602)). Qed.
Lemma lem7152812 {_133751 : Type'} (_95602 : _133751 -> real) (_95603 : _133751 -> Prop) (_95604 : _133751 -> Prop) : (term302 _133751 _95602 _95603 _95604) = (term299 _133751 _95602 _95603 _95604).
Proof. exact (MK_COMB (@lem7152811 _133751 _95603 _95604 _95602) (@lem7152810 _133751 _95603 _95604)). Qed.
Lemma lem7152823 {_133751 : Type'} (_95602 : _133751 -> real) (_95603 : _133751 -> Prop) (_95604 : _133751 -> Prop) : ((term225 _133751 _95603 _95604 _95602) = (term302 _133751 _95602 _95603 _95604)) = ((term299 _133751 _95602 _95603 _95604) = (term299 _133751 _95602 _95603 _95604)).
Proof. exact (MK_COMB (@lem7152755 _133751 _95602 _95603 _95604) (@lem7152812 _133751 _95602 _95603 _95604)). Qed.
Lemma lem7152825 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7152826 (x : Prop) : (x = x) = True.
Proof. exact (@lem7152825 Prop x). Qed.
Lemma lem7152827 {_133751 : Type'} (_95602 : _133751 -> real) (_95603 : _133751 -> Prop) (_95604 : _133751 -> Prop) : ((term299 _133751 _95602 _95603 _95604) = (term299 _133751 _95602 _95603 _95604)) = True.
Proof. exact (@lem7152826 (term299 _133751 _95602 _95603 _95604)). Qed.
Lemma lem7152828 {_133751 : Type'} (_95602 : _133751 -> real) (_95603 : _133751 -> Prop) (_95604 : _133751 -> Prop) : ((term225 _133751 _95603 _95604 _95602) = (term302 _133751 _95602 _95603 _95604)) = True.
Proof. exact (TRANS (@lem7152823 _133751 _95602 _95603 _95604) (@lem7152827 _133751 _95602 _95603 _95604)). Qed.
Lemma lem7152829 {_133751 : Type'} (_95602 : _133751 -> real) (_95603 : _133751 -> Prop) (_95604 : _133751 -> Prop) : True = ((term225 _133751 _95603 _95604 _95602) = (term302 _133751 _95602 _95603 _95604)).
Proof. exact (SYM (@lem7152828 _133751 _95602 _95603 _95604)). Qed.
Lemma lem7152830 {_133751 : Type'} (_95602 : _133751 -> real) (_95603 : _133751 -> Prop) (_95604 : _133751 -> Prop) : (term225 _133751 _95603 _95604 _95602) = (term302 _133751 _95602 _95603 _95604).
Proof. exact (EQ_MP (@lem7152829 _133751 _95602 _95603 _95604) (@lem0)). Qed.
Lemma lem7152831 {_133751 : Type'} (_95602 : _133751 -> real) (_95603 : _133751 -> Prop) (_95604 : _133751 -> Prop) (h1 : term11 _133751) : term302 _133751 _95602 _95603 _95604.
Proof. exact (EQ_MP (@lem7152830 _133751 _95602 _95603 _95604) (@lem7152097 _133751 _95603 _95604 _95602 h1)). Qed.
Lemma lem7152833 (b : Prop) (a : Prop) : (a \/ b) = (term257 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7152834 {_133751 : Type'} (_95603 : _133751 -> Prop) (_95604 : _133751 -> Prop) (_95602 : _133751 -> real) : (term302 _133751 _95602 _95603 _95604) = (term303 _133751 _95603 _95604 _95602).
Proof. exact (@lem7152833 (term191 _133751 _95603 _95604) ((term194 _133751 _95603 _95604 _95602) = (term78 _133751 _95603 _95604 _95602))). Qed.
Lemma lem7152836 (a : Prop) (b : Prop) : (term259 a b) = (term260 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7152837 {_133751 : Type'} (_95603 : _133751 -> Prop) (_95604 : _133751 -> Prop) : (term304 _133751 _95603 _95604) = (term305 _133751 _95603 _95604).
Proof. exact (@lem7152836 (term219 _133751 _95603) (term188 _133751 _95603 _95604)). Qed.
Lemma lem7152839 (a : Prop) : (term263 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7152840 {_133751 : Type'} (_95603 : _133751 -> Prop) : (term264 _133751 _95603) = (@FINITE _133751 _95603).
Proof. exact (@lem7152839 (@FINITE _133751 _95603)). Qed.
Lemma lem7152841 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7152842 {_133751 : Type'} (_95603 : _133751 -> Prop) : (term265 _133751 _95603) = (term266 _133751 _95603).
Proof. exact (MK_COMB (@lem7152841) (@lem7152840 _133751 _95603)). Qed.
Lemma lem7152844 (a : Prop) (b : Prop) : (term259 a b) = (term260 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7152845 {_133751 : Type'} (_95603 : _133751 -> Prop) (_95604 : _133751 -> Prop) : (term306 _133751 _95603 _95604) = (term307 _133751 _95603 _95604).
Proof. exact (@lem7152844 (term219 _133751 _95604) (term224 _133751 _95603 _95604)). Qed.
Lemma lem7152847 (a : Prop) : (term263 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7152848 {_133751 : Type'} (_95604 : _133751 -> Prop) : (term264 _133751 _95604) = (@FINITE _133751 _95604).
Proof. exact (@lem7152847 (@FINITE _133751 _95604)). Qed.
Lemma lem7152849 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7152850 {_133751 : Type'} (_95604 : _133751 -> Prop) : (term265 _133751 _95604) = (term266 _133751 _95604).
Proof. exact (MK_COMB (@lem7152849) (@lem7152848 _133751 _95604)). Qed.
Lemma lem7152852 (a : Prop) : (term263 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7152853 {_133751 : Type'} (_95603 : _133751 -> Prop) (_95604 : _133751 -> Prop) : (term308 _133751 _95603 _95604) = (@DISJOINT _133751 _95603 _95604).
Proof. exact (@lem7152852 (@DISJOINT _133751 _95603 _95604)). Qed.
Lemma lem7152854 {_133751 : Type'} (_95603 : _133751 -> Prop) (_95604 : _133751 -> Prop) : (term307 _133751 _95603 _95604) = (term193 _133751 _95603 _95604).
Proof. exact (MK_COMB (@lem7152850 _133751 _95604) (@lem7152853 _133751 _95603 _95604)). Qed.
Lemma lem7152855 {_133751 : Type'} (_95603 : _133751 -> Prop) (_95604 : _133751 -> Prop) : (term306 _133751 _95603 _95604) = (term193 _133751 _95603 _95604).
Proof. exact (TRANS (@lem7152845 _133751 _95603 _95604) (@lem7152854 _133751 _95603 _95604)). Qed.
Lemma lem7152856 {_133751 : Type'} (_95603 : _133751 -> Prop) (_95604 : _133751 -> Prop) : (term305 _133751 _95603 _95604) = (term199 _133751 _95603 _95604).
Proof. exact (MK_COMB (@lem7152842 _133751 _95603) (@lem7152855 _133751 _95603 _95604)). Qed.
Lemma lem7152857 {_133751 : Type'} (_95603 : _133751 -> Prop) (_95604 : _133751 -> Prop) : (term304 _133751 _95603 _95604) = (term199 _133751 _95603 _95604).
Proof. exact (TRANS (@lem7152837 _133751 _95603 _95604) (@lem7152856 _133751 _95603 _95604)). Qed.
Lemma lem7152858 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7152859 {_133751 : Type'} (_95603 : _133751 -> Prop) (_95604 : _133751 -> Prop) : (term309 _133751 _95603 _95604) = (term310 _133751 _95603 _95604).
Proof. exact (MK_COMB (@lem7152858) (@lem7152857 _133751 _95603 _95604)). Qed.
Lemma lem7152860 {_133751 : Type'} (_95603 : _133751 -> Prop) (_95604 : _133751 -> Prop) (_95602 : _133751 -> real) : ((term194 _133751 _95603 _95604 _95602) = (term78 _133751 _95603 _95604 _95602)) = ((term194 _133751 _95603 _95604 _95602) = (term78 _133751 _95603 _95604 _95602)).
Proof. exact (eq_refl ((term194 _133751 _95603 _95604 _95602) = (term78 _133751 _95603 _95604 _95602))). Qed.
Lemma lem7152861 {_133751 : Type'} (_95603 : _133751 -> Prop) (_95604 : _133751 -> Prop) (_95602 : _133751 -> real) : (term303 _133751 _95603 _95604 _95602) = (term45 _133751 _95603 _95604 _95602).
Proof. exact (MK_COMB (@lem7152859 _133751 _95603 _95604) (@lem7152860 _133751 _95603 _95604 _95602)). Qed.
Lemma lem7152862 {_133751 : Type'} (_95603 : _133751 -> Prop) (_95604 : _133751 -> Prop) (_95602 : _133751 -> real) : (term302 _133751 _95602 _95603 _95604) = (term45 _133751 _95603 _95604 _95602).
Proof. exact (TRANS (@lem7152834 _133751 _95603 _95604 _95602) (@lem7152861 _133751 _95603 _95604 _95602)). Qed.
Lemma lem7152864 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term12 _133751) (h2 : term13 _133751) (h3 : term14 _133751) (h4 : term76 _133751 s t u f) : term193 _133751 s t.
Proof. exact (conj (@lem7152602 _133751 s t u f h2 h3 h4) (@lem7152635 _133751 s t u f h1 h4)). Qed.
Lemma lem7152865 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term12 _133751) (h2 : term13 _133751) (h3 : term14 _133751) (h4 : term76 _133751 s t u f) : term199 _133751 s t.
Proof. exact (conj (@lem7152573 _133751 s t u f h2 h3 h4) (@lem7152864 _133751 s t u f h1 h2 h3 h4)). Qed.
Lemma lem7152867 {_133751 : Type'} (_95603 : _133751 -> Prop) (_95604 : _133751 -> Prop) (_95602 : _133751 -> real) (h1 : term11 _133751) : term45 _133751 _95603 _95604 _95602.
Proof. exact (EQ_MP (@lem7152862 _133751 _95603 _95604 _95602) (@lem7152831 _133751 _95602 _95603 _95604 h1)). Qed.
Lemma lem7152868 {_133751 : Type'} (_95603 : _133751 -> Prop) (_95604 : _133751 -> Prop) (_95602 : _133751 -> real) (h1 : term11 _133751) : term45 _133751 _95603 _95604 _95602.
Proof. exact (@lem7152867 _133751 _95603 _95604 _95602 h1). Qed.
Lemma lem7152869 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (_95602 : _133751 -> real) (h1 : term11 _133751) : term45 _133751 s t _95602.
Proof. exact (@lem7152868 _133751 s t _95602 h1). Qed.
Lemma lem7152872 {_133751 : Type'} (_95602 : _133751 -> real) (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term12 _133751) (h2 : term13 _133751) (h3 : term11 _133751) (h4 : term14 _133751) (h5 : term76 _133751 s t u f) : (term194 _133751 s t _95602) = (term78 _133751 s t _95602).
Proof. exact (@lem7152869 _133751 s t _95602 h3 (@lem7152865 _133751 s t u f h1 h2 h4 h5)). Qed.
Lemma lem7152873 {_133751 : Type'} (_95602 : _133751 -> real) (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term12 _133751) (h2 : term13 _133751) (h3 : term11 _133751) (h4 : term14 _133751) (h5 : term76 _133751 s t u f) : (term194 _133751 s t _95602) = (term78 _133751 s t _95602).
Proof. exact (@lem7152872 _133751 _95602 s t u f h1 h2 h3 h4 h5). Qed.
Lemma lem7152874 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term12 _133751) (h2 : term13 _133751) (h3 : term11 _133751) (h4 : term14 _133751) (h5 : term76 _133751 s t u f) : (term194 _133751 s t f) = (term78 _133751 s t f).
Proof. exact (@lem7152873 _133751 f s t u f h1 h2 h3 h4 h5). Qed.
Lemma lem7152875 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term12 _133751) (h2 : term13 _133751) (h3 : term11 _133751) (h4 : term14 _133751) (h5 : term76 _133751 s t u f) : term311 _133751 s t f.
Proof. exact (fun h0 : term312 _133751 s t f => @lem7152874 _133751 s t u f h1 h2 h3 h4 h5). Qed.
Lemma lem7152877 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7152878 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (f : _133751 -> real) : (term311 _133751 s t f) = ((term194 _133751 s t f) = (term78 _133751 s t f)).
Proof. exact (@lem7152877 ((term194 _133751 s t f) = (term78 _133751 s t f))). Qed.
Lemma lem7152879 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term12 _133751) (h2 : term13 _133751) (h3 : term11 _133751) (h4 : term14 _133751) (h5 : term76 _133751 s t u f) : (term194 _133751 s t f) = (term78 _133751 s t f).
Proof. exact (EQ_MP (@lem7152878 _133751 s t f) (@lem7152875 _133751 s t u f h1 h2 h3 h4 h5)). Qed.
Lemma lem7152881 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem7152882 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (f : _133751 -> real) : (term194 _133751 s t f) = (term194 _133751 s t f).
Proof. exact (@lem7152881 (term194 _133751 s t f)). Qed.
Lemma lem7152883 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (f : _133751 -> real) : term313 _133751 s t f.
Proof. exact (fun h0 : term314 _133751 s t f => @lem7152882 _133751 s t f). Qed.
Lemma lem7152885 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7152886 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (f : _133751 -> real) : (term313 _133751 s t f) = ((term194 _133751 s t f) = (term194 _133751 s t f)).
Proof. exact (@lem7152885 ((term194 _133751 s t f) = (term194 _133751 s t f))). Qed.
Lemma lem7152887 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (f : _133751 -> real) : (term194 _133751 s t f) = (term194 _133751 s t f).
Proof. exact (EQ_MP (@lem7152886 _133751 s t f) (@lem7152883 _133751 s t f)). Qed.
Lemma lem7152905 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7152906 (y : real) (x : real) (z : real) : (term315 x y z) = (term316 y x z).
Proof. exact (@lem7152905 (y = z) (term317 x z)). Qed.
Lemma lem7152916 (x : real) (y : real) : (term318 x y) = (term318 x y).
Proof. exact (eq_refl (term318 x y)). Qed.
Lemma lem7152917 (y : real) (x : real) (z : real) : (term245 x y z) = (term319 y x z).
Proof. exact (MK_COMB (@lem7152916 x y) (@lem7152906 y x z)). Qed.
Lemma lem7152921 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7152922 (y : real) (x : real) (z : real) : (term319 y x z) = (term320 y x z).
Proof. exact (@lem7152921 (y = z) (term317 x y) (term317 x z)). Qed.
Lemma lem7152944 (y : real) (x : real) (z : real) : (term245 x y z) = (term320 y x z).
Proof. exact (TRANS (@lem7152917 y x z) (@lem7152922 y x z)). Qed.
Lemma lem7152945 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7152946 (y : real) (x : real) (z : real) : (term321 x y z) = (term322 y x z).
Proof. exact (MK_COMB (@lem7152945) (@lem7152944 y x z)). Qed.
Lemma lem7152968 (y : real) (x : real) (z : real) : (term320 y x z) = (term320 y x z).
Proof. exact (eq_refl (term320 y x z)). Qed.
Lemma lem7152969 (y : real) (x : real) (z : real) : ((term245 x y z) = (term320 y x z)) = ((term320 y x z) = (term320 y x z)).
Proof. exact (MK_COMB (@lem7152946 y x z) (@lem7152968 y x z)). Qed.
Lemma lem7152971 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7152972 (x : Prop) : (x = x) = True.
Proof. exact (@lem7152971 Prop x). Qed.
Lemma lem7152973 (y : real) (x : real) (z : real) : ((term320 y x z) = (term320 y x z)) = True.
Proof. exact (@lem7152972 (term320 y x z)). Qed.
Lemma lem7152974 (y : real) (x : real) (z : real) : ((term245 x y z) = (term320 y x z)) = True.
Proof. exact (TRANS (@lem7152969 y x z) (@lem7152973 y x z)). Qed.
Lemma lem7152975 (y : real) (x : real) (z : real) : True = ((term245 x y z) = (term320 y x z)).
Proof. exact (SYM (@lem7152974 y x z)). Qed.
Lemma lem7152976 (y : real) (x : real) (z : real) : (term245 x y z) = (term320 y x z).
Proof. exact (EQ_MP (@lem7152975 y x z) (@lem0)). Qed.
Lemma lem7152977 (y : real) (x : real) (z : real) : term320 y x z.
Proof. exact (EQ_MP (@lem7152976 y x z) (@lem7152442 x y z)). Qed.
Lemma lem7152979 (b : Prop) (a : Prop) : (a \/ b) = (term257 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7152980 (x : real) (y : real) (z : real) : (term320 y x z) = (term323 x y z).
Proof. exact (@lem7152979 (term324 y x z) (y = z)). Qed.
Lemma lem7152982 (a : Prop) (b : Prop) : (term259 a b) = (term260 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7152983 (y : real) (x : real) (z : real) : (term325 y x z) = (term326 y x z).
Proof. exact (@lem7152982 (term317 x y) (term317 x z)). Qed.
Lemma lem7152985 (a : Prop) : (term263 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7152986 (x : real) (y : real) : (term327 x y) = (x = y).
Proof. exact (@lem7152985 (x = y)). Qed.
Lemma lem7152987 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7152988 (x : real) (y : real) : (term328 x y) = (term329 x y).
Proof. exact (MK_COMB (@lem7152987) (@lem7152986 x y)). Qed.
Lemma lem7152990 (a : Prop) : (term263 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7152991 (x : real) (z : real) : (term327 x z) = (x = z).
Proof. exact (@lem7152990 (x = z)). Qed.
Lemma lem7152992 (y : real) (x : real) (z : real) : (term326 y x z) = (term330 y x z).
Proof. exact (MK_COMB (@lem7152988 x y) (@lem7152991 x z)). Qed.
Lemma lem7152993 (y : real) (x : real) (z : real) : (term325 y x z) = (term330 y x z).
Proof. exact (TRANS (@lem7152983 y x z) (@lem7152992 y x z)). Qed.
Lemma lem7152994 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7152995 (y : real) (x : real) (z : real) : (term331 y x z) = (term332 y x z).
Proof. exact (MK_COMB (@lem7152994) (@lem7152993 y x z)). Qed.
Lemma lem7152996 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem7152997 (x : real) (y : real) (z : real) : (term323 x y z) = (term333 x y z).
Proof. exact (MK_COMB (@lem7152995 y x z) (@lem7152996 y z)). Qed.
Lemma lem7152998 (x : real) (y : real) (z : real) : (term320 y x z) = (term333 x y z).
Proof. exact (TRANS (@lem7152980 x y z) (@lem7152997 x y z)). Qed.
Lemma lem7153000 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term12 _133751) (h2 : term13 _133751) (h3 : term11 _133751) (h4 : term14 _133751) (h5 : term76 _133751 s t u f) : term334 _133751 s t f.
Proof. exact (conj (@lem7152879 _133751 s t u f h1 h2 h3 h4 h5) (@lem7152887 _133751 s t f)). Qed.
Lemma lem7153002 (x : real) (y : real) (z : real) : term333 x y z.
Proof. exact (EQ_MP (@lem7152998 x y z) (@lem7152977 y x z)). Qed.
Lemma lem7153003 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (f : _133751 -> real) : term335 _133751 s t f.
Proof. exact (@lem7153002 (term194 _133751 s t f) (term78 _133751 s t f) (term194 _133751 s t f)). Qed.
Lemma lem7153006 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term12 _133751) (h2 : term13 _133751) (h3 : term11 _133751) (h4 : term14 _133751) (h5 : term76 _133751 s t u f) : (term78 _133751 s t f) = (term194 _133751 s t f).
Proof. exact (@lem7153003 _133751 s t f (@lem7153000 _133751 s t u f h1 h2 h3 h4 h5)). Qed.
Lemma lem7153007 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term12 _133751) (h2 : term13 _133751) (h3 : term11 _133751) (h4 : term14 _133751) (h5 : term76 _133751 s t u f) : term336 _133751 s t f.
Proof. exact (fun h0 : term230 _133751 s t f => @lem7153006 _133751 s t u f h1 h2 h3 h4 h5). Qed.
Lemma lem7153009 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7153010 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (f : _133751 -> real) : (term336 _133751 s t f) = ((term78 _133751 s t f) = (term194 _133751 s t f)).
Proof. exact (@lem7153009 ((term78 _133751 s t f) = (term194 _133751 s t f))). Qed.
Lemma lem7153011 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term12 _133751) (h2 : term13 _133751) (h3 : term11 _133751) (h4 : term14 _133751) (h5 : term76 _133751 s t u f) : (term78 _133751 s t f) = (term194 _133751 s t f).
Proof. exact (EQ_MP (@lem7153010 _133751 s t f) (@lem7153007 _133751 s t u f h1 h2 h3 h4 h5)). Qed.
Lemma lem7153014 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7153016 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (f : _133751 -> real) : (term230 _133751 s t f) = (term337 _133751 s t f).
Proof. exact (@lem7153014 ((term78 _133751 s t f) = (term194 _133751 s t f))). Qed.
Lemma lem7153019 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term76 _133751 s t u f) : term337 _133751 s t f.
Proof. exact (EQ_MP (@lem7153016 _133751 s t f) (@lem7152111 _133751 s t u f h1)). Qed.
Lemma lem7153022 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term12 _133751) (h2 : term13 _133751) (h3 : term11 _133751) (h4 : term14 _133751) (h5 : term76 _133751 s t u f) : False.
Proof. exact (@lem7153019 _133751 s t u f h5 (@lem7153011 _133751 s t u f h1 h2 h3 h4 h5)). Qed.
Lemma lem7153023 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term12 _133751) (h2 : term13 _133751) (h3 : term11 _133751) (h4 : term14 _133751) (h5 : term76 _133751 s t u f) : term338.
Proof. exact (fun h0 : ~ False => @lem7153022 _133751 s t u f h1 h2 h3 h4 h5). Qed.
Lemma lem7153025 (p : Prop) : (term248 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7153026 : term338 = False.
Proof. exact (@lem7153025 False). Qed.
Lemma lem7153029 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term12 _133751) (h2 : term13 _133751) (h3 : term11 _133751) (h4 : term14 _133751) (h5 : term76 _133751 s t u f) : False.
Proof. exact (EQ_MP (@lem7153026) (@lem7153023 _133751 s t u f h1 h2 h3 h4 h5)). Qed.
Lemma lem7153030 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term12 _133751) (h2 : term13 _133751) (h3 : term11 _133751) (h4 : term14 _133751) (h5 : term76 _133751 s t u f) : (term76 _133751 s t u f) = False.
Proof. exact (prop_ext (fun h6 : term76 _133751 s t u f => @lem7153029 _133751 s t u f h1 h2 h3 h4 h5) (fun h6 : False => @lem7151333 _133751 s t u f h5)). Qed.
Lemma lem7153031 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term12 _133751) (h2 : term13 _133751) (h3 : term11 _133751) (h4 : term14 _133751) (h5 : term76 _133751 s t u f) : False.
Proof. exact (EQ_MP (@lem7153030 _133751 s t u f h1 h2 h3 h4 h5) (@lem7151333 _133751 s t u f h5)). Qed.
Lemma lem7153032 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term12 _133751) (h2 : term13 _133751) (h3 : term11 _133751) (h4 : term14 _133751) (h5 : term76 _133751 s t u f) : (term14 _133751) = False.
Proof. exact (prop_ext (fun h6 : term14 _133751 => @lem7153031 _133751 s t u f h1 h2 h3 h4 h5) (fun h6 : False => @lem7150993 _133751 h4)). Qed.
Lemma lem7153033 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (u : _133751 -> Prop) (f : _133751 -> real) (h1 : term12 _133751) (h2 : term13 _133751) (h3 : term11 _133751) (h4 : term14 _133751) (h5 : term76 _133751 s t u f) : False.
Proof. exact (EQ_MP (@lem7153032 _133751 s t u f h1 h2 h3 h4 h5) (@lem7150993 _133751 h4)). Qed.
Lemma lem7153034 {_133751 : Type'} (s : _133751 -> Prop) (t : _133751 -> Prop) (f : _133751 -> real) (h1 : term12 _133751) (h2 : term13 _133751) (h3 : term11 _133751) (h4 : term87 _133751 s t f) (h5 : term14 _133751) : False.
Proof. exact (ex_elim (@lem7150924 _133751 s t f h4) (fun u : _133751 -> Prop => fun h0 : term86 _133751 s t f u => @lem7153033 _133751 s t u f h1 h2 h3 h5 h0)). Qed.
Lemma lem7153035 {_133751 : Type'} (s : _133751 -> Prop) (f : _133751 -> real) (h1 : term12 _133751) (h2 : term13 _133751) (h3 : term11 _133751) (h4 : term94 _133751 s f) (h5 : term14 _133751) : False.
Proof. exact (ex_elim (@lem7150923 _133751 s f h4) (fun t : _133751 -> Prop => fun h0 : term93 _133751 s f t => @lem7153034 _133751 s t f h1 h2 h3 h0 h5)). Qed.
Lemma lem7153036 {_133751 : Type'} (f : _133751 -> real) (h1 : term12 _133751) (h2 : term13 _133751) (h3 : term11 _133751) (h4 : term10 _133751 f) (h5 : term14 _133751) : False.
Proof. exact (ex_elim (@lem7149786 _133751 f h4) (fun s : _133751 -> Prop => fun h0 : term99 _133751 f s => @lem7153035 _133751 s f h1 h2 h3 h0 h5)). Qed.
Lemma lem7153037 {_133751 : Type'} (f : _133751 -> real) (h1 : term12 _133751) (h2 : term13 _133751) (h3 : term11 _133751) (h4 : term10 _133751 f) (h5 : term14 _133751) : (term14 _133751) = False.
Proof. exact (prop_ext (fun h6 : term14 _133751 => @lem7153036 _133751 f h1 h2 h3 h4 h5) (fun h6 : False => @lem7149862 _133751 h5)). Qed.
Lemma lem7153038 {_133751 : Type'} (f : _133751 -> real) (h1 : term12 _133751) (h2 : term13 _133751) (h3 : term11 _133751) (h4 : term10 _133751 f) (h5 : term14 _133751) : False.
Proof. exact (EQ_MP (@lem7153037 _133751 f h1 h2 h3 h4 h5) (@lem7149862 _133751 h5)). Qed.
Lemma lem7153039 {_133751 : Type'} (f : _133751 -> real) (h1 : term12 _133751) (h2 : term13 _133751) (h3 : term10 _133751 f) (h4 : term14 _133751) : term19 _133751.
Proof. exact (fun h0 : term11 _133751 => @lem7153038 _133751 f h1 h2 h0 h3 h4). Qed.
Lemma lem7153040 {_133751 : Type'} : (term19 _133751) = (term20 _133751).
Proof. exact (@lem69 (term11 _133751)). Qed.
Lemma lem7153041 {_133751 : Type'} (f : _133751 -> real) (h1 : term12 _133751) (h2 : term13 _133751) (h3 : term10 _133751 f) (h4 : term14 _133751) : term20 _133751.
Proof. exact (EQ_MP (@lem7153040 _133751) (@lem7153039 _133751 f h1 h2 h3 h4)). Qed.
Lemma lem7153042 {_131550 _133751 : Type'} (f : _133751 -> real) (h1 : term12 _133751) (h2 : term13 _133751) (h3 : term10 _133751 f) (h4 : term14 _133751) : term23 _131550 _133751.
Proof. exact (fun h0 : term11 _131550 => @lem7153041 _133751 f h1 h2 h3 h4). Qed.
Lemma lem7153043 {_131550 _133751 : Type'} (f : _133751 -> real) (h1 : term13 _133751) (h2 : term10 _133751 f) (h3 : term14 _133751) : term26 _131550 _133751.
Proof. exact (fun h0 : term12 _133751 => @lem7153042 _131550 _133751 f h0 h1 h2 h3). Qed.
Lemma lem7153044 {_131550 _133751 : Type'} (f : _133751 -> real) (h1 : term13 _133751) (h2 : term10 _133751 f) (h3 : term14 _133751) : term28 _131550 _133751.
Proof. exact (fun h0 : term12 _131550 => @lem7153043 _131550 _133751 f h1 h2 h3). Qed.
Lemma lem7153045 {_131550 _133751 : Type'} (f : _133751 -> real) (h1 : term10 _133751 f) (h2 : term14 _133751) : term31 _131550 _133751.
Proof. exact (fun h0 : term13 _133751 => @lem7153044 _131550 _133751 f h0 h1 h2). Qed.
Lemma lem7153046 {_131550 _133751 : Type'} (f : _133751 -> real) (h1 : term10 _133751 f) (h2 : term14 _133751) : term33 _131550 _133751.
Proof. exact (fun h0 : term13 _131550 => @lem7153045 _131550 _133751 f h1 h2). Qed.
Lemma lem7153047 {_131550 _133751 : Type'} (f : _133751 -> real) (h1 : term10 _133751 f) : term36 _131550 _133751.
Proof. exact (fun h0 : term14 _133751 => @lem7153046 _131550 _133751 f h1 h0). Qed.
Lemma lem7153048 {_131550 _133751 : Type'} (f : _133751 -> real) (h1 : term10 _133751 f) : term38 _131550 _133751.
Proof. exact (fun h0 : term14 _131550 => @lem7153047 _131550 _133751 f h1). Qed.
Lemma lem7153049 {_131550 _133751 : Type'} (f : _133751 -> real) : term40 _131550 _133751 f.
Proof. exact (fun h0 : term10 _133751 f => @lem7153048 _131550 _133751 f h0). Qed.
Lemma lem7153054 {_131550 _133751 : Type'} : term44 _131550 _133751.
Proof. exact (fun f : _133751 -> real => @lem7153049 _131550 _133751 f). Qed.
Lemma lem7153055 {_131550 _133751 : Type'} : term43 _131550 _133751.
Proof. exact (EQ_MP (@lem7149671 _131550 _133751) (@lem7153054 _131550 _133751)). Qed.
Lemma lem7153056 {_131550 _133751 : Type'} (f : _133751 -> real) : term339 _131550 _133751 f.
Proof. exact (@lem7153055 _131550 _133751 f). Qed.
Lemma lem7153057 {_131550 _133751 : Type'} (f : _133751 -> real) : (term339 _131550 _133751 f) = (term15 _131550 _133751 f).
Proof. exact (eq_refl (term339 _131550 _133751 f)). Qed.
Lemma lem7153058 {_131550 _133751 : Type'} (f : _133751 -> real) : term15 _131550 _133751 f.
Proof. exact (EQ_MP (@lem7153057 _131550 _133751 f) (@lem7153056 _131550 _133751 f)). Qed.
Lemma lem7153060 {_131550 _133751 : Type'} (f : _133751 -> real) : term15 _131550 _133751 f.
Proof. exact (@lem7149086 _131550 _133751 f (@lem7153058 _131550 _133751 f)). Qed.
Lemma lem7153061 {_131550 _133751 : Type'} (f : _133751 -> real) (h1 : term10 _133751 f) : term37 _131550 _133751.
Proof. exact (@lem7153060 _131550 _133751 f (@lem7149056 _133751 f h1)). Qed.
Lemma lem7153062 {_131550 _133751 : Type'} (f : _133751 -> real) (h1 : term10 _133751 f) : term35 _131550 _133751.
Proof. exact (@lem7153061 _131550 _133751 f h1 (@lem7149068 _131550)). Qed.
Lemma lem7153063 {_131550 _133751 : Type'} (f : _133751 -> real) (h1 : term10 _133751 f) : term32 _131550 _133751.
Proof. exact (@lem7153062 _131550 _133751 f h1 (@lem7149067 _133751)). Qed.
Lemma lem7153064 {_131550 _133751 : Type'} (f : _133751 -> real) (h1 : term10 _133751 f) : term30 _131550 _133751.
Proof. exact (@lem7153063 _131550 _133751 f h1 (@lem7149066 _131550)). Qed.
Lemma lem7153065 {_131550 _133751 : Type'} (f : _133751 -> real) (h1 : term10 _133751 f) : term27 _131550 _133751.
Proof. exact (@lem7153064 _131550 _133751 f h1 (@lem7149065 _133751)). Qed.
Lemma lem7153066 {_131550 _133751 : Type'} (f : _133751 -> real) (h1 : term10 _133751 f) : term25 _131550 _133751.
Proof. exact (@lem7153065 _131550 _133751 f h1 (@lem7149061 _131550)). Qed.
Lemma lem7153067 {_131550 _133751 : Type'} (f : _133751 -> real) (h1 : term10 _133751 f) : term22 _131550 _133751.
Proof. exact (@lem7153066 _131550 _133751 f h1 (@lem7149060 _133751)). Qed.
Lemma lem7153068 {_133751 : Type'} (f : _133751 -> real) (h1 : term10 _133751 f) : term19 _133751.
Proof. exact (@lem7153067 Prop _133751 f h1 (@lem7067826 Prop)). Qed.
Lemma lem7153069 {_133751 : Type'} (f : _133751 -> real) (h1 : term10 _133751 f) : False.
Proof. exact (@lem7153068 _133751 f h1 (@lem7149057 _133751)). Qed.
Lemma lem7153070 {_133751 : Type'} (f : _133751 -> real) (h1 : term10 _133751 f) : (term10 _133751 f) = False.
Proof. exact (prop_ext (fun h2 : term10 _133751 f => @lem7153069 _133751 f h1) (fun h2 : False => @lem7149056 _133751 f h1)). Qed.
Lemma lem7153071 {_133751 : Type'} (f : _133751 -> real) (h1 : term10 _133751 f) : False.
Proof. exact (EQ_MP (@lem7153070 _133751 f h1) (@lem7149056 _133751 f h1)). Qed.
Lemma lem7153072 {_133751 : Type'} (f : _133751 -> real) : term9 _133751 f.
Proof. exact (fun h0 : term10 _133751 f => @lem7153071 _133751 f h0). Qed.
Lemma lem7153073 {_133751 : Type'} (f : _133751 -> real) : term8 _133751 f.
Proof. exact (EQ_MP (@lem7149055 _133751 f) (@lem7153072 _133751 f)). Qed.
